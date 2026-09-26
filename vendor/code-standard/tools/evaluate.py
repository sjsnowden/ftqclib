#!/usr/bin/env python3
"""The `eval` verb: prepare, run and score a directory of sessions against the tasks under `eval/tasks/`, so a rig
that records agent runs can supply the arms, the models and the runs while this object supplies what conformance
looks like (eval/README.md).

Three phases, each callable alone or in sequence (`standard.py eval OUT ...` runs all three):
  prepare OUT --modules M... [--arms A...] [--runner CMD|identity|reference] [--repeat N]
              [--binding PATH] [--questions PATH] [--seed N] [--no-record]
                              write OUT/manifest.json, OUT/arms.sealed.json and OUT/sessions/<id>/ for every
                              task x arm x repeat
  run OUT                     call the runner once per session, in manifest order; write <session>/runner-exit
  score OUT                   score every session's `work/` and write OUT/rows.jsonl, one row per session

A phase refuses to run out of order: `run` refuses an OUT that has already been scored (`rows.jsonl` exists);
`score` refuses an OUT where some session has not been run (no `runner-exit`). Nothing under `OUT/sessions/`
names a session's arm; the mapping lives only in `arms.sealed.json` (mode 0600), which `score` alone reads."""
import hashlib, json, os, random, re, shlex, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import standard as S
import record as R

OBJECT = S.OBJECT
EVAL = os.path.join(OBJECT, "eval")
sys.path.insert(0, EVAL)
import score as EV

ARMS = ("none", "placebo", "brief", "questions")
RUNNER_TIMEOUT_S = int(os.environ.get("ONTOL_EVAL_RUNNER_TIMEOUT_S", "1800"))

# ---- pure helpers ------------------------------------------------------------------------------------------------

def canonical_line(data):
    """One line of canonical JSON for rows.jsonl: sorted keys, stable field order, a trailing newline."""
    return json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(", ", ": ")) + "\n"

def cut_to_words(text, n):
    """`text` truncated after its `n`th whitespace-separated word, so every session of a run gets a placebo of the
    same length in words as that run's brief."""
    tokens = list(re.finditer(r"\S+", text))
    if n <= 0: return ""
    end = tokens[n - 1].end() if n < len(tokens) else len(text)
    return text[:end].rstrip("\n") + "\n"

def select_tasks(modules):
    """Task ids of every `eval/tasks/*/*/task.json` whose module is in `modules`, sorted. Refuses a module the
    object lacks (no `modules/NAME.md`) and a module with no matching tasks."""
    for m in modules:
        if not os.path.exists(os.path.join(OBJECT, "modules", m + ".md")): raise ValueError(f"no module {m} in the object")
    ids = [t for t in EV.tasks() if t.split("/", 1)[0] in modules]
    for m in modules:
        if not any(t.split("/", 1)[0] == m for t in ids): raise ValueError(f"module {m} has no tasks")
    return ids

def take(argv, flag):
    """The values following `flag` up to the next `--flag`, or None when `flag` is absent."""
    if flag not in argv: return None
    i = argv.index(flag)
    j = next((k for k in range(i + 1, len(argv)) if argv[k].startswith("--")), len(argv))
    return argv[i + 1:j]

# ---- prepare ------------------------------------------------------------------------------------------------------

def object_id():
    return hashlib.sha256(S.read(os.path.join(OBJECT, "MANIFEST")).encode()).hexdigest()

def arm_texts(arms, modules, edited_binding_path, questions_path):
    """{arm: text} for every arm in `arms` that writes a `CLAUDE.md` (all but `none`), computed once per run so
    every session of the same arm gets byte-identical text."""
    texts = {}
    need_brief = "brief" in arms or "placebo" in arms
    if need_brief: texts["brief"] = S.brief_text(OBJECT, edited_binding_path, os.path.dirname(edited_binding_path))
    if "questions" in arms: texts["questions"] = S.questions_text(OBJECT, questions_path)
    if "placebo" in arms:
        words = len(re.findall(r"\S+", texts["brief"]))
        texts["placebo"] = cut_to_words(S.read(os.path.join(EVAL, "placebo.md")), words)
    return texts

def prepare(out, modules, arms, runner, repeat, binding, questions, seed, record):
    """Write `manifest.json`, `arms.sealed.json` and a `sessions/<id>/` for every task x arm x repeat. Refuses an
    `out` that is already prepared, a bad `--modules`, and a missing `--binding` or `--questions`."""
    if os.path.exists(os.path.join(out, "manifest.json")): raise ValueError(f"{out} is already prepared")
    if not modules: raise ValueError("--modules is required")
    if repeat < 1: raise ValueError("--repeat must be at least 1")
    task_ids = select_tasks(modules)
    binding_abs = os.path.abspath(binding)
    if not os.path.exists(binding_abs): raise ValueError(f"no binding at {binding}")
    questions_abs = os.path.abspath(questions) if questions else os.path.join(OBJECT, "questions.json")
    if not os.path.exists(questions_abs): raise ValueError(f"no questions file at {questions_abs}")
    unknown = [a for a in arms if a not in ARMS]
    if unknown: raise ValueError(f"no such arm(s): {' '.join(unknown)}")

    os.makedirs(os.path.join(out, "sessions"), exist_ok=True)
    edited_binding_path = os.path.join(out, "binding.md")
    with open(edited_binding_path, "w", encoding="utf-8") as f:
        f.write(S.edit_header(S.read(binding_abs), "modules", [" ".join(modules)]))
    texts = arm_texts(arms, modules, edited_binding_path, questions_abs if questions else None)
    task_paragraph = S.questions_task(OBJECT, questions_abs if questions else None) if record else None
    schema_text = S.canonical_json(S.questions_schema(OBJECT, questions_abs if questions else None)) if record else None

    rng = random.Random(seed)
    combos = [(task, arm, r) for task in task_ids for arm in arms for r in range(repeat)]
    rng.shuffle(combos)
    used, sessions, arm_map = set(), [], {}
    for task, arm, r in combos:
        while True:
            sid = f"{rng.getrandbits(32):08x}"
            if sid not in used: break
        used.add(sid)
        sessions.append({"id": sid, "task": task, "module": task.split("/", 1)[0], "repeat": r})
        arm_map[sid] = arm

    for session in sessions:
        sid, task, arm = session["id"], session["task"], arm_map[session["id"]]
        session_dir = os.path.join(out, "sessions", sid)
        work_dir = os.path.join(session_dir, "work")
        shutil.copytree(os.path.join(EVAL, "tasks", task, "seed"), work_dir)
        task_txt = S.read(os.path.join(EVAL, "tasks", task, "task.txt"))
        if record: task_txt = task_txt.rstrip("\n") + "\n\n" + task_paragraph.rstrip("\n") + "\n"
        with open(os.path.join(session_dir, "task.txt"), "w", encoding="utf-8") as f: f.write(task_txt)
        if arm != "none":
            with open(os.path.join(work_dir, "CLAUDE.md"), "w", encoding="utf-8") as f: f.write(texts[arm])
        if record:
            with open(os.path.join(work_dir, "record.schema.json"), "w", encoding="utf-8") as f: f.write(schema_text)

    manifest = {"object": object_id(), "questions": S.sha256_of(questions_abs), "questions_override": bool(questions),
                "binding": {"path": binding, "sha256": S.sha256_of(binding_abs)}, "modules": modules, "arms": list(arms),
                "tasks": task_ids, "repeat": repeat, "runner": runner, "seed": seed, "record": record,
                "sessions": sessions}
    with open(os.path.join(out, "manifest.json"), "w", encoding="utf-8") as f: f.write(S.canonical_json(manifest))
    sealed_path = os.path.join(out, "arms.sealed.json")
    with open(sealed_path, "w", encoding="utf-8") as f: f.write(S.canonical_json(arm_map))
    os.chmod(sealed_path, 0o600)
    return manifest

# ---- run ------------------------------------------------------------------------------------------------------

def call_runner(runner, session_dir, task):
    """(code, seconds, timed_out) of one call of `runner` on `session_dir`. The built-ins `identity` (does
    nothing) and `reference` (copies the task's `reference/` over `work/`) need no process; anything else is run
    as `CMD SESSION_DIR` with cwd `SESSION_DIR`, under a deadline. A non-zero exit or a timeout is recorded here,
    never raised."""
    start = time.time()
    if runner == "identity":
        return {"code": 0, "seconds": time.time() - start, "timed_out": False}
    if runner == "reference":
        shutil.copytree(os.path.join(EVAL, "tasks", task, "reference"), os.path.join(session_dir, "work"), dirs_exist_ok=True)
        return {"code": 0, "seconds": time.time() - start, "timed_out": False}
    try:
        proc = subprocess.run(shlex.split(runner) + [session_dir], cwd=session_dir, timeout=RUNNER_TIMEOUT_S,
                              capture_output=True, text=True)
        return {"code": proc.returncode, "seconds": time.time() - start, "timed_out": False}
    except subprocess.TimeoutExpired:
        return {"code": None, "seconds": time.time() - start, "timed_out": True}

def load_manifest(out):
    path = os.path.join(out, "manifest.json")
    if not os.path.exists(path): raise ValueError(f"{out} is not prepared: no manifest.json")
    return json.loads(S.read(path))

def run_phase(out):
    """Call the runner once per session, in manifest order, and write each session's `runner-exit`. Refuses an
    `out` that has already been scored."""
    manifest = load_manifest(out)
    if os.path.exists(os.path.join(out, "rows.jsonl")):
        raise ValueError(f"{out} has already been scored: run refuses to run out of order")
    for session in manifest["sessions"]:
        session_dir = os.path.join(out, "sessions", session["id"])
        result = call_runner(manifest["runner"], session_dir, session["task"])
        with open(os.path.join(session_dir, "runner-exit"), "w", encoding="utf-8") as f: f.write(S.canonical_json(result))
    return manifest

# ---- score ------------------------------------------------------------------------------------------------------

def score_phase(out):
    """Score every session's `work/` (and, when `runner-exit` shows it was run, its `record.json` if one was
    recorded), and write `OUT/rows.jsonl`, one canonical row per session in session-id order. Refuses an `out`
    where some session has not been run."""
    manifest = load_manifest(out)
    for session in manifest["sessions"]:
        if not os.path.exists(os.path.join(out, "sessions", session["id"], "runner-exit")):
            raise ValueError(f"{out} has not been run: session {session['id']} has no runner-exit")
    arm_map = json.loads(S.read(os.path.join(out, "arms.sealed.json")))
    binding_sha = manifest["binding"]["sha256"]
    rows = []
    for session in sorted(manifest["sessions"], key=lambda s: s["id"]):
        sid, task = session["id"], session["task"]
        session_dir = os.path.join(out, "sessions", sid)
        work_dir = os.path.join(session_dir, "work")
        result = EV.score(task, work_dir)
        record_result = {"present": False, "defects": [], "unchecked": []}
        record_path = os.path.join(work_dir, "record.json")
        if os.path.exists(record_path):
            with open(record_path, "rb") as f: record_bytes = f.read()
            defects, unchecked = R.judge(record_bytes, R.reader(work_dir))
            record_result = {"present": True, "defects": defects, "unchecked": unchecked}
        exit_data = json.loads(S.read(os.path.join(session_dir, "runner-exit")))
        runner_json_path = os.path.join(session_dir, "runner.json")
        runner_json = json.loads(S.read(runner_json_path)) if os.path.exists(runner_json_path) else None
        rows.append({"session": sid, "task": task, "module": session["module"], "arm": arm_map[sid],
                     "object": manifest["object"], "questions": manifest["questions"],
                     "questions_override": manifest["questions_override"], "binding": binding_sha,
                     "functional": result["functional"], "checks": result["checks"], "held": result["held"],
                     "of": result["of"],
                     "record": record_result,
                     "runner": {"exit": exit_data["code"], "seconds": exit_data["seconds"],
                                "timed_out": exit_data["timed_out"], "json": runner_json}})
    with open(os.path.join(out, "rows.jsonl"), "w", encoding="utf-8") as f:
        for row in rows: f.write(canonical_line(row))
    print_table(rows)
    return rows

def print_table(rows):
    """One line per arm x task: the mean `held` of `of`, and how many sessions passed the functional test."""
    groups = {}
    for row in rows: groups.setdefault((row["arm"], row["task"]), []).append(row)
    for arm, task in sorted(groups):
        group = groups[(arm, task)]
        mean_held = sum(r["held"] for r in group) / len(group)
        passed = sum(1 for r in group if r["functional"])
        print(f"{arm:10} {task:26} held {mean_held:.2f}/{group[0]['of']}  functional {passed}/{len(group)}")

# ---- CLI ------------------------------------------------------------------------------------------------------

def parse_flags(argv):
    modules = take(argv, "--modules") or []
    arms = take(argv, "--arms") or list(ARMS)
    runner = (take(argv, "--runner") or ["identity"])[0]
    repeat = int((take(argv, "--repeat") or ["1"])[0])
    binding = (take(argv, "--binding") or [os.path.join(EVAL, "binding.md")])[0]
    questions = take(argv, "--questions"); questions = questions[0] if questions else None
    seed = int((take(argv, "--seed") or ["0"])[0])
    record = "--no-record" not in argv
    return modules, arms, runner, repeat, binding, questions, seed, record

def main(argv):
    if not argv: print(__doc__); return 2
    phase, rest = (argv[0], argv[1:]) if argv[0] in ("prepare", "run", "score") else ("all", argv)
    if not rest: print(__doc__); return 2
    out, flags = rest[0], rest[1:]
    try:
        if phase in ("all", "prepare"):
            prepare(out, *parse_flags(flags))
            print(f"eval: prepared {out}")
        if phase in ("all", "run"):
            run_phase(out)
            print(f"eval: ran {out}")
        if phase in ("all", "score"):
            score_phase(out)
            print(f"eval: scored {out}")
    except ValueError as error:
        print(f"eval: {error}"); return 2
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
