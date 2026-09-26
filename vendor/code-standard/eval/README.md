# eval — the model-free half of measuring the brief

Does a session that loads the brief write different code from one that does not, in the direction the standard says?
Answering that needs a model, a harness and a rig, none of which this object has or wants (it knows only itself). What
the object can carry is what conformance looks like and how a breach is seen (STANDARD.md 4.5): the tasks, the seeds
with their planted faults, the hidden functional tests, and the scorers. A repository that records agent runs
(OntolMeta, `evals/`) supplies the arms, the models, the efforts and the runs, and applies these scorers to the
recorded final state of each run, so every score can be re-derived from a run directory.

| Path | What it is |
|---|---|
| `tasks/LANG/NN-name/task.txt` | the text the agent is given; it states the interface the hidden test drives |
| `tasks/LANG/NN-name/task.json` | canonical: the task's `checks` (each an `args`, `clause`, `judge`, `name`), its `module`, its `mutants` and `planted` checks (for `controls.py`), and its `test` command |
| `tasks/LANG/NN-name/seed/` | the starting repository the agent sees, with faults planted so the standard bites |
| `tasks/LANG/NN-name/reference/` | one conforming solution: the control that must score full marks |
| `tasks/LANG/NN-name/tests/test.py` | the hidden functional test, run against a tree by the scorer; never in the seed |
| `judges/LANG.py` | the AST helpers and the judges (`NAME(tree, **args) -> bool`) a task's `task.json` names by module and function |
| `score.py` | task-agnostic: `tasks()` lists task ids, `score(TASK, TREE)` runs the task's test and its named checks, as JSON; pure in the tree |
| `controls.py` | a loop over `tasks()`: every check shown to fail on the seed or on the task's mutants, and to hold on the reference; plus the one control with no task, that a `task.json` naming a judge its module lacks is refused |
| `binding.md` | a fixture binding (module python) from which `standard.py eval` generates the brief for the "brief" arm |
| `placebo.md` | about 3,000 words of neutral prose (how tides arise), no lists, no code, no instructions; cut to the "brief" arm's word count for the "placebo" arm, so a repository can tell a real effect from the effect of reading anything at all |

A check is a static reading of the tree (the `ast` module), named for the requirement it serves, and it is a
heuristic: an agent may conform by an idiom the check did not anticipate. When that happens the check is revised
here and the run is re-scored; the score is never edited. The functional test is the ground truth for behaviour.

A language is added with a judges module (`judges/LANG.py`) and task directories (`tasks/LANG/NN-name/`) — nothing
else in `score.py` or `controls.py` names a language.

`score.py score TASK TREE` refuses, with a message and exit 2, a task whose `task.json` is not canonical, names a
judge its module lacks, or names a clause that is not a requirement of the standard (or one of its model clauses
4.1-4.8).

Run `python3 eval/controls.py`; `tests/controls.py` runs it too.

## Running an eval: `standard.py eval`

`tools/evaluate.py`, dispatched from `standard.py eval`, drives the tasks above through four arms — what a session's
`CLAUDE.md` gives it before it starts: `none` (nothing), `placebo` (`placebo.md`, cut to the same length in words as
that run's brief, to separate the effect of the standard from the effect of reading anything at all), `brief` (the
brief generated from `--binding`, default `binding.md`, with its `modules:` header replaced by `--modules`), and
`questions` (`standard.py questions text`). It has three phases, each callable alone (`standard.py eval PHASE OUT
...`) or in sequence (`standard.py eval OUT --modules M... [--arms A...] [--runner R] [--repeat N] [--binding P]
[--questions P] [--seed N] [--no-record]`):

- **prepare** picks every task whose module is in `--modules`, and for each task x arm x repeat writes a session
  under `OUT/sessions/<id>/` (`<id>` eight hex digits drawn from `random.Random(--seed)`): `work/` is the task's
  `seed/`, plus `work/CLAUDE.md` for the arm (`none` gets none); `task.txt` is the task's text, plus the paragraph
  `standard.py questions task` appends (unless `--no-record`); `work/record.schema.json` is `standard.py questions
  schema` (unless `--no-record`). Nothing under `OUT/sessions/` names a session's arm: the mapping is written
  separately, to `OUT/arms.sealed.json` (`{session_id: arm}`, mode 0600), read only by `score`. `OUT/manifest.json`
  (canonical) records `object`, `questions` and `questions_override`, `binding`, `modules`, `arms`, `tasks`,
  `repeat`, `runner`, `seed`, `record`, and the sessions in shuffled order — no timestamps.
- **run** calls the runner once per session, in manifest order, as `CMD SESSION_DIR` with cwd `SESSION_DIR`, under
  a deadline of `ONTOL_EVAL_RUNNER_TIMEOUT_S` seconds (default 1800). The built-in runners `identity` (does
  nothing) and `reference` (copies the task's `reference/` over `work/`) need no process. A runner may write its
  own `SESSION_DIR/runner.json`; `run` leaves it alone. After every call, `run` writes `SESSION_DIR/runner-exit`
  (canonical: `code`, `seconds`, `timed_out`) whatever the exit code was — a non-zero exit or a timeout is recorded,
  never raised. `run` refuses an `OUT` that has already been scored.
- **score** refuses an `OUT` where some session has no `runner-exit`. It scores every session's `work/` with
  `eval/score.py`'s `score()`, and, when `work/record.json` exists, `tools/record.py`'s `judge()` against it; then
  writes `OUT/rows.jsonl`, one canonical single-line JSON object per session in session-id order, with exactly
  these fields: `session, task, module, arm, object, questions, questions_override, binding, functional, checks,
  held, of, record {present, defects, unchecked}, runner {exit, seconds, timed_out, json}` — no timestamps, no
  absolute paths. Scoring the same `OUT` twice yields identical bytes. It also prints a table, one line per arm x
  task, of the mean `held` of `of` and how many sessions passed the functional test.

A task may carry `idioms/<name>/`, further conforming solutions found in runs; the controls require each to pass the
test and hold every check, so a check that knew only the reference's spelling is caught the next time it runs.

Before a row is spent, run the cold pilot: `standard.py eval OUT --modules M --arms none --repeat 1 --runner R`. It
is the control the object cannot run itself: what the model does unprompted is what the checks must be aimed at, a
task whose hidden test fails every cold session has a text that does not state its interface, and a check that
fails every cold session for an idiom the reference did not use is measuring spelling. Eval 001's pilot found one
of each in fifteen sessions.
