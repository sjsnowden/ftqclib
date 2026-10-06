"""Owner-side F01/F02 projections and protected source admission, with no compiler or model execution.

Preparation copies tracked pinned inputs, then changes only the declared task window. Assessment never trusts
worker build products. Formal acceptance requires owner receipts naming captured source and exact commands.
"""
import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tarfile

REVISION = "75589c95949b6d290c53405e0cdc31334120e19a"
ROOT = Path(__file__).resolve().parents[1]
Z_SHEAR = "FTQCLib/Stabilizer/ZShear.lean"
PAIRING = "FTQCLib/Carrier/CharSumPairing.lean"
RESIDUAL = "FTQCLib/Carrier/ResidualBit.lean"
AMPLITUDE = "FTQCLib/Carrier/HadamardAmplitudeCheck.lean"
F01_HEADER = ("theorem zShearBy_zShearBy (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : Pauli n) :\n"
              "    zShearBy M (zShearBy M p) = p := ").encode()
F01_END = b"\n\n/-- The shear as a linear equivalence. -/\nnoncomputable def zShearByEquiv"
SIGNS = ("/-- `signOf 0 = 1`. -/\ntheorem signOf_zero : signOf 0 = 1 := if_pos rfl\n\n"
         "/-- `signOf 1 = −1`. -/\ntheorem signOf_one : signOf 1 = -1 := if_neg one_ne_zero\n\n").encode()
SIGN_ALTERNATE = ("/-- The Walsh sign at a set bit. -/\n"
                  "theorem signOf_one : signOf (1 : ZMod 2) = -1 := by\n"
                  "  unfold signOf\n  rw [if_neg (by decide)]\n\n").encode()
RESIDUAL_MARK = "/-- **The `e_k` pairing.**".encode()
AMPLITUDE_MARK = "/-- The referee on the Bell input at `11`:".encode()
ALTERNATE_PROOF = ("by\n  have h2 : ∀ a b : ZMod 2, a + b + b = a := by decide\n"
                   "  ext i\n  · rfl\n  · simp only [zShearBy_Z, zShearBy_X, Pi.add_apply]\n"
                   "    exact h2 _ _").encode()
UNSTABLE_PROOF = ("by\n  ext i\n  · rfl\n  · simp only [zShearBy_Z, zShearBy_X, Pi.add_apply]\n"
                  "    have h2 : (2 : ZMod 2) = 0 := by decide\n    ring_nf\n    simp [h2]").encode()
FORBIDDEN = frozenset("axiom constant def opaque instance inductive structure namespace end section import "
                      "set_option attribute syntax macro elab initialize run_cmd run_tac unsafe partial extern "
                      "implemented_by native_decide example theorem abbrev export include omit mutual "
                      "open variable universe universes local scoped notation class noncomputable protected private "
                      "prefix postfix infix infixl infixr declare_syntax_cat register_option register_builtin_option "
                      "builtin_initialize deriving extends where elab_rules macro_rules run_elab".split())
IGNORED = frozenset({".git", ".lake", ".scratch", "evals", "CLAUDE.md", "AGENTS.md"})
FILES_MAX, FILE_BYTES_MAX, TREE_BYTES_MAX = 10000, 16 * 1024 * 1024, 256 * 1024 * 1024


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def task_spec(task):
    if task not in ("F01", "F02"):
        raise ValueError("unknown fixture task")
    return json.loads((ROOT / "evals/tasks" / task / "contract.json").read_bytes())


def check_commands(task):
    """Exact owner commands; the caller supplies one private output tree and controlled Lean environment."""
    specification = task_spec(task)
    examiner = str(ROOT / specification["examiner"])
    return [{"id": check["id"], "command": [examiner if word == "{examiner}" else word
                                             for word in check["command"]]}
            for check in specification["checks"]]


def dependent_modules(task, files):
    """Topological changed-module closure needed by the named consumers, never reused as cached oleans."""
    targets = (["FTQCLib.Stabilizer.ZShearCheck"] if task == "F01" else
               ["FTQCLib.Carrier.ResidualBit", "FTQCLib.Carrier.HadamardAmplitudeCheck"])
    changed = ({"FTQCLib.Stabilizer.ZShear"} if task == "F01" else
               {name[:-5].replace("/", ".") for name in (PAIRING, RESIDUAL, AMPLITUDE)})
    state, ordered, dependencies = {}, [], {}

    def visit(module, depth):
        if depth > 64:
            raise ValueError("module import depth exceeds fixture bound")
        if state.get(module) == "done":
            return
        if state.get(module) == "visiting":
            raise ValueError("source import cycle")
        path = module.replace(".", "/") + ".lean"
        if path not in files:
            return
        state[module] = "visiting"
        imports = re.findall(r"(?m)^import ([A-Za-z0-9_.]+)", files[path].decode("utf-8"))
        dependencies[module] = imports
        for dependency in imports:
            visit(dependency, depth + 1)
        ordered.append(module)
        state[module] = "done"

    for target in targets:
        visit(target, 0)
    affected = set(changed)
    found = []
    for module in ordered:
        if module in affected or any(dependency in affected for dependency in dependencies[module]):
            affected.add(module)
            found.append(module)
    return found


def excluded_modules(task, files):
    """Every local descendant artifact can carry withheld declarations; none is a permitted cache input."""
    affected = ({"FTQCLib.Stabilizer.ZShear"} if task == "F01" else
                {name[:-5].replace("/", ".") for name in (PAIRING, RESIDUAL, AMPLITUDE)})
    imports = {name[:-5].replace("/", "."): re.findall(r"(?m)^import ([A-Za-z0-9_.]+)", data.decode("utf-8"))
               for name, data in files.items() if name.endswith(".lean")}
    for _ in range(len(imports) + 1):
        found = affected | {module for module, dependencies in imports.items()
                            if any(dependency in affected for dependency in dependencies)}
        if found == affected:
            return sorted(found)
        affected = found
    raise ValueError("source import closure did not stabilize")


def tracked_files(source):
    """Observe Git identities and tracked bytes; untracked examiner code is never projected."""
    options = {"cwd": source, "capture_output": True, "timeout": 30, "check": False}
    command = git_command(source)
    revision = subprocess.run(command + ["rev-parse", "HEAD"], **options)
    if revision.returncode or revision.stdout.decode("ascii").strip() != REVISION:
        raise ValueError("fixture source must be at the pinned revision")
    changed = subprocess.run(command + ["diff", "--quiet", "HEAD", "--"], **options)
    if changed.returncode:
        raise ValueError("tracked source changes must be captured as another reviewed baseline")
    listed = subprocess.run(command + ["ls-files", "-z"], **options)
    if listed.returncode:
        raise ValueError("cannot enumerate tracked source")
    names = [name.decode("utf-8") for name in listed.stdout.split(b"\0") if name]
    if len(names) > FILES_MAX:
        raise ValueError("source file count exceeds fixture bound")
    archived = subprocess.run(command + ["archive", "--format=tar", "HEAD"], **options)
    if archived.returncode or len(archived.stdout) > TREE_BYTES_MAX:
        raise ValueError("cannot capture bounded pinned Git source")
    found = {}
    with tarfile.open(fileobj=io.BytesIO(archived.stdout), mode="r:") as archive:
        for member in archive:
            relative = Path(member.name)
            if IGNORED.intersection(relative.parts) or member.isdir():
                continue
            if (not member.isfile() or member.size > FILE_BYTES_MAX or relative.is_absolute()
                    or ".." in relative.parts):
                raise ValueError("Git projection must contain bounded regular files")
            found[relative.as_posix()] = archive.extractfile(member).read()
    return found


def git_command(source):
    """WSL may read a Windows-created worktree pointer; use only the Git directory it explicitly names."""
    pointer = source / ".git"
    if os.name == "posix" and pointer.is_file():
        text = pointer.read_text(encoding="utf-8").strip()
        match = re.fullmatch(r"gitdir: ([A-Za-z]):[\\/](.+)", text)
        if match:
            directory = "/mnt/" + match[1].lower() + "/" + match[2].replace("\\", "/")
            return ["git", "-c", "core.autocrlf=true", "--git-dir", directory, "--work-tree", str(source)]
    return ["git"]


def read_files(source, names):
    found, total = {}, 0
    for name in sorted(names):
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("source path escapes its declared root")
        if IGNORED.intersection(relative.parts):
            continue
        path = source / relative
        if path.is_symlink() or not stat.S_ISREG(path.stat().st_mode):
            raise ValueError("fixture input must be a regular file: " + name)
        if path.stat().st_size > FILE_BYTES_MAX:
            raise ValueError("fixture input exceeds byte bound: " + name)
        data = path.read_bytes()
        total += len(data)
        if total > TREE_BYTES_MAX:
            raise ValueError("fixture tree exceeds byte bound")
        found[relative.as_posix()] = data
    return found


def tree_files(source):
    names = []
    visited = 0
    for directory, children, files in os.walk(source, followlinks=False):
        children[:] = [name for name in children if name not in IGNORED]
        for name in children + files:
            if name in IGNORED:
                continue
            path = Path(directory) / name
            visited += 1
            if visited > FILES_MAX:
                raise ValueError("candidate path count exceeds fixture bound")
            if path.is_symlink():
                raise ValueError("candidate contains a symbolic link")
            if name in files:
                names.append(path.relative_to(source).as_posix())
    return read_files(source, names)


def tree_digest(files):
    manifest = {name: sha256(data) for name, data in sorted(files.items())}
    return sha256(json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode())


def with_eol(data, source):
    """New edit bytes use the pinned module's line ending; protected surrounding bytes remain untouched."""
    data = data.replace(b"\r\n", b"\n")
    return data.replace(b"\n", b"\r\n") if b"\r\n" in source else data


def f01_window(data):
    """The fixed source anchor binds the reviewed statement, proof boundary and next declaration."""
    header, ending = with_eol(F01_HEADER, data), with_eol(F01_END, data)
    if data.count(header) != 1 or data.count(ending) != 1:
        raise ValueError("F01 reviewed declaration boundary does not match")
    start = data.index(header) + len(header)
    stop = data.index(ending, start)
    return data[:start], data[start:stop], data[stop:]


def f02_windows(files):
    signs = with_eol(SIGNS, files[PAIRING])
    if files[PAIRING].count(signs) != 1:
        raise ValueError("F02 shared declaration block does not match")
    start = files[PAIRING].index(signs)
    found = {PAIRING: (files[PAIRING][:start], signs, files[PAIRING][start + len(signs):])}
    for name, marker in ((RESIDUAL, RESIDUAL_MARK), (AMPLITUDE, AMPLITUDE_MARK)):
        if files[name].count(marker) != 1:
            raise ValueError("F02 consumer insertion boundary does not match")
        start = files[name].index(marker)
        found[name] = files[name][:start], b"", files[name][start:]
    return found


def overlay(task, files, control):
    """Pure reviewed seeds and controls. Compiler validity of each is a separate observation."""
    found = dict(files)
    if task == "F01":
        prefix, original, suffix = f01_window(files[Z_SHEAR])
        bodies = {"seed": b"by\n  sorry", "reference": original, "alternate": ALTERNATE_PROOF,
                  "unfinished": b"by\n  sorry",
                  "unstable-simp": UNSTABLE_PROOF}
        if control == "weakened-statement":
            found[Z_SHEAR] = prefix.replace(b"= p := ", b"= zShearBy M (zShearBy M p) := ") + b"by\n  rfl" + suffix
        elif control == "changed-definition":
            found[Z_SHEAR] = prefix.replace(b"p.Z + M p.X", b"p.Z") + original + suffix
        elif control == "added-axiom":
            prefix = prefix.replace(with_eol(F01_HEADER, prefix),
                                    with_eol(b"axiom injected : False\n\n" + F01_HEADER, prefix))
            found[Z_SHEAR] = prefix + with_eol(b"by\n  exact False.elim injected", prefix) + suffix
        elif control in bodies:
            found[Z_SHEAR] = prefix + with_eol(bodies[control], prefix) + suffix
        else:
            raise ValueError("unknown F01 control")
        return found
    windows = f02_windows(files)
    replacements = {"seed": {PAIRING: b"", RESIDUAL: SIGNS, AMPLITUDE: SIGN_ALTERNATE},
                    "reference": {PAIRING: SIGNS, RESIDUAL: b"", AMPLITUDE: b""},
                    "alternate": {PAIRING: SIGNS.replace(b"theorem signOf_one : signOf 1 = -1 := if_neg one_ne_zero\n\n",
                                                         SIGN_ALTERNATE.split(b"-/\n", 1)[1]),
                                  RESIDUAL: b"", AMPLITUDE: b""}}
    if control in ("module-deletion", "omitted-import"):
        found = overlay(task, files, "reference")
        if control == "module-deletion":
            del found[AMPLITUDE]
        else:
            found[AMPLITUDE] = found[AMPLITUDE].replace(
                with_eol(b"import FTQCLib.Carrier.HadamardAmplitude\n", found[AMPLITUDE]), b"")
        return found
    if control not in replacements:
        raise ValueError("unknown F02 control")
    for name, (prefix, _, suffix) in windows.items():
        found[name] = prefix + with_eol(replacements[control][name], files[name]) + suffix
    return found


def prepare(task, source, destination, *, control="seed"):
    """Materialize one neutral, fresh source projection; failed preparation never reports ready."""
    try:
        source, destination = Path(source).resolve(), Path(destination).resolve()
        specification = task_spec(task)
        files = overlay(task, tracked_files(source), control)
        metadata = {"checks": check_commands(task), "excluded_modules": excluded_modules(task, files),
                    "examiner_sha256": sha256((ROOT / specification["examiner"]).read_bytes()),
                    "fixture_sha256": sha256(Path(__file__).read_bytes()),
                    "contract_sha256": sha256((ROOT / "evals/tasks" / task / "contract.json").read_bytes())}
        if destination.exists() or destination == source or source in destination.parents:
            raise ValueError("destination must be a fresh directory outside the source tree")
    except (OSError, ValueError, TypeError, KeyError, tarfile.TarError, subprocess.SubprocessError) as error:
        return {"status": "refused", "phase": "read", "reason": str(error)}
    try:
        destination.mkdir(parents=True, exist_ok=False)
        for name, data in files.items():
            path = destination / name
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("xb") as handle:
                handle.write(data)
    except OSError as error:
        return {"status": "failed", "phase": "write", "reason": str(error), "destination": str(destination)}
    return {"status": "prepared", "task": task, "control": control, "source_revision": REVISION,
            "source_sha256": tree_digest(files), "destination": str(destination), "contract": specification,
            **metadata, "formal": "unverified"}


def code_without_comments(text, *, proof_subset=False):
    """Mask comments/strings with spaces; optional proof admission refuses embedded string expressions.

    Generic source/import scanning does not impose the editable proof subset's style restrictions.
    Both modes preserve token boundaries and line/column positions.
    """
    result, index, depth, quoted = list(text), 0, 0, False

    def mask(start, stop):
        for position in range(start, min(stop, len(text))):
            if text[position] not in "\r\n":
                result[position] = " "

    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                mask(index, index + 2)
                index += 2
            elif pair == "-/":
                depth -= 1
                mask(index, index + 2)
                index += 2
            else:
                mask(index, index + 1)
                index += 1
        elif quoted:
            if text[index] == "\\":
                mask(index, index + 2)
                index += 2
            elif proof_subset and text[index] == "{":
                raise ValueError("simp stability: brace-bearing strings are outside the supported proof subset")
            elif text[index] == '"':
                quoted = False
                mask(index, index + 1)
                index += 1
            else:
                mask(index, index + 1)
                index += 1
        elif text[index] == "«":
            stop = text.find("»", index + 1)
            if stop < 0:
                raise ValueError("unfinished escaped identifier in edit window")
            index = stop + 1
        elif pair == "/-":
            mask(index, index + 2)
            depth, index = 1, index + 2
        elif pair == "--":
            newline = text.find("\n", index)
            stop = len(text) if newline < 0 else newline
            mask(index, stop)
            index = stop
        elif (text[index] == "'" and (index == 0 or not (text[index - 1].isalnum()
                                                       or text[index - 1] in "_'?!»"))
              and (character := re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|u[0-9a-fA-F]{4}|.)|[^'\\\r\n])'",
                                          text[index:]))):
            stop = index + len(character[0])
            mask(index, stop)
            index = stop
        elif text[index] == '"':
            previous = index - 1
            while previous >= 0 and result[previous].isspace():
                previous -= 1
            if proof_subset and previous >= 0 and result[previous] == "!":
                raise ValueError("simp stability: interpolated strings are outside the supported proof subset")
            mask(index, index + 1)
            quoted, index = True, index + 1
        else:
            index += 1
    if depth or quoted:
        raise ValueError("unfinished comment or string in edit window")
    return "".join(result)


def simp_stability(code):
    """Small LN.4 admission subset, not Lean parsing: simp/simpa/simp_all/dsimp require only.

    Whitespace/comments and ?/! modifiers are supported before only; configurations and dischargers
    before only are refused. Ordinary lists, locations and using terms after only remain compiler checked.
    Interpolated/brace-bearing strings are refused rather than masking embedded Lean terms as prose.
    Qualified, escaped and longer identifiers are not tactic names. Shadowing an unqualified tactic name
    is outside this conservative subset. dsimp also uses ambient simp declarations unless only is present.
    """
    # Keep dotted names and Lean escaped identifiers whole; Unicode letters/apostrophes are identifier parts.
    # Lean's letter-like/subscript ranges include symbols outside Python's Unicode word category.
    extra = r"\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    first = r"(?:[^\W\d]|[_" + extra + r"])"
    rest = r"[\w'?!\u2080-\u209c\u1d62-\u1d6a\u2c7c" + extra + r"]*"
    part = r"(?:«[^»]*»|" + first + rest + r")"
    tokens = re.findall(part + r"(?:\." + part + r")*|[^\s]", code, flags=re.UNICODE)
    for index, token in enumerate(tokens):
        tactic = re.fullmatch(r"(simp|simpa|simp_all|dsimp)[?!]*", token)
        if not tactic:
            continue
        following = index + 1
        while following < len(tokens) and tokens[following] in ("?", "!"):
            following += 1
        if following == len(tokens) or tokens[following] != "only":
            return ("simp stability: " + tactic[1] + " requires explicit only immediately after optional ?/! "
                    "modifiers; config/discharger prefixes are outside the supported proof subset")
    return None


def admitted_window(task, edited):
    try:
        code = code_without_comments(edited.decode("utf-8"), proof_subset=True)
    except ValueError as error:
        return str(error)
    if task == "F01":
        lines = [line for line in code.splitlines() if line.strip()]
        if not lines or lines[0].split()[0] != "by":
            return "F01 requires a tactic proof in the existing by boundary"
        if any(line == line.lstrip() for line in lines[1:]):
            return "F01 proof escapes its indented top-level body boundary"
    if task == "F02":
        code = re.sub(r"\btheorem\s+signOf_(?:zero|one)\b", "", code)
    tokens = set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*", code))
    if tokens.intersection(FORBIDDEN) or "#" in code or "@[" in code:
        return "edit contains a declaration or command outside the permitted proof/sign lemmas"
    return simp_stability(code)


def f02_ownership(windows, candidate):
    """Cheap source refusal; the protected Lean examiner independently audits pre-merge module data."""
    sites = {"signOf_zero": [], "signOf_one": []}
    for path, (prefix, _, suffix) in windows.items():
        edited = candidate[path][len(prefix):len(candidate[path]) - len(suffix)]
        code = code_without_comments(edited.decode("utf-8"))
        for name in re.findall(r"\btheorem\s+(signOf_zero|signOf_one)\b", code):
            sites[name].append(path)
    reasons = []
    for name, homes in sites.items():
        if homes != [PAIRING]:
            observed = ", ".join(homes) if homes else "none"
            reasons.append(f"F02 declaration home: {name} must have exactly one declaration site in "
                           f"{PAIRING}; observed {observed}")
    return reasons


def admission(task, baseline, candidate):
    if task not in ("F01", "F02"):
        raise ValueError("unknown fixture task")
    if set(baseline) != set(candidate):
        return ["candidate adds or removes protected source files"]
    windows = ({Z_SHEAR: f01_window(baseline[Z_SHEAR])} if task == "F01" else f02_windows(baseline))
    reasons = []
    for name in sorted(baseline):
        if name not in windows:
            if baseline[name] != candidate[name]:
                reasons.append("protected source changed: " + name)
            continue
        prefix, _, suffix = windows[name]
        data = candidate[name]
        if not data.startswith(prefix) or not data.endswith(suffix) or len(data) < len(prefix) + len(suffix):
            reasons.append("protected statement or edit boundary changed: " + name)
            continue
        why = admitted_window(task, data[len(prefix):len(data) - len(suffix)])
        if why:
            reasons.append(name + ": " + why)
    if task == "F02" and not reasons:
        reasons.extend(f02_ownership(windows, candidate))
    return reasons


def assess(task, baseline, candidate, *, compiler_results=None):
    """Source admission and recorded owner checks. Missing, stale or failed compiler evidence never passes."""
    try:
        specification = task_spec(task)
        original, proposed = tree_files(Path(baseline)), tree_files(Path(candidate))
        reasons = admission(task, original, proposed)
        identity = tree_digest(proposed)
        producer = {"fixture_sha256": sha256(Path(__file__).read_bytes()),
                    "examiner_sha256": sha256((ROOT / specification["examiner"]).read_bytes()),
                    "contract_sha256": sha256((ROOT / "evals/tasks" / task / "contract.json").read_bytes())}
    except (OSError, ValueError, TypeError, KeyError) as error:
        return {"status": "refused", "phase": "read", "reason": str(error), "accepted": False}
    result = {"task": task, "source_sha256": identity, "baseline_sha256": tree_digest(original),
              "admitted": not reasons, "reasons": reasons, "accepted": False, "formal": "unverified", **producer}
    if reasons:
        return {**result, "status": "refused"}
    if compiler_results is None:
        return {**result, "status": "needs-checks"}
    if not isinstance(compiler_results, dict):
        return {**result, "status": "needs-checks", "reason": "owner receipts must be a mapping"}
    for check in check_commands(task):
        receipt = compiler_results.get(check["id"], {})
        if not isinstance(receipt, dict) or type(receipt.get("returncode")) is not int:
            return {**result, "status": "needs-checks", "reason": "invalid owner check: " + check["id"]}
        if receipt.get("source_sha256") != identity or receipt.get("command") != check["command"]:
            return {**result, "status": "needs-checks", "reason": "missing or stale owner check: " + check["id"]}
        if receipt.get("status") != "finished":
            return {**result, "status": "needs-checks", "reason": "unfinished owner check: " + check["id"]}
        if receipt.get("returncode") != 0:
            return {**result, "status": "failed", "formal": "failed", "reason": "owner check failed: " + check["id"]}
    return {**result, "status": "accepted", "accepted": True, "formal": "passed"}
