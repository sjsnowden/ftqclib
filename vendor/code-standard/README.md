# code-standard

A coding standard packaged as one object, for use in any repository. Its identity is the SHA-256 of `MANIFEST`.

| Member | What it is |
|---|---|
| `STANDARD.md` | the standard: terms with their sources, the model, the requirements every repository keeps |
| `modules/` | parts a repository opts into: `record-keeping` (state that only accumulates), one per language (`python`, `rust`, `shell`, `lean`: Lean 4 against Mathlib, proofs and running code), and one per machine (`x86-64`, `apple-arm64`, `risc-v`: the price list, idioms, traps and questions of that ISA, with sources pinned), and `documents` (which of the two document styles a document uses, and their rules) |
| `documents/` | the two document styles: `STYLE.html` for engineering reports and other documents for the team, `STYLE-PUBLIC.html` for papers, public pages and other documents for readers outside; each a specimen whose head is copied whole into a document. `build/` holds the script that generates `STYLE-PUBLIC.html` |
| `sources/INDEX.md` | every source by key, address, fragment and SHA-256; the bytes are not here |
| `questions.json` | the six axes' questions (STANDARD.md Annex C, 12.5): id, group, clause, form, arity, question, reason, where |
| `tools/record.py` | the record judge (13.7): whether a written record answers `questions.json`'s questions with referents that exist |
| `tools/evaluate.py` | the `eval` verb: prepares, runs and scores an eval run under four arms (`none`, `placebo`, `brief`, `questions`) |
| `tools/standard.py` | `fetch`, `manifest`, `check`, `brief`, `pin`, `questions`, `record`, `eval`; Python 3 standard library, and `pdftotext` for the quotation check |
| `tests/controls.py` | deliberate breakages that each check must catch |
| `eval/` | the model-free half of measuring the brief: tasks, seeds with planted faults, hidden tests, scorers with controls; a rig that records agent runs supplies the rest |
| `eval/judges/` | per-language AST judges: the functions a task's `task.json` names to check the tree, one module per language |
| `eval/placebo.md` | about 3,000 words of neutral prose, cut to the `brief` arm's word count for the `placebo` arm, so a run can tell a real effect from the effect of reading anything at all |
| `MANIFEST` | every member above and its SHA-256 |

## Using it in a repository

The short way: `path/to/code-standard/tools/standard.py init REPO --title "…" --modules rust shell --meaning docs/DESIGN.md`
does steps 1 to 4 below and prints the lines for `CLAUDE.md`. When this object changes, `standard.py update REPO`
replaces the vendored copy, prints which members changed, re-pins the binding and regenerates the brief.
`standard.py modules BINDING add|remove NAME...` and `standard.py meaning BINDING add|remove DOC...` edit the binding's
header for you and regenerate the brief; the header is the tool's to write, the prose is yours. Nothing is enforced until step 5 is done; until then the
brief is advice the models read.

1. Copy this directory into the repository, for example as `vendor/code-standard/`.
2. Write a binding (`STANDARD.md` clause 12.1): a document whose header names the vendored copy, its manifest hash, the
   modules used, where the brief goes, and the repository's own documents of meaning with their hashes.
3. `vendor/code-standard/tools/standard.py pin BINDING` prints the pins to copy into the header.
4. `vendor/code-standard/tools/standard.py brief BINDING --write` generates the brief. Give the brief to every session and
   agent; the full texts are read when a line is unclear.
5. `vendor/code-standard/tools/standard.py check BINDING` in the repository's pre-commit hook.

`tools/standard.py fetch` fills the source cache (`~/.cache/code-standard`, or `$CODE_STANDARD_CACHE`) from the pinned
addresses; `--from DIR` takes the bytes from a local copy instead, checking every hash either way. Without the cache the
quotation check reports that it could not run.

## Changing it

Edit, run `tools/standard.py manifest`, run `tests/controls.py`, commit. Every repository that vendors a copy then fails
its check until it reviews the change and re-pins.

## Measuring the brief

Does a session that reads the brief write different code, in the direction the standard says? `standard.py eval`
runs the object's own tasks under four arms and scores the results; see `eval/README.md` for the tasks, the judges,
the phases and the row fields.
