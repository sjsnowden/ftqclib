<!-- binding
title: Eval fixture
object: .
object-manifest: fixture; the rig generates the brief from the object it vendors and records that object's hash
modules: python
brief: eval/brief.generated.md
-->

# Eval fixture binding

A binding with no repository behind it, so the brief the "brief" arm loads is the object's own text and the Python
module and nothing else. A rig generates the brief with `standard.py brief eval/binding.md` and gives the agent that
file as `CLAUDE.md`'s import. There are no requirements here: what is measured is the standard, not a repository.
