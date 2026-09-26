<!-- binding
title: ftqclib coding standard
object: vendor/code-standard
object-manifest: 6be6138813f25c111cc3c7b4fb8837631c0f4fd4971b8b039317bb52cffb04c6
modules: lean shell documents
brief: docs/CODE-STYLE.brief.md
meaning: README.md 5fd5ff3f3e95dc62efdacf92aded9e661d02a625fd76023d06fa561d35cac847
-->

# ftqclib coding standard

This is the binding (STANDARD.md clause 12): what the standard's words mean in this repository, which of its rules are
checked here, and the rules this repository adds. The brief is generated from the object and this file; regenerate it
after editing (`vendor/code-standard/tools/standard.py brief docs/CODE-STYLE.md --write`). Nothing is enforced until
`vendor/code-standard/tools/standard.py check docs/CODE-STYLE.md` is added to a hook; until then the brief is advice.

## 1. What this repository is

<!-- One paragraph: what is built here, and the one safety property that comes before every other rule. -->

## 2. State, kinds of code and coordination

<!-- Where the state lives; which code observes, records, derives and acts (4.2); where coordination happens (4.6). -->

<!-- brief: before: Here (ftqclib) -->
- This repository has not yet written down its state, its kinds of code and where it coordinates; until it does,
  the standard's general rules apply unqualified.
<!-- /brief -->

## 3. Meaning

<!-- The documents that give code its meaning (4.4), named in the header with their hashes, and what each covers. -->

## 4. Requirements of this repository

<!-- Each as **XX.n Title.** with a reading line, like the standard's own:
**XX.1 Title.** The rule, in one or two sentences.
> *Means* — what it refers to. *Governs* — the axis. *CALM* — how. *Checked by* — the check, or "advice". *Brief* — the one-line form for the brief.
-->

## 5. Checks

<!-- Which rules are checked, by what, and where the check runs. Everything else is advice. -->

## 6. Language notes

<!-- What the modules' notes mean here: toolchains, targets, exceptions with their reasons. -->

## 7. Open questions

<!-- Where the standard's words do not fit this repository, written down rather than settled by habit. -->
