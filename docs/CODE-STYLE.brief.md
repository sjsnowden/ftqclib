# ftqclib coding standard — brief

Generated from object `6be6138813f25c11` (modules: lean, shell, documents) and `docs/CODE-STYLE.md` at
`56b9e3e48045eac1`. Do not edit: change the binding or the object and regenerate. Every line names its requirement; read
the full text before relying on a line you are unsure of.

## The model

- Six axes: state, transformation, effect, semantics, verification, CALM (4.1). Read every rule against them.
- Four kinds of code (4.2): **observe** what you do not control; **record** the state you persist, and nothing else
  writes it; **derive** answers from recorded state and arguments alone; **act** on the world outside. A function does
  one kind of effect, or none.
- Meaning lives in the documents the binding names; code implements it and never invents it (4.4).
- Every rule names how a breach would be seen; a rule with no check is advice (4.5).
- CALM (4.6): a conclusion is monotonic, or it depends on absence or completeness and is drawn only on a closed scope.
- Safety first: never report more than was observed; never fail silently (4.8).

## Here (ftqclib)

- This repository has not yet written down its state, its kinds of code and where it coordinates; until it does,
  the standard's general rules apply unqualified.

## Requirements: the standard

- **5.1** Never raise on anything the input's source can cause; return a value that says what could not be read, and why.
- **5.2** Names from outside are bytes end to end; text is for display, never for identity, equality or order.
- **5.3** Read only what you were pointed at; where scope is missing, skip, never widen or guess.
- **5.4** Parse outside input once, where it arrives; a refusal there is an outcome with its reason.
- **5.5** Where a guarantee can lapse, report the moment it did.
- **5.6** No handler covers both a read of the outside and a write of your own state.
- **6.1** Each piece of persisted state has one writer, and the binding says how it may change.
- **6.2** Replace a file others read atomically: write elsewhere, fsync, rename over, fsync the directory.
- **6.3** Take the clock, randomness and other nondeterminism as parameters; never reach for them.
- **6.4** If your own state cannot be written, stop, declare nothing finished, and report it.
- **6.5** A result names, by version or hash, the code that produced it.
- **7.1** A derivation reads only recorded state and arguments: no printing, writing, clock, or unnamed files.
- **7.2** Depend on content, never on file position, container order, or how a value was obtained.
- **7.3** A conclusion about absence names its scope and is drawn only when that scope is closed; otherwise decline and say why.
- **7.4** When the answer cannot be computed, say so and why; never put another answer in its place.
- **7.5** Never store what can be derived as if it were a fact; keep it only as a rebuildable view.
- **7.6** State an operation's laws beside it and test each as a property.
- **8.1** Use only the handles and paths you were given, with the least authority the task needs; never use one party's authority on another party's name.
- **8.2** Decide access by permission, not exclusion, so the unforeseen case is refused.
- **8.3** The decision to fail closed lives outside the thing that can fail.
- **8.4** Every thread and child has one owner: wait with a deadline, then kill, reap, and record what was left.
- **8.5** Declare work finished only after every task it started has ended and been reaped.
- **8.6** Every wait and subprocess has a timeout; reaching it is reported as itself, never as a crash.
- **8.7** Secrets: one reader; never in arguments, environment dumps, file names, logs or hashes; scrubbed on every path; searched for in what is kept.
- **8.8** Protection never depends on the design or the code being secret.
- **9.1** Route a failure by its source: own invariant broken, assert and stop; something depended on, stop or return an error, never a fact; something observed, a value with its reason.
- **9.2** Handle every error, and let each handler cover one source only.
- **9.3** A crash is never counted as a refusal or as an answer.
- **9.4** Outcomes and errors of dependencies go in the return type, bugs in assertions; use the simplest type that works.
- **10.1** Bound everything the code does (loops, queues, buffers, waits); recurse only under an asserted depth limit.
- **10.2** Assert preconditions, postconditions and invariants; pair them around storage; assert what must never happen; one condition per assertion.
- **10.3** Simple, explicit control flow; split compound conditions; state them positively; branch in the parent.
- **10.4** The parent holds the state and leaf functions are pure; no duplicated or aliased variables; smallest scope, close to use.
- **10.5** At most 70 lines; few parameters; library options passed explicitly; varying arguments by name; a minimum of abstractions.
- **10.6** Exact nouns and verbs; no abbreviations; units last (`latency_ms_max`); index, count and size distinct; rounding explicit.
- **10.7** Comments say why and cite the measurement; they are sentences; a test opens with its goal and method.
- **10.8** Sketch the cost before building; the slowest resource first; measure before claiming.
- **10.9** No dependency in trusted or secret-holding code without a written reason; shell only to start programs and wait.
- **10.10** Test features, not code: one `check` function, cases as data, no mocks, properties and fuzzing, nondeterminism controlled, faults planted.
- **11.1** The repository's glossary binds every program, comment and document.
- **11.2** One word, one meaning; a term this standard defines means only that.
- **11.3** Keep orientation documents short; name files rather than linking lines; write down the "X never happens" invariants; date claims, and give decisions what would overturn them.

## Requirements: module lean

- **LN.1** Lean follows Mathlib in naming, docstrings, hypotheses and simp discipline; when unsure, read Mathlib's source at the pinned revision, not memory.
- **LN.2** Review the statement apart from its proof; state it at the weakest hypotheses it needs and supply the stronger instance inside the proof.
- **LN.3** Every headline result has a build-failing axiom sweep listing only `propext`, `Classical.choice`, `Quot.sound`; anything opaque to the kernel is named with its reason and kept off a certificate's path.
- **LN.4** `simp only` where stability matters, `decide` only where seen to run, no raised limit without a written reason and an extracted lemma.
- **LN.5** A definition's home is the lowest layer that can state it; one module per object; Mathlib's docstring sections; names that read the statement.
- **LN.6** Prefer a parameter with a compatibility equation to a new instance; declare one only `scoped`, with the collision written down.
- **LN.7** Never disable a linter at file scope; fix the code it names; a per-declaration exception carries its reason.
- **LN.8** Every topic module has a check module: axiom sweep, an agreement row, discriminating rows, kernel rows or a note; mutation aimed and controlled.
- **LN.9** In Lean that runs: effects at the edge in `IO`, outcomes in `Except` never `panic!`, names as `Name` components never re-parsed text, no `partial` where a result is relied on.

## Requirements: module documents

- **DOC.1** Engineering reports, experiment write-ups, design notes and runbooks use `documents/STYLE.html`; papers, public pages and anything written for readers outside the team use `documents/STYLE-PUBLIC.html`. Choose by the reader, not the subject.
- **DOC.2** Copy the chosen style's head whole from `vendor/code-standard/documents/`; never edit a document's style block. Change the style in the object instead.
- **DOC.3** Semantic elements only, a class names a role, one file with no script, fonts or network; follow the rule in the head's comment.
- **DOC.4** In a public figure, one accent (blue-700 `#1A4F8C`) to single out one thing, or up to four pastel fills (`#92BFDB` `#F89A8A` `#F1D67E` `#BFE8D9`, in order, never outlined) to compare several; label or name every coloured mark.
- **DOC.5** Centre figures, and centre a chart on its plot area, not its labels; a caption gives the label, what the image is and where it came from.
- **DOC.6** Write public mathematics in LaTeX and compile it to MathML at build time with the pinned Temml; no images of formulas, no script, no maths font files.
- **DOC.7** Change STYLE-PUBLIC in `documents/build/make_style_public.py`, regenerate, and run it with `--check`; never edit the page by hand.

## Requirements: this repository

- **XX.1** the one-line form for the brief.

## Lean

Mathlib's conventions at the pinned revision; the statement reviewed apart from its proof, at the weakest hypotheses;
a build-failing axiom sweep; `simp only`, no unexplained raised limits; no linter disabled at file scope; a check
module beside every module; in running code, `Except` not `panic!`.

## Shell

POSIX `sh`, `set -eu`, every expansion quoted, a counted deadline on every wait, `trap … EXIT`, `shellcheck -s sh`
clean.

## Documents: which style

- Team reader (report, write-up, design note, runbook): `vendor/code-standard/documents/STYLE.html`.
- Outside reader (paper, public page, note to a collaborator): `vendor/code-standard/documents/STYLE-PUBLIC.html`.
- Copy the chosen head whole; the rules travel in its comment. Open the file to see a specimen of every element.

## Before calling work done

1. State: what persisted state does it touch, and does it change only as the binding says?
2. Transformation: does any answer depend on more than recorded state and arguments?
3. Effect: which one kind of effect does it do, and where does each failure go?
4. Semantics: which document gives it its meaning?
5. Verification: what would show it wrong?
6. CALM: does a conclusion depend on absence? Is its scope closed? Could more input withdraw it?
