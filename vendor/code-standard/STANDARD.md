# Coding standard

Status: draft, first extracted 2026-09-24 from the OntolMeta repository's standard. It is revised as clause 14 says.

This standard says what code shall do so that a program means what its design says it means and fails where it can be
seen. It is read against six axes (4.1): state, transformation, effect, semantics, verification and CALM. It is used by
a repository through a **binding** (clause 12), which names the repository's own documents of meaning, selects modules,
and adds what is true only of that repository. TigerStyle, pinned to one commit, is kept as the discipline inside a
single function (clause 10).

Every term on which a requirement depends is defined in clause 3, and every definition cites the source it is taken from.
Every source is pinned by the SHA-256 of the bytes that were read (`sources/INDEX.md`); the bytes themselves are fetched
into a local cache, not carried here (12.4). A source is the work that introduced the term, a standard or specification,
official documentation, or a peer-reviewed reference work. Openly edited wikis are not sources.

The verbal forms **shall**, **shall not**, **should** and **may** are used as in ISO/IEC Directives Part 2
[ISO-Dir2 p.17]: a requirement, a prohibition, a recommendation, a permission. A NOTE explains and requires nothing.

## 1. Scope

This standard applies to every program in a repository that has a binding. Clauses 4 to 11 apply everywhere; a module
(`modules/`) applies where the binding names it; the binding's own requirements apply in its repository alone. Where a
repository has its own standard for tests, it governs tests.

It does not decide any repository's design. It makes no claim about any repository's code; a binding's known departures
do that, dated.

## 2. Normative references

2.1 The binding of the repository in question, and the documents it names as giving the repository its meaning (12.1).
Where the binding and this standard conflict, the conflict is an open question to be settled in the binding's documents,
not by the code.

2.2 Sources: each is cited by a key in brackets, with a page, section, line or fragment where the text relied on is.
`sources/INDEX.md` gives, for each key, the work, the address its bytes were fetched from, the fragment, the file name and
the SHA-256. A definition in clause 3 that the pinned text does not support is a defect in this standard.

2.3 TigerStyle is `docs/TIGER_STYLE.md` of TigerBeetle at commit `ba8d4b347cbb29057fd52243d2909b7a830f9336` (key TS),
cited as [TS Lnn] by line of that file.

## 3. Terms and definitions

A term is listed if a requirement's meaning depends on it. Each entry gives the source's meaning first, with the place
in the source it is taken from, and then, after *In this standard*, how this standard uses it. A binding narrows a term
further only by citing its own documents. Where the source's words are quoted they are verbatim; elsewhere the entry
paraphrases, and the pinned text is what it must agree with (2.2).

### State

**3.1 state** — "at a given instant in time, the condition of an object that determines the set of all sequences of
actions … in which the object can participate" [SEVOCAB-state (1), from ISO/IEC 10746-2]. An object has state "if its
behavior is influenced by its history", and assignment, which changes state, ends the rule that equals may be
substituted for equals [SICP #%_idx_2838, #%_idx_2990]. *In this standard:* state is what a program persists, as its
binding names it (4.3). What a running program holds only in memory is working data, not state in this sense.

**3.2 essential state; derived data** — essential state is data the system must keep because it cannot be recovered;
derived data "can always be re-derived (from the input data — i.e. from the essential state) whenever required" [TarPit
p.25]. *In this standard:* a binding says which of its repository's data is essential; everything else is derived (7.5).

**3.3 canonical representation** — the one encoding defined for each value, "uniquely defined for each S-expression",
with no choice left to the writer [Rivest97 §6.1]. *In this standard:* required wherever values are compared or hashed
as bytes (RK.6).

**3.4 content addressing** — naming a block of data by a hash of its contents, so that "a block cannot be modified
without changing its address; the behavior is intrinsically write-once" [Venti p.3]. *In this standard:* module RK's
objects.

**3.5 SHA-256** — the hash function of [FIPS180-4 §6.2]. *In this standard:* a hash is written with its algorithm, so
that the algorithm can change without a migration that never finishes.

**3.6 hash tree** — a tree in which each node's value is a one-way function of its children's values, so that the root
authenticates every leaf ("tree authentication") [Merkle79 p.22, p.24]. *In this standard:* module RK's log and trees.

**3.7 log** — "an append-only, totally-ordered sequence of records ordered by time"; applying its changes in order
rebuilds the current state [Kreps13]. *In this standard:* module RK's log is a set of entries that name their parents by
hash; their order in a file is storage, not meaning.

**3.8 event sourcing** — ensuring "that all changes to application state are stored as a sequence of events" [Fowler05].
*In this standard:* module RK: an entry records an event and the state it produced.

**3.9 materialized view** — a view materialized "by storing the tuples of the view in the database", and kept up to date
by view maintenance [GuptaMumick95 p.5]. *In this standard:* derived data kept for speed, which may be deleted and
rebuilt (7.5).

**3.10 durability** — "once a transaction is committed, it cannot be abrogated" [Gray81 p.3].

**3.11 write-ahead logging** — "the log records representing changes to some data must already be on stable storage
before the changed data is allowed to replace the previous version" [ARIES p.4]. *In this standard:* record before the
effect (RK.5).

**3.12 atomic replacement** — when `rename()` replaces an existing name, the name remains visible throughout and refers
to either the old file or the new one [POSIX-rename DESCRIPTION].

**3.13 file name** — "a sequence of bytes … used to name a file", which "shall not contain the <NUL> or <slash>
characters" [POSIX-XBD3 3.146]; bytes, not text. UTF-8 is one reading of bytes, and a byte sequence is valid UTF-8 only
if it matches the grammar of [RFC3629 §4]; Python represents undecodable bytes as lone surrogates with the handler
`surrogateescape` [PEP383]. *In this standard:* 5.2.

**3.14 HEAD** — in git, a reference to the current branch or commit [Git L228–234]. *In this standard:* module RK's
head: the one value held outside the log, vouching for the entry it names and that entry's ancestors only.

**3.15 provenance** — "a record that describes the people, institutions, entities, and activities involved in producing,
influencing, or delivering a piece of data" [PROV-DM #dfn-provenance]. *In this standard:* 6.5, name the instrument.

**3.16 referential transparency** — a language in which "equals can be substituted for equals" in an expression without
changing its value is referentially transparent [SICP #%_idx_2990]. A **transformation** is a computation that keeps
this property: its result depends on its arguments alone. *In this standard:* a derivation (4.2).

**3.17 functional core, imperative shell** — decisions made by a core of pure code, "surrounded by a shell of imperative
code" that does the input and output [Bernhardt12].

**3.18 join-semilattice** — a partial order with a least upper bound ⊔ for all pairs; "it follows that ⊔ is: commutative
… idempotent … and associative" [CRDT p.5 §2.3]. An object whose states form one and whose merge computes the least
upper bound converges [CRDT p.6 Def. 4, Thm. 1].

**3.19 strong eventual consistency** — "Correct replicas that have delivered the same updates have equivalent state"
[CRDT p.5 Def. 3].

**3.20 multi-value register** — a register whose merge keeps all concurrently assigned values, "for instance taking
their union" [CRDT-TR p.23]. *In this standard:* RK.8, disagreement is a value.

**3.21 invariant confluence** — a set of transactions is invariant-confluent with respect to an invariant if merging any
two states reachable from a valid state by those transactions gives a valid state [Bailis15 p.5 Def. 6]; such an
invariant can be kept without coordination.

**3.22 parse, validate** — "a parser is just a function that consumes less-structured input and produces more-structured
output"; the difference from validating "lies almost entirely in how information is preserved" [King19
#the-power-of-parsing].

**3.23 illegal states unrepresentable** — a rule stated as a heading and shown by example: a record of optional fields
is replaced by one variant per state, so that no value describes a state that cannot occur [Minsky11
#make-illegal-states-unrepresentable].

**3.24 correctness by construction** — "a development process that builds correctness into every step" [HallChapman02
p.3].

**3.25 nondeterministic** — an algorithm that may use a multiple-valued function `choice(X)`, so that one input can lead
to more than one computation [Floyd67 p.1]. *In this standard:* 6.3; a binding may sort steps further by how their
result is fixed.

**3.26 effect** — what a computation does besides producing a value. The standard examples are "partiality",
"nondeterminism", "side-effects" on a store or on input and output, "exceptions", "continuations" and "interactive
input", each a "notion of computation" [Moggi91 p.3, Example 1.1]. *In this standard:* a write, a read of the clock, a
draw of randomness, a subprocess, a crash, and not returning are each an effect.

**3.27 capability** — a reference that designates an object and says what may be done with it: "each capability in a
C-list locates by means of a pointer some computing object, and indicates the actions that the computation may perform"
[DennisVanHorn66 p.3]; in object-capability systems, "a capability is an object reference" [MYS03 p.14], and objects
"interact only by sending messages on references" [Miller06 p.81].

**3.28 ambient authority** — "authority that is exercised, but not selected, by its user" [MYS03 p.8].

**3.29 least privilege; least authority** — "every program and every user of the system should operate using the least
set of privileges necessary to complete the job" [S&S §I.A.3 f]; with capabilities, grant "each program only the
authority it needs to do its job" [Miller06 p.34].

**3.30 fail-safe defaults** — "Base access decisions on permission rather than exclusion" [S&S §I.A.3 b].

**3.31 open design** — "The design should not be secret" [S&S §I.A.3 d].

**3.32 economy of mechanism** — "Keep the design as simple and small as possible" [S&S §I.A.3 a].

**3.33 confused deputy** — a program that runs "with authority stemming from two sources" and is led to use one on
another's behalf [Hardy88].

**3.34 trusted computing base** — "the totality of protection mechanisms within a computer system … responsible for
enforcing a security policy" [TCSEC p.112]. Reducing it means reducing "the amount of trusted code", and "minimizing
privilege is not the same as minimizing the amount of trusted code" [djb p.3, p.4].

**3.35 sandbox** — "confining a helper application to a restricted environment" [Goldberg96 p.4]. *In this standard:* a
sandbox contains; it does not decide.

**3.36 structured concurrency** — "every time our control splits into multiple concurrent paths, we want to make sure
that they join up again"; a task can start children only inside "a place for the children to live: a nursery" [NJS-SC
#nurseries-a-structured-replacement-for-go-statements].

**3.37 deadline; cancel scope** — a deadline is an absolute time by which an operation must finish, as against a timeout
relative to when it was called [NJS-TC #absolute-deadlines-are-composable-but-kinda-annoying-to-use]; a cancel scope
applies a cancellation to every blocking operation inside it [NJS-TC #how-cancel-scopes-work].

**3.38 reap** — collect a terminated child's status with `wait()` or `waitpid()`, which "consume the status information
they obtain" [POSIX-wait DESCRIPTION]; until then the child is a zombie process, "the remains of a live process … after
it terminates … and before its status information … is consumed by its parent" [POSIX-XBD3 3.426].

**3.39 time-of-check to time-of-use** — a flaw that "occurs when a program checks for a particular characteristic of an
object, and then takes some action that assumes the characteristic still holds" [BishopDilger96 p.2].

**3.40 dead store elimination** — a compiler optimisation that "can also remove seemingly useless memory writes that the
programmer intended to clear sensitive data after its last use" [Yang17 p.2].

**3.41 fail-fast** — "the module either functions properly or stops" [Gray85 p.12].

### Semantics

**3.42 semantics** — "a correct and meaningful correspondence between programs and mathematical entities"
[ScottStrachey71 p.5]: a meaning for each program and datum, independent of any implementation. *In this standard:* the
meaning of a repository's data and operations is fixed by the documents its binding names (4.4).

**3.43 closed-world assumption** — "everything that you don't know to be true may be assumed false" [Reiter77 p.17].

**3.44 monotonic** — "A program P is monotonic if for any input sets S,T where S ⊆ T, P(S) ⊆ P(T)" [CALM p.3 Def. 1]:
more input never withdraws an output.

**3.45 coordination** — "a program contains coordination if it requires messages to be sent under all possible
partitionings" of its input [CALM p.4].

**3.46 CALM theorem** — "A program has a consistent, coordination-free distributed implementation if and only if it is
monotonic" [CALM p.3 Thm. 1].

**3.47 manifest** — a list sent with a non-monotonic request "of all its update message IDs that preceded" it, so that
replicas can delay the request until they have processed all updates in the manifest [CALM p.4].

**3.48 closed** — a scope is closed when a manifest (3.47) for it has arrived and nothing in the scope can follow it;
only then is the closed-world assumption (3.43) justified for that scope. *In this standard:* a binding says what its
scopes are and what closes each; module RK's is a line's end. The word *sealed* is not used.

**3.49 falsifiable** — open to refutation by observation: "a universal statement is falsified by a single genuine
counter-instance" [Popper #BasiStatFalsConv].

**3.50 preregistration** — "committing to analytic steps without advance knowledge of the research outcomes"; in
prediction the data can show the prediction wrong, while in postdiction "the data are already known" [Nosek18 p.1, p.2].

**3.51 verification; validation** — verification is "confirmation, through the provision of objective evidence, that
specified requirements have been fulfilled" ("the system has been built right"); validation confirms that the
requirements for the intended use are fulfilled ("the right system has been built") [SEVOCAB-verification,
SEVOCAB-validation].

**3.52 assertion; precondition; postcondition** — an assertion states what holds of the variables at a point of
execution; "if the assertion P is true before initiation of a program Q, then the assertion R will be true on its
completion" [Hoare69 p.2]. Later usage calls P the precondition and R the postcondition [Meyer92 p.3].

**3.53 contract; class invariant** — a contract states the obligations and benefits of a routine and its callers: "the
precondition expresses requirements that any call must satisfy", "the postcondition expresses properties that are
ensured in return" [Meyer92 p.3]; "a class invariant is a property that applies to all instances of the class" [Meyer92
p.6].

**3.54 programmer error; operating error** — an operating error is expected and must be handled; an assertion detects a
programmer error, and "the only correct way to handle corrupt code is to crash" [TS L104–107]. The same split is a
recoverable error, "usually the result of programmatic data validation", against a bug, "a kind of error the programmer
didn't expect", which ends in abandonment [Duffy16 #bugs-arent-recoverable-errors].

**3.55 test oracle** — "a predicate that determines whether a given test activity sequence is an acceptable behaviour"
of the system under test [Barr15 p.4].

**3.56 property; law** — a statement quantified over the inputs of a domain; QuickCheck "takes a law as a parameter and
applies it to a large number of randomly generated arguments" [QuickCheck p.2]. *In this standard:* a law is one
executable statement saying what holds for every input of a domain.

**3.57 fuzzing** — testing with a generated "stream of random characters to be consumed by a target program" [Fuzz90
p.4].

**3.58 differential testing** — "if a single test is fed to several comparable programs … and one program gives a
different result, a bug may have been exposed" [McKeeman98 p.2]. Versions written independently fail together far more
often than independence predicts [K&L p.1].

**3.59 mutation testing** — faults "deliberately seeded into the original program … to create a set of faulty programs
called mutants"; a mutant whose result differs from the original's on some test is "killed" [JiaHarman11 p.1, p.4].

**3.60 deterministic simulation** — conducting "a deterministic simulation of an entire … cluster within a
single-threaded process", so that every run can be reproduced [FDB L17].

**3.61 verification-guided development** — "we prove properties about a readable formal model, and rigorously test that
the deployed code matches that model" [VGD p.6], the model's implementation checked by differential random testing
[Cedar24 p.3].

## 4. The model

4.1 **Six axes.** Every requirement is read against six questions. **State** (3.1): what does the code persist, and how
may it change? **Transformation** (3.16): which answers depend on their arguments alone? **Effect** (3.26): what does
the code do besides return a value, and which kind of effect is it? **Semantics** (3.42): which document gives the code
its meaning? **Verification** (3.51): what would show it wrong? **CALM** (3.46): does a conclusion depend on absence or
completeness, and is its scope closed (3.48) when it is drawn?

4.2 **Four kinds of code.** Code is sorted by the effects it may do.

- **Observe** reads what the program does not control: input from users, files it did not write, other programs'
  output, the network.
- **Record** writes the state the program persists (3.1). Nothing else writes it.
- **Derive** computes answers from recorded state and arguments alone: a transformation (3.16), the functional core
  (3.17).
- **Act** changes the world outside the program's own state: starts processes, sends requests, writes elsewhere.

A function does one kind of effect, or none. A function that does two is split, so that a failure is attributed to the
kind it came from (clause 9).

4.3 **State.** A repository's binding (clause 12) names what it persists and how each part may change. Module RK
(record-keeping) gives one model, in which recorded state only accumulates; a repository that updates in place says so in
its binding, and names which cells are overwritten and by whom.

4.4 **Semantics.** Meaning lives in the documents a binding names: design decisions, specifications, a glossary. Code
implements meaning and never invents it. Each requirement's *Means* cites the terms and sources it rests on; the binding
says what it means in its repository.

4.5 **Verification.** Every requirement names how a breach would be seen: a law tested as a property (3.56), fuzzing
(3.57), differential testing (3.58), a replay, an assertion (3.52), or a check the binding lists. A requirement with none
is advice, and says so.

4.6 **CALM.** Every conclusion the code draws is monotonic (3.44), or it needs closure: it depends on absence,
completeness, a threshold or "the latest", and is drawn only where the closed-world assumption (3.43) is justified.
Coordination (3.45) is spent only where closure is needed; the binding names those places.

4.7 **How to read a requirement.** A requirement opens `**ID Title.**` and ends with a reading line:

> *Means* — the terms and sources it rests on. *Governs* — state, transformation or effect. *CALM* — monotonic, needs
> closure, or not applicable. *Checked by* — the kind of check that can see a breach, or "advice". *Brief* — the line the
> brief carries.

IDs are clause numbers here (5.1), a module's letters in a module (RK.1, X86.1), and the binding's own letters in a binding.

4.8 **Goals.**

- Rank safety over performance over developer experience, and say so when they conflict [TS L21–23]. Safety means: the
  program never reports more than it observed, and never fails silently.
- Keep code in a trust boundary small enough for one person to read in full; keep the design as simple and small as
  possible (3.32) [TNaCl p.2] [djb p.3].
- Budget privilege and trusted code separately; a sandbox limits damage and does not reduce what must be trusted (3.34)
  [djb p.4].
- Solve a problem when it is found, or write it down where the next reader meets it [TS L62–79].
- Keep the requirements few enough to remember and specific enough to check mechanically [P10 p.1].
- Before adding a check, run it on the present code and count what it refuses, how much of that is wrong, and how cheap
  the rewrite is where it is not. A check that refuses correct code is worked around: "people completely circumvent the
  feature" [Hejlsberg, "The Scalability of Checked Exceptions"].

<!-- brief: before: The model -->
- Six axes: state, transformation, effect, semantics, verification, CALM (4.1). Read every rule against them.
- Four kinds of code (4.2): **observe** what you do not control; **record** the state you persist, and nothing else
  writes it; **derive** answers from recorded state and arguments alone; **act** on the world outside. A function does
  one kind of effect, or none.
- Meaning lives in the documents the binding names; code implements it and never invents it (4.4).
- Every rule names how a breach would be seen; a rule with no check is advice (4.5).
- CALM (4.6): a conclusion is monotonic, or it depends on absence or completeness and is drawn only on a closed scope.
- Safety first: never report more than was observed; never fail silently (4.8).
<!-- /brief -->

## 5. Observation

**5.1 Total over what it finds.** Code that reads what it does not control shall return a value for everything it
meets. What it cannot read becomes a value that says so, with the reason. It shall not raise for anything the source of
the input can cause.
> *Means* — 3.41, 3.57. *Governs* — effect. *CALM* — not applicable. *Checked by* — fuzzing with hostile input (3.57).
> *Brief* — Never raise on anything the input's source can cause; return a value that says what could not be read, and why.

**5.2 Names are bytes.** File names and other identifiers from outside shall be carried as bytes from the system call to
wherever they are kept (3.13). Text is for display; a conversion for display shall not be used for identity, equality or
order.
> *Means* — 3.13 [POSIX-XBD3 3.146] [RFC3629 §4]. *Governs* — state. *CALM* — not applicable. *Checked by* — fuzzing with
> names that are not valid UTF-8. *Brief* — Names from outside are bytes end to end; text is for display, never for
> identity, equality or order.

**5.3 Scope is given.** An observation shall read only what it was pointed at, by an identifier it was given; where scope
is missing it shall skip the observation, not widen or guess it.
> *Means* — 3.29 [S&S §I.A.3 f]. *Governs* — effect. *CALM* — not applicable. *Checked by* — advice. *Brief* — Read only
> what you were pointed at; where scope is missing, skip, never widen or guess.

**5.4 Parse where it arrives.** Input from outside shall be parsed once, where it arrives, into a value the rest of the
code relies on (3.21, 3.22). A refusal there is an ordinary outcome with its reason, never an exception from deep inside.
> *Means* — 3.21, 3.22. *Governs* — transformation. *CALM* — monotonic. *Checked by* — fuzzing (3.57) and laws on the
> parser (3.56). *Brief* — Parse outside input once, where it arrives; a refusal there is an outcome with its reason.

**5.5 A lapse is reported.** Where a guarantee depends on something that can stop holding — a timeout, a watcher, a
lease — the program shall record or report the moment it stopped holding.
> *Means* — 3.41. *Governs* — effect. *CALM* — needs closure (no report of a lapse is an absence). *Checked by* — advice.
> *Brief* — Where a guarantee can lapse, report the moment it did.

**5.6 Observing and recording apart.** A handler that turns a failure to read the outside into a value shall not also
cover a write of the program's own state. A failure to write one's own state is not a fact about the outside (9.1).
> *Means* — 3.54. *Governs* — effect. *CALM* — not applicable. *Checked by* — a scan for handlers that cover both.
> *Brief* — No handler covers both a read of the outside and a write of your own state.

## 6. Recording

**6.1 One writer per piece of state.** Each piece of persisted state shall have one piece of code that writes it, and
the binding shall say how it may change: appended, replaced, or updated in place.
> *Means* — 3.1, 3.2. *Governs* — state. *CALM* — not applicable. *Checked by* — a scan for writes outside the owner.
> *Brief* — Each piece of persisted state has one writer, and the binding says how it may change.

**6.2 Replace atomically.** A file that another reader may open while it changes shall be replaced, not rewritten in
place: the new content written elsewhere, flushed to the storage device [POSIX-fsync DESCRIPTION], renamed over the old
(3.12), and the directory flushed, so that the replacement is durable (3.10).
> *Means* — 3.10, 3.12. *Governs* — state. *CALM* — not applicable. *Checked by* — a scan for opens for writing of
> shared files. *Brief* — Replace a file others read atomically: write elsewhere, fsync, rename over, fsync the directory.

**6.3 Nondeterminism is a parameter.** The clock, randomness, and anything else that can differ between two runs shall
be taken as parameters, not reached for, so that the code can be run again with the same inputs (3.25). Only functions
the binding names obtain them.
> *Means* — 3.25, 3.60. *Governs* — effect. *CALM* — not applicable. *Checked by* — a scan for reads of the clock and of
> random sources. *Brief* — Take the clock, randomness and other nondeterminism as parameters; never reach for them.

**6.4 A failure to persist is never silent.** If the program cannot write its own state, the writer shall stop and shall
write nothing that says the work is finished; the stop is reported outside that state.
> *Means* — 3.41, 3.54. *Governs* — effect. *CALM* — needs closure (a "finished" record asserts completeness).
> *Checked by* — fault injection on writes. *Brief* — If your own state cannot be written, stop, declare nothing
> finished, and report it.

**6.5 Name the instrument.** A result that someone will rely on shall name the code, and the version of it, that
produced it (3.15).
> *Means* — 3.15 [PROV-DM #dfn-provenance]. *Governs* — state. *CALM* — not applicable. *Checked by* — advice.
> *Brief* — A result names, by version or hash, the code that produced it.

## 7. Derivation

**7.1 Pure.** A derivation shall read only recorded state and its arguments. It shall not print, write, read the clock,
or read anything the recorded state does not name; its caller does those (3.16, 3.17).
> *Means* — 3.16, 3.17 [Bernhardt12]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — a scan of
> derivation modules for effects. *Brief* — A derivation reads only recorded state and arguments: no printing, writing,
> clock, or unnamed files.

**7.2 Content, not layout.** A derivation's result shall not depend on where something sits in a file, on the iteration
order of an unordered container, or on how a value was obtained, only on the value.
> *Means* — 3.16. *Governs* — transformation. *CALM* — not applicable. *Checked by* — a law (3.56): shuffling layout
> leaves the result unchanged. *Brief* — Depend on content, never on file position, container order, or how a value was
> obtained.

**7.3 Every conclusion carries its scope.** A conclusion that depends on absence or completeness shall say which scope
it depends on, and shall be drawn only when that scope is closed (3.48); otherwise it is declined with the reason the
scope is open.
> *Means* — 3.43, 3.44, 3.46, 3.48 [CALM p.3] [Reiter77 p.17]. *Governs* — transformation. *CALM* — this requirement.
> *Checked by* — a prefix replay: a conclusion drawn on a prefix of the input and withdrawn on a longer one fails unless
> it declared its scope. *Brief* — A conclusion about absence names its scope and is drawn only when that scope is closed;
> otherwise decline and say why.

**7.4 Decline, never guess.** A derivation that cannot compute its answer from what it has shall say so and why, and
shall not put another answer in its place.
> *Means* — 3.41. *Governs* — transformation. *CALM* — monotonic. *Checked by* — a law on the inputs that cannot be
> answered. *Brief* — When the answer cannot be computed, say so and why; never put another answer in its place.

**7.5 Derived data is not stored as truth.** What can be computed from recorded state — a status, a count, a standing,
an index — shall be computed when needed, or kept only as a view that may be deleted and rebuilt (3.2, 3.9).
> *Means* — 3.2 [TarPit p.25], 3.9. *Governs* — state. *CALM* — not applicable. *Checked by* — deleting the views and
> rebuilding them gives the same answers. *Brief* — Never store what can be derived as if it were a fact; keep it only as
> a rebuildable view.

**7.6 Laws beside operations.** An operation shall state its laws where it is defined — an inverse, an order that does
not matter, an equality between two ways of computing one thing — and each law shall be tested as a property (3.56).
> *Means* — 3.53, 3.56 [QuickCheck p.2]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — the property
> tests themselves. *Brief* — State an operation's laws beside it and test each as a property.

## 8. Action

**8.1 Only given authority.** Code that acts shall use only the handles, paths and descriptors it was given
(capabilities, 3.27), shall not reach past them with ambient authority (3.28), and shall hold the least authority its
task needs (3.29). It shall not use authority it holds for one party on a name supplied by another, which is how a
program becomes a confused deputy (3.33).
> *Means* — 3.27–3.29, 3.33 [MYS03 p.8] [Hardy88]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a sandbox
> where one can enforce it; otherwise advice. *Brief* — Use only the handles and paths you were given, with the least
> authority the task needs; never use one party's authority on another party's name.

**8.2 Decide by permission.** An access decision shall be based on permission, not exclusion, so that an unforeseen case
is refused (3.30).
> *Means* — 3.30 [S&S §I.A.3 b]. *Governs* — effect. *CALM* — not applicable. *Checked by* — advice. *Brief* — Decide
> access by permission, not exclusion, so the unforeseen case is refused.

**8.3 Fail closed from outside.** The decision to fail closed shall be made outside the component that can fail; a
component cannot catch the failures that stop it starting.
> *Means* — 3.30. *Governs* — effect. *CALM* — not applicable. *Checked by* — a test with a deliberately broken
> component. *Brief* — The decision to fail closed lives outside the thing that can fail.

**8.4 Every task has an owner.** Every thread and child process shall have one owner that outlives it (3.36). At an
orderly end the owner waits with a deadline (3.37); at the deadline it kills, reaps (3.38) and records what was still
running.
> *Means* — 3.36–3.38 [NJS-SC] [POSIX-wait DESCRIPTION]. *Governs* — effect. *CALM* — needs closure (the owner's wait is
> how it learns nothing more is coming). *Checked by* — a list of every place that starts a thread or process, each with
> its join or wait. *Brief* — Every thread and child has one owner: wait with a deadline, then kill, reap, and record
> what was left.

**8.5 Finished means every child has ended.** Nothing shall declare work finished — in a record, a return value or an
exit status — until every task that work started has ended and been reaped.
> *Means* — 3.36, 3.47, 3.48. *Governs* — effect. *CALM* — needs closure: the declaration is a manifest (3.47).
> *Checked by* — a test that holds a child open while the work is told to finish. *Brief* — Declare work finished only
> after every task it started has ended and been reaped.

**8.6 Every wait has a deadline.** Every wait and every subprocess shall have a timeout. Reaching it is reported as
itself, distinct from a crash.
> *Means* — 3.37 [NJS-TC #absolute-deadlines-are-composable-but-kinda-annoying-to-use]. *Governs* — effect. *CALM* — not
> applicable. *Checked by* — a scan for waits and subprocess calls without a timeout. *Brief* — Every wait and subprocess
> has a timeout; reaching it is reported as itself, never as a crash.

**8.7 Secrets.** A secret shall be read by one program only; shall not appear in a command line, an environment dump, a
file name, a log or a hash; shall be held in a buffer that overwrites itself on every path, since a scrub nothing reads
is a dead store (3.40); and what a run wrote shall be searched for it before the run is kept.
> *Means* — 3.40 [Yang17 p.2]. *Governs* — effect. *CALM* — needs closure (the search asserts absence). *Checked by* —
> a search of every kept output for the secret. *Brief* — Secrets: one reader; never in arguments, environment dumps,
> file names, logs or hashes; scrubbed on every path; searched for in what is kept.

**8.8 Open design.** A mechanism's protection shall not depend on its design or its code being secret (3.31); only keys
and credentials are secret.
> *Means* — 3.31 [S&S §I.A.3 d]. *Governs* — effect. *CALM* — not applicable. *Checked by* — advice. *Brief* — Protection
> never depends on the design or the code being secret.

## 9. Failures

**9.1 Sort a failure by where it came from.**

| Source | Response |
|---|---|
| The code's own invariant: a programmer error (3.54) | stop, by assertion (3.52) [TS L104–107] |
| What the code depends on: its own storage, a child it started, the machine | stop the writer (6.4), or an error returned to the caller; never recorded as a fact about the outside |
| What the code observes: input, files, other programs, the network | a value: a row or a finding, with its reason (5.1) |

> *Means* — 3.54 [Duffy16 #bugs-arent-recoverable-errors]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a
> scan for handlers that mix sources (5.6). *Brief* — Route a failure by its source: own invariant broken, assert and
> stop; something depended on, stop or return an error, never a fact; something observed, a value with its reason.

**9.2 Handle every error, one source per handler.** Every error shall be handled; most catastrophic failures come from
mishandled non-fatal errors [Yuan p.9]. A handler shall cover failures from one source of 9.1 only.
> *Means* — 3.54. *Governs* — effect. *CALM* — not applicable. *Checked by* — tests of the error paths. *Brief* — Handle
> every error, and let each handler cover one source only.

**9.3 A crash is not a refusal.** A crash shall never be counted as a refusal or as an answer.
> *Means* — 3.55. *Governs* — effect. *CALM* — not applicable. *Checked by* — tests that tell a refusal from a crash.
> *Brief* — A crash is never counted as a refusal or as an answer.

**9.4 Outcomes in the type, bugs asserted.** An expected outcome, and an error of something depended on, shall be part
of the return type; a programmer error shall be an assertion. Prefer the simplest return type that carries the answer
[TS L426–429].
> *Means* — 3.54 [Duffy16 #bugs-arent-recoverable-errors]. *Governs* — transformation. *CALM* — not applicable.
> *Checked by* — advice. *Brief* — Outcomes and errors of dependencies go in the return type, bugs in assertions; use the
> simplest type that works.

## 10. Inside a function

TigerStyle governs code inside one function, as adopted here and pinned by 2.3. Annex A lists every TigerStyle rule and
whether it is adopted, adapted or not adopted, with the reason.

**10.1 Bounds.** Put a limit on everything the code itself does: every loop, queue, buffer, connection count and wait
[TS L96–99]. Assert that a loop is meant not to terminate [TS L99–100]. Recurse only with an asserted depth limit that
refuses, because input from outside can be as deep as it likes and the interpreter's own limit is a crash [TS L90–91]
[P10 p.2]. A violated bound on the code's own work fails fast (3.41); a bound reached while observing is a value (5.1).
> *Means* — 3.41 [P10 p.2]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a scan for unbounded loops and
> recursion without a depth argument. *Brief* — Bound everything the code does (loops, queues, buffers, waits); recurse
> only under an asserted depth limit.

**10.2 Assertions.** Assert arguments, return values, preconditions, postconditions and invariants (3.52, 3.53)
[TS L109–111]. Assert a property on two paths, above all immediately before writing to storage and immediately after
reading it back [TS L115–118]. Assert what is expected and what must never happen [TS L136–140]. One condition per
assertion [TS L123–124]. Replace a comment about a surprising invariant with an assertion [TS L120–121]. Build a precise
mental model first and encode it as assertions [TS L145–146]; an assertion is a safety net, not a substitute for
understanding [TS L142–149].
> *Means* — 3.52, 3.53 [Hoare69 p.2] [Meyer92 p.3]. *Governs* — transformation. *CALM* — not applicable. *Checked by* —
> review; fuzzing makes assertions fire. *Brief* — Assert preconditions, postconditions and invariants; pair them around
> storage; assert what must never happen; one condition per assertion.

**10.3 Control flow.** Only simple, explicit control flow [TS L90]. Split compound conditions into nested branches
[TS L187–191]. State conditions positively [TS L193–211]. Keep branching in the parent and push non-branching work into
helpers [TS L168–172].
> *Means* — [TS L90]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — review. *Brief* — Simple,
> explicit control flow; split compound conditions; state them positively; branch in the parent.

**10.4 State inside a function.** Centralize state manipulation: the parent keeps the state, helpers compute what should
change, leaf functions are pure (3.16) [TS L173–175]. Do not duplicate variables or take aliases to them [TS L374–375].
Declare each variable at the smallest scope and compute it close to its use; the gap between a check and a use is where
bugs live (3.39) [TS L158–159] [TS L416–424].
> *Means* — 3.16, 3.39. *Governs* — state. *CALM* — not applicable. *Checked by* — review. *Brief* — The parent holds the
> state and leaf functions are pure; no duplicated or aliased variables; smallest scope, close to use.

**10.5 Functions.** At most 70 lines [TS L161–162]. Few parameters, a simple return type, a substantial body
[TS L166–167]. Pass library options explicitly [TS L226–229]. Take behaviour-varying arguments by name and singleton
dependencies positionally [TS L349–354]. Use a minimum of abstractions, and only those that make the best sense of the
domain [TS L91–94].
> *Means* — [TS L161–162]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — a function-length scan.
> *Brief* — At most 70 lines; few parameters; library options passed explicitly; varying arguments by name; a minimum of
> abstractions.

**10.6 Naming.** [TS L273–347], adopted whole: nouns and verbs exact; no abbreviations except a loop index; units and
qualifiers last (`latency_ms_max`); names that inform the call site; related names of equal length; a helper prefixed by
its caller; nouns over participles; one word, one meaning (11.2). Index, count and size are distinct kinds with explicit
conversions [TS L445–450]; rounding is explicit at every division [TS L452–454].
> *Means* — [TS L273–347]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — review. *Brief* — Exact
> nouns and verbs; no abbreviations; units last (`latency_ms_max`); index, count and size distinct; rounding explicit.

**10.7 Comments.** Say why [TS L221–224] [TS L360–361], and cite the measurement or failure that made a line necessary.
A comment is a sentence; an end-of-line note may be a phrase [TS L367–370]. A test opens with its goal and method
[TS L363–365]. Commit messages are written for a reader of `git blame` [TS L356–358].
> *Means* — [TS L221–224]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — review. *Brief* — Comments
> say why and cite the measurement; they are sentences; a test opens with its goal and method.

**10.8 Performance.** Sketch the cost against network, disk, memory and CPU before building [TS L241–243]. Optimise the
slowest resource first, weighted by frequency [TS L245–247]. Measure before claiming.
> *Means* — [TS L241–247]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a measurement named with the
> claim. *Brief* — Sketch the cost before building; the slowest resource first; measure before claiming.

**10.9 Dependencies and tooling.** Add no dependency to code that holds a secret or sits in the trusted base without
writing down why [TS L476–479]. Keep one small standard toolbox [TS L483–487]. A shell script only starts programs and
waits for them; the moment it parses data or decides, it leaves shell.
> *Means* — 3.34 [TS L476–487]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a list of dependencies with
> reasons. *Brief* — No dependency in trusted or secret-holding code without a written reason; shell only to start
> programs and wait.

**10.10 Tests.** Where a repository has its own test standard, it governs. Otherwise:

- Test features, not implementation, so that a test survives the code being replaced [mk-test L151–160].
- Put the API under test behind one `check` function [mk-test L78–80].
- Keep cases as data: value in, value out [mk-test L253–258].
- Nothing stubbed or mocked [mk-test L277]; plain assertions, with a hand-written message once a failure has been
  debugged, and no fluent assertion library [mk-test L313–332].
- A snapshot test has an update mode that rewrites the expected value in place [mk-test L289–300].
- Beyond examples, generate inputs: property tests (3.56) and fuzzing (3.57) [mk-test L417–443]. This standard prefers a
  property or fuzz test first, and a snapshot only where no property can be stated; the preference is its own, not the
  source's.
- Prove properties of a small model and test the implementation against it (3.61) [VGD p.6] [Cedar24 p.3].
- Agreement between implementations one author wrote is not independence (3.58) [K&L p.1].
- Control every source of nondeterminism in a test, so that a failure reproduces from its seed (3.60) [FDB L17].
- Seed faults to measure what the tests catch (3.59) [JiaHarman11 p.1]; a test that passes a planted fault is not yet a
  test. An oracle (3.55) [Barr15 p.4] that comes from the code under test cannot find that the code was always wrong.

> *Means* — 3.55–3.61. *Governs* — transformation. *CALM* — not applicable. *Checked by* — mutation testing (3.59). *Brief* — Test features, not code: one
> `check` function, cases as data, no mocks, properties and fuzzing, nondeterminism controlled, faults planted.

## 11. Words and documents

**11.1 The glossary binds.** The glossary a binding names binds every program, comment and document of its repository.
> *Means* — 3.42. *Governs* — transformation. *CALM* — not applicable. *Checked by* — review. *Brief* — The repository's
> glossary binds every program, comment and document.

**11.2 One word, one meaning.** One word has one meaning in the whole repository [TS L337–340]; a term of clause 3 is used
only as defined there.
> *Means* — [TS L337–340]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — review. *Brief* — One
> word, one meaning; a term this standard defines means only that.

**11.3 Orientation documents.** Keep the orientation document short; give it a bird's-eye view, a map of the code, and
the concerns that cut across it [mk-arch L20, L26–32]. Name files, modules and types rather than linking to lines,
because links go stale [mk-arch L37]. Write down the invariants, above all the "X never happens" ones [mk-arch L41–42].
Attach to a claim what it was written against, and to a decision what would overturn it.
> *Means* — [mk-arch L20]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — review. *Brief* — Keep
> orientation documents short; name files rather than linking lines; write down the "X never happens" invariants; date
> claims, and give decisions what would overturn them.

## 12. Bindings, briefs and vendoring

12.1 **A binding** is one document in a repository that uses this standard. It opens with a header in an HTML comment:

```
<!-- binding
title: <name of the repository's standard>
object: <path to the vendored copy of this object>
object-manifest: <SHA-256 of that copy's MANIFEST>
modules: <module names, space-separated>
brief: <path where the brief is written>
meaning: <path of a document that gives the repository its meaning> <its SHA-256>
-->
```

`meaning` may repeat. After the header the binding says what the repository persists and how (4.3), where coordination is
spent (4.6), what each requirement means there (a table from requirement ID to the repository's decisions), its own
requirements with their own IDs, the checks it has, its open questions, and its known departures from this standard, each
dated.

12.2 **The brief** is generated, never written by hand: `tools/standard.py brief BINDING --write`. It holds the *Brief*
line of every requirement of this standard, of the modules the binding names, and of the binding, and every
`<!-- brief: NAME -->` block of those documents: blocks named `before: NAME` open the brief, blocks named
`last: NAME` close it, and the rest follow the requirements. It names the object and the binding it came from, by hash. The brief is
what is given to every session and agent; the full texts are read when a line is unclear.

12.3 **Vendoring.** A repository copies this object's directory into itself. The copy's identity is the SHA-256 of its
`MANIFEST`; `tools/standard.py check BINDING` fails when a member of the copy differs from `MANIFEST`, when the binding
pins another manifest, when a meaning document has changed since the binding was reviewed, and when the brief differs from
what the object and binding generate. Each of these is fixed by reviewing, then running `tools/standard.py pin BINDING`
and copying the pins it prints into the header, then regenerating the brief.

12.4 **Sources** are not vendored. `tools/standard.py fetch` puts them in a cache outside every repository, each file
named by its SHA-256; the quotation check (13.3) reads them there and reports that it could not run when they are absent.

12.5 **Questions.** `questions.json` is a member of the object: the six axes' questions (Annex C), each with a group,
a clause, and the form and arity of the referent it wants. `tools/standard.py questions schema|text|task` are pure
functions of it alone: the JSON Schema an agent answers against, the text of the eval's `questions` arm, and the
paragraph a task appends to ask for a record (13.7).

## 13. Checks

13.0 A check is listed only once it exists; "planned" means it does not, and the requirements it serves are advice until
it does. The binding lists the repository's own checks, in the same form.

| | Check | Serves | Status |
|---|---|---|---|
| 13.1 | `MANIFEST` matches every member of the object | 12.3 | exists |
| 13.2 | Every key cited has a row in `sources/INDEX.md`, and every row is cited | 2.2 | exists |
| 13.3 | Every quotation in clause 3 occurs in the source it cites, in the cached bytes whose SHA-256 is pinned | 2.2, 3 | exists |
| 13.4 | Every requirement has a *Brief* | 12.2 | exists |
| 13.5 | The binding pins the vendored object and the present meaning documents; its brief is byte for byte what they generate | 12.3 | exists |
| 13.6 | The object's own tool meets this standard: controls in `tests/` show each check above able to fail | 4.5 | exists |
| 13.7 | `questions.json` is canonical, names only real clauses, and Annex C is its rendering | 12.5 | exists |

## 14. Revision

This standard is changed when a requirement is shown to be wrong, unmet or unused. A change says what showed it. A
requirement with no check that nothing has exercised by the next revision is deleted.

## Annex A (informative) — TigerStyle, rule by rule

| TigerStyle | Lines | Here | Reason |
|---|---|---|---|
| Safety, performance, developer experience, in that order | L21–23 | adopted | 4.8 |
| Zero technical debt | L62–79 | adapted | solve it, or write it down where it will be met (4.8) |
| Simple, explicit control flow; no recursion | L90–91 | adapted | recursion with an asserted depth limit that refuses (10.1) |
| A minimum of excellent abstractions | L91–94 | adopted | 10.5 |
| Put a limit on everything; fail fast | L96–100 | adapted | own work fails fast; a bound met while observing is a value (5.1, 10.1) |
| Explicitly sized integer types | L102 | adopted where the language has them | language modules |
| Assertions detect programmer errors; operating errors are handled | L104–107 | adopted | 3.54, 9.1 |
| Two assertions per function on average | L112–113 | not adopted as a number | its reason is a simulator that drives the assertions; where a repository has one, its binding may adopt the number |
| Pair assertions; positive and negative space; split compound assertions; assertions as documentation | L115–140 | adopted | 10.2 |
| Compile-time assertions | L128–134 | adopted where the language has them | language modules |
| Static allocation after startup | L151–156 | not adopted | most languages here allocate implicitly; the bound is on work instead (10.1) |
| Smallest scope; 70 lines; hourglass shape; centralize control flow | L158–172 | adopted | 10.3–10.5 |
| Centralize state manipulation; leaf functions pure | L173–175 | adopted | 10.4 |
| Compiler warnings at the strictest setting | L177 | adopted | language modules |
| Run at your own pace, not in reaction to external events | L179–183 | adapted | adopted where the program drives its own work; code that is itself an event handler cannot, and its binding says so |
| Compound conditions; positive invariants; handle all errors; say why; explicit options | L187–229 | adopted | 9.2, 10.3, 10.5, 10.7 |
| Performance in design; back-of-the-envelope sketches; slowest resource first | L236–247 | adopted | 10.8 |
| Control plane and data plane; batching; CPU as sprinter; hot loops | L249–264 | not adopted as universal | a binding adopts them where the work is CPU- or I/O-bound |
| Naming | L273–347 | adopted, Zig specifics dropped | 10.6 |
| Commit messages; say why; say how; comments as sentences | L356–370 | adopted | 10.7 |
| No duplicated variables or aliases | L374–375 | adopted | 10.4 |
| Pass large arguments by const pointer; in-place initialisation | L377–414 | language modules | Zig-specific as written |
| Shrink scope; place of check to place of use | L416–424 | adopted | 3.39, 10.4 |
| Simpler return types | L426–429 | adopted | 9.4 |
| Run to completion without suspending | L431–433 | adapted | in async code an assertion made before an `await` is not relied on after it |
| Buffer bleeds | L435–438 | adopted | 8.7 |
| Group allocation and release | L440–441 | adopted | language modules |
| Index, count, size; explicit division | L445–454 | adopted | 10.6 |
| `zig fmt`, 4 spaces, 100 columns, braces | L458–472 | adapted | a formatter and 100 columns, per language module |
| Zero dependencies | L476–479 | adapted | 10.9 |
| Standardise on Zig for tooling, no shell scripts | L483–500 | adapted | its reason is portability to Windows; a POSIX-only repository keeps shell for starting programs (10.9) |

## Annex C (informative) — questions for reading any code

<!-- brief: last: Before calling work done -->
1. State: what persisted state does it touch, and does it change only as the binding says?
2. Transformation: does any answer depend on more than recorded state and arguments?
3. Effect: which one kind of effect does it do, and where does each failure go?
4. Semantics: which document gives it its meaning?
5. Verification: what would show it wrong?
6. CALM: does a conclusion depend on absence? Is its scope closed? Could more input withdraw it?
<!-- /brief -->
