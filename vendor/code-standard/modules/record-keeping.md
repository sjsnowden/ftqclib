# Module RK — record-keeping

For a repository whose persisted state is a record that only accumulates: content-addressed objects, a log of entries
that name their parents by hash, and one overwritten cell, the head, that vouches for the log. A binding that names this
module adopts its model and its requirements. Terms are those of the standard's clause 3.

RK.0 **The model.** Recorded state has four shapes.

| Shape | What it is | How it changes |
|---|---|---|
| object | bytes named by their SHA-256 (3.4, 3.5) | put once, never changed |
| entry | a record in the log: its writer, its parents by hash, the event, the state after (3.7, 3.8) | appended, never changed |
| head | the one value held outside the log (3.14) | replaced atomically by its one writer |
| derived file | a stored view (3.9) | rebuilt or deleted at will |

A binding that adds a shape says so, with its rule. The entries of a log are a set: taking in another store's entries is
a union, and union is a join (3.18), so two stores holding the same entries hold the same set whatever the order they
arrived in. A **line** is one writer's entries from its start to its end; its end is its manifest (3.47), and a scope made
of lines is closed (3.48) when every line in it has ended. Coordination (3.45) is spent at the head, which has one writer,
at a line's end, and at any other place the binding names.

<!-- brief: before: Record-keeping (module RK) -->
- Recorded state has four shapes (RK.0): an object, put once under its hash; an entry, appended; the head, the one
  overwritten cell; a derived file, rebuilt or deleted at will. Nothing else is recorded state.
- The log's entries are a set; taking in entries is a union. A line's end closes it. Coordination happens at the head,
  at a line's end, and where the binding says, nowhere else.
<!-- /brief -->

**RK.1 Accumulate only.** Recorded state shall change only by putting an object under its hash, appending an entry, or
replacing the head. Nothing recorded is rewritten, truncated or deleted, except bytes after the last whole entry of a log
cut short, which are moved aside and kept.
> *Means* — 3.2, 3.7 [Kreps13]. *Governs* — state. *CALM* — monotonic. *Checked by* — a scan for opens for writing under a
> store other than an exclusive create, an append to the log, and the head's replacement. *Brief* — State changes only by
> a put, an append, or replacing the head; nothing recorded is rewritten or deleted.

**RK.2 One overwritten cell.** The head is the only recorded value that is overwritten, and it shall be replaced as the
standard's 6.2 says.
> *Means* — 3.12, 3.14 [POSIX-rename DESCRIPTION]. *Governs* — state. *CALM* — needs closure: replacing the head is
> coordination, and it has one writer. *Checked by* — the scan of RK.1. *Brief* — The head is the only overwritten cell;
> replace it atomically (6.2).

**RK.3 Facts are created, never reopened.** A file that holds recorded facts — an object, a tail moved aside, a run's
record — shall be created so that creation fails if the name exists, under a name that cannot collide with another.
> *Means* — 3.4 [Venti p.3]. *Governs* — state. *CALM* — monotonic. *Checked by* — the scan of RK.1. *Brief* — Create a
> file of facts exclusively, under a name that cannot collide; never reopen it for writing.

**RK.4 Record every nondeterministic input.** The clock, randomness, model output and the order in which concurrent
things happened shall be recorded where they are used and never read again, so that replaying the record reaches the
recorded state (3.25).
> *Means* — 3.8 [Fowler05], 3.25 [Floyd67 p.1]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a replay that
> reaches the recorded state. *Brief* — Record every nondeterministic input where it is used; never read it again.

**RK.5 Record before the effect.** Where the design puts the record before what it describes, the entry shall be durable
before the effect begins (3.11).
> *Means* — 3.10 [Gray81 p.3], 3.11 [ARIES p.4]. *Governs* — effect. *CALM* — not applicable. *Checked by* — fault
> injection between the record and the effect. *Brief* — Where the design puts the record first, make it durable before the
> effect begins.

**RK.6 One encoding.** Records shall be built only through one encoder. Every value has one byte encoding (3.3); a set is
sorted by encoded bytes, with no repeats; no field name appears twice in a record.
> *Means* — 3.3 [Rivest97 §6.1], 3.6 [Merkle79 p.24]. *Governs* — state. *CALM* — not applicable. *Checked by* —
> conformance vectors and differential testing of independent parsers (3.58). *Brief* — Build records only through the
> encoder: one encoding per value, sets sorted and unique, no field twice.

**RK.7 A merge is over a set.** A merge shall be computed from the set of all its inputs at once, never by folding two at
a time. Repeating an input or changing their order shall not change the result (3.18).
> *Means* — 3.18, 3.19 [CRDT p.5]. *Governs* — transformation. *CALM* — monotonic in the log. *Checked by* — laws (3.56):
> order and repetition of inputs leave the result unchanged. *Brief* — Merge the whole set of inputs at once, never two at
> a time; order and repeats change nothing.

**RK.8 Disagreement is a value.** Where the inputs of a merge disagree, it shall return a state that holds all of them (a
conflict), as a multi-value register does (3.20). It shall not raise, and it shall not choose by rule or by time.
> *Means* — 3.20 [CRDT-TR p.23]. *Governs* — transformation. *CALM* — monotonic. *Checked by* — laws on conflicting
> inputs. *Brief* — Disagreement is a value, a conflict holding every side; never an error, never a choice by rule or time.

**RK.9 Invariants across a merge.** An invariant that must survive a merge shall be invariant-confluent (3.21). An
invariant that is not becomes a state (RK.8) or a decision made at the head.
> *Means* — 3.21 [Bailis15 p.5]. *Governs* — transformation. *CALM* — an invariant that is not confluent needs
> coordination. *Checked by* — advice. *Brief* — An invariant that must survive a merge is invariant-confluent, or becomes a
> state, or is decided at the head.

**RK.10 Nothing after the end.** The entry that ends a line shall be written only after every task of that line's work
has ended and been reaped (8.5), and no entry of the line shall follow it.
> *Means* — 3.47, 3.48 [CALM p.4]. *Governs* — effect. *CALM* — needs closure: the end is the line's manifest.
> *Checked by* — a check that refuses a log with an entry after its line's end. *Brief* — Write a line's end only after every
> child is reaped; nothing of that line follows it.
