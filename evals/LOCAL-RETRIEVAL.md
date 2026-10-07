# Local retrieval for proof workers

The owner prepares one immutable compiled environment. The worker receives a short
packet and may return `search`, `read_declaration`, `check_candidate`, or `blocked`.
It cannot choose a command, path, module, index, URL or compiler. Retrieval remains
advisory; the owner must compile and check any resulting proof.

`retrieval-decoder.json` is the versioned starting formalism for the proposed
decoder bridge. It selects `ECCLib.Decoding`, `FTQCLib.CSS.Distance`, and
`FTQCLib.CSS.SurfaceCode`, named semantic anchors, and the distinction between
classical kernel correction and quantum correction modulo a stabilizer boundary.
These choices are task data rather than branches in the retrieval implementation.

## Preparation and identity

1. `work/prepare_search_modules.py` materializes pinned Git source in a private
   projection and compiles the local import closure sequentially. Each completed
   module records its artifact hashes immediately. Toolchain/package manifests
   are byte-audited before compilation and checked again afterward. Changed or
   unrecorded outputs refuse the final build receipt.
2. `retrieval_snapshot.py` requires that artifact-bound build receipt. It verifies
   the inputs, compiles an owned import root, asks the Lean helper for the actual
   imported environment, and copies exactly that compiled module closure. The
   isolated retrieval process sees only this projection, not a general worktree,
   checker, private examiner or unaccepted candidate directory.
3. Both native executables and the import closure enter the snapshot identity.
   Loogle is pinned to upstream commit
   `9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0`, built using Lean 4.29.1. The only
   upstream patch changes its toolchain pin. The declaration helper uses the same
   Lean version and is linked as a standalone executable.
4. The builder writes an explicit `ontologic-sha256:` dependency digest into the
   generated root's `.trace`. This adapts the harness's immutable identity to
   Loogle's `depHash` cache interface. It is **not a Lake-generated build receipt**.
   Cold index creation is an owner effect with a ten-minute bound and a 12 GiB
   per-process address-space limit; queries use
   `--index-mode read` and cannot create or update the index.
5. Only after every declared anchor resolves does preparation publish
   `snapshot.ref`. A work item must pin that identity. A missing or stale index
   fails explicitly; it must never become an empty search result.

Every snapshot contains its exact file manifest. A backend instance audits the
bytes once, then checks complete metadata before and after each effect. This is
the existing runtime trust model: workers cannot write grants; hostile local OS
users are outside it. Files are copied without shared writable inodes. Original
build objects, source bytes, and subsequent raw query captures remain in Store.

## Worker protocol

An example search proposal is:

```json
{"action":"search","proof":null,"query":"\"IsCosetLeaderMap\"","name":null,"reason":null}
```

A declaration read is:

```json
{"action":"read_declaration","proof":null,"query":null,"name":["ECCLib","Coding","IsCosetLeaderMap"],"reason":null}
```

Names are structured Lean namespace components; they are never interpolated into
Lean source. The worker protocol currently admits ordinary identifier components,
not every possible escaped or internally generated Lean name. The lookup helper
can represent a broader set of string components, but it never imports a module
selected by the worker.

`retrieval_loop.Session` reserves a request before calling
`local_retrieval.Backend.call`. Search and declaration reads share a finite
work-item budget, including cache hits and failed requests. Search queries are
limited to 512 UTF-8 bytes and five hits. Each hit contains its name, module and
bounded type. Declaration reads return the type, origin, docstring and a bounded
definition body; theorem proof bodies are omitted. The selected declaration
result is limited to 8 KiB. Each process has a wall deadline, address-space/output
limits and no network access.

The next model packet carries the immutable obligation, formalism, current
retrieved evidence and latest bounded feedback. It does not replay the whole
conversation. Full results and execution records stay in Store. Repeated queries
reuse a result within one owner process, keyed by snapshot, operation, payload,
result policy and owner code; cache hits point to the original receipt. Receipts
persist across processes, but automatic cross-process query-result reuse is not
implemented. Prepared on-disk indexes do persist.

Keep one backend alive for the owner run. Fresh-process admission byte-audits the
whole snapshot; the measured first admission took 72 seconds. Starting a fresh
backend for every query would repeat that cost. Queries themselves retain a
30-second process deadline and an 8 GiB address-space bound.

## Integration and limits

The historical F01 comparison remains on its original public-Loogle protocol.
Do not attach this decoder snapshot to a withheld-proof reconstruction test:
its admitted baseline legitimately includes already-proved library declarations.
The new protocol and backend are reusable components for the planned real proof
chain. The chain still needs reviewed per-obligation output windows, protected
examiners, failed-approach tracking, and accepted predecessor admission.

After accepting a predecessor, the owner must build a new dependency projection
and publish a new search snapshot. An existing snapshot is never amended. The
current setup command admits the pinned baseline only; it does not yet implement
automatic DAG retirement-to-snapshot publication.

No public-service fallback occurs silently. `evals/loogle.py` remains available
for an explicitly chosen advisory public search. Local retrieval uses the pinned
project environment and runs without network access.

Run `test_retrieval_loop.py` for pure protocol controls. Run
`test_local_retrieval.py --snapshot <directory> --kernel <kernel-repo>
--output <new-results-directory>` for real local search, declaration, caching,
scope-exclusion, immutable-identity, missing/stale-index and shared-budget tests.
The adapter's array-schema and zero-tool checks use a local synthetic provider;
no live model calls are needed for these controls.

## Opt-in typed evidence needs (protocol 3)

`chain_study.py prepare --evidence-needs` pins `policy.protocol = 3` in a new
manifest and its initial Work IR. Omit the flag to retain protocol 2. Existing
protocol-2 manifests and the historical proof/retrieval protocols keep their
schemas and dispatch policy; source-pinned runs still require their original
source bytes. Unknown protocol versions are refused.

`evidence_protocol.py` exposes `SCHEMA`, `INSTRUCTIONS`, `packet(...)`, and
`Session(backend, max_requests, snapshot_id, initial=())`. The model returns six
required fields, without a tool catalogue:

```json
{"outcome":"need","proof":null,"need":"declaration_names","names":["ECCLib.Coding.IsCosetLeaderMap"],"fragment":null,"reason":null}
```

`outcome` is `candidate`, `need`, or `blocked`. A candidate supplies `proof`; a
blocked outcome supplies `reason`. A need supplies either `declaration_names`
and one to four distinct exact `names`, or `name_fragment` and one literal
identifier `fragment`. A need may also supply a bounded explanatory `reason`;
the owner ignores that explanation when resolving evidence. All other inactive
fields are null. Candidate proof and blocked reason bounds are 16384 and 2048
UTF-8 bytes; names are at most 256 bytes each and fragments at most 240 bytes.
Ordinary Unicode identifiers and dots are admitted; quoted Lean names, prose,
paths and query syntax are outside this prototype.

The deterministic owner maps declaration names to its fixed declaration reader
and fragments to a JSON-quoted literal search. Model values never select a
backend, executable, path, or arbitrary query. Protocol 2's receipt validation,
snapshot binding, cumulative evidence, initial-evidence deduplication, cached
request refusal, pre-effect budget reservation, and all-or-none batch admission
are shared. Candidate outcomes still enter the existing protected checker;
returning a candidate alone never establishes proof acceptance.
An unavailable declaration lookup without a name now preserves its backend
status (such as `timed_out`), rather than misreporting a declaration-name mismatch;
successful and missing lookups still require the exact requested name.

Run `python3 -B test_evidence_protocol.py` for scripted owner dispatch and
candidate-check routing, including invalid needs with no effects, literal
quoting, caches, budgets, and optional need explanations. `test_work_program.py`
checks both explicit versions survive the native Work IR round trip. These
scripted controls are not live-model or Lean acceptance evidence.

On 2026-10-07, compact JSON serialization of schema plus UTF-8 instructions was
1555 bytes for protocol 2 (487 + 1068), and 1313 for protocol 3 (553 + 760):
242 fewer bytes. Explicit field assignments were added after a live worker put
its need only in explanatory prose while leaving the selected payload null.
Such requests remain refused before effects. This excludes evidence packets and provider framing. No local
`tiktoken` module was available in the WSL test runtime; no tokenizer estimate or
model-token saving is claimed. The change is a bounded protocol experiment,
not evidence of improved proof success or model cost.
