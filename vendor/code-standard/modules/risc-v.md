# Module RV — RISC-V (RV64)

For code that runs on 64-bit RISC-V under Linux. What the standard's requirements mean on this machine and the
machine's own rules, with the reasons. A binding that names this module says which profile it builds for (RV.1), which
cores it measures on (RV.9) and which rules it checks; the rest is advice. Vendors publish far less about their cores
than Intel, AMD or Arm do; where a number below is a third party's measurement or a vendor's claim, that is said.

## The machine

RISC-V is a contract with optional clauses: a small integer base and named extensions, and a machine is whatever its
ISA string says. Five facts drive the rest.

- **The target is a profile, not an ISA.** RVA23, ratified 2024-10-21 [RVI-rva23], mandates the vector extension,
  bit manipulation, `Zicond`, `Zfa`, the cache-block operations and more [RVA23]; it is the baseline of current
  distributions. Anything beyond the profile is discovered at run time through `riscv_hwprobe` [Lx-hwprobe]. Most
  boards in developers' hands are not RVA23: the P550 has no vector unit (Lam, Chips and Cheese, 2025-01-26).
- **Vectors are length-agnostic; their prices are not.** One `vsetvli` loop runs unchanged on a 128-bit and a 256-bit
  machine, but the same instruction differs by an order of magnitude between cores and by sixty-four times across LMUL
  on one core [RVVB-x60] [RVVB-p870].
- **There is no flags register.** Compares write a register and branches compare two registers, so carry and overflow
  cost extra instructions [RV-rv32], and a double-word add is seven instructions against two on x86 or Arm
  [Granlund21].
- **The memory model is weak, multi-copy-atomic and formally specified**, with executable models in the
  specification itself [RV-rvwmo]. It is in Arm's class, not x86's.
- **Legal is not fast, and the ISA string does not say which.** Misaligned loads are legal under `Zicclsm`, yet the
  specification warns they may execute extremely slowly [RV-zicclsm]; on the P550 one costs about a thousand cycles
  (Lam, Chips and Cheese, 2025-01-26). In June 2026 RISC-V International's chief architect proposed performance-guidance options, `Oilsm` and
  `Ovlt`, to close that gap in future profiles [Asanovic26].

The style that follows: target a profile and detect beyond it; write vector code once for every length but choose
LMUL and permutations by the slowest target's price list; express selects without branches where the profile allows;
treat alignment, vector length, instruction-cache coherence and every extension as a claim to check, never a default.

## Requirements

**RV.1 A profile named, everything beyond it detected.** Code shall be built for a named profile (`RVA23U64` for new
work) and shall use anything beyond it only behind `riscv_hwprobe` [Lx-hwprobe], never behind `/proc/cpuinfo` or a
caught `SIGILL`: T-Head cores implement a pre-ratification vector extension under the standard encodings, which the
kernel reports only as a vendor extension [Lx-hwprobe]. Each file that assumes an extension states it in its header, as
BLAKE3's RVA23 kernel states V, `Zvbb`, `Zbb` and misaligned vector access [B3-rv]. On a system with unlike harts,
`hwprobe` answers with the logical AND of the CPUs asked about [Lx-hwprobe], and the kernel enables `cbo.zero` for user
space only when every hart has it [Lx-rv-cpufeature L1224–1229]; a probe of one CPU set holds only for threads pinned
to it. Vector state is enabled per process and vector registers are clobbered by system calls [Lx-rv-vector].
> *Means* — 4.5, 5.3 [RVA23] [Lx-hwprobe]. *Governs* — effect. *CALM* — not applicable. *Checked by* — the build's
> `-march` recorded in the binding; a scan for `SIGILL` handlers and `/proc/cpuinfo` reads. *Brief* — Build for a named
> profile; use anything beyond it only behind `hwprobe`, with a tested fallback; state ISA assumptions in the file.

**RV.2 A vector loop is written once, under the specification's freedoms.** A strip-mined loop shall use the `vl` that
`vsetvli` returned: when the remaining count is between one and two vector lengths the hardware may return any value
from half of it up to the maximum, to balance the last two strips [RV-vector]; the specification's own `memcpy` is the
shape [RV-memcpy]. Tail-agnostic and mask-agnostic mean unspecified, not unchanged: those elements may keep their old
value or become all ones [RV-vector]; `tu` is used exactly where the old tail must survive, as simdutf's ASCII
validator ORs every strip into one accumulator [Simdutf-rvv L1–13], and `ta, ma` everywhere else, because undisturbed
policies make the hardware read the destination [RISE]. Data-dependent exits use fault-only-first loads [RV-vector].
The loop is run under QEMU with `rvv_vl_half_avl`, `rvv_ta_all_1s` and `rvv_ma_all_1s` [QEMU-cpu L2976–2979] and at
vector lengths 128, 256 and 512; vector-length-specific code dispatches on `vlenb` and never runs on a narrower machine.
> *Means* — 4.5, 10.10 [RV-vector] [QEMU-cpu]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — the
> QEMU properties above in the test matrix. *Brief* — Use the `vl` the hardware returned; agnostic means unspecified;
> `tu` only where justified; pass under QEMU's spec-freedom switches at three vector lengths.

**RV.3 LMUL and permutations are priced.** Element-wise streaming work shall use a high LMUL, as the kernel's vector
copy and glibc's `memset` use `e8, m8` [Lx-rv-usercopy L38–60] [Glibc-rv-memset L36–52]. Anything that permutes across
lanes (`vrgather`, `vcompress`, slides) shall use LMUL 1 or be split into LMUL-1 pieces, because a gather's cost grows
with the square of LMUL: 4, 16, 64 and 256 cycles at LMUL 1, 2, 4 and 8 on the X60 [RVVB-x60]; simdjson's back end
builds its wider gathers from LMUL-1 gathers for exactly this reason [SJ-rvv L10–28]. Strided accesses are slow on every
core measured, and pathological on the P870, so arrays of structures are split with segment loads [RVVB-p870]
[RVVB-x100]. A result crosses to a scalar register at most once per strip, since the move costs cycles and mask work
belongs in mask registers [Bernstein-gaps]. `vxrm` and `frm` are not written inside a loop: the compilers model a
pipeline flush on the shipping cores [LLVM-rv-procs].
> *Means* — 10.8 [RVVB-x60] [RVVB-p870]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — the
> LMUL of each permutation justified by a named core's numbers; review. *Brief* — High LMUL for element-wise work; LMUL 1
> or split for gathers and slides; segment loads, not strided; one scalar crossing per strip; no CSR writes in loops.

**RV.4 Scalar code uses the profile's idioms and is scheduled for a narrow core.** Scalar code shall use what the
profile mandates: `Zba` scaled adds for indexing, `Zbb` for `orc.b`, `rev8`, rotates, `clz` and `ctz`, as the kernel's
`strlen` finds a terminator in a four-instruction loop [Lx-rv-strlen]; `Zicond` for a select in two or three
instructions [RV-zicond], with the caution that a branchless select lengthens the critical path and that SiFive's
in-order cores already predicate a branch over one instruction [RISE] [LLVM-rv-features]. Overflow and carry are
written with the specification's idioms [RV-rv32]; a wide multiply writes `mulh` then `mul` in that order so cores can
fuse the pair [RV-m]; integer division never traps, so a zero divisor is checked where a trap was expected [RV-m];
indices are `size_t`, because 32-bit values are kept sign-extended and unsigned ones cost an extension. Most silicon in
the field is in-order and dual-issue, with one outstanding miss on the U74 [U74], so loop-carried chains are broken with
several accumulators, loads are hoisted, load→address→load chains are avoided, and unrolling is the programmer's
decision, since nearly every vendor's compiler model disables it by default [LLVM-rv-procs].
> *Means* — 10.8 [RV-rv32] [RV-m] [U74]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — the
> bottleneck named with the measurement (10.8); a build with the target's `-mtune`. *Brief* — `Zba`, `Zbb`, `Zicond` as
> the profile gives; `mulh` then `mul`; division by zero checked; `size_t` indices; scheduled for in-order dual-issue.

**RV.5 Atomics: an AMO where possible, a constrained loop otherwise.** Read-modify-writes shall be AMO instructions,
which complete near the data and always make progress; byte and half-word forms need `Zabha` and compare-and-swap needs
`Zacas`, both profile options, so the kernel falls back to a masked word loop preceded by a write prefetch
[Lx-rv-cmpxchg L19–58]. The memory-order mapping is the psABI's, including the trailing fence after a seq_cst store
that keeps future mappings compatible [psABI-atomic]; a hand-written mapping is a hazard. An LR/SC loop is guaranteed
to progress only when it is constrained: at most sixteen instructions, base integer only, no loads, stores, backward
branches or calls between the pair, and the retry under the same rule [RV-zalrsc]; the compiler expands its own such
loops at the last moment so nothing can break them [LLVM-rv-lrsc], and inline assembly keeps the same discipline by
hand, with a detected fallback where it cannot. Waiting uses `pause`, or `wrs.nto` on the reservation set where
`Zawrs` is present [Lx-rv-cmpxchg]. `Ztso` is not assumed: a binary written for it will not run correctly on a machine
without it, and it is not in RVA23 [RV-ztso]. A new synchronisation idiom is checked against the herd model before a
board [RV-rvwmo].
> *Means* — 3.45, 4.6 [RV-rvwmo] [RV-zalrsc] [psABI-atomic]. *Governs* — effect. *CALM* — needs closure: an ordering
> constraint is coordination, spent only where the binding names it. *Checked by* — a litmus test per new protocol; a
> scan of inline assembly between `lr` and `sc`. *Brief* — AMOs first; the psABI mapping; LR/SC loops constrained to
> sixteen base instructions with a fallback; never assume `Ztso`; new idioms checked on the model.

**RV.6 Alignment is a claim, not a default.** Hot data shall be aligned, and a misaligned access shall be treated as
slow unless `hwprobe` reports the misaligned class as fast, which is the condition under which glibc selects its
unaligned `memcpy` [Glibc-rv-memcpy L35–45] [Lx-hwprobe]: legal under `Zicclsm` [RV-zicclsm], about 1,062 cycles for a
load on the P550, which traps and emulates (Lam, Chips and Cheese, 2025-01-26), and a trap on the U74 [U74]. A misaligned atomic is always a
bug. A misaligned vector access needs `Zicclsm`; without it the result is `SIGBUS`, not a slow path [Lx-uabi]. Packed
records are read with byte loads or `memcpy` unless the probe says fast. The proposed `Oilsm` option would one day make
"misaligned is faster than avoiding it" a guarantee [Asanovic26]; until a profile mandates it, this rule stands.
> *Means* — 10.2 [RV-zicclsm] [Lx-hwprobe]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — an
> alignment assertion on atomics; `hwprobe` consulted before any unaligned fast path. *Brief* — Align hot data;
> misaligned is slow unless `hwprobe` says fast; a misaligned atomic is a bug; misaligned vector needs `Zicclsm`.

**RV.7 Code that writes code, and cache operations, go through the kernel's interfaces.** A program that writes
instructions shall synchronise through `__builtin___clear_cache`, the `riscv_flush_icache` system call, or the
per-thread `prctl` that makes a user `fence.i` valid, never a bare `fence.i`: the instruction orders only the local
hart's fetches, and a thread migrated after it lands on a hart whose instruction cache is not clean [Lx-cmodx]
[Lx-hwprobe]. The draft `Ziccid` extension would make stores visible to fetch without it, aimed at JITs, and is not yet
a profile mandate [RV-ziccid]. Cache-block operations take their block size from `hwprobe`, are not ordered by `fence.i`
or `sfence.vma` [RV-cmo], and user-space invalidation is not enabled by the kernel [Lx-rv-cpufeature].
> *Means* — 8.1 [Lx-cmodx] [RV-cmo]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a scan for `fence.i`
> in user-space code. *Brief* — JITs flush through the kernel interface, never a bare `fence.i`; cache-block ops take
> their size from `hwprobe`.

**RV.8 Floating point: canonical NaNs, saturating conversions, one reduction order.** Code shall not depend on NaN
payloads: arithmetic that produces a NaN returns the canonical NaN, and only loads, stores and sign-injection preserve
bits [RV-f], so a runtime that boxes values in NaNs never routes them through arithmetic. Hand-written assembly that
moves a narrower value into a wider register sets the upper bits to one, or the value is treated as NaN [RV-f].
Out-of-range conversions saturate and NaN converts to the largest integer, where x86 gives its indefinite value [RV-f];
`fmin` and `fmax` follow IEEE 754-2019 and `Zfa` adds the propagating forms and a modular conversion for JavaScript
[RV-zfa]. Contraction is decided as in X86.8, since every RV64GC target fuses and baseline x86-64 does not [GCC-opt].
The ordered vector reduction is deterministic and the unordered one may use any tree, fixed per implementation and
vector length, so a length-agnostic reduction gives different bits on different machines [RV-vector].
> *Means* — 3.60 [RV-f] [RV-vector]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — a golden-value
> test at two vector lengths and against x86. *Brief* — No NaN payloads; narrow values NaN-boxed in assembly;
> conversions saturate; contraction by decision; `vfredosum` where bits must reproduce.

**RV.9 Measure on named silicon, in the order of the evidence.** A performance claim shall be measured on a named
core, never under QEMU or Spike, which decide correctness and say nothing about time. Sampling needs counter-overflow
interrupts, which the U74 lacks and the X60 has on three counters only [Batashev25]; a bare `rdcycle` traps in user
space under the kernel's default, and cycles come through `perf` [Lx-sysctl]. When guides are scarce the sources are
consulted in order: the vendor's manual where one exists [U74]; the vendor's own scheduling model and tuning flags in
the compiler, which are its statement of costs [LLVM-rv-procs] [LLVM-rv-features]; rvv-bench's measured tables
[RVVB-x60] [RVVB-x100] [RVVB-c920v2] [RVVB-p870]; independent microbenchmarks (Lam, Chips and Cheese, 2025-01-26); then a microbenchmark of
one's own. A vendor's SPEC-per-gigahertz figure is a claim. Measure on at least one in-order and one out-of-order
core.
> *Means* — 10.8 [Batashev25] [Lx-sysctl]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a measurement
> record naming the core, kernel and counters. *Brief* — Time only on named silicon; QEMU decides correctness; cycles
> through `perf`; evidence in order: manual, compiler model, rvv-bench, independent measurement, your own.

**RV.10 Provenance stays clean, and the tools' gaps are known.** Pointers shall not be hidden in integers, XORed, or
round-tripped through `long`: pointer masking (`Supm`) carries HWASan today [Lx-uabi], and CHERI arrives as new base
ISAs, RV32Y and RV64Y, whose specification is stable and not yet ratified, under which a pointer is a 16-byte tagged
capability and a forged one faults [CHERI]. The tools' coverage is known and written into the binding: the sanitizers
support riscv64 except MemorySanitizer [CompilerRT L89]; Valgrind supports the scalar base since 3.25 and not vector
code [Valgrind-NEWS]; Miri interprets the target but its weak-memory emulation follows C++ and says nothing about RVWMO
[Miri-README]; Rust's Linux target is tier 2 [Rust-rv].
> *Means* — 8.1, 10.9 [CHERI] [CompilerRT]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — HWASan
> in the test matrix; a scan for pointer↔integer casts. *Brief* — Pointers never hidden in integers; HWASan now, CHERI
> later; know that MSan, vector Valgrind and RVWMO-aware Miri do not exist.

## The price list

Reciprocal throughput in cycles per instruction at SEW = 8, read from rvv-bench's measured tables in September 2026;
columns are LMUL 1, 2, 4 and 8. The X60 and X100 have 256-bit vectors, the C920v2 and P870 128-bit, so per element the
first two are half the figure shown.

| Instruction | X60, in-order | X100, out-of-order | C920v2 | P870 | Source |
|---|---|---|---|---|---|
| `vadd.vv` | 1 / 2 / 4 / 8 | 1 / 2 / 4 / 8 | 0.5 / 1 / 2 / 4 | 0.5 / 1 / 2 / 4 | [RVVB-x60] [RVVB-x100] [RVVB-c920v2] [RVVB-p870] |
| `vrgather.vv` | 4 / 16 / 64 / 256 | 2 / 8 / 32 / 128 | 0.5 / 2.4 / 8 / 32 | 1 / 12 / 26 / 68 | same |
| `vcompress.vm` | 3 / 10 / 36 / 136 | 3 / 10 / 36 / 136 | 0.5 / 2.4 / 5.3 / 20 | 1 / 13 / 16 / 22 | same |
| `vredsum.vs` | 2 / 4 / 9.5 / 35 | 1 / 2 / 5.5 / 19 | 1 / 2 / 4 / 8 | 1 / 2 / 4 / 8 | same |
| strided load `vlse8.v` | 32 / 64 / 128 / 256 | 21 / 50 / 114 / 242 | 16 / 32 / 64 / 128 | 19 / 31 / 59 / 123 | same |
| strided store `vsse8.v` | 34 / 67 / 134 / 268 | 33 / 64 / 128 / 256 | 16 / 32 / 77 / 153 | 160 / 320 / 640 / 1279 | same |
| `vmv.x.s`, vector → scalar | 2 | 6 | 0.65 | 2.4 | same |

Scalar facts: the P550 misaligned load about 1,062 cycles and store about 741, trap and emulate (Lam, Chips and Cheese, 2025-01-26); the U74
dual-issue in-order with one outstanding cache-line fill and a trap on every misaligned access [U74]; a double-word add
seven instructions [Granlund21]. The cores in developers' hands are in the Cortex-A76 class in absolute terms; design
for the P870 and Ascalon class, measure on what exists.

## Traps

| Trap | What happens | What the best code does |
|---|---|---|
| `vl` assumed equal to the remaining count | the last two strips may be balanced by the hardware | use the returned `vl`; test with `rvv_vl_half_avl` (RV.2) |
| Tail or masked elements read | they may be old values or all ones | `ta, ma`, or `tu` with a reason; test with the all-ones switches (RV.2) |
| Gather or slide at LMUL 8 | cost grows with the square of LMUL | LMUL 1 or split (RV.3) |
| Strided loads for arrays of structures | slow everywhere, 160 cycles a store on the P870 | segment loads (RV.3) |
| A result to a scalar register per element | cycles per crossing | once per strip, in mask registers (RV.3) |
| `fence.i` in user space | orders one hart; migration leaves a stale cache | the kernel interface (RV.7) |
| Misaligned as a fast path | a thousand cycles or `SIGBUS` | align; ask `hwprobe` (RV.6) |
| `SIGILL` probing for V | T-Head cores execute the encodings with other meaning | `hwprobe` (RV.1) |
| An unconstrained LR/SC loop | may fail forever | sixteen base instructions, a fallback (RV.5) |
| NaN payloads as data | arithmetic canonicalises them | never through arithmetic (RV.8) |
| Timing under QEMU | says nothing about silicon | named cores only (RV.9) |

## Exemplars

- Linux, `arch/riscv/lib/strlen.S` [Lx-rv-strlen]: a boot-time alternative selects the `Zbb` path; aligned word loads
  that cannot cross a page; `orc.b` and `ctz` in a four-instruction loop.
- Linux, `arch/riscv/lib/uaccess_vector.S` [Lx-rv-usercopy L38–60]: the canonical `e8, m8` loop with exception-table
  fix-ups that read `vstart` to learn how much was written.
- Linux, `arch/riscv/include/asm/cmpxchg.h` [Lx-rv-cmpxchg]: graceful degradation from `Zabha` to a masked word loop
  with a write prefetch; waiting with `wrs.nto` or `pause`.
- glibc, `sysdeps/riscv/rvv/memset.S` [Glibc-rv-memset L36–52], selected by a `hwprobe`-aware resolver
  [Glibc-rv-memcpy L35–45]: splat once, strip-mine stores; the unaligned copy only where the probe says fast.
- simdjson, `rvv-vls/intrinsics.h` [SJ-rvv L10–28]: LMUL-2 and LMUL-4 gathers written as independent LMUL-1 gathers.
- simdutf, `src/rvv/rvv_validate.inl.cpp` [Simdutf-rvv L1–13]: an `m8` accumulator with a tail-undisturbed OR.
- BLAKE3, `rust/guts/src/riscv_rva23u64.S` [B3-rv]: a kernel that names its profile and its assumptions in its first
  lines; unmerged since 2024, which says something about the hardware in developers' hands.
- The specification's own `memcpy` [RV-memcpy]: the strip-mined loop in seven instructions.

## Forward look, to about 2031

- RVA23 becomes the floor; the first server-class RVA23 systems appear in 2026, and the chief architect expects
  several generations before parity in the general server space [Asanovic26]. Non-vector paths become fallbacks.
- Performance guarantees join functional ones: `Oilsm` and `Ovlt` are meant to become mandatory in future profiles
  [Asanovic26]. When they do, the guidance on misaligned access and on shrinking LMUL changes from "avoid" to "assume
  the fast path".
- Matrix work: several approaches are in flight; keep GEMM and convolution behind a library interface.
- `Zalasr` removes the fences from plain acquire and release; the draft `Ziccid` would make JIT patching fence-free
  [RV-ziccid]. Both come behind detection.
- CHERI RV64Y is stable and unratified [CHERI]; code with clean provenance ports cheaply.
- Rust's target is tier 2 with a tier-1 proposal open [Rust-rv]; Lean 4 publishes no riscv64 binaries as of September
  2026, so proof tooling on this ISA is a milestone, not a present fact.

## Questions an expert asks of RISC-V code before calling it done

1. Which profile is it built for, and is each use beyond it behind `hwprobe` with a tested fallback?
2. Does every vector loop use the `vl` that `vsetvli` returned, and does it pass under `rvv_vl_half_avl`?
3. Does anything read tail or masked-off elements? Does it pass with the all-ones switches? Is every `tu` justified?
4. Has it run at vector lengths 128, 256 and 512? If it is length-specific, does it dispatch on `vlenb`?
5. What LMUL does each gather, compress or slide use, and is anything above 1 justified by the slowest target's
   numbers?
6. Are there strided accesses where unit-stride or segment accesses would do? Does anything cross to a scalar register
   per element?
7. Is any access misaligned, and was the `hwprobe` class consulted? Is any atomic misaligned?
8. Is each atomic an AMO where possible, with the psABI ordering? Is every LR/SC loop constrained, with a fallback?
9. Does concurrent code assume TSO? Were new idioms checked against the herd model?
10. Does it write code? Then does it flush through the kernel interface and never a bare `fence.i`?
11. Is contraction set deliberately? Any dependence on NaN payloads, x86 conversion values or the unordered reduction's
    tree?
12. Is division by zero checked where a trap was expected? Are overflow and carry written with the ISA's idioms?
13. Is scalar code scheduled for an in-order dual-issue core?
14. Were performance claims measured on named silicon, on at least one in-order and one out-of-order core, with
    counters?
15. Does each file state its ISA assumptions in its header?
16. Is pointer provenance clean enough for HWASan today and CHERI later?

<!-- brief: RISC-V -->
Build for a named profile and detect beyond it with `hwprobe`; write vector loops once, using the returned `vl`, with
agnostic tails treated as unspecified and tested under QEMU's spec-freedom switches at three vector lengths; high LMUL
for streaming and LMUL 1 for anything that permutes; AMOs first and LR/SC constrained; alignment, instruction-cache
coherence and every extension as claims to check; canonical NaNs and saturating conversions; time only on named
silicon; pointers never hidden in integers.
<!-- /brief -->
