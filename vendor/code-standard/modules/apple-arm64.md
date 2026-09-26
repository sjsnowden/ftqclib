# Module AA — Apple arm64

For code that runs on Apple silicon (M1 to M6, A14 onward) under macOS. What the standard's requirements mean on this
machine and the machine's own rules, with the reasons; Arm's server cores are not covered here. A binding that names
this module says which generations it measures on (AA.9) and which rules it checks; the rest is advice. Apple publishes
its CPU optimisation guide only to a registered developer who accepts an additional agreement [Apple-guide], so every
public number for these cores is a third party's measurement with a named measurer; the M1 performance core is the best
measured and is the baseline below.

## The machine

- **Very wide, very deep, sparsely documented.** The M1 performance core decodes eight instructions per clock behind a
  window of about 630 [Anand-M1]; Johnson measures six integer, four load/store and four SIMD units, and a renamer that
  removes register moves, zeroing and `nop` before they issue [DJ]. Width comes from many pipes, not from long vectors.
  Since 2026 there are three core tiers: M5 Pro and Max add super cores beside performance cores [Apple-M5Pro], and M6
  has super, performance and efficiency cores [Apple-M6]. Code that assumes "P and E" is already out of date.
- **Every general-purpose vector is 128 bits.** NEON is the vector ISA. There is no SVE outside streaming mode; SME2 on
  M4 and later runs on a per-cluster unit fed through L2, and a plain vector instruction in streaming mode is slower
  than its NEON form [Zakharko] [Jena-SME].
- **The memory model is weak but multicopy-atomic, with acquire and release in the ISA** [Pulte18 p.1]; its executable
  form is Arm's `aarch64.cat` [AArch64-cat]. Code that was correct only under x86-TSO, or only because `LDAR` is
  stronger than C++ `acquire`, breaks here (AA.2, AA.3).
- **The environment's constants are variables.** Pages are 16 KiB; the coherence granule is 128 bytes, which is why
  Clang sets the destructive interference size to 128 for Apple cores [Clang-AArch64 L335–339]; there is no user-visible
  CPU affinity, and quality of service is the only lever [Apple-tuning]; the ABI differs from AAPCS64 [Apple-abi];
  features differ by generation and are asked for through `sysctl` [Apple-isa] [Apple-caps].

## Requirements

**AA.1 Ask the system for every constant.** Page size, line size, the number of core tiers and cores per tier
(`hw.nperflevels`, `hw.perflevelN.*` [Apple-caps]), and every optional feature (`hw.optional.arm.FEAT_*` [Apple-isa])
shall be read at run time, never written as numbers. Padding against false sharing is 128 bytes
[Clang-AArch64 L335–339]. Allocators and mappings assume 16 KiB pages and segments aligned to them, which is where
software ported from 4 KiB systems broke on this hardware [Asahi-broken].
> *Means* — 5.3, 10.6 [Apple-caps]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a scan for the literals
> 4096, 64 and a core count in code that runs here. *Brief* — No hard-coded page size, line size, core count or tier;
> ask `sysctl`; pad at 128 bytes; assume 16 KiB pages.

**AA.2 The access carries the order.** Cross-thread communication shall be an atomic with the weakest correct order,
expressed on the access itself: `LDAR` or `LDAPR` for acquire, `STLR` for release, LSE instructions for
read-modify-writes. Seq_cst is also `LDAR` and `STLR`, because a store-release is observed by every core before a later
load-acquire; `LDAPR` drops exactly that guarantee, which is why it is legal for `acquire` and not for `seq_cst`
[Arm-SC]. A `dmb` is written only where no single access can carry the order: the store→load pattern between relaxed
accesses, many earlier loads before one later access, DMA, or system-register effects; never "to be safe". The kernel's
full barrier is `dmb ish` and its release and acquire are single instructions [Lx-arm64-barrier]; its wait sleeps in
`wfe` on the exclusive monitor rather than spinning [Lx-arm64-cmpxchg]. Uncontended ordering has a price even here:
`cas` 3 cycles against `casal` 7 on M1 [DJ-int]. 16-byte atomics rest on `FEAT_LSE2`, detected, not assumed
[Apple-isa].
> *Means* — 3.45, 4.6 [Pulte18] [AArch64-cat]. *Governs* — effect. *CALM* — needs closure: an ordering constraint is
> coordination, spent only where the binding names it. *Checked by* — TSan on this machine; a herd7 litmus test with
> `aarch64.cat` for each new protocol; a C11 model checker. *Brief* — Acquire and release on the access, weakest correct
> order; `dmb` only where no access can carry it; LSE atomics; LSE2 for 16 bytes, detected.

**AA.3 Correct under the weak model, not under Rosetta's.** Native code shall be correct under the Armv8 model. The
hardware's total-store-order mode is a per-thread setting that macOS turns on for translated processes and that Apple
exposes to Linux guests only to speed up Rosetta [Apple-vmtso]; it is not part of the architecture [DJ-rosetta]; native
code has no interface to it; and macOS 27 is the final release to run Intel-only apps [Apple-rosetta-end]. Two incidents
show what breaks. Linux's `test_and_set_bit` returned early, without ordering, when the bit was already set: harmless on
x86, where every locked operation is a full barrier, and it lost TTY data on M1 [Martin-TTY] [Lx-415d8324]. DPDK's ring,
correct C11 that had only ever run under `LDAR`, broke when compilers began emitting `LDAPR` for `acquire`; herd7
reproduced the outcome under RCpc and not under RCsc [Arm-partial]. Neither "works on x86" nor "works on arm64 today" is
evidence; the model is.
> *Means* — 4.5 [Pulte18] [Arm-partial]. *Governs* — effect. *CALM* — not applicable. *Checked by* — the checks of AA.2,
> run on Apple hardware. *Brief* — Correct under the weak model; TSO is Rosetta's, not yours; test on the model and on
> this machine.

**AA.4 Keep work in one register file, and reduce once.** A hot loop shall not cross between general and vector
registers on every iteration: a vector→GPR move costs up to 10 cycles on M1 [DJ], which is why simdjson computes its
prefix XOR with scalar shifts and leaves `PMULL` alone [SJ-arm-bitmask L17–38]. Accumulators stay in vectors and are
reduced once, with at least latency × pipes of them: `fmla` is 4 cycles on four pipes, so sixteen [DJ-simd]. Selects
are `csel`, `csinc` or `ccmp` where the predicate is unpredictable and a branch where it is not. Scaling belongs in the
address, where the load unit shifts for free, not in the ALU, where a shifted operand costs 2 cycles [DJ-int]. Loads
and stores go in pairs from one base, bumped once per unrolled block. Constants beyond the 12-bit and logical
immediates are hoisted into the 32 vector registers, since the renamer removes only two `mov #imm` per eight
instructions and does not fuse `mov` with `movk` [DJ].
> *Means* — 10.8 [DJ]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — the bottleneck named with
> the measurement (10.8); review. *Brief* — No GPR↔vector crossing per iteration; reduce once; accumulators ≥ latency ×
> pipes; `csel` only where unpredictable; scaling in the address.

**AA.5 NEON is the vector ISA; matrices go through Accelerate or SME outer products.** Vector code shall be NEON:
`tbl` as a 16 to 64-byte table lookup at 2 cycles [DJ-simd]; pairwise and narrowing ops for masks; the `shrn #4`
four-bit syndrome in place of `pmovmskb`, which gained 10 to 15 percent on `strlen` [Arm-bitmask]; an integer `umaxv`
rather than a float compare, because flush-to-zero would treat a denormal as zero [SJ-arm-simd L121–144]. Nothing
assumes SVE or its width. Matrix work goes through Accelerate, which Apple names as the alternative to
processor-specific vector code [Apple-diff], or through SME2 where the kernel is your own, and then only for outer
products and ZA-accumulated multi-vector ops: on M4 one performance core reaches 107 GFLOPS with NEON `fmla`, 31 with
the same instruction in streaming mode, and about 2,000 with `fmopa` [Jena-SME].
> *Means* — 10.8, 10.9 [Jena-SME]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — review; a
> streaming-mode kernel is justified by its own measurement. *Brief* — NEON, `tbl` tables and the `shrn` syndrome; no
> SVE assumptions; matrices through Accelerate or SME outer products, measured.

**AA.6 Scheduling is the system's.** Every thread and queue shall carry a quality-of-service class; there is no
affinity interface, and the system places background work on the slower cores [Apple-tuning]. Parallel work is
over-decomposed, at least three times the number of cores in Apple's words, because static partitions finish at
different times on different tiers; spin-waits are removed rather than tuned [Apple-tuning]. libdispatch's own wait
states the preconditions that make it safe, spins at most 1024 yields, then makes a directed yield to the kernel
[Libdispatch-yield L33–79]; its dependency-ordered load is a typed interface, not a bare relaxed load
[Libdispatch-atomic L82–142].
> *Means* — 8.4, 8.6 [Apple-tuning]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a scan for spin loops
> and for threads created without a QoS class. *Brief* — QoS on every thread and queue, no affinity; over-decompose by
> three; no spin-waits.

**AA.7 The ABI and the security features are Apple's.** Code shall follow the Apple arm64 ABI where it differs from
AAPCS64: variadic arguments go on the stack, so a function redeclared as variadic reads garbage; `char` is signed;
`long double` is `double`; `x18` is reserved; callers extend arguments narrower than 32 bits [Apple-abi]. Under
`arm64e`, return addresses, function pointers and vtable entries are signed, so a declaration that differs from its
definition fails authentication where it merely worked before [Apple-pac]; `arm64e.x1` adds checked pointer arithmetic
on the newest hardware [Apple-sec]; hand assembly carries landing pads and unwinders authenticate. Memory Integrity
Enforcement is synchronous memory tagging, always on from A19 and M5 [Apple-MIE]: an over-read stays inside its 16-byte
granule, as Arm's `strlen-mte` keeps every load aligned and in-granule [ArmOR-strlen-mte L30–89]; custom allocators
tag; pointer top bits are no longer free. Code that writes code takes pages with `MAP_JIT` and writes only inside
`pthread_jit_write_with_callback_np` [Apple-jit].
> *Means* — 8.1, 8.8 [Apple-abi] [Apple-pac]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a build and
> test run as `arm64e` with enhanced security on. *Brief* — Apple's ABI, not AAPCS64; build and run as `arm64e`;
> over-reads within 16-byte granules; JIT only through `MAP_JIT`.

**AA.8 Floating point differs from SSE by design.** Contraction shall be decided, not inherited (X86.8): FMA is
baseline here and absent from baseline x86-64, so the same source rounds differently across the two under GCC's
default [GCC-opt]. `FMIN` and `FMAX` propagate NaN and `FMINNM` and `FMAXNM` do not, where `minps` returns its second
operand; `FCVTZS` saturates and maps NaN to 0 where x86 gives `0x8000…`; both are undefined in C and observable.
`long double` is `double` here and quad on Linux arm64 [Apple-abi]. A test that compares with x86 golden values names
these differences.
> *Means* — 3.60 [Apple-abi] [GCC-opt]. *Governs* — transformation. *CALM* — not applicable. *Checked by* — a
> golden-value test built for both ISAs. *Brief* — Contraction by decision; NaN, min/max, float→int and `long double`
> semantics chosen, not inherited.

**AA.9 Measure on the tier, in cycles.** A claim shall be measured with counters, at a fixed QoS class, on a named core
tier, and reported per tier, because macOS reports neither frequency nor placement and the generic timer runs at
24 MHz, so wall-clock time mixes frequency and tier [Sidler25]. Instruments' CPU Counters gives top-down bottleneck
analysis, and Processor Trace, on M4 and later, records every user instruction [WWDC25-308]; microbenchmarks read the
counters through the private `kperf` interface. Count µops and issues separately, because pairs and fused ops make
instruction counts ill-defined [DJ]. Every number after M1 carries its measurer's name; Johnson's M1 tables and
Pavlov's memory latencies are the baseline [DJ] [DJ-int] [DJ-simd] [SevenCPU-M1].
> *Means* — 10.8 [Sidler25]. *Governs* — effect. *CALM* — not applicable. *Checked by* — a measurement record naming
> tier, QoS class, generation and tool. *Brief* — Counters at a fixed QoS, per tier; wall-clock alone says nothing
> here; every number names its measurer.

## The price list

M1 performance core, core clocks, Johnson's measurements unless marked; read in September 2026.

| Operation | Cost | Source |
|---|---|---|
| ALU op | 1 cycle; six per cycle | [DJ-int] |
| ALU op with a shifted register | 2 cycles, two issues | [DJ-int] |
| Load-use, L1 hit | 3 cycles on a pointer chase, 4 with a complex address | [DJ] |
| L2 hit; DRAM | ~18 cycles; 18 cycles plus ~91 ns | [SevenCPU-M1] |
| Branch mispredict | ~13 cycles | [SevenCPU-M1] |
| `fmla`, 4 × 32-bit | 4 cycles, four per cycle: sixteen accumulators | [DJ-simd] |
| `tbl`, one or two tables | 2 cycles, four per cycle | [DJ-simd] |
| `addv`, horizontal sum | 3 cycles, four per cycle (dear on Arm's server cores, cheap here) | [DJ-simd] |
| Vector → GPR move | up to 10 cycles; a round trip ≥ 7 | [DJ] |
| `cas` vs `casal`, uncontended | 3 vs 7 cycles | [DJ-int] |
| `dmb`, `dsb`, `isb` in isolation | ~3, 17, 28 cycles; the real cost is what they drain | [DJ-int] |
| M4, one core, FP32 | NEON `fmla` 107 GFLOPS; streaming-mode `fmla` 31; `fmopa` ~2,000 | [Jena-SME] |

## Traps

| Trap | What happens | What the best code does |
|---|---|---|
| Domain crossing in the loop | an `fmov` or `umov` per iteration is the whole cost | keep the work in one register file (AA.4) |
| `dmb` where an access would do | slower, and it hides which order mattered | acquire or release on the access (AA.2) |
| `LDAR`'s extra strength | code correct only because acquire was RCsc | check on the model; `LDAPR` is what `acquire` now compiles to [Arm-partial] |
| 4 KiB and 64-byte constants | allocators, ELF segments and padding built for other machines | ask the system (AA.1) |
| Spinning across tiers | a fast core spins waiting for a slow one | QoS and system primitives (AA.6) |
| SVE assumed | none outside streaming mode here | NEON, or dispatch (AA.5) |
| Streaming mode for vector work | slower than NEON on M4 for anything but outer products | measure before moving a kernel to SME (AA.5) |
| Variadics, `char`, `long double`, `x18` | the ABI differs from Linux arm64 | Apple's ABI document (AA.7) |
| Tags and top bits | tagging is on; pointer high bits are used | over-read in-granule; allocators tag (AA.7) |

## Exemplars

- simdjson, `arm64/simd.h` [SJ-arm-simd L121–144]: a bitmask by `addp` folds and the `shrn #4` trick; `any()` on an
  integer reduction with the reason written beside it; `arm64/bitmask.h` [SJ-arm-bitmask L17–38]: which register file
  does the work, decided from the price list.
- BLAKE3, `c/blake3_neon.c` [B3-neon L11–67]: a rotate chosen per amount, byte-typed loads because the word-typed
  form has alignment requirements, four inputs hashed across lanes.
- Arm optimized-routines, `strlen-mte.S` [ArmOR-strlen-mte L30–89]: aligned 16-byte loads that never cross a tag
  granule; a `shrn` syndrome; `rbit` and `clz` where base A64 has no `ctz`.
- Linux, `arch/arm64/include/asm/barrier.h` [Lx-arm64-barrier]: release and acquire as single instructions, a fake
  address dependency to order a timer read; `cmpxchg.h` [Lx-arm64-cmpxchg]: waiting in `wfe` on the exclusive monitor.
- libdispatch, `src/shims/yield.h` [Libdispatch-yield L33–79]: Apple's no-spin guidance as code, with its
  preconditions stated; `atomic.h` [Libdispatch-atomic L82–142]: dependency ordering with a name.

## Forward look, to about 2031

- Three core tiers are normal from M6 on [Apple-M6]; code reads the tier count. Rosetta ends as a general facility
  after macOS 27 [Apple-rosetta-end], and with it any excuse for TSO.
- SME2 is Apple's matrix path from M4; streaming mode stays a separate machine with its own measurements
  [Zakharko] [Jena-SME].
- Hardware memory safety is on by default: Memory Integrity Enforcement from A19 and M5 [Apple-MIE], `arm64e.x1`
  checked pointer arithmetic on the newest parts [Apple-sec]. Code that hides data in pointer bits or over-reads
  buffers will crash rather than misbehave.
- Apple's guide stays gated [Apple-guide]; the public record stays a set of named measurements. Keep the measurer's
  name on every number.

## Questions an expert asks of Apple arm64 code before calling it done

1. Which generations and tiers is this for, and is every feature above the baseline detected through `sysctl`?
2. For the hot loop, what are the longest carried chain and the busiest pipe, and are there at least latency × pipes
   independent accumulators?
3. Does the loop cross between general and vector registers on every iteration, or reduce inside the loop?
4. Is any page size, line size, core count, tier count or vector length hard-coded? Is padding 128 bytes?
5. Do over-reads stay within the page and within 16-byte tag granules?
6. Does every thread and queue carry a QoS class? Is parallel work over-decomposed and free of spin-waits?
7. Is every cross-thread access an atomic with the weakest correct order, and is each `dmb` justified by a case no
   access could carry?
8. Does correctness depend on `LDAR` being RCsc, on TSO, or on a control dependency ordering a later load? Has the
   protocol been checked with a litmus test or a model checker, not stress-tested on one machine?
9. Are read-modify-writes LSE instructions, and are 16-byte atomics behind an LSE2 check?
10. Is contraction explicit? Do tests pin or tolerate the NaN, min/max, float→int and `long double` differences from
    x86?
11. Does anything depend on `char` signedness, variadic register passing or `x18`?
12. Does it build and run as `arm64e` with enhanced security on, and does hand assembly carry landing pads?
13. Was it measured with counters, at a fixed QoS, per tier, on this hardware, with the measurer named?

<!-- brief: Apple arm64 -->
Ask the system for every constant (16 KiB pages, 128-byte granule, tiers by `sysctl`); acquire and release on the
access, `dmb` only where no access can carry it, LSE atomics, correct under the weak model and never under Rosetta's
TSO; work stays in one register file and reduces once; NEON, matrices through Accelerate or SME outer products; QoS
on every thread, no affinity, no spinning; Apple's ABI and `arm64e`; contraction by decision; counters per tier with
the measurer named.
<!-- /brief -->
