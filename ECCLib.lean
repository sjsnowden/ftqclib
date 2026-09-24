/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
-- Higher-order Fourier foundations
import ECCLib.Derivative
import ECCLib.Polynomial
import ECCLib.GowersNorm
import ECCLib.DepthTower
import ECCLib.PhaseObstruction
import ECCLib.DualObstruction
import ECCLib.DualNorm
import ECCLib.ProjectedObstruction
import ECCLib.GowersCS
import ECCLib.InverseU2
import ECCLib.FiniteFourier
-- The Weil/coding layer: Gauss sums over 𝔽_q, the finite Heisenberg group and
-- Stone–von Neumann, the Weil representation and its metaplectic bundle (split at odd q), and
-- the coding layer with its computational examples. Deliberately NOT imported:
-- `ECCLib.VerifyIndependence` (environment metaprogramming, excluded from the liftable
-- library by design — build it on demand).
import ECCLib.GaussSum
import ECCLib.GaussSumSign
import ECCLib.GaussSumFq
import ECCLib.Annihilator
import ECCLib.AnnihilatorCheck
import ECCLib.PoissonSummation
import ECCLib.Heisenberg
import ECCLib.StoneVonNeumann
import ECCLib.StoneVonNeumannFull
import ECCLib.SymplecticGeneration
import ECCLib.SiegelGeneration
import ECCLib.WeilGeneration
import ECCLib.WeilGenerationComplete
import ECCLib.WeilRepresentation
import ECCLib.Metaplectic
import ECCLib.ProjectiveWeil
import ECCLib.WeilCharacter
import ECCLib.WeilCocycle
import ECCLib.WeilSplitting
import ECCLib.MonomialGroup
import ECCLib.MonomialWeil
import ECCLib.GaussCollapse
import ECCLib.GaussTorus
import ECCLib.Codes
import ECCLib.MacWilliams
import ECCLib.WeightEnumerator
import ECCLib.Distance
import ECCLib.ReedSolomon
import ECCLib.Decoding
import ECCLib.ReedMuller
import ECCLib.MajorityLogic
import ECCLib.PolyList
import ECCLib.GaoDecoder
import ECCLib.GaoField
import ECCLib.GRS
import ECCLib.BerlekampMassey
import ECCLib.WitnessBM
import ECCLib.GateChecker
import ECCLib.Straightline
import ECCLib.StraightlineGate
import ECCLib.StraightlineEmit
import ECCLib.Circuit
import ECCLib.StructureConstants
import ECCLib.StructureConstantsCheck
import ECCLib.GateAlgebra
import ECCLib.DigitCircuit
import ECCLib.WitnessDigit
import ECCLib.GateField
import ECCLib.GateCarrier
import ECCLib.FieldCert
import ECCLib.GateDecoder
import ECCLib.WitnessGauss
import ECCLib.WitnessOperators
import ECCLib.WitnessCoding
import ECCLib.Delsarte.Krawtchouk
import ECCLib.Delsarte.KrawtchoukCheck
import ECCLib.Delsarte.Shell
import ECCLib.Delsarte.Distribution
import ECCLib.Delsarte.ShellCheck
import ECCLib.Delsarte.Inequality
import ECCLib.Delsarte.LP
import ECCLib.Delsarte.LPCheck
import ECCLib.Delsarte.Corollaries
import ECCLib.Delsarte.BallCert
import ECCLib.Delsarte.CorollariesCheck
import ECCLib.Delsarte.Linear
import ECCLib.Delsarte.LinearCheck
import ECCLib.Delsarte.WitnessLP
import ECCLib.Scheme.LP
import ECCLib.Scheme.PiChar
import ECCLib.Scheme.DelsarteBridge
import ECCLib.Scheme.DelsarteBridgeCheck
import ECCLib.Matrix.CommStarMatrix
import ECCLib.Matrix.CommStarMatrixCheck
import ECCLib.SplitAlgebra
import ECCLib.SplitAlgebraCheck
import ECCLib.Matrix.PermCommutant
import ECCLib.Matrix.PermCommutantCheck
import ECCLib.Scheme.Orbital
import ECCLib.Scheme.OrbitalSpectrumCheck
import ECCLib.Scheme.OrbitalSpectrum
import ECCLib.Scheme.JohnsonCheck
import ECCLib.Scheme.Johnson
import ECCLib.Scheme.TranslationOrbitalCheck
import ECCLib.Scheme.TranslationOrbital
import ECCLib.Scheme.TranslationSpectrum
import ECCLib.Scheme.TranslationSpectrumCheck
import ECCLib.Scheme.SelfPaired
import ECCLib.Scheme.SelfPairedCheck
import ECCLib.Scheme.OrbitalCheck
import ECCLib.Scheme.Orbits
import ECCLib.Scheme.OrbitCount
import ECCLib.Scheme.OrbitCountCheck
import ECCLib.Scheme.Translation
import ECCLib.Scheme.TranslationCheck
import ECCLib.Scheme.Spectrum
import ECCLib.Scheme.FourierBridge
import ECCLib.Scheme.SpectrumCheck
import ECCLib.Scheme.Hamming
import ECCLib.Scheme.HammingCheck
import ECCLib.Scheme.HammingDual
import ECCLib.Scheme.HammingDualCheck
import ECCLib.Scheme.HammingScheme
import ECCLib.Scheme.HammingSchemeCheck
import ECCLib.Scheme.DualAction
import ECCLib.Scheme.DualActionCheck
import ECCLib.Scheme.DualTransitive
import ECCLib.Scheme.DualTransitiveCheck
import ECCLib.Matrix.CoherentAlgebra
import ECCLib.Matrix.CoherentAlgebraCheck
import ECCLib.CommutativeSubalgebra
import ECCLib.CommutativeSubalgebraCheck
import ECCLib.Matrix.CommonEigenvector
import ECCLib.Matrix.CommonEigenvectorCheck
import ECCLib.Matrix.SpectralDetermination
import ECCLib.Matrix.SpectralDeterminationCheck
import ECCLib.SubsetProfile
import ECCLib.SubsetProfileCheck
import ECCLib.PairHarmonic
import ECCLib.PairHarmonicCheck
import ECCLib.Delsarte.PairShellSum
import ECCLib.Delsarte.PairShellSumCheck
import ECCLib.Scheme.JohnsonSpectrum
import ECCLib.Scheme.JohnsonSpectrumCheck
import ECCLib.Scheme.InclusionMatrix
import ECCLib.Scheme.InclusionMatrixCheck
import ECCLib.Scheme.JohnsonMultiplicity
import ECCLib.Scheme.JohnsonMultiplicityCheck
import ECCLib.Scheme.OrbitalOrthogonality
import ECCLib.Scheme.OrbitalOrthogonalityCheck
import ECCLib.Scheme.JohnsonOrthogonality
import ECCLib.Scheme.JohnsonOrthogonalityCheck
import ECCLib.Scheme.Kneser
import ECCLib.Scheme.KneserCheck
import ECCLib.Scheme.HammingGraph
import ECCLib.Scheme.HammingGraphCheck
import ECCLib.Matrix.SpectralPositivity
import ECCLib.Matrix.SpectralPositivityCheck
import ECCLib.Scheme.OrbitalPositivity
import ECCLib.Scheme.OrbitalPositivityCheck
import ECCLib.Scheme.JohnsonDelsarte
import ECCLib.Scheme.JohnsonDelsarteCheck
import ECCLib.Scheme.HammingOrthogonality
import ECCLib.Scheme.HammingOrthogonalityCheck
import ECCLib.Scheme.Homogeneous
import ECCLib.Scheme.HomogeneousCheck
import ECCLib.Delsarte.Eberlein
import ECCLib.Delsarte.EberleinCheck

set_option linter.style.longLine false

/-!
# ECCLib — higher-order Fourier analysis, the Weil representation and coding theory

A self-contained, **Mathlib-only** library in two layers, both imported here so that
`lake build ECCLib` certifies the whole of it.

**Layer 1 — foundations of higher-order Fourier analysis** (the original core):

* `ECCLib.Derivative` — the additive derivative `D_y = fwdDiff y` and its multi-direction iterate;
* `ECCLib.Polynomial` — classical and nonclassical polynomials via the local (iterated-difference)
  definition (Hatami–Hatami–Lovett, Ch 6, Def 6.1 / 6.2), with the mother example proved — over the genuine
  torus `ℝ/ℤ`, via an injective-hom degree transfer — to be nonclassical of degree exactly 2;
* `ECCLib.GowersNorm` — the Gowers uniformity norm `‖·‖_{U^d}`, with the `U¹` identity
  `‖f‖_{U¹} = |𝔼 f|` and monotonicity `‖f‖_{U^d} ≤ ‖f‖_{U^{d+1}}`;
* `ECCLib.GowersCS` — the **Gowers–Cauchy–Schwarz inequality**
  `‖⟨(f_ω)⟩_{U^d}‖ ≤ ∏_ω ‖f_ω‖_{U^d}` for the multilinear box inner product, via the box peeling
  factorization, cube-coordinate symmetry, the self-box = norm identity, and the `2^d`-leaf induction;
* `ECCLib.PhaseObstruction` — polynomial phases saturate the norm: `‖ψ ∘ P‖_{U^{s+1}} = 1` when
  `deg P ≤ s` (the converse direction of the inverse theorem — degree-`s` phases *are* the obstructions);
* `ECCLib.DualObstruction` — polynomial phases have **dual norm ≤ 1**: `‖𝔼[f·\overline{e(P)}]‖ ≤
  ‖f‖_{U^{s+1}}`, so correlating with a degree-`s` phase lower-bounds `‖f‖_{U^{s+1}}` (Candela–González-
  Sánchez–Szegedy `lem:dualnormbound`/`prop:propolyobstruct`, phase-polynomial case);
* `ECCLib.DepthTower` — the tower `|x|/2^k` of degree-exactly-`k` polynomials over `ℝ/ℤ`, **uniformly
  for all `k`** (not a family of `decide`s), classical at `k = 1` and nonclassical above — the HOF image of the
  frame's precision ladder;
* `ECCLib.InverseU2` — the `U²` inverse *deduction* and its self-contained `ℓ⁴ ≤ ℓ^∞·ℓ²` detector
  engine, taking the two Fourier inputs (the `U²`-identity and Parseval) as an explicit interface;
* `ECCLib.FiniteFourier` — the **𝔼-normalized discrete Fourier transform** on an arbitrary finite
  abelian group (inversion, Parseval, the autocorrelation–Fourier identity, and the `U²`-Fourier identity
  `‖f‖_{U²}⁴ = Σ_ξ|f̂(ξ)|⁴`), built directly from character orthogonality since Mathlib upstreams only the
  cyclic (`ZMod N`) transform. Closes the **hypothesis-free `U²` inverse theorem** `u2_inverse`: a `1`-bounded
  function correlates with a single character at least as strongly as its squared `U²` norm.

**Layer 2 — the odd-characteristic Weil representation and coding theory**:

* the Gauss layer — `GaussSum`/`GaussSumSign`/`GaussSumFq`: the quadratic Gauss sum, its definite
  sign over every `𝔽_q` (`quadGaussSum_sign_fq`), the Davenport–Hasse lifting relation, and the
  char-2 vanishing boundary; `PoissonSummation`;
* the Heisenberg layer — `Heisenberg` (the group, Schur, the Schrödinger model),
  `StoneVonNeumann`/`StoneVonNeumannFull` (the full theorem: ψ-isotypic decomposition +
  intertwiner uniqueness, `stone_von_neumann`);
* the symplectic/Weil layer — `SymplecticGeneration` (`Ep = Sp`), `SiegelGeneration`
  (`Sp = ⟨shears, w⟩`), `WeilGeneration`/`WeilGenerationComplete` (the explicit route),
  `WeilRepresentation` (the SvN-transport route);
* the metaplectic bundle — `Metaplectic` (`Mp`, `weilMp`, the exact `1 → ℂˣ → Mp → Sp → 1`),
  `ProjectiveWeil` (`weilProj`), `WeilCharacter` (the character formula
  `Tr(W)·Tr(W⁻¹) = q^{dim ker(ḡ−1)}`), `WeilCocycle` (the canonical trace-1 section and the
  computable cocycle), `WeilSplitting` (**the cover splits at odd `q`**: `mpProj_splits`,
  `weilLinear`);
* the monomial/torus layer — `MonomialGroup`, `MonomialWeil`, `GaussCollapse`, `GaussTorus`;
* the coding layer — `Codes` (dual codes, the DFT bridge
  `fourierOp_indicator`), `MacWilliams` (Krawtchouk, `macwilliams`), `WeightEnumerator` (the
  homogeneous `homMacwilliams`, the weight distribution `weightPoly`/`weightDist`), `Distance`
  (`minDist` and the unconditional Singleton bound `singleton_bound`), `ReedSolomon` (`rsCode`,
  `finrank_rsCode`, and the MDS theorem `minDist_rsCode`), `Decoding` (the decoder specification
  layer: `IsMDDecoder`, `Corrects`, the correction theorem `IsMDDecoder.corrects` +
  the `⌊(d−1)/2⌋` radius; syndrome decoding — `IsCosetLeaderMap`, `synDecoder_isMD`,
  `exists_cosetLeaderMap`, the `mkQ` presentation), `ReedMuller` (the first-order
  Reed–Muller code `rm1` as the range of affine evaluation, `dim = m+1`, the balanced-form
  half-count, the subtraction-free distance theorem `2·d = 2^m`, the **computable
  Walsh–Hadamard decoder** `fwhtDec` over ℤ-valued correlations with `fwhtDec_isMD` and the
  `4t < 2^m` correction guarantee, and the Fourier certificate `walsh_eq_fourier` — the
  decoder's correlation table IS `fourierOp sgnChar` on the ±1-lift, the library's DFT doing
  the decoding; worked examples at `m = 3` including a live corrected transmission run by
  kernel `decide`), `MajorityLogic` (**Reed's majority-logic decoder** for the same
  `rm1` — per-bit majority votes as `Finset.card`s (the affine part telescopes, so a vote
  is bad only at a corrupted point; ≤ 2t bad of 2^m), `reedDec_corrects` at the SAME full
  radius `4t < 2^m` at counting cost, and worked examples: the same transmission as in
  `ReedMuller` healed by theorem AND by live kernel run, plus the machine-checked **agreement row**
  — both verified decoders return the same answer on the same corrupted word), `PolyList` (the
  **computable polynomial kit** for the RS decoder — `FieldOps`/`Model` (operations as data,
  a bijection transporting them to a field), little-endian `List` polynomials with structural
  arithmetic, the noncomputable `toPoly` denotation with its hom lemmas and the coefficient
  workhorse `toPoly_coeff`, the
  subtraction-free semantic degree `pdeg`/`plead`, **fuel-based long division** `pdivMod`
  with the division identity + strict remainder bound `pdivMod_spec` via the leading-term
  cancellation, and proof-side quotient/remainder uniqueness `pdiv_unique`; `ZMod 2` smoke
  instance with kernel-`decide` corners), `GaoDecoder` (**the verified Gao decoder for
  Reed–Solomon codes** — the executable nodal product `prodLin` and Lagrange interpolant
  `pinterp` (with the `eraseIdx` index bookkeeping), the fuel Euclid loop `gaoLoop` with its
  four invariants (`GaoInv`: Bezout divisibility, two subtraction-free size
  sums, strict descent, the `±G₀` determinant) through `gaoLoop_spec`, the root-counting
  engine `prod_X_sub_C_dvd`/`key_dvd`, **`gao_identity`** (at the stop `g = f·v`, `v ≠ 0`,
  by the degree count on `Δ = g·E − f·v·E`), the computable decoder `rsDecode` with the
  `none`-beyond-radius contract, and the main theorem **`rsDecodeF_corrects` —
  `Corrects (rsDecodeF ops M a k) (rsCode a k) t` whenever `2t + k ≤ n`, over any injective
  point family** — with the `2t < minDist` form via the MDS theorem), `GaoField` (the
  coordinate model with `mulVecC` and the decided inverse tables is a `FieldOps.Model` of
  `AdjoinRoot ν` **generically in `(m, r, table)`** (`gfModel` — the named certificates
  `inv4_cert`/`inv8_cert` are the only per-field inputs); instantiated at **GF(16)
  (`[15,9,7]` on the primitive root-power family, `t = 3`, `gf16_rs_corrects`, with the
  by-theorem corrected transmission `gf16_transmission`)** and **GF(256) (full-field
  `[256,224,33]` on the bit enumeration — no order certificate, the AES root is order 51 —
  `t = 16`, `gf256_rs_corrects`)**, plus the MDS rows `d = 7`/`d = 33`), `GRS` (
  **generalized Reed–Solomon codes and the weighted parity check** — `grsCode` with column
  multipliers (`rsCode` = the `v ≡ 1` instance; `finrank = k` by transport along the
  diagonal `scaleEquiv`), the pinned dual multipliers `dualMult` (the Lagrange leading
  coefficients), the moment identity `sum_dualMult_eval` off `Lagrange.coeff_eq_sum`,
  **`dualCode_grsCode`** (Hall 5.1.6: `(GRS v k)^⊥ = GRS (u/v) (n−k)`), `dualCode_rsCode`,
  and **`rsCode_eq_ker_synMap`** — `rsCode a k = ker` of the `u`-WEIGHTED syndrome moment
  map; the unweighted moment map does not present `rsCode` in general),
  `BerlekampMassey` (the Berlekamp–Massey algorithm: the window `Generates` predicate with the
  Massey jump lemma `generates_jump`; the structural no-fuel discrepancy iteration with
  executable `bmTaps` and the stored-L monic `bmLocator`; the `BMInv` induction with
  minimality at every prefix; main theorems **`bmSynth_shortest`** (the returned length IS the
  linear complexity, minimality over ALL F-side generators) and **`bm_error_locator`**
  (on `2t` u-weighted syndromes of a weight-`≤ t` pattern the algorithm returns the weight
  and the monic DIRECT-ROOT locator `∏(X − C aᵢ)` — uniqueness by divisibility + monicity +
  degree, never "the first solution"), with the receiver seam `synSeq_codeword_add`),
  `DigitCircuit` (the odd-`p` gate descent: the dense digit layer with
  totalization-through-decode — `dtabC` blocks whose specs are hypothesis-free on ALL
  inputs, `dcomp` the one `subst` site, the repaired totalizer, digit folds and
  `linWD`/`bilinD`, the word layer consuming the base-generic `repr_mul`/`repr_const_mul`,
  and **`descent_uniform_in_q`** — ONE theorem family over every modulus `p` (2 included)
  and every based `(ZMod p)`-algebra, with the `p = 2` anchors decided as agreement with
  `bit`/XOR/AND and the `p = 3` instances as genuine multi-gate verified networks),
  `WitnessDigit` (the 𝔽₃ repetition-decoder descent — `syn3Net`/`leader3Net`/`dec3Net`
  assembled by one `subst`, `eval_dec3Net` the gate-level semantics, and
  **`dec3Net_corrects`** — the odd-`p` gate-level decoder: the field-level `synDec₃_corrects_one`
  composed with gate preservation, the netlist heals one error BY THEOREM; the live kernel
  run is measured-infeasible in the tree model — the ladder 360 / 317,328 / 14,280,120
  tree gates per composition level — so a live run needs straight-line sharing),
  `WitnessBM` (the GF(16) error-locator example — `gf16_bm_error_locator` on the
  weight-2 pattern's six syndromes with the closed-form dual multipliers
  `dualMult_a16 : uᵢ = αⁱ`, kernel content rows for the executable run — and the
  cross-family differential check: the Euclid-based alternative `bmSynthD` agreeing with
  `bmSynth` by `decide` wherever uniqueness holds, and DIVERGING, machine-checked, on the
  maximal-complexity input where `2L > N` makes the generator non-unique),
  `GateChecker` (**constant folding + the codeword-checker netlist** — the
  semantics-preserving, size-non-increasing `cfold` pass (the compiled syndrome netlist folds
  from 6 gates to the hand-minimal 2, with correctness by the general theorem); the block/flatten
  layer with its one reindexing lemma `blockMat_mulVec`; `constsMat`/`evalVec_constsMat` — any
  constant-linear map over a
  based `𝔽₂`-algebra as one flat verified `linW` netlist; **`checkNet_eq_zero_iff`** — the
  gate-level `rsCode` membership test, exact via the `GRS` kernel presentation, instantiated
  as a verified `24 × 60` checker for the GF(16) `[15,9,7]` code; and the constant-level
  computable crossing `constMulMat_adjBasis_emb`);
* the gate-descent layer — `Circuit`: boolean circuits with a denotational semantics
  and gate counts, the field encoding `bit : ZMod 2 ≃ Bool` (`+ ↦ XOR`, `· ↦ AND`, one gate each),
  the `xorFold` primitive with `parityC`/`dotC` (an `𝔽₂`-linear form descends to an XOR tree),
  `subst` with **compositionality of the semantics** (`eval_subst`), and `tabC` (every boolean
  function of few wires is a netlist, with its exponential cost bound); `GateAlgebra`: the
  word layer with its totality lemma, `linW` (an `𝔽₂`-matrix as a netlist), `bilinNet` (the flat
  bilinear netlist with preservation and exact size), the hypothesis-free **coordinate theorem**
  `repr_mul` over any based algebra (structure constants `strConst`), and the abstract multiplier
  `mulNet` with its addition and fixed-constant relatives; `GateField`: the computable
  coordinate model (`xtimeVec`/`powVec`/`tbl`/`mulVecC`), the crux lemma and the crossing
  equation `strConst_eq_tbl` (the certified abstract multiplier IS the printable netlist —
  `mulNet_adjBasis`, for every `m` and reduction word over the `Monic`-only `AdjoinRoot`
  carrier), GF(16) with its named reduction polynomial `ν₄ = Φ₅` proved irreducible, and the
  m=4/m=8 witnesses by kernel `decide` (gate counts 105 and 727); `GateCarrier`: the named
  carrier as a first-class finite field (`Fintype`/`card = 2^(m+1)` with `Monic` only) and the
  classification bridge `adjEquivGaloisField` (**`GF16 ≃ₐ[ZMod 2] GaloisField 2 4`**), plus the
  scoped `GaloisField 2 n` fallback — the coding layer accepts GF(16) and, abstractly, GF(256)
  today; `FieldCert`: certified irreducibility from a decided inverse table
  (`irreducible_of_inv` — the quotient `IsField` through the evaluation, hence `span {ν}`
  maximal, hence `ν` irreducible; the table needs no trust), instantiated twice — **GF(16) with
  the primitive polynomial `X⁴+X+1`** (`orderOf_root_GF16p = 15`: a certified primitive
  element) and **GF(256) with the AES polynomial `X⁸+X⁴+X³+X+1`** (`nu8_irreducible`, by 255
  kernel products) with its classification bridge
  `gf256EquivGaloisField`; and `GateDecoder`:
  `decoderNet` — the two-stage syndrome/coset-leader datapath — with **`decoderNet_corrects`, the
  gate-level correction guarantee** composing field-level decoder correctness with gate-level
  preservation;
* computational examples — `WitnessGauss`, `WitnessOperators`, `WitnessCoding`.

Imports no `FTQCLib.*`; intended to be liftable into a standalone repository. Layer-1 statements
follow the standard textbook formulations (Hatami–Hatami–Lovett).
-/
