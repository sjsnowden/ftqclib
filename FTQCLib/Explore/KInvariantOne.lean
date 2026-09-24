/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.MetaplecticTwoGroup
import FTQCLib.Frame.EntanglingGate

set_option linter.style.longLine false

/-! # The k-invariant of the metaplectic 2-group at `n = 1`

The metaplectic crossed module (`FTQCLib/Cohomology/MetaplecticTwoGroup.lean`) presents a 2-group
with classifying data `(Sp(2n,𝔽₂), ℤ/4, trivial action, [a])`; the k-invariant `[a] ∈ H³(Sp, ℤ/4)`
is its one uncomputed invariant. This file computes the associator 3-cocycle at `n = 1`, where
`π₀ = Sp(2,𝔽₂) ≅ S₃` (6 elements) and everything is `decide`-scale. Recipe (Baez–Lauda): choose a
section of `π₀`, choose boundary-lifts of the section defects, measure the associator failure in the
band `π₁ = ℤ/4`. The class `[a]` is independent of both choices (Baez–Lauda); any section computes
it.

**How the outcome is read.**

* If the restriction of the extracted cocycle to a Sylow `ℤ/2 ⊆ S₃` is a nonzero class, then
  `[a]₁ ≠ 0` unconditionally (restriction of a coboundary is a coboundary).
* If the restricted class is zero, the conclusion is "`[a]₁ = 0` **modulo the standard transfer
  argument** (cores∘res = [S₃ : ℤ/2] = 3, invertible on `ℤ/4`-coefficients, so res is injective on
  `H³(S₃, ℤ/4)`)"; the transfer argument is NOT formalized here. The global coboundary question on
  `S₃` is a `ℤ/4`-linear system in 36 unknowns — not `decide`-able — and is not attempted.
* Context only, not used: `H³(S₃, ℤ/4) ≅ ℤ/2` (by a universal-coefficient computation, not verified
  here).

**The construction.** The section: `S = [1, A, B, C, A·B, B·A]` where `A, B, C` are lifts of the three
transvections `τ_x, τ_z, τ_y` — all three carry the SAME sign table `s*(p) = 2·X(p)·Z(p)` (validity is a
`decide`); the two 3-cycles are lifted by the products, so their defects vanish by construction, and
`S 0 = 1` normalizes the section. The defect bases are not hand tables: they are COMPUTED from the
`crux_dual` duality formula — for a `g`-trivial signed element `d`, the unique `r` with `δ(sec r) = d` has
`r.X = hlv (d.s z₁)`, `r.Z = hlv (d.s x₁)` — and then VERIFIED (`defect_eq`, via `decide`). The associator
`aCoc i j k` is the phase discrepancy of the two reductions of `S i · S j · S k`, pinned by `aCoc_spec`:

    m(i,j) · m(ij,k) = incl (aCoc i j k) · (S i ▷ m(j,k)) · m(i,jk)

an equation in the Heisenberg group `PauliGroup 1`, with the base-part equality a separate `decide`
(`aCoc_base` — the two sides landing in the same fiber IS the check that the discrepancy is central).
The 3-cocycle identity (`aCoc_cocycle`, 6⁴ instances) is the extraction's self-check.

**Outcome (machine-checked below).** The restriction to the Sylow `ℤ/2 = {1, A}` vanishes
**identically at the cocycle level** (`aCoc_sylow_zero`) — so `res_{ℤ/2}[a]₁ = 0`, and by the zero
branch above: `[a]₁ = 0` modulo the unformalized transfer argument. The representative itself is NOT
identically zero (`aCoc_value_witness` — the section's phase bookkeeping is genuinely nonabelian);
the vanishing is of the restricted class, not the cochain. Consequence: **the 2-group's band
invariant, if nonzero anywhere, lives at `n ≥ 2`** — consistent with `n = 1` being the split case of
the affine extension (`cliffordSectionExists_one`) and with `metaplecticNonSplit_two` first appearing
at `n = 2`. An exploratory file, not part of the `FTQCLib` target; it uses no `native_decide`.
-/

namespace FTQCLib.Explore.KInvariantOne

open FTQCLib FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame FTQCLib.Cohomology

/-! ## The section -/

/-- The `X` Pauli on the single qubit. -/
def x1 : Pauli 1 := paulix 0

/-- The `Z` Pauli on the single qubit. -/
def z1 : Pauli 1 := pauliz 0

/-- The `Y` Pauli on the single qubit. -/
def y1 : Pauli 1 := x1 + z1

/-- **The common sign table of the three transvection lifts:** `s*(p) = 2·X(p)·Z(p)` — `2` on `Y`, `0`
elsewhere. One table validates all three transvections (their distortions agree on every pair). -/
def sStar : Pauli 1 → ZMod 4 := fun p => dbl (p.X 0 * p.Z 0)

/-- The lift of `τ_x`. -/
def secA : SignedSymplectic 1 :=
  ⟨transvectionEquiv x1, transvectionEquiv_isClifford x1, sStar, by decide⟩

/-- The lift of `τ_z`. -/
def secB : SignedSymplectic 1 :=
  ⟨transvectionEquiv z1, transvectionEquiv_isClifford z1, sStar, by decide⟩

/-- The lift of `τ_y`. -/
def secC : SignedSymplectic 1 :=
  ⟨transvectionEquiv y1, transvectionEquiv_isClifford y1, sStar, by decide⟩

/-- **The section of `π₀ ≅ S₃`:** identity, the three transvection lifts, and the two 3-cycles lifted by
products (so those defects vanish by construction). Normalized: `S 0 = 1`. -/
def S : Fin 6 → SignedSymplectic 1
  | 0 => 1
  | 1 => secA
  | 2 => secB
  | 3 => secC
  | 4 => secA * secB
  | 5 => secB * secA

/-- The multiplication table of `S₃` in the section's indexing (`e, τ_x, τ_z, τ_y, τ_xτ_z, τ_zτ_x`;
`mul6 i j` = "apply `j` then `i`", matching `SignedSymplectic`'s composition). -/
def mul6 : Fin 6 → Fin 6 → Fin 6
  | 0, j => j
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 4 | 1, 3 => 5 | 1, 4 => 2 | 1, 5 => 3
  | 2, 0 => 2 | 2, 1 => 5 | 2, 2 => 0 | 2, 3 => 4 | 2, 4 => 3 | 2, 5 => 1
  | 3, 0 => 3 | 3, 1 => 4 | 3, 2 => 5 | 3, 3 => 0 | 3, 4 => 1 | 3, 5 => 2
  | 4, 0 => 4 | 4, 1 => 3 | 4, 2 => 1 | 4, 3 => 2 | 4, 4 => 5 | 4, 5 => 0
  | 5, 0 => 5 | 5, 1 => 2 | 5, 2 => 3 | 5, 3 => 1 | 5, 4 => 0 | 5, 5 => 4

/-- The table is correct: the section multiplies according to `mul6` on the symplectic parts. -/
theorem S_mul_g : ∀ (i j : Fin 6) (p : Pauli 1), (S i * S j).g p = (S (mul6 i j)).g p := by
  decide

/-- The six symplectic parts are pairwise distinct (the section hits six distinct `π₀` classes). -/
theorem S_g_distinct : ∀ i j : Fin 6, i ≠ j →
    (S i).g x1 ≠ (S j).g x1 ∨ (S i).g z1 ≠ (S j).g z1 := by
  decide

/-- Every element of `Pauli 1` is the obvious combination of the basis. -/
private lemma pauli1_basis : ∀ p : Pauli 1, p = p.X 0 • x1 + p.Z 0 • z1 := by decide

/-- A linear equivalence of `Pauli 1` is determined by its values on `x1, z1`. -/
private lemma sp_eq_of_basis {g h : Pauli 1 ≃ₗ[ZMod 2] Pauli 1}
    (hx : g x1 = h x1) (hz : g z1 = h z1) : ∀ p, g p = h p := by
  intro p
  have hp := pauli1_basis p
  calc g p = g (p.X 0 • x1 + p.Z 0 • z1) := by rw [← hp]
    _ = p.X 0 • g x1 + p.Z 0 • g z1 := by rw [map_add, map_smul, map_smul]
    _ = p.X 0 • h x1 + p.Z 0 • h z1 := by rw [hx, hz]
    _ = h (p.X 0 • x1 + p.Z 0 • z1) := by rw [map_add, map_smul, map_smul]
    _ = h p := by rw [← hp]

/-- **The section is exhaustive:** every Clifford-symplectic map of `Pauli 1` is one of the six — so `S`
is a genuine set-section of `π₀ = Sp(2,𝔽₂)` (with `S_g_distinct`, a bijective one). -/
theorem S_g_exhaustive {g : Pauli 1 ≃ₗ[ZMod 2] Pauli 1} (hg : IsClifford g) :
    ∃ i : Fin 6, ∀ p, g p = (S i).g p := by
  have hω : omega (g x1) (g z1) = 1 := by
    have h := hg x1 z1
    rw [omegaBilin_apply, omegaBilin_apply] at h
    rw [h]
    decide
  have hcases : ∀ u v : Pauli 1, omega u v = 1 →
      ∃ i : Fin 6, u = (S i).g x1 ∧ v = (S i).g z1 := by decide
  obtain ⟨i, hu, hv⟩ := hcases _ _ hω
  exact ⟨i, sp_eq_of_basis hu hv⟩

/-! ## The defect lifts, computed by the duality formula -/

/-- The defect bases. **Derivation, not invention:** for the `g`-trivial defect
`d(i,j) = (S i · S j) · S(ij)⁻¹ ∈ im δ`, the unique `r` with `δ(sec r) = d` is given by the `crux_dual`
duality — `r.X = hlv (d.s z1)`, `r.Z = hlv (d.s x1)`. This table is that formula EVALUATED (compiled
`#eval` over the 36 pairs; the inverse-laden evaluation is too heavy for kernel `decide`, so the values are
baked in as literals); the verification that they are correct is `defect_eq` below, which is the property
that matters. Rows/cols at the identity vanish (`rTab_norm` — the section is normalized). -/
def rTab : Fin 6 → Fin 6 → Pauli 1
  | 0, _ => 0
  | 1, 0 => 0 | 1, 1 => x1 | 1, 2 => 0 | 1, 3 => y1 | 1, 4 => x1 | 1, 5 => y1
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => z1 | 2, 3 => y1 | 2, 4 => y1 | 2, 5 => z1
  | 3, 0 => 0 | 3, 1 => x1 | 3, 2 => z1 | 3, 3 => 0 | 3, 4 => z1 | 3, 5 => x1
  | 4, 0 => 0 | 4, 1 => y1 | 4, 2 => y1 | 4, 3 => y1 | 4, 4 => x1 | 4, 5 => z1
  | 5, 0 => 0 | 5, 1 => y1 | 5, 2 => y1 | 5, 3 => y1 | 5, 4 => x1 | 5, 5 => z1

/-- The boundary lift of the `(i,j)` defect: the phase-0 (normalized) Heisenberg element over `rTab i j`. -/
def mElt (i j : Fin 6) : PauliGroup 1 := PauliGroup.sec (rTab i j)

private lemma defect_g : ∀ (i j : Fin 6) (p : Pauli 1),
    (pauliShift (mElt i j) * S (mul6 i j)).g p = (S i * S j).g p := by decide

set_option maxHeartbeats 3200000 in
private lemma defect_s : ∀ (i j : Fin 6) (p : Pauli 1),
    (pauliShift (mElt i j) * S (mul6 i j)).s p = (S i * S j).s p := by decide

/-- **The defect equations:** `δ(m(i,j)) · S(ij) = S(i) · S(j)` — the chosen lifts genuinely trace the
section's failure to be a homomorphism. -/
theorem defect_eq (i j : Fin 6) : pauliShift (mElt i j) * S (mul6 i j) = S i * S j :=
  SignedSymplectic.ext' (LinearEquiv.ext (defect_g i j)) (funext (defect_s i j))

/-- Normalization: the defects along the identity vanish. -/
theorem rTab_norm : (∀ j : Fin 6, rTab 0 j = 0) ∧ (∀ i : Fin 6, rTab i 0 = 0) := by decide

/-! ## The associator -/

/-- **The associator 3-cocycle of the crossed module at `n = 1`:** the phase discrepancy between the two
reductions of `S i · S j · S k` to `S(ijk)`. Values in the band `ℤ/4`. -/
def aCoc (i j k : Fin 6) : ZMod 4 :=
  (mElt i j * mElt (mul6 i j) k).phase
    - (smulH (S i) (mElt j k) * mElt i (mul6 j k)).phase

private lemma aCoc_base : ∀ i j k : Fin 6,
    (mElt i j * mElt (mul6 i j) k).base
      = (smulH (S i) (mElt j k) * mElt i (mul6 j k)).base := by decide

/-- **The defining equation of the associator** in the Heisenberg group:
`m(i,j) · m(ij,k) = incl (aCoc i j k) · (S i ▷ m(j,k)) · m(i,jk)`. The two reductions of the triple
product differ by exactly this central phase. -/
theorem aCoc_spec (i j k : Fin 6) :
    mElt i j * mElt (mul6 i j) k
      = PauliGroup.incl (aCoc i j k) * (smulH (S i) (mElt j k) * mElt i (mul6 j k)) := by
  refine PauliGroup.ext ?_ ?_
  · simp only [PauliGroup.mul_phase, PauliGroup.incl_phase, PauliGroup.incl_base,
      betaFrame_zero_left, aCoc]
    ring
  · simp only [PauliGroup.mul_base, PauliGroup.incl_base, zero_add]
    exact aCoc_base i j k

set_option maxHeartbeats 12000000 in
/-- **The 3-cocycle identity** (trivial action — the band is fixed pointwise, `smulH_incl`): the
extraction's self-check, over all `6⁴` quadruples. -/
theorem aCoc_cocycle : ∀ i j k l : Fin 6,
    aCoc j k l - aCoc (mul6 i j) k l + aCoc i (mul6 j k) l
      - aCoc i j (mul6 k l) + aCoc i j k = 0 := by decide

/-- The cocycle is normalized (any argument at the identity gives `0`). -/
theorem aCoc_norm : ∀ j k : Fin 6, aCoc 0 j k = 0 ∧ aCoc j 0 k = 0 ∧ aCoc j k 0 = 0 := by decide

/-! ## The outcome -/

/-- The representative is NOT identically zero — the section's phase bookkeeping is genuinely
nonabelian (a witness value; the class, not the cochain, is what vanishes below). -/
theorem aCoc_value_witness : aCoc 1 2 3 = 3 := by decide

/-- **The Sylow restriction vanishes identically at the cocycle level.** `{0, 1}` (identity and the
`τ_x` lift) is a Sylow `ℤ/2` of `S₃` (`mul6 1 1 = 0`); on it the associator is the zero cochain — so
the restricted class `res_{ℤ/2}[a]₁ ∈ H³(ℤ/2, ℤ/4)` is zero. **Hence** `[a]₁ = 0` modulo the
standard transfer argument (cores∘res = 3, invertible on `ℤ/4` — NOT formalized here). The
unconditional Lean content is this theorem; the band invariant of the metaplectic 2-group, if
nonzero anywhere, lives at `n ≥ 2`. -/
theorem aCoc_sylow_zero : ∀ i j k : Fin 6, i ≤ 1 → j ≤ 1 → k ≤ 1 → aCoc i j k = 0 := by
  decide

end FTQCLib.Explore.KInvariantOne
