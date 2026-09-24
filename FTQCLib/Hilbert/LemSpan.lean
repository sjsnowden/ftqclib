/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.PauliCondition
import FTQCLib.Stabilizer.Dimension
import FTQCLib.Hilbert.BornCollapse
import FTQCLib.Hilbert.StabilizerEquiv
import FTQCLib.Hilbert.Separation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

set_option linter.unusedSectionVars false

/-! # Every Pauli lies in a Lagrangian (`lem:span`, seed step)

A **Lagrangian** of the symplectic space `Pauli n` is a full-rank isotropic
subspace: an `IsStabilizer` submodule `L` with `finrank L = n` (the maximal
possible dimension for an isotropic subspace, by `finrank_le_of_isStabilizer`).

This file proves that every Pauli `p` is contained in some Lagrangian:

* `exists_lagrangian_mem` — `∃ L, IsStabilizer L ∧ finrank L = n ∧ p ∈ L`.

It also constructs, for any stabilizer subspace `L`, a **reference sign** `β`: a choice of signs
trivializing the Pauli-product cocycle on `L`, matching the `SignedStab` data
(`sign_zero` + `valid`):

* `exists_refSign` — `∃ β, β 0 = 1 ∧ ∀ p q ∈ L, β q · β p · pauliPhase p q = β (p+q)`.

Finally it closes `lem:span` itself by **character orthogonality**: twisting `β` by each additive
character `χ : AddChar ↥L ℂ` gives a family of pure stabilizer densities `charSignedStab β … χ`, and
averaging `stabProjector (charSignedStab β … χ)` against `χ⟨p⟩` over all `χ` recovers `H(p)`
(`AddChar.sum_apply_eq_ite` collapses the inner sum to `card ↥L = 2ⁿ` at `q = p`):

* `pauliHermitian_eq_char_sum` — `H(p) = β p · ∑_χ χ⟨p⟩ · stabProjector (charSignedStab β … χ)`;
* `pauliHermitian_mem_span_pureStabDensity` — every `H(p)` lies in the pure-stabilizer-density span;
* `pureStabDensity_span_top` — the pure stabilizer densities span `End ℂ (QState n)` (`lem:span`).

The witness comes from the spectral theorem: the Hermitian Paulis `{H(g) : g ∈ L}` are pairwise
commuting self-adjoint operators on `QState n`
(`pauliHermitian_comm_of_omega_zero`, since `IsStabilizer` forces `ω = 0`), so by
`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute` they share a nonzero joint eigenvector `ψ`;
`β(g)` is the corresponding eigenvalue. Applying `H(q)` to the eigen-equation for `p` and using the
phase law `H(q) ∘ H(p) = pauliPhase p q · H(p+q)` gives the cocycle, after noting
`pauliPhase p q² = 1` on commuting pairs (`pauliPhase_sq_of_omega_zero`).

The construction is a **seed plus extension**. The seed is the all-Z subspace
`allZ = {q | q.X = 0}` (the kernel of the X-projection `xProj`), which is a
Lagrangian: it is isotropic because `omega` vanishes when both X-parts are zero,
and it has dimension `n` by rank-nullity (`xProj` is surjective onto
`(ZMod 2)^n`). The extension is `pauliCondition allZ p`, which by
`pauliCondition_isStabilizer`, `pauliCondition_finrank`, and `pauliCondition_mem`
is again a rank-`n` isotropic subspace and additionally contains `p`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## The X-projection and the all-Z seed Lagrangian -/

/-- The X-projection `Pauli n →ₗ[ZMod 2] (Fin n → ZMod 2)`, `q ↦ q.X`. Linear
because the X-component is additive (`X_add`) and `ZMod 2`-homogeneous
(`X_smul`). -/
def xProj : FTQCLib.Pauli n →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun q := q.X
  map_add' p q := X_add p q
  map_smul' c q := X_smul c q

@[simp]
theorem xProj_apply (q : FTQCLib.Pauli n) : xProj q = q.X := rfl

/-- The all-Z subspace `{q : Pauli n | q.X = 0}`, realized as the kernel of the
X-projection. Its members are the Paulis with trivial X-support, i.e. the
products of single-qubit `Z` operators. -/
def allZ : Submodule (ZMod 2) (FTQCLib.Pauli n) := LinearMap.ker xProj

/-- Membership in `allZ` is exactly "zero X-component". -/
theorem mem_allZ {q : FTQCLib.Pauli n} :
    q ∈ (allZ : Submodule (ZMod 2) (FTQCLib.Pauli n)) ↔ q.X = 0 := by
  rw [allZ, LinearMap.mem_ker, xProj_apply]

/-- The all-Z subspace is isotropic: if `p.X = 0` and `q.X = 0`, then
`omega p q = ∑ p.Z·q.X + ∑ p.X·q.Z = 0`, since both factors `q.X` and `p.X`
vanish. -/
theorem isStabilizer_allZ : IsStabilizer (allZ : Submodule (ZMod 2) (FTQCLib.Pauli n)) := by
  intro p hp q hq
  have hpX : p.X = 0 := mem_allZ.mp hp
  have hqX : q.X = 0 := mem_allZ.mp hq
  simp [omega, hpX, hqX]

/-- The X-projection is surjective: any `x : Fin n → ZMod 2` is `xProj ⟨x, 0⟩`. -/
theorem xProj_surjective : Function.Surjective (xProj : FTQCLib.Pauli n → (Fin n → ZMod 2)) :=
  fun x => ⟨⟨x, 0⟩, rfl⟩

/-- The all-Z seed is a Lagrangian: `finrank allZ = n`. By rank-nullity for
`xProj`, `finrank (range xProj) + finrank (ker xProj) = finrank (Pauli n) = 2n`;
surjectivity gives `finrank (range xProj) = n`, so `finrank allZ = n`. -/
theorem finrank_allZ : finrank (ZMod 2) (allZ : Submodule (ZMod 2) (FTQCLib.Pauli n)) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (xProj (n := n))
  have h_range : finrank (ZMod 2) (LinearMap.range (xProj (n := n))) = n := by
    rw [LinearMap.range_eq_top.mpr xProj_surjective, finrank_top, Module.finrank_pi,
      Fintype.card_fin]
  rw [h_range, finrank_Pauli] at h
  rw [allZ]
  omega

/-! ## Every Pauli lies in a Lagrangian -/

/-- **`lem:span` (seed step).** Every Pauli `p` lies in some Lagrangian: a
full-rank isotropic stabilizer subspace `L` with `finrank L = n` and `p ∈ L`.

The witness is `pauliCondition allZ p`, the Pauli conditioning of the all-Z seed
Lagrangian by `p`. Conditioning preserves the isotropy
(`pauliCondition_isStabilizer`) and the full rank (`pauliCondition_finrank`),
and forces `p` into the result (`pauliCondition_mem`). -/
theorem exists_lagrangian_mem (p : FTQCLib.Pauli n) :
    ∃ L : Submodule (ZMod 2) (FTQCLib.Pauli n),
      IsStabilizer L ∧ Module.finrank (ZMod 2) L = n ∧ p ∈ L :=
  ⟨pauliCondition allZ p,
    pauliCondition_isStabilizer isStabilizer_allZ p,
    pauliCondition_finrank isStabilizer_allZ finrank_allZ p,
    pauliCondition_mem allZ p⟩

/-! ## Finiteness and cardinality of submodule subtypes

Downstream character-orthogonality steps sum over `AddChar ↥L ℂ`, which needs a
`Fintype ↥L` instance. `Pauli n` is module-finite over the finite ring `ZMod 2`,
hence finite (`Module.finite_of_finite`), so every submodule subtype `↥L` is finite;
`Fintype.ofFinite` then upgrades this to a (noncomputable) `Fintype`. We also record
that a rank-`n` subspace has `2 ^ n` elements. -/

/-- `Pauli n` is a finite type. It is module-finite over the finite ring `ZMod 2`
(`Module.Finite (ZMod 2) (Pauli n)`), so `Module.finite_of_finite` yields finiteness.
Supplies the `Finite ↥L` needed by `fintypeSubmodule` via `Subtype.finite`. -/
instance finitePauli : Finite (FTQCLib.Pauli n) := Module.finite_of_finite (ZMod 2)

/-- A `Fintype` instance for submodule subtypes of `Pauli n`. Since `Pauli n` is a
finite type (`finitePauli`), every submodule subtype `↥L` is finite, and
`Fintype.ofFinite` upgrades this to a (noncomputable) `Fintype`. Needed because
summing over `AddChar ↥L ℂ` requires `Fintype ↥L`, which typeclass search does not
otherwise provide (only `Finite ↥L` is automatic). -/
noncomputable instance fintypeSubmodule
    (L : Submodule (ZMod 2) (FTQCLib.Pauli n)) : Fintype ↥L :=
  Fintype.ofFinite _

/-- A rank-`n` subspace of `Pauli n` has `2 ^ n` elements. Over the field
`ZMod 2`, `Module.card_eq_pow_finrank` gives `Fintype.card ↥L = 2 ^ finrank ↥L`
(using `ZMod.card 2 : Fintype.card (ZMod 2) = 2`); rewriting by the rank
hypothesis `h` yields `2 ^ n`. -/
theorem card_submodule_eq_pow_finrank {L : Submodule (ZMod 2) (FTQCLib.Pauli n)}
    (h : Module.finrank (ZMod 2) L = n) : Fintype.card ↥L = 2 ^ n := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, h]

/-! ## The reference-sign cocycle `β`

For a stabilizer subspace `L`, the Hermitian Paulis `{H(g) : g ∈ L}` pairwise commute and are
self-adjoint, so the spectral theorem furnishes a nonzero joint eigenvector. Its eigenvalues give a
choice of signs `β` trivializing the Pauli-product cocycle on `L` (the `SignedStab` data). -/

/-- Two Hermitian Paulis commute when their symplectic form vanishes. From `pauliHermitian_swap`
the swap scalar is `(-1)` raised to the cocycle exponent, whose parity is `ω(p,q)`
(`omega_natCast`); `ω(p,q) = 0` makes the exponent even, so the scalar is `1`. -/
theorem pauliHermitian_comm_of_omega_zero {p q : FTQCLib.Pauli n} (h : omega p q = 0) :
    pauliHermitian p ∘ₗ pauliHermitian q = pauliHermitian q ∘ₗ pauliHermitian p := by
  rw [pauliHermitian_swap]
  have heven : Even (zDotVal p q.X + zDotVal q p.X) := by
    rw [← ZMod.natCast_eq_zero_iff_even, omega_natCast, h]
  rw [heven.neg_one_pow, one_smul]

/-- The Pauli-product phase squares to one on a commuting pair (`ω(p,q) = 0`):
`pauliPhase p q * pauliPhase p q = 1`. From `(H(q) ∘ H(p))² = id` computed two ways — using
commutativity it collapses to `(H(q) ∘ H(q)) ∘ (H(p) ∘ H(p)) = id`, while the phase law makes it
`(pauliPhase p q)² • id` — and the trace (`tr id = 2ⁿ ≠ 0`) forces the scalar to `1`. -/
theorem pauliPhase_sq_of_omega_zero {p q : FTQCLib.Pauli n} (h : omega p q = 0) :
    pauliPhase p q * pauliPhase p q = 1 := by
  have hcomm := pauliHermitian_comm_of_omega_zero h
  have hid : (pauliHermitian q ∘ₗ pauliHermitian p) ∘ₗ (pauliHermitian q ∘ₗ pauliHermitian p)
      = LinearMap.id := by
    calc (pauliHermitian q ∘ₗ pauliHermitian p) ∘ₗ (pauliHermitian q ∘ₗ pauliHermitian p)
        = pauliHermitian q ∘ₗ (pauliHermitian p ∘ₗ pauliHermitian q) ∘ₗ pauliHermitian p := by
          simp only [LinearMap.comp_assoc]
      _ = pauliHermitian q ∘ₗ (pauliHermitian q ∘ₗ pauliHermitian p) ∘ₗ pauliHermitian p := by
          rw [hcomm]
      _ = (pauliHermitian q ∘ₗ pauliHermitian q) ∘ₗ (pauliHermitian p ∘ₗ pauliHermitian p) := by
          simp only [LinearMap.comp_assoc]
      _ = LinearMap.id := by rw [pauliHermitian_sq, pauliHermitian_sq, LinearMap.comp_id]
  have hphase : (pauliHermitian q ∘ₗ pauliHermitian p) ∘ₗ (pauliHermitian q ∘ₗ pauliHermitian p)
      = (pauliPhase p q * pauliPhase p q) • LinearMap.id := by
    rw [pauliHermitian_mul_phase p q, LinearMap.smul_comp, LinearMap.comp_smul,
      smul_smul, pauliHermitian_sq]
  rw [hphase] at hid
  have htr := congrArg (LinearMap.trace ℂ (QState n)) hid
  rw [map_smul, ← pauliHermitian_zero, pauliHermitian_trace, if_pos rfl, smul_eq_mul] at htr
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  have hc : pauliPhase p q * pauliPhase p q * (2 : ℂ) ^ n = 1 * (2 : ℂ) ^ n := by
    rw [one_mul]; exact htr
  exact mul_right_cancel₀ h2n hc

open scoped Function in
/-- **Reference sign (the β cocycle of `lem:span`).** For any stabilizer subspace `L` there is a
choice of signs `β : Pauli n → ℂ` with `β 0 = 1` trivializing the Pauli-product cocycle:
`β q · β p · pauliPhase p q = β (p+q)` for all `p, q ∈ L`. This is exactly the `SignedStab` data
(`sign_zero` + `valid`).

The Hermitian Paulis `{H(g) : g ∈ L}` are pairwise commuting (`pauliHermitian_comm_of_omega_zero`,
using `IsStabilizer`) symmetric operators on the finite-dimensional space `QState n`, so by the
spectral theorem (`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`) their joint eigenspaces span
`⊤ ≠ ⊥`; a nonzero joint eigenvector `ψ` then satisfies `H(g) ψ = χ(g) • ψ`. Set
`β(p) := χ⟨p⟩` on `L` (and `0` off `L`). Then `β 0 = 1` from `H(0) = id` and `ψ ≠ 0`; and applying
`H(q)` to `H(p) ψ = β p • ψ`, the phase law `H(q) ∘ H(p) = pauliPhase p q • H(p+q)` yields
`β p · β q = pauliPhase p q · β(p+q)`, which combined with `pauliPhase p q² = 1`
(`pauliPhase_sq_of_omega_zero`) gives the stated cocycle. -/
theorem exists_refSign {L : Submodule (ZMod 2) (FTQCLib.Pauli n)}
    (hS : FTQCLib.Stabilizer.IsStabilizer L) :
    ∃ β : FTQCLib.Pauli n → ℂ, β 0 = 1 ∧
      ∀ p ∈ L, ∀ q ∈ L, β q * β p * pauliPhase p q = β (p + q) := by
  classical
  set T : ↥L → QState n →ₗ[ℂ] QState n := fun g => pauliHermitian g.val with hT_def
  have hTsym : ∀ g, (T g).IsSymmetric := fun g => pauliHermitian_isSymmetric g.val
  have hTcomm : Pairwise (Commute on T) := by
    intro g g' _
    change T g * T g' = T g' * T g
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact pauliHermitian_comm_of_omega_zero (hS g.val g.property g'.val g'.property)
  have htop : ⨆ χ : ↥L → ℂ, ⨅ g, Module.End.eigenspace (T g) (χ g) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTsym hTcomm
  have hne_bot : (⨆ χ : ↥L → ℂ, ⨅ g, Module.End.eigenspace (T g) (χ g)) ≠ ⊥ := by
    rw [htop]; exact top_ne_bot
  have hexχ : ∃ χ : ↥L → ℂ, (⨅ g, Module.End.eigenspace (T g) (χ g)) ≠ ⊥ :=
    not_forall.mp (fun hall => hne_bot (iSup_eq_bot.mpr hall))
  obtain ⟨χ, hχ⟩ := hexχ
  obtain ⟨ψ, hψmem, hψne⟩ := (Submodule.ne_bot_iff _).mp hχ
  have heigen : ∀ g : ↥L, pauliHermitian g.val ψ = χ g • ψ := by
    intro g
    have hmem : ψ ∈ Module.End.eigenspace (T g) (χ g) := Submodule.mem_iInf _ |>.mp hψmem g
    exact Module.End.mem_eigenspace_iff.mp hmem
  refine ⟨fun p => if h : p ∈ L then χ ⟨p, h⟩ else 0, ?_, ?_⟩
  · have h0 : (0 : FTQCLib.Pauli n) ∈ L := L.zero_mem
    simp only [h0, dif_pos]
    have he := heigen ⟨0, h0⟩
    rw [pauliHermitian_zero] at he
    have h1 : (1 : ℂ) • ψ = χ ⟨0, h0⟩ • ψ := by rw [one_smul]; exact he
    exact (smul_left_injective ℂ hψne h1).symm
  · intro p hp q hq
    have hpq : p + q ∈ L := L.add_mem hp hq
    simp only [hp, hq, hpq, dif_pos]
    have hep := heigen ⟨p, hp⟩
    have heq := heigen ⟨q, hq⟩
    have hepq := heigen ⟨p + q, hpq⟩
    have hkey : (χ ⟨p, hp⟩ * χ ⟨q, hq⟩) • ψ
        = (pauliPhase p q * χ ⟨p + q, hpq⟩) • ψ := by
      have lhs : pauliHermitian q (pauliHermitian p ψ) = (χ ⟨p, hp⟩ * χ ⟨q, hq⟩) • ψ := by
        rw [hep, map_smul, heq, smul_smul, mul_comm]
      have rhs : pauliHermitian q (pauliHermitian p ψ)
          = (pauliPhase p q * χ ⟨p + q, hpq⟩) • ψ := by
        have hcf := LinearMap.congr_fun (pauliHermitian_mul_phase p q) ψ
        rw [LinearMap.comp_apply] at hcf
        rw [hcf, LinearMap.smul_apply, hepq, smul_smul]
      rw [← lhs, rhs]
    have hcancel : χ ⟨p, hp⟩ * χ ⟨q, hq⟩ = pauliPhase p q * χ ⟨p + q, hpq⟩ :=
      smul_left_injective ℂ hψne hkey
    have hsq := pauliPhase_sq_of_omega_zero (hS p hp q hq)
    calc χ ⟨q, hq⟩ * χ ⟨p, hp⟩ * pauliPhase p q
        = (χ ⟨p, hp⟩ * χ ⟨q, hq⟩) * pauliPhase p q := by ring
      _ = (pauliPhase p q * χ ⟨p + q, hpq⟩) * pauliPhase p q := by rw [hcancel]
      _ = (pauliPhase p q * pauliPhase p q) * χ ⟨p + q, hpq⟩ := by ring
      _ = χ ⟨p + q, hpq⟩ := by rw [hsq, one_mul]

/-! ## The character-twisted stabilizer family

Twisting the reference sign `β` of a Lagrangian `L` by an additive character `χ : AddChar ↥L ℂ`
yields a `SignedStab`; averaging the corresponding projectors over all `χ` recovers each Hermitian
Pauli, closing `lem:span`. -/

open scoped Classical in
/-- A signed stabilizer twisted by an additive character `χ` of `↥L`. The sign on `L` is the
reference sign `β` modulated by the character value `χ`, so that the cocycle law (`valid`) follows
from `β`'s reference-sign law (`hβv`) and multiplicativity of `χ` (`AddChar.map_add_eq_mul`). -/
noncomputable def charSignedStab {L : Submodule (ZMod 2) (FTQCLib.Pauli n)}
    (β : FTQCLib.Pauli n → ℂ) (hβ0 : β 0 = 1)
    (hβv : ∀ p ∈ L, ∀ q ∈ L, β q * β p * pauliPhase p q = β (p + q))
    (χ : AddChar ↥L ℂ) : SignedStab n where
  L := L
  sign q := if h : q ∈ L then β q * χ ⟨q, h⟩ else 0
  sign_zero := by
    have h0 : (0 : FTQCLib.Pauli n) ∈ L := L.zero_mem
    simp only [h0, dif_pos]
    have : (⟨(0 : FTQCLib.Pauli n), h0⟩ : ↥L) = 0 := rfl
    rw [hβ0, this, AddChar.map_zero_eq_one, mul_one]
  valid := by
    intro p hp q hq
    have hpq : p + q ∈ L := L.add_mem hp hq
    simp only [hp, hq, hpq, dif_pos]
    have hχ : χ ⟨q, hq⟩ * χ ⟨p, hp⟩ = χ ⟨p + q, hpq⟩ := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      apply Subtype.ext
      change q + p = p + q
      rw [add_comm]
    calc (β q * χ ⟨q, hq⟩) * (β p * χ ⟨p, hp⟩) * pauliPhase p q
        = (β q * β p * pauliPhase p q) * (χ ⟨q, hq⟩ * χ ⟨p, hp⟩) := by ring
      _ = β (p + q) * χ ⟨p + q, hpq⟩ := by rw [hβv p hp q hq, hχ]

open scoped Classical in
/-- Per-coordinate character orthogonality on a Lagrangian. Summing the `H(q)`-coefficient of the
`χ`-twisted projector against `χ⟨p⟩` over all characters `χ` collapses to `β p` at `q = p` and `0`
otherwise: `∑_χ χ⟨p⟩ · stabCoeff(charSignedStab … χ) q = if q = p then β p else 0`. The `q ∉ L`
terms vanish coefficient-wise; for `q ∈ L` it is `(2ⁿ)⁻¹·β q·∑_χ χ⟨p+q⟩`, and
`AddChar.sum_apply_eq_ite` evaluates the inner sum to `card ↥L = 2ⁿ` exactly when `p + q = 0`,
i.e. `q = p`. -/
theorem charSum_stabCoeff {L : Submodule (ZMod 2) (FTQCLib.Pauli n)}
    (β : FTQCLib.Pauli n → ℂ) (hβ0 : β 0 = 1)
    (hβv : ∀ p ∈ L, ∀ q ∈ L, β q * β p * pauliPhase p q = β (p + q))
    (hrank : finrank (ZMod 2) L = n) {p : FTQCLib.Pauli n} (hp : p ∈ L) (q : FTQCLib.Pauli n) :
    (∑ χ : AddChar ↥L ℂ, χ ⟨p, hp⟩ * stabCoeff (charSignedStab β hβ0 hβv χ) q)
      = if q = p then β p else 0 := by
  by_cases hq : q ∈ L
  · -- On `L`: pull out `(2ⁿ)⁻¹ · β q` and evaluate the character sum.
    have hcoeff : ∀ χ : AddChar ↥L ℂ,
        χ ⟨p, hp⟩ * stabCoeff (charSignedStab β hβ0 hβv χ) q
          = (2 ^ n : ℂ)⁻¹ * β q * (χ ⟨p, hp⟩ * χ ⟨q, hq⟩) := by
      intro χ
      simp only [stabCoeff, charSignedStab, hq, if_pos, dif_pos]
      ring
    rw [Finset.sum_congr rfl (fun χ _ => hcoeff χ), ← Finset.mul_sum]
    -- The membership-witnessed sum `⟨p⟩ + ⟨q⟩ = 0` in `↥L` is `p + q = 0`, equivalently `q = p`.
    have hzero_iff : (⟨p, hp⟩ + ⟨q, hq⟩ : ↥L) = 0 ↔ q = p := by
      rw [← Subtype.coe_inj, AddSubmonoid.coe_add, ZeroMemClass.coe_zero]
      change (p : FTQCLib.Pauli n) + q = 0 ↔ q = p
      constructor
      · intro h
        have hpq : (p : FTQCLib.Pauli n) + q + q = q := by rw [h, zero_add]
        rw [add_assoc, pauli_add_self, add_zero] at hpq
        exact hpq.symm
      · rintro rfl; exact pauli_add_self _
    have hsum : (∑ χ : AddChar ↥L ℂ, χ ⟨p, hp⟩ * χ ⟨q, hq⟩)
        = if q = p then (2 ^ n : ℂ) else 0 := by
      have hcard : (Fintype.card ↥L : ℂ) = (2 ^ n : ℂ) := by
        rw [card_submodule_eq_pow_finrank hrank]; push_cast; ring
      calc (∑ χ : AddChar ↥L ℂ, χ ⟨p, hp⟩ * χ ⟨q, hq⟩)
          = ∑ χ : AddChar ↥L ℂ, χ (⟨p, hp⟩ + ⟨q, hq⟩) := by
            refine Finset.sum_congr rfl (fun χ _ => ?_)
            rw [AddChar.map_add_eq_mul]
        _ = if (⟨p, hp⟩ + ⟨q, hq⟩ : ↥L) = 0 then (Fintype.card ↥L : ℂ) else 0 :=
            AddChar.sum_apply_eq_ite _
        _ = if q = p then (2 ^ n : ℂ) else 0 := by rw [hcard]; simp only [hzero_iff]
    rw [hsum]
    by_cases hqp : q = p
    · rw [if_pos hqp, if_pos hqp, hqp, mul_right_comm,
        inv_mul_cancel₀ (pow_ne_zero n two_ne_zero), one_mul]
    · rw [if_neg hqp, mul_zero, if_neg hqp]
  · -- Off `L`: every coefficient is zero.
    have hcoeff : ∀ χ : AddChar ↥L ℂ,
        χ ⟨p, hp⟩ * stabCoeff (charSignedStab β hβ0 hβv χ) q = 0 := by
      intro χ
      simp only [stabCoeff, charSignedStab, hq, if_neg, mul_zero, not_false_iff]
    rw [Finset.sum_congr rfl (fun χ _ => hcoeff χ), Finset.sum_const_zero]
    have hqp : q ≠ p := fun h => hq (h ▸ hp)
    rw [if_neg hqp]

/-- Reference signs square to one: `β p · β p = 1` for `p ∈ L`. The reference-sign law (`hβv`) at
`q = p` reads `β p · β p · pauliPhase p p = β (p + p) = β 0 = 1`, with `pauliPhase p p = 1`
(`pauliPhase_self`) and `p + p = 0` (`pauli_add_self`). -/
theorem refSign_mul_self {L : Submodule (ZMod 2) (FTQCLib.Pauli n)} (β : FTQCLib.Pauli n → ℂ)
    (hβ0 : β 0 = 1) (hβv : ∀ p ∈ L, ∀ q ∈ L, β q * β p * pauliPhase p q = β (p + q))
    {p : FTQCLib.Pauli n} (hp : p ∈ L) : β p * β p = 1 := by
  have h := hβv p hp p hp
  rw [pauliPhase_self, mul_one, pauli_add_self, hβ0] at h
  exact h

open scoped Classical in
/-- **Character-sum collapse for `H(p)` (the engine of `lem:span`).** Each Hermitian Pauli on a
Lagrangian `L ∋ p` is recovered as a `β p`-scaled character average of the twisted projectors:
`H(p) = β p · ∑_χ χ⟨p⟩ · stabProjector(charSignedStab … χ)`. Expanding each projector over the
Hermitian-Pauli basis, swapping the `χ`- and `q`-sums, and applying the per-coordinate orthogonality
`charSum_stabCoeff` leaves only the `q = p` term `β p · H(p)`; the outer `β p ·`, with
`β p · β p = 1` (`refSign_mul_self`), recovers `H(p)`. -/
theorem pauliHermitian_eq_char_sum {L : Submodule (ZMod 2) (FTQCLib.Pauli n)}
    (β : FTQCLib.Pauli n → ℂ) (hβ0 : β 0 = 1)
    (hβv : ∀ p ∈ L, ∀ q ∈ L, β q * β p * pauliPhase p q = β (p + q))
    (hrank : finrank (ZMod 2) L = n) {p : FTQCLib.Pauli n} (hp : p ∈ L) :
    pauliHermitian p
      = β p • ∑ χ : AddChar ↥L ℂ, χ ⟨p, hp⟩ • stabProjector (charSignedStab β hβ0 hβv χ) := by
  have key : (∑ χ : AddChar ↥L ℂ, χ ⟨p, hp⟩ • stabProjector (charSignedStab β hβ0 hβv χ))
      = β p • pauliHermitian p := by
    calc (∑ χ : AddChar ↥L ℂ, χ ⟨p, hp⟩ • stabProjector (charSignedStab β hβ0 hβv χ))
        = ∑ χ : AddChar ↥L ℂ, ∑ q : FTQCLib.Pauli n,
            (χ ⟨p, hp⟩ * stabCoeff (charSignedStab β hβ0 hβv χ) q) • pauliHermitian q := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [stabProjector_eq_sum_univ, Finset.smul_sum]
          exact Finset.sum_congr rfl (fun q _ => by rw [smul_smul])
      _ = ∑ q : FTQCLib.Pauli n, ∑ χ : AddChar ↥L ℂ,
            (χ ⟨p, hp⟩ * stabCoeff (charSignedStab β hβ0 hβv χ) q) • pauliHermitian q :=
          Finset.sum_comm
      _ = ∑ q : FTQCLib.Pauli n,
            (∑ χ : AddChar ↥L ℂ, χ ⟨p, hp⟩ * stabCoeff (charSignedStab β hβ0 hβv χ) q)
              • pauliHermitian q := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [← Finset.sum_smul]
      _ = ∑ q : FTQCLib.Pauli n, (if q = p then β p else 0) • pauliHermitian q := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [charSum_stabCoeff β hβ0 hβv hrank hp q]
      _ = β p • pauliHermitian p := by
          simp only [ite_smul, zero_smul]
          rw [Finset.sum_ite_eq' Finset.univ p (fun q => β p • pauliHermitian q)]
          simp only [Finset.mem_univ, if_true]
  rw [key, smul_smul, refSign_mul_self β hβ0 hβv hp, one_smul]

/-! ## `lem:span`: pure stabilizer densities span the operator space -/

/-- **Every Hermitian Pauli lies in the span of the pure stabilizer densities.** Pick a Lagrangian
`L ∋ p` (`exists_lagrangian_mem`) and a reference sign `β` (`exists_refSign`); then
`pauliHermitian_eq_char_sum` writes `H(p)` as a `β p`-scaled finite sum of the twisted projectors
`stabProjector (charSignedStab … χ)`, each of which is an `IsPureStabDensity` (`L` is a full
Lagrangian by `hSL`/`hrank`). Membership follows by `Submodule.smul_mem`, `Submodule.sum_mem`, and
`Submodule.subset_span`. -/
theorem pauliHermitian_mem_span_pureStabDensity (p : FTQCLib.Pauli n) :
    pauliHermitian p ∈ Submodule.span ℂ {ρ : QState n →ₗ[ℂ] QState n | IsPureStabDensity ρ} := by
  obtain ⟨L, hSL, hrank, hpL⟩ := exists_lagrangian_mem p
  obtain ⟨β, hβ0, hβv⟩ := exists_refSign hSL
  rw [pauliHermitian_eq_char_sum β hβ0 hβv hrank hpL]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun χ _ => Submodule.smul_mem _ _ ?_))
  refine Submodule.subset_span ?_
  exact ⟨charSignedStab β hβ0 hβv χ, hSL, hrank, rfl⟩

/-- **`lem:span` (the pure-state span).** The pure stabilizer density operators span all of
`End ℂ (QState n)`. By `pureStabDensity_span_top_of_pauliHermitian_mem` this reduces to every
Hermitian Pauli lying in their span (`pauliHermitian_mem_span_pureStabDensity`), and the Hermitian
Paulis already span the operator space (`pauliHermitian_span_top`). -/
theorem pureStabDensity_span_top :
    Submodule.span ℂ {ρ : QState n →ₗ[ℂ] QState n | IsPureStabDensity ρ} = ⊤ :=
  pureStabDensity_span_top_of_pauliHermitian_mem pauliHermitian_mem_span_pureStabDensity

end FTQCLib.Hilbert
