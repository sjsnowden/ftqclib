/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.MeasurementCollapse
import FTQCLib.Hilbert.LemSpan
import FTQCLib.Hilbert.FrameKernel

/-! # The bridge lemma — stabilizer states as the frame's level-≤2 kernels

The bridge folds the *states* and *measurement* into the frame's exponent calculus: a stabilizer
state is one of the frame's own level-≤2 kernels, restricted to its support coset (Dehaene–De Moor
/ Labib shape).

**Z-type scope:** the support/face clauses hold for Z-type Paulis (`q.X = 0`) — the diagonal
sector. For X-type the support grows and the bridge factors through Clifford covariance, outside
the frame.

The clauses are labelled as follows: (a0) state extraction — the unit eigenvector and its
uniqueness; (a1) the support coset; (a2) the amplitude form. The bounded clauses come first
((a0), (a1), the support face, and the shallow dictionary), then the (a2) amplitude form, stated as
the named `Prop` `StabStateAmplitudeForm`. It is discharged in `FrameBridgeAmplitude.lean` and
`FrameBridgeAmplitudeQuad.lean` (`stabilizerState_isLevel2Kernel_unconditional`).

**Carrier discipline:** `QState n` is the ℓ² space (`EuclideanSpace ℂ (Fin n → ZMod 2)`, where
`stabProjector`/`pauliHermitian`/norms live); `QubitSpace n` is the bare function type (where
`kernel`/`realPhase` live). They are bridged by `toQState` (`Inner.lean`); amplitudes of a `QState`
are read via `toQState.symm`.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hilbert FTQCLib.Hierarchy FTQCLib.Pauli

variable {n : ℕ}

/-! ### (a0) State extraction — the unit eigenvector -/

/-- **(a0), existence half.** Every signed stabilizer has a **unit** vector fixed by every
stabilizer element — the normalized witness of `exists_stabilizerState`. (Uniqueness up to phase is
the separate rank-1 lemma, which needs the full-Lagrangian hypothesis.) -/
theorem stabilizerState_unit_eigen (S : SignedStab n) :
    ∃ ψ : QState n, ‖ψ‖ = 1 ∧ ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ := by
  obtain ⟨ψ, hψ_ne, hψ_fix⟩ := exists_stabilizerState S
  have hne : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ_ne
  refine ⟨((‖ψ‖ : ℂ))⁻¹ • ψ, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hne]
  · intro g hg
    rw [map_smul, hψ_fix g hg]

/-! ### (a0) Uniqueness — the projector is rank one -/

/-- **(a0), uniqueness half.** For a **full Lagrangian** (`|L| = 2ⁿ`) the stabilizer projector is
**rank one**: its range is `1`-dimensional. An idempotent (`stabProjector_idem`, needs `|L| = 2ⁿ`)
self-adjoint operator with trace `1` projects onto a line — so the unit eigenvector `ψ_S` is unique up
to phase, and any stabilizer eigenvector is a scalar multiple of it (`IsProj.trace`: `tr = finrank`). -/
theorem stabProjector_finrank_range_eq_one (S : SignedStab n)
    (hcard : (Set.toFinite (S.L : Set (Pauli n))).toFinset.card = 2 ^ n) :
    Module.finrank ℂ (LinearMap.range (stabProjector S)) = 1 := by
  have hproj : LinearMap.IsProj (LinearMap.range (stabProjector S)) (stabProjector S) :=
    ⟨fun x => LinearMap.mem_range_self _ x,
     fun x hx => by
       obtain ⟨y, rfl⟩ := hx
       exact LinearMap.congr_fun (stabProjector_idem S hcard) y⟩
  have h := hproj.trace
  rw [stabProjector_trace S] at h
  exact_mod_cast h.symm

/-- **Explicit support of the projector on a basis vector.** `stabProjector S |u⟩` is supported on
the coset `u + π_X(L)`: each `H(p)|u⟩` (`p ∈ L`) lands on `u + p.X`, and off-`L` terms vanish
(`stabCoeff = 0`). With rank-one this gives `supp ⊆ coset` for every eigenvector; it is also the
seed of the (a2) fiber-sum amplitude. -/
theorem stabProjector_qComputational_support (S : SignedStab n) (u w : Fin n → ZMod 2)
    (hw : stabProjector S (qComputational u) w ≠ 0) :
    ∃ p ∈ S.L, w = u + p.X := by
  by_contra hcon
  push_neg at hcon
  apply hw
  rw [← toQState_symm_apply, stabProjector_eq_sum_univ, LinearMap.sum_apply, map_sum,
    Finset.sum_apply]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rw [toQState_symm_apply]
  by_cases hp : p ∈ S.L
  · have hne : w ≠ u + p.X := hcon p hp
    rw [LinearMap.smul_apply, pauliHermitian_qComputational]
    simp [PiLp.smul_apply, qComputational_eq_single, hne]
  · have h0 : stabCoeff S p = 0 := by simp [stabCoeff, hp]
    rw [LinearMap.smul_apply, h0, zero_smul]
    simp

/-! ### (a1) Support coset — containment in the Z-hyperplanes -/

/-- **(a1), containment half.** For a unit eigenvector `ψ` of the sector `S` and a **Z-type**
stabilizer element `g ∈ S.L` (`g.X = 0`), the support of `ψ` lies in the Z-hyperplane
`{w : (-1)^{g.Z·w} = S.sign g}`: wherever `ψ w ≠ 0`, the diagonal sign forced by `g`
matches `S.sign g`. This is the bounded half of `supp(ψ) = A_S`; for Z-type `g` the Hermitian
Pauli acts diagonally (`xzWeight g = 0`, no support shift), so the eigen-equation is pointwise. -/
theorem signedStab_support_subset (S : SignedStab n) (ψ : QState n)
    (hψ : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    {g : Pauli n} (hg : g ∈ S.L) (hgZ : g.X = 0)
    {w : Fin n → ZMod 2} (hw : ψ w ≠ 0) :
    S.sign g * (-1 : ℂ) ^ (zDotVal g w) = 1 := by
  have hpt : ((S.sign g • pauliHermitian g) ψ) w = ψ w := by rw [hψ g hg]
  rw [LinearMap.smul_apply, PiLp.smul_apply, pauliHermitian_apply_fun, hgZ, sub_zero,
    smul_eq_mul] at hpt
  have hxz : xzWeight g = 0 := by unfold xzWeight; rw [hgZ]; unfold zDotVal; simp
  rw [hxz, pow_zero, one_mul, ← mul_assoc] at hpt
  exact mul_right_cancel₀ hw (by rw [one_mul]; exact hpt)

/-- **Amplitude transport** (the (a1)→(a2) workhorse). For any stabilizer element `p ∈ S.L`, the
eigen-equation relates the amplitude at `w` to the amplitude at `w - p.X` by a **unit-modulus**
factor `S.sign p · iˣᶻ · (-1)^{p.Z·(w-p.X)}`. The X-part `p.X` transports amplitude across the
support coset (giving constant modulus and the (a1) equality); the accumulated phase along a path
is the quadratic exponent `q_S` of (a2). Direct from `pauliHermitian_apply_fun`. -/
theorem signedStab_amplitude_transport (S : SignedStab n) (ψ : QState n)
    (hψ : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    {p : Pauli n} (hp : p ∈ S.L) (w : Fin n → ZMod 2) :
    ψ w = (S.sign p * Complex.I ^ xzWeight p * (-1 : ℂ) ^ zDotVal p (w - p.X)) * ψ (w - p.X) := by
  have hpt : ((S.sign p • pauliHermitian p) ψ) w = ψ w := by rw [hψ p hp]
  rw [LinearMap.smul_apply, PiLp.smul_apply, pauliHermitian_apply_fun, smul_eq_mul] at hpt
  rw [← hpt]; ring

/-- **Constant modulus** (the (a1) modulus clause, per step). The transport factor is unit-modulus
(`|S.sign p| = 1` by `sign_mul_self`, `|iˣᶻ| = |(-1)^·| = 1`), so `|ψ|` agrees at `w` and `w - p.X`.
Iterating over `p ∈ L` makes `|ψ|` constant on the support coset `A_S` (the `π_X(L)`-orbit). -/
theorem signedStab_modulus_transport (S : SignedStab n) (ψ : QState n)
    (hψ : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    {p : Pauli n} (hp : p ∈ S.L) (w : Fin n → ZMod 2) :
    ‖ψ w‖ = ‖ψ (w - p.X)‖ := by
  have hsign : ‖S.sign p‖ = 1 := by
    rcases mul_self_eq_one_iff.mp (sign_mul_self S hp) with h | h
    · rw [h, norm_one]
    · rw [h, norm_neg, norm_one]
  have hc : ‖S.sign p * Complex.I ^ xzWeight p * (-1 : ℂ) ^ zDotVal p (w - p.X)‖ = 1 := by
    simp [norm_pow, Complex.norm_I, hsign]
  rw [signedStab_amplitude_transport S ψ hψ hp w, norm_mul, hc, one_mul]

/-- **(a1) coset ⊆ support** (the easy half of `supp = A_S`). If `ψ x₀ ≠ 0`, then `ψ` is nonzero at
every coset point `x₀ + p.X` for `p ∈ L`: transport from `x₀ + p.X` back to `x₀` is a unit-modulus
(hence nonzero) factor. The reverse containment (support ⊆ coset) is the X-transport / self-duality
half. -/
theorem signedStab_coset_subset_support (S : SignedStab n) (ψ : QState n)
    (hψ : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    {x₀ : Fin n → ZMod 2} (hx₀ : ψ x₀ ≠ 0) {p : Pauli n} (hp : p ∈ S.L) :
    ψ (x₀ + p.X) ≠ 0 := by
  rw [signedStab_amplitude_transport S ψ hψ hp (x₀ + p.X)]
  have hsub : x₀ + p.X - p.X = x₀ := by abel
  rw [hsub]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) hx₀
  · intro h0; have h := sign_mul_self S hp; rw [h0, mul_zero] at h; exact zero_ne_one h
  · exact pow_ne_zero _ Complex.I_ne_zero
  · exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)

/-- **(a1) support ⊆ coset** (the X-transport, rank-one half). For a full Lagrangian, a stabilizer
eigenvector `ψ` has support inside a single coset `x₀ + π_X(L)` (any `x₀ ∈ supp`): `ψ` sits in the
1-dim projector range (`stabProjector S ψ = ψ`), and `stabProjector S |x₀⟩` is nonzero there
(`⟪·, ψ⟫ = ψ x₀ ≠ 0`), so `ψ` is proportional to it and inherits its coset support
(`stabProjector_qComputational_support`). With `coset ⊆ support` this gives `supp ψ = x₀ + π_X(L)`. -/
theorem signedStab_support_subset_coset (S : SignedStab n) (ψ : QState n)
    (hcard : (Set.toFinite (S.L : Set (Pauli n))).toFinset.card = 2 ^ n)
    (hψfix : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    {x₀ : Fin n → ZMod 2} (hx₀ : ψ x₀ ≠ 0) {w : Fin n → ZMod 2} (hw : ψ w ≠ 0) :
    ∃ p ∈ S.L, w = x₀ + p.X := by
  have hfix : stabProjector S ψ = ψ := by
    show ((2 ^ n : ℂ)⁻¹ • ∑ p ∈ (Set.toFinite (S.L : Set (Pauli n))).toFinset,
        S.sign p • pauliHermitian p) ψ = ψ
    rw [LinearMap.smul_apply, LinearMap.sum_apply,
      Finset.sum_congr rfl (fun p hp => hψfix p ((Set.Finite.mem_toFinset _).mp hp)),
      Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (pow_ne_zero n two_ne_zero), one_smul]
  set φ₀ := stabProjector S (qComputational x₀) with hφ₀def
  have hsym : (stabProjector S).IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (stabProjector_isSelfAdjoint S)
  have hinner : inner ℂ φ₀ ψ = ψ x₀ := by
    rw [hφ₀def, hsym (qComputational x₀) ψ, hfix, qComputational_eq_single,
      EuclideanSpace.inner_single_left, map_one, one_mul]
  have hφ₀ne : φ₀ ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at hinner; exact hx₀ hinner.symm
  have hφ₀mem : φ₀ ∈ LinearMap.range (stabProjector S) := LinearMap.mem_range_self _ _
  have hψmem : ψ ∈ LinearMap.range (stabProjector S) := ⟨ψ, hfix⟩
  have hspan : LinearMap.range (stabProjector S) = Submodule.span ℂ {φ₀} := by
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · rw [Submodule.span_singleton_le_iff_mem]; exact hφ₀mem
    · rw [finrank_span_singleton hφ₀ne, stabProjector_finrank_range_eq_one S hcard]
  rw [hspan] at hψmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hψmem
  have hφ₀w : φ₀ w ≠ 0 := fun h0 => hw (by rw [← hc, PiLp.smul_apply, h0, smul_zero])
  exact stabProjector_qComputational_support S x₀ w hφ₀w

/-- **(a1) support = coset** (the full support-iff). For a full Lagrangian, a nonzero stabilizer
eigenvector has `supp ψ = x₀ + π_X(L)` for any base point `x₀ ∈ supp`: assembles
`signedStab_support_subset_coset` (forward) with `signedStab_coset_subset_support` (backward). This
is the support clause of `StabStateAmplitudeForm`. -/
theorem signedStab_support_iff (S : SignedStab n) (ψ : QState n)
    (hcard : (Set.toFinite (S.L : Set (Pauli n))).toFinset.card = 2 ^ n)
    (hψfix : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) (hψne : ψ ≠ 0) :
    ∃ x₀ : Fin n → ZMod 2, ∀ w, ψ w ≠ 0 ↔ ∃ p ∈ S.L, w = x₀ + p.X := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ x₀ ≠ 0 := by
    by_contra hcon; push_neg at hcon
    refine hψne ((LinearEquiv.map_eq_zero_iff toQState.symm).mp ?_)
    funext w; rw [toQState_symm_apply]; exact hcon w
  refine ⟨x₀, fun w => ⟨fun hw => signedStab_support_subset_coset S ψ hcard hψfix hx₀ hw, ?_⟩⟩
  rintro ⟨p, hp, rfl⟩
  exact signedStab_coset_subset_support S ψ hψfix hx₀ hp

/-- **Amplitude on the coset** (the formula `q_S` must reproduce). For `p ∈ L`, the support point
`x₀ + p.X` carries the single μ₄ factor `S.sign p · iˣᶻ · (-1)^{p.Z·x₀}` times the base amplitude
`ψ x₀`. The factor is independent of the lift `p` (well-defined on `π_X(L)`, since `ψ x₀` is fixed),
and its three pieces are exactly the (a2) exponent: the sign `= i^{2·}`, the `iˣᶻ` (the genuine
degree-2 part via `xzWeight`), and the `(-1)^{p.Z·x₀} = i^{2·}` linear part. -/
theorem signedStab_amplitude_on_coset (S : SignedStab n) (ψ : QState n)
    (hψ : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    (x₀ : Fin n → ZMod 2) {p : Pauli n} (hp : p ∈ S.L) :
    ψ (x₀ + p.X) = (S.sign p * Complex.I ^ xzWeight p * (-1 : ℂ) ^ zDotVal p x₀) * ψ x₀ := by
  have h := signedStab_amplitude_transport S ψ hψ hp (x₀ + p.X)
  rwa [show x₀ + p.X - p.X = x₀ from by abel] at h

/-! ### (a2) Amplitude form, isolated behind a named `Prop` -/

/-- **A global linear lift of `π_X(L)` into `L`.** There is a linear `τ : 𝔽₂ⁿ → Pauli n` that, on the
X-projection `π_X(L)`, lands in `L` and inverts `xProj` (`τ y ∈ L`, `(τ y).X = y`). A right inverse of
the surjection `L ↠ π_X(L)` (`exists_rightInverse_of_surjective`), extended off `π_X(L)` to the whole
space (`LinearMap.exists_extend`). Linearity is what makes the amplitude factor `F ∘ τ` a degree-≤2
polynomial in `w`, hence the level-≤2 exponent `q_S`. -/
theorem exists_piX_lift (L : Submodule (ZMod 2) (FTQCLib.Pauli n)) :
    ∃ τ : (Fin n → ZMod 2) →ₗ[ZMod 2] FTQCLib.Pauli n,
      ∀ y ∈ Submodule.map xProj L, τ y ∈ L ∧ (τ y).X = y := by
  set f : ↥L →ₗ[ZMod 2] (Fin n → ZMod 2) := xProj ∘ₗ L.subtype with hf
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨τ, hτ⟩ := (L.subtype ∘ₗ g).exists_extend
  have hrange : LinearMap.range f = Submodule.map xProj L := by
    rw [hf, LinearMap.range_comp, Submodule.range_subtype]
  refine ⟨τ, fun y hy => ?_⟩
  rw [← hrange] at hy
  have hτy : τ y = (g ⟨y, hy⟩ : FTQCLib.Pauli n) := by
    have h := LinearMap.congr_fun hτ ⟨y, hy⟩; simpa using h
  have hgx : f (g ⟨y, hy⟩) = y :=
    congrArg Subtype.val (LinearMap.congr_fun hg ⟨y, hy⟩)
  refine ⟨hτy ▸ (g ⟨y, hy⟩).2, ?_⟩
  rw [hτy, ← xProj_apply]
  exact hgx

/-- **(a2) — the Dehaene–De Moor amplitude form.** For a full-rank
sector `S` (`finrank L = n`, a Lagrangian) and a **nonzero** joint stabilizer eigenvector `ψ`, there
are a base point `x₀`, a frame exponent `q` of **level ≤ 2**, and a constant `c` with:

* **support is the affine coset** `x₀ + π_X(L)`: `ψ w ≠ 0 ↔ ∃ p ∈ L, w = x₀ + p.X` (DDM (1)+(3));
* on that support `ψ w = c · exp(i · realPhase q w)` — the `μ₄`/1/4-stratum quadratic phase (DDM (4)).

Uniform modulus (`|ψ w| = |c|`, DDM (2)) is then automatic (`exp` is unit-modulus) and `|c| = 2^{-d/2}`
follows from `‖ψ‖ = 1`. This is exactly **Dehaene–De Moor Thm 5(ii)** (qubit, Z-type/diagonal scope).
The value group is `μ₄` (the `i`-power gives a precision-2 *linear* term, the cocycle a degree-2
*order-2* term, so `effectiveLevel = 2`, tight — level 3 needs T's precision-3 or CCZ's degree-3,
both non-Clifford), and the support clause is what makes the named statement faithful rather than
just its phase half. Labib's depth-≤1 nonclassical quadratic phase is independent agreement in the
literature. Isolated as a named `Prop`; discharged via the explicit projector / amplitude transport
in `FrameBridgeAmplitude.lean` and `FrameBridgeAmplitudeQuad.lean`. -/
def StabStateAmplitudeForm (n : ℕ) : Prop :=
  ∀ (S : SignedStab n) (ψ : QState n),
    Module.finrank (ZMod 2) S.L = n → ψ ≠ 0 →
    (∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) →
    ∃ (m : ℕ) (q : DiagPhase n m) (c : ℂ) (x₀ : Fin n → ZMod 2),
      DiagPhase.effectiveLevel q ≤ 2 ∧
        (∀ w, ψ w ≠ 0 ↔ ∃ p ∈ S.L, w = x₀ + p.X) ∧
        (∀ w, ψ w ≠ 0 → ψ w = c * Complex.exp (Complex.I * (DiagPhase.realPhase q w : ℂ)))

/-- **Bridge theorem — stabilizer states are the frame's level-≤2 kernels on their support coset**
(conditional on the (a2) amplitude form `StabStateAmplitudeForm`). Every full-rank sector has a
**unit** stabilizer state whose support is the affine coset `x₀ + π_X(L)` and on it equals
`c · exp(i · realPhase q)` for a frame exponent `q` of **level ≤ 2** — i.e. Dehaene–De Moor
Thm 5(ii), the stabilizer fragment realized as objects *of* the kernel frame. Composes the (a0)
existence half (`stabilizerState_unit_eigen`) with the (a2) amplitude form. The unconditional form
is `stabilizerState_isLevel2Kernel_unconditional`. -/
theorem stabilizerState_isLevel2Kernel (ha2 : StabStateAmplitudeForm n)
    (S : SignedStab n) (hL : Module.finrank (ZMod 2) S.L = n) :
    ∃ (ψ : QState n) (m : ℕ) (q : DiagPhase n m) (c : ℂ) (x₀ : Fin n → ZMod 2),
      ‖ψ‖ = 1 ∧ (∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) ∧
        DiagPhase.effectiveLevel q ≤ 2 ∧
          (∀ w, ψ w ≠ 0 ↔ ∃ p ∈ S.L, w = x₀ + p.X) ∧
          (∀ w, ψ w ≠ 0 → ψ w = c * Complex.exp (Complex.I * (DiagPhase.realPhase q w : ℂ))) := by
  obtain ⟨ψ, hψnorm, hψfix⟩ := stabilizerState_unit_eigen S
  have hψne : ψ ≠ 0 := norm_ne_zero_iff.mp (by rw [hψnorm]; exact one_ne_zero)
  obtain ⟨m, q, c, x₀, hlvl, hsupp, hform⟩ := ha2 S ψ hL hψne hψfix
  exact ⟨ψ, m, q, c, x₀, hψnorm, hψfix, hlvl, hsupp, hform⟩

/-! ### Shallow dictionary — the post-measurement sign carrier -/

/-- **Dictionary, shallow half** (`(a0)+(a1)` outcome-carrier, ε-in-χ′ clause). On the conditioned
sector, the measured Pauli carries the outcome `ε`, and on its δ=1 coset the post-measurement sign is
the ε-twisted original. A direct repackaging of the proven `measSign` facts. -/
theorem dictionary_sign_carrier (S : SignedStab n) (Q M : Pauli n) (ε : ℂ) (hMQ : omega M Q = 1) :
    measSign S Q M ε Q = ε ∧
      (∀ g ∈ FTQCLib.Stabilizer.pauliCondition S.L Q, omega M g = 1 →
        measSign S Q M ε g = ε * S.sign (g + Q) * pauliPhase Q (g + Q)) :=
  ⟨measSign_Q S Q M ε hMQ, fun _g hg hδ => measSign_of_one S Q M ε hg hδ⟩

end FTQCLib.Frame
