/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.Trace
import ECCLib.GaussSum

set_option linter.style.longLine false
-- The `Fintype F` / `DecidableEq ι` instances below are used in the *proofs* (the delta expansion
-- sums over `ι → F`), not in the statements; the linter's `Finite` suggestion does not apply.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The Weyl operator layer over 𝔽_q — the Schrödinger representation

The translation–modulation algebra of the discrete Fourier transform on `𝔽_q^ι`: the historical
"Heisenberg/Schrödinger" objects, stripped to their harmonic-analysis content. Carrier
`(ι → F) → ℂ`, mirroring the char-2 `QubitSpace n = (Fin n → ZMod 2) → ℂ` of `FTQCLib` so the char-2
proof shapes (`operator_scalar_of_centralizes_pauli`) transfer.

This file: the operators, their actions on the delta basis, the composition laws, and the braiding
(Weyl) relation `T_a ∘ M_b = ψ⟨b,a⟩ • (M_b ∘ T_a)`. The Schur/commutant theorem follows in the next
layer.

**Boundary (a deliberate choice).** `Heis` bakes `[Fintype ι]` into its
definition, and the whole development is tied to the **split model**: the symplectic space is
`V = (ι→F) × (ι→F)` with the standard pairing `⟨b,x⟩ = Σ bᵢxᵢ` and the standard symplectic form
built from it. A consumer with an *intrinsic* symplectic space `(V, ω)` must first choose a
polarization (a Lagrangian splitting) to land here — standard, but it is a genuine step this
library does not perform for them. Symplectic-basis existence is the classical route
(Artin; Grove).
-/

namespace ECCLib.Heisenberg

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-- The standard pairing `⟨b, x⟩ = ∑ i, bᵢ·xᵢ` on the position space. -/
def pairing (b x : ι → F) : F := ∑ i, b i * x i

lemma pairing_add_right (b y a : ι → F) : pairing b (y + a) = pairing b y + pairing b a := by
  unfold pairing
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]

lemma pairing_add_left (b b' y : ι → F) : pairing (b + b') y = pairing b y + pairing b' y := by
  unfold pairing
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_mul]

lemma pairing_symm (b x : ι → F) : pairing b x = pairing x b := by
  unfold pairing
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

@[simp] lemma pairing_zero_left (y : ι → F) : pairing (0 : ι → F) y = 0 := by
  unfold pairing
  exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, zero_mul]

@[simp] lemma pairing_zero_right (b : ι → F) : pairing b (0 : ι → F) = 0 := by
  unfold pairing
  exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, mul_zero]

lemma pairing_neg_left (b y : ι → F) : pairing (-b) y = - pairing b y := by
  unfold pairing
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply, neg_mul]

lemma pairing_neg_right (b y : ι → F) : pairing b (-y) = - pairing b y := by
  unfold pairing
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply, mul_neg]

open Classical in
/-- The delta function at `x` (the "computational basis" of the char-2 instance). -/
noncomputable def delta (x : ι → F) : (ι → F) → ℂ := fun y => if y = x then 1 else 0

/-- **Translation** `(T_a f)(y) = f(y + a)`. -/
def translation (a : ι → F) : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) where
  toFun f := fun y => f (y + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Modulation** `(M_b f)(y) = ψ(⟨b,y⟩)·f(y)`. -/
def modulation (ψ : AddChar F ℂ) (b : ι → F) : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) where
  toFun f := fun y => ψ (pairing b y) * f y
  map_add' f g := by
    funext y
    simp [mul_add]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype ι] in
@[simp] lemma translation_apply (a : ι → F) (f : (ι → F) → ℂ) (y : ι → F) :
    translation a f y = f (y + a) := rfl

@[simp] lemma modulation_apply (ψ : AddChar F ℂ) (b : ι → F) (f : (ι → F) → ℂ) (y : ι → F) :
    modulation ψ b f y = ψ (pairing b y) * f y := rfl

open Classical in
/-- Translation moves deltas: `T_a δ_x = δ_{x−a}`. -/
theorem translation_delta (a x : ι → F) :
    translation a (delta x) = delta (x - a) := by
  funext y
  simp only [translation_apply, delta]
  by_cases h : y + a = x
  · rw [if_pos h, if_pos (by rw [← h]; ring)]
  · rw [if_neg h, if_neg (fun hc => h (by rw [hc]; ring))]

open Classical in
/-- Modulation scales deltas: `M_b δ_x = ψ(⟨b,x⟩)·δ_x`. -/
theorem modulation_delta (ψ : AddChar F ℂ) (b x : ι → F) :
    modulation ψ b (delta x) = ψ (pairing b x) • delta x := by
  funext y
  simp only [modulation_apply, delta, Pi.smul_apply, smul_eq_mul]
  by_cases h : y = x
  · rw [if_pos h, h]
  · rw [if_neg h]
    ring

omit [Fintype ι] in
/-- Translations compose additively. -/
theorem translation_comp (a a' : ι → F) :
    translation a ∘ₗ translation a' = translation (a + a') (F := F) (ι := ι) := by
  ext f y
  simp only [LinearMap.comp_apply, translation_apply]
  rw [add_assoc]

/-- Modulations compose additively. -/
theorem modulation_comp (ψ : AddChar F ℂ) (b b' : ι → F) :
    modulation ψ b ∘ₗ modulation ψ b' = modulation ψ (b + b') := by
  ext f y
  simp only [LinearMap.comp_apply, modulation_apply]
  rw [pairing_add_left, AddChar.map_add_eq_mul]
  ring

/-- **The braiding (Weyl) relation**: `T_a ∘ M_b = ψ(⟨b,a⟩) • (M_b ∘ T_a)` — translations and
modulations commute up to the scalar `ψ(⟨b,a⟩)`, the germ of the Heisenberg central extension. -/
theorem translation_comp_modulation (ψ : AddChar F ℂ) (a b : ι → F) :
    translation a ∘ₗ modulation ψ b
      = ψ (pairing b a) • (modulation ψ b ∘ₗ translation a) := by
  ext f y
  simp only [LinearMap.comp_apply, translation_apply, modulation_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [pairing_add_right, AddChar.map_add_eq_mul]
  ring

/-! ### The Schur/commutant theorem -/

/-- `ψ` never vanishes: `ψ(p)·ψ(−p) = ψ(0) = 1`. -/
lemma addChar_ne_zero (ψ : AddChar F ℂ) (p : F) : ψ p ≠ 0 := fun h0 => by
  have h1 : ψ p * ψ (-p) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

open Classical in
/-- **Separation**: a nontrivial `ψ` composed with the pairing separates points — for `z ≠ 0`,
some `b` has `ψ(⟨b,z⟩) ≠ 1`. -/
theorem exists_pairing_ne_one {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {z : ι → F} (hz : z ≠ 0) :
    ∃ b : ι → F, ψ (pairing b z) ≠ 1 := by
  obtain ⟨c, hc⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨i₀, hi₀⟩ : ∃ i, z i ≠ 0 := Function.ne_iff.mp hz
  refine ⟨fun j => if j = i₀ then c * (z i₀)⁻¹ else 0, ?_⟩
  have hpair : pairing (fun j => if j = i₀ then c * (z i₀)⁻¹ else 0) z = c := by
    unfold pairing
    rw [Finset.sum_eq_single i₀]
    · dsimp only
      rw [if_pos rfl, mul_assoc, inv_mul_cancel₀ hi₀, mul_one]
    · intro j _ hj
      dsimp only
      rw [if_neg hj, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rwa [hpair]

section Irreducibility

variable [Fintype F] [DecidableEq ι]

omit [Field F] in
open Classical in
/-- Every function is the delta-expansion of its values. -/
lemma eq_sum_smul_delta (f : (ι → F) → ℂ) : f = ∑ x : ι → F, f x • delta x := by
  funext y
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, delta, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.univ) y f, if_pos (Finset.mem_univ y)]

/-- `b ↦ ψ(⟨b,z⟩)` as an additive character of the momentum space — the character whose orthogonality
extracts deltas. -/
def pairingChar (ψ : AddChar F ℂ) (z : ι → F) : AddChar (ι → F) ℂ where
  toFun b := ψ (pairing b z)
  map_zero_eq_one' := by rw [pairing_zero_left, AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by rw [pairing_add_left, AddChar.map_add_eq_mul]

omit [Fintype F] [DecidableEq ι] in
@[simp] lemma pairingChar_apply (ψ : AddChar F ℂ) (z b : ι → F) :
    pairingChar ψ z b = ψ (pairing b z) := rfl

/-- **Character orthogonality on the momentum space**: `∑_b ψ⟨b,z⟩ = 0` for `z ≠ 0`. This is
`exists_pairing_ne_one` (separation) fed to `AddChar.sum_eq_zero_of_ne_one`. -/
theorem sum_pairingChar_eq_zero {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {z : ι → F} (hz : z ≠ 0) : ∑ b : ι → F, ψ (pairing b z) = 0 := by
  -- `0` is the trivial character in `AddChar`'s additive notation
  have hne : pairingChar ψ z ≠ 0 := by
    obtain ⟨b, hb⟩ := exists_pairing_ne_one hψ hz
    exact AddChar.ne_zero_iff.mpr ⟨b, hb⟩
  simpa using AddChar.sum_eq_zero_iff_ne_zero.mpr hne

open Classical in
/-- **Schur for the Weyl algebra over `𝔽_q`**: an operator commuting with every translation and
every modulation is a scalar multiple of the identity. The general-characteristic form of the
char-2 `operator_scalar_of_centralizes_pauli`, by the same two-step diagonal argument: modulations
separate points (killing off-diagonal components), translations act transitively (forcing the
diagonal constant). -/
theorem operator_scalar_of_commutes {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (T : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ))
    (hTr : ∀ a, T ∘ₗ translation a = translation a ∘ₗ T)
    (hMo : ∀ b, T ∘ₗ modulation ψ b = modulation ψ b ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  -- Step A: `T δ_x` is supported at `x`
  have hsupp : ∀ x w : ι → F, w ≠ x → T (delta x) w = 0 := by
    intro x w hwx
    obtain ⟨b, hb⟩ := exists_pairing_ne_one hψ (sub_ne_zero.mpr hwx)
    have h := congrFun (congrArg (fun S : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) =>
      S (delta x)) (hMo b)) w
    simp only [LinearMap.comp_apply, modulation_delta, map_smul, Pi.smul_apply,
      smul_eq_mul, modulation_apply] at h
    -- h : ψ⟨b,x⟩ · (T δ_x) w = ψ⟨b,w⟩ · (T δ_x) w
    have hw : x + (w - x) = w := by
      funext i
      simp
    have hfac : ψ (pairing b w) = ψ (pairing b x) * ψ (pairing b (w - x)) := by
      rw [← AddChar.map_add_eq_mul, ← pairing_add_right, hw]
    rw [hfac, mul_assoc] at h
    have hcanc := mul_left_cancel₀ (addChar_ne_zero ψ (pairing b x)) h
    -- hcanc : (T δ_x) w = ψ⟨b,w−x⟩ · (T δ_x) w — a nontrivial eigenvalue forces zero
    by_contra ht
    have h1 : ψ (pairing b (w - x)) * T (delta x) w = 1 * T (delta x) w := by
      rw [one_mul, ← hcanc]
    exact hb (mul_right_cancel₀ ht h1)
  -- `T δ_x = c_x • δ_x`
  have hdiag : ∀ x : ι → F, T (delta x) = (T (delta x) x) • delta x := by
    intro x
    funext w
    by_cases hwx : w = x
    · subst hwx
      simp [delta]
    · rw [hsupp x w hwx, Pi.smul_apply]
      simp [delta, hwx]
  -- Step B: the diagonal is constant
  have hconst : ∀ x : ι → F, T (delta x) x = T (delta 0) 0 := by
    intro x
    have h := congrArg (fun S : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) => S (delta x)) (hTr x)
    simp only [LinearMap.comp_apply, translation_delta, sub_self] at h
    -- h : T δ_0 = T_x (T δ_x)
    rw [hdiag x, map_smul, translation_delta, sub_self] at h
    have := congrFun h 0
    rw [hdiag 0] at this
    simp only [Pi.smul_apply, delta, if_true, smul_eq_mul, mul_one] at this
    exact this.symm
  -- Step C: linearity closes
  refine ⟨T (delta 0) 0, LinearMap.ext fun f => ?_⟩
  conv_lhs => rw [eq_sum_smul_delta f]
  rw [map_sum]
  have hterm : ∀ x : ι → F, T (f x • delta x) = T (delta 0) 0 • (f x • delta x) := by
    intro x
    rw [map_smul, hdiag x, hconst x, smul_comm]
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.smul_sum, ← eq_sum_smul_delta]
  rfl

end Irreducibility

/-- **Averaging extracts a delta.** For any `f`, `∑_b ψ(−⟨b,x⟩)·(M_b f) = |V|·f(x)·δ_x`. This is
Maschke's averaging mechanism applied to the (abelian) modulation subgroup: the average against the
character `b ↦ ψ(⟨b,x⟩)` is exactly the projection onto the `δ_x` line. -/
theorem sum_modulation_smul_eq [Fintype F] [DecidableEq ι] {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (f : (ι → F) → ℂ) (x : ι → F) :
    ∑ b : ι → F, ψ (-(pairing b x)) • modulation ψ b f
      = ((Fintype.card (ι → F) : ℂ) * f x) • delta x := by
  classical
  funext y
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, modulation_apply, smul_eq_mul, delta]
  by_cases hxy : y = x
  · subst hxy
    rw [if_pos rfl, mul_one]
    have : ∀ b : ι → F, ψ (-(pairing b y)) * (ψ (pairing b y) * f y) = f y := by
      intro b
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_const, nsmul_eq_mul,
      ← Fintype.card]
  · rw [if_neg hxy, mul_zero]
    have hz : y - x ≠ 0 := sub_ne_zero.mpr hxy
    have hterm : ∀ b : ι → F, ψ (-(pairing b x)) * (ψ (pairing b y) * f y)
        = ψ (pairing b (y - x)) * f y := by
      intro b
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      rw [sub_eq_add_neg, pairing_add_right, pairing_neg_right]
      ring
    rw [Finset.sum_congr rfl fun b _ => hterm b, ← Finset.sum_mul,
      sum_pairingChar_eq_zero hψ hz, zero_mul]

/-- **The Schrödinger representation is irreducible** (no-invariant-subspace form). Any subspace
invariant under all translations and modulations is `⊥` or `⊤`.

This is the form Stone–von Neumann is stated in, as opposed to the commutant form
(`operator_scalar_of_commutes`). The proof is constructive and needs neither Schur nor Mathlib's
Maschke: averaging over the modulation subgroup (`sum_modulation_smul_eq` — Maschke's own mechanism)
pulls an explicit `δ_x` out of any nonzero `f ∈ M`, and the translations then sweep `δ_x` across every
point, so `M` contains a basis. -/
theorem irreducible_of_invariant [Fintype F] [DecidableEq ι] {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (M : Submodule ℂ ((ι → F) → ℂ))
    (hT : ∀ a, ∀ f ∈ M, translation a f ∈ M)
    (hM : ∀ b, ∀ f ∈ M, modulation ψ b f ∈ M) :
    M = ⊥ ∨ M = ⊤ := by
  classical
  rcases eq_or_ne M ⊥ with h | h
  · exact Or.inl h
  refine Or.inr ?_
  -- a nonzero element, and a point where it does not vanish
  obtain ⟨f, hfM, hf0⟩ := (Submodule.ne_bot_iff M).mp h
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := Function.ne_iff.mp hf0
  -- averaging over the modulations puts `δ_x` in `M`
  have hcard : (Fintype.card (ι → F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdelta : delta x ∈ M := by
    have hsum : ∑ b : ι → F, ψ (-(pairing b x)) • modulation ψ b f ∈ M :=
      Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hM b f hfM)
    rw [sum_modulation_smul_eq hψ f x] at hsum
    have := Submodule.smul_mem M (((Fintype.card (ι → F) : ℂ) * f x)⁻¹) hsum
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hcard hx), one_smul] at this
  -- translations sweep it across every point
  have hall : ∀ y : ι → F, delta y ∈ M := by
    intro y
    have := hT (x - y) _ hdelta
    rwa [translation_delta, sub_sub_cancel] at this
  -- so `M` contains the delta basis, hence everything
  refine Submodule.eq_top_iff'.mpr fun g => ?_
  rw [eq_sum_smul_delta g]
  exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (hall y)

/-! ### The Weyl operators

`W(p,m) = ψ(½⟨m,p⟩)·M_m∘T_p` — the **½-normalized** (symmetric) Weyl operator. The normalization is
what makes the composition cocycle the *symplectic form itself* (`weyl_comp`), rather than the
polarization `⟨m_y,p_x⟩`; and `ω` is `Sp`-invariant by definition while the polarization is not. That
is the whole reason for the ½: it is what lets `Sp` act on the group object below, which is the first
step of the Weil representation. Requires `2 ≠ 0`, i.e. odd characteristic — and that requirement is
not an artifact: at `char = 2` no such normalization exists, which is exactly why the char-2 instance
(`FTQCLib/Cohomology/PauliExtension.lean`) needs a `ℤ/4`-valued centre instead. -/

/-- The **½-normalized Weyl operator** `W(p,m) = ψ(½⟨m,p⟩)·M_m∘T_p`.

*Disambiguation* — the library has four distinct "Weyl/Fourier" objects: **this** `weyl` (the
½-normalized operator on functions), `Siegel.weyl` (the linear equivalence `(p,m) ↦ (m,−p)` on the
vector space `W`), `Heis.fourierMap` (the same Weyl element as a symplectic map of the Heisenberg
group), and `fourierOp` (the DFT, `fourierMap`'s Weil operator). -/
noncomputable def weyl (ψ : AddChar F ℂ) (p m : ι → F) : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) :=
  ψ ((2 : F)⁻¹ * pairing m p) • (modulation ψ m ∘ₗ translation p)

@[simp] lemma weyl_apply (ψ : AddChar F ℂ) (p m : ι → F) (f : (ι → F) → ℂ) (y : ι → F) :
    weyl ψ p m f y = ψ ((2 : F)⁻¹ * pairing m p) * (ψ (pairing m y) * f (y + p)) := rfl

omit [Fintype ι] in
@[simp] lemma translation_zero : translation (0 : ι → F) = LinearMap.id := by
  ext f y
  simp

@[simp] lemma modulation_zero (ψ : AddChar F ℂ) :
    modulation ψ (0 : ι → F) = LinearMap.id := by
  ext f y
  simp [AddChar.map_zero_eq_one]

/-- `W(p,0) = T_p` (the ½-twist is trivial on the position axis). -/
lemma weyl_zero_mom (ψ : AddChar F ℂ) (p : ι → F) : weyl ψ p 0 = translation p := by
  rw [weyl, modulation_zero, LinearMap.id_comp, pairing_zero_left, mul_zero,
    AddChar.map_zero_eq_one, one_smul]

/-- `W(0,m) = M_m` (the ½-twist is trivial on the momentum axis). -/
lemma weyl_zero_pos (ψ : AddChar F ℂ) (m : ι → F) : weyl ψ 0 m = modulation ψ m := by
  rw [weyl, translation_zero, LinearMap.comp_id, pairing_zero_right, mul_zero,
    AddChar.map_zero_eq_one, one_smul]

/-- **The Weyl composition law, symmetric form**: for `2 ≠ 0`,
`W(p,m) ∘ W(p',m') = ψ(½·ω((p,m),(p',m'))) • W(p+p', m+m')`, where `ω` is the symplectic form
`⟨m',p⟩ − ⟨m,p'⟩`. **The cocycle is now `½ω`, which `Sp` preserves** — the polarized cocycle it
replaces was not `Sp`-invariant, and that is why the naive `Sp` action failed on the old group. -/
theorem weyl_comp (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (p m p' m' : ι → F) :
    weyl ψ p m ∘ₗ weyl ψ p' m'
      = ψ ((2 : F)⁻¹ * (pairing m' p - pairing m p')) • weyl ψ (p + p') (m + m') := by
  ext f y
  simp only [LinearMap.comp_apply, weyl_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  -- the whole content is one identity among the character's arguments; ½+½=1 is where `2 ≠ 0` enters
  have key : ψ ((2 : F)⁻¹ * pairing m p) * ψ (pairing m y) * ψ ((2 : F)⁻¹ * pairing m' p')
        * ψ (pairing m' (y + p))
      = ψ ((2 : F)⁻¹ * (pairing m' p - pairing m p')) * ψ ((2 : F)⁻¹ * pairing (m + m') (p + p'))
        * ψ (pairing (m + m') y) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    simp only [pairing_add_left, pairing_add_right]
    field_simp
    ring
  rw [add_assoc y p p']
  linear_combination f (y + (p + p')) * key

/-! ### The group object: the central extension `1 → F → H(V) → V → 1` -/

/-- The **Heisenberg group** `H(V)` over `F`, with `V = (ι → F) × (ι → F)` (positions × momenta):
the set `V × F` with multiplication twisted by **half the symplectic form**, `½ω(x,y)`.

The choice of cocycle is the whole design of this object. Any 2-cocycle whose antisymmetrization is
`ω` gives *a* Heisenberg group (all such are isomorphic when `2 ≠ 0`), and the commutator comes out as
`ω` either way. But only the **symmetric** choice `½ω` is preserved by `Sp(V)` — the polarization
`⟨m_y,p_x⟩` is not — and `Sp`-invariance of the cocycle is exactly what makes `(v,c) ↦ (gv,c)` an
automorphism. That map is the first step of the Weil representation, so the cocycle is chosen to make
it available. At `char = 2` no symmetric choice exists (`½` does not); the char-2 object is genuinely
different and needs a `ℤ/4` centre (`FTQCLib/Cohomology/PauliExtension.lean`). -/
@[ext] structure Heis (F : Type*) [Field F] (ι : Type*) [Fintype ι] where
  /-- The position component. -/
  pos : ι → F
  /-- The momentum component. -/
  mom : ι → F
  /-- The central component. -/
  cen : F

namespace Heis

/-- The symplectic form on `V`: `ω(x,y) = ⟨m_y, p_x⟩ − ⟨m_x, p_y⟩`. Defined before the group law,
because it *is* the group law's cocycle (up to the ½). -/
def symp (x y : Heis F ι) : F := pairing y.mom x.pos - pairing x.mom y.pos

lemma symp_antisymm (x y : Heis F ι) : symp x y = - symp y x := by
  unfold symp; ring

instance : Mul (Heis F ι) :=
  ⟨fun x y => ⟨x.pos + y.pos, x.mom + y.mom, x.cen + y.cen + (2 : F)⁻¹ * symp x y⟩⟩

instance : One (Heis F ι) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (Heis F ι) :=
  ⟨fun x => ⟨-x.pos, -x.mom, -x.cen⟩⟩

@[simp] lemma mul_pos (x y : Heis F ι) : (x * y).pos = x.pos + y.pos := rfl
@[simp] lemma mul_mom (x y : Heis F ι) : (x * y).mom = x.mom + y.mom := rfl
@[simp] lemma mul_cen (x y : Heis F ι) :
    (x * y).cen = x.cen + y.cen + (2 : F)⁻¹ * symp x y := rfl
@[simp] lemma one_pos : (1 : Heis F ι).pos = 0 := rfl
@[simp] lemma one_mom : (1 : Heis F ι).mom = 0 := rfl
@[simp] lemma one_cen : (1 : Heis F ι).cen = 0 := rfl
@[simp] lemma inv_pos (x : Heis F ι) : x⁻¹.pos = -x.pos := rfl
@[simp] lemma inv_mom (x : Heis F ι) : x⁻¹.mom = -x.mom := rfl
@[simp] lemma inv_cen (x : Heis F ι) : x⁻¹.cen = -x.cen := rfl

instance : Group (Heis F ι) :=
  Group.ofLeftAxioms
    (fun x y z => by
      refine Heis.ext (add_assoc _ _ _) (add_assoc _ _ _) ?_
      change x.cen + y.cen + (2 : F)⁻¹ * symp x y + z.cen + (2 : F)⁻¹ * symp (x * y) z
        = x.cen + (y.cen + z.cen + (2 : F)⁻¹ * symp y z) + (2 : F)⁻¹ * symp x (y * z)
      unfold symp
      simp only [mul_pos, mul_mom, pairing_add_left, pairing_add_right]
      ring)
    (fun x => by
      refine Heis.ext (zero_add _) (zero_add _) ?_
      change 0 + x.cen + (2 : F)⁻¹ * symp 1 x = x.cen
      unfold symp
      simp only [one_pos, one_mom, pairing_zero_left, pairing_zero_right]
      ring)
    (fun x => by
      refine Heis.ext (neg_add_cancel _) (neg_add_cancel _) ?_
      change -x.cen + x.cen + (2 : F)⁻¹ * symp x⁻¹ x = 0
      unfold symp
      simp only [inv_pos, inv_mom, pairing_neg_left, pairing_neg_right]
      ring)

/-- The central embedding `s ↦ (0, 0, s)`. -/
def central (s : F) : Heis F ι := ⟨0, 0, s⟩

@[simp] lemma central_pos (s : F) : (central s : Heis F ι).pos = 0 := rfl
@[simp] lemma central_mom (s : F) : (central s : Heis F ι).mom = 0 := rfl
@[simp] lemma central_cen (s : F) : (central s : Heis F ι).cen = s := rfl

@[simp] lemma symp_central_left (s : F) (x : Heis F ι) : symp (central s) x = 0 := by
  unfold symp central; simp

@[simp] lemma symp_central_right (s : F) (x : Heis F ι) : symp x (central s) = 0 := by
  unfold symp central; simp

/-- The central elements are central. -/
theorem central_comm (s : F) (x : Heis F ι) : central s * x = x * central s := by
  refine Heis.ext (by simp [central]) (by simp [central]) ?_
  change s + x.cen + (2 : F)⁻¹ * symp (central s) x = x.cen + s + (2 : F)⁻¹ * symp x (central s)
  rw [symp_central_left, symp_central_right]
  ring

/-- **The commutator is the symplectic form** — the defining property of the Heisenberg group:
`x·y = central (ω x y) · (y·x)`. This is `weyl_comp`'s braiding, made a group identity. -/
theorem mul_eq_central_symp_mul (h2 : (2 : F) ≠ 0) (x y : Heis F ι) :
    x * y = central (symp x y) * (y * x) := by
  refine Heis.ext (by simp [central, add_comm]) (by simp [central, add_comm]) ?_
  change x.cen + y.cen + (2 : F)⁻¹ * symp x y
    = symp x y + (y.cen + x.cen + (2 : F)⁻¹ * symp y x) + (2 : F)⁻¹ * symp (central (symp x y)) (y * x)
  rw [symp_central_left, symp_antisymm y x]
  have h : (2 : F)⁻¹ + (2 : F)⁻¹ = 1 := by rw [← two_mul]; exact mul_inv_cancel₀ h2
  linear_combination (symp x y) * h

/-- The central subgroup, as a `MonoidHom` from the additive group of `F`. -/
def centralHom : Multiplicative F →* Heis F ι where
  toFun s := central (Multiplicative.toAdd s)
  map_one' := rfl
  map_mul' s t := by
    refine Heis.ext (by simp [central]) (by simp [central]) ?_
    change (Multiplicative.toAdd s) + (Multiplicative.toAdd t)
      = (Multiplicative.toAdd s) + (Multiplicative.toAdd t) + (2 : F)⁻¹ * symp (central _) (central _)
    rw [symp_central_left, mul_zero, add_zero]

/-- The projection to `V`, forgetting the central coordinate. -/
def projHom : Heis F ι →* Multiplicative ((ι → F) × (ι → F)) where
  toFun x := Multiplicative.ofAdd (x.pos, x.mom)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem centralHom_injective : Function.Injective (centralHom (F := F) (ι := ι)) := by
  intro s t h
  have := congrArg Heis.cen h
  exact this

theorem projHom_surjective : Function.Surjective (projHom (F := F) (ι := ι)) :=
  fun v => ⟨⟨(Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2, 0⟩, rfl⟩

/-- **The central extension is exact**: `range (F → H) = ker (H → V)`, i.e.
`1 → F → H(V) → V → 1` is a short exact sequence. -/
theorem range_centralHom_eq_ker_projHom :
    (centralHom (F := F) (ι := ι)).range = (projHom (F := F) (ι := ι)).ker := by
  ext x
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨s, rfl⟩
    rfl
  · intro h
    have hx : (x.pos, x.mom) = (0, 0) := congrArg Multiplicative.toAdd h
    exact ⟨Multiplicative.ofAdd x.cen,
      Heis.ext (congrArg Prod.fst hx).symm (congrArg Prod.snd hx).symm rfl⟩

end Heis

/-! ### The Schrödinger representation of `H(V)` -/

/-- **The Schrödinger representation** `ρ(p,m,c) = ψ(c)·M_m∘T_p` — a genuine monoid homomorphism
`H(V) →* End(ℂ[𝔽_q^ι])`, the Weyl cocycle now absorbed into the group law. -/
noncomputable def schrodinger (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) :
    Heis F ι →* Module.End ℂ ((ι → F) → ℂ) where
  toFun x := ψ x.cen • weyl ψ x.pos x.mom
  map_one' := by
    change ψ (0 : F) • weyl ψ (0 : ι → F) 0 = 1
    rw [AddChar.map_zero_eq_one, one_smul, weyl_zero_mom, translation_zero,
      Module.End.one_eq_id]
  map_mul' x y := by
    change ψ ((x * y).cen) • weyl ψ ((x * y).pos) ((x * y).mom)
      = (ψ x.cen • weyl ψ x.pos x.mom) * (ψ y.cen • weyl ψ y.pos y.mom)
    rw [smul_mul_smul_comm, Module.End.mul_eq_comp, weyl_comp h2, Heis.mul_cen, Heis.mul_pos,
      Heis.mul_mom, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, smul_smul]
    rfl

@[simp] lemma schrodinger_apply (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (x : Heis F ι) :
    schrodinger h2 ψ x = ψ x.cen • weyl ψ x.pos x.mom := rfl

/-- The representation restricted to the position axis is the translation family. -/
lemma schrodinger_translation (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (a : ι → F) :
    schrodinger h2 ψ (⟨a, 0, 0⟩ : Heis F ι) = translation a := by
  rw [schrodinger_apply]
  change ψ (0 : F) • weyl ψ a 0 = translation a
  rw [AddChar.map_zero_eq_one, one_smul, weyl_zero_mom]

/-- The representation restricted to the momentum axis is the modulation family. -/
lemma schrodinger_modulation (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (b : ι → F) :
    schrodinger h2 ψ (⟨0, b, 0⟩ : Heis F ι) = modulation ψ b := by
  rw [schrodinger_apply]
  change ψ (0 : F) • weyl ψ 0 b = modulation ψ b
  rw [AddChar.map_zero_eq_one, one_smul, weyl_zero_pos]

/-- **The central character**: the center acts by the scalar `ψ(s)`. -/
theorem schrodinger_central (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (s : F) :
    schrodinger h2 ψ (Heis.central s : Heis F ι) = ψ s • LinearMap.id := by
  rw [schrodinger_apply]
  change ψ s • weyl ψ (0 : ι → F) 0 = ψ s • LinearMap.id
  rw [weyl_zero_mom, translation_zero]

open Classical in
/-- **The Schrödinger representation is irreducible** (commutant form): any endomorphism commuting
with the whole Heisenberg group is a scalar. The `H(V)`-packaged form of
`operator_scalar_of_commutes` — the Stone–von Neumann argument quantifies over exactly
this shape. -/
theorem schrodinger_irreducible [Fintype F] [DecidableEq ι] (h2 : (2 : F) ≠ 0)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (T : Module.End ℂ ((ι → F) → ℂ))
    (hT : ∀ x : Heis F ι, T * schrodinger h2 ψ x = schrodinger h2 ψ x * T) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  refine operator_scalar_of_commutes hψ T (fun a => ?_) (fun b => ?_)
  · have h := hT ⟨a, 0, 0⟩
    rwa [schrodinger_translation h2, Module.End.mul_eq_comp, Module.End.mul_eq_comp] at h
  · have h := hT ⟨0, b, 0⟩
    rwa [schrodinger_modulation h2, Module.End.mul_eq_comp, Module.End.mul_eq_comp] at h

/-! ### The symplectic action on `H(V)`

The point of the symmetric cocycle. A linear map `g` of `V` that **preserves `ω`** acts on `H(V)` by
`(v,c) ↦ (gv,c)`, fixing the centre pointwise — and it is an automorphism *for no other reason than*
`Sp`-invariance of the cocycle. On the polarized model this fails: the polarization `⟨m_y,p_x⟩` is
preserved by only a handful of symplectic maps (2 of 24 over `𝔽₃`), so the naive action is not a
homomorphism there. This is the map `g ↦ (π ∘ g)` that the Weil representation is built from. -/

namespace Heis

/-- A **symplectic map** of `V`, in the coordinates `H(V)` carries: an additive map of the
position/momentum data preserving `ω`. (Packaged on `Heis`, acting trivially on the centre;
the centre coordinate is inert.) -/
structure IsSymplectic (g : Heis F ι → Heis F ι) : Prop where
  /-- `g` is additive on positions. -/
  map_pos : ∀ x y : Heis F ι, (g (x * y)).pos = (g x).pos + (g y).pos
  /-- `g` is additive on momenta. -/
  map_mom : ∀ x y : Heis F ι, (g (x * y)).mom = (g x).mom + (g y).mom
  /-- `g` leaves the centre coordinate alone. -/
  map_cen : ∀ x : Heis F ι, (g x).cen = x.cen
  /-- `g` preserves the symplectic form — the defining property. -/
  map_symp : ∀ x y : Heis F ι, symp (g x) (g y) = symp x y

/-- **The symplectic action.** A symplectic `g` acts on `H(V)` by a group
homomorphism. The proof is one rewrite: the cocycle is `½ω`, and `g` preserves `ω`.

This is exactly what the polarized cocycle could not support, and it is the first step of the Weil
representation: from it one forms the twisted representation `π ∘ g`, which has the same central
character as `π`, whence Stone–von Neumann supplies an intertwiner. -/
theorem isSymplectic_map_mul {g : Heis F ι → Heis F ι} (hg : IsSymplectic g) (x y : Heis F ι) :
    g (x * y) = g x * g y := by
  refine Heis.ext (hg.map_pos x y) (hg.map_mom x y) ?_
  rw [hg.map_cen, mul_cen, mul_cen, hg.map_cen, hg.map_cen, hg.map_symp]

/-- The symplectic action, packaged as a `MonoidHom`. -/
def symplecticHom {g : Heis F ι → Heis F ι} (hg : IsSymplectic g) : Heis F ι →* Heis F ι where
  toFun := g
  map_one' := by
    refine Heis.ext ?_ ?_ (hg.map_cen 1)
    · have h := hg.map_pos 1 1
      simp only [one_mul] at h
      simpa using h
    · have h := hg.map_mom 1 1
      simp only [one_mul] at h
      simpa using h
  map_mul' := isSymplectic_map_mul hg

/-- A symplectic action **fixes the centre pointwise** — the hypothesis Stone–von Neumann is stated
relative to, and the reason `π ∘ g` has the same central character as `π`. -/
theorem symplecticHom_central {g : Heis F ι → Heis F ι} (hg : IsSymplectic g) (s : F)
    (hcen : (g (central s)).pos = 0 ∧ (g (central s)).mom = 0) :
    symplecticHom hg (central s) = central s := by
  refine Heis.ext hcen.1 hcen.2 (hg.map_cen _)

end Heis


/-! ### The Weil operator is well defined projectively

The symplectic action gives the twisted representation `π ∘ g`. Suppose an intertwiner `W` between
`π` and `π ∘ g` exists (that existence is Stone–von Neumann, proved below). Then Schur — proved
above — forces it to be **unique up to a scalar**. That is precisely why `g ↦ W(g)` lands in `PGL`
rather than `GL`, i.e. why the Weil representation is *a priori* projective and linearizing it is a
further question rather than a freebie. -/

/-- **The Weil operator is unique up to a scalar.** If `W` (invertible) and `W'` both intertwine the
Schrödinger representation with its `g`-twist, then `W' = c • W`. Direct consequence of
`schrodinger_irreducible`: `W⁻¹W'` commutes with the whole Heisenberg group, hence is scalar. -/
theorem weil_operator_unique [Fintype F] [DecidableEq ι] (h2 : (2 : F) ≠ 0)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {g : Heis F ι → Heis F ι}
    (W : (Module.End ℂ ((ι → F) → ℂ))ˣ) (W' : Module.End ℂ ((ι → F) → ℂ))
    (hW : ∀ x, (W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
        = schrodinger h2 ψ (g x) * (W : Module.End ℂ ((ι → F) → ℂ)))
    (hW' : ∀ x, W' * schrodinger h2 ψ x = schrodinger h2 ψ (g x) * W') :
    ∃ c : ℂ, W' = c • (W : Module.End ℂ ((ι → F) → ℂ)) := by
  -- conjugating the intertwining relation by `W⁻¹` moves the twist to the other side
  have hinv : ∀ x, schrodinger h2 ψ x * (↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ))
      = (↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ (g x) := by
    intro x
    have h := congrArg
      (fun z => (↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * z * (↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)))
      (hW x)
    simpa [mul_assoc, Units.inv_mul, Units.mul_inv] using h
  -- so `W⁻¹W'` centralizes the Heisenberg group, and Schur makes it a scalar
  obtain ⟨c, hc⟩ := schrodinger_irreducible h2 hψ
    ((↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * W') (fun x => by
      calc (↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * W' * schrodinger h2 ψ x
          = (↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * (W' * schrodinger h2 ψ x) := by
            rw [mul_assoc]
        _ = (↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * (schrodinger h2 ψ (g x) * W') := by rw [hW' x]
        _ = ((↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ (g x)) * W' := by
            rw [mul_assoc]
        _ = (schrodinger h2 ψ x * (↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ))) * W' := by rw [hinv x]
        _ = schrodinger h2 ψ x * ((↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * W') := by rw [mul_assoc])
  refine ⟨c, ?_⟩
  have : (W : Module.End ℂ ((ι → F) → ℂ)) * ((↑W⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * W') = W' := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [← this, hc, mul_smul_comm, Module.End.mul_eq_comp, LinearMap.comp_id]


/-! ### An explicit Weil operator: the shear and its chirp

The two preceding sections say `Sp` acts and that an intertwiner, if it exists, is unique up to a
scalar. Existence in general is Stone–von Neumann. But for the **shears** — the symplectic maps
`(p,m) ↦ (p, m − S·p)` with `S` symmetric — the intertwiner can be written down: it is the
**chirp**, multiplication by the quadratic phase `ψ(½⟨S y, y⟩)`. So the Weil operator exists
outright on this family, with no appeal to SvN, and the ½ in the group law is what makes the
computation close.

This is the specialization to `B = 𝔽_q` of Cruickshank–Gutiérrez Frez–Szechtman's `W(u_S) e_a =
β(a* S a) e_a` (arXiv:1906.03468, Thm `weilrepskewh`). -/

/-- A **symmetric** additive endomorphism of the momentum/position space: `⟨S a, b⟩ = ⟨S b, a⟩`. These
are exactly the `S` for which the shear below is symplectic. -/
structure IsSymmetricMap (S : (ι → F) → (ι → F)) : Prop where
  /-- `S` is additive. -/
  map_add : ∀ a b, S (a + b) = S a + S b
  /-- `S` is self-adjoint for the pairing. -/
  symm : ∀ a b, pairing (S a) b = pairing (S b) a

/-- The **chirp**: multiplication by the quadratic phase `ψ(½⟨S y, y⟩)`. -/
def chirp (ψ : AddChar F ℂ) (S : (ι → F) → (ι → F)) :
    ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) where
  toFun f := fun y => ψ ((2 : F)⁻¹ * pairing (S y) y) * f y
  map_add' f g := by funext y; simp [mul_add]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma chirp_apply (ψ : AddChar F ℂ) (S : (ι → F) → (ι → F)) (f : (ι → F) → ℂ) (y : ι → F) :
    chirp ψ S f y = ψ ((2 : F)⁻¹ * pairing (S y) y) * f y := rfl

namespace Heis

/-- The **shear** `(p, m, c) ↦ (p, m − S·p, c)`. -/
def shear (S : (ι → F) → (ι → F)) (x : Heis F ι) : Heis F ι := ⟨x.pos, x.mom - S x.pos, x.cen⟩

/-- **The shear is symplectic** — precisely when `S` is symmetric. So this is the first nontrivial
instance of `IsSymplectic`, and `symplecticHom` applies to it. -/
theorem isSymplectic_shear {S : (ι → F) → (ι → F)} (hS : IsSymmetricMap S) :
    IsSymplectic (shear S) where
  map_pos x y := rfl
  map_mom x y := by
    change x.mom + y.mom - S (x.pos + y.pos) = (x.mom - S x.pos) + (y.mom - S y.pos)
    rw [hS.map_add]
    ring
  map_cen x := rfl
  map_symp x y := by
    change pairing (y.mom - S y.pos) x.pos - pairing (x.mom - S x.pos) y.pos
      = pairing y.mom x.pos - pairing x.mom y.pos
    rw [sub_eq_add_neg (y.mom), sub_eq_add_neg (x.mom), pairing_add_left, pairing_add_left,
      pairing_neg_left, pairing_neg_left, hS.symm y.pos x.pos]
    ring

end Heis

/-- **The chirp intertwines the shear**:
`C_S ∘ W(p,m) = W(p, m − S·p) ∘ C_S`.

An explicit Weil operator, existence and all, for every shear — no Stone–von Neumann required. The
`½`s cancel by symmetry of `S`, and `½+½=1` is where `2 ≠ 0` enters, exactly as in `weyl_comp`. -/
theorem chirp_comp_weyl (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) {S : (ι → F) → (ι → F)}
    (hS : IsSymmetricMap S) (p m : ι → F) :
    chirp ψ S ∘ₗ weyl ψ p m = weyl ψ p (m - S p) ∘ₗ chirp ψ S := by
  ext f y
  simp only [LinearMap.comp_apply, chirp_apply, weyl_apply]
  have key : ψ ((2 : F)⁻¹ * pairing (S y) y) * (ψ ((2 : F)⁻¹ * pairing m p) * ψ (pairing m y))
      = ψ ((2 : F)⁻¹ * pairing (m - S p) p) * ψ (pairing (m - S p) y)
        * ψ ((2 : F)⁻¹ * pairing (S (y + p)) (y + p)) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul]
    congr 1
    rw [hS.map_add]
    simp only [sub_eq_add_neg, pairing_add_left, pairing_add_right, pairing_neg_left]
    rw [hS.symm y p]
    field_simp
    ring
  calc ψ ((2 : F)⁻¹ * pairing (S y) y) * (ψ ((2 : F)⁻¹ * pairing m p) * (ψ (pairing m y) * f (y + p)))
      = (ψ ((2 : F)⁻¹ * pairing (S y) y) * (ψ ((2 : F)⁻¹ * pairing m p) * ψ (pairing m y)))
          * f (y + p) := by ring
    _ = (ψ ((2 : F)⁻¹ * pairing (m - S p) p) * ψ (pairing (m - S p) y)
          * ψ ((2 : F)⁻¹ * pairing (S (y + p)) (y + p))) * f (y + p) := by rw [key]
    _ = ψ ((2 : F)⁻¹ * pairing (m - S p) p)
          * (ψ (pairing (m - S p) y) * (ψ ((2 : F)⁻¹ * pairing (S (y + p)) (y + p)) * f (y + p))) := by
        ring


/-! ### The Fourier element

The other Bruhat stratum. The Fourier operator `(𝓕f)(y) = ∑ₓ ψ(⟨y,x⟩)·f(x)` intertwines the
Schrödinger representation with the twist by `g(p,m) = (m,−p)` — the "Weyl element" of `Sp`. This is
the Egorov identity that Gurevich–Hadani–Howe organize their proof around (`F_n = C_n·ρ_n(w)`): the
DFT **is** the Weil operator of the Weyl element, up to normalization.

Note what is and is not needed here. The **intertwining** is pure character algebra — no Gauss sum.
The Gauss sum enters only when one asks for `𝓕`'s *normalization* (`𝓕²`, `𝓕⁴`, invertibility), which
is where `ECCLib/GaussSumSign.lean`'s `quadGaussSum_sign_fq` gets spent. Keeping the two apart
is the non-circularity the standard treatments insist on. -/

section Fourier

variable [Fintype F] [DecidableEq ι]

/-- The **Fourier operator** `(𝓕f)(y) = ∑ₓ ψ(⟨y,x⟩)·f(x)` (unnormalized).

*Disambiguation*: this is the DFT on functions — the Weil operator of the symplectic map
`Heis.fourierMap`. Not to be confused with the Weyl *operator* `weyl` or `Siegel.weyl` (see the
`weyl` docstring for the four-object glossary). -/
noncomputable def fourierOp (ψ : AddChar F ℂ) : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) where
  toFun f := fun y => ∑ x : ι → F, ψ (pairing y x) * f x
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

@[simp] lemma fourierOp_apply (ψ : AddChar F ℂ) (f : (ι → F) → ℂ) (y : ι → F) :
    fourierOp ψ f y = ∑ x : ι → F, ψ (pairing y x) * f x := rfl

/-- `𝓕` turns translations into modulations: `𝓕 ∘ T_a = M_{−a} ∘ 𝓕`. -/
theorem fourierOp_comp_translation (ψ : AddChar F ℂ) (a : ι → F) :
    fourierOp ψ ∘ₗ translation a = modulation ψ (-a) ∘ₗ fourierOp ψ := by
  ext f y
  simp only [LinearMap.comp_apply, fourierOp_apply, translation_apply, modulation_apply]
  rw [Finset.mul_sum]
  -- reindex x ↦ x + a; the phase ψ(−⟨y,a⟩) then factors out of every term
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => ?_
  change ψ (pairing y x) * f (x + a) = ψ (pairing (-a) y) * (ψ (pairing y (x + a)) * f (x + a))
  rw [pairing_add_right, AddChar.map_add_eq_mul, pairing_neg_left, pairing_symm a y]
  have : ψ (-pairing y a) * ψ (pairing y a) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc ψ (pairing y x) * f (x + a)
      = (ψ (-pairing y a) * ψ (pairing y a)) * (ψ (pairing y x) * f (x + a)) := by
        rw [this, one_mul]
    _ = ψ (-pairing y a) * ψ (pairing y x) * ψ (pairing y a) * f (x + a) := by ring
    _ = ψ (-pairing y a) * (ψ (pairing y x) * ψ (pairing y a) * f (x + a)) := by ring

/-- `𝓕` turns modulations into translations: `𝓕 ∘ M_b = T_b ∘ 𝓕`. -/
theorem fourierOp_comp_modulation (ψ : AddChar F ℂ) (b : ι → F) :
    fourierOp ψ ∘ₗ modulation ψ b = translation b ∘ₗ fourierOp ψ := by
  ext f y
  simp only [LinearMap.comp_apply, fourierOp_apply, modulation_apply, translation_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← pairing_add_left]

namespace Heis

/-- The **Weyl element** of `Sp`: `g(p,m) = (m,−p)`.

*Disambiguation*: this is the symplectic map on the Heisenberg group whose Weil operator is the DFT
`fourierOp`; `Siegel.weyl` is the same element on the plain vector space `W`; the Weyl *operator*
`weyl` is unrelated to this element (see the `weyl` docstring for the four-object glossary). -/
def fourierMap (x : Heis F ι) : Heis F ι := ⟨x.mom, -x.pos, x.cen⟩

omit [Fintype F] [DecidableEq ι] in
/-- The Weyl element is symplectic. -/
theorem isSymplectic_fourierMap : IsSymplectic (fourierMap (F := F) (ι := ι)) where
  map_pos x y := rfl
  map_mom x y := by
    change -(x.pos + y.pos) = -x.pos + -y.pos
    ring
  map_cen x := rfl
  map_symp x y := by
    change pairing (-y.pos) x.mom - pairing (-x.pos) y.mom
      = pairing y.mom x.pos - pairing x.mom y.pos
    rw [pairing_neg_left, pairing_neg_left, pairing_symm y.pos x.mom, pairing_symm x.pos y.mom]
    ring

end Heis

/-- **The Fourier operator is the Weil operator of the Weyl element**:
`𝓕 ∘ W(p,m) = W(m,−p) ∘ 𝓕`.

Pure character algebra — no Gauss sum. The braiding relation supplies the phase, and `½+½=1` (i.e.
`2 ≠ 0`) closes it, as everywhere else in this file. -/
theorem fourierOp_comp_weyl (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (p m : ι → F) :
    fourierOp ψ ∘ₗ weyl ψ p m = weyl ψ m (-p) ∘ₗ fourierOp ψ := by
  -- unfold both Weyl operators to their (phase, modulation, translation) form
  have hL : weyl ψ p m = ψ ((2 : F)⁻¹ * pairing m p) • (modulation ψ m ∘ₗ translation p) := rfl
  have hR : weyl ψ m (-p) = ψ ((2 : F)⁻¹ * pairing (-p) m) • (modulation ψ (-p) ∘ₗ translation m) :=
    rfl
  rw [hL, hR, LinearMap.comp_smul, LinearMap.smul_comp]
  -- move 𝓕 across the two axes, then re-order with the braiding
  have hmove : fourierOp ψ ∘ₗ (modulation ψ m ∘ₗ translation p)
      = ψ (pairing (-p) m) • (modulation ψ (-p) ∘ₗ translation m ∘ₗ fourierOp ψ) := by
    rw [← LinearMap.comp_assoc, fourierOp_comp_modulation, LinearMap.comp_assoc,
      fourierOp_comp_translation, ← LinearMap.comp_assoc,
      translation_comp_modulation ψ m (-p), LinearMap.smul_comp, LinearMap.comp_assoc]
  rw [hmove, smul_smul, ← LinearMap.comp_assoc]
  congr 1
  -- the phases: ½⟨m,p⟩ + ⟨−p,m⟩ = ½⟨−p,m⟩, i.e. ½+½=1 again
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [pairing_neg_left, pairing_symm p m]
  field_simp
  ring

end Fourier


/-! ### The Bruhat route: Weil operators close under composition

Rather than prove Stone–von Neumann (existence for *all* of `Sp` at once), observe that the symplectic
maps carrying a Weil operator form a **subgroup**: if `W_g` intertwines `g` and `W_h` intertwines `h`,
then `W_g W_h` intertwines `g ∘ h`, by one reindexing. So the Weil representation extends for free to
everything the Bruhat generators generate — the shears (chirps) and the Weyl element (the DFT).

What this leaves is a purely group-theoretic fact, quarantined away from the representation theory:
`Sp(2n,𝔽_q) = ⟨shears, w⟩`. That is the Bruhat decomposition, and it is now the *only* thing standing
between this file and the Weil representation of all of `Sp` — no analysis, no SvN, no cover. -/

section Weil

variable [Fintype F] [DecidableEq ι]

/-- `g` **has a Weil operator**: an invertible `W` intertwining the Schrödinger representation with
its `g`-twist. By `weil_operator_unique`, `W` is then determined up to a scalar. -/
def HasWeilOperator (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (g : Heis F ι → Heis F ι) : Prop :=
  ∃ W : (Module.End ℂ ((ι → F) → ℂ))ˣ,
    ∀ x, (W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
      = schrodinger h2 ψ (g x) * (W : Module.End ℂ ((ι → F) → ℂ))

/-- **A named Weil operator** for `g`, extracted from a `HasWeilOperator` witness — so consumers
can chain and state properties of *an* operator instead of `∃`-eliminating at every use. The
extraction is `Classical.choice`: this operator is **not canonical** (any two differ by a scalar,
`weil_operator_unique`). The canonical choice exists: trace non-vanishing is
`WeilCharacter.weilTrace_ne_zero` (the Weil character formula), and the unique trace-1
operator is `WeilCharacter.weilNorm` — prefer it when `g` is symplectic; this raw
extraction remains for pre-normalization plumbing. -/
noncomputable def weilUnit {h2 : (2 : F) ≠ 0} {ψ : AddChar F ℂ} {g : Heis F ι → Heis F ι}
    (h : HasWeilOperator h2 ψ g) : (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  h.choose

omit [Fintype F] [DecidableEq ι] in
/-- The defining intertwining property of `weilUnit`. -/
theorem weilUnit_spec {h2 : (2 : F) ≠ 0} {ψ : AddChar F ℂ} {g : Heis F ι → Heis F ι}
    (h : HasWeilOperator h2 ψ g) :
    ∀ x, (weilUnit h : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
      = schrodinger h2 ψ (g x) * (weilUnit h : Module.End ℂ ((ι → F) → ℂ)) :=
  h.choose_spec

omit [Fintype F] [DecidableEq ι] in
theorem hasWeilOperator_id (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) :
    HasWeilOperator h2 ψ (id : Heis F ι → Heis F ι) :=
  ⟨1, fun x => by simp⟩

omit [Fintype F] [DecidableEq ι] in
/-- **Weil operators compose** — the subgroup property, and the engine of the Bruhat route. -/
theorem HasWeilOperator.comp {h2 : (2 : F) ≠ 0} {ψ : AddChar F ℂ}
    {g h : Heis F ι → Heis F ι} (hg : HasWeilOperator h2 ψ g) (hh : HasWeilOperator h2 ψ h) :
    HasWeilOperator h2 ψ (g ∘ h) := by
  obtain ⟨Wg, hWg⟩ := hg
  obtain ⟨Wh, hWh⟩ := hh
  refine ⟨Wg * Wh, fun x => ?_⟩
  calc ((Wg * Wh : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        * schrodinger h2 ψ x
      = (Wg : Module.End ℂ ((ι → F) → ℂ)) * ((Wh : Module.End ℂ ((ι → F) → ℂ))
          * schrodinger h2 ψ x) := by rw [Units.val_mul, mul_assoc]
    _ = (Wg : Module.End ℂ ((ι → F) → ℂ)) * (schrodinger h2 ψ (h x)
          * (Wh : Module.End ℂ ((ι → F) → ℂ))) := by rw [hWh]
    _ = ((Wg : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ (h x))
          * (Wh : Module.End ℂ ((ι → F) → ℂ)) := by rw [mul_assoc]
    _ = (schrodinger h2 ψ (g (h x)) * (Wg : Module.End ℂ ((ι → F) → ℂ)))
          * (Wh : Module.End ℂ ((ι → F) → ℂ)) := by rw [hWg]
    _ = schrodinger h2 ψ ((g ∘ h) x)
          * ((Wg * Wh : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) := by
        rw [Units.val_mul, mul_assoc]
        rfl

omit [Fintype F] [DecidableEq ι] in
/-- The chirp is invertible: `C_S ∘ C_{−S} = id`. -/
theorem chirp_comp_chirp_neg (ψ : AddChar F ℂ) (S : (ι → F) → (ι → F)) :
    chirp ψ S ∘ₗ chirp ψ (fun z => -(S z)) = LinearMap.id := by
  ext f y
  simp only [LinearMap.comp_apply, chirp_apply, LinearMap.id_apply]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, pairing_neg_left]
  rw [show (2 : F)⁻¹ * pairing (S y) y + (2 : F)⁻¹ * -pairing (S y) y = 0 by ring,
    AddChar.map_zero_eq_one, one_mul]

/-- The chirp as a unit of `End`. -/
noncomputable def chirpUnit (ψ : AddChar F ℂ) (S : (ι → F) → (ι → F)) :
    (Module.End ℂ ((ι → F) → ℂ))ˣ where
  val := chirp ψ S
  inv := chirp ψ (fun z => -(S z))
  val_inv := chirp_comp_chirp_neg ψ S
  inv_val := by
    have h := chirp_comp_chirp_neg ψ (fun z => -(S z))
    simpa using h

/-- The **conjugate Fourier operator** `(𝓕̄f)(y) = ∑ₓ ψ(−⟨y,x⟩)·f(x)`. -/
noncomputable def fourierOpConj (ψ : AddChar F ℂ) : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) where
  toFun f := fun y => ∑ x : ι → F, ψ (-(pairing y x)) * f x
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- **Fourier inversion**: `𝓕̄ ∘ 𝓕 = |V| • id`. Pure character orthogonality
(`sum_pairingChar_eq_zero`) — **no Gauss sum**. The Gauss sum is about `𝓕`'s *phase*, not its
invertibility, and keeping them apart is what keeps the Gauss sum → Weil operator dependency
non-circular. -/
theorem fourierOpConj_comp_fourierOp {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    fourierOpConj ψ ∘ₗ fourierOp ψ
      = (Fintype.card (ι → F) : ℂ) • (LinearMap.id : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ)) := by
  ext f z
  simp only [LinearMap.comp_apply, fourierOpConj, fourierOp_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
  -- swap the order of summation and collapse the inner character sum
  rw [Finset.sum_congr rfl fun y _ => Finset.mul_sum .., Finset.sum_comm]
  have hinner : ∀ x : ι → F,
      ∑ y : ι → F, ψ (-(pairing z y)) * (ψ (pairing y x) * f x)
        = (∑ y : ι → F, ψ (pairing y (x - z))) * f x := by
    intro x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    rw [sub_eq_add_neg, pairing_add_right, pairing_neg_right, pairing_symm z y]
    ring
  rw [Finset.sum_congr rfl fun x _ => hinner x]
  rw [Finset.sum_eq_single z]
  · rw [sub_self]
    have : ∀ y : ι → F, ψ (pairing y (0 : ι → F)) = 1 := by
      intro y; rw [pairing_zero_right, AddChar.map_zero_eq_one]
    rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · intro x _ hx
    rw [sum_pairingChar_eq_zero hψ (sub_ne_zero.mpr hx), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ z) h

omit [Fintype F] [DecidableEq ι] in
/-- **Every shear has a Weil operator** — its chirp. -/
theorem hasWeilOperator_shear (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ)
    {S : (ι → F) → (ι → F)} (hS : IsSymmetricMap S) :
    HasWeilOperator h2 ψ (Heis.shear S) := by
  refine ⟨chirpUnit ψ S, fun x => ?_⟩
  change chirp ψ S * schrodinger h2 ψ x = schrodinger h2 ψ (Heis.shear S x) * chirp ψ S
  simp only [schrodinger_apply, Module.End.mul_eq_comp, LinearMap.comp_smul, LinearMap.smul_comp]
  rw [chirp_comp_weyl h2 ψ hS]
  rfl

/-- `𝓕 ∘ 𝓕̄ = |V| • id` as well (the same computation with `ψ` conjugated). -/
theorem fourierOp_comp_fourierOpConj {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    fourierOp ψ ∘ₗ fourierOpConj ψ
      = (Fintype.card (ι → F) : ℂ) • (LinearMap.id : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ)) := by
  ext f z
  simp only [LinearMap.comp_apply, fourierOpConj, fourierOp_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun y _ => Finset.mul_sum .., Finset.sum_comm]
  have hinner : ∀ x : ι → F,
      ∑ y : ι → F, ψ (pairing z y) * (ψ (-(pairing y x)) * f x)
        = (∑ y : ι → F, ψ (pairing y (z - x))) * f x := by
    intro x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    rw [sub_eq_add_neg, pairing_add_right, pairing_neg_right, pairing_symm z y]
  rw [Finset.sum_congr rfl fun x _ => hinner x, Finset.sum_eq_single z]
  · rw [sub_self]
    have : ∀ y : ι → F, ψ (pairing y (0 : ι → F)) = 1 := by
      intro y; rw [pairing_zero_right, AddChar.map_zero_eq_one]
    rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · intro x _ hx
    rw [sum_pairingChar_eq_zero hψ (sub_ne_zero.mpr (Ne.symm hx)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ z) h

/-- **Reversal** `(Rf)(z) = f(−z)`. -/
def reversal : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) where
  toFun f := fun z => f (-z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [Fintype F] [DecidableEq ι] in
@[simp] lemma reversal_apply (f : (ι → F) → ℂ) (z : ι → F) : reversal f z = f (-z) := rfl

omit [Fintype ι] [Fintype F] [DecidableEq ι] in
theorem reversal_comp_reversal :
    reversal (F := F) (ι := ι) ∘ₗ reversal
      = (LinearMap.id : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ)) := by
  ext f z
  simp

/-- `R ∘ 𝓕 = 𝓕̄`. -/
theorem reversal_comp_fourierOp (ψ : AddChar F ℂ) :
    reversal (F := F) (ι := ι) ∘ₗ fourierOp ψ = fourierOpConj ψ := by
  ext f z
  simp only [LinearMap.comp_apply, reversal_apply, fourierOp_apply, fourierOpConj,
    LinearMap.coe_mk, AddHom.coe_mk]
  exact Finset.sum_congr rfl fun x _ => by rw [pairing_neg_left]

/-- **`𝓕² = |V| • R`** — the DFT squares to `|V|` times reversal. -/
theorem fourierOp_comp_fourierOp {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    fourierOp (ι := ι) ψ ∘ₗ fourierOp ψ = (Fintype.card (ι → F) : ℂ) • reversal := by
  have h : reversal ∘ₗ (fourierOp ψ ∘ₗ fourierOp ψ)
      = (Fintype.card (ι → F) : ℂ) • (LinearMap.id : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ)) := by
    rw [← LinearMap.comp_assoc, reversal_comp_fourierOp, fourierOpConj_comp_fourierOp hψ]
  calc fourierOp ψ ∘ₗ fourierOp ψ
      = (LinearMap.id : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ)) ∘ₗ (fourierOp ψ ∘ₗ fourierOp ψ) := by
        rw [LinearMap.id_comp]
    _ = (reversal ∘ₗ reversal) ∘ₗ (fourierOp ψ ∘ₗ fourierOp ψ) := by rw [reversal_comp_reversal]
    _ = reversal ∘ₗ (reversal ∘ₗ (fourierOp ψ ∘ₗ fourierOp ψ)) := by rw [LinearMap.comp_assoc]
    _ = reversal ∘ₗ ((Fintype.card (ι → F) : ℂ) • LinearMap.id) := by rw [h]
    _ = (Fintype.card (ι → F) : ℂ) • reversal := by
        rw [LinearMap.comp_smul, LinearMap.comp_id]

/-- **`𝓕⁴ = |V|² • id`.** This is the relation that leaves the Weil operator of the Weyl element
determined only up to a **fourth root**: `w⁴ = 1` in `Sp`, so a normalized `𝓕' = c·𝓕` needs
`c⁴·|V|² = 1`, and four scalars satisfy that. `trace_fourierOp_eq_quadGaussSum_pow` — i.e. the Gauss
sum — is what selects the branch. Exactly the skeleton of `GaussSumSign.lean`'s own proof (`A⁴ = p²I`
plus a determinant to pin the fourth root), and of Gurevich–Hadani–Howe's (`C_n⁴ = n²`, then `det`). -/
theorem fourierOp_pow_four {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (fourierOp ψ ∘ₗ fourierOp ψ) ∘ₗ (fourierOp ψ ∘ₗ fourierOp ψ)
      = ((Fintype.card (ι → F) : ℂ) ^ 2)
        • (LinearMap.id : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ)) := by
  rw [fourierOp_comp_fourierOp hψ, LinearMap.smul_comp, LinearMap.comp_smul,
    reversal_comp_reversal, smul_smul, sq]

/-- The DFT as a unit of `End`, inverse `|V|⁻¹ • 𝓕̄`. Invertibility is *inversion*, not the Gauss sum. -/
noncomputable def fourierUnit {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (Module.End ℂ ((ι → F) → ℂ))ˣ where
  val := fourierOp ψ
  inv := ((Fintype.card (ι → F) : ℂ))⁻¹ • fourierOpConj ψ
  val_inv := by
    have hc : (Fintype.card (ι → F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    change fourierOp ψ * (((Fintype.card (ι → F) : ℂ))⁻¹ • fourierOpConj ψ) = 1
    rw [Module.End.mul_eq_comp, LinearMap.comp_smul, fourierOp_comp_fourierOpConj hψ,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
    rfl
  inv_val := by
    have hc : (Fintype.card (ι → F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    change (((Fintype.card (ι → F) : ℂ))⁻¹ • fourierOpConj ψ) * fourierOp ψ = 1
    rw [Module.End.mul_eq_comp, LinearMap.smul_comp, fourierOpConj_comp_fourierOp hψ,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
    rfl

/-- **The Weyl element has a Weil operator** — the DFT. -/
theorem hasWeilOperator_fourierMap (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    HasWeilOperator h2 ψ (Heis.fourierMap (F := F) (ι := ι)) := by
  refine ⟨fourierUnit hψ, fun x => ?_⟩
  change fourierOp ψ * schrodinger h2 ψ x = schrodinger h2 ψ (Heis.fourierMap x) * fourierOp ψ
  simp only [schrodinger_apply, Module.End.mul_eq_comp, LinearMap.comp_smul, LinearMap.smul_comp]
  rw [fourierOp_comp_weyl h2 ψ]
  rfl

end Weil


/-! ### Self-duality of `𝔽_q^ι` via `ψ`

Stone–von Neumann needs to know that the characters of the position space are *exactly* the
`⟨·,x⟩`. That is the self-duality `L ≅ L̂` induced by `ψ` and the pairing: injective by separation
(`exists_pairing_ne_one`), surjective by counting (`AddChar.card_eq`). -/

section SelfDual

variable [Fintype F] [DecidableEq ι]

omit [Fintype F] [DecidableEq ι] in
/-- `x ↦ ψ⟨·,x⟩` is injective — two points with the same character are equal. -/
theorem pairingChar_injective {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    Function.Injective (pairingChar (ι := ι) ψ) := by
  intro x y hxy
  by_contra hne
  obtain ⟨b, hb⟩ := exists_pairing_ne_one hψ (sub_ne_zero.mpr hne)
  apply hb
  have h : ψ (pairing b x) = ψ (pairing b y) := congrFun (congrArg (⇑) hxy) b
  -- ψ⟨b,x−y⟩ = ψ⟨b,x⟩·ψ(−⟨b,y⟩) = ψ⟨b,y⟩·ψ(−⟨b,y⟩) = ψ(0) = 1
  rw [sub_eq_add_neg, pairing_add_right, pairing_neg_right, AddChar.map_add_eq_mul, h,
    ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

/-- **Self-duality**: every character of the position space is `ψ⟨·,x⟩` for a unique `x`. Injective
by separation, surjective by `AddChar.card_eq` (`|L̂| = |L|`). -/
theorem pairingChar_bijective {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    Function.Bijective (pairingChar (ι := ι) ψ) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨pairingChar_injective hψ, AddChar.card_eq.symm⟩

/-- Every character of the position space is a `pairingChar`. -/
theorem exists_eq_pairingChar {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (η : AddChar (ι → F) ℂ) :
    ∃ x : ι → F, pairingChar ψ x = η :=
  (pairingChar_bijective hψ).surjective η

end SelfDual


/-! ### Where the Gauss sum enters: `Tr(𝓕)`

Everything so far has been character algebra: the intertwinings, Fourier inversion, and the
invertibility of `𝓕` never touched a Gauss sum. That is deliberate — Gurevich–Hadani–Howe derive the
Gauss *sign* **from** the Weil representation, so a formalization that used the Weil representation to
normalize `𝓕` and then claimed the sign would be circular. We run the arrow the other way.

Here is the join. The Gauss sum **is the trace of the DFT**: in the delta basis `𝓕` has matrix
`ψ(⟨y,x⟩)`, so its diagonal is `ψ(⟨x,x⟩)` and

`Tr(𝓕) = ∑_x ψ(⟨x,x⟩) = (∑_a ψ(a²))^{|ι|} = (quadGaussSum ψ)^{|ι|}`,

which `ECCLib/GaussSumSign.lean` and `GaussSumFq.lean` evaluate outright. This is the trace that
pins the normalizing scalar (GHH pin theirs from `det F_n` and `F⁴ = n²·Id`), i.e. the constant that
turns the projective Weil representation into a linear one. -/

section GaussSumBridge

variable [Fintype F] [DecidableEq ι]

omit [Fintype ι] [Fintype F] in
/-- `ψ` turns a finite sum into a product. -/
theorem addChar_map_sum (ψ : AddChar F ℂ) (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

omit [Field F] [DecidableEq ι] in
open Classical in
/-- The delta family **is** the standard basis of `(ι → F) → ℂ`. -/
theorem delta_eq_basisFun (x : ι → F) : delta x = (Pi.basisFun ℂ (ι → F)) x := by
  funext y
  rw [Pi.basisFun_apply, delta]
  simp [Pi.single_apply, eq_comm]

/-- **The trace of the DFT is the quadratic character sum** `∑_x ψ(⟨x,x⟩)`. -/
theorem trace_fourierOp (ψ : AddChar F ℂ) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (fourierOp ψ) = ∑ x : ι → F, ψ (pairing x x) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ι → F)), Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← delta_eq_basisFun]
  change fourierOp ψ (delta x) x = ψ (pairing x x)
  rw [fourierOp_apply, Finset.sum_eq_single x]
  · rw [delta, if_pos rfl, mul_one]
  · intro b _ hb
    rw [delta, if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- `∑_x ψ(⟨x,x⟩) = (∑_a ψ(a²))^{|ι|}` — the diagonal quadratic form factors coordinatewise. -/
theorem sum_pairing_self (ψ : AddChar F ℂ) :
    ∑ x : ι → F, ψ (pairing x x) = (∑ a : F, ψ (a ^ 2)) ^ (Fintype.card ι) := by
  classical
  have hchar : ∀ x : ι → F, ψ (pairing x x) = ∏ i : ι, ψ (x i ^ 2) := by
    intro x
    unfold pairing
    rw [addChar_map_sum]
    exact Finset.prod_congr rfl fun i _ => by rw [sq]
  rw [Finset.sum_congr rfl fun x _ => hchar x, ← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset F) (fun (_ : ι) (a : F) => ψ (a ^ 2)),
    Finset.prod_const, Finset.card_univ]

/-- **The Gauss sum is the trace of the DFT**:
`Tr(𝓕) = (quadGaussSum ψ)^{|ι|}`.

This is the consumption point of `ECCLib/GaussSumSign.lean` + `GaussSumFq.lean`: their
`quadGaussSum_sign` / `quadGaussSum_sign_fq` evaluate the right-hand side, and hence this trace, in
closed form. Nothing earlier in this file needed it — the Weil operators exist and are invertible
without it — so the arrow runs (already-proven Gauss sign) ⟹ (normalization), never the reverse. -/
theorem trace_fourierOp_eq_quadGaussSum_pow (ψ : AddChar F ℂ) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (fourierOp ψ)
      = (ECCLib.quadGaussSum ψ) ^ (Fintype.card ι) := by
  rw [trace_fourierOp, sum_pairing_self]
  rfl

end GaussSumBridge


/-! ### Stone–von Neumann, part 2

The key step. Everything before this point is about *our* space `ℂ[𝔽_q^ι]`; SvN part 2 quantifies
over an **arbitrary** representation `ρ : H(V) →* End(W)` with central character `ψ` and produces an
equivariant embedding of the Schrödinger model into it. The proof is Prasad's (0912.0574),
specialized: Fourier projectors over the modulation subgroup produce a joint eigenvector in `W`;
self-duality says its eigenvalue is `ψ⟨·,x₀⟩` for a point `x₀`; translating the eigenvector around
gives a delta-like family, and `δ_x ↦ u_x` is the intertwiner. Injectivity is part 1
(`irreducible_of_invariant`) applied to the kernel. -/

section SvNHelpers

lemma pairing_sub_left (b b' y : ι → F) :
    pairing (b - b') y = pairing b y - pairing b' y := by
  rw [sub_eq_add_neg, pairing_add_left, pairing_neg_left, sub_eq_add_neg]

lemma pairing_sub_right (b y y' : ι → F) :
    pairing b (y - y') = pairing b y - pairing b y' := by
  rw [sub_eq_add_neg, pairing_add_right, pairing_neg_right, sub_eq_add_neg]

namespace Heis

/-- Pure position elements compose additively. -/
lemma pos_mul_pos (a t : ι → F) :
    (⟨a, 0, 0⟩ : Heis F ι) * ⟨t, 0, 0⟩ = ⟨a + t, 0, 0⟩ := by
  refine Heis.ext rfl (by change (0 : ι → F) + 0 = 0; simp) ?_
  change 0 + 0 + (2 : F)⁻¹ * symp _ _ = 0
  unfold symp
  change 0 + 0 + (2 : F)⁻¹ * (pairing 0 a - pairing 0 t) = 0
  simp

/-- Pure momentum elements compose additively. -/
lemma mom_mul_mom (b m : ι → F) :
    (⟨0, b, 0⟩ : Heis F ι) * ⟨0, m, 0⟩ = ⟨0, b + m, 0⟩ := by
  refine Heis.ext (by change (0 : ι → F) + 0 = 0; simp) rfl ?_
  change 0 + 0 + (2 : F)⁻¹ * symp _ _ = 0
  unfold symp
  change 0 + 0 + (2 : F)⁻¹ * (pairing m 0 - pairing b 0) = 0
  simp

/-- Momentum past position: `⟨0,b,0⟩·⟨t,0,0⟩ = ⟨t, b, −½⟨b,t⟩⟩`. -/
lemma mom_mul_pos (b t : ι → F) :
    (⟨0, b, 0⟩ : Heis F ι) * ⟨t, 0, 0⟩ = ⟨t, b, -((2 : F)⁻¹ * pairing b t)⟩ := by
  refine Heis.ext (by change (0 : ι → F) + t = t; simp) (by change b + 0 = b; simp) ?_
  change 0 + 0 + (2 : F)⁻¹ * symp _ _ = -((2 : F)⁻¹ * pairing b t)
  unfold symp
  change 0 + 0 + (2 : F)⁻¹ * (pairing 0 0 - pairing b t) = -((2 : F)⁻¹ * pairing b t)
  simp


/-- Position past momentum: `⟨t,0,0⟩·⟨0,b,0⟩ = ⟨t, b, ½⟨b,t⟩⟩`. -/
lemma pos_mul_mom (t b : ι → F) :
    (⟨t, 0, 0⟩ : Heis F ι) * ⟨0, b, 0⟩ = ⟨t, b, (2 : F)⁻¹ * pairing b t⟩ := by
  refine Heis.ext (by change t + 0 = t; simp) (by change (0 : ι → F) + b = b; simp) ?_
  change 0 + 0 + (2 : F)⁻¹ * symp _ _ = (2 : F)⁻¹ * pairing b t
  unfold symp
  change 0 + 0 + (2 : F)⁻¹ * (pairing b t - pairing 0 0) = (2 : F)⁻¹ * pairing b t
  simp

/-- Multiplying by a central element only shifts the centre coordinate. -/
lemma central_mul (c : F) (x : Heis F ι) :
    (central c : Heis F ι) * x = ⟨x.pos, x.mom, c + x.cen⟩ := by
  refine Heis.ext (by change (0 : ι → F) + x.pos = x.pos; simp)
    (by change (0 : ι → F) + x.mom = x.mom; simp) ?_
  change c + x.cen + (2 : F)⁻¹ * symp (central c) x = c + x.cen
  rw [symp_central_left, mul_zero, add_zero]

/-- **The factorization** `x = central(c − ½⟨m,p⟩) · ⟨p,0,0⟩ · ⟨0,m,0⟩` — every element is a central
piece times a pure translation times a pure modulation. This is what lets equivariance be checked on
the three generator families alone. -/
lemma factor (x : Heis F ι) :
    x = (central (x.cen - (2 : F)⁻¹ * pairing x.mom x.pos) : Heis F ι)
      * ⟨x.pos, 0, 0⟩ * ⟨0, x.mom, 0⟩ := by
  rw [mul_assoc, pos_mul_mom, central_mul]
  refine Heis.ext rfl rfl ?_
  change x.cen = x.cen - (2 : F)⁻¹ * pairing x.mom x.pos + (2 : F)⁻¹ * pairing x.mom x.pos
  ring

end Heis

end SvNHelpers

end ECCLib.Heisenberg










