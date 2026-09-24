/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Gates.CliffordGateGeneration
import FTQCLib.Hilbert.CliffordSymplectic
import Mathlib.Tactic.LinearCombination

/-!
# Clifford ≅ affine symplectic (group packaging)

This file packages the Clifford–symplectic correspondence (`cliffordToSymplectic`,
ω-preservation, Schur,
uniqueness mod phase) into group-theoretic form, toward `Clₙ / U(1)·Pauli ≅ Sp(V)`.

Conventions (Mathlib `automorphismGroup`): `f * g = g.trans f` (apply `g` first), `1 = refl`,
`f⁻¹ = f.symm`. Heisenberg conjugation `conjEquiv U V = U V U⁻¹`, so
`conjEquiv (U*V) = conjEquiv U ∘ conjEquiv V` and Φ is a genuine homomorphism.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates

variable {n : ℕ}

/-- Conjugation by the identity is trivial. -/
theorem conjEquiv_one (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) : conjEquiv 1 V = V := by
  simp [conjEquiv, LinearEquiv.one_eq_refl]

/-- Conjugation is multiplicative in the conjugating element:
`conjEquiv (U*V) W = conjEquiv U (conjEquiv V W)`. -/
theorem conjEquiv_mul (U V W : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    conjEquiv (U * V) W = conjEquiv U (conjEquiv V W) := by
  rw [LinearEquiv.mul_eq_trans]
  ext ψ; simp [conjEquiv_apply]

/-- The identity unitary is Clifford. -/
theorem isCliffordOperator_one :
    IsCliffordOperator (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n) := by
  intro p
  rw [conjEquiv_one]
  refine ⟨1, p, ?_⟩
  ext ψ
  simp [pauliEquiv_apply, Units.val_one]

/-- Conjugating a phased Pauli by a Clifford yields a phased Pauli. -/
theorem isPhasedPauli_conjEquiv {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) {W : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hW : IsPhasedPauli W) :
    IsPhasedPauli (conjEquiv U W) := by
  obtain ⟨β, q, hβ⟩ := hW
  obtain ⟨γ, q', hγ⟩ := hU q
  refine ⟨β * γ, q', ?_⟩
  refine LinearMap.ext fun ψ => ?_
  have hW' := LinearMap.congr_fun hβ (U.symm ψ)
  have hU' := LinearMap.congr_fun hγ ψ
  simp only [LinearEquiv.coe_coe, conjEquiv_apply, pauliEquiv_apply, LinearMap.smul_apply]
    at hW' hU' ⊢
  rw [hW', map_smul, hU', smul_smul, Units.val_mul]

/-- The Clifford operators are closed under composition (`U * V = U ∘ V`). -/
theorem isCliffordOperator_mul {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) :
    IsCliffordOperator (U * V) := by
  intro p
  rw [conjEquiv_mul]
  exact isPhasedPauli_conjEquiv hU (hV p)

/-- The Clifford operators are closed under inverse (here `U.symm`). For each Pauli `p`, pick the
preimage `q` under the (bijective) symplectic map and invert the conjugation `U (·) U⁻¹`. -/
theorem isCliffordOperator_symm {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) : IsCliffordOperator U.symm := by
  intro p
  obtain ⟨q, hq⟩ := (cliffordToSymplectic hU).surjective p
  rw [cliffordToSymplectic_apply] at hq
  have hspec := cliffordToSymplecticFun_spec hU q
  rw [hq] at hspec
  refine ⟨(cliffordToSymplecticPhase hU q)⁻¹, q, ?_⟩
  refine LinearMap.ext fun ψ => ?_
  have hkey := LinearMap.congr_fun hspec (U ψ)
  simp only [LinearEquiv.coe_coe, conjEquiv_apply, pauliEquiv_apply, LinearMap.smul_apply,
    LinearEquiv.symm_apply_apply] at hkey
  have hkey2 : pauliOperator q ψ
      = (↑(cliffordToSymplecticPhase hU q) : ℂ) • U.symm (pauliOperator p (U ψ)) := by
    have h := congrArg U.symm hkey
    rw [LinearEquiv.symm_apply_apply, map_smul] at h
    exact h
  simp only [LinearEquiv.coe_coe, conjEquiv_apply, pauliEquiv_apply, LinearMap.smul_apply,
    LinearEquiv.symm_symm]
  rw [hkey2, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- Inverse closure in the group (`U⁻¹ = U.symm`). -/
theorem isCliffordOperator_inv {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) : IsCliffordOperator U⁻¹ :=
  isCliffordOperator_symm hU

/-- **The Clifford group** as a subgroup of the linear automorphisms of `QubitSpace n`. -/
def cliffordSubgroup (n : ℕ) : Subgroup (QubitSpace n ≃ₗ[ℂ] QubitSpace n) where
  carrier := {U | IsCliffordOperator U}
  one_mem' := isCliffordOperator_one
  mul_mem' ha hb := isCliffordOperator_mul ha hb
  inv_mem' ha := isCliffordOperator_inv ha

@[simp] theorem mem_cliffordSubgroup {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} :
    U ∈ cliffordSubgroup n ↔ IsCliffordOperator U := Iff.rfl

/-! ## Functoriality of `Φ = cliffordToSymplectic` -/

/-- Explicit conjugation of a phased Pauli: if `W = β·pauliOperator q`, then
`conjEquiv U W = (β · phase_U(q)) · pauliOperator (Fun_U q)`. -/
theorem conjEquiv_smul_pauliOperator {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) {W : QubitSpace n ≃ₗ[ℂ] QubitSpace n} {β : ℂˣ} {q : Pauli n}
    (hW : W.toLinearMap = (β : ℂ) • pauliOperator q) :
    (conjEquiv U W).toLinearMap
      = ((β * cliffordToSymplecticPhase hU q : ℂˣ) : ℂ)
          • pauliOperator (cliffordToSymplecticFun hU q) := by
  refine LinearMap.ext fun ψ => ?_
  have hW' := LinearMap.congr_fun hW (U.symm ψ)
  have hU' := LinearMap.congr_fun (cliffordToSymplecticFun_spec hU q) ψ
  simp only [LinearEquiv.coe_coe, conjEquiv_apply, pauliEquiv_apply, LinearMap.smul_apply]
    at hW' hU' ⊢
  rw [hW', map_smul, hU', smul_smul, Units.val_mul]

/-- `Φ(1) = id`: the identity Clifford induces the identity symplectic map. -/
theorem cliffordToSymplecticFun_one (p : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_one) p = p := by
  symm
  refine cliffordToSymplecticFun_unique isCliffordOperator_one p (α := 1) ?_
  rw [conjEquiv_one]
  refine LinearMap.ext fun ψ => ?_
  simp [pauliEquiv_apply, Units.val_one]

/-- `Φ(U*V) = Φ(U) ∘ Φ(V)` at the level of the underlying Pauli maps. -/
theorem cliffordToSymplecticFun_mul {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) (p : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_mul hU hV) p
      = cliffordToSymplecticFun hU (cliffordToSymplecticFun hV p) := by
  symm
  have hwit : (conjEquiv (U * V) (pauliEquiv p)).toLinearMap
      = ((cliffordToSymplecticPhase hV p
            * cliffordToSymplecticPhase hU (cliffordToSymplecticFun hV p) : ℂˣ) : ℂ)
          • pauliOperator (cliffordToSymplecticFun hU (cliffordToSymplecticFun hV p)) := by
    rw [conjEquiv_mul]
    exact conjEquiv_smul_pauliOperator hU (cliffordToSymplecticFun_spec hV p)
  exact cliffordToSymplecticFun_unique (isCliffordOperator_mul hU hV) p hwit

/-- Witness-irrelevance: `cliffordToSymplectic` depends only on `U`, not on the Clifford proof. -/
theorem cliffordToSymplectic_irrel {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h h' : IsCliffordOperator U) : cliffordToSymplectic h = cliffordToSymplectic h' := by
  refine LinearEquiv.ext fun p => ?_
  simp only [cliffordToSymplectic_apply]

/-- `Φ(1) = 1`. -/
theorem cliffordToSymplectic_one :
    cliffordToSymplectic (isCliffordOperator_one (n := n)) = 1 := by
  refine LinearEquiv.ext fun p => ?_
  simp [cliffordToSymplectic_apply, cliffordToSymplecticFun_one]

/-- `Φ(U*V) = Φ(U)*Φ(V)` (LinearEquiv level). -/
theorem cliffordToSymplectic_comp {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) :
    cliffordToSymplectic (isCliffordOperator_mul hU hV)
      = cliffordToSymplectic hU * cliffordToSymplectic hV := by
  refine LinearEquiv.ext fun p => ?_
  simp only [LinearEquiv.mul_apply, cliffordToSymplectic_apply]
  exact cliffordToSymplecticFun_mul hU hV p

/-- **Homomorphism form: `Φ : Clₙ →* Sp(V)`**, the projective action of the Clifford
group on the Pauli phase space. -/
noncomputable def cliffordToSp : cliffordSubgroup n →* spSubgroup n where
  toFun U := ⟨cliffordToSymplectic U.2, cliffordToSymplectic_isClifford U.2⟩
  map_one' := by
    refine Subtype.ext ?_
    change cliffordToSymplectic (1 : cliffordSubgroup n).2 = (1 : Pauli n ≃ₗ[ZMod 2] Pauli n)
    rw [cliffordToSymplectic_irrel (1 : cliffordSubgroup n).2 isCliffordOperator_one,
      cliffordToSymplectic_one]
  map_mul' U V := by
    refine Subtype.ext ?_
    change cliffordToSymplectic (U * V).2 = cliffordToSymplectic U.2 * cliffordToSymplectic V.2
    rw [cliffordToSymplectic_irrel (U * V).2 (isCliffordOperator_mul U.2 V.2),
      cliffordToSymplectic_comp]

/-- **First isomorphism theorem:** the projective Clifford group modulo the kernel
of `Φ` is the realized symplectic group `range Φ`:  `Clₙ / ker Φ ≃* range Φ`.

Unconditional. With surjectivity `CliffordSymplecticLift n` (every symplectic automorphism lifts
to a Clifford unitary via H, S, CNOT, CZ; proved as `cliffordSymplecticLift_unconditional` in
`FTQCLib.Hilbert.GateLifts`), `range Φ = Sp(V)`, giving `Clₙ / ker Φ ≃* Sp(V)`; and `ker Φ` is
exactly `U(1)·Pauli` (the phased Paulis, by Schur). -/
noncomputable def cliffordQuotientEquivRange :
    cliffordSubgroup n ⧸ (cliffordToSp (n := n)).ker ≃* (cliffordToSp (n := n)).range :=
  QuotientGroup.quotientKerEquivRange cliffordToSp

/-! ## Kernel of Φ: Paulis act trivially (reverse inclusion `Pauli ⊆ ker Φ`)

Conjugating a Pauli `pauliOperator q` by another Pauli `pauliOperator r` returns a *sign* times
`pauliOperator q` — the **same** Pauli, because `(r + q) + r = q` over `𝔽₂`. Hence a Pauli
operator is Clifford and induces the **identity** symplectic map, so it lies in `ker Φ`. This is
the easy half of `ker Φ = U(1)·Pauli`; the forward half (`ker Φ ⊆ U(1)·Pauli`, via Schur and
ω-nondegeneracy through `BilinForm.toDual`) is proved in the next section. -/

/-- Conjugation of one Pauli by another is a sign times the *same* Pauli. The sign is the product of
the three `pauliOperator`-product cocycle factors; the Pauli is unchanged because `(r + q) + r = q`
over `𝔽₂`. -/
theorem conjEquiv_pauliEquiv_pauliEquiv (r q : Pauli n) :
    (conjEquiv (pauliEquiv r) (pauliEquiv q)).toLinearMap
      = ((-1 : ℂ) ^ (zDotVal r r.X + zDotVal q r.X + zDotVal r (r + q).X)) • pauliOperator q := by
  have hrr : (r : Pauli n) + r = 0 := by
    apply Pauli.ext
    · funext i
      change r.X i + r.X i = (0 : Pauli n).X i
      rw [X_zero, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    · funext i
      change r.Z i + r.Z i = (0 : Pauli n).Z i
      rw [Z_zero, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
  have hrq : (r + q) + r = q := by
    rw [add_comm r q, add_assoc, hrr, add_zero]
  refine LinearMap.ext fun ψ => ?_
  simp only [LinearEquiv.coe_coe, conjEquiv_apply, pauliEquiv_apply, pauliEquiv_symm_apply,
    map_smul]
  rw [pauliOperator_apply_pauliOperator_apply r q ψ, map_smul,
    pauliOperator_apply_pauliOperator_apply (r + q) r ψ, hrq, LinearMap.smul_apply,
    smul_smul, smul_smul]
  congr 1
  rw [← pow_add, ← pow_add]

/-- A Pauli operator is a Clifford operator. -/
theorem isCliffordOperator_pauliEquiv (r : Pauli n) :
    IsCliffordOperator (pauliEquiv r) := by
  intro q
  refine ⟨(-1 : ℂˣ) ^ (zDotVal r r.X + zDotVal q r.X + zDotVal r (r + q).X), q, ?_⟩
  rw [conjEquiv_pauliEquiv_pauliEquiv]
  congr 1

/-- A Pauli operator induces the **identity** symplectic map: `Φ(pauliEquiv r) = 1`. -/
theorem cliffordToSymplectic_pauliEquiv (r : Pauli n) :
    cliffordToSymplectic (isCliffordOperator_pauliEquiv r) = 1 := by
  refine LinearEquiv.ext fun q => ?_
  rw [cliffordToSymplectic_apply]
  have hwit : (conjEquiv (pauliEquiv r) (pauliEquiv q)).toLinearMap
      = (((-1 : ℂˣ) ^ (zDotVal r r.X + zDotVal q r.X + zDotVal r (r + q).X) : ℂˣ) : ℂ)
          • pauliOperator q := by
    rw [conjEquiv_pauliEquiv_pauliEquiv]
    congr 1
  exact (cliffordToSymplecticFun_unique (isCliffordOperator_pauliEquiv r) q hwit).symm

/-- **Reverse inclusion of the kernel characterization:** every Pauli operator lies in `ker Φ`.
Together with the forward inclusion (Schur + ω-nondegeneracy), this gives `ker Φ = U(1)·Pauli`. -/
theorem pauliEquiv_mem_ker (r : Pauli n) :
    (⟨pauliEquiv r, isCliffordOperator_pauliEquiv r⟩ : cliffordSubgroup n)
      ∈ (cliffordToSp (n := n)).ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change cliffordToSymplectic (isCliffordOperator_pauliEquiv r) = 1
  exact cliffordToSymplectic_pauliEquiv r

/-! ## Kernel of Φ: forward inclusion `ker Φ ⊆ U(1)·Pauli`

For `U ∈ ker Φ` (i.e. `Φ(U) = 1`), `U` conjugates every Pauli to a *phase multiple of itself*:
`conjEquiv U (pauliEquiv p) = φ(p) • pauliOperator p`, with `φ := cliffordToSymplecticPhase`.
The phases `φ` form a genuine **character** `φ(p+q) = φ(p)·φ(q)` — the product cocycle cancels
because `Fun = id`, so the two `(-1)^{zDotVal q p.X}` factors multiply to `1`. A `{±1}`-character is
`(-1)^{ω(r,·)}` for a unique `r` (ω-nondegeneracy via `omegaBilin.toDual`), and then
`U = α·pauliOp(r)` by Schur / uniqueness-mod-phase. -/

/-- The conjugation phases of a kernel element form an additive character: `φ(p+q) = φ(p)·φ(q)`. The
product cocycle cancels because the symplectic action is trivial (`Fun = id`). -/
private theorem phase_add_of_ker
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (hker : cliffordToSymplectic hU = 1) (p q : Pauli n) :
    (cliffordToSymplecticPhase hU (p + q) : ℂ)
      = (cliffordToSymplecticPhase hU p : ℂ) * (cliffordToSymplecticPhase hU q : ℂ) := by
  -- `Fun = id` on the kernel.
  have hfun : ∀ s, cliffordToSymplecticFun hU s = s := fun s => by
    have h := cliffordToSymplectic_apply hU s
    rw [hker] at h
    exact h.symm
  -- Conjugation fixes each Pauli up to its phase.
  have hsp : ∀ s, (conjEquiv U (pauliEquiv s)).toLinearMap
      = (cliffordToSymplecticPhase hU s : ℂ) • pauliOperator s := fun s => by
    rw [cliffordToSymplecticFun_spec hU s, hfun s]
  -- `conjEquiv U` unfolds to the operator sandwich `U ∘ · ∘ U⁻¹`.
  have hC : ∀ s : Pauli n, (conjEquiv U (pauliEquiv s)).toLinearMap
      = U.toLinearMap ∘ₗ pauliOperator s ∘ₗ U.symm.toLinearMap := fun s => by
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearEquiv.coe_coe, conjEquiv_apply, pauliEquiv_apply, LinearMap.comp_apply]
  -- The sandwich is multiplicative (`U⁻¹ ∘ U = id` cancels in the middle).
  have hCmul : ∀ M N : QubitSpace n →ₗ[ℂ] QubitSpace n,
      (U.toLinearMap ∘ₗ M ∘ₗ U.symm.toLinearMap) ∘ₗ (U.toLinearMap ∘ₗ N ∘ₗ U.symm.toLinearMap)
        = U.toLinearMap ∘ₗ (M ∘ₗ N) ∘ₗ U.symm.toLinearMap := fun M N => by
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  -- Conjugation distributes over the Pauli product (with the `(-1)^k` cocycle factor).
  have h3 : (conjEquiv U (pauliEquiv q)).toLinearMap ∘ₗ (conjEquiv U (pauliEquiv p)).toLinearMap
      = ((-1 : ℂ) ^ zDotVal q p.X) • (conjEquiv U (pauliEquiv (p + q))).toLinearMap := by
    rw [hC q, hC p, hCmul, pauliOperator_mul, hC (p + q)]
    simp only [LinearMap.comp_smul, LinearMap.smul_comp]
  have hk2 : (-1 : ℂ) ^ (zDotVal q p.X + zDotVal q p.X) = 1 := by
    rw [← two_mul, pow_mul]; norm_num
  have hkk : (-1 : ℂ) ^ zDotVal q p.X * (-1 : ℂ) ^ zDotVal q p.X = 1 := by
    rw [← pow_add]; exact hk2
  -- Invert the cocycle: `conjEquiv(p+q) = (-1)^k • (conjEquiv q ∘ conjEquiv p)`.
  have h3' : (conjEquiv U (pauliEquiv (p + q))).toLinearMap
      = ((-1 : ℂ) ^ zDotVal q p.X)
          • ((conjEquiv U (pauliEquiv q)).toLinearMap ∘ₗ
              (conjEquiv U (pauliEquiv p)).toLinearMap) := by
    rw [h3, smul_smul, ← pow_add, hk2, one_smul]
  -- Compute the phase of the product directly.
  have key : (conjEquiv U (pauliEquiv (p + q))).toLinearMap
      = ((cliffordToSymplecticPhase hU p * cliffordToSymplecticPhase hU q : ℂˣ) : ℂ)
          • pauliOperator (p + q) := by
    rw [h3', hsp q, hsp p, LinearMap.smul_comp, LinearMap.comp_smul, pauliOperator_mul]
    simp only [smul_smul]
    congr 1
    rw [Units.val_mul]
    linear_combination
      (cliffordToSymplecticPhase hU p : ℂ) * (cliffordToSymplecticPhase hU q : ℂ) * hkk
  have huniq := cliffordToSymplecticPhase_unique hU (p + q) key
  rw [← huniq, Units.val_mul]

/-- Over `𝔽₂`, every Pauli is its own additive inverse. -/
private theorem add_self_pauli (p : Pauli n) : p + p = 0 := by
  apply Pauli.ext
  · funext i
    change p.X i + p.X i = (0 : Pauli n).X i
    rw [X_zero, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · funext i
    change p.Z i + p.Z i = (0 : Pauli n).Z i
    rw [Z_zero, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-- The trivial phase: `φ(0) = 1` (a character sends `0` to the identity). -/
private theorem phase_zero_of_ker {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hker : cliffordToSymplectic hU = 1) :
    (cliffordToSymplecticPhase hU 0 : ℂ) = 1 := by
  have h := phase_add_of_ker hU hker 0 0
  rw [add_zero] at h
  have hne : (cliffordToSymplecticPhase hU 0 : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (cliffordToSymplecticPhase hU 0 : ℂ) * 1
      = (cliffordToSymplecticPhase hU 0 : ℂ) * (cliffordToSymplecticPhase hU 0 : ℂ) := by
    rw [mul_one]; exact h
  exact (mul_left_cancel₀ hne h2).symm

/-- The phases are `2`-torsion: `φ(p)·φ(p) = 1`, so `φ(p) ∈ {±1}` (since `p + p = 0`). -/
private theorem phase_sq_of_ker {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hker : cliffordToSymplectic hU = 1) (p : Pauli n) :
    (cliffordToSymplecticPhase hU p : ℂ) * (cliffordToSymplecticPhase hU p : ℂ) = 1 := by
  have h := phase_add_of_ker hU hker p p
  rw [add_self_pauli p, phase_zero_of_ker hU hker] at h
  exact h.symm

/-- The character `φ` as a `ZMod 2`-linear functional `ψ` with `φ(p) = (-1)^{ψ(p)}`:
`ψ(p) = 0` if `φ(p) = 1`, else `1`. Linearity is exactly the character property of `φ`. -/
private noncomputable def kerPhaseFunctional {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hker : cliffordToSymplectic hU = 1) :
    Pauli n →ₗ[ZMod 2] ZMod 2 where
  toFun p := if (cliffordToSymplecticPhase hU p : ℂ) = 1 then 0 else 1
  map_add' p q := by
    have hpq := phase_add_of_ker hU hker p q
    rcases mul_self_eq_one_iff.mp (phase_sq_of_ker hU hker p) with ha | ha <;>
      rcases mul_self_eq_one_iff.mp (phase_sq_of_ker hU hker q) with hb | hb
    · rw [if_pos (by rw [hpq, ha, hb]; norm_num), if_pos ha, if_pos hb]
      decide
    · rw [if_neg (by rw [hpq, ha, hb]; norm_num), if_pos ha,
        if_neg (by rw [hb]; norm_num)]
      decide
    · rw [if_neg (by rw [hpq, ha, hb]; norm_num), if_neg (by rw [ha]; norm_num),
        if_pos hb]
      decide
    · rw [if_pos (by rw [hpq, ha, hb]; norm_num), if_neg (by rw [ha]; norm_num),
        if_neg (by rw [hb]; norm_num)]
      decide
  map_smul' c p := by
    have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hc c with hc0 | hc1
    · subst hc0; simp [phase_zero_of_ker hU hker]
    · subst hc1; simp

private theorem kerPhaseFunctional_apply {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hker : cliffordToSymplectic hU = 1) (p : Pauli n) :
    kerPhaseFunctional hU hker p
      = if (cliffordToSymplecticPhase hU p : ℂ) = 1 then 0 else 1 := rfl

/-- `φ(p) = (-1)^{ψ(p)}` (as a complex number), where `ψ = kerPhaseFunctional`. -/
private theorem phase_eq_neg_one_pow {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hker : cliffordToSymplectic hU = 1) (p : Pauli n) :
    (cliffordToSymplecticPhase hU p : ℂ) = (-1 : ℂ) ^ (kerPhaseFunctional hU hker p).val := by
  rw [kerPhaseFunctional_apply]
  by_cases h : (cliffordToSymplecticPhase hU p : ℂ) = 1
  · rw [if_pos h, h]
    have : (0 : ZMod 2).val = 0 := by decide
    rw [this, pow_zero]
  · rw [if_neg h]
    rcases mul_self_eq_one_iff.mp (phase_sq_of_ker hU hker p) with h1 | h1
    · exact absurd h1 h
    · rw [h1]
      have : (1 : ZMod 2).val = 1 := by decide
      rw [this, pow_one]

/-- Bridge: `↑(zDotVal p q.X + zDotVal q p.X) = ω(p,q)` in `ZMod 2` (re-proved locally; the global
copy lives in `BornCollapse`, outside this file's import closure). -/
private theorem omega_zDotVal_cast (p q : Pauli n) :
    ((zDotVal p q.X + zDotVal q p.X : ℕ) : ZMod 2) = omega p q := by
  unfold zDotVal omega
  push_cast
  simp only [ZMod.natCast_zmod_val]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The phase by which `pauliEquiv r` conjugates `pauliEquiv p` is the commutation sign
`(-1)^{ω(r,p)}`. (The explicit cocycle exponent `E(r,p)` agrees with `ω(r,p)` modulo `2`.) -/
theorem phase_pauliEquiv_eq (r p : Pauli n) :
    (cliffordToSymplecticPhase (isCliffordOperator_pauliEquiv r) p : ℂ)
      = (-1 : ℂ) ^ (omega r p).val := by
  have hwit : (conjEquiv (pauliEquiv r) (pauliEquiv p)).toLinearMap
      = (((-1 : ℂˣ) ^ (zDotVal r r.X + zDotVal p r.X + zDotVal r (r + p).X) : ℂˣ) : ℂ)
          • pauliOperator p := by
    rw [conjEquiv_pauliEquiv_pauliEquiv]
    congr 1
  rw [← cliffordToSymplecticPhase_unique (isCliffordOperator_pauliEquiv r) p hwit]
  change (-1 : ℂ) ^ (zDotVal r r.X + zDotVal p r.X + zDotVal r (r + p).X)
      = (-1 : ℂ) ^ (omega r p).val
  apply neg_one_pow_eq_of_mod_two_eq
  rw [← omega_zDotVal_cast, ZMod.val_natCast, X_add]
  have hD := zDotVal_add_right_mod_two r r.X p.X
  omega

/-- **Forward inclusion of the kernel characterization:** if `Φ(U) = 1` (the induced symplectic map
is trivial) then `U` is a phased Pauli. Together with `pauliEquiv_mem_ker`, this gives
`ker Φ = U(1)·Pauli`. The witnessing Pauli `r` is recovered from the character `φ` of `U` by
ω-nondegeneracy (`omegaBilin.toDual`), and `U = α·pauliOp(r)` by uniqueness-mod-phase. -/
theorem isPhasedPauli_of_cliffordToSymplectic_eq_one
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (hker : cliffordToSymplectic hU = 1) : IsPhasedPauli U := by
  set r := (LinearMap.BilinForm.toDual omegaBilin (omegaBilin_nondegenerate (n := n))).symm
    (kerPhaseFunctional hU hker) with hr_def
  have hr_omega : ∀ p, omega r p = kerPhaseFunctional hU hker p := by
    intro p
    have h := LinearMap.BilinForm.apply_toDual_symm_apply
      (B := omegaBilin (n := n)) (hB := omegaBilin_nondegenerate)
      (f := kerPhaseFunctional hU hker) (v := p)
    rw [omegaBilin_apply] at h
    rw [hr_def]
    exact h
  have h_phase : ∀ p, (cliffordToSymplecticPhase hU p : ℂ)
      = (cliffordToSymplecticPhase (isCliffordOperator_pauliEquiv r) p : ℂ) := by
    intro p
    rw [phase_eq_neg_one_pow hU hker, phase_pauliEquiv_eq, hr_omega]
  have h_sym : cliffordToSymplectic hU
      = cliffordToSymplectic (isCliffordOperator_pauliEquiv r) := by
    rw [hker, cliffordToSymplectic_pauliEquiv]
  obtain ⟨α, hα⟩ :=
    cliffordOperator_unique_mod_phase hU (isCliffordOperator_pauliEquiv r) h_sym h_phase
  have hpe : (pauliEquiv r).toLinearMap = pauliOperator r := by
    refine LinearMap.ext fun ψ => ?_
    simp [pauliEquiv_apply]
  rw [hpe] at hα
  refine ⟨α⁻¹, r, ?_⟩
  rw [hα, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- **`ker Φ ⊆ U(1)·Pauli`, at the subgroup level:** every element of `ker Φ` is a phased Pauli. -/
theorem isPhasedPauli_of_mem_ker (U : cliffordSubgroup n)
    (hU : U ∈ (cliffordToSp (n := n)).ker) : IsPhasedPauli U.val := by
  rw [MonoidHom.mem_ker] at hU
  have h1 : cliffordToSymplectic U.2 = 1 := congrArg Subtype.val hU
  exact isPhasedPauli_of_cliffordToSymplectic_eq_one U.2 h1

/-- Conjugation is invariant under rescaling the conjugating operator: the global scalar `β` and its
inverse cancel. -/
private theorem conjEquiv_scaleEquiv (β : ℂˣ) (V W : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    conjEquiv (scaleEquiv β V) W = conjEquiv V W := by
  refine LinearEquiv.toLinearMap_injective (LinearMap.ext fun ψ => ?_)
  simp only [conjEquiv_apply, scaleEquiv_apply, scaleEquiv_symm_apply, LinearEquiv.coe_coe,
    map_smul]
  rw [smul_smul,
    show ((β⁻¹ : ℂˣ) : ℂ) * (β : ℂ) = 1 from by
      rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero β)], one_smul]

/-- A phased Pauli (Clifford) induces the **identity** symplectic map — the reverse of the forward
inclusion, now for *all* phased Paulis (not just bare `pauliEquiv r`). -/
private theorem cliffordToSymplectic_eq_one_of_isPhasedPauli
    {W : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hW : IsCliffordOperator W)
    (hp : IsPhasedPauli W) : cliffordToSymplectic hW = 1 := by
  obtain ⟨α, s, hαs⟩ := hp
  have hW_eq : W = scaleEquiv α (pauliEquiv s) := by
    refine LinearEquiv.toLinearMap_injective ?_
    rw [scaleEquiv_toLinearMap, hαs]
    congr 1
  refine LinearEquiv.ext fun p => ?_
  rw [cliffordToSymplectic_apply]
  have hwit : (conjEquiv W (pauliEquiv p)).toLinearMap
      = (((-1 : ℂˣ) ^ (zDotVal s s.X + zDotVal p s.X + zDotVal s (s + p).X) : ℂˣ) : ℂ)
          • pauliOperator p := by
    rw [hW_eq, conjEquiv_scaleEquiv, conjEquiv_pauliEquiv_pauliEquiv]
    congr 1
  exact (cliffordToSymplecticFun_unique hW p hwit).symm

/-- **Kernel characterization (`ker Φ = U(1)·Pauli`):** an element of the Clifford
group lies in `ker Φ` iff it is a phased Pauli. -/
theorem mem_cliffordToSp_ker_iff (U : cliffordSubgroup n) :
    U ∈ (cliffordToSp (n := n)).ker ↔ IsPhasedPauli U.val := by
  refine ⟨isPhasedPauli_of_mem_ker U, fun hp => ?_⟩
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change cliffordToSymplectic U.2 = 1
  exact cliffordToSymplectic_eq_one_of_isPhasedPauli U.2 hp

/-! ## Surjectivity of `Φ` (the Clifford–symplectic lift): conditional form

The full lift `CliffordSymplecticLift n` — every `IsClifford` symplectic automorphism is `Φ` of a
Clifford unitary — is equivalent to surjectivity of `Φ = cliffordToSp`. Surjectivity reduces to
*generation of the symplectic group `Sp(2n, 𝔽₂)`* by the gate images `Φ(H), Φ(S), Φ(CNOT),
Φ(CZ)`, together with Hilbert-side lifts of those gates. That generation theorem is a char-2
symplectic result absent from Mathlib (its `SymplecticGroup` carries only the group definition;
the orthogonal `reflections_generate` does not transfer to an isotropic form over `𝔽₂`).

This section proves the statements *around* that fact: the reduction
`Surjective Φ → CliffordSymplecticLift n`, its packaging through the gate generators (with the
generation theorem and the gate lifts as explicit `Prop` hypotheses), the `n = 0` base case, and
the isomorphism `Clₙ / ker Φ ≃* Sp(V)` that surjectivity yields. The generation theorem is
`spGeneratedByCliffordGates` (`FTQCLib.Gates.CliffordGateGeneration`); the gate lifts and the
unconditional lift `cliffordSymplecticLift_unconditional` are in `FTQCLib.Hilbert.GateLifts`. -/

/-- **Reduction to surjectivity.** If `Φ = cliffordToSp` is surjective then every `IsClifford`
symplectic automorphism lifts to a Clifford unitary, i.e. `CliffordSymplecticLift n` holds. This
isolates the entire content of the lift in the surjectivity of `Φ`. -/
theorem cliffordSymplecticLift_of_surjective
    (h : Function.Surjective (cliffordToSp (n := n))) : CliffordSymplecticLift n := by
  intro T hT
  obtain ⟨U, hU⟩ := h ⟨T, hT⟩
  exact ⟨U.1, U.2, congrArg Subtype.val hU⟩

/-- If the gate generators lie in `range Φ` (the Hilbert-side gate lifts) and
they generate `Sp(V)` (`SpGeneratedByCliffordGates`), then `Φ` is surjective. A pure
homomorphism-closure argument. -/
theorem surjective_cliffordToSp_of_generation
    (hmem : cliffordGateGens n ⊆ (cliffordToSp (n := n)).range)
    (hgen : SpGeneratedByCliffordGates n) :
    Function.Surjective (cliffordToSp (n := n)) := by
  have hgen' : Subgroup.closure (cliffordGateGens n) = ⊤ := hgen
  have hrange : (cliffordToSp (n := n)).range = ⊤ := by
    rw [eq_top_iff, ← hgen']
    exact (Subgroup.closure_le _).mpr hmem
  exact MonoidHom.range_eq_top.mp hrange

/-- **Conditional lift.** Given Hilbert-side lifts of the gates (`hmem`) and the generation
theorem (`hgen`), the Clifford–symplectic lift holds. -/
theorem cliffordSymplecticLift_of_generation
    (hmem : cliffordGateGens n ⊆ (cliffordToSp (n := n)).range)
    (hgen : SpGeneratedByCliffordGates n) : CliffordSymplecticLift n :=
  cliffordSymplecticLift_of_surjective (surjective_cliffordToSp_of_generation hmem hgen)

/-- **The isomorphism from surjectivity.** With `Φ` surjective the first isomorphism theorem
upgrades `cliffordQuotientEquivRange` to the full isomorphism `Clₙ / ker Φ ≃* Sp(V)` (and, with
the kernel characterization `ker Φ = U(1)·Pauli`, to `Clₙ / U(1)·Pauli ≃* Sp(V)`). -/
noncomputable def cliffordQuotientEquivSp
    (h : Function.Surjective (cliffordToSp (n := n))) :
    cliffordSubgroup n ⧸ (cliffordToSp (n := n)).ker ≃* spSubgroup n :=
  QuotientGroup.quotientKerEquivOfSurjective cliffordToSp h

/-- **Base case `n = 0`** (unconditional): on zero qubits `Pauli 0` is trivial, so
every symplectic automorphism is the identity `= Φ(1)`. -/
theorem cliffordSymplecticLift_zero : CliffordSymplecticLift 0 := by
  have hsub : Subsingleton (Pauli 0) := by
    refine ⟨fun a b => ?_⟩
    ext i
    · exact i.elim0
    · exact i.elim0
  intro T _hT
  refine ⟨1, isCliffordOperator_one, ?_⟩
  rw [cliffordToSymplectic_one]
  exact LinearEquiv.ext fun p => Subsingleton.elim _ _

end FTQCLib.Hilbert
