/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierAmplitude
import FTQCLib.Examples.DyadicCharacter
import FTQCLib.Stabilizer.AmplitudeStabilizer
import FTQCLib.Examples.HadamardTotality

/-!
# Well-formedness and the floor stratum

A record `⟨m, h, Q, c, L, x₀⟩` is a **carrier** when its precision is positive, its `L` is a
Lagrangian (isotropic and co-isotropic), and its denotation is not the zero function
(`IsCarrier`); the dimension of `L` is then `n` (`finrank_eq_of_isCarrier`). A carrier is on the
**floor** when its Lagrangian stabilizes its denotation with signs (`IsFloor`) — a stratum of the
carriers, not an invariant. On the floor the Lagrangian is determined by the state
(`L_eq_of_stateEq_of_isFloor`).

At `h = 0` the floor has an exponent-level reading. For `g ∈ L` write the **defect**
`q(w + g.X) − q(w) − 2^{m−1}·(g.Z·w)`; the basepoint-free exponent law (`ShiftLaw`) says the
defect is constant over the support coset, for each `g`. `isFloor_iff_shiftLaw` proves this is
exactly the floor at `h = 0`: the Pauli action of `g` on the amplitude `c·charOf(q(w))` reads the
defect through the dyadic character, and a constant defect means a scalar action — the scalar is
`±1` because every Pauli is an involution. The sign is not a hypothesis of the law; the law has
no basepoint, and no constraint on the constant.

**Completeness at `h = 0`.** Two `h = 0` records at one precision with the same nonzero
denotation have the same support coset and exponents that differ by a constant on it, absorbed by
the scale (`gauge_of_stateEq`): the gauge rewrites R1–R4 of `CarrierAmplitude.lean` generate
`StateEq` there. This is a fact about `h = 0` and `amp ≠ 0`, not about the floor.

Everything here is frame-pure. No `FTQCLib.Hilbert`.

## Main definitions

* `IsCarrier`, `IsFloor` — well-formedness and the floor stratum.
* `ShiftLaw` — the basepoint-free exponent law on an `h = 0` record.

## Main results

* `finrank_eq_of_isCarrier`, `c_ne_zero_of_isCarrier`.
* `L_eq_of_stateEq_of_isFloor` — the floor's Lagrangian is determined by the state.
* `isFloor_iff_shiftLaw` — the floor at `h = 0` is the exponent law.
* `gauge_of_stateEq` — completeness of R1–R4 at `h = 0`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## Well-formedness -/

/-- A carrier record: positive precision, a Lagrangian `L` (isotropic and co-isotropic), and a
nonzero denotation. -/
def IsCarrier (S : KernelSumState n) : Prop :=
  1 ≤ S.m ∧ IsStabilizer S.L ∧ LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L ∧ amp S ≠ 0

/-- `ampCore` with scale `0` is `0`. -/
theorem ampCore_c_zero (m h : ℕ) (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2) :
    ampCore m h Q 0 w = 0 := by
  unfold ampCore
  simp

/-- A record with scale `0` denotes the zero function. -/
theorem amp_c_zero (S : KernelSumState n) (hc : S.c = 0) : amp S = 0 := by
  funext w
  by_cases hw : ∃ p ∈ S.L, w = S.x₀ + p.X
  · rw [amp_pos hw, hc, ampCore_c_zero]
    rfl
  · rw [amp_neg hw]
    rfl

/-- A carrier's scale is nonzero. -/
theorem c_ne_zero_of_isCarrier {S : KernelSumState n} (hS : IsCarrier S) : S.c ≠ 0 :=
  fun hc => hS.2.2.2 (amp_c_zero S hc)

/-- A carrier's Lagrangian has dimension `n`. -/
theorem finrank_eq_of_isCarrier {S : KernelSumState n} (hS : IsCarrier S) :
    finrank (ZMod 2) S.L = n := by
  have hle : finrank (ZMod 2) S.L ≤ n := finrank_le_of_isStabilizer hS.2.1
  have hmono : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal omegaBilin S.L)
      ≤ finrank (ZMod 2) S.L := Submodule.finrank_mono hS.2.2.1
  rw [LinearMap.BilinForm.finrank_orthogonal omegaBilin_nondegenerate, finrank_Pauli] at hmono
  omega

/-! ## The floor stratum -/

/-- The floor stratum: a carrier whose Lagrangian stabilizes its denotation with signs. -/
def IsFloor (S : KernelSumState n) : Prop :=
  IsCarrier S ∧ StabilizedBy S.L (amp S)

/-- On the floor the Lagrangian is determined by the state. -/
theorem L_eq_of_stateEq_of_isFloor {S T : KernelSumState n} (hS : IsFloor S) (hT : IsFloor T)
    (h : StateEq S T) : S.L = T.L := by
  have h' : amp S = amp T := h
  refine eq_of_stabilizedBy_of_stabilizedBy (finrank_eq_of_isCarrier hS.1)
    (finrank_eq_of_isCarrier hT.1) hS.1.2.2.2 hS.2 ?_
  rw [h']
  exact hT.2

/-! ## The `h = 0` amplitude and its support -/

/-- On support, an `h = 0` record denotes `c · charOf(q(w))`. -/
theorem amp_ofKernelState_pos (K : KernelState n) {w : Fin n → ZMod 2}
    (hw : ∃ p ∈ K.L, w = K.x₀ + p.X) :
    amp (ofKernelState K) w = K.c * charOf K.m (DiagPhase.eval K.q w) := by
  rw [amp_pos (S := ofKernelState K) hw]
  change ampCore K.m 0 K.q K.c w = _
  rw [ampCore_zero, exp_realPhase_eq_charOf]

/-- Off support, an `h = 0` record denotes `0`. -/
theorem amp_ofKernelState_neg (K : KernelState n) {w : Fin n → ZMod 2}
    (hw : ¬ ∃ p ∈ K.L, w = K.x₀ + p.X) : amp (ofKernelState K) w = 0 :=
  amp_neg (S := ofKernelState K) hw

/-- Two `𝔽₂`-vectors sum to zero when equal. -/
theorem vec_add_self (v : Fin n → ZMod 2) : v + v = 0 := by
  funext j
  exact (show ∀ x : ZMod 2, x + x = 0 by decide) (v j)

/-- The support coset is closed under adding the X-part of an element of `L`. -/
theorem support_add_X {K : KernelState n} {g : Pauli n} (hg : g ∈ K.L) {w : Fin n → ZMod 2}
    (hw : ∃ p ∈ K.L, w = K.x₀ + p.X) : ∃ p ∈ K.L, w + g.X = K.x₀ + p.X := by
  obtain ⟨p, hp, rfl⟩ := hw
  exact ⟨p + g, Submodule.add_mem _ hp hg, by rw [X_add, add_assoc]⟩

/-- Adding the X-part of an element of `L` preserves and reflects support membership. -/
theorem support_add_X_iff {K : KernelState n} {g : Pauli n} (hg : g ∈ K.L)
    (w : Fin n → ZMod 2) :
    (∃ p ∈ K.L, w + g.X = K.x₀ + p.X) ↔ (∃ p ∈ K.L, w = K.x₀ + p.X) := by
  constructor
  · intro h
    have h' := support_add_X hg h
    rwa [add_assoc, vec_add_self, add_zero] at h'
  · exact support_add_X hg

/-- The offset is on the support. -/
theorem x₀_mem_support (K : KernelState n) : ∃ p ∈ K.L, K.x₀ = K.x₀ + p.X :=
  ⟨0, Submodule.zero_mem _, by simp⟩

/-! ## The exponent law -/

/-- The basepoint-free exponent law on an `h = 0` record: for each `g ∈ L` the defect
`q(w + g.X) − q(w) − 2^{m−1}·(g.Z·w)` is one constant over the support coset. -/
def ShiftLaw (K : KernelState n) : Prop :=
  ∀ g ∈ K.L, ∃ k : ZMod (2 ^ K.m), ∀ w : Fin n → ZMod 2, (∃ p ∈ K.L, w = K.x₀ + p.X) →
    DiagPhase.eval K.q (w + g.X) - DiagPhase.eval K.q w
      - (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g w : ℕ) : ZMod (2 ^ K.m)) = k

/-- The parity identity behind both directions: the top-bit multiple of `g.Z·(w + g.X)` is the
top-bit multiple of `g.Z·w` plus that of `yWeight g`. -/
theorem two_pow_pred_mul_zDot_add_X {m : ℕ} (g : Pauli n) (w : Fin n → ZMod 2) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) * ((zDot g (w + g.X) : ℕ) : ZMod (2 ^ m))
      = (2 : ZMod (2 ^ m)) ^ (m - 1) * ((zDot g w : ℕ) : ZMod (2 ^ m))
        + (2 : ZMod (2 ^ m)) ^ (m - 1) * ((yWeight g : ℕ) : ZMod (2 ^ m)) := by
  rw [← mul_add, ← Nat.cast_add]
  apply two_pow_pred_mul_eq_of_cast_eq
  rw [zDot_cast_two_add_right, Nat.cast_add]
  rfl

/-- The sign of `g` at `w + g.X` is the sign at `w` times the sign of `yWeight g`. -/
theorem neg_one_pow_zDot_add_X (g : Pauli n) (w : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDot g (w + g.X) = (-1) ^ zDot g w * (-1) ^ yWeight g := by
  rw [← pow_add]
  apply neg_one_pow_eq_of_cast_eq
  rw [zDot_cast_two_add_right, Nat.cast_add]
  rfl

/-- On an `h = 0` record with positive precision, a constant defect `k` along `g` makes the action
of `g` the scalar `i^{yWeight g}·(−1)^{yWeight g}·charOf k` on the denotation. -/
theorem pauliAct_amp_ofKernelState_of_defect (K : KernelState n) (hm : 1 ≤ K.m) {g : Pauli n}
    (hg : g ∈ K.L) {k : ZMod (2 ^ K.m)}
    (hk : ∀ w : Fin n → ZMod 2, (∃ p ∈ K.L, w = K.x₀ + p.X) →
      DiagPhase.eval K.q (w + g.X) - DiagPhase.eval K.q w
        - (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g w : ℕ) : ZMod (2 ^ K.m)) = k) :
    pauliAct g (amp (ofKernelState K))
      = fun w => (Complex.I ^ yWeight g * (-1) ^ yWeight g * charOf K.m k)
          * amp (ofKernelState K) w := by
  funext w
  simp only [pauliAct]
  by_cases hw : ∃ p ∈ K.L, w = K.x₀ + p.X
  · have hw' := support_add_X hg hw
    rw [amp_ofKernelState_pos K hw', amp_ofKernelState_pos K hw]
    have hshift : DiagPhase.eval K.q (w + g.X)
        = DiagPhase.eval K.q w + k
          + (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g w : ℕ) : ZMod (2 ^ K.m)) := by
      linear_combination hk w hw
    rw [hshift, charOf_add, charOf_add, charOf_two_pow_mul hm, neg_one_pow_zDot_add_X]
    have hsq : ((-1 : ℂ) ^ zDot g w) * (-1) ^ zDot g w = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    linear_combination (Complex.I ^ yWeight g * (-1) ^ yWeight g * charOf K.m k * K.c
      * charOf K.m (DiagPhase.eval K.q w)) * hsq
  · have hw' : ¬ ∃ p ∈ K.L, w + g.X = K.x₀ + p.X := fun h => hw ((support_add_X_iff hg w).mp h)
    rw [amp_ofKernelState_neg K hw', amp_ofKernelState_neg K hw]
    ring

/-- **The floor at `h = 0` is the exponent law.** -/
theorem isFloor_iff_shiftLaw (K : KernelState n) (hc : IsCarrier (ofKernelState K)) :
    IsFloor (ofKernelState K) ↔ ShiftLaw K := by
  have hm : 1 ≤ K.m := hc.1
  have hcne : K.c ≠ 0 := c_ne_zero_of_isCarrier hc
  constructor
  · rintro ⟨-, hs⟩ g hg
    obtain ⟨s, hsg⟩ := hs g hg
    -- the character of the shifted defect is one scalar over the support
    have key : ∀ w : Fin n → ZMod 2, (∃ p ∈ K.L, w = K.x₀ + p.X) →
        Complex.I ^ yWeight g * charOf K.m
          ((2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g (w + g.X) : ℕ) : ZMod (2 ^ K.m))
            + (DiagPhase.eval K.q (w + g.X) - DiagPhase.eval K.q w))
          = (-1) ^ s.val := by
      intro w hw
      have hw' := support_add_X hg hw
      have h1 := congrFun hsg w
      simp only [pauliAct] at h1
      rw [amp_ofKernelState_pos K hw', amp_ofKernelState_pos K hw,
        ← charOf_sub_mul K.m (DiagPhase.eval K.q (w + g.X)) (DiagPhase.eval K.q w)] at h1
      have hne : K.c * charOf K.m (DiagPhase.eval K.q w) ≠ 0 :=
        mul_ne_zero hcne (charOf_ne_zero _ _)
      have h2 : (Complex.I ^ yWeight g * (-1) ^ zDot g (w + g.X)
          * charOf K.m (DiagPhase.eval K.q (w + g.X) - DiagPhase.eval K.q w))
            * (K.c * charOf K.m (DiagPhase.eval K.q w))
          = (-1) ^ s.val * (K.c * charOf K.m (DiagPhase.eval K.q w)) := by
        linear_combination h1
      have h3 := mul_right_cancel₀ hne h2
      rw [← charOf_two_pow_mul hm (zDot g (w + g.X)), mul_assoc, ← charOf_add] at h3
      exact h3
    refine ⟨DiagPhase.eval K.q (K.x₀ + g.X) - DiagPhase.eval K.q K.x₀
      - (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g K.x₀ : ℕ) : ZMod (2 ^ K.m)), ?_⟩
    intro w hw
    have hI : Complex.I ^ yWeight g ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    have hEq := charOf_injective K.m
      (mul_left_cancel₀ hI ((key w hw).trans (key K.x₀ (x₀_mem_support K)).symm))
    have hpar_w := two_pow_pred_mul_zDot_add_X (m := K.m) g w
    have hpar_x := two_pow_pred_mul_zDot_add_X (m := K.m) g K.x₀
    have h2 : (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * 2 = 0 := two_pow_pred_mul_two
    linear_combination hEq - hpar_w + hpar_x - ((zDot g w : ℕ) : ZMod (2 ^ K.m)) * h2
      + ((zDot g K.x₀ : ℕ) : ZMod (2 ^ K.m)) * h2
  · intro hlaw
    refine ⟨hc, ?_⟩
    intro g hg
    obtain ⟨k, hk⟩ := hlaw g hg
    -- the action of `g` is the scalar `lam` on the denotation
    set lam : ℂ := Complex.I ^ yWeight g * (-1) ^ yWeight g * charOf K.m k with hlam
    have hact : pauliAct g (amp (ofKernelState K)) = fun w => lam * amp (ofKernelState K) w :=
      pauliAct_amp_ofKernelState_of_defect K hm hg hk
    -- the scalar squares to one, so it is a sign
    have hsq : lam * lam = 1 := by
      have hinv := pauliAct_pauliAct g (amp (ofKernelState K))
      rw [hact, pauliAct_mul_left, hact] at hinv
      obtain ⟨w, hw⟩ := Function.ne_iff.mp hc.2.2.2
      have h := congrFun hinv w
      simp only [Pi.zero_apply] at hw
      have h' : (lam * lam) * amp (ofKernelState K) w = 1 * amp (ofKernelState K) w := by
        rw [one_mul]
        linear_combination h
      exact mul_right_cancel₀ hw h'
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exact ⟨0, by rw [hact, h1]; simp⟩
    · refine ⟨1, ?_⟩
      rw [hact, h1]
      have hv : ((1 : ZMod 2)).val = 1 := by decide
      rw [hv]
      simp

/-! ## Completeness at `h = 0` -/

/-- A nonzero `h = 0` record is nonzero exactly on its support. -/
theorem amp_ofKernelState_ne_zero_iff (K : KernelState n) (hc : K.c ≠ 0) (w : Fin n → ZMod 2) :
    amp (ofKernelState K) w ≠ 0 ↔ ∃ p ∈ K.L, w = K.x₀ + p.X := by
  constructor
  · intro h
    by_contra hw
    exact h (amp_ofKernelState_neg K hw)
  · intro hw
    rw [amp_ofKernelState_pos K hw]
    exact mul_ne_zero hc (charOf_ne_zero _ _)

/-- **Completeness at `h = 0`.** Two `h = 0` records at one precision with the same nonzero
denotation have the same X-shadow, offsets differing by a shadow vector, and exponents differing
by one constant on the support, absorbed by the scale — R1–R4 generate `StateEq` at `h = 0`. -/
theorem gauge_of_stateEq {m : ℕ} {q q' : DiagPhase n m} {c c' : ℂ}
    {L L' : Submodule (ZMod 2) (Pauli n)} {x₀ x₀' : Fin n → ZMod 2}
    (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : amp (ofKernelState ⟨m, q, c, L, x₀⟩) = amp (ofKernelState ⟨m, q', c', L', x₀'⟩)) :
    Submodule.map xProj L = Submodule.map xProj L'
      ∧ x₀' - x₀ ∈ Submodule.map xProj L
      ∧ ∃ a : ZMod (2 ^ m), c' * charOf m a = c
          ∧ ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X)
            → DiagPhase.eval q' w = DiagPhase.eval q w + a := by
  set K : KernelState n := ⟨m, q, c, L, x₀⟩ with hK
  set K' : KernelState n := ⟨m, q', c', L', x₀'⟩ with hK'
  -- the supports coincide
  have hsupp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) ↔ (∃ p ∈ L', w = x₀' + p.X) := by
    intro w
    rw [← amp_ofKernelState_ne_zero_iff K hc w, ← amp_ofKernelState_ne_zero_iff K' hc' w, h]
  have hx₀' : ∃ p ∈ L, x₀' = x₀ + p.X := (hsupp x₀').mpr (x₀_mem_support K')
  have hx₀ : ∃ p ∈ L', x₀ = x₀' + p.X := (hsupp x₀).mp (x₀_mem_support K)
  have hdiff : x₀' - x₀ ∈ Submodule.map xProj L := by
    obtain ⟨p, hp, hpX⟩ := hx₀'
    refine Submodule.mem_map.mpr ⟨p, hp, ?_⟩
    rw [xProj_apply, hpX]
    abel
  have hdiff' : x₀ - x₀' ∈ Submodule.map xProj L' := by
    obtain ⟨p, hp, hpX⟩ := hx₀
    refine Submodule.mem_map.mpr ⟨p, hp, ?_⟩
    rw [xProj_apply, hpX]
    abel
  refine ⟨?_, hdiff, ?_⟩
  · -- the shadows coincide
    ext v
    constructor
    · intro hv
      have h1 : ∃ p ∈ L, x₀ + v = x₀ + p.X := by
        obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp hv
        exact ⟨p, hp, by rw [xProj_apply] at hpX; rw [hpX]⟩
      have h2 := (mem_support_iff (ofKernelState K') (x₀ + v)).mp ((hsupp _).mp h1)
      change x₀ + v - x₀' ∈ Submodule.map xProj L' at h2
      have h3 : v = (x₀ + v - x₀') - (x₀ - x₀') := by abel
      rw [h3]
      exact Submodule.sub_mem _ h2 hdiff'
    · intro hv
      have h1 : ∃ p ∈ L', x₀' + v = x₀' + p.X := by
        obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp hv
        exact ⟨p, hp, by rw [xProj_apply] at hpX; rw [hpX]⟩
      have h2 := (mem_support_iff (ofKernelState K) (x₀' + v)).mp ((hsupp _).mpr h1)
      change x₀' + v - x₀ ∈ Submodule.map xProj L at h2
      have h3 : v = (x₀' + v - x₀) - (x₀' - x₀) := by abel
      rw [h3]
      exact Submodule.sub_mem _ h2 hdiff
  · -- the exponents differ by a constant on the support
    refine ⟨DiagPhase.eval q' x₀ - DiagPhase.eval q x₀, ?_, ?_⟩
    · have h0 := congrFun h x₀
      rw [amp_ofKernelState_pos K (x₀_mem_support K),
        amp_ofKernelState_pos K' ((hsupp x₀).mp (x₀_mem_support K))] at h0
      change c * charOf m (DiagPhase.eval q x₀) = c' * charOf m (DiagPhase.eval q' x₀) at h0
      have hne : charOf m (DiagPhase.eval q x₀) ≠ 0 := charOf_ne_zero _ _
      apply mul_right_cancel₀ hne
      rw [mul_assoc, charOf_sub_mul]
      exact h0.symm
    · intro w hw
      have hw' := (hsupp w).mp hw
      have h0 := congrFun h x₀
      rw [amp_ofKernelState_pos K (x₀_mem_support K),
        amp_ofKernelState_pos K' ((hsupp x₀).mp (x₀_mem_support K))] at h0
      change c * charOf m (DiagPhase.eval q x₀) = c' * charOf m (DiagPhase.eval q' x₀) at h0
      have hw0 := congrFun h w
      rw [amp_ofKernelState_pos K hw, amp_ofKernelState_pos K' hw'] at hw0
      change c * charOf m (DiagPhase.eval q w) = c' * charOf m (DiagPhase.eval q' w) at hw0
      -- charOf (q' w − q w) = charOf (q' x₀ − q x₀), from the two equations
      have hne : c * charOf m (DiagPhase.eval q x₀) * charOf m (DiagPhase.eval q w) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hc (charOf_ne_zero _ _)) (charOf_ne_zero _ _)
      have hEq : charOf m (DiagPhase.eval q' w - DiagPhase.eval q w)
          = charOf m (DiagPhase.eval q' x₀ - DiagPhase.eval q x₀) := by
        apply mul_left_cancel₀ hne
        have e1 := charOf_sub_mul m (DiagPhase.eval q' w) (DiagPhase.eval q w)
        have e2 := charOf_sub_mul m (DiagPhase.eval q' x₀) (DiagPhase.eval q x₀)
        linear_combination (c * charOf m (DiagPhase.eval q x₀)) * e1
          - (c * charOf m (DiagPhase.eval q w)) * e2
          + charOf m (DiagPhase.eval q' w) * h0
          - charOf m (DiagPhase.eval q' x₀) * hw0
      have := charOf_injective m hEq
      linear_combination this

end FTQCLib.Frame.Walkthrough
