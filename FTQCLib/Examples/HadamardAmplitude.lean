/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardTotality
import FTQCLib.Examples.CarrierAmplitude

/-!
# The amplitude half of `hRaise`: the frame-side amplitude against the Walsh referee

Every Hadamard rule is certified by one equation, `amp (rule i S) = walshTransform i (amp S)`,
where `amp` is the support-restricted amplitude of a carrier state and `walshTransform` is the
single-bit Walsh transform of an arbitrary amplitude function (`FTQCLib/Examples/CharSumPairing.lean`).
`amp` lives in `FTQCLib/Examples/CarrierAmplitude.lean` (the carrier's denotation and its gauge); this
file proves that equation for the support-raising rule `hRaise` (`FTQCLib/Examples/HadamardRaise.lean`).

The proof has a support half and an amplitude half, and they meet at one `𝔽₂` value. On the
support of `hRaise`'s output, exactly one of the two Walsh branches `w[i ← 0]`, `w[i ← 1]` lies on
the input support (`branch_unique` gives at most one; the shadow equality `shadow_swap_eq` gives at
least one), and the representer pins which: the surviving branch is `w[i ← t(w)]` with
`t(w) = raiseConst + u ⬝ w`, the same branch value the exponent bridge `hRaise_eval` reads. On the
amplitude side, the emitted `2^{m−1}·t·X_i` term contributes exactly the Walsh sign `(−1)^{t·w_i}`
once `1 ≤ m`, so `ampCore` of the output is `(1/√2)·(−1)^{t·w_i}·ampCore` of the input at the
surviving branch — which is what the Walsh transform's two-term sum collapses to when one term is
off support.

Everything here is frame-pure: `DiagPhase`, `Pauli`, `Submodule`, `ℂ`. No `FTQCLib.Hilbert`.

## Main definitions

* `bellState`, `sParityL`, `sParityState` — the two example states on genuine Lagrangians: Bell at
  `m = 1`, and the odd-parity state at `m = 2` with the exponent reading the Hadamarded bit, a
  nonzero offset, and two correlated bits.

## Main results

* `hRaise_mem_support_iff` — the output support is exactly the set of `w` with one Walsh branch on
  the input support.
* `branch_eq_of_mem_support` — the representer pins the surviving branch to `raiseConst + u ⬝ w`.
* `ampCore_hRaise` — the `ampCore`-level identity: one branch, one Walsh sign, one `1/√2`.
* `amp_hRaise` — **the main theorem**: `amp (hRaise i u S) = walshTransform i (amp S)`.
* `amp_hRaise_indep` — the output amplitude does not depend on the choice of representer.
* `amp_hRaise_bell`, `amp_hRaise_sParity` — the main theorem discharged on the two examples.

## Implementation notes

* `amp` and its two branches live in `CarrierAmplitude.lean`; the Hilbert-side `F`
  (`FTQCLib/Hilbert/CharSumCorrespondence.lean`) is a separate definition that coincides with it.
* The hypotheses of `amp_hRaise` are: co-isotropy (the weakest hypothesis
  the support half uses, `orthogonal_le_of_lagrangian` discharging it for the carrier states), the
  representer pair `u i = 0` and `∀ v ∈ π_X(L), u ⬝ v = v i`, and `1 ≤ m`. The shadow condition
  `e_i ∉ π_X(L)` is not a hypothesis: it follows from the representer
  (`notMem_shadow_of_representer`). At `m = 0` the ring is trivial and the emitted sign vanishes,
  so `1 ≤ m` is load-bearing; the check module carries the row.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The `𝔽₂` pairing against an updated point -/

/-- `dotF2` is additive on the right, in subtraction form. -/
theorem dotF2_sub_right (u v v' : Fin n → ZMod 2) :
    dotF2 u (v - v') = dotF2 u v - dotF2 u v' := by
  unfold dotF2
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.sub_apply, mul_sub]

/-- A representer with `u i = 0` does not see the `i`-th coordinate: updating it changes nothing
in the pairing. -/
theorem dotF2_update_of_eq_zero {u : Fin n → ZMod 2} {i : Fin n} (hui : u i = 0)
    (w : Fin n → ZMod 2) (b : ZMod 2) :
    dotF2 u (Function.update w i b) = dotF2 u w := by
  unfold dotF2
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    rw [hui, zero_mul, zero_mul]
  · rw [Function.update_of_ne hj]

/-! ## The coset arithmetic of the two Walsh branches -/

/-- A Walsh branch of `w`, measured from the input offset, is `w` measured from the output offset
(the offset zeroed at `i`) minus a multiple of `e_i` — the multiple recording which branch. -/
theorem update_sub_offset (w x₀ : Fin n → ZMod 2) (i : Fin n) (b : ZMod 2) :
    Function.update w i b - x₀
      = (w - Function.update x₀ i 0) - (b + x₀ i + w i) • (Pi.single i 1 : Fin n → ZMod 2) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.sub_apply, Pi.smul_apply, Function.update_self, Pi.single_eq_same, smul_eq_mul]
    exact (show ∀ a b c : ZMod 2, a - b = c - 0 - (a + b + c) * 1 by decide) b (x₀ j) (w j)
  · simp only [Pi.sub_apply, Pi.smul_apply, Function.update_of_ne hj, Pi.single_eq_of_ne hj,
      smul_eq_mul, mul_zero, sub_zero]

/-- Membership in `V ⊔ ⟨e⟩` over `𝔽₂`: `v` is in it iff `v` or `v − e` is in `V`. -/
theorem mem_sup_span_single_iff (V : Submodule (ZMod 2) (Fin n → ZMod 2))
    (e v : Fin n → ZMod 2) :
    v ∈ V ⊔ Submodule.span (ZMod 2) {e} ↔ ∃ a : ZMod 2, v - a • e ∈ V := by
  constructor
  · intro h
    obtain ⟨v₁, hv₁, z, hz, rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨a, by simpa using hv₁⟩
  · rintro ⟨a, ha⟩
    have hv : v = (v - a • e) + a • e := by abel
    rw [hv]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))

/-! ## The support of `hRaise`'s output -/

/-- **Where the output lives.** On a co-isotropic `L` whose shadow omits `e_i`, a word is on
`hRaise`'s output support iff one of its two Walsh branches is on the input support. The support
equality `shadow_swap_eq` supplies the shadow; the coset arithmetic supplies the branch. -/
theorem hRaise_mem_support_iff (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L)
    (hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj S.L)
    (w : Fin n → ZMod 2) :
    (∃ p ∈ (hRaise i u S).L, w = (hRaise i u S).x₀ + p.X)
      ↔ ∃ b : ZMod 2, ∃ p ∈ S.L, Function.update w i b = S.x₀ + p.X := by
  rw [mem_support_iff (hRaise i u S) w, hRaise_shadow i u S horth hi, hRaise_x₀,
    mem_sup_span_single_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a + S.x₀ i + w i, (mem_support_iff S _).mpr ?_⟩
    rw [update_sub_offset,
      (show ∀ a b c : ZMod 2, a + b + c + b + c = a by decide) a (S.x₀ i) (w i)]
    exact ha
  · rintro ⟨b, hb⟩
    refine ⟨b + S.x₀ i + w i, ?_⟩
    have h := (mem_support_iff S _).mp hb
    rwa [update_sub_offset] at h

/-- **The representer pins the branch.** If the branch `w[i ← b]` is on the input support, then
`b` is the branch value `raiseConst + u ⬝ w` — the value `hRaise_eval` freezes the coordinate to.
With `branch_unique` this is the whole of "exactly one branch survives, and we know which". -/
theorem branch_eq_of_mem_support {i : Fin n} {u : Fin n → ZMod 2} (S : KernelSumState n)
    (hui : u i = 0) (hrep : ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i)
    {w : Fin n → ZMod 2} {b : ZMod 2}
    (hb : ∃ p ∈ S.L, Function.update w i b = S.x₀ + p.X) :
    b = raiseConst i u S.x₀ + dotF2 u w := by
  have hv := hrep _ ((mem_support_iff S _).mp hb)
  rw [dotF2_sub_right, dotF2_update_of_eq_zero hui, Pi.sub_apply, Function.update_self] at hv
  unfold raiseConst
  exact (show ∀ b x d e : ZMod 2, d - e = b - x → b = x + e + d by decide)
    b (S.x₀ i) (dotF2 u w) (dotF2 u S.x₀) hv

/-! ## The amplitude half -/

/-- **One summand of the output character sum.** The output exponent at `w ++ y` is the input
exponent at the surviving branch `w[i ← t] ++ y` plus the emitted `2^{m−1}·t·w_i`, and the latter
exponentiates to the Walsh sign `(−1)^{t·w_i}` — the `hRaise` twin of `hBranch_eval`'s coupling
step. Needs `1 ≤ m`: at `m = 0` the sign term is `0` in the trivial ring. -/
theorem exp_hRaise_term {h m : ℕ} (hm : 1 ≤ m) (i : Fin n) (u : Fin n → ZMod 2) (b : ZMod 2)
    (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2) (y : Fin h → ZMod 2) :
    Complex.exp (Complex.I * (DiagPhase.realPhase
        (raiseSubst i u b Q
          + MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * raiseForm u b
              * MvPolynomial.X (Fin.castAdd h i)) (Fin.append w y) : ℂ))
      = (-1 : ℂ) ^ ((b + dotF2 u w).val * (w i).val)
        * Complex.exp (Complex.I *
            (DiagPhase.realPhase Q (Fin.append (Function.update w i (b + dotF2 u w)) y) : ℂ)) := by
  have hdot : (dotF2 u fun j => Fin.append w y (Fin.castAdd h j)) = dotF2 u w := by
    congr 1
    funext j
    exact Fin.append_left w y j
  rw [exp_realPhase_add]
  have h1 : DiagPhase.realPhase (raiseSubst i u b Q) (Fin.append w y)
      = DiagPhase.realPhase Q (Fin.append (Function.update w i (b + dotF2 u w)) y) := by
    unfold DiagPhase.realPhase
    rw [raiseSubst_eval, hdot, update_append_castAdd]
  have heval : ((MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * raiseForm u b
      * MvPolynomial.X (Fin.castAdd h i) : DiagPhase (n + h) m)).eval (Fin.append w y)
      = ((MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1) * ((b + dotF2 u w).val : ZMod (2 ^ m)))
          * MvPolynomial.X (Fin.castAdd h i) : DiagPhase (n + h) m)).eval (Fin.append w y) := by
    rw [DiagPhase.eval_mul, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X,
      two_pow_mul_raiseForm_eval, hdot, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
  have h2 : DiagPhase.realPhase
      (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * raiseForm u b
        * MvPolynomial.X (Fin.castAdd h i) : DiagPhase (n + h) m) (Fin.append w y)
      = DiagPhase.realPhase
          (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1) * ((b + dotF2 u w).val : ZMod (2 ^ m)))
            * MvPolynomial.X (Fin.castAdd h i) : DiagPhase (n + h) m) (Fin.append w y) := by
    unfold DiagPhase.realPhase
    rw [heval]
  rw [h1, h2, exp_coupling hm]
  ring

/-- **The `ampCore`-level identity.** The output amplitude at `w` is `1/√2` times the Walsh sign
`(−1)^{t·w_i}` times the input amplitude at the surviving branch `w[i ← t]`, with
`t = raiseConst + u ⬝ w`. No support hypothesis: this is the raw character sum, and the `1/√2` is
`hRaise`'s `c ↦ c/√2`. -/
theorem ampCore_hRaise (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n) (hm : 1 ≤ S.m)
    (w : Fin n → ZMod 2) :
    ampCore (hRaise i u S).m (hRaise i u S).h (hRaise i u S).Q (hRaise i u S).c w
      = (1 / (Real.sqrt 2 : ℂ))
          * ((-1 : ℂ) ^ ((raiseConst i u S.x₀ + dotF2 u w).val * (w i).val)
            * ampCore S.m S.h S.Q S.c
                (Function.update w i (raiseConst i u S.x₀ + dotF2 u w))) := by
  change ampCore S.m S.h
      (raiseSubst i u (raiseConst i u S.x₀) S.Q
        + MvPolynomial.C ((2 : ZMod (2 ^ S.m)) ^ (S.m - 1)) * raiseForm u (raiseConst i u S.x₀)
            * MvPolynomial.X (Fin.castAdd S.h i))
      (S.c / (Real.sqrt 2 : ℂ)) w = _
  unfold ampCore
  rw [Finset.sum_congr rfl (fun y _ => exp_hRaise_term hm i u (raiseConst i u S.x₀) S.Q w y),
    ← Finset.mul_sum]
  ring

/-- **`hRaise` is the Walsh transform on the support-restricted amplitude.**
On a co-isotropic `L`, with `u` a representer of the coordinate functional on the shadow with
`u i = 0`, and `1 ≤ m`: `amp (hRaise i u S) = walshTransform i (amp S)`. The shadow condition
`e_i ∉ π_X(L)` is a consequence of the representer, not an extra hypothesis. -/
theorem amp_hRaise (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L)
    (hui : u i = 0) (hrep : ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i) (hm : 1 ≤ S.m) :
    amp (hRaise i u S) = walshTransform i (amp S) := by
  have hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj S.L :=
    notMem_shadow_of_representer hui hrep
  funext w
  unfold walshTransform
  by_cases hsup : ∃ p ∈ (hRaise i u S).L, w = (hRaise i u S).x₀ + p.X
  · obtain ⟨b, hb⟩ := (hRaise_mem_support_iff i u S horth hi w).mp hsup
    have hbt : b = raiseConst i u S.x₀ + dotF2 u w := branch_eq_of_mem_support S hui hrep hb
    rw [amp_pos hsup, ampCore_hRaise i u S hm w, ← hbt]
    have hoff : ¬ ∃ p ∈ S.L, Function.update w i (b + 1) = S.x₀ + p.X := by
      intro hb'
      have h' := branch_eq_of_mem_support S hui hrep hb'
      rw [← hbt] at h'
      exact absurd h' ((show ∀ b : ZMod 2, b + 1 ≠ b by decide) b)
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) b with h0 | h1
    · subst h0
      have hoff1 : ¬ ∃ p ∈ S.L, Function.update w i 1 = S.x₀ + p.X := by
        rwa [zero_add] at hoff
      rw [amp_pos hb, amp_neg hoff1, ZMod.val_zero, zero_mul, pow_zero, one_mul, mul_zero,
        add_zero]
    · subst h1
      have hoff0 : ¬ ∃ p ∈ S.L, Function.update w i 0 = S.x₀ + p.X := by
        rwa [(show (1 : ZMod 2) + 1 = 0 by decide)] at hoff
      rw [amp_pos hb, amp_neg hoff0, (show ((1 : ZMod 2)).val = 1 by decide), one_mul,
        neg_one_pow_val]
      ring
  · rw [amp_neg hsup]
    have hnone : ∀ b : ZMod 2, ¬ ∃ p ∈ S.L, Function.update w i b = S.x₀ + p.X := fun b hb =>
      hsup ((hRaise_mem_support_iff i u S horth hi w).mpr ⟨b, hb⟩)
    rw [amp_neg (hnone 0), amp_neg (hnone 1)]
    ring

/-- **Choice-independence.** Two representers give the same output amplitude: both equal the
Walsh transform of the input. `u` is data for the exponent, not for the denotation. -/
theorem amp_hRaise_indep (i : Fin n) (u u' : Fin n → ZMod 2) (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L)
    (hui : u i = 0) (hrep : ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i)
    (hui' : u' i = 0) (hrep' : ∀ v ∈ Submodule.map xProj S.L, dotF2 u' v = v i)
    (hm : 1 ≤ S.m) :
    amp (hRaise i u S) = amp (hRaise i u' S) := by
  rw [amp_hRaise i u S horth hui hrep hm, amp_hRaise i u' S horth hui' hrep' hm]

/-! ## The witnesses, on genuine Lagrangians

Two states, chosen by the degrees of freedom they exercise. The Bell state (`m = 1`, flat
exponent, zero offset) is the coverage row. The
odd-parity state (`m = 2`, exponent `X₀` so the freeze reads the Hadamarded bit, offset
`(1,0,0)` so `raiseConst = 1`, representer `![0,1,1]` with two active bits) is the discriminating
row: it is the support-level counterpart of the exponent-level example `hRaise_sParity_exponent`,
whose `L` is the placeholder `⊤`. -/

/-- The Bell state on the carrier: `L = bellL`, zero offset, flat exponent, `m = 1`. -/
noncomputable def bellState : KernelSumState 2 where
  m := 1
  h := 0
  Q := 0
  c := 1
  L := bellL
  x₀ := 0

/-- `amp_hRaise` on the Bell state, every hypothesis discharged on `bellL`. -/
theorem amp_hRaise_bell :
    amp (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState)
      = walshTransform 0 (amp bellState) :=
  amp_hRaise 0 ![0, 1] bellState bellL_coisotropic bellL_representer.1 bellL_representer.2 le_rfl

/-- The odd-parity Lagrangian `⟨Z₀Z₁Z₂, X₀X₁, X₁X₂⟩` by its constraints: even X-weight, equal
Z-entries. Its X-shadow is the even-weight plane, which omits `e₀`. -/
def sParityL : Submodule (ZMod 2) (Pauli 3) where
  carrier := {p | p.X 0 + p.X 1 + p.X 2 = 0 ∧ p.Z 0 = p.Z 1 ∧ p.Z 1 = p.Z 2}
  zero_mem' := ⟨rfl, rfl, rfl⟩
  add_mem' := fun {p q} hp hq =>
    ⟨by
      simp only [X_add, Pi.add_apply]
      linear_combination hp.1 + hq.1,
     by simp [hp.2.1, hq.2.1], by simp [hp.2.2, hq.2.2]⟩
  smul_mem' := fun c {p} hp =>
    ⟨by
      simp only [X_smul, Pi.smul_apply, smul_eq_mul]
      linear_combination c * hp.1,
     by simp [hp.2.1], by simp [hp.2.2]⟩

@[simp] theorem mem_sParityL {p : Pauli 3} :
    p ∈ sParityL ↔ p.X 0 + p.X 1 + p.X 2 = 0 ∧ p.Z 0 = p.Z 1 ∧ p.Z 1 = p.Z 2 :=
  Iff.rfl

/-- The odd-parity Lagrangian is co-isotropic, discharged against its three generators. -/
theorem sParityL_coisotropic :
    LinearMap.BilinForm.orthogonal omegaBilin sParityL ≤ sParityL := by
  intro q hq
  have ha := hq ⟨0, ![1, 1, 1]⟩ ⟨by decide, by decide, by decide⟩
  have hb := hq ⟨![1, 1, 0], 0⟩ ⟨by decide, rfl, rfl⟩
  have hc := hq ⟨![0, 1, 1], 0⟩ ⟨by decide, rfl, rfl⟩
  change omega (⟨0, ![1, 1, 1]⟩ : Pauli 3) q = 0 at ha
  change omega (⟨![1, 1, 0], 0⟩ : Pauli 3) q = 0 at hb
  change omega (⟨![0, 1, 1], 0⟩ : Pauli 3) q = 0 at hc
  rw [omega_pureZ] at ha
  rw [omega_pureX] at hb hc
  unfold dotF2 at ha hb hc
  rw [Fin.sum_univ_three] at ha hb hc
  refine ⟨?_, ?_, ?_⟩
  · exact (show ∀ a b c : ZMod 2, 1 * a + 1 * b + 1 * c = 0 → a + b + c = 0 by decide)
      _ _ _ ha
  · exact (show ∀ a b c : ZMod 2, 1 * a + 1 * b + 0 * c = 0 → a = b by decide) _ _ _ hb
  · exact (show ∀ a b c : ZMod 2, 0 * a + 1 * b + 1 * c = 0 → b = c by decide) _ _ _ hc

/-- Bit `0` of the odd-parity Lagrangian is not X-supported: `e₀` has odd weight. -/
theorem sParityL_not_mem_shadow :
    (Pi.single 0 1 : Fin 3 → ZMod 2) ∉ Submodule.map xProj sParityL := by
  intro hmem
  obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp hmem
  rw [xProj_apply] at hpX
  have h := hp.1
  rw [hpX] at h
  exact absurd h (by decide)

/-- `![0,1,1]` is *the* representer for bit `0` on the even-weight shadow: `u 0 = 0`, and
`u ⬝ v = v₁ + v₂ = v₀` there. -/
theorem sParityL_representer :
    (![0, 1, 1] : Fin 3 → ZMod 2) 0 = 0
      ∧ ∀ v ∈ Submodule.map xProj sParityL, dotF2 ![0, 1, 1] v = v 0 := by
  refine ⟨by decide, ?_⟩
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
  rw [xProj_apply]
  unfold dotF2
  rw [Fin.sum_univ_three]
  exact (show ∀ a b c : ZMod 2, a + b + c = 0 → 0 * a + 1 * b + 1 * c = a by decide)
    _ _ _ hp.1

/-- The odd-parity state on the carrier at `m = 2`: support `x₀ + π_X(sParityL)` with
`x₀ = (1,0,0)` (the odd-parity coset), exponent `X₀` (the S-phase `i^{v₀}`, so the freeze has
work to do), `h = 0`. -/
noncomputable def sParityState : KernelSumState 3 where
  m := 2
  h := 0
  Q := MvPolynomial.X (Fin.castAdd 0 0)
  c := 1
  L := sParityL
  x₀ := ![1, 0, 0]

/-- `amp_hRaise` on the odd-parity state at `m = 2`, every hypothesis discharged: the emitted
sign, the frozen exponent reading the bit, the nonzero offset, and the two-bit representer are
all live in this row. -/
theorem amp_hRaise_sParity :
    amp (hRaise 0 (![0, 1, 1] : Fin 3 → ZMod 2) sParityState)
      = walshTransform 0 (amp sParityState) :=
  amp_hRaise 0 ![0, 1, 1] sParityState sParityL_coisotropic sParityL_representer.1
    sParityL_representer.2 (by decide)

end FTQCLib.Frame.Walkthrough
