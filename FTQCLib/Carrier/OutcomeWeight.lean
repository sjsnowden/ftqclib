/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.Conditioning
import FTQCLib.Carrier.CarrierState
import FTQCLib.Carrier.CharSumPairing

/-!
# The outcome weight

Carrier states are not renormalised (decision D3, `docs/TARGETS.md`): conditioning a carrier state
`S` on a Pauli `P` with its sign at outcome `b` (`condition`, `FTQCLib/Carrier/Conditioning.lean`)
keeps the factor of the projection, and the weight of the outcome is the squared norm of what is
left. The norm is `ampNormSq S = Σ_w |amp S w|²`, the squared norm of the support-restricted
amplitude, and `outcomeWeight S P b` is `ampNormSq` of the conditioned state. A weight of zero is
an outcome that cannot occur; its conditioned state is the zero state (D10).

`carrierNormSq` (`FTQCLib/Carrier/CharSumPairing.lean`) is not this norm in general: it sums
`ampCore` over every word and ignores the support. The two agree when the support is every word,
that is when the support's directions `π_X(L)` are the whole space.

**The two weights sum to the input's norm.** The projections `Π_0` and `Π_1` of
`pauliProjection` add up to the identity and are orthogonal, since a Hermitian Pauli squares to
the identity and is self-adjoint; so the squared norms of the two conditioned amplitudes add up to
the input's. This needs `amp_condition`, and so the co-isotropy of `L` it takes.

**On a floor each weight is 0, ½ or 1 of the input's.** A floor's amplitude is stabilized, with
signs, by its Lagrangian `L`. If `P` commutes with all of `L` it lies in `L^⊥ ⊆ L`, so it acts on
the amplitude as a sign and the outcome is certain or impossible. Otherwise an element of `L`
anticommutes with `P`, acts on the amplitude as a sign and exchanges the two projections, so the
two weights are equal. The theorem takes only what that argument uses, co-isotropy and the
stabilization; a floor (`IsFloor`) supplies both.

## Main definitions

* `ampNormSq` — the squared norm `Σ_w |amp S w|²` of the amplitude.
* `outcomeWeight` — the weight of outcome `b`: `ampNormSq` of `condition S P b`.

## Main results

* `outcomeWeight_eq` — the weight is the squared norm of the projection `½(S + (−1)^b · P S)`.
* `outcomeWeight_add` — the two weights sum to `ampNormSq S`.
* `outcomeWeight_floor` — on a stabilized, co-isotropic state each weight is `0`, `ampNormSq S / 2`
  or `ampNormSq S`.
* `ampNormSq_eq_carrierNormSq` — on full support the two norms agree.
* `normSq_half_add_add_normSq_half_sub`, `sum_normSq_projection` — the parallelogram law for the
  two halves, and its sum: the outcome-bit form's projections keep `Σ_w |·|²`. Public for T14's
  norm along a protocol (entry 2026-10-01e).

## Implementation notes

* `outcomeWeight_add`, `outcomeWeight_floor` and `ampNormSq_eq_carrierNormSq` are stated here and
  proved at T11.3.1 and T11.3.2 (`docs/STEPS.md`, phase 2).
* Weights are real numbers, not probabilities: the input is sub-normalised (D3), and a probability
  is a weight divided by `ampNormSq S` where that is nonzero.
* Everything here is frame-pure: no `FTQCLib.Hilbert` module is imported.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The norm and the weight -/

/-- The squared norm of a carrier state's amplitude, `Σ_w |amp S w|²`: the support-restricted
amplitude, so words off the support count zero. -/
noncomputable def ampNormSq (S : KernelSumState n) : ℝ :=
  ∑ w : Fin n → ZMod 2, Complex.normSq (amp S w)

/-- **The weight of outcome `b`** of conditioning `S` on the Pauli `P` with its sign: the squared
norm of the conditioned state, which is not renormalised (D3). -/
noncomputable def outcomeWeight (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2) : ℝ :=
  ampNormSq (condition S P b)

/-- The weight is the squared norm of the projection `½(S + (−1)^b · P S)` of the input's
amplitude, for a co-isotropic Lagrangian. -/
theorem outcomeWeight_eq (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (b : ZMod 2) :
    outcomeWeight S P b = ∑ w : Fin n → ZMod 2, Complex.normSq (pauliProjection P b (amp S) w) := by
  unfold outcomeWeight ampNormSq
  rw [amp_condition S horth P b]

/-- A sum over the words of `Fin (N + 1)` is a sum over the last bit and the first `N`. -/
theorem sum_words_snoc {N : ℕ} (g : (Fin (N + 1) → ZMod 2) → ℝ) :
    ∑ u : Fin (N + 1) → ZMod 2, g u = ∑ c : ZMod 2, ∑ w : Fin N → ZMod 2, g (Fin.snoc w c) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun _ => ZMod 2) _ _ (fun _ => rfl)).symm

/-- A free bit appended as `∣0⟩ + ∣1⟩` doubles the weight: the scale is kept (D3). -/
theorem ampNormSq_appendFreeBit (S : KernelSumState n) :
    ampNormSq (appendFreeBit S) = 2 * ampNormSq S := by
  unfold ampNormSq
  rw [amp_appendFreeBit, sum_words_snoc]
  simp only [Fin.init_snoc, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  norm_num

/-! ## The weights -/

/-- The parallelogram law for the two halves: `|½(a + c)|² + |½(a − c)|² = (|a|² + |c|²)/2`. -/
theorem normSq_half_add_add_normSq_half_sub (a c : ℂ) :
    Complex.normSq (1 / 2 * (a + c)) + Complex.normSq (1 / 2 * (a + -1 * c))
      = (Complex.normSq a + Complex.normSq c) / 2 := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.div_re, Complex.div_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **The two weights sum to the input's norm.** For a co-isotropic Lagrangian, the weights of the
two outcomes of conditioning on a Pauli with its sign add up to `ampNormSq S`: the two projections
are orthogonal and add up to the input. Proved at T11.3.1. -/
theorem outcomeWeight_add (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n) :
    outcomeWeight S P 0 + outcomeWeight S P 1 = ampNormSq S := by
  have hval0 : (0 : ZMod 2).val = 0 := rfl
  have hval1 : (1 : ZMod 2).val = 1 := rfl
  rw [outcomeWeight_eq S horth P 0, outcomeWeight_eq S horth P 1, ← Finset.sum_add_distrib]
  simp only [pauliProjection, hval0, hval1, pow_zero, pow_one, one_mul,
    normSq_half_add_add_normSq_half_sub]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_normSq_act]
  unfold ampNormSq
  ring

/-- A sign `(−1)^b` is `1` or `−1`. -/
private theorem neg_one_pow_val_cases (b : ZMod 2) :
    (-1 : ℂ) ^ b.val = 1 ∨ (-1 : ℂ) ^ b.val = -1 := by
  rcases neg_one_pow_eq_or ℂ b.val with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- When the Pauli with its sign acts on the amplitude as a sign, the projection is the amplitude
or zero, so the weight is all of the norm or none of it. -/
private theorem weight_of_sign (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (b s : ZMod 2) (hs : pauliAct P.pauli (amp S) = fun w => (-1) ^ s.val * amp S w) :
    outcomeWeight S P b = 0 ∨ outcomeWeight S P b = ampNormSq S / 2
      ∨ outcomeWeight S P b = ampNormSq S := by
  set u : ℂ := (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ P.sign.val * (-1 : ℂ) ^ s.val) with hu
  have hproj : ∀ w, pauliProjection P b (amp S) w = (1 / 2 : ℂ) * (1 + u) * amp S w := by
    intro w
    simp only [pauliProjection, SignedPauli.act, hs, hu]
    ring
  have hu_cases : u = 1 ∨ u = -1 := by
    rcases neg_one_pow_val_cases b with h1 | h1 <;>
      rcases neg_one_pow_val_cases P.sign with h2 | h2 <;>
      rcases neg_one_pow_val_cases s with h3 | h3 <;>
      simp only [hu, h1, h2, h3] <;> norm_num
  rw [outcomeWeight_eq S horth P b]
  simp only [hproj]
  rcases hu_cases with h | h
  · right
    right
    unfold ampNormSq
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [h]
    norm_num
  · left
    rw [h]
    simp

/-- An element of `L` that anticommutes with `P` and acts on the amplitude as a sign exchanges
the two projections, so the weight of `b` is the weight of `b + 1`. -/
private theorem outcomeWeight_eq_succ (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    {g : Pauli n} (homega : omega P.pauli g = 1) (s : ZMod 2)
    (hs : pauliAct g (amp S) = fun w => (-1) ^ s.val * amp S w) (b : ZMod 2) :
    outcomeWeight S P b = outcomeWeight S P (b + 1) := by
  have hswap : ∀ w, pauliAct g (pauliProjection P b (amp S)) w
      = (-1) ^ s.val * pauliProjection P (b + 1) (amp S) w := by
    intro w
    have hanti := pauliAct_anticomm homega (amp S) w
    rw [hs, pauliAct_mul_left] at hanti
    simp only at hanti
    simp only [pauliAct, pauliProjection, SignedPauli.act] at hanti ⊢
    rw [neg_one_pow_val_add_one]
    have hsw := congrFun hs w
    simp only [pauliAct] at hsw
    linear_combination (1 / 2 : ℂ) * hsw
      + (1 / 2 : ℂ) * (-1) ^ b.val * (-1) ^ P.sign.val * hanti
  rw [outcomeWeight_eq S horth P b, outcomeWeight_eq S horth P (b + 1),
    ← sum_normSq_pauliAct g]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hswap, map_mul, map_pow, Complex.normSq_neg, Complex.normSq_one, one_pow, one_mul]

/-- **On a floor each weight is 0, ½ or 1 of the input's.** For a co-isotropic Lagrangian that
stabilizes the amplitude with signs, as on a floor (`IsFloor`), the weight of each outcome of
conditioning on a Pauli with its sign is `0`, half of `ampNormSq S`, or all of it. Proved at
T11.3.2. -/
theorem outcomeWeight_floor (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L)
    (hstab : StabilizedBy S.L (amp S)) (P : SignedPauli n) (b : ZMod 2) :
    outcomeWeight S P b = 0 ∨ outcomeWeight S P b = ampNormSq S / 2
      ∨ outcomeWeight S P b = ampNormSq S := by
  by_cases hP : P.pauli ∈ LinearMap.BilinForm.orthogonal omegaBilin S.L
  · obtain ⟨s, hs⟩ := hstab P.pauli (horth hP)
    exact weight_of_sign S horth P b s hs
  · rw [LinearMap.BilinForm.mem_orthogonal_iff] at hP
    push Not at hP
    obtain ⟨g, hg, hne⟩ := hP
    have hone : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    have homega : omega P.pauli g = 1 := by
      rw [omega_comm]
      exact hone _ hne
    obtain ⟨s, hs⟩ := hstab g hg
    have h01 : outcomeWeight S P 0 = outcomeWeight S P 1 :=
      outcomeWeight_eq_succ S horth P homega s hs 0
    have hadd := outcomeWeight_add S horth P
    right
    left
    fin_cases b
    · show outcomeWeight S P 0 = ampNormSq S / 2
      linarith
    · show outcomeWeight S P 1 = ampNormSq S / 2
      linarith

/-- The two projections at the new last bit keep `Σ_w |·|²`: the sum over `(w, b)` of
`|Π_b f (w)|²` is `Σ_w |f w|²`, the projections being orthogonal halves of `f`. -/
theorem sum_normSq_projection {N : ℕ} (P : SignedPauli N) (f : (Fin N → ZMod 2) → ℂ) :
    ∑ v : Fin (N + 1) → ZMod 2,
        Complex.normSq (pauliProjection P (v (Fin.last N)) f (Fin.init v))
      = ∑ w : Fin N → ZMod 2, Complex.normSq (f w) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => ZMod 2)
    (fun x => Complex.normSq (pauliProjection P x.1 f x.2)) _ (fun x => by
      change _ = Complex.normSq (pauliProjection P
        ((Fin.snoc x.2 x.1 : Fin (N + 1) → ZMod 2) (Fin.last N)) f
        (Fin.init (Fin.snoc x.2 x.1 : Fin (N + 1) → ZMod 2)))
      rw [Fin.snoc_last, Fin.init_snoc])]
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hval0 : (0 : ZMod 2).val = 0 := rfl
  have hval1 : (1 : ZMod 2).val = 1 := rfl
  rw [Fintype.sum_prod_type, huniv, Finset.sum_pair (by decide), ← Finset.sum_add_distrib]
  simp only [pauliProjection, hval0, hval1, pow_zero, pow_one, one_mul,
    normSq_half_add_add_normSq_half_sub]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_normSq_act]
  ring

/-! ## Agreement with `carrierNormSq` -/

/-- **On full support the two norms agree.** When the support's directions `π_X(L)` are the whole
space, every word is on the support, `amp` is `ampCore` everywhere, and `ampNormSq` is
`carrierNormSq`. Proved at T11.3.2. -/
theorem ampNormSq_eq_carrierNormSq (S : KernelSumState n)
    (hfull : Submodule.map xProj S.L = ⊤) : ampNormSq S = carrierNormSq S := by
  unfold ampNormSq carrierNormSq
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hw : ∃ p ∈ S.L, w = S.x₀ + p.X := by
    rw [mem_support_iff, hfull]
    exact Submodule.mem_top
  rw [amp_pos hw]

end FTQCLib.Frame.Walkthrough
