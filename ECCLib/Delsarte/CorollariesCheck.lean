/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.BallCert

set_option linter.style.longLine false

/-!
# Classical bounds — regression checks

The two-route cross-check, exercised twice: Singleton proved by the LP
certificate AND by direct puncturing (same concrete conclusion, two independent
routes), and Hamming proved by disjoint balls AND by the `b̂²` LP certificate.
Kernel spot-rows for the Singleton transform identity (independently computed values), and
the demonstration that the `k ≤ m` guard on the Singleton coefficients is
load-bearing (the unguarded sum is NONZERO on the distance range — the
ℕ-truncation trap, kernel-checked). Build-failing axiom sweep at the bottom.
-/

namespace ECCLib.Delsarte

/-! ## Singleton transform spot-rows (kernel) -/

theorem check_st_value :
    ∑ k ∈ Finset.range 6,
        (if k ≤ 3 then ((5 - k).choose (3 - k) : ℤ) else 0) * kraw 2 5 k 0 = 80 := by
  decide

theorem check_st_gap_d :
    ∑ k ∈ Finset.range 6,
        (if k ≤ 3 then ((5 - k).choose (3 - k) : ℤ) else 0) * kraw 2 5 k 3 = 0 := by
  decide

theorem check_st_gap_n :
    ∑ k ∈ Finset.range 6,
        (if k ≤ 3 then ((5 - k).choose (3 - k) : ℤ) else 0) * kraw 2 5 k 5 = 0 := by
  decide

/-- The `k ≤ m` guard is LOAD-BEARING: the UNGUARDED sum (ℕ-truncation turning the
tail into spurious 1s) is nonzero at `i = 4` where the certificate must vanish.
(First candidate `i = 3` was refuted by the kernel — the spurious tail happens to
cancel there; the row records a parameter where it does not.) -/
theorem check_unguarded_trap :
    ∑ k ∈ Finset.range 6, (((5 - k).choose (3 - k) : ℤ)) * kraw 2 5 k 4 ≠ 0 := by
  decide

/-! ## Singleton, two routes, one concrete conclusion: `|C| ≤ 27` at `(3, 5, 3)` -/

theorem check_singleton_lp (C : Finset (Fin 5 → ZMod 3))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ hammingDist x y) : C.card ≤ 27 := by
  have h := singleton_bound_lp (ι := Fin 5) (A := ZMod 3) (d := 3)
    (by norm_num) (by simp) C hd
  simpa using h

theorem check_singleton_direct (C : Finset (Fin 5 → ZMod 3))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ hammingDist x y) : C.card ≤ 27 := by
  have h := singleton_bound_direct (ι := Fin 5) (Q := ZMod 3) (d := 3)
    (by norm_num) (by simp) C hd
  simpa using h

/-! ## Plotkin instance: `(q, n, d) = (3, 4, 4)` — `4·|C| ≤ 12` -/

theorem check_plotkin (C : Finset (Fin 4 → ZMod 3))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 4 ≤ hammingDist x y) :
    (C.card : ℤ) * 4 ≤ 12 := by
  have h := plotkin_bound (ι := Fin 4) (A := ZMod 3) (d := 4) (by norm_num) C hd
  simpa using h

/-! ## Hamming, two routes, at `(2, 7, t = 1)`: `|C| · 8 ≤ 128` -/

theorem check_hamming_direct (C : Finset (Fin 7 → ZMod 2))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ hammingDist x y) :
    C.card * 8 ≤ 128 := by
  have h := hamming_bound_direct (ι := Fin 7) (A := ZMod 2) (t := 1) C hd
  simpa using h

theorem check_hamming_lp (C : Finset (Fin 7 → ZMod 2))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ hammingDist x y) :
    (C.card : ℤ) * 8 ≤ 128 := by
  have h := hamming_bound_lp (ι := Fin 7) (A := ZMod 2) (t := 1) (by simp) C hd
  simpa using h

/-! ## Ball-transform spot-rows -/

theorem check_bhat : bhat 2 7 1 0 = 8 := by decide
theorem check_bhat_mid : bhat 2 7 1 3 = 2 := by decide
theorem check_bhat_zero : bhat 2 7 1 4 = 0 := by decide

end ECCLib.Delsarte

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Delsarte.singleton_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.singleton_transform

/-- info: 'ECCLib.Delsarte.singleton_bound_lp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.singleton_bound_lp

/-- info: 'ECCLib.Delsarte.singleton_bound_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.singleton_bound_direct

/-- info: 'ECCLib.Delsarte.plotkin_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.plotkin_bound

/-- info: 'ECCLib.Delsarte.hamming_bound_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.hamming_bound_direct

/-- info: 'ECCLib.Delsarte.hamming_bound_lp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.hamming_bound_lp

/-- info: 'ECCLib.Delsarte.ball_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.ball_spectral

/-- info: 'ECCLib.Delsarte.wordShellSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.wordShellSum

/-- info: 'ECCLib.Delsarte.homog_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.homog_mul
