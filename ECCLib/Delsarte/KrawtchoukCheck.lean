/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.Krawtchouk

set_option linter.style.longLine false

/-!
# Krawtchouk layer — regression checks

Contents: the junk-box `decide` tripwires (definition vs. closed forms, catching
normalization drift), the permanent off-domain guard for the degree-one closed form,
independently computed regression anchors, and a build-failing axiom sweep via
`#guard_msgs`.

The definition itself is checked against the literature: summand,
generating-function factor placement, `K₀`, `K₁`, and the orthogonality relation all
match Cohn–Zhao arXiv:1212.1913 eqs. (1)–(2) (generating function per
MacWilliams–Sloane p. 151) and McKinley 2003 §3.5.
-/

namespace ECCLib.Delsarte

/-- Junk-box tripwire: `K₀ ≡ 1` agrees with the definition over the whole box,
including the ℕ-truncation junk region `i > n`. -/
theorem check_kraw_zero_box :
    ∀ q ∈ Finset.range 6, ∀ n ∈ Finset.range 9, ∀ i ∈ Finset.range 12,
      kraw q n 0 i = 1 := by decide

/-- Junk-box tripwire: `K_k(0) = C(n,k)(q−1)^k`, unconditional over the box. -/
theorem check_kraw_at_zero_box :
    ∀ q ∈ Finset.range 6, ∀ n ∈ Finset.range 9, ∀ k ∈ Finset.range 9,
      kraw q n k 0 = (n.choose k : ℤ) * ((q : ℤ) - 1) ^ k := by decide

/-- Junk-box tripwire: the `K₁` closed form on its domain `i ≤ n`. -/
theorem check_kraw_one_box :
    ∀ q ∈ Finset.range 6, ∀ n ∈ Finset.range 9, ∀ i ∈ Finset.range 9,
      i ≤ n → kraw q n 1 i = ((q : ℤ) - 1) * n - q * i := by decide

/-- Junk-box tripwire: the `K₂` closed form on its domain. -/
theorem check_kraw_two_box :
    ∀ q ∈ Finset.range 6, ∀ n ∈ Finset.range 9, ∀ i ∈ Finset.range 9,
      i ≤ n → kraw q n 2 i
        = ((q : ℤ) - 1) ^ 2 * ((n - i).choose 2 : ℤ)
          - ((q : ℤ) - 1) * i * ((n : ℤ) - i) + (i.choose 2 : ℤ) := by decide

/-- PERMANENT GUARD: the `K₁` closed form is FALSE off-domain —
`kraw 2 3 1 5 = −5`, the closed form gives `−7`. Keeps `kraw_one`'s hypothesis from
being "simplified" away. -/
theorem check_kraw_one_offDomain_guard :
    kraw 2 3 1 5 ≠ ((2 : ℤ) - 1) * 3 - 2 * 5 := by decide

/-! Regression anchors — computed independently by exact-arithmetic scripts,
kernel-confirmed here. -/

theorem check_anchor_binary_n7 : kraw 2 7 2 0 = 21 := by decide
theorem check_anchor_ternary : kraw 3 4 2 0 = 24 := by decide
theorem check_anchor_n12 : kraw 2 12 2 6 = -6 := by decide
theorem check_anchor_golay_a : kraw 2 23 5 7 = -273 := by decide
theorem check_anchor_golay_b : kraw 2 23 11 7 = -910 := by decide
theorem check_anchor_golay_c : kraw 2 23 2 0 = 253 := by decide

/-- The coefficient hinge exercised at a concrete point. -/
theorem check_hinge : kraw 3 5 2 1 = (krawPoly 3 5 1).coeff 2 := kraw_eq_coeff 3 5 2 1

end ECCLib.Delsarte

/-! ## Axiom sweep (build-failing: `#guard_msgs` errors on any drift) -/

/-- info: 'ECCLib.Delsarte.kraw_eq_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.kraw_eq_coeff

/-- info: 'ECCLib.Delsarte.coeff_one_add_C_mul_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.coeff_one_add_C_mul_X_pow

/-- info: 'ECCLib.Delsarte.kraw_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.kraw_at_zero

/-- info: 'ECCLib.Delsarte.kraw_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.kraw_one

/-- info: 'ECCLib.Delsarte.kraw_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.kraw_two
