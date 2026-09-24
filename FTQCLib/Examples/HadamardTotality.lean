/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardRaise
import FTQCLib.Examples.CharSumPairing
import FTQCLib.Stabilizer.Logical
import FTQCLib.Stabilizer.Dimension

/-!
# The totality layer: the shadow dichotomy, its data, and the support half of `hRaise`

The Hadamard rules assign a constructor to every `(bit, state)` pair by the one test
`e_i ∈ π_X(L)`: `applyHFiner` when the Hadamarded basis vector is already in the X-shadow,
`hRaise` when it is not. This file builds the layer that makes the assignment total and
exclusive, and the support half of the raising gate:

* **The key lemma** (`exists_pureZ_read`): on a co-isotropic `L` whose shadow omits `e_i`,
  some pure-`Z` stabilizer reads bit `i` (`w i = 1`, `⟨0, w⟩ ∈ L`). Proved from the library's
  ω-duality (`orthogonal_orthogonal_omegaBilin`) — the local derivation of the pure-`Z` ↔
  annihilator fact, so nothing outside this cluster is imported for it.
* **Representer existence** (`exists_representer`): `u := e_i + w` represents the coordinate
  functional on the shadow with `u i = 0` — the data `hRaise` consumes, produced rather than
  assumed. Its refutation half (`notMem_shadow_of_representer`) makes the dichotomy exclusive:
  **`applyHFiner`'s guard holds iff `hRaise`'s data does not exist**
  (`representer_iff_notMem_shadow`, packaged as `hadamard_dichotomy`).
* **The support half** (`shadow_swap_eq`, `hRaise_shadow`): the X-shadow of the swapped
  Lagrangian is *exactly* the old shadow plus the raised line — equality, not containment.
  The hypothesis-free half (`shadow_swap_sup`) needs no Lagrangian at all; the membership
  half is the key lemma pushed through the swap.
* **The referee is an involution** (`walshTransform_involutive`): `H² = id` at the amplitude
  level, for the same `walshTransform` every Hadamard rule is certified against.

## Main definitions

* `bellL` — the Bell Lagrangian `⟨X₀X₁, Z₀Z₁⟩` by its constraints: the support-side example
  whose bit 0 is neither pinned nor X-supported, where only `hRaise` applies.

## Main results

* `exists_pureZ_read`, `exists_representer` — the dichotomy's data, from co-isotropy.
* `representer_iff_notMem_shadow`, `hadamard_dichotomy` — the dichotomy as a theorem.
* `shadow_swap_eq`, `hRaise_shadow` — the support half: the shadow gains exactly `e_i`.
* `branch_pair` — the output-side companion of `branch_unique`: with `e_i` in a shadow the
  two Walsh branches are on-coset together or not at all.
* `walshTransform_involutive` — the referee's `H² = id`.

## Implementation notes

* `LinearMap.BilinForm.orthogonal_sup`/`orthogonal_inf` are declared into Mathlib's namespace:
  they are not in Mathlib's `LinearAlgebra` library and are stated at full generality, so they
  are candidates for upstreaming.
* `orthogonal_omegaBilin_eq_self` restates a fact that exists only as a `private` theorem in
  `FTQCLib/Stabilizer/PauliCondition.lean` (`orthogonal_eq_self_of_isStabilizer_full`).
* `walshTransform_involutive`'s natural home is `FTQCLib/Examples/CharSumPairing.lean`, the
  referee's module; it is stated here, next to its uses.
* The support object is `Submodule.map xProj` — the form `branch_unique` already uses; the
  `supportSpace`/`xProjₗ` duplicate (`FTQCLib/Hierarchy/FloorEquivalence.lean`) is not
  used in this file.
-/

namespace LinearMap.BilinForm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The orthogonal complement of a sup is the inf of the complements — no hypotheses. -/
theorem orthogonal_sup (B : LinearMap.BilinForm R M) (U V : Submodule R M) :
    B.orthogonal (U ⊔ V) = B.orthogonal U ⊓ B.orthogonal V := by
  ext x
  rw [Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
      fun v hv => h v (Submodule.mem_sup_right hv)⟩
  · rintro ⟨hU, hV⟩ y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    have hu0 : B u x = 0 := hU u hu
    have hv0 : B v x = 0 := hV v hv
    change B (u + v) x = 0
    rw [map_add, LinearMap.add_apply, hu0, hv0, add_zero]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The orthogonal complement of an inf is the sup of the complements — the double-orthogonal
identity pushed through `orthogonal_sup`. Needs non-degeneracy, reflexivity, and finite
dimension, exactly as `orthogonal_orthogonal` does. -/
theorem orthogonal_inf {B : LinearMap.BilinForm K V}
    (hB : B.Nondegenerate) (hr : B.IsRefl) (U W : Submodule K V) :
    B.orthogonal (U ⊓ W) = B.orthogonal U ⊔ B.orthogonal W := by
  have h1 : U ⊓ W = B.orthogonal (B.orthogonal U ⊔ B.orthogonal W) := by
    rw [orthogonal_sup, orthogonal_orthogonal hB hr, orthogonal_orthogonal hB hr]
  rw [h1, orthogonal_orthogonal hB hr]

end LinearMap.BilinForm

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The `𝔽₂` pairing against basis vectors and pure-type Paulis -/

/-- `dotF2` is additive on the left. -/
theorem dotF2_add_left (u u' v : Fin n → ZMod 2) :
    dotF2 (u + u') v = dotF2 u v + dotF2 u' v := by
  unfold dotF2
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, add_mul]

/-- Dotting against a basis vector on the right picks the coordinate. -/
theorem dotF2_single (u : Fin n → ZMod 2) (i : Fin n) : dotF2 u (Pi.single i 1) = u i := by
  unfold dotF2
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Dotting against a basis vector on the left picks the coordinate. -/
theorem dotF2_single_left (v : Fin n → ZMod 2) (i : Fin n) :
    dotF2 (Pi.single i 1) v = v i := by
  unfold dotF2
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- `ω` of a pure-`Z` Pauli against anything is the `𝔽₂` pairing with the X-part. -/
theorem omega_pureZ (w : Fin n → ZMod 2) (q : Pauli n) :
    omega (⟨0, w⟩ : Pauli n) q = dotF2 w q.X := by
  simp [omega, dotF2]

/-- `ω` of a pure-`X` Pauli against anything is the `𝔽₂` pairing with the Z-part. -/
theorem omega_pureX (v : Fin n → ZMod 2) (q : Pauli n) :
    omega (⟨v, 0⟩ : Pauli n) q = dotF2 v q.Z := by
  simp [omega, dotF2]

/-! ## The ω-orthogonal facts the key lemma consumes -/

/-- The Z-Lagrangian is its own ω-orthogonal complement. -/
theorem orthogonal_omegaBilin_Lz :
    LinearMap.BilinForm.orthogonal omegaBilin (Lz (n := n)) = Lz := by
  ext q
  constructor
  · intro hq
    rw [mem_Lz]
    funext i
    have h := hq ⟨0, Pi.single i 1⟩ (mem_Lz.mpr rfl)
    change omega (⟨0, Pi.single i 1⟩ : Pauli n) q = 0 at h
    rw [omega_pureZ, dotF2_single_left] at h
    exact h
  · intro hq p hp
    change omega p q = 0
    have hpX : p.X = 0 := mem_Lz.mp hp
    have hqX : q.X = 0 := mem_Lz.mp hq
    simp [omega, hpX, hqX]

/-- A Lagrangian (isotropic, full rank) is its own ω-orthogonal complement. Public
restatement of the `private` `orthogonal_eq_self_of_isStabilizer_full`
(`FTQCLib/Stabilizer/PauliCondition.lean`). -/
theorem orthogonal_omegaBilin_eq_self {L : Submodule (ZMod 2) (Pauli n)}
    (hS : IsStabilizer L) (hRank : Module.finrank (ZMod 2) L = n) :
    LinearMap.BilinForm.orthogonal omegaBilin L = L := by
  have h_le : L ≤ LinearMap.BilinForm.orthogonal omegaBilin L := by
    intro s hs q hq
    change omega q s = 0
    rw [omega_comm]
    exact hS s hs q hq
  have h_rank :
      Module.finrank (ZMod 2) L
        = Module.finrank (ZMod 2) (LinearMap.BilinForm.orthogonal omegaBilin L) := by
    rw [LinearMap.BilinForm.finrank_orthogonal omegaBilin_nondegenerate, finrank_Pauli, hRank]
    omega
  exact (Submodule.eq_of_le_of_finrank_eq h_le h_rank).symm

/-- The co-isotropy the totality layer runs on, at the Lagrangian instance. Every theorem
below that takes `horth` is stated at co-isotropy — the weakest hypothesis its proof uses —
and this is the discharge for Lagrangian carrier states. -/
theorem orthogonal_le_of_lagrangian {L : Submodule (ZMod 2) (Pauli n)}
    (hS : IsStabilizer L) (hRank : Module.finrank (ZMod 2) L = n) :
    LinearMap.BilinForm.orthogonal omegaBilin L ≤ L :=
  (orthogonal_omegaBilin_eq_self hS hRank).le

/-! ## The key lemma: off-shadow bits are read by a pure-`Z` stabilizer -/

/-- **The key lemma.** On a co-isotropic `L`, a bit whose basis vector is outside the X-shadow
is read by some pure-`Z` stabilizer: `∃ w, w i = 1 ∧ ⟨0, w⟩ ∈ L`. If no pure-`Z` member of
`L` read the bit, `X_i` would be ω-orthogonal to `L ⊓ Lz`, hence (duality) in `L ⊔ Lz` — and
its `L`-component would put `e_i` in the shadow. Both the pinned mode (`w = e_i`) and the
correlated mode (`w` reading several bits) are instances; this is the fact that keeps `hRaise`
from ever being stuck. -/
theorem exists_pureZ_read {L : Submodule (ZMod 2) (Pauli n)}
    (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L) {i : Fin n}
    (hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj L) :
    ∃ w : Fin n → ZMod 2, w i = 1 ∧ (⟨0, w⟩ : Pauli n) ∈ L := by
  by_contra hcon
  push Not at hcon
  have hxi : (⟨Pi.single i 1, 0⟩ : Pauli n)
      ∈ LinearMap.BilinForm.orthogonal omegaBilin (L ⊓ Lz) := by
    intro p hp
    obtain ⟨hpL, hpz⟩ := Submodule.mem_inf.mp hp
    have hpX : p.X = 0 := mem_Lz.mp hpz
    change omega p (⟨Pi.single i 1, 0⟩ : Pauli n) = 0
    rw [omega_comm, omega_pureX, dotF2_single_left]
    have hmem : (⟨0, p.Z⟩ : Pauli n) ∈ L := by
      have hp0 : p = (⟨0, p.Z⟩ : Pauli n) := Pauli.ext hpX rfl
      rw [← hp0]
      exact hpL
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (p.Z i) with h0 | h1
    · exact h0
    · exact absurd hmem (hcon p.Z h1)
  rw [LinearMap.BilinForm.orthogonal_inf omegaBilin_nondegenerate omegaBilin_isRefl,
    orthogonal_omegaBilin_Lz] at hxi
  have hxi' : (⟨Pi.single i 1, 0⟩ : Pauli n) ∈ L ⊔ Lz :=
    sup_le_sup_right horth Lz hxi
  obtain ⟨l, hl, z, hz, hsum⟩ := Submodule.mem_sup.mp hxi'
  refine hi (Submodule.mem_map.mpr ⟨l, hl, ?_⟩)
  have hzX : z.X = 0 := mem_Lz.mp hz
  have hX : l.X + z.X = Pi.single i 1 := by
    have h := congrArg Pauli.X hsum
    rwa [X_add] at h
  rw [xProj_apply]
  rwa [hzX, add_zero] at hX

/-! ## Representer existence — the data `hRaise` consumes, produced -/

/-- **Representer existence.** On a Lagrangian whose shadow omits `e_i`, the coordinate
functional on the shadow is represented by `u := e_i + w` with `u i = 0`, where `w` is the
key lemma's pure-`Z` reader: `dotF2 u v = v i` for every shadow vector `v`. Isotropy makes
`w` ⊥ the shadow; adding `e_i` shifts the represented functional to the coordinate and kills
the `i`-entry at once. -/
theorem exists_representer {L : Submodule (ZMod 2) (Pauli n)} (hS : IsStabilizer L)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L) {i : Fin n}
    (hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj L) :
    ∃ u : Fin n → ZMod 2, u i = 0 ∧ ∀ v ∈ Submodule.map xProj L, dotF2 u v = v i := by
  obtain ⟨w, hwi, hwL⟩ := exists_pureZ_read horth hi
  refine ⟨Pi.single i 1 + w, ?_, ?_⟩
  · rw [Pi.add_apply, Pi.single_eq_same, hwi]
    decide
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
    have hw0 : dotF2 w p.X = 0 := by
      have h := hS ⟨0, w⟩ hwL p hp
      rwa [omega_pureZ] at h
    rw [xProj_apply, dotF2_add_left, dotF2_single_left, hw0, add_zero]

/-! ## The dichotomy as a theorem -/

/-- The refutation half: a representer with `u i = 0` dotted against `e_i` itself gives
`0 = 1` — so once `e_i` is in the shadow, `hRaise`'s data cannot exist. Unconditional. -/
theorem notMem_shadow_of_representer {L : Submodule (ZMod 2) (Pauli n)} {i : Fin n}
    {u : Fin n → ZMod 2} (hui : u i = 0)
    (hrep : ∀ v ∈ Submodule.map xProj L, dotF2 u v = v i) :
    (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj L := by
  intro hmem
  have h := hrep _ hmem
  rw [dotF2_single, hui, Pi.single_eq_same] at h
  exact absurd h (by decide)

/-- **The dichotomy.** On a Lagrangian, `hRaise`'s data (a representer with `u i = 0`) exists
iff `applyHFiner`'s guard (`e_i` in the shadow) fails: the two constructors' applicability
conditions are complementary, through the data itself. -/
theorem representer_iff_notMem_shadow {L : Submodule (ZMod 2) (Pauli n)}
    (hS : IsStabilizer L) (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L)
    (i : Fin n) :
    (∃ u : Fin n → ZMod 2, u i = 0 ∧ ∀ v ∈ Submodule.map xProj L, dotF2 u v = v i)
      ↔ (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj L := by
  constructor
  · rintro ⟨u, hui, hrep⟩
    exact notMem_shadow_of_representer hui hrep
  · intro hi
    exact exists_representer hS horth hi

/-- The dichotomy, packaged as an exclusive-or: every bit of every Lagrangian state is
assigned exactly one constructor, and the assigned constructor has its data. -/
theorem hadamard_dichotomy {L : Submodule (ZMod 2) (Pauli n)}
    (hS : IsStabilizer L) (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L)
    (i : Fin n) :
    Xor' ((Pi.single i 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L)
      (∃ u : Fin n → ZMod 2, u i = 0 ∧ ∀ v ∈ Submodule.map xProj L, dotF2 u v = v i) := by
  by_cases h : (Pi.single i 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L
  · exact Or.inl ⟨h, fun hu => (representer_iff_notMem_shadow hS horth i).mp hu h⟩
  · exact Or.inr ⟨exists_representer hS horth h, h⟩

/-- Pinned bits sit on the `hRaise` side of the dichotomy: if no stabilizer carries `X` at
`i`, the shadow omits `e_i`. No Lagrangian input. -/
theorem notMem_shadow_of_pinned {L : Submodule (ZMod 2) (Pauli n)} {i : Fin n}
    (hpin : ∀ p ∈ L, p.X i = 0) :
    (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj L := by
  intro hmem
  obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp hmem
  rw [xProj_apply] at hpX
  have h0 : p.X i = 0 := hpin p hp
  rw [hpX, Pi.single_eq_same] at h0
  exact absurd h0 (by decide)

/-- Under pinning, `u = 0` is a representer — the pinned mode is `hRaise`'s `u = 0` slot,
which is why `applyHPinned` never needed a linear form. No Lagrangian input. -/
theorem pinned_representer_zero {L : Submodule (ZMod 2) (Pauli n)} {i : Fin n}
    (hpin : ∀ p ∈ L, p.X i = 0) :
    ∀ v ∈ Submodule.map xProj L, dotF2 0 v = v i := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
  rw [xProj_apply, hpin p hp]
  simp [dotF2]

/-- The dichotomy's test is decidable whenever membership in `L` is: the shadow test
transports decidability through the finite search over `Pauli n`. -/
instance decidableMemShadow (L : Submodule (ZMod 2) (Pauli n)) [DecidablePred (· ∈ L)] :
    DecidablePred (· ∈ Submodule.map xProj L) := fun v =>
  decidable_of_iff (∃ p : Pauli n, p ∈ L ∧ xProj p = v) Submodule.mem_map.symm

/-! ## The support half: the shadow gains exactly the raised line -/

/-- The X-component of the one-bit swap, as a rank-one correction: off `i` unchanged, at `i`
the X- and Z-entries exchange. -/
theorem xProj_pauliSwapOn_singleton (i : Fin n) (p : Pauli n) :
    xProj (pauliSwapOn {i} p)
      = xProj p + (p.X i + p.Z i) • (Pi.single i 1 : Fin n → ZMod 2) := by
  funext j
  change (pauliSwapOn {i} p).X j
    = p.X j + (p.X i + p.Z i) * (Pi.single i 1 : Fin n → ZMod 2) j
  by_cases hj : j = i
  · subst hj
    rw [pauliSwapOn_X, if_pos (Finset.mem_singleton_self j), Pi.single_eq_same, mul_one]
    exact (show ∀ a b : ZMod 2, b = a + (a + b) by decide) (p.X j) (p.Z j)
  · rw [pauliSwapOn_X, if_neg (by simp [hj]), Pi.single_eq_of_ne hj, mul_zero, add_zero]

/-- **The hypothesis-free half.** Up to the raised line, the swap moves nothing: adjoining
`e_i` to either shadow gives the same subspace, for every `L`. The membership of `e_i`
itself is the only content the Lagrangian buys (`single_mem_shadow_swap`). -/
theorem shadow_swap_sup (i : Fin n) (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map xProj (Submodule.map (pauliSwapOn {i}) L)
        ⊔ Submodule.span (ZMod 2) {(Pi.single i 1 : Fin n → ZMod 2)}
      = Submodule.map xProj L
          ⊔ Submodule.span (ZMod 2) {(Pi.single i 1 : Fin n → ZMod 2)} := by
  have key : ∀ M : Submodule (ZMod 2) (Pauli n),
      Submodule.map xProj (Submodule.map (pauliSwapOn {i}) M)
        ≤ Submodule.map xProj M
            ⊔ Submodule.span (ZMod 2) {(Pi.single i 1 : Fin n → ZMod 2)} := by
    intro M v hv
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
    rw [xProj_pauliSwapOn_singleton]
    have hsingle : (Pi.single i 1 : Fin n → ZMod 2)
        ∈ Submodule.map xProj M
            ⊔ Submodule.span (ZMod 2) {(Pi.single i 1 : Fin n → ZMod 2)} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_map.mpr ⟨p, hp, rfl⟩))
      (Submodule.smul_mem _ _ hsingle)
  refine le_antisymm (sup_le (key L) le_sup_right) (sup_le ?_ le_sup_right)
  have h := key (Submodule.map (pauliSwapOn {i}) L)
  rwa [map_pauliSwapOn_map] at h

/-- The raised bit joins the shadow: the key lemma's pure-`Z` reader, pushed through the
swap, is a stabilizer of the image whose X-part is exactly `e_i`. -/
theorem single_mem_shadow_swap {L : Submodule (ZMod 2) (Pauli n)}
    (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L) {i : Fin n}
    (hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj L) :
    (Pi.single i 1 : Fin n → ZMod 2)
      ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {i}) L) := by
  obtain ⟨w, hwi, hwL⟩ := exists_pureZ_read horth hi
  refine Submodule.mem_map.mpr
    ⟨pauliSwapOn {i} ⟨0, w⟩, Submodule.mem_map_of_mem hwL, ?_⟩
  rw [xProj_apply]
  funext j
  by_cases hj : j = i
  · subst hj
    rw [pauliSwapOn_X, if_pos (Finset.mem_singleton_self j), Pi.single_eq_same]
    exact hwi
  · rw [pauliSwapOn_X, if_neg (by simp [hj]), Pi.single_eq_of_ne hj]
    rfl

/-- **The support half.** On a co-isotropic `L` whose shadow omits `e_i`, the
X-shadow of the swapped subspace is *exactly* the old shadow plus the raised line — equality
of shadows, the stronger of the two possible forms (the other being containment). With `hRaise_L`
(`rfl`) this is the statement that the raising gate's support component does what its name says. -/
theorem shadow_swap_eq {L : Submodule (ZMod 2) (Pauli n)}
    (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L) {i : Fin n}
    (hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj L) :
    Submodule.map xProj (Submodule.map (pauliSwapOn {i}) L)
      = Submodule.map xProj L
          ⊔ Submodule.span (ZMod 2) {(Pi.single i 1 : Fin n → ZMod 2)} := by
  have hspan : Submodule.span (ZMod 2) {(Pi.single i 1 : Fin n → ZMod 2)}
      ≤ Submodule.map xProj (Submodule.map (pauliSwapOn {i}) L) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact single_mem_shadow_swap horth hi
  rw [← shadow_swap_sup i L]
  exact (sup_eq_left.mpr hspan).symm

/-- The gate corollary: `hRaise`'s output shadow is the input shadow plus the raised line.
`u` is arbitrary — the support half never reads the representer. -/
theorem hRaise_shadow (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L)
    (hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj S.L) :
    Submodule.map xProj (hRaise i u S).L
      = Submodule.map xProj S.L
          ⊔ Submodule.span (ZMod 2) {(Pi.single i 1 : Fin n → ZMod 2)} := by
  rw [hRaise_L]
  exact shadow_swap_eq horth hi

/-- The output-side companion of `branch_unique`: once `e_i` is in a shadow (as it is in
`hRaise`'s output, by `hRaise_shadow`), the two Walsh branches of any word are on the coset
together or not at all — the raised bit is genuinely free. -/
theorem branch_pair {M : Submodule (ZMod 2) (Fin n → ZMod 2)} {i : Fin n}
    (hmem : (Pi.single i 1 : Fin n → ZMod 2) ∈ M) (x₀ w : Fin n → ZMod 2) :
    Function.update w i 0 - x₀ ∈ M ↔ Function.update w i 1 - x₀ ∈ M := by
  constructor
  · intro h0
    have h := M.sub_mem h0 hmem
    rwa [show Function.update w i 0 - x₀ - Pi.single i 1
        = Function.update w i 1 - x₀ from by rw [← update_sub_update w i]; abel] at h
  · intro h1
    have h := M.add_mem h1 hmem
    rwa [show Function.update w i 1 - x₀ + Pi.single i 1
        = Function.update w i 0 - x₀ from by rw [← update_sub_update w i]; abel] at h

/-! ## The referee is an involution -/

/-- **`H² = id` at the amplitude level.** The single-bit Walsh transform — the referee every
Hadamard rule is certified against — is an involution: the pair of branch values is
resolved by the sign of the read bit. With `walsh_normSq_isometry` this is the referee's own
unitarity-and-order-two, no carrier and no Hilbert space involved. -/
theorem walshTransform_involutive (k : Fin n) :
    Function.Involutive (walshTransform (n := n) k) := by
  intro f
  funext w
  have h2 : (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs0 : signOf (0 : ZMod 2) = 1 := by unfold signOf; rw [if_pos rfl]
  have hs1 : signOf (1 : ZMod 2) = -1 := by unfold signOf; rw [if_neg (by decide)]
  simp only [walshTransform, Function.update_idem, Function.update_self, hs0, hs1]
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (w k) with hk | hk
  · have hw : Function.update w k 0 = w := by rw [← hk]; exact Function.update_eq_self k w
    rw [hk, hs0, hw]
    linear_combination (2 * f w) * h2
  · have hw : Function.update w k 1 = w := by rw [← hk]; exact Function.update_eq_self k w
    rw [hk, hs1, hw]
    linear_combination (2 * f w) * h2

/-! ## The Bell state — the support side

`bellIn` (`HadamardRaise.lean`) fixed `L` to the placeholder `⊤` because the `Q`-component
of `hRaise` reads no support data. This block supplies the support side: the Bell Lagrangian
itself, presented by its constraints so that membership is definitional, with bit `0`
neither pinned (`X₀X₁` reads it) nor X-supported (`e₀ ∉ ⟨(1,1)⟩`) — the case in which only
`hRaise` applies, with the representer that `hRaise_bell_exponent` chooses by hand now
*derived*. -/

/-- The Bell Lagrangian `⟨X₀X₁, Z₀Z₁⟩`, by its constraints: equal X-entries, equal
Z-entries. -/
def bellL : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.X 0 = p.X 1 ∧ p.Z 0 = p.Z 1}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := fun hp hq => ⟨by simp [hp.1, hq.1], by simp [hp.2, hq.2]⟩
  smul_mem' := fun c _ hp => ⟨by simp [hp.1], by simp [hp.2]⟩

@[simp] theorem mem_bellL {p : Pauli 2} : p ∈ bellL ↔ p.X 0 = p.X 1 ∧ p.Z 0 = p.Z 1 :=
  Iff.rfl

/-- The Bell Lagrangian is isotropic. -/
theorem bellL_isStabilizer : IsStabilizer bellL := by
  intro p hp q hq
  show omega p q = 0
  unfold omega
  rw [Fin.sum_univ_two, Fin.sum_univ_two, hp.1, hp.2, hq.1, hq.2]
  exact (show ∀ a b c d : ZMod 2, a * b + a * b + (c * d + c * d) = 0 by decide) _ _ _ _

/-- The Bell Lagrangian is co-isotropic: anything ω-orthogonal to it already satisfies its
two constraints. Discharged directly against the generators, no rank computation. -/
theorem bellL_coisotropic : LinearMap.BilinForm.orthogonal omegaBilin bellL ≤ bellL := by
  intro q hq
  have ha := hq ⟨![1, 1], 0⟩ ⟨by decide, rfl⟩
  have hb := hq ⟨0, ![1, 1]⟩ ⟨rfl, by decide⟩
  change omega (⟨![1, 1], 0⟩ : Pauli 2) q = 0 at ha
  change omega (⟨0, ![1, 1]⟩ : Pauli 2) q = 0 at hb
  rw [omega_pureX] at ha
  rw [omega_pureZ] at hb
  unfold dotF2 at ha hb
  rw [Fin.sum_univ_two] at ha hb
  have key : ∀ a b : ZMod 2, 1 * a + 1 * b = 0 → a = b := by decide
  exact ⟨key _ _ hb, key _ _ ha⟩

/-- Bit `0` of the Bell Lagrangian is not X-supported: its shadow is `⟨(1,1)⟩ ∌ e₀`. -/
theorem bellL_not_mem_shadow :
    (Pi.single 0 1 : Fin 2 → ZMod 2) ∉ Submodule.map xProj bellL := by
  intro hmem
  obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp hmem
  rw [xProj_apply] at hpX
  have h0 : p.X 0 = 1 := by rw [hpX, Pi.single_eq_same]
  have h1 : p.X 1 = 0 := by
    rw [hpX, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  have h := hp.1
  rw [h0, h1] at h
  exact absurd h (by decide)

/-- The vector `u = ![0,1]` used in `hRaise_bell_exponent` is *the* representer for the Bell
shadow at bit `0`: `u 0 = 0` and `u ⬝ v = v 0` on the shadow. The representer chosen by hand
there is derived by the support layer. -/
theorem bellL_representer :
    (![0, 1] : Fin 2 → ZMod 2) 0 = 0
      ∧ ∀ v ∈ Submodule.map xProj bellL, dotF2 ![0, 1] v = v 0 := by
  refine ⟨by decide, ?_⟩
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
  rw [xProj_apply]
  unfold dotF2
  rw [Fin.sum_univ_two]
  change (0 : ZMod 2) * p.X 0 + 1 * p.X 1 = p.X 0
  rw [zero_mul, one_mul, zero_add, ← hp.1]

/-- The key lemma's pure-`Z` reader at Bell is `Z₀Z₁` itself: `w = ![1,1]`, `w 0 = 1`,
`⟨0, w⟩ ∈ bellL`. The representer above is `e₀ + w`, exactly the general construction. -/
theorem bellL_pureZ_read :
    (![1, 1] : Fin 2 → ZMod 2) 0 = 1 ∧ (⟨0, ![1, 1]⟩ : Pauli 2) ∈ bellL :=
  ⟨by decide, ⟨rfl, by decide⟩⟩

end FTQCLib.Frame.Walkthrough
