/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Hamming
import ECCLib.Scheme.DelsarteBridge
import ECCLib.Scheme.DualAction
import ECCLib.Scheme.DualTransitive

/-!
# The dual side of the Hamming instance

The dual weight-`k` shells are STABLE under the contragredient
action of the monomial group. This needs no transitivity — the dual of a monomial map is
again monomial, and that is proved here by computing the coordinate restrictions of a
transformed character on `Pi.single` vectors:

* `coordChar ((scaleAut g) • ξ) i = g i • coordChar ξ i` — a coordinatewise scaling of the
  character tuple (`coordChar_scaleAut_smul`);
* `coordChar ((permAut σ) • ξ) i = coordChar ξ (σ i)` — a reindexing (`coordChar_permAut_smul`).

Both preserve the tuple's Hamming weight, so `dualWeight ξ := hammingNorm (coordChar ξ)` is
a monomial-group invariant (`dualWeight_monomial_smul`), and since `ξ ∈ shellSet ι A k ↔
dualWeight ξ = k` (`mem_shellSet_iff`) the shells are stable (`shellSet_stable`).

Stability is what a scheme consumer needs in order to know that `qEnt (shellSet …)` is a
class function, which is the fact `Scheme/Spectrum.lean`'s `qEnt_smul` wants at the Hamming
instance. It does not by itself say that a shell is a single orbit.

The **strong form** does, and is proved below (`orb_eq_shellSet`): given transitivity on the
nonzero alphabet, the dual weight shells are exactly the dual orbits. It needs dual-side
transitivity, which `Scheme/DualTransitive.lean` supplies by counting, and then the orbit
classification at the dual alphabet transported along `coordChar` — for which the two
coordinate identities above are precisely the transport.

## Main definitions

* `dualWeight` — the Hamming weight of a character's tuple of coordinate restrictions.

## Main results

* `dualWeight_monomial_smul` — the dual weight is a monomial-group invariant.
* `mem_shellSet_iff` — membership in the dual shell is having that dual weight.
* `shellSet_stable` — the dual shells are stable, with no transitivity hypothesis.
* `dualWeight_eq_iff_monomial` / `orb_eq_shellSet` — with transitivity, the dual shells are
  exactly the dual orbits.

## Implementation notes

`orb_eq_shellSet` carries `[Finite G]`, which the weak form does not: it routes through
`transOnNonzero_dual`, and that is a Burnside argument summing over the group.

The action is the scoped contragredient of `Scheme/Orbits.lean` at `H := AddAut (ι → A)`
(Mathlib's `AddAut.applyDistribMulAction` supplies the `DistribMulAction`).
-/

namespace ECCLib.Scheme

open Finset
open scoped BigOperators

section DualWeight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
variable {G : Type*} [Group G] [DistribMulAction G A]

/-- The dual weight of a character of the word space: the Hamming weight of its tuple of
coordinate restrictions. -/
noncomputable def dualWeight (ξ : AddChar (ι → A) ℂ) : ℕ := hammingNorm (coordChar ξ)

omit [Fintype ι] [Fintype A] [DecidableEq A] in
/-- Scaling a `Pi.single` vector coordinatewise scales its single entry. -/
theorem smul_pi_single (c : ι → G) (i : ι) (a : A) :
    (fun j => c j • (Pi.single i a : ι → A) j) = Pi.single i (c i • a) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] in
/-- `scaleAut` turns pointwise multiplication into composition. -/
theorem scaleAut_mul (g h : ι → G) :
    scaleAut (A := A) g * scaleAut (A := A) h = scaleAut (A := A) (g * h) := by
  ext v i
  change g i • (h i • v i) = (g i * h i) • v i
  rw [mul_smul]

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] in
@[simp] theorem scaleAut_one : scaleAut (A := A) (1 : ι → G) = 1 := by
  ext v i
  change (1 : G) • v i = v i
  rw [one_smul]

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] in
theorem scaleAut_inv (g : ι → G) :
    (scaleAut (A := A) g)⁻¹ = scaleAut (A := A) (fun i => (g i)⁻¹) := by
  have hmul : scaleAut (A := A) (fun i => (g i)⁻¹) * scaleAut (A := A) g = 1 := by
    rw [scaleAut_mul,
      show (fun i => (g i)⁻¹) * g = 1 from funext fun i => inv_mul_cancel (g i), scaleAut_one]
  exact (eq_inv_of_mul_eq_one_left hmul).symm

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] in
/-- `permAut` is an anti-homomorphism of the permutation group. -/
theorem permAut_mul (σ τ : Equiv.Perm ι) :
    permAut (A := A) σ * permAut (A := A) τ = permAut (A := A) (τ * σ) := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] in
@[simp] theorem permAut_one : permAut (A := A) (1 : Equiv.Perm ι) = 1 := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] in
theorem permAut_inv (σ : Equiv.Perm ι) :
    (permAut (A := A) σ)⁻¹ = permAut (A := A) σ⁻¹ := by
  have hmul : permAut (A := A) σ⁻¹ * permAut (A := A) σ = 1 := by
    rw [permAut_mul, mul_inv_cancel, permAut_one]
  exact (eq_inv_of_mul_eq_one_left hmul).symm

omit [Fintype ι] [Fintype A] [DecidableEq A] in
/-- Permuting a `Pi.single` vector moves its support. -/
theorem permAut_inv_pi_single (σ : Equiv.Perm ι) (i : ι) (a : A) :
    (permAut (A := A) σ)⁻¹ (Pi.single i a) = Pi.single (σ i) a := by
  rw [permAut_inv]
  funext j
  rw [permAut_apply]
  by_cases hj : j = σ i
  · subst hj
    rw [show σ⁻¹ (σ i) = i from by simp, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne]
    intro hcon
    apply hj
    have hb := congrArg (fun x => σ x) hcon
    simpa using hb

/-! ## The coordinate restrictions of a transformed character -/

omit [Fintype ι] [Fintype A] [DecidableEq A] in
/-- The dual of a coordinatewise scaling is a coordinatewise scaling of the character
tuple. -/
theorem coordChar_scaleAut_smul (g : ι → G) (ξ : AddChar (ι → A) ℂ) :
    coordChar ((scaleAut (A := A) g) • ξ) = fun i => g i • coordChar ξ i := by
  funext i
  ext a
  rw [coordChar_apply, contra_smul_apply, contra_smul_apply, coordChar_apply]
  change ξ ((scaleAut (A := A) g)⁻¹ (Pi.single i a)) = ξ (Pi.single i ((g i)⁻¹ • a))
  rw [scaleAut_inv]
  congr 1
  exact smul_pi_single (fun j => (g j)⁻¹) i a

omit [Fintype ι] [Fintype A] [DecidableEq A] in
/-- The dual of a coordinate permutation is a reindexing of the character tuple. -/
theorem coordChar_permAut_smul (σ : Equiv.Perm ι) (ξ : AddChar (ι → A) ℂ) :
    coordChar ((permAut (A := A) σ) • ξ) = fun i => coordChar ξ (σ i) := by
  funext i
  ext a
  rw [coordChar_apply, contra_smul_apply, coordChar_apply]
  change ξ ((permAut (A := A) σ)⁻¹ (Pi.single i a)) = ξ (Pi.single (σ i) a)
  rw [permAut_inv_pi_single]

/-! ## Invariance of the dual weight -/

omit [Fintype A] [DecidableEq A] in
/-- A coordinatewise scaling preserves the dual weight. -/
theorem dualWeight_scaleAut_smul (g : ι → G) (ξ : AddChar (ι → A) ℂ) :
    dualWeight ((scaleAut (A := A) g) • ξ) = dualWeight ξ := by
  unfold dualWeight
  rw [coordChar_scaleAut_smul]
  unfold hammingNorm
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp only [ne_eq, contra_smul_eq_zero_iff]

omit [Fintype A] [DecidableEq A] in
/-- A coordinate permutation preserves the dual weight. -/
theorem dualWeight_permAut_smul (σ : Equiv.Perm ι) (ξ : AddChar (ι → A) ℂ) :
    dualWeight ((permAut (A := A) σ) • ξ) = dualWeight ξ := by
  unfold dualWeight
  rw [coordChar_permAut_smul]
  unfold hammingNorm
  refine Finset.card_bij' (fun i _ => σ i) (fun j _ => σ.symm j) ?_ ?_ ?_ ?_
  · intro i hi
    simpa using hi
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simpa using hj
  · intro i _
    simp
  · intro j _
    simp

omit [Fintype A] [DecidableEq A] in
/-- **The weak form**: the dual weight is invariant under the whole monomial group. -/
theorem dualWeight_monomial_smul {φ : AddAut (ι → A)} (hφ : φ ∈ monomialSubgroup ι A G)
    (ξ : AddChar (ι → A) ℂ) : dualWeight (φ • ξ) = dualWeight ξ := by
  induction hφ using Subgroup.closure_induction generalizing ξ with
  | mem x hx =>
      rcases hx with ⟨g, rfl⟩ | ⟨σ, rfl⟩
      · exact dualWeight_scaleAut_smul g ξ
      · exact dualWeight_permAut_smul σ ξ
  | one => rw [one_smul]
  | mul x y _ _ ihx ihy => rw [mul_smul, ihx, ihy]
  | inv x hx ihx =>
      have h := ihx (x⁻¹ • ξ)
      rw [smul_inv_smul] at h
      exact h.symm

/-! ## Stability of the dual shells -/

/-- Membership in the dual weight-`k` shell IS having dual weight `k`. -/
theorem mem_shellSet_iff (k : ℕ) (ξ : AddChar (ι → A) ℂ) :
    ξ ∈ shellSet ι A k ↔ dualWeight ξ = k := by
  rw [shellSet, Finset.mem_image]
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    rw [Finset.mem_filter] at hχ
    rw [dualWeight, coordChar_piChar]
    exact hχ.2
  · intro h
    refine ⟨coordChar ξ, ?_, piChar_coordChar ξ⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h⟩

/-- **`shellSet_stable` (weak form).** The dual weight-`k` shell is stable under
the contragredient action of the monomial group — with NO transitivity hypothesis. -/
theorem shellSet_stable (k : ℕ) {φ : AddAut (ι → A)} (hφ : φ ∈ monomialSubgroup ι A G)
    {ξ : AddChar (ι → A) ℂ} (hξ : ξ ∈ shellSet ι A k) : φ • ξ ∈ shellSet ι A k := by
  rw [mem_shellSet_iff] at hξ ⊢
  rw [dualWeight_monomial_smul (G := G) hφ, hξ]

/-- The dual class sum of a shell is a class function for the monomial group: the fact a
scheme consumer needs (`Spectrum.qEnt_smul` at the Hamming instance), now available without
knowing that the shell is a single orbit. -/
theorem qEnt_shellSet_smul (k : ℕ) {φ : AddAut (ι → A)} (hφ : φ ∈ monomialSubgroup ι A G)
    (v : ι → A) : qEnt (shellSet ι A k) (φ • v) = qEnt (shellSet ι A k) v := by
  classical
  rw [qEnt, qEnt]
  refine Finset.sum_nbij' (i := fun ξ => φ⁻¹ • ξ) (j := fun ξ => φ • ξ) ?_ ?_ ?_ ?_ ?_
  · intro ξ hξ
    exact shellSet_stable (G := G) k (Subgroup.inv_mem _ hφ) hξ
  · intro ξ hξ
    exact shellSet_stable (G := G) k hφ hξ
  · intro ξ _
    exact smul_inv_smul φ ξ
  · intro ξ _
    exact inv_smul_smul φ ξ
  · intro ξ _
    simp only [contra_smul_apply, inv_inv]

end DualWeight


/-! ## The strong form: the dual shells ARE the dual orbits -/

section StrongForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Finite A]
variable {G : Type*} [Group G] [Finite G] [DistribMulAction G A]

/-- **The orbit classification at the dual alphabet, transported.** Two characters of the word
space have equal dual weight exactly when a monomial automorphism carries one to the other.

The hypothesis is transitivity on the nonzero elements of `A`; `transOnNonzero_dual` turns it
into transitivity on the nontrivial characters of `A`, which is what the classification needs
at the dual alphabet. The transport back to characters of `ι → A` is `coordChar_scaleAut_smul` and
`coordChar_permAut_smul` read in reverse, plus injectivity of `coordChar`. -/
theorem dualWeight_eq_iff_monomial (htrans : TransOnNonzero G A) (ξ η : AddChar (ι → A) ℂ) :
    dualWeight η = dualWeight ξ ↔ ∃ φ ∈ monomialSubgroup ι A G, φ • ξ = η := by
  classical
  constructor
  · intro h
    have hdual : TransOnNonzero G (AddChar A ℂ) := transOnNonzero_dual htrans
    have h' : hammingNorm (coordChar ξ) = hammingNorm (coordChar η) := by
      unfold dualWeight at h
      exact h.symm
    obtain ⟨σ, d, hd⟩ :=
      (hammingNorm_eq_iff_monomial (A := AddChar A ℂ) (G := G) hdual).mp h'
    refine ⟨scaleAut d * permAut σ, Subgroup.mul_mem _ (scaleAut_mem d) (permAut_mem σ), ?_⟩
    have hcc : coordChar ((scaleAut (A := A) d * permAut (A := A) σ) • ξ) = coordChar η := by
      rw [mul_smul, coordChar_scaleAut_smul, coordChar_permAut_smul, hd]
    have := congrArg piChar hcc
    rwa [piChar_coordChar, piChar_coordChar] at this
  · rintro ⟨φ, hφ, rfl⟩
    exact dualWeight_monomial_smul (G := G) hφ ξ

section Shells

variable [Fintype A] [DecidableEq A]

/-- **The dual analogue of `orb_eq_shell`**: the dual orbit of a character is its dual weight
shell. With `orb_eq_shell` on the primal side, both index sets of the Hamming scheme are now
weight shells. -/
theorem orb_eq_shellSet (htrans : TransOnNonzero G A) (ξ : AddChar (ι → A) ℂ) :
    orb (↑(monomialSubgroup ι A G)) ξ = shellSet ι A (dualWeight ξ) := by
  classical
  ext η
  rw [mem_orb, mem_shellSet_iff]
  constructor
  · rintro ⟨⟨φ, hφ⟩, rfl⟩
    exact dualWeight_monomial_smul (G := G) hφ ξ
  · intro h
    obtain ⟨φ, hφ, hx⟩ := (dualWeight_eq_iff_monomial htrans ξ η).mp h
    exact ⟨⟨φ, hφ⟩, hx⟩

end Shells

end StrongForm

end ECCLib.Scheme
