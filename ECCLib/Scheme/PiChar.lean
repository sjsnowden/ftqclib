/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.BigOperators.Pi

/-!
# The dual of a finite product

`AddChar (ι → A) ℂ ≃ (ι → AddChar A ℂ)`: a tuple of alphabet characters IS a character of
the word space (`piChar χ v = ∏ i, χ i (v i)`), and every character of the word space
arises this way (`coordChar` restricts to the coordinates). Mathlib has only the
direct-sum injection `AddChar.directSum`; the equivalence for `ι → A` is supplied here
with an explicit two-sided inverse (computable). `piChar χ v` is definitionally the
Delsarte layer's `tupleChar χ v` — the rfl bridge lives in `Scheme/DelsarteBridge.lean`
so this file stays Mathlib-only.
-/

namespace ECCLib.Scheme

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A]

omit [DecidableEq ι] in
/-- The tuple character as a character of the product group. -/
def piChar (χ : ι → AddChar A ℂ) : AddChar (ι → A) ℂ where
  toFun v := ∏ i, χ i (v i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' u v := by
    simp only [Pi.add_apply, AddChar.map_add_eq_mul]
    rw [Finset.prod_mul_distrib]

omit [DecidableEq ι] in
@[simp] theorem piChar_apply (χ : ι → AddChar A ℂ) (v : ι → A) :
    piChar χ v = ∏ i, χ i (v i) := rfl

omit [Fintype ι] in
/-- The coordinate restrictions of a character of the product group. -/
def coordChar (χ : AddChar (ι → A) ℂ) (i : ι) : AddChar A ℂ :=
  χ.compAddMonoidHom (AddMonoidHom.single (fun _ : ι => A) i)

omit [Fintype ι] in
@[simp] theorem coordChar_apply (χ : AddChar (ι → A) ℂ) (i : ι) (a : A) :
    coordChar χ i a = χ (Pi.single i a) := rfl

theorem piChar_coordChar (χ : AddChar (ι → A) ℂ) : piChar (coordChar χ) = χ := by
  ext v
  simp only [piChar_apply, coordChar_apply]
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  have key : ∀ s : Finset ι,
      χ (∑ i ∈ s, Pi.single i (v i)) = ∏ i ∈ s, χ (Pi.single i (v i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]
  rw [show χ v = χ (∑ i, Pi.single i (v i)) from by rw [← hv]]
  exact (key Finset.univ).symm

theorem coordChar_piChar (χ : ι → AddChar A ℂ) : coordChar (piChar χ) = χ := by
  funext i
  ext a
  simp only [coordChar_apply, piChar_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, AddChar.map_zero_eq_one]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The dual of a finite product is the product of the duals.** -/
def piCharEquiv : (ι → AddChar A ℂ) ≃ AddChar (ι → A) ℂ where
  toFun := piChar
  invFun := coordChar
  left_inv := coordChar_piChar
  right_inv := piChar_coordChar

omit [DecidableEq ι] in
theorem piChar_injective : Function.Injective (piChar (ι := ι) (A := A)) := by
  classical
  exact (piCharEquiv (ι := ι) (A := A)).injective

end ECCLib.Scheme
