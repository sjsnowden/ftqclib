/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.CommonEigenvector
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Checks for `ECCLib/Matrix/CommonEigenvector.lean`

Axiom sweeps, and the generality row that is the module's reason to exist at its stated
hypotheses: the character is built **over `ℤ`** — no field anywhere — which is the compiled
form of the fact that `[NoZeroDivisors K]` suffices and `[Field K]` is not needed.
-/

namespace ECCLib.Scheme

open Matrix

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.IsCommonEigenvector' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.IsCommonEigenvector

/-- info: 'ECCLib.Scheme.isCommonEigenvector_basis' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isCommonEigenvector_basis

/-- info: 'ECCLib.Scheme.eq_of_smul_eq_smul_of_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eq_of_smul_eq_smul_of_ne_zero

/-- info: 'ECCLib.Scheme.IsCommonEigenvector.eigenvalue_unique' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.IsCommonEigenvector.eigenvalue_unique

/-- info: 'ECCLib.Scheme.IsCommonEigenvector.algHom' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.IsCommonEigenvector.algHom

/-- info: 'ECCLib.Scheme.IsCommonEigenvector.coe_algHom' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.IsCommonEigenvector.coe_algHom

/-! ## The `ℤ` generality row — no field anywhere

The all-ones vector on a one-point carrier is a common eigenvector of the full matrix algebra
over `ℤ`, and its functional is an algebra character. `ℤ` is not a field and not
`IsAlgClosed`; only `NoZeroDivisors` is consumed. This row is what the statement's
hypotheses claim, compiled. -/

theorem isCommonEigenvector_int :
    IsCommonEigenvector (⊤ : Subalgebra ℤ (Matrix Unit Unit ℤ)) (fun _ => 1)
      (fun M => (M : Matrix Unit Unit ℤ) () ()) where
  ne_zero h := one_ne_zero (congrFun h ())
  mulVec_eq M := by
    funext x
    simp [Matrix.mulVec, dotProduct]

/-- The character over `ℤ`, compiled: the refutation of "`Field` is genuinely needed". -/
example : ↥(⊤ : Subalgebra ℤ (Matrix Unit Unit ℤ)) →ₐ[ℤ] ℤ :=
  isCommonEigenvector_int.algHom

/-- info: 'ECCLib.Scheme.isCommonEigenvector_int' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isCommonEigenvector_int

end ECCLib.Scheme
