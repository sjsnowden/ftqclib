/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.CommutativeSubalgebra

/-!
# Checks for `ECCLib/CommutativeSubalgebra.lean`

Axiom sweeps. The instance-diamond row against `Subalgebra.toCommRing` lives in
`Scheme/OrbitalSpectrumCheck.lean`, where it was first required; the separating example that
makes the class strictly weaker than self-pairing is `commutative_not_isSelfPaired_Cyc3`,
ibid. This module imports only the extracted module and Mathlib, so it is itself a test of
the extraction.
-/

namespace ECCLib.Scheme

/-- info: 'ECCLib.Scheme.Subalgebra.IsCommutative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Subalgebra.IsCommutative

/-- info: 'ECCLib.Scheme.Subalgebra.instCommRingOfIsCommutative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Subalgebra.instCommRingOfIsCommutative

end ECCLib.Scheme
