/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.LP
import ECCLib.Scheme.PiChar
import ECCLib.Delsarte.Inequality

/-!
# `delsarte_nonneg` recovered from the H-free class-map inequality

The library's `ECCLib.Delsarte.delsarte_nonneg` — the Delsarte inequality over
ANY finite abelian alphabet — is re-derived VERBATIM as an instance of the abstract
class-map inequality `Scheme.class_delsarte_nonneg`: the class map is `hammingNorm`, the
character set is the dual weight-`k` shell pushed through `piChar`, the class function
is `kraw`, and the one input is the Delsarte layer's crux `charShellSum`. No group, no
transitivity, no bound on `k`. This is the ONLY module of the
scheme layer that imports the Delsarte layer.

The defeq tripwire at the end is load-bearing: it accepts the bridge's statement with
the original theorem, so any drift in hypotheses (a hidden `k` guard, an extra transitivity
assumption) fails to compile.
-/

namespace ECCLib.Scheme

open Finset ECCLib.Delsarte
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

omit [DecidableEq ι] [Fintype A] [DecidableEq A] in
/-- `piChar` IS the Delsarte layer's `tupleChar`, definitionally. -/
theorem piChar_eq_tupleChar (χ : ι → AddChar A ℂ) (v : ι → A) :
    piChar χ v = tupleChar χ v := rfl

/-- The dual weight-`k` shell as a set of characters of the word space. -/
noncomputable def shellSet (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] (k : ℕ) :
    Finset (AddChar (ι → A) ℂ) :=
  (Finset.univ.filter (fun χ : ι → AddChar A ℂ => hammingNorm χ = k)).image piChar

/-- **The dual weight shells have the primal shell sizes**: `piChar` is injective and the
character alphabet has the alphabet's cardinality (`AddChar.card_eq`). -/
theorem card_shellSet (k : ℕ) :
    (shellSet ι A k).card = (Fintype.card ι).choose k * (Fintype.card A - 1) ^ k := by
  classical
  rw [shellSet, Finset.card_image_of_injective _ piChar_injective, card_shell,
    AddChar.card_eq]

/-- The dual class sum of the weight-`k` shell is the Krawtchouk number — this is the Delsarte
layer's `charShellSum`, transported along `piChar`. -/
theorem qEnt_shellSet (k : ℕ) (v : ι → A) :
    qEnt (shellSet ι A k) v
      = ((kraw (Fintype.card A) (Fintype.card ι) k (hammingNorm v) : ℤ) : ℂ) := by
  rw [qEnt, shellSet, Finset.sum_image (fun x _ y _ h => piChar_injective h)]
  rw [← charShellSum (ι := ι) (A := A) k v]
  rfl

omit [DecidableEq ι] [Fintype A] in
/-- The abstract class count at the Hamming class map IS the Delsarte layer's
`pairCount`. -/
theorem classCount_hammingNorm (C : Finset (ι → A)) (i : ℕ) :
    classCount C (fun v => hammingNorm v) i = pairCount C i := by
  unfold classCount pairCount
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  rw [hammingDist_eq_hammingNorm]
  have : -p.1 + p.2 = p.2 - p.1 := by abel
  rw [this]

omit [DecidableEq ι] in
/-- **THE BRIDGE ROW.** The library's `delsarte_nonneg`, verbatim, as an instance of
the H-free class-map inequality. -/
theorem bridge_delsarte_nonneg (C : Finset (ι → A)) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (Fintype.card ι + 1),
          (pairCount C i : ℤ) * kraw (Fintype.card A) (Fintype.card ι) k i := by
  classical
  have h := class_delsarte_nonneg (V := ι → A) C (fun v => hammingNorm v)
    (Finset.range (Fintype.card ι + 1))
    (fun v => Finset.mem_range.mpr (Nat.lt_succ_of_le hammingNorm_le_card_fintype))
    (shellSet ι A k)
    (fun i => kraw (Fintype.card A) (Fintype.card ι) k i)
    (fun v => qEnt_shellSet k v)
  simpa only [classCount_hammingNorm] using h

omit [DecidableEq ι] in
/-- **Defeq tripwire (both directions).** The bridge's statement is accepted by the original
theorem and vice versa — identical hypotheses, identical conclusion. -/
example (C : Finset (ι → A)) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (Fintype.card ι + 1),
          (pairCount C i : ℤ) * kraw (Fintype.card A) (Fintype.card ι) k i :=
  delsarte_nonneg C k

omit [DecidableEq ι] in
example : ∀ (C : Finset (ι → A)) (k : ℕ),
    0 ≤ ∑ i ∈ Finset.range (Fintype.card ι + 1),
          (pairCount C i : ℤ) * kraw (Fintype.card A) (Fintype.card ι) k i :=
  fun C k => bridge_delsarte_nonneg C k

end ECCLib.Scheme
