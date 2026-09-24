/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
/-
# Witnesses for Berlekamp–Massey

Two layers:

1. **The GF(16) identification witness**: `bm_error_locator` instantiated at the certified
   `[15, 9, 7]` field on the u-weighted syndromes of a weight-2 pattern — BY THEOREM, with
   kernel `decide` content rows for the executable run. The dual multipliers enter in
   closed form: for the full root-power family, `dualMult a16 i = α^i` (the nodal
   polynomial is `X^15 + 1`), via the `chkM15` materialization ladder.
2. **The cross-family differential check**: an extended-Euclid formulation of the
   synthesis problem, defined locally, with machine-checked agreement rows against
   `bmSynth` on inputs covering every branch — two structurally unrelated algorithms, one
   answer.
-/
import ECCLib.BerlekampMassey
import ECCLib.GateChecker

namespace ECCLib.Coding

variable {R : Type*}

/-! ## The dual multipliers in closed form -/

/-- For the full root-power family the dual multipliers are the powers themselves:
`u_i = α^i` (nodal polynomial `X^15 + 1`, derivative `X^14`). -/
theorem dualMult_a16 (i : Fin 15) :
    dualMult a16 i = AdjoinRoot.root (nu 3 r4p) ^ (i : ℕ) := by
  rw [← emb_uWord15 i]
  simp only [uWord15_eq_powVec]
  exact emb_powVec r4p _ (root_pow_top 3 r4p) (i : ℕ)

/-! ## The GF(16) witness pattern: weight 2 at positions 2 and 7 -/

/-- The error pattern: value `1` at positions 2 and 7. -/
noncomputable def e16 : Fin 15 → GF16p := fun i => if i = 2 ∨ i = 7 then 1 else 0

theorem e16_support : (Finset.univ.filter (fun i => e16 i ≠ 0)) = {2, 7} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, e16]
  by_cases h2 : i = 2
  · simp [h2]
  · by_cases h7 : i = 7
    · simp [h7]
    · simp [h2, h7]

theorem e16_card : (Finset.univ.filter (fun i => e16 i ≠ 0)).card = 2 := by
  rw [e16_support]
  decide

/-- The six u-weighted syndrome words, computable on the Pi-word carrier:
`s_j = α^(2(j+1)) + α^(7(j+1))`. -/
def synWords : List (Fin 4 → ZMod 2) :=
  (List.range 6).map fun j => powVec r4p (2 * (j + 1)) + powVec r4p (7 * (j + 1))

theorem synWords_length : synWords.length = 2 * 3 := by
  simp [synWords]

/-- Reading a mapped range list below its length. -/
theorem getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

/-- The syndrome words φ-read to the u-weighted syndrome sequence of the pattern. -/
theorem synWords_map (j : ℕ) (hj : j < 2 * 3) :
    emb (AdjoinRoot.root (nu 3 r4p)) (synWords.getD j gf16Ops.zero)
      = synSeq a16 e16 j := by
  rw [synWords, getD_map_range _ _ (by omega)]
  rw [show (powVec r4p (2 * (j + 1)) + powVec r4p (7 * (j + 1)))
      = gf16Ops.add (powVec r4p (2 * (j + 1))) (powVec r4p (7 * (j + 1))) from rfl]
  rw [gf16Model.map_add, emb_powVec r4p _ (root_pow_top 3 r4p),
    emb_powVec r4p _ (root_pow_top 3 r4p)]
  rw [synSeq]
  have hsum : ∑ i, dualMult a16 i * a16 i ^ j * e16 i
      = ∑ i ∈ ({2, 7} : Finset (Fin 15)), dualMult a16 i * a16 i ^ j * e16 i := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
    have h0 : e16 i = 0 := by
      by_contra hne
      exact hi (by rw [← e16_support]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
    rw [h0, mul_zero]
  rw [hsum, Finset.sum_pair (by decide : (2 : Fin 15) ≠ 7)]
  rw [show e16 2 = 1 from by simp [e16], show e16 7 = 1 from by simp [e16],
    mul_one, mul_one, dualMult_a16, dualMult_a16]
  rw [show a16 2 = AdjoinRoot.root (nu 3 r4p) ^ (((2 : Fin 15)) : ℕ) from rfl,
    show a16 7 = AdjoinRoot.root (nu 3 r4p) ^ (((7 : Fin 15)) : ℕ) from rfl]
  rw [show (((2 : Fin 15)) : ℕ) = 2 from rfl, show (((7 : Fin 15)) : ℕ) = 7 from rfl]
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  rw [show 2 + 2 * j = 2 * (j + 1) by ring, show 7 + 7 * j = 7 * (j + 1) by ring]

/-- **The GF(16) identification witness, by theorem**: on the six syndromes of the
weight-2 pattern, the algorithm returns length 2 and the locator `(X − α²)(X − α⁷)`. -/
theorem gf16_bm_error_locator :
    (bmSynth gf16Ops synWords).1 = 2
    ∧ toPoly (emb (AdjoinRoot.root (nu 3 r4p)))
        (bmLocator gf16Ops (bmSynth gf16Ops synWords)) = errLocator a16 e16 := by
  have h := bm_error_locator gf16Model a16_injective (t := 3)
    (by rw [e16_card]; norm_num) synWords_length synWords_map
  rwa [e16_card] at h

/-! Kernel content rows: the executable run, decided end to end. The locator content row
pins the whole word list — `(X − α²)(X − α⁷) = X² + (α² + α⁷)X + α⁹` in char 2,
little-endian with the stored-length pad. -/

set_option maxRecDepth 8192 in
example : (bmSynth gf16Ops synWords).1 = 2 := by decide

set_option maxRecDepth 8192 in
example : bmLocator gf16Ops (bmSynth gf16Ops synWords)
    = [powVec r4p 9, powVec r4p 2 + powVec r4p 7, powVec r4p 0] := by decide

/-! ## The cross-family differential check

Extended Euclid on `(X^N, reversed syndromes)`, stopping at the degree crossing — a
structurally unrelated algorithm whose output is directly the taps list. -/

/-- Euclid-family Berlekamp–Massey: remainder/cofactor descent with fuel. -/
def bmLoopD (ops : FieldOps R) : ℕ → List R → List R → List R → List R → List R × List R
  | 0, _, _, rc, vc => (rc, vc)
  | fuel + 1, rp, vp, rc, vc =>
    if pdeg ops rc < pdeg ops vc then (rc, vc)
    else
      bmLoopD ops fuel rc vc (pdivMod ops rp rc).2
        (psub ops vp (pmul ops (pdivMod ops rp rc).1 vc))

/-- The rival synthesizer: normalized minimal cofactor, output as a taps list. -/
def bmSynthD (ops : FieldOps R) (s : List R) : List R :=
  let out := bmLoopD ops (s.length + 2) (pshift ops s.length [ops.one]) [] s.reverse
    [ops.one]
  pneg ops (psmul ops (ops.inv (plead ops out.2)) (ptrim ops out.2)).dropLast

/-! Agreement rows: two algorithm families, one answer — on the branch-coverage inputs,
including the 𝔽₃ evaluation-point-zero run. -/

example : bmSynthD zmod2Ops [1, 1, 0, 1, 1, 0]
    = bmTaps zmod2Ops (bmSynth zmod2Ops [1, 1, 0, 1, 1, 0]) := by decide

example : bmSynthD zmod2Ops [1, 0, 1, 0, 1, 0]
    = bmTaps zmod2Ops (bmSynth zmod2Ops [1, 0, 1, 0, 1, 0]) := by decide

/-! On the maximal-complexity input `[0,0,0,1]` the input sits in the NON-UNIQUE regime
(`2L > N`): both families return `L = 4`, but different — equally valid, vacuous —
generators. The divergence is machine-checked: agreement may only be demanded where
uniqueness holds. -/

example : (bmSynthD zmod2Ops [0, 0, 0, 1]).length = (bmSynth zmod2Ops [0, 0, 0, 1]).1 := by
  decide

example : bmSynthD zmod2Ops [0, 0, 0, 1]
    ≠ bmTaps zmod2Ops (bmSynth zmod2Ops [0, 0, 0, 1]) := by decide

example : bmSynthD zmod2Ops [0, 0, 0, 0]
    = bmTaps zmod2Ops (bmSynth zmod2Ops [0, 0, 0, 0]) := by decide

example : bmSynthD zmod2Ops [] = bmTaps zmod2Ops (bmSynth zmod2Ops []) := by decide

example : bmSynthD zmod3Ops [2, 1, 1, 1]
    = bmTaps zmod3Ops (bmSynth zmod3Ops [2, 1, 1, 1]) := by decide

end ECCLib.Coding
