/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
/-
# The 𝔽₃ repetition-decoder descent

The odd-characteristic counterpart of the binary repetition-code netlist of
`WitnessCoding.lean`: the library's computable 𝔽₃ syndrome decoder
(`synDec₃ = synDecoder H₃ leader₃`) descended to a verified digit netlist — the syndrome map as a
`linWD` matrix block, the coset-leader table as a `dtabW` lookup, the final subtraction
coordinatewise, assembled by one `subst` — with the field-level correction theorem
(`synDec₃_corrects_one`, where `[Fact (3).Prime]` lives) composed against gate-level
semantics preservation into `dec3Net_corrects`: the netlist heals one error, proven.

**Live evaluation is infeasible in the tree model** (measured by `#eval sizeVec`; kernel
`decide` did not finish in 420 s, the interpreter in 240 s): `leader3Net` = 360 tree gates,
`syn3Net` = 317,328, one composition `compV leader3Net syn3Net` = 14,280,120 — every tabulated
wire-read duplicates the full downstream tree, so the assembled `dec3Net` is ~10⁸⁺ nodes, beyond
kernel AND interpreter. The witnesses therefore stand BY THEOREM (`dec3Net_corrects` below); live
evaluation would need the sharing layer (`compV` through the straightline adapters, whose shared
count collapses the duplication).
-/
import ECCLib.DigitCircuit
import ECCLib.WitnessCoding

namespace ECCLib.Coding

open Circuit Matrix ECCLib.Witness

/-! ## The syndrome map as a matrix -/

/-- `H₃` as a matrix: `(y₀ − y₁, y₁ − y₂)`. -/
def mH₃ : Matrix (Fin 2) (Fin 3) (ZMod 3) := ![![1, -1, 0], ![0, 1, -1]]

theorem mH₃_mulVec (y : Fin 3 → ZMod 3) : mH₃ *ᵥ y = H₃ y := by
  funext j
  fin_cases j <;>
    simp [mH₃, Matrix.mulVec, dotProduct, H₃, Fin.sum_univ_three] <;>
    ring

/-! ## The three stages and the assembled decoder -/

def syn3Net : CircuitVec (3 * dw 3) (2 * dw 3) := linWD 3 mH₃

def leader3Net : CircuitVec (2 * dw 3) (3 * dw 3) := dtabW 3 2 3 leader₃

/-- The decoder netlist `y ↦ y − leader₃ (H₃ y)`: the subtractor fed with the raw input
on the left and the leader-of-syndrome pipeline on the right, in one `subst`. -/
def dec3Net : CircuitVec (3 * dw 3) (3 * dw 3) :=
  fun o => subst (subNetD 3 3 o) (fun iw =>
    Fin.addCases (motive := fun _ => Circuit (3 * dw 3))
      (fun d₁ => Circuit.wire (finProdFinEquiv (d₁, (finProdFinEquiv.symm iw).2)))
      (fun d₂ => compV leader3Net syn3Net (finProdFinEquiv (d₂, (finProdFinEquiv.symm iw).2)))
      (finProdFinEquiv.symm iw).1)

/-- **Gate-level semantics of the decoder netlist**: on any encoded received word, the
netlist computes exactly the syndrome decoder's field-level correction. -/
theorem eval_dec3Net (y : Fin 3 → ZMod 3) :
    evalVec dec3Net (flatB (encWD y)) = flatB (encWD (y - leader₃ (H₃ y))) := by
  have hpipe : evalVec (compV leader3Net syn3Net) (flatB (encWD y))
      = flatB (encWD (leader₃ (H₃ y))) := by
    rw [evalVec_compV, syn3Net, evalVec_linWD, mH₃_mulVec, leader3Net, eval_dtabW]
  have hσ : (fun iw : Fin ((3 + 3) * dw 3) => eval
      (Fin.addCases (motive := fun _ => Circuit (3 * dw 3))
        (fun d₁ => Circuit.wire (finProdFinEquiv (d₁, (finProdFinEquiv.symm iw).2)))
        (fun d₂ => compV leader3Net syn3Net
          (finProdFinEquiv (d₂, (finProdFinEquiv.symm iw).2)))
        (finProdFinEquiv.symm iw).1) (flatB (encWD y)))
      = flatB (encWD (Fin.append y (leader₃ (H₃ y)))) := by
    funext iw
    have hRHS : flatB (encWD (Fin.append y (leader₃ (H₃ y)))) iw
        = encD (Fin.append y (leader₃ (H₃ y)) (finProdFinEquiv.symm iw).1)
            (finProdFinEquiv.symm iw).2 := rfl
    rw [hRHS]
    generalize (finProdFinEquiv.symm iw).1 = d
    generalize (finProdFinEquiv.symm iw).2 = b
    induction d using Fin.addCases with
    | left d₁ =>
      rw [Fin.addCases_left, Fin.append_left]
      change flatB (encWD y) (finProdFinEquiv (d₁, b)) = encD (y d₁) b
      simp [flatB, encWD]
    | right d₂ =>
      rw [Fin.addCases_right, Fin.append_right]
      have h := congrFun hpipe (finProdFinEquiv (d₂, b))
      refine h.trans ?_
      simp [flatB, encWD]
  funext o
  change eval (subst (subNetD 3 3 o) _) (flatB (encWD y)) = _
  rw [eval_subst]
  rw [show (fun iw => eval _ (flatB (encWD y))) = _ from hσ]
  exact congrFun (eval_subNetD 3 y (leader₃ (H₃ y))) o

/-- **The composed correction theorem**: the netlist heals any single error on any
codeword — the field-level `synDec₃_corrects_one` (`Fact (3).Prime` lives there) joined
to gate-level preservation. -/
theorem dec3Net_corrects {c e : Fin 3 → ZMod 3} (hc : c ∈ C₃) (he : hammingNorm e ≤ 1) :
    evalVec dec3Net (flatB (encWD (c + e))) = flatB (encWD c) := by
  rw [eval_dec3Net]
  have h : some ((c + e) - leader₃ (H₃ (c + e))) = some c :=
    synDec₃_corrects_one c hc e he
  rw [Option.some.inj h]

end ECCLib.Coding
