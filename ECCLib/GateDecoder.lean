/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Decoding
import ECCLib.Circuit

set_option linter.unusedSectionVars false

/-!
# The gate-level decoder: composing decoder correctness with circuit preservation

This is the interface at which the field-level and gate-level layers meet. Above it, `Decoding.lean`
proves that a coset-leader syndrome decoder corrects `t` errors whenever `2t < d`, entirely at the
level of the field. Below it, `Circuit.lean` descends `𝔽₂`-linear and tabulated maps onto gates with
preservation theorems. Here they compose:

* **`decoderNet synNet Lnet`** — the two-stage datapath: compute the syndrome, look up its coset
  leader, correct. In characteristic 2 the correction `y − L (H y)` is a bitwise XOR, so the
  correction stage costs one gate per coordinate. Expressing this at all needs `Circuit.subst`
  (wire renaming is not enough — the syndrome netlist's *outputs* feed the leader netlist's
  *inputs*).
* **`eval_decoderNet`** — the netlist computes `y ↦ y − L (H y)` through the encoding, given that
  its two stages compute `H` and `L`.
* **`decoderNet_corrects`** — **the gate-level correction guarantee**: for every codeword of
  `ker H` and every error of weight at most `t`, with `2t < minDist (ker H)`, the netlist's output
  *is the encoded sent codeword*. Field-level decoder correctness composed with gate-level
  semantics preservation.

The shape of the hypotheses is the point. A netlist for a coset-leader map looks impossible at
first sight — `L` is obtained by `Classical.choose` over a `Finset` argmin, and quantified over
words it is astronomically wide. But `IsCosetLeaderMap` and `synDecoder` apply `L` **only at
`H y`**, so `L`'s domain is the *syndrome* module: its netlist has as many input wires as the
syndrome has coordinates, and for a small code it is a small table (`Circuit.tabC`). That is why
the two hypotheses below are dischargeable where a single hypothesis about the whole decoder is
not.
-/

namespace ECCLib.Coding

open ECCLib ECCLib.Circuit

variable {n r : ℕ}

/-- The **two-stage decoder netlist**: syndrome, then tabulated coset leader, then correct. -/
def decoderNet (synNet : CircuitVec n r) (Lnet : CircuitVec r n) : CircuitVec n n :=
  fun o => .xor (.wire o) (subst (Lnet o) synNet)

/-- The netlist computes the syndrome decoder's output through the bit encoding. -/
theorem eval_decoderNet {H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)}
    {L : (Fin r → ZMod 2) → (Fin n → ZMod 2)}
    {synNet : CircuitVec n r} {Lnet : CircuitVec r n}
    (hH : ∀ y, evalVec synNet (fun i => bit (y i)) = fun j => bit (H y j))
    (hL : ∀ s, evalVec Lnet (fun j => bit (s j)) = fun i => bit (L s i))
    (y : Fin n → ZMod 2) :
    evalVec (decoderNet synNet Lnet) (fun i => bit (y i))
      = fun o => bit ((y - L (H y)) o) := by
  funext o
  have hstage : (fun j => eval (synNet j) (fun i => bit (y i))) = fun j => bit (H y j) := hH y
  have hLo : eval (Lnet o) (fun j => bit (H y j)) = bit (L (H y) o) :=
    congrFun (hL (H y)) o
  rw [evalVec_apply, decoderNet]
  simp only [eval_xor, eval_wire, eval_subst, hstage, hLo]
  rw [← bit_add]
  congr 1
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  simp [Pi.sub_apply, sub_eq_add_neg, hneg]

/-- **The gate-level correction guarantee.** Every codeword of `ker H`, corrupted in at most `t`
coordinates with `2t < minDist (ker H)`, is recovered *by the netlist* — the field-level decoder
correctness theorem composed with gate-level semantics preservation. -/
theorem decoderNet_corrects {H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)}
    {L : (Fin r → ZMod 2) → (Fin n → ZMod 2)}
    {synNet : CircuitVec n r} {Lnet : CircuitVec r n}
    (hH : ∀ y, evalVec synNet (fun i => bit (y i)) = fun j => bit (H y j))
    (hL : ∀ s, evalVec Lnet (fun j => bit (s j)) = fun i => bit (L s i))
    (hLead : IsCosetLeaderMap H L) {t : ℕ} (h2t : 2 * t < minDist (LinearMap.ker H))
    (c : Fin n → ZMod 2) (hc : c ∈ LinearMap.ker H)
    (e : Fin n → ZMod 2) (he : hammingNorm e ≤ t) :
    evalVec (decoderNet synNet Lnet) (fun i => bit ((c + e) i)) = fun o => bit (c o) := by
  have hfix : (c + e) - L (H (c + e)) = c :=
    Option.some_injective _ (synDecoder_corrects hLead h2t c hc e he)
  rw [eval_decoderNet hH hL, hfix]

end ECCLib.Coding
