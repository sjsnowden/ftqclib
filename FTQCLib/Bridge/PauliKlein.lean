/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Error
import FTQCLib.Frame.ArfSum
import ECCLib.Delsarte.Shell

/-!
# The Klein-word chart

The per-coordinate chart identifying `Pauli n` with the Hamming word space over the Klein
alphabet `ZMod 2 × ZMod 2` — the join through which the Delsarte/association-scheme results
of `ECCLib` speak about Pauli codes. The existing `linearEquivProd` is its TRANSPOSE
(X-block × Z-block, not per-coordinate) and is not a substitute: the block reading disagrees
with `weight` on every Pauli carrying a `Y` (`FTQCLib.Bridge.PauliKleinCheck` exhibits one).

The chart carries: the metric identification (`weight = hammingNorm`, whence
distance-of-difference = Hamming distance of the images), the symplectic identification
(`omega` = the coordinatewise sum of `hypOmega`, CRSS eq. (1) read against the Klein
symplectic form), and the weight-shell count `#{p : weight p = d} = C(n,d)·3^d`
transported from `ECCLib.Delsarte.card_shell`. The chart is character-free: the character
bridge (`pauliChar`) belongs with the MacWilliams identity, where characters are first
consumed. Imports run `FTQCLib → ECCLib` only.

## Main definitions

* `pauliKleinEquiv` — the chart, as a `ZMod 2`-linear equivalence.

## Main results

* `weight_eq_hammingNorm`, `weight_sub_eq_hammingDist` — the metric identification.
* `omega_eq_sum_hypOmega` — the symplectic identification.
* `card_weight_shell` — the shell count `C(n,d)·3^d`.
-/

namespace FTQCLib.Pauli

open Finset FTQCLib.Stabilizer

variable {n : ℕ}

/-- **The Klein-word chart**: `Pauli n` read per coordinate as a word over the Klein
alphabet — coordinate `i` carries the pair `(X i, Z i)`. This is the transpose of
`linearEquivProd` (which groups the X-block against the Z-block and does NOT respect
the Pauli weight). -/
def pauliKleinEquiv : Pauli n ≃ₗ[ZMod 2] (Fin n → ZMod 2 × ZMod 2) where
  toFun p := fun i => (p.X i, p.Z i)
  invFun w := ⟨fun i => (w i).1, fun i => (w i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pauliKleinEquiv_apply (p : Pauli n) (i : Fin n) :
    pauliKleinEquiv p i = (p.X i, p.Z i) := rfl

/-- **The metric identification**: the Pauli weight is the Hamming norm of the Klein
word. This is the statement that makes `weight` the `q = 4` Hamming weight, joining the
Pauli-code and classical-code sides. -/
theorem weight_eq_hammingNorm (p : Pauli n) :
    weight p = hammingNorm (pauliKleinEquiv p) := by
  rw [weight, hammingNorm]
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  simp only [pauliKleinEquiv_apply, ne_eq, Prod.mk_eq_zero, not_and_or]

/-- Distances correspond: the weight of a difference is the Hamming distance of the
images. -/
theorem weight_sub_eq_hammingDist (p q : Pauli n) :
    weight (p - q) = hammingDist (pauliKleinEquiv p) (pauliKleinEquiv q) := by
  rw [weight_eq_hammingNorm, map_sub, hammingDist_comm, hammingDist_eq_hammingNorm,
    neg_add_eq_sub]

/-- **The symplectic identification**: `omega` is the coordinatewise sum of the Klein
symplectic form `hypOmega` — CRSS's eq. (1) read against the unique nondegenerate
alternating form on the Klein group. -/
theorem omega_eq_sum_hypOmega (p q : Pauli n) :
    omega p q
      = ∑ i, FTQCLib.ArfSum.hypOmega (pauliKleinEquiv p i) (pauliKleinEquiv q i) := by
  rw [omega, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pauliKleinEquiv_apply, FTQCLib.ArfSum.hypOmega]
  ring

/-- **The weight-shell count**: `#{p : Pauli n | weight p = d} = C(n,d)·3^d` — the size
`|E_d|` of the Shor–Laflamme shell, transported from `ECCLib.Delsarte.card_shell` through
the chart. -/
theorem card_weight_shell (n d : ℕ) :
    #(Finset.univ.filter fun p : Pauli n => weight p = d) = n.choose d * 3 ^ d := by
  have hcard : #(Finset.univ.filter fun p : Pauli n => weight p = d)
      = #(Finset.univ.filter
          fun w : Fin n → ZMod 2 × ZMod 2 => hammingNorm w = d) := by
    refine Finset.card_bij (fun p _ => pauliKleinEquiv p) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_univ _, by rw [← weight_eq_hammingNorm]; exact hp.2⟩
    · intro p hp q hq h
      exact pauliKleinEquiv.injective h
    · intro w hw
      refine ⟨pauliKleinEquiv.symm w, ?_, by simp⟩
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [weight_eq_hammingNorm]
      simpa using hw.2
  rw [hcard, ECCLib.Delsarte.card_shell]
  simp [Fintype.card_fin]

end FTQCLib.Pauli
