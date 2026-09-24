/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.BallCert
import Mathlib.Data.List.GetD

set_option linter.style.longLine false

/-!
# Worked examples for the Delsarte LP bound

Every certificate's arithmetic was machine-verified exactly (Python, exact integers)
before entering this file, and every Lean-side field is discharged by the kernel.
Certificates come from exact LP solves. The two listed attainment codes are
kernel-checked at `maxRecDepth 20000` (the binding resource is recursion depth, not
heartbeats); the repetition-code attainments are BY
THEOREM (`repCode_dist`), because sharpness of the repetition code is mathematics,
not a search — and because the `ZMod 10` scan at `n = 8` overflows the elaborator's
native stack (`lean::stack_space_exception`).

The instances:
* **(2,8,4) → 16, the flagship**: Plotkin is INAPPLICABLE (`2d = n` makes its
  hypothesis fail), yet the LP lands sharp; the extended Hamming `[8,4,4]` (= RM(1,3))
  attains it, kernel-checked.
* **(2,12,6) → 24 and (3,5,3) → 18**: sharp LP values that NO LINEAR code can attain
  (24 and 18 are not prime powers) — the cleanest demonstration that the theorem is
  genuinely about arbitrary codes. Attaining codes are standard literature
  (Nadler; ternary (5,18,3)) and are NOT constructed here — bound rows only.
* **(2,7,3) → 16**: the perfect Hamming code, attained, cross-checking the
  sphere-packing bound (the LP meets it exactly at a perfect code).
* **q = 6 and q = 10 rows**: non-prime-power alphabets — inexpressible in any field
  layer; repetition codes attain both. The q = 6 bound is ALSO stated over the bare
  alphabet `Fin 6` through the structureless transport (no algebraic structure).
* **Golay (2,23,7) → 4096**: the bound row at Golay scale (attainment is standard
  literature, NOT claimed here).
-/

namespace ECCLib.Delsarte

open Finset

/-- Nonnegativity of `getD`-encoded coefficient lists, once and for all. -/
theorem getD_nonneg {L : List ℤ} (hL : ∀ x ∈ L, 0 ≤ x) (k : ℕ) : 0 ≤ L.getD k 0 := by
  rcases Nat.lt_or_ge k L.length with h | h
  · rw [List.getD_eq_getElem L 0 h]
    exact hL _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]

/-! ## The certificates (gate LP solves, kernel-discharged) -/

/-- `(2,8,4)`: `β = (40, 33, 0, 1, 0, 0, 10, 0, 0)` — Plotkin-inapplicable flagship. -/
def cert284 : LPCert 2 8 4 where
  beta := fun k => [40, 33, 0, 1, 0, 0, 10, 0, 0].getD k 0
  beta_nonneg := getD_nonneg (by decide)
  beta_zero_pos := by decide
  neg := by decide

/-- `(2,12,6)`: `β = (6, 6, 1, 0, …)` — Plotkin also inapplicable (`qd = (q−1)n`). -/
def cert1263 : LPCert 2 12 6 where
  beta := fun k => [6, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD k 0
  beta_nonneg := getD_nonneg (by decide)
  beta_zero_pos := by decide
  neg := by decide

/-- `(2,7,3)`: `β = (3, 3, 1, 0, 0, 0, 0, 3)` — the perfect-Hamming instance. -/
def cert273 : LPCert 2 7 3 where
  beta := fun k => [3, 3, 1, 0, 0, 0, 0, 3].getD k 0
  beta_nonneg := getD_nonneg (by decide)
  beta_zero_pos := by decide
  neg := by decide

/-- `(3,5,3)`: `β = (6, 3, 1, 0, 0, 1)` — sharp value 18, not a power of 3. -/
def cert353 : LPCert 3 5 3 where
  beta := fun k => [6, 3, 1, 0, 0, 1].getD k 0
  beta_nonneg := getD_nonneg (by decide)
  beta_zero_pos := by decide
  neg := by decide

/-- `(6,5,5)`: the Plotkin-shaped certificate at a COMPOSITE alphabet size. -/
def cert655 : LPCert 6 5 5 where
  beta := fun k => [5, 1, 0, 0, 0, 0].getD k 0
  beta_nonneg := getD_nonneg (by decide)
  beta_zero_pos := by decide
  neg := by decide

/-- `(10,8,8)`: composite alphabet size ten. -/
def cert1088 : LPCert 10 8 8 where
  beta := fun k => [8, 1, 0, 0, 0, 0, 0, 0, 0].getD k 0
  beta_nonneg := getD_nonneg (by decide)
  beta_zero_pos := by decide
  neg := by decide

/-- The Golay-scale certificate `(2,23,7)`, 24 entries, value `11354112 = 2772·4096`. -/
def golayCert : LPCert 2 23 7 where
  beta := fun k => [2772, 2772, 1722, 857, 323, 95, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 10, 79, 277, 777, 1617, 2772].getD k 0
  beta_nonneg := getD_nonneg (by decide)
  beta_zero_pos := by decide
  neg := by
    set_option maxRecDepth 40000 in
    set_option maxHeartbeats 1600000 in
    decide


/-! ## The certificates at their carrier types (the `cert243'` pattern — one name
per instantiation so the floor rows and the master share atoms) -/

def cert284' : LPCert (Fintype.card (ZMod 2)) (Fintype.card (Fin 8)) 4 := cert284
def cert1263' : LPCert (Fintype.card (ZMod 2)) (Fintype.card (Fin 12)) 6 := cert1263
def cert273' : LPCert (Fintype.card (ZMod 2)) (Fintype.card (Fin 7)) 3 := cert273
def cert353' : LPCert (Fintype.card (ZMod 3)) (Fintype.card (Fin 5)) 3 := cert353
def cert655' : LPCert (Fintype.card (ZMod 6)) (Fintype.card (Fin 5)) 5 := cert655
def cert655f : LPCert (Fintype.card (Fin 6)) (Fintype.card (Fin 5)) 5 := cert655
def cert1088' : LPCert (Fintype.card (ZMod 10)) (Fintype.card (Fin 8)) 8 := cert1088
def golayCert' : LPCert (Fintype.card (ZMod 2)) (Fintype.card (Fin 23)) 7 := golayCert

/-! ## The bounds -/

/-- **The flagship**: `A₂(8,4) ≤ 16` where Plotkin's hypothesis FAILS (`2d = n`). -/
theorem bound_2_8_4 (C : Finset (Fin 8 → ZMod 2))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 4 ≤ hammingDist x y) : C.card ≤ 16 := by
  have h := cert284'.card_le_floor C hd
  have hval : (cert284'.value / cert284'.beta 0).toNat = 16 := by decide
  omega

/-- `A₂(12,6) ≤ 24` — a sharp value no linear code can attain. -/
theorem bound_2_12_6 (C : Finset (Fin 12 → ZMod 2))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 6 ≤ hammingDist x y) : C.card ≤ 24 := by
  have h := cert1263'.card_le_floor C hd
  have hval : (cert1263'.value / cert1263'.beta 0).toNat = 24 := by decide
  omega

/-- `A₂(7,3) ≤ 16` — met exactly by the perfect Hamming code. -/
theorem bound_2_7_3 (C : Finset (Fin 7 → ZMod 2))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ hammingDist x y) : C.card ≤ 16 := by
  have h := cert273'.card_le_floor C hd
  have hval : (cert273'.value / cert273'.beta 0).toNat = 16 := by decide
  omega

/-- `A₃(5,3) ≤ 18` — a sharp value no linear code can attain. -/
theorem bound_3_5_3 (C : Finset (Fin 5 → ZMod 3))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ hammingDist x y) : C.card ≤ 18 := by
  have h := cert353'.card_le_floor C hd
  have hval : (cert353'.value / cert353'.beta 0).toNat = 18 := by decide
  omega

/-- `A₆(5,5) ≤ 6` — composite alphabet, inexpressible in any field layer. -/
theorem bound_6_5_5 (C : Finset (Fin 5 → ZMod 6))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 5 ≤ hammingDist x y) : C.card ≤ 6 := by
  have h := cert655'.card_le_floor C hd
  have hval : (cert655'.value / cert655'.beta 0).toNat = 6 := by decide
  omega

/-- The `q = 6` bound over the BARE alphabet `Fin 6` — no algebraic structure at all,
through the structureless transport. -/
theorem bound_fin6 (C : Finset (Fin 5 → Fin 6))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 5 ≤ hammingDist x y) :
    (C.card : ℤ) * 5 ≤ 30 := by
  have h := cert655f.card_mul_le_value_alphabet C hd
  have hβ : cert655f.beta 0 = 5 := by decide
  have hval : cert655f.value = 30 := by decide
  rw [hβ, hval] at h
  exact h

/-- `A₁₀(8,8) ≤ 10` — composite alphabet size ten. -/
theorem bound_10_8_8 (C : Finset (Fin 8 → ZMod 10))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 8 ≤ hammingDist x y) : C.card ≤ 10 := by
  have h := cert1088'.card_le_floor C hd
  have hval : (cert1088'.value / cert1088'.beta 0).toNat = 10 := by decide
  omega

/-- **Golay scale**: `A₂(23,7) ≤ 4096` (attainment by the binary Golay code is
standard literature, NOT claimed here). -/
theorem bound_golay (C : Finset (Fin 23 → ZMod 2))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 7 ≤ hammingDist x y) : C.card ≤ 4096 := by
  have h := golayCert'.card_le_floor C hd
  have hval : (golayCert'.value / golayCert'.beta 0).toNat = 4096 := by
    set_option maxRecDepth 40000 in
    set_option maxHeartbeats 1600000 in
    decide
  omega

/-! ## Attainment (sharpness witnesses, kernel-checked at `maxRecDepth 20000`) -/

/-- The extended Hamming `[8,4,4]` = RM(1,3): 16 words, distance 4 — attains the
flagship bound. -/
def extHam : Finset (Fin 8 → ZMod 2) :=
  {![0,0,0,0,0,0,0,0], ![0,1,0,1,0,1,0,1], ![0,0,1,1,0,0,1,1], ![0,1,1,0,0,1,1,0],
   ![0,0,0,0,1,1,1,1], ![0,1,0,1,1,0,1,0], ![0,0,1,1,1,1,0,0], ![0,1,1,0,1,0,0,1],
   ![1,1,1,1,1,1,1,1], ![1,0,1,0,1,0,1,0], ![1,1,0,0,1,1,0,0], ![1,0,0,1,1,0,0,1],
   ![1,1,1,1,0,0,0,0], ![1,0,1,0,0,1,0,1], ![1,1,0,0,0,0,1,1], ![1,0,0,1,0,1,1,0]}

theorem extHam_card : extHam.card = 16 := by decide

set_option maxRecDepth 20000 in
theorem extHam_dist :
    ∀ x ∈ extHam, ∀ y ∈ extHam, x ≠ y → 4 ≤ hammingDist x y := by decide

/-- The Hamming `[7,4,3]`: 16 words, distance 3 — attains the perfect-code bound. -/
def ham74 : Finset (Fin 7 → ZMod 2) :=
  {![0,0,0,0,0,0,0], ![1,0,0,0,0,1,1], ![0,1,0,0,1,0,1], ![0,0,1,0,1,1,0],
   ![0,0,0,1,1,1,1], ![1,1,0,0,1,1,0], ![1,0,1,0,1,0,1], ![1,0,0,1,1,0,0],
   ![0,1,1,0,0,1,1], ![0,1,0,1,0,1,0], ![0,0,1,1,0,0,1], ![1,1,1,0,0,0,0],
   ![1,1,0,1,0,0,1], ![1,0,1,1,0,1,0], ![0,1,1,1,1,0,0], ![1,1,1,1,1,1,1]}

theorem ham74_card : ham74.card = 16 := by decide

set_option maxRecDepth 20000 in
theorem ham74_dist :
    ∀ x ∈ ham74, ∀ y ∈ ham74, x ≠ y → 3 ≤ hammingDist x y := by decide

/-- The repetition code over any alphabet: the constant words. Its sharpness is a
THEOREM — distinct constants differ in EVERY coordinate — so no kernel scan is
needed (the `ZMod 10` scan at `n = 8` in fact overflows the elaborator's native
stack; the theorem route is both cheaper and general). -/
def repCode (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) : Finset (Fin n → A) :=
  Finset.univ.image (fun c => fun _ => c)

theorem repCode_card (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) (hn : n ≠ 0) :
    (repCode A n).card = Fintype.card A := by
  have hinj : Function.Injective (fun c : A => (fun _ => c : Fin n → A)) :=
    fun a b hab => congrFun hab ⟨0, Nat.pos_of_ne_zero hn⟩
  rw [repCode, Finset.card_image_of_injective _ hinj, Finset.card_univ]

theorem repCode_dist (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) :
    ∀ x ∈ repCode A n, ∀ y ∈ repCode A n, x ≠ y → n ≤ hammingDist x y := by
  intro x hx y hy hne
  simp only [repCode, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a ≠ b := fun h => hne (by rw [h])
  have hdc : hammingDist (fun _ : Fin n => a) (fun _ : Fin n => b)
      = (Finset.univ.filter fun i : Fin n =>
          (fun _ : Fin n => a) i ≠ (fun _ : Fin n => b) i).card := rfl
  rw [hdc, Finset.filter_true_of_mem (fun i _ => hab), Finset.card_univ,
    Fintype.card_fin]

/-- The repetition code over `ZMod 6`: 6 words at distance 5 — attains `A₆(5,5) = 6`. -/
abbrev rep6 : Finset (Fin 5 → ZMod 6) := repCode (ZMod 6) 5

theorem rep6_card : rep6.card = 6 := by
  rw [repCode_card _ _ (by norm_num), ZMod.card]

theorem rep6_dist :
    ∀ x ∈ rep6, ∀ y ∈ rep6, x ≠ y → 5 ≤ hammingDist x y := repCode_dist _ _

/-- The repetition code over `ZMod 10`: 10 words at distance 8 — attains
`A₁₀(8,8) = 10`. -/
abbrev rep10 : Finset (Fin 8 → ZMod 10) := repCode (ZMod 10) 8

theorem rep10_card : rep10.card = 10 := by
  rw [repCode_card _ _ (by norm_num), ZMod.card]

theorem rep10_dist :
    ∀ x ∈ rep10, ∀ y ∈ rep10, x ≠ y → 8 ≤ hammingDist x y := repCode_dist _ _

end ECCLib.Delsarte

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Delsarte.bound_2_8_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.bound_2_8_4

/-- info: 'ECCLib.Delsarte.bound_3_5_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.bound_3_5_3

/-- info: 'ECCLib.Delsarte.bound_6_5_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.bound_6_5_5

/-- info: 'ECCLib.Delsarte.bound_fin6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.bound_fin6

/-- info: 'ECCLib.Delsarte.bound_golay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.bound_golay

/-- info: 'ECCLib.Delsarte.extHam_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.extHam_dist
