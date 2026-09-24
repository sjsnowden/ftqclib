/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GaoDecoder
import ECCLib.FieldCert

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# The Gao decoder at the certified fields

The instantiation layer: the coordinate model `Fin (m+1) → ZMod 2` with the library's certified
multiplier `mulVecC` and decided inverse tables is a `FieldOps.Model` of the quotient field
`AdjoinRoot ν` through the evaluation `emb` — **generically in `(m, r, table)`** (`gfModel`,
mirroring `irreducible_of_inv`'s shape: the named certificates `inv4_cert`/`inv8_cert` are
the only per-field inputs). Instantiated twice:

* **GF(16)** with the primitive `X⁴ + X + 1`: the classical `[15, 9, 7]` code on the
  root-power family (`orderOf_root_GF16p = 15` gives injectivity), corrected at `t = 3`
  (`gf16_rs_corrects`), with a by-theorem corrected transmission;
* **GF(256)**, the AES field: the full-field `[256, 224, 33]` code on the bit-enumeration
  family (injectivity = `emb_injective ∘ bitsVec_injective`, no order certificate needed —
  the AES root has order 51, so it is not primitive), corrected at `t = 16`
  (`gf256_rs_corrects`).

Everything the decoder executes (`mulVecC`, `tblInv`, `powVec`, and the whole `rsDecode`
chain) is computable and kernel-reducible; `AdjoinRoot` appears only in the spec layer.
-/

namespace ECCLib.Coding

open Polynomial ECCLib

/-! ## The generic Model engine -/

section Engine

variable (m : ℕ) (r : Fin (m + 1) → ZMod 2)

/-- Computable field operations on the coordinate model: pointwise addition, identity
negation (characteristic 2), the certified multiplier, a decided inverse table. -/
def gfOps (invL : List (List ℕ)) : FieldOps (Fin (m + 1) → ZMod 2) where
  zero := 0
  one := powVec r 0
  add := (· + ·)
  neg := id
  mul := mulVecC r
  inv := tblInv invL
  beq := fun v w => decide (v = w)

private lemma emb_zero {A : Type*} [CommRing A] [Algebra (ZMod 2) A] (α : A) :
    emb α (0 : Fin (m + 1) → ZMod 2) = 0 := by
  unfold emb
  simp

private lemma emb_add {A : Type*} [CommRing A] [Algebra (ZMod 2) A] (α : A)
    (v w : Fin (m + 1) → ZMod 2) :
    emb α (v + w) = emb α v + emb α w := by
  unfold emb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_smul]

/-- **The coordinate model is a model of the quotient field** — generic in the reduction
word and the certified table. The two hypotheses are exactly the named table certificates. -/
theorem gfModel [Fact (Irreducible (nu m r))] (invL : List (List ℕ))
    (hcert : ∀ v, v ≠ 0 → mulVecC r v (tblInv invL v) = powVec r 0)
    (hzero : tblInv invL (0 : Fin (m + 1) → ZMod 2) = 0) :
    (gfOps m r invL).Model (emb (AdjoinRoot.root (nu m r))) := by
  have hα := root_pow_top m r
  refine ⟨?_, emb_zero m _, ?_, emb_add m _, ?_, ?_, ?_, ?_⟩
  · -- bijective: injective + equal cardinalities
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨emb_injective m r, ?_⟩
    rw [card_adjoinRoot_nu, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · -- one
    rw [show (gfOps m r invL).one = powVec r 0 from rfl, emb_powVec r _ hα 0, pow_zero]
  · -- neg (characteristic 2)
    intro v
    have hvv : v + v = 0 := by
      funext i
      have h2 : ∀ u : ZMod 2, u + u = 0 := by decide
      simpa using h2 (v i)
    rw [show (gfOps m r invL).neg v = v from rfl]
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← emb_add, hvv, emb_zero]
  · -- mul
    intro v w
    exact emb_mulVecC r _ hα v w
  · -- inv
    intro v
    by_cases hv : v = 0
    · rw [show (gfOps m r invL).inv v = tblInv invL v from rfl, hv, hzero, emb_zero, inv_zero]
    · rw [show (gfOps m r invL).inv v = tblInv invL v from rfl]
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← emb_mulVecC r _ hα, hcert v hv, emb_powVec r _ hα 0, pow_zero]
  · -- beq
    intro v w
    rw [show (gfOps m r invL).beq v w = decide (v = w) from rfl]
    constructor
    · intro h
      rw [decide_eq_true_iff.mp h]
    · intro h
      exact decide_eq_true_iff.mpr (emb_injective m r h)

end Engine

/-! ## The two certified instantiations -/

/-- The computable GF(16) operations (primitive polynomial `X⁴ + X + 1`). -/
def gf16Ops : FieldOps (Fin 4 → ZMod 2) := gfOps 3 r4p inv4L

/-- The coordinate model IS GF(16), through the evaluation at the root. -/
theorem gf16Model : gf16Ops.Model (emb (AdjoinRoot.root (nu 3 r4p)) : _ → GF16p) :=
  gfModel 3 r4p inv4L inv4_cert tblInv_inv4L_zero

/-- The computable GF(256) operations (the AES polynomial). -/
def gf256Ops : FieldOps (Fin 8 → ZMod 2) := gfOps 7 r8 inv8L

/-- The coordinate model IS GF(256). -/
theorem gf256Model : gf256Ops.Model (emb (AdjoinRoot.root (nu 7 r8)) : _ → GF256) :=
  gfModel 7 r8 inv8L inv8_cert tblInv_inv8L_zero

/-! ## The point families -/

/-- The classical GF(16) evaluation family: the first 15 powers of the certified primitive
root. -/
noncomputable def a16 : Fin 15 → GF16p := fun i => AdjoinRoot.root (nu 3 r4p) ^ (i : ℕ)

theorem a16_injective : Function.Injective a16 := by
  intro i j h
  have horder := orderOf_root_GF16p
  have hinj := pow_injOn_Iio_orderOf (x := AdjoinRoot.root (nu 3 r4p))
  refine Fin.ext (hinj ?_ ?_ h)
  · rw [Set.mem_Iio, horder]
    exact i.isLt
  · rw [Set.mem_Iio, horder]
    exact j.isLt

/-- The bit-vector enumeration of the byte space. -/
def bitsVec (i : Fin 256) : Fin 8 → ZMod 2 := fun k => if (i : ℕ).testBit (k : ℕ) then 1 else 0

theorem bitsVec_injective : Function.Injective bitsVec := by
  intro i j h
  have hbool : ∀ a b : Bool, ((if a then 1 else 0 : ZMod 2) = if b then 1 else 0) → a = b := by
    decide
  refine Fin.ext (Nat.eq_of_testBit_eq fun k => ?_)
  rcases Nat.lt_or_ge k 8 with hk | hk
  · exact hbool _ _ (congrFun h ⟨k, hk⟩)
  · have hpow : (256 : ℕ) ≤ 2 ^ k :=
      calc (256 : ℕ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hi : (i : ℕ) < 2 ^ k := lt_of_lt_of_le i.isLt hpow
    have hj : (j : ℕ) < 2 ^ k := lt_of_lt_of_le j.isLt hpow
    rw [Nat.testBit_lt_two_pow hi, Nat.testBit_lt_two_pow hj]

/-- The full-field GF(256) evaluation family: all 256 elements, enumerated through the
coordinate model. No order certificate needed (the AES root is NOT primitive — order 51);
injectivity is `emb_injective` outright. -/
noncomputable def a256 : Fin 256 → GF256 := fun i => emb (AdjoinRoot.root (nu 7 r8)) (bitsVec i)

theorem a256_injective : Function.Injective a256 := fun _ _ h =>
  bitsVec_injective (emb_injective 7 r8 h)

/-! ## The flagship correction guarantees -/

/-- **`[15, 9, 7]` over GF(16)**: the Gao decoder corrects any `t` with `2t + 9 ≤ 15` — the
main case `t = 3`. -/
theorem gf16_rs_corrects :
    Corrects (rsDecodeF gf16Ops gf16Model a16 9) (rsCode a16 9) 3 :=
  rsDecodeF_corrects gf16Ops gf16Model a16_injective (by norm_num) (by norm_num)

/-- The `[15, 9]` code is MDS: `d = 7`. -/
theorem minDist_rsCode_a16 : minDist (rsCode a16 9) = 7 := by
  have h := minDist_rsCode (a := a16) a16_injective (k := 9) (by norm_num)
    (by rw [Fintype.card_fin]; norm_num)
  rw [Fintype.card_fin] at h
  omega

/-- **`[256, 224, 33]` over the AES GF(256)**, full-field: the Gao decoder corrects
`t = 16` errors — the CCSDS-shaped guarantee at `n = q`. -/
theorem gf256_rs_corrects :
    Corrects (rsDecodeF gf256Ops gf256Model a256 224) (rsCode a256 224) 16 :=
  rsDecodeF_corrects gf256Ops gf256Model a256_injective (by norm_num) (by norm_num)

/-- The `[256, 224]` code is MDS: `d = 33`. -/
theorem minDist_rsCode_a256 : minDist (rsCode a256 224) = 33 := by
  have h := minDist_rsCode (a := a256) a256_injective (k := 224) (by norm_num)
    (by rw [Fintype.card_fin]; norm_num)
  rw [Fintype.card_fin] at h
  omega

/-! ## A corrected transmission (by theorem)

The field-level carrier is noncomputable (`AdjoinRoot`, classical `DecidableEq`), so no
`decide` runs here: the message, codeword, and error are symbolic, the weight bound is a
support-subset argument, and the correction is the theorem applied. The LIVE run of the
executable decoder happens at the list level. -/

/-- The transmitted message: `f = X² + 1 ∈ F[X]_{<9}`. -/
noncomputable def msg16 : Polynomial GF16p := X ^ 2 + 1

theorem msg16_mem : msg16 ∈ degreeLT GF16p 9 := by
  rw [Polynomial.mem_degreeLT]
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · rw [degree_X_pow]
    exact_mod_cast by norm_num
  · exact lt_of_le_of_lt degree_one_le (by exact_mod_cast by norm_num)

/-- The transmitted codeword. -/
noncomputable def sent16 : Fin 15 → GF16p := rsEval a16 msg16

/-- A weight-3 error: value `1` at the first three positions. -/
noncomputable def err16 : Fin 15 → GF16p := fun i => if (i : ℕ) < 3 then 1 else 0

theorem err16_wt : hammingNorm err16 ≤ 3 := by
  refine le_trans (hammingNorm_le_card_of_subset
    (S := Finset.univ.filter fun i : Fin 15 => (i : ℕ) < 3) fun i hi => ?_) (by decide)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hlt
  exact hi (by simp [err16, hlt])

/-- **The corrected transmission**: three errors on a `[15, 9, 7]` codeword, healed by the
verified Gao decoder. -/
theorem gf16_transmission :
    rsDecodeF gf16Ops gf16Model a16 9 (sent16 + err16) = some sent16 :=
  gf16_rs_corrects sent16 (mem_rsCode.mpr ⟨msg16, msg16_mem, rfl⟩) err16 err16_wt

end ECCLib.Coding
