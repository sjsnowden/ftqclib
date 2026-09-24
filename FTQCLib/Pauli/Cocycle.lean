/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Symplectic
import Mathlib.Tactic.LinearCombination

/-! # The Pauli-product cocycle, frame-native (`ℤ/4`)

`betaFrame p q : ZMod 4` is the `ℤ/4` `i`-exponent of the Hermitian-Pauli product
phase `H(q) ∘ H(p) = i^{betaFrame p q} · H(p+q)`. It is defined purely from the
symplectic bit data — the `i`-power weight `yWeight` (the `Y`-count `Z·X`) and the
`Z·X` dot product `zDot` — with **no Hilbert layer**. Since `(-1)^k = i^{2k}`, the
real `(-1)`-pieces enter doubled.

The textbook identity tying this to the `H(p)` operators is a *separate* bridge in `FTQCLib/Hilbert`;
nothing here imports it. -/

namespace FTQCLib.Pauli

variable {n : ℕ}

/-- Frame-native `Z·v` dot product (the `(-1)`-exponent data), `ℕ`-valued. -/
def zDot (p : Pauli n) (v : Fin n → ZMod 2) : ℕ := ∑ i, (p.Z i).val * (v i).val

/-- Frame-native `i`-power weight: the `Y`-count `Z·X` of `p`. -/
def yWeight (p : Pauli n) : ℕ := zDot p p.X

@[simp] lemma zDot_zero_left (v : Fin n → ZMod 2) : zDot (0 : Pauli n) v = 0 := by
  simp [zDot]

@[simp] lemma yWeight_zero : yWeight (0 : Pauli n) = 0 := by
  simp [yWeight]

/-- In characteristic two every Pauli is its own inverse: `p + p = 0`. -/
@[simp] lemma pauli_add_self (p : Pauli n) : p + p = 0 := by
  ext i
  · change p.X i + p.X i = (0 : Pauli n).X i
    rw [X_zero, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _
  · change p.Z i + p.Z i = (0 : Pauli n).Z i
    rw [Z_zero, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _

/-- The `ℤ/4` Pauli-product cocycle exponent (`H(q)∘H(p) = i^{betaFrame p q} H(p+q)`). -/
def betaFrame (p q : Pauli n) : ZMod 4 :=
  ((yWeight p + yWeight q + yWeight (p + q)
    + 2 * (zDot q p.X + zDot (p + q) (p + q).X) : ℕ) : ZMod 4)

/-- Trivial on the diagonal: `betaFrame p p = 0` (each stabilizer sign squares to one). -/
@[simp] theorem betaFrame_self (p : Pauli n) : betaFrame p p = 0 := by
  have hzx : zDot p p.X = yWeight p := rfl
  unfold betaFrame
  rw [pauli_add_self, yWeight_zero, X_zero, zDot_zero_left, hzx]
  have h4 : (yWeight p + yWeight p + 0 + 2 * (yWeight p + 0)) = 4 * yWeight p := by ring
  rw [h4, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- The `Z·v` dot product reduces mod two to the `ZMod 2` dot product. -/
theorem zDot_cast_two (p : Pauli n) (v : Fin n → ZMod 2) :
    ((zDot p v : ℕ) : ZMod 2) = ∑ i, p.Z i * v i := by
  unfold zDot
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.cast_mul]
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- Doubling in `ZMod 4` depends only on parity: `2·a = 2·(a mod 2)`. -/
theorem two_mul_natCast_four (a : ℕ) :
    (2 : ZMod 4) * (a : ZMod 4) = 2 * (((a : ZMod 2).val : ℕ) : ZMod 4) := by
  have h_mod : 2 * a ≡ 2 * (a % 2) [MOD 4] := by unfold Nat.ModEq; omega
  have h_cast : ((2 * a : ℕ) : ZMod 4) = ((2 * (a % 2) : ℕ) : ZMod 4) :=
    (ZMod.natCast_eq_natCast_iff (2 * a) (2 * (a % 2)) 4).mpr h_mod
  have hpc : (2 : ZMod 4) * (a : ZMod 4) = ((2 * a : ℕ) : ZMod 4) := by push_cast; ring
  rw [hpc, h_cast, ZMod.val_natCast]
  push_cast; ring

/-- For `ZMod 2` elements, doubling the value is additive in `ZMod 4` (a four-case check). -/
theorem two_val_add (a b : ZMod 2) :
    (2 : ZMod 4) * ((a + b).val : ZMod 4) = 2 * (a.val : ZMod 4) + 2 * (b.val : ZMod 4) := by
  revert a b; decide

/-- The `ZMod 2 → ZMod 4` value cast turns `+` into XOR-with-carry:
`s(a+b) = s a + s b − 2·(s a · s b)`. The `−2·…` carry is the load-bearing correction in the floor
quadratic-refinement (`encodeE`) shift identity. -/
theorem val_add_cast (a b : ZMod 2) :
    ((a + b).val : ZMod 4) = (a.val : ZMod 4) + (b.val : ZMod 4)
      - 2 * ((a.val : ZMod 4) * (b.val : ZMod 4)) := by
  revert a b; decide

/-- **Factor-2 collapse.** Multiplied by `2·Y`, the XOR carry vanishes: `(a+b).val` and
`a.val + b.val` agree (the carry `−2 a b` times `2Y` is `−4·… = 0`). This kills the quadratic-part
corrections in the `encodeE` shift identity. -/
theorem val_add_two_mul (a b : ZMod 2) (Y : ZMod 4) :
    ((a + b).val : ZMod 4) * (2 * Y)
      = ((a.val : ZMod 4) + (b.val : ZMod 4)) * (2 * Y) := by
  have h4 : (4 : ZMod 4) = 0 := by decide
  rw [val_add_cast]
  linear_combination (-(a.val : ZMod 4) * (b.val : ZMod 4) * Y) * h4

/-- The doubled `Z·v` dot product is additive in its first Pauli argument (in `ZMod 4`). -/
theorem two_zDot_add (p q : Pauli n) (w : Fin n → ZMod 2) :
    (2 : ZMod 4) * ((zDot (p + q) w : ℕ) : ZMod 4)
      = 2 * ((zDot p w : ℕ) : ZMod 4) + 2 * ((zDot q w : ℕ) : ZMod 4) := by
  rw [two_mul_natCast_four (zDot (p + q) w), two_mul_natCast_four (zDot p w),
    two_mul_natCast_four (zDot q w)]
  have hc : ((zDot (p + q) w : ℕ) : ZMod 2)
      = ((zDot p w : ℕ) : ZMod 2) + ((zDot q w : ℕ) : ZMod 2) := by
    rw [zDot_cast_two, zDot_cast_two, zDot_cast_two]
    simp only [Z_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hc]
  exact two_val_add _ _

/-- **Bilinear factor-2 collapse.** Multiplied by `2·B`, a product of two XOR sums splits as if the
carries were absent: `(a+b).val·(c+d).val·2B = (a.val+b.val)·(c.val+d.val)·2B`. The quadratic-part
identity for the `encodeE` shift (each cross term carries a `2·zDot`). -/
theorem val_add_mul_two (a b c d : ZMod 2) (B : ZMod 4) :
    ((a + b).val : ZMod 4) * ((c + d).val : ZMod 4) * (2 * B)
      = ((a.val : ZMod 4) + (b.val : ZMod 4))
          * ((c.val : ZMod 4) + (d.val : ZMod 4)) * (2 * B) := by
  have step1 : ((a + b).val : ZMod 4) * ((c + d).val : ZMod 4) * (2 * B)
      = ((c + d).val : ZMod 4) * (2 * (((a + b).val : ZMod 4) * B)) := by ring
  rw [step1, val_add_two_mul c d]
  have step2 : ((c.val : ZMod 4) + (d.val : ZMod 4)) * (2 * (((a + b).val : ZMod 4) * B))
      = ((a + b).val : ZMod 4) * (2 * (((c.val : ZMod 4) + (d.val : ZMod 4)) * B)) := by ring
  rw [step2, val_add_two_mul a b]
  ring

/-- The doubled `Z·v` dot product is additive in its **vector** argument (in `ZMod 4`). -/
theorem two_zDot_add_right (p : Pauli n) (v w : Fin n → ZMod 2) :
    (2 : ZMod 4) * ((zDot p (v + w) : ℕ) : ZMod 4)
      = 2 * ((zDot p v : ℕ) : ZMod 4) + 2 * ((zDot p w : ℕ) : ZMod 4) := by
  rw [two_mul_natCast_four (zDot p (v + w)), two_mul_natCast_four (zDot p v),
    two_mul_natCast_four (zDot p w)]
  have hc : ((zDot p (v + w) : ℕ) : ZMod 2)
      = ((zDot p v : ℕ) : ZMod 2) + ((zDot p w : ℕ) : ZMod 2) := by
    rw [zDot_cast_two, zDot_cast_two, zDot_cast_two]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hc]
  exact two_val_add _ _

/-- **Isotropic swap.** On a commuting pair (`ω(p,q) = 0`) the doubled cross dot products agree:
`2·zDot p q.X = 2·zDot q p.X` in `ZMod 4` (their `ZMod 2` parts agree, since `ω` is their sum). -/
theorem two_zDot_swap_of_omega {p q : Pauli n} (h : omega p q = 0) :
    (2 : ZMod 4) * ((zDot p q.X : ℕ) : ZMod 4) = 2 * ((zDot q p.X : ℕ) : ZMod 4) := by
  rw [two_mul_natCast_four (zDot p q.X), two_mul_natCast_four (zDot q p.X)]
  have homega : omega p q = ((zDot p q.X : ℕ) : ZMod 2) + ((zDot q p.X : ℕ) : ZMod 2) := by
    rw [zDot_cast_two, zDot_cast_two]
    unfold omega
    congr 1
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [h] at homega
  have key : ∀ A B : ZMod 2, 0 = A + B → A = B := by decide
  rw [key _ _ homega]

@[simp] lemma zDot_zero_right (p : Pauli n) : zDot p (0 : Fin n → ZMod 2) = 0 := by
  simp [zDot]

/-- Every `ZMod 2` element is `0` or `1`. -/
theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- The doubled `Z·v` dot product scales by `ZMod 2` in its vector argument (in `ZMod 4`). -/
theorem two_zDot_smul_right (g : Pauli n) (a : ZMod 2) (b : Fin n → ZMod 2) :
    2 * ((zDot g (a • b) : ℕ) : ZMod 4) = (a.val : ZMod 4) * (2 * ((zDot g b : ℕ) : ZMod 4)) := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · rw [zero_smul, zDot_zero_right, show ((0 : ZMod 2).val : ZMod 4) = 0 from by decide]; simp
  · rw [one_smul, show ((1 : ZMod 2).val : ZMod 4) = 1 from by decide, one_mul]

/-- The doubled `Z·v` dot product scales by `ZMod 2` in its Pauli argument (in `ZMod 4`). -/
theorem two_zDot_smul_left (a : ZMod 2) (g : Pauli n) (u : Fin n → ZMod 2) :
    2 * ((zDot (a • g) u : ℕ) : ZMod 4) = (a.val : ZMod 4) * (2 * ((zDot g u : ℕ) : ZMod 4)) := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · rw [zero_smul, zDot_zero_left, show ((0 : ZMod 2).val : ZMod 4) = 0 from by decide]; simp
  · rw [one_smul, show ((1 : ZMod 2).val : ZMod 4) = 1 from by decide, one_mul]

/-- The doubled `Z·v` dot product commutes with a finite sum in its vector argument. -/
theorem two_zDot_sum_right {ι : Type*} (g : Pauli n) (s : Finset ι)
    (f : ι → Fin n → ZMod 2) :
    2 * ((zDot g (∑ i ∈ s, f i) : ℕ) : ZMod 4)
      = ∑ i ∈ s, 2 * ((zDot g (f i) : ℕ) : ZMod 4) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s' ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, two_zDot_add_right, ih]

/-- The doubled `Z·v` dot product commutes with a finite sum in its Pauli argument. -/
theorem two_zDot_sum_left {ι : Type*} (s : Finset ι) (f : ι → Pauli n)
    (u : Fin n → ZMod 2) :
    2 * ((zDot (∑ i ∈ s, f i) u : ℕ) : ZMod 4)
      = ∑ i ∈ s, 2 * ((zDot (f i) u : ℕ) : ZMod 4) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s' ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, two_zDot_add, ih]

/-- **Antisymmetry / commutation.** Swapping the arguments shifts the cocycle by `2·ω`:
`betaFrame q p = betaFrame p q + 2·ω(p,q)` (lifting `ω : ZMod 2` into `{0,2} ⊆ ZMod 4`). On a
Lagrangian (`ω = 0`) the cocycle is therefore symmetric. -/
theorem betaFrame_swap (p q : Pauli n) :
    betaFrame q p = betaFrame p q + 2 * (((omega p q).val : ℕ) : ZMod 4) := by
  have homega : omega p q = ((zDot p q.X : ℕ) : ZMod 2) + ((zDot q p.X : ℕ) : ZMod 2) := by
    rw [zDot_cast_two, zDot_cast_two]
    unfold omega
    congr 1
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have key : (2 : ZMod 4) * ((zDot p q.X : ℕ) : ZMod 4)
      = 2 * ((zDot q p.X : ℕ) : ZMod 4) + 2 * (((omega p q).val : ℕ) : ZMod 4) := by
    rw [two_mul_natCast_four (zDot p q.X), two_mul_natCast_four (zDot q p.X), homega, two_val_add]
    have hzero : ∀ y : ZMod 4, 2 * y + 2 * y = 0 := by decide
    linear_combination -hzero ((((zDot q p.X : ℕ) : ZMod 2).val : ℕ) : ZMod 4)
  unfold betaFrame
  have hyw : yWeight (q + p) = yWeight (p + q) := by rw [add_comm q p]
  have hzd : zDot (q + p) (q + p).X = zDot (p + q) (p + q).X := by rw [add_comm q p]
  rw [hyw, hzd]
  push_cast
  linear_combination key

/-- **The 2-cocycle condition** `δβ = 0` (additive, trivial-action form): the associativity
identity `β(q,r) − β(p+q,r) + β(p,q+r) − β(p,q) = 0`, forced by the two bracketings of
`H(r)∘H(q)∘H(p)`. The cohomological backbone — the law that makes the Pauli central
extension's twisted product associative. Proof (cf. `betaFrame_swap`): the `yWeight`
self-terms pair with the quadratic `2·zDot` self-terms into `4·(…) = 0`, and the cross
terms cancel by `2·zDot` bilinearity. -/
theorem betaFrame_cocycle (p q r : Pauli n) :
    betaFrame q r - betaFrame (p + q) r + betaFrame p (q + r) - betaFrame p q = 0 := by
  have hbil1 : (2 : ZMod 4) * ((zDot r (p + q).X : ℕ) : ZMod 4)
      = 2 * ((zDot r p.X : ℕ) : ZMod 4) + 2 * ((zDot r q.X : ℕ) : ZMod 4) := by
    rw [show (p + q).X = p.X + q.X from X_add p q]; exact two_zDot_add_right r p.X q.X
  have hbil2 : (2 : ZMod 4) * ((zDot (q + r) p.X : ℕ) : ZMod 4)
      = 2 * ((zDot q p.X : ℕ) : ZMod 4) + 2 * ((zDot r p.X : ℕ) : ZMod 4) := two_zDot_add q r p.X
  have z1 : (((zDot (q + r) (q + r).X : ℕ) : ZMod 4)) * 4 = 0 := by
    rw [show (4 : ZMod 4) = 0 from by decide, mul_zero]
  have z2 : (((zDot (p + q) (p + q).X : ℕ) : ZMod 4)) * 4 = 0 := by
    rw [show (4 : ZMod 4) = 0 from by decide, mul_zero]
  unfold betaFrame yWeight
  push_cast
  simp only [add_assoc]
  linear_combination hbil2 - hbil1 + z1 - z2

/-- The **quadratic refinement** of `ω`: `q(p) = ∑ᵢ pₓ(i)·p_z(i)`, valued in `ZMod 2`. It is the
parity of `yWeight` (`qForm_eq_yWeight_cast`), and it is what separates the symplectic group from
the orthogonal group of `q` — the image of the frame's gate alphabet at precision one. -/
def qForm (p : Pauli n) : ZMod 2 := ∑ i, p.X i * p.Z i

/-- `qForm` is the parity of `yWeight`. -/
theorem qForm_eq_yWeight_cast (p : Pauli n) : qForm p = ((yWeight p : ℕ) : ZMod 2) := by
  unfold qForm yWeight
  rw [zDot_cast_two]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

end FTQCLib.Pauli
