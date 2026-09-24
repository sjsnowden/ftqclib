/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Explore.GroupDoors
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Data.Matrix.Basis

set_option linter.style.longLine false

/-! # `𝔤₂(𝔽₂)` from its root system

The comparison `L(3)(𝔽₂) ≟ 𝔤₂(𝔽₂)` in `FTQCLib/Explore/GroupDoors.lean` rests on the dichotomy lemma
plus the fact that `𝔤₂(𝔽₂)` carries a nonzero ad-eigenvector of eigenvalue 1. This file proves that
fact by BUILDING the algebra and machine-checking the eigenvector — no table is trusted.

**Construction (no hand-entered structure constants).** The only inputs are the twelve G₂ roots in
the simple-root basis (`roots`) and the Gram matrix of the G₂ inner product ((α,α) = 2, (β,β) = 6,
(α,β) = −3) — both textbook-standard and visible below. Everything else is COMPUTED by Lean from
them, following the Chevalley-basis rules (Humphreys §25.2): Cartan pairings
`⟨r, s∨⟩ = 2(r,s)/(s,s)`, coroot coefficients `h_r = (2r₁/(r,r))·h_α + (6r₂/(r,r))·h_β`, and
`N_{r,s} = ±(p+1)` with `p` the root-string length — over `𝔽₂` the Chevalley signs vanish and
`±2 ↦ 0`, so the table `t` is sign-free. The algebra is realized by its ADJOINT matrices inside
`gl₁₄(𝔽₂)` (`adMat`), where the Jacobi identity is free (matrix commutator). `g2` is the Lie
subalgebra they GENERATE — closed by construction, so the non-nilpotence proof below needs only
cheap `decide`s. **Faithfulness:** the fourteen adjoint matrices are linearly independent
(`toMat_injective`, via an explicit probe matrix with explicit inverse `1 + E₀₁` — one matrix
product by `decide`), so `g2` contains a 14-dimensional space. The closure equations
`⁅adMat i, adMat j⁆ = ad ⁅eᵢ, eⱼ⁆` — which ARE the table's Jacobi identity, and pin `g2` to exactly
the 14-dimensional span (hence center-free = the Chevalley algebra itself, not a quotient) — are the
kernel-heavy check, separated into `GTwoCert.lean`; the closure holds by compiled evaluation
(`#eval decide ... = true`); the kernel check is a long, memory-heavy job, kept in a separate module
that nothing imports so that it is built only on demand. (What `decide` certifies is Lie-ness,
dimension, and the eigenvector; that the input data IS the G₂ root system is the visible 12-vector
list + Gram matrix.)

**The eigenvector.** `⁅h_β, x_α⁆ = ⟨α, β∨⟩·x_α = −x_α ≡ x_α (mod 2)` with `x_α ≠ 0` (`lie_Hg_Xg`,
`Xg_ne_zero`), so by the dichotomy lemma `eq_zero_of_lie_eq_self`:

* `g2_not_nilpotent` — **`𝔤₂(𝔽₂)` is not a nilpotent Lie algebra**;
* `not_nilpotent_of_surjective_g2` — nor is anything surjecting onto it (so central extensions, the
  abstract Chevalley form under any identification, etc.).

So, unconditionally, no nilpotent Lie algebra — in particular `L(3)(𝔽₂)`, its quotients, and
anything the frame's abelian difference data generates (`FTQCLib/Explore/LieClosure.lean`) — is
isomorphic to `𝔤₂(𝔽₂)`. An exploratory file, not part of the `FTQCLib` target; it uses no
`native_decide`. -/

namespace FTQCLib.Explore.GTwo

open FTQCLib.Explore.GroupDoors

/-! ## The root data — the only inputs -/

/-- The twelve G₂ roots in the `(α, β)` simple-root basis (`α` short, `β` long). -/
def roots : Fin 12 → Int × Int
  | 0 => (1,0)   | 1 => (0,1)   | 2 => (1,1)   | 3 => (2,1)   | 4 => (3,1)   | 5 => (3,2)
  | 6 => (-1,0)  | 7 => (0,-1)  | 8 => (-1,-1) | 9 => (-2,-1) | 10 => (-3,-1) | 11 => (-3,-2)

def isRoot (v : Int × Int) : Bool := (List.finRange 12).any (fun k => roots k = v)

def rootIdx (v : Int × Int) : Fin 12 :=
  ((List.finRange 12).find? (fun k => roots k = v)).getD 0

/-- The G₂ inner product: `(α,α) = 2`, `(β,β) = 6`, `(α,β) = −3`. -/
def ip (r s : Int × Int) : Int := 2*r.1*s.1 + 6*r.2*s.2 - 3*(r.1*s.2 + r.2*s.1)

/-- The Cartan pairing `⟨r, s∨⟩ = 2(r,s)/(s,s)` (an exact division for roots), mod 2. -/
def pair2 (r s : Int × Int) : ZMod 2 := ((2 * ip r s / ip s s : Int) : ZMod 2)

/-- Coroot coefficients of `h_r` in `(h_α, h_β)`, mod 2. -/
def cor (r : Int × Int) : ZMod 2 × ZMod 2 :=
  (((2*r.1 / ip r r : Int) : ZMod 2), ((6*r.2 / ip r r : Int) : ZMod 2))

/-- The root-string length `p = max{k : s − k·r ∈ Φ}` (`k ≤ 3` in G₂). -/
def stringP (r s : Int × Int) : Nat :=
  if isRoot (s.1 - 3*r.1, s.2 - 3*r.2) then 3
  else if isRoot (s.1 - 2*r.1, s.2 - 2*r.2) then 2
  else if isRoot (s.1 - r.1, s.2 - r.2) then 1 else 0

/-- `N_{r,s} mod 2 = p + 1` when `r + s` is a root, else `0` (Chevalley; signs vanish mod 2). -/
def nMod2 (r s : Int × Int) : ZMod 2 :=
  if isRoot (r.1 + s.1, r.2 + s.2) then ((stringP r s + 1 : Nat) : ZMod 2) else 0

/-! ## The bracket table and its adjoint realization -/

/-- Basis vectors of the coordinate space (indices `0,1` = `h_α, h_β`; `2+k` = `x_{roots k}`). -/
def eVec (i : Fin 14) : Fin 14 → ZMod 2 := fun j => if j = i then 1 else 0

/-- The Chevalley bracket table over `𝔽₂`, computed from the root data. -/
def t : Fin 14 → Fin 14 → (Fin 14 → ZMod 2) := fun i j =>
  if (i : ℕ) < 2 ∧ (j : ℕ) < 2 then 0
  else if h : (i : ℕ) < 2 ∧ 2 ≤ (j : ℕ) then
    (pair2 (roots ⟨(j : ℕ) - 2, by omega⟩) (if (i : ℕ) = 0 then (1,0) else (0,1))) • eVec j
  else if h2 : 2 ≤ (i : ℕ) ∧ (j : ℕ) < 2 then
    (pair2 (roots ⟨(i : ℕ) - 2, by omega⟩) (if (j : ℕ) = 0 then (1,0) else (0,1))) • eVec i
  else if h3 : 2 ≤ (i : ℕ) ∧ 2 ≤ (j : ℕ) then
    let r := roots ⟨(i : ℕ) - 2, by omega⟩
    let s := roots ⟨(j : ℕ) - 2, by omega⟩
    if r.1 + s.1 = 0 ∧ r.2 + s.2 = 0 then
      (cor r).1 • eVec 0 + (cor r).2 • eVec 1
    else if isRoot (r.1 + s.1, r.2 + s.2) then
      nMod2 r s • eVec ⟨2 + (rootIdx (r.1 + s.1, r.2 + s.2) : ℕ), by omega⟩
    else 0
  else 0

/-- The bracket table as an evaluated LITERAL (92 nonzero entries). The kernel reduces a `tLit` lookup in
tens of steps where a `t` evaluation (root-list scans, `Int` divisions) costs thousands — so the heavy
`decide`s below run on `tLit`, and `t_eq_tLit` certifies once that the literal IS the root-derived table. -/
def tLit : Fin 14 → Fin 14 → (Fin 14 → ZMod 2)
  | 0, 3 => eVec 3   | 0, 4 => eVec 4   | 0, 5 => eVec 5   | 0, 6 => eVec 6
  | 0, 9 => eVec 9   | 0, 10 => eVec 10 | 0, 11 => eVec 11 | 0, 12 => eVec 12
  | 1, 2 => eVec 2   | 1, 4 => eVec 4   | 1, 6 => eVec 6   | 1, 7 => eVec 7
  | 1, 8 => eVec 8   | 1, 10 => eVec 10 | 1, 12 => eVec 12 | 1, 13 => eVec 13
  | 2, 1 => eVec 2   | 2, 3 => eVec 4   | 2, 5 => eVec 6   | 2, 8 => eVec 0
  | 2, 10 => eVec 9  | 2, 12 => eVec 11
  | 3, 0 => eVec 3   | 3, 2 => eVec 4   | 3, 6 => eVec 7   | 3, 9 => eVec 1
  | 3, 10 => eVec 8  | 3, 13 => eVec 12
  | 4, 0 => eVec 4   | 4, 1 => eVec 4   | 4, 5 => eVec 7   | 4, 8 => eVec 3
  | 4, 9 => eVec 2   | 4, 10 => eVec 0 + eVec 1 | 4, 13 => eVec 11
  | 5, 0 => eVec 5   | 5, 2 => eVec 6   | 5, 4 => eVec 7   | 5, 11 => eVec 1
  | 5, 12 => eVec 8  | 5, 13 => eVec 10
  | 6, 0 => eVec 6   | 6, 1 => eVec 6   | 6, 3 => eVec 7   | 6, 8 => eVec 5
  | 6, 11 => eVec 2  | 6, 12 => eVec 0 + eVec 1 | 6, 13 => eVec 9
  | 7, 1 => eVec 7   | 7, 9 => eVec 6   | 7, 10 => eVec 5  | 7, 11 => eVec 4
  | 7, 12 => eVec 3  | 7, 13 => eVec 0
  | 8, 1 => eVec 8   | 8, 2 => eVec 0   | 8, 4 => eVec 3   | 8, 6 => eVec 5
  | 8, 9 => eVec 10  | 8, 11 => eVec 12
  | 9, 0 => eVec 9   | 9, 3 => eVec 1   | 9, 4 => eVec 2   | 9, 7 => eVec 6
  | 9, 8 => eVec 10  | 9, 12 => eVec 13
  | 10, 0 => eVec 10 | 10, 1 => eVec 10 | 10, 2 => eVec 9  | 10, 3 => eVec 8
  | 10, 4 => eVec 0 + eVec 1 | 10, 7 => eVec 5 | 10, 11 => eVec 13
  | 11, 0 => eVec 11 | 11, 5 => eVec 1  | 11, 6 => eVec 2  | 11, 7 => eVec 4
  | 11, 8 => eVec 12 | 11, 10 => eVec 13
  | 12, 0 => eVec 12 | 12, 1 => eVec 12 | 12, 2 => eVec 11 | 12, 5 => eVec 8
  | 12, 6 => eVec 0 + eVec 1 | 12, 7 => eVec 3 | 12, 9 => eVec 13
  | 13, 1 => eVec 13 | 13, 3 => eVec 12 | 13, 4 => eVec 11 | 13, 5 => eVec 10
  | 13, 6 => eVec 9  | 13, 7 => eVec 0
  | _, _ => 0

/-- **Provenance: the literal is exactly the root-derived Chevalley table.** -/
theorem t_eq_tLit : ∀ i j : Fin 14, t i j = tLit i j := by decide

/-- The adjoint matrix of the `i`-th basis element: column `j` is the coordinate vector of `⁅eᵢ, eⱼ⁆`. -/
def adMat (i : Fin 14) : Matrix (Fin 14) (Fin 14) (ZMod 2) :=
  Matrix.of (fun k j => tLit i j k)

/-- Coordinates → matrices: the linear realization map. -/
def toMat : (Fin 14 → ZMod 2) →ₗ[ZMod 2] Matrix (Fin 14) (Fin 14) (ZMod 2) where
  toFun v := ∑ i, v i • adMat i
  map_add' u v := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, RingHom.id_apply]

@[simp] lemma toMat_apply (v : Fin 14 → ZMod 2) : toMat v = ∑ i, v i • adMat i := rfl

/-- The table is symmetric with zero diagonal (char 2 antisymmetry). -/
theorem t_symm_diag : (∀ i j : Fin 14, t i j = t j i) ∧ (∀ i : Fin 14, t i i = 0) := by decide

/-! ## Faithfulness: the fourteen adjoint matrices are independent -/

/-- Probe positions: fourteen matrix entries whose evaluation matrix is invertible (found by offline
GF(2) elimination; certified by `probeMinv_mul` below). -/
def probePos : Fin 14 → Fin 14 × Fin 14
  | 0 => (12,12) | 1 => (13,13) | 2 => (11,12) | 3 => (12,13) | 4 => (11,13)
  | 5 => (10,13) | 6 => (9,13)  | 7 => (7,1)   | 8 => (12,11) | 9 => (13,12)
  | 10 => (13,11) | 11 => (13,10) | 12 => (13,9) | 13 => (13,1)

/-- The probe-evaluation matrix `M k i = (adMat i) (probePos k)`. -/
def probeM : Matrix (Fin 14) (Fin 14) (ZMod 2) :=
  Matrix.of fun k i => adMat i (probePos k).1 (probePos k).2

/-- Its explicit inverse: `1 + E₀₁`. -/
def probeMinv : Matrix (Fin 14) (Fin 14) (ZMod 2) := 1 + Matrix.single 0 1 1

theorem probeMinv_mul : probeMinv * probeM = 1 := by decide

/-- Probing a realized matrix reads off `probeM.mulVec`. -/
theorem probe_toMat (v : Fin 14 → ZMod 2) (k : Fin 14) :
    (toMat v) (probePos k).1 (probePos k).2 = probeM.mulVec v k := by
  simp only [toMat_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, probeM, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The realization is faithful:** the fourteen adjoint matrices are linearly independent — the algebra
below contains a space of dimension exactly 14. -/
theorem toMat_injective (v : Fin 14 → ZMod 2) (hv : toMat v = 0) : v = 0 := by
  have hM : probeM.mulVec v = 0 := by
    funext k
    rw [← probe_toMat, hv]
    simp
  have h2 := congrArg probeMinv.mulVec hM
  rwa [Matrix.mulVec_mulVec, probeMinv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2

/-! ## The algebra and its non-nilpotence -/

/-- **`𝔤₂(𝔽₂)`, realized adjointly:** the Lie subalgebra of `gl₁₄(𝔽₂)` GENERATED by the fourteen adjoint
matrices — closed by construction (no closure computation needed for non-nilpotence). That it equals the
14-dimensional span (i.e. the generators are already bracket-closed — the table's Jacobi identity) is the
kernel-heavy check, separated into `GTwoCert.lean` (see the build note there). -/
def g2 : LieSubalgebra (ZMod 2) (Matrix (Fin 14) (Fin 14) (ZMod 2)) :=
  LieSubalgebra.lieSpan (ZMod 2) _ (Set.range adMat)

theorem toMat_eVec (i : Fin 14) : toMat (eVec i) = adMat i := by
  rw [toMat_apply]
  have h : ∀ j : Fin 14, eVec i j • adMat j = if j = i then adMat j else 0 := fun j => by
    simp only [eVec]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj, one_smul]
    · rw [if_neg hj, if_neg hj, zero_smul]
  rw [Finset.sum_congr rfl fun j _ => h j,
    Finset.sum_ite_eq' Finset.univ i fun j => adMat j]
  exact if_pos (Finset.mem_univ i)

/-- `h_β` in the algebra. -/
def Hg : g2 := ⟨adMat 1, LieSubalgebra.subset_lieSpan ⟨1, rfl⟩⟩

/-- `x_α` in the algebra. -/
def Xg : g2 := ⟨adMat 2, LieSubalgebra.subset_lieSpan ⟨2, rfl⟩⟩

/-- **The eigenvector relation:** `⁅h_β, x_α⁆ = ⟨α, β∨⟩·x_α = −x_α ≡ x_α` over `𝔽₂` — the odd Cartan
pairing of G₂ surviving mod 2. -/
theorem lie_Hg_Xg : ⁅Hg, Xg⁆ = Xg := by
  apply Subtype.ext
  change ⁅adMat 1, adMat 2⁆ = adMat 2
  decide

theorem Xg_ne_zero : Xg ≠ 0 := by
  intro h
  have h2 : adMat 2 = 0 := congrArg Subtype.val h
  exact (by decide : adMat 2 ≠ (0 : Matrix (Fin 14) (Fin 14) (ZMod 2))) h2

/-- **`𝔤₂(𝔽₂)` is not nilpotent** — by the dichotomy lemma applied to the machine-checked
eigenvector. -/
theorem g2_not_nilpotent : ¬ LieRing.IsNilpotent g2 := by
  intro hnil
  exact Xg_ne_zero (eq_zero_of_lie_eq_self (R := ZMod 2) Hg Xg lie_Hg_Xg)

/-- Nothing surjecting onto `𝔤₂(𝔽₂)` is nilpotent either — central extensions and the abstract Chevalley
form included (images of nilpotent algebras are nilpotent). -/
theorem not_nilpotent_of_surjective_g2 {L : Type*} [LieRing L] [LieAlgebra (ZMod 2) L]
    (f : L →ₗ⁅ZMod 2⁆ g2) (hf : Function.Surjective f) : ¬ LieRing.IsNilpotent L := by
  intro hnil
  exact g2_not_nilpotent (hf.lieAlgebra_isNilpotent (f := f))

end FTQCLib.Explore.GTwo
