/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.LinearCombination
import FTQCLib.Stabilizer.Defs

/-!
# The Z-shear

A Z-shear is a linear map of `Pauli n` that fixes every X-part and adds to the Z-part a linear
function of the X-part: `⟨x, z⟩ ↦ ⟨x, z + M x⟩` for a linear map `M` of the X-space. It is an
involution (`zShearBy_zShearBy`), shears compose by adding their maps (`zShearBy_add`), and the
shear is symplectic when the pairing `(x, y) ↦ ∑ i, M x i * y i` is symmetric (`omega_zShearBy`);
it then carries isotropic subspaces to isotropic subspaces (`isStabilizer_map_zShearBy`). Symmetry
is only ever used on the X-parts of the subspace moved (`IsSymmPairingOn`,
`isStabilizer_map_zShearBy_of_symm_on`), which is the form the diagonal class rule on the frame's
carrier supplies: the datum of a level-two diagonal exponent makes its polar matrix symmetric on
the shadow of the Lagrangian, and nothing more is asked.

The shear *at the bit `k` by the vector `d`* (`zShear k d`) is the shear by the linear map
`shearLin k d`, whose matrix is `d·e_kᵀ + e_k·dᵀ + d_k·E_kk`: it sends a Pauli with X-part `e_k`
to the same X-part with `d` added to its Z-part (`zShear_reader`), and it is the identity on
Paulis whose X-part is orthogonal to `d` and vanishes at `k`. Its pairing is symmetric by
construction (`isSymmPairing_shearLin`), so it is symplectic with no hypothesis.

Two roles in the frame: the diagonal Clifford gates act on a Lagrangian by a shear (`S` at `i` is
the shear at `i` by `e_i`; `CZ` on `i, j` is the shear at `i` by `e_j`; a level-two diagonal
exponent is the shear by its polar matrix), and the eliminating Hadamard aligns a Lagrangian at a
bit by one shear before it swaps.

## Main definitions

* `zShearBy M` — the shear by a linear map `M` of the X-space, as `Pauli n →ₗ[ZMod 2] Pauli n`.
* `IsSymmPairing M`, `IsSymmPairingOn M V` — the pairing of `M` is symmetric, everywhere or on `V`.
* `shearRow k d x`, `shearLin k d` — the Z-correction of the shear at `k` by `d`, as a function
  and as a linear map (`shearRow_single_self`, `shearRow_single_ne`, `shearRow_zero`: its values
  on the letters' vectors).
* `zShear k d` — the shear at `k` by `d`: `zShearBy (shearLin k d)`.
* `zShearByEquiv M`, `zShearEquiv k d` — the same maps as linear equivalences (involutions).

## Main results

* `zShearBy_X`, `zShearBy_Z`, `zShearBy_zShearBy`, `zShearBy_add` — what the shear does, the
  involution, the group law; `map_zShearBy_add`, `map_zShearBy_list_sum`,
  `map_zShearBy_finset_sum` — pushing a subspace by the shear of a sum is a fold of the summands'
  shears.
* `omega_zShearBy`, `isStabilizer_map_zShearBy` — a symmetric pairing gives a symplectic shear
  that carries isotropic subspaces to isotropic subspaces; `omega_zShearBy_of_mem`,
  `isStabilizer_map_zShearBy_of_symm_on` — the same from symmetry on the X-parts moved.
* `isSymmPairing_mulVecLin` — the pairing of a symmetric matrix is symmetric.
* `zShear_eq_zShearBy` — the shear at a bit is the shear by its row, definitionally.
* `zShear_X`, `zShear_Z`, `zShear_reader`, `zShear_zShear`, `omega_zShear`,
  `isStabilizer_map_zShear` — the one-bit shear's lemmas, as instances of the general ones.

## Implementation notes

Symmetry of the pairing is stated as the explicit sum `∑ i, M x i * y i = ∑ i, x i * M y i`
rather than through `Matrix.IsSymm`: the shear is a linear map, and the class rule delivers
symmetry on a subspace, where no matrix statement applies; `isSymmPairing_mulVecLin` is the
bridge from a symmetric matrix. The `𝔽₂` pairing of the one-bit row appears as the explicit sum
`∑ j, d j * x j`; the frame layer's `dotF2` is that sum definitionally, and this module sits below
it. Dimension transport (`finrank`) lives beside its consumer, not here.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli

variable {n : ℕ}

/-! ## The shear by a linear map -/

/-- The Z-shear by the linear map `M` of the X-space: `⟨x, z⟩ ↦ ⟨x, z + M x⟩`. -/
def zShearBy (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Pauli n →ₗ[ZMod 2] Pauli n where
  toFun p := ⟨p.X, p.Z + M p.X⟩
  map_add' p q := by
    ext i
    · rfl
    · change (p + q).Z i + M (p + q).X i = (p.Z i + M p.X i) + (q.Z i + M q.X i)
      rw [Z_add, X_add, map_add, Pi.add_apply, Pi.add_apply]
      ring
  map_smul' c p := by
    ext i
    · rfl
    · change (c • p).Z i + M (c • p).X i = c * (p.Z i + M p.X i)
      rw [Z_smul, X_smul, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring

/-- The shear fixes the X-part. -/
@[simp] theorem zShearBy_X (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : Pauli n) :
    (zShearBy M p).X = p.X := rfl

/-- The shear adds `M` of the X-part to the Z-part. -/
theorem zShearBy_Z (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : Pauli n) :
    (zShearBy M p).Z = p.Z + M p.X := rfl

/-- The shear is an involution. -/
theorem zShearBy_zShearBy (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : Pauli n) :
    zShearBy M (zShearBy M p) = p := by
  have h2 : ∀ a b : ZMod 2, a + b + b = a := by decide
  ext i
  · rfl
  · rw [zShearBy_Z, zShearBy_X, zShearBy_Z, Pi.add_apply, Pi.add_apply, h2]

/-- The shear as a linear equivalence. -/
noncomputable def zShearByEquiv (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Pauli n ≃ₗ[ZMod 2] Pauli n :=
  LinearEquiv.ofInvolutive (zShearBy M) (zShearBy_zShearBy M)

/-- **The group law**: the shear by a sum of maps is the composite of the shears. -/
theorem zShearBy_add (M N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : Pauli n) :
    zShearBy (M + N) p = zShearBy M (zShearBy N p) := by
  ext i
  · rfl
  · simp only [zShearBy_Z, zShearBy_X, LinearMap.add_apply, Pi.add_apply]
    ring

/-- The shear by the zero map is the identity. -/
theorem zShearBy_zero :
    zShearBy (0 : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  ext i
  · rfl
  · rw [zShearBy_Z, LinearMap.zero_apply, add_zero]
    rfl

/-- Pushing a subspace by the shear of a sum is pushing it by the two shears in turn. -/
theorem map_zShearBy_add (M N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map (zShearBy (M + N)) L =
      Submodule.map (zShearBy N) (Submodule.map (zShearBy M) L) := by
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro p
  rw [LinearMap.comp_apply, add_comm]
  exact zShearBy_add N M p

/-- **The fold.** The shear by a list's sum pushes a subspace by the list's shears in turn. -/
theorem map_zShearBy_list_sum (Ms : List ((Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))
    (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map (zShearBy Ms.sum) L =
      Ms.foldl (fun L' M => Submodule.map (zShearBy M) L') L := by
  induction Ms generalizing L with
  | nil => rw [List.sum_nil, zShearBy_zero, Submodule.map_id, List.foldl_nil]
  | cons M Ms ih => rw [List.sum_cons, map_zShearBy_add, ih, List.foldl_cons]

/-- The fold over a finite set of maps, in the order of its list. -/
theorem map_zShearBy_finset_sum {ι : Type*} (s : Finset ι)
    (M : ι → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map (zShearBy (∑ p ∈ s, M p)) L =
      s.toList.foldl (fun L' p => Submodule.map (zShearBy (M p)) L') L := by
  rw [← Finset.sum_map_toList, map_zShearBy_list_sum, List.foldl_map]

/-! ## The shear is symplectic when its pairing is symmetric -/

/-- The pairing of `M`, `(x, y) ↦ ∑ i, M x i * y i`, is symmetric on the vectors of `V`. -/
def IsSymmPairingOn (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, (∑ i, M x i * y i) = ∑ i, x i * M y i

/-- The pairing of `M` is symmetric. -/
def IsSymmPairing (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) : Prop :=
  ∀ x y : Fin n → ZMod 2, (∑ i, M x i * y i) = ∑ i, x i * M y i

/-- A symmetric pairing is symmetric on every subspace. -/
theorem IsSymmPairing.on {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)}
    (hM : IsSymmPairing M) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : IsSymmPairingOn M V :=
  fun x _ y _ => hM x y

/-- The computation behind symplecticity: when the pairing agrees on the two X-parts, the shear
preserves `ω` on the pair — the added terms sum to twice the pairing, which vanishes. -/
theorem omega_zShearBy_of_eq {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)} {p q : Pauli n}
    (h : (∑ i, M p.X i * q.X i) = ∑ i, p.X i * M q.X i) :
    omega (zShearBy M p) (zShearBy M q) = omega p q := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  unfold omega
  simp only [zShearBy_X, zShearBy_Z, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  linear_combination h + (∑ i, p.X i * M q.X i) * h2

/-- The shear by a symmetric pairing preserves `ω`. -/
theorem omega_zShearBy {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)} (hM : IsSymmPairing M)
    (p q : Pauli n) : omega (zShearBy M p) (zShearBy M q) = omega p q :=
  omega_zShearBy_of_eq (hM p.X q.X)

/-- The shear preserves `ω` on a pair whose X-parts lie where the pairing is symmetric. -/
theorem omega_zShearBy_of_mem {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)}
    {V : Submodule (ZMod 2) (Fin n → ZMod 2)} (hM : IsSymmPairingOn M V) {p q : Pauli n}
    (hp : p.X ∈ V) (hq : q.X ∈ V) : omega (zShearBy M p) (zShearBy M q) = omega p q :=
  omega_zShearBy_of_eq (hM p.X hp q.X hq)

/-- **The on-shadow form.** A shear whose pairing is symmetric on the X-parts of an isotropic
subspace carries it to an isotropic subspace. -/
theorem isStabilizer_map_zShearBy_of_symm_on {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)}
    {V : Submodule (ZMod 2) (Fin n → ZMod 2)} (hM : IsSymmPairingOn M V)
    {L : Submodule (ZMod 2) (Pauli n)} (hL : ∀ p ∈ L, p.X ∈ V) (hS : IsStabilizer L) :
    IsStabilizer (Submodule.map (zShearBy M) L) := by
  intro p hp q hq
  obtain ⟨p', hp', rfl⟩ := Submodule.mem_map.mp hp
  obtain ⟨q', hq', rfl⟩ := Submodule.mem_map.mp hq
  rw [omega_zShearBy_of_mem hM (hL p' hp') (hL q' hq')]
  exact hS p' hp' q' hq'

/-- The shear by a symmetric pairing carries isotropic subspaces to isotropic subspaces. -/
theorem isStabilizer_map_zShearBy {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)}
    (hM : IsSymmPairing M) {L : Submodule (ZMod 2) (Pauli n)} (hS : IsStabilizer L) :
    IsStabilizer (Submodule.map (zShearBy M) L) :=
  isStabilizer_map_zShearBy_of_symm_on (hM.on ⊤) (fun _ _ => Submodule.mem_top) hS

open Matrix in
/-- The pairing of a symmetric matrix is symmetric. -/
theorem isSymmPairing_mulVecLin {A : Matrix (Fin n) (Fin n) (ZMod 2)} (hA : A.IsSymm) :
    IsSymmPairing (Matrix.mulVecLin A) := by
  intro x y
  change (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y)
  rw [dotProduct_comm (A *ᵥ x) y, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq,
    dotProduct_comm]

/-! ## The row of the shear at a bit -/

/-- The Z-correction of the shear at `k` by `d`: `M x` for `M = d·e_kᵀ + e_k·dᵀ + d_k·E_kk`. -/
def shearRow (k : Fin n) (d x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  (x k) • d + ((∑ j, d j * x j) + d k * x k) • (Pi.single k 1 : Fin n → ZMod 2)

/-- The row is additive. -/
theorem shearRow_add (k : Fin n) (d x y : Fin n → ZMod 2) :
    shearRow k d (x + y) = shearRow k d x + shearRow k d y := by
  funext i
  simp only [shearRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- The row is homogeneous. -/
theorem shearRow_smul (k : Fin n) (d : Fin n → ZMod 2) (c : ZMod 2) (x : Fin n → ZMod 2) :
    shearRow k d (c • x) = c • shearRow k d x := by
  have hs : (∑ j, d j * (c • x) j) = c * ∑ j, d j * x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [Pi.smul_apply, smul_eq_mul]; ring)
  unfold shearRow
  rw [hs]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The row at a reader's X-part `e_k` is `d` itself. -/
theorem shearRow_single (k : Fin n) (d : Fin n → ZMod 2) :
    shearRow k d (Pi.single k 1) = d := by
  have hs : (∑ j, d j * (Pi.single k 1 : Fin n → ZMod 2) j) = d k := by
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  funext i
  simp only [shearRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, Pi.single_eq_same, mul_one]
  rw [one_mul, h2, zero_mul, add_zero]

/-- The row of the zero shear vanishes. -/
theorem shearRow_zero (k : Fin n) (v : Fin n → ZMod 2) : shearRow k 0 v = 0 := by
  unfold shearRow
  simp

/-- The row of the shear `(k, e_k)` at `v` is `v_k·e_k`. -/
theorem shearRow_single_self (k : Fin n) (v : Fin n → ZMod 2) :
    shearRow k (Pi.single k 1) v = (v k) • (Pi.single k 1 : Fin n → ZMod 2) := by
  have hs : (∑ j, (Pi.single k 1 : Fin n → ZMod 2) j * v j) = v k := by
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, one_mul]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  unfold shearRow
  rw [hs, Pi.single_eq_same, one_mul, h2, zero_smul, add_zero]

/-- The row of the shear `(i, e_j)` at `v` is `v_i·e_j + v_j·e_i` (`i ≠ j`). -/
theorem shearRow_single_ne {i j : Fin n} (hij : i ≠ j) (v : Fin n → ZMod 2) :
    shearRow i (Pi.single j 1) v =
      (v i) • (Pi.single j 1 : Fin n → ZMod 2) + (v j) • (Pi.single i 1 : Fin n → ZMod 2) := by
  have hs : (∑ l, (Pi.single j 1 : Fin n → ZMod 2) l * v l) = v j := by
    rw [Finset.sum_eq_single j (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_mul]
  unfold shearRow
  rw [hs, Pi.single_eq_of_ne hij, zero_mul, add_zero]

/-- The pairing of the row against a vector: the symmetric form the shear adds to `ω`. -/
theorem sum_shearRow_mul (k : Fin n) (d x y : Fin n → ZMod 2) :
    (∑ i, shearRow k d x i * y i)
      = x k * (∑ j, d j * y j) + ((∑ j, d j * x j) + d k * x k) * y k := by
  have h1 : (∑ i, (x k • d) i * y i) = x k * ∑ j, d j * y j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [Pi.smul_apply, smul_eq_mul]; ring)
  have h2 : ∀ c : ZMod 2, (∑ i, (c • (Pi.single k 1 : Fin n → ZMod 2)) i * y i) = c * y k := by
    intro c
    rw [Finset.sum_eq_single k
      (fun j _ hj => by rw [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ k) h), Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one]
  unfold shearRow
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [h1, h2]
  ring

/-- The row as a linear map of the X-space. -/
def shearLin (k : Fin n) (d : Fin n → ZMod 2) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun := shearRow k d
  map_add' := shearRow_add k d
  map_smul' := shearRow_smul k d

/-- The linear map is the row. -/
@[simp] theorem shearLin_apply (k : Fin n) (d x : Fin n → ZMod 2) :
    shearLin k d x = shearRow k d x := rfl

/-- The pairing of the row is symmetric: the one-bit shear is symplectic with no hypothesis. -/
theorem isSymmPairing_shearLin (k : Fin n) (d : Fin n → ZMod 2) : IsSymmPairing (shearLin k d) := by
  intro x y
  have hr : (∑ i, x i * shearRow k d y i) = ∑ i, shearRow k d y i * x i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  simp only [shearLin_apply]
  rw [hr, sum_shearRow_mul k d x y, sum_shearRow_mul k d y x]
  ring

/-! ## The shear at a bit -/

/-- The Z-shear at the bit `k` by the vector `d`, the shear by its row:
`⟨x, z⟩ ↦ ⟨x, z + shearRow k d x⟩`. -/
def zShear (k : Fin n) (d : Fin n → ZMod 2) : Pauli n →ₗ[ZMod 2] Pauli n :=
  zShearBy (shearLin k d)

/-- The shear at a bit is the shear by its row, definitionally. -/
theorem zShear_eq_zShearBy (k : Fin n) (d : Fin n → ZMod 2) :
    zShear k d = zShearBy (shearLin k d) := rfl

/-- The shear fixes the X-part. -/
@[simp] theorem zShear_X (k : Fin n) (d : Fin n → ZMod 2) (p : Pauli n) :
    (zShear k d p).X = p.X := rfl

/-- The shear adds the row to the Z-part. -/
theorem zShear_Z (k : Fin n) (d : Fin n → ZMod 2) (p : Pauli n) :
    (zShear k d p).Z = p.Z + shearRow k d p.X := rfl

/-- **On a reader of `k`** (X-part `e_k`) the shear adds exactly `d` to the Z-part. -/
theorem zShear_reader (k : Fin n) (d : Fin n → ZMod 2) {g : Pauli n} (hg : g.X = Pi.single k 1) :
    zShear k d g = ⟨Pi.single k 1, g.Z + d⟩ := by
  ext i
  · rw [zShear_X, hg]
  · rw [zShear_Z, hg, shearRow_single]

/-- The shear is an involution. -/
theorem zShear_zShear (k : Fin n) (d : Fin n → ZMod 2) (p : Pauli n) :
    zShear k d (zShear k d p) = p :=
  zShearBy_zShearBy (shearLin k d) p

/-- The shear as a linear equivalence. -/
noncomputable def zShearEquiv (k : Fin n) (d : Fin n → ZMod 2) : Pauli n ≃ₗ[ZMod 2] Pauli n :=
  LinearEquiv.ofInvolutive (zShear k d) (zShear_zShear k d)

/-- The shear preserves `ω`: the added form is symmetric, and twice anything vanishes. -/
theorem omega_zShear (k : Fin n) (d : Fin n → ZMod 2) (p q : Pauli n) :
    omega (zShear k d p) (zShear k d q) = omega p q :=
  omega_zShearBy (isSymmPairing_shearLin k d) p q

/-- The shear carries isotropic subspaces to isotropic subspaces. -/
theorem isStabilizer_map_zShear (k : Fin n) (d : Fin n → ZMod 2)
    {L : Submodule (ZMod 2) (Pauli n)} (hS : IsStabilizer L) :
    IsStabilizer (Submodule.map (zShear k d) L) :=
  isStabilizer_map_zShearBy (isSymmPairing_shearLin k d) hS

end FTQCLib.Stabilizer
