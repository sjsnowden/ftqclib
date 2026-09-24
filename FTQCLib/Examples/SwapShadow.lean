/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardTotality
import FTQCLib.Pauli.Cocycle
import FTQCLib.Stabilizer.ZShear

/-!
# The X-shadow under the one-bit swap at an X-supported bit, and alignment at a bit

At a bit `k` whose basis vector lies in the X-shadow `V = π_X L` of a subspace `L`, the one-bit
swap `pauliSwapOn {k}` moves the shadow by a rank-one correction read off a *reader* of `k` — an
element of `L` with X-part `e_k`. Two facts decide the eliminating Hadamard's Lagrangian:

* **rotate** — if some reader has Z-entry `1` at `k`, the swapped shadow is `V` itself
  (`mem_xProj_map_pauliSwapOn_iff_of_alignedRotate`); this needs no isotropy;
* **collapse** — if the Pauli `⟨e_k, σ + e_k⟩` lies in `L`, with `σ k = 1` and `ω`-orthogonal to
  `L`, the swapped shadow is `V` cut by the equation `⟨σ, v⟩ = 0`
  (`mem_xProj_map_pauliSwapOn_iff_of_alignedCollapse`).

Both conditions are *alignment at the bit*: a property of `L`'s Z-part on the fibre over `e_k`.
Off the floor it is produced by one Z-shear (`FTQCLib/Stabilizer/ZShear.lean`), which fixes every
shadow (`map_xProj_map_of_X_eq`, `map_xProj_map_zShearBy`, `map_xProj_map_zShear`: any map fixing
the X-parts does) and moves a reader's Z-part to whatever is wanted
(`alignedRotate_map_zShear_of_reader`, `alignedCollapse_map_zShear_of_reader`). On an isotropic
`L` the Z-entry of a reader at `k` is the same for every reader (`reader_Z_eq`).

## Main definitions

* `IsReader L k g` — `g ∈ L` with X-part `e_k`.
* `AlignedRotate L k`, `AlignedCollapse L k σ` — the two alignment conditions at the bit.
* `zPauli σ` — the Z-type Pauli `⟨0, σ⟩` of a datum, the conditioning Pauli of a collapse bit.

## Main results

* `mem_xProj_map_pauliSwapOn_iff_of_alignedRotate`,
  `mem_xProj_map_pauliSwapOn_iff_of_alignedCollapse` — the swapped shadow in the two cases.
* `reader_Z_eq` — the reader's Z-entry at the bit is an invariant of an isotropic `L`.
* `map_xProj_map_of_X_eq`, `map_xProj_map_zShearBy`, `map_xProj_map_zShear`,
  `exists_alignedRotate_map_zShear`, `exists_alignedCollapse_map_zShear` — a map fixing the X-parts
  does not move the shadow; the shear aligns without moving it.
* `map_pauliSwapOn_eq_pauliCondition` — **coherence**: at a collapse-aligned bit of an isotropic
  `L` the swap's image of `L` is `pauliCondition L (zPauli σ)`, the Lagrangian rewrite of
  measurement.

## Implementation notes

`HadamardTotality.lean` carries the swap's shadow at a bit *outside* the shadow (`shadow_swap_eq`,
under co-isotropy); this module is the X-supported case, and it imports that module for
`xProj_pauliSwapOn_singleton`, the `dotF2` calculus and `omega_pureZ` rather than restating them.
The shadow statements are membership equivalences, not submodule equalities: the elimination
certificate consumes the support of the output record pointwise, and the collapse cut is stated
with the pairing `dotF2 σ v` instead of a `LinearMap.ker`. `xProj` here is
`RegisterWalkthrough.lean`'s; `FloorEquivalence.lean`'s `xProjₗ` is the same map under another name.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The pairing on the right -/

/-- `dotF2` is additive on the right. -/
theorem dotF2_add_right (u v v' : Fin n → ZMod 2) :
    dotF2 u (v + v') = dotF2 u v + dotF2 u v' := by
  unfold dotF2
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, mul_add]

/-- `dotF2` is homogeneous on the right. -/
theorem dotF2_smul_right (u : Fin n → ZMod 2) (c : ZMod 2) (v : Fin n → ZMod 2) :
    dotF2 u (c • v) = c * dotF2 u v := by
  unfold dotF2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]; ring

/-- `ω` is the pairing of the Z-part against the X-part, both ways. -/
theorem omega_eq_dotF2 (p q : Pauli n) : omega p q = dotF2 p.Z q.X + dotF2 p.X q.Z := rfl

/-- Twice any word vanishes. -/
theorem add_self_word (w : Fin n → ZMod 2) : w + w = 0 := by
  funext i
  rw [Pi.add_apply, CharTwo.add_self_eq_zero]
  rfl

/-! ## Readers -/

/-- A reader of the bit `k` in `L`: an element with X-part `e_k`. -/
def IsReader (L : Submodule (ZMod 2) (Pauli n)) (k : Fin n) (g : Pauli n) : Prop :=
  g ∈ L ∧ g.X = Pi.single k 1

/-- A reader exists exactly when the bit is X-supported. -/
theorem exists_reader_iff (L : Submodule (ZMod 2) (Pauli n)) (k : Fin n) :
    (∃ g, IsReader L k g) ↔ (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L := by
  constructor
  · rintro ⟨g, hg, hgX⟩
    exact Submodule.mem_map.mpr ⟨g, hg, by rw [xProj_apply, hgX]⟩
  · rintro ⟨g, hg, hgX⟩
    exact ⟨g, hg, by rw [← hgX, xProj_apply]⟩

/-- `ω` of two readers is the sum of their Z-entries at the bit. -/
theorem omega_reader (k : Fin n) {g g' : Pauli n} (hgX : g.X = Pi.single k 1)
    (hg'X : g'.X = Pi.single k 1) : omega g g' = g.Z k + g'.Z k := by
  rw [omega_eq_dotF2, hgX, hg'X, dotF2_single, dotF2_single_left]

/-- **On an isotropic `L` the Z-entry of a reader at the bit is an invariant.** -/
theorem reader_Z_eq {L : Submodule (ZMod 2) (Pauli n)} (hS : IsStabilizer L) {k : Fin n}
    {g g' : Pauli n} (hg : IsReader L k g) (hg' : IsReader L k g') : g.Z k = g'.Z k := by
  have h := hS g hg.1 g' hg'.1
  rw [omega_reader k hg.2 hg'.2] at h
  exact (show ∀ a b : ZMod 2, a + b = 0 → a = b by decide) _ _ h

/-! ## Alignment at the bit -/

/-- Rotate alignment: a reader with Z-entry `1` at the bit. -/
def AlignedRotate (L : Submodule (ZMod 2) (Pauli n)) (k : Fin n) : Prop :=
  ∃ g, IsReader L k g ∧ g.Z k = 1

/-- Collapse alignment at the datum `σ`: the Pauli `⟨e_k, σ + e_k⟩` lies in `L`. -/
def AlignedCollapse (L : Submodule (ZMod 2) (Pauli n)) (k : Fin n) (σ : Fin n → ZMod 2) : Prop :=
  (⟨Pi.single k 1, σ + Pi.single k 1⟩ : Pauli n) ∈ L

/-- Rotate alignment puts the bit in the shadow. -/
theorem single_mem_of_alignedRotate {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n}
    (hal : AlignedRotate L k) : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L :=
  (exists_reader_iff L k).mp ⟨hal.choose, hal.choose_spec.1⟩

/-- Collapse alignment puts the bit in the shadow. -/
theorem single_mem_of_alignedCollapse {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n}
    {σ : Fin n → ZMod 2} (hal : AlignedCollapse L k σ) :
    (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L :=
  Submodule.mem_map.mpr ⟨_, hal, rfl⟩

/-! ## The swapped shadow -/

/-- When the bit is in the shadow, the swap's shadow sits inside the shadow. -/
theorem xProj_pauliSwapOn_mem {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n}
    (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L) {p : Pauli n} (hp : p ∈ L) :
    xProj (pauliSwapOn {k} p) ∈ Submodule.map xProj L := by
  rw [xProj_pauliSwapOn_singleton]
  exact Submodule.add_mem _ (Submodule.mem_map_of_mem hp) (Submodule.smul_mem _ _ hk)

/-- **Rotate.** With an aligned reader the swap's shadow is the shadow. No isotropy is used. -/
theorem mem_xProj_map_pauliSwapOn_iff_of_alignedRotate {L : Submodule (ZMod 2) (Pauli n)}
    {k : Fin n} (hal : AlignedRotate L k) (v : Fin n → ZMod 2) :
    v ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {k}) L) ↔ v ∈ Submodule.map xProj L := by
  obtain ⟨g, ⟨hg, hgX⟩, hgZ⟩ := hal
  have hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L :=
    Submodule.mem_map.mpr ⟨g, hg, by rw [xProj_apply, hgX]⟩
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
    exact xProj_pauliSwapOn_mem hk hp
  · intro hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
    rcases zmod_two_eq_zero_or_one (p.X k + p.Z k) with hc | hc
    · refine Submodule.mem_map.mpr ⟨pauliSwapOn {k} p, Submodule.mem_map_of_mem hp, ?_⟩
      rw [xProj_pauliSwapOn_singleton, hc, zero_smul, add_zero]
    · refine Submodule.mem_map.mpr
        ⟨pauliSwapOn {k} (p + g), Submodule.mem_map_of_mem (Submodule.add_mem _ hp hg), ?_⟩
      have hcoef : (p + g).X k + (p + g).Z k = 1 := by
        rw [X_add, Z_add, Pi.add_apply, Pi.add_apply, hgX, Pi.single_eq_same, hgZ]
        exact (show ∀ a b : ZMod 2, a + b = 1 → a + 1 + (b + 1) = 1 by decide) _ _ hc
      rw [xProj_pauliSwapOn_singleton, hcoef, one_smul]
      simp only [xProj_apply, X_add, hgX]
      rw [add_assoc, add_self_word, add_zero]

/-- **Collapse.** With `⟨e_k, σ + e_k⟩ ∈ L`, `σ k = 1`, and that Pauli `ω`-orthogonal to `L`, the
swap's shadow is the shadow cut by `⟨σ, v⟩ = 0`. -/
theorem mem_xProj_map_pauliSwapOn_iff_of_alignedCollapse {L : Submodule (ZMod 2) (Pauli n)}
    {k : Fin n} {σ : Fin n → ZMod 2} (hal : AlignedCollapse L k σ) (hσ : σ k = 1)
    (horth : ∀ p ∈ L, omega (⟨Pi.single k 1, σ + Pi.single k 1⟩ : Pauli n) p = 0)
    (v : Fin n → ZMod 2) :
    v ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {k}) L)
      ↔ v ∈ Submodule.map xProj L ∧ dotF2 σ v = 0 := by
  have hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L :=
    single_mem_of_alignedCollapse hal
  -- the reader's orthogonality reads the swap's coefficient off `σ`
  have hcoef : ∀ p ∈ L, p.X k + p.Z k = dotF2 σ p.X := by
    intro p hp
    have h := horth p hp
    have hX : (⟨Pi.single k 1, σ + Pi.single k 1⟩ : Pauli n).X = Pi.single k 1 := rfl
    have hZ : (⟨Pi.single k 1, σ + Pi.single k 1⟩ : Pauli n).Z = σ + Pi.single k 1 := rfl
    rw [omega_eq_dotF2, hX, hZ, dotF2_add_left, dotF2_single_left, dotF2_single_left] at h
    exact (show ∀ a b c : ZMod 2, a + b + c = 0 → b + c = a by decide) _ _ _ h
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
    refine ⟨xProj_pauliSwapOn_mem hk hp, ?_⟩
    rw [xProj_pauliSwapOn_singleton, hcoef p hp, dotF2_add_right, dotF2_smul_right, dotF2_single,
      hσ, mul_one, xProj_apply, CharTwo.add_self_eq_zero]
  · rintro ⟨hv, hσv⟩
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨pauliSwapOn {k} p, Submodule.mem_map_of_mem hp, ?_⟩
    rw [xProj_apply] at hσv
    rw [xProj_pauliSwapOn_singleton, hcoef p hp, hσv, zero_smul, add_zero]

/-! ## Alignment by a shear -/

/-- A linear map that fixes every X-part does not move the shadow. -/
theorem map_xProj_map_of_X_eq (f : Pauli n →ₗ[ZMod 2] Pauli n) (hf : ∀ p, (f p).X = p.X)
    (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map xProj (Submodule.map f L) = Submodule.map xProj L := by
  ext v
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
    exact Submodule.mem_map.mpr ⟨p, hp, by rw [xProj_apply, xProj_apply, hf]⟩
  · intro hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr
      ⟨f p, Submodule.mem_map_of_mem hp, by rw [xProj_apply, xProj_apply, hf]⟩

/-- The shear by a linear map does not move the shadow. -/
theorem map_xProj_map_zShearBy (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map xProj (Submodule.map (zShearBy M) L) = Submodule.map xProj L :=
  map_xProj_map_of_X_eq _ (zShearBy_X M) L

/-- The shear at a bit does not move the shadow. -/
theorem map_xProj_map_zShear (k : Fin n) (d : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map xProj (Submodule.map (zShear k d) L) = Submodule.map xProj L :=
  map_xProj_map_of_X_eq _ (zShear_X k d) L

/-- A reader survives a shear as a reader. -/
theorem isReader_map_zShear {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n} (d : Fin n → ZMod 2)
    {g : Pauli n} (hg : IsReader L k g) :
    IsReader (Submodule.map (zShear k d) L) k (zShear k d g) :=
  ⟨Submodule.mem_map_of_mem hg.1, by rw [zShear_X, hg.2]⟩

/-- **Rotate alignment by a shear.** The shear by `(1 + g.Z k)•e_k` makes the reader `g` aligned. -/
theorem alignedRotate_map_zShear_of_reader {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n}
    {g : Pauli n} (hg : IsReader L k g) :
    AlignedRotate (Submodule.map (zShear k ((1 + g.Z k) • Pi.single k 1)) L) k := by
  refine ⟨zShear k ((1 + g.Z k) • Pi.single k 1) g, isReader_map_zShear _ hg, ?_⟩
  rw [zShear_reader _ _ hg.2]
  change g.Z k + ((1 + g.Z k) • (Pi.single k 1 : Fin n → ZMod 2)) k = 1
  rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  exact (show ∀ a : ZMod 2, a + (1 + a) = 1 by decide) _

/-- **Collapse alignment by a shear.** The shear by `g.Z + σ + e_k` makes the reader `g` the Pauli
`⟨e_k, σ + e_k⟩`. -/
theorem alignedCollapse_map_zShear_of_reader {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n}
    {g : Pauli n} (hg : IsReader L k g) (σ : Fin n → ZMod 2) :
    AlignedCollapse (Submodule.map (zShear k (g.Z + σ + Pi.single k 1)) L) k σ := by
  unfold AlignedCollapse
  have h : zShear k (g.Z + σ + Pi.single k 1) g
      = (⟨Pi.single k 1, σ + Pi.single k 1⟩ : Pauli n) := by
    rw [zShear_reader _ _ hg.2]
    congr 1
    rw [← add_assoc, ← add_assoc, add_self_word, zero_add]
  rw [← h]
  exact Submodule.mem_map_of_mem hg.1

/-- At an X-supported bit some shear aligns for rotate. -/
theorem exists_alignedRotate_map_zShear {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n}
    (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L) :
    ∃ d, AlignedRotate (Submodule.map (zShear k d) L) k := by
  obtain ⟨g, hg⟩ := (exists_reader_iff L k).mpr hk
  exact ⟨_, alignedRotate_map_zShear_of_reader hg⟩

/-- At an X-supported bit some shear aligns for collapse at any datum. -/
theorem exists_alignedCollapse_map_zShear {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n}
    (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj L) (σ : Fin n → ZMod 2) :
    ∃ d, AlignedCollapse (Submodule.map (zShear k d) L) k σ := by
  obtain ⟨g, hg⟩ := (exists_reader_iff L k).mpr hk
  exact ⟨_, alignedCollapse_map_zShear_of_reader hg σ⟩

/-- On an isotropic `L`, collapse alignment gives the orthogonality the collapse shadow theorem
consumes. -/
theorem orth_of_alignedCollapse {L : Submodule (ZMod 2) (Pauli n)} (hS : IsStabilizer L)
    {k : Fin n} {σ : Fin n → ZMod 2} (hal : AlignedCollapse L k σ) :
    ∀ p ∈ L, omega (⟨Pi.single k 1, σ + Pi.single k 1⟩ : Pauli n) p = 0 :=
  fun p hp => hS _ hal p hp

/-! ## The coherence identity: the collapse swap is a Pauli conditioning

At a collapse-aligned bit the swap's image of `L` is the Pauli conditioning of `L` by `Z^σ`
(`pauliCondition`, the Lagrangian rewrite of measurement): at a collapse bit the eliminating H
rewrites the Lagrangian exactly as conditioning on the datum's Z-Pauli does. The scale `√2` and the
absence of a Born weight are the only differences, and both live in `c`, not in `L`. -/

/-- The Z-type Pauli of a datum, `Z^σ = ⟨0, σ⟩`. -/
def zPauli (σ : Fin n → ZMod 2) : Pauli n := ⟨0, σ⟩

@[simp] theorem zPauli_X (σ : Fin n → ZMod 2) : (zPauli σ).X = 0 := rfl

@[simp] theorem zPauli_Z (σ : Fin n → ZMod 2) : (zPauli σ).Z = σ := rfl

/-- `⟨u, v⟩ = ⟨v, u⟩`. -/
theorem dotF2_comm (u v : Fin n → ZMod 2) : dotF2 u v = dotF2 v u := by
  unfold dotF2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `ω(Z^σ, p) = ⟨σ, p.X⟩`. -/
theorem omega_zPauli (σ : Fin n → ZMod 2) (p : Pauli n) : omega (zPauli σ) p = dotF2 σ p.X := by
  rw [omega_eq_dotF2, zPauli_Z, zPauli_X]
  simp only [dotF2, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- The swap at `k` fixes a Pauli whose two entries at `k` agree. -/
theorem pauliSwapOn_singleton_eq_self {k : Fin n} {p : Pauli n} (h : p.X k = p.Z k) :
    pauliSwapOn {k} p = p := by
  ext i
  · rw [pauliSwapOn_X]
    split_ifs with hi
    · rw [Finset.mem_singleton.mp hi, h]
    · rfl
  · rw [pauliSwapOn_Z]
    split_ifs with hi
    · rw [Finset.mem_singleton.mp hi, h]
    · rfl

/-- The swap at `k` carries the collapse reader `⟨e_k, σ + e_k⟩` (with `σ k = 1`) to `Z^σ`. -/
theorem pauliSwapOn_reader_eq_zPauli {k : Fin n} {σ : Fin n → ZMod 2} (hk : σ k = 1) :
    pauliSwapOn {k} (⟨Pi.single k 1, σ + Pi.single k 1⟩ : Pauli n) = zPauli σ := by
  ext i
  · rw [pauliSwapOn_X, zPauli_X, Pi.zero_apply]
    split_ifs with hi
    · rw [Finset.mem_singleton.mp hi]
      change σ k + (Pi.single k 1 : Fin n → ZMod 2) k = 0
      rw [Pi.single_eq_same, hk]
      decide
    · have hik : i ≠ k := fun h => hi (Finset.mem_singleton.mpr h)
      change (Pi.single k 1 : Fin n → ZMod 2) i = 0
      rw [Pi.single_eq_of_ne hik]
  · rw [pauliSwapOn_Z, zPauli_Z]
    split_ifs with hi
    · rw [Finset.mem_singleton.mp hi]
      change (Pi.single k 1 : Fin n → ZMod 2) k = σ k
      rw [Pi.single_eq_same, hk]
    · have hik : i ≠ k := fun h => hi (Finset.mem_singleton.mpr h)
      change σ i + (Pi.single k 1 : Fin n → ZMod 2) i = σ i
      rw [Pi.single_eq_of_ne hik, add_zero]

/-- **Coherence: the collapse swap is a Pauli conditioning.** On an isotropic `L`, at a bit `k`
collapse-aligned at the datum `σ` with `σ k = 1`, the swap's image of `L` is the conditioning of `L`
by `Z^σ`: the reader `⟨e_k, σ + e_k⟩` goes to `Z^σ`, every element of `L` commuting with `Z^σ` is
fixed by the swap, and every other element is such a fixed element plus the reader. -/
theorem map_pauliSwapOn_eq_pauliCondition {L : Submodule (ZMod 2) (Pauli n)} (hS : IsStabilizer L)
    {k : Fin n} {σ : Fin n → ZMod 2} (hal : AlignedCollapse L k σ) (hk : σ k = 1) :
    Submodule.map (pauliSwapOn {k}) L = pauliCondition L (zPauli σ) := by
  set g : Pauli n := ⟨Pi.single k 1, σ + Pi.single k 1⟩ with hg
  have hgX : g.X = Pi.single k 1 := rfl
  have hgZ : g.Z = σ + Pi.single k 1 := rfl
  have hgL : g ∈ L := hal
  -- `ω(Z^σ, g) = σ k = 1`: the conditioning Pauli is not in `L`
  have hQ : zPauli σ ∉ L := fun hQL => by
    have h0 := hS _ hQL g hgL
    rw [omega_zPauli, hgX, dotF2_single, hk] at h0
    exact one_ne_zero h0
  -- on `L`, `⟨σ, p.X⟩ = p.X k + p.Z k`
  have key : ∀ p ∈ L, dotF2 σ p.X = p.X k + p.Z k := by
    intro p hp
    have h0 := hS p hp g hgL
    rw [omega_eq_dotF2, hgX, hgZ, dotF2_single, dotF2_add_right, dotF2_single, dotF2_comm] at h0
    exact (show ∀ a b c : ZMod 2, c + (a + b) = 0 → a = b + c by decide) _ _ _ h0
  -- the elements fixed by the swap are the kept slice `L ⊓ (Z^σ)^⊥`
  have mem_slice : ∀ p ∈ L, p.X k = p.Z k →
      p ∈ L ⊓ LinearMap.BilinForm.orthogonal omegaBilin (Submodule.span (ZMod 2) {zPauli σ}) := by
    intro p hp hpk
    refine Submodule.mem_inf.mpr ⟨hp, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro q hq
    rw [Submodule.mem_span_singleton] at hq
    obtain ⟨c, rfl⟩ := hq
    change omega (c • zPauli σ) p = 0
    rw [omega_smul_left, omega_zPauli, key p hp, hpk,
      show p.Z k + p.Z k = 0 from (by decide : ∀ a : ZMod 2, a + a = 0) _, mul_zero]
  rw [pauliCondition_of_not_mem hQ]
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro p hp
    rw [Submodule.mem_comap]
    by_cases hpk : p.X k = p.Z k
    · rw [pauliSwapOn_singleton_eq_self hpk]
      exact Submodule.mem_sup_left (mem_slice p hp hpk)
    · have hpg : (p + g).X k = (p + g).Z k := by
        rw [X_add, Z_add, Pi.add_apply, Pi.add_apply, hgX, hgZ, Pi.add_apply, Pi.single_eq_same, hk]
        exact (show ∀ a b : ZMod 2, ¬ a = b → a + 1 = b + (1 + 1) by decide) _ _ hpk
      have h1 : pauliSwapOn {k} p + zPauli σ = p + g := by
        rw [← pauliSwapOn_reader_eq_zPauli hk, ← hg, ← map_add, pauliSwapOn_singleton_eq_self hpg]
      have hswap : pauliSwapOn {k} p = (p + g) + zPauli σ := by
        rw [← h1, add_assoc, pauli_add_self, add_zero]
      rw [hswap]
      exact Submodule.add_mem_sup (mem_slice _ (L.add_mem hp hgL) hpg)
        (Submodule.mem_span_singleton_self _)
  · apply sup_le
    · intro p hp
      obtain ⟨hpL, hpO⟩ := Submodule.mem_inf.mp hp
      have hω : omega (zPauli σ) p = 0 :=
        LinearMap.BilinForm.mem_orthogonal_iff.mp hpO _ (Submodule.mem_span_singleton_self _)
      rw [omega_zPauli, key p hpL] at hω
      exact Submodule.mem_map.mpr ⟨p, hpL, pauliSwapOn_singleton_eq_self
        ((show ∀ a b : ZMod 2, a + b = 0 → a = b by decide) _ _ hω)⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.mem_map.mpr ⟨g, hgL, pauliSwapOn_reader_eq_zPauli hk⟩

end FTQCLib.Frame.Walkthrough
