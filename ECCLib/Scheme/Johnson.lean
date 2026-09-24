/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.OrbitalSpectrum
import ECCLib.SubsetProfile
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# The Johnson scheme

The `k`-subsets of an `n`-set, acted on by all permutations. Two ordered pairs of `k`-subsets lie
in the same orbital exactly when their intersections have the same size — so the orbitals are the
level sets of a single invariant, and the scheme's whole combinatorial structure is that one fact.

## Main results

* `mem_orbit_iff_interCard_eq` — the classification, **unconditional** in `n` and `k`.
* `isSelfPaired_kSub` — Johnson is self-paired, so its commutativity is *discharged*, not assumed.
* `card_orbits_kSub` — the orbital count, `min k (n − k) + 1` under `k ≤ n`.
* `card_orbits_finset_kSub` — the same count in the library's computable `orbits` form.

## What is proved here versus assumed

Self-pairing is **derived** from `swap_mem_orbit`: swapping a pair of `k`-subsets preserves the
intersection size, so the swapped pair is in the same orbital. That means the spectral layer's
commutativity hypothesis is discharged at Johnson rather than carried, and everything from
`Scheme/OrbitalSpectrum.lean` applies.

## On the carrier

Mathlib ships the `k`-subset action already, as `Set.powersetCard.subMulAction` with its
`MulAction` instance and pretransitivity. This file nonetheless keeps its own subtype carrier and
bridges to Mathlib's with `carrierEquiv`, for one measured reason: **the `Set.powersetCard`
carrier does not kernel-reduce**, while the `powersetCard`-`Finset` subtype decides at every size
tried. Witness rows need the latter. The bridge means no theorem is proved twice.

## The counting argument

The classification gives injectivity of `orbit ↦ interCard`. The count additionally needs the
range: for each admissible `t`, a pair meeting in exactly `t` points. Those are built by
extracting three pairwise-disjoint blocks — `D` of size `2k − t`, then `A ⊆ D` of size `t`, then
`B ⊆ D \ A` of size `k − t`, with `C = (D \ A) \ B` — and taking `x = A ∪ B`, `y = A ∪ C`. No
`Fin` index is ever named, and the guard is spent exactly once, at the extraction of `D`.

The guard is stated as `2 * k ≤ n + t` rather than `2 * k - t ≤ n`: the same content, but it keeps
truncated subtraction out of every downstream `omega`.

## Implementation notes

`KSub` is an `abbrev`, not a `def`, so that `Fintype`, `DecidableEq` and the product instances are
found without help.

No formalization of the Johnson scheme was located in Mathlib v4.29.1.
-/

namespace ECCLib.Scheme

namespace Johnson

open Finset


/-- Given two maps out of a finite type whose fibers have equal cardinalities, a permutation
of the source carrying one map to the other. -/
theorem exists_perm_comp_eq_of_natCard_fiber_eq {α β : Type*} [Finite α] {f g : α → β}
    (h : ∀ b, Nat.card {a // f a = b} = Nat.card {a // g a = b}) :
    ∃ σ : Equiv.Perm α, ∀ a, g (σ a) = f a :=
  ⟨Equiv.ofFiberEquiv fun b => (Finite.card_eq.mp (h b)).some,
    fun a => Equiv.ofFiberEquiv_map _ a⟩

/-- The `k`-subsets of `Fin n`. -/
abbrev KSub (n k : ℕ) := {S : Finset (Fin n) // S ∈ Finset.univ.powersetCard k}

variable {n k : ℕ}

namespace KSub

theorem card_val (x : KSub n k) : x.1.card = k := (Finset.mem_powersetCard.mp x.2).2

/-- Conversely to `nonempty` below, an inhabited carrier forces `k ≤ n`: a witness is a
`k`-subset of an `n`-set. Together they make `[Nonempty (KSub n k)]` the exact carrier-level
form of the guard `k ≤ n`. -/
theorem k_le_of_nonempty [hne : Nonempty (KSub n k)] : k ≤ n := by
  obtain ⟨x⟩ := hne
  have h1 := Finset.card_le_card (Finset.subset_univ x.1)
  rwa [card_val, Finset.card_univ, Fintype.card_fin] at h1

/-- The carrier is nonempty exactly when a `k`-subset exists, i.e. when `k ≤ n`. This is what
discharges `Nonempty X` — and through it the spectrum's nonemptiness — at every Johnson
instantiation of the spectral layer. -/
theorem nonempty (h : k ≤ n) : Nonempty (KSub n k) := by
  have hne : (Finset.univ.powersetCard k : Finset (Finset (Fin n))).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simpa using h
  exact ⟨⟨hne.choose, hne.choose_spec⟩⟩

instance : SMul (Equiv.Perm (Fin n)) (KSub n k) :=
  ⟨fun σ x => ⟨x.1.map σ.toEmbedding, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, by rw [Finset.card_map, card_val]⟩⟩⟩

@[simp] theorem val_smul (σ : Equiv.Perm (Fin n)) (x : KSub n k) :
    (σ • x).1 = x.1.map σ.toEmbedding := rfl

@[simp] theorem mem_smul_iff {σ : Equiv.Perm (Fin n)} {x : KSub n k} {a : Fin n} :
    a ∈ (σ • x).1 ↔ σ.symm a ∈ x.1 := by
  rw [val_smul, Finset.mem_map_equiv]

instance : MulAction (Equiv.Perm (Fin n)) (KSub n k) where
  one_smul x := Subtype.ext (Finset.ext fun a => by simp)
  mul_smul σ τ x := Subtype.ext (Finset.ext fun a => by
    simp only [mem_smul_iff, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.mul_apply])

end KSub

/-- The Johnson invariant of an ordered pair of `k`-subsets: the size of the intersection. -/
def interCard (p : KSub n k × KSub n k) : ℕ := (p.1.1 ∩ p.2.1).card

/-- Invariance: the intersection size is constant on orbits.  (The easy direction.) -/
theorem interCard_smul (σ : Equiv.Perm (Fin n)) (p : KSub n k × KSub n k) :
    interCard (σ • p) = interCard p := by
  have : ((σ • p).1.1 ∩ (σ • p).2.1) = (p.1.1 ∩ p.2.1).map σ.toEmbedding := by
    rw [Prod.smul_fst, Prod.smul_snd, KSub.val_smul, KSub.val_smul, Finset.map_inter]
  rw [interCard, interCard, this, Finset.card_map]

/-- The four-block indicator of an ordered pair of subsets: which of the two sets `a` lies in. -/
def blockMap (p : KSub n k × KSub n k) (a : Fin n) : Bool × Bool :=
  (decide (a ∈ p.1.1), decide (a ∈ p.2.1))

theorem natCard_fiber_blockMap (p : KSub n k × KSub n k) (b : Bool × Bool) :
    Nat.card {a // blockMap p a = b} = (univ.filter fun a => blockMap p a = b).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem filter_blockMap_tt (p : KSub n k × KSub n k) :
    (univ.filter fun a => blockMap p a = (true, true)) = p.1.1 ∩ p.2.1 := by
  ext a; simp [blockMap, Prod.ext_iff]

theorem filter_blockMap_tf (p : KSub n k × KSub n k) :
    (univ.filter fun a => blockMap p a = (true, false)) = p.1.1 \ p.2.1 := by
  ext a; simp [blockMap, Prod.ext_iff]

theorem filter_blockMap_ft (p : KSub n k × KSub n k) :
    (univ.filter fun a => blockMap p a = (false, true)) = p.2.1 \ p.1.1 := by
  ext a; simp [blockMap, Prod.ext_iff, and_comm]

theorem filter_blockMap_ff (p : KSub n k × KSub n k) :
    (univ.filter fun a => blockMap p a = (false, false)) = (p.1.1 ∪ p.2.1)ᶜ := by
  ext a; simp [blockMap, Prod.ext_iff]

/-- Equal intersection size forces all four block sizes to agree. -/
theorem natCard_fiber_blockMap_eq {p q : KSub n k × KSub n k} (h : interCard q = interCard p)
    (b : Bool × Bool) :
    Nat.card {a // blockMap p a = b} = Nat.card {a // blockMap q a = b} := by
  have hp1 : p.1.1.card = k := KSub.card_val _
  have hp2 : p.2.1.card = k := KSub.card_val _
  have hq1 : q.1.1.card = k := KSub.card_val _
  have hq2 : q.2.1.card = k := KSub.card_val _
  have hint : (p.1.1 ∩ p.2.1).card = (q.1.1 ∩ q.2.1).card := h.symm
  -- the two sdiff blocks
  have hsd1 : (p.1.1 \ p.2.1).card = (q.1.1 \ q.2.1).card := by
    have e1 := Finset.card_sdiff_add_card_inter p.1.1 p.2.1
    have e2 := Finset.card_sdiff_add_card_inter q.1.1 q.2.1
    omega
  have hsd2 : (p.2.1 \ p.1.1).card = (q.2.1 \ q.1.1).card := by
    have e1 := Finset.card_sdiff_add_card_inter p.2.1 p.1.1
    have e2 := Finset.card_sdiff_add_card_inter q.2.1 q.1.1
    have c1 : (p.2.1 ∩ p.1.1).card = (p.1.1 ∩ p.2.1).card := by rw [Finset.inter_comm]
    have c2 : (q.2.1 ∩ q.1.1).card = (q.1.1 ∩ q.2.1).card := by rw [Finset.inter_comm]
    omega
  -- the outside block
  have hun : (p.1.1 ∪ p.2.1).card = (q.1.1 ∪ q.2.1).card := by
    have e1 := Finset.card_union_add_card_inter p.1.1 p.2.1
    have e2 := Finset.card_union_add_card_inter q.1.1 q.2.1
    omega
  have hcompl : ((p.1.1 ∪ p.2.1)ᶜ).card = ((q.1.1 ∪ q.2.1)ᶜ).card := by
    rw [Finset.card_compl, Finset.card_compl, hun]
  rw [natCard_fiber_blockMap, natCard_fiber_blockMap]
  obtain ⟨b1, b2⟩ := b
  cases b1 <;> cases b2
  · rw [filter_blockMap_ff, filter_blockMap_ff]; exact hcompl
  · rw [filter_blockMap_ft, filter_blockMap_ft]; exact hsd2
  · rw [filter_blockMap_tf, filter_blockMap_tf]; exact hsd1
  · rw [filter_blockMap_tt, filter_blockMap_tt]; exact hint

/-- **The Johnson orbital classification.**  Two ordered pairs of `k`-subsets of `Fin n` lie in
the same orbit of the diagonal relabelling action exactly when their intersections have the
same size. -/
theorem mem_orbit_iff_interCard_eq (p q : KSub n k × KSub n k) :
    q ∈ MulAction.orbit (Equiv.Perm (Fin n)) p ↔ interCard q = interCard p := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact interCard_smul σ p
  · intro h
    obtain ⟨σ, hσ⟩ := exists_perm_comp_eq_of_natCard_fiber_eq (natCard_fiber_blockMap_eq h)
    refine MulAction.mem_orbit_iff.mpr ⟨σ, Prod.ext (Subtype.ext (Finset.ext fun a => ?_))
      (Subtype.ext (Finset.ext fun a => ?_))⟩
    · have hb := congrArg Prod.fst (hσ (σ.symm a))
      simp only [Equiv.apply_symm_apply, blockMap] at hb
      rw [Prod.smul_fst, KSub.mem_smul_iff, ← decide_eq_decide]
      exact hb.symm
    · have hb := congrArg Prod.snd (hσ (σ.symm a))
      simp only [Equiv.apply_symm_apply, blockMap] at hb
      rw [Prod.smul_snd, KSub.mem_smul_iff, ← decide_eq_decide]
      exact hb.symm

/-- Transitivity form: `S_n` is transitive on ordered pairs of `k`-subsets with a prescribed
intersection size. -/
theorem exists_smul_eq_of_interCard_eq {x y x' y' : KSub n k}
    (h : (x'.1 ∩ y'.1).card = (x.1 ∩ y.1).card) :
    ∃ σ : Equiv.Perm (Fin n), σ • x = x' ∧ σ • y = y' := by
  obtain ⟨σ, hσ⟩ := (mem_orbit_iff_interCard_eq (x, y) (x', y')).mpr h
  exact ⟨σ, congrArg Prod.fst hσ, congrArg Prod.snd hσ⟩

/-- Every Johnson orbital is self-paired: swapping the two coordinates stays inside the orbit.
This is the hypothesis the symmetry/commutativity argument for the commutant consumes. -/
theorem swap_mem_orbit (p : KSub n k × KSub n k) :
    p.swap ∈ MulAction.orbit (Equiv.Perm (Fin n)) p := by
  rw [mem_orbit_iff_interCard_eq]
  simp [interCard, Finset.inter_comm]

/-- Orbit-equality form of the classification. -/
theorem orbit_eq_orbit_iff_interCard_eq (p q : KSub n k × KSub n k) :
    MulAction.orbit (Equiv.Perm (Fin n)) p = MulAction.orbit (Equiv.Perm (Fin n)) q ↔
      interCard p = interCard q := by
  rw [MulAction.orbit_eq_iff, mem_orbit_iff_interCard_eq]

/-! ### The range step and the orbital count -/

/-- **Range step.** Every admissible intersection size `t` is realised by an explicit pair of
`k`-subsets of `Fin n`.  The guard `2 * k ≤ n + t` is the untruncated form of `2k - t ≤ n`. -/
theorem exists_interCard_eq {n k t : ℕ} (htk : t ≤ k) (hn : 2 * k ≤ n + t) :
    ∃ p : KSub n k × KSub n k, interCard p = t := by
  have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
  obtain ⟨D, -, hD⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := 2 * k - t)
      (by rw [huniv]; omega)
  obtain ⟨A, hAD, hA⟩ := Finset.exists_subset_card_eq (s := D) (n := t) (by omega)
  have hDA : (D \ A).card = 2 * (k - t) := by
    rw [Finset.card_sdiff_of_subset hAD, hD, hA]; omega
  obtain ⟨B, hBDA, hB⟩ := Finset.exists_subset_card_eq (s := D \ A) (n := k - t) (by omega)
  have hCsub : (D \ A) \ B ⊆ D \ A := Finset.sdiff_subset
  have hCc : ((D \ A) \ B).card = k - t := by
    rw [Finset.card_sdiff_of_subset hBDA, hDA, hB]; omega
  have hAB : Disjoint A B :=
    Finset.disjoint_right.mpr fun a ha => (Finset.mem_sdiff.mp (hBDA ha)).2
  have hAC : Disjoint A ((D \ A) \ B) :=
    Finset.disjoint_right.mpr fun a ha => (Finset.mem_sdiff.mp (hCsub ha)).2
  have hBC : Disjoint B ((D \ A) \ B) :=
    Finset.disjoint_right.mpr fun a ha => (Finset.mem_sdiff.mp ha).2
  refine ⟨(⟨A ∪ B, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩⟩,
           ⟨A ∪ ((D \ A) \ B), Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩⟩), ?_⟩
  · rw [Finset.card_union_of_disjoint hAB, hA, hB]; omega
  · rw [Finset.card_union_of_disjoint hAC, hA, hCc]; omega
  · change ((A ∪ B) ∩ (A ∪ ((D \ A) \ B))).card = t
    rw [← Finset.union_inter_distrib_left, Finset.disjoint_iff_inter_eq_empty.mp hBC,
      Finset.union_empty, hA]

/-- Upper bound on the Johnson invariant. -/
theorem interCard_le_k {n k : ℕ} (p : KSub n k × KSub n k) : interCard p ≤ k := by
  have h : (p.1.1 ∩ p.2.1).card ≤ p.1.1.card := Finset.card_le_card Finset.inter_subset_left
  rw [KSub.card_val] at h
  exact h

/-- Lower bound on the Johnson invariant, in untruncated form. -/
theorem two_mul_le_add_interCard {n k : ℕ} (p : KSub n k × KSub n k) :
    2 * k ≤ n + interCard p := by
  have h1 := Finset.card_union_add_card_inter p.1.1 p.2.1
  have h2 : (p.1.1 ∪ p.2.1).card ≤ n := by
    simpa using Finset.card_le_univ (p.1.1 ∪ p.2.1)
  rw [KSub.card_val, KSub.card_val] at h1
  have h3 : interCard p = (p.1.1 ∩ p.2.1).card := rfl
  omega

/-- **The Johnson orbital count.** -/
theorem card_orbits_kSub {n k : ℕ} (h : k ≤ n) :
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (KSub n k × KSub n k))
      = min k (n - k) + 1 := by
  have key : ∀ i : Fin (min k (n - k) + 1),
      ∃ p : KSub n k × KSub n k, interCard p = (k - min k (n - k)) + i.1 := by
    intro i
    have hi : i.1 < min k (n - k) + 1 := i.2
    exact exists_interCard_eq (by omega) (by omega)
  choose w hw using key
  have hbij : Function.Bijective
      (fun i : Fin (min k (n - k) + 1) =>
        (Quotient.mk'' (w i) : MulAction.orbitRel.Quotient (Equiv.Perm (Fin n))
          (KSub n k × KSub n k))) := by
    constructor
    · intro i j hij
      have h1 : w i ∈ MulAction.orbit (Equiv.Perm (Fin n)) (w j) :=
        MulAction.orbitRel.Quotient.mem_orbit.mpr hij
      have h2 := (mem_orbit_iff_interCard_eq (w j) (w i)).mp h1
      rw [hw i, hw j] at h2
      exact Fin.ext (by omega)
    · intro x
      refine Quotient.inductionOn' x ?_
      intro p
      have hle := interCard_le_k p
      have hge := two_mul_le_add_interCard p
      have hmem : w ⟨interCard p - (k - min k (n - k)), by omega⟩ ∈
          MulAction.orbit (Equiv.Perm (Fin n)) p := by
        rw [mem_orbit_iff_interCard_eq, hw]
        change k - min k (n - k) + (interCard p - (k - min k (n - k))) = interCard p
        omega
      exact ⟨_, MulAction.orbitRel.Quotient.mem_orbit.mp hmem⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## Johnson meets the general theory -/

/-- **Johnson is self-paired.** Swapping a pair of `k`-subsets preserves the intersection size, so
the swapped pair lies in the same orbital. This *discharges* the spectral layer's commutativity
hypothesis rather than assuming it. -/
theorem isSelfPaired_kSub {n k : ℕ} :
    IsSelfPaired (Equiv.Perm (Fin n)) (KSub n k) := by
  intro x y
  obtain ⟨g, hg⟩ := swap_mem_orbit ((x, y) : KSub n k × KSub n k)
  exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

/-- Consequently the Johnson orbital algebra is commutative, over any commutative ring. -/
theorem isCommutative_johnsonAlgebra {n k : ℕ} (R : Type*) [CommRing R] :
    Subalgebra.IsCommutative (orbitalAlgebra R (Equiv.Perm (Fin n)) (KSub n k)) :=
  isCommutative_orbitalAlgebra_of_isSelfPaired isSelfPaired_kSub

/-- The count, in the library's computable `orbits` form. This statement is only reachable
because the orbit-count bridge does not require `AddCommGroup`: the Johnson carrier is a
pair of `Finset` subtypes and has no additive structure whatsoever. -/
theorem card_orbits_finset_kSub {n k : ℕ} (h : k ≤ n) :
    (orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)).card = min k (n - k) + 1 := by
  rw [← card_orbitRel_quotient]
  exact card_orbits_kSub h

/-- The classical form in the quotient index, under the stronger guard. -/
theorem card_orbits_kSub_of_two_mul_le {n k : ℕ} (h : 2 * k ≤ n) :
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (KSub n k × KSub n k))
      = k + 1 := by
  rw [card_orbits_kSub (by omega)]
  omega

/-- The classical form, under the stronger guard. -/
theorem card_orbits_finset_kSub_of_two_mul_le {n k : ℕ} (h : 2 * k ≤ n) :
    (orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)).card = k + 1 := by
  rw [card_orbits_finset_kSub (by omega)]
  omega

/-- **The dimension of the Johnson orbital algebra.** -/
theorem finrank_johnsonAlgebra {n k : ℕ} (h : k ≤ n) :
    Module.finrank ℂ (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
      = min k (n - k) + 1 := by
  rw [finrank_orbitalAlgebra, card_orbits_finset_kSub h]

/-! ## The bridge to Mathlib's carrier

Mathlib's own `k`-subset carrier, with its action and pretransitivity, is
`Set.powersetCard`. The two carriers are the same subtype up to the phrasing of the membership
condition. -/

/-- The library's carrier and Mathlib's are the same type. -/
def carrierEquiv (n k : ℕ) : KSub n k ≃ ↥(Set.powersetCard (Fin n) k) :=
  Equiv.subtypeEquivRight (by
    intro S
    simp [Finset.mem_powersetCard, Set.powersetCard, Finset.subset_univ])

/-! ## Valences — how many `k`-subsets meet a fixed one in exactly `t` points

Delsarte (4.21), in this library's convention. The count is the regularity data every
downstream statement consumes: it is the `v_k` appearing in the `Q` eigenmatrix, and it is what
lets the multiplicities be reached from orthogonality rather than from a rank theorem.

`card_filter_inter_card_eq` mentions no group, no orbit and no scheme — only `Finset` and
`powersetCard`. The general **profile** form lives in `ECCLib/SubsetProfile.lean` at strictly
weaker hypotheses (arbitrary ambient `Finset`, the two sizes decoupled, no `Fintype`), and the
statement below derives from it in four lines.

## References

Delsarte, Philips Res. Rep. Suppl. **10** (1973), §4.2, equation (4.21) — where the valence is
asserted without proof ("leaving the verification to the reader"). -/

/-- The counting lemma, in plain `Finset` terms. -/
theorem card_filter_inter_card_eq {t : ℕ} (x : Finset (Fin n)) (hx : x.card = k) (ht : t ≤ k) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter
        (fun y => (x ∩ y).card = t)).card
      = k.choose t * (Fintype.card (Fin n) - k).choose (k - t) := by
  classical
  have h := ECCLib.card_filter_profile_powersetCard
    (Ω := (Finset.univ : Finset (Fin n))) (Finset.subset_univ x) ht
  rw [Finset.card_univ_diff, hx] at h
  rw [← h]
  exact congrArg Finset.card (Finset.filter_congr fun y _ => by rw [Finset.inter_comm])

/-! ## Lift to `KSub` / `interCard` — the valence proper -/

/-- **The Johnson valence** (Delsarte (4.21), our convention): the number of `k`-subsets meeting a
fixed one in exactly `t` points. -/
theorem card_filter_interCard_eq {t : ℕ} (x : KSub n k) (ht : t ≤ k) :
    (Finset.univ.filter (fun y : KSub n k => interCard (x, y) = t)).card
      = k.choose t * (n - k).choose (k - t) := by
  classical
  have hx : x.1.card = k := KSub.card_val x
  have hbij : (Finset.univ.filter (fun y : KSub n k => interCard (x, y) = t)).card
      = (((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun y => (x.1 ∩ y).card = t)).card := by
    refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨y.2, hy.2⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro y hy
      simp only [Finset.mem_filter] at hy
      refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hy.2
  rw [hbij, card_filter_inter_card_eq x.1 hx ht, Fintype.card_fin]

/-- **The Johnson valence at the extreme `t = k`**: only `x` itself meets `x` in all `k` points. -/
theorem card_filter_interCard_eq_self (x : KSub n k) :
    (Finset.univ.filter (fun y : KSub n k => interCard (x, y) = k)).card = 1 := by
  simpa using card_filter_interCard_eq x (le_refl k)

/-- **The Johnson valence at the extreme `t = 0`**: the `k`-subsets of the complement. -/
theorem card_filter_interCard_eq_zero (x : KSub n k) :
    (Finset.univ.filter (fun y : KSub n k => interCard (x, y) = 0)).card
      = (n - k).choose k := by
  simpa using card_filter_interCard_eq x (Nat.zero_le k)

end Johnson

end ECCLib.Scheme
