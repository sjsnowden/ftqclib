/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.FuncDeriv
import FTQCLib.Codes.AJOGeneral
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Powerset

set_option linter.unusedSectionVars false

/-! # Möbius inversion on the Boolean lattice `{0,1}ⁿ`

The natural inverse of the discrete derivative `funcDeriv` on
F₂-valued phase functions. Underpins the polynomial reconstruction
step of CGK reverse: a function `f : (F₂)ⁿ → A` is determined by its
iterated discrete derivatives at `0`, via
`f(v) = Σ_{S ⊆ supp(v)} Δ_S f(0)`.

Cf. Rota 1964 *On the foundations of combinatorial theory I, theory
of Möbius functions*; Stanley *Enumerative Combinatorics* §3.7.

## Layout

* Polymorphic discrete derivative `funcDerivG` and its iteration
  `funcDerivSubset` over a finite subset `S ⊆ {0,…,n−1}`.
* Commutativity of single derivatives (`funcDerivG_comm`) and the
  unfold of `funcDerivSubset` over `insert`.
* Characteristic function `charFn : Finset (Fin n) → (Fin n → ZMod 2)`
  realising a subset as a binary vector; involution
  `supp_charFn` / `charFn_supp`.
* The Möbius / Newton-forward closed form
  `funcDerivSubset_zero_eq_mobius_sum`:

      `Δ_S f(0) = Σ_{T ⊆ S} (−1)^{|S|−|T|} • f(charFn T)`.

* The inversion theorem `mobius_inversion_boolean`:

      `f(v) = Σ_{S ⊆ supp(v)} Δ_S f(0)`.

* The named coefficient `mobiusCoeff S f := funcDerivSubset S f 0`,
  used downstream by Module β (CGK reverse iteration).

We work over an arbitrary `AddCommGroup A` so the file applies both
to the polynomial-coefficient ring `ZMod (2^m)` (CGK reverse, where
Δ_S f(0) is a level-(k−|S|) phase) and to the real-phase target
`ℝ / 2πℤ` (AJO reading of the discrete derivative).

For the original `ZMod (2^m)`-valued `funcDeriv` defined in
`FTQCLib/Hierarchy/FuncDeriv.lean`, see `funcDeriv_eq_funcDerivG` which
identifies the two.
-/

namespace FTQCLib.Hierarchy

namespace BooleanMobius

variable {n : ℕ}

/-! ### Polymorphic discrete derivative -/

/-- The **polymorphic discrete derivative** on phase functions
`f : (F₂)ⁿ → A`. At `v ∈ (F₂)ⁿ` it returns `f(v + e_i) − f v`, where
`+` is mod-2 addition in `(F₂)ⁿ` (XOR). Coefficient ring `A` need
only be an `AddCommGroup` for the difference to make sense; for the
quantum applications `A = ZMod (2^m)` (CGK reverse) or `A = ℝ`
(AJO real-phase reading). Mirrors `DiagPhase.funcDeriv` from
`FTQCLib/Hierarchy/FuncDeriv.lean`. -/
def funcDerivG {A : Type*} [AddCommGroup A] (i : Fin n)
    (f : (Fin n → ZMod 2) → A) :
    (Fin n → ZMod 2) → A :=
  fun v => f (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) - f v

/-- Specialised compatibility with `DiagPhase.funcDeriv` (over
`ZMod (2^m)`): the polymorphic and monomorphic versions agree
definitionally. -/
lemma funcDerivG_eq_funcDeriv {m : ℕ} (i : Fin n)
    (f : (Fin n → ZMod 2) → ZMod (2 ^ m)) :
    funcDerivG i f = DiagPhase.funcDeriv (m := m) i f :=
  rfl

/-- Unfold `funcDerivG` to its difference form. -/
lemma funcDerivG_apply {A : Type*} [AddCommGroup A] (i : Fin n)
    (f : (Fin n → ZMod 2) → A) (v : Fin n → ZMod 2) :
    funcDerivG i f v
      = f (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) - f v :=
  rfl

/-! ### Commutativity

The single-position discrete derivatives commute because addition in
`(F₂)ⁿ` is commutative: `(v + e_i) + e_j = (v + e_j) + e_i`. -/

/-- **Commutativity of `funcDerivG`.** Two single derivatives can be
swapped at no cost. The proof reduces to the commutativity of `+`
in the input function. -/
theorem funcDerivG_comm {A : Type*} [AddCommGroup A] (i j : Fin n)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG j f) = funcDerivG j (funcDerivG i f) := by
  funext v
  -- LHS = f((v + e_i) + e_j) - f(v + e_i) - (f(v + e_j) - f v)
  -- RHS = f((v + e_j) + e_i) - f(v + e_j) - (f(v + e_i) - f v)
  -- Equal by commutativity of `+` on `(F₂)ⁿ`.
  simp only [funcDerivG_apply]
  have h : v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)
            + (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)
          = v + (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)
            + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) := by
    abel
  rw [h]
  abel

/-! ### Iterated derivative over a subset

`funcDerivSubset S f` iterates `funcDerivG i` over every `i ∈ S`.
By `funcDerivG_comm`, the order is irrelevant. We define it via
`Finset.fold`-style recursion; the fundamental lemma is
`funcDerivSubset_insert`.
-/

/-- The **iterated discrete derivative** over a finite subset
`S ⊆ {0,…,n−1}`. Implemented as the `List.foldr` of `funcDerivG i`
over the (arbitrary order) `S.toList`. Because `funcDerivG`s commute
(`funcDerivG_comm`), the value is order-independent — proved as
`funcDerivSubset_insert`. -/
noncomputable def funcDerivSubset {A : Type*} [AddCommGroup A]
    (S : Finset (Fin n)) (f : (Fin n → ZMod 2) → A) :
    (Fin n → ZMod 2) → A :=
  S.toList.foldr (fun i g => funcDerivG i g) f

/-- `List.foldr` of `funcDerivG` is permutation-invariant on the list
of indices. This is the precise form of order independence we need
to lift the `List.foldr` definition to a `Finset` (multiset)
function. -/
private lemma foldr_funcDerivG_perm
    {A : Type*} [AddCommGroup A]
    {l₁ l₂ : List (Fin n)} (hperm : l₁.Perm l₂)
    (f : (Fin n → ZMod 2) → A) :
    l₁.foldr (fun i g => funcDerivG i g) f
      = l₂.foldr (fun i g => funcDerivG i g) f := by
  induction hperm with
  | nil => rfl
  | cons i _ ih =>
      simp only [List.foldr_cons]
      rw [ih]
  | swap i j l =>
      simp only [List.foldr_cons]
      exact funcDerivG_comm j i _
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- Unfold `funcDerivSubset` on the empty subset: it is the identity. -/
@[simp] lemma funcDerivSubset_empty {A : Type*} [AddCommGroup A]
    (f : (Fin n → ZMod 2) → A) :
    funcDerivSubset (∅ : Finset (Fin n)) f = f := by
  change (∅ : Finset (Fin n)).toList.foldr (fun i g => funcDerivG i g) f = f
  rw [Finset.toList_empty]
  rfl

/-- The recursion equation for `funcDerivSubset` on `insert i S`
(when `i ∉ S`). This is the workhorse for inductive proofs. The
order-independence of `List.foldr` is used here: `(insert i S).toList`
is a permutation of `i :: S.toList` (not literally equal). -/
lemma funcDerivSubset_insert {A : Type*} [AddCommGroup A]
    {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivSubset (insert i S) f
      = funcDerivG i (funcDerivSubset S f) := by
  -- The lists `(insert i S).toList` and `i :: S.toList` are permutations.
  have hperm : (insert i S).toList.Perm (i :: S.toList) := by
    have h1 : ((insert i S).toList : Multiset (Fin n)) = (insert i S).1 :=
      Finset.toList_toFinset (insert i S) ▸ Finset.coe_toList (insert i S)
    -- Use `Multiset.coe_eq_coe` to lift list permutation to multiset equality.
    have hmulteq : ((insert i S).toList : Multiset (Fin n))
                 = (i ::ₘ (S.toList : Multiset (Fin n))) := by
      rw [Finset.coe_toList, Finset.insert_val_of_notMem hi,
          show (i ::ₘ (S.toList : Multiset (Fin n))) = i ::ₘ S.1 by
            rw [Finset.coe_toList]]
    exact Multiset.coe_eq_coe.mp hmulteq
  change (insert i S).toList.foldr (fun j g => funcDerivG j g) f
       = funcDerivG i (S.toList.foldr (fun j g => funcDerivG j g) f)
  rw [foldr_funcDerivG_perm hperm]
  simp only [List.foldr_cons]

/-! ### Characteristic function on `(F₂)ⁿ`

For `T ⊆ {0,…,n−1}`, `charFn T : Fin n → ZMod 2` is the indicator
vector (1 on `T`, 0 off). We will need:

* `charFn ∅ = 0` (the zero vector).
* `charFn T` is its own support: `supp (charFn T) = T`.
* `charFn (supp v) = v` (the support–indicator involution).
-/

/-- The **characteristic function** of a subset `T ⊆ Fin n`,
realised as the binary vector with `1` on `T` and `0` off. -/
noncomputable def charFn (T : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun i => if i ∈ T then 1 else 0

@[simp] lemma charFn_empty : charFn (∅ : Finset (Fin n)) = 0 := by
  funext i; simp [charFn]

lemma charFn_apply (T : Finset (Fin n)) (i : Fin n) :
    charFn T i = if i ∈ T then 1 else 0 := rfl

/-- The support of `charFn T` is `T`. -/
@[simp] lemma supp_charFn (T : Finset (Fin n)) :
    FTQCLib.Codes.supp (charFn T) = T := by
  unfold FTQCLib.Codes.supp charFn
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h
  · simp [h]
  · constructor
    · intro hcontra; exact absurd hcontra (by decide)
    · intro hcontra; exact absurd hcontra h

/-- A `ZMod 2` element is either `0` or `1`. Re-stated locally for use
in `charFn_supp`. -/
private lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hval : a = (a.val : ZMod 2) := (ZMod.natCast_zmod_val a).symm
  interval_cases a.val
  · left; rw [hval]; norm_cast
  · right; rw [hval]; norm_cast

/-- `charFn (supp v) = v`: the support–indicator pair is an
involution. -/
@[simp] lemma charFn_supp (v : Fin n → ZMod 2) :
    charFn (FTQCLib.Codes.supp v) = v := by
  funext i
  unfold charFn FTQCLib.Codes.supp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : v i = 1
  · simp [h]
  · rcases zmod_two_eq_zero_or_one (v i) with h0 | h1
    · simp [h0]
    · exact absurd h1 h

/-! ### The Möbius closed form at `v = 0`

We prove the closed form

  `funcDerivSubset S f 0 = Σ_{T ⊆ S} (−1)^{|S|−|T|} • f(charFn T)`

by induction on `S`. The key inductive step uses `funcDerivG_apply`,
the `Finset.powerset_insert` decomposition, and the involution
`charFn`.

For the recursion we need a slightly stronger lemma — the value at
arbitrary `v` is the alternating sum over `T ⊆ S` of `f(v + charFn T)`
with signs `(−1)^{|S|−|T|}`. The closed form at `0` follows by
`charFn_empty` and `zero_add`.
-/

/-- A useful rewrite: `charFn (insert i T) j` is `charFn T j + e_i j`
in `ZMod 2`, when `i ∉ T`. (This is the `+` of `ZMod 2`, which is
XOR, matching the symmetric-difference identity.) -/
private lemma charFn_insert_eq_add_single
    {i : Fin n} {T : Finset (Fin n)} (hi : i ∉ T) :
    charFn (insert i T)
      = charFn T + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) := by
  funext j
  unfold charFn
  by_cases hji : j = i
  · subst hji
    simp [hi, Pi.single_eq_same]
  · have h1 : (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) j = 0 :=
      Pi.single_eq_of_ne hji 1
    by_cases hjT : j ∈ T
    · simp only [hjT, Finset.mem_insert, hji, Pi.add_apply, h1,
                 if_true, false_or, add_zero]
    · simp only [hjT, Finset.mem_insert, hji, Pi.add_apply, h1,
                 if_false, false_or, add_zero]

/-- Sign rewrite: `(−1)^(k+1) = −(−1)^k` over `ℤ`. -/
private lemma neg_one_pow_succ_int (k : ℕ) :
    ((-1 : ℤ) ^ (k + 1)) = -((-1 : ℤ) ^ k) := by
  rw [pow_succ]; ring

/-- **The Möbius value formula at an arbitrary base point `v`.**

For any `v : Fin n → ZMod 2` and any subset `S`, the iterated
discrete derivative satisfies

  `funcDerivSubset S f v = Σ_{T ⊆ S} (−1)^(|S|−|T|) • f(v + charFn T)`.

Proof by induction on `S`. The inductive step splits `T ⊆ insert i S`
into those with `i ∉ T` (where `(−1)^(|insert i S|−|T|) = −(−1)^(|S|−|T|)`)
and those with `i ∈ T` (matched bijectively to subsets of `S` by
removing `i`, contributing the positive sign).

This is the central lemma; everything else is a corollary. -/
theorem funcDerivSubset_eq_alt_sum
    {A : Type*} [AddCommGroup A]
    (S : Finset (Fin n)) (f : (Fin n → ZMod 2) → A)
    (v : Fin n → ZMod 2) :
    funcDerivSubset S f v
      = ∑ T ∈ S.powerset,
          ((-1 : ℤ) ^ (S.card - T.card)) • f (v + charFn T) := by
  -- Induct on `S` with a motive that quantifies over `v` so that `ih`
  -- is usable at multiple base points (we need it at `v` and `v + e_i`).
  induction S using Finset.induction_on generalizing v with
  | empty =>
      simp [funcDerivSubset_empty, Finset.powerset_empty]
  | insert i S hi ih =>
      -- LHS: funcDerivG i (funcDerivSubset S f) v
      --    = funcDerivSubset S f (v + e_i) - funcDerivSubset S f v.
      rw [funcDerivSubset_insert hi, funcDerivG_apply]
      -- Apply the inductive hypothesis at both `v + e_i` and `v`.
      rw [ih (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)), ih v]
      -- RHS unfolds via `powerset_insert`.
      rw [Finset.powerset_insert]
      -- Sum splits as `Σ_{T ⊆ S} ... + Σ_{T ⊆ S} ... applied to insert i T`.
      have hdisj :
          Disjoint S.powerset (S.powerset.image (insert i)) := by
        rw [Finset.disjoint_left]
        intro T hT hT'
        rw [Finset.mem_image] at hT'
        obtain ⟨T', _, hT'eq⟩ := hT'
        rw [Finset.mem_powerset] at hT
        have : i ∈ T := hT'eq ▸ Finset.mem_insert_self _ _
        exact hi (hT this)
      rw [Finset.sum_union hdisj]
      -- The `image` sum reindexes as a sum over `T ⊆ S`.
      have hinj : Set.InjOn (insert i) (S.powerset : Set (Finset (Fin n))) := by
        intro T₁ hT₁ T₂ hT₂ hins
        rw [Finset.mem_coe, Finset.mem_powerset] at hT₁ hT₂
        have hi1 : i ∉ T₁ := fun h => hi (hT₁ h)
        have hi2 : i ∉ T₂ := fun h => hi (hT₂ h)
        -- `insert i T₁ = insert i T₂` and `i ∉ T₁`, `i ∉ T₂` ⇒ `T₁ = T₂`.
        ext x
        constructor
        · intro hx
          have : x ∈ insert i T₁ := Finset.mem_insert_of_mem hx
          rw [hins] at this
          rcases Finset.mem_insert.mp this with hxi | hxT₂
          · exact absurd (hxi ▸ hx) hi1
          · exact hxT₂
        · intro hx
          have : x ∈ insert i T₂ := Finset.mem_insert_of_mem hx
          rw [← hins] at this
          rcases Finset.mem_insert.mp this with hxi | hxT₁
          · exact absurd (hxi ▸ hx) hi2
          · exact hxT₁
      rw [Finset.sum_image (fun T₁ hT₁ T₂ hT₂ h => hinj hT₁ hT₂ h)]
      -- Now split each summand using the sign rewrite.
      -- The target equality reads:
      --   (Σ_{T⊆S} α_T (v+e_i+charFn T)) - (Σ_{T⊆S} α_T (v+charFn T))
      -- = Σ_{T⊆S} β_T (v+charFn T) + Σ_{T⊆S} β_{insert i T} (v+charFn (insert i T))
      -- where α_T = (-1)^(|S|-|T|), β_T = (-1)^(|insert i S|-|T|).
      -- Use `charFn (insert i T) = charFn T + e_i` to combine.
      -- Strategy: bring all RHS to LHS via index manipulations.
      have hicard : (insert i S).card = S.card + 1 :=
        Finset.card_insert_of_notMem hi
      -- For the `image (insert i)` sum, use `charFn (insert i T) = charFn T + e_i`.
      -- Then `v + charFn (insert i T) = v + e_i + charFn T`.
      have hreindex : ∀ T ∈ S.powerset,
          ((-1 : ℤ) ^ ((insert i S).card - (insert i T).card))
            • f (v + charFn (insert i T))
          = ((-1 : ℤ) ^ (S.card - T.card))
            • f (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) + charFn T) := by
        intro T hT
        rw [Finset.mem_powerset] at hT
        have hiT : i ∉ T := fun h => hi (hT h)
        have hTcard : (insert i T).card = T.card + 1 :=
          Finset.card_insert_of_notMem hiT
        rw [hicard, hTcard]
        rw [Nat.add_sub_add_right]
        rw [charFn_insert_eq_add_single hiT]
        congr 1
        abel_nf
      rw [Finset.sum_congr rfl hreindex]
      -- Similarly, the original `S.powerset` sum on RHS uses sign
      -- `(-1)^(|insert i S|-|T|) = (-1)^(|S|+1-|T|) = -(-1)^(|S|-|T|)`.
      have hsignflip : ∀ T ∈ S.powerset,
          ((-1 : ℤ) ^ ((insert i S).card - T.card)) • f (v + charFn T)
          = -(((-1 : ℤ) ^ (S.card - T.card)) • f (v + charFn T)) := by
        intro T hT
        rw [Finset.mem_powerset] at hT
        have hTle : T.card ≤ S.card := Finset.card_le_card hT
        rw [hicard]
        -- (S.card + 1) - T.card = (S.card - T.card) + 1
        rw [Nat.sub_add_comm hTle]
        rw [neg_one_pow_succ_int]
        rw [neg_smul]
      rw [Finset.sum_congr rfl hsignflip]
      -- The goal now reads (up to abel):
      --   Σ α_T • f(v+e_i+charFn T) - Σ α_T • f(v+charFn T)
      --   = Σ -(α_T • f(v+charFn T)) + Σ α_T • f(v+e_i+charFn T).
      -- Combine the negated sum into a single subtraction and finish.
      rw [Finset.sum_neg_distrib]
      abel

/-- **The Möbius closed form at `0`** (the form CGK reverse needs).

Specialising `funcDerivSubset_eq_alt_sum` to `v = 0` and using
`charFn ∅ = 0`, `zero_add`, we get

  `funcDerivSubset S f 0 = Σ_{T ⊆ S} (−1)^(|S|−|T|) • f(charFn T)`.

This is the Möbius transform / Newton-forward coefficient `Δ_S f(0)`
expanded as a signed sum of values at the indicator vectors. -/
theorem funcDerivSubset_zero_eq_mobius_sum
    {A : Type*} [AddCommGroup A]
    (S : Finset (Fin n)) (f : (Fin n → ZMod 2) → A) :
    funcDerivSubset S f 0
      = ∑ T ∈ S.powerset,
          ((-1 : ℤ) ^ (S.card - T.card)) • f (charFn T) := by
  rw [funcDerivSubset_eq_alt_sum S f 0]
  apply Finset.sum_congr rfl
  intro T _
  rw [zero_add]

/-! ### The inversion theorem

The substantive content: a function `f` is reconstructed from its
Möbius coefficients `c_S := Δ_S f(0)` via

  `f(v) = Σ_{S ⊆ supp(v)} c_S`.

Proof: expand each `c_S` via `funcDerivSubset_zero_eq_mobius_sum`,
then swap sums and check that for each `T ⊆ supp v`, the total
coefficient of `f(charFn T)` is

  `Σ_{S : T ⊆ S ⊆ supp v} (−1)^(|S|−|T|)`

By the binomial / inclusion-exclusion identity
`sum_powerset_neg_one_pow_card`, this is `1` if `T = supp v` and `0`
otherwise. The surviving term `f(charFn (supp v)) = f(v)` then gives
the result.
-/

/-- The key combinatorial identity, restated for our index set:
for `T ⊆ U`, the sum

  `Σ_{S : T ⊆ S ⊆ U} (−1)^(|S|−|T|)`

equals `1` if `T = U` and `0` otherwise. (Reduces to
`Finset.sum_powerset_neg_one_pow_card` on `U \ T` by the
`S ↔ T ∪ R` bijection with `R ⊆ U \ T`.) -/
private lemma sum_alt_pow_eq_indicator
    {U T : Finset (Fin n)} (hTU : T ⊆ U) :
    (∑ S ∈ U.powerset with T ⊆ S,
        ((-1 : ℤ) ^ (S.card - T.card)))
      = if T = U then 1 else 0 := by
  -- Reindex via `S = T ∪ R` for `R ⊆ U \ T`.
  -- We use `Finset.sum_powerset_neg_one_pow_card` on `U \ T`.
  -- The bijection: subsets of `U \ T` ↔ subsets `S` with `T ⊆ S ⊆ U`,
  -- via `R ↦ T ∪ R`.
  have hbij :
      (U.powerset.filter (fun S => T ⊆ S)) =
        (U \ T).powerset.image (fun R => T ∪ R) := by
    ext S
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hSU, hTS⟩
      refine ⟨S \ T, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hSU hx.1, hx.2⟩
      · ext x
        rw [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · -- Forward: (x ∈ T ∨ (x ∈ S ∧ x ∉ T)) → x ∈ S.
          rintro (hxT | ⟨hxS, _⟩)
          · exact hTS hxT
          · exact hxS
        · -- Reverse: x ∈ S → x ∈ T ∨ (x ∈ S ∧ x ∉ T).
          intro hxS
          by_cases hxT : x ∈ T
          · exact Or.inl hxT
          · exact Or.inr ⟨hxS, hxT⟩
    · rintro ⟨R, hR, hSeq⟩
      rw [Finset.mem_powerset] at hR
      subst hSeq
      refine ⟨?_, Finset.subset_union_left⟩
      intro x hx
      rcases Finset.mem_union.mp hx with hxT | hxR
      · exact hTU hxT
      · exact (Finset.mem_sdiff.mp (hR hxR)).1
  rw [hbij]
  -- Sum over the image; reindex via `Finset.sum_image`.
  have hinj : ∀ R₁ ∈ (U \ T).powerset, ∀ R₂ ∈ (U \ T).powerset,
      T ∪ R₁ = T ∪ R₂ → R₁ = R₂ := by
    intro R₁ hR₁ R₂ hR₂ heq
    rw [Finset.mem_powerset] at hR₁ hR₂
    have hd1 : Disjoint T R₁ := by
      rw [Finset.disjoint_left]
      intro x hxT hxR
      exact (Finset.mem_sdiff.mp (hR₁ hxR)).2 hxT
    have hd2 : Disjoint T R₂ := by
      rw [Finset.disjoint_left]
      intro x hxT hxR
      exact (Finset.mem_sdiff.mp (hR₂ hxR)).2 hxT
    ext x
    constructor
    · intro hx
      have hx' : x ∈ T ∪ R₁ := Finset.mem_union_right _ hx
      rw [heq] at hx'
      rcases Finset.mem_union.mp hx' with hxT | hxR
      · exact absurd hxT (Finset.disjoint_right.mp hd1 hx)
      · exact hxR
    · intro hx
      have hx' : x ∈ T ∪ R₂ := Finset.mem_union_right _ hx
      rw [← heq] at hx'
      rcases Finset.mem_union.mp hx' with hxT | hxR
      · exact absurd hxT (Finset.disjoint_right.mp hd2 hx)
      · exact hxR
  rw [Finset.sum_image hinj]
  -- Now: ∑ R ⊆ U \ T, (-1)^(|T ∪ R| - |T|) = ∑ R, (-1)^|R|.
  have hcard : ∀ R ∈ (U \ T).powerset,
      ((-1 : ℤ) ^ ((T ∪ R).card - T.card)) = ((-1 : ℤ) ^ R.card) := by
    intro R hR
    rw [Finset.mem_powerset] at hR
    have hd : Disjoint T R := by
      rw [Finset.disjoint_left]
      intro x hxT hxR
      exact (Finset.mem_sdiff.mp (hR hxR)).2 hxT
    rw [Finset.card_union_of_disjoint hd]
    rw [Nat.add_sub_cancel_left]
  rw [Finset.sum_congr rfl hcard]
  rw [Finset.sum_powerset_neg_one_pow_card]
  -- (U \ T) = ∅ ↔ T = U.
  by_cases heq : T = U
  · subst heq
    rw [if_pos rfl]
    rw [if_pos (Finset.sdiff_self T)]
  · rw [if_neg heq]
    have hne : U \ T ≠ ∅ := by
      intro hempty
      apply heq
      have h1 : U ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hempty
      exact Finset.Subset.antisymm hTU h1
    rw [if_neg hne]

/-- **Möbius inversion on the Boolean lattice.**

For any function `f : (F₂)ⁿ → A` (with `A` an `AddCommGroup`) and
any binary vector `v`,

  `f(v) = Σ_{S ⊆ supp(v)} (funcDerivSubset S f 0)`.

This is the Newton-forward / Möbius inversion formula: every phase
function on `(F₂)ⁿ` is recovered from its iterated discrete
derivatives at `0`. Cf. Rota 1964 *Foundations of combinatorial
theory I*.

Used by Module β of CGK reverse to reconstruct the phase function of
`U_P` from its operator-side conjugation data. -/
theorem mobius_inversion_boolean
    {A : Type*} [AddCommGroup A]
    (f : (Fin n → ZMod 2) → A) (v : Fin n → ZMod 2) :
    f v
      = ∑ S ∈ (FTQCLib.Codes.supp v).powerset, funcDerivSubset S f 0 := by
  set U := FTQCLib.Codes.supp v with hU
  -- Expand each Möbius coefficient.
  have hRHS :
      (∑ S ∈ U.powerset, funcDerivSubset S f 0)
      = ∑ S ∈ U.powerset,
          ∑ T ∈ S.powerset,
            ((-1 : ℤ) ^ (S.card - T.card)) • f (charFn T) := by
    apply Finset.sum_congr rfl
    intro S _
    exact funcDerivSubset_zero_eq_mobius_sum S f
  rw [hRHS]
  -- Swap the order of summation: outer sum over S ⊆ U, inner over T ⊆ S
  -- becomes outer over T ⊆ U, inner over S with T ⊆ S ⊆ U.
  have hswap :
      ∀ S T : Finset (Fin n),
        (S ∈ U.powerset ∧ T ∈ S.powerset)
          ↔ (S ∈ U.powerset.filter (fun S => T ⊆ S) ∧ T ∈ U.powerset) := by
    intro S T
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · rintro ⟨hSU, hTS⟩
      exact ⟨⟨hSU, hTS⟩, hTS.trans hSU⟩
    · rintro ⟨⟨hSU, hTS⟩, _⟩
      exact ⟨hSU, hTS⟩
  rw [Finset.sum_comm' (s := U.powerset) (t := fun S => S.powerset)
      (t' := U.powerset) (s' := fun T => U.powerset.filter (fun S => T ⊆ S))
      (h := hswap)]
  -- Now sum is ∑_{T ⊆ U} ∑_{S : T ⊆ S ⊆ U} (-1)^(|S|-|T|) • f(charFn T)
  -- Factor out f(charFn T) from inner sum.
  have hinner : ∀ T ∈ U.powerset,
      ∑ S ∈ U.powerset.filter (fun S => T ⊆ S),
          ((-1 : ℤ) ^ (S.card - T.card)) • f (charFn T)
      = (∑ S ∈ U.powerset.filter (fun S => T ⊆ S),
          ((-1 : ℤ) ^ (S.card - T.card))) • f (charFn T) := by
    intro T _
    rw [← Finset.sum_smul]
  rw [Finset.sum_congr rfl hinner]
  -- Apply the key indicator identity.
  have houter : ∀ T ∈ U.powerset,
      (∑ S ∈ U.powerset.filter (fun S => T ⊆ S),
          ((-1 : ℤ) ^ (S.card - T.card))) • f (charFn T)
      = if T = U then f (charFn T) else 0 := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [sum_alt_pow_eq_indicator hT]
    by_cases heq : T = U
    · simp [heq, one_smul]
    · simp [heq, zero_smul]
  rw [Finset.sum_congr rfl houter]
  -- Now only the T = U term survives.
  have hUmem : U ∈ U.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl _)
  rw [Finset.sum_ite_eq' U.powerset U (fun T => f (charFn T))]
  rw [if_pos hUmem]
  rw [hU, charFn_supp]

/-! ### The named coefficient

The downstream API uses `mobiusCoeff S f := funcDerivSubset S f 0`
to refer to the Möbius / Newton-forward coefficient. -/

/-- **The Möbius coefficient of `f` at `S`**: the iterated discrete
derivative of `f` at the zero vector. By Möbius inversion
(`mobius_inversion_boolean`),
`f(v) = Σ_{S ⊆ supp(v)} mobiusCoeff S f`. -/
noncomputable def mobiusCoeff {A : Type*} [AddCommGroup A] (S : Finset (Fin n))
    (f : (Fin n → ZMod 2) → A) : A :=
  funcDerivSubset S f 0

/-- Unfold `mobiusCoeff` to its definition. -/
lemma mobiusCoeff_apply {A : Type*} [AddCommGroup A] (S : Finset (Fin n))
    (f : (Fin n → ZMod 2) → A) :
    mobiusCoeff S f = funcDerivSubset S f 0 := rfl

/-- The Möbius transform of `f` is exactly the signed powerset sum:

  `mobiusCoeff S f = Σ_{T ⊆ S} (−1)^{|S|−|T|} • f(charFn T)`.

Mathematical content of `funcDerivSubset_zero_eq_mobius_sum`, written
in `mobiusCoeff` form for downstream readability. -/
theorem mobiusCoeff_eq_alt_sum
    {A : Type*} [AddCommGroup A]
    (S : Finset (Fin n)) (f : (Fin n → ZMod 2) → A) :
    mobiusCoeff S f
      = ∑ T ∈ S.powerset,
          ((-1 : ℤ) ^ (S.card - T.card)) • f (charFn T) :=
  funcDerivSubset_zero_eq_mobius_sum S f

/-- **Möbius inversion in `mobiusCoeff` form**:
`f(v) = Σ_{S ⊆ supp(v)} mobiusCoeff S f`. -/
theorem eq_sum_mobiusCoeff
    {A : Type*} [AddCommGroup A]
    (f : (Fin n → ZMod 2) → A) (v : Fin n → ZMod 2) :
    f v = ∑ S ∈ (FTQCLib.Codes.supp v).powerset, mobiusCoeff S f :=
  mobius_inversion_boolean f v

end BooleanMobius

end FTQCLib.Hierarchy
