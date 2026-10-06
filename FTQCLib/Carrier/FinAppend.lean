/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tuples on `Fin (n + k)` split by `Fin.append`

A register on `n + k` bits is often read as `n` bits followed by `k` (the read and the unread bits
of `UnreadBits.lean`, a word and its ancillas). These facts about `Fin.append` against `castAdd`,
`natAdd`, `Function.update` and `Fin.insertNth` are general, so they live here, once, in a module
that imports Mathlib alone (docs/STEPS.md, entry 2026-10-01n). Mathlib at the pinned revision has
none of the three.

## Main results

* `castAdd_ne_natAdd` — the first `n` and the last `k` coordinates are disjoint.
* `update_append_natAdd` — updating a last coordinate of `Fin.append x u` updates `u`.
* `insertNth_natAdd_append` — inserting at a last coordinate of `Fin.append x u` inserts into `u`.
* `append_comp_castAdd`, `append_comp_natAdd` — the two blocks of `Fin.append u v` are `u` and `v`
  (entry 2026-10-02c: five copies before).
* `sum_fin_cons` — a sum over tuples on `N + 1` coordinates splits off the first.
-/

namespace FTQCLib.Frame.Walkthrough

variable {n : ℕ} {α : Type*}

/-- `castAdd` and `natAdd` never meet: the first `n` and the last `k` coordinates are disjoint. -/
theorem castAdd_ne_natAdd {k : ℕ} (i : Fin n) (j : Fin k) :
    Fin.castAdd k i ≠ Fin.natAdd n j := by
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at hval
  have hi := i.isLt
  omega

/-- Updating one of the last `k` coordinates of `Fin.append x u` updates `u`. -/
theorem update_append_natAdd {k : ℕ} (x : Fin n → α) (u : Fin k → α)
    (i : Fin k) (b : α) :
    Function.update (Fin.append x u) (Fin.natAdd n i) b = Fin.append x (Function.update u i b) := by
  funext l
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · rw [Function.update_of_ne (castAdd_ne_natAdd l i), Fin.append_left, Fin.append_left]
  · by_cases hl : l = i
    · rw [hl, Function.update_self, Fin.append_right, Function.update_self]
    · have hne : Fin.natAdd n l ≠ Fin.natAdd n i := fun h => hl ((Fin.natAdd_inj n).mp h)
      rw [Function.update_of_ne hne, Fin.append_right, Fin.append_right, Function.update_of_ne hl]

/-- Inserting at one of the last coordinates of `Fin.append x u` inserts into `u`. -/
theorem insertNth_natAdd_append {k : ℕ} (j : Fin (k + 1)) (β : α)
    (x : Fin n → α) (u : Fin k → α) :
    (Fin.insertNth (Fin.natAdd n j : Fin (n + k + 1)) β (Fin.append x u) :
        Fin (n + k + 1) → α)
      = Fin.append x (Fin.insertNth j β u) := by
  rw [Fin.insertNth_eq_iff]
  refine ⟨?_, ?_⟩
  · change β = Fin.append x (Fin.insertNth j β u) (Fin.natAdd n j)
    rw [Fin.append_right, Fin.insertNth_apply_same]
  · funext l
    refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · change Fin.append x u (Fin.castAdd k l)
        = Fin.append x (Fin.insertNth j β u) ((Fin.natAdd n j : Fin (n + k + 1)).succAbove
          (Fin.castAdd k l))
      have hlt : (Fin.castAdd k l).castSucc < (Fin.natAdd n j : Fin (n + k + 1)) := by
        rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
        have hl := l.isLt
        omega
      have hcast : (Fin.castAdd k l).castSucc = (Fin.castAdd (k + 1) l : Fin (n + (k + 1))) :=
        Fin.ext (by rw [Fin.val_castSucc, Fin.val_castAdd, Fin.val_castAdd])
      rw [Fin.succAbove_of_castSucc_lt _ _ hlt, hcast, Fin.append_left, Fin.append_left]
    · change Fin.append x u (Fin.natAdd n l)
        = Fin.append x (Fin.insertNth j β u) ((Fin.natAdd n j : Fin (n + k + 1)).succAbove
          (Fin.natAdd n l))
      rw [Fin.append_right]
      rcases lt_or_ge l.castSucc j with hlj | hlj
      · have hlt : (Fin.natAdd n l).castSucc < (Fin.natAdd n j : Fin (n + k + 1)) := by
          rw [Fin.lt_def] at hlj ⊢
          rw [Fin.val_castSucc, Fin.val_natAdd, Fin.val_natAdd]
          rw [Fin.val_castSucc] at hlj
          omega
        have hcast : (Fin.natAdd n l).castSucc
            = (Fin.natAdd n l.castSucc : Fin (n + (k + 1))) :=
          Fin.ext (by rw [Fin.val_castSucc, Fin.val_natAdd, Fin.val_natAdd, Fin.val_castSucc])
        rw [Fin.succAbove_of_castSucc_lt _ _ hlt, hcast, Fin.append_right,
          ← Fin.succAbove_of_castSucc_lt _ _ hlj, Fin.insertNth_apply_succAbove]
      · have hle : (Fin.natAdd n j : Fin (n + k + 1)) ≤ (Fin.natAdd n l).castSucc := by
          rw [Fin.le_def] at hlj ⊢
          rw [Fin.val_castSucc, Fin.val_natAdd, Fin.val_natAdd]
          rw [Fin.val_castSucc] at hlj
          omega
        have hsucc : (Fin.natAdd n l).succ = (Fin.natAdd n l.succ : Fin (n + (k + 1))) :=
          Fin.ext (by rw [Fin.val_succ, Fin.val_natAdd, Fin.val_natAdd, Fin.val_succ]; omega)
        rw [Fin.succAbove_of_le_castSucc _ _ hle, hsucc, Fin.append_right,
          ← Fin.succAbove_of_le_castSucc _ _ hlj, Fin.insertNth_apply_succAbove]

/-- The first block of `Fin.append u v` is `u`. -/
theorem append_comp_castAdd {k : ℕ} (u : Fin n → α) (v : Fin k → α) :
    Fin.append u v ∘ Fin.castAdd k = u := by
  funext i
  exact Fin.append_left u v i

/-- The last block of `Fin.append u v` is `v`. -/
theorem append_comp_natAdd {k : ℕ} (u : Fin n → α) (v : Fin k → α) :
    Fin.append u v ∘ Fin.natAdd n = v := by
  funext i
  exact Fin.append_right u v i

/-- A sum over the tuples on `N + 1` coordinates is a sum over the first coordinate of a sum over the
rest (entry 2026-10-02e: two copies before, at `ZMod 2`). -/
theorem sum_fin_cons {M : Type*} [Fintype α] [AddCommMonoid M] {N : ℕ} (F : (Fin (N + 1) → α) → M) :
    ∑ y, F y = ∑ a : α, ∑ y : Fin N → α, F (Fin.cons a y) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

end FTQCLib.Frame.Walkthrough
