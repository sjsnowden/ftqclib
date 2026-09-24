/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.DualAction
import Mathlib.Data.ZMod.Basic

/-!
# Checks for the dual action

No `decide` rows: every statement here is indexed by characters, whose `Fintype`/`DecidableEq`
instances are Mathlib's classical ones. The checks are the axiom sweep, the agreement row, and
the discriminating instantiations.

**The agreement row.** At `g = 1` everything is fixed on both sides, so `card_fixedBy_dual_eq`
must collapse to `|V̂| = |V|` — which Mathlib proves independently, from Pontryagin duality.
That is a check on the counting itself, not on the statement's shape.

**The discriminating rows.** Nothing here assumes a Hamming setting, a field, or transitivity.
Three instantiations make that visible: `ZMod 4`, whose alphabet admits no transitive
automorphism group at all; `ZMod 6`, neither elementary abelian nor of prime-power order; and
the Klein alphabet used by the Hamming instance.
-/

namespace ECCLib.Scheme

open MulAction

/-- **The agreement row.** At the identity, the count identity says that a finite abelian
group and its dual have the same size. -/
example {V : Type*} [AddCommGroup V] [Fintype V] {G : Type*} [Group G]
    [DistribMulAction G V] : Fintype.card (AddChar V ℂ) = Fintype.card V := by
  classical
  have h := card_fixedBy_dual_eq (V := V) (1 : G)
  have hd : fixedBy (AddChar V ℂ) (1 : G) = Set.univ := by
    ext χ; simp
  have hp : fixedBy V (1 : G) = Set.univ := by
    ext v; simp
  rw [hd, hp, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_univ, Set.ncard_univ,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  exact h

/-- The same statement as Mathlib proves it, for comparison. -/
example {V : Type*} [AddCommGroup V] [Fintype V] :
    Fintype.card (AddChar V ℂ) = Fintype.card V := AddChar.card_eq

/-- **Discriminating row 1** — `ZMod 4`, the alphabet with NO transitive automorphism group
on its nonzero elements. The count identity holds anyway. -/
example (g : (ZMod 4)ˣ) :
    Nat.card (fixedBy (AddChar (ZMod 4) ℂ) g) = Nat.card (fixedBy (ZMod 4) g) :=
  card_fixedBy_dual_eq g

/-- **Discriminating row 2** — `ZMod 6`: neither elementary abelian nor of prime-power order,
so no field or shell structure is available. -/
example (g : (ZMod 6)ˣ) :
    Nat.card (fixedBy (AddChar (ZMod 6) ℂ) g) = Nat.card (fixedBy (ZMod 6) g) :=
  card_fixedBy_dual_eq g

/-- **Discriminating row 3** — the Klein alphabet under its full automorphism group. -/
example (g : AddAut (ZMod 2 × ZMod 2)) :
    Nat.card (fixedBy (AddChar (ZMod 2 × ZMod 2) ℂ) g)
      = Nat.card (fixedBy (ZMod 2 × ZMod 2) g) :=
  card_fixedBy_dual_eq g

/-- The criterion in its consumer form: a fixed character annihilates every shift. -/
example {V : Type*} [AddCommGroup V] {G : Type*} [Group G]
    [DistribMulAction G V] (g : G) (χ : AddChar V ℂ) (h : g • χ = χ) (v : V) :
    χ (g • v - v) = 1 := by
  have hmem := (mem_fixedBy_dual_iff g χ).mp h
  rw [mem_charAnnihSubgroup] at hmem
  simpa using hmem _ (AddMonoidHom.mem_range.mpr ⟨v, rfl⟩)

/-- **The orbit counts agree with no transitivity hypothesis**, exercised where transitivity
fails on both sides. -/
example : Nat.card (orbitRel.Quotient (ZMod 4)ˣ (AddChar (ZMod 4) ℂ))
    = Nat.card (orbitRel.Quotient (ZMod 4)ˣ (ZMod 4)) := card_orbits_dual_eq

/-- The same at `ZMod 6`. -/
example : Nat.card (orbitRel.Quotient (ZMod 6)ˣ (AddChar (ZMod 6) ℂ))
    = Nat.card (orbitRel.Quotient (ZMod 6)ˣ (ZMod 6)) := card_orbits_dual_eq

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.contra_smul_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.contra_smul_zero

/-- info: 'ECCLib.Scheme.fixedBy_eq_ker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.fixedBy_eq_ker

/-- info: 'ECCLib.Scheme.mem_fixedBy_dual_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_fixedBy_dual_iff

/-- info: 'ECCLib.Scheme.fixedBy_dual_eq_annihilator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.fixedBy_dual_eq_annihilator

/-- info: 'ECCLib.Scheme.card_fixedBy_dual_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_fixedBy_dual_eq

/-- info: 'ECCLib.Scheme.card_orbits_dual_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_orbits_dual_eq
