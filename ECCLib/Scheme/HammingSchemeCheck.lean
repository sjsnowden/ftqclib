/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.HammingScheme

/-!
# Checks for the Hamming scheme instantiation

No `decide` rows: every statement here is indexed by characters, whose `Fintype`/`DecidableEq`
instances are Mathlib's classical ones. The checks are the axiom sweep plus the rows below.

**The agreement rows.** Two facts proved here were already proved by a different route
elsewhere, and must come out the same way:

* the weak form `shellSet_stable` (in `Scheme/HammingDual.lean`, proved from invariance of the
  dual weight)
  is re-derived here through the ORBIT — a shell is an orbit, an orbit is stable — which is a
  different argument for the same conclusion;
* `qEnt_orbit_eq_kraw` read at a dual shell must reduce to `qEnt_shellSet`, the
  identity it generalises.

**The discriminating row.** `orb_eq_shellSet` carries a transitivity hypothesis that
`shellSet_stable` does not. The instantiation that shows this matters is the Klein alphabet,
where transitivity holds and the theorem therefore applies with no side condition; at `ZMod 4`
the hypothesis is unavailable (`no_transitive_group`), and the weak form is all that survives.
-/

namespace ECCLib.Scheme

open Finset MulAction ECCLib.Delsarte

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
variable {G : Type*} [Group G] [Finite G] [DistribMulAction G A]

/-- **Agreement row 1.** The weak form, re-derived through the orbit description rather than
through invariance of the dual weight. -/
example (htrans : TransOnNonzero G A) (k : ℕ) {φ : AddAut (ι → A)}
    (hφ : φ ∈ monomialSubgroup ι A G) {ξ : AddChar (ι → A) ℂ} (hξ : ξ ∈ shellSet ι A k) :
    φ • ξ ∈ shellSet ι A k := by
  have hk : dualWeight ξ = k := (mem_shellSet_iff k ξ).mp hξ
  have hmem : φ • ξ ∈ orb (↥(monomialSubgroup ι A G)) ξ := mem_orb.mpr ⟨⟨φ, hφ⟩, rfl⟩
  rwa [orb_eq_shellSet htrans, hk] at hmem

/-- The same statement as `shellSet_stable` proves it, for comparison. -/
example (k : ℕ) {φ : AddAut (ι → A)} (hφ : φ ∈ monomialSubgroup ι A G)
    {ξ : AddChar (ι → A) ℂ} (hξ : ξ ∈ shellSet ι A k) : φ • ξ ∈ shellSet ι A k :=
  shellSet_stable (G := G) k hφ hξ

/-- **Agreement row 2.** At a dual shell, the orbit form of the `Q`-entry must reduce to the
identity `qEnt_shellSet` it generalises. -/
example (htrans : TransOnNonzero G A) (k : ℕ) {χ : AddChar (ι → A) ℂ}
    (hχ : χ ∈ shellSet ι A k) (u : ι → A) :
    qEnt (shellSet ι A k) u
      = ((kraw (Fintype.card A) (Fintype.card ι) k (hammingNorm u) : ℤ) : ℂ) := by
  have hk : dualWeight χ = k := (mem_shellSet_iff k χ).mp hχ
  have hSmem : shellSet ι A k
      ∈ orbits (↥(monomialSubgroup ι A G)) (AddChar (ι → A) ℂ) := by
    have h := orb_mem_orbits (H := ↥(monomialSubgroup ι A G)) χ
    rwa [orb_eq_shellSet htrans, hk] at h
  rw [qEnt_orbit_eq_kraw htrans hSmem hχ u, hk]

/-- **The dual orbits ARE the dual shells** — `orb_eq_shellSet`, in the
form the scheme layer consumes. -/
example (htrans : TransOnNonzero G A) (ξ : AddChar (ι → A) ℂ) :
    orb (↥(monomialSubgroup ι A G)) ξ = shellSet ι A (dualWeight ξ) :=
  orb_eq_shellSet htrans ξ

/-- **The discriminating row.** At the Klein (Pauli) alphabet the transitivity hypothesis is
available, so the theorem applies with no side condition — this is the instantiation a
version of the theorem that had kept the hypothesis abstract could not deliver. -/
example (rep : Finset (AddChar (Fin 3 → ZMod 2 × ZMod 2) ℂ) →
      AddChar (Fin 3 → ZMod 2 × ZMod 2) ℂ)
    (hrep : ∀ S ∈ orbits (↥(monomialSubgroup (Fin 3) (ZMod 2 × ZMod 2)
        (AddAut (ZMod 2 × ZMod 2)))) (AddChar (Fin 3 → ZMod 2 × ZMod 2) ℂ), rep S ∈ S)
    {R : Finset (Fin 3 → ZMod 2 × ZMod 2)}
    (hR : R ∈ orbits (↥(monomialSubgroup (Fin 3) (ZMod 2 × ZMod 2)
        (AddAut (ZMod 2 × ZMod 2)))) (Fin 3 → ZMod 2 × ZMod 2))
    (u : Fin 3 → ZMod 2 × ZMod 2) :
    ∑ S ∈ orbits (↥(monomialSubgroup (Fin 3) (ZMod 2 × ZMod 2)
        (AddAut (ZMod 2 × ZMod 2)))) (AddChar (Fin 3 → ZMod 2 × ZMod 2) ℂ),
        pEnt R (rep S)
          * ((kraw (Fintype.card (ZMod 2 × ZMod 2)) (Fintype.card (Fin 3))
              (dualWeight (rep S)) (hammingNorm u) : ℤ) : ℂ)
      = (Fintype.card (Fin 3 → ZMod 2 × ZMod 2) : ℂ) * (if u ∈ R then 1 else 0) :=
  PQ_klein rep hrep hR u

/-- **The Krawtchouk main theorem instantiates live at the Klein carrier, every hypothesis
constructed**: on `Fin 3 → ZMod 2 × ZMod 2` with the full monomial group, the split character
of an orbit adjacency at the spectral index of a dual orbit is the Krawtchouk number at
(weight of the primal representative, dual weight of the character) — no free hypotheses, so
the row cannot hold vacuously. -/
example (v : Fin 3 → ZMod 2 × ZMod 2) (χ : AddChar (Fin 3 → ZMod 2 × ZMod 2) ℂ) :
    ECCLib.splitChar ℂ
      ↥(schemeAlgebra
        (↥(monomialSubgroup (Fin 3) (ZMod 2 × ZMod 2) (AddAut (ZMod 2 × ZMod 2))))
        (Fin 3 → ZMod 2 × ZMod 2))
      (translationSpectrumEquiv ⟨orb _ χ, orb_mem_orbits χ⟩)
      ⟨adj (orb _ v), adj_mem_schemeAlgebra (orb_mem_orbits v)⟩
      = ((kraw (Fintype.card (ZMod 2 × ZMod 2)) (Fintype.card (Fin 3))
          (hammingNorm v) (dualWeight χ) : ℤ) : ℂ) :=
  splitChar_adj_eq_kraw klein_transOnNonzero (orb_mem_orbits v) (self_mem_orb v) _
    (self_mem_orb χ)

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.dualWeight_eq_iff_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.dualWeight_eq_iff_monomial

/-- info: 'ECCLib.Scheme.orb_eq_shellSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orb_eq_shellSet

/-- info: 'ECCLib.Scheme.qEnt_orbit_eq_kraw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.qEnt_orbit_eq_kraw

/-- info: 'ECCLib.Scheme.PQ_hamming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.PQ_hamming

/-- info: 'ECCLib.Scheme.PQ_klein' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.PQ_klein

/-- info: 'ECCLib.Scheme.pEnt_shell_eq_kraw' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.pEnt_shell_eq_kraw

/-- info: 'ECCLib.Scheme.splitChar_adj_eq_kraw' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.splitChar_adj_eq_kraw

/-- info: 'ECCLib.Scheme.spectralMult_hamming' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.spectralMult_hamming
