/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.HammingDual
import ECCLib.Scheme.Spectrum
import ECCLib.Scheme.TranslationSpectrum

/-!
# The Hamming scheme as an instance of the abstract layer

The abstract scheme layer proves `P · Q = |V| · I` for any finite abelian group under any
finite symmetry group (`Spectrum.PQ_eq`). This module instantiates it at the Hamming setting
and reads the entries off, which is what turns a statement about orbits into the classical
one about weight shells and Krawtchouk numbers.

Both index sets are weight shells: the primal orbits by `orb_eq_shell`, the dual
orbits by `orb_eq_shellSet`. The `Q`-entries are Krawtchouk numbers by
`qEnt_shellSet`. So the abstract identity becomes, for a primal shell `R` and a
word `u`,

`∑ over dual shells, P(R, ·) · K_{dual weight}(‖u‖) = qⁿ · [u ∈ R]`.

## Main results

* `qEnt_orbit_eq_kraw` — the `Q`-entry at a dual orbit is a Krawtchouk number, indexed by the
  dual weight of any representative.
* `PQ_hamming` — `P · Q = qⁿ · I` at the Hamming scheme, with the `Q`-entries exhibited as
  Krawtchouk numbers.
* `PQ_klein` — the same at the Klein (Pauli) alphabet, where transitivity holds by
  `klein_transOnNonzero`.

## Implementation notes

**No self-duality of the alphabet is needed.** Identifying the `P`-entries as Krawtchouk
numbers might seem to need an identification `A ≃ AddChar A ℂ`, but it does not: the primal
generating-function mirror (`Delsarte/Shell.lean`'s `wordShellSum`)
reaches the `P`-entries with no self-duality anywhere — `pEnt_shell_eq_kraw` below, and
through the translation-spectrum identification, `splitChar_adj_eq_kraw`: **both eigenmatrices
of the Hamming scheme are Krawtchouk matrices, in the canonical `MaximalSpectrum` index.**
-/

namespace ECCLib.Scheme

open Finset MulAction ECCLib.Delsarte
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
variable {G : Type*} [Group G] [Finite G] [DistribMulAction G A]

/-- **The `Q`-entry at a dual orbit is a Krawtchouk number.** The orbit is a dual weight shell
(`orb_eq_shellSet`), and the class sum of a dual shell is a Krawtchouk number
(`qEnt_shellSet`); the index is the dual weight of any representative, since the dual weight
is constant on an orbit. -/
theorem qEnt_orbit_eq_kraw (htrans : TransOnNonzero G A)
    {S : Finset (AddChar (ι → A) ℂ)}
    (hS : S ∈ orbits (↥(monomialSubgroup ι A G)) (AddChar (ι → A) ℂ))
    {χ : AddChar (ι → A) ℂ} (hχ : χ ∈ S) (u : ι → A) :
    qEnt S u
      = ((kraw (Fintype.card A) (Fintype.card ι) (dualWeight χ) (hammingNorm u) : ℤ) : ℂ) := by
  classical
  have horb : orb (↥(monomialSubgroup ι A G)) χ = S := (mem_iff_orb_eq hS).mp hχ
  rw [← horb, orb_eq_shellSet htrans, qEnt_shellSet]

/-- **`P · Q = qⁿ · I` at the Hamming scheme.** The abstract eigenmatrix duality with the
`Q`-entries read off as Krawtchouk numbers. -/
theorem PQ_hamming (htrans : TransOnNonzero G A)
    (rep : Finset (AddChar (ι → A) ℂ) → AddChar (ι → A) ℂ)
    (hrep : ∀ S ∈ orbits (↥(monomialSubgroup ι A G)) (AddChar (ι → A) ℂ), rep S ∈ S)
    {R : Finset (ι → A)} (hR : R ∈ orbits (↥(monomialSubgroup ι A G)) (ι → A))
    (u : ι → A) :
    ∑ S ∈ orbits (↥(monomialSubgroup ι A G)) (AddChar (ι → A) ℂ),
        pEnt R (rep S)
          * ((kraw (Fintype.card A) (Fintype.card ι) (dualWeight (rep S))
              (hammingNorm u) : ℤ) : ℂ)
      = (Fintype.card (ι → A) : ℂ) * (if u ∈ R then 1 else 0) := by
  classical
  rw [← PQ_eq rep hrep hR u]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [qEnt_orbit_eq_kraw htrans hS (hrep S hS) u]

omit [Finite G] in
/-- The primal shells really are the index set on the other side: `R` above ranges over the
Hamming weight shells (`orb_eq_shell`). -/
theorem mem_orbits_iff_shell (htrans : TransOnNonzero G A) (x : ι → A) :
    orb (↥(monomialSubgroup ι A G)) x
      = Finset.univ.filter (fun y => hammingNorm y = hammingNorm x) :=
  orb_eq_shell htrans x

/-- **The Pauli instance.** At the Klein alphabet the transitivity hypothesis holds, so the
eigenmatrix duality reads off with no side condition. This is the Pauli case at full
strength: both index sets are weight shells and the `Q`-entries are Krawtchouk numbers. -/
theorem PQ_klein
    (rep : Finset (AddChar (ι → ZMod 2 × ZMod 2) ℂ) → AddChar (ι → ZMod 2 × ZMod 2) ℂ)
    (hrep : ∀ S ∈ orbits (↥(monomialSubgroup ι (ZMod 2 × ZMod 2)
        (AddAut (ZMod 2 × ZMod 2)))) (AddChar (ι → ZMod 2 × ZMod 2) ℂ), rep S ∈ S)
    {R : Finset (ι → ZMod 2 × ZMod 2)}
    (hR : R ∈ orbits (↥(monomialSubgroup ι (ZMod 2 × ZMod 2)
        (AddAut (ZMod 2 × ZMod 2)))) (ι → ZMod 2 × ZMod 2))
    (u : ι → ZMod 2 × ZMod 2) :
    ∑ S ∈ orbits (↥(monomialSubgroup ι (ZMod 2 × ZMod 2) (AddAut (ZMod 2 × ZMod 2))))
        (AddChar (ι → ZMod 2 × ZMod 2) ℂ),
        pEnt R (rep S)
          * ((kraw (Fintype.card (ZMod 2 × ZMod 2)) (Fintype.card ι) (dualWeight (rep S))
              (hammingNorm u) : ℤ) : ℂ)
      = (Fintype.card (ι → ZMod 2 × ZMod 2) : ℂ) * (if u ∈ R then 1 else 0) :=
  PQ_hamming klein_transOnNonzero rep hrep hR u

/-! ## The `P`-entries are Krawtchouk numbers — no self-duality -/

/-- **The `P`-entry at a weight shell is a Krawtchouk number.** `pEnt` conjugates the
character; conjugation is evaluation at the negation, negation preserves the shell, and the
primal shell character sum (`wordShellSum`) is the Krawtchouk number at the dual weight. -/
theorem pEnt_shell_eq_kraw (w : ℕ) (ξ : AddChar (ι → A) ℂ) :
    pEnt (Finset.univ.filter fun v : ι → A => hammingNorm v = w) ξ
      = ((kraw (Fintype.card A) (Fintype.card ι) w (dualWeight ξ) : ℤ) : ℂ) := by
  classical
  rw [pEnt]
  have hstep : ∀ v ∈ Finset.univ.filter (fun v : ι → A => hammingNorm v = w),
      (starRingEnd ℂ) (ξ v) = ξ (-v) := fun v _ =>
    (AddChar.map_neg_eq_conj ξ v).symm
  rw [Finset.sum_congr rfl hstep]
  rw [show (∑ v ∈ Finset.univ.filter (fun v : ι → A => hammingNorm v = w), ξ (-v))
      = ∑ v ∈ Finset.univ.filter (fun v : ι → A => hammingNorm v = w), ξ v from
    Finset.sum_nbij' (i := fun v => -v) (j := fun v => -v)
      (fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (ECCLib.Delsarte.hammingNorm_neg v).trans (Finset.mem_filter.mp hv).2⟩)
      (fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (ECCLib.Delsarte.hammingNorm_neg v).trans (Finset.mem_filter.mp hv).2⟩)
      (fun v _ => neg_neg v) (fun v _ => neg_neg v)
      (fun v _ => rfl)]
  have hfac : ∀ v : ι → A, ξ v = tupleChar (coordChar ξ) v := by
    intro v
    conv_lhs => rw [← piChar_coordChar ξ]
    rw [piChar_apply, tupleChar]
  rw [Finset.sum_congr rfl fun v _ => hfac v, wordShellSum]
  rfl

omit [Finite G] in
/-- **Both eigenmatrices of the Hamming scheme are Krawtchouk matrices, canonically
indexed**: through the translation-spectrum identification, the split-character value of a
shell adjacency at the spectral index of a dual orbit is the Krawtchouk number at
(shell weight, dual weight). No self-duality of the alphabet is used. -/
theorem splitChar_adj_eq_kraw (htrans : TransOnNonzero G A)
    {R : Finset (ι → A)}
    (hR : R ∈ orbits (↥(monomialSubgroup ι A G)) (ι → A)) {x : ι → A} (hx : x ∈ R)
    (S : ↥(orbits (↥(monomialSubgroup ι A G)) (AddChar (ι → A) ℂ)))
    {χ₀ : AddChar (ι → A) ℂ} (hχ₀ : χ₀ ∈ (S : Finset (AddChar (ι → A) ℂ))) :
    ECCLib.splitChar ℂ ↥(schemeAlgebra (↥(monomialSubgroup ι A G)) (ι → A))
      (translationSpectrumEquiv S) ⟨adj R, adj_mem_schemeAlgebra hR⟩
      = ((kraw (Fintype.card A) (Fintype.card ι) (hammingNorm x) (dualWeight χ₀) : ℤ) : ℂ)
      := by
  rw [splitChar_adj_eq_pEnt hR S hχ₀]
  have hshell : R = Finset.univ.filter (fun y : ι → A => hammingNorm y = hammingNorm x) := by
    rw [← (mem_iff_orb_eq hR).mp hx]
    exact orb_eq_shell htrans x
  rw [hshell, pEnt_shell_eq_kraw]

/-- **The Hamming multiplicities**: at the spectral index of a dual orbit with a
representative of dual weight `w`, the multiplicity is the shell size `C(n,w)·(q−1)^w` —
both eigenmatrices Krawtchouk, multiplicities the binomial shell counts, all in the
canonical index. -/
theorem spectralMult_hamming (htrans : TransOnNonzero G A)
    (S : ↥(orbits (↥(monomialSubgroup ι A G)) (AddChar (ι → A) ℂ)))
    {ξ : AddChar (ι → A) ℂ} (hξ : ξ ∈ (S : Finset (AddChar (ι → A) ℂ))) :
    spectralMult (schemeAlgebra (↥(monomialSubgroup ι A G)) (ι → A))
        (translationSpectrumEquiv S)
      = (Fintype.card ι).choose (dualWeight ξ)
          * (Fintype.card A - 1) ^ (dualWeight ξ) := by
  rw [spectralMult_translationSpectrumEquiv]
  rw [show (S : Finset (AddChar (ι → A) ℂ))
      = orb (↥(monomialSubgroup ι A G)) ξ from ((mem_iff_orb_eq S.2).mp hξ).symm]
  rw [orb_eq_shellSet htrans ξ, card_shellSet]

end ECCLib.Scheme
