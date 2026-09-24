/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.HammingScheme
import ECCLib.Scheme.HammingOrthogonality

/-!
# The Hamming graph and the hypercube

The translation-side twin of `Scheme/Kneser.lean`: the **Hamming graph** `H(n,q)` — words
adjacent at Hamming distance `1` — is the weight-`1` relation of the Hamming scheme, so the
Krawtchouk identification of the eigenmatrices (`splitChar_adj_eq_kraw`) hands over its
complete spectrum through the degree-one Krawtchouk closed form (`kraw_one`): eigenvalue
`(q−1)n − q·w` on the eigenspace of canonical index `w`, of dimension `C(n,w)·(q−1)^w`
(`spectralMult_hamming`). At `q = 2` this is the **hypercube** `Q_n`: eigenvalues `n − 2w`
with multiplicities `C(n,w)`. The bridge is one triviality (`zmod_two_transOnNonzero`: any
group is transitive on the one nonzero element of `ZMod 2`) and two rewrites; nothing else is
new.

## Main results

* `splitChar_adj_hammingGraph` — **the Hamming graph spectrum**: the eigenvalue of the
  distance-`1` adjacency at the spectral index of a dual orbit of dual weight `w` is
  `(q−1)n − q·w`.
* `zmod_two_transOnNonzero` — the binary alphabet satisfies the transitivity hypothesis
  under any group.
* `splitChar_adj_hypercube`, `spectralMult_hypercube` — the `q = 2` reading: eigenvalues
  `n − 2w`, multiplicities `C(n,w)`, no transitivity hypothesis left.
-/

namespace ECCLib.Scheme

open Finset MulAction ECCLib.Delsarte

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
variable {G : Type*} [Group G] [Finite G] [DistribMulAction G A]

omit [Finite G] in
/-- **The Hamming graph spectrum**: the split-character value of a distance-`1` adjacency
at the spectral index of a dual orbit is `(q−1)n − q·w`, `w` the dual weight of any
representative — `splitChar_adj_eq_kraw` evaluated through the degree-one closed
form, the guard `w ≤ n` discharged by `dualWeight_le`. -/
theorem splitChar_adj_hammingGraph (htrans : TransOnNonzero G A)
    {R : Finset (ι → A)}
    (hR : R ∈ orbits (↥(monomialSubgroup ι A G)) (ι → A)) {x : ι → A} (hx : x ∈ R)
    (hx1 : hammingNorm x = 1)
    (S : ↥(orbits (↥(monomialSubgroup ι A G)) (AddChar (ι → A) ℂ)))
    {χ₀ : AddChar (ι → A) ℂ} (hχ₀ : χ₀ ∈ (S : Finset (AddChar (ι → A) ℂ))) :
    ECCLib.splitChar ℂ ↥(schemeAlgebra (↥(monomialSubgroup ι A G)) (ι → A))
      (translationSpectrumEquiv S) ⟨adj R, adj_mem_schemeAlgebra hR⟩
      = ((((Fintype.card A : ℤ) - 1) * Fintype.card ι
          - Fintype.card A * dualWeight χ₀ : ℤ) : ℂ) := by
  rw [splitChar_adj_eq_kraw htrans hR hx S hχ₀, hx1,
    kraw_one _ _ _ (dualWeight_le χ₀)]

omit [Fintype ι] [DecidableEq ι] [AddCommGroup A] [Fintype A] [DecidableEq A]
  [Finite G] [DistribMulAction G A] in
/-- Any group is transitive on the nonzero elements of the binary alphabet — there is
only one. This is what removes the transitivity hypothesis from every hypercube reading
of the Hamming spectrum. -/
theorem zmod_two_transOnNonzero [DistribMulAction G (ZMod 2)] :
    TransOnNonzero G (ZMod 2) := by
  intro a b ha hb
  have h : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  refine ⟨1, ?_⟩
  rw [one_smul, h a ha, h b hb]

omit [Finite G] in
/-- **The hypercube spectrum**: at the binary alphabet the distance-`1`
adjacency — the hypercube `Q_n` — has eigenvalue `n − 2w` at the spectral index of dual
weight `w`, with no transitivity hypothesis. -/
theorem splitChar_adj_hypercube [DistribMulAction G (ZMod 2)]
    {R : Finset (ι → ZMod 2)}
    (hR : R ∈ orbits (↥(monomialSubgroup ι (ZMod 2) G)) (ι → ZMod 2))
    {x : ι → ZMod 2} (hx : x ∈ R) (hx1 : hammingNorm x = 1)
    (S : ↥(orbits (↥(monomialSubgroup ι (ZMod 2) G)) (AddChar (ι → ZMod 2) ℂ)))
    {χ₀ : AddChar (ι → ZMod 2) ℂ} (hχ₀ : χ₀ ∈ (S : Finset (AddChar (ι → ZMod 2) ℂ))) :
    ECCLib.splitChar ℂ
      ↥(schemeAlgebra (↥(monomialSubgroup ι (ZMod 2) G)) (ι → ZMod 2))
      (translationSpectrumEquiv S) ⟨adj R, adj_mem_schemeAlgebra hR⟩
      = (((Fintype.card ι : ℤ) - 2 * dualWeight χ₀ : ℤ) : ℂ) := by
  rw [splitChar_adj_hammingGraph zmod_two_transOnNonzero hR hx hx1 S hχ₀]
  norm_num [ZMod.card]

/-- **The hypercube multiplicities**: at the binary alphabet the eigenspace of dual
weight `w` has dimension `C(n,w)` — the binomial row, `(q−1)^w = 1`. -/
theorem spectralMult_hypercube [DistribMulAction G (ZMod 2)]
    (S : ↥(orbits (↥(monomialSubgroup ι (ZMod 2) G)) (AddChar (ι → ZMod 2) ℂ)))
    {ξ : AddChar (ι → ZMod 2) ℂ} (hξ : ξ ∈ (S : Finset (AddChar (ι → ZMod 2) ℂ))) :
    spectralMult (schemeAlgebra (↥(monomialSubgroup ι (ZMod 2) G)) (ι → ZMod 2))
        (translationSpectrumEquiv S)
      = (Fintype.card ι).choose (dualWeight ξ) := by
  rw [spectralMult_hamming zmod_two_transOnNonzero S hξ]
  norm_num [ZMod.card]

end ECCLib.Scheme
