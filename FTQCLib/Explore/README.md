# FTQCLib/Explore — exploratory formalization

Buildable Lean **exploratory computations** toward open questions, kept separate from the main
library. Files here `import FTQCLib` freely, build standalone
(`lake build FTQCLib.Explore.<File>`), and are **not imported** by `FTQCLib.lean` (like
`FTQCLib/Examples/`) — they are not part of the default target and carry no stability promise.
Each records a small, decisive computation formally.

Conventions:
- one self-contained question per file; the module docstring states the question and how the
  outcome is read;
- `#print axioms` on any main result, target `[propext, Classical.choice, Quot.sound]`;
- a file that becomes part of the library proper moves into the relevant `FTQCLib/` subtree.

## Contents

- **Higher-order Fourier / higher-Weil**: toward a characteristic-2 higher-degree analogue of the
  Weil representation.
  - `CubicPolarization.lean` (axiom-clean) — the cubic phase polarizes to a symmetric trilinear
    cocycle; the nonclassical (`ZMod 8`) cubic lands at the sign level `4 = 2^{m-1}`.
  - `TowerPolarization.lean` (axiom-clean) — the two-axis generalization: the `m`-fold difference
    of `|v|` over `ZMod (2^m)` is the sign level `2^{m-1}` (`S`/`T`/`T^{1/2}`), and the degree-`d`
    multilinear monomial's `d`-fold difference is `1` (`CZ`/`CCZ`/`CCCZ`). The tower's
    top-difference law.
  - `CubicAut.lean` (axiom-clean) — the polarized CCZ cubic IS the determinant form, and every
    invertible 𝔽₂ matrix stabilizes it (`Aut = GL(3,𝔽₂)`, the char-2 collapse) — the naive
    "higher-Sp = Aut(cubic)" group route degenerates.
  - `LieClosure.lean` (axiom-clean) — the Lie framing: no alternating 3-cocycle exists (via
    `funcDerivG_comm`); `exp(D) = 1+D` exactly; integration = the abelian translation group. The
    Lie framing reduces to the cohomological one.
  - `FactorizationHomology.lean` (axiom-clean) — the factorization pair `(D, D+2)` is the Tate
    complex of the (free) shift action; globally EXACT with explicit hyperplane witnesses; the
    relative class on constants is nonzero (ℤ/4); the witness that kills it costs exactly one
    interaction degree. The framing is filtered homological algebra over `A[(𝔽₂)ⁿ]`.
  - `GroupDoors.lean` (axiom-clean) — the dichotomy lemma (nilpotent Lie algebras have no
    eigenvalue-1 ad-eigenvectors) settles `L(3)(𝔽₂) ≟ 𝔤₂(𝔽₂)` structurally for every nilpotent
    candidate; "Aut(cubic) ∩ Sp" is not posable as stated and identifies with the
    `frameDistortion` vanishing locus.
  - `FilteredTate.lean` (axiom-clean) — the Möbius basis diagonalizes the shift complex (two laws
    for `c_S(D_i f)`); the level filtration is Tate-stable; the graded action is the sign character
    (NOT trivial); the relative Tate group is computed exactly at every level
    (`normOp_witness_degLE_iff`), the death schedule is sharp, and the whole-group Ĥ⁰ is 0.
  - `KInvariantOne.lean` (axiom-clean) — the metaplectic 2-group's k-invariant at n = 1: explicit
    S₃ section, computed defect lifts, associator and the 6⁴ cocycle identity by `decide`. The
    Sylow restriction is identically zero, so [a]₁ = 0 modulo the (unformalized) transfer
    argument; the representative is nonzero (a(1,2,3) = 3). The band invariant, if nonzero, lives
    at n ≥ 2.
  - `GTwo.lean` (axiom-clean) — `𝔤₂(𝔽₂)` from root data alone; `g2` = the generated subalgebra of
    gl₁₄(𝔽₂); independence via an explicit probe matrix and its inverse; `⁅h_β,x_α⁆ = x_α ≠ 0` +
    the `GroupDoors` dichotomy ⇒ `g2_not_nilpotent`.
  - `GTwoCert.lean` (built on demand) — the closure equations (= the table's Jacobi identity;
    g2 = the 14-dimensional span). Verified by compiled evaluation; the kernel `decide` is a long,
    memory-heavy job. Imported by nothing; build it on an otherwise idle machine.
