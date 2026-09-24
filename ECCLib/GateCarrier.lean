/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GateField
import ECCLib.Distance
import Mathlib.FieldTheory.Finite.GaloisField

set_option linter.unusedSectionVars false

/-!
# The carrier as a first-class finite field, and the classification bridge

**The named carrier `AdjoinRoot ν` is the library's primary finite-field object** — it is the
only carrier with the certified netlist — and `GaloisField` is the classification anchor and
the no-named-`ν` fallback.

* **A — carrier finiteness, `Monic` only** (no irreducibility anywhere): `Fintype`, a single
  named `DecidableEq` instance (so every consumer elaborates with the same one — the
  `Distance.lean` discipline), `finrank = m + 1`, `card = 2^(m+1)`. Mathlib's finite-field
  theory (`IsGalois`, norms, cyclic units, the subfield classification) attaches to abstract
  `[Field] [Finite]` carriers, so once `ν` is irreducible the carrier gets all of it for free.
* **B — the classification bridge**: under `[Fact (Irreducible ν)]`,
  `AdjoinRoot ν ≃ₐ[ZMod 2] GaloisField 2 (m+1)` by one application of
  `GaloisField.algEquivGaloisFieldOfFintype` — the certificate that nothing is lost by working
  on the named carrier. Instantiated at `m = 3`: **`GF16 ≃ₐ[ZMod 2] GaloisField 2 4`**.
* **C — the abstract fallback**, scoped to `GaloisField 2 n`: `Fintype`, `DecidableEq`, and the
  `Fintype.card` form of the cardinality — for stating results at sizes with no certified `ν`
  (the named AES carrier `GF256` is certified separately, in `FieldCert.lean`).
* **D — smoke**: the coding layer accepts `GF16`, and — through the fallback — accepts
  `GaloisField 2 8`: Reed–Solomon-scale statements over GF(256) are available abstractly.

Instance hygiene: global instances only for the two specific families
(`AdjoinRoot (nu m r)`, `GaloisField 2 n`); the noncomputable `Fintype`s never sit on a `decide`
path (the examples decide live on the coordinate model); every card proof pins its field
argument (`Module.card_eq_pow_finrank (K := ZMod 2)` — Mathlib's own porting note at
`GaloisField.lean:94` documents the hazard).
-/

namespace ECCLib

open Module

/-! ## A — the carrier is a finite type, `Monic` only -/

variable (m : ℕ) (r : Fin (m + 1) → ZMod 2)

noncomputable instance : Fintype (AdjoinRoot (nu m r)) :=
  haveI := (nu_monic m r).finite_adjoinRoot
  haveI : Finite (AdjoinRoot (nu m r)) := Module.finite_of_finite (ZMod 2)
  Fintype.ofFinite _

/-- The one named `DecidableEq` instance for the carrier — every consumer elaborates with this
same instance. -/
noncomputable instance : DecidableEq (AdjoinRoot (nu m r)) := Classical.decEq _

theorem finrank_adjoinRoot_nu : Module.finrank (ZMod 2) (AdjoinRoot (nu m r)) = m + 1 := by
  rw [Module.finrank_eq_card_basis (adjBasis m r), Fintype.card_fin]

theorem card_adjoinRoot_nu : Fintype.card (AdjoinRoot (nu m r)) = 2 ^ (m + 1) := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := AdjoinRoot (nu m r)), ZMod.card,
    finrank_adjoinRoot_nu]

/-! ## B — the classification bridge -/

/-- **Nothing is lost on the named carrier**: whenever `ν` is irreducible, `AdjoinRoot ν` is
`AlgEquiv` to the Galois field of its cardinality — by library machinery applied to the
`Monic`-only cardinality above. -/
noncomputable def adjEquivGaloisField [Fact (Irreducible (nu m r))] :
    AdjoinRoot (nu m r) ≃ₐ[ZMod 2] GaloisField 2 (m + 1) :=
  GaloisField.algEquivGaloisFieldOfFintype 2 (m + 1) (card_adjoinRoot_nu m r)

/-- **The two GF(16)s are one**: the named-polynomial carrier and Mathlib's splitting-field
construction, connected. -/
noncomputable def gf16EquivGaloisField : GF16 ≃ₐ[ZMod 2] GaloisField 2 4 :=
  adjEquivGaloisField 3 r4

theorem card_GF16 : Fintype.card GF16 = 16 := card_adjoinRoot_nu 3 r4

/-! ## C — the abstract fallback, scoped to characteristic 2 -/

noncomputable instance (n : ℕ) : Fintype (GaloisField 2 n) := Fintype.ofFinite _

noncomputable instance (n : ℕ) : DecidableEq (GaloisField 2 n) := Classical.decEq _

theorem card_galoisField_two (n : ℕ) (hn : n ≠ 0) :
    Fintype.card (GaloisField 2 n) = 2 ^ n := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 n hn]

/-! ## D — smoke: the coding layer accepts both carriers -/

-- the named carrier is a genuine finite field:
noncomputable example : Field GF16 := inferInstance
noncomputable example : Fintype GF16 := inferInstance

-- the coding layer accepts GF16 (the Singleton bound, at the carrier):
example (C : Submodule GF16 (Fin 7 → GF16)) :
    Coding.minDist C + Module.finrank GF16 C ≤ 7 + 1 := by
  simpa using Coding.singleton_bound C

-- and, through the fallback, GF(256) is available to the coding layer TODAY — abstractly, with
-- only the netlist connection awaiting the named m = 8 polynomial:
example (C : Submodule (GaloisField 2 8) (Fin 5 → GaloisField 2 8)) :
    Coding.minDist C + Module.finrank (GaloisField 2 8) C ≤ 5 + 1 := by
  simpa using Coding.singleton_bound C

end ECCLib
