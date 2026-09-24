/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basis
import FTQCLib.Gates.Clifford
import FTQCLib.Gates.CNOT
import FTQCLib.Stabilizer.Defs
import Mathlib.Data.Fin.Tuple.Basic

set_option linter.unusedSectionVars false

/-! # Transversal gates

A transversal gate on `m` blocks of `n` qubits is a Clifford operation on
`Pauli (m * n)` whose symplectic action decomposes as a tensor product

  U = V₁ ⊗ V₂ ⊗ ⋯ ⊗ Vₙ

where each `V_k` acts only on the `m` physical qubits at transversal
position `k`. In the simplest and most useful cases all the `V_k` are
equal: a single per-position gate `V` is applied at every position.

This file specialises to two-block transversal gates, viewing
`Pauli (n + n)` as two `n`-qubit blocks via the `Fin.castAdd n` /
`Fin.natAdd n` decomposition of `Fin (n + n)`. We define:

* **`transversalCNOT n`** — apply physical CNOT with control in block 1
  and target in block 2 at every transversal position `k : Fin n`.

We prove:

* **`transversalCNOT_isClifford`** — transversal CNOT is Clifford
  (preserves the symplectic form `omegaBilin`).
* **`transversalCNOT_X_block1`, `transversalCNOT_X_block2`,
  `transversalCNOT_Z_block1`, `transversalCNOT_Z_block2`** — the
  explicit symplectic-action formulas at each block × sector.

These formulas package the four propagation rules

  X(block 1, k) ↦ X(block 1, k)                  (X-control unchanged)
  X(block 2, k) ↦ X(block 2, k) + X(block 1, k)  (X-target picks up control)
  Z(block 1, k) ↦ Z(block 1, k) + Z(block 2, k)  (Z-control picks up target)
  Z(block 2, k) ↦ Z(block 2, k)                  (Z-target unchanged)

at every transversal position `k`, independently and in parallel.
-/

namespace FTQCLib.Codes

open FTQCLib.Pauli FTQCLib.Gates FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The symplectic action as named helper functions

We extract the `X`- and `Z`-component actions of transversal CNOT as
top-level functions before assembling the `LinearEquiv`. This pattern
makes the per-component `Fin.addCases` reductions accessible as `simp`
lemmas, which keeps the `LinearEquiv` field proofs from being defeated
by stuck lambda applications. -/

/-- The X-component of transversal CNOT applied to `p`. At position
`Fin.castAdd n k` (block 1), it equals `p.X (Fin.castAdd n k)`; at
position `Fin.natAdd n k` (block 2), it equals
`p.X (Fin.natAdd n k) + p.X (Fin.castAdd n k)`. -/
def tcnotX (p : Pauli (n + n)) : Fin (n + n) → ZMod 2 :=
  Fin.addCases
    (fun k : Fin n => p.X (Fin.castAdd n k))
    (fun k : Fin n => p.X (Fin.natAdd n k) + p.X (Fin.castAdd n k))

/-- The Z-component of transversal CNOT applied to `p`. At position
`Fin.castAdd n k` (block 1), it equals
`p.Z (Fin.castAdd n k) + p.Z (Fin.natAdd n k)`; at position
`Fin.natAdd n k` (block 2), it equals `p.Z (Fin.natAdd n k)`. -/
def tcnotZ (p : Pauli (n + n)) : Fin (n + n) → ZMod 2 :=
  Fin.addCases
    (fun k : Fin n => p.Z (Fin.castAdd n k) + p.Z (Fin.natAdd n k))
    (fun k : Fin n => p.Z (Fin.natAdd n k))

@[simp] theorem tcnotX_castAdd (p : Pauli (n + n)) (k : Fin n) :
    tcnotX p (Fin.castAdd n k) = p.X (Fin.castAdd n k) := by
  unfold tcnotX; rw [Fin.addCases_left]

/-- Simp-normal form of `tcnotX_natAdd`: the right-half index appears in
the simp-normal form `k.addNat n`, not `Fin.natAdd n k`. (Mathlib's
`Fin.natAdd_eq_addNat` is a simp lemma in the `natAdd → addNat` direction,
so post-simp goals carry `addNat`.) -/
@[simp] theorem tcnotX_addNat (p : Pauli (n + n)) (k : Fin n) :
    tcnotX p (k.addNat n) = p.X (k.addNat n) + p.X (Fin.castAdd n k) := by
  rw [← Fin.natAdd_eq_addNat]
  unfold tcnotX; rw [Fin.addCases_right]

@[simp] theorem tcnotZ_castAdd (p : Pauli (n + n)) (k : Fin n) :
    tcnotZ p (Fin.castAdd n k) = p.Z (Fin.castAdd n k) + p.Z (k.addNat n) := by
  rw [← Fin.natAdd_eq_addNat]
  unfold tcnotZ; rw [Fin.addCases_left]

@[simp] theorem tcnotZ_addNat (p : Pauli (n + n)) (k : Fin n) :
    tcnotZ p (k.addNat n) = p.Z (k.addNat n) := by
  rw [← Fin.natAdd_eq_addNat]
  unfold tcnotZ; rw [Fin.addCases_right]

/-- The per-component function applied to itself recovers the original
component, on the X side: tcnotX (⟨tcnotX p, tcnotZ p⟩) = p.X. The CNOT
gate is an involution over `ZMod 2`, so two applications cancel. -/
theorem tcnotX_tcnotX (p : Pauli (n + n)) :
    tcnotX ⟨tcnotX p, tcnotZ p⟩ = p.X := by
  funext i
  induction i using Fin.addCases with
  | left k => simp
  | right k =>
    -- Goal: tcnotX ⟨tcnotX p, tcnotZ p⟩ (Fin.natAdd n k) = p.X (Fin.natAdd n k)
    simp only [Fin.natAdd_eq_addNat, tcnotX_addNat, tcnotX_castAdd]
    -- (p.X (k.addNat n) + p.X (Fin.castAdd n k)) + p.X (Fin.castAdd n k)
    --   = p.X (k.addNat n)
    have hb : (p.X (Fin.castAdd n k) : ZMod 2) + p.X (Fin.castAdd n k) = 0 :=
      CharTwo.add_self_eq_zero _
    calc p.X (k.addNat n) + p.X (Fin.castAdd n k) + p.X (Fin.castAdd n k)
        = p.X (k.addNat n) + (p.X (Fin.castAdd n k) + p.X (Fin.castAdd n k)) :=
          add_assoc _ _ _
      _ = p.X (k.addNat n) + 0 := by rw [hb]
      _ = p.X (k.addNat n) := add_zero _

/-- The per-component function applied to itself recovers the original
component, on the Z side. -/
theorem tcnotZ_tcnotZ (p : Pauli (n + n)) :
    tcnotZ ⟨tcnotX p, tcnotZ p⟩ = p.Z := by
  funext i
  induction i using Fin.addCases with
  | left k =>
    -- Goal: tcnotZ ⟨tcnotX p, tcnotZ p⟩ (Fin.castAdd n k) = p.Z (Fin.castAdd n k)
    simp only [tcnotZ_castAdd, tcnotZ_addNat]
    -- p.Z (Fin.castAdd n k) + p.Z (k.addNat n) + p.Z (k.addNat n)
    --   = p.Z (Fin.castAdd n k)
    have hb : (p.Z (k.addNat n) : ZMod 2) + p.Z (k.addNat n) = 0 :=
      CharTwo.add_self_eq_zero _
    calc p.Z (Fin.castAdd n k) + p.Z (k.addNat n) + p.Z (k.addNat n)
        = p.Z (Fin.castAdd n k) + (p.Z (k.addNat n) + p.Z (k.addNat n)) :=
          add_assoc _ _ _
      _ = p.Z (Fin.castAdd n k) + 0 := by rw [hb]
      _ = p.Z (Fin.castAdd n k) := add_zero _
  | right k => simp

/-- The X-action is additive in the input Pauli. -/
theorem tcnotX_add (p q : Pauli (n + n)) :
    tcnotX (p + q) = tcnotX p + tcnotX q := by
  funext i
  induction i using Fin.addCases with
  | left k => simp [X_add]
  | right k => simp [X_add]; abel

/-- The Z-action is additive in the input Pauli. -/
theorem tcnotZ_add (p q : Pauli (n + n)) :
    tcnotZ (p + q) = tcnotZ p + tcnotZ q := by
  funext i
  induction i using Fin.addCases with
  | left k => simp [Z_add]; abel
  | right k => simp [Z_add]

/-- The X-action is `(ZMod 2)`-linear in the input Pauli. -/
theorem tcnotX_smul (c : ZMod 2) (p : Pauli (n + n)) :
    tcnotX (c • p) = c • tcnotX p := by
  funext i
  induction i using Fin.addCases with
  | left k => simp
  | right k => simp; ring

/-- The Z-action is `(ZMod 2)`-linear in the input Pauli. -/
theorem tcnotZ_smul (c : ZMod 2) (p : Pauli (n + n)) :
    tcnotZ (c • p) = c • tcnotZ p := by
  funext i
  induction i using Fin.addCases with
  | left k => simp; ring
  | right k => simp

/-! ## Transversal CNOT as a `LinearEquiv` -/

/-- Transversal CNOT across two `n`-qubit blocks. In `Pauli (n + n)` the
first `n` positions (`Fin.castAdd n k`, `k : Fin n`) form block 1 (the
"control" block) and the last `n` positions (`Fin.natAdd n k`) form
block 2 (the "target" block). The gate applies physical CNOT with
control in block 1 and target in block 2 at every transversal position
`k`. As an involution over `ZMod 2`, it is its own inverse. -/
def transversalCNOT (n : ℕ) : Pauli (n + n) ≃ₗ[ZMod 2] Pauli (n + n) where
  toFun p := ⟨tcnotX p, tcnotZ p⟩
  invFun p := ⟨tcnotX p, tcnotZ p⟩
  left_inv p := by
    apply Pauli.ext
    · exact tcnotX_tcnotX p
    · exact tcnotZ_tcnotZ p
  right_inv p := by
    apply Pauli.ext
    · exact tcnotX_tcnotX p
    · exact tcnotZ_tcnotZ p
  map_add' p q := by
    apply Pauli.ext
    · exact tcnotX_add p q
    · exact tcnotZ_add p q
  map_smul' c p := by
    apply Pauli.ext
    · exact tcnotX_smul c p
    · exact tcnotZ_smul c p

@[simp] theorem transversalCNOT_X (p : Pauli (n + n)) :
    ((transversalCNOT n) p).X = tcnotX p := rfl

@[simp] theorem transversalCNOT_Z (p : Pauli (n + n)) :
    ((transversalCNOT n) p).Z = tcnotZ p := rfl

/-! ## Symplectic action of `transversalCNOT` on the four block × sector
    components -/

/-- Transversal CNOT leaves block 1's X-sector unchanged. -/
@[simp] theorem transversalCNOT_X_block1 (p : Pauli (n + n)) (k : Fin n) :
    ((transversalCNOT n) p).X (Fin.castAdd n k) = p.X (Fin.castAdd n k) := by
  rw [transversalCNOT_X, tcnotX_castAdd]

/-- Transversal CNOT propagates block 1's X-sector into block 2. -/
@[simp] theorem transversalCNOT_X_block2 (p : Pauli (n + n)) (k : Fin n) :
    ((transversalCNOT n) p).X (k.addNat n) =
      p.X (k.addNat n) + p.X (Fin.castAdd n k) := by
  rw [transversalCNOT_X, tcnotX_addNat]

/-- Transversal CNOT propagates block 2's Z-sector into block 1. -/
@[simp] theorem transversalCNOT_Z_block1 (p : Pauli (n + n)) (k : Fin n) :
    ((transversalCNOT n) p).Z (Fin.castAdd n k) =
      p.Z (Fin.castAdd n k) + p.Z (k.addNat n) := by
  rw [transversalCNOT_Z, tcnotZ_castAdd]

/-- Transversal CNOT leaves block 2's Z-sector unchanged. -/
@[simp] theorem transversalCNOT_Z_block2 (p : Pauli (n + n)) (k : Fin n) :
    ((transversalCNOT n) p).Z (k.addNat n) = p.Z (k.addNat n) := by
  rw [transversalCNOT_Z, tcnotZ_addNat]

/-! ## Clifford property -/

/-- Transversal CNOT preserves the symplectic form `omega`. Each
transversal position contributes the same propagation rules as a
single-qubit CNOT, and across positions the contributions are
independent, so the cross-position omega bilinear pairing is preserved
sum-by-sum. The intra-position extra terms cancel in characteristic 2
(each cross term `p.Z (k.addNat n) * q.X (Fin.castAdd n k)` appears
twice, as does `p.X (Fin.castAdd n k) * q.Z (k.addNat n)`). -/
theorem transversalCNOT_preserves_omega (p q : Pauli (n + n)) :
    omega (transversalCNOT n p) (transversalCNOT n q) = omega p q := by
  unfold omega
  -- Split each sum over Fin (n + n) into cast- and nat-halves
  rw [Fin.sum_univ_add (fun i => (transversalCNOT n p).Z i * (transversalCNOT n q).X i),
      Fin.sum_univ_add (fun i => (transversalCNOT n p).X i * (transversalCNOT n q).Z i),
      Fin.sum_univ_add (fun i => p.Z i * q.X i),
      Fin.sum_univ_add (fun i => p.X i * q.Z i)]
  -- Rewrite each integrand using the tcnotX/tcnotZ propagation formulas
  simp only [transversalCNOT_X_block1, transversalCNOT_X_block2,
             transversalCNOT_Z_block1, transversalCNOT_Z_block2,
             Fin.natAdd_eq_addNat]
  -- Distribute and reorganize so that "wanted" terms match and "extra"
  -- terms cancel in characteristic 2. We do this by exhibiting an
  -- equality of finsums via Finset.sum_congr per block, then summing.
  -- Distribute multiplications inside each sum so the products separate.
  rw [show (∑ k : Fin n, (p.Z (Fin.castAdd n k) + p.Z (k.addNat n)) *
              q.X (Fin.castAdd n k)) =
            (∑ k : Fin n, p.Z (Fin.castAdd n k) * q.X (Fin.castAdd n k)) +
            (∑ k : Fin n, p.Z (k.addNat n) * q.X (Fin.castAdd n k)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => add_mul _ _ _]
  rw [show (∑ k : Fin n, p.Z (k.addNat n) *
              (q.X (k.addNat n) + q.X (Fin.castAdd n k))) =
            (∑ k : Fin n, p.Z (k.addNat n) * q.X (k.addNat n)) +
            (∑ k : Fin n, p.Z (k.addNat n) * q.X (Fin.castAdd n k)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => mul_add _ _ _]
  rw [show (∑ k : Fin n, p.X (Fin.castAdd n k) *
              (q.Z (Fin.castAdd n k) + q.Z (k.addNat n))) =
            (∑ k : Fin n, p.X (Fin.castAdd n k) * q.Z (Fin.castAdd n k)) +
            (∑ k : Fin n, p.X (Fin.castAdd n k) * q.Z (k.addNat n)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => mul_add _ _ _]
  rw [show (∑ k : Fin n, (p.X (k.addNat n) + p.X (Fin.castAdd n k)) *
              q.Z (k.addNat n)) =
            (∑ k : Fin n, p.X (k.addNat n) * q.Z (k.addNat n)) +
            (∑ k : Fin n, p.X (Fin.castAdd n k) * q.Z (k.addNat n)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => add_mul _ _ _]
  -- The RHS is similarly decomposed:
  --   ∑ ZX_cast + ∑ ZX_nat + ∑ XZ_cast + ∑ XZ_nat
  -- The LHS is the same plus two pairs of extra terms that cancel in CharTwo.
  -- Cross terms (each appears twice and cancels):
  --   ∑_k p.Z (k.addNat n) * q.X (Fin.castAdd n k)
  --   ∑_k p.X (Fin.castAdd n k) * q.Z (k.addNat n)
  have h_inner_cancel :
      ∀ (A : Fin n → ZMod 2), (∑ k, A k) + (∑ k, A k) = 0 := by
    intro A
    rw [← Finset.sum_add_distrib]
    refine (Finset.sum_eq_zero ?_)
    intro k _
    exact CharTwo.add_self_eq_zero (A k)
  set ZXcast := ∑ k : Fin n, p.Z (Fin.castAdd n k) * q.X (Fin.castAdd n k) with hZXcast
  set ZXnat := ∑ k : Fin n, p.Z (k.addNat n) * q.X (k.addNat n) with hZXnat
  set ZXcross := ∑ k : Fin n, p.Z (k.addNat n) * q.X (Fin.castAdd n k) with hZXcross
  set XZcast := ∑ k : Fin n, p.X (Fin.castAdd n k) * q.Z (Fin.castAdd n k) with hXZcast
  set XZnat := ∑ k : Fin n, p.X (k.addNat n) * q.Z (k.addNat n) with hXZnat
  set XZcross := ∑ k : Fin n, p.X (Fin.castAdd n k) * q.Z (k.addNat n) with hXZcross
  have hZXcross_cancel : ZXcross + ZXcross = 0 := h_inner_cancel _
  have hXZcross_cancel : XZcross + XZcross = 0 := h_inner_cancel _
  -- The two RHS sums match ZXnat with `i.addNat n` index notation up to alpha-renaming
  -- which Lean already canonicalizes. The goal reduces by additive rearrangement.
  -- We close with an `abel`-style rewrite + the two cancellations.
  -- LHS = (ZXcast + ZXcross) + (ZXnat + ZXcross) + ((XZcast + XZcross) + (XZnat + XZcross))
  -- RHS = ZXcast + ZXnat + (XZcast + XZnat)
  -- LHS - RHS = (ZXcross + ZXcross) + (XZcross + XZcross) = 0 + 0 = 0
  -- Equivalently, LHS = RHS + 0 + 0 = RHS.
  have hLHS_RHS :
      (ZXcast + ZXcross + (ZXnat + ZXcross) +
        (XZcast + XZcross + (XZnat + XZcross))) =
      (ZXcast + ZXnat + (XZcast + XZnat)) + ((ZXcross + ZXcross) + (XZcross + XZcross)) := by
    ring
  rw [hLHS_RHS, hZXcross_cancel, hXZcross_cancel, add_zero, add_zero]

/-- Transversal CNOT is Clifford: a symplectic transformation of the
bilinear form `omegaBilin`. -/
theorem transversalCNOT_isClifford :
    IsClifford (transversalCNOT n) :=
  fun p q => by simpa using transversalCNOT_preserves_omega p q

end FTQCLib.Codes
