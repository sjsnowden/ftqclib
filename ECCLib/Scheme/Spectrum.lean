/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Translation
import ECCLib.Scheme.LP
import Mathlib.RingTheory.Idempotents

/-!
# The spectral layer: diagonalization, idempotents, and the eigenmatrix duality

* **Diagonalisation — `circulant_mulVec_char`**: every character `χ` is an eigenvector of every
  circulant `circulant k`, with eigenvalue `eig k χ = Σ_v k v · conj(χ v)` (plain sum,
  conjugate on the `P` side); eigenvalues are multiplicative across the
  convolution product (`eig_mulVec`); on an orbit adjacency `adj R` the eigenvalue is
  `pEnt R χ = Σ_{v∈R} conj(χ v)`, constant along dual `H`-orbits (`pEnt_dual_smul`).
* **Idempotents — `charProj χ = circulant (|V|⁻¹ • χ)`** is the rank-one projector onto the
  `χ`-line (`charProj_mulVec_char`: it fixes `χ`, kills every other character — the
  un-negated span), and the family is Mathlib's `CompleteOrthogonalIdempotents`; summing
  over a dual class gives `orbProj S`, a member of the scheme algebra, and the dual-orbit
  family is again complete orthogonal idempotents (`completeOrthogonalIdempotents_orbProj`).
* **The eigenmatrix duality `PQ = |V|·I`** — `PQ_eq`, UNCONDITIONAL, for ANY choice of
  dual-orbit representatives (the representative-independence is the content of
  `pEnt_dual_smul`); the two change-of-basis expansions `adj_eq_sum_orbProj` and
  `orbProj_eq_sum_adj` (the latter representative-free through `orbVal`).

The dual orbits are `orbits H (AddChar V ℂ)` under the scoped contragredient action of
`Scheme/Orbits.lean`; the classical `Fintype`/`DecidableEq` on characters are Mathlib's
(no kernel computation is ever indexed by them). The file is sectioned by instance need:
characters only, then `DecidableEq V` (Finset membership), then the group `H`.
References: Delsarte 1973 §2.3 (2.13)–(2.16), Martin–Tanaka 2009 §6 (19)–(21),
Godsil 2010 §2.1.
-/

namespace ECCLib.Scheme

open Finset Matrix
open scoped BigOperators ComplexConjugate

/-! ## Characters only: eigenvalues, rank-one projectors, dual-class idempotents -/

section Characters

variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- Group orthogonality in the plain-sum normalisation:
`Σ_u χ u · conj(η u) = |V|·[χ = η]`. -/
theorem sum_char_mul_conj_group (χ η : AddChar V ℂ) :
    ∑ u : V, χ u * conj (η u) = if χ = η then (Fintype.card V : ℂ) else 0 := by
  have h : (fun u => χ u * conj (η u)) = (fun u => (χ - η) u) := by
    funext u
    rw [AddChar.sub_apply, AddChar.map_neg_eq_conj]
  rw [h, AddChar.sum_eq_ite (χ - η)]
  simp only [sub_eq_zero]

/-- The eigenvalue of `circulant k` on the character `χ`: a plain character sum, conjugate
on the `P` side. -/
noncomputable def eig (k : V → ℂ) (χ : AddChar V ℂ) : ℂ := ∑ v : V, k v * conj (χ v)

/-- **Simultaneous diagonalisation**: every character is an eigenvector of every
circulant. -/
theorem circulant_mulVec_char (k : V → ℂ) (χ : AddChar V ℂ) :
    Matrix.circulant k *ᵥ (⇑χ) = eig k χ • (⇑χ) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, Pi.smul_apply, smul_eq_mul, eig]
  rw [← Equiv.sum_comp (Equiv.subLeft i) (fun j => k (i - j) * χ j), Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [show i - u = i + (-u) by abel, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  ring

/-- Eigenvalues are multiplicative across the convolution product: `eig` is a character of
the translation algebra. -/
theorem eig_mulVec (k l : V → ℂ) (χ : AddChar V ℂ) :
    eig (Matrix.circulant k *ᵥ l) χ = eig k χ * eig l χ := by
  have h := congrFun (circulant_mulVec_char (Matrix.circulant k *ᵥ l) χ) 0
  rw [← Matrix.circulant_mul, ← Matrix.mulVec_mulVec, circulant_mulVec_char l,
    Matrix.mulVec_smul, circulant_mulVec_char k] at h
  simp only [Pi.smul_apply, smul_eq_mul, AddChar.map_zero_eq_one, mul_one] at h
  rw [mul_comm]
  exact h.symm

/-- The rank-one spectral projector attached to a character. -/
noncomputable def charProj (χ : AddChar V ℂ) : Matrix V V ℂ :=
  Matrix.circulant (fun v => (Fintype.card V : ℂ)⁻¹ * χ v)

/-- `charProj χ` fixes `χ` and kills every other character — the projection onto the
`χ`-line (the UN-negated span). -/
theorem charProj_mulVec_char (χ η : AddChar V ℂ) :
    charProj χ *ᵥ (⇑η) = (if χ = η then (1 : ℂ) else 0) • (⇑η) := by
  rw [charProj, circulant_mulVec_char]
  congr 1
  simp only [eig, mul_assoc, ← Finset.mul_sum, sum_char_mul_conj_group]
  split_ifs with h
  · exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  · simp

theorem charProj_mul_apply (χ η : AddChar V ℂ) (i j : V) :
    (charProj χ * charProj η) i j
      = (Fintype.card V : ℂ)⁻¹ * (Fintype.card V : ℂ)⁻¹ * η (i - j)
          * (if χ = η then (Fintype.card V : ℂ) else 0) := by
  simp only [Matrix.mul_apply, charProj, Matrix.circulant_apply]
  rw [← Equiv.sum_comp (Equiv.subLeft i) (fun l => (Fintype.card V : ℂ)⁻¹ * χ (i - l) *
    ((Fintype.card V : ℂ)⁻¹ * η (l - j)))]
  have hstep : ∀ u : V, (Fintype.card V : ℂ)⁻¹ * χ (i - (i - u)) *
      ((Fintype.card V : ℂ)⁻¹ * η ((i - u) - j))
      = ((Fintype.card V : ℂ)⁻¹ * (Fintype.card V : ℂ)⁻¹ * η (i - j)) * (χ u * conj (η u)) := by
    intro u
    rw [sub_sub_cancel, show i - u - j = (i - j) + (-u) by abel, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_conj]
    ring
  simp only [Equiv.subLeft_apply]
  rw [Finset.sum_congr rfl fun u _ => hstep u, ← Finset.mul_sum, sum_char_mul_conj_group]

theorem charProj_mul (χ η : AddChar V ℂ) :
    charProj χ * charProj η = if χ = η then charProj χ else 0 := by
  have hN : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  rw [charProj_mul_apply]
  split_ifs with h
  · subst h
    simp only [charProj, Matrix.circulant_apply]
    field_simp
  · simp

/-- The spectral projector has unit trace: it projects onto a line. -/
theorem trace_charProj (χ : AddChar V ℂ) : (charProj χ).trace = 1 := by
  rw [charProj, Matrix.trace]
  rw [show ∑ v, (Matrix.circulant fun v => (Fintype.card V : ℂ)⁻¹ * χ v).diag v
      = ∑ _v : V, (Fintype.card V : ℂ)⁻¹ * χ 0 from
    Finset.sum_congr rfl fun v _ => by
      rw [Matrix.diag_apply, Matrix.circulant_apply, sub_self]]
  rw [AddChar.map_zero_eq_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  exact_mod_cast Fintype.card_ne_zero

theorem charProj_mul_self (χ : AddChar V ℂ) : charProj χ * charProj χ = charProj χ := by
  rw [charProj_mul, if_pos rfl]

theorem charProj_mul_of_ne {χ η : AddChar V ℂ} (h : χ ≠ η) : charProj χ * charProj η = 0 := by
  rw [charProj_mul, if_neg h]

/-- The `P`-entry: the eigenvalue of the adjacency operator of the class `R` on `χ`. -/
noncomputable def pEnt (R : Finset V) (χ : AddChar V ℂ) : ℂ := ∑ v ∈ R, conj (χ v)

/-- The idempotent of a dual class: the sum of its rank-one projectors. -/
noncomputable def orbProj (S : Finset (AddChar V ℂ)) : Matrix V V ℂ := ∑ χ ∈ S, charProj χ

/-- `orbProj S` is the circulant of `|V|⁻¹ · qEnt S`. -/
theorem orbProj_eq_circulant (S : Finset (AddChar V ℂ)) :
    orbProj S = Matrix.circulant (fun v => (Fintype.card V : ℂ)⁻¹ * qEnt S v) := by
  ext i j
  simp only [orbProj, Matrix.sum_apply, charProj, Matrix.circulant_apply, qEnt, Finset.mul_sum]

theorem orbProj_mul_orbProj (S T : Finset (AddChar V ℂ)) :
    orbProj S * orbProj T = ∑ χ ∈ S ∩ T, charProj χ := by
  simp only [orbProj, Finset.sum_mul_sum, charProj_mul]
  rw [Finset.sum_congr rfl fun χ _ => Finset.sum_ite_eq T χ (fun _ => charProj χ)]
  exact Finset.sum_ite_mem S T charProj

theorem orbProj_mul_self (S : Finset (AddChar V ℂ)) : orbProj S * orbProj S = orbProj S := by
  rw [orbProj_mul_orbProj, Finset.inter_self]
  rfl

end Characters

/-! ## With `DecidableEq V`: classes as `Finset`s -/

section Classes

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The rank-one projectors sum to the identity (Fourier inversion, in matrix clothing). -/
theorem sum_charProj : ∑ χ : AddChar V ℂ, charProj (V := V) χ = 1 := by
  have hN : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hstep : ∑ χ : AddChar V ℂ, charProj (V := V) χ
      = Matrix.circulant (fun v : V => (Fintype.card V : ℂ)⁻¹ * ∑ χ : AddChar V ℂ, χ v) := by
    ext i j
    simp only [Matrix.sum_apply, charProj, Matrix.circulant_apply, Finset.mul_sum]
  rw [hstep, show (fun v : V => (Fintype.card V : ℂ)⁻¹ * ∑ χ : AddChar V ℂ, χ v)
      = (Pi.single 0 1 : V → ℂ) from ?_]
  · exact Matrix.circulant_single_one ℂ V
  · funext v
    rw [AddChar.sum_apply_eq_ite, Pi.single_apply]
    by_cases hv : v = 0
    · subst hv
      simp [hN]
    · rw [if_neg hv, if_neg hv, mul_zero]

/-- **At the finest grain**: the rank-one projectors are complete orthogonal idempotents. -/
theorem completeOrthogonalIdempotents_charProj :
    CompleteOrthogonalIdempotents (charProj (V := V)) :=
  ⟨⟨fun χ => charProj_mul_self χ, fun _ _ hne => charProj_mul_of_ne hne⟩, sum_charProj⟩

theorem pEnt_eq_eig (R : Finset V) (χ : AddChar V ℂ) :
    pEnt R χ = eig (fun v => if v ∈ R then (1 : ℂ) else 0) χ := by
  simp only [pEnt, eig, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The eigenvalue equation at the matrix level**: the adjacency of any class acts on each
rank-one projector by its `P`-entry. -/
theorem adj_mul_charProj (R : Finset V) (χ : AddChar V ℂ) :
    adj R * charProj χ = pEnt R χ • charProj χ := by
  rw [adj, charProj, Matrix.circulant_mul]
  have hfun : (fun v => (Fintype.card V : ℂ)⁻¹ * χ v)
      = (Fintype.card V : ℂ)⁻¹ • ⇑χ := funext fun v => rfl
  rw [hfun, Matrix.mulVec_smul, circulant_mulVec_char, ← pEnt_eq_eig, smul_comm,
    Matrix.circulant_smul, Matrix.circulant_smul]


/-- The adjacency operator of a class acts on `χ` by its `P`-entry. -/
theorem adj_mulVec_char (R : Finset V) (χ : AddChar V ℂ) :
    adj R *ᵥ (⇑χ) = pEnt R χ • (⇑χ) := by
  rw [adj, circulant_mulVec_char, pEnt_eq_eig]

/-- **The `PQ` core** (`P·Q = |V|·I` before orbit indexing): pairing the `P`-entries of a class
against all characters at a point detects membership in the class. -/
theorem sum_pEnt_mul (R : Finset V) (u : V) :
    ∑ χ : AddChar V ℂ, pEnt R χ * χ u = (Fintype.card V : ℂ) * (if u ∈ R then 1 else 0) := by
  simp only [pEnt, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hstep : ∀ v ∈ R, ∑ χ : AddChar V ℂ, conj (χ v) * χ u
      = if u = v then (Fintype.card V : ℂ) else 0 := by
    intro v _
    have hpt : ∀ χ : AddChar V ℂ, conj (χ v) * χ u = χ (u - v) := by
      intro χ
      rw [show u - v = u + (-v) by abel, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
      ring
    rw [Finset.sum_congr rfl fun χ _ => hpt χ, AddChar.sum_apply_eq_ite]
    simp only [sub_eq_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq R u (fun _ => (Fintype.card V : ℂ))]
  by_cases hu : u ∈ R
  · rw [if_pos hu, if_pos hu, mul_one]
  · rw [if_neg hu, if_neg hu, mul_zero]

end Classes

/-! ## With the symmetry group `H`: constancy on orbits, the dual-orbit idempotents, `PQ` -/

section Orbit

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {H : Type*} [Group H] [Fintype H] [DistribMulAction H V]

/-- **Dual-orbit constancy of the eigenvalues**: the `P`-entry of an orbit adjacency is
constant along the dual `H`-orbits. -/
theorem pEnt_dual_smul {R : Finset V} (hR : R ∈ orbits H V) (h : H) (χ : AddChar V ℂ) :
    pEnt R (h • χ) = pEnt R χ := by
  simp only [pEnt, contra_smul_apply]
  rw [← sum_orb_smul (H := H) hR h⁻¹ (fun v => conj (χ v))]

/-- The matrix eigenvalue equation on a dual-orbit idempotent: the `P`-entry is constant
along the dual orbit, so any member reads it off. -/
theorem adj_mul_orbProj {R : Finset V} (hR : R ∈ orbits H V) {S : Finset (AddChar V ℂ)}
    (hS : S ∈ orbits H (AddChar V ℂ)) {χ₀ : AddChar V ℂ} (hχ₀ : χ₀ ∈ S) :
    adj R * orbProj S = pEnt R χ₀ • orbProj S := by
  rw [orbProj, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [adj_mul_charProj]
  congr 1
  have h1 := (mem_iff_orb_eq hS).mp hχ₀
  have h2 : χ ∈ orb H χ₀ := by rw [h1]; exact hχ
  obtain ⟨h, hh⟩ := mem_orb.mp h2
  rw [← hh, pEnt_dual_smul (H := H) hR]

omit [Fintype V] [DecidableEq V] in
/-- **Primal-orbit constancy of the dual class sums**: `qEnt S` is constant along the
`H`-orbits of `V` when `S` is a dual orbit. -/
theorem qEnt_smul [Finite V] {S : Finset (AddChar V ℂ)} (hS : S ∈ orbits H (AddChar V ℂ))
    (h : H) (v : V) : qEnt S (h • v) = qEnt S v := by
  simp only [qEnt]
  rw [← sum_orb_smul (H := H) hS h⁻¹ (fun χ : AddChar V ℂ => χ v)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [contra_smul_apply, inv_inv]

omit [Fintype V] [DecidableEq V] in
/-- The dual class sum of a dual orbit is an invariant kernel. -/
theorem isInv_qEnt [Finite V] {S : Finset (AddChar V ℂ)} (hS : S ∈ orbits H (AddChar V ℂ)) :
    IsInv H (qEnt S) := fun h v => qEnt_smul hS h v

/-- The idempotent of a dual orbit lies in the scheme algebra. -/
theorem orbProj_mem_schemeAlgebra {S : Finset (AddChar V ℂ)}
    (hS : S ∈ orbits H (AddChar V ℂ)) : orbProj S ∈ schemeAlgebra H V := by
  rw [orbProj_eq_circulant]
  exact (mem_schemeAlgebra_iff_circulant _).mpr
    ⟨_, isInv_smul (Fintype.card V : ℂ)⁻¹ (isInv_qEnt hS), rfl⟩

omit [DecidableEq V] in
/-- Distinct dual orbits have orthogonal idempotents. -/
theorem orbProj_mul_of_ne {S T : Finset (AddChar V ℂ)} (hS : S ∈ orbits H (AddChar V ℂ))
    (hT : T ∈ orbits H (AddChar V ℂ)) (hne : S ≠ T) : orbProj S * orbProj T = 0 := by
  rw [orbProj_mul_orbProj]
  have hdisj : S ∩ T = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro χ hχ
    rw [Finset.mem_inter] at hχ
    exact hne (eq_of_mem_orbits_of_mem hS hT hχ.1 hχ.2)
  rw [hdisj, Finset.sum_empty]

/-- The dual-orbit idempotents sum to the identity. -/
theorem sum_orbProj : ∑ S ∈ orbits H (AddChar V ℂ), orbProj S = 1 := by
  simp only [orbProj]
  rw [sum_orbits (H := H) (fun χ : AddChar V ℂ => charProj χ)]
  exact sum_charProj

/-- **The dual-orbit idempotents** are complete orthogonal idempotents of the scheme
algebra. -/
theorem completeOrthogonalIdempotents_orbProj :
    CompleteOrthogonalIdempotents
      (fun S : ↥(orbits H (AddChar V ℂ)) => orbProj (S : Finset (AddChar V ℂ))) :=
  ⟨⟨fun S => orbProj_mul_self (S : Finset (AddChar V ℂ)),
    fun S T hne => orbProj_mul_of_ne S.2 T.2 (fun h => hne (Subtype.ext h))⟩,
   by
    rw [Finset.sum_coe_sort (orbits H (AddChar V ℂ)) (fun S => orbProj S)]
    exact sum_orbProj⟩

/-! ### The eigenmatrix duality `PQ = |V|·I` -/

/-- **`P·Q = |V|·I`, unconditionally, for ANY choice of dual-orbit representatives.** Summing
over the dual orbits the `P`-entry at a representative times the `Q`-entry (dual class sum)
at a point detects membership of the point in the primal orbit. The freedom in `rep` IS the
representative-independence: it rests on `pEnt_dual_smul`. -/
theorem PQ_eq (rep : Finset (AddChar V ℂ) → AddChar V ℂ)
    (hrep : ∀ S ∈ orbits H (AddChar V ℂ), rep S ∈ S)
    {R : Finset V} (hR : R ∈ orbits H V) (u : V) :
    ∑ S ∈ orbits H (AddChar V ℂ), pEnt R (rep S) * qEnt S u
      = (Fintype.card V : ℂ) * (if u ∈ R then 1 else 0) := by
  rw [← sum_pEnt_mul R u,
    ← sum_orbits (H := H) (fun χ : AddChar V ℂ => pEnt R χ * χ u)]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [qEnt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  congr 1
  have h1 : orb H χ = S := (mem_iff_orb_eq hS).mp hχ
  have h2 : rep S ∈ orb H χ := by
    rw [h1]
    exact hrep S hS
  obtain ⟨h, hh⟩ := mem_orb.mp h2
  rw [← hh, pEnt_dual_smul (H := H) hR]

/-- **Spectral decomposition of an orbit adjacency** along the dual-orbit idempotents
(`A_R = Σ_S P_{R,S} E_S`), for any choice of representatives. -/
theorem adj_eq_sum_orbProj (rep : Finset (AddChar V ℂ) → AddChar V ℂ)
    (hrep : ∀ S ∈ orbits H (AddChar V ℂ), rep S ∈ S)
    {R : Finset V} (hR : R ∈ orbits H V) :
    adj R = ∑ S ∈ orbits H (AddChar V ℂ), pEnt R (rep S) • orbProj S := by
  have hN : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  simp only [adj, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, orbProj_eq_circulant,
    Matrix.circulant_apply]
  have hpull : ∑ S ∈ orbits H (AddChar V ℂ),
      pEnt R (rep S) * ((Fintype.card V : ℂ)⁻¹ * qEnt S (i - j))
      = (Fintype.card V : ℂ)⁻¹ *
          ∑ S ∈ orbits H (AddChar V ℂ), pEnt R (rep S) * qEnt S (i - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by ring
  rw [hpull, PQ_eq rep hrep hR (i - j), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **The inverse expansion** (`|V|·E_S = Σ_R Q_{S,R} A_R`), representative-free through
`orbVal`. -/
theorem orbProj_eq_sum_adj {S : Finset (AddChar V ℂ)} (hS : S ∈ orbits H (AddChar V ℂ)) :
    (Fintype.card V : ℂ) • orbProj S = ∑ R ∈ orbits H V, orbVal (qEnt S) R • adj R := by
  have hN : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← circulant_eq_sum_adj (isInv_qEnt hS), orbProj_eq_circulant]
  ext i j
  simp only [Matrix.smul_apply, Matrix.circulant_apply, smul_eq_mul]
  rw [mul_inv_cancel_left₀ hN]

/-! ### The negation orbit and the transpose count

The translation-scheme mirror of `trace_orbitalAdj_mul_orbitalAdj`: transposing a
difference-set adjacency negates the difference, so the trace of a product of adjacencies
is a diagonal against the **negation orbit**. -/

omit [Fintype V] in
/-- Negation carries orbits to orbits: the action is by additive maps. -/
theorem orb_neg (v : V) : orb H (-v) = (orb H v).image (fun w => -w) := by
  ext u
  rw [Finset.mem_image]
  constructor
  · intro h
    obtain ⟨g, hg⟩ := mem_orb.mp h
    exact ⟨g • v, mem_orb.mpr ⟨g, rfl⟩, by rw [← hg, smul_neg]⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨g, hg⟩ := mem_orb.mp hw
    exact mem_orb.mpr ⟨g, by rw [smul_neg, hg]⟩

omit [Fintype V] in
theorem mem_image_neg {R : Finset V} {u : V} :
    u ∈ R.image (fun w => -w) ↔ -u ∈ R := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [neg_neg]
  · intro h
    exact ⟨-u, h, neg_neg u⟩

/-- The negation image of an orbit is an orbit. -/
theorem image_neg_mem_orbits {R : Finset V} (hR : R ∈ orbits H V) :
    R.image (fun w => -w) ∈ orbits H V := by
  obtain ⟨v, hv⟩ := nonempty_of_mem_orbits hR
  rw [show R = orb H v from ((mem_iff_orb_eq hR).mp hv).symm, ← orb_neg]
  exact orb_mem_orbits _

omit [Fintype V] in
@[simp] theorem image_neg_image_neg (R : Finset V) :
    (R.image (fun w => -w)).image (fun w => -w) = R := by
  ext u
  rw [mem_image_neg, mem_image_neg, neg_neg]

/-- **The transpose count for translation schemes**: the trace of a product of
difference-set adjacencies is `|V| · #R` when the second set is the negation of the first,
and zero otherwise. -/
theorem trace_adj_mul_adj {R R' : Finset V} (hR : R ∈ orbits H V) (hR' : R' ∈ orbits H V) :
    (adj R * adj R').trace
      = if R' = R.image (fun w => -w)
          then (Fintype.card V : ℂ) * (#R : ℂ) else 0 := by
  classical
  have hexp : (adj R * adj R').trace
      = ∑ x : V, ∑ d : V,
          (if d ∈ R then (1 : ℂ) else 0) * if -d ∈ R' then (1 : ℂ) else 0 := by
    rw [Matrix.trace]
    rw [show ∑ x, (adj R * adj R').diag x
        = ∑ x : V, ∑ y : V,
            (if x - y ∈ R then (1 : ℂ) else 0) * if y - x ∈ R' then (1 : ℂ) else 0 from
      Finset.sum_congr rfl fun x _ => by
        rw [Matrix.diag_apply, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun y _ => by
          rw [adj, adj, Matrix.circulant_apply, Matrix.circulant_apply]]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_nbij' (i := fun y => x - y) (j := fun d => x - d)
      (fun y _ => Finset.mem_univ _) (fun d _ => Finset.mem_univ _)
      (fun y _ => by change x - (x - y) = y; abel)
      (fun d _ => by change x - (x - d) = d; abel) ?_
    intro y _
    change (if x - y ∈ R then (1 : ℂ) else 0) * (if y - x ∈ R' then (1 : ℂ) else 0)
      = (if x - y ∈ R then (1 : ℂ) else 0) * (if -(x - y) ∈ R' then (1 : ℂ) else 0)
    rw [show y - x = -(x - y) from by abel]
  rw [hexp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show ∑ d : V, (if d ∈ R then (1 : ℂ) else 0) * (if -d ∈ R' then (1 : ℂ) else 0)
      = ∑ d : V, if d ∈ R ∧ -d ∈ R' then (1 : ℂ) else 0 from
    Finset.sum_congr rfl fun d _ => by
      by_cases h1 : d ∈ R <;> by_cases h2 : -d ∈ R' <;> simp [h1, h2]]
  rw [Finset.sum_boole]
  rw [show Finset.univ.filter (fun d : V => d ∈ R ∧ -d ∈ R')
      = R ∩ R'.image (fun w => -w) from by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      mem_image_neg]]
  by_cases heq : R' = R.image (fun w => -w)
  · rw [if_pos heq, heq, image_neg_image_neg, Finset.inter_self]
  · rw [if_neg heq]
    have hdisj : R ∩ R'.image (fun w => -w) = ∅ := by
      by_contra hne
      obtain ⟨u, hu⟩ := Finset.nonempty_of_ne_empty hne
      rw [Finset.mem_inter] at hu
      have := eq_of_mem_orbits_of_mem (image_neg_mem_orbits hR') hR hu.2 hu.1
      exact heq (by rw [← this, image_neg_image_neg])
    rw [hdisj]
    simp

end Orbit

end ECCLib.Scheme
