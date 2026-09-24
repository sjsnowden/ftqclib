/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CliffordWordFloor
import FTQCLib.Gates.CliffordGateGeneration

/-!
# Every symplectic map is a Clifford word on the floor

The letters of the Clifford alphabet (`CliffordWordFloor.lean`) each move a height-zero floor to a
height-zero floor (`runNormal_floor`) and move its Lagrangian by their symplectic map
(`runNormal_L`). This module identifies those maps with the library's gate maps and reads off the
group statement: **for every symplectic `T` and every height-zero floor at precision `m ≥ 2` there
is a well-formed word whose run keeps the floor at height zero, moves its Lagrangian by `T`, and
moves its amplitude by the referee** (`exists_runNormal_of_isClifford`).

The combinatorial half is `exists_wordWF_wordLin_eq`: every `IsClifford T` is `wordLin gs` for a
well-formed `gs`. It is a closure induction on `closure_bigGateSet_eq_spSubgroup`
(`FTQCLib/Gates/CliffordGateGeneration.lean`) in the **ambient** group — the subtype form would carry
`Subtype.val` through every case. Two of the four cases have content: `mul` fixes the word order,
since `x * y` applies `y` first (`coe_mul`) while `wordLin_append` composes head first, so the word
for `x * y` is `gs_y ++ gs_x`; and `inv` reverses the word, which works because every letter's map
is an involution (`letterLin_involutive`).

What the statement adds over its inputs: `runNormal_floor` and the generation theorem are proved
elsewhere. The new content is the four identifications below, which connect the alphabet to the
gate maps, together with `runNormal_L` (`CliffordWordFloor.lean`).

## Main results

* `pauliSwapOn_singleton_eq_hadamardAt`, `zShearBy_shearLin_self_eq_phaseAt`,
  `zShearBy_shearLin_ne_eq_czAt`, `cnotPauli_eq_cnotAt` — the four identifications.
* `letterLin_H`, `letterLin_sLetter`, `letterLin_czLetter`, `letterLin_Cnot` — each letter's map
  is the corresponding gate map (`S` needs `2 ≤ m`, `CZ` needs `1 ≤ m` and `i ≠ j`).
* `exists_wordWF_wordLin_eq` — every symplectic map is a well-formed word's map, at `2 ≤ m`.
* `exists_runNormal_of_isClifford` — the composite statement on a floor.

Everything here is frame-pure. No `FTQCLib.Hilbert`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer FTQCLib.Gates Module

variable {n : ℕ}

/-! ## The four identifications -/

/-- **H.** The swap at one bit is the Hadamard gate map. -/
theorem pauliSwapOn_singleton_eq_hadamardAt (k : Fin n) :
    pauliSwapOn ({k} : Finset (Fin n)) = (hadamardAt k : Pauli n →ₗ[ZMod 2] Pauli n) := by
  refine LinearMap.ext fun p => Pauli.ext ?_ ?_ <;> funext i
  · change (if i ∈ ({k} : Finset (Fin n)) then p.Z i else p.X i)
      = Function.update p.X k (p.Z k) i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Finset.mem_singleton, hik]
  · change (if i ∈ ({k} : Finset (Fin n)) then p.X i else p.Z i)
      = Function.update p.Z k (p.X k) i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Finset.mem_singleton, hik]

/-- **S.** The shear at `k` by `e_k` is the phase gate map. -/
theorem zShearBy_shearLin_self_eq_phaseAt (k : Fin n) :
    zShearBy (shearLin k (Pi.single k 1)) = (phaseAt k : Pauli n →ₗ[ZMod 2] Pauli n) := by
  refine LinearMap.ext fun p => Pauli.ext rfl ?_
  funext i
  change p.Z i + shearRow k (Pi.single k 1) p.X i
    = Function.update p.Z k (p.Z k + p.X k) i
  rw [shearRow_single_self]
  by_cases hik : i = k
  · subst hik
    rw [Function.update_self, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · rw [Function.update_of_ne hik, Pi.smul_apply, Pi.single_eq_of_ne hik, smul_zero, add_zero]

/-- **CZ.** The shear at `i` by `e_j` is the controlled-Z gate map (`i ≠ j`). -/
theorem zShearBy_shearLin_ne_eq_czAt {i j : Fin n} (hij : i ≠ j) :
    zShearBy (shearLin i (Pi.single j 1)) = (czAt i j hij : Pauli n →ₗ[ZMod 2] Pauli n) := by
  refine LinearMap.ext fun p => Pauli.ext rfl ?_
  funext l
  change p.Z l + shearRow i (Pi.single j 1) p.X l = czZ i j p l
  rw [shearRow_single_ne hij]
  unfold czZ
  by_cases hlj : l = j
  · subst hlj
    rw [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hij), smul_eq_mul, smul_eq_mul, mul_one, mul_zero, add_zero]
  · by_cases hli : l = i
    · subst hli
      rw [Function.update_of_ne hlj, Function.update_self, Pi.add_apply, Pi.smul_apply,
        Pi.smul_apply, Pi.single_eq_of_ne hij, Pi.single_eq_same, smul_eq_mul, smul_eq_mul,
        mul_one, mul_zero, zero_add]
    · rw [Function.update_of_ne hlj, Function.update_of_ne hli, Pi.add_apply, Pi.smul_apply,
        Pi.smul_apply, Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj, smul_zero, smul_zero,
        add_zero, add_zero]

/-- **CNOT.** The symplectic lift is the CNOT gate map (`i ≠ j`). -/
theorem cnotPauli_eq_cnotAt {i j : Fin n} (hij : i ≠ j) :
    cnotPauli i j = (cnotAt i j hij : Pauli n →ₗ[ZMod 2] Pauli n) :=
  LinearMap.ext fun _ => rfl

/-! ## Each letter's map is its gate map -/

theorem letterLin_H {m : ℕ} (k : Fin n) :
    letterLin (NormalGate.H k : NormalGate n m) = (hadamardAt k : Pauli n →ₗ[ZMod 2] Pauli n) :=
  pauliSwapOn_singleton_eq_hadamardAt k

theorem letterLin_sLetter {m : ℕ} (hm : 2 ≤ m) (i : Fin n) :
    letterLin (sLetter m i) = (phaseAt i : Pauli n →ₗ[ZMod 2] Pauli n) := by
  change zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce (sGate m i)))) = _
  rw [boolReduce_sGate, polarMatrix_sGate hm, mulVecLin_single_self,
    zShearBy_shearLin_self_eq_phaseAt]

theorem letterLin_czLetter {m : ℕ} (hm : 1 ≤ m) {i j : Fin n} (hij : i ≠ j) :
    letterLin (czLetter m i j) = (czAt i j hij : Pauli n →ₗ[ZMod 2] Pauli n) := by
  change zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce (czGate m i j)))) = _
  rw [boolReduce_czGate _ hij, polarMatrix_czGate hm hij, mulVecLin_single_pair hij,
    zShearBy_shearLin_ne_eq_czAt hij]

theorem letterLin_Cnot {m : ℕ} {i j : Fin n} (hij : i ≠ j) :
    letterLin (NormalGate.Cnot i j : NormalGate n m)
      = (cnotAt i j hij : Pauli n →ₗ[ZMod 2] Pauli n) :=
  cnotPauli_eq_cnotAt hij

/-! ## Words: the one-letter case, the involution, and the reverse -/

theorem wordLin_singleton {m : ℕ} (g : NormalGate n m) : wordLin [g] = letterLin g :=
  LinearMap.ext fun _ => rfl

/-- Every letter's symplectic map is an involution — the fact the `inv` case of the induction
rests on. -/
theorem letterLin_involutive {m : ℕ} (g : NormalGate n m) (hg : g.WF) (p : Pauli n) :
    letterLin g (letterLin g p) = p := by
  cases g with
  | H k => exact pauliSwapOn_pauliSwapOn {k} p
  | Diag D => exact zShearBy_zShearBy _ p
  | Cnot i j => exact cnotPauli_cnotPauli i j hg p

/-- A well-formed word reversed is well-formed. -/
theorem wordWF_reverse {m : ℕ} {gs : List (NormalGate n m)} (hwf : WordWF gs) :
    WordWF gs.reverse := fun g hg => hwf g (List.mem_reverse.mp hg)

/-- **The reverse inverts the word**: the maps compose to the identity. -/
theorem wordLin_reverse_comp {m : ℕ} {gs : List (NormalGate n m)} (hwf : WordWF gs) (p : Pauli n) :
    wordLin gs.reverse (wordLin gs p) = p := by
  induction gs generalizing p with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.WF := hwf g (List.mem_cons_self ..)
    have hwf' : WordWF gs := fun g' hg' => hwf g' (List.mem_cons_of_mem _ hg')
    rw [List.reverse_cons, wordLin_cons]
    change wordLin (gs.reverse ++ [g]) (wordLin gs (letterLin g p)) = p
    rw [wordLin_append, wordLin_singleton]
    change letterLin g (wordLin gs.reverse (wordLin gs (letterLin g p))) = p
    rw [ih hwf', letterLin_involutive g hg]

/-! ## The group statement -/

/-- The coercion of a product is the composite, right factor first. -/
theorem coe_mul_linearMap (x y : Pauli n ≃ₗ[ZMod 2] Pauli n) :
    ((x * y : Pauli n ≃ₗ[ZMod 2] Pauli n) : Pauli n →ₗ[ZMod 2] Pauli n)
      = ((x : Pauli n →ₗ[ZMod 2] Pauli n).comp (y : Pauli n →ₗ[ZMod 2] Pauli n)) :=
  LinearMap.ext fun _ => rfl

/-- Each generator of `bigGateSet` is a one-letter well-formed word. -/
theorem exists_wordWF_of_mem_bigGateSet {m : ℕ} (hm : 2 ≤ m)
    {x : Pauli n ≃ₗ[ZMod 2] Pauli n} (hx : x ∈ bigGateSet n) :
    ∃ gs : List (NormalGate n m), WordWF gs ∧
      wordLin gs = (x : Pauli n →ₗ[ZMod 2] Pauli n) := by
  rcases hx with (((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨i, j, hij, rfl⟩) | ⟨i, j, hij, rfl⟩)
  · exact ⟨[NormalGate.H k], fun g hg => by
      rw [List.mem_singleton] at hg; subst hg; trivial,
      by rw [wordLin_singleton, letterLin_H]⟩
  · exact ⟨[sLetter m k], fun g hg => by
      rw [List.mem_singleton] at hg; subst hg; exact sLetter_wf m k,
      by rw [wordLin_singleton, letterLin_sLetter hm]⟩
  · exact ⟨[NormalGate.Cnot i j], fun g hg => by
      rw [List.mem_singleton] at hg; subst hg; exact hij,
      by rw [wordLin_singleton, letterLin_Cnot hij]⟩
  · exact ⟨[czLetter m i j], fun g hg => by
      rw [List.mem_singleton] at hg; subst hg; exact czLetter_wf m i j,
      by rw [wordLin_singleton, letterLin_czLetter (by omega) hij]⟩

/-- **Every symplectic map is a well-formed word's map**, at precision at least two. -/
theorem exists_wordWF_wordLin_eq {m : ℕ} (hm : 2 ≤ m) {T : Pauli n ≃ₗ[ZMod 2] Pauli n}
    (hT : IsClifford T) :
    ∃ gs : List (NormalGate n m), WordWF gs ∧
      wordLin gs = (T : Pauli n →ₗ[ZMod 2] Pauli n) := by
  have hmem : T ∈ Subgroup.closure (bigGateSet n) := by
    rw [closure_bigGateSet_eq_spSubgroup]
    exact hT
  clear hT
  induction hmem using Subgroup.closure_induction with
  | mem x hx => exact exists_wordWF_of_mem_bigGateSet hm hx
  | one => exact ⟨[], fun g hg => absurd hg (List.not_mem_nil), LinearMap.ext fun _ => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨gsx, hwfx, hx⟩ := ihx
    obtain ⟨gsy, hwfy, hy⟩ := ihy
    refine ⟨gsy ++ gsx, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hwfy g h
      · exact hwfx g h
    · rw [wordLin_append, hx, hy, coe_mul_linearMap]
  | inv x _ ihx =>
    obtain ⟨gs, hwf, hx⟩ := ihx
    refine ⟨gs.reverse, wordWF_reverse hwf, LinearMap.ext fun p => ?_⟩
    have h := wordLin_reverse_comp hwf (x.symm p)
    rw [show wordLin gs (x.symm p) = x (x.symm p) from congrFun (congrArg _ hx) _,
      LinearEquiv.apply_symm_apply] at h
    exact h

/-- **The composite statement.** For every symplectic `T` and every height-zero floor at precision
`m ≥ 2` there is a well-formed word whose run is a height-zero floor at precision `m`, whose
Lagrangian is `T` of the input's, and whose amplitude is the referee's. -/
theorem exists_runNormal_of_isClifford {m : ℕ} (hm : 2 ≤ m) {T : Pauli n ≃ₗ[ZMod 2] Pauli n}
    (hT : IsClifford T) {S : KernelSumState n} (hF : IsFloor S) (h0 : S.h = 0) (hSm : S.m = m) :
    ∃ gs : List (NormalGate n m), WordWF gs ∧
      IsFloor (runNormal gs S) ∧ (runNormal gs S).h = 0 ∧ (runNormal gs S).m = m ∧
      (runNormal gs S).L = Submodule.map (T : Pauli n →ₗ[ZMod 2] Pauli n) S.L ∧
      amp (runNormal gs S) = runNormalAmp gs (amp S) := by
  obtain ⟨gs, hwf, hlin⟩ := exists_wordWF_wordLin_eq (n := n) hm hT
  obtain ⟨hF', h0', hm', hamp⟩ := runNormal_floor gs hwf hF h0 hSm
  exact ⟨gs, hwf, hF', h0', hm', by rw [runNormal_L gs hwf hF h0 hSm, hlin], hamp⟩


/-! ## Why the statement needs `2 ≤ m`: the invariant at precision one

At precision one every diagonal letter's polar matrix is alternating on the vector it is applied
to — a consequence of the shift datum, since twice the constant vanishes in `ZMod 2`. So every
letter of the alphabet preserves the quadratic form `q(p) = ∑ᵢ xᵢ zᵢ` on `Pauli n`, hence so does
every word. The phase gate does not: it sends `q` to `q + x_k`. The alphabet's image at precision
one therefore lies in the orthogonal group of `q`, and `phaseAt k` is the map of no word at any
`n` — an invariant, not an enumeration. -/

/-- **The polar matrix is alternating at precision one.** Reading the shift datum at `w = v` and at
`w = 0` and adding, the pairing of `v` with itself is twice a constant, which vanishes. -/
theorem dotF2_polarMatrix_self_zero {D : DiagPhase n 1} (hD : levelExt D ≤ 2)
    (x : Fin n → ZMod 2) :
    dotF2 (Matrix.mulVecLin (polarMatrix (boolReduce D)) x) x = 0 := by
  obtain ⟨c, hc⟩ := diagShiftDatumBy_polarMatrix D hD ⊤ x Submodule.mem_top
  have hxx : x + x = 0 := by
    funext i
    change x i + x i = 0
    rcases zmod_two_eq_zero_or_one (x i) with h | h <;> rw [h] <;> decide
  have hz0 : dotF2 (Matrix.mulVecLin (polarMatrix (boolReduce D)) x) (0 : Fin n → ZMod 2) = 0 := by
    simp [dotF2]
  have hpow : (2 : ZMod (2 ^ 1)) ^ (1 - 1) = 1 := by decide
  have h2 : (2 : ZMod (2 ^ 1)) = 0 := by decide
  have h0 := hc 0
  have hx := hc x
  rw [zero_add, hz0, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero] at h0
  rw [hxx, hpow, one_mul] at hx
  have hsum : (((dotF2 (Matrix.mulVecLin (polarMatrix (boolReduce D)) x) x).val : ℕ)
      : ZMod (2 ^ 1)) = 0 := by
    linear_combination -h0 - hx - c * h2
  rcases zmod_two_eq_zero_or_one
      (dotF2 (Matrix.mulVecLin (polarMatrix (boolReduce D)) x) x) with h | h
  · exact h
  · rw [h] at hsum
    exact absurd hsum (by decide)

/-- A shear whose pairing kills the X-part preserves `q`. -/
theorem qForm_zShearBy_of_self_zero {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)}
    {p : Pauli n} (h : dotF2 (M p.X) p.X = 0) : qForm (zShearBy M p) = qForm p := by
  unfold qForm
  rw [zShearBy_X, zShearBy_Z]
  have : ∀ i, p.X i * (p.Z + M p.X) i = p.X i * p.Z i + M p.X i * p.X i := by
    intro i; rw [Pi.add_apply]; ring
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
  change _ + dotF2 (M p.X) p.X = _
  rw [h, add_zero]

/-- The swap at a bit preserves `q`. -/
theorem qForm_pauliSwapOn_singleton (k : Fin n) (p : Pauli n) :
    qForm (pauliSwapOn ({k} : Finset (Fin n)) p) = qForm p := by
  unfold qForm
  refine Finset.sum_congr rfl fun i _ => ?_
  change (if i ∈ ({k} : Finset (Fin n)) then p.Z i else p.X i) *
      (if i ∈ ({k} : Finset (Fin n)) then p.X i else p.Z i) = p.X i * p.Z i
  by_cases hik : i ∈ ({k} : Finset (Fin n))
  · rw [if_pos hik, if_pos hik, mul_comm]
  · rw [if_neg hik, if_neg hik]

/-- The CNOT lift preserves `q`. -/
theorem qForm_cnotPauli {i j : Fin n} (hij : i ≠ j) (p : Pauli n) :
    qForm (cnotPauli i j p) = qForm p := by
  unfold qForm
  rw [Finset.sum_congr rfl (fun l _ => by
    change cnotBitMap i j p.X l * cnotBitMap j i p.Z l = _
    rfl : ∀ l ∈ Finset.univ, (cnotPauli i j p).X l * (cnotPauli i j p).Z l
      = cnotBitMap i j p.X l * cnotBitMap j i p.Z l)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) _
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
    ← Finset.add_sum_erase _ (fun l => p.X l * p.Z l) (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) (fun l => p.X l * p.Z l)
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hrest : ∀ l ∈ (Finset.univ.erase i).erase j,
      cnotBitMap i j p.X l * cnotBitMap j i p.Z l = p.X l * p.Z l := by
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    unfold cnotBitMap
    rw [Function.update_of_ne hlj, Function.update_of_ne hli]
  rw [Finset.sum_congr rfl hrest]
  unfold cnotBitMap
  rw [Function.update_of_ne hij, Function.update_self, Function.update_self,
    Function.update_of_ne hij.symm]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination (p.X i * p.Z j) * h2

/-- **Every well-formed letter preserves `q` at precision one.** -/
theorem qForm_letterLin (g : NormalGate n 1) (hg : g.WF) (p : Pauli n) :
    qForm (letterLin g p) = qForm p := by
  cases g with
  | H k => exact qForm_pauliSwapOn_singleton k p
  | Diag D => exact qForm_zShearBy_of_self_zero (dotF2_polarMatrix_self_zero hg p.X)
  | Cnot i j => exact qForm_cnotPauli hg p

/-- **Every well-formed word preserves `q` at precision one.** -/
theorem qForm_wordLin {gs : List (NormalGate n 1)} (hwf : WordWF gs) (p : Pauli n) :
    qForm (wordLin gs p) = qForm p := by
  induction gs generalizing p with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.WF := hwf g (List.mem_cons_self ..)
    have hwf' : WordWF gs := fun g' hg' => hwf g' (List.mem_cons_of_mem _ hg')
    change qForm (wordLin gs (letterLin g p)) = qForm p
    rw [ih hwf', qForm_letterLin g hg]

/-- **The phase gate moves `q`** by the X-coordinate at its bit. -/
theorem qForm_phaseAt (k : Fin n) (p : Pauli n) :
    qForm (phaseAt k p) = qForm p + p.X k := by
  unfold qForm
  change (∑ i, p.X i * Function.update p.Z k (p.Z k + p.X k) i) = (∑ i, p.X i * p.Z i) + p.X k
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ (fun i => p.X i * p.Z i) (Finset.mem_univ k),
    Finset.sum_congr rfl (fun l hl =>
      by rw [Function.update_of_ne (Finset.mem_erase.mp hl).1] :
      ∀ l ∈ Finset.univ.erase k, p.X l * Function.update p.Z k (p.Z k + p.X k) l
        = p.X l * p.Z l),
    Function.update_self]
  have hsq : p.X k * p.X k = p.X k := by
    rcases zmod_two_eq_zero_or_one (p.X k) with h | h <;> rw [h] <;> decide
  rw [mul_add, hsq]
  ring

/-- **The row that makes `2 ≤ m` necessary.** At precision one no well-formed word has the phase
gate's symplectic map: every word preserves `q`, and `phaseAt k` moves it on any Pauli whose
X-coordinate at `k` is `1`. -/
theorem not_exists_wordWF_wordLin_eq_phaseAt (k : Fin n) :
    ¬ ∃ gs : List (NormalGate n 1), WordWF gs ∧
        wordLin gs = (phaseAt k : Pauli n →ₗ[ZMod 2] Pauli n) := by
  rintro ⟨gs, hwf, hgs⟩
  have hq := qForm_wordLin hwf (paulix k)
  rw [show wordLin gs (paulix k) = phaseAt k (paulix k) from congrFun (congrArg _ hgs) _,
    qForm_phaseAt, paulix_X, Pi.single_eq_same] at hq
  have h1 : qForm (paulix k) + 1 = qForm (paulix k) := hq
  exact absurd (by linear_combination h1 : (1 : ZMod 2) = 0) (by decide)

end FTQCLib.Frame.Walkthrough
