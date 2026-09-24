/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Distance

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The decoder specification layer

The specifications the verified decoders are checked against, and the theorem that connects them
to the distance layer:

* **`IsMDDecoder dec C`** — `dec` always returns a codeword at minimal Hamming distance from the
  received word (minimum-distance decoding). The decoder carrier is `Option`-valued throughout
  the layer: bounded-distance decoders genuinely fail beyond their radius, and total decoders
  wrap in `some`.
* **`Corrects dec C t`** — every transmission corrupted in at most `t` coordinates decodes to
  the sent codeword (the bounded-distance-decoding shape).
* **The correction theorem** `IsMDDecoder.corrects` — an MD decoder corrects `t` errors whenever
  `2t < minDist C`, in the subtraction-free form; `IsMDDecoder.corrects_half` derives the
  literature-facing `⌊(d−1)/2⌋` radius. The content is unique decoding
  (`eq_of_hammingDist_le`): two codewords within `t` of one word coincide, by
  `minDist_le_hammingDist` + the triangle inequality.
* **`exists_mdDecoder`** — every code has an MD decoder (the classical spec-layer witness;
  deliberately non-algorithmic — the executable decoders are built separately and
  computably).
-/

namespace ECCLib.Coding

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [DecidableEq F]

/-! ## The decoder specifications -/

/-- A **minimum-distance decoder** for `C`: on every received word it returns some codeword at
minimal Hamming distance. -/
def IsMDDecoder (dec : (ι → F) → Option (ι → F)) (C : Submodule F (ι → F)) : Prop :=
  ∀ y, ∃ c, dec y = some c ∧ c ∈ C ∧ ∀ c' ∈ C, hammingDist y c ≤ hammingDist y c'

/-- **`t`-bounded-distance correction**: every transmission corrupted in at most `t` coordinates
decodes to the sent codeword. -/
def Corrects (dec : (ι → F) → Option (ι → F)) (C : Submodule F (ι → F)) (t : ℕ) : Prop :=
  ∀ c ∈ C, ∀ e : ι → F, hammingNorm e ≤ t → dec (c + e) = some c

/-! ## The correction theorem -/

/-- **Unique decoding**: two codewords within `t` of the same word coincide when `2t < d`. -/
theorem eq_of_hammingDist_le {C : Submodule F (ι → F)} {t : ℕ} (h2t : 2 * t < minDist C)
    {y c₁ c₂ : ι → F} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (h₁ : hammingDist y c₁ ≤ t) (h₂ : hammingDist y c₂ ≤ t) : c₁ = c₂ := by
  by_contra hne
  have hd := minDist_le_hammingDist hc₁ hc₂ hne
  have htri := hammingDist_triangle c₁ y c₂
  rw [hammingDist_comm c₁ y] at htri
  omega

/-- Corrupting a word by an error of weight `w` moves it Hamming distance exactly `w`. -/
lemma hammingDist_add_left (c e : ι → F) : hammingDist (c + e) c = hammingNorm e := by
  rw [hammingDist_comm, hammingDist_eq_hammingNorm, neg_add_cancel_left]

/-- **The correction theorem** (subtraction-free form): a minimum-distance decoder corrects `t`
errors whenever `2t < minDist C`. -/
theorem IsMDDecoder.corrects {dec : (ι → F) → Option (ι → F)} {C : Submodule F (ι → F)}
    (hdec : IsMDDecoder dec C) {t : ℕ} (h2t : 2 * t < minDist C) : Corrects dec C t := by
  intro c hc e he
  obtain ⟨c', hdc, hc', hmin⟩ := hdec (c + e)
  have hdc_c : hammingDist (c + e) c ≤ t := by
    rw [hammingDist_add_left]
    exact he
  have hdc_c' : hammingDist (c + e) c' ≤ t := le_trans (hmin c hc) hdc_c
  rw [eq_of_hammingDist_le h2t hc' hc hdc_c' hdc_c] at hdc
  exact hdc

/-- The literature-facing radius: an MD decoder corrects `⌊(d−1)/2⌋` errors (nontrivial code). -/
theorem IsMDDecoder.corrects_half {dec : (ι → F) → Option (ι → F)} {C : Submodule F (ι → F)}
    (hdec : IsMDDecoder dec C) (hbot : C ≠ ⊥) :
    Corrects dec C ((minDist C - 1) / 2) := by
  refine hdec.corrects ?_
  have := minDist_pos hbot
  omega

/-- **Every code has a minimum-distance decoder** — the classical realizability witness for the
spec layer. Deliberately non-algorithmic (`Classical.choose` over a `Finset` argmin); the
executable decoders realize the same specification computably. -/
theorem exists_mdDecoder (C : Submodule F (ι → F)) :
    ∃ dec : (ι → F) → Option (ι → F), IsMDDecoder dec C := by
  classical
  have hne : ((C : Set (ι → F)).toFinset).Nonempty :=
    ⟨0, Set.mem_toFinset.mpr C.zero_mem⟩
  have h : ∀ y : ι → F, ∃ c ∈ (C : Set (ι → F)).toFinset,
      ∀ c' ∈ (C : Set (ι → F)).toFinset, hammingDist y c ≤ hammingDist y c' :=
    fun y => Finset.exists_min_image _ (hammingDist y) hne
  refine ⟨fun y => some (h y).choose, fun y => ⟨(h y).choose, rfl, ?_, ?_⟩⟩
  · exact Set.mem_toFinset.mp (h y).choose_spec.1
  · intro c' hc'
    exact (h y).choose_spec.2 c' (Set.mem_toFinset.mpr hc')

/-! ## Syndrome decoding

The code is presented as the kernel of a **syndrome map** `H` into an arbitrary module — maps,
not matrices (a parity-check *matrix* is a basis choice, made in the gate-descent layer),
and nothing is lost: every code is the kernel of its quotient map (`Submodule.ker_mkQ`), which
`synDecoder_mkQ_isMD` consumes as an instance. -/

section Syndrome

variable {W : Type*} [AddCommGroup W] [Module F W]

/-- A **coset-leader map** for the syndrome map `H`: on every realized syndrome it returns an
element of the same coset (`H (L (H y)) = H y`) of minimal Hamming weight
(`wt (L (H y)) ≤ wt y` — quantified over all `y`, this is exactly per-coset minimality). -/
def IsCosetLeaderMap (H : (ι → F) →ₗ[F] W) (L : W → (ι → F)) : Prop :=
  ∀ y : ι → F, H (L (H y)) = H y ∧ hammingNorm (L (H y)) ≤ hammingNorm y

/-- The **syndrome decoder**: subtract the coset leader of the received word's syndrome. -/
def synDecoder (H : (ι → F) →ₗ[F] W) (L : W → (ι → F)) : (ι → F) → Option (ι → F) :=
  fun y => some (y - L (H y))

/-- **A coset-leader syndrome decoder is a minimum-distance decoder for `ker H`** — the coset
minimality of the leader IS the MD property: for `c ∈ ker H` the word `y − c` has the same
syndrome as `y`, so the leader's weight bounds `wt (y − c) = d(y, c)`. -/
theorem synDecoder_isMD {H : (ι → F) →ₗ[F] W} {L : W → (ι → F)}
    (hL : IsCosetLeaderMap H L) :
    IsMDDecoder (synDecoder H L) (LinearMap.ker H) := by
  intro y
  refine ⟨y - L (H y), rfl, ?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, (hL y).1, sub_self]
  · intro c' hc'
    have hsynd : H (y - c') = H y := by
      rw [map_sub, LinearMap.mem_ker.mp hc', sub_zero]
    have hmin := (hL (y - c')).2
    rw [hsynd] at hmin
    have h1 : hammingDist y (y - L (H y)) = hammingNorm (L (H y)) := by
      rw [hammingDist_comm, hammingDist_eq_hammingNorm, ← sub_eq_neg_add, sub_sub_cancel]
    have h2 : hammingDist y c' = hammingNorm (y - c') := by
      rw [hammingDist_comm, hammingDist_eq_hammingNorm, ← sub_eq_neg_add]
    rw [h1, h2]
    exact hmin

/-- The correction guarantee, inherited from the spec layer. -/
theorem synDecoder_corrects {H : (ι → F) →ₗ[F] W} {L : W → (ι → F)}
    (hL : IsCosetLeaderMap H L) {t : ℕ} (h2t : 2 * t < minDist (LinearMap.ker H)) :
    Corrects (synDecoder H L) (LinearMap.ker H) t :=
  (synDecoder_isMD hL).corrects h2t

/-- **Coset-leader maps exist for every syndrome map** (classically): choose a minimum-weight
element in each realized fiber; unrealized syndromes never occur as `H y`. -/
theorem exists_cosetLeaderMap (H : (ι → F) →ₗ[F] W) : ∃ L, IsCosetLeaderMap H L := by
  classical
  have h : ∀ s : W, (∃ z : ι → F, H z = s) →
      ∃ z, H z = s ∧ ∀ z', H z' = s → hammingNorm z ≤ hammingNorm z' := by
    intro s hs
    obtain ⟨z0, hz0⟩ := hs
    obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun z : ι → F => H z = s)) hammingNorm
      ⟨z0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz0⟩⟩
    exact ⟨z, (Finset.mem_filter.mp hz).2,
      fun z' hz' => hmin z' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz'⟩)⟩
  refine ⟨fun s => if hs : ∃ z : ι → F, H z = s then (h s hs).choose else 0, fun y => ?_⟩
  have hy : ∃ z : ι → F, H z = H y := ⟨y, rfl⟩
  simp only [dif_pos hy]
  exact ⟨(h _ hy).choose_spec.1, (h _ hy).choose_spec.2 y rfl⟩

/-- **Nothing is lost by the kernel presentation**: every code is the kernel of its quotient
map, so a coset-leader map for `C.mkQ` yields an MD decoder for `C` itself. -/
theorem synDecoder_mkQ_isMD {C : Submodule F (ι → F)} {L : ((ι → F) ⧸ C) → (ι → F)}
    (hL : IsCosetLeaderMap C.mkQ L) : IsMDDecoder (synDecoder C.mkQ L) C := by
  have h := synDecoder_isMD hL
  rwa [Submodule.ker_mkQ] at h

end Syndrome

end ECCLib.Coding
