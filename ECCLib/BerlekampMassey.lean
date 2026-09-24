/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
/-
# Berlekamp–Massey: shortest-LFSR synthesis and the error locator

The Berlekamp–Massey algorithm, formalized as follows: the discrepancy iteration on the
`PolyList` kit's `List R` carrier, structural recursion on the syndrome list (no fuel),
the connection LENGTH carried as data (never read off a list length or a degree — the
evaluation-point-zero runs drop the physical degree below `L`), and the monic
direct-root locator read at the stored length. Minimality is carried in the loop invariant
at every prefix; the Massey exchange bound is `generates_jump`.

Public statement surface is subtraction-free: tap extraction is the executable `bmTaps`
(additive indexing + reverse); the reverse-indexed coefficient reading exists only as an
internal bridge. The examples at the end cover EVERY branch of the step (no-change update,
`2L = n` jump, `δ = 0` run) with connection-list CONTENT rows — a branch silently corrupted
in transcription can pass any test set that misses its branch.
-/
import ECCLib.PolyList
import ECCLib.GRS
import Mathlib.Data.List.GetD

namespace ECCLib.Coding

variable {R : Type*} {F : Type*} [Field F]

/-! ## The spec layer: window generation and shortest generators -/

/-- The length-`L` linear recurrence with coefficients `cf` generates the `N`-prefix of
`sf`: every length-`L` window inside the prefix predicts the next symbol. `L = 0` says the
prefix is zero; `L ≥ N` is vacuous (every sequence has complexity at most its length). -/
def Generates (L : ℕ) (cf : Fin L → F) (sf : ℕ → F) (N : ℕ) : Prop :=
  ∀ d : ℕ, d + L < N → sf (d + L) = ∑ l : Fin L, cf l * sf (d + (l : ℕ))

/-- Restriction to a shorter prefix. -/
theorem generates_mono {L : ℕ} {cf : Fin L → F} {sf : ℕ → F} {N N' : ℕ}
    (h : Generates L cf sf N) (hN : N' ≤ N) : Generates L cf sf N' :=
  fun d hd => h d (lt_of_lt_of_le hd hN)

/-- Generation only reads the prefix: sequences agreeing below `N` generate together. -/
theorem generates_congr {L : ℕ} {cf : Fin L → F} {sf sf' : ℕ → F} {N : ℕ}
    (h : Generates L cf sf N) (hs : ∀ j, j < N → sf' j = sf j) :
    Generates L cf sf' N := by
  intro d hd
  rw [hs _ hd]
  rw [h d hd]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hs _ (by omega)]

/-- The length-0 recurrence generates exactly the zero prefix. -/
theorem generates_zero_iff {cf : Fin 0 → F} {sf : ℕ → F} {N : ℕ} :
    Generates 0 cf sf N ↔ ∀ j, j < N → sf j = 0 := by
  constructor
  · intro h j hj
    have := h j (by omega)
    simpa using this
  · intro h d hd
    simpa using h d (by omega)

/-- `L` is the linear complexity of the `N`-prefix: some length-`L` recurrence generates
it, and none shorter does. -/
def IsShortestGenerator (L : ℕ) (sf : ℕ → F) (N : ℕ) : Prop :=
  (∃ cf : Fin L → F, Generates L cf sf N) ∧
    ∀ (L' : ℕ) (cf' : Fin L' → F), Generates L' cf' sf N → L ≤ L'

/-- **The jump lemma** (Massey's lower bound): if `(L, cf)` generates the `n`-prefix but
fails at position `n` (witnessed subtraction-free by `d₀` with `d₀ + L = n`), then every
generator `(Lc, cfc)` of the `(n+1)`-prefix has `n + 1 ≤ L + Lc`. -/
theorem generates_jump {L Lc : ℕ} {cf : Fin L → F} {cfc : Fin Lc → F}
    {sf : ℕ → F} {n d₀ : ℕ}
    (h : Generates L cf sf n) (hc : Generates Lc cfc sf (n + 1))
    (hd₀ : d₀ + L = n)
    (hfail : sf (d₀ + L) ≠ ∑ l : Fin L, cf l * sf (d₀ + (l : ℕ))) :
    n + 1 ≤ L + Lc := by
  by_contra hlt
  obtain ⟨r, hr⟩ : ∃ r, n = Lc + r + L := ⟨n - L - Lc, by omega⟩
  apply hfail
  have hd : d₀ = Lc + r := by omega
  subst hd
  -- the competitor predicts position n
  have h1 : sf (Lc + r + L) = ∑ l : Fin Lc, cfc l * sf (L + r + (l : ℕ)) := by
    have := hc (L + r) (by omega)
    rw [show L + r + Lc = Lc + r + L by omega] at this
    exact this
  -- expand each inner value by the short recurrence
  have h2 : ∀ l : Fin Lc,
      sf (L + r + (l : ℕ)) = ∑ k : Fin L, cf k * sf (r + (l : ℕ) + (k : ℕ)) := by
    intro l
    have := h (r + (l : ℕ)) (by omega)
    rw [show r + (l : ℕ) + L = L + r + (l : ℕ) by omega] at this
    exact this
  -- swap, and contract each inner sum by the competitor
  have h3 : ∀ k : Fin L,
      ∑ l : Fin Lc, cfc l * sf (r + (k : ℕ) + (l : ℕ)) = sf (r + (k : ℕ) + Lc) := by
    intro k
    exact (hc (r + (k : ℕ)) (by omega)).symm
  calc sf (Lc + r + L)
      = ∑ l : Fin Lc, cfc l * sf (L + r + (l : ℕ)) := h1
    _ = ∑ l : Fin Lc, cfc l * ∑ k : Fin L, cf k * sf (r + (l : ℕ) + (k : ℕ)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [h2 l]
    _ = ∑ l : Fin Lc, ∑ k : Fin L, cfc l * (cf k * sf (r + (l : ℕ) + (k : ℕ))) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k : Fin L, ∑ l : Fin Lc, cfc l * (cf k * sf (r + (l : ℕ) + (k : ℕ))) :=
        Finset.sum_comm
    _ = ∑ k : Fin L, cf k * ∑ l : Fin Lc, cfc l * sf (r + (k : ℕ) + (l : ℕ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show r + (k : ℕ) + (l : ℕ) = r + (l : ℕ) + (k : ℕ) by omega]
        ring
    _ = ∑ k : Fin L, cf k * sf (r + (k : ℕ) + Lc) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [h3 k]
    _ = ∑ k : Fin L, cf k * sf (Lc + r + (k : ℕ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show r + (k : ℕ) + Lc = Lc + r + (k : ℕ) by omega]

/-! ## The algorithm

State representation: a plain data structure with the
invariant as an external `Prop`-structure (the `GaoInv` pattern). The consumed prefix is
carried REVERSED (`rev`), so the discrepancy is a truncating dot product `pdot C rev'`
whose ascending `C`-indices meet descending window positions — no index subtraction. The
two Nat subtractions below (`n + 1 - L` under branch guard `2L ≤ n`; the locator pad
`L + 1 - length` under invariant `length ≤ L + 1`) are inside defs, per the `pdivModAux`
precedent; statements stay subtraction-free. -/

/-- Truncating dot product (stops at the shorter list). -/
def pdot (ops : FieldOps R) : List R → List R → R
  | [], _ => ops.zero
  | _, [] => ops.zero
  | a :: p, c :: q => ops.add (ops.mul a c) (pdot ops p q)

/-- Loop state: `n` symbols consumed, current `(L, C)`, last length-change data
`(B, b, m)`, consumed prefix reversed. -/
structure BMState (R : Type*) where
  n : ℕ
  L : ℕ
  C : List R
  B : List R
  b : R
  m : ℕ
  rev : List R

def bmInit (ops : FieldOps R) : BMState R := ⟨0, 0, [ops.one], [ops.one], ops.one, 1, []⟩

/-- One Massey step: compute the discrepancy; keep / update / jump. -/
def bmStep (ops : FieldOps R) (st : BMState R) (x : R) : BMState R :=
  let rv := x :: st.rev
  let δ := pdot ops st.C rv
  if ops.beq δ ops.zero then
    { st with n := st.n + 1, m := st.m + 1, rev := rv }
  else if 2 * st.L ≤ st.n then
    { n := st.n + 1
      L := st.n + 1 - st.L
      C := psub ops st.C (pshift ops st.m (psmul ops (ops.mul δ (ops.inv st.b)) st.B))
      B := st.C
      b := δ
      m := 1
      rev := rv }
  else
    { st with
      n := st.n + 1
      C := psub ops st.C (pshift ops st.m (psmul ops (ops.mul δ (ops.inv st.b)) st.B))
      m := st.m + 1
      rev := rv }

/-- Structural recursion on the syndrome list — no fuel. -/
def bmLoop (ops : FieldOps R) : List R → BMState R → BMState R
  | [], st => st
  | x :: rest, st => bmLoop ops rest (bmStep ops st x)

/-- The synthesizer: the final `(L, C)`. -/
def bmSynth (ops : FieldOps R) (s : List R) : ℕ × List R :=
  let st := bmLoop ops s (bmInit ops)
  (st.L, st.C)

/-- Executable tap extraction, additive indexing: `taps[l] = −C[L − l]` arrives via
`reverse`, never via index subtraction. The recurrence reads
`s (d + L) = ∑ l, taps[l] · s (d + l)`. -/
def bmTaps (ops : FieldOps R) (LC : ℕ × List R) : List R :=
  ((List.range LC.1).map fun i => ops.neg (LC.2.getD (i + 1) ops.zero)).reverse

/-- The monic locator word: the connection list padded to the STORED length `L + 1`, then
reversed — the pad is what keeps the monic top at an evaluation-point-zero degree drop
(e.g. `bmLocator (2, [1,1]) = [0,1,1]`). -/
def bmLocator (ops : FieldOps R) (LC : ℕ × List R) : List R :=
  (LC.2 ++ List.replicate (LC.1 + 1 - LC.2.length) ops.zero).reverse

/-! ## Internal bridge layer

Window sums with reverse indexing live HERE and only here: the public surface stays
additive; the reverse-indexed reading is an internal bridge. -/

section Bridge

variable {ops : FieldOps R} {φ : R → F}

/-- `pshift` reads zero below the shift. -/
theorem getD_pshift_lt : ∀ (m i : ℕ), i < m →
    ∀ B : List R, (pshift ops m B).getD i ops.zero = ops.zero
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, 0, _, B => rfl
  | m + 1, i + 1, h, B => by
    change (ops.zero :: pshift ops m B).getD (i + 1) ops.zero = ops.zero
    rw [List.getD_cons_succ]
    exact getD_pshift_lt m i (by omega) B

/-- `pshift` reads the base list above the shift (additive form). -/
theorem getD_pshift_add (B : List R) : ∀ (m j : ℕ),
    (pshift ops m B).getD (m + j) ops.zero = B.getD j ops.zero
  | 0, j => by simp [pshift]
  | m + 1, j => by
    change (ops.zero :: pshift ops m B).getD (m + 1 + j) ops.zero = B.getD j ops.zero
    rw [show m + 1 + j = (m + j) + 1 by omega, List.getD_cons_succ]
    exact getD_pshift_add B m j

/-- Coefficient reading of the Massey update `C' = C − c·X^m·B`, via the `toPoly`
homomorphisms. -/
theorem getD_massey_update (M : ops.Model φ) (Cl B : List R) (c : R) (m i : ℕ) :
    φ ((psub ops Cl (pshift ops m (psmul ops c B))).getD i ops.zero)
      = φ (Cl.getD i ops.zero) - φ c * φ ((pshift ops m B).getD i ops.zero) := by
  have h := toPoly_coeff M (psub ops Cl (pshift ops m (psmul ops c B))) i
  rw [toPoly_psub M, toPoly_pshift M, toPoly_psmul M] at h
  rw [← h, Polynomial.coeff_sub, toPoly_coeff M Cl]
  congr 1
  rw [show Polynomial.X ^ m * (Polynomial.C (φ c) * toPoly φ B)
      = Polynomial.C (φ c) * (Polynomial.X ^ m * toPoly φ B) by ring,
    Polynomial.coeff_C_mul, ← toPoly_pshift M, toPoly_coeff M]

/-- The internal window reading at window length `Lw`, base `d`:
`Σ_{k ≤ Lw} φ Cl[Lw − k] · sf (d + k)`. With `φ Cl[0] = 1`, vanishing at every window
inside the prefix IS generation by the executable taps (`generates_taps_iff_wsum`). -/
def wsum (φ : R → F) (ops : FieldOps R) (Cl : List R) (Lw : ℕ) (sf : ℕ → F) (d : ℕ) : F :=
  ∑ k ∈ Finset.range (Lw + 1), φ (Cl.getD (Lw - k) ops.zero) * sf (d + k)

/-- Reading the executable taps at an in-range index (the reverse-index bridge). -/
theorem bmTaps_map_getD (M : ops.Model φ) (Cl : List R) (Lw : ℕ) {l : ℕ} (hl : l < Lw) :
    ((bmTaps ops (Lw, Cl)).map φ).getD l 0 = -(φ (Cl.getD (Lw - l) ops.zero)) := by
  rw [bmTaps, List.map_reverse]
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  rw [List.getElem_reverse]
  simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  rw [M.map_neg, show Lw - 1 - l + 1 = Lw - l by omega]

/-- Generation by the executable taps ⟺ every in-prefix window sum vanishes. -/
theorem generates_taps_iff_wsum (M : ops.Model φ) {Cl : List R} {Lw : ℕ}
    (hc0 : φ (Cl.getD 0 ops.zero) = 1) (sf : ℕ → F) (N : ℕ) :
    Generates Lw (fun l => ((bmTaps ops (Lw, Cl)).map φ).getD (l : ℕ) 0) sf N
      ↔ ∀ d, d + Lw < N → wsum φ ops Cl Lw sf d = 0 := by
  have hsplit : ∀ d, wsum φ ops Cl Lw sf d
      = (∑ k ∈ Finset.range Lw, φ (Cl.getD (Lw - k) ops.zero) * sf (d + k)) + sf (d + Lw) := by
    intro d
    rw [wsum, Finset.sum_range_succ, Nat.sub_self, hc0, one_mul]
  have htaps : ∀ d, (∑ l : Fin Lw, ((bmTaps ops (Lw, Cl)).map φ).getD (l : ℕ) 0 * sf (d + (l : ℕ)))
      = -(∑ k ∈ Finset.range Lw, φ (Cl.getD (Lw - k) ops.zero) * sf (d + k)) := by
    intro d
    rw [Fin.sum_univ_eq_sum_range
      (fun j => ((bmTaps ops (Lw, Cl)).map φ).getD j 0 * sf (d + j)) Lw]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [bmTaps_map_getD M Cl Lw (Finset.mem_range.mp hl)]
    ring
  constructor
  · intro h d hd
    rw [hsplit d, h d hd, htaps d]
    ring
  · intro h d hd
    have hz := h d hd
    rw [hsplit d] at hz
    rw [htaps d]
    linear_combination hz

/-- φ of the truncating dot product, summed to any bound covering the first list. -/
theorem pdot_spec (M : ops.Model φ) : ∀ (p q : List R) (n : ℕ), p.length ≤ n →
    φ (pdot ops p q)
      = ∑ i ∈ Finset.range n, φ (p.getD i ops.zero) * φ (q.getD i ops.zero)
  | [], q, n, _ => by
    rw [pdot, M.map_zero]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [show ([] : List R).getD i ops.zero = ops.zero from rfl, M.map_zero]
    ring
  | a :: p, [], n, h => by
    rw [show pdot ops (a :: p) [] = ops.zero from rfl, M.map_zero]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [show ([] : List R).getD i ops.zero = ops.zero from rfl, M.map_zero]
    ring
  | a :: p, c :: q, 0, h => by simp at h
  | a :: p, c :: q, n + 1, h => by
    rw [pdot, M.map_add, M.map_mul, Finset.sum_range_succ',
      pdot_spec M p q n (by simpa using h)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- **The discrepancy bridge**: `pdot` of the connection list against a window list that
reads the sequence top-down IS the window sum at the top window. -/
theorem pdot_bridge (M : ops.Model φ) {Cl : List R} {Lw n : ℕ}
    (hlen : Cl.length ≤ Lw + 1) (hLn : Lw ≤ n) {w : List R}
    (sf : ℕ → F) (hread : ∀ i, i ≤ Lw → φ (w.getD i ops.zero) = sf (n - i))
    {d₀ : ℕ} (hd₀ : d₀ + Lw = n) :
    φ (pdot ops Cl w) = wsum φ ops Cl Lw sf d₀ := by
  rw [pdot_spec M Cl w (Lw + 1) hlen, wsum]
  rw [show ∑ k ∈ Finset.range (Lw + 1), φ (Cl.getD (Lw - k) ops.zero) * sf (d₀ + k)
      = ∑ k ∈ Finset.range (Lw + 1), φ (Cl.getD (Lw - k) ops.zero) * sf (n - (Lw - k)) by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [show d₀ + k = n - (Lw - k) by omega]]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [show Lw + 1 - 1 - i = Lw - i by omega, hread (Lw - i) (by omega)]

/-- `padd` length is the max. -/
theorem length_padd : ∀ p q : List R, (padd ops p q).length = max p.length q.length
  | [], q => by simp [padd]
  | a :: p, [] => by simp [padd]
  | a :: p, b :: q => by
    rw [show padd ops (a :: p) (b :: q) = ops.add a b :: padd ops p q from rfl]
    simp only [List.length_cons, length_padd p q]
    omega

theorem length_psub (p q : List R) : (psub ops p q).length = max p.length q.length := by
  rw [psub, length_padd]
  simp [pneg]

theorem length_pshift (m : ℕ) (p : List R) : (pshift ops m p).length = m + p.length := by
  simp [pshift]

theorem length_psmul (c : R) (p : List R) : (psmul ops c p).length = p.length := by
  simp [psmul]

/-- Sums whose first `m` terms vanish shift to base `m`. -/
private theorem sum_range_shift_of_zero {M₀ : Type*} [AddCommMonoid M₀] :
    ∀ (m t : ℕ) (f : ℕ → M₀), (∀ i, i < m → f i = 0) →
      ∑ i ∈ Finset.range (m + t), f i = ∑ j ∈ Finset.range t, f (m + j)
  | 0, t, f, _ => by simp
  | m + 1, t, f, h0 => by
    rw [show m + 1 + t = (m + t) + 1 by omega, Finset.sum_range_succ']
    rw [h0 0 (by omega), add_zero]
    rw [sum_range_shift_of_zero m t (fun i => f (i + 1)) (fun i hi => h0 (i + 1) (by omega))]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    omega

/-- The window sum against the taps: `wsum = sf(top) − Σ taps·sf` (needs the unit constant
term). The executable-taps face of the discrepancy. -/
theorem wsum_eq_sub (M : ops.Model φ) {Cl : List R} {Lw : ℕ}
    (hc0 : φ (Cl.getD 0 ops.zero) = 1) (sf : ℕ → F) (d : ℕ) :
    wsum φ ops Cl Lw sf d
      = sf (d + Lw)
        - ∑ l : Fin Lw, ((bmTaps ops (Lw, Cl)).map φ).getD (l : ℕ) 0 * sf (d + (l : ℕ)) := by
  have htaps : (∑ l : Fin Lw, ((bmTaps ops (Lw, Cl)).map φ).getD (l : ℕ) 0 * sf (d + (l : ℕ)))
      = -(∑ k ∈ Finset.range Lw, φ (Cl.getD (Lw - k) ops.zero) * sf (d + k)) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j => ((bmTaps ops (Lw, Cl)).map φ).getD j 0 * sf (d + j)) Lw]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [bmTaps_map_getD M Cl Lw (Finset.mem_range.mp hl)]
    ring
  rw [wsum, Finset.sum_range_succ, Nat.sub_self, hc0, one_mul, htaps]
  ring

/-- **The window-shift lemma**: a shifted list read at a long window is the base list's
window sum at the shifted base. With `m = 0` this is window EXTENSION (reading a short
list at a longer window). -/
theorem wsum_pshift (M : ops.Model φ) (B : List R) {LB m Lw : ℕ}
    (hB : B.length ≤ LB + 1) (halign : m + LB ≤ Lw) (sf : ℕ → F) (d : ℕ) :
    (∑ k ∈ Finset.range (Lw + 1), φ ((pshift ops m B).getD (Lw - k) ops.zero) * sf (d + k))
      = wsum φ ops B LB sf (d + (Lw - m - LB)) := by
  rw [← Finset.sum_range_reflect]
  have hstep1 : ∀ i ∈ Finset.range (Lw + 1),
      φ ((pshift ops m B).getD (Lw - (Lw + 1 - 1 - i)) ops.zero) * sf (d + (Lw + 1 - 1 - i))
        = φ ((pshift ops m B).getD i ops.zero) * sf (d + (Lw - i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show Lw + 1 - 1 - i = Lw - i by omega, show Lw - (Lw - i) = i by omega]
  rw [Finset.sum_congr rfl hstep1]
  rw [show Lw + 1 = m + (Lw + 1 - m) by omega]
  rw [sum_range_shift_of_zero (m := m) (t := Lw + 1 - m)
    (f := fun i => φ ((pshift ops m B).getD i ops.zero) * sf (d + (Lw - i)))
    (fun i hi => by
      change φ ((pshift ops m B).getD i ops.zero) * sf (d + (Lw - i)) = 0
      rw [getD_pshift_lt m i hi B, M.map_zero, zero_mul])]
  have hstep2 : ∀ j ∈ Finset.range (Lw + 1 - m),
      φ ((pshift ops m B).getD (m + j) ops.zero) * sf (d + (Lw - (m + j)))
        = φ (B.getD j ops.zero) * sf (d + (Lw - (m + j))) := by
    intro j _
    rw [getD_pshift_add B m j]
  rw [Finset.sum_congr rfl hstep2]
  rw [← Finset.sum_subset (s₁ := Finset.range (LB + 1)) (s₂ := Finset.range (Lw + 1 - m))
    (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
    (fun j _ hj => by
      change φ (B.getD j ops.zero) * sf (d + (Lw - (m + j))) = 0
      rw [List.getD_eq_default _ _ (by simp at hj; omega), M.map_zero, zero_mul])]
  rw [← Finset.sum_range_reflect]
  rw [wsum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show LB + 1 - 1 - k = LB - k by omega,
    show Lw - (m + (LB - k)) = Lw - m - LB + k by omega,
    ← add_assoc]

/-- Window extension: a short connection list read at a longer window. -/
theorem wsum_extend (M : ops.Model φ) (Cl : List R) {Lc Lw : ℕ}
    (hcl : Cl.length ≤ Lc + 1) (hle : Lc ≤ Lw) (sf : ℕ → F) (d : ℕ) :
    wsum φ ops Cl Lw sf d = wsum φ ops Cl Lc sf (d + (Lw - Lc)) := by
  have h := wsum_pshift (m := 0) (Lw := Lw) M Cl hcl (by omega) sf d
  exact h

/-- Linearity of the window sum through the Massey update. -/
theorem wsum_massey_update (M : ops.Model φ) (Cl B : List R) (c : R) (m : ℕ) {Lw : ℕ}
    (sf : ℕ → F) (d : ℕ) :
    wsum φ ops (psub ops Cl (pshift ops m (psmul ops c B))) Lw sf d
      = wsum φ ops Cl Lw sf d
        - φ c * ∑ k ∈ Finset.range (Lw + 1),
            φ ((pshift ops m B).getD (Lw - k) ops.zero) * sf (d + k) := by
  rw [wsum, wsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [getD_massey_update M]
  ring

/-- Peeling one element off a reversed take (the window's newest symbol). -/
theorem take_reverse_succ {α : Type*} (d : α) : ∀ (s : List α) (n : ℕ), n < s.length →
    (s.take (n + 1)).reverse = s.getD n d :: (s.take n).reverse
  | a :: s, 0, _ => rfl
  | a :: s, n + 1, h => by
    have ih := take_reverse_succ d s n (by simpa using h)
    simp only [List.take_succ_cons, List.reverse_cons, List.getD_cons_succ]
    rw [ih]
    rfl

/-- Reading the window list `x :: rev` top-down: entry `i` is the sequence at `n − i`. -/
theorem window_read {s : List R} {n : ℕ} (hn : n < s.length) :
    ∀ i, i ≤ n → ((s.getD n ops.zero :: (s.take n).reverse).getD i ops.zero)
      = s.getD (n - i) ops.zero := by
  intro i hi
  match i with
  | 0 => simp
  | j + 1 =>
    rw [List.getD_cons_succ]
    have hlen : (s.take n).length = n := List.length_take_of_le (by omega)
    have hj : j < n := by omega
    rw [List.getD_reverse _ (by omega : j < (s.take n).length)]
    rw [hlen]
    have htake : (s.take n).getD (n - 1 - j) ops.zero = s.getD (n - 1 - j) ops.zero := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
      rw [List.getElem_take]
      exact (List.getD_eq_getElem _ _ (by omega)).symm
    rw [htake, show n - 1 - j = n - (j + 1) by omega]

end Bridge

/-! ## The invariant

The `GaoInv` pattern: an external `Prop`-structure over the plain state, threaded through
`bmLoop` by structural induction. Generation is carried in the internal `wsum` form
(converted to the public taps form only in the main theorems); minimality is carried at
EVERY prefix — the Massey exchange must fire at each length change. -/

section Invariant

variable {ops : FieldOps R} {φ : R → F}

/-- The loop invariant. `sf` abbreviates the φ-read of the syndrome list. In `hwit`,
case (i) is the virgin state (no nonzero discrepancy seen); case (ii) carries the last
length-change data: window base `dB`, previous length `LB`, with `dB + 1 = L` the stored
subtraction-free form of Massey's `L = p + 1 − L_B` at `p = dB + LB`. -/
structure BMInv (φ : R → F) (ops : FieldOps R) (s : List R) (st : BMState R) : Prop where
  hnrev : st.n = st.rev.length
  hrev : st.rev = (s.take st.n).reverse
  hLn : st.L ≤ st.n
  hclen : st.C.length ≤ st.L + 1
  hc0 : φ (st.C.getD 0 ops.zero) = 1
  hgen : ∀ d, d + st.L < st.n →
    wsum φ ops st.C st.L (fun j => φ (s.getD j ops.zero)) d = 0
  hmin : ∀ (L' : ℕ) (cf' : Fin L' → F),
    Generates L' cf' (fun j => φ (s.getD j ops.zero)) st.n → st.L ≤ L'
  hwit :
    (st.L = 0 ∧ st.C = [ops.one] ∧ st.B = [ops.one] ∧ st.b = ops.one ∧ st.m = st.n + 1)
    ∨ (∃ dB LB : ℕ, dB + 1 = st.L ∧ 2 * LB ≤ dB + LB ∧ dB + LB + st.m = st.n
        ∧ 1 ≤ st.m ∧ st.B.length ≤ LB + 1 ∧ φ (st.B.getD 0 ops.zero) = 1
        ∧ (∀ d, d + LB < dB + LB →
            wsum φ ops st.B LB (fun j => φ (s.getD j ops.zero)) d = 0)
        ∧ φ st.b = wsum φ ops st.B LB (fun j => φ (s.getD j ops.zero)) dB
        ∧ φ st.b ≠ 0)

/-- The invariant holds at the initial state. -/
theorem bmInv_init (M : ops.Model φ) (s : List R) : BMInv φ ops s (bmInit ops) where
  hnrev := rfl
  hrev := rfl
  hLn := le_refl 0
  hclen := le_refl 1
  hc0 := by rw [show (bmInit ops).C.getD 0 ops.zero = ops.one from rfl, M.map_one]
  hgen := fun d hd => absurd (show d + 0 < (0 : ℕ) from hd) (by omega)
  hmin := fun L' _ _ => Nat.zero_le L'
  hwit := Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The discrepancy read at the top window: under the invariant, `pdot C (x :: rev)` IS
the window sum at base `d₀` for any `d₀ + L = n`. -/
theorem bmInv_disc (M : ops.Model φ) {s : List R} {st : BMState R}
    (inv : BMInv φ ops s st) (hn : st.n < s.length) {d₀ : ℕ} (hd₀ : d₀ + st.L = st.n) :
    φ (pdot ops st.C (s.getD st.n ops.zero :: st.rev))
      = wsum φ ops st.C st.L (fun j => φ (s.getD j ops.zero)) d₀ := by
  refine pdot_bridge M inv.hclen (by omega) _ (fun i hi => ?_) hd₀
  rw [inv.hrev, window_read hn i (by omega)]

/-- **Step closure, δ = 0**: the keep branch preserves the invariant. -/
theorem bmInv_step_zero (M : ops.Model φ) {s : List R} {st : BMState R}
    (inv : BMInv φ ops s st) (hn : st.n < s.length)
    (hδ : ops.beq (pdot ops st.C (s.getD st.n ops.zero :: st.rev)) ops.zero = true) :
    BMInv φ ops s (bmStep ops st (s.getD st.n ops.zero)) := by
  have hstep : bmStep ops st (s.getD st.n ops.zero)
      = { st with
          n := st.n + 1
          m := st.m + 1
          rev := s.getD st.n ops.zero :: st.rev } := by
    rw [bmStep]
    simp only [hδ]
    rfl
  rw [hstep]
  have hzero : ∀ d₀, d₀ + st.L = st.n →
      wsum φ ops st.C st.L (fun j => φ (s.getD j ops.zero)) d₀ = 0 := by
    intro d₀ hd₀
    rw [← bmInv_disc M inv hn hd₀]
    exact (M.beq_zero_iff _).mp hδ
  exact {
    hnrev := show st.n + 1 = (s.getD st.n ops.zero :: st.rev).length by
      rw [List.length_cons, ← inv.hnrev]
    hrev := show s.getD st.n ops.zero :: st.rev = (s.take (st.n + 1)).reverse by
      rw [take_reverse_succ ops.zero s st.n hn, inv.hrev]
    hLn := Nat.le_succ_of_le inv.hLn
    hclen := inv.hclen
    hc0 := inv.hc0
    hgen := fun d hd => by
      have hd' : d + st.L < st.n + 1 := hd
      rcases Nat.lt_or_ge (d + st.L) st.n with h | h
      · exact inv.hgen d h
      · exact hzero d (by omega)
    hmin := fun L' cf' hg => inv.hmin L' cf' (generates_mono hg (Nat.le_succ st.n))
    hwit := by
      rcases inv.hwit with ⟨h1, h2, h3, h4, h5⟩ | ⟨dB, LB, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      · exact Or.inl ⟨h1, h2, h3, h4, show st.m + 1 = st.n + 1 + 1 by omega⟩
      · exact Or.inr ⟨dB, LB, h1, h2, show dB + LB + (st.m + 1) = st.n + 1 by omega,
          show 1 ≤ st.m + 1 by omega, h5, h6, h7, h8, h9⟩ }

/-- A false boolean zero-test is a φ-nonzero value. -/
theorem beq_zero_false (M : ops.Model φ) {x : R}
    (hδ : ops.beq x ops.zero = false) : φ x ≠ 0 := by
  intro h
  rw [(M.beq_zero_iff x).mpr h] at hδ
  exact Bool.noConfusion hδ

/-- **Step closure, update** (δ ≠ 0, `2L > n`): the no-length-change branch preserves the
invariant. The window alignment `m + LB ≤ L` IS the branch guard — the design's (\*). -/
theorem bmInv_step_update (M : ops.Model φ) {s : List R} {st : BMState R}
    (inv : BMInv φ ops s st) (hn : st.n < s.length)
    (hδ : ops.beq (pdot ops st.C (s.getD st.n ops.zero :: st.rev)) ops.zero = false)
    (hguard : ¬ 2 * st.L ≤ st.n) :
    BMInv φ ops s (bmStep ops st (s.getD st.n ops.zero)) := by
  rcases inv.hwit with ⟨hL0, _, _, _, _⟩
    | ⟨dB, LB, hdB, h2LB, hsum, hm1, hBlen, hB0, hBgen, hb, hbne⟩
  · exact absurd (show 2 * st.L ≤ st.n by omega) hguard
  set x := s.getD st.n ops.zero with hx
  set δw := pdot ops st.C (x :: st.rev) with hδw
  set c := ops.mul δw (ops.inv st.b) with hc
  have hstep : bmStep ops st x
      = { st with
          n := st.n + 1
          C := psub ops st.C (pshift ops st.m (psmul ops c st.B))
          m := st.m + 1
          rev := x :: st.rev } := by
    simp only [bmStep]
    split_ifs with h1
    · rw [hδ] at h1
      exact Bool.noConfusion h1
    · rw [hc, hδw]
  have hφδ : φ δw ≠ 0 := beq_zero_false M hδ
  have halign : st.m + LB ≤ st.L := by omega
  have hφc : φ c = φ δw * (φ st.b)⁻¹ := by rw [hc, M.map_mul, M.map_inv]
  have hdisc : ∀ d₀, d₀ + st.L = st.n →
      wsum φ ops st.C st.L (fun j => φ (s.getD j ops.zero)) d₀ = φ δw :=
    fun d₀ hd₀ => (bmInv_disc M inv hn hd₀).symm
  rw [hstep]
  exact {
    hnrev := show st.n + 1 = (x :: st.rev).length by rw [List.length_cons, ← inv.hnrev]
    hrev := show x :: st.rev = (s.take (st.n + 1)).reverse by
      rw [take_reverse_succ ops.zero s st.n hn, inv.hrev]
    hLn := Nat.le_succ_of_le inv.hLn
    hclen := show (psub ops st.C (pshift ops st.m (psmul ops c st.B))).length ≤ st.L + 1 by
      rw [length_psub, length_pshift, length_psmul]
      have h1 := inv.hclen
      omega
    hc0 := show φ ((psub ops st.C (pshift ops st.m (psmul ops c st.B))).getD 0 ops.zero) = 1 by
      rw [getD_massey_update M, getD_pshift_lt st.m 0 (by omega) st.B, M.map_zero, mul_zero,
        sub_zero, inv.hc0]
    hgen := fun d hd => by
      have hd' : d + st.L < st.n + 1 := hd
      change wsum φ ops (psub ops st.C (pshift ops st.m (psmul ops c st.B))) st.L
        (fun j => φ (s.getD j ops.zero)) d = 0
      rw [wsum_massey_update M,
        wsum_pshift (sf := fun j => φ (s.getD j ops.zero)) (d := d) M st.B hBlen halign]
      rcases Nat.lt_or_ge (d + st.L) st.n with hcase | hcase
      · rw [inv.hgen d hcase, hBgen (d + (st.L - st.m - LB)) (by omega)]
        ring
      · have hdn : d + st.L = st.n := by omega
        rw [hdisc d hdn, show d + (st.L - st.m - LB) = dB by omega, ← hb, hφc,
          mul_assoc, inv_mul_cancel₀ hbne, mul_one, sub_self]
    hmin := fun L' cf' hg => inv.hmin L' cf' (generates_mono hg (Nat.le_succ st.n))
    hwit := Or.inr ⟨dB, LB, hdB, h2LB, show dB + LB + (st.m + 1) = st.n + 1 by omega,
      show 1 ≤ st.m + 1 by omega, hBlen, hB0, hBgen, hb, hbne⟩ }

/-- **Step closure, jump** (δ ≠ 0, `2L ≤ n`): the length-change branch. Minimality at the
new length is `generates_jump`; the new witness data is the pre-jump state, with the
alignment `m' + L_B' = L'` EXACT — the design's (\*\*). -/
theorem bmInv_step_jump (M : ops.Model φ) {s : List R} {st : BMState R}
    (inv : BMInv φ ops s st) (hn : st.n < s.length)
    (hδ : ops.beq (pdot ops st.C (s.getD st.n ops.zero :: st.rev)) ops.zero = false)
    (hguard : 2 * st.L ≤ st.n) :
    BMInv φ ops s (bmStep ops st (s.getD st.n ops.zero)) := by
  set x := s.getD st.n ops.zero with hx
  set δw := pdot ops st.C (x :: st.rev) with hδw
  set c := ops.mul δw (ops.inv st.b) with hc
  set L' := st.n + 1 - st.L with hL'
  have hstep : bmStep ops st x
      = { n := st.n + 1
          L := L'
          C := psub ops st.C (pshift ops st.m (psmul ops c st.B))
          B := st.C
          b := δw
          m := 1
          rev := x :: st.rev } := by
    simp only [bmStep]
    split_ifs with h1
    · rw [hδ] at h1
      exact Bool.noConfusion h1
    · rw [hc, hδw, hL']
  have hφδ : φ δw ≠ 0 := beq_zero_false M hδ
  have hLL' : st.L ≤ L' := by have := inv.hLn; omega
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ + st.L = st.n := ⟨st.n - st.L, by have := inv.hLn; omega⟩
  have hdisc : wsum φ ops st.C st.L (fun j => φ (s.getD j ops.zero)) d₀ = φ δw :=
    (bmInv_disc M inv hn hd₀).symm
  have hgenC : Generates st.L
      (fun l => ((bmTaps ops (st.L, st.C)).map φ).getD (l : ℕ) 0)
      (fun j => φ (s.getD j ops.zero)) st.n :=
    (generates_taps_iff_wsum M inv.hc0 _ st.n).mpr inv.hgen
  have hmB : st.m + st.B.length ≤ L' + 1 := by
    rcases inv.hwit with ⟨hL0, _, hB1, _, hm⟩ | ⟨dB, LB, hdB, _, hsum, _, hBlen, _, _, _, _⟩
    · rw [hB1]
      simp only [List.length_cons, List.length_nil]
      omega
    · omega
  rw [hstep]
  exact {
    hnrev := show st.n + 1 = (x :: st.rev).length by rw [List.length_cons, ← inv.hnrev]
    hrev := show x :: st.rev = (s.take (st.n + 1)).reverse by
      rw [take_reverse_succ ops.zero s st.n hn, inv.hrev]
    hLn := show L' ≤ st.n + 1 by omega
    hclen := show (psub ops st.C (pshift ops st.m (psmul ops c st.B))).length ≤ L' + 1 by
      rw [length_psub, length_pshift, length_psmul]
      have h1 := inv.hclen
      omega
    hc0 := show φ ((psub ops st.C (pshift ops st.m (psmul ops c st.B))).getD 0 ops.zero) = 1 by
      have hm1 : 1 ≤ st.m := by
        rcases inv.hwit with ⟨_, _, _, _, hm⟩ | ⟨_, _, _, _, _, hm1', _, _, _, _, _⟩
        · omega
        · exact hm1'
      rw [getD_massey_update M, getD_pshift_lt st.m 0 (by omega) st.B, M.map_zero, mul_zero,
        sub_zero, inv.hc0]
    hgen := fun d hd => by
      have hd' : d + L' < st.n + 1 := hd
      rcases inv.hwit with ⟨hL0, _, _, _, _⟩
        | ⟨dB, LB, hdB, _, hsum, _, hBlen, _, hBgen, hb, hbne⟩
      · exact absurd hd' (by omega)
      · change wsum φ ops (psub ops st.C (pshift ops st.m (psmul ops c st.B))) L'
          (fun j => φ (s.getD j ops.zero)) d = 0
        have halignB : st.m + LB ≤ L' := by omega
        rw [wsum_massey_update M,
          wsum_pshift (sf := fun j => φ (s.getD j ops.zero)) (d := d) M st.B hBlen halignB,
          wsum_extend (sf := fun j => φ (s.getD j ops.zero)) (d := d) M st.C inv.hclen hLL']
        have hφc : φ c = φ δw * (φ st.b)⁻¹ := by rw [hc, M.map_mul, M.map_inv]
        rcases Nat.lt_or_ge (d + L') st.n with hcase | hcase
        · rw [inv.hgen (d + (L' - st.L)) (by omega),
            hBgen (d + (L' - st.m - LB)) (by omega)]
          ring
        · have hdn : d + L' = st.n := by omega
          rw [show d + (L' - st.L) = d₀ by omega, hdisc,
            show d + (L' - st.m - LB) = dB by omega, ← hb, hφc,
            mul_assoc, inv_mul_cancel₀ hbne, mul_one, sub_self]
    hmin := fun Lc cf' hg => by
      have hjump := generates_jump hgenC hg hd₀ (fun heq => hφδ (by
        rw [← hdisc, wsum_eq_sub M inv.hc0]
        rw [heq, sub_self]))
      exact show L' ≤ Lc by omega
    hwit := by
      refine Or.inr ⟨d₀, st.L, show d₀ + 1 = L' by omega,
        show 2 * st.L ≤ d₀ + st.L by omega, show d₀ + st.L + 1 = st.n + 1 by omega,
        le_refl 1, inv.hclen, inv.hc0, fun d hdd => inv.hgen d (by omega), ?_, hφδ⟩
      exact hdisc.symm }

/-- Every step advances the counter. -/
theorem bmStep_n (st : BMState R) (x : R) : (bmStep ops st x).n = st.n + 1 := by
  simp only [bmStep]
  split_ifs <;> rfl

theorem bmLoop_n : ∀ (rest : List R) (st : BMState R),
    (bmLoop ops rest st).n = st.n + rest.length
  | [], st => by simp [bmLoop]
  | x :: rest, st => by
    rw [show bmLoop ops (x :: rest) st = bmLoop ops rest (bmStep ops st x) from rfl,
      bmLoop_n rest _, bmStep_n]
    simp only [List.length_cons]
    omega

/-- The invariant threads through the whole loop. -/
theorem bmLoop_inv (M : ops.Model φ) {s : List R} : ∀ (rest : List R) (st : BMState R),
    BMInv φ ops s st → rest = s.drop st.n → BMInv φ ops s (bmLoop ops rest st)
  | [], st, inv, _ => inv
  | x :: rest, st, inv, hrest => by
    have hn : st.n < s.length := by
      by_contra hle
      rw [List.drop_eq_nil_of_le (by omega)] at hrest
      exact List.cons_ne_nil x rest hrest
    have hx : x = s.getD st.n ops.zero := by
      have h0 : (x :: rest).getD 0 ops.zero = s.getD st.n ops.zero := by
        rw [hrest, List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_drop, List.getD_eq_getElem _ _ (by omega)]
        simp
      exact h0
    have hrest' : rest = s.drop (st.n + 1) := by
      rw [← List.tail_drop, ← hrest]
      rfl
    have hstepinv : BMInv φ ops s (bmStep ops st x) := by
      rw [hx]
      cases hbe : ops.beq (pdot ops st.C (s.getD st.n ops.zero :: st.rev)) ops.zero with
      | true => exact bmInv_step_zero M inv hn hbe
      | false =>
        rcases Nat.lt_or_ge st.n (2 * st.L) with hg | hg
        · exact bmInv_step_update M inv hn hbe (by omega)
        · exact bmInv_step_jump M inv hn hbe hg
    exact bmLoop_inv M rest (bmStep ops st x) hstepinv (by rw [bmStep_n, ← hrest'])

end Invariant

/-! ## Main theorems (a): synthesis and minimality -/

section MainTheorems

variable {ops : FieldOps R} {φ : R → F}

/-- The final state's invariant. -/
theorem bmFinal_inv (M : ops.Model φ) (s : List R) :
    BMInv φ ops s (bmLoop ops s (bmInit ops)) :=
  bmLoop_inv M s (bmInit ops) (bmInv_init M s) rfl

theorem bmFinal_n (ops : FieldOps R) (s : List R) :
    (bmLoop ops s (bmInit ops)).n = s.length := by
  rw [bmLoop_n]
  exact show 0 + s.length = s.length by omega

/-- **The algorithm's taps generate the whole sequence.** -/
theorem bmSynth_generates (M : ops.Model φ) (s : List R) :
    Generates (bmSynth ops s).1
      (fun l => ((bmTaps ops (bmSynth ops s)).map φ).getD (l : ℕ) 0)
      (fun j => φ (s.getD j ops.zero)) s.length := by
  have inv := bmFinal_inv M s
  have hn := bmFinal_n ops s
  have h := (generates_taps_iff_wsum M inv.hc0 (fun j => φ (s.getD j ops.zero))
    (bmLoop ops s (bmInit ops)).n).mpr inv.hgen
  rw [hn] at h
  exact h

/-- **Minimality**: no shorter recurrence generates the sequence — quantified over ALL
F-side generators, not algorithm outputs. -/
theorem bmSynth_minimal (M : ops.Model φ) (s : List R) {L' : ℕ} {cf' : Fin L' → F}
    (h : Generates L' cf' (fun j => φ (s.getD j ops.zero)) s.length) :
    (bmSynth ops s).1 ≤ L' := by
  have inv := bmFinal_inv M s
  have hn := bmFinal_n ops s
  exact inv.hmin L' cf' (by rw [hn]; exact h)

/-- **The synthesized length IS the linear complexity.** -/
theorem bmSynth_shortest (M : ops.Model φ) (s : List R) :
    IsShortestGenerator (bmSynth ops s).1 (fun j => φ (s.getD j ops.zero)) s.length :=
  ⟨⟨_, bmSynth_generates M s⟩, fun _ _ h => bmSynth_minimal M s h⟩

end MainTheorems

/-! ## The locator polynomial

Monic of degree exactly the STORED length — the pad is what survives the
evaluation-point-zero degree drop. -/

section Locator

variable {ops : FieldOps R} {φ : R → F}

theorem length_bmLocator {Lw : ℕ} {Cl : List R} (hclen : Cl.length ≤ Lw + 1) :
    (bmLocator ops (Lw, Cl)).length = Lw + 1 := by
  rw [bmLocator]
  simp only [List.length_reverse, List.length_append, List.length_replicate]
  omega

/-- Coefficient reading of the locator: coefficient `i` is the connection list at `Lw − i`
(so the top coefficient is the unit constant term). -/
theorem coeff_bmLocator (M : ops.Model φ) {Lw : ℕ} {Cl : List R}
    (hclen : Cl.length ≤ Lw + 1) {i : ℕ} (hi : i ≤ Lw) :
    (toPoly φ (bmLocator ops (Lw, Cl))).coeff i = φ (Cl.getD (Lw - i) ops.zero) := by
  rw [toPoly_coeff M, bmLocator]
  rw [List.getD_reverse _ (by
    simp only [List.length_append, List.length_replicate]
    omega)]
  simp only [List.length_append, List.length_replicate]
  rw [show Cl.length + (Lw + 1 - Cl.length) - 1 - i = Lw - i by omega]
  rcases Nat.lt_or_ge (Lw - i) Cl.length with hc | hc
  · rw [List.getD_eq_getElem _ _ (by
      simp only [List.length_append, List.length_replicate]
      omega)]
    rw [List.getElem_append_left hc]
    exact congrArg φ (List.getD_eq_getElem _ _ hc).symm
  · rw [List.getD_eq_getElem _ _ (by
      simp only [List.length_append, List.length_replicate]
      omega)]
    rw [List.getElem_append_right (by omega)]
    rw [List.getElem_replicate]
    exact congrArg φ (List.getD_eq_default _ _ hc).symm

/-- The locator is monic of degree exactly the stored length. -/
theorem bmLocator_monic_natDegree (M : ops.Model φ) {Lw : ℕ} {Cl : List R}
    (hclen : Cl.length ≤ Lw + 1) (hc0 : φ (Cl.getD 0 ops.zero) = 1) :
    (toPoly φ (bmLocator ops (Lw, Cl))).Monic ∧
      (toPoly φ (bmLocator ops (Lw, Cl))).natDegree = Lw := by
  have htop : (toPoly φ (bmLocator ops (Lw, Cl))).coeff Lw = 1 := by
    rw [coeff_bmLocator M hclen (le_refl Lw), Nat.sub_self, hc0]
  have hbeyond : ∀ j, Lw < j → (toPoly φ (bmLocator ops (Lw, Cl))).coeff j = 0 := by
    intro j hj
    rw [toPoly_coeff M, List.getD_eq_default _ _ (by rw [length_bmLocator hclen]; omega),
      M.map_zero]
  have hdegle : (toPoly φ (bmLocator ops (Lw, Cl))).natDegree ≤ Lw :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hbeyond
  have hdeg : (toPoly φ (bmLocator ops (Lw, Cl))).natDegree = Lw :=
    le_antisymm hdegle
      (Polynomial.le_natDegree_of_ne_zero (by rw [htop]; exact one_ne_zero))
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one Lw hdegle htop, hdeg⟩

/-- **The synthesized locator is monic** … -/
theorem bmLocator_monic (M : ops.Model φ) (s : List R) :
    (toPoly φ (bmLocator ops (bmSynth ops s))).Monic :=
  (bmLocator_monic_natDegree M (bmFinal_inv M s).hclen (bmFinal_inv M s).hc0).1

/-- … **of degree exactly the synthesized length** — even when the connection list's
physical degree drops (the 𝔽₃ zero-point example below). -/
theorem bmLocator_natDegree (M : ops.Model φ) (s : List R) :
    (toPoly φ (bmLocator ops (bmSynth ops s))).natDegree = (bmSynth ops s).1 :=
  (bmLocator_monic_natDegree M (bmFinal_inv M s).hclen (bmFinal_inv M s).hc0).2

end Locator

/-! ## The error-locator layer (main theorem (b))

The u-weighted syndrome sequence of an error pattern, the monic DIRECT-ROOT locator
(`∏ (X − C (a i))` — no `∀ i, a i ≠ 0` anywhere), and the moment
machinery: window sums against the syndromes ARE weighted moments of the pattern, `2t`
of them identify a weight-`≤ t` locator uniquely, and divisibility + monicity + degree
force equality — never "the algorithm's first solution". -/

section ErrorLocator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]

/-- The u-weighted syndrome sequence of a pattern: the `synMap` moments, ℕ-indexed. -/
noncomputable def synSeq (a e : ι → F) : ℕ → F :=
  fun j => ∑ i, dualMult a i * a i ^ j * e i

/-- The monic direct-root error locator. -/
noncomputable def errLocator (a e : ι → F) : Polynomial F :=
  ∏ i ∈ Finset.univ.filter (fun i => e i ≠ 0), (Polynomial.X - Polynomial.C (a i))

omit [DecidableEq ι] in
theorem errLocator_monic (a e : ι → F) : (errLocator a e).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (a i)

omit [DecidableEq ι] in
theorem errLocator_natDegree (a e : ι → F) :
    (errLocator a e).natDegree = (Finset.univ.filter (fun i => e i ≠ 0)).card := by
  rw [errLocator, Polynomial.natDegree_prod_of_monic _ _
    (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp

omit [DecidableEq ι] in
theorem errLocator_root {a e : ι → F} {i : ι} (hi : e i ≠ 0) :
    (errLocator a e).eval (a i) = 0 := by
  rw [errLocator, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) (by simp)

omit [DecidableEq F] in
/-- **The window→moment expansion**: a polynomial's window sum against the syndrome
sequence is the weighted moment of the pattern against its values. -/
theorem window_eq_moment (a e : ι → F) {P : Polynomial F} {Lp : ℕ}
    (hP : P.natDegree < Lp + 1) (d : ℕ) :
    (∑ l ∈ Finset.range (Lp + 1), P.coeff l * synSeq a e (d + l))
      = ∑ i, dualMult a i * a i ^ d * e i * P.eval (a i) := by
  simp only [synSeq]
  have h1 : ∀ l ∈ Finset.range (Lp + 1),
      P.coeff l * ∑ i, dualMult a i * a i ^ (d + l) * e i
        = ∑ i, P.coeff l * (dualMult a i * a i ^ (d + l) * e i) :=
    fun l _ => Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_eq_sum_range' hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pow_add]
  ring

omit [DecidableEq ι] [DecidableEq F] in
/-- **Moment injectivity** (the Vandermonde dual, by pure evaluation): a vector supported
on `E` whose first `|E|` moments vanish is zero. -/
theorem moment_inj {a : ι → F} (ha : Function.Injective a) (E : Finset ι)
    {z : ι → F}
    (hsupp : ∀ i ∉ E, z i = 0)
    (hmom : ∀ j, j < E.card → ∑ i, z i * a i ^ j = 0) :
    ∀ i, z i = 0 := by
  classical
  intro i₀
  by_cases hi₀ : i₀ ∈ E
  · set P : Polynomial F := ∏ k ∈ E.erase i₀, (Polynomial.X - Polynomial.C (a k)) with hP
    have hdeg : P.natDegree < E.card := by
      rw [hP, Polynomial.natDegree_prod_of_monic _ _
        (fun k _ => Polynomial.monic_X_sub_C (a k))]
      simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
      have := Finset.card_erase_lt_of_mem hi₀
      omega
    have hzero : ∑ i, z i * P.eval (a i) = 0 := by
      have hexp : ∑ i, z i * P.eval (a i)
          = ∑ l ∈ Finset.range E.card, P.coeff l * ∑ i, z i * a i ^ l := by
        have h1 : ∀ i ∈ (Finset.univ : Finset ι), z i * P.eval (a i)
            = ∑ l ∈ Finset.range E.card, z i * (P.coeff l * a i ^ l) := fun i _ => by
          rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hexp]
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [hmom l (Finset.mem_range.mp hl), mul_zero]
    have hsingle : ∑ i, z i * P.eval (a i) = z i₀ * P.eval (a i₀) := by
      refine Finset.sum_eq_single i₀ (fun i _ hne => ?_) (fun h => absurd (Finset.mem_univ i₀) h)
      by_cases hiE : i ∈ E
      · rw [hP, Polynomial.eval_prod,
          Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hiE⟩) (by simp), mul_zero]
      · rw [hsupp i hiE, zero_mul]
    have hPne : P.eval (a i₀) ≠ 0 := by
      rw [hP, Polynomial.eval_prod]
      refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hk).1 (ha h.symm)
    have := hsingle ▸ hzero
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hPne
  · exact hsupp i₀ hi₀

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Linear factors at common roots divide, by pairwise coprimality — the `ι`-generic
restatement of the library's `prod_X_sub_C_dvd` (kept standalone). -/
theorem prod_X_sub_C_dvd_of_roots {a : ι → F} (ha : Function.Injective a) :
    ∀ (E : Finset ι) (p : Polynomial F), (∀ i ∈ E, p.eval (a i) = 0)
      → (∏ i ∈ E, (Polynomial.X - Polynomial.C (a i))) ∣ p := by
  classical
  intro E
  induction E using Finset.induction_on with
  | empty => intro p _; simp
  | insert i E hiE ih =>
    intro p h
    rw [Finset.prod_insert hiE]
    obtain ⟨q, rfl⟩ : (Polynomial.X - Polynomial.C (a i)) ∣ p :=
      Polynomial.dvd_iff_isRoot.mpr (h i (Finset.mem_insert_self i E))
    refine mul_dvd_mul_left _ (ih q fun k hk => ?_)
    have hev := h k (Finset.mem_insert_of_mem hk)
    rw [Polynomial.eval_mul] at hev
    rcases mul_eq_zero.mp hev with h0 | h0
    · exfalso
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h0
      exact hiE (ha (sub_eq_zero.mp h0) ▸ hk)
    · exact h0

/-- The error locator's windows against the syndrome sequence all vanish. -/
theorem errLocator_window_vanish (a e : ι → F)
    {ν : ℕ} (hν : ν = (Finset.univ.filter (fun i => e i ≠ 0)).card) (d : ℕ) :
    ∑ l ∈ Finset.range (ν + 1), (errLocator a e).coeff l * synSeq a e (d + l) = 0 := by
  rw [window_eq_moment a e (by rw [errLocator_natDegree, hν]; omega) d]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : e i = 0
  · rw [hi]
    ring
  · rw [errLocator_root hi, mul_zero]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- A monic polynomial whose windows against `sf` vanish is a generator: its negated low
coefficients are the taps. -/
theorem generates_of_window_vanish {P : Polynomial F} {ν : ℕ} (hm : P.Monic)
    (hd : P.natDegree = ν) {sf : ℕ → F} {N : ℕ}
    (hv : ∀ d, d + ν < N → ∑ l ∈ Finset.range (ν + 1), P.coeff l * sf (d + l) = 0) :
    Generates ν (fun l => -(P.coeff (l : ℕ))) sf N := by
  intro d hdN
  have h := hv d hdN
  rw [Finset.sum_range_succ] at h
  have htop : P.coeff ν = 1 := hd ▸ hm.coeff_natDegree
  rw [htop, one_mul] at h
  rw [Fin.sum_univ_eq_sum_range (fun l => -(P.coeff l) * sf (d + l)) ν]
  have hneg : ∑ l ∈ Finset.range ν, -(P.coeff l) * sf (d + l)
      = -∑ l ∈ Finset.range ν, P.coeff l * sf (d + l) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hneg]
  linear_combination h

/-- **Window vanishing forces divisibility by the locator**: if a polynomial of degree
`≤ LQ` annihilates all in-prefix windows of the syndrome sequence and the weight+degree
budget fits in `2t`, the error locator divides it. -/
theorem window_vanish_dvd {a e : ι → F} (ha : Function.Injective a) {t : ℕ}
    {Q : Polynomial F} {LQ : ℕ} (hdQ : Q.natDegree ≤ LQ)
    (hwin : ∀ d, d + LQ < 2 * t →
      ∑ l ∈ Finset.range (LQ + 1), Q.coeff l * synSeq a e (d + l) = 0)
    (hbudget : (Finset.univ.filter (fun i => e i ≠ 0)).card + LQ ≤ 2 * t) :
    errLocator a e ∣ Q := by
  have hmom : ∀ j, j < (Finset.univ.filter (fun i => e i ≠ 0)).card →
      ∑ i, (dualMult a i * e i * Q.eval (a i)) * a i ^ j = 0 := by
    intro j hj
    have hw := hwin j (by omega)
    rw [window_eq_moment a e (by omega) j] at hw
    rw [← hw]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hz := moment_inj ha (Finset.univ.filter (fun i => e i ≠ 0))
    (z := fun i => dualMult a i * e i * Q.eval (a i))
    (fun i hiE => by
      change dualMult a i * e i * Q.eval (a i) = 0
      have he0 : e i = 0 := by
        by_contra hne
        exact hiE (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      rw [he0]
      ring)
    hmom
  have hroots : ∀ i ∈ Finset.univ.filter (fun i => e i ≠ 0), Q.eval (a i) = 0 := by
    intro i hiE
    have hi := hz i
    have hei : e i ≠ 0 := (Finset.mem_filter.mp hiE).2
    change dualMult a i * e i * Q.eval (a i) = 0 at hi
    rcases mul_eq_zero.mp hi with h01 | hQ0
    · rcases mul_eq_zero.mp h01 with hdm | he
      · exact absurd hdm (dualMult_ne_zero ha i)
      · exact absurd he hei
    · exact hQ0
  rw [errLocator]
  exact prod_X_sub_C_dvd_of_roots ha _ Q hroots

/-- **Error-locator identification**: on exactly `2t` u-weighted syndromes of a weight-`≤ t`
pattern, the algorithm returns the pattern's weight as its length and the monic
direct-root error locator as its locator polynomial. Uniqueness comes from
divisibility + monicity + degree, never from the algorithm. -/
theorem bm_error_locator {ops : FieldOps R} {φ : R → F} (M : ops.Model φ)
    {a e : ι → F} (ha : Function.Injective a)
    {t : ℕ} (hwt : (Finset.univ.filter (fun i => e i ≠ 0)).card ≤ t)
    {s : List R} (hlen : s.length = 2 * t)
    (hmap : ∀ j, j < 2 * t → φ (s.getD j ops.zero) = synSeq a e j) :
    (bmSynth ops s).1 = (Finset.univ.filter (fun i => e i ≠ 0)).card
    ∧ toPoly φ (bmLocator ops (bmSynth ops s)) = errLocator a e := by
  set ν := (Finset.univ.filter (fun i => e i ≠ 0)).card with hν
  have hgenErr : Generates ν (fun l => -((errLocator a e).coeff (l : ℕ)))
      (fun j => φ (s.getD j ops.zero)) s.length := by
    refine generates_of_window_vanish (errLocator_monic a e)
      ((errLocator_natDegree a e).trans hν.symm) (fun d hd => ?_)
    have hconv : ∑ l ∈ Finset.range (ν + 1),
        (errLocator a e).coeff l * φ (s.getD (d + l) ops.zero)
          = ∑ l ∈ Finset.range (ν + 1), (errLocator a e).coeff l * synSeq a e (d + l) := by
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      rw [hmap (d + l) (by omega)]
    exact hconv.trans (errLocator_window_vanish a e hν d)
  have hLrν : (bmSynth ops s).1 ≤ ν := bmSynth_minimal M s hgenErr
  have hlocwin : ∀ d, d + (bmSynth ops s).1 < 2 * t →
      ∑ l ∈ Finset.range ((bmSynth ops s).1 + 1),
        (toPoly φ (bmLocator ops (bmSynth ops s))).coeff l * synSeq a e (d + l) = 0 := by
    intro d hd
    have hws := (bmFinal_inv M s).hgen d (by
      rw [bmFinal_n]
      exact show d + (bmSynth ops s).1 < s.length by omega)
    have hconv : ∑ l ∈ Finset.range ((bmSynth ops s).1 + 1),
        (toPoly φ (bmLocator ops (bmSynth ops s))).coeff l * synSeq a e (d + l)
          = ∑ l ∈ Finset.range ((bmSynth ops s).1 + 1),
              φ ((bmSynth ops s).2.getD ((bmSynth ops s).1 - l) ops.zero)
                * φ (s.getD (d + l) ops.zero) := by
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' : l ≤ (bmSynth ops s).1 := by
        have := Finset.mem_range.mp hl
        omega
      rw [← hmap (d + l) (by omega)]
      exact congrArg (· * φ (s.getD (d + l) ops.zero))
        (coeff_bmLocator M (bmFinal_inv M s).hclen hl')
    rw [hconv]
    exact hws
  have hdvd : errLocator a e ∣ toPoly φ (bmLocator ops (bmSynth ops s)) :=
    window_vanish_dvd ha (le_of_eq (bmLocator_natDegree M s)) hlocwin (by omega)
  have heq : toPoly φ (bmLocator ops (bmSynth ops s)) = errLocator a e :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (errLocator_monic a e)
      (bmLocator_monic M s) hdvd
      (by rw [bmLocator_natDegree M s, errLocator_natDegree a e]; omega)
  have hLeq : (bmSynth ops s).1 = ν := by
    have hnd := congrArg Polynomial.natDegree heq
    rw [bmLocator_natDegree M s, errLocator_natDegree a e] at hnd
    omega
  exact ⟨hLeq, heq⟩

omit [DecidableEq F] in
/-- **The receiver seam**: below `2t`, the u-weighted syndromes of a corrupted codeword
are those of the error alone — so `bm_error_locator` applies to what the receiver
actually computes. -/
theorem synSeq_codeword_add {a : ι → F} (ha : Function.Injective a) {k t : ℕ}
    (htk : 2 * t + k ≤ Fintype.card ι) {c e : ι → F} (hc : c ∈ rsCode a k)
    {j : ℕ} (hj : j < 2 * t) :
    synSeq a (c + e) j = synSeq a e j := by
  obtain ⟨p, hp, rfl⟩ := mem_rsCode.mp hc
  have hsplit : synSeq a (rsEval a p + e) j
      = (∑ i, dualMult a i * ((Polynomial.X ^ j * p).eval (a i))) + synSeq a e j := by
    simp only [synSeq, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [rsEval, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring
  rw [hsplit]
  have hdeg : (Polynomial.X ^ j * p).degree < ((Fintype.card ι - 1 : ℕ) : WithBot ℕ) := by
    rcases eq_or_ne p 0 with rfl | hp0
    · rw [mul_zero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · have hXj : (Polynomial.X : Polynomial F) ^ j ≠ 0 := pow_ne_zero j Polynomial.X_ne_zero
      have hne : Polynomial.X ^ j * p ≠ 0 := mul_ne_zero hXj hp0
      rw [Polynomial.degree_eq_natDegree hne]
      have hnd : (Polynomial.X ^ j * p).natDegree = j + p.natDegree := by
        rw [Polynomial.natDegree_mul hXj hp0, Polynomial.natDegree_X_pow]
      have hpk : p.natDegree < k :=
        (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr (Polynomial.mem_degreeLT.mp hp)
      rw [hnd]
      exact_mod_cast show j + p.natDegree < Fintype.card ι - 1 by omega
  rw [sum_dualMult_eval ha hdeg, zero_add]

end ErrorLocator

/-! ## Branch-coverage examples

Every branch of `bmStep` is exercised with CONTENT rows, at 𝔽₂ and — for the
evaluation-point-zero geometry — 𝔽₃. The expected values were derived independently of
the implementation. -/

/-- 𝔽₃ ops for the examples below (mirrors `zmod2Ops`). -/
def zmod3Ops : FieldOps (ZMod 3) where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  inv := (·⁻¹)
  beq := fun x y => decide (x = y)

-- degenerate inputs: empty, all-zero (L = 0, unit connection, empty taps)
example : bmSynth zmod2Ops [] = (0, [1]) := by decide
example : bmSynth zmod2Ops [0, 0, 0, 0] = (0, [1]) := by decide
example : bmTaps zmod2Ops (bmSynth zmod2Ops [0, 0, 0, 0]) = [] := by decide
example : bmLocator zmod2Ops (bmSynth zmod2Ops [0, 0, 0, 0]) = [1] := by decide

-- the 2L = n jump event at the first symbol, and the maximal-complexity case L = N
example : (bmSynth zmod2Ops [1]).1 = 1 := by decide
example : (bmSynth zmod2Ops [0, 0, 0, 1]).1 = 4 := by decide

-- a run exercising ALL THREE branches (jump, δ = 0 keep, no-change update):
-- the m-sequence prefix [1,0,1,0,1] has L = 2
example : (bmSynth zmod2Ops [1, 0, 1, 0, 1]).1 = 2 := by decide

-- content rows (never L alone): symmetric and asymmetric tap pins
example : (bmSynth zmod2Ops [1, 1, 0, 1, 1, 0]).1 = 2 := by decide
example : bmTaps zmod2Ops (bmSynth zmod2Ops [1, 1, 0, 1, 1, 0]) = [1, 1] := by decide
example : bmTaps zmod2Ops (bmSynth zmod2Ops [1, 0, 1, 0, 1, 0]) = [1, 0] := by decide

-- the evaluation-point-zero geometry (𝔽₃, u-weighted moments of the weight-2 pattern
-- {(a=0, e=1), (a=1, e=1)}, 2t = 4 syndromes): L = 2 while the connection list's
-- semantic degree DROPS (top coefficient φ-zero) — the stored-L pad restores the monic
-- degree-2 locator X² − X = X(X − 1), the factor X carrying the zero point
example : bmSynth zmod3Ops [2, 1, 1, 1] = (2, [1, 2, 0]) := by decide
example : bmTaps zmod3Ops (bmSynth zmod3Ops [2, 1, 1, 1]) = [0, 1] := by decide
example : bmLocator zmod3Ops (bmSynth zmod3Ops [2, 1, 1, 1]) = [0, 2, 1] := by decide

-- the stored-L padding pin in isolation
example : bmLocator zmod2Ops (2, [1, 1]) = [0, 1, 1] := by decide

end ECCLib.Coding
