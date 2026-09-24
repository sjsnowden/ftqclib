/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.PauliExtension
import FTQCLib.Cohomology.SingleInvolutionLift
import FTQCLib.Cohomology.SignedSymplecticTwoGroup

set_option linter.style.longLine false

/-!
# The metaplectic crossed module — the frame's degree-2 data as a 2-group presentation

The frame's degree-2 metaplectic data assembles into a **crossed module**

    δ = `pauliShift` : `PauliGroup n` ⟶ `SignedSymplectic n`,   (a, r) ↦ (1, 2ω(r,·))

with the action `x · (a, r) = (a + x.s r, x.g r)` (`smulH`). Every axiom is an already-built law:

* `pauliShift` is a homomorphism — bilinearity of `ω`;
* **action-wellformedness IS the `valid` law** (`smulH_mul`): expanding `x·(m·m') = (x·m)·(x·m')` produces
  exactly `s(p+q) = s p + s q + frameDistortion g p q` — the crossed-module reading *explains* the defining
  field of `SignedSymplectic`;
* **CM1** (`pauliShift_smulH`): `δ(x·m) = x δ(m) x⁻¹` — the sign cochain cancels and the identity reduces to
  symplecticity of `g`;
* **CM2, the Peiffer identity** (`smulH_pauliShift`): `δ(m)·m' = m m' m⁻¹` — the built swap law
  `betaFrame_swap` plus the cocycle identity `betaFrame_cocycle`;
* `π₁ = ker δ` = the **central `ℤ/4`** (`pauliShift_eq_one_iff` + `PauliGroup.incl_central`), on which the
  whole of `SignedSymplectic` acts trivially (`smulH_incl`) — the **band**;
* `π₀ = coker δ ≅ Sp(2n,𝔽₂)`: `im δ = ker(g-projection)` exactly (`gProj_ker_eq_range`, via nondegeneracy and
  the `crux_dual` duality), the projection is surjective onto the Clifford-symplectic subgroup
  (`exists_signedSymplectic_g`, from the built Clifford model — a Hilbert-side route; a frame-pure route via
  transvection generation is available but not needed here), and `pi0Equiv` packages the first isomorphism.

**Classifying data** (Baez–Lauda Thm 43/Cor 44): the presented 2-group is `(π₀, π₁, action, [a])` =
`(Sp(2n,𝔽₂), ℤ/4, trivial, [a])` — a **central extension of 2-groups** `1 → B(ℤ/4) → 𝒢 → Sp(2n,𝔽₂) → 1`. The
k-invariant `[a] ∈ H³(Sp(2n,𝔽₂), ℤ/4)` is *determined* by this construction (section + defect-lifts +
associator, following Baez–Lauda) but is **not a Lean term in this file and is not computed**.
Because the Pauli part of every defect lift is forced by nondegeneracy, `[a]` is pure `ℤ/4`-phase
bookkeeping of `betaFrame` along a section.

**Relation to Genestier–Lysenko**: at `k = 𝔽₂` their classical
layer (§2.2) matches these objects definition-for-definition — `H(V)` = `PauliGroup`, `ASp(V)`'s α-law =
`valid`, their eq. (3) = the swap law. They *name* the crossed-module presentation as the expected-but-missing
object for their geometric `Ĝ` ("we would rather expect that Ĝ corresponds to a nontrivial crossed module";
open problem in §3.3). This file supplies the presentation at the **classical (ASp/mod-2) level** — the
`AMp(V)` row of their Prop. 1, `π₀ = Sp(2n,𝔽₂)` — not at the Witt level of their geometric `Ĝ`
(`π₀ = Sp(2n,ℤ/4)`). The presentation is nontrivial *as presented* (nonabelian source, non-central boundary,
genuine action — the shape they predicted); whether it is nontrivial *as a 2-group* is exactly `[a] ≠ 0`,
distinct from `metaplecticNonSplit_two` (a different extension — do not transfer).
-/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame

variable {n : ℕ}

/-! ## Preliminaries -/

/-- Two signed-symplectic elements with the same symplectic part and the same sign cochain are equal. -/
theorem SignedSymplectic.ext' {x y : SignedSymplectic n} (hg : x.g = y.g) (hs : x.s = y.s) :
    x = y := by
  cases x; cases y
  simp only at hg hs
  subst hg; subst hs
  rfl

/-- Every sign cochain vanishes at `0` (from `valid` at `p = q = 0`). -/
theorem SignedSymplectic.s_zero (x : SignedSymplectic n) : x.s 0 = 0 := by
  have h := x.valid 0 0
  rw [add_zero, frameDistortion_self, add_zero] at h
  linear_combination -h

/-- Symplectic transport of `omega` along a Clifford map. -/
theorem isClifford_omega {T : Pauli n ≃ₗ[ZMod 2] Pauli n} (hT : IsClifford T) (a b : Pauli n) :
    omega (T a) (T b) = omega a b := by
  have h := hT a b
  rwa [omegaBilin_apply, omegaBilin_apply] at h

@[simp] theorem dbl_zero : dbl (0 : ZMod 2) = 0 := by decide

theorem dbl_eq_zero_iff {x : ZMod 2} : dbl x = 0 ↔ x = 0 := by revert x; decide

/-! ## The boundary map δ -/

/-- The signed-symplectic element `(1, 2ω(r,·))` — the image of a Pauli translation. -/
def shiftChar (r : Pauli n) : SignedSymplectic n where
  g := LinearEquiv.refl (ZMod 2) (Pauli n)
  hg := isClifford_refl
  s := fun p => dbl (omega r p)
  valid := by
    intro p q
    rw [SignedSymplectic.frameDistortion_refl, add_zero, omega_add_right, dbl_add]

@[simp] lemma shiftChar_g (r : Pauli n) :
    (shiftChar r).g = LinearEquiv.refl (ZMod 2) (Pauli n) := rfl

@[simp] lemma shiftChar_s (r p : Pauli n) : (shiftChar r).s p = dbl (omega r p) := rfl

/-- **The boundary of the metaplectic crossed module:** `δ(a, r) = (1, 2ω(r,·))`. A homomorphism by
bilinearity of `ω`. -/
def pauliShift : PauliGroup n →* SignedSymplectic n where
  toFun m := shiftChar m.base
  map_one' := by
    refine SignedSymplectic.ext' rfl (funext fun p => ?_)
    simp [PauliGroup.one_base, omega_zero_left, SignedSymplectic.one_s]
  map_mul' m m' := by
    refine SignedSymplectic.ext' ?_ (funext fun p => ?_)
    · simp [SignedSymplectic.mul_g]
    · simp [SignedSymplectic.mul_s, PauliGroup.mul_base, omega_add_left, dbl_add, add_comm]

@[simp] lemma pauliShift_apply (m : PauliGroup n) : pauliShift m = shiftChar m.base := rfl

/-! ## `π₁`: the kernel is the central `ℤ/4` — the band -/

/-- **The kernel of δ is exactly the central `ℤ/4`:** `δ(m) = 1` iff `m = incl a` for some phase `a`.
With `PauliGroup.incl_central` (already built), this is `π₁ = ℤ/4`, central in the Heisenberg group. -/
theorem pauliShift_eq_one_iff {m : PauliGroup n} :
    pauliShift m = 1 ↔ ∃ a : ZMod 4, PauliGroup.incl a = m := by
  rw [← PauliGroup.proj_eq_zero_iff]
  constructor
  · intro h
    have hs : ∀ p, dbl (omega m.base p) = 0 := fun p => by
      have hp := congrArg (fun z : SignedSymplectic n => z.s p) h
      simpa [SignedSymplectic.one_s] using hp
    have hω : ∀ p, omega m.base p = 0 := fun p => dbl_eq_zero_iff.mp (hs p)
    have hbase : m.base = 0 :=
      omegaBilin_nondegenerate.1 m.base (fun y => by rw [omegaBilin_apply]; exact hω y)
    exact hbase
  · intro h
    refine SignedSymplectic.ext' rfl (funext fun p => ?_)
    have hbase : m.base = 0 := h
    simp [hbase, omega_zero_left, SignedSymplectic.one_s]

/-! ## The action, and action-wellformedness = the `valid` law -/

/-- **The signed-symplectic action on the Heisenberg group:** `x · (a, r) = (a + x.s r, x.g r)`. -/
def smulH (x : SignedSymplectic n) (m : PauliGroup n) : PauliGroup n :=
  ⟨m.phase + x.s m.base, x.g m.base⟩

@[simp] lemma smulH_phase (x : SignedSymplectic n) (m : PauliGroup n) :
    (smulH x m).phase = m.phase + x.s m.base := rfl

@[simp] lemma smulH_base (x : SignedSymplectic n) (m : PauliGroup n) :
    (smulH x m).base = x.g m.base := rfl

/-- **Action-wellformedness IS the `valid` law.** `x` acts multiplicatively on the Heisenberg group —
expanding both sides reduces exactly to `s(p+q) = s p + s q + frameDistortion g p q`. This is the
crossed-module *explanation* of `SignedSymplectic`'s defining field. -/
theorem smulH_mul (x : SignedSymplectic n) (m m' : PauliGroup n) :
    smulH x (m * m') = smulH x m * smulH x m' := by
  refine PauliGroup.ext ?_ ?_
  · simp only [smulH_phase, PauliGroup.mul_phase, PauliGroup.mul_base, smulH_base]
    rw [x.valid m.base m'.base]
    simp only [frameDistortion]
    ring
  · simp [PauliGroup.mul_base, map_add]

theorem one_smulH (m : PauliGroup n) : smulH (1 : SignedSymplectic n) m = m := by
  refine PauliGroup.ext ?_ ?_
  · simp [SignedSymplectic.one_s]
  · simp [SignedSymplectic.one_g]

theorem mul_smulH (x y : SignedSymplectic n) (m : PauliGroup n) :
    smulH (x * y) m = smulH x (smulH y m) := by
  refine PauliGroup.ext ?_ ?_
  · simp [SignedSymplectic.mul_s, add_assoc]
  · simp [SignedSymplectic.mul_g]

/-- The action fixes the band pointwise: `x · incl a = incl a` (the `π₀`-action on `π₁` is trivial —
the presented 2-group is a *central* extension of 2-groups). -/
theorem smulH_incl (x : SignedSymplectic n) (a : ZMod 4) :
    smulH x (PauliGroup.incl a) = PauliGroup.incl a := by
  refine PauliGroup.ext ?_ ?_
  · simp [PauliGroup.incl, SignedSymplectic.s_zero]
  · simp [PauliGroup.incl, map_zero]

/-! ## CM1 — equivariance of the boundary (= symplecticity) -/

/-- **CM1:** `δ(x·m) = x · δ(m) · x⁻¹`. The sign-cochain terms cancel; the identity reduces to
`ω(g r, p) = ω(r, g⁻¹ p)` — symplecticity of `g`. -/
theorem pauliShift_smulH (x : SignedSymplectic n) (m : PauliGroup n) :
    pauliShift (smulH x m) = x * pauliShift m * x⁻¹ := by
  refine SignedSymplectic.ext' ?_ (funext fun p => ?_)
  · simp [SignedSymplectic.mul_g, SignedSymplectic.inv_g]
  · simp only [pauliShift_apply, smulH_base, shiftChar_s,
      SignedSymplectic.mul_s, SignedSymplectic.inv_s, SignedSymplectic.mul_g, shiftChar_g,
      LinearEquiv.trans_apply, LinearEquiv.refl_apply]
    have hcoe : (x⁻¹ : SignedSymplectic n).g = x.g.symm := rfl
    rw [hcoe]
    have h := isClifford_omega x.hg m.base (x.g.symm p)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← h]
    ring

/-! ## CM2 — the Peiffer identity (= the swap law + the cocycle identity) -/

/-- **CM2, the Peiffer identity:** `δ(m) · m' = m · m' · m⁻¹`. The conjugation phase in the Heisenberg
group is `β(b,b') + β(b+b',b)`, which equals `2ω(b,b')` by the built cocycle identity
(`betaFrame_cocycle`) and swap law (`betaFrame_swap`). -/
theorem smulH_pauliShift (m m' : PauliGroup n) :
    smulH (pauliShift m) m' = m * m' * m⁻¹ := by
  refine PauliGroup.ext ?_ ?_
  · simp only [smulH_phase, pauliShift_apply, shiftChar_s,
      PauliGroup.mul_phase, PauliGroup.mul_base, PauliGroup.inv_phase, PauliGroup.inv_base]
    have hcoc := betaFrame_cocycle m'.base m.base m.base
    rw [betaFrame_self, pauli_add_self, betaFrame_zero_right] at hcoc
    have hswap := betaFrame_swap m.base m'.base
    have hdbl : dbl (omega m.base m'.base)
        = 2 * (((omega m.base m'.base).val : ℕ) : ZMod 4) := rfl
    rw [hdbl]
    have hcomm : m'.base + m.base = m.base + m'.base := add_comm _ _
    rw [hcomm] at hcoc
    set c : ZMod 4 := (((omega m.base m'.base).val : ℕ) : ZMod 4) with hc
    have h4 : c + c + c + c = 0 := by
      have hall : ∀ w : ZMod 4, w + w + w + w = 0 := by decide
      exact hall c
    linear_combination hcoc + hswap + h4
  · simp only [smulH_base, pauliShift_apply, shiftChar_g, LinearEquiv.refl_apply,
      PauliGroup.mul_base, PauliGroup.inv_base]
    rw [add_assoc, add_comm m'.base, ← add_assoc, pauli_add_self, zero_add]

/-! ## `π₀ ≅ Sp(2n,𝔽₂)` -/

/-- The symplectic projection, as a homomorphism into the automorphism group of the Pauli space
(`LinearEquiv.automorphismGroup`, whose product is `f * g = g.trans f` — matching `mul_g` exactly). -/
def gProj : SignedSymplectic n →* (Pauli n ≃ₗ[ZMod 2] Pauli n) where
  toFun x := x.g
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma gProj_apply (x : SignedSymplectic n) : gProj x = x.g := rfl

/-- **The image of δ is exactly the kernel of the projection.** `⊇`: a `g`-trivial element's sign
cochain is an additive (`kernel_s_additive`), 2-torsion (`two_smul_s`) character, hence `2ω(u,·)` for
a unique `u` by the `crux_dual` duality. `⊆`: by construction. -/
theorem gProj_ker_eq_range : (gProj (n := n)).ker = (pauliShift (n := n)).range := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro hx
    have hxg : x.g = LinearEquiv.refl (ZMod 2) (Pauli n) := hx
    have h2 : ∀ p, 2 * x.s p = 0 := SignedSymplectic.two_smul_s x
    have hadd : ∀ p q, x.s (p + q) = x.s p + x.s q :=
      SignedSymplectic.kernel_s_additive x hxg
    have hzero : x.s 0 = 0 := SignedSymplectic.s_zero x
    let κ : Pauli n →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun p => hlv (x.s p)
        map_add' := fun p q => by rw [hadd]; exact hlv_add (h2 p) (h2 q)
        map_smul' := by
          intro c p
          have hc : c = 0 ∨ c = 1 := by revert c; decide
          rcases hc with rfl | rfl
          · simp [hzero, hlv]
          · simp }
    obtain ⟨u, hu⟩ := crux_dual LinearMap.id κ
      (fun p hp => by
        have hp0 : p = 0 := by simpa using hp
        simp [hp0, κ, hzero, hlv])
    refine ⟨PauliGroup.sec u, ?_⟩
    refine SignedSymplectic.ext' (by rw [hxg]; rfl) (funext fun p => ?_)
    have hup := hu p
    rw [LinearMap.id_apply] at hup
    have : dbl (hlv (x.s p)) = x.s p := dbl_hlv (h2 p)
    calc (pauliShift (PauliGroup.sec u)).s p = dbl (omega u p) := rfl
      _ = dbl (κ p) := by rw [hup]
      _ = x.s p := this
  · rintro ⟨m, rfl⟩
    rfl

/-- **Per-element existence:** every Clifford-symplectic map carries some valid sign cochain — via the
Clifford model (`act` + `cliffordModPhaseToSp_surjective`). So the projection is surjective onto the
Clifford subgroup and `π₀ ≅ Sp(2n,𝔽₂)`. (This existence proof runs through the Hilbert-side model; a
frame-pure route via transvection generation exists but is not needed for `π₀`.) -/
theorem exists_signedSymplectic_g {g : Pauli n ≃ₗ[ZMod 2] Pauli n} (hg : IsClifford g) :
    ∃ x : SignedSymplectic n, x.g = g := by
  obtain ⟨c, hc⟩ := FTQCLib.Hilbert.cliffordModPhaseToSp_surjective n ⟨g, FTQCLib.Gates.mem_spSubgroup.mpr hg⟩
  exact ⟨act c, by rw [act_g, hc]⟩

/-- The projection's range is exactly the Clifford maps. -/
theorem mem_gProj_range_iff {g : Pauli n ≃ₗ[ZMod 2] Pauli n} :
    g ∈ (gProj (n := n)).range ↔ IsClifford g := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.hg
  · intro hg
    obtain ⟨x, hx⟩ := exists_signedSymplectic_g hg
    exact ⟨x, hx⟩

instance : ((pauliShift (n := n)).range).Normal :=
  gProj_ker_eq_range (n := n) ▸ (MonoidHom.normal_ker (gProj (n := n)))

/-- **`π₀` of the crossed module:** `SignedSymplectic n ⧸ im δ ≅ range(gProj)` — the Clifford-symplectic
group (all of `Sp(2n,𝔽₂)` by `mem_gProj_range_iff` + `cliffordModPhaseToSp_surjective`). -/
noncomputable def pi0Equiv :
    (SignedSymplectic n ⧸ (pauliShift (n := n)).range) ≃* (gProj (n := n)).range :=
  ((QuotientGroup.quotientMulEquivOfEq (gProj_ker_eq_range (n := n)).symm).trans
    (QuotientGroup.quotientKerEquivRange (gProj (n := n))))

end FTQCLib.Cohomology
