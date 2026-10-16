import Mathlib
import MzSl2.F737e

/-!
# Fact 737, step 4d: central extensions of `G₀` by a discrete kernel split over `ℤ`

Let `π : X → G₀` be a continuous open surjective homomorphism whose kernel is central and meets
some compact open subgroup `W` trivially, and let `ι : ker π → ℤ` be a homomorphism. Then there is
a continuous homomorphism `η : X → ℤ` extending `ι`.

Proof: `π|_W` is a homeomorphism onto the open subgroup `π(W)`, which gives a continuous section
`s` with `s(1) = 1`; `c(x,y) = ι(s x s y s(xy)⁻¹)` is a continuous 2-cocycle; Casselman–Wigner gives
`c = δb`; perfectness of `G₀` makes `b` integer valued; `η(ξ) = ι(ξ s(πξ)⁻¹) + b(πξ)`.
-/

open Topology Set Subgroup Filter

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

section Discrete

variable {X Y : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [TopologicalSpace Y]

/-- A continuous map with values in a subgroup meeting an open subgroup trivially is locally
constant. -/
theorem eventually_const_of_discrete {Z W : Subgroup X} (hW : IsOpen (W : Set X))
    (hZW : ∀ z ∈ Z, z ∈ W → z = 1) {g : Y → X} (hg : Continuous g) (hgZ : ∀ y, g y ∈ Z) (y0 : Y) :
    ∀ᶠ y in 𝓝 y0, g y = g y0 := by
  have hO : IsOpen ((fun x => (g y0)⁻¹ * x) ⁻¹' (W : Set X)) :=
    hW.preimage (continuous_const.mul continuous_id)
  have hmem : g y0 ∈ (fun x => (g y0)⁻¹ * x) ⁻¹' (W : Set X) := by simp [W.one_mem]
  filter_upwards [hg.continuousAt (hO.mem_nhds hmem)] with y hy
  have h1 : (g y0)⁻¹ * g y ∈ Z := Z.mul_mem (Z.inv_mem (hgZ y0)) (hgZ y)
  have := hZW _ h1 hy
  rw [inv_mul_eq_one] at this; exact this.symm

theorem continuous_comp_of_discrete {Z W : Subgroup X} (hW : IsOpen (W : Set X))
    (hZW : ∀ z ∈ Z, z ∈ W → z = 1) {g : Y → X} (hg : Continuous g) (hgZ : ∀ y, g y ∈ Z)
    {T : Type*} [TopologicalSpace T] (φ : X → T) : Continuous (φ ∘ g) := by
  rw [continuous_iff_continuousAt]
  intro y0
  have := eventually_const_of_discrete hW hZW hg hgZ y0
  exact (continuousAt_const (y := φ (g y0))).congr (this.mono fun y hy => by simp [hy])

end Discrete

variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]

/-- A continuous section of `π` with `s(1) = 1`. -/
theorem exists_section (π : X →* Hc (Λp p)) (hπc : Continuous π) (hπo : IsOpenMap π)
    (hπs : Function.Surjective π) (W : Subgroup X) (hWc : IsCompact (W : Set X))
    (hWo : IsOpen (W : Set X)) (hWZ : ∀ z ∈ W, π z = 1 → z = 1) :
    ∃ s : Hc (Λp p) → X, Continuous s ∧ (∀ y, π (s y) = y) ∧ s 1 = 1 := by
  classical
  set πW : Subgroup (Hc (Λp p)) := W.map π
  have hπWo : IsOpen (πW : Set (Hc (Λp p))) := hπo _ hWo
  -- `π|_W` is a closed embedding
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hWc
  set e : W → Hc (Λp p) := fun w => π w
  have hinj : Function.Injective e := by
    intro a b hab
    have : (a : X)⁻¹ * b ∈ W := W.mul_mem (W.inv_mem a.2) b.2
    have h1 := hWZ _ this (by rw [map_mul, map_inv]; simp only [e] at hab; rw [hab, inv_mul_cancel])
    rw [inv_mul_eq_one] at h1; exact Subtype.ext h1
  have hemb : IsClosedEmbedding e := (hπc.comp continuous_subtype_val).isClosedEmbedding hinj
  have hrange : Set.range e = (πW : Set (Hc (Λp p))) := by
    ext y; constructor
    · rintro ⟨w, rfl⟩; exact ⟨w, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
  set θ0 := hemb.isEmbedding.toHomeomorph.symm
  let θ : Hc (Λp p) → X := fun z => if h : z ∈ Set.range e then ((θ0 ⟨z, h⟩ : W) : X) else 1
  have hθ : ∀ z (h : z ∈ Set.range e), π (θ z) = z := by
    intro z h
    simp only [θ, dif_pos h]
    have := hemb.isEmbedding.toHomeomorph.apply_symm_apply ⟨z, h⟩
    exact congrArg Subtype.val this
  have hθc : ContinuousOn θ (Set.range e) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (Set.range e).restrict θ = fun z => ((θ0 z : W) : X) := by
      funext z; simp only [Set.restrict_apply, θ, dif_pos z.2]
    rw [this]; exact continuous_subtype_val.comp θ0.continuous
  -- coset representatives and their lifts
  haveI : DiscreteTopology (Hc (Λp p) ⧸ πW) := QuotientGroup.discreteTopology hπWo
  let r : Hc (Λp p) ⧸ πW → Hc (Λp p) := fun c => c.out
  let x : Hc (Λp p) ⧸ πW → X := fun c => Function.surjInv hπs (r c)
  have hx : ∀ c, π (x c) = r c := fun c => Function.surjInv_eq hπs _
  have hmem : ∀ y : Hc (Λp p), (r (QuotientGroup.mk y))⁻¹ * y ∈ Set.range e := by
    intro y
    rw [hrange]
    obtain ⟨h, he⟩ := QuotientGroup.mk_out_eq_mul πW y
    show (Quotient.out (QuotientGroup.mk y : Hc (Λp p) ⧸ πW))⁻¹ * y ∈ (πW : Set _)
    rw [he]; simpa using πW.inv_mem h.2
  let s0 : Hc (Λp p) → X := fun y => x (QuotientGroup.mk y) * θ ((r (QuotientGroup.mk y))⁻¹ * y)
  have hs0 : ∀ y, π (s0 y) = y := by
    intro y; simp only [s0, map_mul, hx, hθ _ (hmem y)]; group
  have hs0c : Continuous s0 := by
    rw [continuous_iff_continuousAt]
    intro y0
    set c0 : Hc (Λp p) ⧸ πW := QuotientGroup.mk y0
    have hev : ∀ᶠ y in 𝓝 y0, (QuotientGroup.mk y : Hc (Λp p) ⧸ πW) = c0 :=
      (continuous_quotient_mk'.continuousAt (x := y0)).eventually
        (isOpen_discrete {c0} |>.mem_nhds rfl)
    have hc : ContinuousAt (fun y => x c0 * θ ((r c0)⁻¹ * y)) y0 := by
      refine continuousAt_const.mul ?_
      have h1 : ContinuousAt θ ((r c0)⁻¹ * y0) :=
        hθc.continuousAt (by rw [hrange]; exact hπWo.mem_nhds (by rw [← hrange]; exact hmem y0))
      exact h1.comp (continuousAt_const.mul continuousAt_id)
    exact hc.congr (hev.mono fun y hy => by simp only [s0, hy])
  refine ⟨fun y => s0 y * (s0 1)⁻¹, hs0c.mul continuous_const, fun y => ?_, by simp⟩
  rw [map_mul, map_inv, hs0, hs0, inv_one, mul_one]

/-- **Splitting of central extensions of `G₀` by `ℤ`.** -/
theorem exists_hom_extending (π : X →* Hc (Λp p)) (hπc : Continuous π) (hπo : IsOpenMap π)
    (hπs : Function.Surjective π) (hcen : ∀ z, π z = 1 → ∀ x : X, x * z = z * x)
    (W : Subgroup X) (hWc : IsCompact (W : Set X)) (hWo : IsOpen (W : Set X))
    (hWZ : ∀ z ∈ W, π z = 1 → z = 1) (ι : X → ℤ)
    (hι : ∀ a b, π a = 1 → π b = 1 → ι (a * b) = ι a + ι b) :
    ∃ η : X → ℤ, Continuous η ∧ (∀ a b, η (a * b) = η a + η b) ∧ ∀ z, π z = 1 → η z = ι z := by
  obtain ⟨s, hsc, hs, hs1⟩ := exists_section π hπc hπo hπs W hWc hWo hWZ
  set Z := π.ker
  have hZW : ∀ z ∈ Z, z ∈ W → z = 1 := fun z hz hzW => hWZ z hzW hz
  -- the cocycle
  set k : Hc (Λp p) × Hc (Λp p) → X := fun xy => s xy.1 * s xy.2 * (s (xy.1 * xy.2))⁻¹
  have hkZ : ∀ xy, k xy ∈ Z := by
    intro xy; show π (k xy) = 1; simp [k, hs]
  have hkc : Continuous k := by
    simp only [k]; exact ((hsc.comp continuous_fst).mul (hsc.comp continuous_snd)).mul
      ((hsc.comp (continuous_fst.mul continuous_snd)).inv)
  set c : Hc (Λp p) × Hc (Λp p) → ℤ := fun xy => ι (k xy)
  have hcc : Continuous c := continuous_comp_of_discrete hWo hZW hkc hkZ ι
  have hkid : ∀ x y z, k (x, y) * k (x * y, z) = k (y, z) * k (x, y * z) := by
    intro x y z
    have h1 : s x * s y * s z = k (x, y) * k (x * y, z) * s (x * y * z) := by
      simp only [k]; group
    have h2 : s x * s y * s z = k (y, z) * k (x, y * z) * s (x * y * z) := by
      have hc := hcen (k (y, z)) (hkZ _) (s x)
      simp only [k] at hc ⊢
      calc s x * s y * s z = s x * (s y * s z * (s (y * z))⁻¹) * s (y * z) := by group
        _ = s y * s z * (s (y * z))⁻¹ * s x * s (y * z) := by rw [hc]
        _ = _ := by rw [mul_assoc x y z]; group
    exact mul_right_cancel (h1.symm.trans h2)
  have hcoc : ∀ x y z, c (y, z) - c (x * y, z) + c (x, y * z) - c (x, y) = 0 := by
    intro x y z
    have := congrArg ι (hkid x y z)
    rw [hι _ _ (hkZ _) (hkZ _), hι _ _ (hkZ _) (hkZ _)] at this
    simp only [c]; linarith
  -- Casselman–Wigner
  obtain ⟨b, hbc, hbe⟩ := casselman_wigner_G0 (fun xy => (c xy : ℝ))
    ((continuous_of_discreteTopology (f := fun n : ℤ => (n : ℝ))).comp hcc)
    (fun x y z => by have := hcoc x y z; exact_mod_cast this)
  -- normalisations
  have hι1 : ι 1 = 0 := by have := hι 1 1 (map_one π) (map_one π); simp at this; exact this
  have hk11 : k (1, 1) = 1 := by simp [k, hs1]
  have hb1 : b 1 = 0 := by
    have := hbe 1 1; simp only [c, hk11, hι1, mul_one, Int.cast_zero] at this; linarith
  -- `b` is integer valued: `x ↦ b x mod ℤ` is a homomorphism to `ℝ/ℤ`, hence trivial
  have hbint : ∀ x, ∃ n : ℤ, (n : ℝ) = b x := by
    let χ : Hc (Λp p) →* Multiplicative (AddCircle (1 : ℝ)) :=
      { toFun := fun x => Multiplicative.ofAdd ((b x : ℝ) : AddCircle (1 : ℝ))
        map_one' := by simp [hb1]
        map_mul' := fun x y => by
          rw [← ofAdd_add, ← AddCircle.coe_add]
          congr 1
          rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
          exact ⟨c (x, y), by rw [← hbe x y]; simp⟩ }
    intro x
    have h := congrArg (fun f => f x) (G0_hom_comm_trivial χ)
    simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply] at h
    have h' : ((b x : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [← ofAdd_zero] at h; exact Multiplicative.ofAdd.injective h
    rw [AddCircle.coe_eq_zero_iff] at h'
    obtain ⟨n, hn⟩ := h'
    exact ⟨n, by simpa using hn⟩
  choose β hβ using hbint
  have hβc : Continuous β := by
    rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
    have : ((↑) : ℤ → ℝ) ∘ β = b := funext hβ
    rw [this]; exact hbc
  have hβ1 : β 1 = 0 := by exact_mod_cast (hβ 1).trans hb1
  have hβmul : ∀ x y, β (x * y) = β x + β y - c (x, y) := by
    intro x y
    have := hbe x y; rw [← hβ, ← hβ, ← hβ] at this
    have h : ((β (x * y) : ℤ) : ℝ) = ((β x + β y - c (x, y) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  -- the extension
  set w : X → X := fun ξ => ξ * (s (π ξ))⁻¹
  have hwZ : ∀ ξ, w ξ ∈ Z := by
    intro ξ; show π (w ξ) = 1; simp [w, hs]
  have hwc : Continuous w := continuous_id.mul ((hsc.comp hπc).inv)
  refine ⟨fun ξ => ι (w ξ) + β (π ξ), ?_, ?_, ?_⟩
  · exact (continuous_comp_of_discrete hWo hZW hwc hwZ ι).add (hβc.comp hπc)
  · intro a a'
    have hdec : w (a * a') = w a * w a' * k (π a, π a') := by
      have hc := hcen (w a') (hwZ a') (s (π a))
      simp only [w, k, map_mul] at hc ⊢
      calc a * a' * (s (π a * π a'))⁻¹
          = a * (s (π a))⁻¹ * (s (π a) * (a' * (s (π a'))⁻¹)) * s (π a') *
              (s (π a * π a'))⁻¹ := by group
        _ = a * (s (π a))⁻¹ * (a' * (s (π a'))⁻¹ * s (π a)) * s (π a') *
              (s (π a * π a'))⁻¹ := by rw [hc]
        _ = _ := by group
    simp only [hdec, map_mul]
    rw [hι _ _ (Z.mul_mem (hwZ a) (hwZ a')) (hkZ _), hι _ _ (hwZ a) (hwZ a'), hβmul]
    simp only [c]; ring
  · intro z hz
    simp only [w, hz, hs1, inv_one, mul_one, hβ1, add_zero]

end MzSl2
