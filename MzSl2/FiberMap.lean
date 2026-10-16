import Mathlib
import MzSl2.CompletionTDLC

/-!
# The fibre map `Γ//L → Γ//M` for `L ≤ M` (fact 737, construction of `q`)

Elements of `Hc L` (closure of `ρ_L(G)`) preserve the fibres of `G/L → G/M`, hence induce
permutations of `G/M`. This gives a continuous homomorphism `qmap : Hc L → Hc M` with
`qmap ∘ ρ_L = ρ_M`.
-/

open Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {G : Type*} [Group G] {L M : Subgroup G}

/-- The projection `G/L → G/M`. -/
def cosetProj (hLM : L ≤ M) : Cosets L → Cosets M :=
  Quotient.map' id (fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢; exact hLM h)

theorem cosetProj_mk (hLM : L ≤ M) (g : G) : cosetProj hLM (Cosets.mk L g) = Cosets.mk M g := rfl

theorem cosetProj_smul (hLM : L ≤ M) (g : G) (x : Cosets L) :
    cosetProj hLM (g • x) = g • cosetProj hLM x := by
  obtain ⟨h, rfl⟩ := Cosets.mk_surjective L x
  rfl

theorem cosetProj_surjective (hLM : L ≤ M) : Function.Surjective (cosetProj hLM) := by
  intro z; obtain ⟨g, rfl⟩ := Cosets.mk_surjective M z; exact ⟨Cosets.mk L g, rfl⟩

/-- Fibre-preserving permutations. -/
def FP (hLM : L ≤ M) : Set (Sym (Cosets L)) :=
  {σ | ∀ x y, cosetProj hLM x = cosetProj hLM y → cosetProj hLM (σ x) = cosetProj hLM (σ y)}

theorem isClosed_FP (hLM : L ≤ M) : IsClosed (FP hLM) := by
  have : FP hLM = ⋂ x : Cosets L, ⋂ y : Cosets L,
      {σ : Sym (Cosets L) | cosetProj hLM x = cosetProj hLM y →
        cosetProj hLM (σ x) = cosetProj hLM (σ y)} := by
    ext σ; simp [FP]
  rw [this]
  refine isClosed_iInter fun x => isClosed_iInter fun y => ?_
  by_cases hxy : cosetProj hLM x = cosetProj hLM y
  · simp only [hxy, true_implies]
    have hc : Continuous fun σ : Sym (Cosets L) => (σ x, σ y) :=
      (Sym.continuous_eval x).prodMk (Sym.continuous_eval y)
    exact (isClosed_discrete {q : Cosets L × Cosets L |
      cosetProj hLM q.1 = cosetProj hLM q.2}).preimage hc
  · simp [hxy]

theorem ρ_mem_FP (hLM : L ≤ M) (g : G) : ρ L g ∈ FP hLM := by
  intro x y h
  simp only [ρ_apply, cosetProj_smul, h]

/-- Elements of the completion preserve fibres. -/
theorem Hc_preserves_fibres (hLM : L ≤ M) {σ : Sym (Cosets L)} (hσ : σ ∈ Hc L)
    (x y : Cosets L) (h : cosetProj hLM x = cosetProj hLM y) :
    cosetProj hLM (σ x) = cosetProj hLM (σ y) := by
  have hsub : (Hc L : Set (Sym (Cosets L))) ⊆ FP hLM := by
    rw [Hc, Subgroup.topologicalClosure_coe]
    exact closure_minimal (by rintro _ ⟨g, rfl⟩; exact ρ_mem_FP hLM g) (isClosed_FP hLM)
  exact hsub hσ x y h

/-- A section of the projection. -/
noncomputable def cosetSec (hLM : L ≤ M) : Cosets M → Cosets L :=
  Function.surjInv (cosetProj_surjective hLM)

theorem proj_sec (hLM : L ≤ M) (z : Cosets M) : cosetProj hLM (cosetSec hLM z) = z :=
  Function.surjInv_eq _ z

/-- The induced permutation. -/
noncomputable def qsym (hLM : L ≤ M) (σ : Hc L) : Sym (Cosets M) :=
  (⟨fun z => cosetProj hLM ((σ : Sym (Cosets L)) (cosetSec hLM z)),
    fun z => cosetProj hLM (((σ : Sym (Cosets L)))⁻¹ (cosetSec hLM z)),
    fun z => by
      have h := Hc_preserves_fibres hLM ((Hc L).inv_mem σ.2) _ _
        (proj_sec hLM (cosetProj hLM ((σ : Sym (Cosets L)) (cosetSec hLM z))))
      simp only [Sym.inv_apply_self] at h
      dsimp only
      rw [h, proj_sec],
    fun z => by
      have h := Hc_preserves_fibres hLM σ.2 _ _
        (proj_sec hLM (cosetProj hLM (((σ : Sym (Cosets L)))⁻¹ (cosetSec hLM z))))
      simp only [Sym.apply_inv_self] at h
      dsimp only
      rw [h, proj_sec]⟩ : Equiv.Perm (Cosets M))

theorem qsym_apply (hLM : L ≤ M) (σ : Hc L) (z : Cosets M) :
    qsym hLM σ z = cosetProj hLM ((σ : Sym (Cosets L)) (cosetSec hLM z)) := rfl

theorem qsym_inv_apply (hLM : L ≤ M) (σ : Hc L) (z : Cosets M) :
    (qsym hLM σ)⁻¹ z = cosetProj hLM (((σ : Sym (Cosets L)))⁻¹ (cosetSec hLM z)) := rfl

theorem qsym_proj (hLM : L ≤ M) (σ : Hc L) (x : Cosets L) :
    qsym hLM σ (cosetProj hLM x) = cosetProj hLM ((σ : Sym (Cosets L)) x) :=
  Hc_preserves_fibres hLM σ.2 _ _ (proj_sec hLM _)

theorem qsym_mul (hLM : L ≤ M) (σ τ : Hc L) : qsym hLM (σ * τ) = qsym hLM σ * qsym hLM τ := by
  apply Sym.ext'; intro z
  rw [Sym.mul_apply, qsym_apply hLM τ, qsym_proj, qsym_apply, Subgroup.coe_mul, Sym.mul_apply]

theorem qsym_one (hLM : L ≤ M) : qsym hLM 1 = 1 := by
  apply Sym.ext'; intro z; rw [qsym_apply]; exact proj_sec hLM z

theorem qsym_ρH (hLM : L ≤ M) (g : G) : qsym hLM (ρH L g) = ρ M g := by
  apply Sym.ext'; intro z
  rw [qsym_apply, ρH_coe, ρ_apply, ρ_apply, cosetProj_smul, proj_sec]

theorem continuous_qsym (hLM : L ≤ M) : Continuous (qsym hLM) := by
  apply continuous_induced_rng.mpr
  refine (continuous_pi fun z => ?_).prodMk (continuous_pi fun z => ?_)
  · show Continuous fun σ : Hc L => qsym hLM σ z
    simp only [qsym_apply]
    exact continuous_of_discreteTopology.comp
      ((Sym.continuous_eval _).comp continuous_subtype_val)
  · show Continuous fun σ : Hc L => (qsym hLM σ)⁻¹ z
    simp only [qsym_inv_apply]
    exact continuous_of_discreteTopology.comp
      ((Sym.continuous_eval_inv _).comp continuous_subtype_val)

theorem qsym_mem_Hc (hLM : L ≤ M) (σ : Hc L) : qsym hLM σ ∈ Hc M := by
  have hd : σ ∈ _root_.closure (Set.range (ρH L)) := by
    rw [(denseRange_ρH L).closure_range]; trivial
  have h1 := map_mem_closure (continuous_qsym hLM) hd
    (t := ((ρ M).range : Set (Sym (Cosets M)))) (by
      rintro _ ⟨g, rfl⟩; exact ⟨g, (qsym_ρH hLM g).symm⟩)
  exact h1

/-- The fibre map. -/
noncomputable def qmap (hLM : L ≤ M) : Hc L →* Hc M where
  toFun σ := ⟨qsym hLM σ, qsym_mem_Hc hLM σ⟩
  map_one' := Subtype.ext (qsym_one hLM)
  map_mul' σ τ := Subtype.ext (qsym_mul hLM σ τ)

theorem qmap_apply (hLM : L ≤ M) (σ : Hc L) (x : Cosets L) :
    ((qmap hLM σ : Hc M) : Sym (Cosets M)) (cosetProj hLM x) =
      cosetProj hLM ((σ : Sym (Cosets L)) x) := qsym_proj hLM σ x

theorem qmap_ρH (hLM : L ≤ M) (g : G) : qmap hLM (ρH L g) = ρH M g :=
  Subtype.ext (qsym_ρH hLM g)

theorem continuous_qmap (hLM : L ≤ M) : Continuous (qmap hLM) :=
  (continuous_qsym hLM).subtype_mk _

theorem cosetProj_base (hLM : L ≤ M) : cosetProj hLM (base L) = base M := rfl

theorem qmap_mem_UH_iff (hLM : L ≤ M) (σ : Hc L) :
    qmap hLM σ ∈ UH M ↔ cosetProj hLM ((σ : Sym (Cosets L)) (base L)) = base M := by
  rw [← SetLike.mem_coe, coe_UH, mem_preimage, SetLike.mem_coe]
  show ((qmap hLM σ : Hc M) : Sym (Cosets M)) (base M) = base M ↔ _
  rw [← cosetProj_base hLM, qmap_apply]

/-- The preimage of `U_M` is the closure of `ρ_L(M)`. -/
theorem qmap_preimage_UH (hLM : L ≤ M) :
    (qmap hLM) ⁻¹' (UH M : Set (Hc M)) = _root_.closure (ρH L '' (M : Set G)) := by
  have hρM : ∀ g : G, qmap hLM (ρH L g) ∈ UH M ↔ g ∈ M := by
    intro g; rw [qmap_ρH]; exact ρH_mem_UH_iff M g
  have hopen : IsOpen ((qmap hLM) ⁻¹' (UH M : Set (Hc M))) :=
    (isOpen_UH M).preimage (continuous_qmap hLM)
  apply Subset.antisymm
  · intro σ hσ
    rw [mem_closure_iff]
    intro o ho hσo
    obtain ⟨_, ⟨h1, h2⟩, g, rfl⟩ := (denseRange_ρH L).inter_open_nonempty _ (ho.inter hopen)
      ⟨σ, hσo, hσ⟩ |>.imp fun x hx => hx
    exact ⟨ρH L g, h1, g, (hρM g).mp h2, rfl⟩
  · refine closure_minimal ?_ (Subgroup.isClosed_of_isOpen ((UH M).comap (qmap hLM)) hopen)
    rintro _ ⟨g, hg, rfl⟩
    exact (hρM g).mpr hg

theorem qmap_UH_le (hLM : L ≤ M) : (UH L).map (qmap hLM) ≤ UH M := by
  rintro _ ⟨σ, hσ, rfl⟩
  rw [qmap_mem_UH_iff]
  have : (σ : Sym (Cosets L)) (base L) = base L := by
    exact (Set.ext_iff.mp (coe_UH L) σ).mp hσ
  rw [this]; rfl

end MzSl2
