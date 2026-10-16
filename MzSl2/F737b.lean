import Mathlib
import MzSl2.F737a
import MzSl2.Invariant

/-!
# Fact 737, (3) ⇒ (5): a compact open subgroup of `E` normal in `H`

Instead of the semidirect product `E ⋊ Γ_disc` we use the isomorphic closed subgroup
`P = {(h, γ) : q h = ρ_Λ γ} ≤ H × Γ_disc` and `σ(γ) = (ρ γ, γ)`. The subgroup `(V ∩ E) × 1` is
compact open in `P` and normalised by `σ(d)`; fact c627 gives a compact open subgroup of `P`
normalised by `σ(Γ)`, whose slice over `1` is the required `C`.
-/

open Matrix Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable (p : ℕ) [hp : Fact p.Prime]

/-- `Γ` with the discrete topology. -/
def Gd := Γ p

instance : Group (Gd p) := inferInstanceAs (Group (Γ p))
instance : TopologicalSpace (Gd p) := ⊥
instance : DiscreteTopology (Gd p) := ⟨rfl⟩
instance : IsTopologicalGroup (Gd p) where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology

/-- The identity `Γ → Γ_disc`. -/
def toGd : Γ p →* Gd p := MonoidHom.id _

variable {p} {L : Subgroup (Γ p)} (hL : L ≤ Λp p)

/-- `P = {(h, γ) : q h = ρ_Λ γ}`. -/
noncomputable def Pgrp : Subgroup (Hc L × Gd p) :=
  MonoidHom.eqLocus ((qmap hL).comp (MonoidHom.fst _ _))
    ((ρH (Λp p)).comp ((MonoidHom.id (Γ p)).comp (MonoidHom.snd _ (Gd p))))

theorem mem_Pgrp {x : Hc L × Gd p} : x ∈ Pgrp hL ↔ qmap hL x.1 = ρH (Λp p) (x.2 : Γ p) := Iff.rfl

theorem isClosed_Pgrp : IsClosed (Pgrp hL : Set (Hc L × Gd p)) := by
  have hc1 : Continuous fun x : Hc L × Gd p => qmap hL x.1 :=
    (continuous_qmap hL).comp continuous_fst
  have hc2 : Continuous fun x : Hc L × Gd p => ρH (Λp p) (x.2 : Γ p) :=
    continuous_of_discreteTopology.comp continuous_snd
  exact isClosed_eq hc1 hc2

/-- `σ(γ) = (ρ γ, γ)`. -/
noncomputable def σP : Γ p →* Pgrp hL where
  toFun γ := ⟨(ρH L γ, (γ : Gd p)), by rw [mem_Pgrp]; exact qmap_ρH hL γ⟩
  map_one' := by ext <;> simp <;> rfl
  map_mul' a b := by ext <;> simp <;> rfl

theorem σP_fst (γ : Γ p) : ((σP hL γ : Pgrp hL) : Hc L × Gd p).1 = ρH L γ := rfl
theorem σP_snd (γ : Γ p) : ((σP hL γ : Pgrp hL) : Hc L × Gd p).2 = γ := rfl

/-- **737, (3) ⇒ (5).** -/
theorem exists_normal_compact (hLc : IsCommensurated L) (V : Subgroup (Hc L))
    (hV : IsCompactOpenSubgroup V)
    (hinv : ∀ x ∈ V, qmap hL x = 1 →
      ρH L (dγ p) * x * (ρH L (dγ p))⁻¹ ∈ V ∧ (ρH L (dγ p))⁻¹ * x * ρH L (dγ p) ∈ V) :
    ∃ C : Subgroup (Hc L), C ≤ (qmap hL).ker ∧ IsCompact (C : Set (Hc L)) ∧
      (∃ O : Set (Hc L), IsOpen O ∧ (C : Set (Hc L)) = O ∩ (qmap hL).ker) ∧ C.Normal := by
  haveI := locallyCompact_Hc L hLc
  set E := (qmap hL).ker
  set P := Pgrp hL
  -- `P` is a tdlc group
  haveI : LocallyCompactSpace (P : Set (Hc L × Gd p)) :=
    (isClosed_Pgrp hL).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace P := inferInstanceAs (LocallyCompactSpace (P : Set (Hc L × Gd p)))
  -- the slice `(V ∩ E) × 1`
  let W : Subgroup P :=
    { carrier := {x | (x : Hc L × Gd p).1 ∈ V ∧ (x : Hc L × Gd p).2 = 1}
      one_mem' := ⟨V.one_mem, rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by
        show (a : Hc L × Gd p).2 * (b : Hc L × Gd p).2 = 1; rw [ha.2, hb.2, mul_one]⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by
        show ((a : Hc L × Gd p).2)⁻¹ = 1; rw [ha.2, inv_one]⟩ }
  have hslice : ∀ x : P, (x : Hc L × Gd p).2 = 1 → qmap hL (x : Hc L × Gd p).1 = 1 := by
    intro x hx
    have := (mem_Pgrp hL).mp x.2
    rw [this, hx]; exact map_one _
  have hWopen : IsOpen (W : Set P) := by
    have : (W : Set P) = (fun x : P => (x : Hc L × Gd p)) ⁻¹'
        ((V : Set (Hc L)) ×ˢ ({1} : Set (Gd p))) := by
      ext x; simp [W]
    rw [this]
    exact (hV.2.prod (isOpen_discrete _)).preimage continuous_subtype_val
  have hWcpt : IsCompact (W : Set P) := by
    have hVE : IsCompact ((V : Set (Hc L)) ∩ E) :=
      hV.1.inter_right ((isClosed_singleton.preimage (continuous_qmap hL)))
    let f : Hc L → Hc L × Gd p := fun e => (e, 1)
    have hf : Continuous f := continuous_id.prodMk continuous_const
    have himg : IsCompact (f '' ((V : Set (Hc L)) ∩ E)) := hVE.image hf
    have hsubP : f '' ((V : Set (Hc L)) ∩ E) ⊆ (P : Set (Hc L × Gd p)) := by
      rintro _ ⟨e, ⟨-, he⟩, rfl⟩
      rw [SetLike.mem_coe, mem_Pgrp]; simp only [f]
      rw [show qmap hL e = 1 from he]; exact (map_one _).symm
    rw [(isClosed_Pgrp hL).isClosedEmbedding_subtypeVal.isCompact_iff]
    convert himg using 1
    ext y; constructor
    · rintro ⟨x, ⟨hxV, hx2⟩, rfl⟩
      refine ⟨(x : Hc L × Gd p).1, ⟨hxV, hslice x hx2⟩, ?_⟩
      exact Prod.ext rfl hx2.symm
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨f e, hsubP ⟨e, he, rfl⟩⟩, ⟨he.1, rfl⟩, rfl⟩
  have hWnorm : ConjAct.toConjAct (σP hL (dγ p)) • W = W := by
    ext x
    rw [mem_conj_smul_iff]
    constructor
    · intro hx
      have hx' := hx
      -- `σ(d)⁻¹ x σ(d) ∈ W` forces `x ∈ W`
      obtain ⟨h1, h2⟩ := hx'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv,
        Prod.snd_inv, σP_fst, σP_snd] at h1 h2
      have key : ∀ a b : Gd p, a⁻¹ * b * a = 1 → b = 1 := by
        intro a b h
        calc b = a * (a⁻¹ * b * a) * a⁻¹ := by group
          _ = 1 := by rw [h]; group
      have hx2 : (x : Hc L × Gd p).2 = 1 := key _ _ h2
      have hq : qmap hL ((ρH L (dγ p))⁻¹ * (x : Hc L × Gd p).1 * ρH L (dγ p)) = 1 := by
        rw [map_mul, map_mul, hslice x hx2]; simp
      have := (hinv _ h1 hq).1
      refine ⟨by simpa [mul_assoc] using this, hx2⟩
    · rintro ⟨hxV, hx2⟩
      refine ⟨?_, ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, σP_fst]
        exact (hinv _ hxV (hslice x hx2)).2
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, σP_snd, hx2,
          mul_one]
        exact inv_mul_cancel _
  -- c627 in `P`
  obtain ⟨V', hV', hV'n⟩ := exists_invariant_compactOpen p (σP hL) ⟨W, ⟨hWcpt, hWopen⟩, hWnorm⟩
  -- the slice of `V'` over `1`
  let C : Subgroup (Hc L) :=
    { carrier := {e | ∃ x ∈ V', (x : Hc L × Gd p) = (e, 1)}
      one_mem' := ⟨1, V'.one_mem, rfl⟩
      mul_mem' := fun {a b} ⟨x, hx, hxe⟩ ⟨y, hy, hye⟩ =>
        ⟨x * y, V'.mul_mem hx hy, by simp [hxe, hye]⟩
      inv_mem' := fun {a} ⟨x, hx, hxe⟩ => ⟨x⁻¹, V'.inv_mem hx, by simp [hxe]⟩ }
  have hCE : C ≤ E := by
    rintro e ⟨x, -, hxe⟩
    have h2 : (x : Hc L × Gd p).2 = 1 := congrArg Prod.snd hxe
    have h1 : (x : Hc L × Gd p).1 = e := congrArg Prod.fst hxe
    have := hslice x h2
    rwa [h1] at this
  have hCc : IsCompact (C : Set (Hc L)) := by
    have hcl : IsClosed {x : P | (x : Hc L × Gd p).2 = 1} :=
      (isClosed_discrete {(1 : Gd p)}).preimage (continuous_snd.comp continuous_subtype_val)
    have := (hV'.1.inter_right hcl).image (continuous_fst.comp continuous_subtype_val)
    convert this using 1
    ext e; constructor
    · rintro ⟨x, hx, hxe⟩
      exact ⟨x, ⟨hx, congrArg Prod.snd hxe⟩, congrArg Prod.fst hxe⟩
    · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
      exact ⟨x, hx, Prod.ext rfl hx2⟩
  -- `V'` is open in `P`: write it as `P ∩ O'`
  obtain ⟨O', hO', hO'eq⟩ := isOpen_induced_iff.mp hV'.2
  refine ⟨C, hCE, ?_, ⟨(fun e : Hc L => ((e, 1) : Hc L × Gd p)) ⁻¹' O',
    hO'.preimage (continuous_id.prodMk continuous_const), ?_⟩, ?_⟩
  · exact hCc
  · ext e; constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨?_, hCE ⟨x, hx, hxe⟩⟩
      have : x ∈ (Subtype.val ⁻¹' O' : Set P) := by rw [hO'eq]; exact hx
      simp only [mem_preimage] at this ⊢; rw [← hxe]; exact this
    · rintro ⟨heO, heE⟩
      have hP : ((e, 1) : Hc L × Gd p) ∈ P := by
        rw [mem_Pgrp]; rw [show qmap hL e = 1 from heE]; exact (map_one _).symm
      refine ⟨⟨(e, 1), hP⟩, ?_, rfl⟩
      have : (⟨(e, 1), hP⟩ : P) ∈ (Subtype.val ⁻¹' O' : Set P) := heO
      rw [hO'eq] at this; exact this
  · -- normal: normalised by the dense image `ρ(Γ)` and closed
    have hCnorm : ∀ γ : Γ p, ∀ c ∈ C, ρH L γ * c * (ρH L γ)⁻¹ ∈ C := by
      rintro γ c ⟨x, hx, hxe⟩
      refine ⟨σP hL γ * x * (σP hL γ)⁻¹, ?_, ?_⟩
      · rw [← hV'n γ]; rw [mem_conj_smul_iff]; simpa [mul_assoc] using hx
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxe]
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_mul, Prod.fst_inv, σP_fst]
        · simp only [Prod.snd_mul, Prod.snd_inv, σP_snd]
          change toGd p γ * 1 * (toGd p γ)⁻¹ = 1; simp
    have hCcl : IsClosed (C : Set (Hc L)) := hCc.isClosed
    constructor
    intro c hc h
    have hcl : IsClosed {k : Hc L | k * c * k⁻¹ ∈ C} := hCcl.preimage (by fun_prop)
    have hd : h ∈ _root_.closure (Set.range (ρH L)) := by
      rw [(denseRange_ρH L).closure_range]; trivial
    exact hcl.closure_subset_iff.mpr (by rintro _ ⟨γ, rfl⟩; exact hCnorm γ c hc) hd

end MzSl2
