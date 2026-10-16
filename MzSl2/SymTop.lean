import Mathlib

/-!
# The permutation group of a discrete set with the topology of pointwise convergence

`Sym X` is `Equiv.Perm X` with the topology induced by `σ ↦ (σ, σ⁻¹) ∈ (X → X) × (X → X)`,
for a discrete set `X`. It is a Hausdorff, totally disconnected topological group; point
stabilisers are open; the set of permutations preserving a family of finite sets is compact.
-/

open Topology Set

namespace MzSl2

variable (X : Type*) [TopologicalSpace X] [DiscreteTopology X]

/-- Permutations of `X` with the pointwise-convergence topology. -/
def Sym := Equiv.Perm X

namespace Sym

instance : Group (Sym X) := inferInstanceAs (Group (Equiv.Perm X))
instance : EquivLike (Sym X) X X := inferInstanceAs (EquivLike (Equiv.Perm X) X X)

variable {X}

@[simp] theorem mul_apply (σ τ : Sym X) (x : X) : (σ * τ) x = σ (τ x) := rfl
@[simp] theorem one_apply (x : X) : (1 : Sym X) x = x := rfl
@[simp] theorem inv_apply_self (σ : Sym X) (x : X) : σ⁻¹ (σ x) = x :=
  Equiv.symm_apply_apply (σ : Equiv.Perm X) x
@[simp] theorem apply_inv_self (σ : Sym X) (x : X) : σ (σ⁻¹ x) = x :=
  Equiv.apply_symm_apply (σ : Equiv.Perm X) x

theorem ext' {σ τ : Sym X} (h : ∀ x, σ x = τ x) : σ = τ := Equiv.ext h

variable (X) in
/-- The embedding into pairs of maps. -/
def toPair (σ : Sym X) : (X → X) × (X → X) := (fun x => σ x, fun x => σ⁻¹ x)

instance : TopologicalSpace (Sym X) := TopologicalSpace.induced (toPair X) inferInstance

theorem toPair_injective : Function.Injective (toPair X) := by
  intro σ τ h
  exact ext' fun x => congrFun (congrArg Prod.fst h) x

theorem isEmbedding_toPair : IsEmbedding (toPair X) := ⟨⟨rfl⟩, toPair_injective⟩

theorem continuous_toPair : Continuous (toPair X) := isEmbedding_toPair.continuous

/-- Evaluation `σ ↦ σ x` is continuous. -/
theorem continuous_eval (x : X) : Continuous fun σ : Sym X => σ x :=
  (continuous_apply x).comp (continuous_fst.comp continuous_toPair)

theorem continuous_eval_inv (x : X) : Continuous fun σ : Sym X => σ⁻¹ x :=
  (continuous_apply x).comp (continuous_snd.comp continuous_toPair)

/-- Composition of maps of a discrete set is continuous. -/
theorem continuous_comp_maps : Continuous fun p : (X → X) × (X → X) => p.1 ∘ p.2 := by
  refine continuous_pi fun x => ?_
  have h : Continuous fun q : (X → X) × X => q.1 q.2 :=
    continuous_prod_of_discrete_right.mpr fun y => continuous_apply y
  exact h.comp (continuous_fst.prodMk ((continuous_apply x).comp continuous_snd))

instance : IsTopologicalGroup (Sym X) where
  continuous_mul := by
    rw [continuous_induced_rng]
    have h1 : Continuous fun p : Sym X × Sym X => (fun x => p.1 x) ∘ (fun x => p.2 x) :=
      continuous_comp_maps.comp
        ((continuous_fst.comp (continuous_toPair.comp continuous_fst)).prodMk
          (continuous_fst.comp (continuous_toPair.comp continuous_snd)))
    have h2 : Continuous fun p : Sym X × Sym X => (fun x => p.2⁻¹ x) ∘ (fun x => p.1⁻¹ x) :=
      continuous_comp_maps.comp
        ((continuous_snd.comp (continuous_toPair.comp continuous_snd)).prodMk
          (continuous_snd.comp (continuous_toPair.comp continuous_fst)))
    refine (h1.prodMk h2).congr ?_
    intro p
    simp only [toPair, Function.comp_def, mul_inv_rev, mul_apply]
  continuous_inv := by
    rw [continuous_induced_rng]
    refine ((continuous_snd.comp continuous_toPair).prodMk
      (continuous_fst.comp continuous_toPair)).congr ?_
    intro σ; simp [toPair]

instance : T2Space (Sym X) := isEmbedding_toPair.t2Space

instance : TotallyDisconnectedSpace (Sym X) := by
  rw [totallyDisconnectedSpace_iff]
  apply isEmbedding_toPair.isTotallyDisconnected
  exact isTotallyDisconnected_of_totallyDisconnectedSpace _

/-- Stabiliser of a point. -/
def stab (x : X) : Subgroup (Sym X) where
  carrier := {σ | σ x = x}
  one_mem' := rfl
  mul_mem' {σ τ} hσ hτ := by simp_all [Set.mem_setOf_eq]
  inv_mem' {σ} hσ := by
    simp only [Set.mem_setOf_eq] at hσ ⊢
    conv_lhs => rw [← hσ]
    exact inv_apply_self σ x

theorem isOpen_stab (x : X) : IsOpen (stab x : Set (Sym X)) :=
  (isOpen_discrete {x}).preimage (continuous_eval x)

theorem isClosed_stab (x : X) : IsClosed (stab x : Set (Sym X)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_stab x)

/-- Permutations preserving a family of finite sets form a compact set. -/
theorem isCompact_preserving (O : X → Set X) (hO : ∀ x, (O x).Finite) :
    IsCompact {σ : Sym X | ∀ x, σ x ∈ O x ∧ σ⁻¹ x ∈ O x} := by
  rw [isEmbedding_toPair.isCompact_iff]
  have hT : IsCompact ((Set.pi univ O) ×ˢ (Set.pi univ O)) :=
    (isCompact_univ_pi fun x => (hO x).isCompact).prod (isCompact_univ_pi fun x => (hO x).isCompact)
  have hR : IsClosed {p : (X → X) × (X → X) | ∀ x, p.1 (p.2 x) = x ∧ p.2 (p.1 x) = x} := by
    simp only [setOf_forall]
    refine isClosed_iInter fun x => IsClosed.inter ?_ ?_
    · exact (isClosed_discrete {x}).preimage
        ((continuous_apply x).comp (continuous_comp_maps (X := X)))
    · exact (isClosed_discrete {x}).preimage
        ((continuous_apply x).comp (continuous_comp_maps (X := X) |>.comp continuous_swap))
  convert hT.inter_left hR using 1
  ext ⟨f, g⟩
  simp only [mem_image, mem_setOf_eq, mem_inter_iff, mem_prod, mem_pi, mem_univ, true_implies]
  constructor
  · rintro ⟨σ, hσ, h⟩
    simp only [toPair, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun x => ⟨by simp, by simp⟩, fun x => (hσ x).1, fun x => (hσ x).2⟩
  · rintro ⟨h, hf, hg⟩
    let e : Equiv.Perm X := ⟨f, g, fun x => (h x).2, fun x => (h x).1⟩
    exact ⟨e, fun x => ⟨hf x, hg x⟩, rfl⟩

end Sym

end MzSl2
