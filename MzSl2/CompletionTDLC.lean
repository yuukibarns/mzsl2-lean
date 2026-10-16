import Mathlib
import MzSl2.Completion
import MzSl2.ScaleLemmas

/-!
# The Schlichting completion is a metrizable tdlc group

For `L` commensurated in `G` we regard `Hc L` as a type. It is a Hausdorff, totally
disconnected, locally compact topological group, metrizable when `G` is countable;
`UH L` (the closure of `ρ(L)`) is a compact open subgroup with `ρ⁻¹(UH) = L`, and the image
of `ρ` is dense.
-/

open Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {G : Type*} [Group G] (L : Subgroup G)

/-- `ρ` as a map into the completion. -/
def ρH : G →* Hc L := (ρ L).codRestrict (Hc L) (ρ_mem_Hc L)

@[simp] theorem ρH_coe (g : G) : ((ρH L g : Hc L) : Sym (Cosets L)) = ρ L g := rfl

/-- The compact open subgroup `U = closure ρ(L)` of the completion. -/
def UH : Subgroup (Hc L) := (Uc L).subgroupOf (Hc L)

theorem coe_UH : ((UH L : Set (Hc L))) = Subtype.val ⁻¹' (Sym.stab (base L) : Set _) := by
  ext ⟨σ, hσ⟩
  simp only [UH, SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_preimage]
  rw [← SetLike.mem_coe, Uc_eq]
  exact ⟨fun h => h.2, fun h => ⟨hσ, h⟩⟩

theorem isOpen_UH : IsOpen (UH L : Set (Hc L)) := by
  rw [coe_UH]; exact (Sym.isOpen_stab _).preimage continuous_subtype_val

theorem isCompact_UH (hL : IsCommensurated L) : IsCompact (UH L : Set (Hc L)) := by
  have hce : IsClosedEmbedding (Subtype.val : Hc L → Sym (Cosets L)) :=
    (isClosed_Hc L).isClosedEmbedding_subtypeVal
  have : (UH L : Set (Hc L)) = Subtype.val ⁻¹' (Uc L : Set (Sym (Cosets L))) := rfl
  rw [this]
  exact hce.isCompact_preimage (isCompact_Uc L hL)

theorem UH_isCompactOpen (hL : IsCommensurated L) : IsCompactOpenSubgroup (UH L) :=
  ⟨isCompact_UH L hL, isOpen_UH L⟩

theorem exists_compactOpen (hL : IsCommensurated L) :
    ∃ V : Subgroup (Hc L), IsCompactOpenSubgroup V := ⟨_, UH_isCompactOpen L hL⟩

theorem ρH_mem_UH_iff (g : G) : ρH L g ∈ UH L ↔ g ∈ L := by
  rw [UH, Subgroup.mem_subgroupOf, ρH_coe]; exact ρ_preimage_Uc L g

theorem denseRange_ρH : DenseRange (ρH L) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro o ho ⟨⟨σ, hσ⟩, hσo⟩
  obtain ⟨o', ho', rfl⟩ := isOpen_induced_iff.mp ho
  have hσ' : σ ∈ _root_.closure ((ρ L).range : Set (Sym (Cosets L))) := hσ
  obtain ⟨_, hτo, ⟨g, rfl⟩⟩ := mem_closure_iff.mp hσ' o' ho' hσo
  exact ⟨ρH L g, hτo, g, rfl⟩

instance : T2Space (Hc L) := inferInstance
instance : TotallyDisconnectedSpace (Hc L) := inferInstance

theorem locallyCompact_Hc (hL : IsCommensurated L) : LocallyCompactSpace (Hc L) :=
  (isCompact_UH L hL).locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_UH L).mem_nhds (UH L).one_mem)

instance [Countable G] : Countable (Cosets L) := (Cosets.mk_surjective L).countable

instance metrizable_Sym {X : Type*} [TopologicalSpace X] [DiscreteTopology X] [Countable X] :
    TopologicalSpace.MetrizableSpace (Sym X) :=
  Sym.isEmbedding_toPair.metrizableSpace

instance [Countable G] : TopologicalSpace.MetrizableSpace (Hc L) :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace (Hc L : Set (Sym (Cosets L))))

end MzSl2
