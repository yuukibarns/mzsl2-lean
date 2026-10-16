import Mathlib
import MzSl2.SymTop

/-!
# The Schlichting completion `G // L`

For a group `G` and a subgroup `L` commensurated by `G`, `Hc L` is the closure of the image of
the permutation representation `ρ : G → Sym (G ⧸ L)`. It is a Hausdorff totally disconnected
topological group, the closure `U` of `ρ(L)` is a compact open subgroup equal to the stabiliser
of the base coset, and `ρ⁻¹(U) = L` (facts e69, 801, 737, step "construction").
-/

open Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {G : Type*} [Group G]

/-- Left cosets, as a discrete space. -/
def Cosets (L : Subgroup G) := G ⧸ L

namespace Cosets

variable (L : Subgroup G)

instance : TopologicalSpace (Cosets L) := ⊥
instance : DiscreteTopology (Cosets L) := ⟨rfl⟩
instance : MulAction G (Cosets L) := inferInstanceAs (MulAction G (G ⧸ L))

/-- The coset `g L`. -/
def mk (g : G) : Cosets L := (QuotientGroup.mk g : G ⧸ L)

theorem mk_surjective : Function.Surjective (mk L) := QuotientGroup.mk_surjective

theorem smul_mk (g h : G) : g • mk L h = mk L (g * h) := rfl

theorem mk_eq_mk {g h : G} : mk L g = mk L h ↔ g⁻¹ * h ∈ L := QuotientGroup.eq

end Cosets

/-- A subgroup is commensurated (by the whole group). -/
def IsCommensurated (L : Subgroup G) : Prop :=
  ∀ g : G, Commensurable (ConjAct.toConjAct g • L) L

theorem mem_conjAct_smul_iff {g x : G} {H : Subgroup G} :
    x ∈ (ConjAct.toConjAct g • H) ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
  simp

variable (L : Subgroup G)

/-- The permutation representation on cosets. -/
def ρ : G →* Sym (Cosets L) := MulAction.toPermHom G (Cosets L)

theorem ρ_apply (g : G) (x : Cosets L) : ρ L g x = g • x := rfl

/-- The Schlichting completion, as a closed subgroup of `Sym (G ⧸ L)`. -/
def Hc : Subgroup (Sym (Cosets L)) := (ρ L).range.topologicalClosure

theorem isClosed_Hc : IsClosed (Hc L : Set (Sym (Cosets L))) :=
  Subgroup.isClosed_topologicalClosure _

theorem ρ_mem_Hc (g : G) : ρ L g ∈ Hc L :=
  Subgroup.le_topologicalClosure _ ⟨g, rfl⟩

/-- The base point `L ∈ G ⧸ L`. -/
def base : Cosets L := Cosets.mk L 1

theorem ρ_mem_stab_iff (g : G) : ρ L g ∈ Sym.stab (base L) ↔ g ∈ L := by
  change g • Cosets.mk L 1 = Cosets.mk L 1 ↔ g ∈ L
  rw [Cosets.smul_mk, mul_one, Cosets.mk_eq_mk]
  constructor
  · intro h; simpa using L.inv_mem h
  · intro h; simpa using L.inv_mem h

/-- The closure `U` of `ρ(L)`. -/
def Uc : Subgroup (Sym (Cosets L)) := (L.map (ρ L)).topologicalClosure

theorem Uc_le_Hc : Uc L ≤ Hc L :=
  Subgroup.topologicalClosure_minimal _
    (by rintro _ ⟨l, -, rfl⟩; exact ρ_mem_Hc L l) (isClosed_Hc L)

theorem Uc_le_stab : Uc L ≤ Sym.stab (base L) :=
  Subgroup.topologicalClosure_minimal _
    (by rintro _ ⟨l, hl, rfl⟩; exact (ρ_mem_stab_iff L l).mpr hl) (Sym.isClosed_stab _)

/-- `U` is the stabiliser of the base point inside `Hc`. -/
theorem Uc_eq : (Uc L : Set (Sym (Cosets L))) = (Hc L : Set _) ∩ Sym.stab (base L) := by
  apply Subset.antisymm
  · exact fun σ hσ => ⟨Uc_le_Hc L hσ, Uc_le_stab L hσ⟩
  · rintro σ ⟨hH, hS⟩
    rw [Uc, Subgroup.topologicalClosure_coe, mem_closure_iff]
    intro o ho hσo
    have hH' : σ ∈ _root_.closure ((ρ L).range : Set (Sym (Cosets L))) := hH
    rw [mem_closure_iff] at hH'
    obtain ⟨_, ⟨hτo, hτS⟩, ⟨g, rfl⟩⟩ :=
      hH' (o ∩ Sym.stab (base L)) (ho.inter (Sym.isOpen_stab _)) ⟨hσo, hS⟩
    exact ⟨ρ L g, hτo, g, (ρ_mem_stab_iff L g).mp hτS, rfl⟩

theorem ρ_preimage_Uc (g : G) : ρ L g ∈ Uc L ↔ g ∈ L := by
  constructor
  · intro h; exact (ρ_mem_stab_iff L g).mp (Uc_le_stab L h)
  · intro h; exact Subgroup.le_topologicalClosure _ ⟨g, h, rfl⟩

/-- Orbits of a commensurated subgroup on cosets are finite. -/
theorem finite_orbit (hL : IsCommensurated L) (g : G) :
    {y : Cosets L | ∃ l ∈ L, y = l • Cosets.mk L g}.Finite := by
  have hi : ((ConjAct.toConjAct g • L).subgroupOf L).index ≠ 0 := (hL g).1
  haveI : ((ConjAct.toConjAct g • L).subgroupOf L).FiniteIndex := ⟨hi⟩
  let f : L ⧸ (ConjAct.toConjAct g • L).subgroupOf L → Cosets L :=
    Quotient.lift (fun l : L => (l : G) • Cosets.mk L g) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ (ConjAct.toConjAct g • L).subgroupOf L :=
        QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf, mem_conjAct_smul_iff] at hab'
      simp only [Cosets.smul_mk, Cosets.mk_eq_mk]
      simpa [mul_assoc] using hab')
  refine (Set.finite_range f).subset ?_
  rintro y ⟨l, hl, rfl⟩
  exact ⟨QuotientGroup.mk ⟨l, hl⟩, rfl⟩

/-- `U` is compact. -/
theorem isCompact_Uc (hL : IsCommensurated L) : IsCompact (Uc L : Set (Sym (Cosets L))) := by
  let O : Cosets L → Set (Cosets L) := fun x => {y | ∃ l ∈ L, y = l • x}
  have hO : ∀ x, (O x).Finite := by
    intro x
    obtain ⟨g, rfl⟩ := Cosets.mk_surjective L x
    exact finite_orbit L hL g
  have hK := Sym.isCompact_preserving O hO
  refine hK.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
  apply closure_minimal _ hK.isClosed
  rintro _ ⟨l, hl, rfl⟩ x
  exact ⟨⟨l, hl, rfl⟩, ⟨l⁻¹, L.inv_mem hl, by rw [← map_inv]; rfl⟩⟩

theorem isOpen_Uc_in_Hc : ∃ V : Set (Sym (Cosets L)), IsOpen V ∧
    (Uc L : Set (Sym (Cosets L))) = (Hc L : Set _) ∩ V :=
  ⟨_, Sym.isOpen_stab (base L), Uc_eq L⟩

end MzSl2
