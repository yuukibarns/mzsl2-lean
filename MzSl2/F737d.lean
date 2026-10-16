import Mathlib
import MzSl2.F737c

/-!
# Fact 737, step 4b: the kernel of the action on `E/C` is open, normal and of finite index

`H₀ = {h : h e h⁻¹ e⁻¹ ∈ C for all e ∈ E}`. It is open because `E` is generated modulo `C` by a
finite set; its preimage in `Γ` is normal and infinite (it contains a finite-index subgroup of
the infinite group `L`), hence of finite index by the normal subgroup theorem; by density
`H₀` has finite index in `H`.
-/

open Matrix Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

/-- The normal subgroup theorem for subgroups of the group `Γ`. -/
theorem nst_Γ (N' : Subgroup (Γ p)) (hn : N'.Normal) :
    (N' : Set (Γ p)).Finite ∨ N'.index ≠ 0 := by
  have hle : N'.map (Γ p).subtype ≤ Γ p := map_subtype_le _
  have hnorm : ∀ g ∈ Γ p, ∀ n ∈ N'.map (Γ p).subtype, g * n * g⁻¹ ∈ N'.map (Γ p).subtype := by
    intro g hg n hn'
    obtain ⟨n0, hn0, hn0e⟩ := Subgroup.mem_map.mp hn'
    let g' : Γ p := ⟨g, hg⟩
    have hc : g' * n0 * g'⁻¹ ∈ N' := hn.conj_mem n0 hn0 g'
    refine Subgroup.mem_map.mpr ⟨g' * n0 * g'⁻¹, hc, ?_⟩
    rw [map_mul, map_mul, map_inv, hn0e]
    rfl
  have h := normal_subgroup_theorem p (N'.map (Γ p).subtype) hle hnorm
  rcases h with h | h
  · left
    rw [Subgroup.coe_map] at h
    exact Set.Finite.of_finite_image h Subtype.val_injective.injOn
  · right
    have e : (N'.map (Γ p).subtype).subgroupOf (Γ p) = N' :=
      Subgroup.comap_map_eq_self_of_injective (Γ p).subtype_injective N'
    rwa [relIndex, e] at h

section ActKer

variable {H : Type*} [Group H] (E C : Subgroup H) [hE : E.Normal] [hC : C.Normal]

/-- The kernel of the conjugation action on `E/C`. -/
def actKer : Subgroup H where
  carrier := {h | ∀ e ∈ E, h * e * h⁻¹ * e⁻¹ ∈ C}
  one_mem' := fun e _ => by simp [C.one_mem]
  mul_mem' := fun {h k} hh hk e he => by
    have h1 := hC.conj_mem _ (hk e he) h
    have h2 := hh e he
    have := C.mul_mem h1 h2
    have eq : h * (k * e * k⁻¹ * e⁻¹) * h⁻¹ * (h * e * h⁻¹ * e⁻¹) = h * k * e * (h * k)⁻¹ * e⁻¹ := by
      group
    rwa [eq] at this
  inv_mem' := fun {h} hh e he => by
    have he' : h⁻¹ * e * h ∈ E := by simpa using hE.conj_mem e he h⁻¹
    have := C.inv_mem (hh _ he')
    have eq : (h * (h⁻¹ * e * h) * h⁻¹ * (h⁻¹ * e * h)⁻¹)⁻¹ = h⁻¹ * e * h⁻¹⁻¹ * e⁻¹ := by group
    rwa [eq] at this

theorem actKer_normal : (actKer E C).Normal := by
  constructor
  intro h hh k e he
  have he' : k⁻¹ * e * k ∈ E := by simpa using hE.conj_mem e he k⁻¹
  have := hC.conj_mem _ (hh _ he') k
  have eq : k * (h * (k⁻¹ * e * k) * h⁻¹ * (k⁻¹ * e * k)⁻¹) * k⁻¹ =
      k * h * k⁻¹ * e * (k * h * k⁻¹)⁻¹ * e⁻¹ := by group
  rwa [eq] at this

/-- Elements commuting with a fixed `f` modulo `C`. -/
def zC (f : H) : Subgroup H where
  carrier := {h | h * f * h⁻¹ * f⁻¹ ∈ C}
  one_mem' := by simp [C.one_mem]
  mul_mem' := fun {h k} hh hk => by
    have := C.mul_mem (hC.conj_mem _ hk h) hh
    have eq : h * (k * f * k⁻¹ * f⁻¹) * h⁻¹ * (h * f * h⁻¹ * f⁻¹) = h * k * f * (h * k)⁻¹ * f⁻¹ := by
      group
    rwa [eq] at this
  inv_mem' := fun {h} hh => by
    have := C.inv_mem (hC.conj_mem _ hh h⁻¹)
    have eq : (h⁻¹ * (h * f * h⁻¹ * f⁻¹) * h⁻¹⁻¹)⁻¹ = h⁻¹ * f * h⁻¹⁻¹ * f⁻¹ := by group
    rwa [eq] at this

/-- If `h` centralises a generating set of `E` modulo `C`, it lies in `actKer`. -/
theorem mem_actKer_of_gen {F : Set H} (hgen : (E : Set H) ⊆ Subgroup.closure (F ∪ (C : Set H))) {h : H}
    (hF : ∀ f ∈ F, h * f * h⁻¹ * f⁻¹ ∈ C) : h ∈ actKer E C := by
  let T : Subgroup H :=
    { carrier := {e | h * e * h⁻¹ * e⁻¹ ∈ C}
      one_mem' := by simp [C.one_mem]
      mul_mem' := fun {a b} ha hb => by
        have := C.mul_mem ha (hC.conj_mem _ hb a)
        have eq : h * a * h⁻¹ * a⁻¹ * (a * (h * b * h⁻¹ * b⁻¹) * a⁻¹) = h * (a * b) * h⁻¹ * (a * b)⁻¹ := by
          group
        rwa [eq] at this
      inv_mem' := fun {a} ha => by
        have := hC.conj_mem _ (C.inv_mem ha) a⁻¹
        have eq : a⁻¹ * (h * a * h⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ = h * a⁻¹ * h⁻¹ * a⁻¹⁻¹ := by group
        rwa [eq] at this }
  have hle : Subgroup.closure (F ∪ (C : Set H)) ≤ T := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hF x hx
    · show h * x * h⁻¹ * x⁻¹ ∈ C
      exact C.mul_mem (hC.conj_mem x hx h) (C.inv_mem hx)
  intro e he
  exact hle (hgen he)

end ActKer

variable {L : Subgroup (Γ p)} (hL : L ≤ Λp p)

/-- **737 (4b).** The action kernel is open and of finite index. -/
theorem actKer_open_finiteIndex (hLc : IsCommensurated L) (hLinf : (L : Set (Γ p)).Infinite)
    (C : Subgroup (Hc L)) [hCn : C.Normal] (hCE : C ≤ (qmap hL).ker) (O : Set (Hc L))
    (hO : IsOpen O) (hOC : (C : Set (Hc L)) = O ∩ (qmap hL).ker) {F : Set (Hc L)}
    (hFfin : F.Finite) (hFE : F ⊆ (qmap hL).ker)
    (hgen : ((qmap hL).ker : Set (Hc L)) ⊆ Subgroup.closure (F ∪ (C : Set (Hc L)))) :
    IsOpen (actKer (qmap hL).ker C : Set (Hc L)) ∧ (actKer (qmap hL).ker C).FiniteIndex := by
  haveI := locallyCompact_Hc L hLc
  set E := (qmap hL).ker
  set A := actKer E C
  -- openness
  have hZ : ∀ f ∈ F, IsOpen (zC C f : Set (Hc L)) := by
    intro f hf
    have : (zC C f : Set (Hc L)) = (fun h : Hc L => h * f * h⁻¹ * f⁻¹) ⁻¹' O := by
      ext h
      simp only [zC, SetLike.mem_coe, Subgroup.mem_mk, Set.mem_setOf_eq, mem_preimage]
      constructor
      · intro hh
        have : h * f * h⁻¹ * f⁻¹ ∈ (C : Set (Hc L)) := hh
        rw [hOC] at this; exact this.1
      · intro hh
        have hmem : h * f * h⁻¹ * f⁻¹ ∈ E := by
          have hfE := hFE hf
          exact E.mul_mem (by simpa using (inferInstance : E.Normal).conj_mem f hfE h)
            (E.inv_mem hfE)
        show h * f * h⁻¹ * f⁻¹ ∈ (C : Set (Hc L))
        rw [hOC]; exact ⟨hh, hmem⟩
    rw [this]; exact hO.preimage (by fun_prop)
  set Z := ⨅ f ∈ hFfin.toFinset, zC C f
  have hZopen : IsOpen (Z : Set (Hc L)) := by
    simp only [Z, Subgroup.coe_iInf]
    exact isOpen_biInter_finset fun f hf => hZ f ((Set.Finite.mem_toFinset _).mp hf)
  have hZA : Z ≤ A := by
    intro h hh
    apply mem_actKer_of_gen E C hgen
    intro f hf
    have : h ∈ zC C f := by
      simp only [Z, Subgroup.mem_iInf] at hh
      exact hh f ((Set.Finite.mem_toFinset _).mpr hf)
    exact this
  have hAopen : IsOpen (A : Set (Hc L)) := Subgroup.isOpen_mono hZA hZopen
  refine ⟨hAopen, ⟨?_⟩⟩
  -- finite index via the normal subgroup theorem
  haveI : A.Normal := actKer_normal E C
  set Γ' := A.comap (ρH L)
  haveI : Γ'.Normal := Subgroup.Normal.comap inferInstance _
  have hL1 : Γ'.relIndex L ≠ 0 := by
    have hL' : L = (UH L).comap (ρH L) := by ext x; exact (ρH_mem_UH_iff L x).symm
    rw [relIndex_comap]
    refine relIndex_ne_zero_of_le_right' ?_
      (relIndex_ne_zero_of_isOpen_of_isCompact hAopen (isCompact_UH L hLc))
    rintro _ ⟨l, hl, rfl⟩; exact (ρH_mem_UH_iff L l).mpr hl
  have hΓ'inf : (Γ' : Set (Γ p)).Infinite := by
    intro hfin
    apply hLinf
    exact finite_of_finite_of_relIndex (D := Γ' ⊓ L) (hfin.subset fun x hx => hx.1)
      (by rw [Subgroup.inf_relIndex_right]; exact hL1)
  have hΓ'fi : Γ'.index ≠ 0 := (nst_Γ Γ' inferInstance).resolve_left hΓ'inf
  haveI : Γ'.FiniteIndex := ⟨hΓ'fi⟩
  let f : Γ p ⧸ Γ' → Hc L ⧸ A := QuotientGroup.map Γ' A (ρH L) le_rfl
  have hf : Function.Surjective f := by
    rintro ⟨h⟩
    have hO' : IsOpen ((fun y => h⁻¹ * y) ⁻¹' (A : Set (Hc L))) :=
      hAopen.preimage (continuous_const.mul continuous_id)
    obtain ⟨_, hy, γ, rfl⟩ := (denseRange_ρH L).inter_open_nonempty _ hO'
      ⟨h, by simp [A.one_mem]⟩
    refine ⟨QuotientGroup.mk γ, ?_⟩
    show (QuotientGroup.mk (ρH L γ) : Hc L ⧸ A) = QuotientGroup.mk h
    exact QuotientGroup.eq.mpr (by simpa using A.inv_mem hy)
  haveI : Finite (Hc L ⧸ A) := Finite.of_surjective f hf
  exact Subgroup.index_ne_zero_of_finite

end MzSl2
