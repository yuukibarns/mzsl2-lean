import Mathlib
import MzSl2.F737f

/-!
# Fact 737, step 4e: a homomorphism onto `ℤ` when `E/C` is infinite

Pure group theory. Let `C ≤ E ≤ G` with `E` generated modulo `C` by a finite set, and let `H₀`
act trivially on `E/C` by conjugation and have finite index in `E`. If `[E : C] = ∞`, then the image
of `A = E ∩ H₀` in `E/C` is an infinite, finitely generated (Schreier) abelian group, so it maps
onto `ℤ` (structure theorem). This gives `λ : A → ℤ` additive, vanishing on `C`, and onto.
-/

open Subgroup

namespace MzSl2

variable {G : Type*} [Group G]

/-- **737 (4e).** -/
theorem exists_hom_to_int {E C H₀ : Subgroup G} (hCE : C ≤ E) (hCH₀ : C ≤ H₀) {F : Set G} (hFfin : F.Finite)
    (hFE : F ⊆ E) (hgen : (E : Set G) ⊆ Subgroup.closure (F ∪ (C : Set G)))
    (hact : ∀ h ∈ H₀, ∀ e ∈ E, h * e * h⁻¹ * e⁻¹ ∈ C) (hH₀ : H₀.relIndex E ≠ 0)
    (hCnE : ∀ e ∈ E, ∀ c ∈ C, e * c * e⁻¹ ∈ C) (hinf : C.relIndex E = 0) :
    ∃ lam : G → ℤ, (∀ a ∈ E ⊓ H₀, ∀ b ∈ E ⊓ H₀, lam (a * b) = lam a + lam b) ∧
      (∀ c ∈ C, lam c = 0) ∧ ∃ a ∈ E ⊓ H₀, lam a = 1 := by
  classical
  set C' := C.subgroupOf E
  haveI hC'n : C'.Normal := ⟨fun c hc e => by
    rw [mem_subgroupOf] at hc ⊢
    simpa using hCnE e e.2 c hc⟩
  set Q := E ⧸ C'
  set mk : E →* Q := QuotientGroup.mk' C'
  -- `Q` is finitely generated
  set F' : Set E := Subtype.val ⁻¹' F
  have hF' : F'.Finite := hFfin.preimage Subtype.val_injective.injOn
  haveI hQfg : Group.FG Q := by
    rw [Group.fg_iff]
    refine ⟨mk '' F', ?_, hF'.image _⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective C' q
    set T := (Subgroup.closure (mk '' F')).comap mk
    have hle : Subgroup.closure (F ∪ (C : Set G)) ≤ T.map E.subtype := by
      rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · exact ⟨⟨x, hFE hx⟩, Subgroup.subset_closure
          (Set.mem_image_of_mem mk (show (⟨x, hFE hx⟩ : E) ∈ F' from hx)), rfl⟩
      · refine ⟨⟨x, hCE hx⟩, ?_, rfl⟩
        show mk ⟨x, hCE hx⟩ ∈ Subgroup.closure (mk '' F')
        rw [show mk ⟨x, hCE hx⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr hx]
        exact one_mem _
    obtain ⟨e', he', hee'⟩ := hle (hgen e.2)
    rw [show e' = e from Subtype.ext hee'] at he'
    exact he'
  -- the image of `A`
  set A' : Subgroup Q := (H₀.subgroupOf E).map mk
  have hA'comm : ∀ x y : A', x * y = y * x := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show mk a * mk b = mk b * mk a
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq (s := C')).mpr
    rw [mem_subgroupOf]
    have := hact _ (H₀.inv_mem (mem_subgroupOf.mp hb)) _ (E.inv_mem a.2)
    simpa [mul_assoc] using this
  have hA'fi : A'.index ≠ 0 :=
    ne_zero_of_dvd_ne_zero hH₀ (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective C'))
  haveI : A'.FiniteIndex := ⟨hA'fi⟩
  haveI : Group.FG A' := Subgroup.fg_of_index_ne_zero A'
  letI cg : CommGroup A' := { (inferInstance : Group A') with mul_comm := hA'comm }
  -- `A'` is infinite
  have hA'inf : Infinite A' := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    have h1 := Subgroup.card_mul_index A'
    have h2 : Nat.card Q ≠ 0 := by
      rw [← h1]; exact mul_ne_zero Nat.card_pos.ne' hA'fi
    haveI : Finite Q := (Nat.card_ne_zero.mp h2).2
    exact (Subgroup.index_ne_zero_of_finite : C'.index ≠ 0) hinf
  -- structure theorem
  obtain ⟨ι, j, _, _, pr, hpr, ex, ⟨eqv⟩⟩ := CommGroup.equiv_free_prod_prod_multiplicative_zmod A'
  have hj : Nonempty j := by
    by_contra hj
    rw [not_nonempty_iff] at hj
    haveI : ∀ i, NeZero (pr i ^ ex i) := fun i => ⟨pow_ne_zero _ (hpr i).ne_zero⟩
    haveI : Finite ((j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (pr i ^ ex i)))) :=
      inferInstance
    haveI := Finite.of_equiv _ eqv.symm.toEquiv
    exact not_finite A'
  obtain ⟨j0⟩ := hj
  let χ : A' →* Multiplicative ℤ :=
    (Pi.evalMonoidHom (fun _ : j => Multiplicative ℤ) j0).comp
      ((MonoidHom.fst _ _).comp eqv.toMonoidHom)
  have hχs : Function.Surjective χ := by
    intro z
    refine ⟨eqv.symm (Pi.mulSingle j0 z, 1), ?_⟩
    simp [χ]
  have hmemA : ∀ g (hg : g ∈ E ⊓ H₀), mk ⟨g, hg.1⟩ ∈ A' := fun g hg =>
    ⟨⟨g, hg.1⟩, mem_subgroupOf.mpr hg.2, rfl⟩
  let lam : G → ℤ := fun g =>
    if hg : g ∈ E ⊓ H₀ then Multiplicative.toAdd (χ ⟨mk ⟨g, hg.1⟩, hmemA g hg⟩) else 0
  have hlam : ∀ g (hg : g ∈ E ⊓ H₀),
      lam g = Multiplicative.toAdd (χ ⟨mk ⟨g, hg.1⟩, hmemA g hg⟩) := fun g hg => dif_pos hg
  refine ⟨lam, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [hlam a ha, hlam b hb, hlam (a * b) ((E ⊓ H₀).mul_mem ha hb), ← toAdd_mul, ← map_mul]
    rfl
  · intro c hc
    have hcA : c ∈ E ⊓ H₀ := ⟨hCE hc, hCH₀ hc⟩
    rw [hlam c hcA]
    have : (⟨mk ⟨c, hcA.1⟩, hmemA c hcA⟩ : A') = 1 :=
      Subtype.ext ((QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hc))
    rw [this, map_one, toAdd_one]
  · obtain ⟨y, hy⟩ := hχs (Multiplicative.ofAdd 1)
    obtain ⟨_, ⟨a, ha, rfl⟩⟩ := y
    have haA : (a : G) ∈ E ⊓ H₀ := ⟨a.2, mem_subgroupOf.mp ha⟩
    refine ⟨a, haA, ?_⟩
    rw [hlam _ haA]
    convert congrArg Multiplicative.toAdd hy using 1
    rfl

end MzSl2
