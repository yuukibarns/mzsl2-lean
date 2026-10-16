import Mathlib
import MzSl2.FiberMap
import MzSl2.PhiMap
import MzSl2.Invariant
import MzSl2.D751Help
import MzSl2.F737i
import MzSl2.F8de

/-!
# Fact 737, "(3) ⇒ (1)": a `ρ(d)`-invariant compact open subgroup of the comparison kernel forces
finite integral index

Setting: `N ≤ Γ` infinite, commensurated; `L = N ∩ SL₂(ℤ)`; `H = Γ//L`; `q : H → Γ//Λ` the fibre
map; `E = ker q`; `g = ρ(d)`. If `V ≤ H` is compact open and `V ∩ E` is invariant under
conjugation by `g`, then `[SL₂(ℤ) : L] < ∞`.
-/

open Matrix Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Fact 737, (3) ⇒ (1)**, for a general commensurated `L ≤ Λ`. -/
theorem core737_of {L : Subgroup (Γ p)} (hL : L ≤ Λp p) (hLc : IsCommensurated L)
    (hLinf : (L : Set (Γ p)).Infinite) {m : ℕ} (hm : 0 < m)
    (huL : uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    (hvL : vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    (V : Subgroup (Hc L)) (hV : IsCompactOpenSubgroup V)
    (hinv : ∀ x ∈ V, qmap hL x = 1 →
      ρH L (dγ p) * x * (ρH L (dγ p))⁻¹ ∈ V ∧ (ρH L (dγ p))⁻¹ * x * ρH L (dγ p) ∈ V) :
    L.relIndex (Λp p) ≠ 0 := by
  classical
  haveI := locallyCompact_Hc L hLc
  set q := qmap hL
  set E := q.ker
  have hEcl : IsClosed (E : Set (Hc L)) := isClosed_singleton.preimage (continuous_qmap hL)
  -- 1. `C`, `F`, `H₀`
  obtain ⟨C, hCE, hCc, ⟨O, hO, hOC⟩, hCn⟩ := exists_normal_compact hL hLc V hV hinv
  obtain ⟨F, hFfin, hFE, hgen⟩ := exists_finite_gen hL hLc hm huL hvL C hCE O hO hOC
  obtain ⟨hH₀o, hH₀fi⟩ := actKer_open_finiteIndex hL hLc hLinf C hCE O hO hOC hFfin hFE hgen
  set H₀ := actKer E C
  haveI hH₀n : H₀.Normal := actKer_normal E C
  have hH₀idx : H₀.index ≠ 0 := hH₀fi.1
  by_contra hcon
  -- 2. `[E : C] = ∞`, otherwise `E` is compact
  have hCE0 : C.relIndex E = 0 := by
    by_contra h
    refine absurd hcon ?_
    refine relIndex_ne_zero_of_ker_compact hL hLc hm huL hvL ?_
    haveI : (C.subgroupOf E).FiniteIndex := ⟨h⟩
    have hsub : (E : Set (Hc L)) ⊆
        (Set.range fun c : E ⧸ C.subgroupOf E => ((c.out : E) : Hc L)) * (C : Set (Hc L)) := by
      intro e he
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (C.subgroupOf E) ⟨e, he⟩
      refine Set.mem_mul.mpr ⟨_, ⟨QuotientGroup.mk ⟨e, he⟩, rfl⟩, ((c : E) : Hc L)⁻¹,
        C.inv_mem (mem_subgroupOf.mp c.2), ?_⟩
      dsimp only
      rw [hc]; simp
    exact ((Set.finite_range _).isCompact.mul hCc).of_isClosed_subset hEcl hsub
  -- 3. `λ`
  have hCH₀ : C ≤ H₀ := by
    intro c hc e he
    have := C.mul_mem hc (hCn.conj_mem _ (C.inv_mem hc) e)
    simpa [mul_assoc] using this
  have hH₀E : H₀.relIndex E ≠ 0 :=
    relIndex_ne_zero_of_le_right' le_top (by rwa [relIndex_top_right])
  obtain ⟨lam, hladd, hlC, a0, ha0, hla0⟩ := exists_hom_to_int hCE hCH₀ hFfin hFE hgen
    (fun h hh e he => hh e he) hH₀E (fun e _ c hc => hCn.conj_mem c hc e) hCE0
  have hmemA : ∀ a, a ∈ H₀ → q a = 1 → a ∈ E ⊓ H₀ := fun a ha hqa => ⟨hqa, ha⟩
  -- 4. hypotheses of `exists_eta`
  have hqo : IsOpenMap q := qmap_isOpenMap hL hLc hm huL hvL
  have hqs : Function.Surjective q := qmap_surjective hL hLc hm huL hvL
  have hqH₀ : ∀ y, ∃ h ∈ H₀, q h = y := by
    haveI : (H₀.map q).Normal := hH₀n.map q hqs
    have htop := G0_normal_finiteIndex_eq_top (H₀.map q)
      (ne_zero_of_dvd_ne_zero hH₀idx (Subgroup.index_map_dvd _ hqs))
    intro y
    have : y ∈ H₀.map q := by rw [htop]; trivial
    obtain ⟨h, hh, rfl⟩ := this
    exact ⟨h, hh, rfl⟩
  have hadd : ∀ a b, a ∈ H₀ → b ∈ H₀ → q a = 1 → q b = 1 → lam (a * b) = lam a + lam b :=
    fun a b ha hb hqa hqb => hladd a (hmemA a ha hqa) b (hmemA b hb hqb)
  have hconj : ∀ h ∈ H₀, ∀ a ∈ H₀, q a = 1 → lam (h * a * h⁻¹) = lam a := by
    intro h hh a ha hqa
    have haE : a ∈ E := hqa
    have hc : h * a * h⁻¹ * a⁻¹ ∈ C := hh a haE
    have e : h * a * h⁻¹ = (h * a * h⁻¹ * a⁻¹) * a := by group
    rw [e, hladd _ ⟨hCE hc, hCH₀ hc⟩ _ (hmemA a ha hqa), hlC _ hc, zero_add]
  have h1O : (1 : Hc L) ∈ O := by
    have : (1 : Hc L) ∈ (C : Set (Hc L)) := C.one_mem
    rw [hOC] at this; exact this.1
  have hcl : IsClosed {h : Hc L | h ∈ H₀ ∧ q h = 1 ∧ lam h = 0} := by
    apply isClosed_of_closure_subset
    intro x hx
    have hAcl : IsClosed ((E ⊓ H₀ : Subgroup (Hc L)) : Set (Hc L)) :=
      hEcl.inter (Subgroup.isClosed_of_isOpen _ hH₀o)
    have hxA : x ∈ E ⊓ H₀ :=
      closure_minimal (fun y hy => (⟨hy.2.1, hy.1⟩ : y ∈ E ⊓ H₀)) hAcl hx
    obtain ⟨k, hkO, hkS⟩ := mem_closure_iff.mp hx ((fun y => x⁻¹ * y) ⁻¹' O)
      (hO.preimage (continuous_const.mul continuous_id)) (by simpa using h1O)
    have hkA : k ∈ E ⊓ H₀ := ⟨hkS.2.1, hkS.1⟩
    have hxk : x⁻¹ * k ∈ C := by
      rw [← SetLike.mem_coe, hOC]
      exact ⟨hkO, E.mul_mem (E.inv_mem hxA.1) hkA.1⟩
    refine ⟨hxA.2, hxA.1, ?_⟩
    have := hladd x hxA _ ⟨hCE hxk, hCH₀ hxk⟩
    rw [mul_inv_cancel_left, hlC _ hxk, add_zero] at this
    rw [← this]; exact hkS.2.2
  -- a compact open subgroup `V₀ ≤ H₀` with `V₀ ⊆ O`
  obtain ⟨V₀, hV₀H, hV₀O, hV₀c, hV₀o⟩ : ∃ V₀ : Subgroup (Hc L), V₀ ≤ H₀ ∧
      (V₀ : Set (Hc L)) ⊆ O ∧ IsCompact (V₀ : Set (Hc L)) ∧ IsOpen (V₀ : Set (Hc L)) := by
    haveI : CompactSpace (UH L) := isCompact_iff_compactSpace.mp (isCompact_UH L hLc)
    obtain ⟨Nn, hNn⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (G := UH L) ((hH₀o.inter hO).preimage continuous_subtype_val)
      (show ((1 : UH L) : Hc L) ∈ (H₀ : Set (Hc L)) ∩ O from ⟨H₀.one_mem, h1O⟩)
    refine ⟨Nn.toSubgroup.map (UH L).subtype, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩; exact (hNn hx).1
    · rintro _ ⟨x, hx, rfl⟩; exact (hNn hx).2
    · rw [Subgroup.coe_map]
      exact (Subgroup.isClosed_of_isOpen _ Nn.isOpen').isCompact.image continuous_subtype_val
    · rw [Subgroup.coe_map]
      exact (isOpen_UH L).isOpenMap_subtype_val _ Nn.isOpen'
  have hV₀lam : ∀ v ∈ V₀, q v = 1 → lam v = 0 := by
    intro v hv hqv
    apply hlC
    rw [← SetLike.mem_coe, hOC]
    exact ⟨hV₀O hv, hqv⟩
  -- 5. `η` and the contradiction
  obtain ⟨η, hηc, hηadd, hηext⟩ := exists_eta q (continuous_qmap hL) hqo H₀ hH₀o hqH₀ lam hadd
    hconj hcl V₀ hV₀H hV₀c hV₀o hV₀lam
  have h0 := eta_eq_zero hLc hLinf H₀ hH₀o hH₀idx η hηc hηadd ⟨a0, ha0.2⟩
  rw [hηext ⟨a0, ha0.2⟩ ha0.1, hla0] at h0
  exact one_ne_zero h0

/-- **Fact 737, (3) ⇒ (1).** -/
theorem core737 {N : Subgroup (Γ p)} (hN : IsCommensurated N) (hinf : (N : Set (Γ p)).Infinite)
    (V : Subgroup (Hc (N ⊓ Λp p))) (hV : IsCompactOpenSubgroup V)
    (hinv : ∀ x ∈ V, qmap (inf_le_right : N ⊓ Λp p ≤ Λp p) x = 1 →
      ρH _ (dγ p) * x * (ρH _ (dγ p))⁻¹ ∈ V ∧ (ρH _ (dγ p))⁻¹ * x * ρH _ (dγ p) ∈ V) :
    (N ⊓ Λp p).relIndex (Λp p) ≠ 0 := by
  obtain ⟨m, hm, hu, hv⟩ := exists_uv_mem hN hinf
  refine core737_of inf_le_right (hN.inf Λp_commensurated)
    (fun hfin => hinf (finite_of_finite_integral hN hfin)) hm
    ⟨hu, by have := uZ_mem_Λp (p := p) (m : ℤ); convert this using 2; push_cast; rfl⟩
    ⟨hv, by have := vZ_mem_Λp (p := p) (m : ℤ); convert this using 2; push_cast; rfl⟩ V hV hinv

end MzSl2
