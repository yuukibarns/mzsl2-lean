import Mathlib
import MzSl2.F737g

/-!
# Fact 737, step 4f: extending `λ` to a continuous homomorphism on `H₀`

Let `q : H → G₀` be continuous and open, `H₀ ≤ H` open, normal, with `q(H₀) = G₀`, and let `λ` be
additive on `A = H₀ ∩ ker q` and invariant under `H₀`-conjugation, with `K = ker λ` closed. Put
`X = H₀/K` and `π : X → G₀` induced by `q`; then `ker π = A/K` is central, and a compact open
subgroup `V₀ ≤ H₀` on which `λ` vanishes over `ker q` maps to a compact open subgroup of `X`
meeting `ker π` trivially. `exists_hom_extending` gives a continuous `η : X → ℤ` extending `λ`.
-/

open Topology Set Subgroup

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

/-- **737 (4f).** -/
theorem exists_eta (q : H →* Hc (Λp p)) (hqc : Continuous q) (hqo : IsOpenMap q)
    (H₀ : Subgroup H) [hH₀n : H₀.Normal] (hH₀o : IsOpen (H₀ : Set H))
    (hqH₀ : ∀ y, ∃ h ∈ H₀, q h = y) (lam : H → ℤ)
    (hadd : ∀ a b, a ∈ H₀ → b ∈ H₀ → q a = 1 → q b = 1 → lam (a * b) = lam a + lam b)
    (hconj : ∀ h ∈ H₀, ∀ a ∈ H₀, q a = 1 → lam (h * a * h⁻¹) = lam a)
    (hcl : IsClosed {h : H | h ∈ H₀ ∧ q h = 1 ∧ lam h = 0})
    (V₀ : Subgroup H) (hV₀ : V₀ ≤ H₀) (hV₀c : IsCompact (V₀ : Set H))
    (hV₀o : IsOpen (V₀ : Set H)) (hV₀lam : ∀ v ∈ V₀, q v = 1 → lam v = 0) :
    ∃ η : H₀ → ℤ, Continuous η ∧ (∀ a b, η (a * b) = η a + η b) ∧
      ∀ a : H₀, q a = 1 → η a = lam a := by
  classical
  have hlam1 : lam 1 = 0 := by
    have := hadd 1 1 H₀.one_mem H₀.one_mem (map_one q) (map_one q); simp at this; exact this
  have hlaminv : ∀ a, a ∈ H₀ → q a = 1 → lam a⁻¹ = -lam a := by
    intro a ha hqa
    have := hadd a⁻¹ a (H₀.inv_mem ha) ha (by simp [hqa]) hqa
    rw [inv_mul_cancel, hlam1] at this; linarith
  -- the closed normal subgroup `K = ker λ` of `H₀`
  let K : Subgroup H₀ :=
    { carrier := {x | q x = 1 ∧ lam x = 0}
      one_mem' := ⟨map_one q, hlam1⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨by simp [ha.1, hb.1], ?_⟩
        show lam ((a : H) * b) = 0
        rw [hadd _ _ a.2 b.2 ha.1 hb.1, ha.2, hb.2, add_zero]
      inv_mem' := fun {a} ha => by
        refine ⟨by simp [ha.1], ?_⟩
        show lam ((a : H)⁻¹) = 0
        rw [hlaminv _ a.2 ha.1, ha.2, neg_zero] }
  have hmemK : ∀ x : H₀, x ∈ K ↔ q x = 1 ∧ lam x = 0 := fun x => Iff.rfl
  haveI hKn : K.Normal := ⟨fun x hx g => by
    rw [hmemK] at hx ⊢
    refine ⟨by simp [hx.1], ?_⟩
    show lam ((g : H) * x * (g : H)⁻¹) = 0
    rw [hconj _ g.2 _ x.2 hx.1, hx.2]⟩
  haveI hKc : IsClosed (K : Set H₀) := by
    have : (K : Set H₀) = Subtype.val ⁻¹' {h : H | h ∈ H₀ ∧ q h = 1 ∧ lam h = 0} := by
      ext x; simp only [SetLike.mem_coe, mem_preimage, mem_setOf_eq]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
    rw [this]; exact hcl.preimage continuous_subtype_val
  -- `X = H₀/K` and `π`
  let mk : H₀ →* H₀ ⧸ K := QuotientGroup.mk' K
  let π : H₀ ⧸ K →* Hc (Λp p) :=
    QuotientGroup.lift K (q.comp H₀.subtype) (fun x hx => (MonoidHom.mem_ker).mpr hx.1)
  have hπmk : ∀ x : H₀, π (mk x) = q x := fun x => rfl
  have hπc : Continuous π := by
    rw [(QuotientGroup.isQuotientMap_mk K).continuous_iff]
    exact hqc.comp continuous_subtype_val
  have hπo : IsOpenMap π := by
    intro S hS
    have hpre : IsOpen ((QuotientGroup.mk : H₀ → H₀ ⧸ K) ⁻¹' S) :=
      hS.preimage QuotientGroup.continuous_mk
    have : π '' S = q '' (Subtype.val '' ((QuotientGroup.mk : H₀ → H₀ ⧸ K) ⁻¹' S)) := by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
        exact ⟨x, ⟨x, hz, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨_, hx, rfl⟩
    rw [this]
    exact hqo _ (hH₀o.isOpenMap_subtype_val _ hpre)
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨h, hh, rfl⟩ := hqH₀ y
    exact ⟨mk ⟨h, hh⟩, rfl⟩
  have hcen : ∀ z, π z = 1 → ∀ x : H₀ ⧸ K, x * z = z * x := by
    intro z hz x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have hqa : q a = 1 := hz
    show mk h * mk a = mk a * mk h
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq (s := K)).mpr
    rw [hmemK]
    have e : (((h * a)⁻¹ * (a * h) : H₀) : H) = (a : H)⁻¹ * ((h : H)⁻¹ * a * (h : H)⁻¹⁻¹) := by
      simp [mul_assoc]
    rw [e]
    have hc : (h : H)⁻¹ * a * (h : H)⁻¹⁻¹ ∈ H₀ := H₀.mul_mem (H₀.mul_mem (H₀.inv_mem h.2) a.2)
      (H₀.inv_mem (H₀.inv_mem h.2))
    have hqc' : q ((h : H)⁻¹ * a * (h : H)⁻¹⁻¹) = 1 := by simp [hqa]
    refine ⟨by simp [hqa], ?_⟩
    rw [hadd _ _ (H₀.inv_mem a.2) hc (by simp [hqa]) hqc', hlaminv _ a.2 hqa,
      hconj _ (H₀.inv_mem h.2) _ a.2 hqa]
    ring
  -- `ι`
  have hrep : ∀ g : H₀, q g = 1 →
      lam (((QuotientGroup.mk g : H₀ ⧸ K).out : H₀) : H) = lam g := by
    intro g hg
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk]
    have hkK := (hmemK k).mp k.2
    show lam ((g : H) * (k : H₀)) = lam g
    rw [hadd _ _ g.2 (k : H₀).2 hg hkK.1, hkK.2, add_zero]
  let ι : H₀ ⧸ K → ℤ := fun x => lam ((x.out : H₀) : H)
  have hιmk : ∀ g : H₀, q g = 1 → ι (mk g) = lam g := hrep
  have hι : ∀ a b, π a = 1 → π b = 1 → ι (a * b) = ι a + ι b := by
    intro a b ha hb
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have ha' : q a' = 1 := ha
    have hb' : q b' = 1 := hb
    change ι (mk a' * mk b') = ι (mk a') + ι (mk b')
    rw [← map_mul, hιmk _ (by simp [ha', hb']), hιmk _ ha', hιmk _ hb']
    exact hadd _ _ a'.2 b'.2 ha' hb'
  -- `W`
  have hH₀cl : IsClosed (H₀ : Set H) := Subgroup.isClosed_of_isOpen _ hH₀o
  let W : Subgroup (H₀ ⧸ K) := (V₀.subgroupOf H₀).map mk
  have hV₀'c : IsCompact ((V₀.subgroupOf H₀ : Subgroup H₀) : Set H₀) :=
    hH₀cl.isClosedEmbedding_subtypeVal.isCompact_preimage hV₀c
  have hWc : IsCompact (W : Set (H₀ ⧸ K)) := by
    have := hV₀'c.image (QuotientGroup.continuous_mk (N := K))
    simpa [W, mk] using this
  have hWo : IsOpen (W : Set (H₀ ⧸ K)) := by
    have := QuotientGroup.isOpenMap_coe (N := K) _
      (hV₀o.preimage continuous_subtype_val : IsOpen ((V₀.subgroupOf H₀ : Subgroup H₀) : Set H₀))
    rw [Subgroup.coe_map]; exact this
  have hWZ : ∀ z ∈ W, π z = 1 → z = 1 := by
    rintro _ ⟨v, hv, rfl⟩ hz
    have hqv : q v = 1 := hz
    exact (QuotientGroup.eq_one_iff _).mpr ((hmemK v).mpr ⟨hqv, hV₀lam _ (mem_subgroupOf.mp hv) hqv⟩)
  obtain ⟨ηX, hηc, hηadd, hηext⟩ :=
    exists_hom_extending π hπc hπo hπs hcen W hWc hWo hWZ ι hι
  refine ⟨fun x => ηX (mk x), hηc.comp QuotientGroup.continuous_mk, fun a b => ?_, fun a ha => ?_⟩
  · simp only [map_mul]; exact hηadd _ _
  · show ηX (mk a) = lam a
    rw [hηext _ ha]; exact hιmk a ha

end MzSl2
