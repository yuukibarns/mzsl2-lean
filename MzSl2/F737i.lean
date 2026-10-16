import Mathlib
import MzSl2.F737h
import MzSl2.F737d

/-!
# Fact 737, step 4g: no nonzero continuous homomorphism `H₀ → ℤ`

Let `H₀ ≤ Γ//L` be open, normal, of finite index, with `L` infinite and commensurated, and let
`η : H₀ → ℤ` be a continuous homomorphism. Then `η = 0`:

* `η` vanishes on the compact subgroup `U ∩ H₀` (its image is a finite subgroup of `ℤ`);
* `f = η ∘ ρ` on `Γ₁ = ρ⁻¹(H₀)` kills `L ∩ Γ₁`, so `ker f` contains the finitely many
  `Γ`-conjugates of the infinite group `L ∩ Γ₁`; their intersection is infinite and lies in the
  normal core of `ker f`, which has finite index by the normal subgroup theorem;
* so `f(Γ₁)` is a finite subgroup of `ℤ`, i.e. `0`; by density and continuity `η = 0`.
-/

open Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

/-- **737 (4g).** -/
theorem eta_eq_zero {L : Subgroup (Γ p)} (hLc : IsCommensurated L)
    (hLinf : (L : Set (Γ p)).Infinite) (H₀ : Subgroup (Hc L)) [hH₀n : H₀.Normal]
    (hH₀o : IsOpen (H₀ : Set (Hc L))) (hH₀fi : H₀.index ≠ 0) (η : H₀ → ℤ) (hηc : Continuous η)
    (hηadd : ∀ a b, η (a * b) = η a + η b) (a : H₀) : η a = 0 := by
  classical
  by_contra hne
  let ηh : H₀ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (η x)) (fun a b => by simp [hηadd])
  have hηpow : ∀ (x : H₀) (k : ℕ), η (x ^ k) = k * η x := by
    intro x k
    have := congrArg Multiplicative.toAdd (map_pow ηh x k)
    simpa [ηh] using this
  -- (b) `η` vanishes on `U ∩ H₀`
  have hH₀cl : IsClosed (H₀ : Set (Hc L)) := Subgroup.isClosed_of_isOpen _ hH₀o
  have hU : ∀ x : H₀, (x : Hc L) ∈ UH L → η x = 0 := by
    have hcpt : IsCompact (Subtype.val ⁻¹' (UH L : Set (Hc L)) : Set H₀) :=
      hH₀cl.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_UH L hLc)
    have hfin : (η '' (Subtype.val ⁻¹' (UH L : Set (Hc L)))).Finite :=
      (hcpt.image hηc).finite_of_discrete
    intro x hx
    by_contra hx0
    apply (Set.infinite_of_injective_forall_mem (α := ℕ) (f := fun k => (k : ℤ) * η x) ?_ ?_) hfin
    · intro k l hkl
      have := mul_right_cancel₀ hx0 hkl
      exact_mod_cast this
    · intro k
      refine ⟨x ^ k, ?_, hηpow x k⟩
      show ((x ^ k : H₀) : Hc L) ∈ UH L
      rw [Subgroup.coe_pow]; exact pow_mem hx k
  -- `f`
  let Γ₁ : Subgroup (Γ p) := H₀.comap (ρH L)
  haveI hΓ₁n : Γ₁.Normal := Subgroup.Normal.comap hH₀n _
  have hΓ₁fi : Γ₁.index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact relIndex_ne_zero_of_le_right' le_top (by rwa [relIndex_top_right])
  haveI : Γ₁.FiniteIndex := ⟨hΓ₁fi⟩
  let f : Γ p → ℤ := fun γ => if h : ρH L γ ∈ H₀ then η ⟨ρH L γ, h⟩ else 0
  have hf : ∀ γ (h : γ ∈ Γ₁), f γ = η ⟨ρH L γ, h⟩ := fun γ h => dif_pos h
  have hfadd : ∀ γ δ, γ ∈ Γ₁ → δ ∈ Γ₁ → f (γ * δ) = f γ + f δ := by
    intro γ δ hγ hδ
    rw [hf _ (Γ₁.mul_mem hγ hδ), hf _ hγ, hf _ hδ, ← hηadd]
    congr 1; ext; simp
  have hf1 : f 1 = 0 := by
    have := hfadd 1 1 Γ₁.one_mem Γ₁.one_mem; simp at this; exact this
  have hfinv : ∀ γ, γ ∈ Γ₁ → f γ⁻¹ = -f γ := by
    intro γ hγ
    have := hfadd γ⁻¹ γ (Γ₁.inv_mem hγ) hγ
    rw [inv_mul_cancel, hf1] at this; linarith
  have hfpow : ∀ γ, γ ∈ Γ₁ → ∀ k : ℕ, f (γ ^ k) = k * f γ := by
    intro γ hγ k
    induction k with
    | zero => simp [hf1]
    | succ k ih =>
      rw [pow_succ, hfadd _ _ (Γ₁.pow_mem hγ k) hγ, ih]; push_cast; ring
  -- (a) some `γ ∈ Γ₁` has `f γ ≠ 0`
  obtain ⟨γ0, hγ0, hfγ0⟩ : ∃ γ, γ ∈ Γ₁ ∧ f γ ≠ 0 := by
    have hS : IsOpen (Subtype.val '' (η ⁻¹' {η a}) : Set (Hc L)) :=
      hH₀o.isOpenMap_subtype_val _ ((isOpen_discrete _).preimage hηc)
    obtain ⟨γ, x, hx, hxγ⟩ := (denseRange_ρH L).exists_mem_open hS ⟨a, a, rfl, rfl⟩
    have hγ : γ ∈ Γ₁ := by show ρH L γ ∈ H₀; rw [← hxγ]; exact x.2
    refine ⟨γ, hγ, ?_⟩
    rw [hf _ hγ]
    have : (⟨ρH L γ, hγ⟩ : H₀) = x := Subtype.ext hxγ.symm
    rw [this, show η x = η a from hx]; exact hne
  -- the kernel of `f`
  let K : Subgroup (Γ p) :=
    { carrier := {γ | γ ∈ Γ₁ ∧ f γ = 0}
      one_mem' := ⟨Γ₁.one_mem, hf1⟩
      mul_mem' := fun {x y} hx hy => ⟨Γ₁.mul_mem hx.1 hy.1, by
        rw [hfadd _ _ hx.1 hy.1, hx.2, hy.2, add_zero]⟩
      inv_mem' := fun {x} hx => ⟨Γ₁.inv_mem hx.1, by rw [hfinv _ hx.1, hx.2, neg_zero]⟩ }
  have hKconj : ∀ g ∈ Γ₁, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    rintro g hg k ⟨hk1, hk2⟩
    refine ⟨Γ₁.mul_mem (Γ₁.mul_mem hg hk1) (Γ₁.inv_mem hg), ?_⟩
    rw [hfadd _ _ (Γ₁.mul_mem hg hk1) (Γ₁.inv_mem hg), hfadd _ _ hg hk1, hk2, hfinv _ hg]
    ring
  set M := L ⊓ Γ₁
  have hMK : M ≤ K := by
    rintro l ⟨hlL, hlΓ⟩
    refine ⟨hlΓ, ?_⟩
    rw [hf _ hlΓ]
    exact hU _ ((ρH_mem_UH_iff L l).mpr hlL)
  -- `M` is commensurated and infinite
  have hΓ₁c : IsCommensurated Γ₁ := by
    intro g
    have : ConjAct.toConjAct g • Γ₁ = Γ₁ := by
      ext x; rw [mem_conjAct_smul_iff]
      constructor
      · intro hx; simpa [mul_assoc] using hΓ₁n.conj_mem _ hx g
      · intro hx; simpa using hΓ₁n.conj_mem _ hx g⁻¹
    rw [this]
  have hMc : IsCommensurated M := hLc.inf hΓ₁c
  have hML : M.relIndex L ≠ 0 := by
    rw [inf_relIndex_left]
    exact relIndex_ne_zero_of_le_right' le_top (by rwa [relIndex_top_right])
  -- the finite intersection of conjugates
  let D : Subgroup (Γ p) :=
    ⨅ t : Γ p ⧸ Γ₁, ConjAct.toConjAct (Quotient.out t)⁻¹ • M
  have hDM : D.relIndex M ≠ 0 := relIndex_iInf_ne_zero fun t => (hMc _).1
  have hDinf : (D : Set (Γ p)).Infinite := by
    intro hDfin
    exact hLinf (finite_of_finite_of_relIndex (finite_of_finite_of_relIndex hDfin hDM) hML)
  have hDcore : D ≤ K.normalCore := by
    intro x hx b
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ₁ b
    set o := Quotient.out (QuotientGroup.mk b : Γ p ⧸ Γ₁)
    have hxo : o * x * o⁻¹ ∈ M := by
      have := (Subgroup.mem_iInf.mp hx) (QuotientGroup.mk b)
      rw [mem_conjAct_smul_iff] at this
      simpa using this
    have hg' : b * o⁻¹ ∈ Γ₁ := by
      rw [hh]
      have := hΓ₁n.conj_mem _ (Γ₁.inv_mem h.2) b
      simpa [mul_assoc] using this
    have := hKconj _ hg' _ (hMK hxo)
    simpa [mul_assoc] using this
  -- normal subgroup theorem
  have hcore : K.normalCore.index ≠ 0 :=
    (nst_Γ K.normalCore inferInstance).resolve_left fun hfin => hDinf (hfin.subset hDcore)
  have hpow := K.normalCore_le (Subgroup.pow_index_mem K.normalCore γ0)
  have h0 := hpow.2
  rw [hfpow _ hγ0] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact hcore (by exact_mod_cast h)
  · exact hfγ0 h

end MzSl2
