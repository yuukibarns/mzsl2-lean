import Mathlib
import MzSl2.Dichotomy
import MzSl2.U801

/-!
# Fact 8de: from finite integral index to the trichotomy

If `N ≤ Γ` is infinite, commensurated, and `N ∩ SL₂(ℤ)` has finite index in `SL₂(ℤ)`, then `N`
is commensurable with `SL₂(ℤ)` or has finite index in `Γ`. With fact d751 (finite integral
index) this gives `MainTheorem`; `mainTheorem_of_d751` records that reduction.
-/

open Matrix Subgroup Topology Set

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

theorem Λ'_eq_comap : Λ.subgroupOf (Γ p) = (Kp p).comap (ιΓ p) := by
  ext g; rw [mem_comap]; exact (ιΓ_mem_Kp_iff g).symm

/-- `N` contains `u(m)` and `v(m)` for a common `m > 0`. -/
theorem exists_uv_mem {N : Subgroup (Γ p)} (hN : IsCommensurated N)
    (hinf : (N : Set (Γ p)).Infinite) :
    ∃ m : ℕ, 0 < m ∧
      uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ N ∧
      vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ N := by
  obtain ⟨a, ha, hua⟩ := exists_u_mem hN hinf
  obtain ⟨b, hb, hvb⟩ := exists_v_mem hN hinf
  refine ⟨a * b, Nat.mul_pos ha hb, ?_, ?_⟩
  · have := N.zpow_mem hua (b : ℤ)
    rw [uΓ_zpow] at this
    convert this using 2; push_cast; ring
  · have := N.zpow_mem hvb (a : ℤ)
    rw [vΓ_zpow] at this
    convert this using 2; push_cast; ring

/-- **Fact 8de.** -/
theorem trichotomy_of_finite_integral_index {N : Subgroup (Γ p)} (hN : IsCommensurated N)
    (hinf : (N : Set (Γ p)).Infinite) (hfi : N.relIndex (Λ.subgroupOf (Γ p)) ≠ 0) :
    Commensurable N (Λ.subgroupOf (Γ p)) ∨ N.index ≠ 0 := by
  obtain ⟨m, hm, hu, hv⟩ := exists_uv_mem hN hinf
  obtain ⟨R, hR⟩ := Kr_le_closure hm hu hv
  set J := (N.map (ιΓ p)).topologicalClosure
  have hJ : (J : Set (SLp p)) = _root_.closure (ιΓ p '' (N : Set (Γ p))) := by
    rw [Subgroup.topologicalClosure_coe]; rfl
  have hRJ : Kr p R ≤ J := fun x hx => by rw [← SetLike.mem_coe, hJ]; exact hR hx
  rcases compact_or_top hRJ with hc | htop
  · -- compact closure: `N` is commensurable with `SL₂(ℤ)`
    left
    refine ⟨hfi, ?_⟩
    rw [Λ'_eq_comap, relIndex_comap]
    have h1 : (Kp p).relIndex J ≠ 0 := relIndex_ne_zero_of_isOpen_of_isCompact isOpen_Kp hc
    exact relIndex_ne_zero_of_le_right' (Subgroup.le_topologicalClosure _) h1
  · -- dense: `Γ = SL₂(ℤ) · N`, so `N` has finite index
    right
    have hdec : ∀ γ : Γ p, ∃ l ∈ Λ.subgroupOf (Γ p), ∃ n ∈ N, γ = l * n := by
      intro γ
      have hmem : ιΓ p γ⁻¹ ∈ _root_.closure (ιΓ p '' (N : Set (Γ p))) := by
        rw [← hJ, htop]; trivial
      have hO : IsOpen {y : SLp p | (ιΓ p γ⁻¹)⁻¹ * y ∈ Kp p} :=
        isOpen_Kp.preimage (continuous_const.mul continuous_id)
      obtain ⟨_, hyO, n, hnN, rfl⟩ := mem_closure_iff.mp hmem _ hO
        (by show (ιΓ p γ⁻¹)⁻¹ * ιΓ p γ⁻¹ ∈ Kp p; rw [inv_mul_cancel]; exact (Kp p).one_mem)
      have hl : γ * n ∈ Λ.subgroupOf (Γ p) := by
        rw [← ιΓ_mem_Kp_iff]
        simpa [map_mul, map_inv] using hyO
      refine ⟨(γ * n), hl, n⁻¹, N.inv_mem hnN, by group⟩
    haveI : (N.subgroupOf (Λ.subgroupOf (Γ p))).FiniteIndex := ⟨hfi⟩
    let f : (Λ.subgroupOf (Γ p)) ⧸ N.subgroupOf (Λ.subgroupOf (Γ p)) → Γ p ⧸ N :=
      Quotient.map' (fun l => (l : Γ p)) (by
        intro a b hab
        rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab
        exact QuotientGroup.leftRel_apply.mpr (by simpa using hab))
    have hf : Function.Surjective f := by
      rintro ⟨γ⟩
      obtain ⟨l, hl, n, hn, rfl⟩ := hdec γ
      refine ⟨Quotient.mk'' ⟨l, hl⟩, Quotient.sound' ?_⟩
      rw [QuotientGroup.leftRel_apply]
      simpa using hn
    haveI : Finite (Γ p ⧸ N) := Finite.of_surjective f hf
    exact Subgroup.index_ne_zero_of_finite

/-- **Reduction of the main theorem to fact d751.** -/
theorem mainTheorem_of_d751
    (h751 : ∀ (p : ℕ) [Fact p.Prime] (N : Subgroup (Γ p)), IsCommensurated N →
      (N : Set (Γ p)).Infinite → N.relIndex (Λ.subgroupOf (Γ p)) ≠ 0) :
    MainTheorem := by
  intro p _ N hNΓ hcomm
  set N' := N.subgroupOf (Γ p)
  have hN' : IsCommensurated N' := isCommensurated_subgroupOf hNΓ hcomm
  by_cases hfin : (N : Set (SpecialLinearGroup (Fin 2) ℚ)).Finite
  · exact Or.inl hfin
  right
  have hinf : (N' : Set (Γ p)).Infinite := fun h => hfin ((finite_subgroupOf_iff hNΓ).mp h)
  rcases trichotomy_of_finite_integral_index hN' hinf (h751 p N' hN' hinf) with h | h
  · left
    exact ⟨by rw [← relIndex_subgroupOf (Λ_le_Γ p)]; exact h.1,
      by rw [← relIndex_subgroupOf hNΓ]; exact h.2⟩
  · right; exact h

end MzSl2
