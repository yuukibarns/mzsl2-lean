import Mathlib
import MzSl2.PadicBasics

/-!
# Open closures from unipotent elements (replaces Rapinchuk's Lemma 2.7)

If `L ≤ Γ` contains `u(m)` and `v(m)` for some integer `m > 0`, then the closure of `ι(L)` in
`SL₂(ℚ_p)` contains a congruence subgroup `K(R)`, hence is open.

Proof: with `c = p^a` the `p`-part of `m`, the closure contains `u(t)` and `v(t)` for all
`‖t‖ ≤ ‖c‖` (ℤ is dense in ℤ_p). Every `x ∈ K(3a)` factors as `v(γ/α) diag(α,α⁻¹) u(β/α)`, and
`diag(α,α⁻¹) = u((α-1)/c²) v(c²) u((α⁻¹-1)/c²) v(-αc²)` (`key_801`); all parameters have norm
`≤ ‖c‖`.
-/

open Matrix Subgroup Topology Set Metric

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

/-- Iwahori factorisation of a matrix with invertible upper-left entry. -/
theorem iwahori_identity {K : Type*} [Field K] {a b c d : K} (ha : a ≠ 0) (h : a * d - b * c = 1) :
    !![a, b; c, d] = v (c / a) * dg a * u (b / a) := by
  obtain rfl : d = (1 + b * c) / a := by rw [eq_div_iff ha]; linear_combination h
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [u, v, dg, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Elements of `ℚ_p` of norm `≤ 1` are limits of integers. -/
theorem mem_closure_int {s : ℚ_[p]} (hs : ‖s‖ ≤ 1) :
    s ∈ _root_.closure (Set.range fun k : ℤ => (k : ℚ_[p])) := by
  have hd := (PadicInt.denseRange_intCast (p := p)).closure_range
  have hmem : (⟨s, hs⟩ : ℤ_[p]) ∈ _root_.closure (Set.range (Int.cast : ℤ → ℤ_[p])) := by
    rw [hd]; trivial
  have hc : Continuous (fun z : ℤ_[p] => (z : ℚ_[p])) := continuous_subtype_val
  have := map_mem_closure hc hmem (t := Set.range fun k : ℤ => (k : ℚ_[p]))
    (by rintro _ ⟨k, rfl⟩; exact ⟨k, by simp⟩)
  simpa using this

theorem uP_mem_closure {L : Subgroup (Γ p)} {m : ℕ}
    (hu : uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    {t : ℚ_[p]} (ht : ‖t‖ ≤ ‖(m : ℚ_[p])‖) (hm : (m : ℚ_[p]) ≠ 0) :
    uP t ∈ _root_.closure (ιΓ p '' (L : Set (Γ p))) := by
  set s := t / (m : ℚ_[p])
  have hs : ‖s‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ ht (norm_nonneg _)
  have hcl := mem_closure_int hs
  have hg : Continuous fun x : ℚ_[p] => uP ((m : ℚ_[p]) * x) :=
    continuous_uP.comp (continuous_mul_left _)
  have := map_mem_closure hg hcl (t := ιΓ p '' (L : Set (Γ p))) (by
    rintro _ ⟨k, rfl⟩
    refine ⟨uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ^ k,
      L.zpow_mem hu k, ?_⟩
    rw [uΓ_zpow, ιΓ_uΓ]; congr 1; push_cast; ring)
  have e : (m : ℚ_[p]) * s = t := by simp only [s]; field_simp
  rwa [e] at this

theorem vP_mem_closure {L : Subgroup (Γ p)} {m : ℕ}
    (hv : vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    {t : ℚ_[p]} (ht : ‖t‖ ≤ ‖(m : ℚ_[p])‖) (hm : (m : ℚ_[p]) ≠ 0) :
    vP t ∈ _root_.closure (ιΓ p '' (L : Set (Γ p))) := by
  set s := t / (m : ℚ_[p])
  have hs : ‖s‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ ht (norm_nonneg _)
  have hcl := mem_closure_int hs
  have hg : Continuous fun x : ℚ_[p] => vP ((m : ℚ_[p]) * x) :=
    continuous_vP.comp (continuous_mul_left _)
  have := map_mem_closure hg hcl (t := ιΓ p '' (L : Set (Γ p))) (by
    rintro _ ⟨k, rfl⟩
    refine ⟨vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ^ k,
      L.zpow_mem hv k, ?_⟩
    rw [vΓ_zpow, ιΓ_vΓ]; congr 1; push_cast; ring)
  have e : (m : ℚ_[p]) * s = t := by simp only [s]; field_simp
  rwa [e] at this

/-- **Open closure.** If `L` contains `u(m)` and `v(m)` (`m > 0`), the closure of `ι(L)`
contains some `K(R)`. -/
theorem Kr_le_closure {L : Subgroup (Γ p)} {m : ℕ} (hm : 0 < m)
    (hu : uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    (hv : vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L) :
    ∃ R, (Kr p R : Set (SLp p)) ⊆ _root_.closure (ιΓ p '' (L : Set (Γ p))) := by
  obtain ⟨a, m', hnd, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.out.one_lt.ne'
  set c : ℚ_[p] := (p : ℚ_[p]) ^ a
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hc0 : c ≠ 0 := pow_ne_zero _ hp0
  have hm0 : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm.ne'
  have hcm : ‖(m : ℚ_[p])‖ = ‖c‖ := by
    have h1 : ‖(m' : ℚ_[p])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd)
    rw [hfac]; push_cast; rw [norm_mul, h1, mul_one]
  have hc1 : ‖c‖ ≤ 1 := by
    rw [norm_pow, Padic.norm_p]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le))
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  -- the closure is a subgroup
  set C := (L.map (ιΓ p)).topologicalClosure
  have hC : (C : Set (SLp p)) = _root_.closure (ιΓ p '' (L : Set (Γ p))) := by
    rw [Subgroup.topologicalClosure_coe]; rfl
  have huC : ∀ t : ℚ_[p], ‖t‖ ≤ ‖c‖ → uP t ∈ C := fun t ht => by
    rw [← SetLike.mem_coe, hC]; exact uP_mem_closure hu (hcm ▸ ht) hm0
  have hvC : ∀ t : ℚ_[p], ‖t‖ ≤ ‖c‖ → vP t ∈ C := fun t ht => by
    rw [← SetLike.mem_coe, hC]; exact vP_mem_closure hv (hcm ▸ ht) hm0
  refine ⟨3 * a + 1, ?_⟩
  rw [← hC]
  intro x hx
  set ε : ℝ := ‖(p : ℚ_[p]) ^ (3 * a + 1)‖
  have hp1 : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hεc : ε ≤ ‖c‖ ^ 3 := by
    simp only [ε, c, norm_pow]
    rw [pow_succ, ← pow_mul, mul_comm a 3]
    exact mul_le_of_le_one_right (by positivity) hp1.le
  have hε1 : ε < 1 := by
    simp only [ε, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hp1 (by omega)
  have hx' : ∀ i j, ‖matP p x i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ ε := by
    intro i j
    have := hx i j
    rwa [show ((3 * a + 1 : ℕ) : ℤ) = ((3 * a + 1 : ℕ) : ℤ) from rfl, ← Padic.norm_p_pow] at this
  set α := matP p x 0 0
  set β := matP p x 0 1
  set γ := matP p x 1 0
  set δ := matP p x 1 1
  have hdet : α * δ - β * γ = 1 := by
    have := x.2; rw [Matrix.det_fin_two] at this; exact this
  have hc3 : ‖c‖ ^ 3 ≤ ‖c‖ := by
    calc ‖c‖ ^ 3 = ‖c‖ * ‖c‖ ^ 2 := by ring
      _ ≤ ‖c‖ * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) hc1
      _ = ‖c‖ := mul_one _
  have hα1 : ‖α - 1‖ ≤ ε := by simpa using hx' 0 0
  have hβ : ‖β‖ ≤ ε := by simpa using hx' 0 1
  have hγ : ‖γ‖ ≤ ε := by simpa using hx' 1 0
  -- `α` is a unit
  have hαn : ‖α‖ = 1 := by
    apply le_antisymm
    · have e : α = (α - 1) + 1 := by ring
      rw [e]; exact norm_add_le_of (hα1.trans hε1.le) (by simp)
    · have e : (1 : ℚ_[p]) = -(α - 1) + α := by ring
      have h := Padic.nonarchimedean (-(α - 1)) α
      rw [← e, norm_one, norm_neg] at h
      rcases le_max_iff.mp h with h' | h'
      · linarith [hα1.trans_lt hε1]
      · exact h'
  have hα0 : α ≠ 0 := by intro h; rw [h, norm_zero] at hαn; exact zero_ne_one hαn
  have hc2 : ‖c ^ 2‖ ≤ ‖c‖ := by
    rw [norm_pow]; calc ‖c‖ ^ 2 = ‖c‖ * ‖c‖ := sq _
      _ ≤ ‖c‖ * 1 := by gcongr
      _ = ‖c‖ := mul_one _
  have hdiv : ∀ y : ℚ_[p], ‖y‖ ≤ ‖c‖ ^ 3 → ‖y / c ^ 2‖ ≤ ‖c‖ := by
    intro y hy
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    calc ‖y‖ ≤ ‖c‖ ^ 3 := hy
      _ = ‖c‖ * ‖c‖ ^ 2 := by ring
  -- the factorisation
  have hfac : x = vP (γ / α) * (uP ((α - 1) / c ^ 2) * vP (c ^ 2) * uP ((α⁻¹ - 1) / c ^ 2) *
      vP (-α * c ^ 2)) * uP (β / α) := by
    apply matP_injective
    simp only [matP_mul, matP_uP, matP_vP]
    rw [key_801 hc0 hα0]
    have e : matP p x = !![α, β; γ, δ] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [e]
    exact iwahori_identity hα0 hdet
  rw [hfac]
  refine C.mul_mem (C.mul_mem (hvC _ ?_) (C.mul_mem (C.mul_mem (C.mul_mem (huC _ ?_) (hvC _ hc2))
    (huC _ ?_)) (hvC _ ?_))) (huC _ ?_)
  · rw [norm_div, hαn, div_one]; exact (hγ.trans hεc).trans hc3
  · exact hdiv _ (hα1.trans hεc)
  · apply hdiv
    have e : α⁻¹ - 1 = -(α - 1) / α := by field_simp; ring
    rw [e, norm_div, norm_neg, hαn, div_one]; exact hα1.trans hεc
  · rw [norm_mul, norm_neg, hαn, one_mul]; exact hc2
  · rw [norm_div, hαn, div_one]; exact (hβ.trans hεc).trans hc3

end MzSl2
