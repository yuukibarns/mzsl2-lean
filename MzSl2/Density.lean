import Mathlib
import MzSl2.PadicBasics

/-!
# Density of `Γ = SL₂(ℤ[1/p])` in `SL₂(ℚ_p)`

* `ℤ[1/p]` is dense in `ℚ_p`;
* every `y ∈ SL₂(ℚ_p)` with `y₁₀ ≠ 0` is `u(a) v(c) u(b)`;
* `ι(Γ)` is dense in `SL₂(ℚ_p)`;
* root groups generate: a subgroup of `SL₂(ℚ_p)` containing all `u(t)`, `v(t)` is everything.
-/

open Matrix Subgroup Topology Set Metric

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

/-- `ℤ[1/p]` is dense in `ℚ_p`. -/
theorem R_dense (q : ℚ_[p]) {ε : ℝ} (hε : 0 < ε) : ∃ x ∈ R p, ‖q - (x : ℚ_[p])‖ < ε := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  -- choose `n` with `‖q p^n‖ ≤ 1`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖q‖ ≤ (p : ℝ) ^ n := pow_unbounded_of_one_lt _ hp1 |>.imp
    fun _ h => h.le
  have hz : ‖q * (p : ℚ_[p]) ^ n‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, _root_.zpow_neg, zpow_natCast]
    rw [mul_inv_le_iff₀ (by positivity)]; simpa using hn
  -- approximate `q p^n` by an integer
  have hd := (PadicInt.denseRange_intCast (p := p))
  have hεn : 0 < ε * (p : ℝ) ^ (-(n : ℤ)) := by positivity
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hd ⟨q * (p : ℚ_[p]) ^ n, hz⟩ _ hεn
  refine ⟨(k : ℚ) / (p : ℚ) ^ n, ⟨k, n, rfl⟩, ?_⟩
  have hk' : ‖q * (p : ℚ_[p]) ^ n - (k : ℚ_[p])‖ < ε * (p : ℝ) ^ (-(n : ℤ)) := by
    have h1 : dist (q * (p : ℚ_[p]) ^ n) ((k : ℤ_[p]) : ℚ_[p]) <
        ε * (p : ℝ) ^ (-(n : ℤ)) := hk
    rw [dist_eq_norm] at h1
    simpa using h1
  have e : q - (((k : ℚ) / (p : ℚ) ^ n : ℚ) : ℚ_[p]) =
      (q * (p : ℚ_[p]) ^ n - (k : ℚ_[p])) / (p : ℚ_[p]) ^ n := by
    push_cast; field_simp
  rw [e, norm_div, Padic.norm_p_pow, div_lt_iff₀ (by positivity)]
  exact hk'

/-- Bruhat-type factorisation `y = u(a) v(c) u(b)` when `y₁₀ ≠ 0`. -/
theorem eq_uvu (y : SLp p) (h : matP p y 1 0 ≠ 0) :
    y = uP ((matP p y 0 0 - 1) / matP p y 1 0) * vP (matP p y 1 0) *
      uP ((matP p y 1 1 - 1) / matP p y 1 0) := by
  apply matP_injective
  have hdet : matP p y 0 0 * matP p y 1 1 - matP p y 0 1 * matP p y 1 0 = 1 := by
    have := y.2; rw [Matrix.det_fin_two] at this; exact this
  simp only [matP_mul, matP_uP, matP_vP]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [u, v, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination -hdet | linear_combination hdet

/-- A subgroup containing all root group elements is everything. -/
theorem eq_top_of_roots {J : Subgroup (SLp p)} (hu : ∀ t, uP t ∈ J) (hv : ∀ t, vP t ∈ J) :
    J = ⊤ := by
  rw [eq_top_iff]
  intro y _
  by_cases h : matP p y 1 0 = 0
  · -- `y v(1)` has nonzero lower-left entry `y₁₁`
    have hdet : matP p y 0 0 * matP p y 1 1 - matP p y 0 1 * matP p y 1 0 = 1 := by
      have := y.2; rw [Matrix.det_fin_two] at this; exact this
    have h11 : matP p y 1 1 ≠ 0 := by intro h'; rw [h, h'] at hdet; simp at hdet
    set z := y * vP 1
    have hz : matP p z 1 0 ≠ 0 := by
      simp only [z, matP_mul, matP_vP]
      simp [v, Matrix.mul_apply, Fin.sum_univ_two, h, h11]
    have hzJ : z ∈ J := by rw [eq_uvu z hz]; exact J.mul_mem (J.mul_mem (hu _) (hv _)) (hu _)
    have : y = z * vP (-1) := by
      apply matP_injective
      simp only [z, matP_mul, matP_vP, mul_assoc, v_mul_v]; norm_num [v_zero]
    rw [this]; exact J.mul_mem hzJ (hv _)
  · rw [eq_uvu y h]; exact J.mul_mem (J.mul_mem (hu _) (hv _)) (hu _)

/-- `ι(Γ)` is dense in `SL₂(ℚ_p)`. -/
theorem denseRange_ιΓ : DenseRange (ιΓ p) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro O hO ⟨y, hyO⟩
  -- move to a point with nonzero lower-left entry
  obtain ⟨y', hy'O, hy'⟩ : ∃ y' ∈ O, matP p y' 1 0 ≠ 0 := by
    by_cases h : matP p y 1 0 = 0
    · have hdet : matP p y 0 0 * matP p y 1 1 - matP p y 0 1 * matP p y 1 0 = 1 := by
        have := y.2; rw [Matrix.det_fin_two] at this; exact this
      have h11 : matP p y 1 1 ≠ 0 := by intro h'; rw [h, h'] at hdet; simp at hdet
      have hc : Continuous fun t : ℚ_[p] => y * vP t := continuous_const.mul continuous_vP
      have hopen := hO.preimage hc
      have h0 : (0 : ℚ_[p]) ∈ (fun t : ℚ_[p] => y * vP t) ⁻¹' O := by
        show y * vP 0 ∈ O
        have : vP (0 : ℚ_[p]) = 1 := matP_injective (by simp [v_zero, matP_one])
        rw [this, mul_one]; exact hyO
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
      -- a small nonzero `t`
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(p : ℚ_[p]) ^ n‖ < δ := by
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ
          (show ‖(p : ℚ_[p])‖ < 1 by
            rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
        exact ⟨n, by rw [norm_pow]; exact hn⟩
      refine ⟨y * vP ((p : ℚ_[p]) ^ n), hball (by simpa using hn), ?_⟩
      simp only [matP_mul, matP_vP]
      simp [v, Matrix.mul_apply, Fin.sum_univ_two, h, h11,
        pow_ne_zero n (show (p : ℚ_[p]) ≠ 0 by exact_mod_cast hp.out.ne_zero)]
    · exact ⟨y, hyO, h⟩
  -- the map `(a, c, b) ↦ u(a) v(c) u(b)` is continuous
  set F : ℚ_[p] × ℚ_[p] × ℚ_[p] → SLp p := fun x => uP x.1 * vP x.2.1 * uP x.2.2
  have hF : Continuous F := by
    simp only [F]
    exact ((continuous_uP.comp continuous_fst).mul (continuous_vP.comp
      (continuous_fst.comp continuous_snd))).mul (continuous_uP.comp
        (continuous_snd.comp continuous_snd))
  set x0 : ℚ_[p] × ℚ_[p] × ℚ_[p] := ((matP p y' 0 0 - 1) / matP p y' 1 0, matP p y' 1 0,
    (matP p y' 1 1 - 1) / matP p y' 1 0)
  have hx0 : F x0 ∈ O := by
    have := eq_uvu y' hy'; simp only [F, x0]; rw [← this]; exact hy'O
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hF) x0 hx0
  obtain ⟨a, ha, ha'⟩ := R_dense x0.1 hδ
  obtain ⟨c, hc, hc'⟩ := R_dense x0.2.1 hδ
  obtain ⟨b, hb, hb'⟩ := R_dense x0.2.2 hδ
  have hmem : ((a : ℚ_[p]), (c : ℚ_[p]), (b : ℚ_[p])) ∈ ball x0 δ := by
    rw [mem_ball, Prod.dist_eq, Prod.dist_eq]
    simp only [dist_eq_norm]
    refine max_lt ?_ (max_lt ?_ ?_)
    · rw [norm_sub_rev]; exact ha'
    · rw [norm_sub_rev]; exact hc'
    · rw [norm_sub_rev]; exact hb'
  refine ⟨F ((a : ℚ_[p]), (c : ℚ_[p]), (b : ℚ_[p])), hball hmem,
    uΓ a ha * vΓ c hc * uΓ b hb, ?_⟩
  simp only [F, map_mul, ιΓ_uΓ, ιΓ_vΓ]

end MzSl2
