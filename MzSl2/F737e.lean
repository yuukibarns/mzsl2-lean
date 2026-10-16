import Mathlib
import MzSl2.PhiMap

/-!
# Fact 737, step 4c: `G₀ = Γ//Λ ≅ PSL₂(ℚ_p)` is perfect, has no finite quotients, and has
`H²_c(G₀, ℝ) = 0`

* every homomorphism from `SL₂(ℚ_p)` (hence from `G₀`) to a commutative group is trivial:
  root elements are commutators `[diag(p,p⁻¹), u(·)]`;
* every finite-index normal subgroup of `SL₂(ℚ_p)` (hence of `G₀`) is everything: root groups are
  divisible;
* continuous real 2-cocycles on `G₀` are coboundaries of continuous cochains: pull back along `Φ`,
  apply Casselman–Wigner, and descend (the cochain is constant on `{±1}`-cosets, and `Φ` is a
  quotient map).
-/

open Matrix Topology Set Subgroup

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

theorem dP_conj_uP {a : ℚ_[p]} (ha : a ≠ 0) (s : ℚ_[p]) :
    dP a ha * uP s * (dP a ha)⁻¹ * (uP s)⁻¹ = uP ((a ^ 2 - 1) * s) := by
  apply matP_injective
  simp only [matP_mul, matP_inv, matP_dP, matP_uP]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dg, u, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem dP_conj_vP {a : ℚ_[p]} (ha : a ≠ 0) (s : ℚ_[p]) :
    dP a ha * vP s * (dP a ha)⁻¹ * (vP s)⁻¹ = vP ((a⁻¹ ^ 2 - 1) * s) := by
  apply matP_injective
  simp only [matP_mul, matP_inv, matP_dP, matP_vP]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dg, v, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- Homomorphisms from `SL₂(ℚ_p)` to commutative groups are trivial. -/
theorem SLp_hom_comm_trivial {A : Type*} [CommGroup A] (χ : SLp p →* A) : χ = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp2 : (p : ℚ_[p]) ^ 2 - 1 ≠ 0 := by
    have : (p : ℚ_[p]) ^ 2 ≠ 1 := by
      intro h
      have : (p ^ 2 : ℕ) = 1 := by exact_mod_cast h
      have := hp.out.one_lt; nlinarith
    exact sub_ne_zero.mpr this
  have hp2' : (p : ℚ_[p])⁻¹ ^ 2 - 1 ≠ 0 := by
    have : (p : ℚ_[p])⁻¹ ^ 2 ≠ 1 := by
      intro h
      apply hp2
      have : (p : ℚ_[p]) ^ 2 = 1 := by
        rw [inv_pow] at h; exact (inv_eq_one.mp h)
      rw [this]; ring
    exact sub_ne_zero.mpr this
  have hcomm : ∀ x y : SLp p, χ (x * y * x⁻¹ * y⁻¹) = 1 := by
    intro x y; simp [map_mul, map_inv, mul_comm (χ x), mul_assoc]
  have hu : ∀ t, uP t ∈ χ.ker := by
    intro t
    have := hcomm (dP (p : ℚ_[p]) hp0) (uP (t / ((p : ℚ_[p]) ^ 2 - 1)))
    rw [dP_conj_uP] at this
    rw [MonoidHom.mem_ker]; convert this using 3; field_simp
  have hv : ∀ t, vP t ∈ χ.ker := by
    intro t
    have := hcomm (dP (p : ℚ_[p]) hp0) (vP (t / ((p : ℚ_[p])⁻¹ ^ 2 - 1)))
    rw [dP_conj_vP] at this
    have h1 : (1 : ℚ_[p]) - (p : ℚ_[p]) ^ 2 ≠ 0 := by
      intro h; apply hp2; linear_combination -h
    rw [MonoidHom.mem_ker]; convert this using 3; field_simp
  have htop := eq_top_of_roots hu hv
  ext x
  have : x ∈ χ.ker := by rw [htop]; trivial
  simpa using this

theorem uP_pow (t : ℚ_[p]) (n : ℕ) : uP t ^ n = uP ((n : ℚ_[p]) * t) := by
  apply matP_injective
  induction n with
  | zero => simp [matP_one, u_zero]
  | succ n ih =>
    rw [pow_succ, matP_mul, ih]; simp only [matP_uP, u_mul_u]; push_cast; ring_nf

theorem vP_pow (t : ℚ_[p]) (n : ℕ) : vP t ^ n = vP ((n : ℚ_[p]) * t) := by
  apply matP_injective
  induction n with
  | zero => simp [matP_one, v_zero]
  | succ n ih =>
    rw [pow_succ, matP_mul, ih]; simp only [matP_vP, v_mul_v]; push_cast; ring_nf

/-- Finite-index normal subgroups of `SL₂(ℚ_p)` are everything. -/
theorem SLp_normal_finiteIndex_eq_top (M : Subgroup (SLp p)) [M.Normal] (hM : M.index ≠ 0) :
    M = ⊤ := by
  have hn : (M.index : ℚ_[p]) ≠ 0 := by exact_mod_cast hM
  apply eq_top_of_roots
  · intro t
    have := Subgroup.pow_index_mem M (uP (t / M.index))
    rwa [uP_pow, mul_div_cancel₀ _ hn] at this
  · intro t
    have := Subgroup.pow_index_mem M (vP (t / M.index))
    rwa [vP_pow, mul_div_cancel₀ _ hn] at this

/-- `G₀` is perfect. -/
theorem G0_hom_comm_trivial {A : Type*} [CommGroup A] (χ : Hc (Λp p) →* A) : χ = 1 := by
  have h := SLp_hom_comm_trivial (χ.comp Φ)
  ext y
  obtain ⟨x, rfl⟩ := Φ_surjective y
  have := congrArg (fun f => f x) h
  simpa using this

/-- `G₀` has no proper finite-index normal subgroups. -/
theorem G0_normal_finiteIndex_eq_top (M : Subgroup (Hc (Λp p))) [M.Normal] (hM : M.index ≠ 0) :
    M = ⊤ := by
  haveI : (M.comap Φ).Normal := Subgroup.Normal.comap inferInstance _
  have h1 : (M.comap Φ).index ≠ 0 := by
    rw [Subgroup.index_comap_of_surjective _ Φ_surjective]; exact hM
  have h2 := SLp_normal_finiteIndex_eq_top (M.comap Φ) h1
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := Φ_surjective y
  have : x ∈ M.comap Φ := by rw [h2]; trivial
  exact this

/-- **Casselman–Wigner for `G₀`.** -/
theorem casselman_wigner_G0 (f : Hc (Λp p) × Hc (Λp p) → ℝ) (hf : Continuous f)
    (hcoc : ∀ x y z, f (y, z) - f (x * y, z) + f (x, y * z) - f (x, y) = 0) :
    ∃ b : Hc (Λp p) → ℝ, Continuous b ∧ ∀ x y, f (x, y) = b x + b y - b (x * y) := by
  set F : SLp p × SLp p → ℝ := fun xy => f (Φ xy.1, Φ xy.2)
  have hF : Continuous F := hf.comp ((continuous_Φ.comp continuous_fst).prodMk
    (continuous_Φ.comp continuous_snd))
  obtain ⟨b0, hb0, hb0e⟩ := casselman_wigner_real p F hF (fun x y z => by
    simp only [F, map_mul]; exact hcoc _ _ _)
  -- `b0` is constant on cosets of `ker Φ = {±1}`
  set κ := f (1, 1)
  have hconst : ∀ x : Hc (Λp p), f (x, 1) = κ := by
    intro x; have := hcoc x 1 1; simp at this; linarith
  have hb01 : b0 1 = κ := by
    have := hb0e 1 1; simp only [F, map_one, mul_one] at this; linarith
  have hker : ∀ x z : SLp p, Φ z = 1 → b0 (x * z) = b0 x := by
    intro x z hz
    have hz2 : z * z = 1 := by
      rcases (Φ_eq_one_iff z).mp hz with h | h
      · have : z = 1 := matP_injective (by rw [h, matP_one]); rw [this, mul_one]
      · apply matP_injective; rw [matP_mul, h, matP_one]; simp
    have e1 := hb0e x z
    simp only [F, hz, hconst] at e1
    have e2 := hb0e z z
    simp only [F, hz, map_mul, mul_one, hconst, hz2, hb01] at e2
    have hbz : b0 z = κ := by linarith
    linarith
  -- descend along the open quotient map `Φ`
  have hq : IsQuotientMap (Φ (p := p)) :=
    Φ_isOpenMap.isQuotientMap continuous_Φ Φ_surjective
  have hwd : ∀ x y : SLp p, Φ x = Φ y → b0 x = b0 y := by
    intro x y hxy
    have hz : Φ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have := hker x (x⁻¹ * y) hz
    rw [mul_inv_cancel_left] at this; exact this.symm
  let b : Hc (Λp p) → ℝ := fun y => b0 (Function.surjInv Φ_surjective y)
  have hbΦ : ∀ x, b (Φ x) = b0 x := fun x =>
    hwd _ _ (Function.surjInv_eq Φ_surjective (Φ x))
  refine ⟨b, ?_, ?_⟩
  · rw [hq.continuous_iff]
    have : b ∘ Φ = b0 := funext hbΦ
    rw [this]; exact hb0
  · intro y1 y2
    obtain ⟨x1, rfl⟩ := Φ_surjective y1
    obtain ⟨x2, rfl⟩ := Φ_surjective y2
    rw [← map_mul, hbΦ, hbΦ, hbΦ]
    exact hb0e x1 x2

end MzSl2
