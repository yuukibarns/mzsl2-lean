import Mathlib
import MzSl2.Statement

/-!
# Concrete elements of `Γ = SL₂(ℤ[1/p])`

`uΓ a`, `vΓ a` (for `a ∈ ℤ[1/p]`), `dγ = diag(p, p⁻¹)`, `wγ`, as elements of the subgroup
`Γ p`, together with their matrices and the relations used in c627, e69, 801, d751.
-/

open Matrix Subgroup

namespace MzSl2

variable (p : ℕ) [hp : Fact p.Prime]

/-- The matrix of an element of `Γ`. -/
def mat (g : Γ p) : Matrix (Fin 2) (Fin 2) ℚ := ((g : SpecialLinearGroup (Fin 2) ℚ) : Matrix _ _ ℚ)

variable {p}

theorem mat_mul (g h : Γ p) : mat p (g * h) = mat p g * mat p h := rfl
theorem mat_one : mat p 1 = 1 := rfl
theorem mat_injective : Function.Injective (mat p) := by
  intro g h hgh
  exact Subtype.ext (Subtype.ext hgh)
theorem mat_inv (g : Γ p) : mat p g⁻¹ = adjugate (mat p g) := rfl

theorem mat_pow (g : Γ p) (n : ℕ) : mat p (g ^ n) = mat p g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, mat_mul, ih, pow_succ]

theorem mat_list_prod (l : List (Γ p)) : mat p l.prod = (l.map (mat p)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.prod_cons, mat_mul, ih, List.map_cons, List.prod_cons]

theorem R_one : (1 : ℚ) ∈ R p := (R p).one_mem
theorem R_zero : (0 : ℚ) ∈ R p := (R p).zero_mem
theorem R_p_inv : (p : ℚ)⁻¹ ∈ R p := ⟨1, 1, by simp⟩
theorem R_p : (p : ℚ) ∈ R p := ⟨p, 0, by simp⟩

/-- `u(a)` in `Γ`. -/
def uΓ (a : ℚ) (ha : a ∈ R p) : Γ p :=
  ⟨⟨u a, by simp [u, Matrix.det_fin_two_of]⟩, by
    intro i j; fin_cases i <;> fin_cases j <;> simp [u, ha, R_one, R_zero]⟩

/-- `v(a)` in `Γ`. -/
def vΓ (a : ℚ) (ha : a ∈ R p) : Γ p :=
  ⟨⟨v a, by simp [v, Matrix.det_fin_two_of]⟩, by
    intro i j; fin_cases i <;> fin_cases j <;> simp [v, ha, R_one, R_zero]⟩

variable (p) in
/-- `d = diag(p, p⁻¹)` in `Γ`. -/
def dγ : Γ p := ⟨dΓ p, dΓ_mem p⟩

variable (p) in
/-- `w = [[0,-1],[1,0]]` in `Γ`. -/
def wγ : Γ p :=
  ⟨⟨w, by simp [w, Matrix.det_fin_two_of]⟩, by
    intro i j; fin_cases i <;> fin_cases j <;> simp [w, R_one, R_zero, (R p).neg_mem]⟩

@[simp] theorem mat_uΓ (a : ℚ) (ha : a ∈ R p) : mat p (uΓ a ha) = u a := rfl
@[simp] theorem mat_vΓ (a : ℚ) (ha : a ∈ R p) : mat p (vΓ a ha) = v a := rfl
@[simp] theorem mat_dγ : mat p (dγ p) = dg (p : ℚ) := rfl
@[simp] theorem mat_wγ : mat p (wγ p) = w := rfl

theorem uΓ_mul (a b : ℚ) (ha : a ∈ R p) (hb : b ∈ R p) :
    uΓ a ha * uΓ b hb = uΓ (a + b) ((R p).add_mem ha hb) :=
  mat_injective (by rw [mat_mul]; simp [u_mul_u])

theorem vΓ_mul (a b : ℚ) (ha : a ∈ R p) (hb : b ∈ R p) :
    vΓ a ha * vΓ b hb = vΓ (a + b) ((R p).add_mem ha hb) :=
  mat_injective (by rw [mat_mul]; simp [v_mul_v])

theorem uΓ_zero : uΓ (0 : ℚ) R_zero = (1 : Γ p) := mat_injective (by simp [u_zero, mat_one])
theorem vΓ_zero : vΓ (0 : ℚ) R_zero = (1 : Γ p) := mat_injective (by simp [v_zero, mat_one])

theorem R_intCast_mul (j : ℤ) {a : ℚ} (ha : a ∈ R p) : (j : ℚ) * a ∈ R p :=
  (R p).mul_mem (intCast_mem (R p) j) ha

theorem uΓ_zpow (a : ℚ) (ha : a ∈ R p) (j : ℤ) :
    uΓ a ha ^ j = uΓ ((j : ℚ) * a) (R_intCast_mul j ha) := by
  have hn : ∀ n : ℕ, uΓ a ha ^ n = uΓ ((n : ℚ) * a) (by exact_mod_cast R_intCast_mul n ha) := by
    intro n
    exact mat_injective (by rw [mat_pow]; simp [u_pow])
  rcases j with n | n
  · simpa using hn n
  · rw [zpow_negSucc, hn]
    refine mat_injective ?_
    rw [mat_inv]
    simp [u, Matrix.adjugate_fin_two]
    push_cast; ring_nf

theorem vΓ_zpow (a : ℚ) (ha : a ∈ R p) (j : ℤ) :
    vΓ a ha ^ j = vΓ ((j : ℚ) * a) (R_intCast_mul j ha) := by
  have hn : ∀ n : ℕ, vΓ a ha ^ n = vΓ ((n : ℚ) * a) (by exact_mod_cast R_intCast_mul n ha) := by
    intro n
    exact mat_injective (by rw [mat_pow]; simp [v_pow])
  rcases j with n | n
  · simpa using hn n
  · rw [zpow_negSucc, hn]
    refine mat_injective ?_
    rw [mat_inv]
    simp [v, Matrix.adjugate_fin_two]
    push_cast; ring_nf

theorem mat_dγ_pow (r : ℕ) : mat p (dγ p ^ r) = dg ((p : ℚ) ^ r) := by
  rw [mat_pow, mat_dγ, dg_pow]

theorem mat_dγ_pow_inv (r : ℕ) : mat p (dγ p ^ r)⁻¹ = dg ((p : ℚ) ^ r)⁻¹ := by
  rw [mat_inv, mat_dγ_pow]
  simp [dg, Matrix.adjugate_fin_two]

/-- c627: `u(a) = d^{-r} u(1)^b d^r` with `b ∈ ℤ`, for every `a ∈ ℤ[1/p]` (for some `r`). -/
theorem uΓ_eq_conj (a : ℚ) (ha : a ∈ R p) :
    ∃ (r : ℕ) (b : ℤ), uΓ a ha = (dγ p ^ r)⁻¹ * uΓ 1 R_one ^ b * dγ p ^ r := by
  obtain ⟨m, k, hmk⟩ := ha
  refine ⟨k, m * p ^ k, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mat_injective
  simp only [mat_mul, mat_dγ_pow_inv, uΓ_zpow, mat_uΓ, mat_dγ_pow]
  have := dg_conj_u (inv_ne_zero (pow_ne_zero k hp0)) (((m * p ^ k : ℤ) : ℚ) * 1)
  rw [inv_inv] at this
  rw [this]; show u a = _; rw [hmk]; congr 1; push_cast; field_simp

/-- c627: `v(a) = d^{r} v(1)^b d^{-r}` with `b ∈ ℤ`. -/
theorem vΓ_eq_conj (a : ℚ) (ha : a ∈ R p) :
    ∃ (r : ℕ) (b : ℤ), vΓ a ha = dγ p ^ r * vΓ 1 R_one ^ b * (dγ p ^ r)⁻¹ := by
  obtain ⟨m, k, hmk⟩ := ha
  refine ⟨k, m * p ^ k, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mat_injective
  simp only [mat_mul, mat_dγ_pow_inv, vΓ_zpow, mat_vΓ, mat_dγ_pow]
  rw [dg_conj_v (pow_ne_zero k hp0)]; show v a = _; rw [hmk]
  congr 1; push_cast; field_simp

theorem R_div_pow {a : ℚ} (ha : a ∈ R p) (r : ℕ) : a / (p : ℚ) ^ r ∈ R p := by
  rw [div_eq_mul_inv, ← inv_pow]; exact (R p).mul_mem ha ((R p).pow_mem R_p_inv r)

theorem uΓ_div_pow (a : ℚ) (ha : a ∈ R p) (r : ℕ) :
    uΓ (a / (p : ℚ) ^ r) (R_div_pow ha r) ^ (p ^ r) = uΓ a ha := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine mat_injective ?_
  rw [mat_pow, mat_uΓ, u_pow, mat_uΓ]; congr 1; push_cast; field_simp

/-- `u(1) = u(p^{-r})^{p^r}`: upper unipotents are infinitely `p`-divisible. -/
theorem uΓ_divisible (a : ℚ) (ha : a ∈ R p) (r : ℕ) :
    ∃ k : Γ p, k ^ (p ^ r) = uΓ a ha := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hk : a / (p : ℚ) ^ r ∈ R p := by
    rw [div_eq_mul_inv, ← inv_pow]; exact (R p).mul_mem ha ((R p).pow_mem R_p_inv r)
  refine ⟨uΓ _ hk, mat_injective ?_⟩
  rw [mat_pow, mat_uΓ, u_pow, mat_uΓ]; congr 1; push_cast; field_simp

theorem vΓ_divisible (a : ℚ) (ha : a ∈ R p) (r : ℕ) :
    ∃ k : Γ p, k ^ (p ^ r) = vΓ a ha := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hk : a / (p : ℚ) ^ r ∈ R p := by
    rw [div_eq_mul_inv, ← inv_pow]; exact (R p).mul_mem ha ((R p).pow_mem R_p_inv r)
  refine ⟨vΓ _ hk, mat_injective ?_⟩
  rw [mat_pow, mat_vΓ, v_pow, mat_vΓ]; congr 1; push_cast; field_simp

/-- `w d w⁻¹ = d⁻¹`. -/
theorem wγ_conj_dγ : wγ p * dγ p * (wγ p)⁻¹ = (dγ p)⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mat_injective
  rw [mat_mul, mat_mul, mat_inv, mat_inv]
  simp only [mat_wγ, mat_dγ]
  simp [w, dg, Matrix.adjugate_fin_two]

end MzSl2
