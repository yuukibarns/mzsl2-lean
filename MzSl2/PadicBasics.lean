import Mathlib
import MzSl2.GammaElems

/-!
# `SL₂(ℚ_p)`, `SL₂(ℤ_p)` and the embedding of `Γ = SL₂(ℤ[1/p])`

* `ιΓ : Γ → SL₂(ℚ_p)` (injective homomorphism);
* `Kp = SL₂(ℤ_p)` (entries of norm `≤ 1`) is a compact open subgroup;
* `Kr r` (entries `≡ δ_ij` modulo `p^r`) are open subgroups of `Kp`;
* `Γ ∩ SL₂(ℤ_p) = SL₂(ℤ)`;
* root group elements `uP t, vP t` depend continuously on `t ∈ ℚ_p`.
-/

open Matrix Subgroup Topology Set Metric

namespace MzSl2

variable (p : ℕ) [hp : Fact p.Prime]

/-- `SL₂(ℚ_p)`. -/
abbrev SLp := SpecialLinearGroup (Fin 2) ℚ_[p]

/-- The matrix of an element of `SL₂(ℚ_p)`. -/
abbrev matP (A : SLp p) : Matrix (Fin 2) (Fin 2) ℚ_[p] := (A : Matrix (Fin 2) (Fin 2) ℚ_[p])

/-- The embedding `SL₂(ℚ) → SL₂(ℚ_p)`. -/
noncomputable def ι : SpecialLinearGroup (Fin 2) ℚ →* SLp p :=
  SpecialLinearGroup.map (Rat.castHom ℚ_[p])

/-- The embedding `Γ → SL₂(ℚ_p)`. -/
noncomputable def ιΓ : Γ p →* SLp p := (ι p).comp (Γ p).subtype

variable {p}

@[simp] theorem matP_ιΓ (g : Γ p) (i j : Fin 2) :
    matP p (ιΓ p g) i j = ((mat p g i j : ℚ) : ℚ_[p]) := rfl

theorem matP_mul (A B : SLp p) : matP p (A * B) = matP p A * matP p B := rfl
theorem matP_one : matP p 1 = 1 := rfl
theorem matP_inv (A : SLp p) : matP p A⁻¹ = adjugate (matP p A) := rfl

theorem matP_injective : Function.Injective (matP p) := fun _ _ h => Subtype.ext h

theorem ιΓ_injective : Function.Injective (ιΓ p) := by
  intro g h hgh
  apply mat_injective
  ext i j
  have := congrArg (fun A => matP p A i j) hgh
  simp only [matP_ιΓ] at this
  exact_mod_cast this

theorem continuous_matP_apply (i j : Fin 2) : Continuous fun A : SLp p => matP p A i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/-! ### Ultrametric estimates -/

theorem norm_add_le_of {x y : ℚ_[p]} {c : ℝ} (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ c) : ‖x + y‖ ≤ c :=
  (Padic.nonarchimedean x y).trans (max_le hx hy)

theorem norm_mul_le_of {x y : ℚ_[p]} {c : ℝ} (hc : c ≤ 1) (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ 1) :
    ‖x * y‖ ≤ c := by
  rw [norm_mul]; nlinarith [norm_nonneg x, norm_nonneg y]

theorem norm_mul_le_of' {x y : ℚ_[p]} {c : ℝ} (hc : c ≤ 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ c) :
    ‖x * y‖ ≤ c := by
  rw [mul_comm]; exact norm_mul_le_of hc hy hx

/-! ### `SL₂(ℤ_p)` -/

variable (p) in
/-- `SL₂(ℤ_p)`: entries of norm at most one. -/
def Kp : Subgroup (SLp p) where
  carrier := {A | ∀ i j, ‖matP p A i j‖ ≤ 1}
  one_mem' := by intro i j; fin_cases i <;> fin_cases j <;> simp
  mul_mem' := by
    intro A B hA hB i j
    change ‖(matP p A * matP p B) i j‖ ≤ 1
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact norm_add_le_of (norm_mul_le_of le_rfl (hA _ _) (hB _ _))
      (norm_mul_le_of le_rfl (hA _ _) (hB _ _))
  inv_mem' := by
    intro A hA
    have hA' : ∀ i j, ‖matP p A i j‖ ≤ 1 := hA
    intro i j
    change ‖(adjugate (matP p A)) i j‖ ≤ 1
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [norm_neg, hA']

theorem isOpen_Kp : IsOpen (Kp p : Set (SLp p)) := by
  have : (Kp p : Set (SLp p)) =
      ⋂ i, ⋂ j, (fun A : SLp p => matP p A i j) ⁻¹' closedBall (0 : ℚ_[p]) 1 := by
    ext A; simp [Kp, mem_closedBall_zero_iff]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage (continuous_matP_apply i j)

theorem isCompact_Kp : IsCompact (Kp p : Set (SLp p)) := by
  have hB : IsCompact (Set.pi univ fun _ : Fin 2 => Set.pi univ fun _ : Fin 2 =>
      closedBall (0 : ℚ_[p]) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have := (SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℚ_[p])).isCompact_preimage hB
  have e : (Kp p : Set (SLp p)) = (Subtype.val : SLp p → Matrix (Fin 2) (Fin 2) ℚ_[p]) ⁻¹'
      (Set.pi univ fun _ : Fin 2 => Set.pi univ fun _ : Fin 2 => closedBall (0 : ℚ_[p]) 1) := by
    ext A
    show (∀ i j, ‖matP p A i j‖ ≤ 1) ↔
      ∀ i ∈ univ, ∀ j ∈ univ, (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j ∈ closedBall (0 : ℚ_[p]) 1
    simp [mem_closedBall_zero_iff]
  rw [e]; exact this

/-! ### Congruence subgroups `K(r)` -/

variable (p) in
/-- `K(r)`: entries congruent to `δ_ij` modulo `p^r`. -/
def Kr (r : ℕ) : Subgroup (SLp p) where
  carrier := {A | ∀ i j, ‖matP p A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(r : ℤ))}
  one_mem' := by
    intro i j; simp only [matP_one, sub_self, norm_zero]; positivity
  mul_mem' := by
    intro A B hA hB i j
    have hc : (p : ℝ) ^ (-(r : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)
    set X := matP p A - 1
    set Y := matP p B - 1
    have hX : ∀ i j, ‖X i j‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := hA
    have hY : ∀ i j, ‖Y i j‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := hB
    have hX1 : ∀ i j, ‖X i j‖ ≤ 1 := fun i j => (hX i j).trans hc
    have e : matP p (A * B) - 1 = X * Y + X + Y := by
      simp only [X, Y, matP_mul]; noncomm_ring
    change ‖(matP p (A * B)) i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ _
    rw [← Matrix.sub_apply, e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_two]
    exact norm_add_le_of (norm_add_le_of (norm_add_le_of
      (norm_mul_le_of' hc (hX1 _ _) (hY _ _)) (norm_mul_le_of' hc (hX1 _ _) (hY _ _)))
      (hX _ _)) (hY _ _)
  inv_mem' := by
    intro A hA
    have hA' : ∀ i j, ‖matP p A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤
      (p : ℝ) ^ (-(r : ℤ)) := hA
    intro i j
    change ‖(adjugate (matP p A)) i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ _
    rw [Matrix.adjugate_fin_two]
    have h00 := hA' 0 0; have h01 := hA' 0 1; have h10 := hA' 1 0; have h11 := hA' 1 1
    simp at h00 h01 h10 h11
    fin_cases i <;> fin_cases j <;> simp [norm_neg, h00, h01, h10, h11]

theorem Kr_le_Kp (r : ℕ) : Kr p r ≤ Kp p := by
  intro A hA i j
  have hc : (p : ℝ) ^ (-(r : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)
  have h := (hA i j).trans hc
  have e : matP p A i j = (matP p A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) +
      (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := by ring
  rw [e]
  refine norm_add_le_of h ?_
  fin_cases i <;> fin_cases j <;> simp

theorem isOpen_Kr (r : ℕ) : IsOpen (Kr p r : Set (SLp p)) := by
  have hr : (p : ℝ) ^ (-(r : ℤ)) ≠ 0 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have : (Kr p r : Set (SLp p)) = ⋂ i, ⋂ j, (fun A : SLp p =>
      matP p A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) ⁻¹'
        closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(r : ℤ))) := by
    ext A; simp [Kr, mem_closedBall_zero_iff]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (IsUltrametricDist.isOpen_closedBall _ hr).preimage
      ((continuous_matP_apply i j).sub continuous_const)

/-! ### `Γ ∩ SL₂(ℤ_p) = SL₂(ℤ)` -/

/-- An element of `ℤ[1/p]` which is `p`-adically integral is an integer. -/
theorem R_integral_iff {x : ℚ} (hx : x ∈ R p) : ‖(x : ℚ_[p])‖ ≤ 1 ↔ ∃ z : ℤ, (z : ℚ) = x := by
  constructor
  · intro h
    obtain ⟨a, n, rfl⟩ := hx
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    have ha : ((a : ℚ) : ℚ_[p]) = (((a : ℚ) / p ^ n : ℚ) : ℚ_[p]) * (p : ℚ_[p]) ^ n := by
      push_cast; field_simp
    have hnorm : ‖(a : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      have : ‖((a : ℚ) : ℚ_[p])‖ = ‖(((a : ℚ) / p ^ n : ℚ) : ℚ_[p])‖ * (p : ℝ) ^ (-(n : ℤ)) := by
        rw [ha, norm_mul, Padic.norm_p_pow]
      have h2 : ((a : ℚ) : ℚ_[p]) = (a : ℚ_[p]) := by push_cast; rfl
      rw [← h2, this]
      exact mul_le_of_le_one_left (by positivity) h
    obtain ⟨k, hk⟩ := (Padic.norm_int_le_pow_iff_dvd a n).mp hnorm
    refine ⟨k, ?_⟩
    have hpq : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    rw [hk]; push_cast; field_simp
  · rintro ⟨z, rfl⟩
    have := Padic.norm_int_le_one (p := p) z
    simpa using this

theorem ιΓ_mem_Kp_iff (g : Γ p) : ιΓ p g ∈ Kp p ↔ g ∈ Λ.subgroupOf (Γ p) := by
  rw [mem_subgroupOf]
  constructor
  · intro h i j
    have := (R_integral_iff (g.2 i j)).mp (h i j)
    exact Subring.mem_bot.mpr this
  · intro h i j
    exact (R_integral_iff (g.2 i j)).mpr (Subring.mem_bot.mp (h i j))

/-! ### Root group elements of `SL₂(ℚ_p)` -/

/-- `u(t)` in `SL₂(ℚ_p)`. -/
noncomputable def uP (t : ℚ_[p]) : SLp p := ⟨u t, by simp [u, Matrix.det_fin_two_of]⟩

/-- `v(t)` in `SL₂(ℚ_p)`. -/
noncomputable def vP (t : ℚ_[p]) : SLp p := ⟨v t, by simp [v, Matrix.det_fin_two_of]⟩

/-- `diag(t, t⁻¹)` in `SL₂(ℚ_p)`. -/
noncomputable def dP (t : ℚ_[p]) (ht : t ≠ 0) : SLp p := ⟨dg t, by simp [dg, Matrix.det_fin_two_of, ht]⟩

@[simp] theorem matP_uP (t : ℚ_[p]) : matP p (uP t) = u t := rfl
@[simp] theorem matP_vP (t : ℚ_[p]) : matP p (vP t) = v t := rfl
@[simp] theorem matP_dP (t : ℚ_[p]) (ht : t ≠ 0) : matP p (dP t ht) = dg t := rfl

theorem continuous_uP : Continuous (uP (p := p)) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [u] <;> fun_prop

theorem continuous_vP : Continuous (vP (p := p)) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [v] <;> fun_prop

theorem ιΓ_uΓ (a : ℚ) (ha : a ∈ R p) : ιΓ p (uΓ a ha) = uP (a : ℚ_[p]) := by
  apply matP_injective; ext i j
  simp only [matP_ιΓ, mat_uΓ, matP_uP]
  fin_cases i <;> fin_cases j <;> simp [u]

theorem ιΓ_vΓ (a : ℚ) (ha : a ∈ R p) : ιΓ p (vΓ a ha) = vP (a : ℚ_[p]) := by
  apply matP_injective; ext i j
  simp only [matP_ιΓ, mat_vΓ, matP_vP]
  fin_cases i <;> fin_cases j <;> simp [v]

end MzSl2
