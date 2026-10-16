import Mathlib
import MzSl2.FiberMap
import MzSl2.PhiMap

/-!
# Helper lemmas for fact d751

* stabilisers of cosets under `ρ`;
* conjugation of root elements by powers of `d`;
* integrality of `γ⁻¹ u(n) γ` for `n` divisible by a large power of `p`;
* the dynamical Levi set is a subgroup.
-/

open Matrix Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

section General

variable {G : Type*} [Group G] (M : Subgroup G)

theorem ρ_mem_stab_mk_iff (g h : G) : ρ M g ∈ Sym.stab (Cosets.mk M h) ↔ h⁻¹ * g * h ∈ M := by
  change g • Cosets.mk M h = Cosets.mk M h ↔ _
  rw [Cosets.smul_mk, Cosets.mk_eq_mk]
  constructor
  · intro hh; have := M.inv_mem hh; simpa [mul_assoc] using this
  · intro hh; have := M.inv_mem hh; simpa [mul_assoc] using this

end General

section Levi

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

theorem levi_of_subset_compact {g x : H} {K : Set H} (hK : IsCompact K)
    (h : ∀ n : ℤ, g ^ n * x * g ^ (-n) ∈ K) : x ∈ levi g :=
  hK.of_isClosed_subset isClosed_closure (closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n)
    hK.isClosed)

theorem levi_mul {g x y : H} (hx : x ∈ levi g) (hy : y ∈ levi g) : x * y ∈ levi g := by
  have hK : IsCompact (_root_.closure (Set.range fun n : ℤ => g ^ n * x * g ^ (-n)) *
      _root_.closure (Set.range fun n : ℤ => g ^ n * y * g ^ (-n))) := IsCompact.mul hx hy
  refine levi_of_subset_compact hK fun n => ?_
  refine Set.mem_mul.mpr ⟨_, subset_closure ⟨n, rfl⟩, _, subset_closure ⟨n, rfl⟩, ?_⟩
  group

theorem levi_inv {g x : H} (hx : x ∈ levi g) : x⁻¹ ∈ levi g := by
  have hK : IsCompact ((_root_.closure (Set.range fun n : ℤ => g ^ n * x * g ^ (-n)))⁻¹) := hx.inv
  refine levi_of_subset_compact hK fun n => ?_
  refine Set.mem_inv.mpr ?_
  have : (g ^ n * x⁻¹ * g ^ (-n))⁻¹ = g ^ n * x * g ^ (-n) := by group
  rw [this]; exact subset_closure ⟨n, rfl⟩

end Levi

variable {p : ℕ} [hp : Fact p.Prime]

/-- `u(n)` for an integer `n`. -/
noncomputable abbrev uZ (n : ℤ) : Γ p := uΓ (n : ℚ) (intCast_mem (R p) n)
/-- `v(n)` for an integer `n`. -/
noncomputable abbrev vZ (n : ℤ) : Γ p := vΓ (n : ℚ) (intCast_mem (R p) n)

theorem uZ_eq_zpow (n : ℤ) : (uZ n : Γ p) = uΓ 1 R_one ^ n := (uΓ_one_zpow n).symm

theorem vZ_eq_zpow (n : ℤ) : (vZ n : Γ p) = vΓ 1 R_one ^ n := by
  rw [vΓ_zpow]; congr 1; ring

theorem uZ_mem_Λp (n : ℤ) : (uZ n : Γ p) ∈ Λp p := uΓ_mem_Λ n

theorem vZ_mem_Λp (n : ℤ) : (vZ n : Γ p) ∈ Λp p := by
  rw [mem_subgroupOf]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [vΓ, v, Subring.mem_bot] <;> try exact ⟨n, rfl⟩

theorem dγ_pow_conj_u (N : ℕ) (a : ℚ) (ha : a ∈ R p) :
    (dγ p ^ N)⁻¹ * uΓ a ha * dγ p ^ N = uΓ (a / (p : ℚ) ^ (2 * N)) (R_div_pow ha (2 * N)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mat_injective
  rw [mat_mul, mat_mul, mat_dγ_pow_inv, mat_dγ_pow, mat_uΓ, mat_uΓ]
  have := dg_conj_u (inv_ne_zero (pow_ne_zero N hp0)) a
  rw [inv_inv] at this
  rw [this]; congr 1; field_simp; ring

theorem dγ_pow_conj_u' (N : ℕ) (a : ℚ) (ha : a ∈ R p) :
    dγ p ^ N * uΓ a ha * (dγ p ^ N)⁻¹ =
      uΓ ((p : ℚ) ^ (2 * N) * a) ((R p).mul_mem (R_pow_mem _) ha) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mat_injective
  rw [mat_mul, mat_mul, mat_dγ_pow_inv, mat_dγ_pow, mat_uΓ, mat_uΓ, dg_conj_u (pow_ne_zero N hp0)]
  congr 1; ring

theorem dγ_pow_conj_v (N : ℕ) (a : ℚ) (ha : a ∈ R p) :
    dγ p ^ N * vΓ a ha * (dγ p ^ N)⁻¹ = vΓ (a / (p : ℚ) ^ (2 * N)) (R_div_pow ha (2 * N)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mat_injective
  rw [mat_mul, mat_mul, mat_dγ_pow_inv, mat_dγ_pow, mat_vΓ, mat_vΓ, dg_conj_v (pow_ne_zero N hp0)]
  congr 1; ring

theorem dγ_pow_conj_v' (N : ℕ) (a : ℚ) (ha : a ∈ R p) :
    (dγ p ^ N)⁻¹ * vΓ a ha * dγ p ^ N =
      vΓ ((p : ℚ) ^ (2 * N) * a) ((R p).mul_mem (R_pow_mem _) ha) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mat_injective
  rw [mat_mul, mat_mul, mat_dγ_pow_inv, mat_dγ_pow, mat_vΓ, mat_vΓ]
  have := dg_inv_conj_v (pow_ne_zero N hp0) a
  rw [this]; congr 1; ring

/-- `u(a) ∈ SL₂(ℤ)` forces `a ∈ ℤ`. -/
theorem int_of_uΓ_mem {a : ℚ} {ha : a ∈ R p} (h : uΓ a ha ∈ Λp p) : ∃ z : ℤ, (z : ℚ) = a := by
  rw [mem_subgroupOf] at h
  exact Subring.mem_bot.mp (h 0 1)

theorem int_of_vΓ_mem {a : ℚ} {ha : a ∈ R p} (h : vΓ a ha ∈ Λp p) : ∃ z : ℤ, (z : ℚ) = a := by
  rw [mem_subgroupOf] at h
  exact Subring.mem_bot.mp (h 1 0)

/-- `p^{2N} ∣ n` when `d^{-N} u(n) d^N` is integral. -/
theorem dvd_of_conj_u_mem (N : ℕ) (n : ℤ) (h : (dγ p ^ N)⁻¹ * uZ n * dγ p ^ N ∈ Λp p) :
    (p : ℤ) ^ (2 * N) ∣ n := by
  rw [dγ_pow_conj_u] at h
  obtain ⟨z, hz⟩ := int_of_uΓ_mem h
  refine ⟨z, ?_⟩
  have hp0 : (p : ℚ) ^ (2 * N) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have : (n : ℚ) = (p : ℚ) ^ (2 * N) * z := by rw [hz]; field_simp
  exact_mod_cast this

theorem dvd_of_conj_v_mem (N : ℕ) (n : ℤ) (h : dγ p ^ N * vZ n * (dγ p ^ N)⁻¹ ∈ Λp p) :
    (p : ℤ) ^ (2 * N) ∣ n := by
  rw [dγ_pow_conj_v] at h
  obtain ⟨z, hz⟩ := int_of_vΓ_mem h
  refine ⟨z, ?_⟩
  have hp0 : (p : ℚ) ^ (2 * N) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have : (n : ℚ) = (p : ℚ) ^ (2 * N) * z := by rw [hz]; field_simp
  exact_mod_cast this

/-- For `γ ∈ Γ`, `γ⁻¹ u(n) γ` is integral once `n` is divisible by a large power of `p`. -/
theorem bot_mul_pow_mem {x : ℚ} {e e' : ℕ} (hx : (p : ℚ) ^ e * x ∈ (⊥ : Subring ℚ)) :
    (p : ℚ) ^ (e + e') * x ∈ (⊥ : Subring ℚ) := by
  have hp : ((p : ℚ) ^ e') ∈ (⊥ : Subring ℚ) := Subring.pow_mem _ (Subring.mem_bot.mpr ⟨p, by simp⟩) _
  have := Subring.mul_mem _ hp hx
  rw [pow_add]; convert this using 1; ring

/-- For `γ ∈ Γ`, `γ⁻¹ u(n) γ` and `γ⁻¹ v(n) γ` are integral once `p^R ∣ n`. -/
theorem exists_conj_u_mem (γ : Γ p) : ∃ R : ℕ, ∀ k : ℤ,
    γ⁻¹ * uZ ((p : ℤ) ^ R * k) * γ ∈ Λp p ∧ γ⁻¹ * vZ ((p : ℤ) ^ R * k) * γ ∈ Λp p := by
  obtain ⟨e₁, he₁⟩ := Γ_clear p γ.2
  obtain ⟨e₂, he₂⟩ := Γ_clear p ((Γ p).inv_mem γ.2)
  set e := e₁ + e₂
  have hG : ∀ i j, (p : ℚ) ^ e * mat p γ i j ∈ (⊥ : Subring ℚ) := fun i j => bot_mul_pow_mem (he₁ i j)
  have hGi : ∀ i j, (p : ℚ) ^ e * mat p γ⁻¹ i j ∈ (⊥ : Subring ℚ) := fun i j => by
    have := bot_mul_pow_mem (e' := e₁) (he₂ i j); rwa [add_comm e₂ e₁] at this
  have hadj : mat p γ⁻¹ * mat p γ = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  have hk : ∀ k : ℤ, ((p : ℤ) ^ (2 * e) * k : ℤ) = ((p : ℚ) ^ e) * ((p : ℚ) ^ e) * k := by
    intro k; push_cast; ring
  refine ⟨2 * e, fun k => ⟨?_, ?_⟩⟩
  · rw [mem_subgroupOf]
    intro i j
    have e1 : mat p (γ⁻¹ * uZ ((p : ℤ) ^ (2 * e) * k) * γ) i j =
        (1 : Matrix (Fin 2) (Fin 2) ℚ) i j +
          k * ((p : ℚ) ^ e * mat p γ⁻¹ i 0) * ((p : ℚ) ^ e * mat p γ 1 j) := by
      have hδ : (1 : Matrix (Fin 2) (Fin 2) ℚ) i j =
          mat p γ⁻¹ i 0 * mat p γ 0 j + mat p γ⁻¹ i 1 * mat p γ 1 j := by
        rw [← hadj, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hδ, mat_mul, mat_mul, mat_uΓ, hk]
      simp only [u, Matrix.mul_apply, Fin.sum_univ_two]
      simp; ring
    show mat p (γ⁻¹ * uZ ((p : ℤ) ^ (2 * e) * k) * γ) i j ∈ _
    rw [e1]
    refine Subring.add_mem _ ?_ (Subring.mul_mem _ (Subring.mul_mem _ (intCast_mem _ k)
      (hGi i 0)) (hG 1 j))
    fin_cases i <;> fin_cases j <;> simp [Subring.zero_mem, Subring.one_mem]
  · rw [mem_subgroupOf]
    intro i j
    have e1 : mat p (γ⁻¹ * vZ ((p : ℤ) ^ (2 * e) * k) * γ) i j =
        (1 : Matrix (Fin 2) (Fin 2) ℚ) i j +
          k * ((p : ℚ) ^ e * mat p γ⁻¹ i 1) * ((p : ℚ) ^ e * mat p γ 0 j) := by
      have hδ : (1 : Matrix (Fin 2) (Fin 2) ℚ) i j =
          mat p γ⁻¹ i 0 * mat p γ 0 j + mat p γ⁻¹ i 1 * mat p γ 1 j := by
        rw [← hadj, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hδ, mat_mul, mat_mul, mat_vΓ, hk]
      simp only [v, Matrix.mul_apply, Fin.sum_univ_two]
      simp; ring
    show mat p (γ⁻¹ * vZ ((p : ℤ) ^ (2 * e) * k) * γ) i j ∈ _
    rw [e1]
    refine Subring.add_mem _ ?_ (Subring.mul_mem _ (Subring.mul_mem _ (intCast_mem _ k)
      (hGi i 1)) (hG 0 j))
    fin_cases i <;> fin_cases j <;> simp [Subring.zero_mem, Subring.one_mem]

end MzSl2
