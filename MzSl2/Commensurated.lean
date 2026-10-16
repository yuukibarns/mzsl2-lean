import Mathlib
import MzSl2.Statement

/-!
# `SL₂(ℤ)` is commensurated by `SL₂(ℤ[1/p])`

This realises the second alternative of the main theorem (`N = SL₂(ℤ)` is infinite,
commensurated and of infinite index), and is step 1 of fact 801.

Proof (as in 8de / 801): for `g ∈ Γ` pick `q = p^k` with `q g` and `q g⁻¹` integral. Then the
principal congruence subgroup `Γ(q²)` of `SL₂(ℤ)`, which has finite index (Mathlib), lies in
`g SL₂(ℤ) g⁻¹`, since `g⁻¹ (1 + q² M) g = 1 + (q g⁻¹) M (q g)`.
-/

open Matrix Subgroup CongruenceSubgroup
open scoped Pointwise MatrixGroups

namespace MzSl2

/-- The embedding `SL₂(ℤ) → SL₂(ℚ)`. -/
abbrev φ : SpecialLinearGroup (Fin 2) ℤ →* SpecialLinearGroup (Fin 2) ℚ :=
  SpecialLinearGroup.map (Int.castRingHom ℚ)

theorem φ_coe (B : SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    ((φ B : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = (B i j : ℚ) := rfl

theorem φ_injective : Function.Injective φ := by
  intro A B h
  ext i j
  have := congrArg (fun X : SpecialLinearGroup (Fin 2) ℚ => (X : Matrix (Fin 2) (Fin 2) ℚ) i j) h
  simp only [φ_coe] at this
  exact_mod_cast this

/-- `Λ` (integral entries) is the image of `SL₂(ℤ)`. -/
theorem Λ_eq_range : Λ = φ.range := by
  ext A
  constructor
  · intro hA
    choose z hz using fun i j => Subring.mem_bot.mp (hA i j)
    have hdet : (Matrix.of z).det = 1 := by
      have h1 := A.2
      rw [Matrix.det_fin_two] at h1
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply]
      rw [← hz 0 0, ← hz 0 1, ← hz 1 0, ← hz 1 1] at h1
      exact_mod_cast h1
    refine ⟨⟨Matrix.of z, hdet⟩, ?_⟩
    ext i j
    exact hz i j
  · rintro ⟨B, rfl⟩ i j
    exact Subring.mem_bot.mpr ⟨B i j, (φ_coe B i j).symm⟩

/-- The principal congruence subgroup of level `n`, inside `SL₂(ℚ)`. -/
abbrev Cong (n : ℕ) : Subgroup (SpecialLinearGroup (Fin 2) ℚ) := (Gamma n).map φ

theorem Cong_le_Λ (n : ℕ) : Cong n ≤ Λ := by
  rw [Λ_eq_range, MonoidHom.range_eq_map]; exact Subgroup.map_mono le_top

theorem Cong_relIndex (n : ℕ) [NeZero n] : (Cong n).relIndex Λ ≠ 0 := by
  rw [Λ_eq_range, MonoidHom.range_eq_map, relIndex_map_map_of_injective _ _ φ_injective,
    relIndex_top_right]
  exact FiniteIndex.index_ne_zero

/-! ### Clearing denominators -/

section Denominators

variable (p : ℕ) [hp : Fact p.Prime]

theorem p_ne_zero : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

/-- Every element of `ℤ[1/p]` becomes integral after multiplying by any large power of `p`. -/
theorem R_clear {x : ℚ} (hx : x ∈ R p) : ∃ k : ℕ, ∀ k' ≥ k, (p : ℚ) ^ k' * x ∈ (⊥ : Subring ℚ) := by
  obtain ⟨a, n, rfl⟩ := hx
  refine ⟨n, fun k' hk' => Subring.mem_bot.mpr ⟨a * p ^ (k' - n), ?_⟩⟩
  have := p_ne_zero p
  rw [show k' = (k' - n) + n by omega, pow_add]
  push_cast; field_simp
  rw [show k' - n + n - n = k' - n by omega]

/-- For `g ∈ Γ`, some `q = p^k` makes `q g` integral. -/
theorem Γ_clear {g : SpecialLinearGroup (Fin 2) ℚ} (hg : g ∈ Γ p) :
    ∃ k : ℕ, ∀ i j, (p : ℚ) ^ k * (g : Matrix (Fin 2) (Fin 2) ℚ) i j ∈ (⊥ : Subring ℚ) := by
  choose k hk using fun i j => R_clear p (hg i j)
  refine ⟨k 0 0 + k 0 1 + k 1 0 + k 1 1, fun i j => hk i j _ ?_⟩
  fin_cases i <;> fin_cases j <;> simp <;> omega

end Denominators

/-! ### Matrices with entries in a subring -/

/-- All entries of `X` lie in `S`. -/
def Ent (S : Subring ℚ) (X : Matrix (Fin 2) (Fin 2) ℚ) : Prop := ∀ i j, X i j ∈ S

theorem Ent.mul {S : Subring ℚ} {X Y : Matrix (Fin 2) (Fin 2) ℚ} (hX : Ent S X) (hY : Ent S Y) :
    Ent S (X * Y) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact S.add_mem (S.mul_mem (hX _ _) (hY _ _)) (S.mul_mem (hX _ _) (hY _ _))

theorem Ent.add {S : Subring ℚ} {X Y : Matrix (Fin 2) (Fin 2) ℚ} (hX : Ent S X) (hY : Ent S Y) :
    Ent S (X + Y) := fun i j => S.add_mem (hX i j) (hY i j)

theorem Ent.one (S : Subring ℚ) : Ent S 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [S.one_mem, S.zero_mem]

/-! ### The congruence subgroup lies in every conjugate -/

variable (p : ℕ) [hp : Fact p.Prime]

/-- Elements of `Γ(n)` are `1 + n M` with `M` integral. -/
theorem Gamma_decomp {n : ℕ} {B : SpecialLinearGroup (Fin 2) ℤ} (hB : B ∈ Gamma n) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ, ∀ i j, B i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + n * M i j := by
  rw [Gamma_mem] at hB
  obtain ⟨h00, h01, h10, h11⟩ := hB
  have e1 : ∀ x : ℤ, (x : ZMod n) = 1 → ∃ c : ℤ, x = 1 + n * c := by
    intro x hx
    have : ((x : ℤ) : ZMod n) = ((1 : ℤ) : ZMod n) := by simpa using hx
    obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this.symm
    exact ⟨c, by linarith⟩
  have e0 : ∀ x : ℤ, (x : ZMod n) = 0 → ∃ c : ℤ, x = 0 + n * c := by
    intro x hx
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx
    exact ⟨c, by linarith⟩
  obtain ⟨c00, hc00⟩ := e1 _ h00
  obtain ⟨c01, hc01⟩ := e0 _ h01
  obtain ⟨c10, hc10⟩ := e0 _ h10
  obtain ⟨c11, hc11⟩ := e1 _ h11
  refine ⟨!![c00, c01; c10, c11], ?_⟩
  intro i j; fin_cases i <;> fin_cases j <;> simp [hc00, hc01, hc10, hc11]

theorem mem_conj_iff {g x : SpecialLinearGroup (Fin 2) ℚ} {H : Subgroup (SpecialLinearGroup (Fin 2) ℚ)} :
    x ∈ (ConjAct.toConjAct g • H) ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
  simp

theorem Cong_le_conj {g : SpecialLinearGroup (Fin 2) ℚ} (hg : g ∈ Γ p) :
    ∃ n : ℕ, n ≠ 0 ∧ Cong n ≤ ConjAct.toConjAct g • Λ := by
  obtain ⟨k₁, hk₁⟩ := Γ_clear p hg
  obtain ⟨k₂, hk₂⟩ := Γ_clear p ((Γ p).inv_mem hg)
  set k := k₁ + k₂
  set q : ℚ := (p : ℚ) ^ k
  have hq : q ≠ 0 := pow_ne_zero _ (p_ne_zero p)
  have hpb : (p : ℚ) ∈ (⊥ : Subring ℚ) := Subring.mem_bot.mpr ⟨p, by simp⟩
  -- `q g` and `q g⁻¹` are integral
  have hY : Ent ⊥ (q • (g : Matrix (Fin 2) (Fin 2) ℚ)) := by
    intro i j
    have : q * (g : Matrix (Fin 2) (Fin 2) ℚ) i j
        = (p : ℚ) ^ k₂ * ((p : ℚ) ^ k₁ * (g : Matrix (Fin 2) (Fin 2) ℚ) i j) := by
      simp only [q, k]; ring
    rw [Matrix.smul_apply, smul_eq_mul, this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hpb _) (hk₁ i j)
  have hX : Ent ⊥ (q • ((g⁻¹ : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) := by
    intro i j
    have : q * ((g⁻¹ : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j
        = (p : ℚ) ^ k₁ * ((p : ℚ) ^ k₂ *
            ((g⁻¹ : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j) := by
      simp only [q, k]; ring
    rw [Matrix.smul_apply, smul_eq_mul, this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hpb _) (hk₂ i j)
  refine ⟨(p ^ k) ^ 2, pow_ne_zero _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
  rintro A ⟨B, hB, rfl⟩
  rw [mem_conj_iff]
  obtain ⟨M, hM⟩ := Gamma_decomp hB
  set Mq : Matrix (Fin 2) (Fin 2) ℚ := M.map (Int.cast : ℤ → ℚ)
  have hMq : Ent ⊥ Mq := fun i j => Subring.mem_bot.mpr ⟨M i j, by simp [Mq]⟩
  have hA : ((φ B : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = 1 + (q ^ 2) • Mq := by
    ext i j
    rw [φ_coe, hM i j]
    fin_cases i <;> fin_cases j <;> simp [Mq, q] <;> ring
  have hgg : ((g⁻¹ : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      (g : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
    change ((g⁻¹ * g : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = 1
    rw [inv_mul_cancel]; rfl
  have key : ((g⁻¹ * φ B * g : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = 1 + (q • ((g⁻¹ : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) * Mq *
          (q • (g : Matrix (Fin 2) (Fin 2) ℚ)) := by
    change ((g⁻¹ : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      ((φ B : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      (g : Matrix (Fin 2) (Fin 2) ℚ) = _
    rw [hA, Matrix.mul_add, Matrix.mul_one,
      Matrix.add_mul, hgg]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, sq]
  intro i j
  rw [key]
  exact ((Ent.one _).add ((hX.mul hMq).mul hY)) i j

/-- `SL₂(ℤ)` is commensurated by `SL₂(ℤ[1/p])`. -/
theorem Λ_commensurated : CommensuratedBy (Γ p) Λ := by
  have half : ∀ g ∈ Γ p, (ConjAct.toConjAct g • Λ).relIndex Λ ≠ 0 := by
    intro g hg
    obtain ⟨n, hn, hle⟩ := Cong_le_conj p hg
    haveI : NeZero n := ⟨hn⟩
    exact ne_zero_of_dvd_ne_zero (Cong_relIndex n) (relIndex_dvd_of_le_left _ hle)
  intro g hg
  rw [Commensurable.commensurator_mem_iff]
  refine ⟨half g hg, ?_⟩
  have h := half g⁻¹ ((Γ p).inv_mem hg)
  have e := Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct g)
    (ConjAct.toConjAct g⁻¹ • Λ) Λ
  rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at e
  rwa [e]

/-- All three alternatives of the main theorem occur. -/
theorem alternatives_occur :
    CommensuratedBy (Γ p) ⊥ ∧ CommensuratedBy (Γ p) Λ ∧ CommensuratedBy (Γ p) (Γ p) ∧
    ((⊥ : Subgroup (SpecialLinearGroup (Fin 2) ℚ)) : Set (SpecialLinearGroup (Fin 2) ℚ)).Finite ∧
    (Λ : Set (SpecialLinearGroup (Fin 2) ℚ)).Infinite ∧ Λ.relIndex (Γ p) = 0 ∧
    (Γ p).relIndex (Γ p) ≠ 0 :=
  ⟨finite_commensurated p ⊥ (by simp), Λ_commensurated p, Γ_commensurated p, by simp,
    Λ_infinite, Λ_relIndex_Γ p, by simp⟩

end MzSl2
