import Mathlib
import MzSl2.Identities

/-!
# The statement of the main theorem, and its elementary parts

We work inside `SL₂(ℚ)`. `R p = ℤ[1/p]`, `Γ p = SL₂(ℤ[1/p])`, `Λ = SL₂(ℤ)`.

`MainTheorem` is the exact statement of Theorem 1.1 of the paper. It is proved as
`MzSl2.mainTheorem` in `MzSl2/D751b.lean`, from the external theorems in `MzSl2/Axioms.lean`.

Proved here: `Λ ≤ Γ`, `Λ` is infinite, `Λ` has infinite index in `Γ`, the three alternatives
are mutually exclusive (so "exactly one" holds whenever one does), and the finite and
finite-index examples are commensurated.
-/

open Matrix Subgroup
open scoped Pointwise

namespace MzSl2

/-- `ℤ[1/p]` as a subring of `ℚ`. -/
def R (p : ℕ) [hp : Fact p.Prime] : Subring ℚ where
  carrier := {x | ∃ (a : ℤ) (n : ℕ), x = a / (p : ℚ) ^ n}
  mul_mem' := by
    rintro _ _ ⟨a, n, rfl⟩ ⟨b, m, rfl⟩
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact ⟨a * b, n + m, by push_cast; rw [pow_add, div_mul_div_comm]⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, n, rfl⟩ ⟨b, m, rfl⟩
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact ⟨a * p ^ m + b * p ^ n, n + m, by push_cast; rw [pow_add]; field_simp⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, n, rfl⟩
    exact ⟨-a, n, by push_cast; ring⟩

/-- `SL₂(S)` for a subring `S ⊆ ℚ`, as a subgroup of `SL₂(ℚ)`. -/
def SLover (S : Subring ℚ) : Subgroup (SpecialLinearGroup (Fin 2) ℚ) where
  carrier := {A | ∀ i j, (A : Matrix (Fin 2) (Fin 2) ℚ) i j ∈ S}
  one_mem' := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [S.one_mem, S.zero_mem]
  mul_mem' := by
    intro A B hA hB i j
    change ((A : Matrix (Fin 2) (Fin 2) ℚ) * (B : Matrix (Fin 2) (Fin 2) ℚ)) i j ∈ S
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact S.add_mem (S.mul_mem (hA _ _) (hB _ _)) (S.mul_mem (hA _ _) (hB _ _))
  inv_mem' := by
    intro A hA i j
    change (adjugate (A : Matrix (Fin 2) (Fin 2) ℚ)) i j ∈ S
    have hA' : ∀ i j, (A : Matrix (Fin 2) (Fin 2) ℚ) i j ∈ S := hA
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [S.neg_mem, hA']

/-- `Γ = SL₂(ℤ[1/p])`. -/
abbrev Γ (p : ℕ) [Fact p.Prime] := SLover (R p)

/-- `Λ = SL₂(ℤ)`, embedded in `SL₂(ℚ)` (entries in the image of `ℤ`). -/
abbrev Λ := SLover (⊥ : Subring ℚ)

/-- A subgroup `N` is commensurated by `Γ` if every element of `Γ` commensurates `N`. -/
def CommensuratedBy (Γ N : Subgroup (SpecialLinearGroup (Fin 2) ℚ)) : Prop :=
  Γ ≤ Commensurable.commensurator N

/-- **Main theorem** (Theorem 1.1): every subgroup of `SL₂(ℤ[1/p])` commensurated by
`SL₂(ℤ[1/p])` is finite, commensurable with `SL₂(ℤ)`, or of finite index.
No finite generation, normality, Zariski density or arithmeticity is assumed. -/
def MainTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : Subgroup (SpecialLinearGroup (Fin 2) ℚ)),
    N ≤ Γ p → CommensuratedBy (Γ p) N →
      (N : Set (SpecialLinearGroup (Fin 2) ℚ)).Finite ∨ Commensurable N Λ ∨ N.relIndex (Γ p) ≠ 0

section Elementary

variable (p : ℕ) [hp : Fact p.Prime]

theorem Λ_le_Γ : Λ ≤ Γ p := fun _ hA i j => (bot_le : (⊥ : Subring ℚ) ≤ R p) (hA i j)

/-- `u(n)` for an integer `n`, as an element of `Λ`. -/
def uΛ (n : ℤ) : SpecialLinearGroup (Fin 2) ℚ :=
  ⟨u (n : ℚ), by simp [u, Matrix.det_fin_two_of]⟩

theorem uΛ_mem (n : ℤ) : uΛ n ∈ Λ := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [uΛ, u, Subring.zero_mem, Subring.one_mem, Subring.mem_bot]

theorem uΛ_injective : Function.Injective uΛ := by
  intro m n h
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) ℚ => (A : Matrix (Fin 2) (Fin 2) ℚ) 0 1) h
  simpa [uΛ, u] using this

theorem Λ_infinite : (Λ : Set (SpecialLinearGroup (Fin 2) ℚ)).Infinite :=
  Set.infinite_of_injective_forall_mem uΛ_injective uΛ_mem

/-- `d = diag(p, p⁻¹)`. -/
def dΓ : SpecialLinearGroup (Fin 2) ℚ :=
  ⟨dg (p : ℚ), by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    simp [dg, Matrix.det_fin_two_of, this]⟩

theorem dΓ_pow_coe (k : ℕ) :
    ((dΓ p ^ k : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = dg ((p : ℚ) ^ k) := by
  induction k with
  | zero => simp [dg]; exact Matrix.one_fin_two
  | succ k ih =>
    rw [pow_succ, ← dg_pow] at *
    change ((dΓ p ^ k : SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) * dg (p : ℚ) = _
    rw [ih, pow_succ]

theorem dΓ_mem : dΓ p ∈ Γ p := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨p, 0, by simp [dΓ, dg]⟩
  · exact ⟨0, 0, by simp [dΓ, dg]⟩
  · exact ⟨0, 0, by simp [dΓ, dg]⟩
  · exact ⟨1, 1, by simp [dΓ, dg]⟩

/-- For `k ≥ 1`, `d^k ∉ SL₂(ℤ)`: its lower-right entry `p^{-k}` is not an integer. -/
theorem dΓ_pow_not_mem {k : ℕ} (hk : 1 ≤ k) : dΓ p ^ k ∉ Λ := by
  intro h
  have h11 := h 1 1
  rw [dΓ_pow_coe] at h11
  simp only [dg, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    Subring.mem_bot] at h11
  obtain ⟨z, hz⟩ := h11
  have hp0 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hmul : ((p : ℤ) ^ k * z : ℤ) = (1 : ℤ) := by
    have : ((p : ℚ) ^ k) * (z : ℚ) = 1 := by
      rw [hz]; field_simp
    exact_mod_cast this
  have hdvd : (p : ℤ) ^ k ∣ 1 := ⟨z, hmul.symm⟩
  have hu := Int.eq_one_or_neg_one_of_mul_eq_one hmul
  have hp2 : (2 : ℤ) ≤ (p : ℤ) ^ k := by
    have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    calc (2 : ℤ) ≤ p := h2
      _ = p ^ 1 := (pow_one _).symm
      _ ≤ p ^ k := pow_le_pow_right₀ (by omega) hk
  omega

/-- `SL₂(ℤ)` has infinite index in `SL₂(ℤ[1/p])`: the cosets `d^n SL₂(ℤ)` are distinct. -/
theorem Λ_relIndex_Γ : Λ.relIndex (Γ p) = 0 := by
  by_contra hne
  rw [Subgroup.relIndex] at hne
  have hne := Subgroup.index_ne_zero_iff_finite.mp hne
  let f : ℕ → (Γ p) ⧸ Λ.subgroupOf (Γ p) := fun n =>
    QuotientGroup.mk ⟨dΓ p ^ n, Subgroup.pow_mem _ (dΓ_mem p) n⟩
  have hf : Function.Injective f := by
    intro m n hmn
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · have := QuotientGroup.eq.mp hmn
      rw [Subgroup.mem_subgroupOf] at this
      apply dΓ_pow_not_mem p (k := n - m) (by omega)
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← pow_sub_mul_pow (dΓ p) (le_of_lt hlt)] ; group
    · have := QuotientGroup.eq.mp hmn.symm
      rw [Subgroup.mem_subgroupOf] at this
      apply dΓ_pow_not_mem p (k := m - n) (by omega)
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← pow_sub_mul_pow (dΓ p) (le_of_lt hlt)] ; group
  exact (Infinite.of_injective f hf).not_finite hne

/-- `Γ` is infinite. -/
theorem Γ_infinite : (Γ p : Set (SpecialLinearGroup (Fin 2) ℚ)).Infinite :=
  (Λ_infinite).mono (Λ_le_Γ p)

/-- A finite-index subgroup of an infinite group is infinite. -/
theorem infinite_of_relIndex_ne_zero {H K : Subgroup (SpecialLinearGroup (Fin 2) ℚ)}
    (hK : (K : Set (SpecialLinearGroup (Fin 2) ℚ)).Infinite) (hHK : H.relIndex K ≠ 0) :
    (H : Set (SpecialLinearGroup (Fin 2) ℚ)).Infinite := by
  intro hH
  apply hK
  have hc := Subgroup.card_mul_index (H.subgroupOf K)
  have h1 : Nat.card (H.subgroupOf K) ≠ 0 := by
    haveI : Finite (H.subgroupOf K) := by
      have : Finite H := hH.to_subtype
      exact Finite.of_injective (fun x : H.subgroupOf K => (⟨x.1.1, x.2⟩ : H))
        (by intro x y hxy; have h := congrArg Subtype.val hxy; exact Subtype.ext (Subtype.ext h))
    exact Nat.card_pos.ne'
  have h2 : Nat.card K ≠ 0 := by
    rw [← hc]; exact mul_ne_zero h1 hHK
  have : Finite K := (Nat.card_ne_zero.mp h2).2
  exact Set.toFinite _

/-- The three alternatives of the main theorem are mutually exclusive. -/
theorem alternatives_exclusive (N : Subgroup (SpecialLinearGroup (Fin 2) ℚ)) (hN : N ≤ Γ p) :
    ¬ ((N : Set (SpecialLinearGroup (Fin 2) ℚ)).Finite ∧ Commensurable N Λ) ∧
    ¬ (Commensurable N Λ ∧ N.relIndex (Γ p) ≠ 0) ∧
    ¬ ((N : Set (SpecialLinearGroup (Fin 2) ℚ)).Finite ∧ N.relIndex (Γ p) ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hfin, hcomm⟩
    exact infinite_of_relIndex_ne_zero Λ_infinite hcomm.1 hfin
  · rintro ⟨hcomm, hfi⟩
    have hNΓ : Commensurable N (Γ p) := ⟨hfi, by rw [Subgroup.relIndex_eq_one.mpr hN]; simp⟩
    exact (hcomm.symm.trans hNΓ).1 (Λ_relIndex_Γ p)
  · rintro ⟨hfin, hfi⟩
    exact infinite_of_relIndex_ne_zero (Γ_infinite p) hfi hfin

/-- Finite subgroups are commensurated by every element. -/
theorem finite_commensurated (N : Subgroup (SpecialLinearGroup (Fin 2) ℚ))
    (hN : (N : Set (SpecialLinearGroup (Fin 2) ℚ)).Finite) : CommensuratedBy (Γ p) N := by
  intro g _
  rw [Commensurable.commensurator_mem_iff]
  haveI : Finite N := hN.to_subtype
  have hconj : (((ConjAct.toConjAct g • N : Subgroup _) : Set (SpecialLinearGroup (Fin 2) ℚ))).Finite := by
    have : (ConjAct.toConjAct g • N : Subgroup _) = N.map (MulAut.conj g).toMonoidHom := by
      ext x; simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
      constructor
      · intro hx; exact ⟨g⁻¹ * x * g, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩; simpa [mul_assoc] using hy
    rw [this, Subgroup.coe_map]; exact hN.image _
  constructor
  · haveI : Finite N := hN.to_subtype
    exact FiniteIndex.index_ne_zero
  · haveI : Finite (ConjAct.toConjAct g • N : Subgroup _) := hconj.to_subtype
    exact FiniteIndex.index_ne_zero

/-- `Γ` is commensurated by itself (third alternative is realised by `N = Γ`). -/
theorem Γ_commensurated : CommensuratedBy (Γ p) (Γ p) := by
  intro g hg
  rw [Commensurable.commensurator_mem_iff]
  have : (ConjAct.toConjAct g • Γ p : Subgroup _) = Γ p := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
    simp only [map_inv, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    constructor
    · intro hx
      have := (Γ p).mul_mem ((Γ p).mul_mem hg hx) ((Γ p).inv_mem hg)
      simpa [mul_assoc] using this
    · intro hx
      exact (Γ p).mul_mem ((Γ p).mul_mem ((Γ p).inv_mem hg) hx) hg
  rw [this]

end Elementary

end MzSl2
