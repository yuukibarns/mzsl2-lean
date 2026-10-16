import Mathlib
import MzSl2.E69
import MzSl2.RelIndexChar
import MzSl2.Arith

/-!
# Fact 801: an infinite commensurated subgroup contains a power of `u(1)` (and of `v(1)`)

Following 801: with `L = N ∩ SL₂(ℤ)` (infinite by e69), the scale axioms in `Γ//L` give an
infinite commensurated `M ≤ SL₂(ℤ)`, commensurable with `L` and normalised by `u = u(1)`.
If `M ∩ ⟨u⟩ = 1`, the relative index character of `D = M ⋊ ⟨u⟩` takes the value `p⁻²` at `d`,
but it is trivial on every root element, and an explicit word in root elements and their
`m`-conjugates equals `d^k`. Contradiction.
-/

open Matrix Subgroup
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

section Basics

variable {G : Type*} [Group G]

theorem IsCommensurated.of_commensurable {A B : Subgroup G} (hA : IsCommensurated A)
    (hAB : Commensurable B A) : IsCommensurated B := fun g =>
  ((hAB.conj (ConjAct.toConjAct g)).trans (hA g)).trans hAB.symm

theorem mem_commensurator_of_isCommensurated {A : Subgroup G} (hA : IsCommensurated A) (g : G) :
    g ∈ Commensurable.commensurator A :=
  (Commensurable.commensurator_mem_iff A g).mpr (hA g)

theorem mem_commensurator_of_mem {A : Subgroup G} {g : G} (hg : g ∈ A) :
    g ∈ Commensurable.commensurator A := by
  rw [Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct g • A = A := by
    ext x; rw [mem_conjAct_smul_iff]
    constructor
    · intro h; simpa [mul_assoc] using A.mul_mem (A.mul_mem hg h) (A.inv_mem hg)
    · intro h; exact A.mul_mem (A.mul_mem (A.inv_mem hg) h) hg
  rw [this]

theorem relIndex_ne_zero_of_le_right' {H K L : Subgroup G} (hKL : K ≤ L) (h : H.relIndex L ≠ 0) :
    H.relIndex K ≠ 0 := fun h0 => h (relIndex_eq_zero_of_le_right hKL h0)

theorem relIndex_ne_zero_of_le_left' {H K L : Subgroup G} (hHK : H ≤ K) (h : H.relIndex L ≠ 0) :
    K.relIndex L ≠ 0 := fun h0 => h (relIndex_eq_zero_of_le_left hHK h0)

/-- Pigeonhole: some positive power of `x ∈ M` lies in a finite-index subgroup `D ≤ M`. -/
theorem exists_pow_mem {D M : Subgroup G} (hfi : D.relIndex M ≠ 0) {x : G} (hx : x ∈ M) :
    ∃ k : ℕ, 0 < k ∧ x ^ k ∈ D := by
  haveI : (D.subgroupOf M).FiniteIndex := ⟨hfi⟩
  let f : ℕ → M ⧸ D.subgroupOf M := fun k => QuotientGroup.mk ⟨x ^ k, M.pow_mem hx k⟩
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨j - i, by omega, ?_⟩
    have := QuotientGroup.eq.mp he
    rw [mem_subgroupOf] at this
    have e : x ^ (j - i) = (x ^ i)⁻¹ * x ^ j := by
      rw [← pow_sub_mul_pow x h.le]; group
    rw [e]; simpa using this
  · refine ⟨i - j, by omega, ?_⟩
    have := QuotientGroup.eq.mp he.symm
    rw [mem_subgroupOf] at this
    have e : x ^ (i - j) = (x ^ j)⁻¹ * x ^ i := by
      rw [← pow_sub_mul_pow x h.le]; group
    rw [e]; simpa using this

theorem normalizes_of_conj_eq {A : Subgroup G} {x : G} (hx : ConjAct.toConjAct x • A = A) :
    ∀ m ∈ A, x * m * x⁻¹ ∈ A := fun _ hm => conj_mem_of_normalizes hx hm

theorem conj_eq_of_normalizes {A : Subgroup G} {x : G} (h : ∀ m ∈ A, x * m * x⁻¹ ∈ A)
    (h' : ∀ m ∈ A, x⁻¹ * m * x ∈ A) : ConjAct.toConjAct x • A = A := by
  ext y; rw [mem_conjAct_smul_iff]
  constructor
  · intro hy; simpa [mul_assoc] using h _ hy
  · intro hy; exact h' _ hy

theorem smul_sup_conj (x : G) (A B : Subgroup G) :
    ConjAct.toConjAct x • (A ⊔ B) = ConjAct.toConjAct x • A ⊔ ConjAct.toConjAct x • B := by
  simp only [Subgroup.pointwise_smul_def]
  exact Subgroup.map_sup A B _

theorem smul_zpowers_conj (x y : G) :
    ConjAct.toConjAct x • zpowers y = zpowers (x * y * x⁻¹) := by
  ext z; rw [mem_conjAct_smul_iff, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [conj_zpow, hk]; group⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [← hk, conj_zpow]; group⟩

end Basics

/-! ### Matrix facts in `Γ` -/

theorem uΓ_one_zpow (j : ℤ) : (uΓ (p := p) 1 R_one) ^ j = uΓ (j : ℚ) (intCast_mem (R p) j) := by
  rw [uΓ_zpow]; congr 1; ring

theorem uΓ_one_infinite_order (j : ℤ) (h : (uΓ (p := p) 1 R_one) ^ j = 1) : j = 0 := by
  rw [uΓ_one_zpow] at h
  have := congrArg (fun g => mat p g 0 1) h
  simp [u, mat_one] at this
  exact_mod_cast this

theorem dγ_conj_uΓ_one : dγ p * uΓ 1 R_one * (dγ p)⁻¹ = (uΓ (p := p) 1 R_one) ^ (p ^ 2) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mat_injective
  rw [mat_mul, mat_mul, mat_inv, mat_pow, mat_dγ, mat_uΓ, u_pow]
  have : adjugate (dg (p : ℚ)) = dg (p : ℚ)⁻¹ := by
    simp [dg, Matrix.adjugate_fin_two]
  rw [this, dg_conj_u hp0]; push_cast; rfl

theorem dγ_inv_conj_pow : (dγ p)⁻¹ * (uΓ (p := p) 1 R_one) ^ (p ^ 2) * dγ p = uΓ 1 R_one := by
  rw [← dγ_conj_uΓ_one]; group

theorem uΓ_mem_Λ (n : ℤ) : uΓ (p := p) (n : ℚ) (intCast_mem (R p) n) ∈ Λ.subgroupOf (Γ p) := by
  rw [mem_subgroupOf]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [uΓ, u, Subring.mem_bot] <;> try exact ⟨n, rfl⟩

/-- The word identity of 801, step 4:
`d^k = u(-T) u(x₁) m u(-1) m⁻¹ u(x₂) m u(t) m⁻¹` with `t = p^k`. -/
theorem word_801 {a b c e t : ℚ} (hc : c ≠ 0) (ht : t ≠ 0) (hdet : a * e - b * c = 1) :
    u (-(a * (1 - t ^ 2) / c)) * u ((t - 1) / c ^ 2) *
      (!![a, b; c, e] * u (-1) * !![e, -b; -c, a]) * u ((t⁻¹ - 1) / c ^ 2) *
      (!![a, b; c, e] * u t * !![e, -b; -c, a]) = dg t := by
  obtain rfl : b = (a * e - 1) / c := by rw [eq_div_iff hc]; linear_combination -hdet
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [u, dg, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-! ### Normalisers -/

section Norm

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_eq {A : Subgroup G} {x : G} (hx : ConjAct.toConjAct x • A = A) :
    x ∈ Subgroup.normalizer (A : Set _) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh; exact conj_mem_of_normalizes hx hh
  · intro hh
    have hinv := normalizes_zpow' hx (-1)
    have := conj_mem_of_normalizes hinv hh
    simpa [_root_.zpow_neg, mul_assoc] using this

theorem conj_mem_of_mem_normalizer {A : Subgroup G} {k x : G} (hk : k ∈ Subgroup.normalizer (A : Set _))
    (hx : x ∈ A) : k * x * k⁻¹ ∈ A := (mem_normalizer_iff.mp hk x).mp hx

end Norm

/-! ### Elements with nonzero lower-left entry -/

theorem exists_c_ne_zero {M : Subgroup (Γ p)} (hMc : IsCommensurated M)
    (hMinf : (M : Set (Γ p)).Infinite) (hMΛ : M ≤ Λ.subgroupOf (Γ p)) :
    ∃ m ∈ M, mat p m 1 0 ≠ 0 := by
  by_contra h
  push_neg at h
  apply hMinf
  -- `M ∩ wMw⁻¹ ⊆ {1, w²}`
  set W := ConjAct.toConjAct (wγ p) • M
  have hsub : ((M ⊓ W : Subgroup (Γ p)) : Set (Γ p)) ⊆ {1, wγ p ^ 2} := by
    rintro x ⟨hxM, hxW⟩
    replace hxW := (mem_conjAct_smul_iff).mp hxW
    have hc := h x hxM
    have hc' := h _ hxW
    have hb : mat p x 0 1 = 0 := by
      have : mat p ((wγ p)⁻¹ * x * wγ p) 1 0 = -mat p x 0 1 := by
        rw [mat_mul, mat_mul, mat_inv, mat_wγ, mat_eq_entries x]
        simp [w, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      rw [this] at hc'; linarith
    have hdet := det_mat x
    rw [hb, hc] at hdet
    simp at hdet
    -- the diagonal entries are integers with product one
    have hxΛ := hMΛ hxM
    rw [mem_subgroupOf] at hxΛ
    obtain ⟨α, hα⟩ := Subring.mem_bot.mp (hxΛ 0 0)
    obtain ⟨δ', hδ⟩ := Subring.mem_bot.mp (hxΛ 1 1)
    have h00 : (x : SpecialLinearGroup (Fin 2) ℚ) 0 0 = mat p x 0 0 := rfl
    have h11 : (x : SpecialLinearGroup (Fin 2) ℚ) 1 1 = mat p x 1 1 := rfl
    rw [h00] at hα; rw [h11] at hδ
    rw [← hα, ← hδ] at hdet
    have hαδ : α * δ' = 1 := by exact_mod_cast hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hαδ with ha | ha
    · left
      have hd : δ' = 1 := by rw [ha] at hαδ; simpa using hαδ
      apply mat_injective
      rw [mat_eq_entries x, mat_one, hb, hc, ← hα, ← hδ, ha, hd]
      exact Matrix.one_fin_two.symm.trans (by simp)
    · right
      have hd : δ' = -1 := by rw [ha] at hαδ; linarith
      apply mat_injective
      rw [mat_eq_entries x, mat_pow, mat_wγ, hb, hc, ← hα, ← hδ, ha, hd]
      ext i j; fin_cases i <;> fin_cases j <;> simp [w, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hfin : ((M ⊓ W : Subgroup (Γ p)) : Set (Γ p)).Finite :=
    (Set.toFinite ({1, wγ p ^ 2} : Set (Γ p))).subset hsub
  exact finite_of_finite_of_relIndex hfin (by
    rw [inf_comm, Subgroup.inf_relIndex_right]; exact (hMc (wγ p)).1)

/-! ### The core contradiction -/

/-- **801, steps 2–4.** An infinite commensurated `M ≤ SL₂(ℤ)` normalised by `u = u(1)`
contains a nontrivial power of `u`. -/
theorem exists_pow_u_mem {M : Subgroup (Γ p)} (hMc : IsCommensurated M)
    (hMinf : (M : Set (Γ p)).Infinite) (hMΛ : M ≤ Λ.subgroupOf (Γ p))
    (hMu : ConjAct.toConjAct (uΓ (p := p) 1 R_one) • M = M) :
    ∃ n : ℤ, n ≠ 0 ∧ (uΓ (p := p) 1 R_one) ^ n ∈ M := by
  by_contra hcon
  push_neg at hcon
  set u := uΓ (p := p) 1 R_one with hu
  set d := dγ p with hd
  have hp2 : 2 ≤ p := hp.out.two_le
  have hinter : ∀ n : ℤ, u ^ n ∈ M → n = 0 := by
    intro n hn; by_contra h; exact hcon n h hn
  -- subgroups
  set M' := ConjAct.toConjAct d • M with hM'
  set J0 := M ⊓ M'
  set U := zpowers u
  set U2 := zpowers (u ^ (p ^ 2))
  set F := J0 ⊔ U2
  set D := M ⊔ U
  -- normalisers
  have huN : u ∈ Subgroup.normalizer (M : Set _) := mem_normalizer_of_conj_eq hMu
  have hUN : U ≤ Subgroup.normalizer (M : Set _) := (zpowers_le).mpr huN
  have hU2U : U2 ≤ U := (zpowers_le).mpr (Subgroup.pow_mem _ (mem_zpowers u) _)
  have hdinv : d⁻¹ * u ^ (p ^ 2) * d = u := dγ_inv_conj_pow
  have hu2N' : u ^ (p ^ 2) ∈ Subgroup.normalizer (M' : Set _) := by
    rw [mem_normalizer_iff]
    intro x
    rw [hM', mem_conjAct_smul_iff, mem_conjAct_smul_iff]
    have e : d⁻¹ * (u ^ (p ^ 2) * x * (u ^ (p ^ 2))⁻¹) * d = u * (d⁻¹ * x * d) * u⁻¹ := by
      calc d⁻¹ * (u ^ (p ^ 2) * x * (u ^ (p ^ 2))⁻¹) * d
          = (d⁻¹ * u ^ (p ^ 2) * d) * (d⁻¹ * x * d) * (d⁻¹ * u ^ (p ^ 2) * d)⁻¹ := by group
        _ = u * (d⁻¹ * x * d) * u⁻¹ := by rw [hdinv]
    rw [e]
    exact mem_normalizer_iff.mp huN _
  have hU2N' : U2 ≤ Subgroup.normalizer (M' : Set _) := (zpowers_le).mpr hu2N'
  have hFN : F ≤ Subgroup.normalizer (M : Set _) :=
    sup_le (inf_le_left.trans (Subgroup.le_normalizer)) (hU2U.trans hUN)
  have hFN' : F ≤ Subgroup.normalizer (M' : Set _) :=
    sup_le (inf_le_right.trans (Subgroup.le_normalizer)) hU2N'
  have hU2J0 : ∀ k ∈ U2, ∀ x ∈ J0, k * x * k⁻¹ ∈ J0 := fun k hk x hx =>
    ⟨conj_mem_of_mem_normalizer (hUN (hU2U hk)) hx.1, conj_mem_of_mem_normalizer (hU2N' hk) hx.2⟩
  -- `u^{p²}`-powers
  have hU2pow : ∀ y ∈ U2, ∃ j : ℤ, y = u ^ ((p : ℤ) ^ 2 * j) := by
    intro y hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact ⟨j, by rw [_root_.zpow_mul, ← zpow_natCast]; push_cast; rfl⟩
  -- `F ∩ M = J0`, `F ∩ M' = J0`
  have hFM : F ⊓ M = J0 := by
    apply le_antisymm
    · rintro x ⟨hxF, hxM⟩
      obtain ⟨j, hj, y, hy, rfl⟩ := sup_eq_prod hU2J0 hxF
      obtain ⟨n, rfl⟩ := hU2pow y hy
      have : u ^ ((p : ℤ) ^ 2 * n) ∈ M := by
        have := M.mul_mem (M.inv_mem hj.1) hxM; simpa using this
      rw [hinter _ this, zpow_zero, mul_one]; exact hj
    · exact le_inf (le_sup_left) inf_le_left
  have hFM' : F ⊓ M' = J0 := by
    apply le_antisymm
    · rintro x ⟨hxF, hxM⟩
      obtain ⟨j, hj, y, hy, rfl⟩ := sup_eq_prod hU2J0 hxF
      obtain ⟨n, rfl⟩ := hU2pow y hy
      have h1 : u ^ ((p : ℤ) ^ 2 * n) ∈ M' := by
        have := M'.mul_mem (M'.inv_mem hj.2) hxM; simpa using this
      rw [hM', mem_conjAct_smul_iff] at h1
      have h2 : d⁻¹ * u ^ ((p : ℤ) ^ 2 * n) * d = u ^ n := by
        have e1 : u ^ ((p : ℤ) ^ 2 * n) = (u ^ (p ^ 2)) ^ n := by
          rw [_root_.zpow_mul]; norm_cast
        have e2 := conj_zpow (a := d⁻¹) (b := u ^ (p ^ 2)) (i := n)
        rw [inv_inv] at e2
        rw [e1, ← e2, hdinv]
      rw [h2] at h1
      rw [hinter _ h1, mul_zero, zpow_zero, mul_one]; exact hj
    · exact le_inf (le_sup_left) inf_le_right
  -- finite indices of `J0`
  have hJM : J0.relIndex M ≠ 0 := by
    show (M ⊓ M').relIndex M ≠ 0
    rw [inf_comm, Subgroup.inf_relIndex_right]; exact (hMc d).1
  have hJM' : J0.relIndex M' ≠ 0 := by
    show (M ⊓ M').relIndex M' ≠ 0
    rw [Subgroup.inf_relIndex_right]; exact (hMc d).2
  -- `δ_M(d) = 1`, i.e. `[M : J0] = [M' : J0]`
  have hδM : δ M d = 1 := by
    have hc := fun g => mem_commensurator_of_isCommensurated hMc g
    have h1 : δ M (wγ p * d * (wγ p)⁻¹) = δ M d := δ_conj (hc _) (hc _)
    rw [wγ_conj_dγ, δ_inv (hc _)] at h1
    have h0 : δ M d ≠ 0 := δ_ne_zero (hc _)
    have hsq : δ M d * δ M d = 1 := by
      calc δ M d * δ M d = δ M d * (δ M d)⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel₀ h0
    have hq : ((δ M d : ℚ≥0) : ℚ) * (δ M d : ℚ) = 1 := by exact_mod_cast hsq
    have hnn : (0 : ℚ) ≤ (δ M d : ℚ) := (δ M d).2
    have : ((δ M d : ℚ≥0) : ℚ) = 1 := by nlinarith
    exact_mod_cast this
  have hJeq : J0.relIndex M = J0.relIndex M' := by
    have e1 : M.relIndex M' = J0.relIndex M' := by
      show M.relIndex M' = (M ⊓ M').relIndex M'; rw [Subgroup.inf_relIndex_right]
    have e2 : M'.relIndex M = J0.relIndex M := by
      show M'.relIndex M = (M ⊓ M').relIndex M; rw [inf_comm, Subgroup.inf_relIndex_right]
    have := hδM
    rw [δ, rr, e1, e2] at this
    have h0 : (J0.relIndex M : ℚ≥0) ≠ 0 := by exact_mod_cast hJM
    rw [div_eq_one_iff_eq h0] at this
    exact_mod_cast this.symm
  -- the index computations
  have hMF : M ⊔ F = M ⊔ U2 := by
    apply le_antisymm
    · exact sup_le le_sup_left (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hDeq : D = (M ⊔ F) ⊔ U := by
    apply le_antisymm
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    · refine sup_le (sup_le le_sup_left (sup_le (inf_le_left.trans le_sup_left)
        (hU2U.trans le_sup_right))) le_sup_right
  have huMF : u ∈ Subgroup.normalizer ((M ⊔ F : Subgroup (Γ p)) : Set (Γ p)) := by
    apply mem_normalizer_of_conj_eq
    rw [hMF, smul_sup_conj, hMu, smul_zpowers_conj]
    congr 2; group
  have hUMF : U ≤ Subgroup.normalizer ((M ⊔ F : Subgroup (Γ p)) : Set (Γ p)) := (zpowers_le).mpr huMF
  have hMFU : (M ⊔ F) ⊓ U = U2 := by
    apply le_antisymm
    · rintro x ⟨hxMF, hxU⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hxU
      rw [hMF] at hxMF
      obtain ⟨m, hm, y, hy, he⟩ := sup_eq_prod (fun k hk x hx => conj_mem_of_mem_normalizer
        (hUN (hU2U hk)) hx) hxMF
      obtain ⟨j, rfl⟩ := hU2pow y hy
      have : u ^ (n - (p : ℤ) ^ 2 * j) ∈ M := by
        have e : u ^ (n - (p : ℤ) ^ 2 * j) = m := by
          rw [_root_.zpow_sub, he]; group
        rw [e]; exact hm
      have h0 := hinter _ this
      have : n = (p : ℤ) ^ 2 * j := by omega
      rw [this, _root_.zpow_mul]
      exact Subgroup.zpow_mem _ (by
        rw [show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
        exact mem_zpowers _) j
    · exact le_inf (le_sup_right.trans le_sup_right) hU2U
  have hi1 : F.relIndex (M ⊔ F) = J0.relIndex M := by
    rw [relIndex_sup_normalizes_left (fun k hk x hx => conj_mem_of_mem_normalizer (hFN hk) hx),
      ← Subgroup.inf_relIndex_right F M, hFM]
  have hi2 : (M ⊔ F).relIndex D = p ^ 2 := by
    rw [hDeq, relIndex_sup_normalizes_right (fun k hk x hx =>
      conj_mem_of_mem_normalizer (hUMF hk) hx), ← Subgroup.inf_relIndex_right, hMFU]
    exact relIndex_zpowers_pow uΓ_one_infinite_order _
  have hFD : F.relIndex D = J0.relIndex M * p ^ 2 := by
    rw [← relIndex_mul_relIndex F (M ⊔ F) D le_sup_right
      (hDeq ▸ le_sup_left), hi1, hi2]
  have hD' : ConjAct.toConjAct d • D = M' ⊔ F := by
    rw [smul_sup_conj, ← hM', smul_zpowers_conj, show d * u * d⁻¹ = u ^ (p ^ 2) from
      dγ_conj_uΓ_one]
    apply le_antisymm
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
    · exact sup_le le_sup_left (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
  have hFD' : F.relIndex (ConjAct.toConjAct d • D) = J0.relIndex M' := by
    rw [hD', relIndex_sup_normalizes_left (fun k hk x hx =>
      conj_mem_of_mem_normalizer (hFN' hk) hx), ← Subgroup.inf_relIndex_right F M', hFM']
  have hFleD : F ≤ D := le_sup_right.trans (hDeq ▸ le_sup_left)
  have hFleD' : F ≤ ConjAct.toConjAct d • D := hD' ▸ le_sup_right
  have hFD0 : F.relIndex D ≠ 0 := by rw [hFD]; exact mul_ne_zero hJM (by positivity)
  have hFD'0 : F.relIndex (ConjAct.toConjAct d • D) ≠ 0 := by rw [hFD']; exact hJM'
  -- `δ_D(d) = p⁻²`
  have hδd : δ D d = ((p : ℚ≥0) ^ 2)⁻¹ := by
    rw [δ, rr_eq hFleD' hFleD hFD'0 hFD0, hFD', hFD, ← hJeq]
    have h0 : (J0.relIndex M : ℚ≥0) ≠ 0 := by exact_mod_cast hJM
    push_cast
    field_simp
  -- membership in the commensurator of `D`
  set C := Commensurable.commensurator D
  have hdC : d ∈ C := by
    rw [Commensurable.commensurator_mem_iff]
    exact ⟨relIndex_ne_zero_of_le_left' hFleD' hFD0,
      relIndex_ne_zero_of_le_left' hFleD hFD'0⟩
  have hMC : ∀ m ∈ M, m ∈ C := fun m hm => mem_commensurator_of_mem (le_sup_left (a := M) hm)
  have huC : u ∈ C := mem_commensurator_of_mem (le_sup_right (b := U) (mem_zpowers u))
  have huRC : ∀ t (ht : t ∈ R p), uΓ t ht ∈ C := by
    intro t ht
    obtain ⟨r, b, e⟩ := uΓ_eq_conj t ht
    rw [e]
    exact C.mul_mem (C.mul_mem (C.inv_mem (C.pow_mem hdC r)) (C.zpow_mem huC b)) (C.pow_mem hdC r)
  have hδu : ∀ t (ht : t ∈ R p), δ D (uΓ t ht) = 1 := by
    intro t ht
    apply eq_one_of_pow_roots (δ_ne_zero (huRC t ht)) hp2
    intro r
    have hkC := huRC _ (R_div_pow ht r)
    exact ⟨δ D _, by rw [← δ_pow hkC, uΓ_div_pow]⟩
  -- an element of `M` with nonzero lower-left entry
  obtain ⟨m, hmM, hc0⟩ := exists_c_ne_zero hMc hMinf hMΛ
  set a := mat p m 0 0 with ha_def
  set b := mat p m 0 1
  set c := mat p m 1 0 with hc_def
  set e := mat p m 1 1
  have hdet : a * e - b * c = 1 := det_mat m
  have hmΛ := hMΛ hmM
  rw [mem_subgroupOf] at hmΛ
  obtain ⟨aZ, haZ⟩ := Subring.mem_bot.mp (hmΛ 0 0)
  obtain ⟨cZ, hcZ⟩ := Subring.mem_bot.mp (hmΛ 1 0)
  have ha : a = aZ := haZ.symm
  have hc : c = cZ := hcZ.symm
  have hcZ0 : cZ ≠ 0 := by intro h; apply hc0; rw [hc, h]; simp
  have hp1 : p ≠ 1 := hp.out.one_lt.ne'
  obtain ⟨v, c0, hnd, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hcZ0) p hp1
  have hc00 : c0 ≠ 0 := by intro h; rw [h, mul_zero] at hfac; exact Int.natAbs_ne_zero.mpr hcZ0 hfac
  have hcop : Nat.Coprime p (((c0 : ℤ)).natAbs ^ 2) := by
    rw [Int.natAbs_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd).pow_right 2
  obtain ⟨k, hk1, z, hz⟩ := exists_pow_modEq_one (c₀ := (c0 : ℤ)) (by exact_mod_cast hc00) hcop
  set t : ℚ := (p : ℚ) ^ k with ht_def
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have ht0 : t ≠ 0 := pow_ne_zero _ hp0
  have hcne : c ≠ 0 := hc0
  have hc2 : c ^ 2 = (p : ℚ) ^ (2 * v) * (c0 : ℚ) ^ 2 := by
    have h1 : (cZ.natAbs : ℤ) ^ 2 = cZ ^ 2 := Int.natAbs_sq cZ
    have h2 : ((cZ.natAbs : ℤ) : ℚ) ^ 2 = (cZ : ℚ) ^ 2 := by exact_mod_cast h1
    rw [hc, ← h2, hfac]; push_cast; ring
  have htz : t - 1 = (c0 : ℚ) ^ 2 * z := by
    have : ((p : ℤ) ^ k - 1 : ℤ) = (c0 : ℤ) ^ 2 * z := hz
    have := congrArg (Int.cast : ℤ → ℚ) this
    push_cast at this; rw [ht_def]; exact this
  -- the parameters lie in `ℤ[1/p]`
  have htR : t ∈ R p := R_pow_mem k
  have hcR : c ∈ R p := by rw [hc]; exact intCast_mem (R p) cZ
  have haR : a ∈ R p := by rw [ha]; exact intCast_mem (R p) aZ
  have htinvR : t⁻¹ ∈ R p := by rw [ht_def, ← inv_pow]; exact (R p).pow_mem R_p_inv k
  have hx1 : (t - 1) / c ^ 2 ∈ R p := by
    have e1 : (t - 1) / c ^ 2 = (z : ℚ) / (p : ℚ) ^ (2 * v) := by
      rw [hc2, htz]; field_simp
    rw [e1]; exact ⟨z, 2 * v, rfl⟩
  have hx2 : (t⁻¹ - 1) / c ^ 2 ∈ R p := by
    have e1 : (t⁻¹ - 1) / c ^ 2 = -t⁻¹ * ((t - 1) / c ^ 2) := by field_simp; ring
    rw [e1]; exact (R p).mul_mem ((R p).neg_mem htinvR) hx1
  have hT : -(a * (1 - t ^ 2) / c) ∈ R p := by
    have e1 : -(a * (1 - t ^ 2) / c) = a * (1 + t) * c * ((t - 1) / c ^ 2) := by
      field_simp; ring
    rw [e1]
    exact (R p).mul_mem ((R p).mul_mem ((R p).mul_mem haR ((R p).add_mem R_one htR)) hcR) hx1
  have hm1 : (-1 : ℚ) ∈ R p := (R p).neg_mem R_one
  -- the word
  have hword : d ^ k = uΓ _ hT * uΓ _ hx1 * (m * uΓ (-1) hm1 * m⁻¹) * uΓ _ hx2 *
      (m * uΓ t htR * m⁻¹) := by
    apply mat_injective
    simp only [mat_mul, mat_inv, mat_uΓ]
    rw [hd, mat_dγ_pow, mat_eq_entries m, Matrix.adjugate_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    exact (word_801 hcne ht0 hdet).symm
  -- evaluate the character on both sides
  have hconj : ∀ y (hy : y ∈ R p), δ D (m * uΓ y hy * m⁻¹) = 1 := fun y hy => by
    rw [δ_conj (hMC m hmM) (huRC y hy), hδu]
  have hRHS : δ D (d ^ k) = 1 := by
    rw [hword]
    have hm1C := C.mul_mem (C.mul_mem (hMC m hmM) (huRC _ hm1)) (C.inv_mem (hMC m hmM))
    have htC := C.mul_mem (C.mul_mem (hMC m hmM) (huRC _ htR)) (C.inv_mem (hMC m hmM))
    rw [δ_mul (C.mul_mem (C.mul_mem (C.mul_mem (huRC _ hT) (huRC _ hx1)) hm1C) (huRC _ hx2)) htC,
      δ_mul (C.mul_mem (C.mul_mem (huRC _ hT) (huRC _ hx1)) hm1C) (huRC _ hx2),
      δ_mul (C.mul_mem (huRC _ hT) (huRC _ hx1)) hm1C, δ_mul (huRC _ hT) (huRC _ hx1),
      hδu, hδu, hδu, hconj, hconj]
    simp
  rw [δ_pow hdC, hδd, inv_pow, inv_eq_one, ← pow_mul] at hRHS
  have : p ^ (2 * k) = 1 := by exact_mod_cast hRHS
  rcases Nat.pow_eq_one.mp this with h | h
  · exact hp1 h
  · omega

/-! ### Fact 801 -/

theorem Λ'_commensurated : IsCommensurated (Λ.subgroupOf (Γ p)) :=
  isCommensurated_subgroupOf (Λ_le_Γ p) (Λ_commensurated p)

theorem uΓ_one_mem_Λ' : uΓ (p := p) 1 R_one ∈ Λ.subgroupOf (Γ p) := by
  have := uΓ_mem_Λ (p := p) 1
  simpa using this

/-- **Fact 801.** An infinite commensurated subgroup of `Γ` contains `u(n)` for some `n > 0`. -/
theorem exists_u_mem {N : Subgroup (Γ p)} (hN : IsCommensurated N)
    (hinf : (N : Set (Γ p)).Infinite) :
    ∃ n : ℕ, 0 < n ∧ uΓ (p := p) (n : ℚ) (by exact_mod_cast intCast_mem (R p) (n : ℤ)) ∈ N := by
  set Λ' := Λ.subgroupOf (Γ p)
  set L := N ⊓ Λ'
  have hLc : IsCommensurated L := hN.inf Λ'_commensurated
  have hLinf : (L : Set (Γ p)).Infinite := fun hfin => hinf (finite_of_finite_integral hN hfin)
  haveI := locallyCompact_Hc L hLc
  set u := uΓ (p := p) 1 R_one
  obtain ⟨V, hV, hVn⟩ := exists_normalized_of_divisible (exists_compactOpen L hLc)
    hp.out.two_le (h := ρH L u) (by
      intro r; obtain ⟨k, hk⟩ := uΓ_divisible (p := p) 1 R_one r
      exact ⟨ρH L k, by rw [← map_pow, hk]⟩)
  set M0 := V.comap (ρH L)
  have hM0u : ConjAct.toConjAct u • M0 = M0 := by
    ext x
    rw [mem_conjAct_smul_iff]
    simp only [M0, mem_comap, map_mul, map_inv]
    conv_rhs => rw [← hVn]
    rw [mem_conjAct_smul_iff]
  have hM0L : Commensurable M0 L := by
    have h := MzSl2.Commensurable.comap (ρH L) (hV.commensurable (UH_isCompactOpen L hLc))
    have hL' : (UH L).comap (ρH L) = L := by ext x; exact ρH_mem_UH_iff L x
    rwa [hL'] at h
  set M := M0 ⊓ Λ'
  have hLΛ : L ≤ Λ' := inf_le_right
  have hML : Commensurable M L := by
    constructor
    · -- `[L : M ∩ L]` finite since `M0 ∩ L ≤ M ∩ L`
      refine relIndex_ne_zero_of_le_left' (H := M0 ⊓ L) ?_ ?_
      · exact fun x hx => Subgroup.mem_inf.mpr ⟨hx.1, hLΛ hx.2⟩
      · rw [Subgroup.inf_relIndex_right]; exact hM0L.1
    · exact relIndex_ne_zero_of_le_right' inf_le_left hM0L.2
  have hMc : IsCommensurated M := hLc.of_commensurable hML
  have hMinf : (M : Set (Γ p)).Infinite := fun hfin =>
    hLinf (finite_of_finite_of_relIndex (D := M ⊓ L) (hfin.subset fun x hx => hx.1)
      (by rw [Subgroup.inf_relIndex_right]; exact hML.1))
  have hMu : ConjAct.toConjAct u • M = M := by
    have hinv := normalizes_zpow' hM0u (-1)
    apply conj_eq_of_normalizes
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨conj_mem_of_normalizes hM0u hx.1,
        Λ'.mul_mem (Λ'.mul_mem uΓ_one_mem_Λ' hx.2) (Λ'.inv_mem uΓ_one_mem_Λ')⟩
    · intro x hx
      have := conj_mem_of_normalizes hinv hx.1
      simp only [_root_.zpow_neg, zpow_one, inv_inv] at this
      exact Subgroup.mem_inf.mpr ⟨this,
        Λ'.mul_mem (Λ'.mul_mem (Λ'.inv_mem uΓ_one_mem_Λ') hx.2) uΓ_one_mem_Λ'⟩
  obtain ⟨n, hn0, hnM⟩ := exists_pow_u_mem hMc hMinf inf_le_right hMu
  obtain ⟨j, hj0, hjL⟩ := exists_pow_mem (D := L ⊓ M) (M := M)
    (by rw [Subgroup.inf_relIndex_right]; exact hML.2) hnM
  have hmem : u ^ (n * j) ∈ N := by
    have := hjL.1.1; rwa [← zpow_natCast, ← _root_.zpow_mul] at this
  rw [uΓ_one_zpow] at hmem
  have hnj : n * (j : ℤ) ≠ 0 := mul_ne_zero hn0 (by exact_mod_cast hj0.ne')
  refine ⟨(n * j).natAbs, Int.natAbs_pos.mpr hnj, ?_⟩
  have hcongr : ∀ (x y : ℚ) (hx : x ∈ R p) (hy : y ∈ R p), x = y → uΓ x hx = uΓ y hy := by
    rintro x y hx hy rfl; rfl
  rcases Int.natAbs_eq (n * j) with h | h
  · convert hmem using 1
    apply hcongr
    rw [← Int.cast_natCast, ← h]
  · have := N.inv_mem hmem
    convert this using 1
    rw [eq_inv_iff_mul_eq_one, uΓ_mul]
    rw [← uΓ_zero]
    apply hcongr
    have h' : (((n * j : ℤ)) : ℚ) = -(((n * j).natAbs : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at h' ⊢; linarith

theorem wγ_conj_uΓ (a : ℚ) (ha : a ∈ R p) :
    wγ p * uΓ a ha * (wγ p)⁻¹ = vΓ (-a) ((R p).neg_mem ha) := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_inv]
  simp only [mat_wγ, mat_uΓ, mat_vΓ]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [w, u, v, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Fact 801, lower version.** An infinite commensurated subgroup contains `v(n)`, `n > 0`. -/
theorem exists_v_mem {N : Subgroup (Γ p)} (hN : IsCommensurated N)
    (hinf : (N : Set (Γ p)).Infinite) :
    ∃ n : ℕ, 0 < n ∧ vΓ (p := p) (n : ℚ) (by exact_mod_cast intCast_mem (R p) (n : ℤ)) ∈ N := by
  set N2 := ConjAct.toConjAct (wγ p)⁻¹ • N
  have hN2 : IsCommensurated N2 := hN.of_commensurable (hN (wγ p)⁻¹)
  have hinf2 : (N2 : Set (Γ p)).Infinite := by
    intro hfin
    apply hinf
    have : (N : Set (Γ p)) ⊆ (fun y => wγ p * y * (wγ p)⁻¹) '' (N2 : Set (Γ p)) := by
      intro x hx
      refine ⟨(wγ p)⁻¹ * x * wγ p, ?_, by group⟩
      rw [SetLike.mem_coe, mem_conjAct_smul_iff]; simpa [mul_assoc] using hx
    exact (hfin.image _).subset this
  obtain ⟨n, hn, hmem⟩ := exists_u_mem hN2 hinf2
  rw [mem_conjAct_smul_iff, inv_inv, wγ_conj_uΓ] at hmem
  refine ⟨n, hn, ?_⟩
  have := N.inv_mem hmem
  convert this using 1
  rw [eq_inv_iff_mul_eq_one, vΓ_mul, ← vΓ_zero]
  congr 1; ring

end MzSl2
