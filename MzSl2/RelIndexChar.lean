import Mathlib
import MzSl2.Completion

/-!
# The relative index character and product indices (used in fact 801)

* `rr A B = [A : A ∩ B] / [B : A ∩ B] ∈ ℚ≥0`, computed through any common finite-index
  subgroup, multiplicative along chains, invariant under conjugation;
* `δ D g = rr (gDg⁻¹) D` is multiplicative on the commensurator of `D`;
* a nonzero element of `ℚ≥0` that is a `p^r`-th power for every `r` equals `1`;
* indices in `H ⊔ K` when `K` normalises `H`, and `[⟨a⟩ : ⟨aⁿ⟩] = n` for `a` of infinite order.
-/

open Subgroup
open scoped Pointwise

namespace MzSl2

variable {G : Type*} [Group G]

/-- `[A : A ∩ B] / [B : A ∩ B]`. -/
noncomputable def rr (A B : Subgroup G) : ℚ≥0 := (B.relIndex A : ℚ≥0) / (A.relIndex B : ℚ≥0)

/-- `rr` through a common subgroup of finite index. -/
theorem rr_eq {A B T : Subgroup G} (hTA : T ≤ A) (hTB : T ≤ B) (hA : T.relIndex A ≠ 0)
    (hB : T.relIndex B ≠ 0) : rr A B = (T.relIndex A : ℚ≥0) / (T.relIndex B : ℚ≥0) := by
  have h1 : T.relIndex (A ⊓ B) * (A ⊓ B).relIndex A = T.relIndex A :=
    relIndex_mul_relIndex T (A ⊓ B) A (le_inf hTA hTB) inf_le_left
  have h2 : T.relIndex (A ⊓ B) * (A ⊓ B).relIndex B = T.relIndex B :=
    relIndex_mul_relIndex T (A ⊓ B) B (le_inf hTA hTB) inf_le_right
  have e1 : (A ⊓ B).relIndex A = B.relIndex A := by rw [inf_comm, inf_relIndex_right]
  have e2 : (A ⊓ B).relIndex B = A.relIndex B := inf_relIndex_right A B
  rw [e1] at h1; rw [e2] at h2
  have hT0 : (T.relIndex (A ⊓ B) : ℚ≥0) ≠ 0 := by
    intro h; rw [Nat.cast_eq_zero] at h; rw [h, zero_mul] at h1; exact hA h1.symm
  rw [rr, ← h1, ← h2]; push_cast
  rw [mul_div_mul_left _ _ hT0]

theorem rr_ne_zero {A B : Subgroup G} (h : Commensurable A B) : rr A B ≠ 0 := by
  rw [rr]; exact div_ne_zero (by exact_mod_cast h.2) (by exact_mod_cast h.1)

/-- Multiplicativity along three pairwise commensurable subgroups. -/
theorem rr_trans {A B C : Subgroup G} (hAB : Commensurable A B) (hBC : Commensurable B C) :
    rr A C = rr A B * rr B C := by
  set T := A ⊓ B ⊓ C
  have hTA : T ≤ A := inf_le_left.trans inf_le_left
  have hTB : T ≤ B := inf_le_left.trans inf_le_right
  have hTC : T ≤ C := inf_le_right
  -- `T` has finite index in each of `A, B, C`
  have hAC := hAB.trans hBC
  have hTA' : T.relIndex A ≠ 0 := relIndex_inf_ne_zero (relIndex_inf_ne_zero (by simp) hAB.2)
    hAC.2
  have hTB' : T.relIndex B ≠ 0 := relIndex_inf_ne_zero (relIndex_inf_ne_zero hAB.1 (by simp))
    hBC.2
  have hTC' : T.relIndex C ≠ 0 := relIndex_inf_ne_zero (relIndex_inf_ne_zero hAC.1 hBC.1)
    (by simp)
  rw [rr_eq hTA hTC hTA' hTC', rr_eq hTA hTB hTA' hTB', rr_eq hTB hTC hTB' hTC']
  have : (T.relIndex B : ℚ≥0) ≠ 0 := by exact_mod_cast hTB'
  field_simp

theorem rr_smul (x : G) (A B : Subgroup G) :
    rr (ConjAct.toConjAct x • A) (ConjAct.toConjAct x • B) = rr A B := by
  rw [rr, rr, relIndex_pointwise_smul, relIndex_pointwise_smul]

theorem rr_self (A : Subgroup G) : rr A A = 1 := by simp [rr]

/-- The relative index character `δ_D(g) = rr (gDg⁻¹) D`. -/
noncomputable def δ (D : Subgroup G) (g : G) : ℚ≥0 := rr (ConjAct.toConjAct g • D) D

theorem conj_commensurable {D : Subgroup G} {g : G} (hg : g ∈ Commensurable.commensurator D) :
    Commensurable (ConjAct.toConjAct g • D) D :=
  (Commensurable.commensurator_mem_iff D g).mp hg

theorem δ_mul {D : Subgroup G} {g h : G} (hg : g ∈ Commensurable.commensurator D)
    (hh : h ∈ Commensurable.commensurator D) : δ D (g * h) = δ D g * δ D h := by
  have e : ConjAct.toConjAct (g * h) • D = ConjAct.toConjAct g • ConjAct.toConjAct h • D := by
    rw [map_mul, mul_smul]
  rw [δ, e, rr_trans ((conj_commensurable hh).conj (ConjAct.toConjAct g)) (conj_commensurable hg),
    rr_smul, δ, δ, mul_comm]

theorem δ_one (D : Subgroup G) : δ D 1 = 1 := by simp [δ, rr_self]

theorem δ_ne_zero {D : Subgroup G} {g : G} (hg : g ∈ Commensurable.commensurator D) : δ D g ≠ 0 :=
  rr_ne_zero (conj_commensurable hg)

theorem δ_inv {D : Subgroup G} {g : G} (hg : g ∈ Commensurable.commensurator D) :
    δ D g⁻¹ = (δ D g)⁻¹ := by
  have h := δ_mul hg ((Commensurable.commensurator D).inv_mem hg)
  rw [mul_inv_cancel, δ_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem δ_pow {D : Subgroup G} {g : G} (hg : g ∈ Commensurable.commensurator D) (n : ℕ) :
    δ D (g ^ n) = δ D g ^ n := by
  induction n with
  | zero => simp [δ_one]
  | succ n ih =>
    rw [pow_succ, δ_mul ((Commensurable.commensurator D).pow_mem hg n) hg, ih, pow_succ]

theorem δ_conj {D : Subgroup G} {g h : G} (hg : g ∈ Commensurable.commensurator D)
    (hh : h ∈ Commensurable.commensurator D) : δ D (g * h * g⁻¹) = δ D h := by
  have hc := Commensurable.commensurator D
  rw [δ_mul ((Commensurable.commensurator D).mul_mem hg hh)
    ((Commensurable.commensurator D).inv_mem hg), δ_mul hg hh, δ_inv hg]
  have : δ D g ≠ 0 := δ_ne_zero hg
  field_simp

/-- A nonzero element of `ℚ≥0` which is a `p^r`-th power for all `r` (`p ≥ 2`) is `1`. -/
theorem eq_one_of_pow_roots {q : ℚ≥0} (hq : q ≠ 0) {p : ℕ} (hp : 2 ≤ p)
    (hroot : ∀ r : ℕ, ∃ x : ℚ≥0, x ^ (p ^ r) = q) : q = 1 := by
  have hbig : ∀ n : ℕ, 2 ≤ n → ∀ r, n ^ (p ^ r) ≥ 2 ^ (p ^ r) := fun n hn r =>
    Nat.pow_le_pow_left hn _
  have hpr : ∀ r : ℕ, r < 2 ^ (p ^ r) := fun r =>
    (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by norm_num)
      (Nat.lt_pow_self (by omega)).le)
  obtain ⟨x, hx⟩ := hroot (q.den + q.num)
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_pow (by positivity)] at hx; exact hq hx.symm
  have hden : q.den = x.den ^ (p ^ (q.den + q.num)) := by
    have := congrArg NNRat.den hx; rw [NNRat.den_pow] at this; exact this.symm
  have hnum : q.num = x.num ^ (p ^ (q.den + q.num)) := by
    have := congrArg NNRat.num hx; rw [NNRat.num_pow] at this; exact this.symm
  have hxd : x.den = 1 := by
    by_contra h
    have h2 : 2 ≤ x.den := by have := x.den_pos; omega
    have := hbig _ h2 (q.den + q.num)
    have := hpr (q.den + q.num)
    omega
  have hxn : x.num = 1 := by
    have hpos : 0 < x.num := NNRat.num_pos.mpr (pos_iff_ne_zero.mpr hx0)
    by_contra h
    have h2 : 2 ≤ x.num := by omega
    have := hbig _ h2 (q.den + q.num)
    have := hpr (q.den + q.num)
    omega
  rw [← NNRat.num_div_den q, hden, hnum, hxd, hxn]; simp

/-! ### Indices in a product `H K` with `K` normalising `H` -/

/-- If `K` normalises `H` then `H K` is a subgroup. -/
def prodSubgroup (H K : Subgroup G) (hK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) : Subgroup G where
  carrier := (H : Set G) * K
  one_mem' := ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
  mul_mem' := by
    rintro _ _ ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
    refine ⟨h1 * (k1 * h2 * k1⁻¹), H.mul_mem hh1 (hK k1 hk1 h2 hh2), k1 * k2, K.mul_mem hk1 hk2, ?_⟩
    group
  inv_mem' := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    refine ⟨k⁻¹ * h⁻¹ * k⁻¹⁻¹, hK _ (K.inv_mem hk) _ (H.inv_mem hh), k⁻¹, K.inv_mem hk, ?_⟩
    group

theorem sup_eq_prod {H K : Subgroup G} (hK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hle : H ⊔ K ≤ prodSubgroup H K hK := sup_le
    (fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, one_mul k⟩)
  obtain ⟨h, hh, k, hk, e⟩ := hle hx
  exact ⟨h, hh, k, hk, e.symm⟩

/-- `[H K : K] = [H : H ∩ K]` when `K` normalises `H`. -/
theorem relIndex_sup_normalizes_left {H K : Subgroup G} (hK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) :
    K.relIndex (H ⊔ K) = K.relIndex H := by
  rw [relIndex, relIndex, index, index]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (Quotient.map' (fun h : H => (⟨h, le_sup_left (a := H) h.2⟩ : (H ⊔ K : Subgroup G)))
      (by
        intro a b hab
        rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab ⊢
        simpa using hab)) ⟨?_, ?_⟩
  · rintro ⟨a⟩ ⟨b⟩ hab
    apply Quotient.sound'
    have := Quotient.exact' hab
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at this ⊢
    simpa using this
  · rintro ⟨⟨x, hx⟩⟩
    obtain ⟨h, hh, k, hk, rfl⟩ := sup_eq_prod hK hx
    refine ⟨Quotient.mk'' ⟨h, hh⟩, Quotient.sound' ?_⟩
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf]
    simpa using hk

/-- `[H K : H] = [K : K ∩ H]` when `K` normalises `H`. -/
theorem relIndex_sup_normalizes_right {H K : Subgroup G}
    (hK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) : H.relIndex (H ⊔ K) = H.relIndex K := by
  rw [relIndex, relIndex, index, index]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (Quotient.map' (fun k : K => (⟨k, le_sup_right (a := H) k.2⟩ : (H ⊔ K : Subgroup G)))
      (by
        intro a b hab
        rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab ⊢
        simpa using hab)) ⟨?_, ?_⟩
  · rintro ⟨a⟩ ⟨b⟩ hab
    apply Quotient.sound'
    have := Quotient.exact' hab
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at this ⊢
    simpa using this
  · rintro ⟨⟨x, hx⟩⟩
    obtain ⟨h, hh, k, hk, rfl⟩ := sup_eq_prod hK hx
    refine ⟨Quotient.mk'' ⟨k, hk⟩, Quotient.sound' ?_⟩
    rw [QuotientGroup.leftRel_apply, mem_subgroupOf]
    -- `k⁻¹ (h k) = (k⁻¹ h k) ∈ H`
    have := hK k⁻¹ (K.inv_mem hk) h hh
    simpa [mul_assoc] using this

/-- `[⟨a⟩ : ⟨aⁿ⟩] = n` for `a` of infinite order. -/
theorem relIndex_zpowers_pow {a : G} (ha : ∀ n : ℤ, a ^ n = 1 → n = 0) (n : ℕ) :
    (zpowers (a ^ n)).relIndex (zpowers a) = n := by
  set f : Multiplicative ℤ →* G := zpowersHom G a
  have hf : Function.Injective f := by
    intro x y hxy
    have : a ^ (Multiplicative.toAdd x - Multiplicative.toAdd y) = 1 := by
      rw [zpow_sub]; simp only [f, zpowersHom_apply] at hxy; rw [hxy, mul_inv_cancel]
    have := ha _ this
    exact Multiplicative.toAdd.injective (by omega)
  have e1 : zpowers a = (⊤ : Subgroup (Multiplicative ℤ)).map f := by
    rw [← MonoidHom.range_eq_map]; exact (range_zpowersHom a).symm
  have e2 : zpowers (a ^ n) = (AddSubgroup.zmultiples (n : ℤ)).toSubgroup.map f := by
    ext x; simp only [mem_zpowers_iff, mem_map, f, zpowersHom_apply]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨Multiplicative.ofAdd ((n : ℤ) * k), ?_, ?_⟩
      · show (n : ℤ) * k ∈ AddSubgroup.zmultiples (n : ℤ)
        exact ⟨k, by simp [mul_comm]⟩
      · show a ^ ((n : ℤ) * k) = (a ^ n) ^ k
        rw [zpow_mul, zpow_natCast]
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      refine ⟨k, ?_⟩
      have : Multiplicative.toAdd y = k * n := by rw [← hk]; simp
      rw [← zpow_natCast, ← zpow_mul, this, mul_comm]
  rw [e1, e2, relIndex_map_map_of_injective _ _ hf, relIndex_top_right]
  have := Int.index_zmultiples (n : ℤ)
  simpa using this

end MzSl2
