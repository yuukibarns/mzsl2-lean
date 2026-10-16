import Mathlib
import MzSl2.Axioms

/-!
# Elementary consequences of the scale axioms

* compact open subgroups are pairwise commensurable, and conjugates are compact open;
* the scale is a positive integer once a compact open subgroup exists;
* an element with `p^r`-th roots for every `r` normalises a compact open subgroup
  (used for unipotents in c627, e69, 801).
-/

open Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem mem_conj_smul_iff {g x : H} {V : Subgroup H} :
    x ∈ (ConjAct.toConjAct g • V) ↔ g⁻¹ * x * g ∈ V := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
  simp

theorem relIndex_ne_zero_of_isOpen_of_isCompact {V W : Subgroup H} (hV : IsOpen (V : Set H))
    (hW : IsCompact (W : Set H)) : V.relIndex W ≠ 0 := by
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW
  have hopen : IsOpen ((V.subgroupOf W : Subgroup W) : Set W) := hV.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hopen
  exact Subgroup.index_ne_zero_of_finite

theorem coe_conj_smul (g : H) (V : Subgroup H) :
    ((ConjAct.toConjAct g • V : Subgroup H) : Set H) = (fun x => g⁻¹ * x * g) ⁻¹' (V : Set H) := by
  ext x; exact mem_conj_smul_iff

theorem coe_conj_smul' (g : H) (V : Subgroup H) :
    ((ConjAct.toConjAct g • V : Subgroup H) : Set H) = (fun x => g * x * g⁻¹) '' (V : Set H) := by
  ext x
  rw [SetLike.mem_coe, mem_conj_smul_iff]
  constructor
  · intro h; exact ⟨g⁻¹ * x * g, h, by group⟩
  · rintro ⟨y, hy, rfl⟩; simpa [mul_assoc] using hy

theorem IsCompactOpenSubgroup.conj {V : Subgroup H} (hV : IsCompactOpenSubgroup V) (g : H) :
    IsCompactOpenSubgroup (ConjAct.toConjAct g • V) := by
  refine ⟨?_, ?_⟩
  · rw [coe_conj_smul']
    exact hV.1.image (by fun_prop)
  · rw [coe_conj_smul]
    exact hV.2.preimage (by fun_prop)

theorem IsCompactOpenSubgroup.relIndex_ne_zero {V W : Subgroup H} (hV : IsCompactOpenSubgroup V)
    (hW : IsCompactOpenSubgroup W) : V.relIndex W ≠ 0 :=
  relIndex_ne_zero_of_isOpen_of_isCompact hV.2 hW.1

theorem IsCompactOpenSubgroup.commensurable {V W : Subgroup H} (hV : IsCompactOpenSubgroup V)
    (hW : IsCompactOpenSubgroup W) : Commensurable V W :=
  ⟨hV.relIndex_ne_zero hW, hW.relIndex_ne_zero hV⟩

/-- The scale is at least one when a compact open subgroup exists. -/
theorem one_le_scale (hex : ∃ V : Subgroup H, IsCompactOpenSubgroup V) (h : H) : 1 ≤ scale h := by
  obtain ⟨V, hV⟩ := hex
  have hne : {n | ∃ V : Subgroup H, IsCompactOpenSubgroup V ∧
      n = V.relIndex (ConjAct.toConjAct h • V)}.Nonempty :=
    ⟨_, V, hV, rfl⟩
  obtain ⟨W, hW, hWe⟩ := Nat.sInf_mem hne
  rw [scale, hWe]
  exact Nat.one_le_iff_ne_zero.mpr (hW.relIndex_ne_zero (hW.conj h))

variable [T2Space H] [TotallyDisconnectedSpace H] [LocallyCompactSpace H]

/-- An element with `p^r`-th roots for all `r` (some `p ≥ 2`) has scale one. -/
theorem scale_eq_one_of_divisible (hex : ∃ V : Subgroup H, IsCompactOpenSubgroup V)
    {p : ℕ} (hp : 2 ≤ p) {h : H} (hdiv : ∀ r : ℕ, ∃ k : H, k ^ (p ^ r) = h) : scale h = 1 := by
  set s := scale h with hs
  have hs1 : 1 ≤ s := one_le_scale hex h
  by_contra hne
  have hs2 : 2 ≤ s := by omega
  obtain ⟨k, hk⟩ := hdiv s
  have hpow := scale_pow k (p ^ s) (Nat.one_le_pow _ _ (by omega))
  rw [hk] at hpow
  have hk1 : 1 ≤ scale k := one_le_scale hex k
  rcases Nat.lt_or_ge (scale k) 2 with hlt | hge
  · have : scale k = 1 := by omega
    rw [this, one_pow] at hpow; omega
  · have h1 : 2 ^ (p ^ s) ≤ scale k ^ (p ^ s) := Nat.pow_le_pow_left hge _
    have h2 : s < 2 ^ s := Nat.lt_two_pow_self
    have h3 : 2 ^ s ≤ 2 ^ (p ^ s) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.lt_pow_self (by omega)).le
    omega

/-- An element with `p^r`-th roots for all `r` normalises a compact open subgroup. -/
theorem exists_normalized_of_divisible (hex : ∃ V : Subgroup H, IsCompactOpenSubgroup V)
    {p : ℕ} (hp : 2 ≤ p) {h : H} (hdiv : ∀ r : ℕ, ∃ k : H, k ^ (p ^ r) = h) :
    ∃ V : Subgroup H, IsCompactOpenSubgroup V ∧ ConjAct.toConjAct h • V = V := by
  rw [← scale_eq_one_iff]
  refine ⟨scale_eq_one_of_divisible hex hp hdiv, scale_eq_one_of_divisible hex hp ?_⟩
  intro r
  obtain ⟨k, hk⟩ := hdiv r
  exact ⟨k⁻¹, by rw [inv_pow, hk]⟩

end MzSl2
