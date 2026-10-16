import Mathlib
import MzSl2.Completion
import MzSl2.Statement

/-!
# General group-theoretic lemmas

Commensurability under preimages, passage from "commensurated by `Γ` inside `SL₂(ℚ)`" to
`IsCommensurated` inside the group `Γ`, intersections, finiteness.
-/

open Subgroup
open scoped Pointwise

namespace MzSl2

section General

variable {G : Type*} [Group G]

theorem Commensurable.comap {K : Type*} [Group K] (f : G →* K) {V U : Subgroup K}
    (h : Commensurable V U) : Commensurable (V.comap f) (U.comap f) :=
  ⟨relIndex_comap_ne_zero f h.1, relIndex_comap_ne_zero f h.2⟩

/-- If `D` is finite and has finite index in `N`, then `N` is finite. -/
theorem finite_of_finite_of_relIndex {D N : Subgroup G} (hD : (D : Set G).Finite)
    (hDN : D.relIndex N ≠ 0) : (N : Set G).Finite := by
  have hc := Subgroup.card_mul_index (D.subgroupOf N)
  have h1 : Nat.card (D.subgroupOf N) ≠ 0 := by
    haveI : Finite (D.subgroupOf N) := by
      have : Finite D := hD.to_subtype
      exact Finite.of_injective (fun x : D.subgroupOf N => (⟨x.1.1, x.2⟩ : D))
        (by intro x y hxy; have h := congrArg Subtype.val hxy; exact Subtype.ext (Subtype.ext h))
    exact Nat.card_pos.ne'
  have h2 : Nat.card N ≠ 0 := by rw [← hc]; exact mul_ne_zero h1 hDN
  have : Finite N := (Nat.card_ne_zero.mp h2).2
  exact Set.toFinite _

/-- Intersections of commensurated subgroups are commensurated. -/
theorem IsCommensurated.inf {A B : Subgroup G} (hA : IsCommensurated A) (hB : IsCommensurated B) :
    IsCommensurated (A ⊓ B) := by
  intro g
  have e : ConjAct.toConjAct g • (A ⊓ B) =
      (ConjAct.toConjAct g • A) ⊓ (ConjAct.toConjAct g • B) := by
    ext x; simp only [mem_inf, mem_conjAct_smul_iff]
  rw [e]
  constructor
  · -- `(gA ∩ gB) ∩ (A ∩ B)` has finite index in `A ∩ B`
    have h1' : ((ConjAct.toConjAct g • A) ⊓ (ConjAct.toConjAct g • B)).relIndex (A ⊓ B) ≠ 0 := by
      have hA' : (ConjAct.toConjAct g • A).relIndex (A ⊓ B) ≠ 0 :=
        fun h => (hA g).1 (relIndex_eq_zero_of_le_right inf_le_left h)
      have hB' : (ConjAct.toConjAct g • B).relIndex (A ⊓ B) ≠ 0 :=
        fun h => (hB g).1 (relIndex_eq_zero_of_le_right inf_le_right h)
      exact relIndex_inf_ne_zero hA' hB'
    exact h1'
  · have hA' : A.relIndex ((ConjAct.toConjAct g • A) ⊓ (ConjAct.toConjAct g • B)) ≠ 0 :=
      fun h => (hA g).2 (relIndex_eq_zero_of_le_right inf_le_left h)
    have hB' : B.relIndex ((ConjAct.toConjAct g • A) ⊓ (ConjAct.toConjAct g • B)) ≠ 0 :=
      fun h => (hB g).2 (relIndex_eq_zero_of_le_right inf_le_right h)
    exact relIndex_inf_ne_zero hA' hB'

end General

/-- Conjugation commutes with `subgroupOf`. -/
theorem conj_subgroupOf {A : Type*} [Group A] {Γ' N : Subgroup A} (g : Γ') :
    ConjAct.toConjAct g • N.subgroupOf Γ' = (ConjAct.toConjAct (g : A) • N).subgroupOf Γ' := by
  ext x
  rw [mem_conjAct_smul_iff, mem_subgroupOf, mem_subgroupOf, mem_conjAct_smul_iff]
  simp

theorem isCommensurated_subgroupOf {A : Type*} [Group A] {Γ' N : Subgroup A} (hN : N ≤ Γ')
    (hc : Γ' ≤ Commensurable.commensurator N) : IsCommensurated (N.subgroupOf Γ') := by
  intro g
  have hg := hc g.2
  rw [Commensurable.commensurator_mem_iff] at hg
  have hle : ConjAct.toConjAct (g : A) • N ≤ Γ' := by
    intro x hx
    rw [mem_conjAct_smul_iff] at hx
    have := Γ'.mul_mem (Γ'.mul_mem g.2 (hN hx)) (Γ'.inv_mem g.2)
    simpa [mul_assoc] using this
  rw [conj_subgroupOf]
  exact ⟨by rw [relIndex_subgroupOf hN]; exact hg.1, by rw [relIndex_subgroupOf hle]; exact hg.2⟩

theorem finite_subgroupOf_iff {A : Type*} [Group A] {Γ' N : Subgroup A} (hN : N ≤ Γ') :
    ((N.subgroupOf Γ' : Subgroup Γ') : Set Γ').Finite ↔ (N : Set A).Finite := by
  constructor
  · intro h
    have : (N : Set A) = Subtype.val '' ((N.subgroupOf Γ' : Subgroup Γ') : Set Γ') := by
      ext x; constructor
      · intro hx; exact ⟨⟨x, hN hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact hy
    rw [this]; exact h.image _
  · intro h
    rw [Subgroup.coe_subgroupOf]
    exact h.preimage Subtype.val_injective.injOn

end MzSl2
