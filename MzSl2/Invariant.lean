import Mathlib
import MzSl2.GammaElems
import MzSl2.ScaleLemmas

/-!
# Fact c627 (core): uniscalar diagonal gives a `Γ`-invariant compact open subgroup

Let `σ : Γ → H` be a homomorphism to a tdlc group. If `σ(d)` normalises a compact open
subgroup, then some compact open subgroup is normalised by all of `σ(Γ)`.

Proof (c627): upper and lower unipotents are infinitely `p`-divisible, so they normalise compact
open subgroups (scale axioms). Every element of `Γ` is a product of at most 27 powers of
`d, u(1), v(1)` (bounded generation). The multiplicative index distance
`D(A,B) = [B : A ∩ B][A : A ∩ B]` is submultiplicative and conjugation invariant, which bounds
`[V : V ∩ γVγ⁻¹]` uniformly; Bergman–Lenstra and a closure argument finish.
-/

open Topology Set Subgroup Matrix
open scoped Pointwise

namespace MzSl2

section Distance

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Multiplicative index distance between commensurable subgroups. -/
noncomputable def D (A B : Subgroup H) : ℕ := A.relIndex B * B.relIndex A

theorem D_comm (A B : Subgroup H) : D A B = D B A := by rw [D, D, mul_comm]

theorem D_self (A : Subgroup H) : D A A = 1 := by simp [D]

theorem D_smul (x : H) (A B : Subgroup H) :
    D (ConjAct.toConjAct x • A) (ConjAct.toConjAct x • B) = D A B := by
  rw [D, D, Subgroup.relIndex_pointwise_smul, Subgroup.relIndex_pointwise_smul]

theorem relIndex_tri {A B C : Subgroup H} (hA : IsCompactOpenSubgroup A)
    (hB : IsCompactOpenSubgroup B) (hC : IsCompactOpenSubgroup C) :
    C.relIndex A ≤ C.relIndex B * B.relIndex A := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex C B A
  have hCB : (C ⊓ B).relIndex A ≠ 0 :=
    relIndex_ne_zero_of_isOpen_of_isCompact (hC.2.inter hB.2) hA.1
  have h2 : C.relIndex A ≤ (C ⊓ B).relIndex A := relIndex_le_of_le_left inf_le_left hCB
  have h3 : C.relIndex (B ⊓ A) ≤ C.relIndex B :=
    relIndex_le_of_le_right inf_le_left (hC.relIndex_ne_zero hB)
  calc C.relIndex A ≤ (C ⊓ B).relIndex A := h2
    _ = C.relIndex (B ⊓ A) * B.relIndex A := h1.symm
    _ ≤ C.relIndex B * B.relIndex A := Nat.mul_le_mul_right _ h3

theorem D_tri {A B C : Subgroup H} (hA : IsCompactOpenSubgroup A)
    (hB : IsCompactOpenSubgroup B) (hC : IsCompactOpenSubgroup C) :
    D A C ≤ D A B * D B C := by
  have h1 := relIndex_tri hA hB hC
  have h2 := relIndex_tri hC hB hA
  calc D A C = A.relIndex C * C.relIndex A := rfl
    _ ≤ (A.relIndex B * B.relIndex C) * (C.relIndex B * B.relIndex A) := Nat.mul_le_mul h2 h1
    _ = D A B * D B C := by simp only [D]; ring

theorem D_mul {V : Subgroup H} (hV : IsCompactOpenSubgroup V) (x y : H) :
    D V (ConjAct.toConjAct (x * y) • V) ≤
      D V (ConjAct.toConjAct x • V) * D V (ConjAct.toConjAct y • V) := by
  have hxy : ConjAct.toConjAct (x * y) • V = ConjAct.toConjAct x • ConjAct.toConjAct y • V := by
    rw [map_mul, mul_smul]
  rw [hxy]
  calc _ ≤ D V (ConjAct.toConjAct x • V) *
        D (ConjAct.toConjAct x • V) (ConjAct.toConjAct x • ConjAct.toConjAct y • V) :=
      D_tri hV (hV.conj x) ((hV.conj y).conj x)
    _ = _ := by rw [D_smul]

theorem D_of_normalizes {V L : Subgroup H} (hV : IsCompactOpenSubgroup V)
    (hL : IsCompactOpenSubgroup L) {x : H} (hx : ConjAct.toConjAct x • L = L) :
    D V (ConjAct.toConjAct x • V) ≤ D V L ^ 2 := by
  calc D V (ConjAct.toConjAct x • V) ≤ D V L * D L (ConjAct.toConjAct x • V) :=
        D_tri hV hL (hV.conj x)
    _ = D V L * D (ConjAct.toConjAct x • L) (ConjAct.toConjAct x • V) := by rw [hx]
    _ = D V L ^ 2 := by rw [D_smul, D_comm L V, sq]

theorem D_list_prod {V : Subgroup H} (hV : IsCompactOpenSubgroup V) (M : ℕ) (hM : 1 ≤ M)
    (l : List H) (hl : ∀ x ∈ l, D V (ConjAct.toConjAct x • V) ≤ M) :
    D V (ConjAct.toConjAct l.prod • V) ≤ M ^ l.length := by
  induction l with
  | nil => simp [D_self]
  | cons a l ih =>
    rw [List.prod_cons, List.length_cons, pow_succ']
    calc _ ≤ D V (ConjAct.toConjAct a • V) * D V (ConjAct.toConjAct l.prod • V) := D_mul hV a _
      _ ≤ M * M ^ l.length :=
        Nat.mul_le_mul (hl a (List.mem_cons_self ..))
          (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem normalizes_zpow {L : Subgroup H} {x : H} (hx : ConjAct.toConjAct x • L = L) (j : ℤ) :
    ConjAct.toConjAct (x ^ j) • L = L := by
  have : ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct H) L := hx
  have h2 := zpow_mem this j
  rw [← map_zpow] at h2
  exact h2

end Distance

section Closure

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

/-- Conjugation as a homeomorphism. -/
def conjHomeo (b : H) : H ≃ₜ H := (Homeomorph.mulLeft b).trans (Homeomorph.mulRight b⁻¹)

theorem conjHomeo_apply (b x : H) : conjHomeo b x = b * x * b⁻¹ := rfl

/-- If `J` is commensurable with a compact open subgroup then its closure is compact open. -/
theorem closure_isCompactOpen {V J : Subgroup H} (hV : IsCompactOpenSubgroup V)
    (hJ : Commensurable J V) : IsCompactOpenSubgroup J.topologicalClosure := by
  constructor
  · -- `J ⊆ S V` for a finite set `S`
    haveI : (V.subgroupOf J).FiniteIndex := ⟨hJ.2⟩
    let S : Set H := Set.range fun q : J ⧸ V.subgroupOf J => ((q.out : J) : H)
    have hS : S.Finite := Set.finite_range _
    have hcpt : IsCompact (S * (V : Set H)) := hS.isCompact.mul hV.1
    refine hcpt.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
    rw [Subgroup.topologicalClosure_coe]
    refine closure_minimal ?_ hcpt.isClosed
    intro j hj
    obtain ⟨h, he⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf J) (⟨j, hj⟩ : J)
    refine Set.mem_mul.mpr ⟨_, ⟨QuotientGroup.mk ⟨j, hj⟩, rfl⟩, (((h : J) : H))⁻¹,
      V.inv_mem (Subgroup.mem_subgroupOf.mp h.2), ?_⟩
    have := congrArg Subtype.val he
    simp only [Subgroup.coe_mul] at this
    show ((Quotient.out (QuotientGroup.mk ⟨j, hj⟩ : J ⧸ V.subgroupOf J) : J) : H) * _ = j
    rw [this]; group
  · -- the closure of `J ⊓ V` is open
    let K : Subgroup H := (J ⊓ V).topologicalClosure
    have hKV : K ≤ V := Subgroup.topologicalClosure_minimal _ inf_le_right
      (Subgroup.isClosed_of_isOpen _ hV.2)
    have hfi : (K.subgroupOf V).index ≠ 0 := by
      have h1 : (J ⊓ V).relIndex V ≠ 0 := by rw [Subgroup.inf_relIndex_right]; exact hJ.1
      exact ne_zero_of_dvd_ne_zero h1 (relIndex_dvd_of_le_left V
        (Subgroup.le_topologicalClosure _))
    haveI : (K.subgroupOf V).FiniteIndex := ⟨hfi⟩
    have hcl : IsClosed ((K.subgroupOf V : Subgroup V) : Set V) :=
      (Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val
    have hopen := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
    have hKo : IsOpen (K : Set H) := by
      have := hV.2.isOpenMap_subtype_val _ hopen
      convert this using 1
      ext x; constructor
      · intro hx; exact ⟨⟨x, hKV hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact hy
    exact Subgroup.isOpen_mono (Subgroup.topologicalClosure_mono inf_le_left) hKo

theorem topologicalClosure_normalized {J : Subgroup H} {b : H}
    (hb : ConjAct.toConjAct b • J = J) :
    ConjAct.toConjAct b • J.topologicalClosure = J.topologicalClosure := by
  apply SetLike.coe_injective
  rw [coe_conj_smul', Subgroup.topologicalClosure_coe]
  have h := (conjHomeo b).image_closure (J : Set H)
  have hf : ⇑(conjHomeo b) = fun x => b * x * b⁻¹ := rfl
  rw [hf] at h
  rw [h, ← coe_conj_smul', hb]

end Closure

variable (p : ℕ) [hp : Fact p.Prime]

/-- Every element of `Γ` is a product of at most 9 elementary elements of `Γ`. -/
theorem bounded_generation_Γ (g : Γ p) :
    ∃ l : List (Γ p), l.length ≤ 9 ∧
      (∀ x ∈ l, ∃ a, ∃ ha : a ∈ R p, x = uΓ a ha ∨ x = vΓ a ha) ∧ l.prod = g := by
  obtain ⟨lm, hlen, hel, hprod⟩ := bounded_generation p g g.2
  have key : ∀ lm : List (Matrix (Fin 2) (Fin 2) ℚ),
      (∀ m ∈ lm, ∃ a ∈ R p, m = u a ∨ m = v a) →
      ∃ lg : List (Γ p), lg.map (mat p) = lm ∧
        ∀ x ∈ lg, ∃ a, ∃ ha : a ∈ R p, x = uΓ a ha ∨ x = vΓ a ha := by
    intro lm hlm
    induction lm with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons m lm ih =>
      obtain ⟨lg, hlg, hlg'⟩ := ih fun x hx => hlm x (List.mem_cons_of_mem _ hx)
      obtain ⟨a, ha, hm⟩ := hlm m (List.mem_cons_self ..)
      rcases hm with rfl | rfl
      · refine ⟨uΓ a ha :: lg, by simp [hlg], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨a, ha, Or.inl rfl⟩
        · exact hlg' x hx
      · refine ⟨vΓ a ha :: lg, by simp [hlg], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨a, ha, Or.inr rfl⟩
        · exact hlg' x hx
  obtain ⟨lg, hlg, hlg'⟩ := key lm hel
  refine ⟨lg, by rw [← hlg, List.length_map] at hlen; exact hlen, hlg', ?_⟩
  apply mat_injective
  rw [mat_list_prod, hlg]
  exact hprod

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [TotallyDisconnectedSpace H] [LocallyCompactSpace H]

/-- **c627 (a) ⇒ (c).** If `σ(d)` normalises a compact open subgroup, some compact open subgroup
is normalised by every `σ(γ)`. -/
theorem exists_invariant_compactOpen (σ : Γ p →* H)
    (hd : ∃ V : Subgroup H, IsCompactOpenSubgroup V ∧ ConjAct.toConjAct (σ (dγ p)) • V = V) :
    ∃ W : Subgroup H, IsCompactOpenSubgroup W ∧ ∀ γ : Γ p, ConjAct.toConjAct (σ γ) • W = W := by
  obtain ⟨Ld, hLd, hLdn⟩ := hd
  have hex : ∃ V : Subgroup H, IsCompactOpenSubgroup V := ⟨Ld, hLd⟩
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨Lu, hLu, hLun⟩ := exists_normalized_of_divisible hex hp2 (h := σ (uΓ 1 R_one)) (by
    intro r; obtain ⟨k, hk⟩ := uΓ_divisible (p := p) 1 R_one r
    exact ⟨σ k, by rw [← map_pow, hk]⟩)
  obtain ⟨Lv, hLv, hLvn⟩ := exists_normalized_of_divisible hex hp2 (h := σ (vΓ 1 R_one)) (by
    intro r; obtain ⟨k, hk⟩ := vΓ_divisible (p := p) 1 R_one r
    exact ⟨σ k, by rw [← map_pow, hk]⟩)
  set V := Ld
  set M := max (max (D V Ld ^ 2) (D V Lu ^ 2)) (max (D V Lv ^ 2) 1)
  have hM1 : 1 ≤ M := le_max_of_le_right (le_max_right _ _)
  have hMd : ∀ j : ℤ, D V (ConjAct.toConjAct (σ (dγ p) ^ j) • V) ≤ M := fun j =>
    (D_of_normalizes hLd hLd (normalizes_zpow hLdn j)).trans
      (le_max_of_le_left (le_max_left _ _))
  have hMu : ∀ j : ℤ, D V (ConjAct.toConjAct (σ (uΓ 1 R_one) ^ j) • V) ≤ M := fun j =>
    (D_of_normalizes hLd hLu (normalizes_zpow hLun j)).trans
      (le_max_of_le_left (le_max_right _ _))
  have hMv : ∀ j : ℤ, D V (ConjAct.toConjAct (σ (vΓ 1 R_one) ^ j) • V) ≤ M := fun j =>
    (D_of_normalizes hLd hLv (normalizes_zpow hLvn j)).trans
      (le_max_of_le_right (le_max_left _ _))
  -- each elementary element costs at most `M^3`
  have helem : ∀ x : Γ p, (∃ a, ∃ ha : a ∈ R p, x = uΓ a ha ∨ x = vΓ a ha) →
      D V (ConjAct.toConjAct (σ x) • V) ≤ M ^ 3 := by
    rintro x ⟨a, ha, rfl | rfl⟩
    · obtain ⟨r, b, hrb⟩ := uΓ_eq_conj a ha
      have e : σ (uΓ a ha) = σ (dγ p) ^ (-(r : ℤ)) * σ (uΓ 1 R_one) ^ b * σ (dγ p) ^ (r : ℤ) := by
        rw [hrb, map_mul, map_mul, map_inv, map_zpow, map_pow, _root_.zpow_neg, zpow_natCast]
      rw [e]
      calc _ ≤ D V (ConjAct.toConjAct (σ (dγ p) ^ (-(r : ℤ)) * σ (uΓ 1 R_one) ^ b) • V) *
            D V (ConjAct.toConjAct (σ (dγ p) ^ (r : ℤ)) • V) := D_mul hLd _ _
        _ ≤ (D V (ConjAct.toConjAct (σ (dγ p) ^ (-(r : ℤ))) • V) *
              D V (ConjAct.toConjAct (σ (uΓ 1 R_one) ^ b) • V)) *
            D V (ConjAct.toConjAct (σ (dγ p) ^ (r : ℤ)) • V) :=
          Nat.mul_le_mul_right _ (D_mul hLd _ _)
        _ ≤ (M * M) * M := Nat.mul_le_mul (Nat.mul_le_mul (hMd _) (hMu _)) (hMd _)
        _ = M ^ 3 := by ring
    · obtain ⟨r, b, hrb⟩ := vΓ_eq_conj a ha
      have e : σ (vΓ a ha) = σ (dγ p) ^ (r : ℤ) * σ (vΓ 1 R_one) ^ b * σ (dγ p) ^ (-(r : ℤ)) := by
        rw [hrb, map_mul, map_mul, map_inv, map_zpow, map_pow, _root_.zpow_neg, zpow_natCast]
      rw [e]
      calc _ ≤ D V (ConjAct.toConjAct (σ (dγ p) ^ (r : ℤ) * σ (vΓ 1 R_one) ^ b) • V) *
            D V (ConjAct.toConjAct (σ (dγ p) ^ (-(r : ℤ))) • V) := D_mul hLd _ _
        _ ≤ (D V (ConjAct.toConjAct (σ (dγ p) ^ (r : ℤ)) • V) *
              D V (ConjAct.toConjAct (σ (vΓ 1 R_one) ^ b) • V)) *
            D V (ConjAct.toConjAct (σ (dγ p) ^ (-(r : ℤ))) • V) :=
          Nat.mul_le_mul_right _ (D_mul hLd _ _)
        _ ≤ (M * M) * M := Nat.mul_le_mul (Nat.mul_le_mul (hMd _) (hMv _)) (hMd _)
        _ = M ^ 3 := by ring
  -- uniform bound over `Γ`
  have hbound : ∀ γ : Γ p, D V (ConjAct.toConjAct (σ γ) • V) ≤ (M ^ 3) ^ 9 := by
    intro γ
    obtain ⟨l, hlen, hel, rfl⟩ := bounded_generation_Γ p γ
    rw [map_list_prod]
    calc _ ≤ (M ^ 3) ^ (l.map σ).length :=
          D_list_prod hLd _ (Nat.one_le_pow _ _ hM1) _ (by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            exact helem y (hel y hy))
      _ ≤ (M ^ 3) ^ 9 := Nat.pow_le_pow_right (Nat.one_le_pow _ _ hM1) (by simpa using hlen)
  -- Bergman–Lenstra
  obtain ⟨J, hJ, hJn⟩ := bergman_lenstra V σ.range ((M ^ 3) ^ 9) (by
    rintro _ ⟨γ, rfl⟩
    refine ⟨(hLd.conj _).relIndex_ne_zero hLd, ?_⟩
    calc (ConjAct.toConjAct (σ γ) • V).relIndex V
        ≤ V.relIndex (ConjAct.toConjAct (σ γ) • V) * (ConjAct.toConjAct (σ γ) • V).relIndex V :=
          Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (hLd.relIndex_ne_zero (hLd.conj _)))
      _ ≤ _ := hbound γ)
  exact ⟨J.topologicalClosure, closure_isCompactOpen hLd hJ,
    fun γ => topologicalClosure_normalized (hJn _ ⟨γ, rfl⟩)⟩

end MzSl2
