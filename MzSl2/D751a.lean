import Mathlib
import MzSl2.D751Help

/-!
# Fact d751, step 1: compact root closures and their comparison kernels lie in `M_g`

`L ≤ SL₂(ℤ)` commensurated with `u(m), v(m) ∈ L`; `H = Γ//L`, `q : H → Γ//Λ` the fibre map,
`g = ρ(d)`. `C₊ = closure ⟨ρ(u(1))⟩` and `C₋ = closure ⟨ρ(v(1))⟩` are compact, and
`C_± ∩ ker q ⊆ M_g`.

This replaces the pro-`p` splitting of 801/d751: if `z ∈ C₊` and `q z = 1` then `z` is a limit of
`ρ(u(n))` with `p^{2N} ∣ n` (stabiliser of the coset `d^N Λ`), so `g^{-N} z g^N ∈ C₊`.
-/

open Matrix Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime] {L : Subgroup (Γ p)}

/-- `C₊ = closure ⟨ρ(u(1))⟩`. -/
noncomputable def Cp (L : Subgroup (Γ p)) : Subgroup (Hc L) :=
  (zpowers (ρH L (uΓ 1 R_one))).topologicalClosure

/-- `C₋ = closure ⟨ρ(v(1))⟩`. -/
noncomputable def Cm (L : Subgroup (Γ p)) : Subgroup (Hc L) :=
  (zpowers (ρH L (vΓ 1 R_one))).topologicalClosure

theorem ρ_uZ_mem_zpowers (n : ℤ) : ρH L (uZ n) ∈ zpowers (ρH L (uΓ 1 R_one)) :=
  ⟨n, by simp only [uZ_eq_zpow, map_zpow]⟩

theorem ρ_vZ_mem_zpowers (n : ℤ) : ρH L (vZ n) ∈ zpowers (ρH L (vΓ 1 R_one)) :=
  ⟨n, by simp only [vZ_eq_zpow, map_zpow]⟩

theorem mem_zpowers_u {x : Hc L} (hx : x ∈ zpowers (ρH L (uΓ 1 R_one))) :
    ∃ n : ℤ, x = ρH L (uZ n) := by
  obtain ⟨n, rfl⟩ := hx; exact ⟨n, by simp only [uZ_eq_zpow, map_zpow]⟩

theorem mem_zpowers_v {x : Hc L} (hx : x ∈ zpowers (ρH L (vΓ 1 R_one))) :
    ∃ n : ℤ, x = ρH L (vZ n) := by
  obtain ⟨n, rfl⟩ := hx; exact ⟨n, by simp only [vZ_eq_zpow, map_zpow]⟩

/-- A cyclic subgroup with a power in `L` has compact closure. -/
theorem isCompact_closure_zpowers (hLc : IsCommensurated L) {a : Γ p} {m : ℕ} (hm : 0 < m)
    (ham : a ^ (m : ℤ) ∈ L) :
    IsCompact ((zpowers (ρH L a)).topologicalClosure : Set (Hc L)) := by
  set S : Set (Hc L) := ⋃ i ∈ Finset.range m, (fun y => ρH L (a ^ (i : ℤ)) * y) '' (UH L : Set _)
  have hS : IsCompact S := (Finset.range m).isCompact_biUnion fun i _ =>
    (isCompact_UH L hLc).image (continuous_const.mul continuous_id)
  refine hS.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
  rw [Subgroup.topologicalClosure_coe]
  refine closure_minimal ?_ hS.isClosed
  rintro _ ⟨n, rfl⟩
  show ρH L a ^ n ∈ S
  have hdiv := Int.emod_add_mul_ediv n m
  have hmod0 : 0 ≤ n % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have hmodlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  refine Set.mem_biUnion (x := (n % (m : ℤ)).toNat) (Finset.mem_range.mpr (by omega)) ?_
  refine ⟨ρH L (a ^ (m : ℤ)) ^ (n / (m : ℤ)), ?_, ?_⟩
  · exact (UH L).zpow_mem ((ρH_mem_UH_iff L _).mpr ham) _
  · simp only [← map_zpow, ← map_mul]
    show ρH L (a ^ ((n % (m : ℤ)).toNat : ℤ) * (a ^ (m : ℤ)) ^ (n / (m : ℤ))) = ρH L (a ^ n)
    rw [← _root_.zpow_mul, ← _root_.zpow_add, Int.toNat_of_nonneg hmod0]
    congr 2

theorem isCompact_Cp (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m) (hu : uZ (m : ℤ) ∈ L) :
    IsCompact (Cp L : Set (Hc L)) :=
  isCompact_closure_zpowers hLc hm (by rw [← uZ_eq_zpow]; exact hu)

theorem isCompact_Cm (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m) (hv : vZ (m : ℤ) ∈ L) :
    IsCompact (Cm L : Set (Hc L)) :=
  isCompact_closure_zpowers hLc hm (by rw [← vZ_eq_zpow]; exact hv)

/-! ### Conjugation by powers of `g = ρ(d)` -/

theorem conj_closure_subset {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (x : H) {A B : Set H} (hAB : ∀ a ∈ A, x * a * x⁻¹ ∈ B) {z : H} (hz : z ∈ _root_.closure A) :
    x * z * x⁻¹ ∈ _root_.closure B :=
  map_mem_closure (f := fun y => x * y * x⁻¹) (by fun_prop) hz hAB

theorem g_pow_conj_Cp (N : ℕ) {z : Hc L} (hz : z ∈ Cp L) :
    ρH L (dγ p) ^ N * z * (ρH L (dγ p) ^ N)⁻¹ ∈ Cp L := by
  have hz' : z ∈ _root_.closure (zpowers (ρH L (uΓ 1 R_one)) : Set (Hc L)) := hz
  show _ ∈ ((zpowers (ρH L (uΓ 1 R_one))).topologicalClosure : Set (Hc L))
  rw [Subgroup.topologicalClosure_coe]
  refine conj_closure_subset _ (fun a ha => ?_) hz'
  obtain ⟨n, rfl⟩ := mem_zpowers_u ha
  rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, dγ_pow_conj_u']
  have : uΓ ((p : ℚ) ^ (2 * N) * (n : ℚ)) ((R p).mul_mem (R_pow_mem _) (intCast_mem (R p) n)) =
      uZ ((p : ℤ) ^ (2 * N) * n) := by
    apply mat_injective; simp
  rw [this]; exact ρ_uZ_mem_zpowers _

theorem g_pow_inv_conj_Cm (N : ℕ) {z : Hc L} (hz : z ∈ Cm L) :
    (ρH L (dγ p) ^ N)⁻¹ * z * (ρH L (dγ p) ^ N) ∈ Cm L := by
  have hz' : z ∈ _root_.closure (zpowers (ρH L (vΓ 1 R_one)) : Set (Hc L)) := hz
  show _ ∈ ((zpowers (ρH L (vΓ 1 R_one))).topologicalClosure : Set (Hc L))
  rw [Subgroup.topologicalClosure_coe]
  have := conj_closure_subset (ρH L (dγ p) ^ N)⁻¹ (B := (zpowers (ρH L (vΓ 1 R_one)) : Set _))
    (fun a ha => ?_) hz'
  · simpa using this
  obtain ⟨n, rfl⟩ := mem_zpowers_v ha
  rw [inv_inv, ← map_pow, ← map_inv, ← map_mul, ← map_mul, dγ_pow_conj_v']
  have : vΓ ((p : ℚ) ^ (2 * N) * (n : ℚ)) ((R p).mul_mem (R_pow_mem _) (intCast_mem (R p) n)) =
      vZ ((p : ℤ) ^ (2 * N) * n) := by
    apply mat_injective; simp
  rw [this]; exact ρ_vZ_mem_zpowers _

/-! ### Elements of `C_± ∩ ker q` -/

variable (hL : L ≤ Λp p)

theorem qmap_ρH_stab (γ h : Γ p) :
    ((qmap hL (ρH L γ) : Hc (Λp p)) : Sym (Cosets (Λp p))) ∈ Sym.stab (Cosets.mk (Λp p) h) ↔
      h⁻¹ * γ * h ∈ Λp p := by
  rw [qmap_ρH, ρH_coe]; exact ρ_mem_stab_mk_iff _ γ h

/-- If `z ∈ C₊` and `q z = 1`, then `z` lies in the closure of `ρ(u(p^{2N} ℤ))`. -/
theorem mem_closure_u_pow (N : ℕ) {z : Hc L} (hz : z ∈ Cp L) (hq : qmap hL z = 1) :
    z ∈ _root_.closure ((fun k : ℤ => ρH L (uZ ((p : ℤ) ^ (2 * N) * k))) '' univ) := by
  set W : Set (Hc L) := (fun σ : Hc L => ((qmap hL σ : Hc (Λp p)) : Sym (Cosets (Λp p)))) ⁻¹'
    (Sym.stab (Cosets.mk (Λp p) (dγ p ^ N)) : Set _)
  have hW : IsOpen W := (Sym.isOpen_stab _).preimage
    (continuous_subtype_val.comp (continuous_qmap hL))
  have hzW : z ∈ W := by
    simp only [W, Set.mem_preimage, SetLike.mem_coe]
    rw [hq]; exact (Sym.stab _).one_mem
  have hz' : z ∈ _root_.closure (zpowers (ρH L (uΓ 1 R_one)) : Set (Hc L)) := hz
  rw [mem_closure_iff] at hz' ⊢
  intro o ho hzo
  obtain ⟨_, ⟨hxo, hxW⟩, hx⟩ := hz' (o ∩ W) (ho.inter hW) ⟨hzo, hzW⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_u hx
  have hst := (qmap_ρH_stab hL (uZ n) (dγ p ^ N)).mp hxW
  obtain ⟨k, hk⟩ := dvd_of_conj_u_mem N n hst
  refine ⟨ρH L (uZ n), hxo, k, trivial, ?_⟩
  rw [hk]

theorem mem_closure_v_pow (N : ℕ) {z : Hc L} (hz : z ∈ Cm L) (hq : qmap hL z = 1) :
    z ∈ _root_.closure ((fun k : ℤ => ρH L (vZ ((p : ℤ) ^ (2 * N) * k))) '' univ) := by
  set W : Set (Hc L) := (fun σ : Hc L => ((qmap hL σ : Hc (Λp p)) : Sym (Cosets (Λp p)))) ⁻¹'
    (Sym.stab (Cosets.mk (Λp p) (dγ p ^ N)⁻¹) : Set _)
  have hW : IsOpen W := (Sym.isOpen_stab _).preimage
    (continuous_subtype_val.comp (continuous_qmap hL))
  have hzW : z ∈ W := by
    simp only [W, Set.mem_preimage, SetLike.mem_coe]
    rw [hq]; exact (Sym.stab _).one_mem
  have hz' : z ∈ _root_.closure (zpowers (ρH L (vΓ 1 R_one)) : Set (Hc L)) := hz
  rw [mem_closure_iff] at hz' ⊢
  intro o ho hzo
  obtain ⟨_, ⟨hxo, hxW⟩, hx⟩ := hz' (o ∩ W) (ho.inter hW) ⟨hzo, hzW⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_v hx
  have hst := (qmap_ρH_stab hL (vZ n) (dγ p ^ N)⁻¹).mp hxW
  rw [inv_inv] at hst
  obtain ⟨k, hk⟩ := dvd_of_conj_v_mem N n hst
  refine ⟨ρH L (vZ n), hxo, k, trivial, ?_⟩
  rw [hk]

/-- **d751 (1).** `C₊ ∩ ker q ⊆ M_g`. -/
theorem levi_of_Cp (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m) (hu : uZ (m : ℤ) ∈ L)
    {z : Hc L} (hz : z ∈ Cp L) (hq : qmap hL z = 1) : z ∈ levi (ρH L (dγ p)) := by
  refine levi_of_subset_compact (isCompact_Cp hLc hm hu) fun n => ?_
  rcases n with N | N
  · simpa using g_pow_conj_Cp N hz
  · -- negative powers: use the closure of `ρ(u(p^{2(N+1)} ℤ))`
    have hcl := mem_closure_u_pow hL (N + 1) hz hq
    have := conj_closure_subset (ρH L (dγ p) ^ (N + 1))⁻¹
      (A := (fun k : ℤ => ρH L (uZ ((p : ℤ) ^ (2 * (N + 1)) * k))) '' univ)
      (B := (zpowers (ρH L (uΓ 1 R_one)) : Set (Hc L))) (fun a ha => ?_) hcl
    · have e : ρH L (dγ p) ^ Int.negSucc N * z * ρH L (dγ p) ^ (-Int.negSucc N) =
          (ρH L (dγ p) ^ (N + 1))⁻¹ * z * (ρH L (dγ p) ^ (N + 1))⁻¹⁻¹ := by
        rw [zpow_negSucc, Int.neg_negSucc, inv_inv]; norm_cast
      rw [e]
      show _ ∈ ((zpowers (ρH L (uΓ 1 R_one))).topologicalClosure : Set (Hc L))
      rw [Subgroup.topologicalClosure_coe]; exact this
    obtain ⟨k, -, rfl⟩ := ha
    rw [inv_inv, ← map_pow, ← map_inv, ← map_mul, ← map_mul, dγ_pow_conj_u]
    have : uΓ ((((p : ℤ) ^ (2 * (N + 1)) * k : ℤ) : ℚ) / (p : ℚ) ^ (2 * (N + 1)))
        (R_div_pow (intCast_mem (R p) _) _) = uZ k := by
      have hp0 : (p : ℚ) ^ (2 * (N + 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      apply mat_injective; simp only [mat_uΓ]; congr 1; push_cast
      field_simp
    rw [this]; exact ρ_uZ_mem_zpowers _

/-- **d751 (1).** `C₋ ∩ ker q ⊆ M_g`. -/
theorem levi_of_Cm (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m) (hv : vZ (m : ℤ) ∈ L)
    {z : Hc L} (hz : z ∈ Cm L) (hq : qmap hL z = 1) : z ∈ levi (ρH L (dγ p)) := by
  refine levi_of_subset_compact (isCompact_Cm hLc hm hv) fun n => ?_
  rcases n with N | N
  · -- nonnegative powers: use the closure of `ρ(v(p^{2N} ℤ))`
    have hcl := mem_closure_v_pow hL N hz hq
    have := conj_closure_subset (ρH L (dγ p) ^ N)
      (A := (fun k : ℤ => ρH L (vZ ((p : ℤ) ^ (2 * N) * k))) '' univ)
      (B := (zpowers (ρH L (vΓ 1 R_one)) : Set (Hc L))) (fun a ha => ?_) hcl
    · have e : ρH L (dγ p) ^ (Int.ofNat N) * z * ρH L (dγ p) ^ (-(Int.ofNat N)) =
          ρH L (dγ p) ^ N * z * (ρH L (dγ p) ^ N)⁻¹ := by
        simp
      rw [e]
      show _ ∈ ((zpowers (ρH L (vΓ 1 R_one))).topologicalClosure : Set (Hc L))
      rw [Subgroup.topologicalClosure_coe]; exact this
    obtain ⟨k, -, rfl⟩ := ha
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, dγ_pow_conj_v]
    have : vΓ ((((p : ℤ) ^ (2 * N) * k : ℤ) : ℚ) / (p : ℚ) ^ (2 * N))
        (R_div_pow (intCast_mem (R p) _) _) = vZ k := by
      have hp0 : (p : ℚ) ^ (2 * N) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      apply mat_injective; simp only [mat_vΓ]; congr 1; push_cast
      field_simp
    rw [this]; exact ρ_vZ_mem_zpowers _
  · have := g_pow_inv_conj_Cm (N + 1) hz
    have e : ρH L (dγ p) ^ Int.negSucc N * z * ρH L (dγ p) ^ (-Int.negSucc N) =
        (ρH L (dγ p) ^ (N + 1))⁻¹ * z * (ρH L (dγ p) ^ (N + 1)) := by
      rw [zpow_negSucc, Int.neg_negSucc]; norm_cast
    rw [e]; exact this

end MzSl2
