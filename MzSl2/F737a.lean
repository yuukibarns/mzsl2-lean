import Mathlib
import MzSl2.FiberMap
import MzSl2.PhiMap
import MzSl2.D751Help

/-!
# Fact 737: the comparison map is open and onto; compact kernel gives finite integral index

`L ≤ Λ` commensurated with `u(m), v(m) ∈ L`; `q : Γ//L → Γ//Λ` the fibre map, `U = U_L`.

* `q(U)` is open (its closure contains `Φ(K(R))`, open by the open mapping theorem and Iwahori);
* `q` is surjective and open;
* if `E = ker q` is compact, then `[Λ : L] < ∞` (737, (2) ⇒ (1)).
-/

open Matrix Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime] {L : Subgroup (Γ p)}

/-- `Hc L` is σ-compact (countably many translates of `U`). -/
theorem sigmaCompact_Hc (hLc : IsCommensurated L) : SigmaCompactSpace (Hc L) := by
  obtain ⟨e, he⟩ := exists_surjective_nat (Γ p)
  refine ⟨⟨fun n => (fun y => ρH L (e n) * y) '' (UH L : Set (Hc L)),
    fun n => (isCompact_UH L hLc).image (continuous_const.mul continuous_id), ?_⟩⟩
  apply Set.eq_univ_of_forall
  intro h
  have hO : IsOpen ((fun y => h⁻¹ * y) ⁻¹' (UH L : Set (Hc L))) :=
    (isOpen_UH L).preimage (continuous_const.mul continuous_id)
  obtain ⟨_, hy, γ, rfl⟩ := (denseRange_ρH L).inter_open_nonempty _ hO
    ⟨h, by simp [(UH L).one_mem]⟩
  obtain ⟨n, rfl⟩ := he γ
  refine Set.mem_iUnion.mpr ⟨n, (ρH L (e n))⁻¹ * h, ?_, by group⟩
  have := (UH L).inv_mem hy
  simpa using this

variable (hL : L ≤ Λp p)

theorem qmap_UH_isOpen (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m)
    (hu : uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    (hv : vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L) :
    IsOpen (((UH L).map (qmap hL)) : Set (Hc (Λp p))) := by
  obtain ⟨R, hR⟩ := Kr_le_closure hm hu hv
  have hΦ : IsOpen (Φ '' (Kr p R : Set (SLp p))) := Φ_isOpenMap _ (isOpen_Kr R)
  have hcpt : IsCompact (((UH L).map (qmap hL)) : Set (Hc (Λp p))) :=
    (isCompact_UH L hLc).image (continuous_qmap hL)
  have hsub : Φ '' (Kr p R : Set (SLp p)) ⊆ ((UH L).map (qmap hL) : Set (Hc (Λp p))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hcl := map_mem_closure continuous_Φ (hR hx)
      (t := ((UH L).map (qmap hL) : Set (Hc (Λp p)))) (by
        rintro _ ⟨l, hl, rfl⟩
        refine ⟨ρH L l, (ρH_mem_UH_iff L l).mpr hl, ?_⟩
        rw [qmap_ρH, Φ_ιΓ])
    exact hcpt.isClosed.closure_subset hcl
  have h1 : (1 : Hc (Λp p)) ∈ Φ '' (Kr p R : Set (SLp p)) := ⟨1, (Kr p R).one_mem, map_one _⟩
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hΦ.mem_nhds h1) hsub)

theorem qmap_surjective (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m)
    (hu : uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    (hv : vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L) :
    Function.Surjective (qmap hL) := by
  have hopen : IsOpen ((qmap hL).range : Set (Hc (Λp p))) :=
    Subgroup.isOpen_mono (Subgroup.map_le_range _ _) (qmap_UH_isOpen hL hLc hm hu hv)
  have hcl : IsClosed ((qmap hL).range : Set (Hc (Λp p))) := Subgroup.isClosed_of_isOpen _ hopen
  have hdense : Dense ((qmap hL).range : Set (Hc (Λp p))) := by
    refine (denseRange_ρH (Λp p)).mono ?_
    rintro _ ⟨γ, rfl⟩; exact ⟨ρH L γ, qmap_ρH hL γ⟩
  intro y
  have : y ∈ ((qmap hL).range : Set (Hc (Λp p))) := by
    rw [← hcl.closure_eq, hdense.closure_eq]; trivial
  exact this

theorem qmap_isOpenMap (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m)
    (hu : uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    (hv : vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L) :
    IsOpenMap (qmap hL) := by
  haveI := sigmaCompact_Hc hLc
  haveI := locallyCompact_Hc (Λp p) Λp_commensurated
  exact (qmap hL).isOpenMap_of_sigmaCompact (qmap_surjective hL hLc hm hu hv) (continuous_qmap hL)

/-- **737, (2) ⇒ (1).** If the comparison kernel is compact, `[Λ : L] < ∞`. -/
theorem relIndex_ne_zero_of_ker_compact (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m)
    (hu : uΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    (hv : vΓ (p := p) (m : ℚ) (by exact_mod_cast intCast_mem (R p) (m : ℤ)) ∈ L)
    (hE : IsCompact ((qmap hL).ker : Set (Hc L))) :
    L.relIndex (Λp p) ≠ 0 := by
  haveI := locallyCompact_Hc L hLc
  set q := qmap hL
  set U := UH L
  set qU := U.map q
  set B := (UH (Λp p)).comap q
  set EU := qU.comap q
  have hqUo : IsOpen (qU : Set (Hc (Λp p))) := qmap_UH_isOpen hL hLc hm hu hv
  -- `EU = E · U` is compact
  have hEU : IsCompact (EU : Set (Hc L)) := by
    have hcpt : IsCompact ((q.ker : Set (Hc L)) * (U : Set (Hc L))) :=
      hE.mul (isCompact_UH L hLc)
    refine hcpt.of_isClosed_subset ?_ ?_
    · exact ((isCompact_UH L hLc).image (continuous_qmap hL)).isClosed.preimage (continuous_qmap hL)
    · rintro x ⟨u, hu', hxu⟩
      refine Set.mem_mul.mpr ⟨x * u⁻¹, ?_, u, hu', by group⟩
      show q (x * u⁻¹) = 1
      rw [map_mul, map_inv, ← hxu, mul_inv_cancel]
  have h1 : U.relIndex EU ≠ 0 := relIndex_ne_zero_of_isOpen_of_isCompact (isOpen_UH L) hEU
  have h2 : EU.relIndex B ≠ 0 := by
    rw [relIndex_comap]
    have : qU.relIndex (UH (Λp p)) ≠ 0 :=
      relIndex_ne_zero_of_isOpen_of_isCompact hqUo (isCompact_UH _ Λp_commensurated)
    exact relIndex_ne_zero_of_le_right' (map_comap_le _ _) this
  have h3 : U.relIndex B ≠ 0 := relIndex_ne_zero_trans h1 h2
  have hL' : L = U.comap (ρH L) := by ext x; exact (ρH_mem_UH_iff L x).symm
  rw [hL', relIndex_comap]
  refine relIndex_ne_zero_of_le_right' ?_ h3
  rintro _ ⟨l, hl, rfl⟩
  show q (ρH L l) ∈ UH (Λp p)
  rw [qmap_ρH]; exact (ρH_mem_UH_iff _ l).mpr hl

end MzSl2
