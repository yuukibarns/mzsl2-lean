import Mathlib
import MzSl2.D751a
import MzSl2.F737
import MzSl2.F8de

/-!
# Fact d751: the comparison kernel lies in the dynamical Levi subgroup, hence `[Λ : L] < ∞`

Steps 2–5 of d751. Step 2: integral matrices with fixed upper-left entry `a` have images in the
compact set `K_a = ⋃_γ C₋ ρ(γ) C₊`. Step 3: for `A ∈ Λ` with `p ∤ a` and `p^R ∣ b, c` there are
`z₋, z₊` (limits of `ρ(v(p^R ℤ))`, `ρ(u(p^R ℤ))`) with `z₋ ρ(A) z₊ ∈ M_g`. Step 4: every
`x ∈ E = ker q` lies in `M_g`. Step 5: a tidy subgroup gives a `g`-invariant compact open
subgroup of `E`, and fact 737 gives `[Λ : L] < ∞`.
-/

open Matrix Topology Set Subgroup Filter
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Integral matrices as elements of `Γ` -/

/-- An integral determinant-one matrix as an element of `Γ`. -/
noncomputable def intToΓ (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) : Γ p :=
  ⟨⟨M.map (Int.cast : ℤ → ℚ), by
      have := RingHom.map_det (Int.castRingHom ℚ) M
      rw [h] at this
      simpa [RingHom.mapMatrix_apply] using this.symm⟩, by
    intro i j; exact intCast_mem (R p) (M i j)⟩

theorem mat_intToΓ (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) :
    mat p (intToΓ M h) = M.map (Int.cast : ℤ → ℚ) := rfl

/-- Integer entries of an element of `Λ`. -/
theorem exists_int_matrix {A : Γ p} (hA : A ∈ Λp p) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 1 ∧ mat p A = M.map (Int.cast : ℤ → ℚ) := by
  rw [mem_subgroupOf] at hA
  choose z hz using fun i j => Subring.mem_bot.mp (hA i j)
  refine ⟨Matrix.of z, ?_, ?_⟩
  · have h1 := det_mat A
    have e : ∀ i j, mat p A i j = (z i j : ℚ) := fun i j => (hz i j).symm
    rw [e, e, e, e] at h1
    rw [Matrix.det_fin_two]; simp only [Matrix.of_apply]
    exact_mod_cast h1
  · ext i j; exact (hz i j).symm

/-! ### `dγ` to integer powers -/

theorem mat_dγ_zpow (n : ℤ) : mat p (dγ p ^ n) = dg ((p : ℚ) ^ n) := by
  rcases n with n | n
  · simpa using mat_dγ_pow n
  · rw [zpow_negSucc, mat_dγ_pow_inv, zpow_negSucc]

/-! ### Conjugating integral matrices by powers of `d` -/

/-- If `p^{2|n|}` divides the off-diagonal entries of `B ∈ Λ`, then `dⁿ B d⁻ⁿ ∈ Λ`, with the same
upper-left entry. -/
theorem dγ_zpow_conj_mem {B : Γ p} (hB : B ∈ Λp p) (n : ℤ) {b c : ℤ}
    (hbB : mat p B 0 1 = b) (hcB : mat p B 1 0 = c)
    (hb : (p : ℤ) ^ (2 * n.natAbs) ∣ b) (hc : (p : ℤ) ^ (2 * n.natAbs) ∣ c) :
    dγ p ^ n * B * (dγ p ^ n)⁻¹ ∈ Λp p ∧ mat p (dγ p ^ n * B * (dγ p ^ n)⁻¹) 0 0 = mat p B 0 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hs : (p : ℚ) ^ n ≠ 0 := zpow_ne_zero _ hp0
  have hmat : mat p (dγ p ^ n * B * (dγ p ^ n)⁻¹) =
      !![mat p B 0 0, ((p : ℚ) ^ n) ^ 2 * b; c / ((p : ℚ) ^ n) ^ 2, mat p B 1 1] := by
    rw [mat_mul, mat_mul, mat_inv, mat_dγ_zpow, mat_eq_entries B, hbB, hcB]
    have : adjugate (dg ((p : ℚ) ^ n)) = dg ((p : ℚ) ^ n)⁻¹ := by
      simp [dg, Matrix.adjugate_fin_two]
    rw [this, dg_conj hs]; rfl
  refine ⟨?_, by rw [hmat]; simp⟩
  have hBΛ := hB
  rw [mem_subgroupOf] at hBΛ
  rw [mem_subgroupOf]
  intro i j
  show mat p (dγ p ^ n * B * (dγ p ^ n)⁻¹) i j ∈ _
  rw [hmat]
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨c', hc'⟩ := hc
  have hent : ∀ x : ℚ, (∃ z : ℤ, (z : ℚ) = x) → x ∈ (⊥ : Subring ℚ) := fun x ⟨z, hz⟩ =>
    Subring.mem_bot.mpr ⟨z, hz⟩
  have hpK : ∀ K : ℕ, (p : ℚ) ^ K ≠ 0 := fun K => pow_ne_zero _ hp0
  obtain ⟨K, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hnK : (K : ℤ).natAbs = K := Int.natAbs_natCast K
    rw [hnK] at hb' hc'
    have e1 : ((p : ℚ) ^ (K : ℤ)) ^ 2 * b = (((p : ℤ) ^ (2 * K) * b : ℤ) : ℚ) := by
      rw [zpow_natCast]; push_cast; ring
    have e2 : (c : ℚ) / ((p : ℚ) ^ (K : ℤ)) ^ 2 = (c' : ℚ) := by
      rw [hc', zpow_natCast]; push_cast; have := hpK K; field_simp; ring
    fin_cases i <;> fin_cases j
    · exact hBΛ 0 0
    · exact hent _ ⟨_, e1.symm⟩
    · exact hent _ ⟨_, e2.symm⟩
    · exact hBΛ 1 1
  · have hnK : (-(K : ℤ)).natAbs = K := by simp
    rw [hnK] at hb' hc'
    have e1 : ((p : ℚ) ^ (-(K : ℤ))) ^ 2 * b = (b' : ℚ) := by
      rw [hb', _root_.zpow_neg, zpow_natCast]; push_cast; have := hpK K; field_simp; ring
    have e2 : (c : ℚ) / ((p : ℚ) ^ (-(K : ℤ))) ^ 2 = (((p : ℤ) ^ (2 * K) * c : ℤ) : ℚ) := by
      rw [_root_.zpow_neg, zpow_natCast]; push_cast; have := hpK K; field_simp; ring
    fin_cases i <;> fin_cases j
    · exact hBΛ 0 0
    · exact hent _ ⟨_, e1.symm⟩
    · exact hent _ ⟨_, e2.symm⟩
    · exact hBΛ 1 1

/-! ### Step 2: fixed upper-left entry -/

variable {L : Subgroup (Γ p)}

/-- `K_a = ⋃_{γ ∈ F} C₋ ρ(γ) C₊`. -/
def Kset (L : Subgroup (Γ p)) (F : Finset (Matrix (Fin 2) (Fin 2) ℤ)) : Set (Hc L) :=
  ⋃ γ ∈ F, ⋃ h : γ.det = 1, (Cm L : Set (Hc L)) * {ρH L (intToΓ γ h)} * (Cp L : Set (Hc L))

theorem isCompact_Kset (hCm : IsCompact (Cm L : Set (Hc L))) (hCp : IsCompact (Cp L : Set (Hc L)))
    (F : Finset (Matrix (Fin 2) (Fin 2) ℤ)) : IsCompact (Kset L F) :=
  F.isCompact_biUnion fun _ _ => isCompact_iUnion fun _ => (hCm.mul isCompact_singleton).mul hCp

theorem exists_Kset (a : ℤ) (ha : a ≠ 0) : ∃ F : Finset (Matrix (Fin 2) (Fin 2) ℤ),
    ∀ A ∈ Λp p, mat p A 0 0 = a → ρH L A ∈ Kset L F := by
  obtain ⟨F, hF1, hF2⟩ := fixed_entry_decomp a ha
  refine ⟨F, fun A hA haA => ?_⟩
  obtain ⟨M, hMdet, hM⟩ := exists_int_matrix hA
  have hM00 : M 0 0 = a := by
    have := congrFun (congrFun hM 0) 0; rw [haA, Matrix.map_apply] at this
    exact_mod_cast this.symm
  have hdet : a * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← hM00]; have := hMdet; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨k, l, γ, hγ, he⟩ := hF2 (M 0 1) (M 1 0) (M 1 1) hdet
  have hγdet := (hF1 γ hγ).1
  have hA' : A = vZ k * intToΓ γ hγdet * uZ l := by
    apply mat_injective
    rw [mat_mul, mat_mul, mat_intToΓ, hM]
    have hMe : M = !![a, M 0 1; M 1 0, M 1 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hM00]
    rw [hMe, he]
    change (Int.castRingHom ℚ).mapMatrix (!![1, 0; k, 1] * γ * !![1, l; 0, 1]) = _
    have e1 : (Int.castRingHom ℚ).mapMatrix !![1, 0; k, 1] = v (k : ℚ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [v]
    have e2 : (Int.castRingHom ℚ).mapMatrix !![1, l; 0, 1] = u (l : ℚ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [u]
    rw [map_mul, map_mul, e1, e2]
    rfl
  rw [hA', map_mul, map_mul]
  refine Set.mem_biUnion hγ (Set.mem_iUnion.mpr ⟨hγdet, ?_⟩)
  refine Set.mem_mul.mpr ⟨_, Set.mem_mul.mpr ⟨_, ?_, _, rfl, rfl⟩, _, ?_, rfl⟩
  · exact Subgroup.le_topologicalClosure _ (ρ_vZ_mem_zpowers k)
  · exact Subgroup.le_topologicalClosure _ (ρ_uZ_mem_zpowers l)

/-! ### Step 3: approximation with compact root corrections -/

/-- Closure of `ρ(u(p^R ℤ))`. -/
def CpR (L : Subgroup (Γ p)) (R : ℕ) : Set (Hc L) :=
  _root_.closure (Set.range fun k : ℤ => ρH L (uZ ((p : ℤ) ^ R * k)))

/-- Closure of `ρ(v(p^R ℤ))`. -/
def CmR (L : Subgroup (Γ p)) (R : ℕ) : Set (Hc L) :=
  _root_.closure (Set.range fun k : ℤ => ρH L (vZ ((p : ℤ) ^ R * k)))

theorem CpR_subset (R : ℕ) : CpR L R ⊆ (Cp L : Set (Hc L)) := by
  refine closure_minimal ?_ (Subgroup.isClosed_topologicalClosure _)
  rintro _ ⟨k, rfl⟩; exact Subgroup.le_topologicalClosure _ (ρ_uZ_mem_zpowers _)

theorem CmR_subset (R : ℕ) : CmR L R ⊆ (Cm L : Set (Hc L)) := by
  refine closure_minimal ?_ (Subgroup.isClosed_topologicalClosure _)
  rintro _ ⟨k, rfl⟩; exact Subgroup.le_topologicalClosure _ (ρ_vZ_mem_zpowers _)

theorem coprime_pow_of_not_dvd {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) (R : ℕ) : IsCoprime ((p : ℤ) ^ R) a := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  exact (hpZ.coprime_iff_not_dvd.mpr ha).pow_left

theorem approx (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m) (hu : uZ (m : ℤ) ∈ L)
    (hv : vZ (m : ℤ) ∈ L) {A : Γ p} (hA : A ∈ Λp p) {a b c : ℤ} (haA : mat p A 0 0 = a)
    (hbA : mat p A 0 1 = b) (hcA : mat p A 1 0 = c) (hpa : ¬ (p : ℤ) ∣ a) {R : ℕ}
    (hb : (p : ℤ) ^ R ∣ b) (hc : (p : ℤ) ^ R ∣ c) :
    ∃ zm ∈ CmR L R, ∃ zp ∈ CpR L R, zm * ρH L A * zp ∈ levi (ρH L (dγ p)) := by
  haveI := locallyCompact_Hc L hLc
  have ha0 : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero _)
  obtain ⟨F, hF⟩ := exists_Kset (L := L) a ha0
  have hKc : IsCompact (Kset L F) :=
    isCompact_Kset (isCompact_Cm hLc hm hv) (isCompact_Cp hLc hm hu) F
  -- congruence choices
  have hk : ∀ j : ℕ, ∃ k : ℤ, (p : ℤ) ^ (j + R) ∣ c + a * k := fun j =>
    congr_solvable hp.out hpa c (j + R)
  have hl : ∀ j : ℕ, ∃ l : ℤ, (p : ℤ) ^ (j + R) ∣ b + a * l := fun j =>
    congr_solvable hp.out hpa b (j + R)
  choose k hk using hk
  choose l hl using hl
  have hkR : ∀ j, (p : ℤ) ^ R ∣ k j := by
    intro j
    have h1 : (p : ℤ) ^ R ∣ c + a * k j := (pow_dvd_pow _ (by omega)).trans (hk j)
    have h2 : (p : ℤ) ^ R ∣ a * k j := by
      have := dvd_sub h1 hc; simpa using this
    exact (coprime_pow_of_not_dvd hpa R).dvd_of_dvd_mul_left h2
  have hlR : ∀ j, (p : ℤ) ^ R ∣ l j := by
    intro j
    have h1 : (p : ℤ) ^ R ∣ b + a * l j := (pow_dvd_pow _ (by omega)).trans (hl j)
    have h2 : (p : ℤ) ^ R ∣ a * l j := by
      have := dvd_sub h1 hb; simpa using this
    exact (coprime_pow_of_not_dvd hpa R).dvd_of_dvd_mul_left h2
  -- the correction sequence lies in a compact set
  have hCmR : IsCompact (CmR L R) := (isCompact_Cm hLc hm hv).of_isClosed_subset isClosed_closure
    (CmR_subset R)
  have hCpR : IsCompact (CpR L R) := (isCompact_Cp hLc hm hu).of_isClosed_subset isClosed_closure
    (CpR_subset R)
  have hseq : ∀ j, (ρH L (vZ (k j)), ρH L (uZ (l j))) ∈ CmR L R ×ˢ CpR L R := by
    intro j
    obtain ⟨k', hk'⟩ := hkR j
    obtain ⟨l', hl'⟩ := hlR j
    exact ⟨subset_closure ⟨k', by rw [hk']⟩, subset_closure ⟨l', by rw [hl']⟩⟩
  obtain ⟨⟨zm, zp⟩, ⟨hzm, hzp⟩, φ, hφ, hlim⟩ := (hCmR.prod hCpR).tendsto_subseq hseq
  refine ⟨zm, hzm, zp, hzp, ?_⟩
  set Aj : ℕ → Γ p := fun j => vZ (k j) * A * uZ (l j)
  have hρA : Tendsto (fun j => ρH L (Aj (φ j))) atTop (𝓝 (zm * ρH L A * zp)) := by
    have hc : Continuous fun q : Hc L × Hc L => q.1 * ρH L A * q.2 := by fun_prop
    have := (hc.tendsto _).comp hlim
    refine this.congr fun j => ?_
    simp [Aj, map_mul]
  -- entries of `A_j`
  have hAjΛ : ∀ j, Aj j ∈ Λp p := fun j =>
    (Λp p).mul_mem ((Λp p).mul_mem (vZ_mem_Λp _) hA) (uZ_mem_Λp _)
  have hAj : ∀ j, mat p (Aj j) = !![(a : ℚ), ((b + a * l j : ℤ) : ℚ);
      ((c + a * k j : ℤ) : ℚ), mat p A 1 1 + k j * b + (c + a * k j) * l j] := by
    intro j
    simp only [Aj, mat_mul, mat_vΓ, mat_uΓ]
    rw [mat_eq_entries A, haA, hbA, hcA]
    ext i i'; fin_cases i <;> fin_cases i' <;>
      simp [u, v, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  -- for each `n`, eventually `gⁿ ρ(A_j) g⁻ⁿ ∈ K_a`
  refine levi_of_subset_compact hKc fun n => ?_
  have hev : ∀ᶠ j in atTop, ρH L (dγ p) ^ n * ρH L (Aj (φ j)) * ρH L (dγ p) ^ (-n) ∈ Kset L F := by
    rw [eventually_atTop]
    refine ⟨2 * n.natAbs, fun j hj => ?_⟩
    have hφj : j ≤ φ j := hφ.id_le j
    have hdiv : ∀ x : ℤ, (p : ℤ) ^ (φ j + R) ∣ x → (p : ℤ) ^ (2 * n.natAbs) ∣ x := fun x hx =>
      (pow_dvd_pow _ (by omega)).trans hx
    obtain ⟨hmem, h00⟩ := dγ_zpow_conj_mem (hAjΛ (φ j)) n
      (b := b + a * l (φ j)) (c := c + a * k (φ j))
      (by rw [hAj]; simp) (by rw [hAj]; simp) (hdiv _ (hl _)) (hdiv _ (hk _))
    have := hF _ hmem (by rw [h00, hAj]; simp)
    simpa [map_mul, map_zpow, _root_.zpow_neg] using this
  have hcont : Continuous fun y : Hc L => ρH L (dγ p) ^ n * y * ρH L (dγ p) ^ (-n) := by fun_prop
  exact hKc.isClosed.mem_of_tendsto ((hcont.tendsto _).comp hρA) hev

/-! ### Step 4: the comparison kernel lies in `M_g` -/

variable (hL : L ≤ Λp p)

/-- Points of `⋂_R closure ρ(u(p^R ℤ))` (resp. `v`) lie in `ker q`. -/
theorem qmap_eq_one_of_CpR {z : Hc L} (hz : ∀ R, z ∈ CpR L R) : qmap hL z = 1 := by
  apply Subtype.ext; apply Sym.ext'; intro y
  obtain ⟨γ, rfl⟩ := Cosets.mk_surjective (Λp p) y
  obtain ⟨R, hR⟩ := exists_conj_u_mem γ
  have hcl : IsClosed {w : Hc L | ((qmap hL w : Hc (Λp p)) : Sym (Cosets (Λp p))) ∈
      Sym.stab (Cosets.mk (Λp p) γ)} :=
    (Sym.isClosed_stab _).preimage (continuous_subtype_val.comp (continuous_qmap hL))
  have hsub : CpR L R ⊆ {w : Hc L | ((qmap hL w : Hc (Λp p)) : Sym (Cosets (Λp p))) ∈
      Sym.stab (Cosets.mk (Λp p) γ)} := by
    refine closure_minimal ?_ hcl
    rintro _ ⟨k, rfl⟩
    exact (qmap_ρH_stab hL _ γ).mpr (hR k).1
  exact hsub (hz R)

theorem qmap_eq_one_of_CmR {z : Hc L} (hz : ∀ R, z ∈ CmR L R) : qmap hL z = 1 := by
  apply Subtype.ext; apply Sym.ext'; intro y
  obtain ⟨γ, rfl⟩ := Cosets.mk_surjective (Λp p) y
  obtain ⟨R, hR⟩ := exists_conj_u_mem γ
  have hcl : IsClosed {w : Hc L | ((qmap hL w : Hc (Λp p)) : Sym (Cosets (Λp p))) ∈
      Sym.stab (Cosets.mk (Λp p) γ)} :=
    (Sym.isClosed_stab _).preimage (continuous_subtype_val.comp (continuous_qmap hL))
  have hsub : CmR L R ⊆ {w : Hc L | ((qmap hL w : Hc (Λp p)) : Sym (Cosets (Λp p))) ∈
      Sym.stab (Cosets.mk (Λp p) γ)} := by
    refine closure_minimal ?_ hcl
    rintro _ ⟨k, rfl⟩
    exact (qmap_ρH_stab hL _ γ).mpr (hR k).2
  exact hsub (hz R)

theorem CpR_anti {R S : ℕ} (h : R ≤ S) : CpR L S ⊆ CpR L R := by
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨k, rfl⟩
  refine subset_closure ⟨(p : ℤ) ^ (S - R) * k, ?_⟩
  simp only; congr 2; rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem CmR_anti {R S : ℕ} (h : R ≤ S) : CmR L S ⊆ CmR L R := by
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨k, rfl⟩
  refine subset_closure ⟨(p : ℤ) ^ (S - R) * k, ?_⟩
  simp only; congr 2; rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

/-- **d751 (4).** `ker q ⊆ M_g`. -/
theorem ker_le_levi (hLc : IsCommensurated L) {m : ℕ} (hm : 0 < m) (hu : uZ (m : ℤ) ∈ L)
    (hv : vZ (m : ℤ) ∈ L) {x : Hc L} (hx : qmap hL x = 1) : x ∈ levi (ρH L (dγ p)) := by
  haveI := locallyCompact_Hc L hLc
  set g := ρH L (dγ p)
  -- `x` is a limit of `ρ(A_i)` with `A_i ∈ Λ`
  have hxcl : x ∈ _root_.closure (ρH L '' (Λp p : Set (Γ p))) := by
    rw [← qmap_preimage_UH hL, mem_preimage, hx]; exact (UH (Λp p)).one_mem
  obtain ⟨seq, hseqS, hseq⟩ := mem_closure_iff_seq_limit.mp hxcl
  choose A hAΛ hAρ using hseqS
  -- eventually `A_i` fixes the cosets `d^{±N} Λ`
  have hev : ∀ N : ℕ, ∀ᶠ i in atTop,
      (dγ p ^ N)⁻¹ * A i * dγ p ^ N ∈ Λp p ∧ ((dγ p ^ N)⁻¹)⁻¹ * A i * (dγ p ^ N)⁻¹ ∈ Λp p := by
    intro N
    set W : Set (Hc L) := (fun σ : Hc L => ((qmap hL σ : Hc (Λp p)) : Sym (Cosets (Λp p)))) ⁻¹'
      ((Sym.stab (Cosets.mk (Λp p) (dγ p ^ N)) : Set _) ∩
        (Sym.stab (Cosets.mk (Λp p) (dγ p ^ N)⁻¹) : Set _))
    have hW : IsOpen W := ((Sym.isOpen_stab _).inter (Sym.isOpen_stab _)).preimage
      (continuous_subtype_val.comp (continuous_qmap hL))
    have hxW : x ∈ W := by
      simp only [W, Set.mem_preimage]; rw [hx]
      exact ⟨(Sym.stab _).one_mem, (Sym.stab _).one_mem⟩
    filter_upwards [hseq (hW.mem_nhds hxW)] with i hi
    have hi' : ρH L (A i) ∈ W := by rw [hAρ i]; exact hi
    simp only [W, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe] at hi'
    exact ⟨(qmap_ρH_stab hL _ _).mp hi'.1, (qmap_ρH_stab hL _ _).mp hi'.2⟩
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_eventually hev
  -- integer entries of `B_N = A_{φ N}`
  have hent : ∀ N, ∃ a b c : ℤ, mat p (A (φ N)) 0 0 = a ∧ mat p (A (φ N)) 0 1 = b ∧
      mat p (A (φ N)) 1 0 = c ∧ (p : ℤ) ^ (2 * N) ∣ b ∧ (p : ℤ) ^ (2 * N) ∣ c := by
    intro N
    obtain ⟨M, hMdet, hM⟩ := exists_int_matrix (hAΛ (φ N))
    have h00 : mat p (A (φ N)) 0 0 = M 0 0 := by rw [hM]; simp
    have h01 : mat p (A (φ N)) 0 1 = M 0 1 := by rw [hM]; simp
    have h10 : mat p (A (φ N)) 1 0 = M 1 0 := by rw [hM]; simp
    refine ⟨M 0 0, M 0 1, M 1 0, h00, h01, h10, ?_, ?_⟩
    · -- `d^{-N} A d^N` has upper-right entry `b / p^{2N}`
      have h := (hφP N).1
      rw [mem_subgroupOf] at h
      obtain ⟨z, hz⟩ := Subring.mem_bot.mp (h 0 1)
      have e : mat p ((dγ p ^ N)⁻¹ * A (φ N) * dγ p ^ N) 0 1 = M 0 1 / (p : ℚ) ^ (2 * N) := by
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
        rw [mat_mul, mat_mul, mat_dγ_pow_inv, mat_dγ_pow, mat_eq_entries (A (φ N)), h01]
        have := dg_conj (inv_ne_zero (pow_ne_zero N hp0)) (mat p (A (φ N)) 0 0) (M 0 1 : ℚ)
          (mat p (A (φ N)) 1 0) (mat p (A (φ N)) 1 1)
        rw [inv_inv] at this
        rw [this]; simp; field_simp; ring
      have hz' : (z : ℚ) = mat p ((dγ p ^ N)⁻¹ * A (φ N) * dγ p ^ N) 0 1 := hz
      rw [e] at hz'
      refine ⟨z, ?_⟩
      have hp0 : (p : ℚ) ^ (2 * N) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      have : (M 0 1 : ℚ) = (p : ℚ) ^ (2 * N) * z := by rw [hz']; field_simp
      exact_mod_cast this
    · have h := (hφP N).2
      rw [inv_inv, mem_subgroupOf] at h
      obtain ⟨z, hz⟩ := Subring.mem_bot.mp (h 1 0)
      have e : mat p (dγ p ^ N * A (φ N) * (dγ p ^ N)⁻¹) 1 0 = M 1 0 / (p : ℚ) ^ (2 * N) := by
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
        rw [mat_mul, mat_mul, mat_dγ_pow_inv, mat_dγ_pow, mat_eq_entries (A (φ N)), h10]
        rw [dg_conj (pow_ne_zero N hp0)]; simp; field_simp; ring
      have hz' : (z : ℚ) = mat p (dγ p ^ N * A (φ N) * (dγ p ^ N)⁻¹) 1 0 := hz
      rw [e] at hz'
      refine ⟨z, ?_⟩
      have hp0 : (p : ℚ) ^ (2 * N) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      have : (M 1 0 : ℚ) = (p : ℚ) ^ (2 * N) * z := by rw [hz']; field_simp
      exact_mod_cast this
  choose a b c ha hb hc hbd hcd using hent
  -- `p ∤ a` for `N ≥ 1`
  have hpa : ∀ N, ¬ (p : ℤ) ∣ a (N + 1) := by
    intro N hdvd
    obtain ⟨M, hMdet, hM⟩ := exists_int_matrix (hAΛ (φ (N + 1)))
    have hdet := det_mat (A (φ (N + 1)))
    obtain ⟨e', he'⟩ := Subring.mem_bot.mp ((mem_subgroupOf.mp (hAΛ (φ (N + 1)))) 1 1)
    have h11 : mat p (A (φ (N + 1))) 1 1 = e' := he'.symm
    rw [ha, hb, hc, h11] at hdet
    have hdetZ : a (N + 1) * e' - b (N + 1) * c (N + 1) = 1 := by exact_mod_cast hdet
    have hpb : (p : ℤ) ∣ b (N + 1) := (dvd_pow_self _ (by omega)).trans (hbd (N + 1))
    have : (p : ℤ) ∣ 1 := by
      rw [← hdetZ]; exact dvd_sub (dvd_mul_of_dvd_left hdvd _) (dvd_mul_of_dvd_left hpb _)
    exact (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one this
  -- step 3 at level `2(N+1)`
  have hstep : ∀ N, ∃ zm ∈ CmR L (2 * (N + 1)), ∃ zp ∈ CpR L (2 * (N + 1)),
      zm * ρH L (A (φ (N + 1))) * zp ∈ levi g := fun N =>
    approx hLc hm hu hv (hAΛ _) (ha _) (hb _) (hc _) (hpa N) (hbd _) (hcd _)
  choose zm hzm zp hzp hlev using hstep
  -- a convergent subsequence of the corrections
  have hCm := isCompact_Cm hLc hm hv
  have hCp := isCompact_Cp hLc hm hu
  have hin : ∀ N, (zm N, zp N) ∈ (Cm L : Set (Hc L)) ×ˢ (Cp L : Set (Hc L)) := fun N =>
    ⟨CmR_subset _ (hzm N), CpR_subset _ (hzp N)⟩
  obtain ⟨⟨zM, zP⟩, ⟨hzMC, hzPC⟩, ψ, hψ, hlim⟩ := (hCm.prod hCp).tendsto_subseq hin
  -- the limits lie in `ker q`
  have hzPE : qmap hL zP = 1 := by
    apply qmap_eq_one_of_CpR hL
    intro R
    refine isClosed_closure.mem_of_tendsto ((continuous_snd.tendsto _).comp hlim) ?_
    rw [eventually_atTop]
    refine ⟨R, fun j hj => CpR_anti (R := R) (S := 2 * (ψ j + 1))
      (by have h1 : j ≤ ψ j := hψ.id_le j; omega) (hzp (ψ j))⟩
  have hzME : qmap hL zM = 1 := by
    apply qmap_eq_one_of_CmR hL
    intro R
    refine isClosed_closure.mem_of_tendsto ((continuous_fst.tendsto _).comp hlim) ?_
    rw [eventually_atTop]
    refine ⟨R, fun j hj => CmR_anti (R := R) (S := 2 * (ψ j + 1))
      (by have h1 : j ≤ ψ j := hψ.id_le j; omega) (hzm (ψ j))⟩
  -- `zM x zP ∈ M_g`
  have hρB : Tendsto (fun j => ρH L (A (φ (ψ j + 1)))) atTop (𝓝 x) := by
    have h1 : StrictMono fun j => φ (ψ j + 1) := hφ.comp (fun a b h => by
      have := hψ h; omega)
    rw [← funext hAρ] at hseq
    exact hseq.comp h1.tendsto_atTop
  have hprod : Tendsto (fun j => zm (ψ j) * ρH L (A (φ (ψ j + 1))) * zp (ψ j)) atTop
      (𝓝 (zM * x * zP)) := by
    have := ((continuous_fst.tendsto _).comp hlim).mul hρB |>.mul
      ((continuous_snd.tendsto _).comp hlim)
    exact this
  have hmid : zM * x * zP ∈ levi g :=
    (levi_isClosed g).mem_of_tendsto hprod (Eventually.of_forall fun j => hlev (ψ j))
  have hzML : zM ∈ levi g := levi_of_Cm hL hLc hm hv hzMC hzME
  have hzPL : zP ∈ levi g := levi_of_Cp hL hLc hm hu hzPC hzPE
  have : x = zM⁻¹ * (zM * x * zP) * zP⁻¹ := by group
  rw [this]
  exact levi_mul (levi_mul (levi_inv hzML) hmid) (levi_inv hzPL)

/-! ### Step 5: fact d751 and the main theorem -/

omit hL in
/-- **Fact d751.** An infinite commensurated subgroup of `Γ` meets `SL₂(ℤ)` in a subgroup of
finite index in `SL₂(ℤ)`. -/
theorem d751 {N : Subgroup (Γ p)} (hN : IsCommensurated N) (hinf : (N : Set (Γ p)).Infinite) :
    N.relIndex (Λp p) ≠ 0 := by
  set L := N ⊓ Λp p
  have hL : L ≤ Λp p := inf_le_right
  have hLc : IsCommensurated L := hN.inf Λp_commensurated
  haveI := locallyCompact_Hc L hLc
  obtain ⟨m, hm, hu, hv⟩ := exists_uv_mem hN hinf
  have huL : uZ (m : ℤ) ∈ L := ⟨by convert hu using 2; push_cast; rfl, uZ_mem_Λp _⟩
  have hvL : vZ (m : ℤ) ∈ L := ⟨by convert hv using 2; push_cast; rfl, vZ_mem_Λp _⟩
  obtain ⟨V, hV, htidy⟩ := tidy_levi (ρH L (dγ p))
  have h := core737 hN hinf V hV (fun x hxV hxq => by
    have hlev := ker_le_levi hL hLc hm huL hvL hxq
    exact ⟨by simpa using htidy x hxV hlev 1, by simpa using htidy x hxV hlev (-1)⟩)
  rwa [Subgroup.inf_relIndex_right] at h

/-- **Main theorem.** -/
theorem mainTheorem : MainTheorem := mainTheorem_of_d751 fun _ _ _ hN hinf => d751 hN hinf

end MzSl2
