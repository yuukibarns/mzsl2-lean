import Mathlib
import MzSl2.Iwahori
import MzSl2.Density

/-!
# Cartan decomposition and open subgroups of `SL₂(ℚ_p)` (fact 8de)

* `K(r)` is normal in `K = SL₂(ℤ_p)`;
* Cartan: every `x ∈ SL₂(ℚ_p)` is `k₁ diag(p⁻ⁿ, pⁿ) k₂` with `k₁, k₂ ∈ K`, `n ≥ 0`;
* a subgroup containing some `K(r)` is compact or all of `SL₂(ℚ_p)`.
-/

open Matrix Subgroup Topology Set Metric

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

theorem Kr_normal (r : ℕ) {k x : SLp p} (hk : k ∈ Kp p) (hx : x ∈ Kr p r) :
    k * x * k⁻¹ ∈ Kr p r := by
  have hc : (p : ℝ) ^ (-(r : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)
  have hk' : ∀ i j, ‖matP p k i j‖ ≤ 1 := hk
  have hki : ∀ i j, ‖matP p k⁻¹ i j‖ ≤ 1 := (Kp p).inv_mem hk
  set X := matP p x - 1
  have hX : ∀ i j, ‖X i j‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := hx
  have hkk : matP p k * matP p k⁻¹ = 1 := by rw [← matP_mul, mul_inv_cancel, matP_one]
  have e : matP p (k * x * k⁻¹) - 1 = matP p k * X * matP p k⁻¹ := by
    simp only [X, matP_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hkk]
  intro i j
  change ‖matP p (k * x * k⁻¹) i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ _
  rw [← Matrix.sub_apply, e, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  refine norm_add_le_of ?_ ?_ <;> refine norm_mul_le_of hc (norm_add_le_of ?_ ?_) (hki _ _) <;>
    exact norm_mul_le_of' hc (hk' _ _) (hX _ _)

theorem uP_mem_Kr {r : ℕ} {t : ℚ_[p]} (ht : ‖t‖ ≤ (p : ℝ) ^ (-(r : ℤ))) : uP t ∈ Kr p r := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [u] <;> first | positivity | simpa using ht

theorem vP_mem_Kr {r : ℕ} {t : ℚ_[p]} (ht : ‖t‖ ≤ (p : ℝ) ^ (-(r : ℤ))) : vP t ∈ Kr p r := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [v] <;> first | positivity | simpa using ht

theorem uP_mem_Kp {t : ℚ_[p]} (ht : ‖t‖ ≤ 1) : uP t ∈ Kp p := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [u, ht]

theorem vP_mem_Kp {t : ℚ_[p]} (ht : ‖t‖ ≤ 1) : vP t ∈ Kp p := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [v, ht]

theorem dP_mem_Kp {t : ℚ_[p]} (ht0 : t ≠ 0) (ht : ‖t‖ = 1) : dP t ht0 ∈ Kp p := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [dg, ht, norm_inv]

/-- The Weyl element in `SL₂(ℚ_p)`. -/
noncomputable def wP : SLp p := ⟨w, by simp [w, Matrix.det_fin_two_of]⟩

@[simp] theorem matP_wP : matP p (wP : SLp p) = w := rfl

theorem wP_mem_Kp : (wP : SLp p) ∈ Kp p := by
  intro i j; rw [matP_wP]; fin_cases i <;> fin_cases j <;> simp [w]

/-- `diag(p⁻ⁿ, pⁿ)`. -/
noncomputable def aP (n : ℕ) : SLp p :=
  dP ((p : ℚ_[p]) ^ n)⁻¹ (inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)))

/-- Cartan decomposition when the upper-left entry has maximal norm. -/
theorem cartan_pivot (y : SLp p) (hmax : ∀ i j, ‖matP p y i j‖ ≤ ‖matP p y 0 0‖) :
    ∃ k₁ ∈ Kp p, ∃ k₂ ∈ Kp p, ∃ n : ℕ, y = k₁ * aP n * k₂ := by
  set π := matP p y 0 0
  have hdet : π * matP p y 1 1 - matP p y 0 1 * matP p y 1 0 = 1 := by
    have := y.2; rw [Matrix.det_fin_two] at this; exact this
  -- `‖π‖ ≥ 1`
  have hπ1 : 1 ≤ ‖π‖ := by
    have h := Padic.nonarchimedean (π * matP p y 1 1) (-(matP p y 0 1 * matP p y 1 0))
    rw [← sub_eq_add_neg, hdet, norm_one, norm_neg, norm_mul, norm_mul] at h
    by_contra hlt
    push_neg at hlt
    have h0 := norm_nonneg π
    have b1 : ‖π‖ * ‖matP p y 1 1‖ < 1 := by
      calc ‖π‖ * ‖matP p y 1 1‖ ≤ ‖π‖ * ‖π‖ := by gcongr; exact hmax 1 1
        _ < 1 := by nlinarith
    have b2 : ‖matP p y 0 1‖ * ‖matP p y 1 0‖ < 1 := by
      calc ‖matP p y 0 1‖ * ‖matP p y 1 0‖ ≤ ‖π‖ * ‖π‖ := by
            gcongr; exact hmax 0 1; exact hmax 1 0
        _ < 1 := by nlinarith
    exact absurd h (not_le.mpr (max_lt b1 b2))
  have hπ0 : π ≠ 0 := by intro h; rw [h, norm_zero] at hπ1; linarith
  -- `‖π‖ = pⁿ`
  have hval := Padic.norm_eq_zpow_neg_valuation hπ0
  set n : ℕ := (-π.valuation).toNat
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hnonneg : 0 ≤ -π.valuation := by
    by_contra h; push_neg at h
    have : (p : ℝ) ^ (-π.valuation) < 1 := zpow_lt_one_of_neg₀ hp1 h
    linarith
  have hπn : ‖π‖ = (p : ℝ) ^ n := by
    rw [hval, ← zpow_natCast]; congr 1; omega
  set ε := π * (p : ℚ_[p]) ^ n
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hε0 : ε ≠ 0 := mul_ne_zero hπ0 (pow_ne_zero _ hp0)
  have hε : ‖ε‖ = 1 := by
    rw [norm_mul, hπn, Padic.norm_p_pow, ← zpow_natCast, ← zpow_add₀ (by positivity)]; simp
  have hb : ‖matP p y 0 1 / π‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ (hmax 0 1) (norm_nonneg _)
  have hc : ‖matP p y 1 0 / π‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ (hmax 1 0) (norm_nonneg _)
  refine ⟨vP (matP p y 1 0 / π), vP_mem_Kp hc, dP ε hε0 * uP (matP p y 0 1 / π),
    (Kp p).mul_mem (dP_mem_Kp hε0 hε) (uP_mem_Kp hb), n, ?_⟩
  apply matP_injective
  simp only [aP, matP_mul, matP_vP, matP_uP, matP_dP]
  have e : matP p y = !![π, matP p y 0 1; matP p y 1 0, matP p y 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  conv_lhs => rw [e, iwahori_identity hπ0 hdet]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (v _) (dg _) (dg _), dg_mul_dg]
  congr 3
  simp only [ε]; field_simp

/-- **Cartan decomposition.** -/
theorem cartan (x : SLp p) : ∃ k₁ ∈ Kp p, ∃ k₂ ∈ Kp p, ∃ n : ℕ, x = k₁ * aP n * k₂ := by
  obtain ⟨⟨i0, j0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun ij => ‖matP p x ij.1 ij.2‖) ⟨⟨0, 0⟩, Finset.mem_univ _⟩
  have hmax' : ∀ i j, ‖matP p x i j‖ ≤ ‖matP p x i0 j0‖ := fun i j =>
    hmax ⟨i, j⟩ (Finset.mem_univ _)
  have hw := (wP_mem_Kp (p := p))
  have hwi := (Kp p).inv_mem hw
  -- move the maximal entry to the corner
  have key : ∀ (σ τ : SLp p), σ ∈ Kp p → τ ∈ Kp p →
      (∀ i j, ‖matP p (σ * x * τ) i j‖ ≤ ‖matP p (σ * x * τ) 0 0‖) →
      ∃ k₁ ∈ Kp p, ∃ k₂ ∈ Kp p, ∃ n : ℕ, x = k₁ * aP n * k₂ := by
    intro σ τ hσ hτ h
    obtain ⟨k₁, hk₁, k₂, hk₂, n, he⟩ := cartan_pivot _ h
    refine ⟨σ⁻¹ * k₁, (Kp p).mul_mem ((Kp p).inv_mem hσ) hk₁, k₂ * τ⁻¹,
      (Kp p).mul_mem hk₂ ((Kp p).inv_mem hτ), n, ?_⟩
    calc x = σ⁻¹ * (σ * x * τ) * τ⁻¹ := by group
      _ = _ := by rw [he]; group
  have ent : ∀ (σ τ : SLp p), matP p (σ * x * τ) = matP p σ * matP p x * matP p τ :=
    fun _ _ => rfl
  have ex : matP p x = !![matP p x 0 0, matP p x 0 1; matP p x 1 0, matP p x 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h00 := hmax' 0 0; have h01 := hmax' 0 1; have h10 := hmax' 1 0; have h11 := hmax' 1 1
  fin_cases i0 <;> fin_cases j0
  · exact key 1 1 (Kp p).one_mem (Kp p).one_mem (by simpa using hmax')
  · refine key 1 wP (Kp p).one_mem hw ?_
    intro i j
    rw [ent, matP_one, matP_wP, ex]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h00 h01 h10 h11
    fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_fin_two, Matrix.one_fin_two] <;>
      assumption
  · refine key wP 1 hw (Kp p).one_mem ?_
    intro i j
    rw [ent, matP_one, matP_wP, ex]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h00 h01 h10 h11
    fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_fin_two, Matrix.one_fin_two] <;>
      assumption
  · refine key wP wP hw hw ?_
    intro i j
    rw [ent, matP_wP, ex]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h00 h01 h10 h11
    fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_fin_two] <;> assumption

theorem aP_conj_uP (n : ℕ) (t : ℚ_[p]) :
    aP n * uP ((p : ℚ_[p]) ^ (2 * n) * t) * (aP n)⁻¹ = uP t := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply matP_injective
  rw [matP_mul, matP_mul, matP_inv]
  simp only [aP, matP_dP, matP_uP]
  have : adjugate (dg ((p : ℚ_[p]) ^ n)⁻¹) = dg ((p : ℚ_[p]) ^ n)⁻¹⁻¹ := by
    simp [dg, Matrix.adjugate_fin_two]
  rw [this, dg_conj_u (inv_ne_zero (pow_ne_zero _ hp0))]
  congr 1; field_simp; ring

theorem isOpen_of_Kr_le {J : Subgroup (SLp p)} {r : ℕ} (hr : Kr p r ≤ J) :
    IsOpen (J : Set (SLp p)) := Subgroup.isOpen_mono hr (isOpen_Kr r)

/-- **Open subgroup dichotomy** (8de): a subgroup of `SL₂(ℚ_p)` containing some `K(r)` is
compact or everything. -/
theorem compact_or_top {J : Subgroup (SLp p)} {r : ℕ} (hr : Kr p r ≤ J) :
    IsCompact (J : Set (SLp p)) ∨ J = ⊤ := by
  by_cases hJc : IsCompact (J : Set (SLp p))
  · exact Or.inl hJc
  right
  have hJcl : IsClosed (J : Set (SLp p)) := Subgroup.isClosed_of_isOpen _ (isOpen_of_Kr_le hr)
  choose k₁ hk₁ k₂ hk₂ nn hx using fun x : SLp p => cartan x
  -- elements of `J` with arbitrarily large Cartan parameter
  have hunb : ∀ N0 : ℕ, ∃ x ∈ J, N0 ≤ nn x := by
    intro N0
    by_contra h
    push_neg at h
    apply hJc
    have hcpt : IsCompact (⋃ m ∈ Finset.range N0,
        (fun q : SLp p × SLp p => q.1 * aP m * q.2) '' ((Kp p : Set (SLp p)) ×ˢ (Kp p : Set _))) :=
      (Finset.range N0).isCompact_biUnion fun m _ =>
        (isCompact_Kp.prod isCompact_Kp).image
          ((continuous_fst.mul continuous_const).mul continuous_snd)
    refine hcpt.of_isClosed_subset hJcl ?_
    intro x hxJ
    refine Set.mem_biUnion (Finset.mem_range.mpr (h x hxJ)) ⟨(k₁ x, k₂ x), ⟨hk₁ x, hk₂ x⟩, ?_⟩
    exact (hx x).symm
  choose xs hxsJ hxsn using hunb
  -- pigeonhole on `K / K(r)`
  haveI : CompactSpace (Kp p) := isCompact_iff_compactSpace.mp isCompact_Kp
  have hKropen : IsOpen (((Kr p r).subgroupOf (Kp p) : Subgroup (Kp p)) : Set (Kp p)) :=
    (isOpen_Kr r).preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hKropen
  let f : ℕ → Kp p ⧸ (Kr p r).subgroupOf (Kp p) := fun N0 =>
    QuotientGroup.mk ⟨k₁ (xs N0), hk₁ _⟩
  obtain ⟨q0, hq0⟩ := Finite.exists_infinite_fiber f
  set k0 : Kp p := q0.out
  have hk0 : (k0 : SLp p) ∈ Kp p := k0.2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  -- conjugates of upper unipotents by `k0` lie in `J`
  have hu : ∀ t : ℚ_[p], (k0 : SLp p) * uP t * (k0 : SLp p)⁻¹ ∈ J := by
    intro t
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (‖t‖ * (p : ℝ) ^ r) hp1
    have hinf : (f ⁻¹' {q0}).Infinite := Set.infinite_coe_iff.mp hq0
    obtain ⟨N0, hN0S, hN0M⟩ := hinf.exists_gt M
    set x := xs N0
    set n := nn x
    have hn : N0 ≤ n := hxsn N0
    -- the parameter `p^{2n} t` is small
    have hsmall : ‖(p : ℚ_[p]) ^ (2 * n) * t‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := by
      rw [norm_mul, Padic.norm_p_pow, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast,
        inv_mul_le_iff₀ (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖t‖ * (p : ℝ) ^ r ≤ (p : ℝ) ^ M := hM.le
        _ ≤ (p : ℝ) ^ (2 * n) := pow_le_pow_right₀ hp1.le (by omega)
    have hy : (k₂ x)⁻¹ * uP ((p : ℚ_[p]) ^ (2 * n) * t) * (k₂ x)⁻¹⁻¹ ∈ Kr p r :=
      Kr_normal r ((Kp p).inv_mem (hk₂ x)) (uP_mem_Kr hsmall)
    have hxyx : x * ((k₂ x)⁻¹ * uP ((p : ℚ_[p]) ^ (2 * n) * t) * (k₂ x)⁻¹⁻¹) * x⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem (hxsJ N0) (hr hy)) (J.inv_mem (hxsJ N0))
    have e1 : x * ((k₂ x)⁻¹ * uP ((p : ℚ_[p]) ^ (2 * n) * t) * (k₂ x)⁻¹⁻¹) * x⁻¹ =
        k₁ x * uP t * (k₁ x)⁻¹ := by
      have hx' : x = k₁ x * aP n * k₂ x := hx x
      generalize k₁ x = K1 at hx' ⊢
      generalize k₂ x = K2 at hx' ⊢
      rw [hx', ← aP_conj_uP n t]; group
    rw [e1] at hxyx
    -- `k₁ x` and `k0` lie in the same `K(r)`-coset
    have hcos : f N0 = q0 := hN0S
    have hmem : (k0 : SLp p)⁻¹ * k₁ x ∈ Kr p r := by
      have : QuotientGroup.mk k0 = f N0 := by rw [hcos]; exact QuotientGroup.out_eq' q0
      have := QuotientGroup.eq.mp this
      rw [mem_subgroupOf] at this
      simpa using this
    have hℓ : (k0 : SLp p) * ((k0 : SLp p)⁻¹ * k₁ x)⁻¹ * (k0 : SLp p)⁻¹ ∈ Kr p r :=
      Kr_normal r hk0 ((Kr p r).inv_mem hmem)
    have := J.mul_mem (J.mul_mem (hr hℓ) hxyx) (J.inv_mem (hr hℓ))
    convert this using 1; group
  -- conjugates of lower unipotents by `k0` lie in `J`
  have hvsmall : ∀ s : ℚ_[p], ‖s‖ ≤ (p : ℝ) ^ (-(r : ℤ)) →
      (k0 : SLp p) * vP s * (k0 : SLp p)⁻¹ ∈ J := fun s hs =>
    hr (Kr_normal r hk0 (vP_mem_Kr hs))
  set c : ℚ_[p] := (p : ℚ_[p]) ^ r
  have hc0 : c ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hcn : ‖c‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := by rw [Padic.norm_p_pow]
  have hcn' : ‖-c‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := by rw [norm_neg]; exact hcn
  have hv : ∀ z : ℚ_[p], (k0 : SLp p) * vP z * (k0 : SLp p)⁻¹ ∈ J := by
    intro z
    have e : vP z = uP (-1 / c) * vP c * uP (-z / c ^ 2) * vP (-c) * uP (1 / c) := by
      apply matP_injective
      simp only [matP_mul, matP_uP, matP_vP]
      rw [conj_8de hc0]; congr 1; field_simp
    rw [e]
    have := J.mul_mem (J.mul_mem (J.mul_mem (J.mul_mem (hu (-1 / c)) (hvsmall c hcn))
      (hu (-z / c ^ 2))) (hvsmall (-c) hcn')) (hu (1 / c))
    convert this using 1; group
  -- conclude
  let J2 := J.comap (MulAut.conj (k0 : SLp p)).toMonoidHom
  have hJ2 : J2 = ⊤ := eq_top_of_roots (fun t => by simpa [J2] using hu t)
    (fun t => by simpa [J2] using hv t)
  rw [eq_top_iff]
  intro g _
  have : (k0 : SLp p)⁻¹ * g * (k0 : SLp p) ∈ J2 := by rw [hJ2]; trivial
  simp only [J2, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  convert this using 1; group

end MzSl2
