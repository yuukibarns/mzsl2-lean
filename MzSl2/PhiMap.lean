import Mathlib
import MzSl2.Dichotomy
import MzSl2.CompletionTDLC
import MzSl2.Commensurated
import MzSl2.U801

/-!
# `SL₂(ℚ_p) → Γ//SL₂(ℤ)` (fact 737: `Γ//Λ ≅ PSL₂(ℚ_p)`)

Through the bijection `Γ/Λ ≅ SL₂(ℚ_p)/SL₂(ℤ_p)` (density of `Γ`, `Γ ∩ SL₂(ℤ_p) = Λ`), the action
of `SL₂(ℚ_p)` on `SL₂(ℚ_p)/SL₂(ℤ_p)` gives `Φ : SL₂(ℚ_p) → Hc Λ`. It is a continuous, open,
surjective homomorphism with kernel `{±1}` and `Φ ∘ ι = ρ_Λ`.
-/

open Matrix Topology Set Subgroup
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

variable (p) in
/-- `Λ = SL₂(ℤ)` as a subgroup of `Γ`. -/
abbrev Λp : Subgroup (Γ p) := Λ.subgroupOf (Γ p)

instance : Countable (Γ p) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  haveI : Countable (SpecialLinearGroup (Fin 2) ℚ) := Subtype.countable
  exact Subtype.countable

theorem Λp_commensurated : IsCommensurated (Λp p) := Λ'_commensurated

theorem ιΓ_inv_mul_mem_Kp_iff (a b : Γ p) : (ιΓ p a)⁻¹ * ιΓ p b ∈ Kp p ↔ a⁻¹ * b ∈ Λp p := by
  rw [← map_inv, ← map_mul, ιΓ_mem_Kp_iff]

/-- The map `Γ/Λ → SL₂(ℚ_p)/SL₂(ℤ_p)`. -/
noncomputable def cosetMap : Cosets (Λp p) → SLp p ⧸ Kp p :=
  Quotient.map' (ιΓ p) (fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢; exact (ιΓ_inv_mul_mem_Kp_iff a b).mpr h)

theorem cosetMap_bijective : Function.Bijective (cosetMap (p := p)) := by
  constructor
  · rintro ⟨a⟩ ⟨b⟩ h
    apply Quotient.sound'
    have := Quotient.exact' h
    rw [QuotientGroup.leftRel_apply] at this ⊢
    exact (ιΓ_inv_mul_mem_Kp_iff a b).mp this
  · rintro ⟨x⟩
    -- the open set `x K` meets `ι(Γ)`
    have hO : IsOpen {y : SLp p | x⁻¹ * y ∈ Kp p} :=
      isOpen_Kp.preimage (continuous_const.mul continuous_id)
    obtain ⟨_, hy, γ, rfl⟩ := denseRange_ιΓ.inter_open_nonempty _ hO
      ⟨x, by simp [(Kp p).one_mem]⟩
    refine ⟨Quotient.mk'' γ, ?_⟩
    show (QuotientGroup.mk (ιΓ p γ) : SLp p ⧸ Kp p) = QuotientGroup.mk x
    exact (QuotientGroup.eq.mpr (by simpa using (Kp p).inv_mem hy))

/-- `Γ/Λ ≅ SL₂(ℚ_p)/SL₂(ℤ_p)`. -/
noncomputable def cosetEquiv : Cosets (Λp p) ≃ SLp p ⧸ Kp p :=
  Equiv.ofBijective _ cosetMap_bijective

theorem cosetEquiv_mk (γ : Γ p) :
    cosetEquiv (Cosets.mk (Λp p) γ) = (QuotientGroup.mk (ιΓ p γ) : SLp p ⧸ Kp p) := rfl

/-- The action of `SL₂(ℚ_p)` transported to `Γ/Λ`. -/
noncomputable def Φsym : SLp p →* Sym (Cosets (Λp p)) where
  toFun x := (⟨fun y => cosetEquiv.symm (x • cosetEquiv y),
    fun y => cosetEquiv.symm (x⁻¹ • cosetEquiv y),
    fun y => by simp, fun y => by simp⟩ : Equiv.Perm (Cosets (Λp p)))
  map_one' := Sym.ext' fun y => by
    show cosetEquiv.symm ((1 : SLp p) • cosetEquiv y) = y; simp
  map_mul' x z := Sym.ext' fun y => by
    show cosetEquiv.symm ((x * z) • cosetEquiv y) =
      cosetEquiv.symm (x • cosetEquiv (cosetEquiv.symm (z • cosetEquiv y)))
    simp [mul_smul]

theorem Φsym_apply (x : SLp p) (y : Cosets (Λp p)) :
    Φsym x y = cosetEquiv.symm (x • cosetEquiv y) := rfl

theorem Φsym_ιΓ (γ : Γ p) : Φsym (ιΓ p γ) = ρ (Λp p) γ := by
  apply Sym.ext'; intro y
  obtain ⟨g, rfl⟩ := Cosets.mk_surjective (Λp p) y
  rw [Φsym_apply, cosetEquiv_mk, ρ_apply, Cosets.smul_mk, Equiv.symm_apply_eq, cosetEquiv_mk,
    map_mul]
  rfl

theorem continuous_Φsym : Continuous (Φsym (p := p)) := by
  haveI : DiscreteTopology (SLp p ⧸ Kp p) := QuotientGroup.discreteTopology isOpen_Kp
  apply continuous_induced_rng.mpr
  refine (continuous_pi fun y => ?_).prodMk (continuous_pi fun y => ?_)
  · show Continuous fun x : SLp p => cosetEquiv.symm (x • cosetEquiv y)
    exact continuous_of_discreteTopology.comp (continuous_id.smul continuous_const)
  · show Continuous fun x : SLp p => (Φsym x)⁻¹ y
    simp only [← map_inv, Φsym_apply]
    exact continuous_of_discreteTopology.comp (continuous_inv.smul continuous_const)

theorem Φsym_mem_Hc (x : SLp p) : Φsym x ∈ Hc (Λp p) := by
  have hd : x ∈ _root_.closure (Set.range (ιΓ p)) := by
    rw [denseRange_ιΓ.closure_range]; trivial
  exact map_mem_closure continuous_Φsym hd (t := ((ρ (Λp p)).range : Set _))
    (by rintro _ ⟨γ, rfl⟩; exact ⟨γ, (Φsym_ιΓ γ).symm⟩)

/-- The map `Φ`. -/
noncomputable def Φ : SLp p →* Hc (Λp p) := (Φsym (p := p)).codRestrict _ Φsym_mem_Hc

theorem Φ_apply (x : SLp p) (y : Cosets (Λp p)) :
    cosetEquiv (((Φ x : Hc (Λp p)) : Sym (Cosets (Λp p))) y) = x • cosetEquiv y := by
  show cosetEquiv (Φsym x y) = _
  rw [Φsym_apply, Equiv.apply_symm_apply]

theorem Φ_ιΓ (γ : Γ p) : Φ (ιΓ p γ) = ρH (Λp p) γ := Subtype.ext (Φsym_ιΓ γ)

theorem continuous_Φ : Continuous (Φ (p := p)) := continuous_Φsym.subtype_mk _

theorem Φ_surjective : Function.Surjective (Φ (p := p)) := by
  intro σ
  -- reduce to the stabiliser of the base point
  obtain ⟨γ, hγ⟩ := Cosets.mk_surjective (Λp p) ((σ : Sym (Cosets (Λp p))) (base (Λp p)))
  set τ := (ρH (Λp p) γ)⁻¹ * σ
  have hτ : τ ∈ UH (Λp p) := by
    rw [← SetLike.mem_coe, coe_UH, mem_preimage, SetLike.mem_coe]
    show ((((ρH (Λp p) γ)⁻¹ * σ : Hc (Λp p)) : Sym (Cosets (Λp p)))) (base (Λp p)) = base (Λp p)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Sym.mul_apply, ρH_coe, ← hγ, ← map_inv, ρ_apply,
      Cosets.smul_mk, inv_mul_cancel]
    rfl
  -- `Φ(K)` is compact, hence closed, and contains `ρ(Λ)`
  have hK : IsCompact (Φ '' (Kp p : Set (SLp p))) := isCompact_Kp.image continuous_Φ
  have hsub : (UH (Λp p) : Set (Hc (Λp p))) ⊆ Φ '' (Kp p : Set (SLp p)) := by
    have e : (UH (Λp p) : Set (Hc (Λp p))) = _root_.closure (ρH (Λp p) '' (Λp p : Set (Γ p))) := by
      have himg : Subtype.val '' (ρH (Λp p) '' (Λp p : Set (Γ p))) =
          (ρ (Λp p)) '' (Λp p : Set (Γ p)) := by rw [Set.image_image]; rfl
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himg]
      rfl
    rw [e]
    refine closure_minimal ?_ hK.isClosed
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨ιΓ p l, (ιΓ_mem_Kp_iff l).mpr hl, Φ_ιΓ l⟩
  obtain ⟨k, -, hk⟩ := hsub hτ
  refine ⟨ιΓ p γ * k, ?_⟩
  rw [map_mul, hk, Φ_ιΓ]; simp [τ]

/-- The core of `SL₂(ℤ_p)`: an element in every conjugate of `SL₂(ℤ_p)` is `±1`. -/
theorem eq_pm_one_of_core (x : SLp p) (hx : ∀ g : SLp p, g⁻¹ * x * g ∈ Kp p) :
    matP p x = 1 ∨ matP p x = -1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  set a := matP p x 0 0
  set b := matP p x 0 1
  set c := matP p x 1 0
  set d := matP p x 1 1
  have hdet : a * d - b * c = 1 := by
    have := x.2; rw [Matrix.det_fin_two] at this; exact this
  have ex : matP p x = !![a, b; c, d] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  -- conjugating by `diag(pⁿ, p⁻ⁿ)` kills the off-diagonal entries
  have hconj : ∀ n : ℕ, ‖c / ((p : ℚ_[p]) ^ n) ^ 2‖ ≤ 1 ∧ ‖b / ((p : ℚ_[p]) ^ n) ^ 2‖ ≤ 1 := by
    intro n
    have hpn : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero _ hp0
    constructor
    · have h := hx (aP n) 1 0
      rw [matP_mul, matP_mul, matP_inv] at h
      simp only [aP, matP_dP] at h
      have e : adjugate (dg ((p : ℚ_[p]) ^ n)⁻¹) = dg ((p : ℚ_[p]) ^ n) := by
        simp [dg, Matrix.adjugate_fin_two]
      rw [e, ex] at h
      have e2 : dg ((p : ℚ_[p]) ^ n) * !![a, b; c, d] * dg ((p : ℚ_[p]) ^ n)⁻¹ =
          !![a, ((p : ℚ_[p]) ^ n) ^ 2 * b; c / ((p : ℚ_[p]) ^ n) ^ 2, d] := dg_conj hpn a b c d
      rw [e2] at h; simpa using h
    · have h := hx (aP n)⁻¹ 0 1
      rw [inv_inv, matP_mul, matP_mul, matP_inv] at h
      simp only [aP, matP_dP] at h
      have e : adjugate (dg ((p : ℚ_[p]) ^ n)⁻¹) = dg ((p : ℚ_[p]) ^ n)⁻¹⁻¹ := by
        simp [dg, Matrix.adjugate_fin_two]
      rw [e, ex] at h
      have e2 := dg_conj (inv_ne_zero hpn) a b c d
      rw [e2] at h
      simp at h
      have : ((p : ℚ_[p]) ^ n)⁻¹ ^ 2 * b = b / ((p : ℚ_[p]) ^ n) ^ 2 := by field_simp
      rw [← this]; simpa using h
  have hzero : ∀ y : ℚ_[p], (∀ n : ℕ, ‖y / ((p : ℚ_[p]) ^ n) ^ 2‖ ≤ 1) → y = 0 := by
    intro y hy
    by_contra hy0
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖y‖⁻¹) hp1
    have h := hy n
    simp only [norm_div, norm_pow, Padic.norm_p] at h
    rw [div_le_one (by positivity)] at h
    have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hq1 : (p : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
    have h1 : ((p : ℝ)⁻¹ ^ n) ^ 2 ≤ (p : ℝ)⁻¹ ^ n :=
      pow_le_of_le_one (by positivity) hq1 two_ne_zero
    have h2 : (p : ℝ)⁻¹ ^ n < ‖y‖ := by
      rw [inv_pow, inv_lt_comm₀ (by positivity) hy']; exact hn
    have h3 : ‖y‖ ≤ ((p : ℝ)⁻¹ ^ n) ^ 2 := by
      have := h; simpa [inv_pow] using this
    linarith
  have hc0 : c = 0 := hzero c fun n => (hconj n).1
  have hb0 : b = 0 := hzero b fun n => (hconj n).2
  -- conjugating by `u(t)` forces `a = d`
  have had : a = d := by
    by_contra hne
    have hne' : a - d ≠ 0 := sub_ne_zero.mpr hne
    set t : ℚ_[p] := (p : ℚ_[p])⁻¹ / (a - d)
    have e1 : matP p ((uP t)⁻¹ * x * uP t) 0 1 = t * a - d * t := by
      rw [matP_mul, matP_mul, matP_inv, ex, hb0, hc0]
      simp [u, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have e : t * a - d * t = (p : ℚ_[p])⁻¹ := by
      have : t * a - d * t = t * (a - d) := by ring
      rw [this]; simp only [t]; field_simp
    have h' := hx (uP t) 0 1
    rw [e1, e, norm_inv, Padic.norm_p, inv_inv] at h'
    linarith
  rw [hb0, hc0, ← had] at hdet
  have ha2 : a * a = 1 := by linear_combination hdet
  have ha : a = 1 ∨ a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by ring_nf; linear_combination ha2
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rw [ex, hb0, hc0, ← had]
  rcases ha with h | h
  · left; rw [h]; exact Matrix.one_fin_two.symm
  · right; rw [h]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem Φ_eq_one_iff (x : SLp p) : Φ x = 1 ↔ matP p x = 1 ∨ matP p x = -1 := by
  constructor
  · intro h
    apply eq_pm_one_of_core
    intro g
    have h1 := congrArg (fun σ : Hc (Λp p) => cosetEquiv ((σ : Sym _) (cosetEquiv.symm
      (QuotientGroup.mk g)))) h
    simp only [Φ_apply, Equiv.apply_symm_apply] at h1
    have h2 : x • (QuotientGroup.mk g : SLp p ⧸ Kp p) = QuotientGroup.mk g := by
      rw [h1]; simp
    have := QuotientGroup.eq.mp h2.symm
    simpa [mul_assoc] using this
  · intro h
    apply Subtype.ext
    apply Sym.ext'
    intro y
    apply cosetEquiv.injective
    rw [Φ_apply]
    show x • cosetEquiv y = cosetEquiv y
    generalize cosetEquiv y = q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
    have hxc : x * g = g * x := by
      apply matP_injective
      rcases h with h | h <;> simp [matP_mul, h]
    have hxK : x ∈ Kp p := by
      intro i j
      rcases h with h | h <;> rw [h] <;> fin_cases i <;> fin_cases j <;> simp
    rw [smul_eq_mul, hxc]
    have : (g * x)⁻¹ * g = x⁻¹ := by group
    rw [this]; exact (Kp p).inv_mem hxK

theorem Φ_isOpenMap : IsOpenMap (Φ (p := p)) := by
  haveI := locallyCompact_Hc (Λp p) Λp_commensurated
  haveI : LocallyCompactSpace (SLp p) := isCompact_Kp.locallyCompactSpace_of_mem_nhds_of_group
    (isOpen_Kp.mem_nhds (Kp p).one_mem)
  haveI : SigmaCompactSpace (SLp p) := ⟨⟨fun n =>
      (fun q : SLp p × SLp p => q.1 * aP n * q.2) '' ((Kp p : Set (SLp p)) ×ˢ (Kp p : Set _)),
    fun n => (isCompact_Kp.prod isCompact_Kp).image
      ((continuous_fst.mul continuous_const).mul continuous_snd),
    by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨k₁, hk₁, k₂, hk₂, n, rfl⟩ := cartan x
      exact Set.mem_iUnion.mpr ⟨n, (k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩⟩⟩
  exact Φ.isOpenMap_of_sigmaCompact Φ_surjective continuous_Φ

end MzSl2
