import Mathlib
import MzSl2.GroupBasics
import MzSl2.GammaElems
import MzSl2.CompletionTDLC
import MzSl2.Commensurated

/-!
# Fact e69: an infinite commensurated subgroup meets `SL₂(ℤ)` in an infinite subgroup

We avoid `p`-adic topology: "discrete in `SL₂(ℚ_p)`" becomes "meets some principal congruence
subgroup `Λ(p^r)` trivially" (`CongP r` below).

Proof (e69): if `L = N ∩ SL₂(ℤ)` is finite, `N` meets some `Λ(p^r)` trivially. The scale axioms in
the completion `Γ//N` give `M` commensurable with `N` and normalised by `u = u(1)`; `M` again
meets some `Λ(p^R)` trivially. Commutators `u(p^k) m u(-p^k) m⁻¹` lie in `M ∩ Λ(p^R)` for large
`k`, which forces `M ⊆ {±I}`, hence `N` finite.
-/

open Matrix Subgroup
open scoped Pointwise

namespace MzSl2

variable {p : ℕ} [hp : Fact p.Prime]

theorem normalizes_zpow' {G : Type*} [Group G] {L : Subgroup G} {x : G}
    (hx : ConjAct.toConjAct x • L = L) (j : ℤ) : ConjAct.toConjAct (x ^ j) • L = L := by
  have : ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct G) L := hx
  have h2 := zpow_mem this j
  rw [← map_zpow] at h2
  exact h2

theorem conj_mem_of_normalizes {G : Type*} [Group G] {L : Subgroup G} {x m : G}
    (hx : ConjAct.toConjAct x • L = L) (hm : m ∈ L) : x * m * x⁻¹ ∈ L := by
  rw [← hx, mem_conjAct_smul_iff]; simpa [mul_assoc] using hm

/-! ### Principal congruence subgroups of level `p^r` inside `Γ` -/

variable (p) in
/-- `Λ(p^r)`: integral matrices congruent to `I` modulo `p^r`, as a subgroup of `Γ`. -/
def CongP (r : ℕ) : Subgroup (Γ p) where
  carrier := {x | ∃ X : Matrix (Fin 2) (Fin 2) ℤ,
    mat p x = 1 + ((p : ℚ) ^ r) • X.map (Int.cast : ℤ → ℚ)}
  one_mem' := ⟨0, by simp [mat_one]⟩
  mul_mem' := by
    rintro x y ⟨X, hX⟩ ⟨Y, hY⟩
    refine ⟨Matrix.of fun i j => X i j + Y i j + p ^ r * (X * Y) i j, ?_⟩
    rw [mat_mul, hX, hY]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring
  inv_mem' := by
    rintro x ⟨X, hX⟩
    refine ⟨!![X 1 1, -X 0 1; -X 1 0, X 0 0], ?_⟩
    rw [mat_inv, hX, Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem CongP_antitone {r s : ℕ} (hrs : r ≤ s) : CongP p s ≤ CongP p r := by
  rintro x ⟨X, hX⟩
  refine ⟨Matrix.of fun i j => p ^ (s - r) * X i j, ?_⟩
  rw [hX]
  have e : (p : ℚ) ^ s = (p : ℚ) ^ r * (p : ℚ) ^ (s - r) := by
    rw [← pow_add, Nat.add_sub_cancel' hrs]
  ext i j
  simp [e]; ring

/-- An element lying in every `Λ(p^r)` is the identity. -/
theorem eq_one_of_forall_CongP {x : Γ p} (hx : ∀ r, x ∈ CongP p r) : x = 1 := by
  apply mat_injective
  rw [mat_one]
  ext i j
  -- `q = x_ij - δ_ij` is divisible by every power of `p`
  set q := mat p x i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j with hq
  suffices q = 0 by rw [hq] at this; linarith
  by_contra hq0
  obtain ⟨r, hr⟩ : ∃ r : ℕ, |q| < (p : ℚ) ^ r := by
    obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt |q| (by exact_mod_cast hp.out.one_lt : (1 : ℚ) < p)
    exact ⟨r, hr⟩
  obtain ⟨X, hX⟩ := hx r
  have hqe : q = (p : ℚ) ^ r * (X i j : ℚ) := by
    rw [hq, hX]; simp
  have hXne : X i j ≠ 0 := by
    intro h; rw [h] at hqe; simp at hqe; exact hq0 hqe
  have h1 : (1 : ℚ) ≤ |(X i j : ℚ)| := by
    have : (1 : ℤ) ≤ |X i j| := Int.one_le_abs hXne
    exact_mod_cast this
  have hp0 : (0 : ℚ) < (p : ℚ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  have : (p : ℚ) ^ r ≤ |q| := by
    rw [hqe, abs_mul, abs_of_pos hp0]
    nlinarith
  linarith

theorem exists_not_mem_CongP {x : Γ p} (hx : x ≠ 1) : ∃ r, x ∉ CongP p r := by
  by_contra h; push_neg at h; exact hx (eq_one_of_forall_CongP h)

/-- `Λ(p^r) ⊆ SL₂(ℤ)`. -/
theorem CongP_le_Λ (r : ℕ) : CongP p r ≤ Λ.subgroupOf (Γ p) := by
  rintro x ⟨X, hX⟩
  rw [mem_subgroupOf]
  intro i j
  have : (x : SpecialLinearGroup (Fin 2) ℚ) i j = mat p x i j := rfl
  rw [Subring.mem_bot]
  refine ⟨(1 : Matrix (Fin 2) (Fin 2) ℤ) i j + p ^ r * X i j, ?_⟩
  change _ = mat p x i j
  rw [hX]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-! ### Step 1: a finite integral part gives trivial intersection with some `Λ(p^r)` -/

theorem trivial_CongP_of_finite {N : Subgroup (Γ p)}
    (hL : ((N ⊓ Λ.subgroupOf (Γ p) : Subgroup (Γ p)) : Set (Γ p)).Finite) :
    ∃ r, ∀ x ∈ N, x ∈ CongP p r → x = 1 := by
  classical
  have hr : ∀ x : Γ p, ∃ r, x ≠ 1 → x ∉ CongP p r := by
    intro x
    by_cases hx : x = 1
    · exact ⟨0, fun h => (h hx).elim⟩
    · obtain ⟨r, hr⟩ := exists_not_mem_CongP hx; exact ⟨r, fun _ => hr⟩
  choose rx hrx using hr
  refine ⟨hL.toFinset.sup rx, fun x hxN hxC => ?_⟩
  by_contra hx1
  have hxL : x ∈ hL.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hxN, CongP_le_Λ _ hxC⟩
  exact hrx x hx1 (CongP_antitone (Finset.le_sup hxL) hxC)

/-! ### Step 2: trivial intersection passes to commensurable overgroups -/

theorem trivial_CongP_transfer {D M : Subgroup (Γ p)} (hDM : D ≤ M) (hfi : D.relIndex M ≠ 0)
    {r : ℕ} (hD : ∀ x ∈ D, x ∈ CongP p r → x = 1) :
    ∃ R, ∀ x ∈ M, x ∈ CongP p R → x = 1 := by
  classical
  -- for a fixed `m`, at most one `d ∈ D` has `m d ∈ Λ(p^r)`
  have key : ∀ m : Γ p, ∃ R, r ≤ R ∧ ∀ d ∈ D, m * d ∈ CongP p R → m * d = 1 := by
    intro m
    by_cases h : ∃ d0 ∈ D, m * d0 ∈ CongP p r
    · obtain ⟨d0, hd0, hmd0⟩ := h
      have huniq : ∀ d ∈ D, m * d ∈ CongP p r → d = d0 := by
        intro d hd hmd
        have h1 : d0⁻¹ * d ∈ D := D.mul_mem (D.inv_mem hd0) hd
        have h2 : d0⁻¹ * d ∈ CongP p r := by
          have := (CongP p r).mul_mem ((CongP p r).inv_mem hmd0) hmd
          simpa [mul_assoc] using this
        have := hD _ h1 h2
        rw [inv_mul_eq_one] at this; exact this.symm
      by_cases h1 : m * d0 = 1
      · exact ⟨r, le_rfl, fun d hd hmd => by rw [huniq d hd hmd]; exact h1⟩
      · obtain ⟨R0, hR0⟩ := exists_not_mem_CongP h1
        refine ⟨max r R0, le_max_left _ _, fun d hd hmd => ?_⟩
        have hdd := huniq d hd (CongP_antitone (le_max_left _ _) hmd)
        subst hdd
        exact (hR0 (CongP_antitone (le_max_right _ _) hmd)).elim
    · push_neg at h
      exact ⟨r, le_rfl, fun d hd hmd => (h d hd hmd).elim⟩
  choose Rm hRm hRm' using key
  haveI : (D.subgroupOf M).FiniteIndex := ⟨hfi⟩
  haveI : Fintype (M ⧸ D.subgroupOf M) := Fintype.ofFinite _
  let rep : M ⧸ D.subgroupOf M → Γ p := fun q => ((q.out : M) : Γ p)
  refine ⟨Finset.univ.sup fun q => Rm (rep q), fun x hxM hxC => ?_⟩
  set q : M ⧸ D.subgroupOf M := QuotientGroup.mk ⟨x, hxM⟩
  obtain ⟨h, he⟩ := QuotientGroup.mk_out_eq_mul (D.subgroupOf M) (⟨x, hxM⟩ : M)
  have hrep : rep q = x * ((h : M) : Γ p) := by
    have := congrArg Subtype.val he; simpa using this
  have hx : x = rep q * ((h : M) : Γ p)⁻¹ := by rw [hrep]; group
  have hhD : ((h : M) : Γ p)⁻¹ ∈ D := D.inv_mem (mem_subgroupOf.mp h.2)
  have hle : Rm (rep q) ≤ Finset.univ.sup fun q => Rm (rep q) :=
    Finset.le_sup (f := fun q => Rm (rep q)) (Finset.mem_univ q)
  rw [hx] at hxC ⊢
  exact hRm' _ _ hhD (CongP_antitone hle hxC)

/-! ### Step 3: a subgroup normalised by `u(1)` meeting `Λ(p^R)` trivially is `⊆ {±I}` -/

theorem comm_formula {K : Type*} [Field K] (a b c d n : K) (h : a * d - b * c = 1) :
    u n * !![a, b; c, d] * u (-n) * !![d, -b; -c, a] =
      !![1 + n * a * c + n ^ 2 * c ^ 2, n * (1 - a ^ 2) - n ^ 2 * a * c; n * c ^ 2, 1 - n * a * c] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [u, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination h | linear_combination n * h

theorem mat_eq_entries (x : Γ p) :
    mat p x = !![mat p x 0 0, mat p x 0 1; mat p x 1 0, mat p x 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem det_mat (x : Γ p) : mat p x 0 0 * mat p x 1 1 - mat p x 0 1 * mat p x 1 0 = 1 := by
  have := (x : SpecialLinearGroup (Fin 2) ℚ).2
  rw [Matrix.det_fin_two] at this
  exact this

theorem R_pow_mem (k : ℕ) : ((p : ℚ) ^ k) ∈ R p := (R p).pow_mem R_p k

theorem subset_pm_one {M : Subgroup (Γ p)} (hMu : ConjAct.toConjAct (uΓ (p := p) 1 R_one) • M = M)
    {t : ℕ} (hM : ∀ x ∈ M, x ∈ CongP p t → x = 1) :
    ∀ m ∈ M, m = 1 ∨ m = wγ p ^ 2 := by
  intro m hm
  set a := mat p m 0 0
  set b := mat p m 0 1
  set c := mat p m 1 0
  set d := mat p m 1 1
  have hdet : a * d - b * c = 1 := det_mat m
  obtain ⟨e, he⟩ := Γ_clear p m.2
  have hent : ∀ i j, ∃ z : ℤ, (p : ℚ) ^ e * mat p m i j = z := by
    intro i j; obtain ⟨z, hz⟩ := Subring.mem_bot.mp (he i j); exact ⟨z, hz.symm⟩
  obtain ⟨α, hα⟩ := hent 0 0
  obtain ⟨β, hβ⟩ := hent 0 1
  obtain ⟨γ, hγ⟩ := hent 1 0
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpe : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ hp0
  -- the commutator with `u(p^k)`, `k = R + 2e`
  set k := t + 2 * e
  set n : ℚ := (p : ℚ) ^ k
  have hn0 : n ≠ 0 := pow_ne_zero _ hp0
  set cm := uΓ n (R_pow_mem k) * m * uΓ (-n) ((R p).neg_mem (R_pow_mem k)) * m⁻¹
  have hcmM : cm ∈ M := by
    have hu : ∀ t : ℚ, ∀ ht : t ∈ R p, (∃ j : ℤ, t = j) → ∀ x ∈ M, uΓ t ht * x * (uΓ t ht)⁻¹ ∈ M := by
      rintro t ht ⟨j, rfl⟩ x hx
      have : uΓ (j : ℚ) ht = uΓ 1 R_one ^ j := by rw [uΓ_zpow]; congr 1; ring
      rw [this]; exact conj_mem_of_normalizes (normalizes_zpow' hMu j) hx
    have h1 : uΓ n (R_pow_mem k) * m * (uΓ n (R_pow_mem k))⁻¹ ∈ M :=
      hu n _ ⟨(p : ℤ) ^ k, by simp [n]⟩ m hm
    have hinv : (uΓ n (R_pow_mem k))⁻¹ = uΓ (-n) ((R p).neg_mem (R_pow_mem k)) := by
      rw [inv_eq_iff_mul_eq_one, uΓ_mul]; convert uΓ_zero using 2; ring
    rw [hinv] at h1
    exact M.mul_mem h1 (M.inv_mem hm)
  have hmat : mat p cm = !![1 + n * a * c + n ^ 2 * c ^ 2, n * (1 - a ^ 2) - n ^ 2 * a * c;
      n * c ^ 2, 1 - n * a * c] := by
    simp only [cm, mat_mul, mat_inv, mat_uΓ]
    rw [mat_eq_entries m, Matrix.adjugate_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    exact comm_formula a b c d n hdet
  have hcmC : cm ∈ CongP p t := by
    refine ⟨!![α * γ + p ^ k * γ ^ 2, p ^ (2 * e) - α ^ 2 - p ^ k * α * γ; γ ^ 2, -(α * γ)], ?_⟩
    rw [hmat]
    have ha : a = α / (p : ℚ) ^ e := by show mat p m 0 0 = _; rw [← hα]; field_simp
    have hc : c = γ / (p : ℚ) ^ e := by show mat p m 1 0 = _; rw [← hγ]; field_simp
    rw [ha, hc]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, n, k, pow_add, pow_mul] <;> (try field_simp) <;> ring
  have hcm1 := hM cm hcmM hcmC
  have hcm1' : mat p cm = 1 := by rw [hcm1, mat_one]
  rw [hmat] at hcm1'
  have e10 := congrFun (congrFun hcm1' 1) 0
  have e01 := congrFun (congrFun hcm1' 0) 1
  simp at e10 e01
  have hc0 : c = 0 := by
    rcases e10 with h | h
    · exact absurd h hn0
    · exact h
  rw [hc0] at e01
  simp at e01
  have ha2 : a ^ 2 = 1 := by
    rcases e01 with h | h
    · exact absurd h hn0
    · linarith
  rw [hc0] at hdet
  have hda : d = a := by
    have : a * d = 1 := by linarith
    have ha' : a * a = 1 := by rw [← sq]; exact ha2
    calc d = d * (a * a) := by rw [ha']; ring
      _ = (a * d) * a := by ring
      _ = a := by rw [this]; ring
  -- now `m = [[a, b], [0, a]]`; kill `b` with the powers of `m²`
  have hm2 : mat p (m ^ 2) = u (2 * a * b) := by
    rw [mat_pow, mat_eq_entries m]
    show !![a, b; c, d] ^ 2 = _
    rw [hc0, hda, sq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [u, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination ha2
  set k2 := t + e
  have hm2C : (m ^ 2) ^ (p ^ k2) ∈ CongP p t := by
    have hb : b = β / (p : ℚ) ^ e := by show mat p m 0 1 = _; rw [← hβ]; field_simp
    have ha1 : a = 1 ∨ a = -1 := by
      have : (a - 1) * (a + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, a = σ := by rcases ha1 with h | h <;> [exact ⟨1, by simp [h]⟩; exact ⟨-1, by simp [h]⟩]
    refine ⟨!![0, 2 * σ * β; 0, 0], ?_⟩
    rw [mat_pow, hm2, u_pow, hσ, hb]
    ext i j; fin_cases i <;> fin_cases j <;> simp [u, Matrix.one_apply, k2, pow_add] <;>
      (try field_simp) <;> ring
  have hm2M : (m ^ 2) ^ (p ^ k2) ∈ M := M.pow_mem (M.pow_mem hm 2) _
  have h1 := hM _ hm2M hm2C
  have h1' : mat p ((m ^ 2) ^ (p ^ k2)) = 1 := by rw [h1, mat_one]
  rw [mat_pow, hm2, u_pow] at h1'
  have e01' := congrFun (congrFun h1' 0) 1
  simp [u] at e01'
  have hb0 : b = 0 := by
    rcases e01' with h | h | h
    · exact absurd h.1 hp.out.ne_zero
    · rw [h] at ha2; simp at ha2
    · exact h
  -- conclude
  have ha1 : a = 1 ∨ a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases ha1 with h | h
  · left
    apply mat_injective
    rw [mat_eq_entries m, mat_one]
    show !![a, b; c, d] = 1
    rw [hc0, hda, hb0, h]; exact Matrix.one_fin_two.symm
  · right
    apply mat_injective
    rw [mat_eq_entries m, mat_pow, mat_wγ]
    show !![a, b; c, d] = _
    rw [hc0, hda, hb0, h]
    ext i j; fin_cases i <;> fin_cases j <;> simp [w, sq, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Fact e69 -/

/-- **Fact e69.** If `N ≤ Γ` is commensurated by `Γ` and `N ∩ SL₂(ℤ)` is finite, `N` is finite. -/
theorem finite_of_finite_integral {N : Subgroup (Γ p)} (hN : IsCommensurated N)
    (hL : ((N ⊓ Λ.subgroupOf (Γ p) : Subgroup (Γ p)) : Set (Γ p)).Finite) :
    (N : Set (Γ p)).Finite := by
  haveI := locallyCompact_Hc N hN
  -- `u(1)` normalises a compact open subgroup of `Γ//N`
  obtain ⟨V, hV, hVn⟩ := exists_normalized_of_divisible (exists_compactOpen N hN)
    hp.out.two_le (h := ρH N (uΓ (p := p) 1 R_one)) (by
      intro r; obtain ⟨k, hk⟩ := uΓ_divisible (p := p) 1 R_one r
      exact ⟨ρH N k, by rw [← map_pow, hk]⟩)
  set M := V.comap (ρH N)
  have hMu : ConjAct.toConjAct (uΓ (p := p) 1 R_one) • M = M := by
    ext x
    rw [mem_conjAct_smul_iff]
    simp only [M, mem_comap, map_mul, map_inv]
    conv_rhs => rw [← hVn]
    rw [mem_conjAct_smul_iff]
  have hcomm : Commensurable M N := by
    have h := MzSl2.Commensurable.comap (ρH N) (hV.commensurable (UH_isCompactOpen N hN))
    have hN' : (UH N).comap (ρH N) = N := by ext x; exact ρH_mem_UH_iff N x
    rwa [hN'] at h
  obtain ⟨r, hr⟩ := trivial_CongP_of_finite hL
  obtain ⟨R, hR⟩ := trivial_CongP_transfer (D := N ⊓ M) (M := M) inf_le_right
    (by rw [Subgroup.inf_relIndex_right]; exact hcomm.2)
    (fun x hx hxC => hr x hx.1 hxC)
  have hpm := subset_pm_one hMu hR
  have hMfin : (M : Set (Γ p)).Finite :=
    (Set.toFinite ({1, wγ p ^ 2} : Set (Γ p))).subset fun m hm => by
      rcases hpm m hm with h | h <;> simp [h]
  exact finite_of_finite_of_relIndex (D := M ⊓ N) (hMfin.subset fun x hx => hx.1)
    (by rw [Subgroup.inf_relIndex_right]; exact hcomm.1)

end MzSl2
