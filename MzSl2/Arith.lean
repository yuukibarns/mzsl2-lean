import Mathlib

/-!
# Integer arithmetic used in the proof

* d751, step 2: the fixed-entry factorisation. For a fixed nonzero `a`, every integral
  determinant-one matrix with upper-left entry `a` is `v(k) γ_r u(ℓ)` with integers `k, ℓ`
  and `γ_r` from a finite list depending only on `a`.
* d751, step 3: the congruence choices `c + a k ≡ 0 (mod p^j)` for `a` prime to `p`.
* 801, step 4: for `c₀` prime to `p` some `p^k ≡ 1 (mod c₀²)` with `k ≥ 1`.
-/

open Matrix

namespace MzSl2

/-- The representative `γ_r = [[a, -y], [r, x]]` for `x a + y r = 1` (junk if not coprime). -/
noncomputable def gam (a r : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if h : IsCoprime a r then !![a, -h.choose_spec.choose; r, h.choose] else 1

theorem gam_spec {a r : ℤ} (h : IsCoprime a r) :
    ∃ x y : ℤ, x * a + y * r = 1 ∧ gam a r = !![a, -y; r, x] := by
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec, ?_⟩
  simp [gam, h]

/-- The explicit factorisation `A = v(k) γ u(ℓ)` once the first column of `v(-k) A`
equals the first column `(a, r)` of `γ`. -/
theorem fixed_entry_factor (a b c e r x y k : ℤ) (h : a * e - b * c = 1)
    (hr : x * a + y * r = 1) (hc : c = r + k * a) :
    !![a, b; c, e] =
      !![1, 0; k, 1] * !![a, -y; r, x] * !![1, x * b + y * (e - k * b); 0, 1] := by
  subst hc
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-b) * hr + (-y) * h
  · ring
  · linear_combination (x - k * y) * h - e * hr

/-- d751, step 2. For `a ≠ 0` there is a finite set `F` of integral determinant-one
matrices with upper-left entry `a` such that every integral determinant-one matrix with
upper-left entry `a` is `v(k) γ u(ℓ)` with `γ ∈ F` and `k, ℓ ∈ ℤ`. -/
theorem fixed_entry_decomp (a : ℤ) (ha : a ≠ 0) :
    ∃ F : Finset (Matrix (Fin 2) (Fin 2) ℤ),
      (∀ γ ∈ F, γ.det = 1 ∧ γ 0 0 = a) ∧
      ∀ b c e : ℤ, a * e - b * c = 1 →
        ∃ k l : ℤ, ∃ γ ∈ F, !![a, b; c, e] = !![1, 0; k, 1] * γ * !![1, l; 0, 1] := by
  classical
  refine ⟨(((Finset.range a.natAbs : Finset ℕ)).filter (fun n : ℕ => IsCoprime a (n : ℤ))).image
    (fun n : ℕ => gam a (n : ℤ)), ?_, ?_⟩
  · intro γ hγ
    simp only [Finset.mem_image, Finset.mem_filter] at hγ
    obtain ⟨n, ⟨-, hcop⟩, rfl⟩ := hγ
    obtain ⟨x, y, hxy, hg⟩ := gam_spec hcop
    rw [hg, Matrix.det_fin_two_of]
    refine ⟨by linear_combination hxy, by simp⟩
  · intro b c e h
    set r := c % a with hr_def
    set k := c / a
    have hc : c = r + k * a := by
      have := Int.emod_add_ediv_mul c a; rw [hr_def]; linarith
    have hr0 : 0 ≤ r := Int.emod_nonneg _ ha
    have hrlt : r < a.natAbs := Int.emod_lt _ ha
    have hcop : IsCoprime a r := ⟨e - b * k, -b, by rw [hc] at h; linear_combination h⟩
    obtain ⟨x, y, hxy, hg⟩ := gam_spec hcop
    refine ⟨k, x * b + y * (e - k * b), gam a r, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨r.toNat, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [Finset.mem_range]; omega
      · rwa [Int.toNat_of_nonneg hr0]
      · rw [Int.toNat_of_nonneg hr0]
    · rw [hg]; exact fixed_entry_factor a b c e r x y k h hxy hc

/-- d751, step 3: if `p ∤ a` then `c + a k ≡ 0 (mod p^j)` is solvable. -/
theorem congr_solvable {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) (c : ℤ) (j : ℕ) :
    ∃ k : ℤ, (p : ℤ) ^ j ∣ c + a * k := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime a ((p : ℤ) ^ j) :=
    ((hpZ.coprime_iff_not_dvd.mpr ha).symm).pow_right
  obtain ⟨x, y, hxy⟩ := hcop
  exact ⟨-c * x, ⟨c * y, by linear_combination (-c) * hxy⟩⟩

/-- 801, step 4: if `c₀ ≠ 0` is prime to `p` then `c₀² ∣ p^k - 1` for some `k ≥ 1`. -/
theorem exists_pow_modEq_one {p : ℕ} {c₀ : ℤ} (hc₀ : c₀ ≠ 0)
    (hcop : Nat.Coprime p (c₀.natAbs ^ 2)) :
    ∃ k : ℕ, 1 ≤ k ∧ c₀ ^ 2 ∣ (p : ℤ) ^ k - 1 := by
  set n := c₀.natAbs ^ 2
  have hn : 0 < n := by positivity
  refine ⟨n.totient, Nat.totient_pos.mpr hn, ?_⟩
  have h := (Nat.ModEq.pow_totient hcop).symm
  have h2 := (Nat.modEq_iff_dvd.mp h)
  have hn' : ((n : ℕ) : ℤ) = c₀ ^ 2 := by simp [n]
  rw [hn'] at h2
  simpa using h2

end MzSl2
