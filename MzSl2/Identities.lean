import Mathlib

/-!
# Explicit matrix identities in the proof

Every explicit matrix computation used by the Pharos proof (facts 801e842024af9f58,
d751ba710b0e8e3c, c627cc3578f66eb7, 8de6b78010939f8d), checked over an arbitrary field.
Inverses are written out (all matrices have determinant one), so each identity is a
plain matrix equation.
-/

open Matrix

namespace MzSl2

variable {K : Type*} [Field K]

/-- Upper root element `u(t) = [[1,t],[0,1]]`. -/
def u (t : K) : Matrix (Fin 2) (Fin 2) K := !![1, t; 0, 1]

/-- Lower root element `v(t) = [[1,0],[t,1]]`. -/
def v (t : K) : Matrix (Fin 2) (Fin 2) K := !![1, 0; t, 1]

/-- Diagonal element `diag(t, t⁻¹)`; the paper's `d` is `dg p`. -/
def dg (t : K) : Matrix (Fin 2) (Fin 2) K := !![t, 0; 0, t⁻¹]

/-- The Weyl element `w = [[0,-1],[1,0]]`. -/
def w : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, 0]

/-- `w(t) = u(t) v(-t⁻¹) u(t)`. -/
def wt (t : K) : Matrix (Fin 2) (Fin 2) K := u t * v (-t⁻¹) * u t

/-- Expand all definitions to explicit 2×2 matrices and compare entries. -/
macro "mat_solve" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [u, v, dg, w, wt, Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;>
    first | ring1 | simp))

/-! ### Root groups -/

theorem u_mul_u (a b : K) : u a * u b = u (a + b) := by mat_solve

theorem v_mul_v (a b : K) : v a * v b = v (a + b) := by mat_solve

theorem u_zero : u (0 : K) = 1 := by mat_solve

theorem v_zero : v (0 : K) = 1 := by mat_solve

theorem u_pow (a : K) (n : ℕ) : u a ^ n = u (n * a) := by
  induction n with
  | zero => simp [u_zero]
  | succ n ih => rw [pow_succ, ih, u_mul_u]; push_cast; ring_nf

theorem v_pow (a : K) (n : ℕ) : v a ^ n = v (n * a) := by
  induction n with
  | zero => simp [v_zero]
  | succ n ih => rw [pow_succ, ih, v_mul_v]; push_cast; ring_nf

theorem dg_mul_dg (s t : K) : dg s * dg t = dg (s * t) := by mat_solve

theorem dg_pow (s : K) (n : ℕ) : dg s ^ n = dg (s ^ n) := by
  induction n with
  | zero => mat_solve
  | succ n ih => rw [pow_succ, ih, dg_mul_dg, pow_succ]

theorem dg_mul_dg_inv {s : K} (hs : s ≠ 0) : dg s * dg s⁻¹ = 1 := by mat_solve

/-! ### Diagonal action on root groups (c627, 801, d751) -/

/-- `d u(t) d⁻¹ = u(s² t)`; for `s = p` this is `d u(t) d⁻¹ = u(p² t)`. -/
theorem dg_conj_u {s : K} (hs : s ≠ 0) (t : K) : dg s * u t * dg s⁻¹ = u (s ^ 2 * t) := by
  mat_solve

/-- `d v(t) d⁻¹ = v(t / s²)`, equivalently `d⁻¹ v(t) d = v(s² t)`. -/
theorem dg_conj_v {s : K} (hs : s ≠ 0) (t : K) : dg s * v t * dg s⁻¹ = v (t / s ^ 2) := by
  mat_solve

theorem dg_inv_conj_v {s : K} (hs : s ≠ 0) (t : K) : dg s⁻¹ * v t * dg s = v (s ^ 2 * t) := by
  mat_solve

/-- Conjugating a general matrix by the diagonal (d751, step 3):
`d M d⁻¹ = [[a, s² b], [c / s², e]]`. -/
theorem dg_conj {s : K} (hs : s ≠ 0) (a b c e : K) :
    dg s * !![a, b; c, e] * dg s⁻¹ = !![a, s ^ 2 * b; c / s ^ 2, e] := by
  mat_solve

/-- `w d w⁻¹ = d⁻¹` (used in 801 step 2 and c627). Here `w⁻¹ = -w`. -/
theorem w_conj_dg {s : K} (hs : s ≠ 0) : w * dg s * (-w) = dg s⁻¹ := by mat_solve

theorem w_mul_neg_w : w * (-w) = (1 : Matrix (Fin 2) (Fin 2) K) := by mat_solve

/-- c627: elementary matrices are products of powers of `d`, `u(1)`, `v(1)`:
`u(a) = d^{-r} u(1)^b d^{r}` with `a = b / s^{2r}`. -/
theorem u_eq_dg_conj {s : K} (hs : s ≠ 0) (r : ℕ) (b : ℕ) :
    dg (s ^ r)⁻¹ * u 1 ^ b * dg (s ^ r) = u ((b : K) / s ^ (2 * r)) := by
  have hsr : (s ^ r) ≠ 0 := pow_ne_zero _ hs
  rw [u_pow]
  have := dg_conj_u (inv_ne_zero hsr) ((b : K) * 1)
  rw [inv_inv] at this
  rw [this]; congr 1; field_simp; ring

theorem v_eq_dg_conj {s : K} (hs : s ≠ 0) (r : ℕ) (b : ℕ) :
    dg (s ^ r) * v 1 ^ b * dg (s ^ r)⁻¹ = v ((b : K) / s ^ (2 * r)) := by
  have hsr : (s ^ r) ≠ 0 := pow_ne_zero _ hs
  rw [v_pow, dg_conj_v hsr]; congr 1; field_simp; ring

/-! ### Fact 801, step 4: the relation putting a power of `d` in the root subgroup -/

/-- `u((t-1)/c²) v(c²) u((t⁻¹-1)/c²) v(-t c²) = diag(t, t⁻¹)`. -/
theorem key_801 {c t : K} (hc : c ≠ 0) (ht : t ≠ 0) :
    u ((t - 1) / c ^ 2) * v (c ^ 2) * u ((t⁻¹ - 1) / c ^ 2) * v (-t * c ^ 2) = dg t := by
  mat_solve

/-- The intermediate products quoted in 801. -/
theorem key_801_step1 {c t : K} (hc : c ≠ 0) :
    u ((t - 1) / c ^ 2) * v (c ^ 2) = !![t, (t - 1) / c ^ 2; c ^ 2, 1] := by mat_solve

theorem key_801_step2 {c t : K} (hc : c ≠ 0) (ht : t ≠ 0) :
    !![t, (t - 1) / c ^ 2; c ^ 2, 1] * u ((t⁻¹ - 1) / c ^ 2) = !![t, 0; c ^ 2, t⁻¹] := by
  mat_solve

/-- `r m = [[0, -1/c], [c, e]]` for `r = u(-a/c)` and `m = [[a,b],[c,e]]` of determinant 1. -/
theorem r_mul_m {a b c e : K} (hc : c ≠ 0) (hdet : a * e - b * c = 1) :
    u (-a / c) * !![a, b; c, e] = !![0, -1 / c; c, e] := by
  obtain rfl : b = (a * e - 1) / c := by rw [eq_div_iff hc]; linear_combination -hdet
  mat_solve

/-- `r m u(x) m⁻¹ r⁻¹ = v(-c² x)`, with `m⁻¹ = [[e,-b],[-c,a]]` and `r⁻¹ = u(a/c)`. -/
theorem conj_801 {a b c e : K} (hc : c ≠ 0) (hdet : a * e - b * c = 1) (x : K) :
    u (-a / c) * !![a, b; c, e] * u x * !![e, -b; -c, a] * u (a / c) = v (-c ^ 2 * x) := by
  obtain rfl : b = (a * e - 1) / c := by rw [eq_div_iff hc]; linear_combination -hdet
  mat_solve

/-- `r⁻¹ d^k r = u(a(1-t²)/c) d^k` with `d^k = diag(t,t⁻¹)` and `r = u(-a/c)`. -/
theorem corr_801 {a c t : K} (hc : c ≠ 0) (ht : t ≠ 0) :
    u (a / c) * dg t * u (-a / c) = u (a * (1 - t ^ 2) / c) * dg t := by
  mat_solve

/-- `m` and `[[e,-b],[-c,a]]` are inverse when `det m = 1`. -/
theorem adj_mul {a b c e : K} (hdet : a * e - b * c = 1) :
    !![a, b; c, e] * !![e, -b; -c, a] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

/-! ### Fact 8de: open subgroups of `SL₂(ℚ_p)` -/

/-- `u(-1/t) v(t) u(x) v(t)⁻¹ u(1/t) = v(-t² x)`. -/
theorem conj_8de {t : K} (ht : t ≠ 0) (x : K) :
    u (-1 / t) * v t * u x * v (-t) * u (1 / t) = v (-t ^ 2 * x) := by
  mat_solve

/-- `w(t) w(-1) = diag(t, t⁻¹)`: diagonal matrices are products of root elements. -/
theorem wt_mul_wt {t : K} (ht : t ≠ 0) : wt t * wt (-1) = dg t := by mat_solve

/-- `w = u(-1) v(1) u(-1)`, used to swap rows in 8de. -/
theorem w_eq : u (-1) * v 1 * u (-1) = (w : Matrix (Fin 2) (Fin 2) K) := by mat_solve

end MzSl2
