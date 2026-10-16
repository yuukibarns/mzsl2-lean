import Mathlib
import MzSl2.Scale
import MzSl2.Statement

/-!
# External theorems, assumed as axioms

These are the only results assumed without proof. Each is a published theorem, stated here in
the narrowest form the proof needs. `#print axioms MzSl2.mainTheorem` lists exactly these (plus
Lean's `propext`, `Classical.choice`, `Quot.sound`).

1. `bounded_generation`: M. Vsemirnov, *Short unitriangular factorizations of SL₂(ℤ[1/p])*,
   Q. J. Math. 65 (2014); B. Morgan, A. Rapinchuk, B. Sury, *Bounded generation of SL₂ over
   rings of S-integers with infinitely many units*, Algebra Number Theory 12 (2018), Thm 1.1:
   every element of `SL₂(ℤ[1/p])` is a product of at most 9 elementary matrices.
2. `bergman_lenstra`: G. Bergman, H. Lenstra, *Subgroups close to normal subgroups*,
   J. Algebra 127 (1989), Theorem 6(iii) (Theorem 5(iii) in the author preprint on file).
3. `normal_subgroup_theorem`: G. Margulis, *Discrete subgroups of semisimple Lie groups* (1991),
   Ch. VIII Thm A (S-arithmetic form, S-rank 2), for `SL₂(ℤ[1/p])`: normal subgroups are
   central (hence finite) or of finite index.
4. `scale_pow`, `scale_eq_one_iff`: G. Willis, *The structure of totally disconnected, locally
   compact groups*, Math. Ann. 300 (1994), §2: Corollary 3 (`s(xⁿ) = s(x)ⁿ`), and the identities
   `s(x) = [xUx⁻¹ : U ∩ xUx⁻¹]`, `s(x⁻¹) = [U : U ∩ xUx⁻¹]` for `U` tidy (p. 354). Willis defines
   `s` via tidy subgroups; that it equals the minimum used here is Willis, J. Algebra 237 (2001),
   Thm 3.1, as stated in Shalom–Willis, GAFA 23 (2013), Def. 2.1 and Thm 2.2(1),(2).
5. `levi_isClosed`, `tidy_levi`: U. Baumgartner, G. Willis, *Contraction groups and scales of
   automorphisms of totally disconnected locally compact groups*, Israel J. Math. 142 (2004),
   §3 (metrizable case): `M_g = P_g ∩ P_{g⁻¹}` is closed (Remark 3.1, via Willis 1994 Prop. 3),
   and for a tidy `V` (which exists, Willis 1994), `V ∩ M_g = V₀ = ⋂ₙ gⁿ V g⁻ⁿ` (Remark 3.1 and
   the remarks after Notation 3.2).
6. `casselman_wigner`: W. Casselman, D. Wigner, *Continuous cohomology and a conjecture of
   Serre's*, Invent. Math. 25 (1974), §4, Corollary 2 (p. 209): for `G` the rational points of a
   simple, simply connected, isotropic group over `ℚ_p`, `Hⁿ(G, ℂ) = 0` for `n ≠ 0`. There `Hⁿ`
   is the cohomology of `G`-invariant continuous homogeneous cochains `G^{n+1} → ℂ` (§1, p. 200);
   in degree 2 this is equivalent to the inhomogeneous form below. Stated here for `SL₂(ℚ_p)`:
   every continuous complex 2-cocycle is the coboundary of a continuous 1-cochain.
   The real version `casselman_wigner_real` is derived below by taking real parts.
-/

open Topology Set Subgroup Matrix
open scoped Pointwise

namespace MzSl2

/-- 1. Bounded elementary generation of `SL₂(ℤ[1/p])`. -/
axiom bounded_generation (p : ℕ) [Fact p.Prime] (g : SpecialLinearGroup (Fin 2) ℚ)
    (hg : g ∈ Γ p) :
    ∃ l : List (Matrix (Fin 2) (Fin 2) ℚ), l.length ≤ 9 ∧
      (∀ m ∈ l, ∃ a ∈ R p, m = u a ∨ m = v a) ∧
      l.prod = (g : Matrix (Fin 2) (Fin 2) ℚ)

/-- 2. Bergman–Lenstra: if the indices `[A : A ∩ bAb⁻¹]`, `b ∈ B`, are finite and uniformly
bounded, then `A` is commensurable with a subgroup normalised by `B`. -/
axiom bergman_lenstra {E : Type*} [Group E] (A B : Subgroup E) (n : ℕ)
    (hn : ∀ b ∈ B, (ConjAct.toConjAct b • A).relIndex A ≠ 0 ∧
      (ConjAct.toConjAct b • A).relIndex A ≤ n) :
    ∃ J : Subgroup E, Commensurable J A ∧ ∀ b ∈ B, ConjAct.toConjAct b • J = J

/-- 3. Margulis' normal subgroup theorem for `SL₂(ℤ[1/p])`. -/
axiom normal_subgroup_theorem (p : ℕ) [Fact p.Prime] (N : Subgroup (SpecialLinearGroup (Fin 2) ℚ))
    (hN : N ≤ Γ p) (hnorm : ∀ g ∈ Γ p, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    (N : Set (SpecialLinearGroup (Fin 2) ℚ)).Finite ∨ N.relIndex (Γ p) ≠ 0

/-- 4a. Willis: the scale is multiplicative on positive powers. -/
axiom scale_pow {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [TotallyDisconnectedSpace H] [LocallyCompactSpace H] (h : H) (n : ℕ) (hn : 1 ≤ n) :
    scale (h ^ n) = scale h ^ n

/-- 4b. Willis: `h` and `h⁻¹` have scale one iff `h` normalises a compact open subgroup. -/
axiom scale_eq_one_iff {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [TotallyDisconnectedSpace H] [LocallyCompactSpace H] (h : H) :
    (scale h = 1 ∧ scale h⁻¹ = 1) ↔
      ∃ V : Subgroup H, IsCompactOpenSubgroup V ∧ ConjAct.toConjAct h • V = V

/-- 5a. Baumgartner–Willis: the dynamical Levi subgroup is closed (metrizable case). -/
axiom levi_isClosed {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [TotallyDisconnectedSpace H] [LocallyCompactSpace H] [TopologicalSpace.MetrizableSpace H]
    (g : H) : IsClosed (levi g)

/-- 5b. Baumgartner–Willis: some compact open subgroup `V` (a tidy one) satisfies
`V ∩ M_g ⊆ ⋂ₙ gⁿ V g⁻ⁿ`. -/
axiom tidy_levi {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [TotallyDisconnectedSpace H] [LocallyCompactSpace H] [TopologicalSpace.MetrizableSpace H]
    (g : H) :
    ∃ V : Subgroup H, IsCompactOpenSubgroup V ∧
      ∀ x ∈ V, x ∈ levi g → ∀ n : ℤ, g ^ n * x * g ^ (-n) ∈ V

/-- 6. Casselman–Wigner: `H²_c(SL₂(ℚ_p), ℂ) = 0` with trivial coefficients. -/
axiom casselman_wigner (p : ℕ) [Fact p.Prime]
    (f : SpecialLinearGroup (Fin 2) ℚ_[p] × SpecialLinearGroup (Fin 2) ℚ_[p] → ℂ)
    (hf : Continuous f)
    (hcoc : ∀ x y z, f (y, z) - f (x * y, z) + f (x, y * z) - f (x, y) = 0) :
    ∃ b : SpecialLinearGroup (Fin 2) ℚ_[p] → ℂ, Continuous b ∧
      ∀ x y, f (x, y) = b x + b y - b (x * y)

/-- `H²_c(SL₂(ℚ_p), ℝ) = 0`: take real parts in `casselman_wigner`. -/
theorem casselman_wigner_real (p : ℕ) [Fact p.Prime]
    (f : SpecialLinearGroup (Fin 2) ℚ_[p] × SpecialLinearGroup (Fin 2) ℚ_[p] → ℝ)
    (hf : Continuous f)
    (hcoc : ∀ x y z, f (y, z) - f (x * y, z) + f (x, y * z) - f (x, y) = 0) :
    ∃ b : SpecialLinearGroup (Fin 2) ℚ_[p] → ℝ, Continuous b ∧
      ∀ x y, f (x, y) = b x + b y - b (x * y) := by
  obtain ⟨b, hb, hbe⟩ := casselman_wigner p (fun xy => (f xy : ℂ))
    (Complex.continuous_ofReal.comp hf) (fun x y z => by exact_mod_cast hcoc x y z)
  refine ⟨fun x => (b x).re, Complex.continuous_re.comp hb, fun x y => ?_⟩
  have := congrArg Complex.re (hbe x y)
  simpa using this

end MzSl2
