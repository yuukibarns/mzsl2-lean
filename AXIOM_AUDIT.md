# Audit of the external axioms (2026-10-16)

Question: is each axiom in `MzSl2/Axioms.lean` (a) a faithful statement of a published theorem,
i.e. never stronger than what the source proves, and (b) well established?

Method: for each axiom I read the theorem in the source text, then compared it symbol by symbol
with the Lean statement, including the definitions it uses (`scale`, `levi`, `u`, `v`, `R p`,
`Γ p`, `ConjAct` conventions, `relIndex`) and the topology instances. The source texts are the
local copies in `~/Documents/codex/Pharos/runtime/projects/mzsl2/literature/papers/`, plus the
original Casselman–Wigner, Willis (1994) and Willis (2001) articles (read 2026-10-16). DOIs and free copies of
every source are in `REFERENCES.md`.

**Verdict: all 8 axioms are faithful.** Each one is the published statement, or a special case or
weakening of it, in the setting where it is used. All 8 are well established. One axiom was
reworded in this audit: Casselman–Wigner is now stated with `ℂ` coefficients, exactly as in the
original Corollary 2, and the real version used in the proof is derived in Lean.

## Conventions checked in Lean

* `ConjAct.toConjAct g • V = gVg⁻¹` (`mem_conjAct_smul_iff`: `x ∈ g • V ↔ g⁻¹xg ∈ V`).
* `V.relIndex K = [K : V ∩ K]`; it is `0` exactly when the index is infinite.
* `R p = {a/pⁿ}` = ℤ[1/p]; `Γ p` = matrices in SL₂(ℚ) with entries in ℤ[1/p];
  `u t = !![1,t;0,1]`, `v t = !![1,0;t,1]`.
* **Topology on SL₂(ℚ_p)** (`SpecialLinearGroup (Fin 2) ℚ_[p]`): checked by `rfl` to be the
  subspace topology of 2×2 matrices over ℚ_p with Mathlib's p-adic metric. This matters:
  with any other topology (for example the discrete one) Casselman–Wigner would be false.

## The axioms

| # | Axiom | Source text read | Comparison |
|---|---|---|---|
| 1 | `bounded_generation` | Morgan–Rapinchuk–Sury, *Algebra Number Theory* 12 (2018), **Thm 1.1** (arXiv 1708.09262v3): "Let O be the ring of S-integers in a number field k, and assume that O× is infinite. Then every matrix in SL₂(O) is a product of at most 9 elementary matrices." | ℤ[1/p] has infinitely many units (±pᵏ). Elementary matrices are E₁₂(a) = `u a`, E₂₁(b) = `v b`. **Exact special case.** Vsemirnov (Q. J. Math. 65, 2014) proved ≤ 5 for ℤ[1/p]. The 2026 survey by Kunyavskiĭ–Morris–Rapinchuk (arXiv 2606.21817) cites both results as established. |
| 2 | `bergman_lenstra` | Bergman–Lenstra, *J. Algebra* 127 (1989), **Thm 6(iii)** (Thm 5(iii) in the author preprint read here): for subgroups H, K ≤ G, the indices [H : H ∩ kHk⁻¹], k ∈ K, have a finite upper bound iff H is commensurable with a subgroup N normalised by K. | Lean: `(b • A).relIndex A = [A : A ∩ bAb⁻¹]`, finite (`≠ 0`) and `≤ n` for b ∈ B (a subgroup). Conclusion: `Commensurable J A`, and `b • J = J` for b ∈ B. **Exact (⇒ direction).** |
| 3 | `normal_subgroup_theorem` | Margulis, *Discrete subgroups of semisimple Lie groups* (1991), **Ch. VIII Thm A**, as stated in Calderoni (arXiv 2203.05135, Thm 4.14): G connected, almost k-simple, Γ S-arithmetic, N ⊴ Γ, rank_S G ≥ 2 ⇒ N central or Γ/N finite. | G = SL₂/ℚ, S = {p}: rank_S = rank_ℝ + rank_{ℚ_p} = 1 + 1 = 2, and Γ = SL₂(ℤ[1/p]). Central means N ⊆ {±1}, hence finite. Lean concludes "finite or finite index". **Weakening.** |
| 4a | `scale_pow` | **Original:** Willis, *Math. Ann.* 300 (1994), §2 **Corollary 3** (p. 354): s(xⁿ) = s(x)ⁿ. Willis defines s(x) = [xK₊x⁻¹ : K₊] using a tidy subgroup. **Restatement:** Shalom–Willis, *GAFA* 23 (2013), **Def 2.1 and Thm 2.2(2)**, with s(x) = min [xVx⁻¹ : V ∩ xVx⁻¹]. | Lean's `scale` is the min formula of SW Def 2.1. **Original:** Willis, *J. Algebra* 237 (2001), **Thm 3.1** (p. 144): s_G(α) = min{[α(U) : α(U) ∩ U] : U compact open}, where s_G(α) = [α(U) : α(U) ∩ U] for U tidy (Def 2.2). This equals the 1994 value [α(U₊) : U₊] (p. 144, citing Willis 1994, proof of Lemma 1). With α = conjugation by x this is exactly `V.relIndex (ConjAct x • V)`. The setting is tdlc groups (T2, totally disconnected, locally compact). Lean assumes n ≥ 1. **Weakening.** |
| 4b | `scale_eq_one_iff` | **Restatement:** SW **Thm 2.2(1)**: s(α) = 1 = s(α⁻¹) iff α(V) = V for some compact open V. **Original:** for U tidy for x, Willis 1994 p. 354 gives s(x) = [xUx⁻¹ : U₁] and s(x⁻¹) = [U : U₁], U₁ = U ∩ xUx⁻¹. If both are 1 then xUx⁻¹ = U₁ = U (used in the proof of Prop. 4). Conversely, if x normalises a compact open V, the min formula gives 1 at once. | α = conjugation by h, so α(V) = `ConjAct h • V` and s(α⁻¹) = `scale h⁻¹`. **Exact.** |
| 5a | `levi_isClosed` | Baumgartner–Willis, *Israel J. Math.* 142 (2004), **Remark 3.1 / Notation 3.2** (arXiv math/0302095): P_α = {x : {αⁿ(x)}ₙ≥₀ bounded} is closed (Willis 1994 Prop. 3); M_α := P_α ∩ P_{α⁻¹}. | "Bounded" means relatively compact (Glöckner, *Glasgow Math. J.* 47 (2005), states M_α this way). Lean's `levi g` = {x : closure{gⁿxg⁻ⁿ : n ∈ ℤ} compact} = P_g ∩ P_{g⁻¹}, which is closed as an intersection of closed sets. Lean also assumes metrizability, which the source doesn't need. **Weakening.** |
| 5b | `tidy_levi` | same §2–3: tidy subgroups exist (Willis 1994; BW Algorithm 2.2), and "V₀ ⩽ V ∩ M_α … with equality if V is tidy", where V₀ = ⋂_{k∈ℤ} αᵏ(V). | x ∈ V ∩ M_g ⇒ x ∈ V₀ ⇒ gⁿxg⁻ⁿ ∈ V for all n ∈ ℤ, which is the Lean conclusion. **Exact (one inclusion).** |
| 6 | `casselman_wigner` | **Original:** Casselman–Wigner, *Invent. Math.* 25 (1974), §4 **Corollary 2** (p. 209, checked on the page image): "One has Hⁿ(G, ℂ) = 0 for n ≠ 0". The standing hypothesis there is that 𝔾 is simple, simply connected and isotropic. Hⁿ(G, A) is defined in §1 (p. 200) as the cohomology of the G-invariants of the complex Cⁿ(G, A) of continuous maps G^{n+1} → A. Restated in Fisher–Mj–van Limbeek 2024, Thm 2.12. | SL₂ over ℚ_p is simple, simply connected and isotropic. Lean states degree 2 with **inhomogeneous** continuous cochains: δb(x,y) = b(x) + b(y) − b(xy), plus the trivial-action cocycle identity. This is the standard equivalent form of CW's homogeneous complex: f(g₀,g₁,g₂) = φ(g₀⁻¹g₁, g₁⁻¹g₂), a bijection that preserves continuity. **Exact special case**, up to that standard translation. The ℝ version used in the proof (`casselman_wigner_real`) is proved in Lean by taking real parts. Topology checked above. |

## Remaining caveats

* **Margulis primary text.** I read Calderoni's statement of Margulis' theorem (J. Lond. Math.
  Soc. 107 (2023), Thm 4.14), not the book. Crossref confirms that the book's Chapter VIII,
  pp. 258–287, is *Normal subgroups and "abstract" homomorphisms of semisimple algebraic groups
  over global fields*, matching the citation "Ch. VIII, Thm A". Relying on this published
  restatement was a deliberate decision (2026-10-16): the theorem is classical, and Calderoni
  states it with full hypotheses in a refereed journal. The book is
  https://link.springer.com/book/9783642057212 (subscription).
* **Cochain conventions.** CW use homogeneous invariant cochains. Lean uses the equivalent
  inhomogeneous form; the translation is the standard one recorded in row 6.
* `scale_pow` and `scale_eq_one_iff` are stated for every tdlc group in every universe. That
  matches the source, which places no countability or metrizability condition on them.
