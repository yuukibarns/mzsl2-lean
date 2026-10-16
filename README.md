# Lean formalization: commensurated subgroups of SL₂(ℤ[1/p])

Lean 4 (v4.33.0-rc1) + Mathlib (commit 79d0395a).

**`MzSl2.mainTheorem : MainTheorem` is proved with no `sorry`.** It depends only on Lean's
`propext`, `Classical.choice` and `Quot.sound`, plus the external theorems assumed in
`MzSl2/Axioms.lean`. Output of `#print axioms MzSl2.mainTheorem` (2026-10-16):

```
'MzSl2.mainTheorem' depends on axioms: [propext, Classical.choice, MzSl2.bergman_lenstra,
 MzSl2.bounded_generation, MzSl2.casselman_wigner, MzSl2.levi_isClosed,
 MzSl2.normal_subgroup_theorem, MzSl2.scale_eq_one_iff, MzSl2.scale_pow, MzSl2.tidy_levi,
 Quot.sound]
```

```
LEAN_NUM_THREADS=4 lake build      # do not `lake update`: Mathlib is pinned
```

To check the axioms, run a file containing `import MzSl2` and `#print axioms MzSl2.mainTheorem`
with `lake env lean`.

## External theorems (the only axioms)

Each one is a published theorem. `Axioms.lean` states it in the narrowest form the proof needs.
All 8 were audited against the source texts on 2026-10-16: each is faithful (the published
statement or a weakening of it). See [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md).

| Axiom | Statement (case used) | Source | Checked against |
|---|---|---|---|
| `bounded_generation` | every element of SL₂(ℤ[1/p]) is a product of ≤ 9 elementary matrices | Vsemirnov, Q. J. Math. 65 (2014); Morgan–Rapinchuk–Sury, Algebra Number Theory 12 (2018) | MRS Thm 1.1 |
| `bergman_lenstra` | uniformly bounded indices $[A : A\cap bAb^{-1}]$, $b\in B$ ⇒ $A$ commensurable with a $B$-normalised subgroup | Bergman–Lenstra, J. Algebra 127 (1989) | Theorem 6(iii) (5(iii) in the preprint) |
| `normal_subgroup_theorem` | normal subgroups of SL₂(ℤ[1/p]) are finite or of finite index | Margulis, *Discrete subgroups of semisimple Lie groups* (1991), Ch. VIII Thm A | Calderoni (arXiv 2203.05135) Thm 4.14 |
| `scale_pow`, `scale_eq_one_iff` | $s(h^n)=s(h)^n$; $s(h)=s(h^{-1})=1$ ⇔ $h$ normalises a compact open subgroup | Willis, Math. Ann. 300 (1994) | Shalom–Willis, GAFA 23 (2013), Thm 2.2 |
| `levi_isClosed`, `tidy_levi` | (metrizable case) $M_g$ is closed; for a tidy $V$, $V\cap M_g\subseteq\bigcap_n g^nVg^{-n}$ | Baumgartner–Willis, Israel J. Math. 142 (2004), §3 | Rem. 3.1 / Not. 3.2 |
| `casselman_wigner` | $H^2_c(\mathrm{SL}_2(\mathbb{Q}_p),\mathbb{C})=0$ (ℝ version derived in Lean) | Casselman–Wigner, Invent. Math. 25 (1974), Cor. 2 | FMvL, J. Éc. polytech. 11 (2024), Thm 2.12 |

## Map of the proof

| Files | Content | Pharos fact |
|---|---|---|
| `Identities`, `Arith`, `GammaElems` | explicit matrix identities, congruence arithmetic, concrete elements of Γ | 801, 8de, c627, d751 |
| `Statement`, `Commensurated` | ℤ[1/p], Γ, Λ, commensuration, the **`MainTheorem`** statement; Λ commensurated; the three alternatives are exclusive and all occur | Thm 1.1 |
| `SymTop`, `Completion`, `CompletionTDLC`, `GroupBasics` | Schlichting completion `Hc L = Γ//L` as a tdlc group; `ρH`, `UH` | — |
| `Scale`, `ScaleLemmas`, `Invariant` | Willis scale; a Γ-invariant compact open subgroup from a uniscalar diagonal | c627 |
| `E69` | an infinite commensurated `N` meets SL₂(ℤ) in an infinite subgroup | e69 |
| `RelIndexChar`, `U801` | relative index character; `N` contains powers of `u(1)`, `v(1)` | 801 |
| `PadicBasics`, `Iwahori`, `Density`, `Dichotomy`, `PhiMap` | p-adics, Iwahori, density, Cartan, open-subgroup dichotomy, `Φ : SL₂(ℚ_p) → Γ//Λ` (continuous, open, onto, kernel ±1) | 8de |
| `FiberMap` | comparison map `qmap : Γ//L → Γ//Λ` | — |
| `F737a`–`F737i`, `F737` | fact 737 "(3) ⇒ (1)": `core737` | 737 |
| `D751Help`, `D751a`, `D751b` | dynamical Levi argument, fact d751, **`mainTheorem`** | d751 |
| `F8de` | finite integral index ⇒ trichotomy (`mainTheorem_of_d751`) | 8de |

### Fact 737 (`F737a`–`F737i`)

Setup: `E = ker q`.

* `F737b`: `C ≤ E` is compact, normal and relatively open.
* `F737c`: `E` is finitely generated modulo `C`.
* `F737d`: `H₀`, the kernel of the action on `E/C`, is open and of finite index.
* `F737e`: `G₀ = Γ//Λ` is perfect, has no finite quotients, and satisfies Casselman–Wigner.
* `F737f`: central extensions of `G₀` by discrete kernels split over ℤ.
* `F737g`: if `[E : C] = ∞`, then `E ∩ H₀` maps onto ℤ (structure theorem for finitely generated
  abelian groups).
* `F737h`: this map extends to a continuous homomorphism `H₀ → ℤ`.
* `F737i`: every such homomorphism is zero (normal subgroup theorem).

So `[E : C] < ∞`, `E` is compact, and `[Λ : L] < ∞` (`F737a`).

## Building from a fresh clone

```
lake exe cache get                 # download prebuilt Mathlib
LEAN_NUM_THREADS=4 lake build
```
