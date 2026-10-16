# References for the axioms

The formal proof assumes eight published theorems, stated in `MzSl2/Axioms.lean`. This file gives,
for each one, the exact place in the literature, the DOI, and a legal free copy where one exists.
The PDFs are not copied into this repository because most of them are under publisher copyright.
Where a licence permits it, an image of the theorem statement is in [`excerpts/`](excerpts/README.md).

All DOIs were checked against Crossref and all arXiv identifiers against the arXiv API
(2026-10-16). Open-access copies were located with OpenAlex. The "Read for the audit" column says
which text was actually compared with the Lean statement (see `AXIOM_AUDIT.md`).

| Axiom | Theorem | Publication | Free copy | Read for the audit |
|---|---|---|---|---|
| `bounded_generation` | Thm 1.1 | A. V. Morgan, A. S. Rapinchuk, B. Sury, *Bounded generation of SL₂ over rings of S-integers with infinitely many units*, Algebra Number Theory **12** (2018), 1949–1974. [doi:10.2140/ant.2018.12.1949](https://doi.org/10.2140/ant.2018.12.1949) | [arXiv:1708.09262](https://arxiv.org/abs/1708.09262) | arXiv v3 |
| (same, ℤ[1/p] case) | main theorem | M. Vsemirnov, *Short unitriangular factorizations of SL₂(ℤ[1/p])*, Q. J. Math. **65** (2014), 279–290. [doi:10.1093/qmath/has044](https://doi.org/10.1093/qmath/has044) | none known | — (cited for priority only) |
| `bergman_lenstra` | Thm 6(iii) (Thm 5(iii) in the preprint) | G. M. Bergman, H. W. Lenstra, Jr., *Subgroups close to normal subgroups*, J. Algebra **127** (1989), 80–97. [doi:10.1016/0021-8693(89)90275-5](https://doi.org/10.1016/0021-8693(89)90275-5) | free to read at the DOI (Elsevier open archive); preprint listed at [hdl:1887/3827](https://hdl.handle.net/1887/3827) (Leiden; not opened) | author preprint |
| `normal_subgroup_theorem` | Ch. VIII (*Normal subgroups and "abstract" homomorphisms of semisimple algebraic groups over global fields*, pp. 258–287), Thm A | G. A. Margulis, *Discrete Subgroups of Semisimple Lie Groups*, Ergeb. Math. Grenzgeb. (3) **17**, Springer, 1991. DOI 10.1007/978-3-642-51445-6; ISBN 978-3-642-05721-2 (print). [SpringerLink](https://link.springer.com/book/9783642057212) (subscription; the DOI's own redirect is broken). | none (book; use a library copy) | statement as quoted in Calderoni, Thm 4.14 |
| (statement used) | Thm 4.14 | F. Calderoni, *Rotation equivalence and cocycle superrigidity*, J. Lond. Math. Soc. **107** (2023), 189–212. [doi:10.1112/jlms.12684](https://doi.org/10.1112/jlms.12684) | open access (CC BY-NC-ND) at the DOI; [arXiv:2203.05135](https://arxiv.org/abs/2203.05135) | arXiv v2 |
| `scale_pow`, `scale_eq_one_iff` | as summarized in Shalom–Willis, Thm 2.2(1),(2) | G. A. Willis, *The structure of totally disconnected, locally compact groups*, Math. Ann. **300** (1994), 341–363. [doi:10.1007/BF01450491](https://doi.org/10.1007/BF01450491) | none known | original (§2, Cor. 3 and p. 354), and Shalom–Willis |
| (statement used) | Def 2.1, Thm 2.2 | Y. Shalom, G. A. Willis, *Commensurated subgroups of arithmetic groups, totally disconnected groups and adelic rigidity*, Geom. Funct. Anal. **23** (2013), 1631–1683. [doi:10.1007/s00039-013-0236-5](https://doi.org/10.1007/s00039-013-0236-5) | [arXiv:0911.1966](https://arxiv.org/abs/0911.1966) | arXiv v1 |
| (equality of definitions) | Thm 3.1 | G. A. Willis, *Further properties of the scale function on a totally disconnected group*, J. Algebra **237** (2001), 142–164. [doi:10.1006/jabr.2000.8584](https://doi.org/10.1006/jabr.2000.8584) | free to read at the DOI (Elsevier open archive) | original (Thm 3.1, Defs 2.1–2.2) |
| `levi_isClosed`, `tidy_levi` | §2, Remark 3.1, Notation 3.2 | U. Baumgartner, G. A. Willis, *Contraction groups and scales of automorphisms of totally disconnected locally compact groups*, Israel J. Math. **142** (2004), 221–248. [doi:10.1007/BF02771534](https://doi.org/10.1007/BF02771534) | [arXiv:math/0302095](https://arxiv.org/abs/math/0302095) | arXiv v2 |
| (wording of `M_g`) | Def. 3, p. 330 | H. Glöckner, *Contraction groups for tidy automorphisms of totally disconnected groups*, Glasg. Math. J. **47** (2005), 329–333. [doi:10.1017/S0017089505002557](https://doi.org/10.1017/S0017089505002557) | free at the DOI; [arXiv:math/0409043](https://arxiv.org/abs/math/0409043) | published version |
| `casselman_wigner` | Cor. 2 | W. Casselman, D. Wigner, *Continuous cohomology and a conjecture of Serre's*, Invent. Math. **25** (1974), 199–211. [doi:10.1007/BF01389727](https://doi.org/10.1007/BF01389727) | [hdl:2027.42/46596](https://hdl.handle.net/2027.42/46596) (University of Michigan Deep Blue) | original (§4, Cor. 2, p. 209) |
| (statement used) | Thm 2.12 (arXiv: Thm 2.25) | D. Fisher, M. Mj, W. van Limbeek, *Commensurators of normal subgroups of lattices*, J. Éc. polytech. Math. **11** (2024), 1099–1122. [doi:10.5802/jep.274](https://doi.org/10.5802/jep.274) | open access (CC BY) at the DOI; [arXiv:2202.04027](https://arxiv.org/abs/2202.04027) | published version and arXiv v3 |

## Checked through a restatement

Eleven of the twelve sources were read in the original. For Margulis' normal subgroup theorem
(book, Ch. VIII, Thm A) we rely on the statement with full hypotheses in a refereed article:
Calderoni, J. Lond. Math. Soc. **107** (2023), Thm 4.14. This was a deliberate choice, because the
theorem is classical and the restatement is published. The book is held by the Tsinghua
mathematics library (call number O152.5 FM33) for anyone who wants to compare.
