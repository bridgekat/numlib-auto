/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.Brezis.Chapter01.Section01
import NumlibSurface.Brezis.Chapter01.Section02
import NumlibSurface.Brezis.Chapter01.Section03
import NumlibSurface.Brezis.Chapter01.Section04
import NumlibSurface.Brezis.Chapter02.Section01
import NumlibSurface.Brezis.Chapter02.Section02
import NumlibSurface.Brezis.Chapter02.Section03
import NumlibSurface.Brezis.Chapter02.Section04
import NumlibSurface.Brezis.Chapter02.Section05
import NumlibSurface.Brezis.Chapter02.Section06
import NumlibSurface.Brezis.Chapter02.Section07
import NumlibSurface.Brezis.Chapter03.Section01
import NumlibSurface.Brezis.Chapter03.Section02
import NumlibSurface.Brezis.Chapter03.Section03
import NumlibSurface.Brezis.Chapter03.Section04
import NumlibSurface.Brezis.Chapter03.Section05
import NumlibSurface.Brezis.Chapter03.Section06
import NumlibSurface.Brezis.Chapter03.Section07
import NumlibSurface.Brezis.Chapter04.Section01
import NumlibSurface.Brezis.Chapter04.Section02
import NumlibSurface.Brezis.Chapter04.Section03
import NumlibSurface.Brezis.Chapter04.Section04
import NumlibSurface.Brezis.Chapter04.Section05
import NumlibSurface.Brezis.Chapter05.Section01
import NumlibSurface.Brezis.Chapter05.Section02
import NumlibSurface.Brezis.Chapter05.Section03
import NumlibSurface.Brezis.Chapter05.Section04
import NumlibSurface.Brezis.Chapter06.Section01
import NumlibSurface.Brezis.Chapter06.Section02
import NumlibSurface.Brezis.Chapter06.Section03
import NumlibSurface.Brezis.Chapter06.Section04
import NumlibSurface.Brezis.Chapter07.Section01
import NumlibSurface.Brezis.Chapter07.Section02
import NumlibSurface.Brezis.Chapter07.Section03
import NumlibSurface.Brezis.Chapter07.Section04
import NumlibSurface.Brezis.Chapter08.Section01
import NumlibSurface.Brezis.Chapter08.Section02
import NumlibSurface.Brezis.Chapter08.Section03
import NumlibSurface.Brezis.Chapter08.Section04
import NumlibSurface.Brezis.Chapter08.Section05
import NumlibSurface.Brezis.Chapter08.Section06
import NumlibSurface.Brezis.Chapter09.Section01
import NumlibSurface.Brezis.Chapter09.Section02
import NumlibSurface.Brezis.Chapter09.Section03
import NumlibSurface.Brezis.Chapter09.Section04
import NumlibSurface.Brezis.Chapter09.Section05
import NumlibSurface.Brezis.Chapter09.Section06
import NumlibSurface.Brezis.Chapter09.Section07
import NumlibSurface.Brezis.Chapter09.Section08
import NumlibSurface.Brezis.Chapter10.Section01
import NumlibSurface.Brezis.Chapter10.Section02
import NumlibSurface.Brezis.Chapter10.Section03
import NumlibSurface.Brezis.Chapter11.Section01
import NumlibSurface.Brezis.Chapter11.Section02
import NumlibSurface.Brezis.Chapter11.Section03
import NumlibSurface.Brezis.Chapter11.Section04

/-!
# Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*

This library formalizes the numbered results of the book [brezis2011functional] by Haim Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations* (Universitext, Springer,
2011). Chapters 1–7 of the book treat the Hahn–Banach theorems and conjugate convex functions, the
theorems of Baire, Banach–Steinhaus, open mapping and closed graph, unbounded operators and their
adjoints, the weak and weak-$\star$ topologies, reflexive, separable and uniformly convex spaces,
the spaces $L^p$, Hilbert spaces and the theorems of Stampacchia and Lax–Milgram, compact operators
and the Riesz–Fredholm theory, and maximal monotone operators with the Hille–Yosida theorem.
Chapters 8–10 apply this theory to Sobolev spaces and boundary value problems in one and in $N$
dimensions, and to the heat and wave equations. Chapter 11 treats spaces of finite dimension and
codimension, quotient spaces, the sequence spaces $\ell^p$, $c$ and $c_0$, and Banach spaces over
$\mathbb{C}$. The library has one module for each section of Chapters 1–11, and the module doc
comment of each lists the numbered items of its section. Each module states the results of its
section in the terms of the book and proves them from Mathlib and the backbone: Chapters 1–3 from
`Numlib.Analysis.Normed.Module` (annihilators, complemented subspaces, weak closedness, weak-$\star$
metrizability, reflexivity, the Milman–Pettis theorem), `Numlib.Analysis.Normed.Operator.Unbounded`
and `Numlib.Analysis.Convex.Duality`; Chapter 4 from `Numlib.MeasureTheory.Function.LpSpace`,
`Numlib.MeasureTheory.Function.EssSupport` and `Numlib.MeasureTheory.Function.LpInterpolation`;
Chapter 5 from `Numlib.Analysis.InnerProductSpace.ConvexProjection`,
`Numlib.Analysis.InnerProductSpace.HilbertSum` and `Numlib.Variational`; Chapter 6 from
`Numlib.Analysis.Normed.Operator.Compact`, `Numlib.Analysis.Normed.Operator.Riesz` and
`Numlib.Analysis.InnerProductSpace.CompactSpectral`; Chapter 7 from
`Numlib.Analysis.InnerProductSpace.MaximalMonotone` and `Numlib.Analysis.ODE.HilleYosida`; Chapter 8
from `Numlib.Analysis.Sobolev.Interval` and `Numlib.Variational.EllipticInterval`; Chapter 9 from
`Numlib.Analysis.Sobolev` and `Numlib.Analysis.PDE.Elliptic`; Chapter 10 from `Numlib.Analysis.PDE`;
and Chapter 11 from `Numlib.Analysis.Normed.Module.FiniteCodim`,
`Numlib.Analysis.Normed.Module.Quotient`, `Numlib.Analysis.Normed.Lp.Sequence` and
`Numlib.Analysis.Normed.Algebra.Spectrum`.

## Coverage

Every Theorem, Proposition, Lemma and Corollary of the main text of Chapters 1–11 is stated, except
the parts of Proposition 4.20, Corollary 9.14, Theorem 9.26 and Proposition 9.29 that are listed
under "Not formalized". A numbered Remark or Example is stated when it makes a precise statement.
The unnumbered definitions of the main text, and the in-text Problems 1 and 2 of Section 3.1, are
stated too. Of the numbered results in the Comments at the ends of the chapters, the library states
Theorem 1.13 (Krein–Milman) in `NumlibSurface.Brezis.Chapter01.Section02`, Theorem 4.29 (Egorov) in
`NumlibSurface.Brezis.Chapter04.Section01`, Theorem 4.33 (Young's inequality, general form) in
`NumlibSurface.Brezis.Chapter04.Section04`, Theorem 5.12 (Fréchet–von Neumann–Jordan, the
characterization of a scalar product by the parallelogram law) in
`NumlibSurface.Brezis.Chapter05.Section01`, and items 1 and 3 of the Comments on Chapter 6 in
`NumlibSurface.Brezis.Chapter06.Section02` to `NumlibSurface.Brezis.Chapter06.Section04`. The
Exercises and Problems of the book are out of scope. Where the main text uses one of them as a step
of a proof, it is a supporting lemma named for what it says, such as Exercise 4.34 in
`NumlibSurface.Brezis.Chapter04.Section05`. The named results among the Problems (the
Eberlein–Šmulian theorem, Clarkson's inequalities, the Poincaré–Wirtinger inequality) are proved in
the backbone where a proof needs them.

## Contents

The doc comment of each module lists the numbered items of its section.

| Source | Module | Subject |
|---|---|---|
| §1.1 | `Chapter01.Section01` | The analytic form of the Hahn–Banach theorem |
| §1.2 | `Chapter01.Section02` | The geometric forms of the Hahn–Banach theorem |
| §1.3 | `Chapter01.Section03` | The bidual $E^{\star\star}$, orthogonality relations |
| §1.4 | `Chapter01.Section04` | A quick introduction to the theory of conjugate convex functions |
| §2.1 | `Chapter02.Section01` | The Baire category theorem |
| §2.2 | `Chapter02.Section02` | The uniform boundedness principle |
| §2.3 | `Chapter02.Section03` | The open mapping theorem and the closed graph theorem |
| §2.4 | `Chapter02.Section04` | Complementary subspaces, right and left invertibility |
| §2.5 | `Chapter02.Section05` | Orthogonality revisited |
| §2.6 | `Chapter02.Section06` | Unbounded linear operators, and the definition of the adjoint |
| §2.7 | `Chapter02.Section07` | Operators with closed range, and surjective operators |
| §3.1 | `Chapter03.Section01` | The coarsest topology for which a collection of maps becomes continuous |
| §3.2 | `Chapter03.Section02` | Definition and elementary properties of the weak topology $\sigma(E,E^\star)$ |
| §3.3 | `Chapter03.Section03` | Weak topology, convex sets, and linear operators |
| §3.4 | `Chapter03.Section04` | The weak-∗ topology $\sigma(E^\star, E)$ |
| §3.5 | `Chapter03.Section05` | Reflexive spaces |
| §3.6 | `Chapter03.Section06` | Separable spaces |
| §3.7 | `Chapter03.Section07` | Uniformly convex spaces |
| §4.1 | `Chapter04.Section01` | Some results about integration that everyone must know |
| §4.2 | `Chapter04.Section02` | Definition and elementary properties of $L^p$ spaces |
| §4.3 | `Chapter04.Section03` | Reflexivity. Separability. Dual of $L^p$ |
| §4.4 | `Chapter04.Section04` | Convolution and regularization |
| §4.5 | `Chapter04.Section05` | Criterion for strong compactness in $L^p$ |
| §5.1 | `Chapter05.Section01` | Definitions and elementary properties. Projection onto a closed convex set |
| §5.2 | `Chapter05.Section02` | The dual space of a Hilbert space |
| §5.3 | `Chapter05.Section03` | The theorems of Stampacchia and Lax–Milgram |
| §5.4 | `Chapter05.Section04` | Hilbert sums, orthonormal bases |
| §6.1 | `Chapter06.Section01` | Definitions, elementary properties, adjoint |
| §6.2 | `Chapter06.Section02` | The Riesz–Fredholm theory |
| §6.3 | `Chapter06.Section03` | The spectrum of a compact operator |
| §6.4 | `Chapter06.Section04` | Spectral decomposition of self-adjoint compact operators |
| §7.1 | `Chapter07.Section01` | Definition and elementary properties of maximal monotone operators |
| §7.2 | `Chapter07.Section02` | The evolution problem $du/dt + Au = 0$ on $[0, +\infty)$ |
| §7.3 | `Chapter07.Section03` | Regularity |
| §7.4 | `Chapter07.Section04` | The self-adjoint case |
| §8.1 | `Chapter08.Section01` | Motivation |
| §8.2 | `Chapter08.Section02` | The Sobolev space $W^{1,p}(I)$ |
| §8.3 | `Chapter08.Section03` | The space $W_0^{1,p}(I)$ and its dual $W^{-1,p'}(I)$ |
| §8.4 | `Chapter08.Section04` | Some examples of boundary value problems |
| §8.5 | `Chapter08.Section05` | The maximum principle |
| §8.6 | `Chapter08.Section06` | Eigenfunctions and spectral decomposition |
| §9.1 | `Chapter09.Section01` | Definition and elementary properties of the Sobolev spaces $W^{1,p}(\Omega)$ |
| §9.2 | `Chapter09.Section02` | Extension operators |
| §9.3 | `Chapter09.Section03` | Sobolev inequalities |
| §9.4 | `Chapter09.Section04` | The space $W_0^{1,p}(\Omega)$ |
| §9.5 | `Chapter09.Section05` | Variational formulation of some boundary value problems |
| §9.6 | `Chapter09.Section06` | Regularity of weak solutions |
| §9.7 | `Chapter09.Section07` | The maximum principle |
| §9.8 | `Chapter09.Section08` | Eigenfunctions and spectral decomposition |
| §10.1 | `Chapter10.Section01` | The heat equation: existence, uniqueness, and regularity |
| §10.2 | `Chapter10.Section02` | The maximum principle |
| §10.3 | `Chapter10.Section03` | The wave equation |
| §11.1 | `Chapter11.Section01` | Finite-dimensional and finite-codimensional spaces |
| §11.2 | `Chapter11.Section02` | Quotient spaces |
| §11.3 | `Chapter11.Section03` | Some classical spaces of sequences |
| §11.4 | `Chapter11.Section04` | Banach spaces over $\mathbb{C}$: what is similar and what is different |

## Conventions

* Section $n.m$ of the book is the module `ChapterNN.SectionMM`, and all its declarations are in the
  namespace `Brezis.ChapterNN`, with the chapter number written with two digits.
* A declaration is named for the item that it states: Theorem 4.2 is `Brezis.Chapter04.theorem_4_2`,
  Lemma 4.1 is `Brezis.Chapter04.lemma_4_1`, Proposition 9.3 is `Brezis.Chapter09.proposition_9_3`,
  and Corollary 9.19 is `Brezis.Chapter09.corollary_9_19`. The book numbers Remarks and Examples
  within each chapter, and their names carry the chapter number: Remark 4 of Chapter 8 is
  `Brezis.Chapter08.remark_8_4`, and Example 3 of Chapter 1 is `Brezis.Chapter01.example_1_3`. In
  Chapter 3 the numbering of the Examples starts again in Section 3.7, and their names carry the
  section number as well: Example 2 of Section 3.7 is `Brezis.Chapter03.example_3_7_2`.
* The clauses of one item, or the two directions of an equivalence, are told apart by a suffix: the
  part label of the source or a word that names the clause, as in `Brezis.Chapter06.theorem_6_6_a`
  and `Brezis.Chapter08.corollary_8_11_deriv`. The name without a suffix, where it exists, is the
  conjunction of the clauses or the main clause.
* An unnumbered "Definition." paragraph of the book is a declaration named for its content, with a
  lemma that identifies it with the backbone or Mathlib object that it stands for, such as
  `Brezis.Chapter09.isClassC1_iff_isContDiffDomain`.
* The dependencies run forward in the order of the chapters: a module imports only modules of its
  own chapter and of earlier chapters, and a later chapter uses the restatement in an earlier
  chapter rather than the backbone result behind it.
* The book works over $\mathbb{R}$, except in Section 11.4, which treats Banach spaces over
  $\mathbb{C}$. The library states everything over `ℝ`, and Section 11.4 over `ℂ`. The backbone
  states its results over a field `𝕜` with `[RCLike 𝕜]` wherever the proof allows.
* The dual $E^\star$ of a real normed space $E$ is `StrongDual ℝ E` with the operator norm, and
  $\langle f, x \rangle$ is `f x`.
* The space $\mathcal{L}(E, F)$ of bounded linear operators is `E →L[ℝ] F`.
* The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)` with Lebesgue measure
  `MeasureTheory.volume`. For $\Omega \subseteq \mathbb{R}^N$, the space $L^p(\Omega)$ is
  `MeasureTheory.Lp ℝ p (volume.restrict Ω)`.

## Deviations from the source

**Chapter 3.**

* **Corollary 3.23** (generalization). The source assumes that $\varphi$ never takes the value
  $-\infty$. The library does not assume this. See `Brezis.Chapter03.corollary_3_23`.

**Chapter 4.**

* **Lemma 4.2** (generalization). The source states the lemma for a Banach space. The library states
  it for every topological space. See `Brezis.Chapter04.lemma_4_2`.
* **Theorem 4.11** (generalization). The source states the theorem for $1 < p < \infty$. The library
  states it for $1 \le p < \infty$, and Theorem 4.14 is its case $p = 1$. See
  `Brezis.Chapter04.theorem_4_11`.
* **Remark after Theorem 4.13** (generalization). The source assumes that
  $\Omega \subseteq \mathbb{R}^N$ is measurable. The library states the result for every subset. See
  `Brezis.Chapter04.theorem_4_13_subset`.
* **Proposition 4.18 and Remark 10** (generalization). The source assumes $f \in L^1$ and
  $g \in L^p$. The library assumes no integrability. See `Brezis.Chapter04.proposition_4_18` and
  `Brezis.Chapter04.remark_4_10`.
* **Theorem 4.26** (generalization). The source assumes that $\Omega$ is measurable. The library
  states the theorem for every set of finite outer measure. See `Brezis.Chapter04.theorem_4_26`.

**Chapter 5.**

* **Theorem 5.11** (reading). The source asserts an orthonormal basis $(e_n)_{n \ge 1}$, which
  cannot exist in finite dimension. The library states a countable Hilbert basis in every dimension,
  and the sequence form for an infinite-dimensional $H$. See `Brezis.Chapter05.theorem_5_11` and
  `Brezis.Chapter05.theorem_5_11_nat`.

**Chapter 6.**

* **Theorem 6.6(a) and (b)** (generalization). The source assumes that $E$ is a Banach space. The
  library proves parts (a) and (b) for every normed space. See `Brezis.Chapter06.theorem_6_6_a`,
  `Brezis.Chapter06.theorem_6_6_b_isClosed` and `Brezis.Chapter06.theorem_6_6_b`.
* **Theorem 6.8(b) and (c)** (generalization). The source assumes $\dim E = \infty$ for all of
  Theorem 6.8. The library states parts (b) and (c) without this hypothesis. See
  `Brezis.Chapter06.theorem_6_8_b` and `Brezis.Chapter06.theorem_6_8_c`.
* **Proposition 6.9** (reading). The statements $m, M \in \sigma(T)$ and $\|T\| = \max\{|m|, |M|\}$
  need $H \neq \{0\}$, which the source leaves implicit. The library assumes it. See
  `Brezis.Chapter06.proposition_6_9_inf_mem`.
* **Theorem 6.11** (reading). The source indexes the Hilbert basis by $n$, as a sequence $(e_n)$.
  The library indexes it by an arbitrary type, which also covers finite dimension. See
  `Brezis.Chapter06.theorem_6_11`.
* **Remark 8** (reading). The source truncates the expansion after the first $k$ eigenvalues. The
  library has no order on the index set, and keeps a finite set of indices that contains every $i$
  with $|\mu_i| > \varepsilon$. See `Brezis.Chapter06.remark_6_8`.

**Chapter 7.**

* **Lemma 7.1** (generalization). The source assumes $w \in C^1([0, +\infty); H)$. The library does
  not assume this, because it follows from the equation when $A_\lambda$ is bounded. See
  `Brezis.Chapter07.lemma_7_1`.
* **Theorem 7.5** (generalization). The source states the theorem for $k \ge 2$. The library states
  it for every $k$. See `Brezis.Chapter07.theorem_7_5`.
* **Remark 8** (reading). The library states the equivalence of the maximal monotonicity of $A$ and
  of $A^\star$ with the extra hypothesis that $D(A^\star)$ is dense, which gives
  $A^{\star\star} = A$. See `Brezis.Chapter07.remark_7_8_adjoint`.
* **Theorem 7.7** (generalization). The library proves uniqueness among all solutions on
  $(0, +\infty)$ that are continuous on $[0, +\infty)$, a larger class than the class of the source.
  See `Brezis.Chapter07.theorem_7_7`.

**Chapter 8.**

* **Lemma 8.3** (generalization). The source assumes $\eta = 1$ on $x < 1/4$ and $\eta = 0$ on
  $x > 3/4$. The library assumes only the second condition. See `Brezis.Chapter08.lemma_8_3`.
* **Remark 10(c)** (generalization). The source states the claim for $1 < p \le \infty$. The library
  states it for $1 \le p \le \infty$. See `Brezis.Chapter08.remark_8_10_c`.
* **Corollary 8.11, the derivative** (generalization). The source assumes $G(0) = 0$. The formula
  $(G \circ u)' = (G' \circ u) u'$ holds without this assumption. See
  `Brezis.Chapter08.corollary_8_11_deriv`.
* **Proposition 8.14** (reading). The source prints $\|F\| = \max(\|f_0\|_{L^{p'}},
  \|f_1\|_{L^{p'}})$ for the norm $\|u\|_{L^p} + \|u'\|_{L^p}$ on $W^{1,p}$. The library uses the
  norm of the Lean type, whose dual norm is the $\ell^{p'}$ norm of the pair $(f_0, f_1)$. See
  `Brezis.Chapter08.proposition_8_14`.
* **Remark 18** (generalization). The source states the characterization of $W_0^{m,p}(I)$ for
  $m \ge 2$. The library states it for every $m \ge 1$, and the case $m = 1$ is Theorem 8.12. See
  `Brezis.Chapter08.remark_8_18` and `Brezis.Chapter08.remark_8_18_of_bounded`.
* **Example 2, existence, uniqueness and minimization** (generalization). The source assumes
  $p \in C^1(\bar I)$ and $q \in C(\bar I)$. The library assumes only $p, q \in L^\infty(I)$ with
  $p \ge \alpha > 0$ and $q \ge 0$. See `Brezis.Chapter08.example_8_2_existsUnique` and
  `Brezis.Chapter08.example_8_2_min`.
* **Example 2, problem (20)** (generalization). The source takes $p \in C^1(\bar I)$ and
  $q, r \in C(\bar I)$. The library takes coefficients in $L^\infty(I)$, with the bounds almost
  everywhere. See `Brezis.Chapter08.example_8_2_general`.
* **Theorem 8.19, Proposition 8.21 and Remark 28** (reading). The source's $\sup_I f$ and $\inf_I f$
  are the essential supremum and infimum, which can be infinite. The library states the bounds (33)
  and (35) for every essential bound of $f$: "$f \le K$ a.e." gives
  $u \le \max\{\alpha, \beta, K\}$. See `Brezis.Chapter08.theorem_8_19`,
  `Brezis.Chapter08.proposition_8_21` and `Brezis.Chapter08.remark_8_28`.

**Chapter 9.**

* **Remark 2, "in particular"** (reading). The library reads $C^1(\bar\Omega)$ as the functions of
  class $C^1$ on $\bar\Omega$ in the sense of `ContDiffOn`. See
  `Brezis.Chapter09.remark_9_2_closure`.
* **Definition of an open set of class $C^\infty$** (reading). The source defines "of class
  $C^\infty$" as "of class $C^m$ for every $m$". The library reads it as one chart of class
  $C^\infty$ at each boundary point, which is a priori stronger. See `Brezis.Chapter09.IsOfClassC`.
* **Corollary 9.11** (reading). The library states the corollary for $N \ge 2$, which the proof of
  the source uses. The case $N = 1$ is a case of Theorem 8.8. See `Brezis.Chapter09.corollary_9_11`.
* **Corollary 9.13** (reading). The library states the corollary under $N \ge 2$ or $p > 1$, which
  the proof by Theorem 9.9, Corollary 9.11 and Theorem 9.12 needs. See
  `Brezis.Chapter09.corollary_9_13`.
* **Corollary 9.14, case $p = N$** (reading). The library states the case for $N \ge 2$, as
  Corollary 9.11. See `Brezis.Chapter09.corollary_9_14_eq`.
* **Corollary 9.15** (reading). The library states the corollary under $N \ge 2$ or $p > 1$, as
  Corollary 9.13. See `Brezis.Chapter09.corollary_9_15`.
* **Theorem 9.16, case $p = N$ and last sentence** (reading). The library states the case $p = N$
  for $N \ge 2$, and the compactness of $W^{1,p}(\Omega) \subset L^p(\Omega)$ for $p \ne 1$ or
  $N \ge 2$; the case $N = p = 1$ is Theorem 8.8. See `Brezis.Chapter09.theorem_9_16_eq` and
  `Brezis.Chapter09.theorem_9_16_self`.
* **Remark 15, case $p = N$** (reading). The library states the case for $N \ge 2$. See
  `Brezis.Chapter09.remark_9_15_eq`.
* **Remark 17, punctured space** (reading). The condition "$\mathbb{R}^N \setminus \Omega$
  sufficiently thin and $p < N$" is informal. The library takes
  $\Omega = \mathbb{R}^N \setminus \{0\}$ with $N \ge 2$, and includes $p = N$. See
  `Brezis.Chapter09.remark_9_17_punctured_of_le`.
* **Proposition 9.18** (generalization). The library proves (i) $\Rightarrow$ (ii) and (i)
  $\Rightarrow$ (iii) for $1 \le p \le \infty$, and (ii) $\Rightarrow$ (iii) for $1 < p \le \infty$,
  all on an arbitrary open set. See `Brezis.Chapter09.proposition_9_18_i_ii`,
  `Brezis.Chapter09.proposition_9_18_ii_iii` and `Brezis.Chapter09.proposition_9_18_i_iii`.
* **Remark 20** (reading). The clauses for $p = N$ assume $N \ge 2$, as Corollary 9.14. The library
  states the constants of the Hölder estimate and of the Sobolev inequality for each fixed $\Omega$,
  and does not record their independence of $\Omega$. See `Brezis.Chapter09.remark_9_20`.
* **Remark 21** (reading). The library states the finite-measure clause for $N \ge 2$, and the
  bounded-projection clause for the last coordinate axis. See `Brezis.Chapter09.remark_9_21`.
* **Proposition 9.20** (reading). The source states $\|F\| = \max_i \|f_i\|_{p'}$ for the norm
  $\sum_i \|h_i\|_p$ on $(L^p)^{N+1}$. The library gives the bound $\|f_i\|_{p'} \le \|F\|$ for the
  norm of the Lean type. See `Brezis.Chapter09.proposition_9_20`.
* **The inclusions $W_0^{1,p}(\Omega) \subset L^2(\Omega) \subset W^{-1,p'}(\Omega)$** (correction).
  The range $2N/(N + 2) \le p$ of the source contains $p = 1$ for $N \le 2$, where $L^2(\Omega)$ is
  not dense in $W^{-1,\infty}(\Omega)$. The library assumes $p > 1$. See
  `Brezis.Chapter09.dual_inclusions_of_le`.
* **Theorem 9.21** (generalization). The source assumes that $\Omega$ is bounded. The library proves
  existence, uniqueness and Dirichlet's principle for every open set. See
  `Brezis.Chapter09.theorem_9_21` and `Brezis.Chapter09.theorem_9_21_isMinOn`.
* **Example 1, Step D** (reading). The source concludes that $-\Delta u + u = f$ holds everywhere in
  $\Omega$, which for $f \in L^2(\Omega)$ presumes a continuous representative of $f$. The library
  makes this a hypothesis. See `Brezis.Chapter09.example_9_1_stepD_of_continuous`.
* **Example 2, the set $K$** (generalization). The source takes $\tilde g \in H^1(\Omega) \cap
  C(\overline\Omega)$ with $\tilde g = g$ on $\Gamma$. The library takes any
  $\tilde g \in H^1(\Omega)$. See `Brezis.Chapter09.admissibleSetInhomogeneous`.
* **Example 3, existence and the symmetric case** (generalization). The source assumes
  $a_{ij} \in C^1(\overline\Omega)$. The library assumes only $a_{ij} \in C(\overline\Omega)$. See
  `Brezis.Chapter09.example_9_3` and `Brezis.Chapter09.example_9_3_isMinOn`.
* **Remark 23, second clause** (reading). The source leaves the hypothesis $N \ge 1$ implicit. The
  library assumes it. See `Brezis.Chapter09.remark_9_23_zero_drift`.
* **Proposition 9.24** (generalization). The source assumes that $\Omega$ is bounded and of class
  $C^1$. The library states the result for every open set. See `Brezis.Chapter09.proposition_9_24`
  and `Brezis.Chapter09.proposition_9_24_isMinOn`.
* **Theorem 9.25, the $C^\infty(\overline\Omega)$ clause with $\Gamma$ bounded** (reading). On an
  unbounded $\Omega$, $f \in C^\infty(\overline\Omega)$ does not give $f \in H^m(\Omega)$, which the
  proof of the source uses. The library assumes $f \in H^m(\Omega)$ for every $m$. See
  `Brezis.Chapter09.theorem_9_25_smooth_of_forall_mem`.
* **Remark 25, hypoellipticity** (generalization). The source takes $\omega \subset\subset \Omega$.
  The library states the result for every open $\omega \subseteq \Omega$. See
  `Brezis.Chapter09.remark_9_25_local`.
* **Proposition 9.29 without first-order term** (reading). The source leaves the hypothesis
  $N \ge 1$ implicit, and the constancy argument of footnote 39 needs it. The library assumes it.
  See `Brezis.Chapter09.proposition_9_29_zero_drift` and the three variants that follow it.
* **Standing assumption of Section 9.8** (reading). The source leaves $\Omega \neq \emptyset$ and
  $N \ge 1$ implicit. The library assumes them, because otherwise $L^2(\Omega)$ is
  finite-dimensional and has no Hilbert basis indexed by `ℕ`. See `Brezis.Chapter09.theorem_9_31`.
* **Remark 30** (correction). The source omits the symmetry $a_{ij} = a_{ji}$, without which there
  is no orthonormal basis of eigenfunctions. The library assumes it, and the eigenvalues $\lambda_n$
  need not be positive. See `Brezis.Chapter09.remark_9_30`.

**Chapter 10.**

* **Standing hypothesis of Chapter 10, Section 10.1** (generalization). The source assumes that
  $\Omega$ is of class $C^\infty$ with $\Gamma$ bounded. The library assumes regularity only where a
  proof uses it: the monotonicity and symmetry of $A$, the energy identities (6) and (11), Theorem
  10.2(a) and Remark 3 hold on every open set, and several results assume only class $C^2$ or $C^3$.
  See `Brezis.Chapter10.theorem_10_1_energy` and `Brezis.Chapter10.theorem_10_2_b`.
* **Theorem 10.1, $u \in L^2(0, \infty; H^1_0(\Omega))$** (correction). The clause is false on an
  unbounded $\Omega$ ($\Omega = \mathbb{R}$ with a Gaussian datum). The library proves
  $\int_0^\infty |\nabla u(t)|^2 \, dt \le \frac12 |u_0|^2$ on every open set and the membership for
  a bounded $\Omega$. See `Brezis.Chapter10.theorem_10_1_memLp_gradient` and
  `Brezis.Chapter10.theorem_10_1_memLp`.
* **Theorem 10.2(a), $u \in L^2(0, \infty; H^2(\Omega))$** (correction). The clause is false on an
  unbounded $\Omega$. The library proves it for a bounded $\Omega$. See
  `Brezis.Chapter10.theorem_10_2_a_memLp`.
* **Theorem 10.2(b), $u \in L^2(0, \infty; H^3(\Omega))$ and
  $\partial_t u \in L^2(0, \infty; H^1_0(\Omega))$** (correction). The clauses are false on an
  unbounded $\Omega$. The library proves them for a bounded $\Omega$. See
  `Brezis.Chapter10.theorem_10_2_b_memLp`.
* **Remark 4** (reading). The boundary values of $\Delta^j u(\cdot, 0)$ must have a meaning. The
  library states the remark for $u$ of class $C^\infty$ on $\mathbb{R}^N \times \mathbb{R}$. See
  `Brezis.Chapter10.remark_10_4`.
* **Theorem 10.3** (reading). The source states the bounds "for all $(x, t) \in Q$" for an
  $L^2$-valued solution, with $\sup_\Omega u_0$ and $\inf_\Omega u_0$. The library reads them almost
  everywhere in $x$ for each $t \ge 0$, for every essential bound $K \ge 0$, and everywhere for a
  continuous representative. See `Brezis.Chapter10.theorem_10_3`,
  `Brezis.Chapter10.theorem_10_3_essSup` and `Brezis.Chapter10.theorem_10_3_pointwise`.
* **Corollary 10.4(ii)** (reading). The source states $\|u\|_{L^\infty(Q)} \le
  \|u_0\|_{L^\infty(\Omega)}$. The library states $\|u(t)\|_{L^\infty(\Omega)} \le
  \|u_0\|_{L^\infty(\Omega)}$ for every $t \ge 0$, because it builds no jointly measurable
  representative of the solution. See `Brezis.Chapter10.corollary_10_4_ii`.
* **Theorem 10.6** (reading). The source leaves $\Omega \neq \emptyset$ implicit; for
  $\Omega = \emptyset$ there is no maximum. The library assumes it for the attained maximum, and
  states the bound form without it. See `Brezis.Chapter10.theorem_10_6` and
  `Brezis.Chapter10.theorem_10_6_le`.
* **Standing hypothesis of Chapter 10, Section 10.3** (generalization). The library states the
  energy identity (32) and Remarks 6, 7 and 9 on every open set, or on every bounded one. Theorem
  10.7 keeps the hypothesis that $\Omega$ is of class $C^\infty$ with $\Gamma$ bounded. See
  `Brezis.Chapter10.theorem_10_7_energy` and `Brezis.Chapter10.remark_10_9`.
* **Remark 7, group of isometries** (generalization). The library obtains the solvability for all
  $t \in \mathbb{R}$ and $|U(t)|_H = |U_0|_H$ by time reversal, which needs neither a bounded
  $\Omega$ nor the Dirichlet scalar product. See `Brezis.Chapter10.remark_10_7_group`.
* **Theorem 10.8** (reading). The library reads the compatibility conditions
  $\Delta^j u_0 = \Delta^j v_0 = 0$ on $\Gamma$, as in the display of the proof, as
  $u_0, v_0 \in D_k$ for every $k$. Then $u_0, v_0 \in H^k(\Omega)$ for every $k$ follows and is not
  assumed. See `Brezis.Chapter10.theorem_10_8`.
* **Remark 10** (reading). As for Remark 4, the library states the remark for $u$ of class
  $C^\infty$ on $\mathbb{R}^N \times \mathbb{R}$. See `Brezis.Chapter10.remark_10_10`.

**Chapter 11.**

* **Factorization through the kernel** (typo). The source prints $\|T\| = \|T\|$ for
  $\|\tilde{T}\| = \|T\|$. See `Brezis.Chapter11.quotKerFactorization`.
* **The identities for a complex scalar product** (typo). The displayed expansion of $|u + v|^2$ has
  $|v|^2$ in place of $|u|^2$. See `Brezis.Chapter11.inner_identities`.
* **Proposition 11.32, display (20)** (correction). The identity $Q(EV(T)) = EV(Q(T))$ fails for a
  constant polynomial $Q$. The library assumes $\deg Q > 0$. See
  `Brezis.Chapter11.proposition_11_32_eigenvalue`.
* **Proposition 11.34** (generalization). The source assumes that $H$ is separable. The library
  states a Hilbert basis indexed by a subset of $H$ without separability. See
  `Brezis.Chapter11.proposition_11_34`.
* **Proposition 11.36** (generalization). The source assumes that $H$ is separable. The library
  states the result without separability. See `Brezis.Chapter11.proposition_11_36`.

## Not formalized

**All chapters.**

* **The Exercises and Problems of the book, and the numbered results of the Comments that "Coverage"
  does not name.** They are out of scope.
* **Remarks that are a discussion without a precise statement.** These are Remarks 1 and 8 of
  Chapter 1; Remark 2 of Chapter 2 and Remarks 10, 13 and 14 of Section 2.6; Remarks 1, 8, 12, 14,
  16 and 18 of Chapter 3; Remarks 2 and 3 of Chapter 7 and footnote 5 of Section 7.4; Remark 15 of
  Chapter 8; and footnotes 33 and 34 of Remark 25 of Chapter 9.

**Chapter 1.**

* **Remark 3, converse (James' theorem).** A Banach space in which every $f \in E^\star$ attains its
  norm is reflexive. The source quotes this result without proof.
* **Remark 4, first clause (Exercise 1.14).** Two disjoint closed convex subsets of $\ell^1$ that no
  closed hyperplane separates.
* **Remark 6, strict inclusion (Exercise 1.16).** An example in $\ell^1$ where
  $(N^\perp)^\perp \neq \overline{N}$.
* **Remark 6, last sentence.** $(N^\perp)^\perp$ is the closure of $N$ in the weak-$\star$ topology,
  which belongs to Chapter 3.
* **Remark 7, last clause (Exercise 1.18(h)).** Inequality (12) is the case $\varphi(t) = |t|^p/p$
  of (11) on $E = \mathbb{R}$.

**Chapter 2.**

* **Remark 8 (Lindenstrauss–Tzafriri).**
* **Remarks 15 and 17, first clauses (Exercises 2.22 and 2.23).** The counterexamples on $\ell^1$.
* **Remark 15, reflexive clause.** It is Theorem 3.24 in Chapter 3.

**Chapter 3.**

* **Remark 7, second clause (Exercise 6.7).** A linear operator is continuous from $E$ weak into $F$
  strong if and only if it has finite rank.
* **Remark 7, last paragraph (Exercise 4.20).** The case of nonlinear maps.
* **Remark 13, the spaces $L^p$, $\ell^p$, $L^1$, $L^\infty$ and $C(K)$.** These claims are stated
  in Chapters 4 and 11.
* **Remark 17(ii) and (iii).**
* **Remark 19, the spaces $L^1$ and $L^\infty$.** These claims are stated in Chapter 4.
* **Example 2 of Section 3.7, the spaces $L^p$ with $1 < p < \infty$.** This claim is Theorem 4.10
  of Chapter 4.

**Chapter 4.**

* **Remarks 6 and 8, the general measure space.** The claims that $L^1(\Omega)$ is not reflexive and
  $L^\infty(\Omega)$ is not separable unless $\Omega$ consists of finitely many atoms are stated
  only for nonempty open subsets of $\mathbb{R}^N$.
* **Remark 10, second sentence.** The claim that $f \star g$ need not have compact support when only
  one of $f$, $g$ has compact support has no example in the source.
* **Proposition 4.20, higher derivatives for $f \in C_c^k$.** The formula
  $D^\alpha(f \star g) = (D^\alpha f) \star g$ is stated for $|\alpha| = 1$ when $f \in C_c^k$, and
  for all $\alpha$ only when $f \in C_c^\infty$, because the backbone covers only a smooth $f$.

**Chapter 5.**

* **Remark 3, the example with a weighted space $\ell^2$.**
* **Remark 3, footnote.** The claim that $T$ is not surjective in general.
* **Theorem 5.16 (Minty–Browder), from the Comments on Chapter 5.**

**Chapter 6.**

* **Remark 1, Enflo's counterexample and Schauder bases.** This part of the remark is
  bibliographical.
* **Remark 7, the dimension of $N(T)$.** The remark that $N(T)$ may be finite or infinite
  dimensional when $0 \in EV(T)$.

**Chapter 7.**

* **Remark 1, second sentence.** The claim that $A + B$ on $D(A) \cap D(B)$ need not be maximal
  monotone is about a counterexample, which is not constructed.
* **Remark 4(b), the counterexample.** The claim that the limit $u(t)$ may lie outside $D(A)$ for
  every $t > 0$ and be nowhere differentiable is about a counterexample, which is not constructed.
* **Remark 5, the converse.** The Hille–Yosida generation theorem, that every continuous semigroup
  of contractions is $S_A$ for a unique maximal monotone $A$, is quoted from the literature without
  proof.
* **Remark 7, the counterexample.** The claim that a symmetric $A$ may have $D(A) \neq D(A^\star)$
  is about a counterexample, which is not constructed.
* **Remark 8, the counterexample.** The claim that $A^\star$ need not be monotone for a symmetric
  monotone $A$ is about a counterexample, which is not constructed.

**Chapter 8.**

* **Remark 3**, on distributions.
* **Remark 8, functions of bounded variation.** The failure of the converse of (i) $\Rightarrow$
  (ii) of Proposition 8.3 for $p = 1$, and the characterizations (a)–(c) of the functions of bounded
  variation.
* **Remark 10(a) on other intervals.** Only the interval $(0, 1)$ is formalized.
* **Remark 10(b) on an unbounded interval.**
* **Remark 12, the second claim.** In general $u \notin L^q(I)$ for $q \in [1, p)$ (Exercise 8.1).
* **Remark 20.** The identification of $F \in W^{-1,p'}(I)$ with the distribution $f_0 - f_1'$.
* **Footnotes 14 and 15 of Example 6.** The general boundary condition of the third type, and the
  Robin problem for small negative $k$.
* **Remark 29.** The eigenvalues of $-u''$ under the boundary conditions of Examples 3, 5, 6 and 7
  of Section 8.4, which the source leaves as an exercise.
* **Remark 30, the spectrum.** The eigenvalues and the spectrum of the operator $T$ on
  $L^2(\mathbb{R})$, which the source leaves to Exercise 8.38.

**Chapter 9.**

* **Remark 3.**
* **Remark 4(ii) for a cut-off function $\alpha$ of class $C^1$ that is not of class $C^\infty$.**
  Both forms of the remark are proved for a smooth $\alpha$ only.
* **Remark 5, second claim.** For a general $\Omega$, no sequence of functions of
  $C_c^1(\mathbb{R}^N)$ need converge to $u$ in $W^{1,p}(\Omega)$. It is a counterexample.
* **Remark 6, the implication (ii) $\Rightarrow$ (iii) at $p = 1$, and the discussion of the
  functions of bounded variation.** It belongs to the theory of $BV$ functions.
* **Remark 7 on a nonconvex $\Omega$, with the geodesic distance.**
* **Remark 8.**
* **Footnote 9.** The explicit constant $(N - 1)p/(N - p)$ of Theorem 9.9.
* **Corollary 9.14, case $p = \infty$.** It is Theorem 9.12 for $p = \infty$ on $\mathbb{R}^N$
  (`Brezis.Chapter09.theorem_9_12_top`), and is not restated on $\Omega$.
* **Remark 13, negative clause.** In general $W^{m,p}(\mathbb{R}^N) \not\subset
  L^\infty(\mathbb{R}^N)$ for $p > 1$ and $m = N/p$.
* **Remark 14(ii).** The injection $W^{1,p}(\Omega) \subset L^{p^*}(\Omega)$ is never compact.
* **Remark 16, Trudinger's inequality.** The source quotes it without proof.
* **Remark 21, the case $N = 1$ of the finite-measure clause.**
* **Remark 22, the heuristic and the comparison.** The heuristic "$D^\alpha u = 0$ on $\Gamma$ for
  $|\alpha| \le m - 1$", and the difference between $W_0^{m,p}(\Omega)$ and
  $W^{m,p}(\Omega) \cap W_0^{1,p}(\Omega)$ for $m \ge 2$.
* **Remark 23, second clause, with a first-order term.** For arbitrary $a_i$ the clause rests on the
  general case of Proposition 9.29, which the source does not prove.
* **Theorem 9.26 on a general domain.** The Neumann analogue of Theorem 9.25 on $\Omega$ of class
  $C^2$ with $\Gamma$ bounded: the source says only that the proof is analogous, and the cut-off
  argument of case C₂ fails for the Neumann problem, while a correct proof needs a Caccioppoli
  estimate that the backbone does not have. See `Numlib.Analysis.PDE.Elliptic.Regularity`.
* **Theorem 9.26 on the half space, the norm bound of the $H^{m+2}$ clause.** It needs a solution
  map for the Neumann problem, and the backbone's `Elliptic.solutionMap` is built only for the test
  space $H_0^1(\Omega)$.
* **Remark 24, the Dirichlet half.** The $H^2$ and $H^{m+2}$ regularity of the Dirichlet problem
  (50) for a general second-order elliptic operator, which the source states without proof. See
  `Numlib.Analysis.PDE.Elliptic.Regularity`.
* **Remark 24, the Neumann half.** The same regularity for the Neumann problem of the general
  operator, with the conormal boundary condition. It needs the Caccioppoli estimate above, and an
  $H^2$ Green formula for the conormal derivative, which the backbone does not have.
* **Proposition 9.29, (79), (80) and (81) with a first-order term, for $N \le 2$.** The proof uses
  the Sobolev inequality of Remark 20 on $W_0^{1,2}(\Omega)$, which needs $N > 2$. See
  `Numlib.Analysis.PDE.Elliptic.MaximumPrinciple`.
* **Remark 27, the last sentence.** The maximum principle for weak solutions of (77), which the
  source quotes from Gilbarg–Trudinger.
* **Remark 29, first clause.** The statement $e_n \in L^\infty(\Omega)$ for a general bounded
  $\Omega$ is given in the source without proof.

**Chapter 10.**

* **Remark 1, nonexistence under (12).** The claim that the backward problem (9), (10), (11) need
  not have a solution even when (12) holds is about a counterexample.
* **Remark 7(ii), $A^* = -A$.** The backbone does not formalize the adjoint for the Dirichlet scalar
  product.

**Chapter 11.**

* **The facts about $\mathbb{R}^p$ in the opening sentence of Section 11.1** (completeness,
  equivalence of norms, compactness of the unit ball). They are Mathlib's
  `FiniteDimensional.complete`, `ContinuousLinearEquiv.ofFinrankEq` and `FiniteDimensional.proper`.
* **The two bracketed warnings of Section 11.1**, that a sum of closed subspaces need not be closed
  and that a subspace of finite codimension need not be closed.
* **Example in the proof of Proposition 11.14.** A strict inequality
  $\dim N^\perp < \operatorname{codim} N$, with a hyperplane $N = \ker \xi$ for
  $\xi \in E^{**} \setminus J(E)$.
* **Final table of Section 11.3, last entry.** The claim that $(\ell^\infty)^*$ is strictly bigger
  than $\ell^1$ is not a numbered claim.
* **The prose comparisons of Section 11.4 with Chapters 1–7**, such as "Chapter 2. All the
  statements are unchanged".
* **The finite-dimensional motivation of the spectral theory in Section 11.4.**
* **The numerical range of $T(u_1, u_2) = (u_2, 0)$.** The computation
  $W(T) = \{|\lambda| \le 1/2\}$.
* **Remark 2 of Section 11.4, second sentence.** The equality $\overline{W(T)} = \operatorname{conv}
  \sigma(T)$ for every normal operator, which the source quotes from Halmos.
-/
