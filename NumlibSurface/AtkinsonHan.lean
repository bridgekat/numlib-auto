/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.AtkinsonHan.Chapter01.Section01
import NumlibSurface.AtkinsonHan.Chapter01.Section02
import NumlibSurface.AtkinsonHan.Chapter01.Section03
import NumlibSurface.AtkinsonHan.Chapter01.Section05
import NumlibSurface.AtkinsonHan.Chapter01.Section06
import NumlibSurface.AtkinsonHan.Chapter02.Section01
import NumlibSurface.AtkinsonHan.Chapter02.Section02
import NumlibSurface.AtkinsonHan.Chapter02.Section03
import NumlibSurface.AtkinsonHan.Chapter02.Section04
import NumlibSurface.AtkinsonHan.Chapter02.Section05
import NumlibSurface.AtkinsonHan.Chapter02.Section06
import NumlibSurface.AtkinsonHan.Chapter02.Section07
import NumlibSurface.AtkinsonHan.Chapter02.Section08
import NumlibSurface.AtkinsonHan.Chapter02.Section09
import NumlibSurface.AtkinsonHan.Chapter03.Section01
import NumlibSurface.AtkinsonHan.Chapter03.Section02
import NumlibSurface.AtkinsonHan.Chapter03.Section03
import NumlibSurface.AtkinsonHan.Chapter03.Section04
import NumlibSurface.AtkinsonHan.Chapter03.Section05
import NumlibSurface.AtkinsonHan.Chapter03.Section06
import NumlibSurface.AtkinsonHan.Chapter03.Section07
import NumlibSurface.AtkinsonHan.Chapter04.Section01
import NumlibSurface.AtkinsonHan.Chapter04.Section02
import NumlibSurface.AtkinsonHan.Chapter04.Section03
import NumlibSurface.AtkinsonHan.Chapter04.Section04
import NumlibSurface.AtkinsonHan.Chapter04.Section05
import NumlibSurface.AtkinsonHan.Chapter05.Section01
import NumlibSurface.AtkinsonHan.Chapter05.Section02
import NumlibSurface.AtkinsonHan.Chapter05.Section03
import NumlibSurface.AtkinsonHan.Chapter05.Section04
import NumlibSurface.AtkinsonHan.Chapter05.Section05
import NumlibSurface.AtkinsonHan.Chapter05.Section06
import NumlibSurface.AtkinsonHan.Chapter06.Section01
import NumlibSurface.AtkinsonHan.Chapter06.Section02
import NumlibSurface.AtkinsonHan.Chapter06.Section03
import NumlibSurface.AtkinsonHan.Chapter07.Section01
import NumlibSurface.AtkinsonHan.Chapter07.Section02
import NumlibSurface.AtkinsonHan.Chapter07.Section03
import NumlibSurface.AtkinsonHan.Chapter07.Section04
import NumlibSurface.AtkinsonHan.Chapter07.Section05
import NumlibSurface.AtkinsonHan.Chapter07.Section06
import NumlibSurface.AtkinsonHan.Chapter08.Section02
import NumlibSurface.AtkinsonHan.Chapter08.Section03
import NumlibSurface.AtkinsonHan.Chapter08.Section04
import NumlibSurface.AtkinsonHan.Chapter08.Section05
import NumlibSurface.AtkinsonHan.Chapter08.Section06
import NumlibSurface.AtkinsonHan.Chapter08.Section07
import NumlibSurface.AtkinsonHan.Chapter08.Section08
import NumlibSurface.AtkinsonHan.Chapter09.Section01
import NumlibSurface.AtkinsonHan.Chapter09.Section02
import NumlibSurface.AtkinsonHan.Chapter09.Section03
import NumlibSurface.AtkinsonHan.Chapter09.Section04
import NumlibSurface.AtkinsonHan.Chapter10.Section01
import NumlibSurface.AtkinsonHan.Chapter10.Section02
import NumlibSurface.AtkinsonHan.Chapter10.Section03
import NumlibSurface.AtkinsonHan.Chapter10.Section04
import NumlibSurface.AtkinsonHan.Chapter11.Section01
import NumlibSurface.AtkinsonHan.Chapter11.Section02
import NumlibSurface.AtkinsonHan.Chapter11.Section03
import NumlibSurface.AtkinsonHan.Chapter11.Section04
import NumlibSurface.AtkinsonHan.Chapter12.Section01
import NumlibSurface.AtkinsonHan.Chapter12.Section02
import NumlibSurface.AtkinsonHan.Chapter12.Section03
import NumlibSurface.AtkinsonHan.Chapter12.Section04
import NumlibSurface.AtkinsonHan.Chapter12.Section05
import NumlibSurface.AtkinsonHan.Chapter12.Section06
import NumlibSurface.AtkinsonHan.Chapter12.Section07
import NumlibSurface.AtkinsonHan.Chapter13.Section01
import NumlibSurface.AtkinsonHan.Chapter13.Section02
import NumlibSurface.AtkinsonHan.Chapter13.Section03
import NumlibSurface.AtkinsonHan.Chapter14.Section01
import NumlibSurface.AtkinsonHan.Chapter14.Section02
import NumlibSurface.AtkinsonHan.Chapter14.Section03
import NumlibSurface.AtkinsonHan.Chapter14.Section04

/-!
# Atkinson and Han, *Theoretical Numerical Analysis*

This library formalizes the numbered items of Kendall Atkinson and Weimin Han, *Theoretical
Numerical Analysis: A Functional Analysis Framework*, 3rd edition [han2009theoretical]. The book
develops the functional analysis that numerical analysis uses (linear, normed and inner product
spaces, linear operators, approximation theory, Fourier analysis, nonlinear operator equations and
Sobolev spaces) and applies it to finite difference methods, weak formulations of elliptic boundary
value problems, the Galerkin and finite element methods, elliptic variational inequalities, integral
equations of the second kind, boundary integral equations and multivariable polynomial
approximation. The library has 74 modules, one for each section of Chapters 1–14 that it covers, and
each module states the results of its section in the terms of the book. The proofs specialize the
backbone, mainly the modules under `Numlib.Analysis.Sobolev`, `Numlib.Analysis.Normed`,
`Numlib.Analysis.Fourier`, `Numlib.Variational`, `Numlib.IntegralEquations` and
`Numlib.Approximation`. A reader of the book finds here a Lean name for every formalized result.

## Coverage

The library formalizes the numbered theorems, lemmas, propositions, corollaries, definitions,
examples, remarks and displayed equations of the sections in the table below, and many of their
exercises. Each module lists in its `Not formalized` section the items of its section that are left
out, and the last section below collects these lists. Out of scope are the numerical tables and
figures, which report computed values, the operation counts of algorithms, and the results that the
book quotes without proof and whose proof needs a theory that Mathlib does not have: degree theory,
the holomorphic functional calculus, spherical harmonics and surface measure on spheres, and the
theory of Lipschitz domains. Section 1.4 and Section 8.1 have no module; the last section below says
why.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1.1 Linear spaces | `Chapter01.Section01` | bases and dimension |
| §1.2 Normed spaces | `Chapter01.Section02` | equivalent norms, completion, Fubini |
| §1.3 Inner product spaces | `Chapter01.Section03` | Cauchy–Schwarz, parallelogram law |
| §1.5 The $L^p$ spaces | `Chapter01.Section05` | Young, Hölder, Minkowski, completeness |
| §1.6 Compact sets | `Chapter01.Section06` | Heine–Borel, Riesz, Arzelà–Ascoli |
| §2.1 Operators | `Chapter02.Section01` | bounded sets have bounded images |
| §2.2 Continuous linear operators | `Chapter02.Section02` | operator norm, $\mathcal{L}(V, W)$ |
| §2.3 The geometric series theorem and its variants | `Chapter02.Section03` | perturbation |
| §2.4 More results on linear operators | `Chapter02.Section04` | bounded inverse, conditioning |
| §2.5 Linear functionals | `Chapter02.Section05` | Hahn–Banach, Riesz representation |
| §2.6 Adjoint operators | `Chapter02.Section06` | self-adjoint operators |
| §2.7 Weak convergence | `Chapter02.Section07` | reflexivity |
| §2.8 Compact linear operators | `Chapter02.Section08` | spectrum, Fredholm alternative |
| §2.9 The resolvent operator | `Chapter02.Section09` | perturbation bound, Neumann expansion |
| §3.1 The Weierstrass approximation theorems | `Chapter03.Section01` | Stone–Weierstrass, Müntz |
| §3.2 Interpolation theory | `Chapter03.Section02` | Lagrange, Hermite, trigonometric |
| §3.3 Best approximation | `Chapter03.Section03` | existence, uniqueness |
| §3.4 Best approximation in inner product spaces | `Chapter03.Section04` | projections |
| §3.5 Orthogonal polynomials | `Chapter03.Section05` | the classical families |
| §3.6 Projection operators | `Chapter03.Section06` | direct sums |
| §3.7 Uniform error bounds | `Chapter03.Section07` | Lebesgue lemma, Jackson's theorems |
| §4.1 Fourier series | `Chapter04.Section01` | coefficients, Parseval |
| §4.2 The Fourier transform | `Chapter04.Section02` | normalization, Plancherel |
| §4.3 The discrete Fourier transform | `Chapter04.Section03` | the matrix $F_n$ |
| §4.4 Haar wavelets | `Chapter04.Section04` | scaling function, wavelet spaces |
| §4.5 Multiresolution analysis | `Chapter04.Section05` | axioms, Haar as an instance |
| §5.1 The Banach fixed-point theorem | `Chapter05.Section01` | strongly monotone operators |
| §5.2 Applications of the fixed-point theorem | `Chapter05.Section02` | matrix splittings |
| §5.3 Differential Calculus for Nonlinear Operators | `Chapter05.Section03` | convex functionals |
| §5.4 Newton's Method | `Chapter05.Section04` | Newton–Kantorovich, chord method |
| §5.5 Completely Continuous Vector Fields | `Chapter05.Section05` | definitions, examples |
| §5.6 Conjugate Gradient Method for Operator Equations | `Chapter05.Section06` | Winther |
| §6.1 Difference Approximations of Derivatives | `Chapter06.Section01` | (6.1.1)–(6.1.4) |
| §6.2 The Lax equivalence theorem | `Chapter06.Section02` | well-posedness, stability |
| §6.3 Two-level difference schemes | `Chapter06.Section03` | consistency, convergence |
| §7.1 Weak derivatives | `Chapter07.Section01` | tensor and multi-index forms |
| §7.2 Sobolev spaces | `Chapter07.Section02` | $W^{k,p}(\Omega)$, $W_0^{k,p}(\Omega)$ |
| §7.3 Density, extensions, embeddings, traces, norms | `Chapter07.Section03` | Deny–Lions |
| §7.4 The Fourier characterization of Sobolev spaces | `Chapter07.Section04` | $H^k$ |
| §7.5 Periodic Sobolev spaces | `Chapter07.Section05` | $H^s(2\pi)$, trapezoidal rule |
| §7.6 Integration by parts formulas | `Chapter07.Section06` | Gauss–Green, Green's formula |
| §8.2 Existence and uniqueness for operator equations | `Chapter08.Section02` | closed range |
| §8.3 The Lax–Milgram lemma | `Chapter08.Section03` | bilinear forms |
| §8.4 Weak formulations of linear elliptic problems | `Chapter08.Section04` | Lemma 8.4.1 |
| §8.5 A boundary value problem of linearized elasticity | `Chapter08.Section05` | Korn |
| §8.6 Mixed and dual formulations | `Chapter08.Section06` | saddle points, minimax |
| §8.7 The generalized Lax–Milgram lemma | `Chapter08.Section07` | inf–sup condition |
| §8.8 A nonlinear problem | `Chapter08.Section08` | existence, uniqueness, energy |
| §9.1 The Galerkin method | `Chapter09.Section01` | Ritz method, Céa's inequality |
| §9.2 The Petrov–Galerkin method | `Chapter09.Section02` | Babuška, Xu–Zikatanov |
| §9.3 The generalized Galerkin method | `Chapter09.Section03` | Strang's first lemma |
| §9.4 The conjugate gradient method in variational form | `Chapter09.Section04` | rates |
| §10.1 One-dimensional finite element examples | `Chapter10.Section01` | cubic Hermite element |
| §10.2 Affine-equivalent finite elements | `Chapter10.Section02` | the affine map $F_K$ |
| §10.3 Interpolation error estimates | `Chapter10.Section03` | regular families |
| §10.4 Convergence and error estimates | `Chapter10.Section04` | Aubin–Nitsche |
| §11.1 From variational equations to variational inequalities | `Chapter11.Section01` | obstacle |
| §11.2 Existence and uniqueness based on convex minimization | `Chapter11.Section02` | $f + j$ |
| §11.3 Existence and uniqueness for elliptic inequalities | `Chapter11.Section03` | (11.3.3) |
| §11.4 Numerical approximation of elliptic inequalities | `Chapter11.Section04` | Falk |
| §12.1 Projection methods for equations of the second kind | `Chapter12.Section01` | stability |
| §12.2 Examples of projection methods | `Chapter12.Section02` | collocation, Galerkin |
| §12.3 Iterated projection methods | `Chapter12.Section03` | Sloan's superconvergence |
| §12.4 The Nyström method | `Chapter12.Section04` | collective compactness |
| §12.5 Product integration | `Chapter12.Section05` | weakly singular kernels |
| §12.6 Iteration methods for the discretized equations | `Chapter12.Section06` | two-grid |
| §12.7 Projection methods for nonlinear equations | `Chapter12.Section07` | §12.7.1 |
| §13.1 Green's theorem, Kelvin transform, double layer kernel | `Chapter13.Section01` | $k(t, s)$ |
| §13.2 The Nyström method for the boundary integral equation | `Chapter13.Section02` | $C_p(L)$ |
| §13.3 The Fourier–Galerkin method for a first kind equation | `Chapter13.Section03` | (13.3.14) |
| §14.1 Multivariable polynomials and best approximation | `Chapter14.Section01` | $\Pi_n^d$ |
| §14.2 Orthogonal polynomials in several variables | `Chapter14.Section02` | the ball |
| §14.3 Hyperinterpolation | `Chapter14.Section03` | exact quadrature |
| §14.4 A Galerkin method for an elliptic equation on the disk | `Chapter14.Section04` | (14.4.8) |

## Conventions

* A declaration that states a numbered item is named after it: `AtkinsonHan.Chapter08.theorem_8_3_4`
  is Theorem 8.3.4, `AtkinsonHan.Chapter02.corollary_2_5_7` is Corollary 2.5.7,
  `AtkinsonHan.Chapter02.equation_2_3_16` is the display (2.3.16), and
  `AtkinsonHan.Chapter09.exercise_9_3_1` is Exercise 9.3.1. Where one item needs several
  declarations (its clauses, the two directions of an equivalence, or the three norms of Example
  2.2.8), a suffix tells them apart, as in `AtkinsonHan.Chapter03.proposition_3_6_9_b`,
  `AtkinsonHan.Chapter08.theorem_8_3_3_subspace` and `AtkinsonHan.Chapter02.example_2_2_8_l1`.
* A definition of the book that has its own vocabulary gets a descriptive name, such as
  `AtkinsonHan.Chapter02.IsBoundedOperator`, `AtkinsonHan.Chapter02.IsSublinear`,
  `AtkinsonHan.BilinForm`, `AtkinsonHan.Chapter05.BookSplitting`,
  `AtkinsonHan.Chapter05.HasGateauxDerivAt`, `AtkinsonHan.Chapter08.IsSaddlePoint` and
  `AtkinsonHan.DualProblem`, and a lemma relates it to the notion of Mathlib or the backbone that it
  agrees with. A numbered definition is often a `def … : Prop` in the words of the book, with a
  companion theorem `…_iff`.
* The declarations of each chapter are in the namespace of the chapter, from `AtkinsonHan.Chapter01`
  to `AtkinsonHan.Chapter14`. The bilinear-form vocabulary that Sections 8.3 and 8.7 and Chapters 9
  and 10 share is in the namespace `AtkinsonHan`. A section module imports the earlier section
  modules whose definitions it uses: for example, §3.3 takes weak convergence from §2.7, and §11.3
  takes strong monotonicity from §5.1.
* The scalar field $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$ of the book is `𝕜` with `[RCLike 𝕜]`.
  Where the book restricts to the reals (§3.4 except Theorems 3.4.6 and 3.4.7, Definition 2.5.4 and
  Theorem 2.5.5, Definition 3.3.6 and Theorem 3.3.7, strictly normed spaces, and Chapters 8, 9 and
  10), the statements are over $\mathbb{R}$. A statement that combines a $\mathbb{K}$-subspace with
  a real convex set carries `[NormedSpace ℝ V]` and `[IsScalarTower ℝ 𝕜 V]`, because `Convex ℝ K`
  does not elaborate under a bare `[NormedSpace 𝕜 V]`. Definitions that need only a linear space, in
  Chapter 1 and in §2.2 and §2.8, are stated over a division ring or a bare `Module`.
* The scalar $\lambda$ of an equation of the second kind is written `l` in §2.8, `lam` in §2.9 and
  in Theorem 12.5.6, and `μ` elsewhere in Chapter 12, because `λ` is a keyword of Lean.
* The inner product $(u, v)$ of the book is linear in its first argument, and Mathlib's
  `inner 𝕜 u v` is linear in its second argument. The book's $(u, v)$ is therefore `inner 𝕜 v u`,
  and several statements of §2.5, §2.6 and §3.4 read with their arguments reversed. The two forms
  agree in the real case.
* The space $\mathcal{L}(V, W)$ is `V →L[𝕜] W`, the dual space $V'$ is `StrongDual 𝕜 V`, and
  $V^\perp$ is `Submodule.orthogonal`. The null space $\mathcal{N}(L)$ and the range
  $\mathcal{R}(L)$ are `LinearMap.ker` and `LinearMap.range`. "$L$ is a bijection of $V$ onto $W$
  with bounded inverse" is `∃ e : V ≃L[𝕜] W, ↑e = L`, and
  `AtkinsonHan.Chapter02.isUnit_iff_exists_continuousLinearEquiv` relates it to `IsUnit`.
  Reflexivity (Definition 2.7.4) is the backbone's `NormedSpace.IsReflexive`; Mathlib's
  `Module.IsReflexive` is the algebraic double dual, a different notion.
* The data of §8.3 and Chapters 9 and 10 is a bilinear form `AtkinsonHan.BilinForm V`, that is
  `V →ₗ[ℝ] V →ₗ[ℝ] ℝ`, with the predicates `AtkinsonHan.BilinForm.IsBoundedWith`,
  `AtkinsonHan.BilinForm.IsEllipticWith` and `LinearMap.BilinForm.IsSymm`. Bundled by
  `AtkinsonHan.BilinForm.toCLM`, such a form is the backbone's `SesqForm ℝ V`, so the results of
  `Numlib.Variational` apply to it with no conversion. A form on two spaces is
  `AtkinsonHan.BilinForm₂`.
* The inf–sup conditions (8.7.2) and (9.2.6) are stated as the book prints them, with the supremum
  of $a(u, v)/\|v\|$ without absolute values. `AtkinsonHan.BilinForm₂.iSup_div_eq_norm_apply` and
  `AtkinsonHan.Chapter09.iSup_div_eq_norm_comp` show that this supremum is the norm of the
  functional $a(u, \cdot)$, by the symmetry $v \mapsto -v$, which is the form of the condition in
  the backbone.
* `sSup` and `sInf` take junk values on unbounded or empty sets. So every statement that the book
  writes with a supremum or an infimum either has the hypothesis that makes it a real supremum
  (Proposition 8.6.2) or proves it (the supremum over the data in the Aubin–Nitsche lemma (10.4.5),
  which the Lax–Milgram estimate for the dual solution bounds).
* $C[a, b]$ is `C(Set.Icc a b, ℝ)`, and $C_p(2\pi)$, the continuous $2\pi$-periodic functions, is
  `C(AddCircle (2 * π), ℝ)`, both with the supremum norm. $C^m[a, b]$ is the backbone's
  `ContDiffMapIcc`, with the norm $\sum_{j \le m} \|v^{(j)}\|_\infty$, which is the norm (2.1.2) of
  the book for $m = 1$. The exponent $p \in [1, \infty]$ of $L^p$ is `p : ℝ≥0∞`. Where $L^p$ or
  $L^2$ lives on the circle (§3.4, §4.1, §12.2, §13.3), the measure is the normalized Haar measure
  `AddCircle.haarAddCircle`, whose norm differs from the norm of the book by a constant factor.
* Where the book poses a problem on a domain of $\mathbb{R}^d$ with a boundary (Chapters 7 and 8 and
  their applications), the ambient space is $\mathbb{R}^{d+1}$, so that the boundary charts and the
  Poincaré inequality of the backbone apply; the $d$ of the book is $d + 1$ there. The book assumes
  Lipschitz domains, which the library does not have. The statements assume instead a Sobolev
  extension domain, a bounded $C^1$ domain or a triangulated plane domain, as the conventions of
  `NumlibSurface.AtkinsonHan.Chapter07.Section03` describe, and each such change is a deviation
  below.
* Where the book has a hypothesis that its proof does not use, the hypothesis is kept and the doc
  comment says so: the convexity in Theorems 3.3.13 and 3.3.15, the condition $\alpha > 0$ in
  Theorems 3.7.1 and 3.7.2, the vector space structure in the metric part of §5.1, the completeness
  of $W$ in Theorem 5.4.2, and the Hilbert space data of Theorem 9.3.1, which
  `AtkinsonHan.Chapter09.theorem_9_3_1'` adds to the abstract `AtkinsonHan.Chapter09.theorem_9_3_1`.

## Deviations from the source

**Chapter 1, Linear Spaces.**

* **Section 1.1, scalars** (generalization). The abstract linear algebra uses any division ring
  in place of real or complex scalars. See `AtkinsonHan.Chapter01.definition_1_1_1`.
* **Example 1.1.2** (reading). The function-space clauses use real-valued functions and state
  the differentiability clause on all of $\mathbb{R}^d$. See `AtkinsonHan.Chapter01.example_1_1_2`.
* **Definition 1.1.3** (reading). The book requires a subspace to be a linear space, which excludes
  the empty set. The definition states only the two closure conditions, and its correspondence with
  `Submodule` assumes that the set is nonempty. See `AtkinsonHan.Chapter01.definition_1_1_3_iff`.
* **Theorem 1.1.10** (generalization). The finite-cardinality identity also applies to infinite
  bases, for which both natural-valued counts are zero. See `AtkinsonHan.Chapter01.theorem_1_1_10`.
* **Example 1.1.12** (correction). The dimension drops by two for $n \ge 1$; at $n = 0$ it drops
  by one. See `AtkinsonHan.Chapter01.example_1_1_12`.
* **Example 1.1.15** (reading). Lean states the isomorphism on the polynomial type and gives the
  coefficient map in the proof. See `AtkinsonHan.Chapter01.example_1_1_15`.
* **Seminorms, balls, convergence, and continuity** (scope). The seminorm predicate assumes an
  existing norm. Several ball, convergence, and continuity facts use only a normed additive
  commutative group. See `AtkinsonHan.Chapter01.definition_1_2_2` and
  `AtkinsonHan.Chapter01.definition_1_2_6`.
* **Examples 1.2.3 and 1.2.5(a)** (scope). The norm formulas also cover zero coordinates and
  empty intervals using the supremum convention.
* **Example 1.2.15** (reading). A power function witnesses failure of each proposed norm bound
  in place of the source's triangular sequence. See `AtkinsonHan.Chapter01.example_1_2_15`.
* **Series, density, bases, and completeness in §1.2** (generalization). The series, density,
  and Cauchy criteria need only a normed additive commutative group. Relative density allows
  nonnested sets, and the basis predicates do not assume infinite dimension.
* **Example 1.2.22** (reading). The supremum-norm completeness covers arbitrary compact sets.
  The incompleteness for finite $p$ is stated on $[0,1]$, using one-sided ramps. See
  `AtkinsonHan.Chapter01.example_1_2_22_incomplete`.
* **Theorem 1.2.26** (generalization). The book states the dominated convergence theorem for
  Lebesgue measure on a measurable set. Lean works on any measure space and assumes almost
  everywhere strong measurability of the terms. See `AtkinsonHan.Chapter01.theorem_1_2_26`.
* **Theorem 1.2.27** (generalization and reading). Lean allows two s-finite measure spaces and
  gives integrability of almost every section and equality of the iterated integrals. The
  source also states integrability of the inner integral functions and equality to the product
  integral. See
  `AtkinsonHan.Chapter01.theorem_1_2_27`.
* **Example 1.2.28(a), the norms** (reading). The completeness results use the sum of derivative
  supremum norms, equivalent to the book's maximum norm. See
  `AtkinsonHan.Chapter01.example_1_2_28_a` and `AtkinsonHan.Chapter01.example_1_2_28_a_periodic`.
* **Example 1.2.28(b), the normed space** (generalization). The norm construction accepts
  $p = \infty$. See `AtkinsonHan.Chapter01.ContDiffMapIccSobolevNorm`.
* **Examples 1.3.6 and 1.3.7** (generalization and reading). The $L^2$ examples use an arbitrary
  measure, and the Sobolev example uses the weak-derivative model on any interval. See
  `AtkinsonHan.Chapter01.example_1_3_6` and `AtkinsonHan.Chapter01.example_1_3_7`.
* **The identity following Definition 1.3.8** (reading). Lean gives the two-vector instance.
  See `AtkinsonHan.Chapter01.definition_1_3_8_pythagoras`.
* **Theorems 1.3.11 and 1.3.12** (generalization and reading). Lean uses unordered sums over
  arbitrary index sets. Theorem 1.3.11 gives (a)–(c), and Theorem 1.3.12 combines the dense-span
  clauses and gives the two Parseval identities.
* **Theorem 1.3.13** (reading). Probability Haar measure on the circle changes the basis
  factor by $\sqrt{2\pi}$. See `AtkinsonHan.Chapter01.theorem_1_3_13`.
* **Lemmas 1.5.3 and 1.5.4 and Theorem 1.5.5** (generalization). The book works on
  $\Omega \subseteq \mathbb{R}^d$ with Lebesgue measure. The statements hold on every measure space,
  and Theorem 1.5.5(c) holds on every finite measure space without the assumption $p \ge 1$. See
  `AtkinsonHan.Chapter01.lemma_1_5_3`, `AtkinsonHan.Chapter01.lemma_1_5_4` and
  `AtkinsonHan.Chapter01.theorem_1_5_5_c`.
* **Definition 1.6.1** (generalization). Compactness is stated for normed additive commutative
  groups and precompactness for arbitrary topological spaces. See
  `AtkinsonHan.Chapter01.definition_1_6_1` and `AtkinsonHan.Chapter01.definition_1_6_1_precompact`.

**Chapter 2, Linear Operators on Normed Spaces.**

* **Definitions 2.1.1 and 2.1.6 and Examples 2.1.2 and 2.1.3** (generalization). The map and
  identity properties apply to arbitrary types, the matrix rank criteria to arbitrary fields,
  and boundedness of total operators to seminormed additive groups. See
  `AtkinsonHan.Chapter02.definition_2_1_1`, `AtkinsonHan.Chapter02.example_2_1_3`, and
  `AtkinsonHan.Chapter02.IsBoundedOperator`.
* **Example 2.1.7** (reading). Lean gives explicit witnesses to unbounded differentiation in
  the supremum norm. See `AtkinsonHan.Chapter02.example_2_1_7`.
* **Definition 2.2.1, (2.2.3), and Theorem 2.2.5** (generalization and reading). Linearity extends
  to division rings. The Lipschitz estimate uses the operator norm, whose formulas use unit
  radius and give zero for an empty supremum. See `AtkinsonHan.Chapter02.theorem_2_2_5`.
* **Example 2.2.7** (reading). The book does not exclude the zero space, on which every operator
  norm is $0$. The statement assumes $V \neq \{0\}$. See `AtkinsonHan.Chapter02.example_2_2_7`.
* **Example 2.2.8** (generalization and reading). The row and column formulas allow real
  scalars and empty index sets. The spectral norm identity uses $A^*A$. See
  `AtkinsonHan.Chapter02.example_2_2_8_l2`.
* **Examples 2.3.2, 2.3.4, and 2.3.6** (generalization and reading). The abstract inverse bounds
  apply to general Banach endomorphisms. The Volterra example uses a continuous square kernel
  and arbitrary nonzero identity coefficient. The sine-kernel norm is bundled with the
  solvability result. See `AtkinsonHan.Chapter02.example_2_3_4_volterra`.
* **Theorem 2.3.5** (reading). A zero inverse norm makes the strict perturbation condition false
  by Lean's reciprocal convention. See `AtkinsonHan.Chapter02.theorem_2_3_5`.
* **Stability and the condition number in §2.4.2** (generalization and correction). Stability
  assumes a bounded isomorphism, the relative bound assumes a nonzero exact solution, and the
  condition number lower bound excludes the zero space. See `AtkinsonHan.Chapter02.one_le_cond`.
* **Theorem 2.4.5, sufficiency** (generalization). The result uses any dense subset and needs
  no completeness. See `AtkinsonHan.Chapter02.tendsto_of_tendsto_on_dense_of_bounded`.
* **Examples 2.5.1, 2.5.3, and 2.5.9, and Corollary 2.5.7** (scope and reading). The real $L^\infty$
  nonrepresentation theorem allows any nonempty open domain of positive dimension, the point
  evaluation identity uses globally continuous functions, and the $L^2$ representation applies
  to any Euclidean subset. The dual ball formula gives zero in the zero space.
* **Example 2.6.1, Theorem 2.6.5, and Exercise 2.6.3** (reading). The kernel equalities are
  almost everywhere. The norm formula and corresponding estimate use a nonzero space so the
  unit sphere is nonempty. See `AtkinsonHan.Chapter02.example_2_6_1_isSelfAdjoint` and
  `AtkinsonHan.Chapter02.theorem_2_6_5`.
* **Section 2.4.4** (generalization). The book approximates the functional
  $Lv = \int_0^1 w(x) v(x) \, dx$. The statement holds for every bounded linear functional $L$ on
  $C[0, 1]$. See `AtkinsonHan.Chapter02.quadrature_convergence`.
* **Example 2.5.1** (generalization). The book takes $\Omega \subseteq \mathbb{R}^d$ bounded and
  open. The identification $(L^p(\Omega))' = L^{p'}(\Omega)$ for $1 \le p < \infty$ holds for every
  set $\Omega$. See `AtkinsonHan.Chapter02.example_2_5_1`.
* **Section 2.6** (generalization). The book restricts the section to real scalars. The statements
  about adjoint and self-adjoint operators hold over $\mathbb{R}$ and over $\mathbb{C}$. See
  `AtkinsonHan.Chapter02.equation_2_6_1`.
* **Example 2.7.3 and Exercises 2.7.3–2.7.4** (reading and generalization). The sine example
  uses Haar probability measure and scaled vectors. The exercises are stated over the reals,
  and the uniformly convex result gives the sufficiency implication without completeness.
* **Theorem 2.7.5** (generalization). The book assumes a Banach space. The statement holds for every
  normed space, because a reflexive normed space is complete. See
  `AtkinsonHan.Chapter02.theorem_2_7_5`.
* **Equations (2.8.5) and (2.8.6)** (reading). The modulus estimate is for continuous inputs.
  The operator norm uses a supremum, which agrees with the maximum on nonempty compact $D$
  by condition (A₁). See `AtkinsonHan.Chapter02.equation_2_8_6`.
* **Example 2.8.5** (reading). The kernel results use continuous factors on a compact measure
  space. The book allows integrable second factors on a closed interval. See
  `AtkinsonHan.Chapter02.example_2_8_5`.
* **Examples 2.8.2, 2.8.8, and 2.8.9** (reading). The singular kernels take value zero on the
  diagonal, and the continuous-kernel result uses restricted ambient Lebesgue measure.
* **Definitions 2.8.3 and 2.8.11 and Theorems 2.8.12–2.8.14** (generalization). Some results
  allow broader scalar fields, incomplete spaces, or nonzero scalars that are not eigenvalues.
* **Theorem 2.8.15, the basis** (correction). The closed span of the nonzero eigenvectors is
  the closure of the range of $K$. With $K=I$ on a nonzero finite-dimensional space, the
  source's printed range of $\lambda I-K$ at $\lambda=1$ is zero. See
  `AtkinsonHan.Chapter02.theorem_2_8_15_enumeration`.
* **Theorem 2.8.15, the reality of the eigenvalues, the index one and the closed range**
  (generalization). The book assumes a compact operator. These three clauses are stated for every
  bounded self-adjoint operator. See `AtkinsonHan.Chapter02.theorem_2_8_15_index`.
* **Definition 2.9.1** (generalization). The book works on a complex Banach space. The definition
  allows real or complex scalars and any normed space. See `AtkinsonHan.Chapter02.definition_2_9_1`.
* **Lemma 2.9.2 and (2.9.3)** (generalization and reading). The perturbation bound assumes a
  nonzero space and controls the resolvent on its domain. The local bounds and series expansion
  work over the reals as well.

**Chapter 3, Approximation Theory.**

* **Theorems 3.1.1 and 3.1.2** (reading and generalization). The polynomial approximation
  bound is strict with arbitrary tolerance, and Stone–Weierstrass allows any compact
  topological space. See `AtkinsonHan.Chapter03.theorem_3_1_1` and
  `AtkinsonHan.Chapter03.theorem_3_1_2`.
* **Corollary 3.1.4** (generalization). The book takes the period $2\pi$. The statement holds for
  the continuous functions of every period $T > 0$. See `AtkinsonHan.Chapter03.corollary_3_1_4`.
* **Section 3.2** (reading and generalization). The abstract interpolation problem allows
  nontrivially normed fields, and the concrete interpolation statements spell out the node
  conditions and regularity of the real data. See `NumlibSurface.AtkinsonHan.Chapter03.Section02`.
* **Definition 3.3.4** (reading). The limit inferior $\liminf_n f(v_n)$ is taken in the extended
  reals. The real `liminf` of Lean is $0$ for a sequence that is not bounded below, and with it
  Theorem 3.3.8 would be false. See `AtkinsonHan.Chapter03.definition_3_3_4`.
* **Theorems 3.3.8, 3.3.10 and 3.3.12–3.3.15** (correction). The minimization and best
  approximation statements require a nonempty feasible set. The strict-convexity uniqueness
  assertion of Theorems 3.3.12 and 3.3.13 is stated in
  `AtkinsonHan.Chapter03.theorem_3_3_13_unique`.
* **Section 3.3** (reading and generalization). Several statements use the underlying real
  normed-space structure. The separation predicates also allow empty sets, and the Chebyshev
  alternation theorem explicitly requires a nondegenerate interval. See
  `NumlibSurface.AtkinsonHan.Chapter03.Section03`.
* **Proposition 3.4.4** (generalization). The two inequalities hold for any two best approximations
  from a convex set, with no completeness of the space. See
  `AtkinsonHan.Chapter03.proposition_3_4_4`.
* **Theorems 3.4.6 and 3.4.7 and (3.4.6)** (generalization). The book works over $\mathbb{R}$. These
  results are stated over $\mathbb{R}$ or $\mathbb{C}$. See `AtkinsonHan.Chapter03.theorem_3_4_6`
  and `AtkinsonHan.Chapter03.theorem_3_4_7`.
* **Theorem 3.4.7, display (3.4.5)** (correction). The book states $\|P_K\| = 1$. This fails for
  $K = \{0\}$, where $P_K = 0$. The library states $\|P_K\| \le 1$, with equality when
  $K \neq \{0\}$. See `AtkinsonHan.Chapter03.theorem_3_4_7`.
* **Theorem 3.4.5** (correction). The finite-dimensional existence theorem requires a nonempty
  feasible set. See `AtkinsonHan.Chapter03.theorem_3_4_5`.
* **Example 3.4.9** (reading). The probability Haar normalization changes the individual
  Fourier coefficients and basis vectors, while preserving the approximant. See
  `AtkinsonHan.Chapter03.example_3_4_9`.
* **Equations (3.5.1)–(3.5.2)** (reading). The criterion for a weight requires pointwise positivity
  in the interior. The orthogonal projection uses a monic family. See
  `AtkinsonHan.Chapter03.isWeight_weightMeasure` and `AtkinsonHan.Chapter03.equation_3_5_2`.
* **Example 3.6.4** (reading). The book's $V_1$ is a general line through the origin of
  $\mathbb{R}^2$, drawn in Figure 3.4. The library states the displayed formula for $V_1$ the
  $x_1$-axis. See `AtkinsonHan.Chapter03.example_3_6_4`.
* **Equations (3.7.15) and (3.7.17)** (correction). The projection kernel and its row norm must
  be integrated against the weighted measure used to define the orthogonal expansion. See
  `AtkinsonHan.Chapter03.equation_3_7_15` and `AtkinsonHan.Chapter03.equation_3_7_17`.
* **Example 3.7.4** (correction). The norm formula integrates the absolute value of the
  Dirichlet kernel, in agreement with (3.7.9). See `AtkinsonHan.Chapter03.example_3_7_4`.
* **(3.7.20)** (correction). The book quotes the bound $\|\mathcal{I}_n\| \le 1 + (2/\pi) \log n$
  for $n \ge 1$. It is false at $n = 1$, where $\|\mathcal{I}_1\| \ge 5/3$. The library proves its
  negation and the bound $\|\mathcal{I}_n\| \le 2 + (2/\pi) \log(2n + 1)$. See
  `AtkinsonHan.Chapter03.not_equation_3_7_20` and `AtkinsonHan.Chapter03.norm_trigInterpCLM_bound`.

**Chapter 4, Fourier Analysis and Wavelets.**

* **Equation (4.1.6)** (correction). Recovering sine and cosine coefficients from the real
  and imaginary parts of the complex Fourier coefficients requires a real-valued input.
  See `AtkinsonHan.Chapter04.equation_4_1_6_cos` and `AtkinsonHan.Chapter04.equation_4_1_6_sin`.
* **Theorem 4.1.1** (generalization). The book assumes that $f$ is piecewise continuous. The library
  assumes only that $f$ is integrable over one period. See `AtkinsonHan.Chapter04.theorem_4_1_1`.
* **Theorem 4.1.2** (generalization). The book states the theorem for the Fourier partial sum
  operators $S_N$ on $L^p$. The library states it for every sequence of bounded operators on $L^p$
  that converges to the identity on the trigonometric polynomials. See
  `AtkinsonHan.Chapter04.theorem_4_1_2`.
* **(4.1.15)** (reading). The hypotheses "the Fourier series is absolutely convergent" and "$f$ is
  continuous after a change on a set of measure zero" are read as the summability of $|a_j| + |b_j|$
  and the convergence of $S_n f(x)$ to $f(x)$ at every $x$. See
  `AtkinsonHan.Chapter04.equation_4_1_15`.
* **Section 4.2** (reading and generalization). The integral inversion formula is pointwise
  for continuous integrable data with integrable transform. The derivative and moment formulas
  cover first order, and the $L^2$ transform is extended by continuity from Schwartz functions.
  See `NumlibSurface.AtkinsonHan.Chapter04.Section02`.
* **The spaces $V_j$ of §4.4** (reading). The book defines $V_j$ as the set of finite linear
  combinations of the functions $\phi(2^j x - k)$. Here $V_j$ is the closure of this set in
  $L^2(\mathbb{R})$. See `AtkinsonHan.Chapter04.equation_4_4_1`.
* **Theorem 4.4.1(3) and the multilevel formulas** (reading). The nested inclusions are given
  without strictness. The multilevel formulas use the coefficients of a common input, while
  the book's reconstruction permits independently modified coefficients. See
  `AtkinsonHan.Chapter04.theorem_4_4_1_3` and `AtkinsonHan.Chapter04.equation_4_4_18`.
* **Section 4.5, density of the wavelet spaces** (correction). The wavelet spaces span a
  dense subspace of $L^2(\mathbb R)$. Their set-theoretic union cannot be dense because the
  spaces are mutually orthogonal. See `AtkinsonHan.Chapter04.theorem_wavelet_spaces`.

**Chapter 5, Nonlinear Equations and Their Solution by Iteration.**

* **Theorem 5.2.4** (scope). The Banach-space existence theorem uses a supplied field bound.
  The separate weighted Picard convergence theorem treats a scalar equation on a one-sided
  interval, with global Lipschitz continuity in the state variable.
* **Example 5.3.10** (scope). Joint continuity of the partial derivative on the full product
  replaces continuity along the graph of a single trial function.
* **Theorem 5.3.19** (generalization). The book states that the minimization problem and the
  variational inequality (5.3.10) are equivalent as problems. Here they are equivalent at each point
  $u \in K$. See `AtkinsonHan.Chapter05.theorem_5_3_19`.
* **Theorem 5.4.2, uniqueness** (correction). The book states that the root is unique in the closed
  ball of radius $t^{**} = (1 + \sqrt{1 - 2h})/(aL)$ about $u_0$. This is false for $h < 1/2$: the
  scalar majorant $p(t) = (L/2) t^2 - t/a + b/a$ satisfies every hypothesis at $u_0 = 0$ and has a
  second zero at distance exactly $t^{**}$. The statement uses the open ball. See
  `AtkinsonHan.Chapter05.theorem_5_4_2_unique`.
* **Equations (5.4.8), (5.4.10) and (5.4.12)** (correction). The derivative of the residual
  subtracts the integral operator derivative. The Newton correction equations use the
  negative residual, which removes the extra factor $u_n(s)$ from both printed integrals.
* **Example 5.5.2** (scope). The source requires $t < 1$ alongside the Lipschitz bound.
  Lean includes $t = 1$. See `AtkinsonHan.Chapter05.example_5_5_2`.
* **Theorem 5.6.2** (generalization). The rate of the book has the factor
  $(\Delta/\delta)^{3/(2k)}$. The statement proves the rate with the smaller factor
  $(\Delta/\delta)^{1/(2k)}$. See `AtkinsonHan.Chapter05.theorem_5_6_2`.

**Chapter 6, Finite Difference Method.**

* **Example 6.1.1, (6.1.19)** (typo). The book prints $u_{j \pm 1}^{m-1}$ where it means
  $v_{j \pm 1}^{m-1}$. See `AtkinsonHan.Chapter06.example_6_1_1`.
* **Proposition 6.2.6** (reading). The statement assumes well-posedness on every horizon $T' \le T$,
  not only on $T$. See `AtkinsonHan.Chapter06.proposition_6_2_6`.
* **Definition 6.2.7** (reading). The truncation error is tested only at the $t \in [0, T]$ with
  $t + \Delta t \le T$, where the solution operators are defined. See
  `AtkinsonHan.Chapter06.IsConsistent`.
* **Definition 6.2.9** (reading). The limit is taken along every pair of sequences
  $(\Delta t_i, m_i)$ with $\Delta t_i \to 0$ and $m_i \Delta t_i \to t$, restricted to
  $m_i \Delta t_i \le T$. See `AtkinsonHan.Chapter06.IsConvergent`.
* **Theorem 6.2.11** (reading). The uniform bound $\|C(\Delta t)\| \le c_1$ appears as a
  theorem hypothesis. The source assumes it when introducing the family. See
  `AtkinsonHan.Chapter06.theorem_6_2_11`.
* **Corollary 6.2.12** (correction). With local error constant $c$ and power bound $M_0$,
  the global constant at time $t$ is $M_0 t c$. The proof uses stability.
* **Exercise 6.2.3** (correction). The equality $\|C(\Delta t)\| = |1 - 2r| + 2r$ needs a small
  space step. The library assumes $\Delta x < \pi/2$. See
  `AtkinsonHan.Chapter06.norm_forwardScheme_eq`.
* **Definition 6.3.1 and Theorem 6.3.2** (generalization). The book works in $\mathbb{R}^{N_x - 1}$
  with a norm chosen for each example. The library uses a fixed real normed space for the
  whole family. The global estimate uses the explicit constant $M_0 T c$. See
  `AtkinsonHan.Chapter06.theorem_6_3_2`.
* **Definition 6.3.1** (reading). The limit "as $h_x, h_t \to 0$" is a limit along a filter on the
  index set of the family. See `AtkinsonHan.Chapter06.IsConsistentScheme`.

**Chapter 7, Sobolev Spaces.**

* **Example 7.1.9** (generalization). The book assumes $v \in C^k(\overline\Omega)$. The library
  assumes $v \in C^k(\Omega)$. See `AtkinsonHan.Chapter07.example_7_1_9`.
* **Example 7.1.9** (reading). The subdomains $\Omega_n$ are the triangles of a triangulation, and
  $v|_{\Omega_n} \in C^{k+1}(\overline\Omega_n)$ means that $v$ agrees on the open triangle with a
  $C^{k+1}$ function on the plane. See `AtkinsonHan.Chapter07.example_7_1_9`.
* **Proposition 7.1.12** (generalization). The book assumes $v \in W^{1,p}(\Omega)$ and concludes
  for every first-order derivative. The library assumes $v, \partial^\alpha v \in L^p(\Omega)$ for
  one $\alpha$ with $|\alpha| = 1$ and concludes for that $\alpha$. See
  `AtkinsonHan.Chapter07.proposition_7_1_12`.
* **Example 7.2.5, the $L^p$ part** (generalization). The book takes $1 \le p < \infty$. The
  statement holds for every $0 < p < \infty$. See `AtkinsonHan.Chapter07.example_7_2_5_memLp`.
* **Definition 7.2.1** (generalization). The boundary class predicate allows unbounded open
  sets. See `AtkinsonHan.Chapter07.definition_7_2_1`.
* **Example 7.2.5, the equivalence for $W^{1,p}$** (correction). The book states $|x|^\lambda \in
  W^{1,p}(\Omega) \iff \lambda > 1 - d/p$ for every real $\lambda$. This fails at $\lambda = 0$ when
  $d \le p$. The statement assumes $\lambda \neq 0$. See
  `AtkinsonHan.Chapter07.example_7_2_5_memW1p`.
* **Example 7.2.5, equation (7.2.1)** (correction). The book states $|x|^\lambda \in W^{k,p}(\Omega)
  \iff \lambda > k - d/p$ with no restriction on $\lambda$. This fails when $\lambda$ is a
  nonnegative even integer, where $|x|^\lambda$ is a polynomial. The statement excludes these
  values. See `AtkinsonHan.Chapter07.example_7_2_5` and `AtkinsonHan.Chapter07.example_7_2_5_const`.
* **Example 7.2.7** (reading). The class $C^k(\overline\Omega)$ is read as the functions that are
  $C^k$ on an open set that contains $\overline\Omega$. See `AtkinsonHan.Chapter07.example_7_2_7`.
* **Definition 7.2.13** (reading). The book asks $v \in L^2(\partial\Omega)$ for every $p$. The
  definition asks $v \in L^p(\partial\Omega)$. See `AtkinsonHan.Chapter07.definition_7_2_13_atlas`.
* **Definition 7.3.6** (generalization). The book assumes that $V$ and $W$ are Banach spaces. The
  definition is for normed spaces. See `AtkinsonHan.Chapter07.definition_7_3_6`.
* **Theorem 7.3.8(a)** (reading). The book leaves $k \ge 1$ implicit. At $k = 0$ the clause would
  say that $L^p(\Omega)$ embeds compactly in $L^q(\Omega)$ for $q < p$, which is false. See
  `AtkinsonHan.Chapter07.theorem_7_3_8_a`.
* **Theorem 7.3.8(b)** (reading). The book prints a continuous embedding, as in Theorem 7.3.7(b).
  The clause is formalized as printed and also as a compact embedding. See
  `AtkinsonHan.Chapter07.theorem_7_3_8_b` and `AtkinsonHan.Chapter07.theorem_7_3_8_b_compact`.
* **Theorem 7.3.10(c)** (correction). The book allows $1 \le p < \infty$. At $p = 1$ the trace maps
  $W^{1,1}(\Omega)$ onto $L^1(\Gamma)$ and is not compact. The library assumes $1 < p < \infty$. See
  `AtkinsonHan.Chapter07.theorem_7_3_10_compact` and
  `AtkinsonHan.Chapter07.theorem_7_3_10_polygon_compact`.
* **Theorem 7.3.11** (generalization). The book asks $v \in C^1(\overline\Omega)$ for
  $\gamma_0 v = v|_\Gamma$. Continuity on $\overline\Omega$ is enough. See
  `AtkinsonHan.Chapter07.theorem_7_3_11_trace₀_ae_eq`.
* **Theorem 7.3.11** (reading). The condition $v \in W^{s,p}(\Omega) \cap C^1(\overline\Omega)$ for
  $\gamma_1 v = \partial v / \partial\nu$ is read as the existence of a representative of class
  $C^1$ on $\mathbb{R}^{d+1}$. See `AtkinsonHan.Chapter07.theorem_7_3_11_trace₁_ae_eq`.
* **Theorem 7.3.14** (generalization). The book takes a disjoint union of the sets $\Omega_\lambda$.
  Disjointness is not assumed. See `AtkinsonHan.Chapter07.theorem_7_3_14`.
* **Example 7.3.16** (reading). The open subset $\Gamma_0$ of $\Gamma$ is $U \cap \Gamma$ for an
  open $U \subseteq \mathbb{R}^{d+1}$, and "$v = 0$ a.e. on $\Gamma_0$" means that $\gamma v = 0$
  $\sigma$-almost everywhere on $U$. See `AtkinsonHan.Chapter07.example_7_3_16`.
* **Example 7.4.2** (reading). The book assumes a Lipschitz domain. The statement assumes a bounded
  open set that is a $W^{1,q}$ extension domain for every $q$, which every bounded $C^1$ domain of
  Definition 7.2.1 is. See `AtkinsonHan.Chapter07.example_7_4_2`.
* **Example 7.4.3** (reading). The book assumes a Lipschitz domain and uses the universal extension
  operator of Stein. The statement assumes a bounded $C^{d+1}$ domain and uses the extension
  operator of order $d + 1$ with its $L^2$ bound. See `AtkinsonHan.Chapter07.example_7_4_3`.
* **Theorem 7.5.7** (generalization). The interpolation bound uses a constant depending on $s$
  alone, uniformly over $0 \le r \le s$. See `AtkinsonHan.Chapter07.theorem_7_5_7`.
* **The classical Gauss–Green formula, Proposition 7.6.1 and (7.6.3)** (reading). The book assumes a
  Lipschitz domain. The statements assume a bounded $C^1$ domain, or a plane domain triangulated
  without slits. See `AtkinsonHan.Chapter07.proposition_7_6_1_classical`,
  `AtkinsonHan.Chapter07.proposition_7_6_1` and `AtkinsonHan.Chapter07.proposition_7_6_1_polygon`.

**Chapter 8, Weak Formulations of Elliptic Boundary Value Problems.**

* **Example 8.2.3** (scope). The Lean example takes the Dirichlet realization of
  $-\Delta$ on a nonempty bounded open domain. The source's closedness argument uses the
  distributional Laplacian with no prescribed boundary condition.
* **Example 8.2.6** (reading). The book takes the seminorm $|v|_{H^1}$ as the norm of
  $V = H_0^1(\Omega)$. The type of $V$ carries the norm of $H^1(\Omega)$, so $\|L\| = 1$ and
  $\langle Lv, v \rangle = \|v\|_V^2$ are stated through the seminorm, and the strong monotonicity
  in the norm of $H^1(\Omega)$ carries the constant of Poincaré's inequality. See
  `AtkinsonHan.Chapter08.example_8_2_6`.
* **Example 8.3.5** (generalization). The book assumes a Lipschitz boundary. The example holds on
  every bounded open set. See `AtkinsonHan.Chapter08.example_8_3_5`.
* **Lemma 8.4.1** (generalization). The book assumes a Lipschitz domain. The lemma assumes a
  connected bounded $W^{1,2}$ extension domain, which includes the $C^1$ domains of Definition
  7.2.1. See `AtkinsonHan.Chapter08.lemma_8_4_1`.
* **Theorem 8.5.1** (generalization). The book assumes a Lipschitz domain. In the pure displacement
  case the theorem holds on every bounded open set. See
  `AtkinsonHan.Chapter08.theorem_8_5_1_dirichlet`.
* **Proposition 8.6.2** (reading). The book does not say whether the suprema and infima are finite.
  The proposition assumes that $L(v, \cdot)$ is bounded above on $B$ for each $v \in A$ and that
  $L(\cdot, q)$ is bounded below on $A$ for each $q \in B$. See
  `AtkinsonHan.Chapter08.proposition_8_6_2`.
* **Equation (8.7.3)** (reading). The book prints $\sup_{u \in U} a(u, v) > 0$ for $v \ne 0$. Read
  as an extended-real supremum, it is positive exactly when a positive value is attained
  for some $u$. Lean uses that witness directly. See
  `AtkinsonHan.Chapter08.theorem_8_7_1`.
* **Lemma 8.8.2** (generalization). The section assumes $1 < p < \infty$. The continuity of $E$
  holds for $1 \le p < \infty$. See `AtkinsonHan.Chapter08.lemma_8_8_2`.

**Chapter 9, The Galerkin Method and Its Variants.**

* **Example 9.1.1** (correction). With the indexing of the book, the displayed formula for the
  entries of the stiffness matrix is off by one. It holds for the basis indexed from $0$. See
  `AtkinsonHan.Chapter09.example_9_1_1`.
* **Remark 9.2.2** (correction). The bound $\|u - u_N\| \le (M / \alpha_N) \inf_{w_N \in U_N} \|u -
  w_N\|$ needs $U_N \ne \{0\}$, which the book does not state. On the trivial trial space the
  Petrov–Galerkin projector is $0$, every other hypothesis holds, and the bound fails. See
  `AtkinsonHan.Chapter09.remark_9_2_2`.

**Chapter 10, Finite Element Analysis.**

* **Exercise 10.1.2** (generalization). The statement is for every symmetric positive definite block
  matrix, not only for the matrix of the finite element system. See
  `AtkinsonHan.Chapter10.exercise_10_1_2`.
* **Exercise 10.1.3** (reading). The claim about a space of piecewise quadratic functions is stated
  as the fact about two neighbouring elements on which its proof rests. See
  `AtkinsonHan.Chapter10.exercise_10_1_3`.
* **Lemma 10.2.2** (generalization). The diameters in the denominator can come from any inscribed
  closed balls. The book takes the largest inscribed balls.
* **Equation (10.2.23) and Exercises 10.2.1 and 10.2.3** (reading). The book quantifies over the
  functions of the local space that are "determined by" their values at the nodes. The statements
  quantify over the coefficients of a general polynomial of the space. See
  `AtkinsonHan.Chapter10.equation_10_2_23`.
* **Theorem 10.3.1** (generalization). The identity holds for any shape functions; the nodal
  property $\hat\varphi_i(\hat x_j) = \delta_{ij}$ is not assumed. See
  `AtkinsonHan.Chapter10.theorem_10_3_1`.
* **Example 10.3.2** (generalization). The book takes a triangle in the plane. The statement holds
  for the barycentric coordinates of every simplex in $\mathbb{R}^d$. See
  `AtkinsonHan.Chapter10.example_10_3_2`.
* **Theorems 10.3.3 and 10.3.5 and Corollary 10.3.7** (generalization). The book takes a triangle
  and $k > 0$. The library takes a bounded connected open subset of $\mathbb{R}^d$ that is a Sobolev
  extension domain for every exponent, with $k + 1 > d/2$. See
  `AtkinsonHan.Chapter10.theorem_10_3_3`.
* **Theorem 10.3.4** (reading). The tensor operator-norm Sobolev seminorm yields constant $1$ in
  both bounds, in place of the unspecified constant for the book's multi-index seminorm.
* **Theorems 10.3.3, 10.3.5 and 10.3.9, Corollary 10.3.7 and Example 10.3.8** (reading). A function
  of $H^{k+1}$ is taken on its representative that is continuous up to the boundary, so that its
  values at the nodes are defined. See `AtkinsonHan.Chapter10.theorem_10_3_3`.
* **Theorem 10.3.5 and Definition 10.3.6** (reading). The book takes $\rho_K$ to be the diameter of
  the largest ball inscribed in $K$. The library uses the diameter of any inscribed closed ball. See
  `AtkinsonHan.Chapter10.IsRegularFamily`.
* **Equation (10.3.9)** (generalization). Mesh size uses a real supremum on arbitrary collections.
  On a nonempty finite mesh it agrees with the book's maximum.
* **Definition 10.3.6** (reading). The book indexes the family by $h \to 0$. The library indexes it
  by any type, with a filter along which the mesh parameter tends to $0$. See
  `AtkinsonHan.Chapter10.IsRegularFamily`.
* **Corollary 10.3.7, Example 10.3.8 and Theorem 10.3.9** (reading). The book leaves implicit a
  bound $h_K \le H$ on the diameters of the elements, on which its constant depends. The library
  makes it a hypothesis. See `AtkinsonHan.Chapter10.corollary_10_3_7`.
* **Example 10.3.8** (generalization). The estimate (10.3.11) is also proved for $m = 2$ and for
  the bilinear element on affine images of the reference square.
* **Theorem 10.3.9** (restriction). The statement uses plane triangulations and $C^1$ shape
  functions on the reference triangle. Conformity on each triangulation supplies the book's
  standing continuity assumption $X_h \subseteq C(\overline\Omega)$.
* **Theorem 10.4.1** (reading). The constant depends on an upper bound $H$ on the mesh parameters,
  and $u \in H^{k+1}(\Omega)$ is taken on a representative that is continuous up to the boundary.
  See `AtkinsonHan.Chapter10.theorem_10_4_1`.
* **Theorem 10.4.1** (generalization). The spaces $V_h$ are any subspaces of $V$ that contain the
  interpolant $\Pi_h u$. See `AtkinsonHan.Chapter10.theorem_10_4_1`.
* **Theorem 10.4.1, convergence** (reading). The density of smooth functions in $V$, which the
  argument of the book uses, is a hypothesis. See `AtkinsonHan.Chapter10.theorem_10_4_1_tendsto`.
* **Example 10.4.2** (reading). The regularity $u \in H^{k+1}(\Omega)$ is taken on a representative
  that is continuous up to the boundary and vanishes on $\Gamma$, the domain lies in a ball
  $B(0, R)$, and $\partial\Omega$ is a union of element edges. See
  `AtkinsonHan.Chapter10.example_10_4_2`.
* **Theorem 10.4.3** (generalization). The book takes $V \subseteq H^1(\Omega)$ and
  $H = L^2(\Omega)$. The library takes real inner product spaces $V$ and $H$ and a continuous linear
  map $\iota : V \to H$ in place of the embedding. See `AtkinsonHan.Chapter10.theorem_10_4_3`.
* **Exercise 10.4.5** (reading). The book writes operator identities. The library states them at one
  point, for a $C^2$ function, with the coordinate derivatives as derivatives along the coordinate
  curves. See `AtkinsonHan.Chapter10.exercise_10_4_5_polar`.

**Chapter 11, Elliptic Variational Inequalities and Their Numerical Approximations.**

* **Example 11.1.1** (reading). The condition $\psi \le 0$ on $\Gamma$ is the hypothesis that
  $\max\{\psi, 0\}$ is an element of $H_0^1(\Omega)$, which is how the book uses it. The same
  reading is used in Examples 11.2.3 and 11.3.10 and Theorem 11.3.12. See
  `AtkinsonHan.Chapter11.obstacleSet_nonempty`, `AtkinsonHan.Chapter11.example_11_2_3` and
  `AtkinsonHan.Chapter11.example_11_3_10`.
* **Example 11.1.1** (generalization). The book assumes a Lipschitz boundary. The obstacle problem
  is stated on every bounded open set. See `AtkinsonHan.Chapter11.example_11_1_1`.
* **(11.1.9)** (generalization). The regularity (11.1.8) is stated on representatives of $f$, $\psi$
  and $u$ in $\Omega$, and the condition $u \in C(\overline\Omega)$ of the book is not needed. See
  `AtkinsonHan.Chapter11.example_11_1_1_pointwise`.
* **(11.1.13)** (correction). The load integral over $\Omega$ uses volume measure, printed as $ds$
  in the book. The interior identity (11.1.14) holds almost everywhere for the $L^2$ load.
* **Exercise 11.2.1** (reading). The real-valued continuous real-linear load is represented by
  the real part of a complex continuous linear functional.
* **Lemma 11.3.5 and Theorem 11.3.7** (restriction). The book allows proper extended-real convex
  functionals. The library uses real-valued functionals on the designated admissible set.
* **Example 11.1.2, Example 11.2.4, Example 11.3.11 and Theorem 11.4.5** (reading). The Lipschitz
  domain of the book is a domain with a boundary trace in the sense of `BoundaryData.TraceFamily`,
  for example a bounded $C^1$ domain or a polygon without slits. See
  `AtkinsonHan.Chapter11.example_11_1_2`, `AtkinsonHan.Chapter11.example_11_2_4`,
  `AtkinsonHan.Chapter11.example_11_3_11` and `AtkinsonHan.Chapter11.theorem_11_4_5`.
* **(11.1.14)–(11.1.15)** (reading). The domain is a bounded $C^1$ domain, and a smooth solution has
  a representative in $C^2(\overline\Omega)$ whose gradient extends continuously to
  $\overline\Omega$. The boundary conditions hold at every point of $\Gamma$, where the book has the
  points at which the normal is defined. See `AtkinsonHan.Chapter11.example_11_1_2_pointwise`.
* **Lemma 11.3.8** (generalization). The book assumes that $A$ is continuous on the
  finite-dimensional subspaces of $V$. The library assumes only that $A$ is right-continuous along
  the segments of $K$ that start at $u$. See `AtkinsonHan.Chapter11.lemma_11_3_8`.
* **The projection argument after Example 11.3.11** (correction). The test vector in
  $a(w-u,v-u) \le 0$ ranges over $K$. The printed formula quantifies over $V$.
* **Theorems 11.4.1 and 11.4.6** (restriction). The weak-limit hypotheses include constant
  reindexings. These force $K_n \subseteq K$ and $j \le j_n$ on $V_n$, respectively, for every $n$.
* **Theorems 11.4.2 and 11.4.7** (reading). The square-root bounds make the constant
  $c = \max\{M/c_0, \sqrt{2/c_0}\}$ explicit. Theorem 11.4.7 takes any discrete admissible set
  in place of the book's subspace. The squared estimate (11.4.7) retains the printed form.
* **Exercise 11.4.3** (generalization). The regularization estimate uses a strongly monotone
  operator in place of the elliptic bilinear form and assumes the uniform functional error bound.
* **Exercise 11.4.2** (correction). The book asks only that the union of the subspaces $V_h$ be
  dense. This does not give a point of every $V_h$ near $u$, so the library also asks that the $V_h$
  be nested. See `AtkinsonHan.Chapter11.exercise_11_4_2`.
* **Example 11.4.3** (reading). The regularity $u, \psi \in H^2(\Omega)$, the boundary conditions
  $u = 0$ and $\psi \le 0$ on $\Gamma$, and $-\Delta u \in L^2(\Omega)$ are hypotheses on
  representatives continuous on $\overline\Omega$, and the polygon is a triangulated domain whose
  boundary is a union of element edges. See `AtkinsonHan.Chapter11.example_11_4_3`.
* **Example 11.4.4** (reading). The regularity of $u$ is stated through explicit representatives,
  the polygon by the condition that every boundary edge lies on one of finitely many sides, and
  $\|\partial u/\partial\nu\|_{L^2(\Gamma)}$ and $\sqrt{\operatorname{meas} \Gamma}$ are assumed
  bounded uniformly in $h$. See `AtkinsonHan.Chapter11.example_11_4_4`.
* **Theorem 11.4.6** (reading). The condition $\liminf_h j_h(v_h) \ge j(v)$ is stated as: for every
  $\alpha < j(v)$, eventually $j_h(v_h) > \alpha$. See `AtkinsonHan.Chapter11.theorem_11_4_6`.
* **Theorem 11.4.6** (generalization). The finite dimension of the spaces $V_h$ and the convexity
  and lower semicontinuity of the $j_h$, which only make the discrete problems solvable, are not
  assumed; the discrete solutions are given. See `AtkinsonHan.Chapter11.theorem_11_4_6`.

**Chapter 12, Numerical Solution of Fredholm Integral Equations of the Second Kind.**

* **Theorem 12.1.2 and (12.1.17)–(12.1.24)** (generalization). The book states the results for a
  sequence of projections $P_n$ onto finite-dimensional subspaces. The library states them for a
  single bounded idempotent $P$, with no finite dimension, and uses a sequence only where a limit is
  taken. See `AtkinsonHan.Chapter12.theorem_12_1_2`.
* **(12.1.24)** (reading). The book divides by $\|\lambda - P K\|$. The library states the lower
  bound in product form, so that no quotient by a norm that can vanish occurs. See
  `AtkinsonHan.Chapter12.equation_12_1_24`.
* **Lemmas 12.1.3 and 12.1.4** (generalization). In the compact-set convergence lemma only the
  domain needs to be complete. In the operator norm lemma the approximating maps need only
  converge pointwise to the identity.
* **(12.2.5) and (12.2.19)** (generalization). The book uses the uniform mesh $h = (b - a)/n$. The
  statements hold for every sequence of partitions whose mesh tends to zero. See
  `AtkinsonHan.Chapter12.equation_12_2_5` and `AtkinsonHan.Chapter12.equation_12_2_19`.
* **(12.2.24) and (12.2.25)** (reading). The periodic estimates use an orthonormal real Fourier
  system. The first gives the full Sobolev norm bound with constant $1$, and the second assumes
  compactness of the operator directly.
* **Lemma 12.3.1** (generalization). The book states the lemma on a Banach space. The statement
  holds on every normed space. See `AtkinsonHan.Chapter12.lemma_12_3_1`.
* **(12.3.11)** (generalization). The book derives the bound for an orthogonal projection on a
  Hilbert space. The statement holds for every bounded idempotent operator on a normed space. See
  `AtkinsonHan.Chapter12.equation_12_3_11`.
* **(12.3.31) and Theorem 12.3.3** (generalization). The book assumes that the kernel is
  continuously differentiable in $y$. The statements assume only that it is Lipschitz in $y$. See
  `AtkinsonHan.Chapter12.norm_kernelCLM_sub_quadInterpCLM_le` and
  `AtkinsonHan.Chapter12.theorem_12_3_3`.
* **The domain $D$ of §12.4** (generalization). The book takes a closed bounded set
  $D \subseteq \mathbb{R}^m$ with Lebesgue measure. The statements hold on every compact space with
  a finite Borel measure. See `AtkinsonHan.Chapter12.theorem_12_4_4`.
* **Theorem 12.4.4** (generalization). The book states the convergence for the Nyström operators on
  $C(D)$. The statement holds for every family that satisfies the conditions A1–A3. See
  `AtkinsonHan.Chapter12.exists_norm_inverse_le_of_isCollectivelyCompactFamily`.
* **Lemma 12.4.7(3)** (generalization). The compact operator $M$ may have any normed space as its
  domain. See `AtkinsonHan.Chapter12.lemma_12_4_7_c`.
* **(12.4.39), (12.4.44) and Example 12.4.6** (reading). The fourth-order remainder constants use
  derivative bounds. The last clause of Example 12.4.6 assumes the second-order auxiliary
  defect explicitly and uses the discrete auxiliary inverse.
* **Theorem 12.5.1** (generalization). The book takes piecewise polynomial interpolation on
  $[a, b]$. The statement holds for every uniformly bounded sequence of operators that converges
  pointwise to the identity, on every compact metric space with a Borel measure. See
  `AtkinsonHan.Chapter12.theorem_12_5_1`.
* **Example 12.5.2 and Lemma 12.5.5** (reading). The product trapezoidal estimate allows
  nonuniform meshes. The graded-mesh estimates require panel endpoints as interpolation nodes,
  and Lemma 12.5.5 gives the uniform estimate (12.5.35).
* **(12.6.20)–(12.6.22) and (12.6.27)** (generalization). The two-grid formulas use arbitrary
  bounded operators and a specified coarse inverse.
* **Theorem 12.5.6** (reading). The book applies Theorem 12.5.4 to obtain the regularity of the
  solution. The statement assumes the regularity that the proof uses. See
  `AtkinsonHan.Chapter12.theorem_12_5_6`.
* **Theorem 12.6.1** (generalization). The book states the theorem for the Nyström operators of
  §12.4. The statement holds for every collectively compact family that converges pointwise. See
  `AtkinsonHan.Chapter12.theorem_12_6_1`.
* **Example 12.6.2** (reading). The eigenfunction formulas are pointwise integral identities.
  The sine formula includes the zero function at frequency zero.
* **Lemma 12.7.1** (generalization). The book asks that $T$ be twice continuously differentiable on
  an open set and works on a closed bounded convex set. The lemma assumes only derivatives at the
  points of a convex set and a bound on the second derivative there. See
  `AtkinsonHan.Chapter12.lemma_12_7_1`.
* **Exercise 12.7.3 and (12.7.13)** (generalization). The differentiability hypotheses are made only
  on a closed ball about $u^*$, with a bound on $T''$ there. See
  `AtkinsonHan.Chapter12.exercise_12_7_3`.

**Chapter 13, Boundary Integral Equations.**

* **Theorem 13.1.1, the Neumann clause** (reading). The book states the classical Neumann problem
  for continuous data on a $C^2$ boundary curve. The library states the weak Neumann problem with
  data in $L^2(\sigma)$ on a bounded connected $C^1$ domain of $\mathbb{R}^{d+1}$, using outward
  normal data in place of the book's inward normal data. See
  `AtkinsonHan.Chapter13.theorem_13_1_1_neumann_weak`.
* **The remark after (13.1.34)** (correction). The display gives minus one-half the signed
  curvature times the parametrization speed. The library follows the display.
* **Theorem 13.1.2** (restriction). The divergence identity covers bounded $C^1$ domains and
  triangulated polygons. The book includes general piecewise smooth noncuspidal curves.
* **(13.1.13)** (partial translation). The Kelvin theorem gives preservation of harmonicity.
  The book also computes the factor relating the two Laplacians.
* **(13.2.4)–(13.2.7)** (generalization). The book states the error analysis for the double layer
  kernel. The theorems hold for every continuous kernel on the torus. See
  `AtkinsonHan.Chapter13.equation_13_2_7`.
* **(13.3.9)–(13.3.14)** (generalization). The book takes $C = A^{-1} B$ and derives its properties
  from the Sobolev theory. The theorem holds for every compact operator $C$ on $L^2(0, 2\pi)$ with
  $I + C$ invertible. See `AtkinsonHan.Chapter13.equation_13_3_14`.

**Chapter 14, Multivariable Polynomial Approximations.**

* **Exercise 14.1.1** (partial translation). The library proves the affine polynomial-space
  identities, including the general-dimensional ellipsoid change of variables. The book also
  asks for the approximation rates on the planar ellipse.
* **The measure of §14.2** (generalization). The book works with the volume of $\mathbb{B}_d$ and
  with the weight of (14.2.11). The results hold for every measure that satisfies
  `Approximation.IsMvWeight`. See `AtkinsonHan.Chapter14.isMvWeight_ballVolume`.
* **Theorem 14.2.3** (reading). The book asserts that the matrices $A_{n,j}$, $B_{n,j}$, $C_{n,j}$
  of the recursion are unique. The theorem states that $x_j \varphi$ lies in $\mathcal{V}_{n-1}^d +
  \mathcal{V}_n^d + \mathcal{V}_{n+1}^d$ and that the three components are unique. See
  `AtkinsonHan.Chapter14.theorem_14_2_3`.
* **Exercise 14.2.1** (partial translation). The library proves the inner-product identity for
  coordinate multiplication. The book asks for the resulting three matrix formulas.
* **(14.2.13)** (generalization). The book states the bound on $C(\mathbb{B}_d)$. It holds on $C(D)$
  for every compact $D \subseteq \mathbb{R}^d$. See `AtkinsonHan.Chapter14.equation_14_2_13`.
* **(14.3.1)** (correction). The book states that the rule is exact on $\Pi_{2n+1}^2$. It is exact
  on $\Pi_{2n}^2$ only; for $n = 1$ it does not integrate $x^3$ exactly. See
  `AtkinsonHan.Chapter14.equation_14_3_1`.
* **(14.3.3)–(14.3.5)** (generalization). The book uses its rule (14.3.1) on the disk. The results
  hold for every quadrature rule that is exact on $\Pi_{2n}^d$, for every weight measure on
  $\mathbb{R}^d$. See `AtkinsonHan.Chapter14.equation_14_3_3`.
* **(14.4.8) and Lemma 14.4.1** (generalization). The trial space and Laplacian bijection are
  formalized in every positive dimension. The codomain is $\Pi_n^d$, where the book prints
  $\Pi_n^2$. The theorem for Example 14.4.2 states the spanning part of the basis assertion.

## Not formalized

**Chapter 1, Linear Spaces.**

* **The exercises of §1.1.**
* **Parts of Example 1.1.2.** The complex coordinate space, continuous extension to the closure,
  boundedness on compact domains, and differentiable periodic spaces are outside the scope of the
  statement.
* **The bases in Example 1.1.12.** Lean states the dimension counts for both spaces.
* **Example 1.2.5(b), the norm $\max_{j \le k} \|f^{(j)}\|_\infty$ of $C^k[a, b]$.** The backbone
  uses the equivalent norm $\sum_{j \le k} \|f^{(j)}\|_\infty$; the bound between the two norms is
  part of `AtkinsonHan.Chapter01.example_1_2_28_a`.
* **Example 1.2.19.** The compactly supported smooth density clause is covered by
  `AtkinsonHan.Chapter01.theorem_1_5_6_open`. The example also states polynomial density.
* **The closing remark of Example 1.2.28(b)**, on the continuity of the derivatives of
  $f \in W^{m,p}(a, b)$. It is an embedding of the backbone and is not restated.
* **Example 1.3.15**, the convergence in $L^2$ of the real Fourier series. It is in the backbone and
  is not restated.
* **The identity after Definition 1.3.8** for $n$ mutually orthogonal elements. Only the case
  $n = 2$ is stated.
* **Theorem 1.3.11(d).** The convergence criterion for a general orthonormal series is outside the
  surface theorem's three-part statement.
* **Section 1.4**, spaces of continuously differentiable functions and Hölder spaces. It has no
  numbered result except Exercises 1.4.1–1.4.13, and its vocabulary is Mathlib's `ContDiff`,
  `HasCompactSupport`, `HolderWith` and `HolderOnWith`, which §3.7 and Theorem 1.5.6 use.
* **The Clarkson inequalities (1.5.5)–(1.5.6).** The book states them without proof; they are not in
  Mathlib, and nothing else uses them.
* **The converse half of Theorem 1.6.3**, that a precompact subset of $C(D)$ is uniformly bounded
  and equicontinuous. Mathlib has no form of it to specialize; only the direction that the book uses
  is proved.

**Chapter 2, Linear Operators on Normed Spaces.**

* **Parts of §2.1.** The inverse into the range for an arbitrary injection and continuity on a
  partial domain are outside the surface statements.
* **The bounded half of Example 2.1.7.** It is the backbone's `ContDiffMapIcc.derivCLM` and is not
  restated.
* **Exercises 2.2.1, 2.2.2, 2.2.6, 2.2.7 and 2.2.8.** Exercise 2.2.6 is not used later, and the
  others are one-line consequences of linearity.
* **The second half of Example 2.3.6**: the inverse (2.3.20), the bound on $\|L^{-1}\|$ and the
  condition (2.3.21). The book leaves this analysis to the reader as Exercise 2.3.5 and gives the
  constants to two decimals only.
* **Example 2.5.3, the further properties of $\hat\ell_c$**, which the book states without proof.
* **Example 2.5.9, the boundary value problem** whose generalized solution the book identifies with
  the representer.
* **Example 2.7.3**, the uniform integrability criterion of Dunford and Pettis, and **Exercise
  2.7.4(b)**, the uniform convexity of $L^p$.
* **Example 2.8.5 with integrable $\gamma_i$.** The continuous-kernel operator does not admit such
  kernels, so the example is stated for continuous $\gamma_i$.
* **Example 2.8.9, the truncation error,** and **Theorem 2.8.12(6), extension of (1)–(5) to compact
  powers.** Lean states compactness of the singular operator and the power-compact Fredholm
  alternative, respectively.
* **Theorem 2.8.15, the general enumeration (2.8.31).** Only the case of an injective $K$ on an
  infinite-dimensional space is stated.
* **Example 2.8.16**, the single-layer operator on the unit sphere. Mathlib has no surface measure
  on the sphere, no spherical harmonics as a Hilbert basis of $L^2$ of the sphere, and no Funk–Hecke
  formula.
* **The classification of the spectrum** into point, continuous and residual spectrum, a definition
  with no theorem attached to it.
* **Theorems 2.9.3 and 2.9.4**, the Riesz–Dunford functional calculus and the Riesz spectral
  projection. The book gives no proofs, and both need contour integrals of operator-valued
  functions, which Mathlib does not have.

**Chapter 3, Approximation Theory.**

* **The estimates (3.2.10)–(3.2.12)** for piecewise linear interpolation in $H^2(a, b)$. They need
  Sobolev spaces.
* **The Newton form of the interpolant**, which the book only cites.
* **Table 3.1** of Example 3.2.5. Its entries need verified numerics.
* **Example 3.3.17 in $L^p(a, b)$.** Only the case of $C[a, b]$ is stated.
* **The Sobolev norm error estimates after (3.5.2) and (3.5.7).** They need the Sobolev spaces
  $H^s(-1, 1)$, and the book refers elsewhere for them.
* **(3.7.10)**, the asymptotics $L_n = (4/\pi^2) \log n + O(1)$, and with it **the last step of
  Example 3.7.4.** The backbone proves the two bounds
  $(4/\pi^2) \log n \le L_n \le 1 + \log(2n + 1)$, which is what the later arguments use.

**Chapter 4, Fourier Analysis and Wavelets.**

* **The Gibbs phenomenon beside Example 4.1.3**, with the constant $(2/\pi) \operatorname{Si}(\pi)$.
  The book asserts it without proof.
* **The $L^p$ boundedness (4.1.12) of the partial sum operators for $1 < p < \infty$.** It is the
  theorem of M. Riesz, which is not in Mathlib; for this reason Theorem 4.1.2 takes the operators as
  data.
* **(4.2.7) for $|\alpha| \ge 2$ and (4.2.8) for $d \ge 2$.**
* **The fast Fourier transform as an algorithm**, with its operation count $O(n \log n)$.
* **Five items of §4.5**: the existence half of the construction (4.5.1)–(4.5.3), which the book
  leaves to Daubechies; the orthonormality of the integer translates of the $D_4$ scaling function;
  the weaker form of axiom (1) with a stable basis; the property
  $f \in W_j \iff f(2^{-j} \cdot) \in W_0$; and the equality $\operatorname{supp} \psi = [-1, 2]$ in
  Exercise 4.5.6, of which only the inclusion is proved.

**Chapter 5, Nonlinear Equations and Their Solution by Iteration.**

* **The remark after Theorem 5.2.3** on the Volterra equation on $[a, \infty)$. The backbone
  Volterra operator is defined only on a compact interval.
* **The exercises of §5.3.**
* **Theorems 5.5.1 and 5.5.4**, the fixed-point theorems of Brouwer and Schauder, and **§5.5.1**,
  the rotation of a completely continuous vector field with its properties P1–P5. Mathlib has
  neither Brouwer's theorem nor degree theory.
* **(5.6.7)–(5.6.9) and Theorem 5.6.3(a) and (b).** The eigen-decomposition of $K$, the identity
  $\sum_j \lambda_j^2 = \|K\|_{HS}^2$ and the eigenvalue decay for a smooth kernel are hypotheses,
  because Mathlib has no decreasing enumeration of the eigenvalues of a compact self-adjoint
  operator, no Hilbert–Schmidt norm for these integral operators and no eigenvalue asymptotics.

**Chapter 6, Finite Difference Method.**

* **The grid and the side conditions of Example 6.1.1, and Figures 6.1 and 6.2.** They are data and
  computed errors, not claims.
* **Exercises 6.2.2 and 6.3.2** (the Crank–Nicolson scheme) and **Exercise 6.3.3** (the generalized
  midpoint scheme).

**Chapter 7, Sobolev Spaces.**

* **Lipschitz domains.** That a Lipschitz domain is an extension domain is the theorem of Stein or
  Calderón, which is not formalized, and the boundary charts of the library are $C^n$ graphs. For
  this reason Examples 7.2.7 and 7.2.8 are stated on triangulated plane domains.
* **Example 7.2.8, the continuity at the vertices.** It needs that the elements around each vertex
  are connected through shared edges, which the axioms of a triangulation do not give.
* **Definitions 7.2.10, 7.2.12 and 7.2.13, further facts**: the completeness, reflexivity and
  Hilbert structure of $W^{s,p}(\Omega)$; the embedding of $L^2(\Omega)$ in $H^{-1}(\Omega)$ and the
  representation of the elements of $H^{-1}(\Omega)$; patches of class $C^{k,\alpha}$ other than
  $C^1$; and the independence of the patch system.
* **Theorem 7.3.5 as printed**, the universal extension operator of Stein. The extension operator of
  the library changes with $k$.
* **Theorems 7.3.7(b), (c) and 7.3.8(b), (c) for $d + 1 = 1$ and $p = 1$.** The backbone's form of
  Corollary 9.15 of [brezis2011functional] excludes this case.
* **Theorem 7.3.10, the range clause**, and **Theorem 7.3.11 as printed.** They need boundary spaces
  of fractional order that do not depend on the atlas and the right inverse of Gagliardo; only the
  $L^p(\Gamma)$ clause of Theorem 7.3.11 at $s = 2$ on a $C^2$ domain is formalized.
* **(7.4.2) for $s < 0$, and Exercises 7.4.3 and 7.4.4.**
* **Items of §7.5**: the operator $\mathcal{D}$ of (7.5.3)–(7.5.5) as an operator; Proposition 7.5.4
  for $k > 0$; Example 7.5.3, which needs distributions on the circle; §7.5.4, the operator with the
  logarithmic kernel, whose symbol the book obtains without proof; and §7.5.5 apart from Definition
  7.5.8 and (7.5.30), that is, Definition 7.5.9, (7.5.20)–(7.5.29), Theorem 7.5.10 and
  (7.5.31)–(7.5.33), which need spherical harmonics and a surface measure on $S^2$.

**Chapter 8, Weak Formulations of Elliptic Boundary Value Problems.**

* **Section 8.1**, the model problem. It has no numbered result; its displays (8.1.1)–(8.1.4) are
  the weak form of the Dirichlet problem that Example 8.2.6 treats.
* **The weak formulations (8.4.1)–(8.4.22)** of the Dirichlet, Neumann, mixed and general
  second-order problems. They are stated with the trace $\gamma : H^1(\Omega) \to H^{1/2}(\Gamma)$;
  their abstract content is the Lax–Milgram lemma `AtkinsonHan.Chapter08.theorem_8_3_4`.
* **Theorem 8.5.1 in the mixed displacement–traction case, and Korn's second inequality.** The
  inequality needs the lemma of Lions, which needs a right inverse of the divergence; neither is in
  Mathlib or in the backbone.
* **The abstract mixed formulation (8.6.21)–(8.6.22)**, for which the book refers to Brezzi, and
  **the model computations (8.6.1)–(8.6.20) and Exercises 8.6.1–8.6.4.**

**Chapter 9, The Galerkin Method and Its Variants.**

* **Table 9.1**, numerical output.
* **Algorithm 2 of §9.4**, the nonlinear conjugate gradient method. The book quotes its convergence
  without proof.

**Chapter 10, Finite Element Analysis.**

* **The finite element systems (10.1.1)–(10.1.6) and (10.1.13)–(10.1.15), Exercise 10.1.1, and the
  dimension count of Exercise 10.1.3.**
* **The model Neumann problem (10.2.4)–(10.2.12)**, whose boundary term needs the trace, and
  **Exercise 10.2.5.**
* **Exercises 10.3.1, 10.3.2, 10.3.4 and 10.3.7, and the remark after Theorem 10.3.9**, which states
  no result.
* **Corollary 10.4.4 as stated, and (10.4.11).** The library does not have the regularity of the
  Dirichlet problem on a convex polygon. The abstract form is
  `AtkinsonHan.Chapter10.corollary_10_4_4_abstract`.
* **Exercises 10.4.1–10.4.4 and 10.4.6.** Each is posed on a specific domain.

**Chapter 11, Elliptic Variational Inequalities and Their Numerical Approximations.**

* **Theorem 11.3.12 in the generality of the book.** Only the case $p = 2$, $a_{ij} = \delta_{ij}$
  on a $C^2$ domain is formalized, as `AtkinsonHan.Chapter11.theorem_11_3_12_two`. The book quotes
  the theorem without proof, and the general case needs $L^p$ regularity theory for $p \neq 2$,
  general elliptic coefficients and $C^{1,1}$ boundaries.
* **The one-dimensional solution formula after Example 11.3.11, and Exercises 11.3.4–11.3.9, 11.3.11
  and 11.3.12.**
* **Exercise 11.4.4, the analysis of (11.4.29), and Exercises 11.4.1 and 11.4.5.**

**Chapter 12, Numerical Solution of Fredholm Integral Equations of the Second Kind.**

* **The linear systems (12.1.5) and (12.1.14) in coordinates, and §12.1.2**, the Galerkin method
  with $V = L^2(D)$. They are the framework at a concrete projection.
* **The numerical data of Examples 12.2.1, 12.3.2, 12.4.1, 12.5.3 and 12.6.2**: Tables 12.1–12.4 and
  Figure 12.1.
* **The concrete computations of §12.3.2**, the linear system for the iterated collocation solution
  and the dimension $d_n = 2n$ in Example 12.3.2.
* **The unconditional form of the last clause of Example 12.4.6.** The bound that it needs is a
  hypothesis.
* **Theorem 12.5.4**, the regularity of the solution of a weakly singular equation, which the book
  cites without proof, and **§12.5.2**, the kernels that are not of the form $l g$.
* **§12.6.3 and §12.6.4**, the linear systems and the operation count, and **the limit (12.6.48)**,
  which the book states without proof.
* **§12.7.2**, the homotopy argument, which needs degree theory, **§12.7.3**, the nonlinear systems,
  and **Exercises 12.7.4–12.7.7.**

**Chapter 13, Boundary Integral Equations.**

* **Planar potential theory**: Green's representation formula, the jump relations of the layer
  potentials, and the identification of the double layer operator with a boundary integral. With
  them go the classical clauses of Theorem 13.1.1, Theorem 13.1.2 on regions with corners, the
  exterior problems (13.1.14)–(13.1.23), and the evaluation of the potential near the boundary
  (13.2.14)–(13.2.23).
* **The spectral rate of the trapezoidal rule** used in §13.2. It needs the periodic Sobolev scale;
  only the convergence for every continuous integrand is used.
* **Exercise 13.2.5 and (13.2.20)**, that $\|K\| = \pi$ for a convex region. It needs a continuous
  argument along a plane curve and a turning number.
* **The bound (13.2.33)**, which the book quotes, **the numerical parts of Examples 13.2.1–13.2.3**,
  and **§13.2.2**, the exterior Neumann problem.
* **The solvability theory (13.3.2)–(13.3.7), the rate (13.3.15), and the commutation
  $P_n A = A P_n$.** The first two need the periodic Sobolev scale.

**Chapter 14, Multivariable Polynomial Approximations.**

* **Theorem 14.1.1**, the multivariate Jackson theorem of Ragozin, and the higher moduli of
  continuity with which it is stated. The book quotes it and does not prove it; the proof needs
  spherical harmonics, a surface measure on $S^d$ and a convolution on the sphere.
* **(14.2.8)–(14.2.9)**, the defining relations of the matrices $A_{n,j}$ and $B_{n,j}$ of Exercise
  14.2.1. The matrices are not written out.
* **(14.2.14)–(14.2.15), Theorems 14.2.4 and 14.2.5, and Exercise 14.2.4.** They need Jacobi
  polynomials, estimates of them, or the surface measure on $S^2$, and Theorem 14.2.5 also needs
  Theorems 14.1.1 and 14.2.4.
* **(14.3.6)–(14.3.7)**, the bound $\|L_n\| = O(n \log n)$. It needs the same estimates of Jacobi
  polynomials.
* **The Sobolev part of §14.4**: (14.4.1)–(14.4.7), (14.4.10)–(14.4.13), Exercises 14.4.2–14.4.3 and
  the numerical part of Example 14.4.2. They quantify over $H^1_0(\mathbb{B}_2)$; see
  `NumlibSurface.AtkinsonHan.Chapter14.Section04`.
-/
