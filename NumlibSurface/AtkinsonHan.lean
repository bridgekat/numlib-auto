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
import NumlibSurface.AtkinsonHan.Chapter08.Section02
import NumlibSurface.AtkinsonHan.Chapter08.Section03
import NumlibSurface.AtkinsonHan.Chapter08.Section06
import NumlibSurface.AtkinsonHan.Chapter08.Section07
import NumlibSurface.AtkinsonHan.Chapter09.Section01
import NumlibSurface.AtkinsonHan.Chapter09.Section02
import NumlibSurface.AtkinsonHan.Chapter09.Section03
import NumlibSurface.AtkinsonHan.Chapter09.Section04
import NumlibSurface.AtkinsonHan.Chapter10.Section04
import NumlibSurface.AtkinsonHan.Chapter11.Section02
import NumlibSurface.AtkinsonHan.Chapter11.Section03
import NumlibSurface.AtkinsonHan.Chapter11.Section04
import NumlibSurface.AtkinsonHan.Chapter12.Section01
import NumlibSurface.AtkinsonHan.Chapter12.Section03
import NumlibSurface.AtkinsonHan.Chapter12.Section04
import NumlibSurface.AtkinsonHan.Chapter12.Section06
import NumlibSurface.AtkinsonHan.Chapter12.Section07

/-!
# Atkinson–Han, *Theoretical Numerical Analysis*

The surface library for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A
Functional Analysis Framework* (3rd ed., Springer, 2009): fifty-one modules, one per section of
the book that the project covers, grouped by chapter. Each states the book's results in the book's
own terms and proves them by specializing the backbone under `Numlib/`. Almost nothing is proved
here that is not proved there — the surface exists to test the backbone against a published account
of the subject, and to give a reader of the book a Lean name for every result formalized.

This module imports the fifty-one section modules and adds nothing of its own.

## Naming

A declaration is named for the result it states, so the name is the index: `theorem_8_3_4` is
Theorem 8.3.4, `corollary_2_5_7` is Corollary 2.5.7, `equation_2_3_16` is the numbered display
(2.3.16) and `exercise_9_3_1` is Exercise 9.3.1. Where one numbered result needs several
declarations — its separate clauses, the two directions of an equivalence, or the three vector
norms of Example 2.2.8 — a trailing word tells them apart, as in `proposition_3_6_9_b`,
`theorem_8_3_3_subspace` and `example_2_2_8_l1`. Book-specific definitions get descriptive names
instead (`IsBoundedOperator`, `IsSublinear`, `BilinForm`, `BookSplitting`, `HasGateauxDerivAt`,
`IsSaddlePoint`, `DualProblem`), each with a bridge lemma to the Mathlib or backbone notion it
agrees with. Declarations live in the per-chapter namespaces `AtkinsonHan.ChapterNN`, one per
chapter the surface covers — the chapter spelled in full, as the module path spells it — with the
bilinear-form vocabulary shared by §8.3, §8.7 and Chapters 9–10 directly in `AtkinsonHan`.

## The outline

| § | module | subject |
|---|---|---|
| **1** | | *Linear Spaces* |
| 1.1 | `Chapter01.Section01` | Linear spaces: bases and dimension |
| 1.2 | `Chapter01.Section02` | Normed spaces, equivalence of norms, completion; Fubini |
| 1.3 | `Chapter01.Section03` | Inner product spaces, Cauchy–Schwarz and the parallelogram law |
| 1.5 | `Chapter01.Section05` | `Lᵖ`: Young, Hölder, Minkowski, completeness, inclusions |
| 1.6 | `Chapter01.Section06` | Compact sets: Heine–Borel with Riesz's converse, and Arzelà–Ascoli |
| **2** | | *Linear Operators on Normed Spaces* |
| 2.1 | `Chapter02.Section01` | Operators; boundedness as "bounded sets have bounded images" |
| 2.2 | `Chapter02.Section02` | Continuity ⇔ boundedness; the operator norm; `𝓛(V, W)` |
| 2.3 | `Chapter02.Section03` | Geometric series, perturbation, consistency and stability |
| 2.4 | `Chapter02.Section04` | Extension, bounded inverse, conditioning, uniform boundedness |
| 2.5 | `Chapter02.Section05` | Linear functionals, Hahn–Banach, Riesz representation |
| 2.6 | `Chapter02.Section06` | Adjoint operators and the norm of a self-adjoint operator |
| 2.7 | `Chapter02.Section07` | Weak convergence, and where it agrees with norm convergence |
| 2.8 | `Chapter02.Section08` | Compact operators, their spectrum and the Fredholm alternative |
| 2.9 | `Chapter02.Section09` | The resolvent operator: perturbation bound and Neumann expansion |
| **3** | | *Approximation Theory* |
| 3.1 | `Chapter03.Section01` | The Weierstrass approximation theorems |
| 3.2 | `Chapter03.Section02` | Interpolation: Lagrange, Hermite, piecewise linear, trigonometric |
| 3.3 | `Chapter03.Section03` | Best approximation: existence, uniqueness, strict convexity |
| 3.4 | `Chapter03.Section04` | Best approximation in inner product spaces; projections |
| 3.5 | `Chapter03.Section05` | The classical orthogonal polynomial families |
| 3.6 | `Chapter03.Section06` | Projection operators and direct sums |
| 3.7 | `Chapter03.Section07` | Uniform error bounds: the Lebesgue lemma and non-convergence |
| **4** | | *Fourier Analysis and Wavelets* |
| 4.1 | `Chapter04.Section01` | Fourier series on the circle, the coefficients, Parseval |
| 4.2 | `Chapter04.Section02` | The Fourier transform, its normalization, and Plancherel |
| 4.3 | `Chapter04.Section03` | The discrete Fourier transform and the matrix `F_n` |
| 4.4 | `Chapter04.Section04` | Haar wavelets: the scaling function and the wavelet spaces |
| 4.5 | `Chapter04.Section05` | Multiresolution analysis, with Haar as its instance |
| **5** | | *Nonlinear Equations and Their Solution by Iteration* |
| 5.1 | `Chapter05.Section01` | The Banach fixed-point theorem; strongly monotone operators |
| 5.2 | `Chapter05.Section02` | Iterative methods: the scalar case and matrix splittings |
| 5.3 | `Chapter05.Section03` | Differential calculus for nonlinear operators; convex functionals |
| 5.4 | `Chapter05.Section04` | Newton's method, Newton–Kantorovich, and the chord method |
| 5.5 | `Chapter05.Section05` | Completely continuous vector fields, as far as Mathlib allows |
| 5.6 | `Chapter05.Section06` | Conjugate gradients for operator equations, with Winther's theorem |
| **6** | | *Finite Difference Method* |
| 6.1 | `Chapter06.Section01` | The four difference quotients and their orders (6.1.1)–(6.1.4) |
| 6.2 | `Chapter06.Section02` | The Lax equivalence theorem for `u' = L u`, `L` a `LinearPMap` |
| 6.3 | `Chapter06.Section03` | Two-level schemes: consistency, stability and convergence |
| **8** | | *Weak Formulations of Elliptic Boundary Value Problems* |
| 8.2 | `Chapter08.Section02` | Existence and uniqueness for operator equations |
| 8.3 | `Chapter08.Section03` | Bilinear forms and the Lax–Milgram lemma |
| 8.6 | `Chapter08.Section06` | Saddle points, the primal and dual problems, the minimax equality |
| 8.7 | `Chapter08.Section07` | The generalized (Nečas) Lax–Milgram lemma |
| **9** | | *The Galerkin Method and Its Variants* |
| 9.1 | `Chapter09.Section01` | The Galerkin method, the Ritz formulation, Céa's inequality |
| 9.2 | `Chapter09.Section02` | The Petrov–Galerkin method, Babuška and Xu–Zikatanov |
| 9.3 | `Chapter09.Section03` | The generalized Galerkin method and Strang's first lemma |
| 9.4 | `Chapter09.Section04` | The conjugate gradient method in variational form |
| **10** | | *Finite Element Analysis* |
| 10.4 | `Chapter10.Section04` | The Aubin–Nitsche lemma |
| **11** | | *Elliptic Variational Inequalities and Their Numerical Approximations* |
| 11.2 | `Chapter11.Section02` | Convex minimization and the inequality equivalent to it |
| 11.3 | `Chapter11.Section03` | Existence, uniqueness and stability for elliptic inequalities |
| 11.4 | `Chapter11.Section04` | The discrete inequality and Falk's error estimate |
| **12** | | *Numerical Solution of Fredholm Integral Equations of the Second Kind* |
| 12.1 | `Chapter12.Section01` | Projection methods for `(μ − K) u = f`: stability and convergence |
| 12.3 | `Chapter12.Section03` | Iterated projection methods and Sloan's superconvergence |
| 12.4 | `Chapter12.Section04` | The Nyström method and collectively compact approximation |
| 12.6 | `Chapter12.Section06` | Two-grid iteration for the discretized equations |
| 12.7 | `Chapter12.Section07` | Projection methods for nonlinear equations |

A section module imports the section modules it builds on, so the import graph runs forwards
through the book: §2.2 on §2.1, §3.3 on §2.4, §4.5 on §4.4, §5.4 on §5.3, §6.3 on §6.2, §9.1 on
§8.3, §9.4 on §5.6 and §9.1, §10.4 on §9.1, §11.4 on §11.3, and §§12.3–12.7 on §12.1. Two
sections reach backwards for a definition rather than restate it: §2.7 takes weak convergence
from §3.3, which needed it first for Example 3.3.5, and §11.3 takes strong monotonicity from
§5.1.

## Ambient conventions

* **Scalars.** The book's `𝕂 ∈ {ℝ, ℂ}` is `[RCLike 𝕜]`. Where the book itself restricts to the
  reals — all of §3.4, Definition 2.5.4 and Theorem 2.5.5, Definition 3.3.6 and Theorem 3.3.7,
  strictly normed spaces, and the whole of Chapters 8, 9 and 10 — the statements are over `ℝ`. A
  statement that mixes a `𝕜`-subspace with a real-convex set carries `[NormedSpace ℝ V]` and
  `[IsScalarTower ℝ 𝕜 V]`, because `Convex ℝ K` does not elaborate under a bare
  `[NormedSpace 𝕜 V]`.
* **Inner products.** The book's `(u, v)` is linear in its *first* argument and Mathlib's
  `⟪u, v⟫` in its second, so the book's `(v, u)` is written `inner 𝕜 u v` throughout. The swap is
  invisible in the real symmetric case, and is why several §2.5, §2.6 and §3.4 statements read
  with their arguments reversed.
* **Operators and duals.** `𝓛(V, W)` is `V →L[𝕜] W` and `V'` is `StrongDual 𝕜 V`. The book's
  "`L` is a bijection of `V` onto `W` whose inverse is bounded" is `∃ e : V ≃L[𝕜] W, ↑e = L`,
  bridged to the ring-theoretic `IsUnit` the backbone uses by
  `isUnit_iff_exists_continuousLinearEquiv`. `Vᗮ` is `Submodule.orthogonal`.
* **Bilinear forms.** The data of §8.3 and Chapters 9–10 is a `BilinForm V` (`V →ₗ[ℝ] V →ₗ[ℝ] ℝ`)
  with unbundled predicates `IsBoundedWith M`, `IsEllipticWith α` and `LinearMap.BilinForm.IsSymm`.
  Bundled by `BilinForm.toCLM`, such a form *is* the backbone's `SesqForm ℝ V`, so the
  `Numlib.Variational` API applies to it with no conversion function; only the
  `RCLike.re`/`starRingEnd` decorations have to be erased, which the backbone's real
  specializations do.
* **Suprema and infima.** `sSup` and `sInf` take junk values on unbounded or empty sets, so every
  statement the book writes with a `sup` or an `inf` either carries the boundedness hypothesis
  that makes it a real supremum (Proposition 8.6.2) or proves it (the supremum over the data in
  the Aubin–Nitsche lemma (10.4.5), bounded through the Lax–Milgram estimate on the dual
  solution).
* **Book-faithful hypotheses.** Where the book carries a hypothesis its own proof does not use,
  the hypothesis is kept and the doc comment says so — Theorem 3.3.13's convexity, the vector
  space structure in the metric half of §5.1, the completeness of `W` in Theorem 5.4.2, and the
  Hilbert data of Theorem 9.3.1, which `theorem_9_3_1'` re-attaches to the abstract
  `theorem_9_3_1`. Such statements carry `set_option linter.unusedVariables false` or
  `linter.unusedSectionVars false` rather than being weakened.

## Where formalizing corrected the book

* **§3.4, the display (3.4.5).** The book states the norm of the orthogonal projection as
  `‖P_K‖ = 1`. That fails for `K = {0}`, where `P_K = 0`. `theorem_3_4_7` states the correct
  form: `‖P_K‖ ≤ 1`, with equality exactly when `K ≠ {0}`.
* **§5.4, Theorem 5.4.2.** The book puts the uniqueness half of the Newton–Kantorovich theorem on
  the *closed* ball of radius `t** = (1 + √(1 − 2h))/(aL)`. That is false whenever `h < ½`: the
  scalar majorant `p t = (L/2)t² − t/a + b/a` satisfies every hypothesis at `u₀ = 0` and has a
  second zero at distance exactly `t**`. `theorem_5_4_2_unique` states uniqueness on the open ball,
  which is what is true.
* **§8.2, Theorem 8.2.7.** The book states `R(L) = N(L*)ᗮ` for a densely defined closed operator
  between Banach spaces. That generality is out of reach — Mathlib has no continuous Banach dual
  of an unbounded densely defined operator — so the theorem is proved only in the bounded
  Hilbert-space case, as `theorem_8_2_7_hilbert`. Everything §8.2 uses downstream (Theorems 8.2.1
  and 8.2.4, closed range from the a priori estimate (8.2.2)) is proved in the book's own
  generality, for `LinearPMap` with `LinearPMap.IsClosed`.
* **§8.7 and §9.2, the inf–sup conditions.** The book writes (8.7.2) and (9.2.6) as suprema of
  `a(u, v)/‖v‖` *without* absolute values, and prints (8.7.3) as `sup_u a(u, v) > 0`. Read
  literally the latter says nothing, since the supremum of a nonzero linear functional is `+∞`;
  it is formalized as `∃ u, 0 < a(u, v)`. Both printed forms are then proved equivalent to the
  backbone's, by `iSup_div_eq_opNorm` (a sign-symmetry argument, `v ↦ -v`) and by
  `BilinForm₂.exists_pos_iff_exists_ne_zero`.
* **§9.2, Remark 9.2.2.** The Xu–Zikatanov bound `‖u − u_N‖ ≤ (M/α_N) inf_{w_N} ‖u − w_N‖` needs
  `U_N ≠ {0}`, which the remark does not say. On the trivial trial space the Petrov–Galerkin
  projector is `0`, every other hypothesis holds vacuously, and the bound fails; the sharpening is
  a statement about a nonzero projector.

## Not formalized, and why

Three bodies of material are missing for want of infrastructure rather than for difficulty, and
each section module names the results it leaves out.

* **Sobolev spaces.** §8.1, §8.4, §8.5 and §8.8 are the book's Sobolev-space theory and its
  application to elliptic boundary value problems; §8.6's model-problem computations
  (8.6.1)–(8.6.20) and Chapter 10 apart from the Aubin–Nitsche lemma are the same material.
  Neither is Example 2.4.2 (the derivative extended to `H¹`), nor Example 2.5.9, nor the concrete
  PDE instances of Chapter 9. What survives is the abstract skeleton — §8.2, §8.3, §8.6, §8.7,
  Chapter 9 and §10.4 — which is where the functional analysis lives; the missing part is the
  verification that a particular boundary value problem satisfies its hypotheses. The same
  boundary cuts Chapters 11 and 12 in two: their abstract spines are formalized — §11.2–11.4 on
  elliptic variational inequalities, §12.1, §12.3, §12.4, §12.6 and §12.7 on projection and
  collectively compact methods for Fredholm equations of the second kind — while their
  applications live in `H¹₀(Ω)` and on a concrete kernel, and are out of scope. So is Chapter 7,
  which is the Sobolev theory itself, and Chapter 13, which is boundary integral equations on a
  Sobolev space over a boundary.
* **Weak compactness in a reflexive space.** Theorems 3.3.8, 3.3.10, 3.3.11 (Mazur), 3.3.12 and
  3.3.14, on minimizers of weakly sequentially lower semicontinuous functionals over a reflexive
  Banach space, and Theorem 8.6.3 (Ekeland–Temam, the existence of a saddle point for a
  convex–concave functional) all rest on weak sequential compactness of the closed unit ball (the
  book's Theorem 2.7.5), which Mathlib does not have. `WeakSeqTendsto` and `example_3_3_5` record
  as much of the setting as can be stated without it; the finite-dimensional and Hilbert cases of
  the same material are proved in full. §2.7 itself is planned and not yet written for the same
  reason.
* **The `C[a, b]` integral-operator toolkit.** `Numlib/IntegralEquations/Basic` has the Fredholm,
  Urysohn and Volterra operators with their norms and Lipschitz constants, which is what §5.2's
  applications and the norm formula (2.2.8) need, and now their *compactness*
  (`IntegralOperator.isCompactOperator_fredholm`), which is what discharges the
  `IsCompactOperator` hypothesis of §12.1 and §12.4 on a concrete operator. What it does not yet
  have is differentiation under the integral sign, so Example 5.3.10 — the Fréchet derivative of
  the Urysohn operator is the Fredholm operator with kernel `∂_u k(t, s, u(s))` — is still open.
  Nor does it have a *weakly singular* kernel: the modulus
  `ω(h) = sup_{‖x−z‖ ≤ h} ∫ |k (x, y) − k (z, y)| dy` of Atkinson–Han §2.8.1 and the operator of a
  kernel that is merely integrable in `y`, without which Examples 2.8.2 and 2.8.9 cannot be
  stated. The concrete halves of Examples 2.3.2 and 2.3.4 are no longer blocked by anything; they
  are simply unwritten.
* **`L²` kernel operators.** Example 2.6.1 and §2.8.3 — a kernel with
  `B = (∫∫ |k|²)^{1/2} < ∞` gives a bounded operator on `L²(a, b)` with `‖K‖ ≤ B`, whose adjoint
  is the transposed kernel — are not stated. Mathlib has no Hilbert–Schmidt operators, and the
  backbone's kernel operator acts on `C(X, ℝ)` for a continuous kernel, a different object.

§1.4, spaces of continuously differentiable functions and Hölder spaces, has no module and needs
none: it contains no numbered result of any kind — the book's numbering there runs
`Exercise 1.4.1`–`1.4.13` and nothing else — and its vocabulary is reached through Mathlib's
`ContDiff`, `HasCompactSupport`, `HolderWith` and `HolderOnWith` where §3.7 and Theorem 1.5.6 need
it. The one thing the section asserts that the library cannot say is that `Cᵐ[a, b]` and
`C^{m,β}[a, b]` are Banach spaces, which is Example 1.2.28 (a) and is blocked on `Cᵐ[a, b]` as a
normed space; Mathlib has `C(X, ℝ)` for compact `X`, hence the case `m = 0` only.

Smaller omissions all have the same shape — an object the backbone or Mathlib has not built yet —
and each is listed in the module it belongs to: trigonometric and interpolatory approximation
(§3.7 almost in its entirety, including Jackson's theorems and the Fourier projections, and
Examples 3.6.5, 3.6.6 and 3.6.8), weighted `L²` spaces and orthogonal polynomials (Examples 3.4.8
and 3.4.9), numerical quadrature (§2.4.4) and Chebyshev equioscillation (Theorems 3.3.19–3.3.20).
§5.5, on completely continuous vector fields, is quoted by the book without proof — Brouwer's and
Schauder's theorems and the rotation properties P1–P5 — and is summarized in `Chapter05.Section03`
rather than formalized.

Two results of §3.3 are open — Theorems 3.3.19 and 3.3.20, Chebyshev equioscillation — and most
of §3.7 is open for a different reason: the trigonometric-approximation layer that Jackson's
theorems and the Fourier projections speak about is not yet in Mathlib or in `Numlib`, and §3.7's
module lists exactly what is waiting on it. Of §3.2 everything is formalized except the `H²(a, b)`
estimates (3.2.10)–(3.2.12) for piecewise linear interpolation, which need Sobolev spaces and are
out of scope with the rest of that material.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/
