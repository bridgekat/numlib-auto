import NumlibSurface.AtkinsonHan.Chapter02.Section03
import NumlibSurface.AtkinsonHan.Chapter02.Section04
import NumlibSurface.AtkinsonHan.Chapter02.Section05
import NumlibSurface.AtkinsonHan.Chapter03.Section03
import NumlibSurface.AtkinsonHan.Chapter03.Section04
import NumlibSurface.AtkinsonHan.Chapter03.Section06
import NumlibSurface.AtkinsonHan.Chapter03.Section07
import NumlibSurface.AtkinsonHan.Chapter05.Section01
import NumlibSurface.AtkinsonHan.Chapter05.Section02
import NumlibSurface.AtkinsonHan.Chapter05.Section03
import NumlibSurface.AtkinsonHan.Chapter05.Section04
import NumlibSurface.AtkinsonHan.Chapter05.Section06
import NumlibSurface.AtkinsonHan.Chapter08.Section02
import NumlibSurface.AtkinsonHan.Chapter08.Section03
import NumlibSurface.AtkinsonHan.Chapter08.Section07
import NumlibSurface.AtkinsonHan.Chapter09.Section01
import NumlibSurface.AtkinsonHan.Chapter09.Section02
import NumlibSurface.AtkinsonHan.Chapter09.Section03
import NumlibSurface.AtkinsonHan.Chapter09.Section04

/-!
# Atkinson–Han, *Theoretical Numerical Analysis*

The surface library for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A
Functional Analysis Framework* (3rd ed., Springer, 2009): nineteen modules, one per section of the
book that the project covers, grouped by chapter. Each states the book's results in the book's own
terms and proves them by specializing the backbone under `Numlib/`. Almost nothing is proved here
that is not proved there — the surface exists to test the backbone against a published account of
the subject, and to give a reader of the book a Lean name for every result formalized.

This module imports the nineteen section modules and adds nothing of its own.

## Naming

A declaration is named for the result it states, so the name is the index: `theorem_8_3_4` is
Theorem 8.3.4, `corollary_2_5_7` is Corollary 2.5.7, `equation_2_3_16` is the numbered display
(2.3.16) and `exercise_9_3_1` is Exercise 9.3.1. Where one numbered result needs several
declarations — its separate clauses, or the two directions of an equivalence — a trailing word
tells them apart, as in `proposition_3_6_9_b` and `theorem_8_3_3_subspace`. Book-specific
definitions get descriptive names instead (`IsSublinear`, `BilinForm`, `BookSplitting`,
`HasGateauxDerivAt`), each with a bridge lemma to the Mathlib or backbone notion it agrees with.
Declarations live in the flat per-chapter namespaces `AtkinsonHan.Ch02`, `AtkinsonHan.Ch03`,
`AtkinsonHan.Ch05`, `AtkinsonHan.Ch08` and `AtkinsonHan.Ch09`, with the bilinear-form vocabulary
shared by §8.3, §8.7 and Chapter 9 directly in `AtkinsonHan`.

## The outline

| § | module | subject |
|---|---|---|
| **2** | | *Linear Operators on Normed Spaces* |
| 2.3 | `Chapter02.Section03` | Geometric series, perturbation, consistency and stability |
| 2.4 | `Chapter02.Section04` | Extension, bounded inverse, conditioning, uniform boundedness |
| 2.5 | `Chapter02.Section05` | Linear functionals, Hahn–Banach, Riesz representation |
| **3** | | *Approximation Theory* |
| 3.3 | `Chapter03.Section03` | Best approximation: existence, uniqueness, strict convexity |
| 3.4 | `Chapter03.Section04` | Best approximation in inner product spaces; projections |
| 3.6 | `Chapter03.Section06` | Projection operators and direct sums |
| 3.7 | `Chapter03.Section07` | Uniform error bounds: the Lebesgue lemma and non-convergence |
| **5** | | *Nonlinear Equations and Their Solution by Iteration* |
| 5.1 | `Chapter05.Section01` | The Banach fixed-point theorem; strongly monotone operators |
| 5.2 | `Chapter05.Section02` | Iterative methods: the scalar case and matrix splittings |
| 5.3 | `Chapter05.Section03` | Differential calculus for nonlinear operators; convex functionals |
| 5.4 | `Chapter05.Section04` | Newton's method and the Newton–Kantorovich theorem |
| 5.6 | `Chapter05.Section06` | The conjugate gradient method for operator equations |
| **8** | | *Variational Formulations of Elliptic Boundary Value Problems* |
| 8.2 | `Chapter08.Section02` | Existence and uniqueness for operator equations |
| 8.3 | `Chapter08.Section03` | Bilinear forms and the Lax–Milgram lemma |
| 8.7 | `Chapter08.Section07` | The generalized (Nečas) Lax–Milgram lemma |
| **9** | | *The Galerkin Method and Its Variants* |
| 9.1 | `Chapter09.Section01` | The Galerkin method, the Ritz formulation, Céa's inequality |
| 9.2 | `Chapter09.Section02` | The Petrov–Galerkin method and Babuška's theorem |
| 9.3 | `Chapter09.Section03` | The generalized Galerkin method and Strang's first lemma |
| 9.4 | `Chapter09.Section04` | The conjugate gradient method in variational form |

A section module imports the section modules it builds on, so the import graph runs forwards
through the book: §3.3 on §2.4, §5.4 on §5.3, §9.1 on §8.3, §9.4 on §5.6 and §9.1.

## Ambient conventions

* **Scalars.** The book's `𝕂 ∈ {ℝ, ℂ}` is `[RCLike 𝕜]`. Where the book itself restricts to the
  reals — all of §3.4, Definition 2.5.4 and Theorem 2.5.5, Definition 3.3.6 and Theorem 3.3.7,
  strictly normed spaces, and the whole of Chapters 8 and 9 — the statements are over `ℝ`. A
  statement that mixes a `𝕜`-subspace with a real-convex set carries `[NormedSpace ℝ V]` and
  `[IsScalarTower ℝ 𝕜 V]`, because `Convex ℝ K` does not elaborate under a bare
  `[NormedSpace 𝕜 V]`.
* **Inner products.** The book's `(u, v)` is linear in its *first* argument and Mathlib's
  `⟪u, v⟫` in its second, so the book's `(v, u)` is written `inner 𝕜 u v` throughout. The swap is
  invisible in the real symmetric case, and is why several §2.5 and §3.4 statements read with
  their arguments reversed.
* **Operators and duals.** `𝓛(V, W)` is `V →L[𝕜] W` and `V'` is `StrongDual 𝕜 V`. The book's
  "`L` is a bijection of `V` onto `W` whose inverse is bounded" is `∃ e : V ≃L[𝕜] W, ↑e = L`,
  bridged to the ring-theoretic `IsUnit` the backbone uses by
  `isUnit_iff_exists_continuousLinearEquiv`. `Vᗮ` is `Submodule.orthogonal`.
* **Bilinear forms.** The data of §8.3 and Chapter 9 is a `BilinForm V` (`V →ₗ[ℝ] V →ₗ[ℝ] ℝ`)
  with unbundled predicates `IsBoundedWith M`, `IsEllipticWith α` and `LinearMap.BilinForm.IsSymm`.
  Bundled by `BilinForm.toCLM`, such a form *is* the backbone's `SesqForm ℝ V`, so the
  `Numlib.Variational` API applies to it with no conversion function; only the
  `RCLike.re`/`starRingEnd` decorations have to be erased, which the backbone's real
  specializations do.
* **Book-faithful hypotheses.** Where the book carries a hypothesis its own proof does not use,
  the hypothesis is kept and the doc comment says so — Theorem 3.3.13's convexity, the vector
  space structure in the metric half of §5.1, and the Hilbert data of Theorem 9.3.1, which
  `theorem_9_3_1'` re-attaches to the abstract `theorem_9_3_1`. Such statements carry
  `set_option linter.unusedVariables false` or `linter.unusedSectionVars false` rather than being
  weakened.

## Where formalizing corrected the book

* **§3.4, the display (3.4.5).** The book states the norm of the orthogonal projection as
  `‖P_K‖ = 1`. That fails for `K = {0}`, where `P_K = 0`. `theorem_3_4_7` states the correct
  form: `‖P_K‖ ≤ 1`, with equality exactly when `K ≠ {0}`.
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

## Deferred to a later phase

Three bodies of material are missing for want of infrastructure rather than for difficulty, and
each section module names the results it leaves out.

* **Sobolev spaces.** §8.1 and §8.4–8.8 are the book's Sobolev-space theory and its application to
  elliptic boundary value problems; they are not formalized, and neither are Example 2.4.2 (the
  derivative extended to `H¹`), Example 2.5.9 and the concrete PDE instances of Chapter 9, because
  Mathlib has no Sobolev spaces. What survives is the abstract skeleton — §8.2, §8.3, §8.7 and
  Chapter 9 — which is where the functional analysis lives; the missing part is the verification
  that a particular boundary value problem satisfies its hypotheses.
* **The theorems about reflexive spaces.** Theorems 3.3.8, 3.3.10, 3.3.11 (Mazur), 3.3.12 and
  3.3.14, on minimizers of weakly sequentially lower semicontinuous functionals over a reflexive
  Banach space, all rest on weak sequential compactness of the closed unit ball (the book's
  Theorem 2.7.5), which Mathlib does not have. `WeakSeqTendsto` and `example_3_3_5` record as much
  of the setting as can be stated without it; the finite-dimensional and Hilbert cases of the same
  material are proved in full.
* **Winther's theorem.** Theorem 5.6.2, the superlinear convergence of conjugate gradients for
  `A = I - K` with `K` compact, is blocked by the spectral theorem for compact self-adjoint
  operators, which Mathlib does not have. The displays (5.6.7)–(5.6.10) and Theorem 5.6.3 (rates
  for Hilbert–Schmidt and `Cᵖ` kernels) are out of scope for the same reason.

Smaller omissions all have the same shape — an object the backbone has not built yet — and each is
listed in the module it belongs to: the `C[a, b]` integral-operator toolkit (Examples 2.3.2, 2.3.6
and 5.3.10, the Fredholm, Urysohn, Volterra and Picard applications of §5.2.3–5.2.4, and the
applications of §5.4), trigonometric and interpolatory approximation (§3.7 almost in its entirety,
including Jackson's theorems and the Fourier projections, and Examples 3.6.5, 3.6.6 and 3.6.8),
`Lᵖ` and `L²` function spaces (Examples 2.5.1, 3.4.8 and 3.4.9), numerical quadrature (§2.4.4) and
Chebyshev equioscillation (Theorems 3.3.19–3.3.20). §5.5, on completely continuous vector fields,
is quoted by the book without proof and is summarized in `Chapter05.Section03` rather than
formalized.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/
