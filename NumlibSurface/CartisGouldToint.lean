/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter01
import NumlibSurface.CartisGouldToint.Chapter02
import NumlibSurface.CartisGouldToint.Chapter03
import NumlibSurface.CartisGouldToint.Chapter04
import NumlibSurface.CartisGouldToint.Chapter05
import NumlibSurface.CartisGouldToint.Chapter06
import NumlibSurface.CartisGouldToint.Chapter07
import NumlibSurface.CartisGouldToint.Chapter08
import NumlibSurface.CartisGouldToint.Chapter09
import NumlibSurface.CartisGouldToint.Chapter10
import NumlibSurface.CartisGouldToint.Chapter11
import NumlibSurface.CartisGouldToint.Chapter12
import NumlibSurface.CartisGouldToint.Chapter13
import NumlibSurface.CartisGouldToint.Chapter14
import NumlibSurface.CartisGouldToint.AppendixA
import NumlibSurface.CartisGouldToint.AppendixB

/-!
# Cartis, Gould and Toint, *Evaluation Complexity of Algorithms for Nonconvex Optimization*

This library formalizes the numbered results of C. Cartis, N. I. M. Gould and Ph. L. Toint,
*Evaluation Complexity of Algorithms for Nonconvex Optimization: Theory, Computation and
Perspectives*, MOS–SIAM Series on Optimization 30, SIAM, 2022 [cartis2022evaluation]. The book
bounds the number of evaluations of the objective function and its derivatives that an algorithm
needs to find an approximate first-, second- or higher-order critical point of a smooth nonconvex
function, shows that the bounds are sharp, and treats the subproblems that the algorithms solve. The
library covers the introductory Chapter 1, Part I (evaluation complexity for low-order optimality,
Chapters 2–11), Part II (evaluation complexity for higher-order optimality, Chapters 12–14) and
Appendices A and B; Part III ("Conclusions and perspectives") has no numbered items. Each module
states the results of the book in the terms of the book and proves them from Mathlib and the
backbone, mainly the optimization modules: the generic trust-region and adaptive-regularization runs
(`Numlib.Optimization.ModelBased.TRRun`, `Numlib.Optimization.ModelBased.ARRun`,
`Numlib.Optimization.ModelBased.HighOrder`), evaluation counting
(`Numlib.Optimization.Complexity.Basic`), Taylor models
(`Numlib.Optimization.ModelBased.TaylorModel`), criticality measures
(`Numlib.Optimization.Optimality.Approximate`, `Numlib.Optimization.Optimality.ConstrainedMeasure`),
constructions of slow examples and lower bounds (`Numlib.Optimization.Complexity.ZeroChain`,
`Numlib.Optimization.Complexity.CarmonChain`), and the theory of the subproblems
(`Numlib.Optimization.Subproblem.Matrix`).

## Coverage

Every numbered theorem, lemma, corollary and example of Chapters 1–14 and of Appendices A and B has
a declaration, and so does every numbered algorithm, as a run predicate with an existence theorem or
a counterexample to existence. The numbered assumptions, the definitions and the displayed equations
that the statements use are formalized with them. Theorem 14.3.9 is proved for the classes of inner
solvers listed under Deviations, and some of its cases are open (see Not formalized). Chapter 11 has
no numbered results; the library states the displayed claims of that chapter that can be checked. In
the Subject column below, "items $a$–$b$" means all numbered results with numbers from $a$ to $b$.
Out of scope are the historical and introductory §§1.2–1.4, Part III, discussion and variants
without numbered results, heuristic procedures, the $O(\cdot)$ restatements of explicit bounds, and
the remarks of the Notes sections.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1.1 Optimality conditions | `Chapter01.Section01` | LICQ, KKT pairs; Theorems 1.1.1–1.1.4 |
| §2.1 A requirement | `Chapter02.Section01` | the assumptions f.Bb, f.C1, f.gL |
| §2.2 Linesearch algorithms | `Chapter02.Section02` | SDBA, SDEX; items 2.2.1–2.2.5 |
| §2.3 The trust-region method | `Chapter02.Section03` | TR1; items 2.3.1–2.3.8 |
| §2.4 The adaptive-regularization method | `Chapter02.Section04` | AR1; items 2.4.1–2.4.5 |
| §3.1 Slow convergence of Newton's method | `Chapter03.Section01` | f.C2, f.HL; Theorem 3.1.1 |
| §3.2 Trust region with second derivatives | `Chapter03.Section02` | TR2; items 3.2.1–3.2.7 |
| §3.3 Regularization with second derivatives | `Chapter03.Section03` | AR2; items 3.3.1–3.3.10 |
| §3.4 More $O(\epsilon^{-3/2})$ algorithms | `Chapter03.Section04` | TRε, iRN; items 3.4.1–3.4.12 |
| §3.5 Optimal complexity | `Chapter03.Section05` | the class $\mathcal{M}$; items 3.5.1–3.5.5 |
| §4.1 The ARp algorithm | `Chapter04.Section01` | ARp, f.DpL; items 4.1.1–4.1.6 |
| §4.2 A lower complexity bound | `Chapter04.Section02` | zero chains; items 4.2.1–4.2.6 |
| §5.1 Least squares and least Euclidean norms | `Chapter05.Section01` | ARpLE; items 5.1.1–5.1.7 |
| §5.2 Partially separable problems | `Chapter05.Section02` | (5.2.1)–(5.2.2) |
| §5.3 Measure-dominated problems | `Chapter05.Section03` | items 5.3.1–5.3.12 |
| §5.4 Phase complexity under strict local convexity | `Chapter05.Section04` | items 5.4.1–5.4.4 |
| §5.5 Universal regularization methods | `Chapter05.Section05` | ARp-H, f.DpH; items 5.5.1–5.5.7 |
| §6.1 Problems with convex constraints | `Chapter06.Section01` | C.CNe; measures (6.1.5)–(6.1.10) |
| §6.2 The ARp-CC algorithm | `Chapter06.Section02` | ARp-CC, ARp1-CC; items 6.2.1–6.2.5 |
| §6.3 Convex constraints, least Euclidean norm | `Chapter06.Section03` | ARpLE-CC; Theorem 6.3.1 |
| §7.1 The general constrained problem | `Chapter07.Section01` | (7.1.1), (7.1.4); Theorem 7.1.1 |
| §7.2 First-order approximate minimizers | `Chapter07.Section02` | TPp-GC; items 7.2.1–7.2.7 |
| §8.1 The context of the step computation | `Chapter08.Section01` | the two subproblems |
| §8.2 A digression on all things secular | `Chapter08.Section02` | items 8.2.1–8.2.8 |
| §8.3 Subproblem solution | `Chapter08.Section03` | Algorithms and Corollaries 8.3.1–8.3.2 |
| §9.1 Matrix factorization | `Chapter09.Section01` | Algorithm 9.1.1, Corollary 9.1.1 |
| §9.2 Finding a point in $\mathcal{L}$ | `Chapter09.Section02` | Algorithm 9.2.1 |
| §9.3 The regularization subproblem | `Chapter09.Section03` | (9.3.3)–(9.3.7); items 9.3.1–9.3.2 |
| §9.4 The trust-region subproblem | `Chapter09.Section04` | bounds and tests (9.4.1)–(9.4.7) |
| §10.1 Krylov-subspace methods | `Chapter10.Section01` | Lanczos (Algorithm 10.1.1) |
| §10.2 Regularization methods | `Chapter10.Section02` | items 10.2.1–10.2.3 |
| §10.3 The trust-region case | `Chapter10.Section03` | items 10.3.1–10.3.3 |
| §11.1 Variable scaling | `Chapter11.Section01` | (11.1.2)–(11.1.7), §§11.1.3–11.1.4 |
| §11.2 Radius and weight updates | `Chapter11.Section02` | (11.2.3)–(11.2.6) |
| §11.3 Least-squares models | `Chapter11.Section03` | (11.3.1)–(11.3.3) |
| §12.1 Optimality conditions revisited | `Chapter12.Section01` | items 12.1.1–12.1.8 |
| §12.2 Minimizers of arbitrary order | `Chapter12.Section02` | TRq, ARqp; items 12.2.1–12.2.17 |
| §12.3 Inexact global minimization in ARqp | `Chapter12.Section03` | relaxed Step 2 of ARqp |
| §13.1 Implicit dynamic accuracy | `Chapter13.Section01` | TRqIDA, ARqpIDA; items 13.1.1–13.1.19 |
| §13.2 Low-degree oracles | `Chapter13.Section02` | (13.2.1)–(13.2.4), Theorem 13.2.1 |
| §13.3 Explicit dynamic accuracy | `Chapter13.Section03` | TRqEDA, ARqpEDA; items 13.3.1–13.3.8 |
| §14.1 Composite optimization problems | `Chapter14.Section01` | ARqpC; items 14.1.1–14.1.11 |
| §14.2 Simple constraints | `Chapter14.Section02` | -SC methods; items 14.2.1–14.2.5 |
| §14.3 Nonconvex constraints | `Chapter14.Section03` | LENq-SC, TPqp-GC; items 14.3.1–14.3.9 |
| §A.8 Taylor's theorem | `AppendixA.Section08` | items A.8.1–A.8.5, (A.16) |
| §A.9 Polynomial Hermite interpolation | `AppendixA.Section09` | Theorems A.9.1–A.9.2 |
| §A.10 Simple series bounds | `AppendixA.Section10` | Lemma A.10.1, (A.34)–(A.36) |
| Appendix B, Chapter 2 | `AppendixB.Chapter02` | Lemmas B.2.1–B.2.6, zig-zag example |
| Appendix B, Chapter 3 | `AppendixB.Chapter03` | Lemma B.3.1 |
| Appendix B, Chapter 4 | `AppendixB.Chapter04` | Lemma B.4.1, derivatives of $\|s\|^{p+\beta}$ |
| Appendix B, Chapter 5 | `AppendixB.Chapter05` | Lemma B.5.1, the exponents $\iota_j$ |
| Appendix B, Chapter 7 | `AppendixB.Chapter07` | Lemma B.7.1 |
| Appendix B, Chapter 8 | `AppendixB.Chapter08` | Lemmas B.8.1–B.8.2, Newton and secant |
| Appendix B, Chapter 10 | `AppendixB.Chapter10` | Lemma B.10.1, tridiagonal inverses |
| Appendix B, Chapter 12 | `AppendixB.Chapter12` | Lemma B.12.1 |

## Conventions

* A declaration is named for the item that it states: `CartisGouldToint.Chapter03.theorem_3_3_5` is
  Theorem 3.3.5, `CartisGouldToint.AppendixB.lemma_B_4_1_i` is Lemma B.4.1 (i),
  `CartisGouldToint.Chapter08.corollary_8_2_4` is Corollary 8.2.4,
  `CartisGouldToint.Chapter12.example_12_2_2` is Example 12.2.2,
  `CartisGouldToint.AppendixA.eq_A_16` is the display (A.16), and
  `CartisGouldToint.Chapter02.algorithm_2_3_1` is Algorithm 2.3.1 as a run predicate. The clauses of
  one result are told apart by a roman numeral or a descriptive suffix
  (`CartisGouldToint.Chapter04.theorem_4_1_5_ii`,
  `CartisGouldToint.Chapter12.theorem_12_1_5_counterexample`).
* The named assumptions of the book are `AssumptionXY`: f.gL is
  `CartisGouldToint.Chapter02.AssumptionGL`, and f.DpL is
  `CartisGouldToint.Chapter04.AssumptionDpL`. Where they fit, the smoothness assumptions on the
  derivatives are the backbone's anchored assumption `LipschitzDerivsAnchored` on the whole space
  together with a bound on the constants. The constants of the book are definitions named for their
  symbols (`CartisGouldToint.Chapter02.kappaSDBA`, `CartisGouldToint.Chapter03.sigmaMaxAR2`).
* The module `ChapterNN.SectionMM` is §N.M, in the namespace `CartisGouldToint.ChapterNN`. The
  module `AppendixA.SectionMM` is §A.M, in the namespace `CartisGouldToint.AppendixA`. The module
  `AppendixB.ChapterNN` holds the separately numbered Lemmas B.N.k, in the namespace
  `CartisGouldToint.AppendixB`. Within the library the dependencies run forward in the order of the
  book.
* The problems live on $\mathbb{R}^n$, which is `EuclideanSpace ℝ (Fin n)`. The gradient
  $\nabla f(x)$ is `gradient f x`. The derivative $\nabla^j f(x)$ of order $j$ is
  `iteratedFDeriv ℝ j f x`, with the operator norm of multilinear maps as the tensor norm (A.7). The
  least eigenvalue $\lambda_{\min}[\nabla^2 f(x)]$ is `minCurvature (iteratedFDeriv ℝ 2 f x)`,
  written `CartisGouldToint.Chapter01.hessianMinEig`. The Taylor models are built from
  `ftaylorSeries ℝ f x`.
* An algorithm is a run predicate. A run is a sequence of iterates, with radii, regularization
  weights and other parameters, that obeys the rules of the algorithm at every iteration before the
  first one that passes the termination test. The nondeterministic choices of the book, such as
  inexact subproblem solutions and parameter updates within ranges, are hypotheses. Every algorithm
  has an existence theorem, or a counterexample where runs need not exist.
* A complexity theorem asserts the existence of the first termination index and explicit bounds on
  the evaluation counts `Optimization.funEvalCount` and `Optimization.derivEvalCount`. A sharpness
  theorem exhibits a function in the class and a run whose first termination index is the claimed
  count.
* An infinite tolerance $\epsilon_2 = +\infty$ is `none : Option ℝ` in Chapters 3–4. In Chapters 5,
  6 and 12–14 the order $q$ of the sought minimizer is explicit, and the tests of higher order are
  switched off. In Chapters 12–14 the tolerances and the radii are vectors `ε δ : ℕ → ℝ` indexed by
  the order.
* In Chapter 13 the inexact derivatives are jets `FormalMultilinearSeries ℝ ℝⁿ ℝ` within the error
  model `Optimization.JetApprox` of the exact jet `ftaylorSeries ℝ f x`. For the methods without a
  termination rule (TRqIDA, ARqpIDA), the bounds count the evaluations up to the first iterate that
  is truly approximately optimal.
* In Chapters 8–11, $H$ is symmetric and $M$ is symmetric positive definite, and every statement is
  transported through the space `Subproblem.ScaledSpace` with the $M$-inner product to the operator
  backbone.

## Deviations from the source

**Chapter 1**

* **Theorem 1.1.2, sufficient condition** (correction). The printed condition, strict curvature on
  the nonzero radial directions $d \in \mathcal{C}(x^*)$ with
  $\langle d, \nabla f(x^*) \rangle = 0$, is not sufficient; the condition is stated on the tangent
  cone, and the two agree for polyhedral $\mathcal{C}$. See
  `CartisGouldToint.Chapter01.theorem_1_1_2_iv` and
  `CartisGouldToint.Chapter01.theorem_1_1_2_iv_counterexample`.
* **(1.1.15) and (1.1.18)** (typo). The source quantifies over all $d$ of the cone, including
  $d = 0$, where the strict inequality fails; the conditions are stated for $d \neq 0$. See
  `CartisGouldToint.Chapter01.theorem_1_1_3_iii` and `CartisGouldToint.Chapter01.theorem_1_1_4_iii`.
* **Theorems 1.1.3 and 1.1.4, constraint qualification** (reading). The source leaves it
  unspecified; LICQ is used. See `CartisGouldToint.Chapter01.licq`.
* **(1.1.14) and (1.1.17)** (generalization). The second-order necessary conditions hold for every
  multiplier vector that satisfies the first-order conditions. See
  `CartisGouldToint.Chapter01.theorem_1_1_3_ii` and `CartisGouldToint.Chapter01.theorem_1_1_4_ii`.

**Chapter 2**

* **Lemma 2.2.1, (2.2.7)** (correction). The printed bound $t_k \ge t_{\mathrm{low}}/2$ needs
  $t_{\mathrm{ini}} \ge t_{\mathrm{low}}/2$; in general $t_k \ge \min(t_{\mathrm{ini}},
  t_{\mathrm{low}}/2)$. See `CartisGouldToint.Chapter02.lemma_2_2_1_index`.
* **Theorem 2.2.2, (2.2.8)** (correction). The printed bound vanishes for
  $t_{\mathrm{ini}} \le 2(1-\alpha)/L$ and omits the first trial point of every iteration. The bound
  is $1 + (\lceil \log_2(L t_{\mathrm{ini}}/(2(1-\alpha))) \rceil + 1) \kappa (f(x_0) -
  f_{\mathrm{low}})/\epsilon^2$ with $\kappa = 1/(\alpha \min(t_{\mathrm{ini}}, (1-\alpha)/L))$,
  which is `CartisGouldToint.Chapter02.kappaSDBA` and equals $\kappa_{\mathrm{SDBA}}$ of the book
  when $t_{\mathrm{ini}} \ge (1-\alpha)/L$. See `CartisGouldToint.Chapter02.theorem_2_2_2`.
* **Theorem 2.2.3** (generalization). The hypothesis $t_{\mathrm{ini}} \ge \alpha$ of the proof is
  not needed. See `CartisGouldToint.Chapter02.theorem_2_2_3`.
* **Theorems 2.2.3 and 2.2.5** (reading). The number $\epsilon^{-2}$ is assumed to be an integer, as
  the proof does in (2.2.14). See `CartisGouldToint.Chapter02.theorem_2_2_3` and
  `CartisGouldToint.Chapter02.theorem_2_2_5`.
* **Lemma 2.3.4** (reading). The bound is stated for every iteration up to and including the
  termination index. See `CartisGouldToint.Chapter02.lemma_2_3_4`.
* **Lemma 2.3.5** (typo). The model decrease, printed $m_k(x_k) - m_k(x_k + s_k)$, is
  $m_k(0) - m_k(s_k)$. See `CartisGouldToint.Chapter02.lemma_2_3_5`.
* **Theorem 2.3.8** (correction). With the printed $B_k = 2t^{-1}$ the Cauchy condition (2.3.4)
  fails; the example uses $B_k = t^{-1} I$ with $t = \Delta_0/2$, and then $\rho_k = 2$. See
  `CartisGouldToint.Chapter02.theorem_2_3_8`.
* **"Reasonable values" after Algorithm 2.4.1** (typo). The values $\gamma_1 = 2$,
  $\gamma_2 = \gamma_3 = 0.5$ contradict (2.4.2); they are not used.

**Chapter 3**

* **Theorems 3.1.1 and 3.2.2** (correction). For the data (3.1.4) the claim
  $\|\nabla f(x_k)\| > \epsilon_1$ can fail at $k = k_\epsilon$. The example prescribes
  $\nabla f(x_{k_\epsilon}) = 0$, and the runs stop exactly at
  $k_\epsilon = \lceil \epsilon_1^{-2} \rceil$. See `CartisGouldToint.Chapter03.theorem_3_1_1` and
  `CartisGouldToint.Chapter03.theorem_3_2_2`.
* **§3.2.1, trust-region constraints** (reading). The constraints $x_k - t g \in \mathcal{R}_k$ and
  $x_k + t u \in \mathcal{B}_{\Delta_k}$ on the Cauchy and eigenpoint steps are
  $\|t g\| \le \Delta_k$ and $\|t u\| \le \Delta_k$. See `CartisGouldToint.Chapter03.tr2Step`.
* **Step 1 of Algorithms 3.2.1 and 3.3.1** (reading). The source also stops at approximate strict
  local minimizers. These satisfy (3.2.9) and (3.3.4), so the termination test is that test alone.
  See `CartisGouldToint.Chapter03.stopTest_of_strict` and `CartisGouldToint.Chapter03.stopTest`.
* **Lemma 3.2.5** (reading). The bound is stated for every iteration up to and including the
  termination index. See `CartisGouldToint.Chapter03.lemma_3_2_5`.
* **Theorem 3.2.6, $\kappa^F_{\mathrm{TR2}}$** (typo). The printed constant lacks a $|\log \cdot|$;
  the constant of the proof is at most the printed one with $|\log \cdot|$ inserted. See
  `CartisGouldToint.Chapter03.kappaFTR2_le_book`.
* **Theorem 3.2.6** (generalization). The unused hypothesis $\epsilon_1 \le 1$ is dropped. See
  `CartisGouldToint.Chapter03.theorem_3_2_6`.
* **Theorem 3.2.7, (3.2.25)** (typo). The iterates are $x_k = k \epsilon$, not $(k - 1) \epsilon$,
  and "$s_1 = \epsilon$" means $s_0$. See `CartisGouldToint.Chapter03.theorem_3_2_7`.
* **Hessian of the model after (3.3.2)** (typo). The displayed Hessian has a spurious factor $2$;
  nothing depends on it. See `Optimization.minCurvature_ge_of_regularizedModel`.
* **Theorems 3.3.6 and 3.3.10** (reading). The source defers the proofs to §12.2.2.4; they are
  proved from the data of Theorem 12.2.15. See `CartisGouldToint.Chapter03.theorem_3_3_6` and
  `CartisGouldToint.Chapter03.theorem_3_3_10`.
* **Theorem 3.3.9, (3.3.30)** (correction). The printed bound on the derivative evaluations ends
  with $+ 1$ and is false; it holds with $+ 2$. See `CartisGouldToint.Chapter03.theorem_3_3_9`.
* **Theorem 3.3.9** (generalization). The unused hypothesis $\epsilon_2 \le 1$ is dropped. See
  `CartisGouldToint.Chapter03.theorem_3_3_9`.
* **Lemma 3.4.1** (generalization). The inequality (3.4.7), printed with $\ge$, is strict. See
  `CartisGouldToint.Chapter03.lemma_3_4_1`.
* **Lemma 3.4.3** (typo). The quadratic inequality and its root in the proof are misprinted;
  (3.4.10) is proved directly. See `CartisGouldToint.Chapter03.lemma_3_4_3`.
* **Lemma 3.4.4** (typo). The case labels (3.4.13) and (3.4.14) in the proof are swapped. See
  `CartisGouldToint.Chapter03.lemma_3_4_4`.
* **Theorem 3.4.6** (correction). A successful iteration without the required decrease is only
  followed by one with it, so the printed bounds hold with a factor $2$ on the leading terms and
  $+ 2$ in place of $+ 1$ for the derivative evaluations. See
  `CartisGouldToint.Chapter03.theorem_3_4_6` and `Optimization.card_successSet_le_two_mul_add_one`.
* **Lemma 3.4.10** (reading). The bound (3.4.42) is stated for a block of unsuccessful iterations
  that is followed by an iteration before termination; a final block can have one more element. See
  `CartisGouldToint.Chapter03.lemma_3_4_10_last`.
* **Theorem 3.4.11** (correction). The count misses the successful iterations; the constants are
  $\kappa^A = \kappa^S (M + 1)$ and $\kappa^B = M + 2$. See
  `CartisGouldToint.Chapter03.theorem_3_4_11`.
* **Theorem 3.4.12** (correction). The claim of the proof that the gradient stays small is
  unjustified; the bounds hold with a factor $2$ on the leading terms and $\kappa^D = 2M + 3$. See
  `CartisGouldToint.Chapter03.theorem_3_4_12`.
* **Lemma 3.5.1** (typo). The printed constant $\kappa_\lambda = 2 \sqrt{\kappa_\lambda (1 +
  \kappa_{rg})}$ is self-referential; it is $2 \sqrt{\bar\kappa_\lambda (1 + \kappa_{rg})}$. See
  `CartisGouldToint.Chapter03.lemma_3_5_1`.
* **Lemma 3.5.1** (generalization). The lemma holds without (3.5.3), $\kappa_{rg} < 1$ and
  $s \neq 0$. See `CartisGouldToint.Chapter03.lemma_3_5_1`.
* **Lemma 3.5.2** (generalization). The assumptions f.Bb and f.gL are not needed, and the bound
  holds with the constant $C^{-1/2}$. See `CartisGouldToint.Chapter03.lemma_3_5_2_sqrt`.
* **Lemma 3.5.3** (generalization). The assumptions f.Bb and f.HL and the step relation (3.5.1) are
  not needed. See `CartisGouldToint.Chapter03.lemma_3_5_3`.
* **Theorem 3.5.4** (generalization). The bound $|f| \le B$ holds on all of $\mathbb{R}$. See
  `CartisGouldToint.Chapter03.theorem_3_5_4`.
* **(3.5.13)** (correction). The claim $f_k \in [1/2, 1]$ holds only for $k < k_\epsilon$;
  $f_{k_\epsilon} \in (0, 1/2]$. See `CartisGouldToint.Chapter03.theorem_3_5_4`.
* **(3.5.17)** (typo). The step is $s_k = +\theta_k \epsilon_1^{1/2} / (2 f_k)$; the printed sign is
  wrong. See `CartisGouldToint.Chapter03.theorem_3_5_4`.
* **Corollary 3.5.5, iRN** (correction). On the data (3.5.12) the ratio (3.4.35) of iRN, which is
  not scale invariant, can be below $\eta$ when $\eta > 1/2$. The example is rescaled to
  $c G(x / c)$ with $c = \min(1, (2 \eta)^{-1/2})$. See
  `CartisGouldToint.Chapter03.corollary_3_5_5_iii`.

**Chapter 4**

* **Algorithm 4.1.1, (4.1.8)–(4.1.9)** (correction). The source also requires
  $\mathcal{M}_k \neq \emptyset$, with which a run can get stuck. The condition is read as "for all
  $d \in \mathcal{M}_k$", as in the proof of Theorem 4.1.5, and so is (4.1.13). See
  `CartisGouldToint.Chapter04.arpStopTest` and `CartisGouldToint.Chapter04.algorithm_4_1_1`.
* **Algorithm 4.1.1 with $\epsilon_3 < \infty$** (correction). A step that satisfies Step 2 need not
  exist, and Theorem 4.1.5 in the third-order case is a statement about runs. See
  `CartisGouldToint.Chapter04.not_exists_algorithm_4_1_1_third_order`.
* **Theorem 4.1.5** (reading). The theorem, printed with one constant $\kappa^S$ for the three
  orders, is split by the order of criticality, each part with the constants of the active orders.
  See `CartisGouldToint.Chapter04.theorem_4_1_5_i`.
* **Theorem 4.1.5** (generalization). The tolerances need only be positive, not in $(0, 1]$. See
  `CartisGouldToint.Chapter04.theorem_4_1_5_i`.
* **Theorem 4.1.6, third-order case** (correction). The proof that the source defers to §12.2.2.4
  has the wrong sign of $\lambda_{\min}$; the case is proved for
  $\sigma_0 \le (p-2)! \min(\theta_2, \theta_3)$. See
  `CartisGouldToint.Chapter04.theorem_4_1_6_iii`.
* **(4.2.6)** (typo). The first term of $f^D$ is $-\Psi(1) \Phi([x]_1)$, not
  $-\Psi([x]_1) \Phi([x]_1)$, with which Lemma 4.2.5 (ii) fails at $x = 0$. See
  `CartisGouldToint.Chapter04.hardFunction`.
* **Theorem 4.2.6** (correction). The proof gives $\#_\epsilon \ge \bar k$ for both classes, not
  $\ge 2 \bar k$, and the form (4.2.7) with $c_0$ needs $\epsilon$ small. See
  `CartisGouldToint.Chapter04.theorem_4_2_6_i`.
* **Theorem 4.2.6, tightness of (4.2.3)** (reading). Only the order in $\epsilon$ is tight, and the
  upper bound uses $L_{f,p} = \max(1, L)$ and an integer part. See
  `CartisGouldToint.Chapter04.theorem_4_2_6_ii`.
* **Lemma 4.2.5 (i)** (generalization). The lemma holds for every $p$, not only for $p \ge 1$. See
  `CartisGouldToint.Chapter04.lemma_4_2_5_i`.
* **Lemma 4.2.5 (iv)** (reading). The absolute constant of the growth bound is $c_1 = 20$. See
  `CartisGouldToint.Chapter04.lemma_4_2_5_iv_growth`.
* **The class $\mathcal{F}(\Delta, p)$** (reading). The members are $C^\infty$, as in footnote 29,
  and the Lipschitz constant is explicit. See `CartisGouldToint.Chapter04.functionClass`.
* **(4.2.1), zero-respecting methods** (reading). Zero respect is defined through null directions of
  the derivative tensors. See `CartisGouldToint.Chapter04.methodClassZR`.
* **Footnote 30 and Theorem 4.2.4** (reading). They assume $L \ge 0$. See
  `CartisGouldToint.Chapter04.comp_adjoint_mem_functionClass` and
  `CartisGouldToint.Chapter04.theorem_4_2_4_i`.
* **Lemmas 4.2.2, 4.2.3 and Theorem 4.2.4** (generalization). The unused hypotheses $\epsilon > 0$,
  $p \ge 1$ and, for Lemma 4.2.2, $f \in \mathcal{F}(\Delta, p)$ are dropped. See
  `CartisGouldToint.Chapter04.lemma_4_2_2`.
* **Lemma 4.2.3** (typo). The source cites (4.2.3) for $\#_\epsilon$; the definition is (4.2.2). See
  `CartisGouldToint.Chapter04.lemma_4_2_3`.

**Chapter 5**

* **Algorithm 5.1.1, third-order test** (correction). With the requirement
  $\mathcal{M}_k \neq \emptyset$ the proof of Theorem 5.1.7 fails when
  $\mathcal{M}_{k+1} = \emptyset$, so "for all $d \in \mathcal{M}_k$" is read vacuously. See
  `CartisGouldToint.Chapter05.ARpLEStop`.
* **Algorithm 5.1.1, existence of runs** (reading). For $q = 3$ an admissible step need not exist;
  runs exist for $q \le 2$. See `CartisGouldToint.Chapter05.algorithm_5_1_1.exists_run`.
* **Lemma 5.1.5** (reading). The statement needs $p \neq 0$, where the book writes
  $p \in \mathbb{N}$. See `CartisGouldToint.Chapter05.lemma_5_1_5`.
* **Theorem 5.1.7** (typo). The multiplier in (5.1.44) is $\kappa^A$ (printed $\kappa^C$); in
  (5.1.51) the conditions are alternatives (printed "and"), and $\mathcal{M}_{j+1}$ is that of
  (4.1.14) (printed (4.1.9)). See `CartisGouldToint.Chapter05.theorem_5_1_7`.
* **Theorem 5.1.7** (reading). The run may also stop by the strict-local-minimizer test (5.1.11).
  See `CartisGouldToint.Chapter05.theorem_5_1_7`.
* **Theorem 5.1.7** (generalization). The tolerances need only be positive, and a general form holds
  for every order $q \le 3$ and all $\ell$, $i$ with $\iota_j \ge 0$ for $j \le q$. See
  `CartisGouldToint.Chapter05.theorem_5_1_7_of_iota_nonneg`.
* **Domination in §5.3** (generalization). Domination is assumed only at the iterates, as the book
  remarks after Lemma 5.3.1. See `CartisGouldToint.Chapter05.IsDominated.range`.
* **Theorems 5.3.3–5.3.5** (generalization). The hypothesis $\Gamma_0 > 0$ is not needed. See
  `CartisGouldToint.Chapter05.theorem_5_3_3`.
* **Theorem 5.3.3** (reading). The bounds $\log|\log\epsilon|$ are stated as
  $\log\max(1, |\log\epsilon|)$. See `CartisGouldToint.Chapter05.theorem_5_3_3`.
* **Theorem 5.3.3, $\kappa^F$** (typo). The constant of Appendix B is corrected to
  `Optimization.superlinearCountConst`. See `CartisGouldToint.Chapter05.theorem_5_3_3`.
* **Theorem 5.3.5, $\kappa^E$** (typo). It uses $\min(1, \alpha)$ for $\alpha$ and
  $\Gamma_0^{-\alpha}$ for the printed $\kappa_\psi^{\nu/\mu}/\kappa_\nu$, and the halving argument
  gives $2M + 2$ successful iterations. See `CartisGouldToint.Chapter05.theorem_5_3_5`.
* **Theorem 5.3.9, constants** (typo). $\kappa^E = \mu\kappa_\psi^{\nu/\mu}/((\nu - \mu)\kappa_\nu)$
  (printed with the exponent $\mu/\nu$) and $\kappa^F = -\kappa^E\Gamma_0^{-\alpha}$ (printed
  $\kappa^B$). See `CartisGouldToint.Chapter05.theorem_5_3_9`.
* **Measure versions of Theorems 5.3.3–5.3.5 and 5.3.7–5.3.9** (reading). Reaching a small measure
  takes up to two successful iterations more than the real-valued gap count, where the book adds
  one. See `CartisGouldToint.Chapter05.ARSetting.exists_measure_le`.
* **Measure versions of Theorems 5.3.7–5.3.9** (correction). For TR methods the iterate reached is
  $x_i$ with $i \le k$, where the book writes $x_k$. See `CartisGouldToint.Chapter05.theorem_5_3_7`.
* **Lemma 5.3.6 (ii)** (typo). "$\Gamma_{k_\square} \ge 1$" means
  $\Gamma_{k_\square} \ge \Gamma_\square$. See `CartisGouldToint.Chapter05.lemma_5_3_6`.
* **Theorem 5.3.7** (reading). The constant $\kappa^F_{\mathrm{TR},1}$ is taken in an integer form
  with a ceiling. See `CartisGouldToint.Chapter05.theorem_5_3_7`.
* **(5.3.2)–(5.3.3)** (generalization). Only the reference value $0$ is needed, not
  $\min \Phi_\ell = 0$. See `CartisGouldToint.Chapter05.Phi_isMeasureDominated`.
* **Theorems 5.3.10 and 5.3.11** (generalization). The exponent $\ell$ need not be even. See
  `CartisGouldToint.Chapter05.theorem_5_3_10`.
* **Theorem 5.3.12** (typo). The display mixes $\kappa^C_{\mathrm{TR1,FRLS}}$ and
  $\kappa^C_{\mathrm{TR,FRLS}}$; one constant is meant. See
  `CartisGouldToint.Chapter05.theorem_5_3_12`.
* **Lemma 5.4.1** (generalization). The bound holds for every $x_*$, not only for a local minimizer
  with $\lambda_* > 0$. See `CartisGouldToint.Chapter05.lemma_5_4_1`.
* **Lemma 5.4.2, (5.4.8)** (correction). The printed constant
  $(1 + \theta_1)/(\lambda_* + \sigma_{\min}/2)$ is false; the bound holds with
  $\kappa_s = 2(1 + \theta_1)/\lambda_*$, which changes the radius $\zeta_*$ of (5.4.5). See
  `CartisGouldToint.Chapter05.norm_step_le_of_strict`, `CartisGouldToint.Chapter05.zetaStar` and
  `CartisGouldToint.Chapter05.lemma_5_4_2`.
* **Lemma 5.4.3 and Theorem 5.4.4, (5.4.14)** (correction). The count
  $\log_2 \log_2(\zeta/\epsilon)$ is one too small in the worst case, has no ceiling and is
  undefined for $\epsilon \ge \zeta$; it is $\lceil \log_2 \log_2(\zeta_*/\epsilon) \rceil_+$. See
  `CartisGouldToint.Chapter05.lemma_5_4_3` and `CartisGouldToint.Chapter05.theorem_5_4_4`.
* **Theorem 5.4.4, second part** (reading). The bound (5.4.17) is stated for $|\mathcal{S}_k|$ at
  every iteration before termination, and (5.4.18) is restricted to these iterations. See
  `CartisGouldToint.Chapter05.theorem_5_4_4`.
* **Algorithm 5.5.1, Step 4** (typo). The third case is "$\rho_k < \eta_1$, or (5.5.10) fails, or
  (5.5.11) fails", the complement of the first two cases. See
  `CartisGouldToint.Chapter05.algorithm_5_5_1`.
* **Lemma 5.5.2** (typo). The display writes $\nabla_s m_k(x_k + s_k)$ for $\nabla_s m_k(s_k)$. See
  `CartisGouldToint.Chapter05.lemma_5_5_2`.
* **Lemma 5.5.4** (typo). In case (b) of the proof, $\epsilon_2$ is printed as $\epsilon_1$. See
  `CartisGouldToint.Chapter05.lemma_5_5_4`.
* **Theorem 5.5.7** (correction). The function is evaluated at $x_0$ and at every trial point,
  $k_\epsilon + 2$ times, so $\kappa^C$ needs an additional $+ 2$. See
  `CartisGouldToint.Chapter05.theorem_5_5_7`.

**Chapter 6**

* **(6.1.5) and (6.1.9)** (typo). The leading minus sign of the measures is missing. See
  `CartisGouldToint.Chapter06.omega1` and `CartisGouldToint.Chapter06.omega3`.
* **Start of §6.1** (correction). The claim that C.CNe ensures that (6.1.1) has a solution is false:
  $f(x) = x$ on $\mathcal{C} = \mathbb{R}$ has no minimizer. See
  `CartisGouldToint.Chapter06.not_assumptionCNe_imp_exists_minimizer`.
* **(6.1.4) and (6.1.6)** (reading). "Within $\mathcal{C}$" is the condition $x \in \mathcal{C}$.
  See `CartisGouldToint.Chapter06.IsApproxMinimizerCC`.
* **Order of the sought minimizer** (reading). An explicit $q \in \{1, 2, 3\}$ with $q \le p$
  replaces the infinite tolerances; second order needs $p \ge 2$ and third order $p \ge 3$. See
  `CartisGouldToint.Chapter06.IsApproxMinimizerCC`, `CartisGouldToint.Chapter06.algorithm_6_2_1` and
  `CartisGouldToint.Chapter06.theorem_6_2_3`.
* **Algorithm 6.2.1, Step 2** (correction). For $q \ge 2$ Step 2 can be infeasible, even at a strict
  global minimizer. Theorem 6.2.3 holds for every run, and runs exist for $q = 1$ and whenever Step
  2 is feasible. See `CartisGouldToint.Chapter06.algorithm_6_2_1_not_exists_step`.
* **Lemma 6.2.1, (6.2.18)–(6.2.19)** (correction). The bounds are proved only for $\|d\| \le 1$. See
  `CartisGouldToint.Chapter06.lemma_6_2_1_iii` and `CartisGouldToint.Chapter06.lemma_6_2_1_iv`.
* **Lemma 6.2.2** (typo). The prefactor of $\kappa^{cc}_j$ is $\eta_1 \sigma_{\min} / (p+1)!$, not
  $\eta_1 \sigma_{\min} / p!$. See `CartisGouldToint.Chapter06.lemma_6_2_2`.
* **Theorems 6.2.3 and 6.2.5** (generalization). The restriction $\epsilon_j \le 1$ is not needed.
  See `CartisGouldToint.Chapter06.theorem_6_2_3` and `CartisGouldToint.Chapter06.theorem_6_2_5`.
* **Existence of runs in §6.2** (generalization). The smoothness of f.DpL.C is used only at the
  points of $\mathcal{C}$. See `CartisGouldToint.Chapter06.exists_algorithm_6_2_1_one` and
  `CartisGouldToint.Chapter06.exists_algorithm_6_2_2`.
* **Test (6.3.2)** (reading). The quotient test is written multiplicatively; the two forms agree
  whenever (6.3.1) fails and $\epsilon_0 \ge 0$. See `CartisGouldToint.Chapter06.stopLE`.
* **Display before (6.3.3)** (typo). It mixes the scaled and unscaled measures; the decrease that
  holds is $\kappa_1 \ell \, \omega_{\Phi_\ell,\mathcal{C},1}(x_{k+1})^{(p+1)/p}$. See
  `CartisGouldToint.Chapter06.arpleCC_decrease`.
* **Theorem 6.3.1** (typo). "(5.1.38) for (5.1.39)" means "or". See
  `CartisGouldToint.Chapter06.theorem_6_3_1`.
* **Theorem 6.3.1** (generalization). Only $\iota_1(p, \ell, i) \ge 0$ is assumed, and
  $\epsilon_0, \epsilon_1 \le 1$ is not needed. See `CartisGouldToint.Chapter06.theorem_6_3_1`.

**Chapter 7**

* **(7.1.1)** (generalization). The set $\mathcal{C}$ need not be closed, bounded, nonempty or
  convex.
* **Theorem 7.1.1** (generalization). The set $\mathcal{S}$ need be neither closed nor a subset of
  $\mathcal{C}$. See `CartisGouldToint.Chapter07.theorem_7_1_1`.
* **(7.1.3)–(7.1.4)** (typo). $\mathcal{C}(x)$ and the gradient are evaluated at $x_*$ and
  $x_\epsilon$, not at a free $x$. See `CartisGouldToint.Chapter07.IsFirstOrderMinimizerGC` and
  `CartisGouldToint.Chapter07.IsApproxFirstOrderGC`.
* **(7.1.3)** (reading). The feasibility $x_* \in \mathcal{C}$ is explicit. See
  `CartisGouldToint.Chapter07.IsFirstOrderMinimizerGC`.
* **Assumption f.B.Fb** (reading). The proviso "if $\mathcal{F}_\beta \neq \emptyset$" is vacuous
  for the universally quantified form. See `CartisGouldToint.Chapter07.AssumptionBFb`.
* **Assumption f.D1pL.C** (typo). $\nabla^j_x f_i$ means $\nabla^j_x f$. See
  `CartisGouldToint.Chapter07.AssumptionFD1pLC`.
* **Algorithm 7.2.1, Phase 2** (correction). Step 1 applies ARp1-CC (Algorithm 6.2.2), not ARp-CC,
  since the proof of Lemma 7.2.6 uses Lemma 6.2.4. See `CartisGouldToint.Chapter07.IsTPpGCPhase2`.
* **Algorithm 7.2.1, Step 2(a)** (correction). With the printed test
  $\|r(x_{k+1}, t_k)\| < \theta \epsilon_0$ Lemma 7.2.1 fails; the test is $\le \theta \epsilon_0$.
  See `CartisGouldToint.Chapter07.Phase2Seq.IsKa`.
* **Lemma 7.2.2, (7.2.24)** (correction). The derivative-evaluation bound lacks the term $+ 2$ of
  Theorem 6.3.1. See `CartisGouldToint.Chapter07.lemma_7_2_2`.
* **Lemma 7.2.5** (generalization). The hypothesis $\Phi_\ell$.DpL.C is not needed. See
  `CartisGouldToint.Chapter07.lemma_7_2_5`.
* **Lemma 7.2.6** (correction). The block argument omits the restart of $\sigma$ at $\sigma_0$ in
  every inner run and the elements $i = 0$ of $\mathcal{I}^s_k$, so that (7.2.39) can fail, and it
  gives no bound on the bad outer iterations. See `CartisGouldToint.Chapter07.lemma_7_2_6`.
* **Theorem 7.2.7** (correction). The number of bad outer iterations is a parameter; under bounded
  gradients it is $N_b = O(\epsilon_0^{-1} \epsilon_1^{-1})$, within the order of (7.2.50) for
  $\epsilon_0 = \epsilon_1$ if and only if $p \le 2$. The derivative count has a term
  $\epsilon_0^{-1}$ that (7.2.53) lacks, and whether (7.2.53) holds is open. See
  `CartisGouldToint.Chapter07.theorem_7_2_7` and
  `CartisGouldToint.Chapter07.theorem_7_2_7_of_gradient_le`.
* **(7.2.47)** (generalization). The constant $\kappa_1^{-1} \theta^{-(p+1)/p}$ replaces the weaker
  $\kappa_1^{-1} \theta^{-(p+2)/p}$. See `CartisGouldToint.Chapter07.kappaSGC`.

**Chapter 8**

* **Lemma 8.2.1** (reading). The hypothesis $\pi(\lambda_s) > \tau(\lambda_s)$ is read as
  $\pi(\lambda) \ge c > \tau(\lambda_s)$ for $\lambda$ near $\lambda_s$ from the right, and $\tau$
  is right-continuous at $\lambda_s$. See `CartisGouldToint.Chapter08.lemma_8_2_1`.
* **Theorem 8.2.2** (generalization). It holds for every $k \ge 0$, not only for $k > 0$. See
  `CartisGouldToint.Chapter08.theorem_8_2_2`.
* **Lemma 8.2.3** (correction). The strict inequalities fail for $g = 0$, and for $\beta = -1/2$
  when $g = M v$ for a generalized eigenvector $v$. See
  `CartisGouldToint.Chapter08.lemma_8_2_3_strict`.
* **Corollary 8.2.4** (correction). The statement needs $g \neq 0$; for $g = 0$ the function
  $\pi(\lambda; \beta)$ is constant. See `CartisGouldToint.Chapter08.corollary_8_2_4`.
* **Corollary 8.2.4** (reading). The starting value "$\pi(\lambda_s; \beta)$" is the right limit at
  $\lambda_s$, which can be $+\infty$. See
  `CartisGouldToint.Chapter08.corollary_8_2_4_tendsto_lambdaS`.
* **Theorem 8.2.5** (correction). The strict inequalities fail for $g = 0$ and for $\delta = 0$, and
  (8.2.21) is an equality for $\beta = -1/2$ when $g = M v$ for a generalized eigenvector $v$. See
  `CartisGouldToint.Chapter08.theorem_8_2_5_strict`.
* **§8.2, transformed secular equations** (correction). The convexity of $-\lambda^\gamma$ for
  $\gamma \in (0, 1]$ and the concavity of $\lambda^\gamma$ for $\gamma < 0$, claimed on
  $\lambda \ge \lambda_s$, hold on $\lambda > 0$; the first interval can contain $0$.
* **§8.3, the sets $\mathcal{N}$, $\mathcal{L}$, $\mathcal{G}$** (correction). The set-builder
  descriptions are wrong when $\lambda_1 > 0$; the interval forms, which partition $\mathbb{R}$, are
  used. See `CartisGouldToint.Chapter08.setN`, `CartisGouldToint.Chapter08.setF_reg_eq_Ioi` and
  `CartisGouldToint.Chapter08.setL_tr_union_setG_tr`.
* **§8.3.1, the transformed target** (typo). The target is $(\lambda/\sigma)^{2\beta/(r-2)}$, not
  $(\lambda/\sigma)^{\beta/(r-2)}$, and the ranges of $\beta$ are $(0, (r-2)/2]$ and $[-1/2, 0)$.
  See `CartisGouldToint.Chapter08.regSecularFn`.
* **Algorithm 8.3.1** (correction). The Newton correction (8.2.25) is undefined at $\beta = 0$, so
  the exponents satisfy $\beta_j \neq 0$. See `CartisGouldToint.Chapter08.algorithm_8_3_1`.
* **Corollaries 8.3.1 and 8.3.2** (correction). When $\lambda_1$ is multiple, one eigenvector does
  not parametrize all minimizers; any nonzero generalized eigenvector for $\lambda_1$ is allowed.
  See `CartisGouldToint.Chapter08.corollary_8_3_1` and `CartisGouldToint.Chapter08.corollary_8_3_2`.
* **(8.3.2)** (reading). The minimum-norm solution is taken in the $M$-norm. See
  `CartisGouldToint.Chapter08.minNormSolution`.
* **Corollary 8.3.2, boundary condition** (correction). For $\lambda^* = 0$ the minimizer need not
  lie on the boundary; $\|s_s + \alpha v\|_M = \Delta$ is stated for $\lambda^* > 0$. See
  `CartisGouldToint.Chapter08.corollary_8_3_2`.

**Chapter 9**

* **Algorithm 9.1.1** (typo). The right-hand side has the sign opposite to (8.2.29), so the vectors
  are $(-1)^k s^{(k)}$; the values $\pi^{(j)}$ are not affected. See
  `CartisGouldToint.Chapter09.algS_eq`.
* **Remark after Algorithm 9.1.1** (typo). With a Cholesky factorization
  $\pi^{(2k+1)} = -\beta_k \|y^{(k+1)}\|^2$, without the printed factor $2$. See
  `CartisGouldToint.Chapter09.corollary_9_1_1`.
* **Algorithm 9.2.1, contraction factor** (correction). The printed factor is not uniformly below
  $1$; the uniform factor $\max(1 - \theta_L, \theta_U, 1/2)$ is used. See
  `CartisGouldToint.Chapter09.algorithm_9_2_1_terminates`.
* **Algorithm 9.2.1, finite termination** (correction). Termination needs the initial lower bound
  strictly below $\lambda^*$. See `CartisGouldToint.Chapter09.algorithm_9_2_1_terminates`.
* **(9.3.5)** (generalization). The bound $\lambda^L \le \lambda^*$ holds for every nonnegative
  root, not only for the rightmost one. See `CartisGouldToint.Chapter09.lambdaStar_bounds_9_3_3`.
* **Theorem 9.3.1** (correction). The hypothesis $z_0 \in \mathcal{Z}_1$, which the source omits, is
  added. See `CartisGouldToint.Chapter09.theorem_9_3_1`.
* **Theorem 9.3.1, the set $\mathcal{Z}_1$** (reading). The condition is read in the $M$-inner
  product. See `CartisGouldToint.Chapter09.theorem_9_3_1`.
* **Theorem 9.3.1, quantifiers and order** (reading). The parameter sequences are fixed before the
  radius $\epsilon$, and the Q-order is stated as two-sided bounds. See
  `CartisGouldToint.Chapter09.theorem_9_3_1`.
* **Algorithm 9.3.1, initial shift** (generalization). Only $H + \lambda^G_0 M \succ 0$ is required,
  not $\lambda^G_0 \in \mathcal{G}$. See `CartisGouldToint.Chapter09.algorithm_9_3_1`.
* **Theorem 9.3.2** (correction). With the Euclidean $\lambda_{\min}$ in (9.3.14c) the theorem is
  false for $M \neq I$; (9.3.14) is stated with the $M$-scalings. See
  `CartisGouldToint.Chapter09.theorem_9_3_2`.
* **(9.3.6), middle term** (correction). The middle term is not a valid bound; only the outer
  inequality is stated. See `CartisGouldToint.Chapter09.exists_abs_sub_le_of_eigen`.
* **(9.4.5)** (correction). The equivalence $m_{\Delta_2} \le m_{\Delta_1} \iff \Delta_2 \ge
  \Delta_1$ is false; only the implication holds. See `CartisGouldToint.Chapter09.trValue_antitone`.
* **(9.4.6) and (9.4.7)** (generalization). The bounds hold for any point on the sphere of radius
  $\Delta^+$ (or $\Delta^-$), not only for minimizers. See
  `CartisGouldToint.Chapter09.optimalValue_bounds_9_4_6`.

**Chapter 10**

* **(10.1.7)** (typo). The leading block of $T_k$ is $T_{k-1}$, not $T_{k-1}^{-1}$. See
  `CartisGouldToint.Chapter10.algorithm_10_1_1_spec`.
* **§10.1.1, nesting of the Krylov subspaces** (typo). $\mathcal{K}(A, b, k + 1)$ is the span of
  $\mathcal{K}(A, b, k) \cup \{A^k b\}$, not the union. See
  `CartisGouldToint.Chapter10.krylovSpace_succ`.
* **Lemma 10.2.1** (typo). The problem is (8.1.3), not the model (8.1.4). See
  `CartisGouldToint.Chapter10.lemma_10_2_1`.
* **Corollaries 10.2.3 and 10.3.3** (correction). The printed iteration bounds cannot hold when the
  logarithm is negative and are undefined for $\kappa_* = 1$. The ceiling is
  $\lceil \cdot \rceil_+$, the case $\kappa_* = 1$ gives some $k \le \min(2, \text{grade})$, and the
  hypothesis $g \neq 0$ is added. See `CartisGouldToint.Chapter10.corollary_10_2_3` and
  `CartisGouldToint.Chapter10.corollary_10_3_3`.

**Chapter 11**

* **(11.1.6)** (typo). The regularization term is $\frac{\sigma}{r} \|s^D\|^r$, printed with
  $\|s\|^r$. See `CartisGouldToint.Chapter11.idealScaling_transform`.
* **(11.1.7)** (typo). The cases read $\lambda_i \ge \delta$ and $\lambda_i \le -\delta$ (printed
  $>$ and $<$), to agree with (11.1.4). See `CartisGouldToint.Chapter11.div_modifiedAbs`.
* **§11.1.3, regularization** (typo). The secular equation has the right-hand side
  $(\lambda/\sigma)^{2/(r-2)}$ (printed $(\lambda^2/\sigma^2)^{2/(r-2)}$), the hard case occurs if
  and only if $\frac12 \|g^D\| \le \sigma^{-1/(r-2)}$ (printed $\ge$), and then $\sum \alpha_i^2 =
  \sigma^{-2/(r-2)} - \frac14 \|g^D\|^2$ (printed as a product). See
  `CartisGouldToint.Chapter11.diagonal_regularization_solution` and
  `CartisGouldToint.Chapter11.diagonal_regularization_hardCase`.
* **(11.2.3) and (11.2.5)** (typo). Both are printed inverted; they are
  $\lambda \approx \|g\|_{M^{-1}} / \Delta$ and $\sigma \approx \|g\|_{M^{-1}} / \Delta^{r-1}$, as
  the derivation, Table 11.2.1 and the rule (11.2.6) confirm. See
  `CartisGouldToint.Chapter11.trMultiplier_asymptotics` and
  `CartisGouldToint.Chapter11.radius_weight_correspondence`.

**Chapter 12**

* **Example 12.1.1** (typo). The printed descent curve is garbled; the curve
  $(t, \frac12 e^{-1/t^2})$ is used. See `CartisGouldToint.Chapter12.example_12_1_1`.
* **Theorem 12.1.1** (generalization). The restriction to tuples of nonzero $s_i$ is dropped. See
  `CartisGouldToint.Chapter12.theorem_12_1_1`.
* **Example 12.1.2** (typo). The printed $\kappa_1 = 1$, $\kappa_2 = 2$ give no saddle;
  $\kappa_1 = 3$, $\kappa_2 = 2$ are used, as in Figure 12.1.2, also in Theorem 12.1.2. See
  `CartisGouldToint.Chapter12.example_12_1_2` and `CartisGouldToint.Chapter12.theorem_12_1_2`.
* **Theorem 12.1.3 (iii)** (generalization). For the projected norm on
  $\ker^1[\nabla f(x)] \cap \ker^2[\nabla^2 f(x)]$ the first- and second-order hypotheses are not
  needed. See `CartisGouldToint.Chapter12.theorem_12_1_3_iii`.
* **Example 12.1.3 (iv)** (correction). The claim is false in $n$ variables and is stated in one
  variable. See `CartisGouldToint.Chapter12.example_12_1_3`.
* **Theorem 12.1.5** (correction). An isolated minimizer $s = 0$ of $T_{f,j}(x, \cdot)$ need not be
  uniformly isolated, and the printed statement is false; the theorem is proved under growth of
  order $j$. See `CartisGouldToint.Chapter12.theorem_12_1_5` and
  `CartisGouldToint.Chapter12.theorem_12_1_5_counterexample`.
* **Theorem 12.1.6 (ii)** (correction). The statement needs $f \in C^2$, not only $C^1$, and the
  constant $\kappa(x)$ is explicit. See `CartisGouldToint.Chapter12.theorem_12_1_6_ii`.
* **Theorem 12.1.7** (generalization). The radius condition is written multiplicatively, so that
  $\nabla^j f(x) = 0$ is allowed. See `CartisGouldToint.Chapter12.theorem_12_1_7`.
* **After Theorem 12.1.7** (typo). The recursive use of the theorem needs
  $\epsilon_q \le \dots \le \epsilon_1$; the printed chain is reversed.
* **Theorem 12.1.8, (12.1.35)** (typo). The printed $\delta^j$ is $\delta_j^j$. See
  `CartisGouldToint.Chapter12.theorem_12_1_8`.
* **Algorithm 12.2.2, Step 1** (typo). The test continues on $>$, not the printed $\ge$, with which
  the sharpness examples never stop. See `CartisGouldToint.Chapter12.algorithm_12_2_2`.
* **Algorithm 12.2.2, Step 2** (reading). Termination in Step 2 is allowed only when $0$ is a global
  minimizer of the model, as Algorithm 12.2.3 guarantees. See
  `CartisGouldToint.Chapter12.algorithm_12_2_2`.
* **(12.2.28)** (typo). The long-step branch is $\|s_k\| \ge 1$, printed $\|s_k\| > 1$, as in
  Algorithm 12.2.3. See `CartisGouldToint.Chapter12.algorithm_12_2_2`.
* **Theorem 12.2.5** (typo). The printed conclusion $\phi^{\delta_\epsilon}_{f,q}$ is
  $\phi^{\delta_\epsilon}_{f,j}$. See `CartisGouldToint.Chapter12.theorem_12_2_5`.
* **Theorem 12.2.6** (correction). The slow data of Appendix B are wrong in the decrease of $f$
  against the Taylor decrease, in $x_k = k\epsilon$, in $\epsilon^{q+1} k_\epsilon \le 1$ (only
  $\le 2$ holds) and in the factor $q!/(q-j)!$ of the residuals; corrected data are used. See
  `CartisGouldToint.Chapter12.theorem_12_2_6` and `Optimization.exists_slowTRq_interpolant`.
* **Lemma 12.2.11** (correction). The factor $1 - \theta$ is $\varsigma - \theta$, with
  $\theta < \varsigma$, and the lemma needs a short step at the iteration $k$. See
  `CartisGouldToint.Chapter12.lemma_12_2_11`.
* **Lemma 12.2.12, $q > 2$** (correction). The constant $\kappa_{\delta,\min}$ is replaced by
  $\hat\kappa = \min(\kappa_{\delta,\min}, \tau_q/2)$, also in Lemma 12.2.13 and Theorem 12.2.14
  (2). See `CartisGouldToint.Chapter12.lemma_12_2_12`.
* **Lemma 12.2.13** (correction). The lemma needs f.D1pL (printed f.D1qL) and holds at successful
  iterations that are followed by an iteration without termination. See
  `CartisGouldToint.Chapter12.lemma_12_2_13`.
* **(12.2.56)** (typo). The printed $(p-j+1)!$ and $\|s_k\|^{p-j+1}$ are $(p-\ell+1)!$ and
  $\|s_k\|^{p-\ell+1}$. See `CartisGouldToint.Chapter12.lemma_12_2_13`.
* **Theorem 12.2.14** (correction). The hypothesis $\theta < \varsigma$ is explicit, and the
  constants have $\varsigma - \theta$ for $1 - \theta$ and, in (2), $\hat\kappa$ for
  $\kappa_{\delta,\min}$. See `CartisGouldToint.Chapter12.theorem_12_2_14_i` and
  `CartisGouldToint.Chapter12.theorem_12_2_14_ii`.
* **Theorem 12.2.14** (reading). The hypothesis $\sigma_{\min} > 0$ is explicit, and the radius
  properties of (1) and (12.2.50) of (2) are hypotheses on the run. See
  `CartisGouldToint.Chapter12.theorem_12_2_14_i` and
  `CartisGouldToint.Chapter12.theorem_12_2_14_ii`.
* **Theorem 12.2.15, $q \ge 3$** (correction). The hypothesis "the choice $\delta_{s_k,j} = 1$ is
  possible" fails for the example of the proof; the theorem is stated for runs whose steps are
  global model minimizers, which are ARqp runs for $q \le 2$. See
  `CartisGouldToint.Chapter12.theorem_12_2_15`,
  `CartisGouldToint.Chapter12.theorem_12_2_15_counterexample` and
  `CartisGouldToint.Chapter12.corollary_12_2_16`.
* **Theorem 12.2.15** (generalization). The statement holds for $\epsilon \in (0, 1]$, not only for
  $\epsilon \le \frac12$. See `CartisGouldToint.Chapter12.theorem_12_2_15`.
* **Example 12.2.2** (typo). The expansion of $s^2(s - \frac12)^2$ is $\frac14 s^2(1 - 4s) + s^4$,
  the measure is $\phi^1_{m,3}(0) = \frac34$, and the radius threshold is $\frac14$. See
  `CartisGouldToint.Chapter12.example_12_2_2`.
* **Theorem 12.2.17** (reading). "$\epsilon$ sufficiently small" is $\epsilon \le \frac12$. See
  `CartisGouldToint.Chapter12.theorem_12_2_17`.
* **(12.2.78)** (typo). The residual of order $q$ is $\epsilon/k_\epsilon$, not $0$. See
  `CartisGouldToint.Chapter12.theorem_12_2_17`.
* **(12.3.1)** (reading). The decrease is $\Delta T_{f,p}(x_k, s_k)$, with
  $\epsilon_{\min}^{\omega}$ as in (12.3.2). See `CartisGouldToint.Chapter12.ARqpRelaxedStep`.
* **Complexity of the relaxed method of §12.3** (reading). The bounds are stated for every
  $\omega \ge \pi_q$, in terms of $\epsilon_{\min}^{\omega}$. See
  `CartisGouldToint.Chapter12.complexity_arqpSufficientDecrease`.

**Chapter 13**

* **Algorithm 13.1.1, Step 0** (typo). The trust-region update needs
  $0 < \gamma_1 \le \gamma_2 < 1 \le \gamma_3$, printed $0 < \gamma_1 < 1 < \gamma_2 < \gamma_3$.
  See `Optimization.TRqIDAParams`.
* **Algorithm 13.1.1, Step 4** (reading). The run predicate performs Step 1 at every iteration, and
  every run of the source is a run of the predicate. See
  `CartisGouldToint.Chapter13.algorithm_13_1_1`.
* **Lemmas 13.1.1 and 13.1.9** (correction). The printed statements are false for $k = 0$; the bound
  is assumed at $\Delta_{k+1}$ (at $\sigma_{k+1}$). See `CartisGouldToint.Chapter13.lemma_13_1_1`
  and `CartisGouldToint.Chapter13.lemma_13_1_9`.
* **Lemma 13.1.4** (generalization). The lemma holds for every admissible $\kappa_\Delta$, of which
  (13.1.31) is one. See `CartisGouldToint.Chapter13.lemma_13_1_4`.
* **Lemma 13.1.6** (reading). The constant $\bar L_f$, defined only in (13.1.63), is
  $L_f + \kappa_{\nabla,\max} \kappa_h$. See `CartisGouldToint.Chapter13.lemma_13_1_6`.
* **Theorem 13.1.8** (correction). The bound (13.1.39) omits the initial derivative estimate and the
  last accuracy-improving iteration; the constant is $\kappa^F + 2$. See
  `CartisGouldToint.Chapter13.theorem_13_1_8`.
* **Theorem 13.1.8** (typo). The conclusion $\phi^\delta_{f,q}$ reads $\phi^\delta_{f,j}$. See
  `CartisGouldToint.Chapter13.theorem_13_1_8`.
* **Algorithm 13.1.2, Step 0** (reading). The constant $\varsigma \in (0, 1]$ of Step 1 is added to
  the list. See `Optimization.ARqpIDAParams`.
* **Algorithm 13.1.2, Step 2** (correction). The test (13.1.46) must be checked for $i \in [1, p]$
  and for long steps, not only for $i \in [1, q]$ and short steps, and $\sigma_{\max}$ of Lemma
  13.1.14 uses $\max(\kappa_s, \kappa_h)$. See `Optimization.ARqpDAStep` and
  `CartisGouldToint.Chapter13.lemma_13_1_14`.
* **Lemma 13.1.12** (generalization). The lemma holds for every bound $\bar\sigma \ge \sigma_i$,
  $i \le k$. See `CartisGouldToint.Chapter13.lemma_13_1_12`.
* **Radii control (13.1.69)–(13.1.70)** (generalization). The results assume the weaker condition
  `Optimization.RadiiControl`, which the condition of the source implies. See
  `Optimization.RadiiControl.of_unit_le_two`.
* **Lemma 13.1.15** (reading). The radii $\delta_k$ are the radii $\delta^{(1)}_k$ at the end of
  Step 1. See `CartisGouldToint.Chapter13.lemma_13_1_15`.
* **Lemma 13.1.17, $q > 2$** (correction). The constant $\kappa_{\delta,\min}^{j-1}$ is replaced by
  $\hat\kappa^{j-1}$ with $\hat\kappa = \min(\kappa_{\delta,\min}, (1 - \theta) / (2 q! A))$. See
  `CartisGouldToint.Chapter13.lemma_13_1_17`.
* **Lemma 13.1.18** (correction). (13.1.82) holds at the successful iterations whose successor is
  not approximately optimal, with the constant $\hat\kappa$. See
  `CartisGouldToint.Chapter13.lemma_13_1_18`.
* **Theorem 13.1.19** (correction). The proof certifies approximate optimality for some radii in
  $(0, 1]^q$, not for the radius one, which follows for $q \le 2$; $\kappa^C$ misses a factor
  $1 + |\log \gamma_1| / \log \gamma_2$ on a term $1$, and the derivative count needs
  $\kappa^F + 3$. See `CartisGouldToint.Chapter13.theorem_13_1_19_i` and
  `CartisGouldToint.Chapter13.theorem_13_1_19_ii`.
* **Theorem 13.1.19** (reading). For $\kappa_h = 0$, $\kappa^F$ is read with $\log 0 = 0$. See
  `CartisGouldToint.Chapter13.theorem_13_1_19_i`.
* **(13.2.1)** (generalization). The error bound holds for every $h > 0$, not only for
  $h \in (0, 1]$. See `CartisGouldToint.Chapter13.eq_13_2_1`.
* **(13.2.2)** (typo). The number of interpolation points is $d = \sum_{i=0}^p \binom{n+i-1}{i}$,
  not $d + 1$. See `CartisGouldToint.Chapter13.eq_13_2_2_card` and
  `CartisGouldToint.Chapter13.eq_13_2_4_scaled`.
* **Display after (13.2.4)** (generalization). Only the bound at the centre is used, and the points
  need only lie in the closed unit ball. See `CartisGouldToint.Chapter13.eq_13_2_4_scaled`.
* **Theorem 13.2.1, (13.2.5)–(13.2.7)** (typo). The bounds are $O(\max_j \dots)$, printed
  $O(\min_j \dots)$. See `CartisGouldToint.Chapter13.theorem_13_2_1_i` and
  `CartisGouldToint.Chapter13.theorem_13_2_1_ii`.
* **Theorem 13.3.4** (typo). The printed constants $\kappa^B_{\rm TRqEDA}$ and
  $\kappa^C_{\rm TRqEDA}$ are garbled; the proof gives the factor $2$ only. See
  `CartisGouldToint.Chapter13.theorem_13_3_4`.
* **Theorem 13.3.4** (correction). The derivative count omits the initial estimate and the last
  accuracy-improving iteration; the constant is $\kappa^F + 2$. See
  `CartisGouldToint.Chapter13.theorem_13_3_4`.
* **Theorem 13.3.8** (correction). As in Theorem 13.1.19, the derivative-estimate count omits the
  initial estimate and the last accuracy-improving iteration; the constant is $\kappa^F + 3$. See
  `CartisGouldToint.Chapter13.theorem_13_3_8_ii`.
* **Lemma 13.3.5** (correction). The bound $\sigma_{\max}$ needs $\max(\kappa_s, \kappa_h)$ in place
  of $\kappa_s$. See `CartisGouldToint.Chapter13.lemma_13_3_5`.
* **Lemma 13.3.7 and Theorem 13.3.8** (correction). The reused Lemmas 13.1.16–13.1.17 need that
  $x_{k+1}$ is not approximately optimal, which does not follow from non-termination. The corrected
  argument needs $\theta < \varsigma / 2$, with $\varsigma/2 - \theta$ for $1 - \theta$ and
  $4 \kappa_s$ for $3 \kappa_{\nabla,\max} \kappa_s$ in the constants; the orders in $\epsilon$ are
  unchanged. See `CartisGouldToint.Chapter13.lemma_13_3_7`,
  `CartisGouldToint.Chapter13.theorem_13_3_8_i` and `CartisGouldToint.Chapter13.theorem_13_3_8_ii`.

**Chapter 14**

* **Assumption h.S0** (typo). The function $h$ is subadditive on $\mathbb{R}^m$, printed "in
  $\mathbb{R}$". See `CartisGouldToint.Chapter14.AssumptionHS0`.
* **(14.1.2)** (correction). With the componentwise constants of c.D1pL the bound is
  $\|\nabla^j c(x)\| \le \sqrt{m} L_{c,j-1}$; the source omits the factor $\sqrt{m}$. See
  `CartisGouldToint.Chapter14.AssumptionCD1pL.norm_iteratedFDeriv_le`.
* **Lemma 14.1.1** (generalization). The hypothesis h.S0 is not used. See
  `CartisGouldToint.Chapter14.lemma_14_1_1`.
* **Example 14.1.1** (generalization). The measure $\phi^\delta_{w,2}(0)$ vanishes for every
  $\delta \in (0, 3/5]$. See `CartisGouldToint.Chapter14.example_14_1_1`.
* **Lemma 14.1.3** (generalization). The lower bound on the radii also holds, and is needed, for
  $j = 1$ when $h$ or $X$ is not convex. See `CartisGouldToint.Chapter14.lemma_14_1_3`.
* **Lemmas 14.1.4 and 14.1.6** (generalization). Only the smoothness and Lipschitz properties that
  the proofs use are assumed. See `CartisGouldToint.Chapter14.lemma_14_1_4` and
  `CartisGouldToint.Chapter14.lemma_14_1_6`.
* **Lemma 14.1.7** (correction). The factor $(1 - \theta)$ is $(\varsigma - \theta)$, the term in
  $\|s_k\|^{p+1}$ has a factor $2$, and the inequality is strict. See
  `CartisGouldToint.Chapter14.lemma_14_1_7`.
* **(B.14.6)** (typo). Inside the sum over $\ell$, the printed $(p - j + 1)!$ and $\|s_k\|^{p-j+1}$
  are $(p - \ell + 1)!$ and $\|s_k\|^{p-\ell+1}$. See `CartisGouldToint.Chapter14.lemma_14_1_7`.
* **Lemma 14.1.7 and Theorem 14.1.10 (1)** (generalization). The hypothesis h.S0 is not used. See
  `CartisGouldToint.Chapter14.lemma_14_1_7` and `CartisGouldToint.Chapter14.theorem_14_1_10_i`.
* **Lemma 14.1.8** (correction). The second case of (14.1.31) needs the factor
  $\epsilon_j^{(j+1)/(p+1)}$, and $(1 - \theta)$ is $(\varsigma - \theta)$ with
  $\theta < \varsigma$. See `CartisGouldToint.Chapter14.lemma_14_1_8`.
* **Lemma 14.1.9** (correction). The decreases hold at successful iterations that are not followed
  by termination, with $(\varsigma - \theta)$ for $(1 - \theta)$. See
  `CartisGouldToint.Chapter14.lemma_14_1_9`.
* **Lemma 14.1.9** (typo). The source writes $f$ and $L_{f,p}$ for $w$ and $L_{w,p}$. See
  `CartisGouldToint.Chapter14.lemma_14_1_9`.
* **Lemma 14.1.9 and Theorem 14.1.10 (2)** (generalization). Any positive lower bound of
  $\min_j \epsilon_j^{j+1}$ can be used, and Theorem 14.1.10 (2) also holds when $h$ is convex and
  $q = 1$. See `CartisGouldToint.Chapter14.lemma_14_1_9` and
  `CartisGouldToint.Chapter14.theorem_14_1_10_ii`.
* **Theorem 14.1.10** (correction). In the constants, $(1 - \theta)$ is $(\varsigma - \theta)$ with
  $\theta < \varsigma$. See `CartisGouldToint.Chapter14.theorem_14_1_10_i` and
  `CartisGouldToint.Chapter14.theorem_14_1_10_ii`.
* **Theorem 14.1.10 (2)** (typo). The factor $3j!$ in the constant is $3q!$. See
  `CartisGouldToint.Chapter14.theorem_14_1_10_ii`.
* **Theorem 14.1.10** (reading). The radius policies that the source assumes are proved for every
  run; part (1) needs $\delta_{0,1} = 1$. See
  `CartisGouldToint.Chapter14.algorithm_14_1_1.radius_policy`.
* **Corollary 14.1.11** (generalization). The statement holds for every $\sigma_0$ and every
  $\epsilon \in (0, 1]$. See `CartisGouldToint.Chapter14.corollary_14_1_11`.
* **Theorem 14.2.1** (generalization). The Lipschitz condition is needed only on the closed ball of
  radius $\delta_j$, and $X$ closed and nonempty, $\delta_j \le 1$ and $\epsilon_j \le 1$ are not
  needed. See `CartisGouldToint.Chapter14.theorem_14_2_1`.
* **Theorem 14.2.1, (14.2.6)** (typo). The printed $\delta^j$ is $\delta_j^j$. See
  `CartisGouldToint.Chapter14.theorem_14_2_1`.
* **Theorem 14.2.1, radius condition** (reading). The condition
  $\|d\| \le (j+1)\epsilon_j / L_{f,j}$ is used as $L_{f,j} \|d\| \le (j+1)\epsilon_j$. See
  `CartisGouldToint.Chapter14.theorem_14_2_1`.
* **(14.2.18)–(14.2.19)** (typo). The printed $\max \ell(d)$ is the minimum of
  $\ell(d) = \langle \nabla f(x), d \rangle$. See `CartisGouldToint.Chapter14.sparseMeasure_eq`.
* **Lemma 14.2.5** (generalization). The hypothesis $\|x\|_0 \le n_{\mathrm{nz}}$ is not needed. See
  `CartisGouldToint.Chapter14.lemma_14_2_5`.
* **Lemma 14.2.2, TRq-SC row of (14.2.12)** (correction). The printed $\pi_j = j + 1$ is false per
  iteration for $q = 2$; the TR rows use $\pi_j = q + 1$. See
  `CartisGouldToint.Chapter14.lemma_14_2_2_trq` and
  `CartisGouldToint.Chapter14.lemma_14_2_2_trq_printed_false_uniform`.
* **Lemma 14.2.2, ARqpIDA-SC row** (correction). The decrease holds at the successful iterations
  that are followed by an iterate that is not approximately optimal. See
  `CartisGouldToint.Chapter14.lemma_14_2_2_arqpida`.
* **Lemma 14.2.2, ARqpEDA-SC row** (correction). The decrease needs $\theta < \varsigma/2$ and holds
  at the successful iterations of Lemma 13.3.7. See
  `CartisGouldToint.Chapter14.lemma_14_2_2_arqpeda`.
* **Lemma 14.2.3** (reading). The constants are explicit, with $|\log \epsilon_{\min}|$ terms; for
  the IDA methods the bound holds up to the first approximately optimal iterate. See
  `CartisGouldToint.Chapter14.lemma_14_2_3_trq` and
  `CartisGouldToint.Chapter14.lemma_14_2_3_trqida`.
* **Lemma 14.2.2 and Theorem 14.2.4, ARqp-SC rows** (reading). The rows are stated by radii mode,
  while the table keys them by $(q, X)$. See `CartisGouldToint.Chapter14.lemma_14_2_2_arqp`.
* **Lemma 14.2.2 and Theorem 14.2.4, ARqpIDA-SC and ARqpEDA-SC rows** (reading). The rows are stated
  by the mode of `Optimization.ARqpDARadiiControl`; on $\mathbb{R}^n$ with $q \le 2$ every ARqpIDA
  run attains the unit-radii bound in either mode. See
  `CartisGouldToint.Chapter14.theorem_14_2_4_arqpida_le_two`.
* **Theorem 14.2.4, sharpness of the TRqIDA-SC and TRqEDA-SC rows** (reading). The slow example of
  Theorem 12.2.6 is a run of these methods only for suitable constants, and TRqEDA is run on $f/2$.
  See `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_trqida` and
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_trqeda`.
* **Theorem 14.2.4, sharpness of the ARqpIDA-SC and ARqpEDA-SC rows** (reading). The slow runs of
  Chapter 12 are adapted: smaller Step-1 radii or weights, $f/2$ for ARqpEDA, and suitable initial
  accuracies. See `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida` and
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpeda`.
* **Theorem 14.2.4, sharpness of the "otherwise" entries** (correction). The reduction of the source
  to $X = \mathbb{R}^n$ does not reach these entries for $q = 2$ and $X \neq \mathbb{R}^n$; they are
  shown on closed nonconvex sets. See
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqp_otherwise` and
  `CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida_otherwise_constrained`.
* **Theorem 14.3.1** (correction). With arcs that only stay in $X$ the theorem is false
  ($X = \mathbb{R}^2$, $c(x) = x_1^2 + x_2^2$, $f(x) = -x_1$, $x_\star = 0$); the arcs stay in
  $X \cap \{c = 0\}$, and X.CQ is then not needed. See `CartisGouldToint.Chapter14.theorem_14_3_1`.
* **Example 14.3.1** (correction). The origin is a minimizer, not a saddle point, with the
  multiplier $y_0 = (-1, 0)$. See `CartisGouldToint.Chapter14.example_14_3_1`.
* **Theorem 14.3.2** (typo). The "neighbourhood of diameter $\delta_j$" is the closed ball of radius
  $\delta_j$. See `CartisGouldToint.Chapter14.theorem_14_3_2`.
* **Theorem 14.3.3** (typo). The iteration bound needs a ceiling. See
  `CartisGouldToint.Chapter14.theorem_14_3_3`.
* **Theorem 14.3.4, Lemma 14.3.7 and Theorem 14.3.9** (correction). The proofs use the false
  inequality $\sum_k \max_j \le \max_j \sum_k$; the bounds hold with $\sum_j$ in place of $\max_j$.
  See `CartisGouldToint.Chapter14.theorem_14_3_4` and `CartisGouldToint.Chapter14.lemma_14_3_7`.
* **(14.3.20)–(14.3.21)** (correction). The multiplicative cost contract fails for INNER = ARqp-SC
  with $q = 1$, $p \ge 2$, and for every INNER that spends at least one evaluation per call when
  every $\pi_j < 2$. It holds for ARqp-SC with the exponents $j + 1$ and, for LENq-SC calls, with
  $j(p+1)/p$ when $q \ge 2$; an additive form holds in all cases and is used. See
  `CartisGouldToint.Chapter14.exists_algorithm_14_3_1_cost_contract_counterexample`,
  `CartisGouldToint.Chapter14.IsARqpSCOutputCost.cost_le_anchored` and
  `CartisGouldToint.Chapter14.theorem_14_3_4_add`.
* **Lemma 14.3.5** (correction). The bounds (14.3.43) and (14.3.46) are false; they hold with extra
  terms such as $(\|\nabla f\| \delta)^2 / (2 (f(x_\epsilon) - t_\epsilon))$. See
  `CartisGouldToint.Chapter14.lemma_14_3_5` and
  `CartisGouldToint.Chapter14.lemma_14_3_5_counterexample`.
* **Lemma 14.3.6** (typo). (14.3.63) bounds $\nabla^j \mu$, not $\nabla^j \nu$. See
  `CartisGouldToint.Chapter14.lemma_14_3_6_ii`.
* **Lemma 14.3.8** (correction). The decreases that its proof uses do not bound the bad outer
  iterations; the lemma counts them separately. See `CartisGouldToint.Chapter14.lemma_14_3_8` and
  `CartisGouldToint.Chapter14.lemma_14_3_8_proof_gap_counterexample`.
* **Theorem 14.3.9, nonspecific INNER** (correction). Under the per-call reading of its INNER
  hypotheses the theorem is false, and under the uniform reading it is vacuous for $\pi_1 < 2$. It
  is proved for an INNER that satisfies Lemma 14.2.2 as stated with radii bounded below, with an
  extra term $O(\epsilon_0^{-1} + \max_j (\epsilon_0 \epsilon_j \rho_j^{j-1})^{-1})$. See
  `CartisGouldToint.Chapter14.theorem_14_3_9`, `CartisGouldToint.Chapter14.theorem_14_3_9_false` and
  `CartisGouldToint.Chapter14.theorem_14_3_9_cost_hypothesis_unsatisfiable`.
* **Theorem 14.3.9, INNER = ARqp-SC** (correction). The printed order holds for the exponents
  $j + 1$ and, with $j(p+1)/p$, for $q = p$; for $q < p$ the extra term is outside the printed
  order, and for $q = 1$, $p \ge 4$ and $q = 2$, $p \ge 5$ the printed theorem fails for runs that
  re-initialize $\mu$ at Step 2.1 of Algorithm 14.1.2. See
  `CartisGouldToint.Chapter14.theorem_14_3_9_arqpc`,
  `CartisGouldToint.Chapter14.theorem_14_3_9_arqp` and
  `CartisGouldToint.Chapter14.theorem_14_3_9_arqp_printed_false`.
* **Theorem 14.3.9, INNER = TRq-SC** (correction). The theorem holds with $\pi_j = q + 1$ and a
  factor $1 + |\log(\epsilon_0 \epsilon_{\min})|$ on the function evaluations, which is needed for
  $q = 1$; the printed order fails for every $q \ge 2$. See
  `CartisGouldToint.Chapter14.theorem_14_3_9_trq`,
  `CartisGouldToint.Chapter14.theorem_14_3_9_trq_log_necessary` and
  `CartisGouldToint.Chapter14.theorem_14_3_9_trq_printed_false`.
* **Algorithm 14.3.2** (reading). The INNER calls of Phase 2 are described by their iterates; with
  INNER = ARqp-SC the radii returned at a Step-2 termination certify (14.3.19), which the radii
  $\delta_{s_k}$ of the book need not. See `CartisGouldToint.Chapter14.IsTPqpGCPhase2` and
  `CartisGouldToint.Chapter14.IsARqpSCCallOut`.
* **Algorithm 14.3.2, (14.3.31)** (reading). Phase 1 ends with $\|c(x_1)\| \le \theta \epsilon_0$,
  printed with $<$. See `CartisGouldToint.Chapter14.algorithm_14_3_2`.
* **Assumption f.D1qLB.Fb** (reading). The book uses it for the trust-region case without a
  definition; f.D1qLB.X is used. See `CartisGouldToint.Chapter14.theorem_14_3_9_trq`.

**Appendix A**

* **Theorem A.8.1** (reading). The conditions $k \ge 1$ and $h \ge 0$, implicit in the book, are
  hypotheses. See `CartisGouldToint.AppendixA.theorem_A_8_1`.
* **Theorem A.8.2** (correction). The point $\xi$ lies strictly between $t$ and $t + h$ only under
  the added hypothesis $h \neq 0$. See `CartisGouldToint.AppendixA.theorem_A_8_2`.
* **Theorem A.8.3, proof of (A.15)** (typo). The proof displays the constant
  $(p-j+1)!/(p-j+\beta)!$; the constant of the statement is proved. See
  `CartisGouldToint.AppendixA.theorem_A_8_3`.
* **Theorem A.8.5** (correction). The added hypothesis $L \ge 0$ is needed: on $\mathbb{R}^0$ with
  $L < 0$ the Lipschitz condition holds and (A.21) fails. See
  `CartisGouldToint.AppendixA.theorem_A_8_5`.
* **Theorem A.9.2** (generalization). The unused hypothesis $p > 0$ is dropped. See
  `CartisGouldToint.AppendixA.theorem_A_9_2`.
* **Theorem A.9.2** (reading). The hypothesis $s_k > 0$ "for $k \in [0 : k_e]$" is read for
  $k < k_e$. See `CartisGouldToint.AppendixA.theorem_A_9_2`.
* **Theorem A.9.2** (typo). The derivative bound "for all $x \in \mathbb{R}^n$" is for all
  $x \in \mathbb{R}$. See `CartisGouldToint.AppendixA.theorem_A_9_2`.

**Appendix B**

* **Lemma B.2.1** (correction). The bound on the interpolant and its derivatives also needs
  $|f_0|, |g_0|, |H_0| \le \kappa_f$. See `CartisGouldToint.AppendixB.lemma_B_2_1_bound`.
* **Corridor function (B.2.19) and Lemma B.2.6** (correction). With the bounded corridor function of
  the book the first minimizer along the ray is only local; a capped square makes it global, so that
  the example of Theorem 2.2.5 realizes the global exact linesearch (2.2.26). See
  `Optimization.ZigZag.f₂` and `CartisGouldToint.AppendixB.lemma_B_2_6`.
* **Lemma B.2.3** (generalization). The bound on $f_2$ holds on the larger bands
  $|y - y_{\mathrm{mid}}(x)| \le 2$, and the bounds on its derivatives on all of $\mathbb{R}^2$. See
  `CartisGouldToint.AppendixB.lemma_B_2_3`.
* **Data (B.2.5)–(B.2.6)** (correction). The step length $\epsilon + \omega_k$ vanishes at
  $k = 2k_\epsilon$; $y_{\mathrm{mid}}$ is kept constant after $x_{k_\epsilon}$. See
  `Optimization.zigZagFunction`.
* **Lemma B.4.1, (B.4.3)** (correction). The equality is false for $\beta \in (0, 1)$ ($n = 2$,
  $p = 1$, $\beta = 1/2$, $s = e_1$); the printed value is the radial value and a lower bound, and
  it is correct for $\beta = 1$, the case that the book uses. See
  `CartisGouldToint.AppendixB.lemma_B_4_1_iii_false` and
  `CartisGouldToint.AppendixB.lemma_B_4_1_iii`.
* **Lemma B.4.1, convexity** (reading). The convexity claims are proved for $s \neq 0$, or for
  $s = 0$ when $j \le p$, and for orders $j \le p + 1$. See
  `CartisGouldToint.AppendixB.lemma_B_4_1_iv`.
* **Lemma B.5.1** (typo). The third exponent of the statement is $\iota_3$, printed $\iota_1$, and
  the proof writes $\iota_1$ for $\iota_2$ and $\iota_3$. See
  `CartisGouldToint.AppendixB.lemma_B_5_1`.
* **Lemma B.5.1** (reading). The conditions $i > \log_2 p$, $i > \log_2(p - 1)$, $i > \log_2(p - 2)$
  are written $p < 2^i$, $p - 1 < 2^i$, $p - 2 < 2^i$. See `CartisGouldToint.AppendixB.lemma_B_5_1`.
* **Lemma B.7.1** (generalization). The uniqueness of the global minimizer $(\omega, 0)$ is also
  proved. See `CartisGouldToint.AppendixB.lemma_B_7_1`.
* **Lemma B.8.1** (correction). The hypothesis $\theta'(\lambda^*) \neq 0$ is added; otherwise
  Newton's method converges only linearly. See `CartisGouldToint.AppendixB.lemma_B_8_1`.
* **Lemma B.8.1, concave case** (correction). The starting condition is $\theta(\lambda_0) < 0$, and
  $\theta(\lambda_1) < 0$ for the secant method, printed $> 0$. See
  `CartisGouldToint.AppendixB.lemma_B_8_1_concave`.
* **Lemma B.8.1, (B.8.3)** (typo). The tangent inequality is printed reversed. See
  `CartisGouldToint.AppendixB.lemma_B_8_1`.
* **Lemma B.8.1, monotonicity** (correction). The iterates increase monotonically but in general not
  strictly. See `CartisGouldToint.AppendixB.lemma_B_8_1`.
* **Lemma B.8.2** (reading). The unused hypothesis that $\lambda^*$ is the root of
  $\pi(\lambda) = \Delta^2$ is dropped, and $g \neq 0$ is stated. See
  `CartisGouldToint.AppendixB.lemma_B_8_2`.
* **(B.10.4)** (reading). The norm $\|M^{-1/2} H M^{-1/2}\|$ is the operator norm of $M^{-1}H$
  induced by $\|\cdot\|_M$; the Euclidean operator norm is only an upper bound. See
  `CartisGouldToint.AppendixB.lemma_B_10_1`.
* **Lemma B.12.1** (generalization). Neither $H$ nor the trilinear form $T$ need be symmetric, and
  the radius $\Delta$ is arbitrary. See `CartisGouldToint.AppendixB.lemma_B_12_1`.

## Not formalized

**Chapter 1**

* **The tensor-product notation (1.1.2).** `iteratedFDeriv` applied to vectors is used instead.
* **(1.1.10)–(1.1.12) and (1.1.19)**, the equivalent forms with a minimum over
  $\mathcal{C}(x^*) \cap \{\|d\| \le 1\}$.
* **The projection form of (1.1.6)**, $\|P_{\mathcal{C}}[x^* - \nabla f(x^*)] - x^*\| = 0$.
* **The reduced-Hessian form of (1.1.14)–(1.1.15).**
* **The hardness remarks** on the optimality conditions.

**Chapter 2**

* **The one-dimensional example of §2.1** showing that f.Bb and f.C1 alone admit no complexity
  bound. It is discussion, not a numbered result.
* **The variants of §§2.2.3.1–2.2.3.3 and §2.2.3.5**: the flexible Armijo condition, the
  Goldstein–Armijo conditions, Nesterov's view and nonmonotone methods. These sections contain no
  numbered results.
* **The relaxed Cauchy condition (2.3.8).** TR1 runs use (2.3.4).

**Chapter 4**

* **§4.1.3 ("A TRp algorithm?").** It contains no numbered statement and defines no algorithm.

**Chapter 5**

* **The remark of §5.2** that partially separable models can be used in trust-region and
  adaptive-regularization methods without a change of their complexity bounds. It is a statement
  about the inputs of those algorithms.
* **The structured trust regions and the element-wise regularizations** of the Notes.
* **The examples of §5.3.1 other than full-rank least squares**: convex functions on a ball,
  strongly convex functions, and $\|x\|^{2i}$.
* **The claim that TR1 and TR2 belong to $\mathrm{TR}_{\psi,\nu}$ with uniform constants.**

**Chapter 6**

* **The remarks of §6.1** on the continuity of $\omega_{f,\mathcal{C},2}(x, 0)$, on computational
  cost, and on norms other than the Euclidean norm.

**Chapter 7**

* **The heuristic perturbation argument after (7.1.5)**, with footnote 52, that motivates the
  scaling by $\|(y, 1)\|$.
* **§7.2.3**, the discussion of penalty, augmented Lagrangian, barrier and SQP methods. It has no
  numbered results.

**Chapter 9**

* **The safeguarded update (9.3.10)–(9.3.12) and the overall procedure of §9.3.7.** They are
  heuristics; their admissible choices are covered by `CartisGouldToint.Chapter09.algorithm_9_2_1`.
* **The closing advice of §9.4.2** to stop Algorithm 9.2.1 as soon as (9.4.3) or (9.4.4) holds. It
  is a heuristic use of the tests; the sufficient conditions that it relies on are
  `CartisGouldToint.Chapter09.test_9_4_3_of_9_4_6`, `CartisGouldToint.Chapter09.test_9_4_4_of_9_4_6`
  and `CartisGouldToint.Chapter09.test_9_4_3_of_9_4_7`.
* **The Gertz–Gill criterion (9.4.8) of the Notes.** The source quotes it without saying what a
  "suitable approximate solution" is.

**Chapter 11**

* **The practical update rules (11.2.1)–(11.2.2).** They are parameter choices for the algorithms of
  Chapter 3.
* **The remarks on Krylov and LSQR methods in §11.3.**

**Chapter 12**

* **The weak approximate minimizers (12.1.40)** of the Notes.
* **The projected-norm relaxation (12.1.24).**
* **The asymptotic $O(\epsilon_2)$ remark after Theorem 12.1.6.**
* **The discussion of §12.1.6.**
* **The $O(\cdot)$ restatements of the complexity bounds and Table 12.2.1.**
* **The qualitative discussion of §12.3** of the premature termination of Algorithm 12.2.3 and of
  the practicality of global polynomial minimization.

**Chapter 13**

* **The derivative-free discussion of §13.2.**
* **The $O(\cdot)$ restatements** of the complexity bounds.

**Chapter 14**

* **The Key Definition of simple constraints after Theorem 14.2.1.** It is a convention on the cost
  of the oracles, not a mathematical property: the evaluation counts never charge the subproblems.
* **Theorem 14.2.4, sharpness of the "otherwise" entry of the ARqpIDA-SC row on $X = \mathbb{R}^n$
  for $3 \le q < p$.** The entry is shown with a feasible set $X \neq \mathbb{R}^n$
  (`CartisGouldToint.Chapter14.theorem_14_2_4_sharp_arqpida_otherwise_constrained`), but the
  reduction of the source to $X = \mathbb{R}^n$ would also need this case.
* **Theorem 14.2.4, ARqp-SC row under the anchored assumptions, existence of runs on a general
  $X$.** The radius hypothesis of `CartisGouldToint.Chapter14.theorem_14_2_4_arqp_anchored` in the
  mode in which the unit radii fail is not discharged for the runs on a general closed $X$.
* **The $O(\cdot)$ restatements of Theorems 14.3.4 and 14.3.9.** The bounds are stated with
  constants chosen before $\epsilon$.
* **Theorem 14.3.9 with INNER = ARqp-SC in the printed order** for $q = 1 < p \le 3$,
  $q = 2 < p \le 4$ and $3 \le q < p$, for runs whose $\mu$ at Step 2.1 is bounded below, and with
  unit radii for $q < p$.
* **Theorem 14.3.9 with INNER = TRq-SC**: whether the logarithmic factor is needed for $q \ge 2$.
* **TRqIDA-SC and TRqEDA-SC as INNER** in Theorem 14.3.9.

**Appendix A**

* **(A.12)**, the Taylor expansion with the Peano remainder. The backbone module
  `Numlib.Analysis.Calculus.MultivariateTaylor.Peano` proves it for $f$ of class $C^n$ at $x$, while
  the book assumes only that $f$ is $n$ times differentiable at $x$.
-/
