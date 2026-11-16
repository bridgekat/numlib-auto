/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter02
import NumlibSurface.ConnGouldToint.Chapter03
import NumlibSurface.ConnGouldToint.Chapter04
import NumlibSurface.ConnGouldToint.Chapter05
import NumlibSurface.ConnGouldToint.Chapter06
import NumlibSurface.ConnGouldToint.Chapter07
import NumlibSurface.ConnGouldToint.Chapter08
import NumlibSurface.ConnGouldToint.Chapter09
import NumlibSurface.ConnGouldToint.Chapter10
import NumlibSurface.ConnGouldToint.Chapter11
import NumlibSurface.ConnGouldToint.Chapter12
import NumlibSurface.ConnGouldToint.Chapter13
import NumlibSurface.ConnGouldToint.Chapter14
import NumlibSurface.ConnGouldToint.Chapter15
import NumlibSurface.ConnGouldToint.Chapter16
import NumlibSurface.ConnGouldToint.Chapter17

/-!
# Conn, Gould and Toint, *Trust-Region Methods*

This library formalizes the book *Trust-Region Methods* by Andrew R. Conn, Nicholas I. M. Gould and
Philippe L. Toint [conn2000trust], published in 2000 in the MPS/SIAM Series on Optimization. The
book develops trust-region methods for unconstrained and constrained optimization, together with
methods for solving the trust-region subproblem and applications to nonlinear equations. At each
iteration such a method minimizes a model $m_k$ of the objective $f$ in a trust region
$\|s\| \le \Delta_k$ around the iterate $x_k$, and it accepts the step and updates the radius
according to the ratio $\rho_k = (f(x_k) - f(x_k + s_k)) / (m_k(x_k) - m_k(x_k + s_k))$ of actual to
predicted decrease. The library covers the background material of Chapters 2–5 (eigenvalues, norms,
optimality conditions, linear algebra and Krylov methods), the convergence theory of the basic
algorithm in Chapters 6 and 8, the subproblem in Chapter 7, conditional and derivative-free models
in Chapter 9, algorithmic extensions in Chapter 10, nonsmooth problems in Chapter 11, convex
constraints in Chapter 12, barrier, penalty and SQP methods in Chapters 13–15, nonlinear equations
and fitting in Chapter 16, and the practical choices of Chapter 17. Many printed statements are
corrected, usually together with an explicit counterexample to the printed statement. The proofs use
the backbone areas `Numlib.Optimization` (trust-region subproblems, model-based methods, optimality
conditions, barriers and penalties), `Numlib.Krylov` (conjugate gradients and the Lanczos method),
`Numlib.LinearAlgebra.Matrix`, `Numlib.Eigen`, `Numlib.Analysis` and `Numlib.Nonlinear`.

## Coverage

The library formalizes the numbered theorems, lemmas, corollaries and algorithms of Chapters 2–17,
the numbered equations and assumptions that their statements use, and some statements that the
source makes in its prose, such as the claim before (2.2.6). Where a printed statement is false, the
library proves a corrected statement and usually also a counterexample to the printed one. The
source has more units than the library has modules: Chapter 1 and Sections 2.1, 6.2, 7.1, 7.6, 8.2,
13.5 and 13.8 have no module of their own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §2.2 Eigenvalues and eigenvectors | `Chapter02.Section02` | (2.2.1)–(2.2.8), Gershgorin discs |
| §2.3 Vector and matrix norms | `Chapter02.Section03` | (2.3.1)–(2.3.6) |
| §3.1 Basic real analysis | `Chapter03.Section01` | Theorems 3.1.1–3.1.6, (3.1.4), (3.1.7) |
| §3.2 Optimality conditions | `Chapter03.Section02` | Theorem 3.2.1 to Theorem 3.2.15 |
| §3.3 Sequences and basic iterations | `Chapter03.Section03` | §3.3.1, Theorems 3.3.1–3.3.2 |
| §4.1 Linear equations in optimization | `Chapter04.Section01` | (4.1.1)–(4.1.3) |
| §4.2 Special matrices | `Chapter04.Section02` | orthonormal matrices (4.2.1) |
| §4.3 Direct methods for solving linear systems | `Chapter04.Section03` | (4.3.1)–(4.3.9) |
| §4.4 Least-squares problems and projections | `Chapter04.Section04` | (4.4.1)–(4.4.14) |
| §5.1 Conjugate gradients | `Chapter05.Section01` | Lemma 5.1.1 to Corollary 5.1.9 |
| §5.2 The Lanczos basis | `Chapter05.Section02` | Lemma 5.2.1, Algorithms 5.2.1–5.2.4 |
| §5.3 Linear least-squares problems | `Chapter05.Section03` | Algorithm 5.3.1, Theorem 5.3.1 |
| §5.4 Problems with linear constraints | `Chapter05.Section04` | Algorithms 5.4.1–5.4.2 |
| §6.1 The basic algorithm | `Chapter06.Section01` | Algorithm 6.1.1, (6.1.2)–(6.1.7) |
| §6.3 The Cauchy point of a quadratic model | `Chapter06.Section03` | Theorems 6.3.1, 6.3.3–6.3.5 |
| §6.4 Convergence to first-order critical points | `Chapter06.Section04` | Theorems 6.4.1–6.4.6 |
| §6.5 Asymptotically convex models | `Chapter06.Section05` | Lemma 6.5.1 to Theorem 6.5.5 |
| §6.6 Exploiting negative curvature | `Chapter06.Section06` | Theorem 6.6.1 to Theorem 6.6.8 |
| §6.7 Variable scaling | `Chapter06.Section07` | Theorem 6.7.1 |
| §7.2 The Euclidean model minimizer | `Chapter07.Section02` | Theorem 7.2.1, Corollary 7.2.2 |
| §7.3 The Moré–Sorensen method | `Chapter07.Section03` | Lemma 7.3.1 to Lemma 7.3.6 |
| §7.3 Separate safeguards | `Chapter07.Section03Algorithms` | Algorithms 7.3.2, 7.3.3, 7.3.6 |
| §7.3.7 The LINPACK direction | `Chapter07.Section03Direction` | §7.3.7, (7.3.16)–(7.3.17) |
| §7.3 LINPACK matrix certificates | `Chapter07.Section03Matrix` | Theorem 7.3.4, hard case |
| §7.3.7 Cholesky pivot detection | `Chapter07.Section03Cholesky` | Algorithm 7.3.4, (7.3.17) |
| §7.3 One-sided stabilization | `Chapter07.Section03HardLimit` | Theorem 7.3.4, hard case |
| §7.4 The scaled Euclidean trust-region problem | `Chapter07.Section04` | Theorem 7.4.1 |
| §7.5 Truncated CG and Lanczos | `Chapter07.Section05` | Theorem 7.5.1 to Theorem 7.5.17 |
| Algorithm 7.5.2 Generalized Lanczos | `Chapter07.Section05Algorithm` | Algorithm 7.5.2 |
| §7.7 The diagonal trust-region Newton iteration | `Chapter07.Section07` | Algorithm 7.7.1 |
| §8.1 Iteration-dependent norms | `Chapter08.Section01` | Lemma 8.1.1 to Theorem 8.1.12 |
| §8.3 Rayleigh infima in Hilbert spaces | `Chapter08.Section03` | (8.3.3) |
| §8.4 Approximate derivatives | `Chapter08.Section04` | Lemma 8.4.1, Theorems 8.4.2–8.4.8 |
| §8.5 Composite objective functions | `Chapter08.Section05` | Theorems 8.5.1–8.5.2 |
| §9.1 Conditional models | `Chapter09.Section01` | Theorem 9.1.1, Lemma 9.1.2(i), (iii) |
| §9.2 First-order convergence | `Chapter09.Section02` | Lemma 9.1.2(ii), Theorem 9.2.1 to 9.2.6 |
| §9.3 Second-order convergence | `Chapter09.Section03` | Algorithm 9.3.1, Theorems 9.3.1, 9.3.3 |
| §9.4 Newton interpolation | `Chapter09.Section04` | Algorithms 9.4.1–9.4.2, Theorems 9.4.1–9.4.4 |
| §9.4 Incomplete quadratic blocks | `Chapter09.InterpolationCounterexample` | Theorem 9.4.4 |
| §9.5 Conditional models with memory | `Chapter09.Section05` | Theorems 9.5.1–9.5.2 |
| §10.1 Nonmonotone method | `Chapter10.Section01` | Lemma 10.1.1 to Theorem 10.1.4 |
| §10.2 Structured trust regions | `Chapter10.Section02` | Lemma 10.2.1 to Theorem 10.2.6 |
| §10.3 Backtracking directions | `Chapter10.Section03` | Algorithm 10.3.1, Theorems 10.3.1–10.3.4 |
| §10.3 The backtracking trust-region algorithm | `Chapter10.Backtracking` | Algorithm 10.3.2 |
| §10.4 Corrected steps | `Chapter10.Section04` | Algorithm 10.4.1, Theorems 10.4.1–10.4.3 |
| §10.5 Radius management | `Chapter10.Section05` | Algorithm 10.5.1, (10.5.1)–(10.5.8) |
| §10.6 Dynamic accuracy | `Chapter10.Section06` | Algorithm 10.6.1, Lemma 10.6.1 |
| §11.1 Nonsmooth steepest descent | `Chapter11.Section01` | Lemma 11.1.1 to Corollary 11.1.4 |
| §11.2 Normalized model error | `Chapter11.Section02` | Lemmas 11.2.1–11.2.4, Theorem 11.2.5 |
| §11.3 Corrected steps | `Chapter11.Section03` | Algorithm 11.3.1, Theorems 11.3.1–11.3.2 |
| §11.4 Residual penalties | `Chapter11.Section04` | Theorem 11.4.1 to Theorem 11.4.3 |
| §11.5 Taylor models of composites | `Chapter11.Section05` | Theorem 11.5.1 |
| §12.1 The projected-gradient path | `Chapter12.Section01` | Theorems 12.1.1–12.1.6 |
| §12.2 Cauchy decrease | `Chapter12.Section02` | Algorithm 12.2.2, Theorems 12.2.1–12.2.2 |
| §12.3 Active constraints | `Chapter12.Section03` | Lemma 12.3.1 to Corollary 12.3.9 |
| §12.3 Cauchy active sets | `Chapter12.Section03Counterexample` | Theorem 12.3.8 |
| §12.3 Remote active set | `Chapter12.Section03ConstraintExample` | constraints of an example |
| §12.3 Iterates | `Chapter12.Section03IterateCounterexample` | Lemma 12.3.7, Theorem 12.3.8 |
| §12.4 Models on an identified face | `Chapter12.Section04` | Lemma 12.4.1 to Theorem 12.4.6 |
| §13.1 The logarithmic barrier | `Chapter13.Section01` | Algorithm 13.1.1, (13.1.1)–(13.1.2) |
| §13.2 First inner algorithm | `Chapter13.Section02` | Algorithm 13.2.1, Theorems 13.2.1–13.2.3 |
| §13.3 Cauchy and eigenpoints | `Chapter13.Section03` | Algorithm 13.3.1, Theorems 13.3.1, 13.3.3 |
| §13.4 Barrier model | `Chapter13.Section04` | Algorithm 13.4.1, Lemma 13.4.1 to Corollary 13.4.4 |
| §13.6 Primal-dual methods | `Chapter13.Section06` | Lemma 13.6.1 to Theorem 13.6.4 |
| §13.7 Scaling of barrier methods | `Chapter13.Section07` | Theorems 13.7.1–13.7.3 |
| §13.9 General inequalities | `Chapter13.Section09` | Algorithms 13.9.1–13.9.2, Theorem 13.9.1 |
| §13.10 Affine slices of the orthant | `Chapter13.Section10` | Algorithm 13.10.1, Theorem 13.10.2 |
| §13.11 Affine scaling | `Chapter13.Section11` | Algorithm 13.11.1, Theorem 13.11.1 |
| §13.12 Coleman–Li scaling | `Chapter13.Section12` | Theorems 13.12.1–13.12.6, two algorithms |
| §14.1 Penalty methods: motivation and notation | `Chapter14.Section01` | AW.1, (14.1.4) |
| §14.2 Quadratic penalty, augmented Lagrangian | `Chapter14.Section02` | Lemmas 14.2.1–14.2.2 |
| §14.3 Quadratic penalty methods | `Chapter14.Section03` | Theorem 14.3.1, Lemma 14.3.2 |
| §14.4 Augmented Lagrangian methods | `Chapter14.Section04` | Lemma 14.4.1 to Theorem 14.4.7 |
| §14.5 Nonsmooth exact penalties | `Chapter14.Section05` | Theorems 14.5.1–14.5.2 |
| §14.6 Smooth exact penalties | `Chapter14.Section06` | Theorem 14.6.1 |
| §15.1 The nonlinear programs of SQP | `Chapter15.Section01` | (15.1.1)–(15.1.2) |
| §15.2 Local convergence of SQP | `Chapter15.Section02` | Theorems 15.2.1–15.2.2 |
| §15.3 SQP with an exact penalty | `Chapter15.Section03` | Theorem 15.3.1 to Theorem 15.3.7 |
| §15.4 Relaxed linearization SQP | `Chapter15.Section04` | Lemma 15.4.1 to Lemma 15.4.21 |
| §15.4 Relaxed SQP algorithms | `Chapter15.RelaxedSQP` | Algorithms 15.4.1–15.4.4 |
| §15.4 Trial segments | `Chapter15.TrialSegmentCounterexample` | counterexample for Lemma 15.4.3 |
| §15.4 Corrections | `Chapter15.Corrections` | Lemmas 15.4.13–15.4.14, Theorem 15.4.15 |
| §15.4 SQP variants | `Chapter15.SQPVariants` | Algorithms 15.4.5–15.4.8 |
| §15.4 Byrd–Omojokun SQP convergence | `Chapter15.ByrdOmojokun` | Theorems 15.4.22–15.4.25 |
| §15.5 Filter SQP methods | `Chapter15.Section05` | Lemma 15.5.1 to Theorem 15.5.14 |
| §15.5 The filter SQP algorithms | `Chapter15.FilterAlgorithm` | Algorithms 15.5.1–15.5.2 |
| §16.1 Nonlinear equations and least squares | `Chapter16.Section01` | Theorems 16.1.1–16.1.4 |
| §16.2 Composite problems | `Chapter16.Section02` | Algorithm 16.2.1, Theorems 16.2.1–16.2.2 |
| §16.3 Complementarity problems | `Chapter16.Section03` | Theorem 16.3.1 |
| §17.1 Practical trust-region parameters | `Chapter17.Section01` | (17.1.1)–(17.1.4) |
| §17.2 The initial radius | `Chapter17.Section02` | Algorithm 17.2.1, (17.2.1)–(17.2.14) |
| §17.3 The generalized Cauchy point on a box | `Chapter17.Section03` | Algorithm 17.3.1 |
| §17.4 Model decrease and stopping residuals | `Chapter17.Section04` | (17.4.1)–(17.4.9) |

## Conventions

* The declarations for Chapter $N$ are in the namespace `ConnGouldToint.ChapterNN`, for example
  `ConnGouldToint.Chapter06`. The constraints of one example of Section 12.3 are in
  `ConnGouldToint.Chapter12.ConstraintExample`.
* A numbered item has a name formed from its kind and number: Theorem 6.4.3 is
  `ConnGouldToint.Chapter06.theorem_6_4_3`, Corollary 7.2.2 is
  `ConnGouldToint.Chapter07.corollary_7_2_2`, Algorithm 7.3.2 is
  `ConnGouldToint.Chapter07.algorithm_7_3_2`, and part (ii) of Lemma 9.1.2 is
  `ConnGouldToint.Chapter09.lemma_9_1_2_ii`. A variant or a counterexample adds a suffix, as in
  `ConnGouldToint.Chapter03.theorem_3_2_8_counterexample`. Numbered equations and definitions have
  descriptive names: the ratio (6.1.4) is `ConnGouldToint.Chapter06.btrRatio`.
* The standing assumptions of the source keep their labels (AF.1, AM.4, AN.1, AA.1, AC.8, AO.4b,
  AW.1 and others). Each assumption is an explicit hypothesis of the theorems that use it, and the
  doc comment names it. For example, the sufficient model decrease AA.1 is
  `ConnGouldToint.Chapter06.HasSufficientModelDecrease`.
* A run of the basic trust-region Algorithm 6.1.1 is `ConnGouldToint.Chapter06.BTRRun`, with
  iterates $x_k$, steps $s_k$, radii $\Delta_k$, trust-region norms $\|\cdot\|_k$ and models $m_k$.
  The later chapters reuse it.
* Many statements of the source in $\mathbb{R}^n$ are stated in a real inner product space or a real
  Hilbert space $E$. Matrices are indexed by finite types such as `Fin n`, and Euclidean vectors are
  elements of `EuclideanSpace ℝ (Fin n)`.
* The derivative $f'(x)$ is `fderiv ℝ f x`, and the gradient $\nabla f(x)$ is either this functional
  or its Riesz representative `gradient f x`; the conventions of each module say which. The Hessian
  form $\langle u, \nabla^2 f(x) u \rangle$ is `fderiv ℝ (fderiv ℝ f) x u u` or
  `iteratedFDeriv ℝ 2 f x (fun _ => u)`. Where $f$ is not differentiable, Lean sets the derivative
  to zero.
* Sequences are indexed from $0$. A subsequence $(x_{k_i})$ is `x ∘ j` for a map `j : ℕ → ℕ` that
  tends to infinity.
* Division follows Lean's convention $a / 0 = 0$. For example, the CG step length is $0$ at a
  direction of zero curvature.
* The conjugate-gradient states of the backbone carry the residual $b - Hx$ of the system $Hx = b$.
  For the system $Hx = -g$ this is the negative of the gradient $Hx + g$ that the source uses.

## Deviations from the source

**Chapter 2. Basic Concepts**

* **Prose before (2.2.6)** (correction). The source places each eigenvalue in the intersection of
  the Gershgorin discs. It lies in their union, and a diagonal $2 \times 2$ matrix has an eigenvalue
  outside one disc. See `ConnGouldToint.Chapter02.gershgorin_union` and
  `ConnGouldToint.Chapter02.gershgorin_intersection_counterexample`.

**Chapter 3. Basic Analysis and Optimality Conditions**

* **Theorem 3.2.8** (correction). The statement assumes nonempty compact feasible sets and gives
  continuity of the minimum value and upper hemicontinuity of the minimizers. The minimizers need
  not be lower hemicontinuous, and without compactness the value need not be continuous. See
  `ConnGouldToint.Chapter03.theorem_3_2_8`, `ConnGouldToint.Chapter03.theorem_3_2_8_counterexample`
  and `ConnGouldToint.Chapter03.theorem_3_2_8_noncompact_value_counterexample`.
* **Theorem 3.2.10** (reading). The continuity of the normal and tangent cones is stated on a face
  with a fixed active set, as upper and lower hemicontinuity of their bounded sections. See
  `ConnGouldToint.Chapter03.theorem_3_2_10_face_continuity`.
* **Theorem 3.2.11** (correction). The multiplier conclusion needs a normal-cone sum rule at the
  minimizer; linearization of the tangent cone alone does not suffice. See
  `ConnGouldToint.Chapter03.theorem_3_2_11_of_normalCone_sum` and
  `ConnGouldToint.Chapter03.theorem_3_2_11_tangent_counterexample`.
* **Corollary 3.2.13** (correction). The first-order condition uses the bound
  $f'(x) d + h^\circ(c(x); c'(x) d)$. It is not equal to the Clarke derivative of the composite in
  general. See `ConnGouldToint.Chapter03.corollary_3_2_13` and
  `ConnGouldToint.Chapter03.clarke_composite_equality_counterexample`.
* **Theorem 3.2.15** (correction). The outer functions are locally Lipschitz, and an active
  constraint needs a strict Clarke descent direction. The printed conditions on the domains of the
  outer functions are not sufficient. See `ConnGouldToint.Chapter03.theorem_3_2_15` and
  `ConnGouldToint.Chapter03.theorem_3_2_15_boundary_counterexample`.
* **Q-rate definitions of Section 3.3.1** (typo). The printed criteria on pp. 50–51 compare the
  successive difference $\|u_{k+1} - u_k\|$ with the error $\|u_k - x\|$. The definitions use the
  successor error $\|u_{k+1} - x\|$. See `ConnGouldToint.Chapter03.ConvergesQQuadratically` and
  `ConnGouldToint.Chapter03.reciprocal_succ_counterexample`.
* **Theorem 3.3.2** (correction). The statement adds the hypothesis that the closed ball of the
  Kantorovich radius about $x_0$ lies in the domain. See `ConnGouldToint.Chapter03.theorem_3_3_2`
  and `ConnGouldToint.Chapter03.newton_correction_small_without_domain_ball`.

**Chapter 4. Basic Linear Algebra**

* **Equation (4.1.2)** (correction). The source assumes only that $H$ and $D$ are invertible. The
  formula also needs the invertibility of $D^{-1} + A H^{-1} A^T$. See
  `ConnGouldToint.Chapter04.woodbury_solution_4_1_2` and
  `ConnGouldToint.Chapter04.woodbury_middle_inverse_counterexample`.
* **Conversion after (4.3.5)** (correction). The diagonal square root multiplies the unit lower
  triangular factor on the right, $L_C = L_L D^{1/2}$, not on the left as printed. See
  `ConnGouldToint.Chapter04.cholesky_of_ldl`.
* **Equation (4.4.10)** (reading). The range-space component of the decomposition lies in the range
  of $A^T$, which is the orthogonal complement of the null space of $A$. See
  `ConnGouldToint.Chapter04.range_null_decomposition_4_4_10`.
* **After (4.4.14)** (correction). Positive semidefinite reduced curvature makes a stationary
  feasible point a global minimizer but does not make it unique; uniqueness needs positive definite
  reduced curvature. See `ConnGouldToint.Chapter04.quadratic_minimum_4_4_14` and
  `ConnGouldToint.Chapter04.semidefinite_reduced_quadratic_not_unique`.

**Chapter 5. Krylov Subspace Methods**

* **Lemma 5.1.5** (correction). The gradient pairings $\langle p_j, r_j \rangle$ must be nonzero at
  all earlier directions, not only at the last. See `ConnGouldToint.Chapter05.lemma_5_1_5` and
  `ConnGouldToint.Chapter05.counterexample_5_1_5`.
* **Theorem 5.1.7 and Corollary 5.1.8** (reading). The error bounds are stated as products, not as
  ratios of errors, so that they also hold when $x_0 = x_*$. See
  `ConnGouldToint.Chapter05.theorem_5_1_7` and `ConnGouldToint.Chapter05.corollary_5_1_8`.

**Chapter 6. Global Convergence of the Basic Algorithm**

* **Theorem 6.3.3** (reading). The accepted step is taken at the first index at which the Armijo
  test holds. A sufficient step length bound guarantees that such an index exists, and the rejected
  predecessor gives the decrease bound. See `ConnGouldToint.Chapter06.theorem_6_3_3`.
* **Lemma 6.5.3** (correction). The statement adds uniform vanishing of the objective and model
  Hessian variation along the trial segments. See `ConnGouldToint.Chapter06.lemma_6_5_3`.
* **Lemma 6.5.4** (correction). The statement adds uniform vanishing of the objective and model
  Hessian variation along the trial segments. See `ConnGouldToint.Chapter06.lemma_6_5_4`.
* **Theorem 6.5.5** (correction). The statement adds local model curvature on the trial segments
  near the limit and vanishing model Hessian variation once the steps vanish. See
  `ConnGouldToint.Chapter06.theorem_6_5_5`.
* **Theorem 6.6.4** (reading). The model error estimate on small radii is an explicit hypothesis. It
  follows from uniform variation of the objective and model Hessians on small trial segments. See
  `ConnGouldToint.Chapter06.theorem_6_6_4`.

**Chapter 7. The Trust-Region Subproblem**

* **Theorem 7.2.1** (reading). The radius is assumed positive. See
  `ConnGouldToint.Chapter07.theorem_7_2_1`.
* **Corollary 7.2.2** (reading). The radius is assumed positive. See
  `ConnGouldToint.Chapter07.corollary_7_2_2`.
* **Lemma 7.3.2** (correction). The secular values of the Newton iterates are nonpositive, not
  negative, because Newton's method can reach the root exactly. See
  `ConnGouldToint.Chapter07.lemma_7_3_2`.
* **Prose following Lemmas 7.3.5 and 7.3.6** (correction). The acceptance coefficient of the model
  value is an upper bound on the chosen coefficient, so the printed comparisons are reversed. See
  `ConnGouldToint.Chapter07.IsAcceptableModelStep.weaken`.
* **Theorem 7.3.4, hard case** (correction). Vector convergence of the corrected steps is proved for
  a fixed unit leftmost eigenvector and a fixed root of the boundary equation. For general
  correction directions, the model values converge and every limit point is a minimizer. See
  `ConnGouldToint.Chapter07.moreSorensen_hard_bracket_then_exact_correction`.
* **Algorithm 7.3.4, Step 3b(iii)** (reading). The two roots of the boundary equation can give the
  same model value, so the rule needs a tie convention. The library chooses the root with the
  positive square root. See `ConnGouldToint.Chapter07.moreSorensen_boundary_correction_tie` and
  `ConnGouldToint.Chapter07.moreSorensenBestBoundaryCoefficient`.
* **Algorithm 7.3.2** (reading). The bracket choices that the source leaves open are midpoints. See
  `ConnGouldToint.Chapter07.algorithm_7_3_2`.
* **Algorithm 7.3.6** (correction). The terminal branch tests solvability and feasibility at the
  exact threshold, because a feasible step at a perturbed shift can report the hard case when the
  exact test would not. See `ConnGouldToint.Chapter07.algorithm_7_3_6_exact_threshold` and
  `ConnGouldToint.Chapter07.algorithm_7_3_6_perturbation_counterexample`.
* **Section 7.3.7, LINPACK sign rule** (correction). The source compares the signed candidates
  $1 - b$ and $-1 - b$, which always selects $v_i = 1$; this choice misses the kernel of the
  $2 \times 2$ all-ones matrix. The rule compares the magnitudes $|1 - b|$ and $|-1 - b|$. See
  `ConnGouldToint.Chapter07.linpackSign`.
* **Equation (7.3.17)** (correction). The kernel identity at a failed pivot holds on the leading
  principal block, not on the full matrix. See
  `ConnGouldToint.Chapter07.choleskyFailedPivot_certificate` and
  `ConnGouldToint.Chapter07.failedCholeskyPivot_full_residual_counterexample`.
* **Theorem 7.4.1** (correction). The statement requires $\Delta > 0$, as in Section 7.2. At
  $\Delta = 0$ the only feasible point is $0$, and the shifted system has no solution when
  $g \neq 0$. See `ConnGouldToint.Chapter07.theorem_7_4_1`.
* **Lemma 7.5.8** (typo). The source prints the condition $g \ge 0$. The intended condition is on
  the iteration index, $k \ge 0$. See `ConnGouldToint.Chapter07.lemma_7_5_8_of_coercive`.
* **Theorem 7.5.12** (reading). The exclusion of the hard case is stated as the nonorthogonality of
  every eigenvector of $T$ to the reduced gradient $\gamma e_1$. See
  `ConnGouldToint.Chapter07.theorem_7_5_12`.
* **Theorem 7.5.16** (reading). The preconditioned problem is stated in the coordinates of the
  preconditioner inner product, where $H$ and $g$ are the preconditioned Hessian and gradient. See
  `ConnGouldToint.Chapter07.theorem_7_5_16`.
* **Algorithm 7.5.2** (reading). The reduced tridiagonal matrix comes from the Lanczos recurrence
  for $M^{-1} H$ in the $M$-inner product, computed independently of the PCG coefficients, as the
  text suggests when the PCG curvature vanishes. The physical residual is checked before stopping.
  See `ConnGouldToint.Chapter07.algorithm_7_5_2`.

**Chapter 8. Further Convergence Theory Issues**

* **Theorem 8.1.4** (reading). First-order convergence of the criticality measure is taken as an
  input, as supplied by Section 8.1.2. See `ConnGouldToint.Chapter08.theorem_8_1_4`.
* **Theorem 8.1.5** (correction). The conclusion on the scaled model curvature along the subsequence
  assumes local persistence of negative curvature. The conclusion on the objective curvature holds
  without it. See `ConnGouldToint.Chapter08.theorem_8_1_5` and
  `ConnGouldToint.Chapter08.theorem_8_1_5_directional`.
* **Theorem 8.1.8** (correction). Uniform norm equivalence alone does not imply AN.3. The library
  proves AN.3 for a fixed norm with Lipschitz gradients along the iterates. See
  `ConnGouldToint.Chapter08.dualNorm_scaling_counterexample` and
  `ConnGouldToint.Chapter08.dualNorm_tendsto_difference_zero`.
* **Theorem 8.1.9** (correction). The decrease bound uses a steepest ray of the trust-region norm.
  The Euclidean Cauchy ray can fail the bound. See `ConnGouldToint.Chapter08.theorem_8_1_9` and
  `ConnGouldToint.Chapter08.theorem_8_1_9_counterexample`.
* **Theorem 8.4.8** (correction). Eventual model convexity is required on every trial segment from
  iterates in a neighborhood of the limit point, not only along the convergent subsequence. See
  `ConnGouldToint.Chapter08.theorem_8_4_8`.
* **Theorems 8.5.1 and 8.5.2(i)** (reading). The agreement of the inner model with $u$ in value and
  derivative at the center, and the bound $|Df_0(x, u(x))(0, z)| \le D \|z\|$ on the outer partial
  derivative in the inner variable, are explicit hypotheses. See
  `ConnGouldToint.Chapter08.theorem_8_5_1_hessian` and
  `ConnGouldToint.Chapter08.theorem_8_5_2_hessian_agreement`.
* **Theorem 8.5.2(ii)** (correction). Lipschitz constants of the constituent Hessians alone do not
  give a uniform Lipschitz constant for the composite Hessians. The corrected statement also assumes
  uniform bounds on both constituent Hessians. See
  `ConnGouldToint.Chapter08.theorem_8_5_2_lipschitz_counterexample` and
  `ConnGouldToint.Chapter08.theorem_8_5_2_lipschitz`.

**Chapter 9. Conditional Models**

* **Theorem 9.1.1** (correction). The radius of the ball must be positive. At radius $0$, validity
  at the center alone gives no gradient bound. See
  `ConnGouldToint.Chapter09.zero_radius_counterexample`.
* **Algorithm 9.1.1** (correction). The printed update contracts the radius after every low-ratio
  iteration, also when the model is invalid. The theorems use the corrected update, which keeps the
  radius in that case. See `ConnGouldToint.Chapter09.theorem_9_2_1_quadratic_counterexample`.
* **Lemma 9.1.2(ii)** (correction). The finite-improvement argument needs a fixed center and a fixed
  radius during a block of rejected iterations with invalid models, which the corrected update
  gives. See `ConnGouldToint.Chapter09.lemma_9_1_2_ii`.
* **Theorem 9.2.1** (correction). The radii are bounded away from zero only under the corrected
  update. See `ConnGouldToint.Chapter09.theorem_9_2_1`.
* **Theorem 9.2.2** (correction). The theorem is proved for the corrected update, with the
  finite-improvement condition on the rejected tail. See `ConnGouldToint.Chapter09.theorem_9_2_2`.
* **Theorem 9.2.3** (correction). The theorem is proved for the corrected update. See
  `ConnGouldToint.Chapter09.theorem_9_2_3`.
* **Lemma 9.2.4** (reading). The condition that the criticality test of Step 1 eventually accepts
  the model is an explicit hypothesis. See `ConnGouldToint.Chapter09.lemma_9_2_4`.
* **Theorem 9.2.5** (correction). The subsequence conclusion needs infinitely many successful
  iterations and compact containment of the successful iterates. The limit-inferior conclusion needs
  neither. See `ConnGouldToint.Chapter09.theorem_9_2_5` and
  `ConnGouldToint.Chapter09.theorem_9_2_5_exists_critical_subseq`.
* **Theorem 9.2.6** (correction). The criticality test supplies the comparison of the objective and
  model gradients at small model gradients, which is an explicit hypothesis. See
  `ConnGouldToint.Chapter09.theorem_9_2_6`.
* **Theorem 9.3.1** (correction). The radius of the ball must be positive. At radius $0$,
  second-order validity gives no Hessian bound. See
  `ConnGouldToint.Chapter09.second_order_zero_radius_counterexample`.
* **Equation (9.3.4)** (correction). The model curvature can stay negative at every refinement. The
  proof of Theorem 9.3.3 needs only a lower bound on the model curvature that tends to zero. See
  `ConnGouldToint.Chapter09.theorem_9_3_3`.
* **Algorithm 9.3.1** (correction). At zero model criticality the printed radius is zero. The
  corrected loop keeps refining at a positive radius, so that the derivative estimates still apply.
  See `ConnGouldToint.Chapter09.secondOrderRefinementRadius`.
* **Equation (9.4.5)** (correction). The normalization divides by the signed pivot, so that the
  diagonal value is $1$. Division by the absolute value fails for a negative pivot. See
  `ConnGouldToint.Chapter09.absolutePivotNormalization_counterexample`.
* **Equation (9.4.6)** (correction). The update is applied after the normalization (9.4.5), so that
  it makes the other functions vanish at the pivot point. See
  `ConnGouldToint.Chapter09.newtonElimination_at_pivot`.
* **Theorem 9.4.4** (correction). The model error bound uses affine reproduction and uniform bounds
  on all Newton blocks on the ball. For an incomplete quadratic block, the printed bounds on
  adjacent blocks and on the last block do not imply the error bound (9.4.21): an example with five
  points violates it for every uniform constant. See
  `ConnGouldToint.Chapter09.theorem_9_4_4_of_uniform_newton_bound` and
  `ConnGouldToint.Chapter09.theorem_9_4_4_incompleteQuadratic_counterexample`.
* **Theorem 9.5.2** (correction). The memory estimate uses the bound on the past local models at the
  last accepted center. The product of recent weights is controlled by the lower radius factor
  $\gamma \Delta_k \le \Delta_{k+1}$ of adjacent iterations, so that the radii can vary during a
  block of rejected iterations. See `ConnGouldToint.Chapter09.theorem_9_5_2`.

**Chapter 10. Algorithmic Extensions**

* **Equation (10.1.2)** (correction). The reference index may stay the same from one iteration to
  the next. The reference value must decrease strictly only when the reference index changes. See
  `ConnGouldToint.Chapter10.IsReferenceSchedule`.
* **Algorithm 10.1.2, Step 3d** (reading). The boxed algorithm tests whether the counter equals the
  window, while the prose before it says that the counter exceeds the window. The definition uses
  the equality test. See `ConnGouldToint.Chapter10.ReferenceBuffer.step`.
* **Equation (10.1.11)** (reading). The count of accepted iterations includes iteration $0$. See
  `ConnGouldToint.Chapter10.successful_count_le`.
* **Equations (10.2.6)–(10.2.7)** (reading). The ratio test and the fit test are equivalent only for
  a positive predicted decrease. At zero predicted decrease they can disagree. The library uses the
  fit test. See `ConnGouldToint.Chapter10.elementRatio_zero_counterexample`.
* **Equation (10.2.24)** (correction). The floor on the radii compares the model error directly with
  the two fit tolerances, and the curvature bound uses the sum of the element curvature bounds. See
  `ConnGouldToint.Chapter10.structuredRadiusFloor`.
* **Theorem 10.2.6** (correction). The theorem needs the uniform norm comparison AN.1. Without it,
  every trial can be rejected at a fixed noncritical iterate. See
  `ConnGouldToint.Chapter10.theorem_10_2_6_without_norm_bound_counterexample`.
* **Theorem 10.3.4** (correction). The source states the angle bound for a trust region in a norm
  that is uniformly equivalent to the Euclidean norm. The bound fails for the $\ell_1$ ball, and the
  formal statement uses a Euclidean ball. See
  `ConnGouldToint.Chapter10.theorem_10_3_4_general_norm_counterexample`.
* **Equation (10.3.5)** (correction). The Armijo test uses the same exponent $j$ on both sides. See
  `ConnGouldToint.Chapter10.backtrackingTRArmijo`.
* **Algorithm 10.3.2, reuse of the rejected step** (correction). The rejected step is reused only if
  it is a descent direction; otherwise the negative gradient is used. Under the printed absolute
  angle condition, the rejected step can point uphill. See
  `ConnGouldToint.Chapter10.backtrackingTR_ascent_reuse_counterexample`.
* **Algorithm 10.3.2, trial test** (correction). An accepted probe must also have a positive
  predicted decrease, so that the ratio test is defined. See
  `ConnGouldToint.Chapter10.backtrackingTRTrial`.
* **Theorem 10.4.1** (correction). The lower bound (10.4.6) is assumed for the augmented decrease
  $\delta_k$, not for the decrease of the original model. See
  `ConnGouldToint.Chapter10.theorem_10_4_1`.
* **Equation (10.4.12)** (reading). The quadratic term uses the displacement of the argument from
  the center, as in (10.4.15), so it cancels from the ratio error (10.4.16). See
  `ConnGouldToint.Chapter10.quadraticAugmentedModel`.
* **Algorithm 10.5.1** (correction). The printed inner loop can run forever, even for exact models.
  The trace records a terminating inner loop, and an optional finite budget of probes guarantees
  termination and keeps the reduction to the basic algorithm. See
  `ConnGouldToint.Chapter10.internalDoubling_unbounded_inner_counterexample` and
  `ConnGouldToint.Chapter10.exists_cappedInternalDoublingTrace`.

**Chapter 11. Nonsmooth Problems**

* **Equation (11.1.16)** (correction). The printed very-successful interval
  $[\gamma_3 \Delta, \Delta_{\max}]$ is empty when $\Delta = \Delta_{\max}$. The lower bound is
  capped at $\min\{\gamma_3 \Delta, \Delta_{\max}\}$. See
  `ConnGouldToint.Chapter11.printedNonsmoothExpansion_infeasible`.
* **Algorithm 11.1.1, Step 3** (reading). A zero predicted decrease gives the ratio $0$, so the step
  is rejected. See `ConnGouldToint.Chapter11.NonsmoothTRRun.ratio`.
* **Lemma 11.1.3** (correction). Pointwise smooth model matching does not give a uniform decrease.
  The statement assumes a uniform one-sided first-order model estimate near the nonstationary point.
  See `ConnGouldToint.Chapter11.oscillatoryModel_fails_uniform_decrease`.
* **Corollary 11.1.4** (correction). The same counterexample shows that pointwise matching does not
  give the uniform Cauchy decrease; the statement assumes the same uniform estimate. See
  `ConnGouldToint.Chapter11.oscillatoryModel_fails_cauchy_decrease`.
* **Lemma 11.2.2** (correction). Pointwise agreement and a compact parameter set do not give uniform
  agreement. The statement adds the equicontinuity of the normalized errors. See
  `ConnGouldToint.Chapter11.compactPerturbedModel_not_uniform`.
* **Lemma 11.2.3** (correction). The statement assumes uniform control (11.2.1) of the normalized
  error. Pointwise agreement alone permits rejections at small radii. See
  `ConnGouldToint.Chapter11.compactPerturbedModel_rejected`.
* **Lemma 11.2.4 and Theorem 11.2.5** (correction). Both use the uniform agreement that the
  corrected Lemma 11.2.3 needs. See `ConnGouldToint.Chapter11.theorem_11_2_5`.
* **Theorems 11.3.1 and 11.3.2** (correction). Both assume uniform normalized agreement of the
  models (11.2.1), as the corrected Lemma 11.2.3 does. See `ConnGouldToint.Chapter11.theorem_11_3_1`
  and `ConnGouldToint.Chapter11.theorem_11_3_2`.
* **Theorem 11.5.1** (correction). The accuracy estimate also assumes that the modeled residual
  $c(x) + c'(x) s + r(x, i, s)$ lies in the domain where $h$ is Lipschitz. See
  `ConnGouldToint.Chapter11.compositeTaylorModel_domain_counterexample`.

**Chapter 12. Projection Methods for Convex Constraints**

* **Equation (12.1.3)** (correction). The radial formula holds only outside the closed ball; a point
  inside the ball is its own projection. See `ConnGouldToint.Chapter12.projection_closedBall`.
* **Theorem 12.1.3** (generalization). The statement does not use the assumptions AC.1 and AC.7 on
  smooth constraints and a finite representation. See `ConnGouldToint.Chapter12.theorem_12_1_3`.
* **Theorem 12.2.1** (correction). The statement assumes that the model gradient at the base point
  equals the objective gradient. With opposite gradients every positive trial fails the upper
  decrease test. See
  `ConnGouldToint.Chapter12.theorem_12_2_1_without_model_gradient_agreement_counterexample`.
* **Algorithm 12.2.2** (reading). A first-order critical base point is returned before the initial
  trial parameter is computed, which would divide by a zero gradient. See
  `ConnGouldToint.Chapter12.isApproxGeneralizedCauchyPoint_of_normal`.
* **Theorem 12.3.4** (correction). The local comparison bounds the criticality measure of the
  relaxed feasible set, with a shifted displacement; a half-line example shows that the trial
  conditions alone do not give the bound for the full feasible set. See
  `ConnGouldToint.Chapter12.theorem_12_3_4_relaxed` and
  `ConnGouldToint.Chapter12.missing_active_local_criticality_counterexample`.
* **Lemma 12.3.7** (correction). The claimed subsequence of successful iterations with the limiting
  active set need not exist. The claim holds when the limit set has a common active set and the
  iterates carry asymptotically accurate normal certificates. See
  `ConnGouldToint.Chapter12.theorem_12_3_8_iterate_identification_counterexample` and
  `ConnGouldToint.Chapter12.lemma_12_3_7_of_normal_certificates`.
* **Theorem 12.3.8** (correction). Eventual identification of the active set fails at the
  generalized Cauchy points for a scalar interval run whose radii alternate between $2$ and $1$, and
  at the iterates for a run with constant radii and only very successful steps. The corrected
  versions assume normal certificates, vanishing radii, vanishing Cauchy and iterate displacements,
  vanishing trial displacements, or bounded positive trial times. See
  `ConnGouldToint.Chapter12.theorem_12_3_8_nonvanishing_radius_counterexample`,
  `ConnGouldToint.Chapter12.theorem_12_3_8_iterate_identification_counterexample` and
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero`.
* **Corollary 12.3.9** (correction). The corollary assumes that the iterates eventually have the
  active set of the limit set, which the printed Theorem 12.3.8 does not provide. See
  `ConnGouldToint.Chapter12.corollary_12_3_9_of_eventually_active`.
* **Theorem 12.4.3** (reading). The trapping of the iterates on the identified face near the limit
  and the small steps near the limit are explicit hypotheses. See
  `ConnGouldToint.Chapter12.theorem_12_4_3`.
* **Lemma 12.4.4** (reading). The feasible extension of the step direction by a uniform length is an
  explicit hypothesis. See `ConnGouldToint.Chapter12.lemma_12_4_4`.
* **Theorem 12.4.5** (reading). The Hessian agreement (12.4.7) is assumed on the trial segments. See
  `ConnGouldToint.Chapter12.theorem_12_4_5`.
* **Equation (12.4.14)** (correction). The printed test has the sign that accepts a strict model
  increase at negative curvature. The test here requires a decrease. See
  `ConnGouldToint.Chapter12.ProjectedEigenTrialAccepted` and
  `ConnGouldToint.Chapter12.eigenTrial_printed_sign_counterexample`.
* **Equation (12.4.16)** (reading). The distance uses the frontier relative to the active equality
  locus, and it is infinite when that frontier is empty. See
  `ConnGouldToint.Chapter12.activeFaceBoundaryDistance`.
* **Theorem 12.4.6** (correction). The decrease bound uses the corrected sign of (12.4.14) and
  includes the face radius. See `ConnGouldToint.Chapter12.theorem_12_4_6`.

**Chapter 13. Barrier Methods for Inequality Constraints**

* **Algorithm 13.1.1** (generalization). An inner run may stop at index $0$ when its starting point
  already passes the stopping test, while the text uses a positive terminal index. See
  `ConnGouldToint.Chapter13.BarrierOuterRun`.
* **AC.8 for the logarithmic barrier** (correction). The source states that (13.1.2) satisfies AC.8.
  This holds only along sequences with bounded coordinates, because a coordinate that tends to
  infinity can cancel the logarithm of a coordinate that tends to zero. See
  `ConnGouldToint.Chapter13.logBarrier_boundary_divergence` and
  `ConnGouldToint.Chapter13.logBarrier_unbounded_boundary_counterexample`.
* **Theorem 13.2.1** (correction). The theorem assumes that the objective $f$ is bounded below along
  the run; this bounds the barrier values, so that AC.8 applies. AC.8 is needed only along
  reindexings of the run. See `ConnGouldToint.Chapter13.theorem_13_2_1`.
* **Theorem 13.2.1 for the logarithmic barrier** (correction). The logarithmic barrier satisfies
  AC.8 only along bounded paths, and a lower-bounded objective does not separate a level set from
  the boundary. Separation holds for bounded iterates, or under a global lower bound, a bounded
  Hessian and AW.2 at a larger parameter. See
  `ConnGouldToint.Chapter13.logBarrier_unbounded_level_counterexample`,
  `ConnGouldToint.Chapter13.logBarrier_bounded_level_separation` and
  `ConnGouldToint.Chapter13.logBarrier_sublevel_separation_of_global_lower`.
* **Theorem 13.4.2, boundary clearance** (correction). AF.1, AF.3 and AW.2 as printed do not imply
  that the sublevel sets of the log-barrier objective stay away from the boundary. See
  `ConnGouldToint.Chapter13.logBarrier_level_clearance_counterexample_of_bounded_hessian`.
* **Corollary 13.3.2** (correction). The corollary uses the corrected hypothesis of Theorem 13.2.1:
  the objective is bounded below along the iterates. See
  `ConnGouldToint.Chapter13.corollary_13_3_2`.
* **Algorithm 13.4.1** (generalization). An inner minimization may stop at index zero when its
  starting point already passes the stopping tests. See
  `ConnGouldToint.Chapter13.PrimalLogBarrierOuterRun`.
* **Theorem 13.4.2** (correction). The printed hypotheses do not give finite stopping. For the
  bilinear objective $x_1 x_2$, a run of Algorithm 13.2.1, and also of Algorithm 13.3.1, with exact
  logarithmic Taylor models is unbounded, has ratios at least $2$, and fails the gradient test at
  every iterate. The inner limits are proved under a uniform clearance, a smooth extension of the
  objective that agrees with it at the iterates and trials, and uniform model estimates. See
  `ConnGouldToint.Chapter13.theorem_13_4_2_unbounded_primal_inner_run`,
  `ConnGouldToint.Chapter13.theorem_13_4_2_unbounded_constrained_primal_inner_run` and
  `ConnGouldToint.Chapter13.theorem_13_4_2_inner_of_extension`.
* **Example after Corollary 13.4.4** (correction). The quadratic (13.4.13) is unbounded below on the
  orthant, so it does not meet the lower-boundedness requirement. A smooth cutoff gives a
  bounded-below objective with the same stopping points and the same limit. See
  `ConnGouldToint.Chapter13.logBarrierCounterRegularized_example`.
* **Equation (13.6.3)** (correction). The printed quadratic term of the barrier model has a negative
  sign; the model uses the positive sign. See
  `ConnGouldToint.Chapter13.primalDualBarrierModel_printed_sign_counterexample`.
* **Algorithm 13.6.1, Step 2** (correction). The printed distance test also admits infeasible
  points; the trial must also be strictly feasible. See
  `ConnGouldToint.Chapter13.primalDual_distance_test_infeasible_counterexample`.
* **Theorem 13.6.2** (correction). Finite stopping needs bounded primal coordinates. A scalar
  all-successful run with unbounded primal coordinates never passes the complementarity test. See
  `ConnGouldToint.Chapter13.theorem_13_6_2_unbounded_run_counterexample` and
  `ConnGouldToint.Chapter13.PrimalDualBarrierInnerRun.frequently_stop_of_extension`.
* **Theorem 13.6.4** (correction). AA.8 needs infinitely many successful iterations; a bounded run
  with all trials rejected violates it. Resetting the dual to $\mu / x$ after a rejection gives AA.8
  when the accepted displacements tend to zero. See
  `ConnGouldToint.Chapter13.theorem_13_6_4_aa8_of_frequently_successful`,
  `ConnGouldToint.Chapter13.theorem_13_6_4_all_rejected_counterexample` and
  `ConnGouldToint.Chapter13.theorem_13_6_4_aa8_of_reset_rejected`.
* **Theorem 13.7.2** (generalization). The bound $\varepsilon^C_k \le L \mu_k$ on the
  complementarity tolerance is assumed only eventually. The condition (13.7.15) implies it after
  increasing the constant. See `ConnGouldToint.Chapter13.theorem_13_7_2`.
* **Theorem 13.7.3** (correction). The theorem keeps the gradient-tolerance rate (13.7.16) of
  Theorem 13.7.2. A one-dimensional quadratic example shows that vanishing scaled tolerances alone
  are insufficient. See `ConnGouldToint.Chapter13.theorem_13_7_3_counterexample`.
* **Equation (13.9.7)** (reading). The complementarity residual $C(x) y - \mu e$ is a vector, and
  the test bounds each component. See `ConnGouldToint.Chapter13.GeneralPrimalDualBarrierStop`.
* **Theorem 13.9.1** (reading). The infimum in (13.9.11) is over unit directions, as in the proof.
  See `ConnGouldToint.Chapter13.theorem_13_9_1`.
* **Theorem 13.9.1** (generalization). The multiplier-error assumption (13.9.10) is not needed: the
  complementarity test controls the barrier curvature on the inactive constraints. See
  `ConnGouldToint.Chapter13.theorem_13_9_1`.
* **Algorithm 13.10.1** (correction). The printed test compares unsigned distances to the boundary,
  which a point outside the feasible set can pass. The trial point must also be strictly feasible.
  See `ConnGouldToint.Chapter13.AffineOrthantBarrierTrial`.
* **Equation (13.12.12)** (correction). The curvature along the scaled Cauchy ray is that of
  $\hat H = S H S + \bar G$, including the positive-gradient diagonal. See
  `ConnGouldToint.Chapter13.unscaledModel_along_scaledRay`.
* **Algorithms 13.12.1 and 13.12.2** (correction). The printed boundary-distance test (13.12.9) also
  admits points outside the orthant, so the trial point must also be strictly positive. See
  `ConnGouldToint.Chapter13.ColemanLiRun` and
  `ConnGouldToint.Chapter13.colemanLi_unsigned_clearance_counterexample`.
* **Theorem 13.12.3** (correction). The decrease bound needs a fraction-to-boundary cap on the ray
  parameter. A one-dimensional example violates the printed bound for every positive criticality
  cap. See `ConnGouldToint.Chapter13.theorem_13_12_3` and
  `ConnGouldToint.Chapter13.theorem_13_12_3_counterexample`.
* **Theorem 13.12.5** (correction). The printed bound is stated at the Cauchy point and is negative.
  The corrected bound is positive and holds at the constrained scaled eigenpoint. See
  `ConnGouldToint.Chapter13.theorem_13_12_5`.
* **Equation (13.12.34)** (correction). Both terms of the reduced model are evaluated at the trial
  displacement. See `ConnGouldToint.Chapter13.tramModel`.
* **Equation (13.12.35)** (typo). The reduced trust-region bound uses the radius of (13.12.33),
  without the stray factor $n$ of the printed display. See
  `ConnGouldToint.Chapter13.tramNorm_le_iff_exists_slack`.

**Chapter 14. Penalty-Function Methods**

* **Equation (14.2.3)** (typo). Both derivatives in the stationarity condition are evaluated at the
  feasible point $x$. See `ConnGouldToint.Chapter14.IsEqualityKKT`.
* **Equation (14.2.26)** (typo). Both multiplier differences on the right side have the sign of the
  identity (14.2.6). See `ConnGouldToint.Chapter14.lemma_14_2_2_i`.
* **Equation (14.3.15)** (correction). The scaling factor of the constraint term is $\mu / \nu - 1$.
  See `ConnGouldToint.Chapter14.gradient_augmentedLagrangian_change_parameter`.
* **Lemma 14.3.2(i)** (correction). The limit is stated for a fixed Lagrangian Hessian, compressed
  to the entire kernel of the constraint derivative. At a feasible point this Hessian is the one in
  the penalty Hessian. See `ConnGouldToint.Chapter14.lemma_14_3_2_i` and
  `ConnGouldToint.Chapter14.lemma_14_3_2_i_of_feasible`.
* **Lemma 14.3.2(ii)–(iii)** (correction). At an infeasible point the Lagrangian Hessian term can
  grow like $1/\mu$, and the printed limits fail. The corrected estimates bound that term
  explicitly. See `ConnGouldToint.Chapter14.lemma_14_3_2_scaled_extremes` and
  `ConnGouldToint.Chapter14.lemma_14_3_2_infeasible_counterexample`.
* **Equation (14.4.10)** (typo). The first-order multiplier update subtracts the constraint term,
  $y_k - c(x_k) / \mu_k$, as in (14.2.5). See `ConnGouldToint.Chapter14.lemma_14_4_1`.
* **Lemma 14.4.1** (generalization). Between the reductions of the penalty parameter, any
  nonincreasing update of the penalty parameter is allowed. See
  `ConnGouldToint.Chapter14.lemma_14_4_1`.
* **Theorem 14.4.2** (reading). The proof of the source uses AA.9 when the penalty parameter tends
  to zero; the statement assumes it. See `ConnGouldToint.Chapter14.theorem_14_4_2`.
* **Theorem 14.5.1** (correction). The penalty weight must be strictly larger than the threshold
  (14.5.2). At the nonstrict threshold the equivalence fails. See
  `ConnGouldToint.Chapter14.theorem_14_5_1` and
  `ConnGouldToint.Chapter14.theorem_14_5_1_threshold_counterexample`.
* **Theorem 14.5.2** (correction). The constraint derivative must be surjective. With a redundant
  constraint, a multiplier can exceed the penalty weight at a minimizer of the penalty function. See
  `ConnGouldToint.Chapter14.theorem_14_5_2` and
  `ConnGouldToint.Chapter14.theorem_14_5_2_redundant_constraint_counterexample`.
* **Equation (14.6.4)** (correction). Away from the feasible set, the Hessian contains the
  derivative of $z \mapsto y'(z)^* c(x)$, which the printed formula omits. A scalar cubic shows that
  this term can be nonzero. See `ConnGouldToint.Chapter14.fderiv_gradient_smoothExactPenalty_eq` and
  `ConnGouldToint.Chapter14.smoothExactPenalty_printed_hessian_counterexample`.

**Chapter 15. Sequential Quadratic Programming Methods**

* **Theorem 15.2.1(i)** (correction). The supplied multipliers must lie in a fixed ball around the
  root multiplier from the first iteration. Convergence of the multipliers alone allows an
  inconsistent first subproblem. See `ConnGouldToint.Chapter15.theorem_15_2_1_i` and
  `ConnGouldToint.Chapter15.sqp_unrestricted_multiplier_counterexample`.
* **Theorem 15.2.2** (reading). The iteration is Newton's method for the KKT equations of the
  equality and active inequality constraints. The theorem proves that, for a close start, its step
  is at every iteration the unique local minimizer of the mixed quadratic program (15.2.16) among
  those of no larger norm, and that it identifies the active set. See
  `ConnGouldToint.Chapter15.theorem_15_2_2_ii`.
* **Theorem 15.2.2(i)** (correction). As in Theorem 15.2.1(i), the supplied multipliers must lie in
  a fixed ball around the root multiplier from the first iteration. See
  `ConnGouldToint.Chapter15.theorem_15_2_2_i`.
* **Equations (15.3.3)–(15.3.4)** (generalization). The penalty is the distance of the constraint
  value to a set $C$ of feasible values. For Euclidean equality and one-sided inequality residuals,
  this is the norm of the violation vector. See `ConnGouldToint.Chapter15.sqpDistanceMerit` and
  `ConnGouldToint.Chapter15.infDist_eq_mixed_violation_norm`.
* **Theorem 15.3.1** (reading). The Clarke chain-rule inclusion for the merit function at the limit
  point is a hypothesis. A multiplier is not assumed to exist. See
  `ConnGouldToint.Chapter15.theorem_15_3_1`.
* **Theorem 15.3.2** (reading). The two parts are stated in normal-functional and in tangent-cone
  form. See `ConnGouldToint.Chapter15.theorem_15_3_2_first_order` and
  `ConnGouldToint.Chapter15.theorem_15_3_2_second_order`.
* **Lemma 15.3.3** (correction). Twice continuous differentiability does not give the quadratic
  estimate. The Taylor expansion of the KKT residual is a quantitative hypothesis. See
  `ConnGouldToint.Chapter15.lemma_15_3_3` and
  `ConnGouldToint.Chapter15.sqp_C2_newton_counterexample`.
* **Lemma 15.3.4** (reading). The hypotheses are a local feasible restoration with a linear residual
  bound and strict exactness of the penalty. See `ConnGouldToint.Chapter15.lemma_15_3_4`.
* **Lemmas 15.3.5 and 15.3.6** (reading). The Taylor remainders are quantitative hypotheses. See
  `ConnGouldToint.Chapter15.lemma_15_3_5` and `ConnGouldToint.Chapter15.lemma_15_3_6`.
* **Theorem 15.3.7** (correction). The ratio estimate needs positive primal error, since the
  reduction can vanish at the solution. See `ConnGouldToint.Chapter15.theorem_15_3_7`.
* **Equation (15.4.12)** (reading). The scaling interval applies to a nonzero trial normal step; a
  zero trial step has the scaling $1$. See `ConnGouldToint.Chapter15.IsSQPNormalScaling`.
* **Lemma 15.4.2** (reading). The left-hand side is evaluated at the stated Cauchy step. See
  `ConnGouldToint.Chapter15.lemma_15_4_2`.
* **Lemma 15.4.3** (correction). The Lipschitz bounds hold along the full trial segment, including
  trial points that are rejected. Lipschitz continuity of the objective derivative near the iterates
  does not control the rejected trial segments, and Theorems 15.4.10–15.4.11 need the same uniform
  control along the trial segments. See `ConnGouldToint.Chapter15.sqp_trialSegment_counterexample`.
* **Theorem 15.4.6** (reading). The radius argument uses the update after a very successful
  iteration. See `ConnGouldToint.Chapter15.theorem_15_4_6`.
* **Lemma 15.4.9** (correction). The coefficient $\nu \sigma / (\nu \sigma + B)$ is positive for
  every bound $B \ge 0$; the printed coefficient can be negative. See
  `ConnGouldToint.Chapter15.printed_tangential_coefficient_nonpos`.
* **Equation (15.4.50)** (correction). The radius floor includes the radius at entry to the
  neighborhood. See `ConnGouldToint.Chapter15.sqpNeighborhoodRadiusFloor_le`.
* **Equations (15.4.57) and (15.4.140)** (correction). The two exit cases give a common bound with
  the minimum of the two coefficients, not the maximum. See
  `ConnGouldToint.Chapter15.sqp_exit_max_counterexamples`.
* **Equation (15.4.71) and Theorem 15.4.10** (correction). The radius threshold includes the Cauchy
  decrease coefficient and the model error coefficient, and the error bound holds uniformly on the
  trial segments. See `ConnGouldToint.Chapter15.sqpTangentialAcceptanceRadius`.
* **Theorem 15.4.11** (correction). The uniform control of the variation of the reduced gradient on
  accepted steps is a hypothesis. See `ConnGouldToint.Chapter15.theorem_15_4_11`.
* **Theorem 15.4.12** (correction). The acceptance guarantee at small radii concerns the original
  trial, while the accepted decrease may come from either trial. See
  `ConnGouldToint.Chapter15.theorem_15_4_12`.
* **Theorem 15.4.16** (correction). The finite cluster set must control the tail of the iterates,
  and the proof uses the maximum curvature over the cluster points. See
  `ConnGouldToint.Chapter15.theorem_15_4_16`.
* **Lemma 15.4.18 and Theorem 15.4.19** (correction). The model error bound holds uniformly on the
  trial segments, and the variation of the normal criticality on accepted steps is controlled. See
  `ConnGouldToint.Chapter15.theorem_15_4_19`.
* **Equation (15.4.131)** (reading). The curvature bound uses a uniform bound on the Jacobian norms,
  not an attained maximum. See `ConnGouldToint.Chapter15.sqpNormalCurvatureBound_le`.
* **Lemma 15.4.21, equation (15.4.142)** (correction). The second entry of the minimum uses the
  reciprocal of the rank constant. See `ConnGouldToint.Chapter15.lemma_15_4_21`.
* **Algorithm 15.4.1, Step 2** (reading). When the normal model decrease is zero, the required
  penalty is the baseline value alone. See `ConnGouldToint.Chapter15.RelaxedSQPTrials.penalty`.
* **Algorithm 15.4.1** (generalization). The null-space coordinates need not be orthonormal. See
  `ConnGouldToint.Chapter15.RelaxedSQPTrials`.
* **Algorithms 15.4.2 and 15.4.3, acceptance** (reading). The original and the corrected trial are
  both tested against the predicted decrease of the original step. A correction that violates the
  norm cap is not tried, and the original ratio is kept. See
  `ConnGouldToint.Chapter15.relaxedSQPProbe` and `ConnGouldToint.Chapter15.RelaxedSQPCorrectedRun`.
* **Algorithm 15.4.3** (reading). The correction systems have unique solutions with a uniformly
  bounded inverse, as in the derivation of the correction estimates. See
  `ConnGouldToint.Chapter15.RelaxedSQPStructuredRun`.
* **Algorithm 15.4.4** (reading). The algorithm follows the boxed rule of the source and adds AA.2d
  to the tangential step of Algorithm 15.4.3. See
  `ConnGouldToint.Chapter15.RelaxedSQPSecondOrderRun`.
* **Lemma 15.4.13** (reading). The bound of Lemma 15.3.6 and the comparison of the primal error with
  the step length are explicit hypotheses. See `ConnGouldToint.Chapter15.lemma_15_4_13`.
* **Lemma 15.4.14** (reading). The two Taylor remainders, the residual bounds and the two correction
  systems are explicit hypotheses. See `ConnGouldToint.Chapter15.lemma_15_4_14`.
* **Theorem 15.4.15** (reading). The theorem is stated for a run that enters a small neighborhood
  late enough, whose accepted step there is the SQP trial or its full correction with explicit
  standard-step estimates, and whose multiplier estimates converge. See
  `ConnGouldToint.Chapter15.theorem_15_4_15`.
* **Algorithms 15.4.6 and 15.4.7, acceptance** (reading). The corrected trial is tested against the
  predicted decrease of the original composite trial, and a correction is tried only if it satisfies
  the norm cap. See `ConnGouldToint.Chapter15.algorithm_15_4_6`.
* **Section 15.4.3, augmented model** (correction). The constant term of the model is the Lagrangian
  value $f(x) - \langle c(x), y\rangle$, so that the squared residual penalty is counted once and
  the model agrees with the merit function at the center. See
  `ConnGouldToint.Chapter15.infeasibilitySQPModel`.
* **Algorithm 15.4.8, Step 2** (correction). The penalty threshold has the term
  $+2\delta_F / ((1 - \nu)\delta_N)$. The printed negative sign can leave the penalty too small for
  (15.4.171). See `ConnGouldToint.Chapter15.infeasibilitySQPPenalty_printed_sign_counterexample`.
* **Theorem 15.4.23** (typo). The printed statement refers to the wrong algorithm; the theorem
  concerns Algorithm 15.4.6, the method with the second-order correction. See
  `ConnGouldToint.Chapter15.theorem_15_4_23`.
* **Theorem 15.4.25** (correction). The argument uses the cluster point of maximal curvature, with a
  corrected curvature margin, and the coverage of the tail by the cluster set is a hypothesis. See
  `ConnGouldToint.Chapter15.theorem_15_4_25`.
* **Algorithm 15.5.1, filter update, and Lemma 15.5.2** (correction). A new entry deletes only the
  entries that it Pareto-dominates, that is, that it dominates in both components. The printed
  margin-based deletion admits a bounded insertion stream with violations bounded away from zero.
  See `ConnGouldToint.Chapter15.FilterSQPStep` and
  `ConnGouldToint.Chapter15.sqpFilter_margin_deletion_counterexample`.
* **Algorithm 15.5.1, rejected trials** (correction). The radius after a rejection is at most
  $\gamma_1 \Delta$ with $\gamma_1 < 1$. The printed parameter range allows $\gamma_1 = 1$, which
  permits a smooth nonstationary run that rejects the same trial forever. See
  `ConnGouldToint.Chapter15.FilterSQPParams` and
  `ConnGouldToint.Chapter15.sqpFilter_unchanged_rejected_radius_counterexample`.
* **Algorithm 15.5.1, radius update** (reading). An accepted trial with ratio below $\eta_1$, which
  can occur when the switching test fails, takes a radius in the shrink interval
  $[\gamma_0 \Delta, \gamma_1 \Delta]$. The printed radius update does not cover this case. See
  `ConnGouldToint.Chapter15.FilterSQPStep` and `ConnGouldToint.Chapter15.sqpFilterRadiusUpdate`.
* **Lemma 15.5.7** (correction). The radius threshold is strict, so the trial passes the objective
  margin strictly, as the acceptance rule requires. See `ConnGouldToint.Chapter15.lemma_15_5_7`.
* **Equations (15.5.7)–(15.5.9)** (reading). When the switching test holds, an accepted trial must
  have a positive predicted decrease. A zero or negative prediction does not certify an objective
  step. See `ConnGouldToint.Chapter15.filterSQPAccepted`.

**Chapter 16. Nonlinear Equations and Nonlinear Fitting**

* **Theorem 16.1.2** (correction). The bounds on the model residuals and their Jacobians hold
  throughout the model regions, not only at the centers. See
  `ConnGouldToint.Chapter16.theorem_16_1_2_unbounded_radii_counterexample`.
* **Theorem 16.1.4** (reading). At a root, positive definiteness of $\nabla^2 f$ is equivalent to
  injectivity of the Jacobian; a surjective Jacobian is not enough. See
  `ConnGouldToint.Chapter16.theorem_16_1_4_surjective_counterexample`.
* **Theorem 16.1.4** (correction). Exact residual models do not force convergence of the iterates to
  one regular root. The model-root result assumes convergence of the iterates and a trust region
  that contains a ball of fixed positive radius. See
  `ConnGouldToint.Chapter16.theorem_16_1_4_exact_model_counterexample`.
* **Equation (16.2.15)** (reading). The Hessian of the epigraph Lagrangian sums the residual
  Hessians over the residual components, weighted by the convex combination of the slopes;
  equivalently it weights the Hessians of the affine branches. See
  `ConnGouldToint.Chapter16.fderiv_fderiv_polyhedralEpigraphLagrangian`.
* **Equation (16.2.24)** (reading). The minimum of the merit function is the real number $h(c(x))$,
  and the set of minimizers is the singleton $\{h(c(x))\}$. See
  `ConnGouldToint.Chapter16.lemma_16_2_3`.
* **Equation (16.3.4)** (reading). The linearization maps a direction to the changes of the residual
  components. This transposes the printed matrix of column gradients and agrees with
  (16.3.8)–(16.3.9). See `ConnGouldToint.Chapter16.complementarityLinearization`.
* **Equation (16.3.8)** (generalization). The formula for the derivative of the merit function also
  holds where both arguments of a residual component vanish. See
  `ConnGouldToint.Chapter16.hasFDerivAt_complementarityMerit`.

**Chapter 17. Practicalities**

* **Equation (17.1.3)** (correction). The factor $1 - \eta_2$ in the denominator multiplies the
  common value and slope only, not the whole denominator. See
  `ConnGouldToint.Chapter17.printedInterpolation_counterexample`.
* **Equation (17.2.2)** (correction). The printed right-hand side $\|g\|^2 / \langle g, H g \rangle$
  is the ray parameter of the minimizer; the radius is this parameter times $\|g\|$. See
  `ConnGouldToint.Chapter17.cauchyInitialRadius_spec`.
* **Equations (17.2.7) and (17.2.11)–(17.2.13)** (reading). The shrink branch admits only factors
  strictly below $1$, and its fallback $\gamma_2$ is strictly below $1$. See
  `ConnGouldToint.Chapter17.safeguardedProbeFactor`.
* **Algorithm 17.2.1** (correction). A restart keeps the restart counter, so at most $j_{\max}$
  restarts happen, and each pass tests at most $i_{\max} + 1$ radii. See
  `ConnGouldToint.Chapter17.chooseInitialRadius`.
* **Algorithm 17.3.1** (correction). A zero slope stops the scan only if the curvature of the
  outgoing piece is nonnegative; at negative curvature the model still decreases. See
  `ConnGouldToint.Chapter17.cauchyQuadratic_lt_on_negative_stationary_segment`.
* **Algorithm 17.3.1** (reading). After the last breakpoint the path is constant, and the scan
  returns that breakpoint without asking for another one. See
  `ConnGouldToint.Chapter17.generalizedCauchyPoint`.
* **Equation (17.4.9)** (correction). The trial point subtracts the Lagrangian gradient $g - a$; the
  printed sign of the multiplier term subtracts $g + a$. See
  `ConnGouldToint.Chapter17.printedProjectionSign_counterexample`.

## Not formalized

No module of the library records an item of its unit as not formalized. Chapter 1 and Sections 2.1,
6.2, 7.1, 7.6, 8.2, 13.5 and 13.8 of the source have no module of their own. Of Section 6.2,
assumption AM.3 and equation (6.2.2) are formalized in
`NumlibSurface.ConnGouldToint.Chapter06.Section03`.
-/
