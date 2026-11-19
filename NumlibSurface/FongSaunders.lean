/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.FongSaunders.Section01
import NumlibSurface.FongSaunders.Section02
import NumlibSurface.FongSaunders.Section03
import NumlibSurface.FongSaunders.Section04
import NumlibSurface.FongSaunders.Section05

/-!
# Fong and Saunders, *CG versus MINRES: an empirical comparison*

This library formalizes the mathematical results of the paper [fong2012cg] by D. C.-L. Fong and M.
A. Saunders, which also appeared as Report SOL 2011-2R, Stanford University, 2011. The paper
compares the conjugate gradient method (CG) and MINRES on a real symmetric positive definite system
$Ax = b$, solved from $x_0 = 0$. It proves that the solution norms $\|x_k\|$ increase and the errors
$\|x^* - x_k\|$ and $\|x^* - x_k\|_A$ decrease for both methods, and that for MINRES, which
coincides with the conjugate residual method (CR) on such systems, also the residual norms $\|r_k\|$
and the normwise relative backward errors decrease. Section 3 applies these results to the stopping
rule (3.4), which is based on the normwise relative backward error. The library formalizes the
theorems of Sections 2 and 3, the exact relations behind the experiments of Section 4, and the
summary Table 5.1. The proofs specialize the Krylov subspace theory of the backbone, in particular
`Numlib.Krylov.CG`, `Numlib.Krylov.CR`, `Numlib.Krylov.Lanczos` and `Numlib.Krylov.Monotonicity`,
together with the projection results of `Numlib.Projection.Optimality`. The module
`NumlibSurface.FongSaunders.Section01` fixes the vocabulary that the other modules use and proves
the lemmas that connect it to the backbone; each later module imports the one before it.

## Coverage

All six numbered theorems of the paper are formalized: Theorems 2.1–2.5 and Theorem 3.1. The library
also formalizes the displayed equations (2.2), (3.2)–(3.6) and (4.1), the definitions (2.1) of a
MINRES iterate and (3.1) of an acceptable solution, the two algorithms of Table 2.1, the
monotonicity profile of Table 5.1, the indefinite example (4.2), and the theorem of Steihaug with
its CR and MINRES analogue that Section 4.2 states in prose. The unnumbered facts that these
statements use, such as the Lanczos relation and the termination of the algorithms, are formalized
too. The empirical half of the paper (test problems, figures and percentages of monotone steps) is
out of scope, and so are Table 5.2 and the discussion of LSQR and LSMR in Section 5, which state
results of other papers.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1 The setting, Krylov subspaces and the Lanczos process | `Section01` | Lanczos relation, $x^*$ |
| §2 Algorithms CG and CR, their monotonicity | `Section02` | Table 2.1, (2.1), Theorems 2.1–2.5 |
| §3 Normwise relative backward errors and stopping rules | `Section03` | (3.1)–(3.6), Theorem 3.1 |
| §4 The exact relations behind the numerical comparison | `Section04` | (4.1), Steihaug's theorem |
| §5 Table 5.1, the summary of monotonicity properties | `Section05` | Table 5.1, example (4.2) |

## Conventions

* A declaration is named for the item that it states: Theorem 2.3 for Algorithm CR is
  `FongSaunders.theorem_2_3_cr`, and equation (4.1) is `FongSaunders.equation_4_1`. Where one
  numbered item needs several declarations (its separate clauses, its CG and its MINRES form, or a
  strict beside a nonstrict version), a trailing word tells them apart, as in
  `FongSaunders.theorem_2_2_a`, `FongSaunders.theorem_3_1_minres` and
  `FongSaunders.theorem_2_3_strict`. Unnumbered constructions have descriptive names, such as
  `FongSaunders.cg`, `FongSaunders.cr`, `FongSaunders.krylov`, `FongSaunders.lanczosVec` and
  `FongSaunders.nrbe`. All declarations are in the namespace `FongSaunders`, and the module
  `SectionNN` formalizes §N.
* The paper works with a real symmetric positive definite system $Ax = b$ of order $n$, with the
  2-norm on vectors and the Frobenius norm on matrices.
* The space $\mathbb{R}^n$ is `FongSaunders.Vec n`, which is `EuclideanSpace ℝ (Fin n)`. On it,
  $\|\cdot\|$ is the 2-norm and `⟪x, y⟫_ℝ` is $x^T y$.
* The matrix $A$ is `A : Matrix (Fin n) (Fin n) ℝ`. Positive definiteness is `A.PosDef`, which over
  $\mathbb{R}$ means that $A$ is symmetric and $x^T A x > 0$ for $x \neq 0$. The lemma
  `FongSaunders.isSymmetricCoercive_of_posDef` turns it into the backbone hypothesis
  `LinearMap.IsSymmetricCoercive`, through which every backbone theorem applies.
* The product $Ax$ is `A ⬝ x`, which is `FongSaunders.mulVecE A x`, that is
  `Matrix.toEuclideanLin A x`.
* The matrix norm $\|A\|$ is the Frobenius norm, from `open scoped Matrix.Norms.Frobenius` in
  `Section03`.
* The starting point $x_0 = 0$ is an instantiation, not a hypothesis. The backbone states its Krylov
  theory for an arbitrary $x_0$, and every result here fixes $x_0 = 0$, as the paper does. Therefore
  the iterates lie in $\mathcal{K}_k(A, b)$, not in $\mathcal{K}_k(A, r_0)$. The choice $x_0 = 0$ is
  also the cause of the two restrictions to $k \ge 1$ in the deviations below. Because the ambient
  space is `FongSaunders.Vec n`, the instance hypotheses `FiniteDimensional` of the backbone are
  discharged automatically, and its real part `RCLike.re` reduces to the identity.

## Deviations from the source

**Section 1**

* **Section 1, Lanczos relations** (generalization). The matrix relations require symmetry
  in place of positive definiteness. The rectangular relation uses zero columns after
  termination and is stated for every $k$. See `FongSaunders.lanczos_relation` and
  `FongSaunders.lanczos_relation_term`.
* **Section 1, Lanczos basis and termination** (generalization). The Arnoldi basis,
  coordinate descriptions and grade bound also apply to nonsymmetric matrices. The
  spanning and coordinate results extend past termination by padding with zero vectors.
  See `FongSaunders.lanczosVec_orthonormal`, `FongSaunders.span_lanczosVec`,
  `FongSaunders.mem_krylov_iff_exists_lanczos` and `FongSaunders.lanczosTerm_le`.
* **Section 1.1, exact solution** (reading). The inverse formula gives $x^*=0$ for a
  singular matrix by the total inverse convention. See `FongSaunders.xstar`.
* **Section 1, Lanczos data** (generalization). The basis vectors are defined by Arnoldi
  for general $A$ and extended by zeros after the grade. The rectangular and square
  tridiagonal arrays are defined at every index, including the terminal index. See
  `FongSaunders.lanczosVec`, `FongSaunders.lanczosT` and `FongSaunders.lanczosTsq`.

**Section 2**

* **Energy norm** (reading). Section 2.1 writes $\|v\|_A$ for $v^T A v$; the library defines
  $\|v\|_A = (v^T A v)^{1/2}$, and every statement about it is unchanged by squaring. See
  `FongSaunders.energyNorm`.
* **Table 2.1** (generalization). The stopped algorithms are extended by a constant state
  after termination, with $\alpha_0=\beta_0=0$. See `FongSaunders.cg` and `FongSaunders.cr`.
* **Theorem 2.3** (generalization). The source proves nondecrease. The strict form proves
  a strict increase at every CR step with nonzero current residual. See
  `FongSaunders.theorem_2_3_strict`.
* **Equation (2.1)** (generalization). Residual minimization is defined even for a singular
  or nonsymmetric matrix. The paper applies it to nonsingular symmetric systems. See
  `FongSaunders.IsMINRESIterate`.
* **Section 2.2, MINRES uniqueness** (reading). The declaration establishes uniqueness
  for positive definite matrices, as needed to identify CR with MINRES. See
  `FongSaunders.isMINRESIterate_unique`.
* **Section 2.3, termination indices** (reading). The first zero residual defines the
  termination index. The formal definition returns $0$ if there is no such residual.
  See `FongSaunders.cgTerm` and `FongSaunders.crTerm`.
* **Theorem 2.5** (reading). The strict decrease applies up to the first zero residual.
  The extended sequence has zero error thereafter. See `FongSaunders.theorem_2_5_cr` and
  `FongSaunders.theorem_2_5_minres`.

**Section 3**

* **Introduction, stopping before CG** (correction). The comparison proved here assumes
  $\alpha=0$ in (3.4) and gives that MINRES stops no later than CG. For a positive matrix
  tolerance, CG can satisfy (3.4) first. See `FongSaunders.minres_stops_first`.
* **Nonzero data in the backward-error results** (reading). The ratios $\|E\| / \|A\|$ and
  $\|f\| / \|b\|$ presuppose $A \neq 0$ and $b \neq 0$, which the paper leaves implicit. With Lean's
  convention $t / 0 = 0$, every perturbation of a zero matrix would be feasible at every tolerance,
  and the results would be vacuous instead of sharp; so the results state both hypotheses. Under
  `A.PosDef` the first follows from the second by `FongSaunders.ne_zero_of_posDef`. See
  `FongSaunders.nrbePert_attains`, `FongSaunders.nrbe_isLeast` and
  `FongSaunders.isAcceptable_iff_nrbe_le_one`.
* **Theorem 3.1, the rows that divide by $\|x_k\|$** (reading). The paper's $E_0$ is undefined
  because $x_0 = 0$, while in Lean the ratio is $0$ at $k = 0$, below every later value; so the
  decrease of $\|E_k\| / \|A\|$, and of $\xi_k$ when $\beta = 0$, is stated for $k \ge 1$. For
  $\beta > 0$ the denominator of $\xi_k$ is positive at $k = 0$, and
  `FongSaunders.nrbe_minres_antitone` states the decrease for all $k$. See
  `FongSaunders.theorem_3_1_minres`, `FongSaunders.theorem_3_1_cr` and
  `FongSaunders.nrbe_minres_antitoneOn`.
* **Equations (3.1)–(3.4), undefined ratios** (reading). The definitions use Lean's
  zero-denominator convention, while the stopping-rule equivalence requires a positive
  denominator. See `FongSaunders.IsAcceptable`, `FongSaunders.nrbe`,
  `FongSaunders.nrbePhi`, `FongSaunders.nrbePertA` and `FongSaunders.nrbe_le_one_iff`.
* **Theorem 3.1, CG clause** (reading). The theorem declarations formalize the
  monotonicity claims for CR and MINRES. The source also states failure of the general
  monotonicity claim for CG with $\alpha,\beta>0$. See `FongSaunders.theorem_3_1_minres`.

**Section 4**

* **Section 4.1.1, product of residual ratios** (generalization). The exact identity
  holds for arbitrary sequences with nonzero denominators. The approximation by the
  stopping tolerance is outside the identity. See `FongSaunders.prod_ratio_residual`.
* **Example (4.2)** (reading). The statements express failure of monotonicity by existence,
  with the printed matrix and right-hand side as witnesses. See
  `FongSaunders.minres_norm_iterate_not_monotone` and
  `FongSaunders.minres_backwardError_not_antitoneOn`.
* **Equation (4.1)** (reading). The result assumes $r_k^M \neq 0$, excluding the step
  that first reaches the exact solution. See `FongSaunders.equation_4_1` and
  `FongSaunders.equation_4_1_minres`.
* **Section 4.2, MINRES coordinates** (reading). The source considers symmetric systems that
  are nonsingular or consistent. The coordinate results here require positive definiteness.
  See `FongSaunders.minres_subproblem` and `FongSaunders.minres_coeff_unique`.
* **Steihaug's theorem for CG** (reading). The curvature test uses the direction
  $p_{j-1}$ entering iteration $j$, as in Table 2.1. See `FongSaunders.steihaug_cg`.
* **Steihaug's theorem for CR and MINRES** (reading). The paper assumes $p_j^T A p_j > 0$ and
  $r_j^T A r_j > 0$ for $1 \le j \le k$, a local hypothesis that its proof through Theorem 2.2(d)
  does not support. The library gives a sufficient condition using $r_j^T A r_j > 0$ at every
  iteration before termination. See `FongSaunders.steihaug_cr`.

**Section 5**

* **The blank CG entries of Table 5.1** (reading). A blank entry is read as the existence of a
  symmetric positive definite system on which the row fails to be monotone; the witnesses are
  $A = \operatorname{diag}(1, 9)$ with $b = (3, 1)^T$, and $A = \operatorname{diag}(1, 13, 16)$ with
  $b = (1, 5, 1)^T$. See `FongSaunders.cg_norm_residual_not_antitone` and
  `FongSaunders.cg_backwardError_not_antitoneOn`.
* **The row $\|r_k\| / \|x_k\|$ of Table 5.1** (reading). The ratio is undefined at $k = 0$ because
  $x_0 = 0$; the row is stated for $k \ge 1$. See `FongSaunders.MINRESProfile`.

## Not formalized

**Section 4**

* **The test set and the diagonal preconditioning of Section 4.** They are empirical.
* **Figures 4.1–4.8 and their percentages of monotone steps.** They are empirical.
* **The "cumulative minimum" heuristic of Section 4.1.1.** It is empirical.
* **The relation to MINRES-QLP in Section 4.2.** It rests on the work of Choi, Paige and Saunders,
  the paper draws no theorem from it, and its missing ingredient, the QLP factorization
  $R_k P_k = L_k$, belongs in the backbone module `Numlib.Krylov.Singular`.

**Section 5**

* **Table 5.2.** It states results of other papers.
* **The discussion of LSQR and LSMR in Section 5.** It states results of other papers.
-/
