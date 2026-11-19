/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.CrossProduct
import Numlib.Conditioning.LeastSquares
import Numlib.LinearAlgebra.Matrix.RankRevealing
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section02

/-!
# Golub and Van Loan, Section 5.3: The full-rank least-squares problem

This module formalizes §5.3 of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full
column rank and let $b \in \mathbb{R}^m$. The least-squares problem asks for the vector $x_{LS}$
that minimizes $\|Ax - b\|_2$. This vector is unique, it solves the normal equations $A^TAx = A^Tb$,
and its residual is $r_{LS} = b - Ax_{LS}$ with $\rho_{LS} = \|r_{LS}\|_2$.

The module states the normal equations and the gradient of $\frac12\|Ax - b\|_2^2$ (§5.3.1), the SVD
expansion (5.3.2)–(5.3.3), the method of normal equations (Algorithm 5.3.1) and its accuracy
(5.3.4), the QR solution (5.3.5), the Householder LS solution (Algorithm 5.3.2) with its backward
error (5.3.6)–(5.3.8), least squares by modified Gram–Schmidt (§5.3.5), the sensitivity of the
problem (Theorem 5.3.1 with (5.3.9), (5.3.10), (5.3.15) and (5.3.16)), the augmented system (5.3.20)
with its QR solution and iterative improvement (§5.3.8), and the nearness problems for points, lines
and planes in $\mathbb{R}^3$ of §5.3.9, (5.3.21)–(5.3.29). The proofs use the least-squares theory
of `Numlib.LinearAlgebra.Matrix.LeastSquares` and `Numlib.Conditioning.LeastSquares`, and the
programs and rounding results of §3.1, §4.2, §5.1 and §5.2.

## Main definitions

* Algorithm 5.3.1, `GolubVanLoan.Chapter05.algorithm_5_3_1`: the method of normal equations: form
  $A^TA$ and $A^Tb$, factor $A^TA = GG^T$ by Cholesky, and solve two triangular systems.
* Algorithm 5.3.2, `GolubVanLoan.Chapter05.algorithm_5_3_2`: the Householder LS solution as printed:
  Householder QR, then $Q^Tb$ with each $\beta_j$ recomputed as $2/v^Tv$, then back substitution.
* Algorithm 5.3.2, `GolubVanLoan.Chapter05.householderLSSolve`: the stages of the printed algorithm
  after the QR factorization.
* Algorithm 5.3.2 with the returned $\beta$, `GolubVanLoan.Chapter05.householderLS`: the same solver
  with the $\beta_j$ that Householder QR returned.
* Equation (5.3.10), `GolubVanLoan.Chapter05.nuLS`: $\nu_{LS} =
  \|Ax_{LS}\|_2/(\sigma_n(A)\|x_{LS}\|_2)$.
* Theorem 5.3.1, `GolubVanLoan.Chapter05.thetaLS`: the angle $\theta_{LS}$ with
  $\sin\theta_{LS} = \|r_{LS}\|_2/\|b\|_2$.
* §5.3.8, `GolubVanLoan.Chapter05.lsIterativeImprovement`: iterative improvement of the augmented
  system, with the residuals in higher precision.
* §5.3.9, `GolubVanLoan.Chapter05.crossMatrix`: the cross-product matrix $v^c$ with
  $p \times q = p^cq$.

## Main results

* §5.3.1, `GolubVanLoan.Chapter05.isLeastSquaresSolution_iff_normalEquations`: $x$ minimizes
  $\|Ax - b\|_2$ if and only if $A^TAx = A^Tb$; for full column rank the minimizer is unique and
  $A^TA$ is positive definite.
* §5.3.1, `GolubVanLoan.Chapter05.gradient_leastSquaresObjective`: $\frac12\|Ax - b\|_2^2$ has the
  gradient $A^T(Ax - b)$.
* Equation (5.3.2), `GolubVanLoan.Chapter05.equation_5_3_2`:
  $x_{LS} = \sum_{i=1}^n (u_i^Tb/\sigma_i)v_i$.
* Equation (5.3.3), `GolubVanLoan.Chapter05.equation_5_3_3`:
  $\rho_{LS}^2 = \sum_{i=n+1}^m (u_i^Tb)^2$.
* Algorithm 5.3.1, `GolubVanLoan.Chapter05.algorithm_5_3_1_spec`: in exact arithmetic the output
  minimizes $\|Ax - b\|_2$.
* Equation (5.3.4), `GolubVanLoan.Chapter05.equation_5_3_4`: a solution of the normal equations
  perturbed by $\eta$ has relative error at most $\eta\kappa_2(A)^2/(1 - \eta\kappa_2(A)^2)$.
* Equation (5.3.4), `GolubVanLoan.Chapter05.equation_5_3_4_rounding`: the same bound for the runs of
  the Cholesky stage of Algorithm 5.3.1.
* Equation (5.3.5), `GolubVanLoan.Chapter05.equation_5_3_5`: with $A = QR$ and $Q^Tb = [c; d]$,
  $\|Ax - b\|_2^2 = \|R_1x - c\|_2^2 + \|d\|_2^2$, and $x_{LS} = R_1^{-1}c$.
* Algorithm 5.3.2, `GolubVanLoan.Chapter05.algorithm_5_3_2_spec`: in exact arithmetic the output
  minimizes $\|Ax - b\|_2$ when every returned $\beta_j$ is nonzero.
* Algorithm 5.3.2, `GolubVanLoan.Chapter05.algorithm_5_3_2_counterexample`: for $A = I_2$ and
  $b = (1, 0)^T$ the printed algorithm returns $(-1, 0)^T$.
* Algorithm 5.3.2 with the returned $\beta$, `GolubVanLoan.Chapter05.householderLS_spec`: in exact
  arithmetic the output minimizes $\|Ax - b\|_2$ for every $A$ of full column rank.
* Equation (5.3.6), `GolubVanLoan.Chapter05.equation_5_3_6`: the computed Householder LS solution
  solves exactly a nearby least-squares problem.
* Equation (5.3.7), `GolubVanLoan.Chapter05.equation_5_3_7`: the bound on $\|\delta A\|_F$ in
  (5.3.6).
* Equation (5.3.8), `GolubVanLoan.Chapter05.equation_5_3_8`: the bound on $\|\delta b\|_2$ in
  (5.3.6).
* §5.3.5, `GolubVanLoan.Chapter05.mgs_augmented`: modified Gram–Schmidt on $[A \mid b]$ gives
  $z = Q_1^Tb$, the least-squares solutions are the solutions of $R_1x = z$, and
  $|\rho| = \rho_{LS}$.
* Equation (5.3.9), `GolubVanLoan.Chapter05.equation_5_3_9`: the 2-norms of $A(A^TA)^{-1}A^T$,
  $(A^TA)^{-1}A^T$, $I - A(A^TA)^{-1}A^T$ and $(A^TA)^{-1}$.
* §5.3.6, `GolubVanLoan.Chapter05.nuLS_le_kappa2`: $\nu_{LS} \le \kappa_2(A)$.
* Theorem 5.3.1, `GolubVanLoan.Chapter05.theorem_5_3_1`: the bounds (5.3.11) on $x_{LS}$ and
  (5.3.12) on $r_{LS}$ under perturbations of relative size $\varepsilon$, up to $K\varepsilon^2$.
* Theorem 5.3.1, `GolubVanLoan.Chapter05.theorem_5_3_1_a`: the bound (5.3.11) in rigorous form.
* Theorem 5.3.1, `GolubVanLoan.Chapter05.theorem_5_3_1_b`: the bound (5.3.12) in rigorous form.
* Equation (5.3.15), `GolubVanLoan.Chapter05.equation_5_3_15`: the derivative of
  $x(t) = (A + tE)^+(b + tf)$ at $t = 0$.
* Equation (5.3.16), `GolubVanLoan.Chapter05.equation_5_3_16`:
  $\cos\theta_{LS} = \|Ax_{LS}\|_2/\|b\|_2$ and $\tan\theta_{LS} = \|r_{LS}\|_2/\|Ax_{LS}\|_2$.
* Equation (5.3.20), `GolubVanLoan.Chapter05.equation_5_3_20`: a solution of the augmented system
  gives a least-squares solution, and the augmented matrix is nonsingular if and only if
  $\operatorname{rank}(A) = n$.
* §5.3.8, `GolubVanLoan.Chapter05.augmentedSolve_qr`: the solution of the augmented system through
  the QR factorization of $A$.
* Equations (5.3.21)–(5.3.25), `GolubVanLoan.Chapter05.equation_5_3_21` to
  `GolubVanLoan.Chapter05.equation_5_3_25`: identities for the cross product and the cross-product
  matrix.
* Equation (5.3.26), `GolubVanLoan.Chapter05.equation_5_3_26`: the point of a line closest to a
  point.
* Equations (5.3.27)–(5.3.28), `GolubVanLoan.Chapter05.equation_5_3_27` and
  `GolubVanLoan.Chapter05.equation_5_3_28`: the closest points of two non-parallel lines.
* Equation (5.3.29), `GolubVanLoan.Chapter05.equation_5_3_29`: the point of a plane closest to a
  point.

## Conventions

* Least-squares statements are on `EuclideanSpace ℝ (Fin m)`. "$x$ minimizes $\|Ax - b\|_2$" is
  `Matrix.IsLeastSquaresSolution A b x`. The vectors of the programs have type `Fin m → ℝ` and are
  converted by `WithLp.toLp 2`.
* "$A$ has full column rank", $\operatorname{rank}(A) = n$, is `LinearIndependent ℝ Aᵀ`. The
  solution $x_{LS}$ is the pseudoinverse `A.pinv` applied to $b$, and $r_{LS} = b - Ax_{LS}$.
* Matrix norms are operator 2-norms (`Matrix.Norms.L2Operator`), except the Frobenius norms of
  (5.3.6)–(5.3.7). $\kappa_2(A)$ is `GolubVanLoan.Chapter05.kappa2`, (5.2.4), and $\sigma_n(A)$ is
  the least singular value `⨅ i, A.colSingularValues i`.
* In (5.3.2)–(5.3.3), $u_i$ and $v_i$ are the columns of the factors of an SVD
  `Matrix.IsSVD A U σ V`, and $u_i^Tb$ is `U.col i ⬝ᵥ b`. Indices are 0-based: the book's
  $u_{n+1}, \dots, u_m$ are the columns `i` with `n ≤ i`.
* The programs follow the conventions of `NumlibSurface.GolubVanLoan`. Algorithm 5.3.1 calls
  Algorithm 1.1.1, Algorithm 4.2.1 and the Cholesky solve `GolubVanLoan.Chapter04.solveCholesky`
  (Algorithms 3.1.3 and 3.1.4). Algorithm 5.3.2 calls Algorithms 5.2.1 and 3.1.2. A computed
  quantity is an element of the run set of its program in a rounding model `fp`, with the hook
  `fp.round`; exact arithmetic is the monad `Id` with the hook `pure`.

## Implementation notes

* The rounding results (5.3.6)–(5.3.8) assume an idempotent rounding model
  (`FloatingPoint.RoundingModel.IsIdempotent`), and they state explicit constants
  $\gamma_k = ku/(1 - ku)$.
* The cross-product matrix is defined here, because Mathlib has the cross product `⨯₃` but no matrix
  form of it.

## Deviations from the source

* **Equation (5.3.5)** (generalization). The QR residual split is independent of rank. The
  inverse formula for the minimizer uses full column rank. See
  `GolubVanLoan.Chapter05.equation_5_3_5`.
* **§5.3.5, augmented modified Gram–Schmidt** (reading). The exact theorem requires independent
  columns of $[A\mid b]$ to justify the final normalization. See
  `GolubVanLoan.Chapter05.mgs_augmented`.
* **Equation (5.3.9)** (reading). The projector norm identities assume $0<n<m$. A full-rank
  square matrix has zero residual projector. See `GolubVanLoan.Chapter05.equation_5_3_9`.
* **§5.3.8, iterative improvement** (reading). The program takes an iteration count and two
  rounding functions. The exact theorem gives a solution after any positive number of
  iterations. See `GolubVanLoan.Chapter05.lsIterativeImprovement` and
  `GolubVanLoan.Chapter05.lsIterativeImprovement_spec`.
* **Equation (5.3.25)** (reading). The normalized inner product requires nonzero vectors. See
  `GolubVanLoan.Chapter05.equation_5_3_25`.
* **Equation (5.3.3)** (typo). The source prints the upper summation limit as $2$; it is $m$. See
  `GolubVanLoan.Chapter05.equation_5_3_3`.
* **Equation (5.3.4)** (reading). The source estimates the relative error as
  $\approx u\kappa_2(A)^2$. The theorem states the rigorous bound
  $\eta\kappa_2(A)^2/(1 - \eta\kappa_2(A)^2)$. See `GolubVanLoan.Chapter05.equation_5_3_4`.
* **Algorithm 5.3.2** (correction). The source recomputes $\beta_j = 2/v^Tv$, which is wrong when
  `house` returned $\beta_j = 0$; the correctness statement needs every returned $\beta_j \neq 0$.
  See `GolubVanLoan.Chapter05.algorithm_5_3_2_spec`,
  `GolubVanLoan.Chapter05.algorithm_5_3_2_counterexample` and
  `GolubVanLoan.Chapter05.householderLS`.
* **Equations (5.3.6)–(5.3.8)** (reading). The source states first-order bounds with the constants
  of Lawson and Hanson. The theorems state rigorous bounds with explicit $\gamma$ constants, for
  runs with nonzero computed $\beta_j$ and nonsingular $\hat R_1$. See
  `GolubVanLoan.Chapter05.equation_5_3_6`.
* **Theorem 5.3.1** (reading). The terms $O(\varepsilon^2)$ are read as $K\varepsilon^2$ for
  $\varepsilon \le \varepsilon_0$. See `GolubVanLoan.Chapter05.theorem_5_3_1`.
* **Theorem 5.3.1, (5.3.11)** (generalization). A rigorous form with $\sigma_n(A) - \|\delta A\|_2$
  in place of $\sigma_n(A)$ holds without the hypothesis $r_{LS} \neq 0$. See
  `GolubVanLoan.Chapter05.theorem_5_3_1_a`.
* **Theorem 5.3.1, (5.3.12)** (reading). A rigorous form holds with
  $\|A\|_2/(\sigma_n(A) - \|\delta A\|_2)$ in place of $\kappa_2(A)$ in the last term. See
  `GolubVanLoan.Chapter05.theorem_5_3_1_b`.
* **Equations (5.3.27)–(5.3.28)** (correction). The source omits the hypothesis that the lines are
  not parallel, $r \neq 0$; for $r = 0$ the formulas divide by zero. See
  `GolubVanLoan.Chapter05.equation_5_3_27`.
* **Equation (5.3.29)** (correction). Three distinct points do not determine a plane; the points
  must not be collinear, $v \neq 0$. See `GolubVanLoan.Chapter05.equation_5_3_29`.

## Not formalized

* **The $p$-norm example of the introduction.**
* **The numerical examples of §5.3.1 and §5.3.2**, in which $\mathrm{fl}(A^TA)$ is singular.
* **Equations (5.3.18)–(5.3.19).** They are heuristic readings.
* **The comparison of methods in §5.3.7.** It is prose.
* **Björck's claim on the gain of correct digits in iterative improvement (§5.3.8).**
* **Equation (5.3.17).** It is the first-order expansion inside the proof of Theorem 5.3.1.
* **The Problems.**
-/

open FloatingPoint Matrix WithLp

namespace GolubVanLoan.Chapter05

variable {m n : ℕ}

/-! ### §5.3.1 Implications of full rank -/

section FullRank

/-- **Section 5.3.1** of [golub2013matrix], the normal equations. Let
$A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$. A vector $x \in \mathbb{R}^n$
minimizes $\|Ax - b\|_2$ if and only if it solves the normal equations
$$A^TAx = A^Tb.$$
If $x$ and $y$ both minimize $\|Ax - b\|_2$, then $A(y - x) = 0$. If $A$ has full column rank,
then the minimizer $x_{LS}$ is unique and $A^TA$ is positive definite.

The source states the second part for minimizers $x$ and $x + z$: then $Az = 0$. Full column
rank is `LinearIndependent ℝ Aᵀ`, and "$x$ minimizes $\|Ax - b\|_2$" is
`Matrix.IsLeastSquaresSolution A b x`. -/
theorem isLeastSquaresSolution_iff_normalEquations {A : Matrix (Fin m) (Fin n) ℝ}
    (b : EuclideanSpace ℝ (Fin m)) :
    (∀ x, IsLeastSquaresSolution A b x ↔ toEuclideanLin (Aᵀ * A) x = toEuclideanLin Aᵀ b) ∧
      (∀ x y, IsLeastSquaresSolution A b x → IsLeastSquaresSolution A b y →
        toEuclideanLin A (y - x) = 0) ∧
      (LinearIndependent ℝ Aᵀ → (∃! x, IsLeastSquaresSolution A b x) ∧ (Aᵀ * A).PosDef) := by
  refine ⟨fun x => ?_, fun x y hx hy => hx.toEuclideanLin_sub_eq_zero hy, fun hA => ?_⟩
  · rw [Matrix.isLeastSquaresSolution_iff_normalEquations, conjTranspose_eq_transpose_of_trivial]
  · refine ⟨existsUnique_isLeastSquaresSolution hA b, ?_⟩
    have := posDef_conjTranspose_mul_self_of_linearIndependent hA
    rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **Section 5.3.1** of [golub2013matrix], the gradient. Let $A \in \mathbb{R}^{m \times n}$ and
$b \in \mathbb{R}^m$. At every $x \in \mathbb{R}^n$ the function
$\phi(x) = \frac12\|Ax - b\|_2^2$ has the gradient
$$\nabla\phi(x) = A^T(Ax - b).$$
So solving the normal equations is the same as solving the gradient equation $\nabla\phi = 0$. -/
theorem gradient_leastSquaresObjective (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (fun y => ‖toEuclideanLin A y - b‖ ^ 2 / 2)
      (toEuclideanLin Aᵀ (toEuclideanLin A x - b)) x :=
  hasGradientAt_leastSquaresObjective A b x

end FullRank

/-! ### §5.3.2 The method of normal equations -/

section NormalEquations

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The first step of Algorithm 5.3.1 of [golub2013matrix]: the lower triangle of $C = A^TA$. Row by
row, each entry $c_{ij} = A(:, i)^TA(:, j)$ with $j \le i$ is computed by Algorithm 1.1.1 with
the hook `rnd`, and the strict upper triangle is $0$. -/
noncomputable def gramLower (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (L : Matrix (Fin n) (Fin n) ℝ) i => do
    let r ← ((List.finRange n).filter (· ≤ i)).foldlM (fun (r : Fin n → ℝ) j => do
      let c ← Chapter01.algorithm_1_1_1 rnd (fun k => A k i) (fun k => A k j)
      pure (Function.update r j c)) 0
    pure (L.updateRow i r)) 0

/-- The second step of Algorithm 5.3.1 of [golub2013matrix]: the product $d = A^Tb$, each entry
$d_i = A(:, i)^Tb$ computed by Algorithm 1.1.1 with the hook `rnd`. -/
noncomputable def transposeMulVec (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (d : Fin n → ℝ) i => do
    let c ← Chapter01.algorithm_1_1_1 rnd (fun k => A k i) b
    pure (Function.update d i c)) 0

/-- **Algorithm 5.3.1** of [golub2013matrix] (Normal Equations). Given
$A \in \mathbb{R}^{m \times n}$ with $\operatorname{rank}(A) = n$ and $b \in \mathbb{R}^m$, the
algorithm computes a vector $x_{LS}$ that minimizes $\|Ax - b\|_2$:
```
Compute the lower triangular portion of C = AᵀA.
Form the matrix-vector product d = Aᵀb.
Compute the Cholesky factorization C = GGᵀ.
Solve Gy = d and Gᵀx_LS = y.
```
The program computes the lower triangle of $C$ by `GolubVanLoan.Chapter05.gramLower` and $d$ by
`GolubVanLoan.Chapter05.transposeMulVec`, and it fills the upper triangle of $C$ by symmetry,
with no rounding. The Cholesky factorization is Algorithm 4.2.1, whose output holds $G$ in its
lower triangle. The two triangular solves are `GolubVanLoan.Chapter04.solveCholesky`, that is,
Algorithms 3.1.3 and 3.1.4 on the lower triangle and on its transpose; §4.2.6 analyses their
rounding errors (see `GolubVanLoan.Chapter05.equation_5_3_4_rounding`). The program has no
hypothesis on $A$. -/
noncomputable def algorithm_5_3_1 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    M (Fin n → ℝ) := do
  let L ← gramLower rnd A
  let C : Matrix (Fin n) (Fin n) ℝ := of fun i j => if j ≤ i then L i j else L j i
  let d ← transposeMulVec rnd A b
  let F ← Chapter04.algorithm_4_2_1 rnd C
  Chapter04.solveCholesky rnd F d

end Programs

/-- A loop that writes each listed row $i$ of a matrix with a value $g_i$ that does not depend on
the state gives the matrix with row $g_i$ at each listed $i$ and the initial row elsewhere. -/
private theorem foldl_updateRow_eq {k l : ℕ} (g : Fin k → Fin l → ℝ) (L : List (Fin k))
    (L₀ : Matrix (Fin k) (Fin l) ℝ) :
    L.foldl (fun (N : Matrix (Fin k) (Fin l) ℝ) i => N.updateRow i (g i)) L₀ =
      of fun i => if i ∈ L then g i else L₀ i :=
  List.foldl_update_eq_ite g L L₀

/-- In exact arithmetic, `GolubVanLoan.Chapter05.gramLower` computes the lower triangle of $A^TA$:
its entry $(i, j)$ is $(A^TA)_{ij}$ for $j \le i$ and $0$ for $j > i$. -/
theorem gramLower_pure (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (gramLower pure A) = of fun i j => if j ≤ i then (Aᵀ * A) i j else 0 := by
  simp only [gramLower, List.idRun_foldlM, Id.run_bind, Chapter01.algorithm_1_1_1_spec,
    Id.run_pure]
  rw [foldl_updateRow_eq]
  ext i j
  simp only [of_apply, List.mem_finRange, ↓reduceIte, List.foldl_update_eq_ite, List.mem_filter,
    decide_eq_true_eq, true_and]
  split_ifs
  · simp [Matrix.mul_apply, dotProduct]
  · rfl

/-- In exact arithmetic, `GolubVanLoan.Chapter05.transposeMulVec` computes $A^Tb$. -/
theorem transposeMulVec_pure (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Id.run (transposeMulVec pure A b) = Aᵀ *ᵥ b := by
  simp only [transposeMulVec, List.idRun_foldlM, Id.run_bind, Chapter01.algorithm_1_1_1_spec,
    Id.run_pure]
  rw [List.foldl_update_eq_ite]
  ext i
  simp [mulVec, dotProduct]

/-- **Algorithm 5.3.1** of [golub2013matrix], correctness in exact arithmetic. Let
$A \in \mathbb{R}^{m \times n}$ have full column rank and let $b \in \mathbb{R}^m$. Then the
output of Algorithm 5.3.1 in exact arithmetic minimizes $\|Ax - b\|_2$.

The matrix $A^TA$ is positive definite, Algorithm 4.2.1 returns its Cholesky factor $G$ with
$A^TA = GG^T$, and the two triangular solves give $GG^Tx = A^Tb$, the normal equations. Exact
arithmetic is the monad `Id` with the hook `pure`. -/
theorem algorithm_5_3_1_spec {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (b : Fin m → ℝ) :
    IsLeastSquaresSolution A (toLp 2 b) (toLp 2 (Id.run (algorithm_5_3_1 pure A b))) := by
  have hPD : (Aᵀ * A).PosDef := ((isLeastSquaresSolution_iff_normalEquations (toLp 2 b)).2.2 hA).2
  have hC : (of fun i j => if j ≤ i then Id.run (gramLower pure A) i j
      else Id.run (gramLower pure A) j i : Matrix (Fin n) (Fin n) ℝ) = Aᵀ * A := by
    rw [gramLower_pure]
    ext i j
    simp only [of_apply]
    split_ifs with h1 h2
    · rfl
    · rw [← transpose_apply (Aᵀ * A), transpose_mul, transpose_transpose]
    · exact absurd (le_of_lt (not_le.1 h1)) h2
  set F := Id.run (Chapter04.algorithm_4_2_1 pure (Aᵀ * A)) with hF
  set G : Matrix (Fin n) (Fin n) ℝ := F - F.strictUpper with hG
  have hGc : G = cholesky (Aᵀ * A) := (Chapter04.algorithm_4_2_1_spec hPD).1
  have hGl : G.IsLowerTriangular := hGc ▸ isLowerTriangular_cholesky _
  have hGd : ∀ i, G i i ≠ 0 := fun i => hGc ▸ (Chapter04.cholesky_diag_pos hPD i).ne'
  have hGG : G * Gᵀ = Aᵀ * A := by rw [hGc]; exact Chapter04.cholesky_mul_transpose hPD
  have hrun : Id.run (algorithm_5_3_1 pure A b) = Id.run (Chapter03.algorithm_3_1_4 pure Gᵀ
      (Id.run (Chapter03.algorithm_3_1_3 pure G (Aᵀ *ᵥ b)))) := by
    simp only [algorithm_5_3_1, Chapter04.solveCholesky, Id.run_bind, transposeMulVec_pure]
    rw [hC]
  rw [hrun]
  set y := Id.run (Chapter03.algorithm_3_1_3 pure G (Aᵀ *ᵥ b)) with hy
  set x := Id.run (Chapter03.algorithm_3_1_4 pure Gᵀ y) with hx
  have h1 : G *ᵥ y = Aᵀ *ᵥ b := Chapter03.algorithm_3_1_3_spec hGl hGd _
  have h2 : Gᵀ *ᵥ x = y := Chapter03.algorithm_3_1_4_spec hGl.transpose_isUpperTriangular
    (fun i => by rw [transpose_apply]; exact hGd i) _
  rw [(isLeastSquaresSolution_iff_normalEquations (toLp 2 b)).1, toEuclideanLin_toLp,
    toEuclideanLin_toLp, ← hGG, ← mulVec_mulVec, h2, h1]

/-- A nonzero vector of $\mathbb{R}^n$ forces $n \ge 1$. -/
private theorem neZero_of_ne_zero {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    NeZero n := by
  refine ⟨fun hn => hx ?_⟩
  subst hn
  ext i
  exact i.elim0

open scoped Matrix.Norms.L2Operator in
/-- **Equation (5.3.4)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, and let $b \in \mathbb{R}^m$ be such that $x_{LS} = A^+b$ is nonzero. Let
$E \in \mathbb{R}^{n \times n}$ and $\eta \in \mathbb{R}$ satisfy $\|E\|_2 \le \eta\|A^TA\|_2$
and $\eta\kappa_2(A)^2 < 1$. If $\hat x_{LS}$ solves the perturbed normal equations
$(A^TA + E)\hat x_{LS} = A^Tb$, then
$$\frac{\|\hat x_{LS} - x_{LS}\|_2}{\|x_{LS}\|_2} \le \frac{\eta\kappa_2(A)^2}{1 -
  \eta\kappa_2(A)^2}.$$
Moreover $\kappa_2(A^TA) = \kappa_2(A)^2$.

**Reading.** The source argues "from what we know about the roundoff properties of the Cholesky
factorization" that the computed solution satisfies such perturbed normal equations with
$\eta = cu$, and it concludes that the relative error is $\approx u\kappa_2(A)^2$. The theorem
states the rigorous bound for every perturbation of this size; the printed estimate is its
first-order form.

Here $\kappa_2$ and $x_{LS}$ are `GolubVanLoan.Chapter05.kappa2` and `A.pinv` applied to $b$.
For the runs of Algorithm 5.3.1 see `GolubVanLoan.Chapter05.equation_5_3_4_rounding`. -/
theorem equation_5_3_4 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {b : EuclideanSpace ℝ (Fin m)} {E : Matrix (Fin n) (Fin n) ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin (Aᵀ * A + E) x = toEuclideanLin Aᵀ b) {η : ℝ}
    (hE : ‖E‖ ≤ η * ‖Aᵀ * A‖) (hη : η * kappa2 A ^ 2 < 1)
    (hx0 : toEuclideanLin A.pinv b ≠ 0) :
    ‖x - toEuclideanLin A.pinv b‖ / ‖toEuclideanLin A.pinv b‖ ≤
        η * kappa2 A ^ 2 / (1 - η * kappa2 A ^ 2) ∧
      kappa2 (Aᵀ * A) = kappa2 A ^ 2 := by
  have := neZero_of_ne_zero hx0
  refine ⟨norm_normalEquations_sub_le hA rfl
    (by rwa [conjTranspose_eq_transpose_of_trivial])
    (by rwa [conjTranspose_eq_transpose_of_trivial]) hη hx0, ?_⟩
  have h := pinvCondNumberLp_two_conjTranspose_mul_self hA
  rwa [conjTranspose_eq_transpose_of_trivial] at h

open scoped Matrix.Norms.L2Operator in
/-- **Equation (5.3.4)** of [golub2013matrix], for the runs of Algorithm 5.3.1. Let
$A \in \mathbb{R}^{m \times n}$ have full column rank, and let $b \in \mathbb{R}^m$ be such that
$x_{LS} = A^+b$ is nonzero. Let the unit roundoff $u$ satisfy $(3n + 3)u < 1$ and
$n\gamma_{n+3} < 1$, where $\gamma_k = ku/(1 - ku)$, and let $\eta$ satisfy
$$\eta \ge \frac{n\gamma_{3n+3}}{1 - n\gamma_{n+3}}, \qquad \eta\kappa_2(A)^2 < 1.$$
Let $F$ be computed by Algorithm 4.2.1 from $C = A^TA$, with every diagonal entry of $F$
nonzero, and let $\hat x$ be computed from $F$ and $d = A^Tb$ by the triangular solves of
Algorithm 5.3.1. Then
$$\frac{\|\hat x - x_{LS}\|_2}{\|x_{LS}\|_2} \le \frac{\eta\kappa_2(A)^2}{1 -
  \eta\kappa_2(A)^2}.$$

As in the source, no roundoff errors occur in the formation of $C = A^TA$ and $d = A^Tb$. The
triangular solves are `GolubVanLoan.Chapter04.solveCholesky`, the solve stage of
`GolubVanLoan.Chapter05.algorithm_5_3_1`. The proof gives the backward error
$(A^TA + E)\hat x = A^Tb$ with $\|E\|_2 \le \eta\|A^TA\|_2$ of §4.2.6
(`GolubVanLoan.Chapter04.cholesky_backward_error`) to `GolubVanLoan.Chapter05.equation_5_3_4`.

**Reading.** Exact Gram and RHS as in source, with quantitative gamma assumptions and conclusion.
-/
theorem equation_5_3_4_rounding {fp : RoundingModel ℝ} (hn : ((3 * n + 3 : ℕ) : ℝ) * fp.u < 1)
    (hγ : n * gamma fp.u (n + 3) < 1) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) {η : ℝ}
    (hηc : n * gamma fp.u (3 * n + 3) / (1 - n * gamma fp.u (n + 3)) ≤ η)
    (hη : η * kappa2 A ^ 2 < 1) (hx0 : toEuclideanLin A.pinv (toLp 2 b) ≠ 0) :
    ∀ F ∈ (Chapter04.algorithm_4_2_1 fp.round (Aᵀ * A)).run, (∀ j, F j j ≠ 0) →
      ∀ x ∈ (Chapter04.solveCholesky fp.round F (Aᵀ *ᵥ b)).run,
        ‖toLp 2 x - toEuclideanLin A.pinv (toLp 2 b)‖ / ‖toEuclideanLin A.pinv (toLp 2 b)‖ ≤
          η * kappa2 A ^ 2 / (1 - η * kappa2 A ^ 2) := by
  intro F hF hd x hx
  obtain ⟨E, hE, hEn⟩ := Chapter04.cholesky_backward_error hn hγ
    (by rw [IsSymm, transpose_mul, transpose_transpose])
    (Aᵀ *ᵥ b) F hF hd x hx
  rw [lpOpNorm_two, lpOpNorm_two] at hEn
  refine (equation_5_3_4 hA (E := E) ?_ ?_ hη hx0).1
  · rw [toEuclideanLin_toLp, toEuclideanLin_toLp, hE]
  · calc ‖E‖ ≤ n * gamma fp.u (3 * n + 3) * ‖Aᵀ * A‖ / (1 - n * gamma fp.u (n + 3)) := hEn
      _ = n * gamma fp.u (3 * n + 3) / (1 - n * gamma fp.u (n + 3)) * ‖Aᵀ * A‖ := by ring
      _ ≤ η * ‖Aᵀ * A‖ := mul_le_mul_of_nonneg_right hηc (norm_nonneg _)

end NormalEquations

/-! ### The SVD expansion (5.3.2)–(5.3.3) -/

section SVD

variable {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) ℝ}

/-- Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$ have an SVD $U^TAV = \Sigma$ with singular
values $\sigma_1 \ge \dots \ge \sigma_n$, and let $u_i$ and $v_i$ be the columns of $U$ and $V$.
Then for every $b \in \mathbb{R}^m$ the pseudoinverse satisfies
$$A^+b = \sum_{i=1}^n \frac{u_i^Tb}{\sigma_i}v_i,$$
where a term with $\sigma_i = 0$ is $0$. -/
theorem pinv_mulVec_eq_sum_of_isSVD (h : IsSVD A U σ V) (hnm : n ≤ m) (b : Fin m → ℝ) :
    A.pinv *ᵥ b = ∑ i : Fin n, ((U.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) • V.col i := by
  rw [h.pinv_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [RCLike.ofReal_real_eq_id, id]
  have hD : ∀ i : Fin n, ((rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) *ᵥ
      (star U *ᵥ b)) i = (U.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i := by
    intro i
    simp only [mulVec, dotProduct, rectDiagonal, of_apply, ite_mul, zero_mul]
    rw [Finset.sum_eq_single (Fin.castLE hnm i) (fun j _ hj => by
      rw [ite_eq_right (fun e => hj (Fin.ext (by simp [e])))]) (by simp)]
    simp only [Fin.val_castLE, ↓reduceIte, star_apply, star_trivial, col_apply]
    rw [div_eq_inv_mul]
  ext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply]
  change ∑ i, V p i * _ = _
  simp only [hD, mul_comm]

/-- **Equation (5.3.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, with $m \ge n$, and let $U^TAV = \Sigma$ be an SVD of $A$ with singular values
$\sigma_1 \ge \dots \ge \sigma_n$, where $u_i$ and $v_i$ are the columns of $U$ and $V$. Then
for every $b \in \mathbb{R}^m$ the vector
$$x_{LS} = \sum_{i=1}^n \frac{u_i^Tb}{\sigma_i}v_i$$
minimizes $\|Ax - b\|_2$.

The SVD is `Matrix.IsSVD A U σ V`, and $u_i^Tb$ is `U.col i ⬝ᵥ b` with 0-based $i$. -/
theorem equation_5_3_2 (h : IsSVD A U σ V) (hA : LinearIndependent ℝ Aᵀ) (hnm : n ≤ m)
    (b : Fin m → ℝ) :
    IsLeastSquaresSolution A (toLp 2 b)
      (toLp 2 (∑ i : Fin n, ((U.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) • V.col i)) := by
  rw [isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent hA, toEuclideanLin_toLp,
    pinv_mulVec_eq_sum_of_isSVD h hnm]

/-- **Equation (5.3.3)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, with $m \ge n$, let $U^TAV = \Sigma$ be an SVD of $A$, and let $x_{LS}$ be the vector
(5.3.2) for $b \in \mathbb{R}^m$. Then the minimum residual $\rho_{LS} = \|Ax_{LS} - b\|_2$
satisfies
$$\rho_{LS}^2 = \sum_{i=n+1}^m (u_i^Tb)^2.$$

**Typo.** The source prints the upper summation limit as $2$. The sum runs over the last $m - n$
columns of $U$, up to $m$.

In 0-based indices, the sum is over the columns $i$ with $n \le i < m$. -/
theorem equation_5_3_3 (h : IsSVD A U σ V) (hA : LinearIndependent ℝ Aᵀ) (hnm : n ≤ m)
    (b : Fin m → ℝ) :
    ‖toEuclideanLin A (toLp 2 (∑ i : Fin n, ((U.col (Fin.castLE hnm i) ⬝ᵥ b) / σ i) • V.col i)) -
        toLp 2 b‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), (U.col i ⬝ᵥ b) ^ 2 := by
  have hr : A.rank = n := by
    rw [← rank_transpose]
    simpa using LinearIndependent.rank_matrix (M := Aᵀ) hA
  rw [← pinv_mulVec_eq_sum_of_isSVD h hnm, ← toEuclideanLin_toLp,
    norm_sub_sq_pinv_eq_sum_of_isSVD h, hr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_toLp_toLp, Real.norm_eq_abs, sq_abs]
  simp only [star_trivial, dotProduct_comm]
  rfl

end SVD

/-! ### §5.3.3 LS solution via QR factorization -/

section QR

/-- **Equation (5.3.5)** of [golub2013matrix], with §5.3.3. Let $A \in \mathbb{R}^{m \times n}$ with
$n \le m$ have a QR factorization $A = QR$, with $Q \in \mathbb{R}^{m \times m}$ orthogonal and
$R \in \mathbb{R}^{m \times n}$ upper triangular. For $b \in \mathbb{R}^m$ write
$$R = \begin{bmatrix} R_1 \\ 0 \end{bmatrix}, \qquad Q^Tb = \begin{bmatrix} c \\ d
  \end{bmatrix}$$
with $R_1 \in \mathbb{R}^{n \times n}$ and $c \in \mathbb{R}^n$. Then
$\|Ax - b\|_2^2 = \|R_1x - c\|_2^2 + \|d\|_2^2$ for every $x \in \mathbb{R}^n$. If moreover $A$
has full column rank, then $x_{LS} = R_1^{-1}c$ minimizes $\|Ax - b\|_2$, and every minimizer
has the residual $\rho_{LS}^2 = \|d\|_2^2$.

The QR factorization is `Matrix.IsQR A Q R`. The block $R_1$ is `R.firstRows hnm`, and
$c = Q_1^Tb$ for the first $n$ columns $Q_1$ of $Q$, `Q.firstColumns hnm`. The number
$\|d\|_2^2$ is the sum of the squares of the entries $(Q^Tb)_i$ with $n \le i$, in 0-based
indices.

**Generalization.** The residual split uses the QR factorization alone. Full column rank is
needed for the inverse-based solution formula. -/
theorem equation_5_3_5 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (hnm : n ≤ m) (b : EuclideanSpace ℝ (Fin m)) :
    (∀ x, ‖toEuclideanLin A x - b‖ ^ 2 =
      ‖toEuclideanLin (R.firstRows hnm) x - toEuclideanLin (Q.firstColumns hnm)ᵀ b‖ ^ 2 +
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)),
          ‖(toEuclideanLin Qᵀ b) i‖ ^ 2) ∧
      (LinearIndependent ℝ Aᵀ →
        IsLeastSquaresSolution A b
          (toEuclideanLin ((R.firstRows hnm)⁻¹ * (Q.firstColumns hnm)ᵀ) b) ∧
        ∀ x, IsLeastSquaresSolution A b x → ‖toEuclideanLin A x - b‖ ^ 2 =
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)),
            ‖(toEuclideanLin Qᵀ b) i‖ ^ 2) := by
  refine ⟨fun x => ?_, fun hA => ⟨?_, fun x hx => ?_⟩⟩
  · have := norm_sub_sq_eq_of_isQR h hnm b x
    simpa only [conjTranspose_eq_transpose_of_trivial] using this
  · have := h.isLeastSquaresSolution hnm hA b
    simpa only [conjTranspose_eq_transpose_of_trivial] using this
  · have := norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution h hnm hA hx
    simpa only [conjTranspose_eq_transpose_of_trivial] using this

/-! ### §5.3.5 LS solution via MGS -/

/-- The augmented matrix $A_+ = [A \mid b] \in \mathbb{R}^{m \times (n+1)}$ of §5.3.5 of
[golub2013matrix]: the columns of $A$ followed by the column $b$. -/
def augmentCol (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Matrix (Fin m) (Fin (n + 1)) ℝ :=
  of fun i => Fin.snoc (α := fun _ => ℝ) (A i) (b i)

/-- **Section 5.3.5** of [golub2013matrix], least squares by modified Gram–Schmidt. Let
$A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$ be such that $A_+ = [A \mid b]$ has
full column rank $n + 1$. Let modified Gram–Schmidt (Algorithm 5.2.6) in exact arithmetic give
$$A_+ = [Q_1 \mid q_{n+1}]\begin{bmatrix} R_1 & z \\ 0 & \rho \end{bmatrix}$$
with $Q_1 \in \mathbb{R}^{m \times n}$, $R_1 \in \mathbb{R}^{n \times n}$, $z \in \mathbb{R}^n$
and $\rho \in \mathbb{R}$. Then $z = Q_1^Tb$; a vector $x \in \mathbb{R}^n$ minimizes
$\|Ax - b\|_2$ if and only if $R_1x = z$; and every such minimizer satisfies
$|\rho| = \|Ax - b\|_2 = \rho_{LS}$.

The factors are the output of `GolubVanLoan.Chapter05.algorithm_5_2_6` at `Id` on
`GolubVanLoan.Chapter05.augmentCol A b`. The blocks $R_1$, $z$ and $\rho$ of its triangular
factor are indexed through `Fin.castSucc` and `Fin.last n`.

**Reading.** The exact modified Gram–Schmidt theorem assumes full column rank of $[A\mid b]$.
When $b$ is already in the range of $A$, the final normalization of the augmented factorization
would divide by zero. -/
theorem mgs_augmented {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hA : LinearIndependent ℝ (augmentCol A b)ᵀ) :
    (fun j => (Id.run (algorithm_5_2_6 pure (augmentCol A b))).2 j.castSucc (Fin.last n)) =
        ((Id.run (algorithm_5_2_6 pure (augmentCol A b))).1.submatrix id Fin.castSucc)ᵀ *ᵥ b ∧
      (∀ x : Fin n → ℝ,
        IsLeastSquaresSolution A (toLp 2 b) (toLp 2 x) ↔
          (Id.run (algorithm_5_2_6 pure (augmentCol A b))).2.submatrix Fin.castSucc Fin.castSucc
            *ᵥ x = fun j => (Id.run (algorithm_5_2_6 pure (augmentCol A b))).2 j.castSucc
              (Fin.last n)) ∧
      ∀ x : Fin n → ℝ, IsLeastSquaresSolution A (toLp 2 b) (toLp 2 x) →
        |(Id.run (algorithm_5_2_6 pure (augmentCol A b))).2 (Fin.last n) (Fin.last n)| =
          ‖toEuclideanLin A (toLp 2 x) - toLp 2 b‖ := by
  obtain ⟨hQR, hpos⟩ := algorithm_5_2_6_spec _ hA
  set Q := (Id.run (algorithm_5_2_6 pure (augmentCol A b))).1 with hQdef
  set R := (Id.run (algorithm_5_2_6 pure (augmentCol A b))).2 with hRdef
  set Q₁ : Matrix (Fin m) (Fin n) ℝ := Q.submatrix id Fin.castSucc with hQ₁
  set R₁ : Matrix (Fin n) (Fin n) ℝ := R.submatrix Fin.castSucc Fin.castSucc with hR₁
  set z : Fin n → ℝ := fun j => R j.castSucc (Fin.last n) with hz
  set ρ := R (Fin.last n) (Fin.last n) with hρ
  set q := Q.col (Fin.last n) with hq
  have hon := isThinQR_col_dotProduct_col hQR
  have hup : ∀ j : Fin n, R (Fin.last n) j.castSucc = 0 := fun j =>
    hQR.isUpperTriangular (Fin.castSucc_lt_last j)
  -- the column split `A = Q₁ R₁`, `b = Q₁ z + ρ q`
  have hAe : A = Q₁ * R₁ := by
    ext p j
    have := congrFun (congrFun hQR.mul_eq p) j.castSucc
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, hup, mul_zero, add_zero] at this
    have h2 : augmentCol A b p j.castSucc = A p j := by simp [augmentCol]
    exact (this.trans h2).symm
  have hbe : b = Q₁ *ᵥ z + ρ • q := by
    ext p
    have := congrFun (congrFun hQR.mul_eq p) (Fin.last n)
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at this
    simp only [augmentCol, of_apply, Fin.snoc_last] at this
    rw [← this]
    simp [mulVec, dotProduct, hQ₁, hz, hq, hρ, mul_comm]
  have hQ₁Q₁ : Q₁ᵀ * Q₁ = 1 := by
    ext i j
    have := hon i.castSucc j.castSucc
    simp only [Fin.castSucc_inj] at this
    simpa [Matrix.mul_apply, Matrix.one_apply, hQ₁, dotProduct] using this
  have hQ₁q : Q₁ᵀ *ᵥ q = 0 := by
    ext i
    have := hon i.castSucc (Fin.last n)
    rw [ite_eq_right (fun e => absurd e (Fin.castSucc_lt_last i).ne)] at this
    simpa [mulVec, hQ₁, hq, dotProduct] using this
  have hqq : q ⬝ᵥ q = 1 := by simpa using hon (Fin.last n) (Fin.last n)
  -- `R₁` is nonsingular
  have hR₁up : R₁.IsUpperTriangular := fun i j hij =>
    hQR.isUpperTriangular (Fin.castSucc_lt_castSucc_iff.2 hij)
  have hdet : R₁ᵀ.det ≠ 0 := by
    rw [det_transpose, det_of_isUpperTriangular hR₁up]
    exact (Finset.prod_pos fun i _ => hpos i.castSucc).ne'
  have hz' : z = Q₁ᵀ *ᵥ b := by
    rw [hbe, mulVec_add, mulVec_mulVec, hQ₁Q₁, one_mulVec, mulVec_smul, hQ₁q, smul_zero,
      add_zero]
  have hres : ∀ x, A *ᵥ x - b = Q₁ *ᵥ (R₁ *ᵥ x - z) - ρ • q := by
    intro x
    rw [hbe, hAe, ← mulVec_mulVec, mulVec_sub]
    abel
  have hnormal : ∀ x, Aᵀ *ᵥ (A *ᵥ x - b) = R₁ᵀ *ᵥ (R₁ *ᵥ x - z) := by
    intro x
    rw [hres, hAe, transpose_mul, ← mulVec_mulVec, mulVec_sub, mulVec_smul,
      mulVec_mulVec, hQ₁Q₁, one_mulVec, hQ₁q, smul_zero, sub_zero]
  have hLS : ∀ x : Fin n → ℝ,
      IsLeastSquaresSolution A (toLp 2 b) (toLp 2 x) ↔ R₁ *ᵥ x = z := by
    intro x
    rw [(isLeastSquaresSolution_iff_normalEquations (toLp 2 b)).1, toEuclideanLin_toLp,
      toEuclideanLin_toLp, (toLp_injective 2).eq_iff, ← mulVec_mulVec, ← sub_eq_zero,
      ← mulVec_sub, hnormal]
    constructor
    · intro h
      exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero hdet h)
    · intro h
      rw [h, sub_self, mulVec_zero]
  refine ⟨hz', hLS, fun x hx => ?_⟩
  rw [toEuclideanLin_toLp, ← toLp_sub, hres, (hLS x).1 hx, sub_self, mulVec_zero, zero_sub]
  have h1 := dotProduct_self_eq_norm_sq (-(ρ • q))
  rw [neg_dotProduct, dotProduct_neg, neg_neg, smul_dotProduct, dotProduct_smul, hqq,
    smul_eq_mul, smul_eq_mul, mul_one] at h1
  have h2 : ‖(toLp 2 (-(ρ • q)) : EuclideanSpace ℝ (Fin m))‖ = |ρ| := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← h1, ← sq, Real.sqrt_sq_eq_abs]
  exact h2.symm

end QR

/-! ### §5.3.3 Algorithm 5.3.2: the Householder LS solution -/

section HouseholderLS

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass $j$ of the $b$-loop of Algorithm 5.3.2 of [golub2013matrix], as printed:
```
v = [1; A(j+1:m, j)]
β = 2/vᵀv
b(j:m) = b(j:m) - β(vᵀb(j:m))v
```
The inner products $v^Tv$ and $v^Tb(j{:}m)$ are Algorithm 1.1.1 over the rows $j{:}m$. The
quotient $\beta$, the product $\beta(v^Tb)$, the products with $v$ and the differences are
rounded, in the printed order. -/
noncomputable def householderLSStep (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) :
    M (Fin m → ℝ) := do
  let v := storedHouseholderVec A j
  let vv ← dotAccum rnd (indexFrom m j) v v 0
  let β ← rnd (2 / vv)
  let s ← dotAccum rnd (indexFrom m j) v b 0
  let t ← rnd (β * s)
  (indexFrom m j).foldlM (fun (b : Fin m → ℝ) i => do
    let p ← rnd (t * v i)
    let c ← rnd (b i - p)
    pure (Function.update b i c)) b

/-- **Algorithm 5.3.2** of [golub2013matrix], the stages after the QR factorization. Let $n \le m$.
Given the output $(A', \beta)$ of Algorithm 5.2.1 and $b \in \mathbb{R}^m$, the program runs the
$b$-loop with recomputed $\beta_j$ (`GolubVanLoan.Chapter05.householderLSStep` for
$j = 1, \dots, n$), and then it solves $R(1{:}n, 1{:}n)x_{LS} = b(1{:}n)$ by back substitution
(Algorithm 3.1.2).

The returned $\beta$ of the factorization is not used. The factor $R$ is the upper triangle
`GolubVanLoan.Chapter05.upperPart` of $A'$. The rounding results (5.3.6)–(5.3.8) are stated for
the runs of this program. -/
noncomputable def householderLSSolve (hnm : n ≤ m) (QR : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ))
    (b : Fin m → ℝ) : M (Fin n → ℝ) := do
  let b ← (List.finRange n).foldlM (householderLSStep rnd QR.1) b
  Chapter03.algorithm_3_1_2 rnd ((upperPart QR.1).firstRows hnm) fun i => b (Fin.castLE hnm i)

/-- **Algorithm 5.3.2** of [golub2013matrix] (Householder LS Solution). If
$A \in \mathbb{R}^{m \times n}$ has full column rank and $b \in \mathbb{R}^m$, then the
algorithm computes a vector $x_{LS} \in \mathbb{R}^n$ such that $\|Ax_{LS} - b\|_2$ is minimum:
```
Use Algorithm 5.2.1 to overwrite A with its QR factorization.
for j = 1:n
    v = [1; A(j+1:m, j)];  β = 2/vᵀv;  b(j:m) = b(j:m) - β(vᵀb(j:m))v
end
Solve R(1:n, 1:n) · x_LS = b(1:n).
```
The program is Algorithm 5.2.1 followed by `GolubVanLoan.Chapter05.householderLSSolve`. As
printed, it discards the $\beta_j$ that Algorithm 5.2.1 returns and recomputes each $\beta_j$
from the stored vector. This is wrong when `house` returned $\beta_j = 0$ (see
`GolubVanLoan.Chapter05.algorithm_5_3_2_spec`); `GolubVanLoan.Chapter05.householderLS` uses the
returned $\beta_j$. The program takes $n \le m$ as an argument. -/
noncomputable def algorithm_5_3_2 (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : M (Fin n → ℝ) := do
  let QR ← algorithm_5_2_1 rnd A
  householderLSSolve rnd hnm QR b

end Programs

/-- A sum over the rows $j{:}m$ of the products of the stored Householder vector $v^{(j)}$ with $w$
is the full inner product $v^{(j)T}w$, because $v^{(j)}$ vanishes above row $j$. -/
private theorem sum_indexFrom_eq_dotProduct (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n)
    (w : Fin m → ℝ) :
    ((indexFrom m j).map fun i => storedHouseholderVec A j i * w i).sum =
      storedHouseholderVec A j ⬝ᵥ w :=
  (sum_eq_sum_map_of_nodup (nodup_indexFrom m j) fun i hi => by
    rw [storedHouseholderVec_eq_zero A j hi, zero_mul]).symm

/-- In exact arithmetic, one pass $j$ of the $b$-loop of Algorithm 5.3.2 of [golub2013matrix] maps
$b$ to $(I - \beta vv^T)b$, where $v$ is the stored Householder vector of column $j$ and
$\beta = 2/v^Tv$ is the recomputed scalar `GolubVanLoan.Chapter05.recomputedBeta`. -/
theorem householderLSStep_pure (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) :
    Id.run (householderLSStep pure A b j) =
      (1 - recomputedBeta A j • vecMulVec (storedHouseholderVec A j)
        (storedHouseholderVec A j)) *ᵥ b := by
  simp only [householderLSStep, dotAccum_pure, Id.run_pure, List.idRun_foldlM,
    pure_bind, zero_add, sum_indexFrom_eq_dotProduct]
  rw [List.foldl_update_of_nodup (nodup_indexFrom m j) (fun i y => y i - 2 /
    (storedHouseholderVec A j ⬝ᵥ storedHouseholderVec A j) * (storedHouseholderVec A j ⬝ᵥ b) *
    storedHouseholderVec A j i) fun _ _ _ _ _ e => by rw [e]]
  funext i
  rw [one_sub_smul_vecMulVec_mulVec_apply, recomputedBeta]
  split_ifs with hi
  · ring
  · rw [storedHouseholderVec_eq_zero A j hi]
    ring

/-- A loop that premultiplies a vector $b$ by symmetric matrices $P_1, \dots, P_k$ in turn gives
$(P_1 \cdots P_k)^Tb$. -/
private theorem foldl_mulVec_eq_transpose_prod_mulVec {α : Type} (P : α → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ a, (P a)ᵀ = P a) (l : List α) (b : Fin m → ℝ) :
    l.foldl (fun b a => P a *ᵥ b) b = ((l.map P).prod)ᵀ *ᵥ b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, transpose_mul, hP, mulVec_mulVec]

/-- The back-substitution stage of Algorithm 5.3.2 of [golub2013matrix], in exact arithmetic. Let
$A \in \mathbb{R}^{m \times n}$ have full column rank, with $n \le m$, and let $A = QR$ be a QR
factorization. Then for every $b \in \mathbb{R}^m$, Algorithm 3.1.2 applied to
$R_1x = (Q^Tb)(1{:}n)$, with $R_1 = R(1{:}n, 1{:}n)$, returns a minimizer of $\|Ax - b\|_2$. -/
theorem isLeastSquaresSolution_solve_firstRows (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {R : Matrix (Fin m) (Fin n) ℝ} (hQR : IsQR A Q R)
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) :
    IsLeastSquaresSolution A (toLp 2 b) (toLp 2 (Id.run (Chapter03.algorithm_3_1_2 pure
      (R.firstRows hnm) fun i => (Qᵀ *ᵥ b) (Fin.castLE hnm i)))) := by
  set x := Id.run (Chapter03.algorithm_3_1_2 pure (R.firstRows hnm)
    fun i => (Qᵀ *ᵥ b) (Fin.castLE hnm i)) with hx
  have hsol : R.firstRows hnm *ᵥ x = fun i => (Qᵀ *ᵥ b) (Fin.castLE hnm i) :=
    Chapter03.algorithm_3_1_2_spec (hQR.isUpperTriangular_firstRows hnm)
      (hQR.firstRows_diag_ne_zero_of_linearIndependent hnm hA) _
  intro y
  have e1 := (equation_5_3_5 hQR hnm (toLp 2 b)).1 (toLp 2 x)
  have e2 := (equation_5_3_5 hQR hnm (toLp 2 b)).1 y
  have h0 : toEuclideanLin (R.firstRows hnm) (toLp 2 x) -
      toEuclideanLin (Q.firstColumns hnm)ᵀ (toLp 2 b) = 0 := by
    rw [toEuclideanLin_toLp, toEuclideanLin_toLp, hsol, sub_eq_zero]
    rfl
  rw [h0, norm_zero] at e1
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [e1, e2]
  nlinarith [sq_nonneg ‖toEuclideanLin (R.firstRows hnm) y -
    toEuclideanLin (Q.firstColumns hnm)ᵀ (toLp 2 b)‖]

/-- **Algorithm 5.3.2** of [golub2013matrix], correctness in exact arithmetic. Let
$A \in \mathbb{R}^{m \times n}$ have full column rank, with $n \le m$, and let
$b \in \mathbb{R}^m$. Assume that every $\beta_j$ that Algorithm 5.2.1 returns for $A$ in exact
arithmetic is nonzero. Then the output of Algorithm 5.3.2 in exact arithmetic minimizes
$\|Ax - b\|_2$.

**Correction.** The source claims the result for every $A$ of full column rank. When `house`
returns $\beta_j = 0$, the recomputed $\beta_j = 2/v^Tv$ differs from it, and the claim fails:
see `GolubVanLoan.Chapter05.algorithm_5_3_2_counterexample`. The hypothesis excludes this case.
For the program that uses the returned $\beta_j$, `GolubVanLoan.Chapter05.householderLS_spec`
proves the claim without the hypothesis.

Under the hypothesis, the recomputed $\beta_j$ are the returned ones
(`GolubVanLoan.Chapter05.equation_5_1_4_beta`), the $b$-loop computes $Q^Tb$ as in (5.1.4), and
the back substitution solves $R_1x = c$ for $Q^Tb = [c; d]$ as in (5.3.5). -/
theorem algorithm_5_3_2_spec (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (hβ : ∀ j, (Id.run (algorithm_5_2_1 pure A)).2 j ≠ 0)
    (b : Fin m → ℝ) :
    IsLeastSquaresSolution A (toLp 2 b) (toLp 2 (Id.run (algorithm_5_3_2 pure hnm A b))) := by
  obtain ⟨hQR, -⟩ := algorithm_5_2_1_spec hnm A
  have hQeq := (equation_5_1_4_beta hnm A).2 hβ
  set st := Id.run (algorithm_5_2_1 pure A) with hst
  set Q := factoredQ st.2 st.1 with hQ
  set R := upperPart st.1 with hR
  have hloop : (List.finRange n).foldl (fun b j => Id.run (householderLSStep pure st.1 b j)) b =
      Qᵀ *ᵥ b := by
    simp only [householderLSStep_pure]
    rw [foldl_mulVec_eq_transpose_prod_mulVec _ (fun j => transpose_one_sub_smul_vecMulVec _ _),
      ← factoredQ_eq_prod, ← hQeq]
  have hrun : Id.run (algorithm_5_3_2 pure hnm A b) =
      Id.run (Chapter03.algorithm_3_1_2 pure (R.firstRows hnm)
        fun i => (Qᵀ *ᵥ b) (Fin.castLE hnm i)) := by
    simp only [algorithm_5_3_2, householderLSSolve, Id.run_bind, List.idRun_foldlM]
    rw [← hst, hloop]
  rw [hrun]
  exact isLeastSquaresSolution_solve_firstRows hnm hQR hA b

/-- A step $j$ of Algorithm 5.2.1 on a column whose entries below row $j$ vanish and whose entry in
row $j$ is nonnegative changes nothing except that it records $\beta_j = 0$. -/
private theorem householderQRStep_of_col_zero (B : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ)
    (j : Fin n) (hjm : (j : ℕ) < m) (hzero : ∀ i : Fin m, (j : ℕ) < i → B i j = 0)
    (hpos : 0 ≤ B ⟨j, hjm⟩ j) :
    Id.run (householderQRStep pure (B, β) j) = (B, Function.update β j 0) := by
  obtain ⟨p, t, hpt⟩ := List.exists_cons_of_ne_nil (indexFrom_ne_nil (m := m) hjm)
  have hp : p = ⟨j, hjm⟩ := by
    have := congrArg List.head? hpt
    rw [List.head?_eq_some_head (indexFrom_ne_nil hjm), head_indexFrom hjm, List.head?_cons]
      at this
    exact (Option.some.inj this).symm
  have hnd := nodup_indexFrom m j
  rw [hpt] at hnd
  have hmem : ∀ i, i ∈ indexFrom m j ↔ i = p ∨ i ∈ t := fun i => by
    rw [hpt, List.mem_cons]
  have htail : ∀ i ∈ t, (j : ℕ) < i := by
    intro i hi
    have h1 : j ≤ (i : ℕ) := mem_indexFrom.1 ((hmem i).2 (Or.inr hi))
    have h2 : i ≠ p := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hi)
    rw [hp] at h2
    exact lt_of_le_of_ne h1 (fun e => h2 (Fin.ext e.symm))
  have hσ : (t.map fun i => B i j * B i j).sum = 0 :=
    List.sum_eq_zero fun y hy => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
      rw [hzero i (htail i hi), mul_zero]
  set v : Fin m → ℝ := fun i => if i = p then 1 else if i ∈ t then B i j else 0 with hv
  have hhouse : Id.run (houseOn pure (indexFrom m j) fun i => B i j) = (v, 0) := by
    rw [hpt]
    subst hp
    simp only [houseOn, dotAccum_pure, pure_bind, hσ, add_zero, hpos, and_true, ↓reduceIte]
    rfl
  have hvout : ∀ i, i ∉ indexFrom m j → v i = 0 := fun i hi => by
    rw [hmem, not_or] at hi
    simp [hv, hi.1, hi.2]
  simp only [householderQRStep, Id.run_bind, Id.run_pure, hhouse]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom n j) hvout 0 B]
  simp only [zero_smul, sub_zero, Matrix.one_mul, ite_self]
  congr 1
  ext i q
  by_cases hq : q = j
  · subst hq
    rw [updateCol_self]
    split_ifs with hi
    · have hne : i ≠ p := by
        rw [hp]
        exact fun e => by rw [e] at hi; exact lt_irrefl _ hi
      have hit : i ∈ t := ((hmem i).1 (mem_indexFrom.2 hi.le)).resolve_left hne
      simp [hv, hne, hit]
    · rfl
  · rw [updateCol_ne hq]
    rfl

/-- Algorithm 5.2.1 in exact arithmetic leaves the identity matrix unchanged and returns
$\beta = 0$. -/
private theorem algorithm_5_2_1_one {k : ℕ} :
    Id.run (algorithm_5_2_1 pure (1 : Matrix (Fin k) (Fin k) ℝ)) = (1, 0) := by
  rw [algorithm_5_2_1, List.idRun_foldlM]
  refine List.foldl_fixed' (fun j => ?_) _
  rw [householderQRStep_of_col_zero _ _ j j.isLt (fun i hi => ?_) (by simp)]
  · simp
  · exact one_apply_ne fun e => by rw [e] at hi; exact lt_irrefl _ hi

/-- **Algorithm 5.3.2** of [golub2013matrix], a counterexample to the printed algorithm. For
$A = I_2$, Algorithm 5.2.1 in exact arithmetic returns $\beta_1 = \beta_2 = 0$. For
$b = (1, 0)^T$, Algorithm 5.3.2 in exact arithmetic returns $(-1, 0)^T$, and $(-1, 0)^T$ does
not minimize $\|I_2x - b\|_2$.

Every Householder step of Algorithm 5.2.1 meets $\sigma = 0$ and $x_1 \ge 0$, so `house` returns
$\beta = 0$ and leaves $A$ unchanged. The printed recomputation $\beta = 2/v^Tv = 2$ then flips
the sign of $b_1$. The exact solution is $(1, 0)^T$.

**Reading.** Identity example proves recomputed coefficient can give wrong result.
-/
theorem algorithm_5_3_2_counterexample :
    (Id.run (algorithm_5_2_1 pure (1 : Matrix (Fin 2) (Fin 2) ℝ))).2 = 0 ∧
      Id.run (algorithm_5_3_2 pure le_rfl (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0]) = ![-1, 0] ∧
      ¬ IsLeastSquaresSolution (1 : Matrix (Fin 2) (Fin 2) ℝ) (toLp 2 ![1, 0])
        (toLp 2 ![-1, 0]) := by
  refine ⟨by rw [algorithm_5_2_1_one], ?_, fun h => ?_⟩
  · have hloop : (List.finRange 2).foldl (fun b j => Id.run (householderLSStep pure
        (1 : Matrix (Fin 2) (Fin 2) ℝ) b j)) ![1, 0] = ![-1, 0] := by
      simp only [householderLSStep_pure]
      rw [show List.finRange 2 = [0, 1] by decide]
      simp only [List.foldl_cons, List.foldl_nil]
      ext i
      fin_cases i <;>
        norm_num [mulVec, dotProduct, Fin.sum_univ_two, vecMulVec_apply, storedHouseholderVec,
          recomputedBeta, Matrix.one_apply]
    have hR : (upperPart (1 : Matrix (Fin 2) (Fin 2) ℝ)).firstRows le_rfl = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperPart, firstRows, Matrix.one_apply]
    simp only [algorithm_5_3_2, householderLSSolve, Id.run_bind, List.idRun_foldlM,
      algorithm_5_2_1_one]
    rw [hloop, hR]
    have hs := Chapter03.algorithm_3_1_2_spec (U := (1 : Matrix (Fin 2) (Fin 2) ℝ))
      blockTriangular_one (by simp) (fun i => (![-1, 0] : Fin 2 → ℝ) (Fin.castLE le_rfl i))
    rw [one_mulVec] at hs
    rw [hs]
    ext i
    fin_cases i <;> rfl
  · have h1 := h (toLp 2 ![1, 0])
    rw [toEuclideanLin_toLp, toEuclideanLin_toLp, one_mulVec, one_mulVec, sub_self,
      norm_zero] at h1
    have h2 : (toLp 2 ![-1, 0] : EuclideanSpace ℝ (Fin 2)) - toLp 2 ![1, 0] ≠ 0 := by
      intro e
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) e
      norm_num at this
    exact h2 (norm_le_zero_iff.1 h1)

end HouseholderLS

/-! ### §5.3.3 The rounding errors of Algorithm 5.3.2 -/

section HouseholderLSRounding

/-- Every run of one pass $j$ of the $b$-loop of Algorithm 5.3.2 leaves $b$ unchanged outside the
rows $j{:}m$, and on these rows it is a computed Householder application
(`FloatingPoint.RoundsHouseholderApply`) with the stored vector $v$ and a computed
$\hat\beta = \mathrm{fl}(2/\mathrm{fl}(v^Tv))$, where the rounded product $\mathrm{fl}(tv_i)$ of
the program is the product $\mathrm{fl}(v_it)$ of that predicate. -/
private theorem householderLSStep_rounds {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) {y : Fin m → ℝ}
    (h : y ∈ (householderLSStep fp.round A b j).run) :
    (∀ i, i ∉ indexFrom m j → y i = b i) ∧ ∃ vv βhat,
      RoundsDot fp (fun i : {i // i ∈ indexFrom m j} => storedHouseholderVec A j i)
        (fun i => storedHouseholderVec A j i) vv ∧ fp.Rounds (2 / vv) βhat ∧
      RoundsHouseholderApply fp βhat
        (fun i : {i // i ∈ indexFrom m j} => storedHouseholderVec A j i) (fun i => b i)
        (fun i => y i) := by
  have hnd := nodup_indexFrom m j
  simp only [householderLSStep, SetM.mem_run_bind, RoundingModel.mem_run_round] at h
  obtain ⟨vv, hvv, βhat, hβ, s, hs, t, ht, hy⟩ := h
  have hloop := SetM.mem_run_foldlM_update_of_nodup
    (fun i c (_ : Fin m → ℝ) => do
      let p ← fp.round (t * storedHouseholderVec A j i); fp.round (c - p))
    (indexFrom m j) hnd (fun _ _ _ _ _ _ => rfl) b y
  simp only [bind_assoc] at hloop
  obtain ⟨hout, hin⟩ := hloop.1 hy
  have hstep : ∀ i : {i // i ∈ indexFrom m j}, ∃ p,
      fp.Rounds (storedHouseholderVec A j i * t) p ∧ fp.Rounds (b i - p) (y i) := fun i => by
    have := hin i i.2
    simp only [SetM.mem_run_bind, RoundingModel.mem_run_round] at this
    obtain ⟨p, hp, hy⟩ := this
    exact ⟨p, by rwa [mul_comm], hy⟩
  choose p hp hyp using hstep
  exact ⟨hout, vv, βhat, roundsDot_subtype_of_mem_run_dotAccum hfp hnd hvv, hβ, s, t, p,
    roundsDot_subtype_of_mem_run_dotAccum hfp hnd hs, ht, hp, hyp⟩

/-- If the stored vector of column $j$ is entrywise a relative perturbation of order $K$ of a vector
$v$ that vanishes outside the rows $j{:}m$, and $I - \beta vv^T$ is orthogonal with
$\beta \neq 0$ (so that $\beta = 2/v^Tv$), then every run $y$ of one pass of the $b$-loop of
Algorithm 5.3.2 on $b$ satisfies $\|y - (I - \beta vv^T)b\|_2 \le 3\gamma_{3(4K + 2m + 1) + m +
3}\|b\|_2$, as in [higham2002accuracy] Lemma 19.2 with the recomputed $\beta$. -/
private theorem householderLSStep_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    {K : ℕ} (hu : ((3 * (4 * K + 2 * m + 1) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) (hjm : (j : ℕ) < m) {v : Fin m → ℝ} {β : ℝ}
    (hvout : ∀ i, i ∉ indexFrom m j → v i = 0)
    (hv : ∀ i, IsRelPert fp.u K (v i) (storedHouseholderVec A j i))
    (hO : 1 - β • vecMulVec v v ∈ orthogonalGroup (Fin m) ℝ) (hβ0 : β ≠ 0)
    (b : Fin m → ℝ) {y : Fin m → ℝ} (h : y ∈ (householderLSStep fp.round A b j).run) :
    ‖(toLp 2 (y - (1 - β • vecMulVec v v) *ᵥ b) : EuclideanSpace ℝ (Fin m))‖ ≤
      3 * gamma fp.u (3 * (4 * K + 2 * m + 1) + m + 3) *
        ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖ := by
  set o := indexFrom m j with ho
  have hnd := nodup_indexFrom m j
  have hlen : o.length ≤ m := (List.length_filter_le _ _).trans (by simp)
  have hcard : Fintype.card {i // i ∈ o} = o.length := card_subtype_mem_of_nodup hnd
  have hu0 := fp.u_nonneg
  have hlt : ∀ a : ℕ, a ≤ 3 * (4 * K + 2 * m + 1) + m + 3 → ((a : ℕ) : ℝ) * fp.u < 1 :=
    fun a ha => (mul_le_mul_of_nonneg_right (Nat.cast_le.2 ha) hu0).trans_lt hu
  have hu1 : fp.u < 1 := by simpa using hlt 1 (by omega)
  obtain ⟨hyout, vv, βhat, hvv, hβhat, happ⟩ := householderLSStep_rounds hfp A b j h
  -- the exact `β` is `2/vᵀv`
  have hvp : v ⟨j, hjm⟩ ≠ 0 := by
    intro h0
    obtain ⟨θ, -, hθ⟩ := hv ⟨j, hjm⟩
    rw [h0, zero_mul] at hθ
    have : storedHouseholderVec A j ⟨j, hjm⟩ = 1 := by simp [storedHouseholderVec]
    rw [this] at hθ
    exact one_ne_zero hθ
  have hβv : β * (v ⬝ᵥ v) = 2 := by
    rcases mul_eq_zero.1 (mul_mul_dotProduct_sub_two_eq_zero_of_mem_orthogonalGroup hvp hO) with
      h0 | h2
    · exact absurd h0 hβ0
    · linarith
  have hvv0 : v ⬝ᵥ v ≠ 0 := fun h0 => by rw [h0, mul_zero] at hβv; norm_num at hβv
  have hβeq : β = 2 / (v ⬝ᵥ v) := eq_div_of_mul_eq hvv0 hβv
  -- restrictions to the rows `j:m`
  have hdot : v ⬝ᵥ v = (fun i : {i // i ∈ o} => v i) ⬝ᵥ (fun i => v i) :=
    dotProduct_eq_dotProduct_subtype hvout v
  -- `β̂` is a relative perturbation of `β`
  have hvvrel : IsRelPert fp.u (2 * K + Fintype.card {i // i ∈ o})
      ((fun i : {i // i ∈ o} => v i) ⬝ᵥ (fun i => v i)) vv :=
    isRelPert_of_roundsDot_self (ι := {i // i ∈ o}) (v := fun i => v i)
      (vhat := fun i => storedHouseholderVec A j i) hu1 (hlt _ (by omega)) (fun i => hv i) hvv
  have hβrel : IsRelPert fp.u (4 * K + 2 * m + 1) β βhat := by
    have h1 := (IsRelPert.refl fp.u (2 : ℝ)).div hu0 (hlt _ (by omega)) hvvrel
    have h2 := h1.rounds (hlt _ (by omega)) hβhat
    rw [hβeq, hdot]
    exact h2.mono hu0 (by omega) (hlt _ (by omega))
  have hvrel : ∀ i : {i // i ∈ o}, IsRelPert fp.u (4 * K + 2 * m + 1) (v i)
      (storedHouseholderVec A j i) := fun i =>
    (hv i).mono hu0 (by omega) (hlt _ (by omega))
  have hP : |β| * ((fun i : {i // i ∈ o} => v i) ⬝ᵥ (fun i => v i)) ≤ 2 := by
    rw [← hdot, hβeq]
    exact abs_two_div_dotProduct_self_mul_le v
  have hsub := norm_sub_le_of_roundsHouseholderApply (k := 4 * K + 2 * m + 1)
    (by rw [hcard]; exact hlt _ (by omega)) hβrel hvrel hP happ
  rw [hcard] at hsub
  -- back to the full vectors
  set D : Fin m → ℝ := y - (1 - β • vecMulVec v v) *ᵥ b with hD
  have hDout : ∀ i, i ∉ o → D i = 0 := fun i hi => by
    rw [hD, Pi.sub_apply, one_sub_smul_vecMulVec_mulVec_apply, hvout i hi, hyout i hi]
    ring
  have hDin : (fun i : {i // i ∈ o} => D i) =
      (fun i : {i // i ∈ o} => y i) -
        (1 - β • vecMulVec (fun i : {i // i ∈ o} => v i) (fun i : {i // i ∈ o} => v i) :
          Matrix {i // i ∈ o} {i // i ∈ o} ℝ) *ᵥ (fun i : {i // i ∈ o} => b i) := by
    funext i
    rw [hD, Pi.sub_apply, Pi.sub_apply, one_sub_smul_vecMulVec_mulVec_apply_subtype hvout,
      dite_eq_left i.2]
  have hγ : 3 * gamma fp.u (3 * (4 * K + 2 * m + 1) + o.length + 3) ≤
      3 * gamma fp.u (3 * (4 * K + 2 * m + 1) + m + 3) :=
    mul_le_mul_of_nonneg_left (gamma_mono hu0 (by omega) hu) (by norm_num)
  rw [norm_toLp_eq_restrict (p := (· ∈ o)) hDout, hDin]
  refine hsub.trans (mul_le_mul hγ (norm_toLp_restrict_le (p := (· ∈ o)) b) (norm_nonneg _) ?_)
  have := gamma_nonneg hu0 hu
  positivity

/-- If every step $q$ of a run of Algorithm 5.2.1 has exact reflector data $(v_q, \beta_q)$ with
orthogonal reflectors $P_q$ and every returned $\hat\beta_q$ is nonzero, then every run $c$ of
the $b$-loop of Algorithm 5.3.2 on $b$ is $c = P_{n-1} \cdots P_0(b + \Delta b)$ with $\|\Delta
b\|_2 \le ((1 + \varepsilon')^n - 1)\|b\|_2$ and $\varepsilon' = 3\gamma_{3(4(18m + 31) +
2m + 1) + m + 3}$, as in [higham2002accuracy] Lemma 19.3 with the recomputed $\beta$. -/
private theorem householderLSLoop_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hnm : n ≤ m) (hu : ((3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    {st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)} {v : ℕ → Fin m → ℝ} {β : ℕ → ℝ}
    (hO : ∀ j, dataReflector v β j ∈ orthogonalGroup (Fin m) ℝ)
    (hdata : ∀ q : Fin n, IsStepData fp.u st q (v q) (β q)) (hβ : ∀ q, st.2 q ≠ 0)
    (b : Fin m → ℝ) {c : Fin m → ℝ}
    (h : c ∈ ((List.finRange n).foldlM (householderLSStep fp.round st.1) b).run) :
    ∃ db : Fin m → ℝ, c = prodRev (dataReflector v β) n *ᵥ (b + db) ∧
      ‖(toLp 2 db : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + 3 * gamma fp.u (3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3)) ^ n - 1) *
          ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖ := by
  set ε := 3 * gamma fp.u (3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3) with hε
  have hε0 : 0 ≤ ε := by have := gamma_nonneg fp.u_nonneg hu; positivity
  refine SetM.forall_mem_run_foldlM_finRange (fun k y => ∃ db : Fin m → ℝ,
      y = prodRev (dataReflector v β) k *ᵥ (b + db) ∧
      ‖(toLp 2 db : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + ε) ^ k - 1) * ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖)
    ⟨0, by simp [prodRev_zero], by simp⟩ ?_ c h
  rintro k y ⟨db, rfl, hdb⟩ y' hy'
  obtain ⟨-, h2, h3, h4⟩ := hdata k
  have hβ0 : β k ≠ 0 := by
    rintro h0
    obtain ⟨θ, -, hθ⟩ := h4
    rw [h0, zero_mul] at hθ
    exact hβ k hθ
  set y := prodRev (dataReflector v β) k *ᵥ (b + db) with hy
  have hstep : ‖(toLp 2 (y' - dataReflector v β k *ᵥ y) : EuclideanSpace ℝ (Fin m))‖ ≤
      ε * ‖(toLp 2 y : EuclideanSpace ℝ (Fin m))‖ :=
    householderLSStep_rounding hfp (K := 18 * m + 31) hu st.1 k (lt_of_lt_of_le k.isLt hnm) h2
      h3 (hO k) hβ0 y hy'
  obtain ⟨db', hy'eq, hdb'⟩ := exists_eq_mulVec_add_of_step (hO k)
    (prodRev_mem_orthogonalGroup fun k _ => hO k) hε0 hy hdb hstep
  exact ⟨db', by rw [hy'eq, prodRev_succ], hdb'⟩

open scoped Matrix.Norms.Frobenius in
/-- **Equation (5.3.6)** of [golub2013matrix] (Lawson and Hanson). Let
$A \in \mathbb{R}^{m \times n}$ with $n \le m$ and $b \in \mathbb{R}^m$. Let the rounding model
be idempotent, with unit roundoff $u$ such that $(3(4(18m + 31) + 2m + 1) + m + 3)u < 1$, and
put
$$\varepsilon = 3\gamma_{3(18m + 31) + m + 3}, \qquad \varepsilon' = 3\gamma_{3(4(18m + 31) +
  2m + 1) + m + 3},$$
where $\gamma_k = ku/(1 - ku)$. Let $(\hat A, \hat\beta)$ be computed by Algorithm 5.2.1 from
$A$, with every $\hat\beta_j \neq 0$ and with nonzero diagonal entries of
$\hat R_1 = \hat R(1{:}n, 1{:}n)$, and let $\hat x$ be computed from $(\hat A, \hat\beta)$ and
$b$ by the remaining stages of Algorithm 5.3.2. Then $\hat x$ solves exactly a nearby
least-squares problem: there are $\delta A \in \mathbb{R}^{m \times n}$ and
$\delta b \in \mathbb{R}^m$ such that $\hat x$ minimizes
$\|(A + \delta A)x - (b + \delta b)\|_2$ and
$$\|\delta A\|_F \le ((1 + \varepsilon)^n(1 + \gamma_n) - 1)\|A\|_F, \qquad \|\delta b\|_2 \le
  ((1 + \varepsilon')^n - 1)\|b\|_2.$$

**Reading.** The source states the first-order bounds $\|\delta A\|_F \le (6m - 3n +
41)nu\|A\|_F + O(u^2)$ and $\|\delta b\|_2 \le (6m - 3n + 40)nu\|b\|_2 + O(u^2)$, with the
constants of Lawson and Hanson. The theorem states rigorous bounds of the same shape, with
explicit $\gamma$ constants in place of these constants. The hypothesis $\hat\beta_j \neq 0$ is
needed by the printed recomputation of $\beta$ (see
`GolubVanLoan.Chapter05.algorithm_5_3_2_spec`), and the hypothesis on $\hat R_1$ by the back
substitution.

The remaining stages are `GolubVanLoan.Chapter05.householderLSSolve`. The constant $\varepsilon$
bounds the error of one computed step of Algorithm 5.2.1, and $\varepsilon'$ bounds the error of
one pass of the $b$-loop with its recomputed $\beta$. With $Z$ the product of the exact
reflectors, $\delta A = E + Z[\Delta R; 0]$ collects the backward error $E$ of the QR
factorization (`GolubVanLoan.Chapter05.algorithm_5_2_1_rounding`) and the backward error
$(\hat R_1 + \Delta R)\hat x = \hat c$, $|\Delta R| \le \gamma_n|\hat R_1|$, of the back
substitution; $\delta b$ is the backward error $\hat c = Z^T(b + \delta b)$ of the $b$-loop. The
proof follows [higham2002accuracy] Theorem 20.3. -/
theorem equation_5_3_6 {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) (hnm : n ≤ m)
    (hu : ((3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ∀ st ∈ (algorithm_5_2_1 fp.round A).run, (∀ j, st.2 j ≠ 0) →
      (∀ i : Fin n, upperPart st.1 (Fin.castLE hnm i) i ≠ 0) →
    ∀ x ∈ (householderLSSolve fp.round hnm st b).run,
      ∃ (δA : Matrix (Fin m) (Fin n) ℝ) (δb : Fin m → ℝ),
      IsLeastSquaresSolution (A + δA) (toLp 2 (b + δb)) (toLp 2 x) ∧
      ‖δA‖ ≤ ((1 + 3 * gamma fp.u (3 * (18 * m + 31) + m + 3)) ^ n * (1 + gamma fp.u n) - 1) *
        ‖A‖ ∧
      ‖(toLp 2 δb : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + 3 * gamma fp.u (3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3)) ^ n - 1) *
          ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖ := by
  have hu0 := fp.u_nonneg
  have hlt : ∀ a : ℕ, a ≤ 3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3 →
      ((a : ℕ) : ℝ) * fp.u < 1 := fun a ha =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 ha) hu0).trans_lt hu
  have hu1 : fp.u < 1 := by simpa using hlt 1 (by omega)
  intro st hst hβ hR x hx
  simp only [householderLSSolve, SetM.mem_run_bind] at hx
  obtain ⟨c, hc, hx⟩ := hx
  obtain ⟨v, β, E, hO, hdata, hE, hEb⟩ :=
    algorithm_5_2_1_rounding_data hfp hnm (hlt _ (by omega)) A hst
  obtain ⟨db, hcdb, hdb⟩ := householderLSLoop_rounding hfp hnm hu hO hdata hβ b hc
  set ε := 3 * gamma fp.u (3 * (18 * m + 31) + m + 3) with hε
  have hε0 : 0 ≤ ε := by
    have := gamma_nonneg hu0 (hlt (3 * (18 * m + 31) + m + 3) (by omega))
    positivity
  set W := prodRev (dataReflector v β) n with hWdef
  have hWO : W ∈ orthogonalGroup (Fin m) ℝ := prodRev_mem_orthogonalGroup (r := n) fun k _ => hO k
  have hWtO : Wᵀ ∈ orthogonalGroup (Fin m) ℝ := transpose_mem_unitaryGroup_iff.2 hWO
  set T := (upperPart st.1).firstRows hnm with hT
  have hTu : T.IsUpperTriangular := fun i j hij => by
    have hij' : (j : ℕ) < i := hij
    change upperPart st.1 (Fin.castLE hnm i) j = 0
    simp only [upperPart, of_apply, Fin.val_castLE]
    exact ite_eq_right (by omega)
  obtain ⟨ΔU, hΔU, hsol⟩ := exists_roundsBackSubstDot_eq hu1
    (by rw [Fintype.card_fin]; exact hlt n (by omega)) hTu hR
    (Chapter03.algorithm_3_1_2_rounds (fp := fp) _ _ x hx)
  -- `ΔR` padded with zero rows
  set Δ : Matrix (Fin m) (Fin n) ℝ := of fun i j => if h : (i : ℕ) < n then ΔU ⟨i, h⟩ j else 0
    with hΔ
  set T' := upperPart st.1 + Δ with hT'
  have hWW : Wᵀ * W = 1 := (mem_orthogonalGroup_iff' _ _).1 hWO
  have hAE : A + E = Wᵀ * upperPart st.1 := by
    rw [hE, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have hA' : A + (E + Wᵀ * Δ) = Wᵀ * T' * (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [Matrix.mul_one, hT', Matrix.mul_add, ← hAE, add_assoc]
  have hz : ∀ (i : Fin m) (j : Fin n), n ≤ (i : ℕ) → T' i j = 0 := fun i j hi => by
    simp only [hT', hΔ, Matrix.add_apply, upperPart, of_apply]
    rw [ite_eq_right (by omega), dite_eq_right_iff.2 fun h => absurd h (by omega), add_zero]
  have hbc : b + db = Wᵀ *ᵥ c := by
    rw [hcdb, mulVec_mulVec, hWW, one_mulVec]
  have hhead : ∀ i : Fin n, (T' *ᵥ x) (Fin.castLE hnm i) = c (Fin.castLE hnm i) := fun i => by
    have := congrFun hsol i
    rw [← this]
    simp only [mulVec, dotProduct, hT', hΔ, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
      of_apply, Fin.val_castLE, i.isLt, dite_true]
    rfl
  refine ⟨E + Wᵀ * Δ, db, fun y => ?_, ?_, hdb⟩
  · -- the least-squares property
    have hsplit := fun z : EuclideanSpace ℝ (Fin n) =>
      norm_toEuclideanLin_sub_sq_eq_of_eq_mul (hWtO : Wᵀ ∈ unitaryGroup (Fin m) ℝ) hnm hA' hz
        (toLp 2 (b + db)) z
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [hsplit, hsplit]
    have h0 : ∑ i : Fin n, ‖(T' *ᵥ (1 *ᵥ ofLp (toLp 2 x))) (Fin.castLE hnm i) -
        ((Wᵀ)ᴴ *ᵥ ofLp (toLp 2 (b + db))) (Fin.castLE hnm i)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [one_mulVec, ofLp_toLp, ofLp_toLp, conjTranspose_eq_transpose_of_trivial,
        transpose_transpose, hbc, mulVec_mulVec, (mem_orthogonalGroup_iff _ _).1 hWO,
        one_mulVec, hhead, sub_self, norm_zero, zero_pow two_ne_zero]
    rw [h0, zero_add]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · -- the size of `δA`
    have hη : 0 ≤ (1 + ε) ^ n - 1 := by
      have : 1 ≤ (1 + ε) ^ n := one_le_pow₀ (by linarith)
      linarith
    have hEF : ‖E‖ ≤ ((1 + ε) ^ n - 1) * ‖A‖ := frobenius_norm_le_of_forall_col_le hη hEb
    have hγ0 : 0 ≤ gamma fp.u n := gamma_nonneg hu0 (hlt n (by omega))
    have hRF : ‖upperPart st.1‖ ≤ (1 + ε) ^ n * ‖A‖ := by
      rw [hE, show W * (A + E) = W * (A + E) * (1 : Matrix (Fin n) (Fin n) ℝ) by
        rw [Matrix.mul_one], frobenius_norm_orthogonal_mul_mul_orthogonal hWO _ (one_mem _)]
      refine (norm_add_le _ _).trans ?_
      linarith
    have hΔF : ‖Δ‖ ≤ gamma fp.u n * ‖upperPart st.1‖ := by
      refine frobenius_norm_le_of_forall_abs_le hγ0 fun i j => ?_
      simp only [hΔ, of_apply]
      split_ifs with h
      · have := hΔU ⟨i, h⟩ j
        rw [Fintype.card_fin] at this
        exact this
      · rw [abs_zero]
        exact mul_nonneg hγ0 (abs_nonneg _)
    have hWΔ : ‖Wᵀ * Δ‖ = ‖Δ‖ := by
      rw [show Wᵀ * Δ = Wᵀ * Δ * (1 : Matrix (Fin n) (Fin n) ℝ) by rw [Matrix.mul_one],
        frobenius_norm_orthogonal_mul_mul_orthogonal hWtO _ (one_mem _)]
    refine (norm_add_le _ _).trans ?_
    rw [hWΔ]
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
    have h1 : gamma fp.u n * ‖upperPart st.1‖ ≤ gamma fp.u n * ((1 + ε) ^ n * ‖A‖) :=
      mul_le_mul_of_nonneg_left hRF hγ0
    nlinarith

open scoped Matrix.Norms.Frobenius in
/-- **Equation (5.3.7)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$
and $b \in \mathbb{R}^m$, let the rounding model be idempotent with
$(3(4(18m + 31) + 2m + 1) + m + 3)u < 1$, and let $\hat x$ be computed by Algorithm 5.3.2 from a
run of Algorithm 5.2.1 with every $\hat\beta_j \neq 0$ and nonsingular $\hat R_1$, as in
(5.3.6). Then there are $\delta A$ and $\delta b$ such that $\hat x$ minimizes
$\|(A + \delta A)x - (b + \delta b)\|_2$ and
$$\|\delta A\|_F \le ((1 + \varepsilon)^n(1 + \gamma_n) - 1)\|A\|_F, \qquad \varepsilon =
  3\gamma_{3(18m + 31) + m + 3}.$$

**Reading.** The source prints $\|\delta A\|_F \le (6m - 3n + 41)nu\|A\|_F + O(u^2)$. The
theorem states the rigorous bound with explicit $\gamma$ constants.

This is the first bound of `GolubVanLoan.Chapter05.equation_5_3_6`. -/
theorem equation_5_3_7 {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) (hnm : n ≤ m)
    (hu : ((3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ∀ st ∈ (algorithm_5_2_1 fp.round A).run, (∀ j, st.2 j ≠ 0) →
      (∀ i : Fin n, upperPart st.1 (Fin.castLE hnm i) i ≠ 0) →
    ∀ x ∈ (householderLSSolve fp.round hnm st b).run,
      ∃ (δA : Matrix (Fin m) (Fin n) ℝ) (δb : Fin m → ℝ),
      IsLeastSquaresSolution (A + δA) (toLp 2 (b + δb)) (toLp 2 x) ∧
      ‖δA‖ ≤ ((1 + 3 * gamma fp.u (3 * (18 * m + 31) + m + 3)) ^ n * (1 + gamma fp.u n) - 1) *
        ‖A‖ := by
  intro st hst hβ hR x hx
  obtain ⟨δA, δb, h, hA, -⟩ := equation_5_3_6 hfp hnm hu A b st hst hβ hR x hx
  exact ⟨δA, δb, h, hA⟩

/-- **Equation (5.3.8)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$
and $b \in \mathbb{R}^m$, let the rounding model be idempotent with
$(3(4(18m + 31) + 2m + 1) + m + 3)u < 1$, and let $\hat x$ be computed by Algorithm 5.3.2 from a
run of Algorithm 5.2.1 with every $\hat\beta_j \neq 0$ and nonsingular $\hat R_1$, as in
(5.3.6). Then there are $\delta A$ and $\delta b$ such that $\hat x$ minimizes
$\|(A + \delta A)x - (b + \delta b)\|_2$ and
$$\|\delta b\|_2 \le ((1 + \varepsilon')^n - 1)\|b\|_2, \qquad \varepsilon' =
  3\gamma_{3(4(18m + 31) + 2m + 1) + m + 3}.$$

**Reading.** The source prints $\|\delta b\|_2 \le (6m - 3n + 40)nu\|b\|_2 + O(u^2)$. The
theorem states the rigorous bound with explicit $\gamma$ constants.

This is the second bound of `GolubVanLoan.Chapter05.equation_5_3_6`. -/
theorem equation_5_3_8 {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) (hnm : n ≤ m)
    (hu : ((3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ∀ st ∈ (algorithm_5_2_1 fp.round A).run, (∀ j, st.2 j ≠ 0) →
      (∀ i : Fin n, upperPart st.1 (Fin.castLE hnm i) i ≠ 0) →
    ∀ x ∈ (householderLSSolve fp.round hnm st b).run,
      ∃ (δA : Matrix (Fin m) (Fin n) ℝ) (δb : Fin m → ℝ),
      IsLeastSquaresSolution (A + δA) (toLp 2 (b + δb)) (toLp 2 x) ∧
      ‖(toLp 2 δb : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + 3 * gamma fp.u (3 * (4 * (18 * m + 31) + 2 * m + 1) + m + 3)) ^ n - 1) *
          ‖(toLp 2 b : EuclideanSpace ℝ (Fin m))‖ := by
  intro st hst hβ hR x hx
  obtain ⟨δA, δb, h, -, hb⟩ := equation_5_3_6 hfp hnm hu A b st hst hβ hR x hx
  exact ⟨δA, δb, h, hb⟩

end HouseholderLSRounding

/-! ### §5.3.6 The sensitivity of the LS problem -/

section Sensitivity

/-- **Theorem 5.3.1** of [golub2013matrix], the angle $\theta_{LS}$. For
$A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$, let $x_{LS} = A^+b$ and
$r_{LS} = b - Ax_{LS}$. The **angle** of the least-squares problem is
$$\theta_{LS} = \arcsin\frac{\|r_{LS}\|_2}{\|b\|_2} \in [0, \pi/2],$$
so that $\sin\theta_{LS} = \|r_{LS}\|_2/\|b\|_2$.

For $b = 0$ the quotient is $0$ in Lean, and $\theta_{LS} = 0$. -/
noncomputable def thetaLS (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.arcsin (‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ / ‖b‖)

/-- **Equation (5.3.10)** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$ and
$b \in \mathbb{R}^m$ with $x_{LS} = A^+b$, the number $\nu_{LS}$ is
$$\nu_{LS} = \frac{\|Ax_{LS}\|_2}{\sigma_n(A)\|x_{LS}\|_2}.$$
Here $\sigma_n(A)$ is the least singular value `⨅ i, A.colSingularValues i`, and the quotient is
$0$ when the denominator is $0$. -/
noncomputable def nuLS (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ /
    ((⨅ i, A.colSingularValues i) * ‖toEuclideanLin A.pinv b‖)

/-- **Equation (5.3.16)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ and
$b \in \mathbb{R}^m$, with $x_{LS} = A^+b$ and $r_{LS} = b - Ax_{LS}$. If $b \neq 0$ and
$Ax_{LS} \neq 0$, then
$$\cos\theta_{LS} = \frac{\|Ax_{LS}\|_2}{\|b\|_2}, \qquad \tan\theta_{LS} =
  \frac{\|r_{LS}\|_2}{\|Ax_{LS}\|_2}.$$

The proof uses $b = Ax_{LS} + r_{LS}$ with $Ax_{LS} \perp r_{LS}$. The angle is
`GolubVanLoan.Chapter05.thetaLS`. -/
theorem equation_5_3_16 (A : Matrix (Fin m) (Fin n) ℝ) {b : EuclideanSpace ℝ (Fin m)}
    (hb : b ≠ 0) (hAx : toEuclideanLin A (toEuclideanLin A.pinv b) ≠ 0) :
    Real.cos (thetaLS A b) = ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ / ‖b‖ ∧
      Real.tan (thetaLS A b) = ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ /
        ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ := by
  set x := toEuclideanLin A.pinv b
  set y := toEuclideanLin A x with hy
  set r := b - y with hr
  have hN : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hY : 0 < ‖y‖ := norm_pos_iff.2 hAx
  have hpy : ‖b‖ ^ 2 = ‖r‖ ^ 2 + ‖y‖ ^ 2 := by
    have := norm_toEuclideanLin_sub_sq_eq_of_normalEquations (normalEquations_pinv A b) 0
    rwa [map_zero, zero_sub, norm_neg, zero_sub, map_neg, norm_neg, ← norm_neg (y - b),
      neg_sub] at this
  have h1 : 1 - (‖r‖ / ‖b‖) ^ 2 = (‖y‖ / ‖b‖) ^ 2 := by
    field_simp
    linarith
  have hs : √(1 - (‖r‖ / ‖b‖) ^ 2) = ‖y‖ / ‖b‖ := by
    rw [h1, Real.sqrt_sq (by positivity)]
  refine ⟨by rw [thetaLS, Real.cos_arcsin, hs], ?_⟩
  rw [thetaLS, Real.tan_arcsin, hs]
  field_simp
  rfl

end Sensitivity

/-! ### Theorem 5.3.1 and the facts (5.3.9) -/

section SensitivityBounds

open scoped Matrix.Norms.L2Operator

/-- If $A$ has linearly independent columns and $x \neq 0$, then $Ax \neq 0$. -/
private theorem toEuclideanLin_ne_zero {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    toEuclideanLin A x ≠ 0 := by
  intro h
  apply hx
  have hinj : Function.Injective A.mulVec := mulVec_injective_iff.2 hA
  have h1 : A *ᵥ ofLp x = A *ᵥ 0 := by
    rw [mulVec_zero]
    have := congrArg ofLp h
    simpa [toEuclideanLin_apply] using this
  have := hinj h1
  ext i
  simpa using congrFun this i

/-- Pythagoras for the least-squares split $b = Ax_{LS} + r_{LS}$:
$\|b\|_2^2 = \|r_{LS}\|_2^2 + \|Ax_{LS}\|_2^2$. -/
private theorem norm_sq_eq_residual_add (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖b‖ ^ 2 = ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ ^ 2 +
      ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ ^ 2 := by
  have := norm_toEuclideanLin_sub_sq_eq_of_normalEquations (normalEquations_pinv A b) 0
  rwa [map_zero, zero_sub, norm_neg, zero_sub, map_neg, norm_neg,
    ← norm_neg (toEuclideanLin A (toEuclideanLin A.pinv b) - b), neg_sub] at this

/-- For $b \neq 0$, $\sin\theta_{LS} = \|r_{LS}\|_2/\|b\|_2$. -/
private theorem sin_thetaLS (A : Matrix (Fin m) (Fin n) ℝ) {b : EuclideanSpace ℝ (Fin m)}
    (hb : b ≠ 0) :
    Real.sin (thetaLS A b) = ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ / ‖b‖ := by
  have hN : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hle : ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ ≤ ‖b‖ := by
    refine le_of_sq_le_sq ?_ hN.le
    have := norm_sq_eq_residual_add A b
    nlinarith [sq_nonneg ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖]
  rw [thetaLS, Real.sin_arcsin (by
      exact le_trans (by norm_num) (div_nonneg (norm_nonneg _) hN.le))
    ((div_le_one hN).2 hle)]

/-- If $\|\delta A\|_2 < \sigma_n(A)$, $\|\delta A\|_2 \le \varepsilon\|A\|_2$ and
$\|\delta b\|_2 \le \varepsilon\|b\|_2$, then with $\sigma' = \sigma_n(A) - \|\delta A\|_2$ the
perturbed solution and residual satisfy $\|\hat x - x\|_2 \le \varepsilon((\|b\|_2 +
\|A\|_2\|x\|_2)/\sigma' + \|A\|_2\|r\|_2/\sigma'^2)$ and $\|\hat r - r\|_2 \le
\varepsilon(\|b\|_2 + \|A\|_2\|x\|_2 + \|A\|_2\|r\|_2/\sigma')$. -/
private theorem ls_perturbation_bounds {A δA : Matrix (Fin m) (Fin n) ℝ}
    {b δb r r' : EuclideanSpace ℝ (Fin m)} {x x' : EuclideanSpace ℝ (Fin n)}
    (hδA : ‖δA‖ < ⨅ i, A.colSingularValues i) (hx : x = toEuclideanLin A.pinv b)
    (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) (hr : r = b - toEuclideanLin A x)
    (hr' : r' = (b + δb) - toEuclideanLin (A + δA) x') {ε : ℝ}
    (hεA : ‖δA‖ ≤ ε * ‖A‖) (hεb : ‖δb‖ ≤ ε * ‖b‖) :
    ‖x' - x‖ ≤ ε * ((‖b‖ + ‖A‖ * ‖x‖) / ((⨅ i, A.colSingularValues i) - ‖δA‖) +
        ‖A‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖) ^ 2) ∧
      ‖r' - r‖ ≤ ε * (‖b‖ + ‖A‖ * ‖x‖ + ‖A‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖)) := by
  have h1 := (norm_leastSquares_sub_le hδA hx hx' hr).2
  have h2 := norm_leastSquares_residual_sub_le hδA hx hx' hr hr'
  have hd : 0 < (⨅ i, A.colSingularValues i) - ‖δA‖ := sub_pos.2 hδA
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · calc (‖δb‖ + ‖δA‖ * ‖x‖) / ((⨅ i, A.colSingularValues i) - ‖δA‖) +
          ‖δA‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖) ^ 2
        ≤ (ε * ‖b‖ + ε * ‖A‖ * ‖x‖) / ((⨅ i, A.colSingularValues i) - ‖δA‖) +
          ε * ‖A‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖) ^ 2 := by gcongr
      _ = _ := by ring
  · calc ‖δb‖ + ‖δA‖ * ‖x‖ + ‖δA‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖)
        ≤ ε * ‖b‖ + ε * ‖A‖ * ‖x‖ + ε * ‖A‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖) := by
          gcongr
      _ = _ := by ring

/-- Let $A, \delta A \in \mathbb{R}^{m \times n}$ and $b, \delta b \in \mathbb{R}^m$ with
$\|A\|_2 > 0$ and $\|b\|_2 > 0$, and let $\varepsilon = \max(\|\delta A\|_2/\|A\|_2, \|\delta
b\|_2/\|b\|_2)$. Then $\|\delta A\|_2 \le \varepsilon\|A\|_2$,
$\|\delta b\|_2 \le \varepsilon\|b\|_2$ and $\varepsilon \ge 0$. -/
theorem le_max_div_mul {A δA : Matrix (Fin m) (Fin n) ℝ} {b δb : EuclideanSpace ℝ (Fin m)}
    (hA : 0 < ‖A‖) (hb : 0 < ‖b‖) :
    ‖δA‖ ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) * ‖A‖ ∧
      ‖δb‖ ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) * ‖b‖ ∧ 0 ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) :=
  ⟨(div_le_iff₀ hA).1 (le_max_left _ _), (div_le_iff₀ hb).1 (le_max_right _ _),
    le_max_of_le_left (div_nonneg (norm_nonneg _) hA.le)⟩

/-- **Theorem 5.3.1** of [golub2013matrix], the bound (5.3.11) in rigorous form. Let
$A \in \mathbb{R}^{m \times n}$ have rank $n$, let $\delta A \in \mathbb{R}^{m \times n}$ with
$\|\delta A\|_2 < \sigma_n(A)$, and let $b, \delta b \in \mathbb{R}^m$ with $b \neq 0$. Let
$x_{LS} = A^+b$ be nonzero, and let $\hat x_{LS} = (A + \delta A)^+(b + \delta b)$. Put
$$\varepsilon = \max\left(\frac{\|\delta A\|_2}{\|A\|_2}, \frac{\|\delta b\|_2}{\|b\|_2}\right),
  \quad \sigma' = \sigma_n(A) - \|\delta A\|_2, \quad \kappa' = \frac{\|A\|_2}{\sigma'}, \quad
  \nu' = \frac{\|Ax_{LS}\|_2}{\sigma'\|x_{LS}\|_2}.$$
Then
$$\frac{\|\hat x_{LS} - x_{LS}\|_2}{\|x_{LS}\|_2} \le
  \varepsilon\left(\frac{\nu'}{\cos\theta_{LS}} + (1 + \nu'\tan\theta_{LS})\kappa'\right).$$

**Generalization.** This is the bracket of (5.3.11) with $\sigma_n(A)$ replaced by $\sigma'$ and
with no $O(\varepsilon^2)$ term. The hypothesis $r_{LS} \neq 0$ of the source is not needed.

The angle is `GolubVanLoan.Chapter05.thetaLS`, and $\sigma_n(A)$ is
`⨅ i, A.colSingularValues i`. For the printed form see `GolubVanLoan.Chapter05.theorem_5_3_1`. -/
theorem theorem_5_3_1_a {A δA : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {b δb : EuclideanSpace ℝ (Fin m)} {x x' : EuclideanSpace ℝ (Fin n)}
    (hδA : ‖δA‖ < ⨅ i, A.colSingularValues i) (hb : b ≠ 0) (hx0 : x ≠ 0)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) :
    ‖x' - x‖ / ‖x‖ ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) *
      (‖toEuclideanLin A x‖ / (((⨅ i, A.colSingularValues i) - ‖δA‖) * ‖x‖) /
          Real.cos (thetaLS A b) +
        (1 + ‖toEuclideanLin A x‖ / (((⨅ i, A.colSingularValues i) - ‖δA‖) * ‖x‖) *
          Real.tan (thetaLS A b)) * (‖A‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖))) := by
  have := neZero_of_ne_zero hx0
  have hAn := l2_opNorm_pos_of_linearIndependent hA
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hAx := toEuclideanLin_ne_zero hA hx0
  have hAxn : 0 < ‖toEuclideanLin A x‖ := norm_pos_iff.2 hAx
  obtain ⟨hεA, hεb, -⟩ := le_max_div_mul (δA := δA) (δb := δb) hAn hbn
  have hd : 0 < (⨅ i, A.colSingularValues i) - ‖δA‖ := sub_pos.2 hδA
  have h := (ls_perturbation_bounds hδA hx hx' rfl rfl hεA hεb).1
  obtain ⟨hcos, htan⟩ := equation_5_3_16 A hb (hx ▸ hAx)
  rw [← hx] at hcos htan
  rw [div_le_iff₀ hxn]
  refine h.trans (le_of_eq ?_)
  rw [hcos, htan]
  field_simp
  ring

/-- **Theorem 5.3.1** of [golub2013matrix], the bound (5.3.12) in rigorous form. Let
$A \in \mathbb{R}^{m \times n}$ have rank $n$, let $\delta A \in \mathbb{R}^{m \times n}$ with
$\|\delta A\|_2 < \sigma_n(A)$, and let $b, \delta b \in \mathbb{R}^m$ with $b \neq 0$. Let
$x_{LS} = A^+b$ and $r_{LS} = b - Ax_{LS}$ be nonzero, and let
$\hat x_{LS} = (A + \delta A)^+(b + \delta b)$ and $\hat r_{LS} = (b + \delta b) - (A + \delta
A)\hat x_{LS}$. With $\varepsilon$ and $\kappa' = \|A\|_2/(\sigma_n(A) - \|\delta A\|_2)$ as in
(5.3.11),
$$\frac{\|\hat r_{LS} - r_{LS}\|_2}{\|r_{LS}\|_2} \le
  \varepsilon\left(\frac{1}{\sin\theta_{LS}} + \frac{\kappa_2(A)}{\nu_{LS}\tan\theta_{LS}} +
  \kappa'\right).$$

**Reading.** The source states (5.3.12) up to a term $O(\varepsilon^2)$, with $\kappa_2(A)$ in
the last term. The rigorous bound has $\kappa'$ in the last term and no $O(\varepsilon^2)$ term.

The number $\nu_{LS}$ is (5.3.10), `GolubVanLoan.Chapter05.nuLS`, and the angle is
`GolubVanLoan.Chapter05.thetaLS`. -/
theorem theorem_5_3_1_b {A δA : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {b δb r r' : EuclideanSpace ℝ (Fin m)} {x x' : EuclideanSpace ℝ (Fin n)}
    (hδA : ‖δA‖ < ⨅ i, A.colSingularValues i) (hb : b ≠ 0) (hx0 : x ≠ 0) (hr0 : r ≠ 0)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) (hr' : r' = (b + δb) - toEuclideanLin (A + δA) x') :
    ‖r' - r‖ / ‖r‖ ≤ max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) *
      (1 / Real.sin (thetaLS A b) + 1 / (nuLS A b * Real.tan (thetaLS A b)) * kappa2 A +
        ‖A‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖)) := by
  have := neZero_of_ne_zero hx0
  have hAn := l2_opNorm_pos_of_linearIndependent hA
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hrn : 0 < ‖r‖ := norm_pos_iff.2 hr0
  have hAx := toEuclideanLin_ne_zero hA hx0
  have hAxn : 0 < ‖toEuclideanLin A x‖ := norm_pos_iff.2 hAx
  have hσ := iInf_colSingularValues_pos_of_linearIndependent hA
  obtain ⟨hεA, hεb, -⟩ := le_max_div_mul (δA := δA) (δb := δb) hAn hbn
  have h := (ls_perturbation_bounds hδA hx hx' hr hr' hεA hεb).2
  obtain ⟨-, htan⟩ := equation_5_3_16 A hb (hx ▸ hAx)
  have hsin := sin_thetaLS A hb
  rw [← hx, ← hr] at htan hsin
  rw [div_le_iff₀ hrn]
  refine h.trans (le_of_eq ?_)
  rw [hsin, htan, kappa2_eq_div hA, nuLS, ← hx]
  field_simp

/-- Let $\sigma > 0$ and $0 \le t \le \sigma/2$. If $\sigma' \ge \sigma - t$, then
$1/\sigma' \le 1/\sigma + 2t/\sigma^2$ and $1/\sigma'^2 \le 1/\sigma^2 + 6t/\sigma^3$. -/
theorem one_div_le_add_of_sub_le {σ σ' t : ℝ} (hσ : 0 < σ) (ht0 : 0 ≤ t) (ht : 2 * t ≤ σ)
    (h : σ - t ≤ σ') :
    1 / σ' ≤ 1 / σ + 2 * t / σ ^ 2 ∧ 1 / σ' ^ 2 ≤ 1 / σ ^ 2 + 6 * t / σ ^ 3 := by
  have hst : 0 < σ - t := by linarith
  have h1 : 1 / σ' ≤ 1 / σ + 2 * t / σ ^ 2 := by
    refine (one_div_le_one_div_of_le hst h).trans ?_
    rw [div_le_iff₀ hst]
    have e : (1 / σ + 2 * t / σ ^ 2) * (σ - t) = 1 + t * (σ - 2 * t) / σ ^ 2 := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ t * (σ - 2 * t) / σ ^ 2 := div_nonneg (mul_nonneg ht0 (by linarith)) (by positivity)
    linarith
  refine ⟨h1, ?_⟩
  have h0 : 0 ≤ 1 / σ' := one_div_nonneg.2 (by linarith)
  have h2 : 1 / σ' ^ 2 ≤ (1 / σ + 2 * t / σ ^ 2) ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    rwa [div_pow, one_pow] at this
  have e2 : 1 / σ ^ 2 + 6 * t / σ ^ 3 - (1 / σ + 2 * t / σ ^ 2) ^ 2 =
      2 * t * (σ - 2 * t) / σ ^ 4 := by
    field_simp
    ring
  have : 0 ≤ 2 * t * (σ - 2 * t) / σ ^ 4 :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

/-- **Theorem 5.3.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have rank $n$, and
let $b \in \mathbb{R}^m$ be such that $b$, $x_{LS} = A^+b$ and $r_{LS} = b - Ax_{LS}$ are
nonzero. Then there are constants $K$ and $\varepsilon_0 > 0$ with the following property. Let
$\delta A \in \mathbb{R}^{m \times n}$ and $\delta b \in \mathbb{R}^m$ satisfy
$$\varepsilon = \max\left(\frac{\|\delta A\|_2}{\|A\|_2}, \frac{\|\delta b\|_2}{\|b\|_2}\right)
  \le \varepsilon_0,$$
and let $\hat x_{LS} = (A + \delta A)^+(b + \delta b)$ and $\hat r_{LS} = (b + \delta b) - (A +
\delta A)\hat x_{LS}$. Then
$$\frac{\|\hat x_{LS} - x_{LS}\|_2}{\|x_{LS}\|_2} \le
  \varepsilon\left\{\frac{\nu_{LS}}{\cos\theta_{LS}} + (1 +
  \nu_{LS}\tan\theta_{LS})\kappa_2(A)\right\} + K\varepsilon^2 \qquad (5.3.11)$$
and
$$\frac{\|\hat r_{LS} - r_{LS}\|_2}{\|r_{LS}\|_2} \le
  \varepsilon\left\{\frac{1}{\sin\theta_{LS}} + \left(\frac{1}{\nu_{LS}\tan\theta_{LS}} +
  1\right)\kappa_2(A)\right\} + K\varepsilon^2. \qquad (5.3.12)$$

**Reading.** The source writes the remainder as $O(\varepsilon^2)$. The theorem reads it as
$K\varepsilon^2$ for $\varepsilon \le \varepsilon_0$, where $K$ and $\varepsilon_0$ depend on
$A$ and $b$.

The proof combines the rigorous bounds behind `GolubVanLoan.Chapter05.theorem_5_3_1_a` and
`GolubVanLoan.Chapter05.theorem_5_3_1_b` with $1/(\sigma_n - \varepsilon\|A\|_2) \le
1/\sigma_n + 2\varepsilon\|A\|_2/\sigma_n^2$ for $\varepsilon \le \varepsilon_0 =
\sigma_n/(2\|A\|_2)$. The number $\nu_{LS}$ is `GolubVanLoan.Chapter05.nuLS`, and the angle is
`GolubVanLoan.Chapter05.thetaLS`. -/
theorem theorem_5_3_1 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {b : EuclideanSpace ℝ (Fin m)} (hb : b ≠ 0)
    (hr0 : b - toEuclideanLin A (toEuclideanLin A.pinv b) ≠ 0)
    (hx0 : toEuclideanLin A.pinv b ≠ 0) :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ (δA : Matrix (Fin m) (Fin n) ℝ) (δb : EuclideanSpace ℝ (Fin m)),
      max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) ≤ ε₀ →
      ‖toEuclideanLin (A + δA).pinv (b + δb) - toEuclideanLin A.pinv b‖ /
          ‖toEuclideanLin A.pinv b‖ ≤
        max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) * (nuLS A b / Real.cos (thetaLS A b) +
          (1 + nuLS A b * Real.tan (thetaLS A b)) * kappa2 A) +
          K * max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) ^ 2 ∧
      ‖((b + δb) - toEuclideanLin (A + δA) (toEuclideanLin (A + δA).pinv (b + δb))) -
          (b - toEuclideanLin A (toEuclideanLin A.pinv b))‖ /
          ‖b - toEuclideanLin A (toEuclideanLin A.pinv b)‖ ≤
        max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) * (1 / Real.sin (thetaLS A b) +
          (1 / (nuLS A b * Real.tan (thetaLS A b)) + 1) * kappa2 A) +
          K * max (‖δA‖ / ‖A‖) (‖δb‖ / ‖b‖) ^ 2 := by
  have := neZero_of_ne_zero hx0
  have hAn := l2_opNorm_pos_of_linearIndependent hA
  have hσ := iInf_colSingularValues_pos_of_linearIndependent hA
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hxn : 0 < ‖toEuclideanLin A.pinv b‖ := norm_pos_iff.2 hx0
  have hrn := norm_pos_iff.2 hr0
  have hAx := toEuclideanLin_ne_zero hA hx0
  have hAxn := norm_pos_iff.2 hAx
  obtain ⟨hcos, htan⟩ := equation_5_3_16 A hb hAx
  have hsin := sin_thetaLS A hb
  have hκ := kappa2_eq_div hA
  set x := toEuclideanLin A.pinv b with hx
  set r := b - toEuclideanLin A x with hr
  set σ := ⨅ i, A.colSingularValues i with hσdef
  set a := ‖A‖ with ha
  set P := ‖b‖ + a * ‖x‖ with hP
  set Q := a * ‖r‖ with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  -- the book's brackets
  have eq1 : nuLS A b / Real.cos (thetaLS A b) +
      (1 + nuLS A b * Real.tan (thetaLS A b)) * kappa2 A = (P / σ + Q / σ ^ 2) / ‖x‖ := by
    rw [nuLS, ← hx, ← hσdef, hcos, htan, hκ, hP, hQ]
    field_simp
    ring
  have eq2 : 1 / Real.sin (thetaLS A b) +
      (1 / (nuLS A b * Real.tan (thetaLS A b)) + 1) * kappa2 A = P / ‖r‖ + a / σ := by
    rw [nuLS, ← hx, ← hσdef, hsin, htan, hκ, hP]
    field_simp
    ring
  refine ⟨(2 * a * P / σ ^ 2 + 6 * a * Q / σ ^ 3) / ‖x‖ + 2 * a ^ 2 / σ ^ 2, σ / (2 * a),
    by positivity, fun δA δb hε => ?_⟩
  set ε := max (‖δA‖ / a) (‖δb‖ / ‖b‖) with hεdef
  obtain ⟨hεA, hεb, hε0⟩ := le_max_div_mul (δA := δA) (δb := δb) hAn hbn
  have ht : 2 * (ε * a) ≤ σ := by
    rw [le_div_iff₀ (by positivity)] at hε
    linarith
  have hδA : ‖δA‖ < σ := by nlinarith
  obtain ⟨h1, h2⟩ := ls_perturbation_bounds hδA hx rfl hr rfl hεA hεb
  obtain ⟨hu, hu2⟩ := one_div_le_add_of_sub_le hσ (by positivity) ht (show σ - ε * a ≤ σ - ‖δA‖ by
    linarith)
  have hK2 : 0 ≤ 2 * a ^ 2 / σ ^ 2 := by positivity
  have hK1 : 0 ≤ (2 * a * P / σ ^ 2 + 6 * a * Q / σ ^ 3) / ‖x‖ := by positivity
  constructor
  · rw [eq1, div_le_iff₀ hxn]
    calc ‖toEuclideanLin (A + δA).pinv (b + δb) - x‖
        ≤ ε * (P * (1 / σ + 2 * (ε * a) / σ ^ 2) + Q * (1 / σ ^ 2 + 6 * (ε * a) / σ ^ 3)) := by
          refine h1.trans ?_
          rw [div_eq_mul_one_div P, div_eq_mul_one_div Q]
          exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hu hP0)
            (mul_le_mul_of_nonneg_left hu2 hQ0)) hε0
      _ = (ε * ((P / σ + Q / σ ^ 2) / ‖x‖) +
            (2 * a * P / σ ^ 2 + 6 * a * Q / σ ^ 3) / ‖x‖ * ε ^ 2) * ‖x‖ := by
          field_simp
          ring
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right hK2
  · rw [eq2, div_le_iff₀ hrn]
    calc ‖(b + δb) - toEuclideanLin (A + δA) (toEuclideanLin (A + δA).pinv (b + δb)) - r‖
        ≤ ε * (P + Q * (1 / σ + 2 * (ε * a) / σ ^ 2)) := by
          refine h2.trans ?_
          rw [div_eq_mul_one_div Q]
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hu hQ0)) hε0
      _ = (ε * (P / ‖r‖ + a / σ) + 2 * a ^ 2 / σ ^ 2 * ε ^ 2) * ‖r‖ := by
          rw [hQ]
          field_simp
          ring
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_left hK1

/-- **Equation (5.3.9)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, with $1 \le n < m$. Then
$$\|A(A^TA)^{-1}A^T\|_2 = 1, \quad \|(A^TA)^{-1}A^T\|_2 = \frac{1}{\sigma_n(A)}, \quad \|I -
  A(A^TA)^{-1}A^T\|_2 = 1, \quad \|(A^TA)^{-1}\|_2 = \frac{1}{\sigma_n(A)^2}.$$

The source says that these facts are easily verified using the SVD. The matrix $(A^TA)^{-1}A^T$
is the pseudoinverse $A^+$. The condition $n \ge 1$ is `[NeZero n]`.

**Reading.** The two projector norms are both one when $0<n<m$ and $A$ has full column rank. In
the square full-rank case the residual projector is zero. -/
theorem equation_5_3_9 [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (hmn : n < m) :
    ‖A * (Aᵀ * A)⁻¹ * Aᵀ‖ = 1 ∧ ‖(Aᵀ * A)⁻¹ * Aᵀ‖ = 1 / ⨅ i, A.colSingularValues i ∧
      ‖1 - A * (Aᵀ * A)⁻¹ * Aᵀ‖ = 1 ∧ ‖(Aᵀ * A)⁻¹‖ = 1 / (⨅ i, A.colSingularValues i) ^ 2 := by
  have hp : A.pinv = (Aᵀ * A)⁻¹ * Aᵀ := by
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA,
      conjTranspose_eq_transpose_of_trivial]
  have hA0 : A ≠ 0 := norm_pos_iff.1 (l2_opNorm_pos_of_linearIndependent hA)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← hp]
    exact l2_opNorm_mul_pinv_eq_one hA0
  · rw [← hp, l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA, one_div]
  · rw [Matrix.mul_assoc, ← hp]
    exact l2_opNorm_one_sub_mul_pinv_eq_one (by simpa using hmn)
  · have h := l2_opNorm_inv_conjTranspose_mul_self hA
    rw [conjTranspose_eq_transpose_of_trivial] at h
    rw [h, one_div, inv_pow]

/-- **Section 5.3.6** of [golub2013matrix], the bound $\nu_{LS} \le \kappa_2(A)$. Let
$A \in \mathbb{R}^{m \times n}$ have full column rank, with $n \ge 1$, and let
$b \in \mathbb{R}^m$. Then
$$\nu_{LS} = \frac{\|Ax_{LS}\|_2}{\sigma_n(A)\|x_{LS}\|_2} \le \frac{\|A\|_2}{\sigma_n(A)} =
  \kappa_2(A).$$

The bound follows from $\|Ax_{LS}\|_2 \le \|A\|_2\|x_{LS}\|_2$. For $x_{LS} = 0$ the number
$\nu_{LS}$ is $0$ by the convention of `GolubVanLoan.Chapter05.nuLS`. -/
theorem nuLS_le_kappa2 [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (b : EuclideanSpace ℝ (Fin m)) : nuLS A b ≤ kappa2 A := by
  have hσ := iInf_colSingularValues_pos_of_linearIndependent hA
  rw [nuLS, kappa2_eq_div hA]
  rcases eq_or_ne (toEuclideanLin A.pinv b) 0 with h | h
  · rw [h, norm_zero, mul_zero, div_zero]
    exact div_nonneg (norm_nonneg _) hσ.le
  · have hxn := norm_pos_iff.2 h
    rw [div_le_div_iff₀ (by positivity) hσ]
    calc ‖toEuclideanLin A (toEuclideanLin A.pinv b)‖ * ⨅ i, A.colSingularValues i
        ≤ ‖A‖ * ‖toEuclideanLin A.pinv b‖ * ⨅ i, A.colSingularValues i := by
          gcongr
          exact norm_toEuclideanLin_apply_le _ _
      _ = ‖A‖ * ((⨅ i, A.colSingularValues i) * ‖toEuclideanLin A.pinv b‖) := by ring

/-- **Equation (5.3.15)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ have full column
rank, let $E \in \mathbb{R}^{m \times n}$ and $b, f \in \mathbb{R}^m$, and let
$x(t) = (A + tE)^+(b + tf)$ be the solution of the perturbed problem (5.3.13) for $t$ near $0$.
Then $x$ is differentiable at $t = 0$, with
$$\dot x(0) = (A^TA)^{-1}A^T(f - Ex_{LS}) + (A^TA)^{-1}E^Tr_{LS},$$
where $x_{LS} = A^+b$ and $r_{LS} = b - Ax_{LS}$. -/
theorem equation_5_3_15 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (E : Matrix (Fin m) (Fin n) ℝ) (b f : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => toEuclideanLin (A + t • E).pinv (b + t • f))
      (toEuclideanLin ((Aᵀ * A)⁻¹ * Aᵀ) (f - toEuclideanLin E (toEuclideanLin A.pinv b)) +
        toEuclideanLin ((Aᵀ * A)⁻¹ * Eᵀ) (b - toEuclideanLin A (toEuclideanLin A.pinv b))) 0 := by
  have h := hasDerivAt_pinv_mulVec_line hA E b f
  nth_rw 1 [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA] at h
  simpa only [conjTranspose_eq_transpose_of_trivial] using h

/-- The derivative of the residual in the proof of Theorem 5.3.1 of [golub2013matrix]. Let
$A \in \mathbb{R}^{m \times n}$ have full column rank, let $E \in \mathbb{R}^{m \times n}$ and
$b, f \in \mathbb{R}^m$, and let $x(t) = (A + tE)^+(b + tf)$ and
$r(t) = (b + tf) - (A + tE)x(t)$. Then $r$ is differentiable at $t = 0$, with
$$\dot r(0) = (I - A(A^TA)^{-1}A^T)(f - Ex_{LS}) - A(A^TA)^{-1}E^Tr_{LS}.$$
-/
theorem equation_5_3_15_residual {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (E : Matrix (Fin m) (Fin n) ℝ) (b f : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => (b + t • f) -
        toEuclideanLin (A + t • E) (toEuclideanLin (A + t • E).pinv (b + t • f)))
      (toEuclideanLin (1 - A * (Aᵀ * A)⁻¹ * Aᵀ)
          (f - toEuclideanLin E (toEuclideanLin A.pinv b)) -
        toEuclideanLin (A * (Aᵀ * A)⁻¹ * Eᵀ)
          (b - toEuclideanLin A (toEuclideanLin A.pinv b))) 0 := by
  set X : ℝ → EuclideanSpace ℝ (Fin n) := fun t => toEuclideanLin (A + t • E).pinv (b + t • f)
    with hXdef
  have hX := equation_5_3_15 hA E b f
  have hX0 : X 0 = toEuclideanLin A.pinv b := by simp [hXdef]
  have hb : HasDerivAt (fun t : ℝ => b + t • f) f 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const f).const_add b
  have hA' := (LinearMap.toContinuousLinearMap (toEuclideanLin A)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hX
  have hE' := (LinearMap.toContinuousLinearMap (toEuclideanLin E)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hX
  have hEt := (hasDerivAt_id (0 : ℝ)).smul hE'
  have hsum := hb.sub (hA'.add hEt)
  have hfun : (fun t : ℝ => (b + t • f) -
      toEuclideanLin (A + t • E) (toEuclideanLin (A + t • E).pinv (b + t • f))) =
      (fun t : ℝ => b + t • f) - (LinearMap.toContinuousLinearMap (toEuclideanLin A) ∘ X +
        (id : ℝ → ℝ) • (LinearMap.toContinuousLinearMap (toEuclideanLin E) ∘ X)) := by
    funext t
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap', id_eq, hXdef]
    rw [show toEuclideanLin (A + t • E) = toEuclideanLin A + t • toEuclideanLin E by
      rw [map_add, map_smul], LinearMap.add_apply, LinearMap.smul_apply]
  have e0 : ∀ v, toEuclideanLin (1 - A * (Aᵀ * A)⁻¹ * Aᵀ) v =
      v - toEuclideanLin A (toEuclideanLin ((Aᵀ * A)⁻¹ * Aᵀ) v) := fun v => by
    rw [map_sub, LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply, Matrix.mul_assoc,
      toEuclideanLin_mul_apply]
  have e1 : ∀ v, toEuclideanLin (A * (Aᵀ * A)⁻¹ * Eᵀ) v =
      toEuclideanLin A (toEuclideanLin ((Aᵀ * A)⁻¹ * Eᵀ) v) := fun v => by
    rw [Matrix.mul_assoc, toEuclideanLin_mul_apply]
  rw [hfun]
  convert hsum using 1
  simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap', id, zero_smul,
    add_zero, zero_add, one_smul]
  rw [e0, e1, map_add]
  abel

end SensitivityBounds

/-! ### §5.3.8 The augmented system -/

section Augmented

/-- **Equation (5.3.20)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ and
$b \in \mathbb{R}^m$. If $r \in \mathbb{R}^m$ and $x \in \mathbb{R}^n$ solve the augmented
system
$$\begin{bmatrix} I_m & A \\ A^T & 0 \end{bmatrix}\begin{bmatrix} r \\ x \end{bmatrix} =
  \begin{bmatrix} b \\ 0 \end{bmatrix},$$
that is, $r + Ax = b$ and $A^Tr = 0$, then $x$ minimizes $\|Ax - b\|_2$. The augmented matrix is
nonsingular if and only if $\operatorname{rank}(A) = n$.

The condition $\operatorname{rank}(A) = n$ is `LinearIndependent ℝ Aᵀ`, and nonsingularity is
`IsUnit`.

**Reading.** Same augmented system implies least squares, with nonsingularity characterized by full
column rank.
-/
theorem equation_5_3_20 (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ (b r : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)),
        r + toEuclideanLin A x = b → toEuclideanLin Aᵀ r = 0 → IsLeastSquaresSolution A b x) ∧
      (IsUnit (fromBlocks 1 A Aᵀ 0) ↔ LinearIndependent ℝ Aᵀ) := by
  refine ⟨fun b r x h1 h2 => ?_, ?_⟩
  · have := isLeastSquaresSolution_of_augmented (M := (1 : Matrix (Fin m) (Fin m) ℝ)) isUnit_one
      (A := A) (b := b) (r := r) (x := x)
      (by simpa using h1) (by rwa [conjTranspose_eq_transpose_of_trivial])
    simpa using this
  · have := isUnit_augmented_iff A
    rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **Section 5.3.8** of [golub2013matrix], the solution of the augmented system by QR. Let
$A \in \mathbb{R}^{m \times n}$ with $n \le m$ have a QR factorization $A = QR$, and let
$R_1 = R(1{:}n, 1{:}n)$. Let $f \in \mathbb{R}^m$ and $g \in \mathbb{R}^n$, write
$Q^Tf = [f_1; f_2]$ with $f_1 \in \mathbb{R}^n$, and let $h, z \in \mathbb{R}^n$ solve
$R_1^Th = g$ and $R_1z = f_1 - h$. Then $p = Q[h; f_2]$ satisfies
$$\begin{bmatrix} I & A \\ A^T & 0 \end{bmatrix}\begin{bmatrix} p \\ z \end{bmatrix} =
  \begin{bmatrix} f \\ g \end{bmatrix}.$$

The source obtains this from the transformed system
$$\begin{bmatrix} I_n & 0 & R_1 \\ 0 & I_{m-n} & 0 \\ R_1^T & 0 & 0 \end{bmatrix}\begin{bmatrix}
  h \\ f_2 \\ z \end{bmatrix} = \begin{bmatrix} f_1 \\ f_2 \\ g \end{bmatrix}.$$
The vector $[h; f_2]$ is $h$ in the first $n$ positions and $Q^Tf$ below. No rank condition is
needed, because $h$ and $z$ are given. -/
theorem augmentedSolve_qr {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (hQR : IsQR A Q R) (hnm : n ≤ m) (f : Fin m → ℝ)
    (g : Fin n → ℝ) {h z : Fin n → ℝ} (hh : (firstRows R hnm)ᵀ *ᵥ h = g)
    (hz : firstRows R hnm *ᵥ z = fun i => (Qᵀ *ᵥ f) (Fin.castLE hnm i) - h i) :
    fromBlocks 1 A Aᵀ 0 *ᵥ Sum.elim
        (Q *ᵥ fun i => if hi : (i : ℕ) < n then h ⟨i, hi⟩ else (Qᵀ *ᵥ f) i) z =
      Sum.elim f g := by
  set y : Fin m → ℝ := fun i => if hi : (i : ℕ) < n then h ⟨i, hi⟩ else (Qᵀ *ᵥ f) i with hy
  have hQ : Qᵀ * Q = 1 := by
    have := hQR.mem_unitaryGroup
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      at this
    exact this
  have hQ' : Q * Qᵀ = 1 := by
    have := hQR.mem_unitaryGroup
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      at this
    exact this
  -- `R z` is `R₁ z` padded with zeros
  have hRz : ∀ i : Fin m, (R *ᵥ z) i =
      if hi : (i : ℕ) < n then (firstRows R hnm *ᵥ z) ⟨i, hi⟩ else 0 := by
    intro i
    split_ifs with hi
    · rfl
    · simp only [mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hQR.apply_eq_zero i j (by have := j.isLt; omega), zero_mul]
  have hyRz : y + R *ᵥ z = Qᵀ *ᵥ f := by
    ext i
    rw [Pi.add_apply, hRz, hy]
    simp only
    split_ifs with hi
    · rw [hz]
      simp only
      rw [add_sub_cancel]
      rfl
    · rw [add_zero]
  have hRy : Rᵀ *ᵥ y = g := by
    ext j
    have h1 : ((firstRows R hnm)ᵀ *ᵥ h) j =
        ∑ k : Fin n, (fun i : Fin m => R i j * y i) (Fin.castLE hnm k) := by
      simp only [mulVec, dotProduct, transpose_apply, firstRows, submatrix_apply, id]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hy, Fin.val_castLE]
    rw [← hh, h1]
    refine Eq.trans ?_ (Fin.sum_castLE_eq_sum_ite hnm (fun i : Fin m => R i j * y i)).symm
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rfl
    · rw [hQR.apply_eq_zero i j (by have := j.isLt; omega), zero_mul]
  rw [fromBlocks_mulVec]
  ext (i | j)
  · simp only [Sum.elim_inl, Function.comp_def, Sum.elim_inr, one_mulVec]
    rw [← hQR.mul_eq, ← mulVec_mulVec, ← mulVec_add, hyRz, mulVec_mulVec, hQ', one_mulVec]
  · simp only [Sum.elim_inr, Function.comp_def, Sum.elim_inl, zero_mulVec, add_zero]
    rw [← hQR.mul_eq, transpose_mul, mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one, hRy]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The product $Q^Ty$ for the factored form $Q = H_1 \cdots H_n$ that Algorithm 5.2.1 of
[golub2013matrix] stores, with the $\beta_j$ that the factorization returned: the reflectors
$H_1, \dots, H_n$ are applied in turn, each by `GolubVanLoan.Chapter05.householderApplyLeft` on
the rows $j{:}m$ of the single column $y$. -/
noncomputable def storedQTransposeMulVec (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ)
    (y : Fin m → ℝ) : M (Fin m → ℝ) := do
  let Y ← (List.finRange n).foldlM (fun (Y : Matrix (Fin m) (Fin 1) ℝ) j =>
    householderApplyLeft rnd (storedHouseholderVec A j) (β j) (indexFrom m j) [0] Y)
    (of fun i _ => y i)
  pure fun i => Y i 0

/-- The product $Qy$ for the factored form $Q = H_1 \cdots H_n$ that Algorithm 5.2.1 of
[golub2013matrix] stores, with the returned $\beta_j$: the reflectors are applied in the reverse
order $H_n, \dots, H_1$. -/
noncomputable def storedQMulVec (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ)
    (y : Fin m → ℝ) : M (Fin m → ℝ) := do
  let Y ← (List.finRange n).reverse.foldlM (fun (Y : Matrix (Fin m) (Fin 1) ℝ) j =>
    householderApplyLeft rnd (storedHouseholderVec A j) (β j) (indexFrom m j) [0] Y)
    (of fun i _ => y i)
  pure fun i => Y i 0

/-- One step of the iterative improvement of §5.3.8 of [golub2013matrix] at the iterate $(r, x)$,
with the QR factorization $(A', \beta)$ of Algorithm 5.2.1. The step computes the residuals
$f = b - r - Ax$ and $g = -A^Tr$ with the higher-precision hook `rndHi`, solves the augmented
system with right-hand side $[f; g]$ by QR as in `GolubVanLoan.Chapter05.augmentedSolve_qr`
($[f_1; f_2] = Q^Tf$, $R_1^Th = g$, $R_1z = f_1 - h$, $p = Q[h; f_2]$), and returns
$(r + p, x + z)$. -/
noncomputable def lsImprovementStep (rndHi : ℝ → M ℝ) (hnm : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (QR : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ))
    (st : (Fin m → ℝ) × (Fin n → ℝ)) : M ((Fin m → ℝ) × (Fin n → ℝ)) := do
  let f ← (List.finRange m).foldlM (fun (f : Fin m → ℝ) i => do
    let s ← dotAccum rndHi (List.finRange n) (A i) st.2 0
    let t ← rndHi (b i - st.1 i)
    let u ← rndHi (t - s)
    pure (Function.update f i u)) 0
  let g ← (List.finRange n).foldlM (fun (g : Fin n → ℝ) k => do
    let s ← dotAccum rndHi (List.finRange m) (fun i => A i k) st.1 0
    pure (Function.update g k (-s))) 0
  let c ← storedQTransposeMulVec rnd QR.1 QR.2 f
  let R₁ := (upperPart QR.1).firstRows hnm
  let h ← Chapter03.algorithm_3_1_1 rnd R₁ᵀ g
  let d ← (List.finRange n).foldlM (fun (d : Fin n → ℝ) k => do
    let e ← rnd (c (Fin.castLE hnm k) - h k)
    pure (Function.update d k e)) 0
  let z ← Chapter03.algorithm_3_1_2 rnd R₁ d
  let p ← storedQMulVec rnd QR.1 QR.2 fun i => if hi : (i : ℕ) < n then h ⟨i, hi⟩ else c i
  let r ← (List.finRange m).foldlM (fun (r : Fin m → ℝ) i => do
    let e ← rnd (r i + p i)
    pure (Function.update r i e)) st.1
  let x ← (List.finRange n).foldlM (fun (x : Fin n → ℝ) k => do
    let e ← rnd (x k + z k)
    pure (Function.update x k e)) st.2
  pure (r, x)

/-- **Section 5.3.8** of [golub2013matrix], iterative improvement of the augmented system (a
displayed, unnumbered algorithm):
```
r⁽⁰⁾ = 0, x⁽⁰⁾ = 0
for k = 0, 1, …
    [f⁽ᵏ⁾; g⁽ᵏ⁾] = [b; 0] - [I A; Aᵀ 0][r⁽ᵏ⁾; x⁽ᵏ⁾]
    [I A; Aᵀ 0][p⁽ᵏ⁾; z⁽ᵏ⁾] = [f⁽ᵏ⁾; g⁽ᵏ⁾]
    [r⁽ᵏ⁺¹⁾; x⁽ᵏ⁺¹⁾] = [r⁽ᵏ⁾; x⁽ᵏ⁾] + [p⁽ᵏ⁾; z⁽ᵏ⁾]
end
```
The source requires that the residuals $f^{(k)}$ and $g^{(k)}$ be computed in higher precision;
the program has a second rounding hook `rndHi` for them. The augmented systems are solved
through the QR factorization of Algorithm 5.2.1, computed once and stored in factored form
(`GolubVanLoan.Chapter05.lsImprovementStep`). The argument `fuel` is the number of iterations.

**Reading.** The program takes a finite iteration count and separate rounding functions for the
ordinary and higher-precision operations. The source describes an open-ended loop. -/
noncomputable def lsIterativeImprovement (rndHi : ℝ → M ℝ) (hnm : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (fuel : ℕ) :
    M ((Fin m → ℝ) × (Fin n → ℝ)) := do
  let QR ← algorithm_5_2_1 rnd A
  (List.range fuel).foldlM (fun st _ => lsImprovementStep rnd rndHi hnm A b QR st) (0, 0)

end Programs

/-- In exact arithmetic, the reflector $I - \beta vv^T$ with the stored Householder vector $v$ of
column $j$, applied on the rows $j{:}m$ of a single column $Y$, gives $(I - \beta vv^T)Y$. -/
private theorem householderApplyLeft_col_pure (A : Matrix (Fin m) (Fin n) ℝ) (β : ℝ) (j : Fin n)
    (Y : Matrix (Fin m) (Fin 1) ℝ) :
    Id.run (householderApplyLeft pure (storedHouseholderVec A j) β (indexFrom m j) [0] Y) =
      (1 - β • vecMulVec (storedHouseholderVec A j) (storedHouseholderVec A j)) * Y :=
  householderApplyLeft_spec_of_forall_mem (nodup_indexFrom m j) (List.nodup_singleton 0)
    (fun q => by rw [Fin.fin_one_eq_zero q]; exact List.mem_singleton_self 0)
    (fun _ hi => storedHouseholderVec_eq_zero A j hi) β Y

/-- In exact arithmetic, `GolubVanLoan.Chapter05.storedQTransposeMulVec` computes $Q^Ty$ for the
factored form $Q$ = `GolubVanLoan.Chapter05.factoredQ β A`. -/
theorem storedQTransposeMulVec_pure (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ)
    (y : Fin m → ℝ) : Id.run (storedQTransposeMulVec pure A β y) = (factoredQ β A)ᵀ *ᵥ y := by
  simp only [storedQTransposeMulVec, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    householderApplyLeft_col_pure]
  rw [foldl_mul_eq_transpose_prod_mul _ (fun j => transpose_one_sub_smul_vecMulVec _ _),
    ← factoredQ_eq_prod]
  funext i
  simp [Matrix.mul_apply, mulVec, dotProduct]

/-- **Algorithm 5.3.2** of [golub2013matrix], with the returned $\beta$. The program runs Algorithm
5.2.1 on $A$, computes $Q^Tb$ from the stored vectors and the $\beta_j$ that Algorithm 5.2.1
returned (`GolubVanLoan.Chapter05.storedQTransposeMulVec`), and solves
$R(1{:}n, 1{:}n)x = (Q^Tb)(1{:}n)$ by Algorithm 3.1.2.

**Correction.** The printed Algorithm 5.3.2 recomputes $\beta_j = 2/v^Tv$ and fails when a
returned $\beta_j$ is $0$ (`GolubVanLoan.Chapter05.algorithm_5_3_2_counterexample`). This
program uses the returned $\beta_j$ instead.

This is the least-squares solver that the later sections call. -/
noncomputable def householderLS {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) (hnm : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : M (Fin n → ℝ) := do
  let QR ← algorithm_5_2_1 rnd A
  let c ← storedQTransposeMulVec rnd QR.1 QR.2 b
  Chapter03.algorithm_3_1_2 rnd ((upperPart QR.1).firstRows hnm) fun i => c (Fin.castLE hnm i)

/-- **Algorithm 5.3.2** of [golub2013matrix], with the returned $\beta$, correctness in exact
arithmetic. Let $A \in \mathbb{R}^{m \times n}$ have full column rank, with $n \le m$, and let
$b \in \mathbb{R}^m$. Then the output of `GolubVanLoan.Chapter05.householderLS` in exact
arithmetic minimizes $\|Ax - b\|_2$.

No condition on the Householder steps is needed, in contrast to
`GolubVanLoan.Chapter05.algorithm_5_3_2_spec`.

**Correction.** Corrected program is exact for any full-column-rank input.
-/
theorem householderLS_spec (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) :
    IsLeastSquaresSolution A (toLp 2 b) (toLp 2 (Id.run (householderLS pure hnm A b))) := by
  obtain ⟨hQR, -⟩ := algorithm_5_2_1_spec hnm A
  simp only [householderLS, Id.run_bind, storedQTransposeMulVec_pure]
  exact isLeastSquaresSolution_solve_firstRows hnm hQR hA b

/-- In exact arithmetic, `GolubVanLoan.Chapter05.storedQMulVec` computes $Qy$ for the factored form
$Q$ = `GolubVanLoan.Chapter05.factoredQ β A`. -/
theorem storedQMulVec_pure (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (y : Fin m → ℝ) :
    Id.run (storedQMulVec pure A β y) = factoredQ β A *ᵥ y := by
  simp only [storedQMulVec, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    householderApplyLeft_col_pure]
  have key : ∀ (l : List (Fin n)) (Y : Matrix (Fin m) (Fin 1) ℝ),
      l.reverse.foldl (fun Y j => (1 - β j • vecMulVec (storedHouseholderVec A j)
        (storedHouseholderVec A j)) * Y) Y =
        (l.map fun j => 1 - β j • vecMulVec (storedHouseholderVec A j)
          (storedHouseholderVec A j)).prod * Y := by
    intro l
    induction l with
    | nil => intro Y; simp
    | cons a l ih =>
      intro Y
      rw [List.reverse_cons, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        List.map_cons, List.prod_cons, Matrix.mul_assoc]
  rw [key, ← factoredQ_eq_prod]
  funext i
  simp [Matrix.mul_apply, mulVec, dotProduct]

/-- One step of the iterative improvement in exact arithmetic, from any iterate $(r, x)$, gives the
solution of the augmented system (5.3.20): afterwards $r + Ax = b$ and $A^Tr = 0$. -/
private theorem lsImprovementStep_pure (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) (st : (Fin m → ℝ) × (Fin n → ℝ)) :
    (Id.run (lsImprovementStep pure pure hnm A b (Id.run (algorithm_5_2_1 pure A)) st)).1 +
        A *ᵥ (Id.run (lsImprovementStep pure pure hnm A b
          (Id.run (algorithm_5_2_1 pure A)) st)).2 = b ∧
      Aᵀ *ᵥ (Id.run (lsImprovementStep pure pure hnm A b
        (Id.run (algorithm_5_2_1 pure A)) st)).1 = 0 := by
  obtain ⟨hQR, -⟩ := algorithm_5_2_1_spec hnm A
  set QR := Id.run (algorithm_5_2_1 pure A) with hQRdef
  set Q := factoredQ QR.2 QR.1 with hQ
  set R₁ := (upperPart QR.1).firstRows hnm with hR₁
  have hup := hQR.isUpperTriangular_firstRows hnm
  have hdiag := hQR.firstRows_diag_ne_zero_of_linearIndependent hnm hA
  set f : Fin m → ℝ := b - st.1 - A *ᵥ st.2 with hf
  set g : Fin n → ℝ := -(Aᵀ *ᵥ st.1) with hg
  set h := Id.run (Chapter03.algorithm_3_1_1 pure R₁ᵀ g) with hh
  set z := Id.run (Chapter03.algorithm_3_1_2 pure R₁
    fun k => (Qᵀ *ᵥ f) (Fin.castLE hnm k) - h k) with hz
  set p := Q *ᵥ fun i => if hi : (i : ℕ) < n then h ⟨i, hi⟩ else (Qᵀ *ᵥ f) i with hp
  have hlow : R₁ᵀ.IsLowerTriangular := fun i j hij => hup hij
  have hh' : R₁ᵀ *ᵥ h = g := Chapter03.algorithm_3_1_1_spec hlow
    (fun i => by rw [transpose_apply]; exact hdiag i) g
  have hrun : Id.run (lsImprovementStep pure pure hnm A b QR st) = (st.1 + p, st.2 + z) := by
    have hf' : (fun k => b k - st.1 k - (0 + ((List.finRange n).map fun j =>
        A k j * st.2 j).sum)) = f := by
      funext k
      simp [hf, mulVec, dotProduct, Fin.sum_univ_def]
    have hg' : (fun k => -(0 + ((List.finRange m).map fun i => A i k * st.1 i).sum)) = g := by
      funext k
      simp [hg, mulVec, dotProduct, Fin.sum_univ_def]
    simp only [lsImprovementStep, Id.run_bind, Id.run_pure, List.idRun_foldlM, dotAccum_pure,
      storedQTransposeMulVec_pure, storedQMulVec_pure, pure_bind, List.foldl_update_eq_ite,
      List.mem_finRange, ↓reduceIte, hf', hg', ← hQ, ← hR₁, ← hh]
    simp only [← hz, ← hp]
    rw [List.foldl_update_of_nodup (List.nodup_finRange m) (fun k y => y k + p k)
        fun _ _ _ _ _ e => by rw [e],
      List.foldl_update_of_nodup (List.nodup_finRange n) (fun k y => y k + z k)
        fun _ _ _ _ _ e => by rw [e]]
    simp only [List.mem_finRange, ↓reduceIte]
    rfl
  have hz' : R₁ *ᵥ z = fun k => (Qᵀ *ᵥ f) (Fin.castLE hnm k) - h k :=
    Chapter03.algorithm_3_1_2_spec hup hdiag _
  have haug := augmentedSolve_qr hQR hnm f g hh' hz'
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, zero_mulVec,
    add_zero] at haug
  have e1 : p + A *ᵥ z = f := funext fun i => congrFun haug (Sum.inl i)
  have e2 : Aᵀ *ᵥ p = g := funext fun j => congrFun haug (Sum.inr j)
  rw [hrun]
  refine ⟨?_, ?_⟩
  · simp only
    rw [mulVec_add, show st.1 + p + (A *ᵥ st.2 + A *ᵥ z) = st.1 + A *ᵥ st.2 + (p + A *ᵥ z) by
      abel, e1, hf]
    abel
  · simp only
    rw [mulVec_add, e2, hg, add_neg_cancel]

/-- Iterative improvement of §5.3.8 of [golub2013matrix] in exact arithmetic. Let
$A \in \mathbb{R}^{m \times n}$ have full column rank, with $n \le m$, let $b \in \mathbb{R}^m$,
and run at least one iteration. Then the output $(r, x)$ solves the augmented system (5.3.20),
that is, $r + Ax = b$ and $A^Tr = 0$, and so $x$ minimizes $\|Ax - b\|_2$.

**Reading.** Finite implementation yields exact augmented solution for a positive budget.
-/
theorem lsIterativeImprovement_spec (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) {fuel : ℕ} (hfuel : 0 < fuel) :
    let out := Id.run (lsIterativeImprovement pure pure hnm A b fuel)
    out.1 + A *ᵥ out.2 = b ∧ Aᵀ *ᵥ out.1 = 0 ∧
      IsLeastSquaresSolution A (toLp 2 b) (toLp 2 out.2) := by
  intro out
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have hout : out = Id.run (lsImprovementStep pure pure hnm A b (Id.run (algorithm_5_2_1 pure A))
      ((List.range k).foldl (fun st _ => Id.run (lsImprovementStep pure pure hnm A b
        (Id.run (algorithm_5_2_1 pure A)) st)) (0, 0))) := by
    simp only [out, lsIterativeImprovement, Id.run_bind, List.idRun_foldlM, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨h1, h2⟩ := lsImprovementStep_pure hnm hA b
    ((List.range k).foldl (fun st _ => Id.run (lsImprovementStep pure pure hnm A b
      (Id.run (algorithm_5_2_1 pure A)) st)) (0, 0))
  rw [← hout] at h1 h2
  refine ⟨h1, h2, (equation_5_3_20 A).1 _ (toLp 2 out.1) _ ?_ ?_⟩
  · rw [toEuclideanLin_toLp, ← toLp_add, h1]
  · rw [toEuclideanLin_toLp, h2]
    rfl

end Augmented

/-! ### §5.3.9 Point/line/plane nearness problems in 3-space -/

section CrossProduct

/-- **Section 5.3.9** of [golub2013matrix], the cross-product matrix. The **cross-product matrix**
of $v \in \mathbb{R}^3$ is
$$v^c = \begin{bmatrix} 0 & -v_3 & v_2 \\ v_3 & 0 & -v_1 \\ -v_2 & v_1 & 0 \end{bmatrix},$$
so that $p \times q = p^cq$ (`GolubVanLoan.Chapter05.crossMatrix_mulVec`).

The entries $v_1, v_2, v_3$ are `v 0`, `v 1`, `v 2`. -/
def crossMatrix (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]

/-- For $p, q \in \mathbb{R}^3$, $p \times q = p^cq = -q^cp = -(q \times p)$. -/
theorem crossMatrix_mulVec (p q : Fin 3 → ℝ) :
    p ⨯₃ q = crossMatrix p *ᵥ q ∧ p ⨯₃ q = -(crossMatrix q *ᵥ p) ∧ p ⨯₃ q = -(q ⨯₃ p) := by
  refine ⟨?_, ?_, (cross_anticomm q p).symm⟩ <;>
  · ext i
    fin_cases i <;> simp [crossMatrix, cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring

/-- For $a, b, x \in \mathbb{R}^k$, the entries of $(ab^T)x$ are $((ab^T)x)_i = a_i(b^Tx)$. -/
theorem vecMulVec_mulVec_apply {k : ℕ} (a b x : Fin k → ℝ) (i : Fin k) :
    (vecMulVec a b *ᵥ x) i = a i * (b ⬝ᵥ x) := by
  simp only [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

/-- **Equation (5.3.21)** of [golub2013matrix]. For $p, q \in \mathbb{R}^3$, the cross product
$p \times q$ is orthogonal to $p$ and to $q$, that is, $p \times q \in \operatorname{span}\{p,
q\}^\perp$. -/
theorem equation_5_3_21 (p q : Fin 3 → ℝ) : p ⬝ᵥ (p ⨯₃ q) = 0 ∧ q ⬝ᵥ (p ⨯₃ q) = 0 :=
  ⟨dot_self_cross p q, dot_cross_self p q⟩

/-- **Equation (5.3.22)** of [golub2013matrix]. For $p, q, r \in \mathbb{R}^3$,
$$(p \times q) \times r = (p^cq)^cr = (qp^T - pq^T)r = (p^Tr)q - (q^Tr)p.$$
-/
theorem equation_5_3_22 (p q r : Fin 3 → ℝ) :
    (p ⨯₃ q) ⨯₃ r = crossMatrix (crossMatrix p *ᵥ q) *ᵥ r ∧
      (p ⨯₃ q) ⨯₃ r = (vecMulVec q p - vecMulVec p q) *ᵥ r ∧
      (p ⨯₃ q) ⨯₃ r = (p ⬝ᵥ r) • q - (q ⬝ᵥ r) • p := by
  have h3 := cross_cross_eq_smul_sub_smul p q r
  refine ⟨by rw [← (crossMatrix_mulVec p q).1, ← (crossMatrix_mulVec _ r).1], ?_, h3⟩
  rw [h3, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec]
  ext i
  simp [mul_comm]

/-- **Equation (5.3.23)** of [golub2013matrix] (the Binet–Cauchy identity). For
$p, q, r, s \in \mathbb{R}^3$,
$$(p \times q)^T(r \times s) = \det\left([p\ q]^T[r\ s]\right) = \det\begin{bmatrix} p^Tr & p^Ts
  \\ q^Tr & q^Ts \end{bmatrix}.$$
-/
theorem equation_5_3_23 (p q r s : Fin 3 → ℝ) :
    (p ⨯₃ q) ⬝ᵥ (r ⨯₃ s) = det !![p ⬝ᵥ r, p ⬝ᵥ s; q ⬝ᵥ r, q ⬝ᵥ s] := by
  rw [cross_dot_cross, det_fin_two_of]

/-- **Equation (5.3.24)** of [golub2013matrix]. For $p \in \mathbb{R}^3$,
$p^cp^c = pp^T - \|p\|_2^2I_3$. -/
theorem equation_5_3_24 (p : Fin 3 → ℝ) :
    crossMatrix p * crossMatrix p = vecMulVec p p - (p ⬝ᵥ p) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMatrix, Matrix.mul_apply, Fin.sum_univ_three, vecMulVec_apply, dotProduct] <;>
    ring

/-- **Equation (5.3.25)** of [golub2013matrix]. For nonzero $p, q \in \mathbb{R}^3$,
$$\|p^cq\|_2^2 = \|p\|_2^2\|q\|_2^2\left(1 -
  \left(\frac{p^Tq}{\|p\|_2\|q\|_2}\right)^2\right).$$

**Reading.** The normalized inner product in the displayed formula requires both vectors to be
nonzero. -/
theorem equation_5_3_25 {p q : Fin 3 → ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    ‖(toLp 2 (crossMatrix p *ᵥ q) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 =
      ‖(toLp 2 p : EuclideanSpace ℝ (Fin 3))‖ ^ 2 * ‖(toLp 2 q : EuclideanSpace ℝ (Fin 3))‖ ^ 2 *
        (1 - (p ⬝ᵥ q / (‖(toLp 2 p : EuclideanSpace ℝ (Fin 3))‖ *
          ‖(toLp 2 q : EuclideanSpace ℝ (Fin 3))‖)) ^ 2) := by
  have hP : 0 < ‖(toLp 2 p : EuclideanSpace ℝ (Fin 3))‖ := by simpa using hp
  have hQ : 0 < ‖(toLp 2 q : EuclideanSpace ℝ (Fin 3))‖ := by simpa using hq
  rw [← (crossMatrix_mulVec p q).1, ← dotProduct_self_eq_norm_sq, cross_dot_cross,
    ← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq, div_pow, mul_pow,
    ← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq, dotProduct_comm q p]
  have hp' : p ⬝ᵥ p ≠ 0 := by rw [dotProduct_self_eq_norm_sq]; positivity
  have hq' : q ⬝ᵥ q ≠ 0 := by rw [dotProduct_self_eq_norm_sq]; positivity
  field_simp

/-- If $v^Tw = 0$, then $\|w\|_2 \le \|w + \tau v\|_2$ for every $\tau \in \mathbb{R}$. -/
private theorem norm_le_of_dotProduct_eq_zero {v w : Fin 3 → ℝ} (h : v ⬝ᵥ w = 0) (τ : ℝ) :
    ‖(toLp 2 w : EuclideanSpace ℝ (Fin 3))‖ ≤
      ‖(toLp 2 (w + τ • v) : EuclideanSpace ℝ (Fin 3))‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq]
  have hvv : 0 ≤ v ⬝ᵥ v := by rw [dotProduct_self_eq_norm_sq]; positivity
  have : (w + τ • v) ⬝ᵥ (w + τ • v) = w ⬝ᵥ w + τ ^ 2 * (v ⬝ᵥ v) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm w v, h]
    ring
  rw [this]
  nlinarith [sq_nonneg τ]

/-- **Equation (5.3.26)** of [golub2013matrix], the nearness of a point and a line. Let
$p_1 \neq p_2$ in $\mathbb{R}^3$, let $v = p_2 - p_1$, and let
$L = \{p_1 + \tau v : \tau \in \mathbb{R}\}$ be the line through $p_1$ and $p_2$. For
$y \in \mathbb{R}^3$ the point
$$z = y + \frac{1}{v^Tv}v^cv^c(y - p_1)$$
lies on $L$, and it is the point of $L$ closest to $y$: $\|z - y\|_2 \le \|p_1 + \tau v - y\|_2$
for every $\tau \in \mathbb{R}$. -/
theorem equation_5_3_26 {p₁ p₂ : Fin 3 → ℝ} (hp : p₁ ≠ p₂) (y : Fin 3 → ℝ) :
    let v := p₂ - p₁
    let z := y + (1 / (v ⬝ᵥ v)) • ((crossMatrix v * crossMatrix v) *ᵥ (y - p₁))
    (∃ τ : ℝ, z = p₁ + τ • v) ∧
      ∀ τ : ℝ, ‖(toLp 2 (z - y) : EuclideanSpace ℝ (Fin 3))‖ ≤
        ‖(toLp 2 (p₁ + τ • v - y) : EuclideanSpace ℝ (Fin 3))‖ := by
  intro v z
  have hv : v ≠ 0 := sub_ne_zero.2 hp.symm
  have hvv : v ⬝ᵥ v ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]; exact pow_ne_zero 2 (by simpa using hv)
  set t := v ⬝ᵥ (y - p₁) / (v ⬝ᵥ v) with ht
  have hz : z = p₁ + t • v := by
    ext i
    simp only [z, equation_5_3_24, sub_mulVec, smul_mulVec, one_mulVec, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vecMulVec_mulVec_apply, ht]
    field_simp
    ring
  refine ⟨⟨t, hz⟩, fun τ => ?_⟩
  have horth : v ⬝ᵥ (z - y) = 0 := by
    rw [hz, show p₁ + t • v - y = t • v - (y - p₁) by abel, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, ht]
    field_simp
    ring
  have := norm_le_of_dotProduct_eq_zero horth (τ - t)
  rwa [show z - y + (τ - t) • v = p₁ + τ • v - y by rw [hz, sub_smul]; abel] at this

/-- For $v, w, d_0 \in \mathbb{R}^3$ with $r = v \times w \neq 0$, the numbers
$\alpha = w^Tr^cd_0/r^Tr$ and $\beta = v^Tr^cd_0/r^Tr$ make $\alpha v - \beta w - d_0$
orthogonal to $v$ and to $w$. -/
private theorem lineLine_orthogonal {v w d₀ : Fin 3 → ℝ} (hr : v ⨯₃ w ≠ 0) :
    let α := w ⬝ᵥ (crossMatrix (v ⨯₃ w) *ᵥ d₀) / ((v ⨯₃ w) ⬝ᵥ (v ⨯₃ w))
    let β := v ⬝ᵥ (crossMatrix (v ⨯₃ w) *ᵥ d₀) / ((v ⨯₃ w) ⬝ᵥ (v ⨯₃ w))
    v ⬝ᵥ (-d₀ + α • v - β • w) = 0 ∧ w ⬝ᵥ (-d₀ + α • v - β • w) = 0 := by
  intro α β
  have hN : (v ⨯₃ w) ⬝ᵥ (v ⨯₃ w) ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]; exact pow_ne_zero 2 (by simpa using hr)
  have hc : crossMatrix (v ⨯₃ w) *ᵥ d₀ = (v ⬝ᵥ d₀) • w - (w ⬝ᵥ d₀) • v := by
    rw [← (crossMatrix_mulVec _ _).1, cross_cross_eq_smul_sub_smul]
  have hNe : (v ⨯₃ w) ⬝ᵥ (v ⨯₃ w) = (v ⬝ᵥ v) * (w ⬝ᵥ w) - (v ⬝ᵥ w) * (v ⬝ᵥ w) := by
    rw [cross_dot_cross, dotProduct_comm w v]
  simp only [α, β, hc, dotProduct_sub, dotProduct_smul, dotProduct_add, dotProduct_neg,
    smul_eq_mul] at hN ⊢
  rw [dotProduct_comm w v] at *
  constructor <;> field_simp <;> rw [hNe] <;> ring

/-- **Equation (5.3.27)** of [golub2013matrix], the nearness of two lines. Let
$p_1, p_2, q_1, q_2 \in \mathbb{R}^3$, let $v = p_2 - p_1$ and $w = q_2 - q_1$, and let
$L_1 = \{p_1 + \tau v\}$ and $L_2 = \{q_1 + \tau w\}$. Assume that $r = v^cw$ is nonzero, that
is, the lines are not parallel. Then the points
$$z_1 = p_1 + \frac{1}{r^Tr}vw^Tr^c(q_1 - p_1), \qquad z_2 = q_1 + \frac{1}{r^Tr}wv^Tr^c(q_1 -
  p_1)$$
lie on $L_1$ and $L_2$, and they minimize the distance between the lines: $\|z_1 - z_2\|_2 \le
\|(p_1 + \tau_1v) - (q_1 + \tau_2w)\|_2$ for all $\tau_1, \tau_2 \in \mathbb{R}$.

**Correction.** The source omits the hypothesis $r \neq 0$. For $r = 0$ the formulas divide by
zero. -/
theorem equation_5_3_27 {p₁ p₂ q₁ q₂ : Fin 3 → ℝ}
    (hr : crossMatrix (p₂ - p₁) *ᵥ (q₂ - q₁) ≠ 0) :
    let v := p₂ - p₁
    let w := q₂ - q₁
    let r := crossMatrix v *ᵥ w
    let z₁ := p₁ + (1 / (r ⬝ᵥ r)) • (vecMulVec v w *ᵥ (crossMatrix r *ᵥ (q₁ - p₁)))
    let z₂ := q₁ + (1 / (r ⬝ᵥ r)) • (vecMulVec w v *ᵥ (crossMatrix r *ᵥ (q₁ - p₁)))
    (∃ τ : ℝ, z₁ = p₁ + τ • v) ∧ (∃ τ : ℝ, z₂ = q₁ + τ • w) ∧
      ∀ τ₁ τ₂ : ℝ, ‖(toLp 2 (z₁ - z₂) : EuclideanSpace ℝ (Fin 3))‖ ≤
        ‖(toLp 2 ((p₁ + τ₁ • v) - (q₁ + τ₂ • w)) : EuclideanSpace ℝ (Fin 3))‖ := by
  intro v w r z₁ z₂
  have hr' : v ⨯₃ w ≠ 0 := by rwa [(crossMatrix_mulVec v w).1]
  have hrr : r = v ⨯₃ w := ((crossMatrix_mulVec v w).1).symm
  obtain ⟨hv, hw⟩ := lineLine_orthogonal (d₀ := q₁ - p₁) hr'
  set α := w ⬝ᵥ (crossMatrix (v ⨯₃ w) *ᵥ (q₁ - p₁)) / ((v ⨯₃ w) ⬝ᵥ (v ⨯₃ w)) with hα
  set β := v ⬝ᵥ (crossMatrix (v ⨯₃ w) *ᵥ (q₁ - p₁)) / ((v ⨯₃ w) ⬝ᵥ (v ⨯₃ w)) with hβ
  have hz₁ : z₁ = p₁ + α • v := by
    ext i
    simp only [z₁, hrr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vecMulVec_mulVec_apply, hα]
    ring
  have hz₂ : z₂ = q₁ + β • w := by
    ext i
    simp only [z₂, hrr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vecMulVec_mulVec_apply, hβ]
    ring
  refine ⟨⟨α, hz₁⟩, ⟨β, hz₂⟩, fun τ₁ τ₂ => ?_⟩
  set e := -(q₁ - p₁) + α • v - β • w with he
  have hze : z₁ - z₂ = e := by rw [hz₁, hz₂, he]; abel
  have hd : (p₁ + τ₁ • v) - (q₁ + τ₂ • w) = e + ((τ₁ - α) • v - (τ₂ - β) • w) := by
    rw [he, sub_smul, sub_smul]; abel
  rw [hze, hd]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq]
  set g := (τ₁ - α) • v - (τ₂ - β) • w with hg
  have hge : e ⬝ᵥ g = 0 := by
    rw [hg, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm e v,
      dotProduct_comm e w, hv, hw]
    simp
  have hgg : 0 ≤ g ⬝ᵥ g := by rw [dotProduct_self_eq_norm_sq]; positivity
  rw [add_dotProduct, dotProduct_add, dotProduct_add, hge, dotProduct_comm g e, hge]
  linarith

/-- **Equation (5.3.28)** of [golub2013matrix]. Let $p_1, p_2, q_1, q_2$, $v$, $w$, $r$, $z_1$,
$z_2$ and the lines $L_1$, $L_2$ be as in (5.3.27), with $r = v^cw \neq 0$. Then the point
$$z_2 = q_1 + \frac{1}{r^Tr}wv^Tr^c(q_1 - p_1)$$
lies on $L_2$, and $\|z_1 - z_2\|_2 \le \|(p_1 + \tau_1v) - (q_1 + \tau_2w)\|_2$ for all
$\tau_1, \tau_2 \in \mathbb{R}$: $z_2$ is the point of $L_2$ closest to $L_1$.

**Correction.** As for (5.3.27), the source omits the hypothesis $r \neq 0$.

This is the second half of `GolubVanLoan.Chapter05.equation_5_3_27`. -/
theorem equation_5_3_28 {p₁ p₂ q₁ q₂ : Fin 3 → ℝ}
    (hr : crossMatrix (p₂ - p₁) *ᵥ (q₂ - q₁) ≠ 0) :
    let v := p₂ - p₁
    let w := q₂ - q₁
    let r := crossMatrix v *ᵥ w
    let z₁ := p₁ + (1 / (r ⬝ᵥ r)) • (vecMulVec v w *ᵥ (crossMatrix r *ᵥ (q₁ - p₁)))
    let z₂ := q₁ + (1 / (r ⬝ᵥ r)) • (vecMulVec w v *ᵥ (crossMatrix r *ᵥ (q₁ - p₁)))
    (∃ τ : ℝ, z₂ = q₁ + τ • w) ∧
      ∀ τ₁ τ₂ : ℝ, ‖(toLp 2 (z₁ - z₂) : EuclideanSpace ℝ (Fin 3))‖ ≤
        ‖(toLp 2 ((p₁ + τ₁ • v) - (q₁ + τ₂ • w)) : EuclideanSpace ℝ (Fin 3))‖ :=
  ⟨(equation_5_3_27 hr).2.1, (equation_5_3_27 hr).2.2⟩

/-- **Equation (5.3.29)** of [golub2013matrix], the nearness of a point and a plane. Let
$p_1, p_2, p_3 \in \mathbb{R}^3$ be such that $v = (p_2 - p_1)^c(p_3 - p_1)$ is nonzero, that
is, the points are not collinear, and let $P = \{x : x^Tv = p_1^Tv\}$. Then $p_1$, $p_2$ and
$p_3$ lie on $P$. For $y \in \mathbb{R}^3$ the point
$$z = p_1 - \frac{1}{v^Tv}v^cv^c(y - p_1)$$
lies on $P$, and it is the point of $P$ closest to $y$: $\|z - y\|_2 \le \|x - y\|_2$ for every
$x \in P$.

**Correction.** The source assumes three distinct points. This is not enough: the points must
not be collinear, so that $v \neq 0$. -/
theorem equation_5_3_29 {p₁ p₂ p₃ : Fin 3 → ℝ}
    (hv : crossMatrix (p₂ - p₁) *ᵥ (p₃ - p₁) ≠ 0) (y : Fin 3 → ℝ) :
    let v := crossMatrix (p₂ - p₁) *ᵥ (p₃ - p₁)
    let z := p₁ - (1 / (v ⬝ᵥ v)) • ((crossMatrix v * crossMatrix v) *ᵥ (y - p₁))
    z ⬝ᵥ v = p₁ ⬝ᵥ v ∧ p₂ ⬝ᵥ v = p₁ ⬝ᵥ v ∧ p₃ ⬝ᵥ v = p₁ ⬝ᵥ v ∧
      ∀ x : Fin 3 → ℝ, x ⬝ᵥ v = p₁ ⬝ᵥ v →
        ‖(toLp 2 (z - y) : EuclideanSpace ℝ (Fin 3))‖ ≤
          ‖(toLp 2 (x - y) : EuclideanSpace ℝ (Fin 3))‖ := by
  intro v z
  have hvv : v ⬝ᵥ v ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]; exact pow_ne_zero 2 (by simpa using hv)
  set t := v ⬝ᵥ (y - p₁) / (v ⬝ᵥ v) with ht
  -- `z = y - t v`
  have hz : z = y - t • v := by
    ext i
    simp only [z, equation_5_3_24, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, vecMulVec_mulVec_apply, ht]
    field_simp
    ring
  have hzv : z ⬝ᵥ v = p₁ ⬝ᵥ v := by
    rw [hz, sub_dotProduct, smul_dotProduct, smul_eq_mul, ht, dotProduct_comm v (y - p₁),
      sub_dotProduct]
    field_simp
    ring
  -- `p₂ - p₁` and `p₃ - p₁` are orthogonal to `v`
  have h2 : p₂ ⬝ᵥ v = p₁ ⬝ᵥ v := by
    have := (equation_5_3_21 (p₂ - p₁) (p₃ - p₁)).1
    rw [(crossMatrix_mulVec _ _).1, sub_dotProduct] at this
    linarith
  have h3 : p₃ ⬝ᵥ v = p₁ ⬝ᵥ v := by
    have := (equation_5_3_21 (p₂ - p₁) (p₃ - p₁)).2
    rw [(crossMatrix_mulVec _ _).1, sub_dotProduct] at this
    linarith
  refine ⟨hzv, h2, h3, fun x hx => ?_⟩
  -- `x - z ⊥ v`, and `z - y = -t v ∥ v`
  have hxz : (x - z) ⬝ᵥ v = 0 := by rw [sub_dotProduct, hx, hzv, sub_self]
  have key : (x - y) ⬝ᵥ (x - y) = (z - y) ⬝ᵥ (z - y) + (x - z) ⬝ᵥ (x - z) := by
    have hzy : z - y = -t • v := by rw [hz]; module
    have e : x - y = (x - z) + (z - y) := by abel
    rw [e, add_dotProduct, dotProduct_add, dotProduct_add, hzy, dotProduct_smul,
      smul_dotProduct, hxz, dotProduct_comm v (x - z), hxz]
    ring
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [← dotProduct_self_eq_norm_sq, ← dotProduct_self_eq_norm_sq, key]
  have : 0 ≤ (x - z) ⬝ᵥ (x - z) := by rw [dotProduct_self_eq_norm_sq]; positivity
  linarith

end CrossProduct

end GolubVanLoan.Chapter05
