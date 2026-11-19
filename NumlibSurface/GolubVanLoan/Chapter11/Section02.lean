/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Numlib.Analysis.Fourier.SineCosineTransform
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.InvariantSubspace
import Numlib.Krylov.Convergence.Polynomial
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import Numlib.Stationary.Block
import Numlib.Stationary.DiagDominant
import Numlib.Stationary.SPD
import Numlib.Stationary.Sweep
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter04.Section08
import NumlibSurface.GolubVanLoan.Chapter07.Section03

/-!
# Golub and Van Loan, Section 11.2: The classical iterations

This module formalizes §11.2 of [golub2013matrix], the classical stationary iterations for a linear
system $Ax = b$ with $A \in \mathbb{R}^{n \times n}$. A splitting $A = M - N$ with $M$ nonsingular
gives the iteration $M x^{(k)} = N x^{(k-1)} + b$. Each step multiplies the error by $G = M^{-1} N$,
and the iteration converges from every starting vector if and only if the spectral radius $\rho(G)$
is less than $1$ (Theorem 11.2.1). With $A = L_A + D_A + U_A$ split into its strictly lower
triangular, diagonal and strictly upper triangular parts, the module defines the componentwise
Jacobi, Gauss–Seidel, SOR and SSOR steps (11.2.2), (11.2.3), (11.2.20) and (11.2.22)–(11.2.23) as
programs, identifies each with the step of a splitting, and proves the convergence theorems for
strictly diagonally dominant and for symmetric positive definite matrices (Theorems 11.2.2–11.2.4).
It also treats the block versions of Jacobi and Gauss–Seidel, the model problem (11.2.10)–(11.2.17)
with its array form and its alternating-direction iteration, and the Chebyshev semi-iterative method
(11.2.28)–(11.2.30).

The proofs specialize the backbone modules `Numlib.Stationary.Splitting`, `Numlib.Stationary.Sweep`,
`Numlib.Stationary.Block`, `Numlib.Stationary.DiagDominant` and `Numlib.Stationary.SPD`. The model
problem uses the Kronecker sum of `Numlib.LinearAlgebra.Matrix.KroneckerSum`, the tridiagonal
Toeplitz matrices of `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz` and the sine transform of
`Numlib.Analysis.Fourier.SineCosineTransform`. The Chebyshev method uses
`Numlib.RingTheory.Polynomial.ChebyshevMinimax`.

## Main definitions

* Equation (11.2.2), `GolubVanLoan.Chapter11.jacobiSweep`: the componentwise Jacobi step.
* Equation (11.2.3), `GolubVanLoan.Chapter11.gaussSeidelSweep`: the componentwise Gauss–Seidel step.
* Equation (11.2.10), `GolubVanLoan.Chapter11.poissonMatrix`: the model matrix $I_{n_1} \otimes
  T_{n_2} + T_{n_1} \otimes I_{n_2}$.
* Equation (11.2.11), `GolubVanLoan.Chapter11.modelT`: the matrix
  $T_m = \operatorname{tridiag}(-1, 2, -1)$.
* §11.2.6, `GolubVanLoan.Chapter11.modelE`: the matrix $E_m = \operatorname{tridiag}(1, 0, 1)$, with
  $T_m = 2I - E_m$.
* §11.2.6, `GolubVanLoan.Chapter11.poissonJacobiArray` and
  `GolubVanLoan.Chapter11.poissonGaussSeidelArray`: the Jacobi and Gauss–Seidel averagings on the
  grid array.
* §11.2.6, `GolubVanLoan.Chapter11.poissonMatrixLex`: the model matrix with the unknowns in
  row-by-row order.
* Equation (11.2.14), `GolubVanLoan.Chapter11.modelEEigenvalues`: the eigenvalues
  $\mu_k^{(m)} = 2 \cos(k\pi/(m + 1))$ of $E_m$.
* §11.2.6, `GolubVanLoan.Chapter11.adiSplittingX` and `GolubVanLoan.Chapter11.adiSplittingY`: the
  two splittings of the alternating-direction iteration.
* Equation (11.2.16), `GolubVanLoan.Chapter11.adiStep`: the alternating-direction step.
* Equation (11.2.20), `GolubVanLoan.Chapter11.sorSweep`: the componentwise SOR step.
* §11.2.7, `GolubVanLoan.Chapter11.backwardSorSweep`: the SOR step from bottom to top.
* Equations (11.2.22)–(11.2.23), `GolubVanLoan.Chapter11.ssorSweep`: one SSOR step.
* Equation (11.2.28), `GolubVanLoan.Chapter11.semiIterativeCombination`: the combination
  $y^{(k)} = \sum_j \nu_j(k) x^{(j)}$ of the iterates.
* §11.2.8, `GolubVanLoan.Chapter11.chebyshevSemiIterativePoly` and
  `GolubVanLoan.Chapter11.chebyshevSymmetricPoly`: the scaled Chebyshev polynomial $p_k$ on
  $[\alpha, \beta]$ and its case $\alpha = -\beta$.
* §11.2.8, `GolubVanLoan.Chapter11.chebyshevSemiIterative`: the Chebyshev semi-iterative method,
  with its loop pass `GolubVanLoan.Chapter11.chebyshevSemiIterativeStep` and its update
  `GolubVanLoan.Chapter11.chebyshevCombine`.

## Main results

* Equation (11.2.4), `GolubVanLoan.Chapter11.equation_11_2_4`: the exact Jacobi step is the step of
  the splitting $M_J = D_A$, $N_J = -(L_A + U_A)$.
* Equation (11.2.5), `GolubVanLoan.Chapter11.equation_11_2_5`: the exact Gauss–Seidel step is the
  step of the splitting $M_{GS} = D_A + L_A$, $N_{GS} = -U_A$.
* §11.2.2, `GolubVanLoan.Chapter11.blockJacobi_eq` and `GolubVanLoan.Chapter11.blockGaussSeidel_eq`:
  a vector satisfies the block Jacobi or block Gauss–Seidel equations if and only if it is the step
  of the block splitting.
* Equations (11.2.6)–(11.2.7), `GolubVanLoan.Chapter11.equation_11_2_7`: the errors of a splitting
  iteration are $x^{(k)} - x = G^k (x^{(0)} - x)$.
* Equation (11.2.8), `GolubVanLoan.Chapter11.equation_11_2_8`: the powers of a $2 \times 2$ Jordan
  block.
* Theorem 11.2.1, `GolubVanLoan.Chapter11.theorem_11_2_1`: a splitting iteration converges from
  every start if and only if $\rho(G) < 1$.
* Equation (11.2.9), `GolubVanLoan.Chapter11.equation_11_2_9`: a bound on $\|G^k\|_2$ from a Schur
  decomposition of $G$.
* Theorem 11.2.2, `GolubVanLoan.Chapter11.theorem_11_2_2`: Jacobi converges for a strictly
  diagonally dominant matrix.
* Theorem 11.2.2, `GolubVanLoan.Chapter11.jacobi_linfty_opNorm_lt_one`: the display in the proof,
  $\|G_J\|_\infty < 1$.
* Theorem 11.2.3, `GolubVanLoan.Chapter11.theorem_11_2_3`: Gauss–Seidel converges for a symmetric
  positive definite matrix.
* §11.2.6, `GolubVanLoan.Chapter11.poissonMatrix_posDef`: the model matrix is symmetric positive
  definite.
* §11.2.6, `GolubVanLoan.Chapter11.isUnit_diagPart_poissonMatrix`: the diagonal of the model matrix
  is nonsingular.
* Equation (11.2.12), `GolubVanLoan.Chapter11.equation_11_2_12`: the Jacobi splitting of the model
  problem has $M_J = 4I$ and $N_J = (I \otimes E_{n_2}) + (E_{n_1} \otimes I)$.
* §11.2.6, `GolubVanLoan.Chapter11.poissonMatrix_mulVec_apply`: the model matrix is the five-point
  stencil.
* §11.2.6, `GolubVanLoan.Chapter11.poissonJacobiArray_eq` and
  `GolubVanLoan.Chapter11.poissonGaussSeidelArray_eq`: the array averagings are one Jacobi step and
  one Gauss–Seidel step for the model system.
* Equation (11.2.13), `GolubVanLoan.Chapter11.equation_11_2_13`: the sine transform matrix
  diagonalizes $E_m$.
* §11.2.6, `GolubVanLoan.Chapter11.jacobi_poisson_diagonal`: the sine basis diagonalizes the Jacobi
  iteration matrix of the model problem.
* Equation (11.2.15), `GolubVanLoan.Chapter11.equation_11_2_15`: the spectral radius of Jacobi on
  the model problem.
* §11.2.6, `GolubVanLoan.Chapter11.adiSplitting_n`: the parts $N_x$ and $N_y$ of the two
  alternating-direction splittings.
* §11.2.6, `GolubVanLoan.Chapter11.adi_error_eq`: the error of the alternating-direction iteration
  and its iteration matrix in the sine basis.
* Equation (11.2.17), `GolubVanLoan.Chapter11.equation_11_2_17`: the spectral radius of the
  alternating-direction iteration, which is less than $1$.
* Equation (11.2.18), `GolubVanLoan.Chapter11.equation_11_2_18`: the SOR splitting has
  $M_\omega = \omega^{-1} D_A + L_A$ and $N_\omega = (\omega^{-1} - 1) D_A - U_A$.
* Equation (11.2.19), `GolubVanLoan.Chapter11.equation_11_2_19`: the exact SOR step is the step of
  the SOR splitting.
* Equation (11.2.21), `GolubVanLoan.Chapter11.equation_11_2_21`: the exact backward SOR step is the
  step of the backward SOR splitting.
* Equations (11.2.22)–(11.2.23), `GolubVanLoan.Chapter11.equation_11_2_22`: the two half steps of
  exact SSOR for a symmetric matrix.
* Equation (11.2.24), `GolubVanLoan.Chapter11.equation_11_2_24`: the formula for $M_{SSOR}$, which
  is symmetric positive definite.
* Equation (11.2.25), `GolubVanLoan.Chapter11.equation_11_2_25`: the exact SSOR step is $x^{(k)} =
  x^{(k-1)} + M_{SSOR}^{-1}(b - A x^{(k-1)})$.
* Theorem 11.2.4, `GolubVanLoan.Chapter11.theorem_11_2_4`: for a symmetric positive definite matrix
  and $0 < \omega < 2$, the SSOR iteration matrix has real eigenvalues in $[0, 1)$ and spectral
  radius less than $1$.
* Equation (11.2.26), `GolubVanLoan.Chapter11.equation_11_2_26`: the errors of exact SSOR are
  $x^{(k)} - x = G^k (x^{(0)} - x)$.
* Equation (11.2.27), `GolubVanLoan.Chapter11.equation_11_2_27`: the scaled SSOR iteration matrix
  and the two formulas for its eigenvalues.
* §11.2.8, `GolubVanLoan.Chapter11.semiIterative_sub_eq`: if $p_k(1) = 1$, then
  $y^{(k)} - x = p_k(G)(x^{(0)} - x)$.
* Equation (11.2.29), `GolubVanLoan.Chapter11.equation_11_2_29`: $\|y^{(k)} - x\|_2 \le \|p_k(G)\|_2
  \|x^{(0)} - x\|_2$.
* §11.2.8, `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le`: the Chebyshev bound $\|y^{(k)} -
  x\|_2 \le \|x - x^{(0)}\|_2 / |c_k(\mu)|$.
* §11.2.8, `GolubVanLoan.Chapter11.chebyshevSemiIterative_spec` and
  `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le'`: the exact Chebyshev program computes
  $y^{(k)}$ with $y^{(k)} - x = p_k(G)(x^{(0)} - x)$, so the Chebyshev bound applies to it.

## Conventions

* The source's $L_A$, $D_A$ and $U_A$ are `Matrix.strictLower A`, `Matrix.diagPart A` and
  `Matrix.strictUpper A`.
* A splitting $A = M - N$ is `Stationary.Splitting A`. It stores $M$, and $N$ is $M - A$. The
  iteration matrix $G = M^{-1} N$ is `Stationary.Splitting.iterationOperator`, and one step
  $x \mapsto M^{-1}(N x + b)$ is `Stationary.Splitting.mulVecStep`.
* The spectral radius $\rho(G)$ of a real matrix is `Matrix.complexSpectralRadius G`, the spectral
  radius of $G$ as a complex matrix, a value in $[0, \infty]$.
* Indices are 0-based. The source's $x_i$ and $a_{ij}$ ($i, j = 1{:}n$) are `x (i - 1)` and
  `A (i - 1) (j - 1)`, and the source's $\mu_k^{(m)}$ ($k = 1{:}m$) is
  `GolubVanLoan.Chapter11.modelEEigenvalues m (k - 1)`.
* In the model problem, $T_m$ and $E_m$ are `Matrix.symmTridiagonalToeplitz`, and the unknowns are
  indexed by `Fin n₁ × Fin n₂`. The lexicographic order of the pairs is the row-by-row order of the
  grid in the source. The sine transform matrix $S_m$ is `Matrix.dst1 m`, whose columns
  `Matrix.sineVec` are the eigenvectors of $T_m$ and $E_m$.

## Implementation notes

* The componentwise steps (11.2.2), (11.2.3) and (11.2.20), the backward SOR step, the array
  averagings of §11.2.6 and the Chebyshev method are programs in the algorithm conventions of
  `NumlibSurface.GolubVanLoan`: they are generic in a monad `M` and a rounding hook `rnd : ℝ → M ℝ`
  that is applied after every `+`, `−`, `×` and `/`, and their loops are `List.foldlM`. The
  componentwise steps share the off-diagonal residual `GolubVanLoan.Chapter11.offDiagResidual`.
* The exact semantics of a program (`M := Id`, `rnd := pure`) is a backbone sweep. An in-place loop
  over a list whose step at $i$ rewrites entry $i$ from the current vector computes at entry $i$ its
  formula on the vector with the new entries before $i$ and the old entries after $i$
  (`List.foldl_update_apply_of_pairwise_rel`). The componentwise recursion `Matrix.sorSweep_apply`
  determines the solution uniquely, by well-founded induction along the order of the sweep.
* The programs do not check for a zero diagonal entry. The theorems assume $a_{ii} \ne 0$ for all
  $i$.
* The alternating-direction step (11.2.16) is an exact map, the composition of two splitting steps,
  not a rounded program, because the source solves two linear systems and fixes no order of
  operations.
* The module uses the restatements of earlier chapters: the nonsingularity of $S_m$ from §4.8.6
  (`GolubVanLoan.Chapter04.dd_eigen`), the positive definiteness of the model matrix from §4.8.4
  (`GolubVanLoan.Chapter04.poisson2D_posDef_bandwidth`) and the Schur power bound (7.3.15)
  (`GolubVanLoan.Chapter07.lemma_7_3_2`).

## Deviations from the source

* **§11.2.2, block Jacobi and Gauss–Seidel** (generalization). Ordered block labels permit
  arbitrary numbers and sizes of blocks and noncontiguous original indices. See
  `GolubVanLoan.Chapter11.blockJacobi_eq` and `GolubVanLoan.Chapter11.blockGaussSeidel_eq`.
* **Equation (11.2.27)** (generalization). The normalized SSOR product and eigenvalue quotient
  hold for symmetric matrices with positive diagonals and any nonzero weight. See
  `GolubVanLoan.Chapter11.equation_11_2_27`.
* **§11.2.8, Chebyshev interval** (reading). The bound requires $\alpha<\beta$ because the
  rescaling divides by $\beta-\alpha$. The program uses finite fuel and the bound is at its
  attained iterate. See `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le` and
  `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le'`.
* **Equation (11.2.8)** (correction). The source prints the corner entry of the $k$-th power as
  $\alpha \lambda^{k-1}$, which is false for $k \ge 2$. The corner entry is
  $k \alpha \lambda^{k-1}$. See `GolubVanLoan.Chapter11.equation_11_2_8`.
* **Equation (11.2.9)** (correction). The proof of Theorem 11.2.1 in the source takes
  $\mu = 2\|E\|_2/(1 - \rho)$, but the bound (7.3.15) needs $\|E\|_F$. The bound is stated with
  $\|E\|_F$. See `GolubVanLoan.Chapter11.equation_11_2_9`.
* **Equation (11.2.9)** (typo). The proof in the source writes $E = A - D$. The strictly upper
  triangular part is $E = T - D$. See `GolubVanLoan.Chapter11.equation_11_2_9`.
* **Theorem 11.2.2** (typo). The proof in the source says "no eigenvalue of $A$"; it means the
  Jacobi iteration matrix $G_J$. See `GolubVanLoan.Chapter11.jacobi_linfty_opNorm_lt_one`.
* **Equation (11.2.17)** (typo). The source prints "$\rho(G) = =$". See
  `GolubVanLoan.Chapter11.equation_11_2_17`.
* **Equations (11.2.18)–(11.2.19)** (correction). The source prints
  $N_\omega = (\omega^{-1} - 1) D_A + U_A$, which is inconsistent with $A = M_\omega - N_\omega$.
  The sign of $U_A$ is changed. See `GolubVanLoan.Chapter11.equation_11_2_18` and
  `GolubVanLoan.Chapter11.equation_11_2_19`.
* **Equation (11.2.20)** (reading). The display of SOR at the component level carries no tag in the
  source. It is taken to be (11.2.20). See `GolubVanLoan.Chapter11.sorSweep`.
* **Equation (11.2.21)** (correction). The source prints $+L_A$ on the right side, which is
  inconsistent with the backward SOR splitting. The sign of $L_A$ is changed. See
  `GolubVanLoan.Chapter11.equation_11_2_21`.
* **Equation (11.2.25)** (generalization). The identity is stated for every $A$ with nonzero
  diagonal entries, not only for symmetric $A$. See `GolubVanLoan.Chapter11.equation_11_2_25`.
* **Theorem 11.2.4** (generalization). The theorem also states that the eigenvalues of $G$ lie in
  $[0, 1)$, which the proof in the source shows. See `GolubVanLoan.Chapter11.theorem_11_2_4`.
* **Section 11.2.8** (typo). The Chebyshev bound in the source writes $\lambda_i \in \lambda(A)$; it
  means the eigenvalues of $G$. See `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le`.

## Not formalized

* **Display (11.2.1).** It is the case $n = 3$ of (11.2.2).
* **The discussion of vectorization and parallelism.**
* **The remark that the Jacobi radius (11.2.15) approaches $1$.** The text does not state the limit
  precisely.
* **Young's theory of the optimal $\omega$.**
* **The Problems.**
-/

open Filter Topology Polynomial Finset
open scoped Matrix Kronecker

namespace GolubVanLoan.Chapter11

variable {n : ℕ}

/-! ### Loop lemmas -/

section Loops

variable {ι : Type*}

/-- Two vectors $z$ and $S$ that satisfy the same recursion $z_i = g_i(z)$, where $g_i$ reads only
the entries $r$-before $i$, are equal when $r$ is well founded. -/
private theorem eq_of_forall_eq_apply (r : ι → ι → Prop) (wf : WellFounded r) {z S : ι → ℝ}
    (g : ι → (ι → ℝ) → ℝ) (hg : ∀ i u v, (∀ j, r j i → u j = v j) → g i u = g i v)
    (hz : ∀ i, z i = g i z) (hS : ∀ i, S i = g i S) : z = S :=
  funext fun i => wf.induction (C := fun i => z i = S i) i fun i ih => by
    rw [hz, hS]; exact hg i z S ih

end Loops

/-- An off-diagonal sum $\sum_{j \ne i} g_j$ is the sum over $j < i$ plus the sum over $j > i$. -/
private theorem sum_ne_eq_sum_lt_add_sum_gt (g : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ univ.filter (· ≠ i), g j =
      ∑ j ∈ univ.filter (· < i), g j + ∑ j ∈ univ.filter (i < ·), g j := by
  rw [← Finset.sum_union (Finset.disjoint_filter.2 fun j _ h1 h2 => lt_asymm h1 h2),
    ← Finset.filter_or]
  exact Finset.sum_congr (Finset.filter_congr fun j _ => ne_iff_lt_or_gt) fun _ _ => rfl

/-! ### The componentwise programs -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The off-diagonal residual of row $i$ in the componentwise iterations (11.2.2), (11.2.3) and
(11.2.20) of [golub2013matrix]. For $A \in \mathbb{R}^{n \times n}$ and $b, x \in \mathbb{R}^n$,
the program computes $$b_i - \sum_{j=1}^{i-1} a_{ij} x_j - \sum_{j=i+1}^{n} a_{ij} x_j.$$

The program starts from $b_i$ and runs over $j \ne i$ in increasing order. Each step rounds the
product $a_{ij} x_j$ and then the difference.

**Reading.** Folds rounded off-diagonal subtraction into a single accumulator.
-/
def offDiagResidual (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (i : Fin n) : M ℝ :=
  ((List.finRange n).filter (· ≠ i)).foldlM (fun s j => do rnd (s - (← rnd (A i j * x j)))) (b i)

/-- **Equation (11.2.2)** of [golub2013matrix] (the Jacobi step). For
$A \in \mathbb{R}^{n \times n}$ and $b, x^{(k-1)} \in \mathbb{R}^n$, the program computes, for
$i = 1{:}n$,
$$x_i^{(k)} = \Bigl(b_i - \sum_{j=1}^{i-1} a_{ij} x_j^{(k-1)} - \sum_{j=i+1}^{n} a_{ij}
  x_j^{(k-1)}\Bigr) \Big/ a_{ii}.$$
Every entry $x_j$ that it reads is an entry of the old vector $x^{(k-1)}$.

The residual is `GolubVanLoan.Chapter11.offDiagResidual` on the old vector, and the quotient is
rounded once. The result overwrites entry $i$ by `Function.update`.

**Reading.** Rounded loop with total division; reads unchanged old iterate.
-/
noncomputable def jacobiSweep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun y i => do
    let s ← offDiagResidual rnd A b x i
    let xi ← rnd (s / A i i)
    pure (Function.update y i xi)) x

/-- **Equation (11.2.3)** of [golub2013matrix] (the Gauss–Seidel step). For
$A \in \mathbb{R}^{n \times n}$ and $b, x^{(k-1)} \in \mathbb{R}^n$, the program computes, for
$i = 1{:}n$,
$$x_i^{(k)} = \Bigl(b_i - \sum_{j=1}^{i-1} a_{ij} x_j^{(k)} - \sum_{j=i+1}^{n} a_{ij}
  x_j^{(k-1)}\Bigr) \Big/ a_{ii}.$$

The arithmetic is that of `GolubVanLoan.Chapter11.jacobiSweep`, but the vector is updated in
place, so that the most recent estimates are used.

**Reading.** Rounded in-place loop with total division.
-/
noncomputable def gaussSeidelSweep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun y i => do
    let s ← offDiagResidual rnd A b y i
    let xi ← rnd (s / A i i)
    pure (Function.update y i xi)) x

/-- **Equation (11.2.20)** of [golub2013matrix] (SOR at the component level, §11.2.7). For
$A \in \mathbb{R}^{n \times n}$, $\omega \in \mathbb{R}$ and $b, x^{(k-1)} \in \mathbb{R}^n$,
the program computes in place, for $i = 1{:}n$,
$$x_i^{(k)} = \omega \Bigl(b_i - \sum_{j=1}^{i-1} a_{ij} x_j^{(k)} - \sum_{j=i+1}^{n} a_{ij}
  x_j^{(k-1)}\Bigr) \Big/ a_{ii} + (1 - \omega) x_i^{(k-1)}.$$

**Reading.** The display carries no tag in the source. It is taken to be the equation (11.2.20),
whose tag does not appear.

The factor $1 - \omega$ is computed and rounded once, before the loop. -/
noncomputable def sorSweep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let c ← rnd (1 - ω)
  (List.finRange n).foldlM (fun y i => do
    let s ← offDiagResidual rnd A b y i
    let g ← rnd (s / A i i)
    let t ← rnd (ω * g)
    let u ← rnd (c * y i)
    let xi ← rnd (t + u)
    pure (Function.update y i xi)) x

/-- **Section 11.2.7** of [golub2013matrix], backward SOR. The program does the arithmetic of
`GolubVanLoan.Chapter11.sorSweep`, with $i$ running from $n$ down to $1$. The source says "we
can just as easily update from bottom to top".

**Reading.** Rounded reverse-order in-place relaxed update.
-/
noncomputable def backwardSorSweep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let c ← rnd (1 - ω)
  (List.finRange n).reverse.foldlM (fun y i => do
    let s ← offDiagResidual rnd A b y i
    let g ← rnd (s / A i i)
    let t ← rnd (ω * g)
    let u ← rnd (c * y i)
    let xi ← rnd (t + u)
    pure (Function.update y i xi)) x

/-- **Equations (11.2.22)–(11.2.23)** of [golub2013matrix] (one SSOR step). A forward SOR sweep from
$x^{(k-1)}$ gives $y^{(k)}$, and a backward SOR sweep from $y^{(k)}$ gives $x^{(k)}$.

**Reading.** Rounded forward then backward in-place sweeps.
-/
noncomputable def ssorSweep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let y ← sorSweep rnd A ω b x
  backwardSorSweep rnd A ω b y

end Programs

/-! ### Exact semantics of the programs -/

/-- In exact arithmetic, the off-diagonal residual is $b_i - \sum_{j \ne i} a_{ij} x_j$. -/
private theorem offDiagResidual_id (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (i : Fin n) :
    Id.run (offDiagResidual pure A b x i) = b i - ∑ j ∈ univ.filter (· ≠ i), A i j * x j := by
  rw [offDiagResidual, List.idRun_foldlM]
  exact (List.foldl_sub_eq_sub_sum_map (fun j => A i j * x j) _ _).trans
    (by rw [List.sum_map_filter_finRange])

/-- The off-diagonal sum with the weights of `List.foldl_update_apply_of_pairwise_rel` along
`List.finRange n` is the sum of $a_{ij} z_j$ over $j < i$ plus the sum of $a_{ij} x_j$ over
$j > i$. -/
private theorem sum_ne_forward (A : Matrix (Fin n) (Fin n) ℝ) (z x : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ univ.filter (· ≠ i), A i j * (if j ∈ List.finRange n ∧ j < i then z j else x j) =
      ∑ j ∈ univ.filter (· < i), A i j * z j + ∑ j ∈ univ.filter (i < ·), A i j * x j := by
  rw [sum_ne_eq_sum_lt_add_sum_gt]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_left ⟨List.mem_finRange j, (Finset.mem_filter.1 hj).2⟩]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_right fun h => lt_asymm h.2 (Finset.mem_filter.1 hj).2]

/-- The off-diagonal sum with the weights of `List.foldl_update_apply_of_pairwise_rel` along the
reversed `List.finRange n` is the sum of $a_{ij} x_j$ over $j < i$ plus the sum of $a_{ij} z_j$
over $j > i$. -/
private theorem sum_ne_backward (A : Matrix (Fin n) (Fin n) ℝ) (z x : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ univ.filter (· ≠ i),
        A i j * (if j ∈ (List.finRange n).reverse ∧ i < j then z j else x j) =
      ∑ j ∈ univ.filter (· < i), A i j * x j + ∑ j ∈ univ.filter (i < ·), A i j * z j := by
  rw [sum_ne_eq_sum_lt_add_sum_gt]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_right fun h => lt_asymm h.2 (Finset.mem_filter.1 hj).2]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_left ⟨List.mem_reverse.2 (List.mem_finRange j), (Finset.mem_filter.1 hj).2⟩]

/-- The exact forward SOR program is the in-place loop $y_i \leftarrow \omega r_i(y)/a_{ii} + (1 -
\omega) y_i$, where $r_i$ is the off-diagonal residual.

**Reading.** Exact closed form with total division.
-/
private theorem sorSweep_run (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    Id.run (sorSweep pure A ω b x) = (List.finRange n).foldl (fun y i => Function.update y i
      (ω * (Id.run (offDiagResidual pure A b y i) / A i i) + (1 - ω) * y i)) x :=
  List.idRun_foldlM

/-- The exact backward SOR program is the same in-place loop in the reverse order.

**Reading.** Exact reverse closed form with total division.
-/
private theorem backwardSorSweep_run (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    Id.run (backwardSorSweep pure A ω b x) = (List.finRange n).reverse.foldl
      (fun y i => Function.update y i
        (ω * (Id.run (offDiagResidual pure A b y i) / A i i) + (1 - ω) * y i)) x :=
  List.idRun_foldlM

/-- If every $a_{ii} \ne 0$, the exact forward SOR program is the backbone sweep `Matrix.sorSweep`.
-/
private theorem sorSweep_id (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A))
    (ω : ℝ) (b x : Fin n → ℝ) : Id.run (sorSweep pure A ω b x) = A.sorSweep ω b x := by
  rw [sorSweep_run]
  refine eq_of_forall_eq_apply (· < ·) wellFounded_lt
    (fun i u => ω / A i i * (b i - ∑ j ∈ univ.filter (· < i), A i j * u j
      - ∑ j ∈ univ.filter (i < ·), A i j * x j) + (1 - ω) * x i) ?_ (fun i => ?_)
    (fun i => Matrix.sorSweep_apply A h ω b x i)
  · intro i u v huv
    rw [Finset.sum_congr rfl fun j hj => by rw [huv j (Finset.mem_filter.1 hj).2]]
  · rw [List.foldl_update_apply_of_pairwise_rel (· < ·) (fun _ _ h h' => lt_asymm h h') _
      (List.pairwise_lt_finRange n) x (List.mem_finRange i), offDiagResidual_id, sum_ne_forward]
    simp only [lt_self_iff_false, and_false, ↓reduceIte]
    ring

/-- If every $a_{ii} \ne 0$, the exact backward SOR program is the backbone sweep
`Matrix.backwardSorSweep`. -/
private theorem backwardSorSweep_id (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Matrix.diagPart A)) (ω : ℝ) (b x : Fin n → ℝ) :
    Id.run (backwardSorSweep pure A ω b x) = A.backwardSorSweep ω b x := by
  rw [backwardSorSweep_run]
  refine eq_of_forall_eq_apply (· > ·) wellFounded_gt
    (fun i u => ω / A i i * (b i - ∑ j ∈ univ.filter (i < ·), A i j * u j
      - ∑ j ∈ univ.filter (· < i), A i j * x j) + (1 - ω) * x i) ?_ (fun i => ?_)
    (fun i => Matrix.backwardSorSweep_apply A h ω b x i)
  · intro i u v huv
    rw [Finset.sum_congr rfl fun j hj => by rw [huv j (Finset.mem_filter.1 hj).2]]
  · have hpw : ((List.finRange n).reverse).Pairwise (fun a b => b < a) :=
      List.pairwise_reverse.2 (List.pairwise_lt_finRange n)
    rw [List.foldl_update_apply_of_pairwise_rel (fun a b => b < a) (fun _ _ h h' => lt_asymm h h')
      _ hpw x
      (List.mem_reverse.2 (List.mem_finRange i)), offDiagResidual_id, sum_ne_backward]
    simp only [lt_self_iff_false, and_false, ↓reduceIte]
    ring

/-- **Equation (11.2.4)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ have
$a_{ii} \ne 0$ for all $i$, and let $b, x \in \mathbb{R}^n$. In exact arithmetic, the Jacobi
step (11.2.2) from $x$ is the step $M_J x^{(k)} = N_J x + b$ of the Jacobi splitting
$A = M_J - N_J$, and this splitting has
$$M_J = D_A, \qquad N_J = -(L_A + U_A).$$

The splitting is `Matrix.jacobiSplitting`. -/
theorem equation_11_2_4 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A))
    (b x : Fin n → ℝ) :
    Id.run (jacobiSweep pure A b x) = (Matrix.jacobiSplitting A h).mulVecStep b x ∧
      (Matrix.jacobiSplitting A h).m = Matrix.diagPart A ∧
      (Matrix.jacobiSplitting A h).n = -(Matrix.strictLower A + Matrix.strictUpper A) := by
  refine ⟨?_, rfl, Matrix.jacobiSplitting_n A h⟩
  have hrun : Id.run (jacobiSweep pure A b x) = (List.finRange n).foldl (fun y i =>
      Function.update y i (Id.run (offDiagResidual pure A b x i) / A i i)) x :=
    List.idRun_foldlM
  rw [← Matrix.jorSweep_one_eq_mulVecStep A h b, hrun]
  funext i
  rw [List.foldl_update_apply_of_pairwise_rel (· < ·) (fun _ _ h h' => lt_asymm h h')
    (fun i _ => Id.run (offDiagResidual pure A b x i) / A i i) (List.pairwise_lt_finRange n) x
    (List.mem_finRange i), offDiagResidual_id, Matrix.jorSweep, Finset.filter_ne']
  ring

/-- **Equation (11.2.5)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ have
$a_{ii} \ne 0$ for all $i$, and let $b, x \in \mathbb{R}^n$. In exact arithmetic, the
Gauss–Seidel step (11.2.3) from $x$ is the step $M_{GS} x^{(k)} = N_{GS} x + b$ of the
Gauss–Seidel splitting $A = M_{GS} - N_{GS}$, and this splitting has
$$M_{GS} = D_A + L_A, \qquad N_{GS} = -U_A.$$

The splitting is `Matrix.gaussSeidelSplitting`. -/
theorem equation_11_2_5 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A))
    (b x : Fin n → ℝ) :
    Id.run (gaussSeidelSweep pure A b x) = (Matrix.gaussSeidelSplitting A h).mulVecStep b x ∧
      (Matrix.gaussSeidelSplitting A h).m = Matrix.diagPart A + Matrix.strictLower A ∧
      (Matrix.gaussSeidelSplitting A h).n = -Matrix.strictUpper A := by
  refine ⟨?_, rfl, Matrix.gaussSeidelSplitting_n A h⟩
  have hrun : Id.run (gaussSeidelSweep pure A b x) = (List.finRange n).foldl (fun y i =>
      Function.update y i (Id.run (offDiagResidual pure A b y i) / A i i)) x :=
    List.idRun_foldlM
  rw [← Matrix.sorSweep_one_eq_mulVecStep A h b, hrun]
  refine eq_of_forall_eq_apply (· < ·) wellFounded_lt
    (fun i u => 1 / A i i * (b i - ∑ j ∈ univ.filter (· < i), A i j * u j
      - ∑ j ∈ univ.filter (i < ·), A i j * x j) + (1 - 1) * x i) ?_ (fun i => ?_)
    (fun i => Matrix.sorSweep_apply A h 1 b x i)
  · intro i u v huv
    rw [Finset.sum_congr rfl fun j hj => by rw [huv j (Finset.mem_filter.1 hj).2]]
  · rw [List.foldl_update_apply_of_pairwise_rel (· < ·) (fun _ _ h h' => lt_asymm h h')
      (fun i y => Id.run (offDiagResidual pure A b y i) / A i i) (List.pairwise_lt_finRange n) x
      (List.mem_finRange i), offDiagResidual_id, sum_ne_forward]
    ring

/-! ### Steps of a splitting -/

section Step

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If $Ax = b$, one step of a splitting maps the error $y - x$ to $G(y - x)$. -/
private theorem mulVecStep_sub {A : Matrix ι ι ℝ} (s : Stationary.Splitting A)
    {b x : ι → ℝ} (hx : A *ᵥ x = b) (y : ι → ℝ) :
    s.mulVecStep b y - x = s.iterationOperator *ᵥ (y - x) := by
  conv_lhs => rw [← (Stationary.Splitting.mulVecStep_fixed_iff s b x).2 hx]
  rw [Stationary.Splitting.mulVecStep_eq_iterationOperator_mulVec_add,
    Stationary.Splitting.mulVecStep_eq_iterationOperator_mulVec_add, Matrix.mulVec_sub]
  abel

/-- A vector $y$ is the step of a splitting from $x$ if and only if $My = Nx + b$. -/
private theorem eq_mulVecStep_iff {A : Matrix ι ι ℝ} (s : Stationary.Splitting A)
    (b x y : ι → ℝ) : y = s.mulVecStep b x ↔ s.m *ᵥ y = s.n *ᵥ x + b := by
  constructor
  · rintro rfl
    exact Matrix.mulVec_nonsing_inv_mulVec s.isUnit _
  · intro h
    change y = s.m⁻¹ *ᵥ (s.n *ᵥ x + b)
    rw [← h, Matrix.nonsing_inv_mulVec_mulVec s.isUnit]

end Step

/-- Row $r$ of $Dv$, for the block diagonal part $D$, is the sum of $a_{rc} v_c$ over the columns
$c$ in the block of $r$. -/
private theorem blockDiagPart_mulVec_apply {p : ℕ} (π : Fin n → Fin p)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (r : Fin n) :
    (Matrix.blockDiagPart π A *ᵥ v) r = ∑ c ∈ univ.filter (fun c => π c = π r), A r c * v c := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.blockDiagPart_apply]
  by_cases hc : π c = π r
  · rw [ite_eq_left hc.symm, ite_eq_left hc]
  · rw [ite_eq_right (Ne.symm hc), ite_eq_right hc, zero_mul]

/-- Row $r$ of $Lv$, for the strict block-lower part $L$, is the sum of $a_{rc} v_c$ over the
columns $c$ in the blocks before the block of $r$. -/
private theorem blockStrictLower_mulVec_apply {p : ℕ} (π : Fin n → Fin p)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (r : Fin n) :
    (Matrix.blockStrictLower π A *ᵥ v) r = ∑ c ∈ univ.filter (fun c => π c < π r), A r c * v c := by
  simp only [Matrix.mulVec, dotProduct, Matrix.blockStrictLower_apply, ite_mul, zero_mul]
  rw [Finset.sum_filter]

/-- Row $r$ of $Uv$, for the strict block-upper part $U$, is the sum of $a_{rc} v_c$ over the
columns $c$ in the blocks after the block of $r$. -/
private theorem blockStrictUpper_mulVec_apply {p : ℕ} (π : Fin n → Fin p)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (r : Fin n) :
    (Matrix.blockStrictUpper π A *ᵥ v) r = ∑ c ∈ univ.filter (fun c => π r < π c), A r c * v c := by
  simp only [Matrix.mulVec, dotProduct, Matrix.blockStrictUpper_apply, ite_mul, zero_mul]
  rw [Finset.sum_filter]

/-- Row $r$ of $Av$ is the sum of $a_{rc} v_c$ over the columns in the block of $r$, plus the sums
over the earlier blocks and over the later blocks. -/
private theorem mulVec_apply_eq_block {p : ℕ} (π : Fin n → Fin p)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (r : Fin n) :
    (A *ᵥ v) r = ∑ c ∈ univ.filter (fun c => π c = π r), A r c * v c +
      ∑ c ∈ univ.filter (fun c => π c < π r), A r c * v c +
      ∑ c ∈ univ.filter (fun c => π r < π c), A r c * v c := by
  conv_lhs => rw [← Matrix.blockDiagPart_add_blockStrictLower_add_blockStrictUpper π A]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply,
    blockDiagPart_mulVec_apply, blockStrictLower_mulVec_apply, blockStrictUpper_mulVec_apply]

/-! ### Block versions -/

/-- **Section 11.2.2** of [golub2013matrix], block Jacobi. Let $A \in \mathbb{R}^{n \times n}$, let
a labelling $\pi$ assign each unknown to one of $p$ blocks, and suppose that the block diagonal
part of $A$ is nonsingular. Let $b, x, x^+ \in \mathbb{R}^n$. Then $x^+$ satisfies the block
equations
$$A_{ii} x^+_i = b_i - \sum_{j \ne i} A_{ij} x_j$$
for every block $i$ if and only if $x^+$ is the step of the block Jacobi splitting from $x$.

The block equations are stated row by row: in row $r$, the columns in the block of $r$ carry
$x^+$ and all other columns carry the old $x$. The blocks need not be contiguous. The splitting
is `Matrix.blockJacobiSplitting`.

**Generalization.** The grouping is any ordered block-label map, so blocks can have arbitrary
sizes and noncontiguous indices. The source displays three contiguous blocks. -/
theorem blockJacobi_eq {p : ℕ} (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Matrix.blockDiagPart π A)) (b x y : Fin n → ℝ) :
    (∀ r, ∑ c ∈ univ.filter (fun c => π c = π r), A r c * y c =
        b r - ∑ c ∈ univ.filter (fun c => π c ≠ π r), A r c * x c) ↔
      y = (Matrix.blockJacobiSplitting π A h).mulVecStep b x := by
  rw [eq_mulVecStep_iff, funext_iff]
  refine forall_congr' fun r => ?_
  have hn : (Matrix.blockJacobiSplitting π A h).n = Matrix.blockDiagPart π A - A := rfl
  have hne := Finset.sum_filter_add_sum_filter_not univ (fun c => π c = π r)
    (fun c => A r c * x c)
  simp only [← ne_eq] at hne
  rw [hn, Matrix.sub_mulVec, Pi.add_apply, Pi.sub_apply]
  change _ ↔ (Matrix.blockDiagPart π A *ᵥ y) r = _
  rw [blockDiagPart_mulVec_apply, blockDiagPart_mulVec_apply]
  simp only [Matrix.mulVec, dotProduct]
  constructor <;> intro h' <;> linarith [hne]

/-- **Section 11.2.2** of [golub2013matrix], block Gauss–Seidel. Let
$A \in \mathbb{R}^{n \times n}$, let a labelling $\pi$ assign each unknown to one of $p$ blocks,
ordered by their labels, and suppose that the block diagonal part of $A$ is nonsingular. Let
$b, x, x^+ \in \mathbb{R}^n$. Then $x^+$ satisfies the block equations
$$A_{ii} x^+_i = b_i - \sum_{j < i} A_{ij} x^+_j - \sum_{j > i} A_{ij} x_j$$
for every block $i$ if and only if $x^+$ is the step of the block Gauss–Seidel splitting from
$x$.

As in `GolubVanLoan.Chapter11.blockJacobi_eq`, the equations are stated row by row. The
splitting is `Matrix.blockGaussSeidelSplitting`.

**Generalization.** The ordered block labels determine which entries have been updated. The
proof applies to any label map, extending the source's three-block display. -/
theorem blockGaussSeidel_eq {p : ℕ} (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Matrix.blockDiagPart π A)) (b x y : Fin n → ℝ) :
    (∀ r, ∑ c ∈ univ.filter (fun c => π c = π r), A r c * y c =
        b r - ∑ c ∈ univ.filter (fun c => π c < π r), A r c * y c
          - ∑ c ∈ univ.filter (fun c => π r < π c), A r c * x c) ↔
      y = (Matrix.blockGaussSeidelSplitting π A h).mulVecStep b x := by
  rw [eq_mulVecStep_iff, funext_iff]
  refine forall_congr' fun r => ?_
  have hm : (Matrix.blockGaussSeidelSplitting π A h).m =
      Matrix.blockDiagPart π A + Matrix.blockStrictLower π A := rfl
  have hn : (Matrix.blockGaussSeidelSplitting π A h).n =
      Matrix.blockDiagPart π A + Matrix.blockStrictLower π A - A := rfl
  rw [hn, hm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [blockDiagPart_mulVec_apply,
    blockDiagPart_mulVec_apply, blockStrictLower_mulVec_apply, blockStrictLower_mulVec_apply,
    mulVec_apply_eq_block π A x r]
  constructor <;> intro h' <;> linarith

/-! ### Splittings and convergence -/

/-- **Equations (11.2.6)–(11.2.7)** of [golub2013matrix]. Let $A = M - N$ be a splitting of
$A \in \mathbb{R}^{n \times n}$ with $M$ nonsingular, and let $Ax = b$. Then the iterates of
$M x^{(k)} = N x^{(k-1)} + b$ from any $x^{(0)}$ satisfy
$$x^{(k)} - x = G^k (x^{(0)} - x), \qquad G = M^{-1} N,$$
for every $k \ge 0$. -/
theorem equation_11_2_7 {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    (s.mulVecStep b)^[k] x₀ - x = s.iterationOperator ^ k *ᵥ (x₀ - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', mulVecStep_sub s hx, ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- **Equation (11.2.8)** of [golub2013matrix]. Let $\lambda$ and $\alpha$ be elements of a
commutative ring, and let $k \ge 1$. Then
$$\begin{bmatrix} \lambda & \alpha \\ 0 & \lambda \end{bmatrix}^k
  = \begin{bmatrix} \lambda^k & k \alpha \lambda^{k-1} \\ 0 & \lambda^k \end{bmatrix}.$$

**Correction.** The source prints the corner entry as $\alpha \lambda^{k-1}$. This is false for
$k \ge 2$: for $\lambda = \alpha = 1$ and $k = 2$ the corner entry is $2$. The corner entry is
$k \alpha \lambda^{k-1}$. -/
theorem equation_11_2_8 {R : Type*} [CommRing R] (l a : R) {k : ℕ} (hk : 1 ≤ k) :
    !![l, a; 0, l] ^ k = !![l ^ k, (k : R) * a * l ^ (k - 1); 0, l ^ k] := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm 1 j, Nat.add_sub_cancel]
  clear hk
  induction j with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ j ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Theorem 11.2.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular, let
$A = M - N$ be a splitting with $M$ nonsingular, let $b \in \mathbb{R}^n$, and let
$G = M^{-1} N$. The iteration (11.2.6), $M x^{(k)} = N x^{(k-1)} + b$, converges to
$x = A^{-1} b$ for every starting vector $x^{(0)}$ if and only if $\rho(G) < 1$.

The proof reduces both sides, through (11.2.7), to the condition $G^k \to 0$. -/
theorem theorem_11_2_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (s : Stationary.Splitting A)
    (b : Fin n → ℝ) :
    (∀ x₀, Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      s.iterationOperator.complexSpectralRadius < 1 := by
  have hx : A *ᵥ (A⁻¹ *ᵥ b) = b := Matrix.mulVec_nonsing_inv_mulVec hA b
  rw [← Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one,
    Matrix.tendsto_zero_iff_forall_mulVec_tendsto_zero]
  constructor
  · intro H v
    have := tendsto_sub_nhds_zero_iff.2 (H (A⁻¹ *ᵥ b + v))
    simpa only [equation_11_2_7 s hx, add_sub_cancel_left] using this
  · intro H x₀
    rw [← tendsto_sub_nhds_zero_iff]
    simpa only [equation_11_2_7 s hx] using H (x₀ - A⁻¹ *ᵥ b)

open scoped Matrix.Norms.Frobenius in
/-- **Equation (11.2.9)** of [golub2013matrix]. Let $G \in \mathbb{C}^{n \times n}$, and let
$Q^H G Q = T = D + E$ be a Schur decomposition: $Q$ is unitary, $T$ is upper triangular, $D$ is
the diagonal of $T$ and $E$ is its strictly upper triangular part. Let $\rho = \max_i |t_{ii}|$,
which is $\rho(G)$, and suppose that $\rho < 1$. Then for every $k \ge 0$
$$\|G^k\|_2 \le \Bigl(1 + \frac{2 \|E\|_F}{1 - \rho}\Bigr)^{n-1}
  \Bigl(\frac{1 + \rho}{2}\Bigr)^k.$$

**Correction.** The proof of Theorem 11.2.1 in the source takes $\mu = 2\|E\|_2/(1 - \rho)$, so
that the display has $\|E\|_2$ in place of $\|E\|_F$. With the 2-norm, the display does not
follow from the bound (7.3.15), which needs $\|E\|_F$. The statement here uses $\|E\|_F$.

**Typo.** The proof in the source writes $E = A - D$. The strictly upper triangular part is
$E = T - D$.

The number $\rho$ is `⨆ i, ‖T i i‖`, which is $0$ for $n = 0$. The norm $\|E\|_F$ is the
Frobenius norm of `Matrix.strictUpper T`, and the 2-norm is `Matrix.lpOpNorm 2`. The proof
applies (7.3.15), `GolubVanLoan.Chapter07.lemma_7_3_2`, with $\mu = 2\|E\|_F/(1 - \rho)$. -/
theorem equation_11_2_9 {G Q T : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hT : star Q * G * Q = T) (hTu : T.IsUpperTriangular) (hρ : (⨆ i, ‖T i i‖) < 1) (k : ℕ) :
    Matrix.lpOpNorm 2 (G ^ k) ≤
      (1 + 2 * ‖Matrix.strictUpper T‖ / (1 - ⨆ i, ‖T i i‖)) ^ (n - 1) *
        ((1 + ⨆ i, ‖T i i‖) / 2) ^ k := by
  set ρ := ⨆ i, ‖T i i‖ with hρdef
  set e := ‖Matrix.strictUpper T‖
  have hρ0 : 0 ≤ ρ := Real.iSup_nonneg fun _ => norm_nonneg _
  have he : 0 ≤ e := norm_nonneg _
  have h1ρ : 0 < 1 - ρ := by linarith
  have hμ : 0 ≤ 2 * e / (1 - ρ) := by positivity
  refine ((GolubVanLoan.Chapter07.lemma_7_3_2 hQ hT hTu hμ).1 k).trans ?_
  have h1μ : 0 < 1 + 2 * e / (1 - ρ) := by positivity
  have hle : e / (1 + 2 * e / (1 - ρ)) ≤ (1 - ρ) / 2 := by
    rw [div_le_iff₀ h1μ]
    have : (1 - ρ) / 2 * (1 + 2 * e / (1 - ρ)) = (1 - ρ) / 2 + e := by
      field_simp
    linarith
  have hb : 0 ≤ ρ + e / (1 + 2 * e / (1 - ρ)) := by positivity
  have := pow_le_pow_left₀ hb (show ρ + e / (1 + 2 * e / (1 - ρ)) ≤ (1 + ρ) / 2 by linarith) k
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ### Diagonal dominance, positive definiteness -/

/-- **Theorem 11.2.2** of [golub2013matrix]. If $A \in \mathbb{R}^{n \times n}$ is strictly
diagonally dominant, then for every $b \in \mathbb{R}^n$ the Jacobi iteration (11.2.4) converges
to $x = A^{-1} b$: the iterates of the exact Jacobi step (11.2.2) tend to $A^{-1} b$ from every
starting vector $x^{(0)}$.

Strict diagonal dominance is row dominance, $\sum_{j \ne i} |a_{ij}| < |a_{ii}|$ for every $i$
(`Matrix.IsStrictDiagDominant`). -/
theorem theorem_11_2_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsStrictDiagDominant)
    (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (fun x => Id.run (jacobiSweep pure A b x))^[k] x₀) atTop
      (𝓝 (A⁻¹ *ᵥ b)) := by
  have h := hA.isUnit_diagPart
  have hf : (fun x => Id.run (jacobiSweep pure A b x)) =
      (Matrix.jacobiSplitting A h).mulVecStep b :=
    funext fun x => (equation_11_2_4 A h b x).1
  rw [hf]
  exact (theorem_11_2_1 hA.isUnit _ b).2 (Matrix.jacobi_complexSpectralRadius_lt_one hA h) x₀

open scoped Matrix.Norms.Operator in
/-- **Theorem 11.2.2** of [golub2013matrix], the display in the proof. Let
$A \in \mathbb{R}^{n \times n}$ be strictly diagonally dominant with $n \ge 1$, and let
$G_J = M_J^{-1} N_J$ be the iteration matrix of the Jacobi splitting. Then
$$\|G_J\|_\infty = \max_{i} \sum_{j \ne i} \Bigl|\frac{a_{ij}}{a_{ii}}\Bigr| < 1.$$
The source concludes that no eigenvalue of $G_J$ has modulus $1$ or more.

**Typo.** The source writes "no eigenvalue of $A$"; it means $G_J$.

The norm $\|\cdot\|_\infty$ is the operator norm of `Matrix.Norms.Operator`, and the maximum is
`Matrix.jacobiContraction`. -/
theorem jacobi_linfty_opNorm_lt_one [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsStrictDiagDominant) :
    ‖(Matrix.jacobiSplitting A hA.isUnit_diagPart).iterationOperator‖ = A.jacobiContraction ∧
      A.jacobiContraction < 1 :=
  ⟨Matrix.linfty_opNorm_jacobi_iterMatrix A _, hA.jacobiContraction_lt_one⟩

/-- **Theorem 11.2.3** of [golub2013matrix]. If $A \in \mathbb{R}^{n \times n}$ is symmetric
positive definite, then for every $b \in \mathbb{R}^n$ the Gauss–Seidel iteration (11.2.5)
converges to $A^{-1} b$ for any $x^{(0)}$: the iterates of the exact Gauss–Seidel step (11.2.3)
tend to $A^{-1} b$.

Positive definiteness is `Matrix.PosDef`, which includes symmetry. -/
theorem theorem_11_2_3 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (fun x => Id.run (gaussSeidelSweep pure A b x))^[k] x₀) atTop
      (𝓝 (A⁻¹ *ᵥ b)) := by
  have h : IsUnit (Matrix.diagPart A) := (Matrix.isUnit_diagPart_iff A).2 fun i => hA.diag_pos.ne'
  have hf : (fun x => Id.run (gaussSeidelSweep pure A b x)) =
      (Matrix.gaussSeidelSplitting A h).mulVecStep b :=
    funext fun x => (equation_11_2_5 A h b x).1
  rw [hf]
  exact (theorem_11_2_1 hA.isUnit _ b).2
    (Matrix.gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef hA h) x₀

/-! ### The model problem -/

/-- **Equation (11.2.11)** of [golub2013matrix]. The matrix $T_m = \operatorname{tridiag}(-1, 2, -1)
\in \mathbb{R}^{m \times m}$, with $2$ on the diagonal and $-1$ on the two adjacent diagonals. -/
abbrev modelT (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.symmTridiagonalToeplitz m (-1) 2

/-- **Section 11.2.6** of [golub2013matrix], the matrix $E_m = \operatorname{tridiag}(1, 0, 1) \in
\mathbb{R}^{m \times m}$, with $1$ on the two diagonals next to the main diagonal and $0$
elsewhere. It satisfies $T_m = 2I - E_m$. -/
abbrev modelE (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.symmTridiagonalToeplitz m 1 0

/-- **Equation (11.2.10)** of [golub2013matrix]. The model matrix
$$A = I_{n_1} \otimes T_{n_2} + T_{n_1} \otimes I_{n_2},$$
indexed by the pairs $(i, j)$ of interior grid points.

It is the Kronecker sum `Matrix.kroneckerSum` on `Fin n₁ × Fin n₂` of the two matrices $T_{n_1}$
and $T_{n_2}$. The lexicographic order of the pairs is the row-by-row order of the grid in the
source. -/
noncomputable abbrev poissonMatrix (n₁ n₂ : ℕ) : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  Matrix.kroneckerSum (modelT n₁) (modelT n₂)

/-- **Section 11.2.6** of [golub2013matrix]. The model matrix (11.2.10) is symmetric positive
definite.

The proof uses the same Kronecker sum in §4.8.4,
`GolubVanLoan.Chapter04.poisson2D_posDef_bandwidth`, with $n_1$ and $n_2$ exchanged. -/
theorem poissonMatrix_posDef (n₁ n₂ : ℕ) : (poissonMatrix n₁ n₂).PosDef := by
  have h := (Chapter04.poisson2D_posDef_bandwidth n₂ n₁).1
  rw [add_comm] at h
  exact h

/-- $T_m = 2I - E_m$. -/
private theorem modelT_eq (m : ℕ) : modelT m = (2 : ℝ) • 1 + (-1 : ℝ) • modelE m := by
  ext i j
  simp only [modelT, modelE, Matrix.symmTridiagonalToeplitz_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- The diagonal part of the model matrix is $4I$. -/
private theorem diagPart_poissonMatrix (n₁ n₂ : ℕ) :
    Matrix.diagPart (poissonMatrix n₁ n₂) = (4 : ℝ) • 1 := by
  ext p q
  rw [Matrix.diagPart_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs with hpq
  · subst hpq
    obtain ⟨a, c⟩ := p
    rw [show poissonMatrix n₁ n₂ = Matrix.kroneckerSum (modelT n₁) (modelT n₂) from rfl,
      Matrix.kroneckerSum_apply]
    simp only [modelT, Matrix.symmTridiagonalToeplitz_apply_self, ite_true]
    norm_num
  · simp

/-- **Section 11.2.6** of [golub2013matrix]. The diagonal part of the model matrix (11.2.10) is
nonsingular, so the model matrix has a Jacobi splitting. -/
theorem isUnit_diagPart_poissonMatrix (n₁ n₂ : ℕ) :
    IsUnit (Matrix.diagPart (poissonMatrix n₁ n₂)) := by
  rw [Matrix.isUnit_diagPart_iff]
  intro p
  have := congrFun (congrFun (diagPart_poissonMatrix n₁ n₂) p) p
  rw [Matrix.diagPart_apply, ite_eq_left rfl] at this
  rw [this]
  simp

/-- **Equation (11.2.12)** of [golub2013matrix]. The model matrix satisfies
$$A = I_{n_1} \otimes T_{n_2} + T_{n_1} \otimes I_{n_2}
  = 4I - (I_{n_1} \otimes E_{n_2}) - (E_{n_1} \otimes I_{n_2}),$$
and its Jacobi splitting $A = M_J - N_J$ has $M_J = 4I$ and $N_J = (I_{n_1} \otimes E_{n_2}) +
(E_{n_1} \otimes I_{n_2})$. -/
theorem equation_11_2_12 (n₁ n₂ : ℕ) :
    poissonMatrix n₁ n₂ = (4 : ℝ) • 1 - (1 ⊗ₖ modelE n₂) - (modelE n₁ ⊗ₖ 1) ∧
      (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).m = (4 : ℝ) • 1 ∧
      (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).n =
        (1 ⊗ₖ modelE n₂) + (modelE n₁ ⊗ₖ 1) := by
  have hA : poissonMatrix n₁ n₂ = (4 : ℝ) • 1 - (1 ⊗ₖ modelE n₂) - (modelE n₁ ⊗ₖ 1) := by
    rw [poissonMatrix, Matrix.kroneckerSum_def, modelT_eq, modelT_eq, Matrix.add_kronecker,
      Matrix.kronecker_add, Matrix.smul_kronecker, Matrix.smul_kronecker, Matrix.kronecker_smul,
      Matrix.kronecker_smul, Matrix.one_kronecker_one]
    module
  have hm : (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).m = (4 : ℝ) • 1 :=
    diagPart_poissonMatrix n₁ n₂
  refine ⟨hA, hm, ?_⟩
  rw [Stationary.Splitting.n, hm, hA]
  abel

/-! ### The model problem as an array averaging -/

section Grid

variable {n₁ n₂ : ℕ}

/-- The position of an interior unknown in the array $U(0{:}n_1 + 1, 0{:}n_2 + 1)$ of §11.2.6 of
[golub2013matrix]: the 0-based unknown $(i, j)$ is at the array index $(i + 1, j + 1)$, the
1-based interior index of the source. -/
def gridPoint (p : Fin n₁ × Fin n₂) : Fin (n₁ + 2) × Fin (n₂ + 2) :=
  (⟨p.1 + 1, by omega⟩, ⟨p.2 + 1, by omega⟩)

/-- Distinct unknowns are at distinct positions of the array. -/
private theorem gridPoint_injective : Function.Injective (gridPoint (n₁ := n₁) (n₂ := n₂)) := by
  intro p q h
  simp only [gridPoint, Prod.mk.injEq, Fin.mk.injEq, add_left_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The sum of the four grid neighbours of the interior unknown at the array position $(i, j)$ in
the array $U$, in the order of the source,
$$U(i-1, j) + U(i, j+1) + U(i+1, j) + U(i, j-1).$$
-/
def gridNeighbourSum (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) : ℝ :=
  U (⟨p.1, by omega⟩, ⟨p.2 + 1, by omega⟩) + U (⟨p.1 + 1, by omega⟩, ⟨p.2 + 2, by omega⟩) +
    U (⟨p.1 + 2, by omega⟩, ⟨p.2 + 1, by omega⟩) + U (⟨p.1 + 1, by omega⟩, ⟨p.2, by omega⟩)

/-- A position $(i, j)$ of the array is **interior** if $1 \le i \le n_1$ and $1 \le j \le n_2$. -/
def IsGridInterior (q : Fin (n₁ + 2) × Fin (n₂ + 2)) : Prop :=
  1 ≤ (q.1 : ℕ) ∧ (q.1 : ℕ) ≤ n₁ ∧ 1 ≤ (q.2 : ℕ) ∧ (q.2 : ℕ) ≤ n₂

/-- Interiority of a grid point is decidable. -/
instance (q : Fin (n₁ + 2) × Fin (n₂ + 2)) : Decidable (IsGridInterior q) := by
  unfold IsGridInterior; infer_instance

/-- The vector $u$ of (11.2.10) of [golub2013matrix]: the interior values $U(1{:}n_1, 1{:}n_2)$ of
an array $U$. -/
def gridInterior (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) : ℝ :=
  U (gridPoint p)

/-- The array that holds a vector $u$ of interior values at the interior positions and $0$ at the
boundary positions. -/
def gridPad (u : Fin n₁ × Fin n₂ → ℝ) (q : Fin (n₁ + 2) × Fin (n₂ + 2)) : ℝ :=
  if h : IsGridInterior q then
    u (⟨q.1 - 1, by simp only [IsGridInterior] at h; omega⟩,
      ⟨q.2 - 1, by simp only [IsGridInterior] at h; omega⟩)
  else 0

/-- The boundary values of an array $U$: the array that equals $U$ at the boundary positions and $0$
at the interior positions. -/
def gridBoundary (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (q : Fin (n₁ + 2) × Fin (n₂ + 2)) : ℝ :=
  if IsGridInterior q then 0 else U q

/-- The right-hand side $b$ of (11.2.10) of [golub2013matrix] in the Laplace case: at each interior
unknown, the sum of the values of $U$ at those of its four neighbours that are boundary
positions. -/
def gridRhs (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) : ℝ :=
  gridNeighbourSum (gridBoundary U) p

/-- An array is the sum of the array of its interior values and the array of its boundary values. -/
private theorem gridPad_gridInterior_add_gridBoundary (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (q) :
    gridPad (gridInterior U) q + gridBoundary U q = U q := by
  unfold gridPad gridBoundary
  split_ifs with h
  · rw [add_zero, gridInterior]
    simp only [IsGridInterior] at h
    congr 1
    simp only [gridPoint]
    ext <;> simp <;> omega
  · rw [zero_add]

/-- The neighbour sum is additive in the array. -/
private theorem gridNeighbourSum_add (U V : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p) :
    gridNeighbourSum (fun q => U q + V q) p = gridNeighbourSum U p + gridNeighbourSum V p := by
  unfold gridNeighbourSum; ring

/-- The neighbour sum of an array is the neighbour sum of the array of its interior values plus the
right-hand side `GolubVanLoan.Chapter11.gridRhs`. -/
private theorem gridNeighbourSum_eq (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) :
    gridNeighbourSum U p = gridNeighbourSum (gridPad (gridInterior U)) p + gridRhs U p := by
  rw [gridRhs, ← gridNeighbourSum_add]
  simp only [gridPad_gridInterior_add_gridBoundary]

/-- Row $i$ of $T_m v$ is $2v_i - v_{i-1} - v_{i+1}$, where the missing neighbours of the first and
the last row count as zero. -/
private theorem modelT_mulVec_apply {m : ℕ} (v : Fin m → ℝ) (i : Fin m) :
    (modelT m *ᵥ v) i = 2 * v i - (if h : 0 < (i : ℕ) then v ⟨i - 1, by omega⟩ else 0) -
      (if h : (i : ℕ) + 1 < m then v ⟨i + 1, h⟩ else 0) := by
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by have := i.isLt; omega⟩
  rw [modelT, Matrix.symmTridiagonalToeplitz_mulVec_apply']
  have e : ((i : ℕ) + 1 < N + 1) ↔ (i : ℕ) < N := by omega
  by_cases h1 : 0 < (i : ℕ) <;> by_cases h2 : (i : ℕ) < N <;>
    simp only [h1, h2, e, dite_true, dite_false] <;> ring

private theorem gridPad_north (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    gridPad u (⟨p.1, by omega⟩, ⟨p.2 + 1, by omega⟩) =
      if h : 0 < (p.1 : ℕ) then u (⟨p.1 - 1, by omega⟩, p.2) else 0 := by
  unfold gridPad
  by_cases h : 0 < (p.1 : ℕ)
  · rw [dite_eq_left_of_eq_true (eq_true (by simp only [IsGridInterior]; omega)),
      dite_eq_left_of_eq_true (eq_true h)]
    congr 1
  · rw [dite_eq_right_of_eq_false (eq_false (by simp only [IsGridInterior]; omega)),
      dite_eq_right_of_eq_false (eq_false h)]

private theorem gridPad_south (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    gridPad u (⟨p.1 + 2, by omega⟩, ⟨p.2 + 1, by omega⟩) =
      if h : (p.1 : ℕ) + 1 < n₁ then u (⟨p.1 + 1, h⟩, p.2) else 0 := by
  unfold gridPad
  by_cases h : (p.1 : ℕ) + 1 < n₁
  · rw [dite_eq_left_of_eq_true (eq_true (by simp only [IsGridInterior]; omega)),
      dite_eq_left_of_eq_true (eq_true h)]
    congr 1
  · rw [dite_eq_right_of_eq_false (eq_false (by simp only [IsGridInterior]; omega)),
      dite_eq_right_of_eq_false (eq_false h)]

private theorem gridPad_west (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    gridPad u (⟨p.1 + 1, by omega⟩, ⟨p.2, by omega⟩) =
      if h : 0 < (p.2 : ℕ) then u (p.1, ⟨p.2 - 1, by omega⟩) else 0 := by
  unfold gridPad
  by_cases h : 0 < (p.2 : ℕ)
  · rw [dite_eq_left_of_eq_true (eq_true (by simp only [IsGridInterior]; omega)),
      dite_eq_left_of_eq_true (eq_true h)]
    congr 1
  · rw [dite_eq_right_of_eq_false (eq_false (by simp only [IsGridInterior]; omega)),
      dite_eq_right_of_eq_false (eq_false h)]

private theorem gridPad_east (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    gridPad u (⟨p.1 + 1, by omega⟩, ⟨p.2 + 2, by omega⟩) =
      if h : (p.2 : ℕ) + 1 < n₂ then u (p.1, ⟨p.2 + 1, h⟩) else 0 := by
  unfold gridPad
  by_cases h : (p.2 : ℕ) + 1 < n₂
  · rw [dite_eq_left_of_eq_true (eq_true (by simp only [IsGridInterior]; omega)),
      dite_eq_left_of_eq_true (eq_true h)]
    congr 1
  · rw [dite_eq_right_of_eq_false (eq_false (by simp only [IsGridInterior]; omega)),
      dite_eq_right_of_eq_false (eq_false h)]

/-- **Section 11.2.6** of [golub2013matrix]: the model matrix is the five-point stencil. For every
vector $u$ of interior values and every interior unknown $(i, j)$,
$$(Au)_{ij} = 4u_{ij} - u_{i-1,j} - u_{i,j+1} - u_{i+1,j} - u_{i,j-1},$$
where $u_{kl} = 0$ when $(k, l)$ is not an interior unknown.

The neighbour sum is `GolubVanLoan.Chapter11.gridNeighbourSum` of the array
`GolubVanLoan.Chapter11.gridPad u`. -/
theorem poissonMatrix_mulVec_apply (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    (poissonMatrix n₁ n₂ *ᵥ u) p = 4 * u p - gridNeighbourSum (gridPad u) p := by
  have hsum : (poissonMatrix n₁ n₂ *ᵥ u) p =
      (modelT n₁ *ᵥ fun a => u (a, p.2)) p.1 + (modelT n₂ *ᵥ fun c => u (p.1, c)) p.2 := by
    obtain ⟨i, j⟩ := p
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, poissonMatrix,
      Matrix.kroneckerSum_apply, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_ite_eq]; simp
    · rw [Finset.sum_eq_single i (fun a _ ha => Finset.sum_eq_zero fun c _ => by
        simp [Ne.symm ha]) (by simp)]
      simp
  rw [hsum, modelT_mulVec_apply, modelT_mulVec_apply, gridNeighbourSum, gridPad_north,
    gridPad_south, gridPad_west, gridPad_east]
  ring

/-- The diagonal entries of the model matrix are $4$. -/
private theorem poissonMatrix_apply_self (p : Fin n₁ × Fin n₂) : poissonMatrix n₁ n₂ p p = 4 := by
  obtain ⟨i, j⟩ := p
  rw [poissonMatrix, Matrix.kroneckerSum_apply]
  simp only [modelT, Matrix.symmTridiagonalToeplitz_apply_self, ite_true]
  norm_num

/-- The interior unknowns in the order of the double loop $i = 1{:}n_1$, $j = 1{:}n_2$ of the
source. -/
private def gridList (n₁ n₂ : ℕ) : List (Fin n₁ × Fin n₂) :=
  (List.finRange n₁).flatMap fun i => (List.finRange n₂).map (Prod.mk i)

private theorem mem_gridList (p : Fin n₁ × Fin n₂) : p ∈ gridList n₁ n₂ := by
  simp [gridList]

/-- The double loop visits the unknowns in lexicographic order. -/
private theorem pairwise_gridList :
    (gridList n₁ n₂).Pairwise fun p q => toLex p < toLex q := by
  rw [gridList, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_finRange n₂).imp fun {a b} h => ?_
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, h⟩)
  · refine (List.pairwise_lt_finRange n₁).imp fun h x hx y hy => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

/-- The double loop of the source is one loop over the list of the unknowns in loop order. -/
private theorem foldl_foldl_eq_foldl_gridList {σ : Type*} (F : Fin n₁ × Fin n₂ → σ → σ) (s : σ) :
    (List.finRange n₁).foldl (fun s i => (List.finRange n₂).foldl (fun s j => F (i, j) s) s) s =
      (gridList n₁ n₂).foldl (fun s p => F p s) s := by
  rw [gridList, List.foldl_flatMap]
  simp only [List.foldl_map]

/-- The position of an interior unknown in the array is interior. -/
private theorem isGridInterior_gridPoint (p : Fin n₁ × Fin n₂) :
    IsGridInterior (gridPoint p) := by
  simp only [IsGridInterior, gridPoint]; omega

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The average $\bigl(W(i-1, j) + W(i, j+1) + W(i+1, j) + W(i, j-1)\bigr)/4$ of the four grid
neighbours of an interior unknown in the array $W$, summed in the order of the source, with
every operation rounded.

**Reading.** Same stencil with explicit addition order and rounding.
-/
noncomputable def gridAverage (W : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) :
    M ℝ := do
  let s₁ ← rnd (W (⟨p.1, by omega⟩, ⟨p.2 + 1, by omega⟩) +
    W (⟨p.1 + 1, by omega⟩, ⟨p.2 + 2, by omega⟩))
  let s₂ ← rnd (s₁ + W (⟨p.1 + 2, by omega⟩, ⟨p.2 + 1, by omega⟩))
  let s₃ ← rnd (s₂ + W (⟨p.1 + 1, by omega⟩, ⟨p.2, by omega⟩))
  rnd (s₃ / 4)

/-- **Section 11.2.6** of [golub2013matrix], the array form of Jacobi. On the array
$U(0{:}n_1 + 1, 0{:}n_2 + 1)$, the program sets $V = U$ and then computes, for $i = 1{:}n_1$ and
$j = 1{:}n_2$,
$$U(i, j) = \bigl(V(i-1, j) + V(i, j+1) + V(i+1, j) + V(i, j-1)\bigr)/4.$$
Every average reads the copy $V$ of the old array.

The array is a function on pairs of indices. Each average is
`GolubVanLoan.Chapter11.gridAverage`.

**Reading.** Reads old copy, updates interior, with monadic rounding.
-/
noncomputable def poissonJacobiArray (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    M (Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :=
  let V := U
  (List.finRange n₁).foldlM (fun U i => (List.finRange n₂).foldlM (fun U j => do
    let u ← gridAverage rnd V (i, j)
    pure (Function.update U (gridPoint (i, j)) u)) U) U

/-- **Section 11.2.6** of [golub2013matrix], the array form of Gauss–Seidel. On the array
$U(0{:}n_1 + 1, 0{:}n_2 + 1)$, the program computes in place, for $i = 1{:}n_1$ and
$j = 1{:}n_2$,
$$U(i, j) = \bigl(U(i-1, j) + U(i, j+1) + U(i+1, j) + U(i, j-1)\bigr)/4,$$
so that $U(i-1, j)$ and $U(i, j-1)$ already hold the new values.

**Reading.** Uses current values in lexicographic order, with monadic rounding.
-/
noncomputable def poissonGaussSeidelArray (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    M (Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :=
  (List.finRange n₁).foldlM (fun U i => (List.finRange n₂).foldlM (fun U j => do
    let u ← gridAverage rnd U (i, j)
    pure (Function.update U (gridPoint (i, j)) u)) U) U

end Programs

private theorem poissonJacobiArray_run (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    Id.run (poissonJacobiArray pure U) = (gridList n₁ n₂).foldl
      (fun W p => Function.update W (gridPoint p) (gridNeighbourSum U p / 4)) U := by
  rw [← foldl_foldl_eq_foldl_gridList]
  simp only [poissonJacobiArray, List.idRun_foldlM]
  rfl

private theorem poissonGaussSeidelArray_run (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    Id.run (poissonGaussSeidelArray pure U) = (gridList n₁ n₂).foldl
      (fun W p => Function.update W (gridPoint p) (gridNeighbourSum W p / 4)) U := by
  rw [← foldl_foldl_eq_foldl_gridList]
  simp only [poissonGaussSeidelArray, List.idRun_foldlM]
  rfl

/-- The array loops leave the boundary values of the array unchanged. -/
private theorem foldl_grid_boundary
    (F : Fin n₁ × Fin n₂ → (Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) → ℝ)
    (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) {q : Fin (n₁ + 2) × Fin (n₂ + 2)}
    (hq : ¬ IsGridInterior q) :
    (gridList n₁ n₂).foldl (fun W p => Function.update W (gridPoint p) (F p W)) U q = U q :=
  List.foldl_update_apply_of_forall_ne gridPoint F (k := q) (fun p _ h =>
    hq (h ▸ isGridInterior_gridPoint p)) U

/-- Row $p$ of the off-diagonal part of the model matrix, applied to $u$, is minus the neighbour sum
of the array of $u$. -/
private theorem sum_erase_poissonMatrix (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    ∑ q ∈ univ.erase p, poissonMatrix n₁ n₂ p q * u q = -gridNeighbourSum (gridPad u) p := by
  have h := Finset.sum_erase_add univ (fun q => poissonMatrix n₁ n₂ p q * u q) (mem_univ p)
  have h' := poissonMatrix_mulVec_apply u p
  rw [Matrix.mulVec, dotProduct] at h'
  rw [poissonMatrix_apply_self] at h
  linarith

/-- **Section 11.2.6** of [golub2013matrix]: the array update is Jacobi. Let $U$ be an array on the
grid $0{:}n_1 + 1$ by $0{:}n_2 + 1$, let $u = U(1{:}n_1, 1{:}n_2)$ be its interior values, and
let $b$ hold, at each interior unknown, the sum of the values of $U$ at its neighbours on the
boundary. Then one exact pass of the array form of Jacobi gives the interior values
$$M_J^{-1}(N_J u + b),$$
which is one Jacobi step (11.2.4) for the model system $Au = b$ of (11.2.10), and it leaves the
boundary values of the array unchanged.

This $b$ is the Laplace case of the model problem: fixed boundary values and no source term. It
is `GolubVanLoan.Chapter11.gridRhs U`, and $u$ is `GolubVanLoan.Chapter11.gridInterior U`. -/
theorem poissonJacobiArray_eq (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    gridInterior (Id.run (poissonJacobiArray pure U)) =
        (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).mulVecStep (gridRhs U)
          (gridInterior U) ∧
      ∀ q, ¬ IsGridInterior q → Id.run (poissonJacobiArray pure U) q = U q := by
  rw [poissonJacobiArray_run]
  refine ⟨?_, fun q hq => foldl_grid_boundary _ U hq⟩
  rw [← Matrix.jorSweep_one_eq_mulVecStep]
  funext p
  obtain ⟨w, -, -, hw⟩ := List.exists_foldl_update_apply_of_pairwise_rel gridPoint
    (fun p q => toLex p < toLex q) (fun _ _ h h' => lt_asymm h h')
    (fun p _ => gridNeighbourSum U p / 4) gridPoint_injective.injOn pairwise_gridList U
    (mem_gridList p)
  rw [gridInterior, hw, Matrix.jorSweep, sum_erase_poissonMatrix, poissonMatrix_apply_self,
    gridNeighbourSum_eq]
  ring

/-- The model matrix (11.2.10) of [golub2013matrix] with its unknowns in the row-by-row order of the
source, which is the lexicographic order of the pairs $(i, j)$. The Gauss–Seidel splitting of
the model problem is taken for this matrix.

It is `GolubVanLoan.Chapter11.poissonMatrix` reindexed by `ofLex`. The order on
`Lex (Fin n₁ × Fin n₂)` decides which entries are strictly lower triangular. -/
noncomputable abbrev poissonMatrixLex (n₁ n₂ : ℕ) :
    Matrix (Lex (Fin n₁ × Fin n₂)) (Lex (Fin n₁ × Fin n₂)) ℝ :=
  (poissonMatrix n₁ n₂).submatrix ofLex ofLex

/-- The diagonal part of the reordered model matrix `GolubVanLoan.Chapter11.poissonMatrixLex` is
nonsingular. -/
theorem isUnit_diagPart_poissonMatrixLex (n₁ n₂ : ℕ) :
    IsUnit (Matrix.diagPart (poissonMatrixLex n₁ n₂)) := by
  rw [Matrix.isUnit_diagPart_iff]
  intro p
  change poissonMatrix n₁ n₂ (ofLex p) (ofLex p) ≠ 0
  rw [poissonMatrix_apply_self]
  norm_num

/-- Row $p$ of the reordered model matrix, without its diagonal entry, is minus the neighbour sum.
-/
private theorem sum_lt_add_sum_gt_poissonMatrixLex (u : Lex (Fin n₁ × Fin n₂) → ℝ)
    (p : Lex (Fin n₁ × Fin n₂)) :
    ∑ q ∈ univ.filter (· < p), poissonMatrixLex n₁ n₂ p q * u q +
        ∑ q ∈ univ.filter (p < ·), poissonMatrixLex n₁ n₂ p q * u q =
      -gridNeighbourSum (gridPad fun r => u (toLex r)) (ofLex p) := by
  rw [← sum_erase_poissonMatrix]
  rw [← Finset.sum_union (Finset.disjoint_filter.2 fun q _ h1 h2 => lt_asymm h1 h2),
    ← Finset.filter_or]
  refine Finset.sum_nbij' ofLex toLex (fun q hq => ?_) (fun q hq => ?_) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun q _ => rfl)
  · simp only [Finset.mem_filter, mem_univ, true_and] at hq
    refine Finset.mem_erase.2 ⟨fun h => ?_, mem_univ _⟩
    have hpq : q = p := h
    rcases hq with h' | h' <;> exact lt_irrefl p (hpq ▸ h')
  · have hq' := (Finset.mem_erase.1 hq).1
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact lt_or_gt_of_ne fun h => hq' (congrArg ofLex h)

/-- **Section 11.2.6** of [golub2013matrix]: the in-place array update is Gauss–Seidel. Let $U$, $u$
and $b$ be as in `GolubVanLoan.Chapter11.poissonJacobiArray_eq`. Then one exact pass of the
array form of Gauss–Seidel gives the interior values
$$M_{GS}^{-1}(N_{GS} u + b),$$
which is one Gauss–Seidel step (11.2.5) for the model system with the unknowns in the row-by-row
order of the source, and it leaves the boundary values of the array unchanged.

The row-by-row order is the lexicographic order of the pairs. The loop visits the unknowns in
this order, and the neighbours $(i-1, j)$ and $(i, j-1)$ come before $(i, j)$. The splitting is
the Gauss–Seidel splitting of `GolubVanLoan.Chapter11.poissonMatrixLex`, and the vectors are
reindexed by `ofLex`. -/
theorem poissonGaussSeidelArray_eq (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    (fun q => gridInterior (Id.run (poissonGaussSeidelArray pure U)) (ofLex q)) =
        (Matrix.gaussSeidelSplitting _ (isUnit_diagPart_poissonMatrixLex n₁ n₂)).mulVecStep
          (fun q => gridRhs U (ofLex q)) (fun q => gridInterior U (ofLex q)) ∧
      ∀ q, ¬ IsGridInterior q → Id.run (poissonGaussSeidelArray pure U) q = U q := by
  rw [poissonGaussSeidelArray_run]
  refine ⟨?_, fun q hq => foldl_grid_boundary _ U hq⟩
  rw [← Matrix.sorSweep_one_eq_mulVecStep]
  set Z := (gridList n₁ n₂).foldl
    (fun W p => Function.update W (gridPoint p) (gridNeighbourSum W p / 4)) U
  set A' := poissonMatrixLex n₁ n₂
  set b' : Lex (Fin n₁ × Fin n₂) → ℝ := fun q => gridRhs U (ofLex q)
  set x' : Lex (Fin n₁ × Fin n₂) → ℝ := fun q => gridInterior U (ofLex q)
  refine eq_of_forall_eq_apply (· < ·) wellFounded_lt
    (fun q u => 1 / A' q q * (b' q - ∑ j ∈ univ.filter (· < q), A' q j * u j
      - ∑ j ∈ univ.filter (q < ·), A' q j * x' j) + (1 - 1) * x' q) ?_ (fun q => ?_)
    (fun q => Matrix.sorSweep_apply A' (isUnit_diagPart_poissonMatrixLex n₁ n₂) 1 b' x' q)
  · intro q u v huv
    rw [Finset.sum_congr rfl fun j hj => by rw [huv j (Finset.mem_filter.1 hj).2]]
  · obtain ⟨w, hw₁, hw₂, hw₃⟩ := List.exists_foldl_update_apply_of_pairwise_rel gridPoint
      (fun p q => toLex p < toLex q) (fun _ _ h h' => lt_asymm h h')
      (fun p W => gridNeighbourSum W p / 4) gridPoint_injective.injOn pairwise_gridList U
      (mem_gridList (ofLex q))
    set u'' : Fin n₁ × Fin n₂ → ℝ := fun r =>
      if toLex r < q then Z (gridPoint r) else U (gridPoint r) with hu''
    have hint : gridInterior w = u'' := by
      funext r
      simp only [gridInterior, hu'']
      split_ifs with hr
      · exact hw₁ r (mem_gridList r) hr
      · refine hw₂ _ fun r' _ hr' h => hr ?_
        rw [← gridPoint_injective h]
        exact hr'
    have hbd : gridBoundary w = gridBoundary U := by
      funext k
      unfold gridBoundary
      split_ifs with hk
      · rfl
      · exact hw₂ k fun r _ _ h => hk (h ▸ isGridInterior_gridPoint r)
    have hsplit := sum_lt_add_sum_gt_poissonMatrixLex (fun j => u'' (ofLex j)) q
    have hlt : ∑ j ∈ univ.filter (· < q), A' q j * gridInterior Z (ofLex j) =
        ∑ j ∈ univ.filter (· < q), A' q j * u'' (ofLex j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : toLex (ofLex j) < q := (Finset.mem_filter.1 hj).2
      simp only [hu'', gridInterior, hj', ite_true]
    have hgt : ∑ j ∈ univ.filter (q < ·), A' q j * x' j =
        ∑ j ∈ univ.filter (q < ·), A' q j * u'' (ofLex j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : ¬ toLex (ofLex j) < q := fun h =>
        lt_asymm h (Finset.mem_filter.1 hj).2
      simp only [x', hu'', gridInterior, hj', ite_false]
    have hq : A' q q = 4 := poissonMatrix_apply_self (ofLex q)
    rw [show gridInterior Z (ofLex q) = gridNeighbourSum w (ofLex q) / 4 from hw₃, hlt, hgt, hq,
      gridNeighbourSum_eq, hint, gridRhs, hbd]
    simp only [b', gridRhs]
    have hpad : (gridPad fun r => u'' (ofLex (toLex r))) = gridPad u'' := rfl
    rw [hpad] at hsplit
    linarith

end Grid

/-- **Equation (11.2.14)** of [golub2013matrix]. The eigenvalues of $E_m$,
$$\mu_k^{(m)} = 2 \cos\Bigl(\frac{k \pi}{m + 1}\Bigr), \qquad k = 1{:}m.$$

The index is 0-based: entry $k$ is $2 \cos((k + 1)\pi/(m + 1))$, the source's $\mu_{k+1}^{(m)}$. -/
noncomputable def modelEEigenvalues (m : ℕ) : Fin m → ℝ :=
  fun k => 2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1))

/-- The sine transform matrix $S_m$ is nonsingular (§4.8.6, `GolubVanLoan.Chapter04.dd_eigen`). -/
private theorem isUnit_dst1 (m : ℕ) : IsUnit (Matrix.dst1 m) :=
  (GolubVanLoan.Chapter04.dd_eigen m).2.1

/-- $E_m S_m = S_m D_m$: the columns of $S_m$ are eigenvectors of $E_m$. -/
private theorem modelE_mul_dst1 (m : ℕ) :
    modelE m * Matrix.dst1 m = Matrix.dst1 m * Matrix.diagonal (modelEEigenvalues m) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have := congrFun (Matrix.symmTridiagonalToeplitz_mulVec_sineVec (a := 1) (b := 0) j) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.dst1_apply_eq_sineVec, modelEEigenvalues]
  rw [this]
  ring

/-- **Equation (11.2.13)** of [golub2013matrix]. Let $S_m \in \mathbb{R}^{m \times m}$ be the sine
transform matrix, $[S_m]_{kj} = \sin(kj\pi/(m + 1))$. Then
$$S_m^{-1} E_m S_m = D_m = \operatorname{diag}(\mu_1^{(m)}, \dots, \mu_m^{(m)}).$$

The matrix $S_m$ is `Matrix.dst1 m`. The source leaves the proof to Problem P11.2.7. -/
theorem equation_11_2_13 (m : ℕ) :
    (Matrix.dst1 m)⁻¹ * modelE m * Matrix.dst1 m = Matrix.diagonal (modelEEigenvalues m) := by
  have hS := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 m)
  rw [Matrix.mul_assoc, modelE_mul_dst1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hS,
    Matrix.one_mul]

/-- Conjugation of a Kronecker product by a Kronecker product: $(S_1 \otimes S_2)^{-1}(X_1 \otimes
X_2)(S_1 \otimes S_2) = (S_1^{-1} X_1 S_1) \otimes (S_2^{-1} X_2 S_2)$. -/
private theorem kronecker_conj {m₁ m₂ : ℕ} (S₁ X₁ : Matrix (Fin m₁) (Fin m₁) ℝ)
    (S₂ X₂ : Matrix (Fin m₂) (Fin m₂) ℝ) :
    (S₁ ⊗ₖ S₂)⁻¹ * (X₁ ⊗ₖ X₂) * (S₁ ⊗ₖ S₂) = (S₁⁻¹ * X₁ * S₁) ⊗ₖ (S₂⁻¹ * X₂ * S₂) := by
  rw [Matrix.inv_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- The sine basis diagonalizes $I \otimes E_{n_2}$: conjugation gives $I \otimes D_{n_2}$. -/
private theorem conj_one_kronecker_modelE (n₁ n₂ : ℕ) :
    (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ * (1 ⊗ₖ modelE n₂) * (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
      1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂) := by
  rw [kronecker_conj, equation_11_2_13, Matrix.mul_one,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 n₁))]

/-- The sine basis diagonalizes $E_{n_1} \otimes I$: conjugation gives $D_{n_1} \otimes I$. -/
private theorem conj_modelE_kronecker_one (n₁ n₂ : ℕ) :
    (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ * (modelE n₁ ⊗ₖ 1) * (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
      Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1 := by
  rw [kronecker_conj, equation_11_2_13, Matrix.mul_one,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 n₂))]

/-- $(4I)^{-1} = \frac{1}{4} I$. -/
private theorem inv_four_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ((4 : ℝ) • (1 : Matrix ι ι ℝ))⁻¹ = (1 / 4 : ℝ) • 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, Matrix.one_mul]
  norm_num

/-- The Jacobi iteration matrix of the model problem is $\frac{1}{4}\bigl((I \otimes E_{n_2}) +
(E_{n_1} \otimes I)\bigr)$. -/
private theorem jacobi_poisson_iterationOperator (n₁ n₂ : ℕ) :
    (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).iterationOperator =
      (1 / 4 : ℝ) • ((1 ⊗ₖ modelE n₂) + (modelE n₁ ⊗ₖ 1)) := by
  obtain ⟨-, hm, hn⟩ := equation_11_2_12 n₁ n₂
  rw [Stationary.Splitting.iterationOperator_eq, hm, hn, ← Matrix.nonsing_inv_eq_ringInverse,
    inv_four_smul_one, Matrix.smul_mul, Matrix.one_mul]

/-- **Section 11.2.6** of [golub2013matrix], the display after (11.2.14). Let
$S = S_{n_1} \otimes S_{n_2}$. Then the Jacobi iteration matrix of the model problem satisfies
$$S^{-1} (M_J^{-1} N_J) S
  = \frac{1}{4}\bigl(I_{n_1} \otimes D_{n_2} + D_{n_1} \otimes I_{n_2}\bigr).$$
-/
theorem jacobi_poisson_diagonal (n₁ n₂ : ℕ) :
    (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ *
        (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).iterationOperator *
        (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
      (1 / 4 : ℝ) • (1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂) +
        Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1) := by
  rw [jacobi_poisson_iterationOperator, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, conj_one_kronecker_modelE, conj_modelE_kronecker_one]

/-- The sine basis $S_{n_1} \otimes S_{n_2}$ of the grid is nonsingular. -/
private theorem isUnit_dst1_kronecker (n₁ n₂ : ℕ) :
    IsUnit (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) :=
  Matrix.IsUnit.kronecker (isUnit_dst1 n₁) (isUnit_dst1 n₂)

/-- If $|d_i| \le r$ for all $i$, with equality at some $i_0$, then the spectral radius of
$\operatorname{diag}(d)$ is $r$. -/
private theorem complexSpectralRadius_diagonal_eq_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) {r : ℝ} (hle : ∀ i, |d i| ≤ r) {i₀ : ι} (h₀ : |d i₀| = r) :
    (Matrix.diagonal d).complexSpectralRadius = ENNReal.ofReal r := by
  rw [Matrix.complexSpectralRadius_diagonal]
  have e : ∀ x : ℝ, ((‖x‖₊ : NNReal) : ENNReal) = ENNReal.ofReal |x| := fun x => by
    rw [← enorm_eq_nnnorm]; exact Real.enorm_eq_ofReal_abs x
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le i₀ ?_)
  · rw [e]; exact ENNReal.ofReal_le_ofReal (hle i)
  · rw [e, h₀]

/-- $|\cos(k\pi/(m + 1))| \le \cos(\pi/(m + 1))$ for $k = 1{:}m$. -/
private theorem abs_cos_le (m : ℕ) (k : Fin m) :
    |Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1))| ≤
      Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hk : ((k : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast k.isLt
  set θ := Real.pi / ((m : ℝ) + 1)
  have hθ0 : 0 ≤ θ := by positivity
  have ht : (((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1) = (((k : ℕ) : ℝ) + 1) * θ := by
    rw [mul_div_assoc]
  rw [ht]
  have h1 : θ ≤ (((k : ℕ) : ℝ) + 1) * θ := le_mul_of_one_le_left hθ0 (by linarith)
  have h2 : (((k : ℕ) : ℝ) + 1) * θ ≤ Real.pi - θ := by
    have : (((k : ℕ) : ℝ) + 1) * θ + θ = (((k : ℕ) : ℝ) + 2) * θ := by ring
    have h3 : (((k : ℕ) : ℝ) + 2) * θ ≤ Real.pi := by
      rw [show θ = Real.pi / ((m : ℝ) + 1) from rfl, ← mul_div_assoc, div_le_iff₀ hm]
      nlinarith [Real.pi_pos]
    linarith
  have hθπ : θ ≤ Real.pi := by
    rw [show θ = Real.pi / ((m : ℝ) + 1) from rfl, div_le_iff₀ hm]
    nlinarith [Real.pi_pos]
  rw [abs_le]
  constructor
  · rw [neg_le, ← Real.cos_pi_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith) (by linarith)
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith) h1

/-- $\cos(\pi/(m + 1)) \ge 0$ for $m \ge 1$. -/
private theorem cos_pi_div_nonneg (m : ℕ) [NeZero m] : 0 ≤ Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · have : 0 ≤ Real.pi / ((m : ℝ) + 1) := by positivity
    linarith [Real.pi_pos]
  · exact div_le_div_of_nonneg_left Real.pi_pos.le two_pos (by linarith)

/-- $\cos(\pi/(m + 1)) < 1$. -/
private theorem cos_pi_div_lt_one (m : ℕ) : Real.cos (Real.pi / ((m : ℝ) + 1)) < 1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
    (div_le_self Real.pi_pos.le (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]))
    (by positivity : (0 : ℝ) < Real.pi / ((m : ℝ) + 1))
  rwa [Real.cos_zero] at h

/-- **Equation (11.2.15)** of [golub2013matrix]. For the model problem with $n_1, n_2 \ge 1$, the
Jacobi iteration matrix has the spectral radius
$$\rho(M_J^{-1} N_J) = \frac{2\cos(\pi/(n_1 + 1)) + 2\cos(\pi/(n_2 + 1))}{4}.$$

The source leaves the proof to Problem P11.2.8. The right side is embedded in $[0, \infty]$ by
`ENNReal.ofReal`. -/
theorem equation_11_2_15 (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    Matrix.complexSpectralRadius
        (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).iterationOperator =
      ENNReal.ofReal ((2 * Real.cos (Real.pi / ((n₁ : ℝ) + 1)) +
        2 * Real.cos (Real.pi / ((n₂ : ℝ) + 1))) / 4) := by
  rw [← Matrix.complexSpectralRadius_conj (isUnit_dst1_kronecker n₁ n₂), jacobi_poisson_diagonal]
  have hd : (1 / 4 : ℝ) • (1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂) +
      Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1) =
      Matrix.diagonal fun p : Fin n₁ × Fin n₂ =>
        (modelEEigenvalues n₁ p.1 + modelEEigenvalues n₂ p.2) / 4 := by
    have h₁ : (1 : Matrix (Fin n₁) (Fin n₁) ℝ) = Matrix.diagonal fun _ => 1 :=
      Matrix.diagonal_one.symm
    have h₂ : (1 : Matrix (Fin n₂) (Fin n₂) ℝ) = Matrix.diagonal fun _ => 1 :=
      Matrix.diagonal_one.symm
    rw [h₁, h₂, Matrix.diagonal_kronecker_diagonal,
      Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_smul]
    congr 1
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hd]
  refine complexSpectralRadius_diagonal_eq_ofReal _ (fun p => ?_) (i₀ := (0, 0)) ?_
  · have h1 := abs_cos_le n₁ p.1
    have h2 := abs_cos_le n₂ p.2
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine (abs_add_le _ _).trans ?_
    simp only [modelEEigenvalues, abs_mul, abs_two]
    linarith
  · simp only [modelEEigenvalues, Fin.val_zero, Nat.cast_zero, zero_add, one_mul]
    rw [abs_of_nonneg]
    have := cos_pi_div_nonneg n₁
    have := cos_pi_div_nonneg n₂
    positivity

/-! ### The alternating-direction iteration (11.2.16) -/

/-- $4I - E_m = \operatorname{tridiag}(-1, 4, -1)$ is nonsingular. -/
private theorem isUnit_four_sub_modelE (m : ℕ) :
    IsUnit ((4 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) - modelE m) := by
  have h : (4 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) - modelE m =
      Matrix.symmTridiagonalToeplitz m (-1) 4 := by
    ext i j
    simp only [modelE, Matrix.symmTridiagonalToeplitz_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  rw [h]
  exact (Matrix.posDef_symmTridiagonalToeplitz m (by norm_num)).isUnit

/-- $4I - (I \otimes Y) = I \otimes (4I - Y)$. -/
private theorem four_smul_one_sub_one_kronecker {m₁ m₂ : ℕ} (Y : Matrix (Fin m₂) (Fin m₂) ℝ) :
    (4 : ℝ) • (1 : Matrix (Fin m₁ × Fin m₂) (Fin m₁ × Fin m₂) ℝ) -
        ((1 : Matrix (Fin m₁) (Fin m₁) ℝ) ⊗ₖ Y) = 1 ⊗ₖ ((4 : ℝ) • 1 - Y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Matrix.kronecker_add, ← neg_one_smul ℝ Y,
    ← neg_one_smul ℝ ((1 : Matrix (Fin m₁) (Fin m₁) ℝ) ⊗ₖ Y), Matrix.kronecker_smul,
    Matrix.kronecker_smul, Matrix.one_kronecker_one]

/-- $4I - (X \otimes I) = (4I - X) \otimes I$. -/
private theorem four_smul_one_sub_kronecker_one {m₁ m₂ : ℕ} (X : Matrix (Fin m₁) (Fin m₁) ℝ) :
    (4 : ℝ) • (1 : Matrix (Fin m₁ × Fin m₂) (Fin m₁ × Fin m₂) ℝ) -
        (X ⊗ₖ (1 : Matrix (Fin m₂) (Fin m₂) ℝ)) = ((4 : ℝ) • 1 - X) ⊗ₖ 1 := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Matrix.add_kronecker, ← neg_one_smul ℝ X,
    ← neg_one_smul ℝ (X ⊗ₖ (1 : Matrix (Fin m₂) (Fin m₂) ℝ)), Matrix.smul_kronecker,
    Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- $4I - (I \otimes E_{n_2})$ is nonsingular, because it is $I \otimes (4I - E_{n_2})$. -/
private theorem isUnit_adiX (n₁ n₂ : ℕ) :
    IsUnit ((4 : ℝ) • (1 : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ) - (1 ⊗ₖ modelE n₂)) := by
  rw [four_smul_one_sub_one_kronecker]
  exact Matrix.IsUnit.kronecker isUnit_one (isUnit_four_sub_modelE n₂)

/-- $4I - (E_{n_1} \otimes I)$ is nonsingular, because it is $(4I - E_{n_1}) \otimes I$. -/
private theorem isUnit_adiY (n₁ n₂ : ℕ) :
    IsUnit ((4 : ℝ) • (1 : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ) - (modelE n₁ ⊗ₖ 1)) := by
  rw [four_smul_one_sub_kronecker_one]
  exact Matrix.IsUnit.kronecker (isUnit_four_sub_modelE n₁) isUnit_one

/-- **Section 11.2.6** of [golub2013matrix], the first splitting of the alternating-direction
iteration. It is the splitting $A = M_x - N_x$ of the model matrix with
$$M_x = 4I - (I_{n_1} \otimes E_{n_2}), \qquad N_x = E_{n_1} \otimes I_{n_2}.$$

The splitting stores $M_x$. The value of $N_x$ is `GolubVanLoan.Chapter11.adiSplitting_n`. -/
noncomputable def adiSplittingX (n₁ n₂ : ℕ) : Stationary.Splitting (poissonMatrix n₁ n₂) :=
  ⟨(4 : ℝ) • 1 - (1 ⊗ₖ modelE n₂), isUnit_adiX n₁ n₂⟩

/-- **Section 11.2.6** of [golub2013matrix], the second splitting of the alternating-direction
iteration. It is the splitting $A = M_y - N_y$ of the model matrix with
$$M_y = 4I - (E_{n_1} \otimes I_{n_2}), \qquad N_y = I_{n_1} \otimes E_{n_2}.$$

The splitting stores $M_y$. The value of $N_y$ is `GolubVanLoan.Chapter11.adiSplitting_n`. -/
noncomputable def adiSplittingY (n₁ n₂ : ℕ) : Stationary.Splitting (poissonMatrix n₁ n₂) :=
  ⟨(4 : ℝ) • 1 - (modelE n₁ ⊗ₖ 1), isUnit_adiY n₁ n₂⟩

/-- **Equation (11.2.16)** of [golub2013matrix]. The alternating-direction step for the model
problem maps $u^{(k-1)}$ to the solution $u^{(k)}$ of
$$M_x v^{(k)} = N_x u^{(k-1)} + b, \qquad M_y u^{(k)} = N_y v^{(k)} + b.$$

It is an exact map, not a rounded program, because the source solves two linear systems and
fixes no order of operations. -/
noncomputable def adiStep (n₁ n₂ : ℕ) (b u : Fin n₁ × Fin n₂ → ℝ) : Fin n₁ × Fin n₂ → ℝ :=
  (adiSplittingY n₁ n₂).mulVecStep b ((adiSplittingX n₁ n₂).mulVecStep b u)

/-- **Section 11.2.6** of [golub2013matrix]. The complementary parts of the two splittings of the
alternating-direction iteration are $N_x = E_{n_1} \otimes I_{n_2}$ and
$N_y = I_{n_1} \otimes E_{n_2}$. -/
theorem adiSplitting_n (n₁ n₂ : ℕ) :
    (adiSplittingX n₁ n₂).n = modelE n₁ ⊗ₖ 1 ∧ (adiSplittingY n₁ n₂).n = 1 ⊗ₖ modelE n₂ := by
  obtain ⟨hA, -, -⟩ := equation_11_2_12 n₁ n₂
  constructor
  · change (4 : ℝ) • 1 - (1 ⊗ₖ modelE n₂) - poissonMatrix n₁ n₂ = _
    rw [hA]; abel
  · change (4 : ℝ) • 1 - (modelE n₁ ⊗ₖ 1) - poissonMatrix n₁ n₂ = _
    rw [hA]; abel

/-- $M_x^{-1} N_x = E_{n_1} \otimes (4I - E_{n_2})^{-1}$. -/
private theorem adiX_iterationOperator (n₁ n₂ : ℕ) :
    (adiSplittingX n₁ n₂).iterationOperator = modelE n₁ ⊗ₖ ((4 : ℝ) • 1 - modelE n₂)⁻¹ := by
  have hm : (adiSplittingX n₁ n₂).m = 1 ⊗ₖ ((4 : ℝ) • 1 - modelE n₂) :=
    four_smul_one_sub_one_kronecker _
  rw [Stationary.Splitting.iterationOperator_eq, ← Matrix.nonsing_inv_eq_ringInverse, hm,
    (adiSplitting_n n₁ n₂).1, Matrix.inv_kronecker, inv_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- $M_y^{-1} N_y = (4I - E_{n_1})^{-1} \otimes E_{n_2}$. -/
private theorem adiY_iterationOperator (n₁ n₂ : ℕ) :
    (adiSplittingY n₁ n₂).iterationOperator = ((4 : ℝ) • 1 - modelE n₁)⁻¹ ⊗ₖ modelE n₂ := by
  have hm : (adiSplittingY n₁ n₂).m = ((4 : ℝ) • 1 - modelE n₁) ⊗ₖ 1 :=
    four_smul_one_sub_kronecker_one _
  rw [Stationary.Splitting.iterationOperator_eq, ← Matrix.nonsing_inv_eq_ringInverse, hm,
    (adiSplitting_n n₁ n₂).2, Matrix.inv_kronecker, inv_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- Conjugation by a matrix $S$ whose determinant is a unit is multiplicative:
$S^{-1} XY S = (S^{-1} X S)(S^{-1} Y S)$. -/
private theorem conj_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : IsUnit S.det) (X Y : Matrix ι ι ℝ) :
    S⁻¹ * (X * Y) * S = (S⁻¹ * X * S) * (S⁻¹ * Y * S) := by
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hS]

/-- Conjugation by a matrix $S$ whose determinant is a unit commutes with inversion:
$S^{-1} X^{-1} S = (S^{-1} X S)^{-1}$. -/
private theorem conj_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : IsUnit S.det) (X : Matrix ι ι ℝ) : S⁻¹ * X⁻¹ * S = (S⁻¹ * X * S)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hS,
    Matrix.mul_assoc]

/-- $S_m^{-1}(4I - E_m) S_m = 4I - D_m$. -/
private theorem conj_four_sub_modelE (m : ℕ) :
    (Matrix.dst1 m)⁻¹ * ((4 : ℝ) • 1 - modelE m) * Matrix.dst1 m =
      (4 : ℝ) • 1 - Matrix.diagonal (modelEEigenvalues m) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 m)),
    equation_11_2_13]

/-- In the sine basis, the iteration matrix of the alternating-direction iteration is the Kronecker
product $\bigl((4I - D_{n_1})^{-1} D_{n_1}\bigr) \otimes \bigl(D_{n_2} (4I -
D_{n_2})^{-1}\bigr)$. -/
private theorem conj_adi (n₁ n₂ : ℕ) :
    (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ *
        ((adiSplittingY n₁ n₂).iterationOperator * (adiSplittingX n₁ n₂).iterationOperator) *
        (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
      (((4 : ℝ) • 1 - Matrix.diagonal (modelEEigenvalues n₁))⁻¹ *
          Matrix.diagonal (modelEEigenvalues n₁)) ⊗ₖ
        (Matrix.diagonal (modelEEigenvalues n₂) *
          ((4 : ℝ) • 1 - Matrix.diagonal (modelEEigenvalues n₂))⁻¹) := by
  have h₁ := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 n₁)
  have h₂ := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 n₂)
  rw [adiY_iterationOperator, adiX_iterationOperator, ← Matrix.mul_kronecker_mul, kronecker_conj,
    conj_mul h₁, conj_mul h₂, conj_inv h₁, conj_inv h₂, conj_four_sub_modelE,
    conj_four_sub_modelE, equation_11_2_13, equation_11_2_13]

/-- **Section 11.2.6** of [golub2013matrix], the error of the alternating-direction iteration. Let
$A$ be the model matrix, let $Ax = b$, and let $G = (M_y^{-1} N_y)(M_x^{-1} N_x)$. Then the
iterates of (11.2.16) from any $u^{(0)}$ satisfy
$$u^{(k)} - x = G^k (u^{(0)} - x)$$
for every $k \ge 0$. With $S = S_{n_1} \otimes S_{n_2}$,
$$S^{-1} G S = (4I - D_{n_1} \otimes I)^{-1} (I \otimes D_{n_2})
  (4I - I \otimes D_{n_2})^{-1} (D_{n_1} \otimes I).$$
-/
theorem adi_error_eq (n₁ n₂ : ℕ) {b x : Fin n₁ × Fin n₂ → ℝ} (hx : poissonMatrix n₁ n₂ *ᵥ x = b)
    (u₀ : Fin n₁ × Fin n₂ → ℝ) (k : ℕ) :
    (adiStep n₁ n₂ b)^[k] u₀ - x =
        ((adiSplittingY n₁ n₂).iterationOperator * (adiSplittingX n₁ n₂).iterationOperator) ^ k *ᵥ
          (u₀ - x) ∧
      (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ *
          ((adiSplittingY n₁ n₂).iterationOperator * (adiSplittingX n₁ n₂).iterationOperator) *
          (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
        ((4 : ℝ) • 1 - Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1)⁻¹ *
          (1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂)) *
          ((4 : ℝ) • 1 - 1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂))⁻¹ *
          (Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1) := by
  constructor
  · have hstep : ∀ u, adiStep n₁ n₂ b u - x = ((adiSplittingY n₁ n₂).iterationOperator *
        (adiSplittingX n₁ n₂).iterationOperator) *ᵥ (u - x) := fun u => by
      rw [adiStep, mulVecStep_sub _ hx, mulVecStep_sub _ hx, Matrix.mulVec_mulVec]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hstep, ih, Matrix.mulVec_mulVec, ← pow_succ']
  · rw [conj_adi, four_smul_one_sub_kronecker_one, four_smul_one_sub_one_kronecker,
      Matrix.inv_kronecker, Matrix.inv_kronecker]
    simp only [inv_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- $4I - \operatorname{diag}(d) = \operatorname{diag}(4 - d)$. -/
private theorem four_smul_one_sub_diagonal {m : ℕ} (d : Fin m → ℝ) :
    (4 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) - Matrix.diagonal d =
      Matrix.diagonal fun i => 4 - d i := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The inverse of a diagonal matrix with nonzero diagonal entries $d_i$ is
$\operatorname{diag}(d_i^{-1})$. -/
private theorem inv_diagonal_of_ne_zero {m : ℕ} (d : Fin m → ℝ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal fun i => (d i)⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  have : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℝ) := funext fun i => inv_mul_cancel₀ (hd i)
  rw [this, Matrix.diagonal_one]

/-- $4 - \mu_k^{(m)} \ne 0$, because the eigenvalues of $E_m$ lie in $[-2, 2]$. -/
private theorem four_sub_modelEEigenvalues_ne_zero (m : ℕ) (k : Fin m) :
    4 - modelEEigenvalues m k ≠ 0 := by
  have := Real.cos_le_one ((((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1))
  simp only [modelEEigenvalues]
  linarith

/-- The scalar bound behind (11.2.17): if $|c| \le c_0 < 1$, then $|2c/(4 - 2c)| \le c_0/(2 - c_0)$.
-/
private theorem abs_adiFactor_le {c c₀ : ℝ} (hc : |c| ≤ c₀) (hc₀ : c₀ < 1) :
    |(4 - 2 * c)⁻¹ * (2 * c)| ≤ c₀ / (2 - c₀) := by
  have hc1 : c ≤ c₀ := (le_abs_self c).trans hc
  have h2c : 0 < 2 - c := by linarith
  have h2c₀ : 0 < 2 - c₀ := by linarith
  have e : (4 - 2 * c)⁻¹ * (2 * c) = c / (2 - c) := by
    rw [show 4 - 2 * c = 2 * (2 - c) by ring]
    field_simp
  rw [e, abs_div, abs_of_pos h2c, div_le_div_iff₀ h2c h2c₀]
  have hc₀0 : 0 ≤ c₀ := (abs_nonneg c).trans hc
  nlinarith [mul_nonneg hc₀0 (sub_nonneg.2 (le_abs_self c))]

/-- $2c/(4 - 2c) = c/(2 - c)$ for $c < 1$. -/
private theorem adiFactor_eq {c : ℝ} (h : c < 1) : (4 - 2 * c)⁻¹ * (2 * c) = c / (2 - c) := by
  rw [show 4 - 2 * c = 2 * (2 - c) by ring]
  have : 2 - c ≠ 0 := by linarith
  field_simp

/-- **Equation (11.2.17)** of [golub2013matrix]. For the model problem with $n_1, n_2 \ge 1$, let
$c_1 = \cos(\pi/(n_1 + 1))$ and $c_2 = \cos(\pi/(n_2 + 1))$. The iteration matrix
$G = (M_y^{-1} N_y)(M_x^{-1} N_x)$ of the alternating-direction iteration (11.2.16) has the
spectral radius
$$\rho(G) = \frac{c_1 c_2}{(2 - c_1)(2 - c_2)} < 1.$$

**Typo.** The source prints "$\rho(G) = =$" with one equality sign too many.

The source leaves the proof to Problem P11.2.9. The right side is embedded in $[0, \infty]$ by
`ENNReal.ofReal`, and the bound $< 1$ is stated for the real number. -/
theorem equation_11_2_17 (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    Matrix.complexSpectralRadius
        ((adiSplittingY n₁ n₂).iterationOperator * (adiSplittingX n₁ n₂).iterationOperator) =
      ENNReal.ofReal (Real.cos (Real.pi / ((n₁ : ℝ) + 1)) * Real.cos (Real.pi / ((n₂ : ℝ) + 1)) /
        ((2 - Real.cos (Real.pi / ((n₁ : ℝ) + 1))) * (2 - Real.cos (Real.pi / ((n₂ : ℝ) + 1))))) ∧
      Real.cos (Real.pi / ((n₁ : ℝ) + 1)) * Real.cos (Real.pi / ((n₂ : ℝ) + 1)) /
        ((2 - Real.cos (Real.pi / ((n₁ : ℝ) + 1))) * (2 - Real.cos (Real.pi / ((n₂ : ℝ) + 1)))) <
        1 := by
  have hc₁0 := cos_pi_div_nonneg n₁
  have hc₂0 := cos_pi_div_nonneg n₂
  have hc₁1 := cos_pi_div_lt_one n₁
  have hc₂1 := cos_pi_div_lt_one n₂
  set c₁ := Real.cos (Real.pi / ((n₁ : ℝ) + 1))
  set c₂ := Real.cos (Real.pi / ((n₂ : ℝ) + 1))
  have hsplit : c₁ * c₂ / ((2 - c₁) * (2 - c₂)) = c₁ / (2 - c₁) * (c₂ / (2 - c₂)) :=
    (div_mul_div_comm _ _ _ _).symm
  have hf : ∀ c : ℝ, 0 ≤ c → c < 1 → 0 ≤ c / (2 - c) ∧ c / (2 - c) < 1 := fun c h0 h1 =>
    ⟨div_nonneg h0 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  refine ⟨?_, ?_⟩
  · rw [← Matrix.complexSpectralRadius_conj (isUnit_dst1_kronecker n₁ n₂), conj_adi,
      four_smul_one_sub_diagonal, four_smul_one_sub_diagonal,
      inv_diagonal_of_ne_zero _ (four_sub_modelEEigenvalues_ne_zero n₁),
      inv_diagonal_of_ne_zero _ (four_sub_modelEEigenvalues_ne_zero n₂),
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_kronecker_diagonal, hsplit]
    refine complexSpectralRadius_diagonal_eq_ofReal _ (fun p => ?_) (i₀ := (0, 0)) ?_
    · rw [abs_mul, mul_comm (modelEEigenvalues n₂ p.2)]
      exact mul_le_mul (abs_adiFactor_le (abs_cos_le n₁ p.1) hc₁1)
        (abs_adiFactor_le (abs_cos_le n₂ p.2) hc₂1) (abs_nonneg _) (hf c₁ hc₁0 hc₁1).1
    · have e₁ : modelEEigenvalues n₁ 0 = 2 * c₁ := by
        simp only [modelEEigenvalues, Fin.val_zero, Nat.cast_zero, zero_add, one_mul]; rfl
      have e₂ : modelEEigenvalues n₂ 0 = 2 * c₂ := by
        simp only [modelEEigenvalues, Fin.val_zero, Nat.cast_zero, zero_add, one_mul]; rfl
      rw [e₁, e₂, mul_comm (2 * c₂), adiFactor_eq hc₁1, adiFactor_eq hc₂1,
        abs_of_nonneg (mul_nonneg (hf c₁ hc₁0 hc₁1).1 (hf c₂ hc₂0 hc₂1).1)]
  · rw [hsplit]
    exact (mul_le_of_le_one_right (hf c₁ hc₁0 hc₁1).1 (hf c₂ hc₂0 hc₂1).2.le).trans_lt
      (hf c₁ hc₁0 hc₁1).2

/-! ### SOR and SSOR -/

/-- **Equation (11.2.18)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ have
$a_{ii} \ne 0$ for all $i$, and let $\omega \ne 0$. The SOR splitting $A = M_\omega - N_\omega$
has
$$M_\omega = \omega^{-1} D_A + L_A, \qquad N_\omega = (\omega^{-1} - 1) D_A - U_A.$$

**Correction.** The source prints $N_\omega = (\omega^{-1} - 1) D_A + U_A$ in (11.2.18) and
(11.2.19). This is inconsistent with $A = M_\omega - N_\omega$, so the sign of $U_A$ is changed
here. The source itself has $-L_A^T$ in (11.2.22).

The splitting is `Matrix.sorSplitting`. -/
theorem equation_11_2_18 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A)) {ω : ℝ}
    (hω : ω ≠ 0) :
    (Matrix.sorSplitting A h hω).m = ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A ∧
      (Matrix.sorSplitting A h hω).n =
        (ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictUpper A := by
  refine ⟨rfl, ?_⟩
  change ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A - A = _
  have e := Matrix.diagPart_add_strictLower_add_strictUpper A
  calc ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A - A
      = ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A -
          (Matrix.diagPart A + Matrix.strictLower A + Matrix.strictUpper A) := by rw [e]
    _ = _ := by module

/-- The parts of the backward SOR splitting are $M = \omega^{-1} D_A + U_A$ and
$N = (\omega^{-1} - 1) D_A - L_A$.

**Reading.** Uses negative strictly lower part in N.
-/
private theorem backwardSorSplitting_m_n (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Matrix.diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    (Matrix.backwardSorSplitting A h hω).m = ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A ∧
      (Matrix.backwardSorSplitting A h hω).n =
        (ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictLower A := by
  refine ⟨rfl, ?_⟩
  change ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A - A = _
  have e := Matrix.diagPart_add_strictLower_add_strictUpper A
  calc ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A - A
      = ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A -
          (Matrix.diagPart A + Matrix.strictLower A + Matrix.strictUpper A) := by rw [e]
    _ = _ := by module

/-- The step $x^+$ of a splitting from $x$ solves $M x^+ = N x + b$. -/
private theorem m_mulVec_mulVecStep {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    (b x : Fin n → ℝ) : s.m *ᵥ s.mulVecStep b x = s.n *ᵥ x + b :=
  Matrix.mulVec_nonsing_inv_mulVec s.isUnit _

/-- **Equation (11.2.19)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ have
$a_{ii} \ne 0$ for all $i$, and let $\omega \ne 0$. In exact arithmetic, the componentwise SOR
step (11.2.20) from $x^{(k-1)}$ is the step of the SOR splitting, and its result $x^{(k)}$
satisfies
$$(\omega^{-1} D_A + L_A) x^{(k)} = \bigl((\omega^{-1} - 1) D_A - U_A\bigr) x^{(k-1)} + b.$$

**Correction.** The source prints $+U_A$ on the right side. See
`GolubVanLoan.Chapter11.equation_11_2_18`. -/
theorem equation_11_2_19 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A)) {ω : ℝ}
    (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    Id.run (sorSweep pure A ω b x) = (Matrix.sorSplitting A h hω).mulVecStep b x ∧
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A) *ᵥ Id.run (sorSweep pure A ω b x) =
        ((ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictUpper A) *ᵥ x + b := by
  have h1 : Id.run (sorSweep pure A ω b x) = (Matrix.sorSplitting A h hω).mulVecStep b x := by
    rw [sorSweep_id A h, Matrix.sorSweep_eq_mulVecStep A h hω]
  refine ⟨h1, ?_⟩
  rw [h1, ← (equation_11_2_18 A h hω).1, ← (equation_11_2_18 A h hω).2]
  exact m_mulVec_mulVecStep _ b x

/-- **Equation (11.2.21)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ have
$a_{ii} \ne 0$ for all $i$, and let $\omega \ne 0$. In exact arithmetic, the backward SOR step
from $x^{(k-1)}$ is the step of the backward SOR splitting, and its result $x^{(k)}$ satisfies
$$(\omega^{-1} D_A + U_A) x^{(k)} = \bigl((\omega^{-1} - 1) D_A - L_A\bigr) x^{(k-1)} + b.$$

**Correction.** The source prints $+L_A$ on the right side, which is inconsistent with the
splitting, as in (11.2.18).

The splitting is `Matrix.backwardSorSplitting`. -/
theorem equation_11_2_21 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A)) {ω : ℝ}
    (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    Id.run (backwardSorSweep pure A ω b x) = (Matrix.backwardSorSplitting A h hω).mulVecStep b x ∧
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A) *ᵥ Id.run (backwardSorSweep pure A ω b x) =
        ((ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictLower A) *ᵥ x + b := by
  have h1 : Id.run (backwardSorSweep pure A ω b x) =
      (Matrix.backwardSorSplitting A h hω).mulVecStep b x := by
    rw [backwardSorSweep_id A h, Matrix.backwardSorSweep_eq_mulVecStep A h hω]
  refine ⟨h1, ?_⟩
  rw [h1, ← (backwardSorSplitting_m_n A h hω).1, ← (backwardSorSplitting_m_n A h hω).2]
  exact m_mulVec_mulVecStep _ b x

/-- For a symmetric matrix $A$, $U_A = L_A^T$. -/
private theorem strictUpper_eq_transpose {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    Matrix.strictUpper A = (Matrix.strictLower A)ᵀ := by
  rw [Matrix.strictLower_transpose, hA.eq]

/-- **Equations (11.2.22)–(11.2.23)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, so that $U_A = L_A^T$, with $a_{ii} \ne 0$ for all $i$, and let $\omega \ne 0$. Write
$D = D_A$ and $L = L_A$. In exact arithmetic, the half step $y^{(k)}$ (the forward SOR sweep)
and the full step $x^{(k)}$ of the SSOR program from $x^{(k-1)}$ satisfy
$$(\omega^{-1} D + L) y^{(k)} = \bigl((\omega^{-1} - 1) D - L^T\bigr) x^{(k-1)} + b,$$
$$(\omega^{-1} D + L^T) x^{(k)} = \bigl((\omega^{-1} - 1) D - L\bigr) y^{(k)} + b.$$
-/
theorem equation_11_2_22 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (h : IsUnit (Matrix.diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A) *ᵥ Id.run (sorSweep pure A ω b x) =
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ) *ᵥ x + b ∧
      (ω⁻¹ • Matrix.diagPart A + (Matrix.strictLower A)ᵀ) *ᵥ Id.run (ssorSweep pure A ω b x) =
        ((ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictLower A) *ᵥ
          Id.run (sorSweep pure A ω b x) + b := by
  rw [← strictUpper_eq_transpose hA]
  exact ⟨(equation_11_2_19 A h hω b x).2,
    (equation_11_2_21 A h hω b (Id.run (sorSweep pure A ω b x))).2⟩

/-- **Equation (11.2.24)** of [golub2013matrix] and the claims after it. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $a_{ii} > 0$ for all $i$, let
$0 < \omega < 2$, and write $D = D_A$ and $L = L_A$. Then
$$M_{SSOR} = \frac{\omega}{2 - \omega} (\omega^{-1} D + L) D^{-1} (\omega^{-1} D + L^T)$$
is the matrix $M$ of the SSOR splitting $A = M - N$, and it is symmetric and positive definite.

The SSOR splitting is `Matrix.ssorSplitting`, whose matrix $M$ is $(\omega(2 - \omega))^{-1}
(D + \omega L) D^{-1} (D + \omega U_A)$. -/
theorem equation_11_2_24 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hd : ∀ i, 0 < A i i)
    {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    let h : IsUnit (Matrix.diagPart A) := (Matrix.isUnit_diagPart_iff A).2 fun i => (hd i).ne'
    (ω / (2 - ω)) • ((ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A) * (Matrix.diagPart A)⁻¹ *
        (ω⁻¹ • Matrix.diagPart A + (Matrix.strictLower A)ᵀ)) =
        (Matrix.ssorSplitting A h hω0.ne' hω2.ne).m ∧
      (Matrix.ssorSplitting A h hω0.ne' hω2.ne).m.IsSymm ∧
      (Matrix.ssorSplitting A h hω0.ne' hω2.ne).m.PosDef := by
  intro h
  refine ⟨?_, Matrix.ssorSplitting_m_isSymm hA h _ _,
    Matrix.ssorSplitting_m_posDef_of_diag_pos (Matrix.isHermitian_iff_isSymm.2 hA) hd h hω0 hω2⟩
  change _ = (ω * (2 - ω))⁻¹ • ((Matrix.diagPart A + ω • Matrix.strictLower A) *
    (Matrix.diagPart A)⁻¹ * (Matrix.diagPart A + ω • Matrix.strictUpper A))
  rw [strictUpper_eq_transpose hA]
  have h2 : (2 : ℝ) - ω ≠ 0 := by linarith
  have e1 : ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A =
      ω⁻¹ • (Matrix.diagPart A + ω • Matrix.strictLower A) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω0.ne', one_smul]
  have e2 : ω⁻¹ • Matrix.diagPart A + (Matrix.strictLower A)ᵀ =
      ω⁻¹ • (Matrix.diagPart A + ω • (Matrix.strictLower A)ᵀ) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω0.ne', one_smul]
  rw [e1, e2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

/-- **Equation (11.2.25)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ have
$a_{ii} \ne 0$ for all $i$, and let $\omega \ne 0, 2$. In exact arithmetic, the SSOR step from
$x^{(k-1)}$ is
$$x^{(k)} = x^{(k-1)} + M_{SSOR}^{-1} (b - A x^{(k-1)}),$$
where $M_{SSOR} = (\omega(2 - \omega))^{-1} (D_A + \omega L_A) D_A^{-1} (D_A + \omega U_A)$.

**Generalization.** The source states the identity for symmetric $A$, where $U_A = L_A^T$ and
$M_{SSOR}$ is the matrix of (11.2.24). The statement here holds for every $A$ with nonzero
diagonal entries.

$M_{SSOR}$ is the matrix $M$ of `Matrix.ssorSplitting`. The source leaves the proof to Problem
P11.2.10. -/
theorem equation_11_2_25 {A : Matrix (Fin n) (Fin n) ℝ} (h : IsUnit (Matrix.diagPart A)) {ω : ℝ}
    (hω : ω ≠ 0) (hω2 : ω ≠ 2) (b x : Fin n → ℝ) :
    Id.run (ssorSweep pure A ω b x) =
      x + (Matrix.ssorSplitting A h hω hω2).m⁻¹ *ᵥ (b - A *ᵥ x) := by
  change Id.run (backwardSorSweep pure A ω b (Id.run (sorSweep pure A ω b x))) = _
  rw [sorSweep_id A h, backwardSorSweep_id A h, Matrix.ssorSweep_eq_mulVecStep A h hω hω2,
    Stationary.Splitting.mulVecStep_eq_add_inv_mulVec]

/-- The iteration matrix of the SSOR splitting of a symmetric matrix is $G = M_\omega^{-T}
N_\omega^T M_\omega^{-1} N_\omega$, the matrix of Theorem 11.2.4.

**Reading.** Same operator product for symmetric matrices and allowed nonzero weight outside
convergence range.
-/
private theorem ssor_iterationOperator_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (h : IsUnit (Matrix.diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (hω2 : ω ≠ 2) :
    (Matrix.ssorSplitting A h hω hω2).iterationOperator =
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
        (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ) := by
  rw [Matrix.ssorSplitting_iterationOperator_eq_mul, Stationary.Splitting.iterationOperator_eq,
    Stationary.Splitting.iterationOperator_eq, ← Matrix.nonsing_inv_eq_ringInverse,
    ← Matrix.nonsing_inv_eq_ringInverse, (backwardSorSplitting_m_n A h hω).1,
    (backwardSorSplitting_m_n A h hω).2, (equation_11_2_18 A h hω).1, (equation_11_2_18 A h hω).2,
    strictUpper_eq_transpose hA, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.diagPart_transpose, hA.eq]
  simp only [Matrix.mul_assoc]

/-- **Theorem 11.2.4** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, and let $0 < \omega < 2$. Let
$$M_\omega = \omega^{-1} D_A + L_A, \qquad N_\omega = (\omega^{-1} - 1) D_A - L_A^T, \qquad
  G = M_\omega^{-T} N_\omega^T M_\omega^{-1} N_\omega,$$
the iteration matrix of SSOR (11.2.22)–(11.2.23) applied to $Ax = b$. Then every eigenvalue of
$G$ is real and lies in $[0, 1)$, and $\rho(G) < 1$.

**Generalization.** The source states that $G$ has real eigenvalues and $\rho(G) < 1$. The
statement here also says that the eigenvalues lie in $[0, 1)$, which the proof in the source
shows.

The eigenvalues are the spectrum of `Matrix.complexify G`. The proof identifies $G$ with the
iteration matrix of `Matrix.ssorSplitting`. -/
theorem theorem_11_2_4 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2) :
    let G := (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)
    spectrum ℂ G.complexify ⊆ Complex.ofReal '' Set.Ico 0 1 ∧ G.complexSpectralRadius < 1 := by
  intro G
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.1 hA.isHermitian
  have hd : ∀ i, 0 < A i i := fun i => hA.diag_pos
  have h : IsUnit (Matrix.diagPart A) := (Matrix.isUnit_diagPart_iff A).2 fun i => (hd i).ne'
  have hG : G = (Matrix.ssorSplitting A h hω0.ne' hω2.ne).iterationOperator :=
    (ssor_iterationOperator_eq hsymm h hω0.ne' hω2.ne).symm
  rw [hG]
  exact ⟨Stationary.Splitting.spectrum_complexify_iterationOperator_subset _ hA
      (Matrix.ssorSplitting_m_sub_posSemidef hA.isHermitian hd h hω0 hω2),
    Matrix.ssorSplitting_complexSpectralRadius_lt_one hA h hω0 hω2⟩

/-- **Equation (11.2.26)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $0 < \omega < 2$, let $Ax = b$, and let $G$ be the matrix of Theorem
11.2.4. Then the iterates of the exact SSOR program from any $x^{(0)}$ satisfy
$$x^{(k)} - x = G^k (x^{(0)} - x), \qquad G = M_\omega^{-T} N_\omega^T M_\omega^{-1} N_\omega,$$
for every $k \ge 0$. -/
theorem equation_11_2_26 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2) {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    (fun y => Id.run (ssorSweep pure A ω b y))^[k] x₀ - x =
      ((ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
        (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)) ^ k *ᵥ (x₀ - x) := by
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.1 hA.isHermitian
  have h : IsUnit (Matrix.diagPart A) :=
    (Matrix.isUnit_diagPart_iff A).2 fun i => hA.diag_pos.ne'
  have hf : (fun y => Id.run (ssorSweep pure A ω b y)) =
      (Matrix.ssorSplitting A h hω0.ne' hω2.ne).mulVecStep b := by
    funext y
    rw [equation_11_2_25 h hω0.ne' hω2.ne, Stationary.Splitting.mulVecStep_eq_add_inv_mulVec]
  rw [hf, equation_11_2_7 _ hx, ssor_iterationOperator_eq hsymm h]

/-- $(cB)^{-1} = c^{-1} B^{-1}$ for $c \ne 0$ and $B$ nonsingular. -/
private theorem inv_smul_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : c ≠ 0)
    {B : Matrix ι ι ℝ} (hB : IsUnit B) : (c • B)⁻¹ = c⁻¹ • B⁻¹ :=
  Matrix.inv_eq_left_inv (by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hB), one_smul])

/-- The scalars cancel in $M^{-T} N^T M^{-1} N$ for $M = \omega^{-1} P$ and $N = \omega^{-1} Q$: the
product is $P^{-T} Q^T P^{-1} Q$. -/
private theorem ssorG_scale {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : ℝ} (hω : ω ≠ 0)
    {P : Matrix ι ι ℝ} (hP : IsUnit P) (Q : Matrix ι ι ℝ) :
    (ω⁻¹ • P)ᵀ⁻¹ * (ω⁻¹ • Q)ᵀ * (ω⁻¹ • P)⁻¹ * (ω⁻¹ • Q) = Pᵀ⁻¹ * Qᵀ * P⁻¹ * Q := by
  rw [Matrix.transpose_smul, Matrix.transpose_smul,
    inv_smul_of_isUnit (inv_ne_zero hω) ((Matrix.isUnit_transpose P).2 hP),
    inv_smul_of_isUnit (inv_ne_zero hω) hP, inv_inv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [inv_mul_cancel₀ hω, mul_one, inv_mul_cancel₀ hω, one_smul]

/-- Conjugation of $P^{-T} Q^T P^{-1} Q$ by a matrix $D_1$ whose determinant is a unit gives
$(D_1^{-1} P^T D_1^{-1})^{-1} (D_1^{-1} Q^T D_1^{-1}) (D_1^{-1} P D_1^{-1})^{-1} (D_1^{-1} Q
D_1^{-1})$. -/
private theorem conj_ssorG {ι : Type*} [Fintype ι] [DecidableEq ι] {D₁ : Matrix ι ι ℝ}
    (hD : IsUnit D₁.det) (P Q : Matrix ι ι ℝ) :
    D₁ * (Pᵀ⁻¹ * Qᵀ * P⁻¹ * Q) * D₁⁻¹ =
      (D₁⁻¹ * Pᵀ * D₁⁻¹)⁻¹ * (D₁⁻¹ * Qᵀ * D₁⁻¹) * (D₁⁻¹ * P * D₁⁻¹)⁻¹ * (D₁⁻¹ * Q * D₁⁻¹) := by
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hD, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hD, Matrix.nonsing_inv_mul_cancel_left _ _ hD]

/-- $D_1^{-1}(a D_1^2 + c K) D_1^{-1} = aI + c D_1^{-1} K D_1^{-1}$. -/
private theorem conj_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {D₁ : Matrix ι ι ℝ}
    (hD : IsUnit D₁.det) (a c : ℝ) (K : Matrix ι ι ℝ) :
    D₁⁻¹ * (a • (D₁ * D₁) + c • K) * D₁⁻¹ = a • 1 + c • (D₁⁻¹ * K * D₁⁻¹) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, ← Matrix.mul_assoc D₁⁻¹ D₁ D₁, Matrix.nonsing_inv_mul _ hD, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hD]

/-- $v \cdot (Yw) = (Y^T v) \cdot w$. -/
private theorem dotProduct_mulVec_eq {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v w : ι → ℝ) :
    v ⬝ᵥ (Y *ᵥ w) = (Yᵀ *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- **Equation (11.2.27)** of [golub2013matrix], from the proof of Theorem 11.2.4. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $a_{ii} > 0$ for all $i$, and let
$\omega \ne 0$. Let $D_1 = \operatorname{diag}(\sqrt{a_{11}}, \dots, \sqrt{a_{nn}})$,
$L_1 = D_1^{-1} L_A D_1^{-1}$, let $G$ be the matrix of Theorem 11.2.4, and let
$G_1 = D_1 G D_1^{-1}$. Then $D_1^2 = D_A$,
$$G_1 = (I + \omega L_1^T)^{-1} (I + \omega L_1)^{-1}
  \bigl((1 - \omega) I - \omega L_1\bigr) \bigl((1 - \omega) I - \omega L_1^T\bigr),$$
and every real eigenpair $G_1 v = \lambda v$ with $v^T v = 1$ satisfies
$$\lambda = \frac{\|(1 - \omega) v - \omega L_1^T v\|_2^2}{\|v + \omega L_1^T v\|_2^2}
  = 1 - \frac{\omega (2 - \omega) (1 + 2 v^T L_1^T v)}{\|v + \omega L_1^T v\|_2^2}.$$

The Lean statement defines $G_1$ by the product formula and proves $D_1 G D_1^{-1} = G_1$. The
squared norms are dot products.

**Generalization.** The normalized product and eigenvalue quotient require only symmetry,
positive diagonal entries, and $\omega \ne 0$. The stronger assumptions in Theorem 11.2.4 yield
the spectral bound. -/
theorem equation_11_2_27 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hd : ∀ i, 0 < A i i)
    {ω : ℝ} (hω : ω ≠ 0) :
    let D₁ := Matrix.diagonal fun i => Real.sqrt (A i i)
    let L₁ := D₁⁻¹ * Matrix.strictLower A * D₁⁻¹
    let G := (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)
    let G₁ := (1 + ω • L₁ᵀ)⁻¹ * (1 + ω • L₁)⁻¹ * ((1 - ω) • 1 - ω • L₁) * ((1 - ω) • 1 - ω • L₁ᵀ)
    D₁ * D₁ = Matrix.diagPart A ∧ D₁ * G * D₁⁻¹ = G₁ ∧
      ∀ (l : ℝ) (v : Fin n → ℝ), G₁ *ᵥ v = l • v → v ⬝ᵥ v = 1 →
        l = ((1 - ω) • v - ω • L₁ᵀ *ᵥ v) ⬝ᵥ ((1 - ω) • v - ω • L₁ᵀ *ᵥ v) /
            ((v + ω • L₁ᵀ *ᵥ v) ⬝ᵥ (v + ω • L₁ᵀ *ᵥ v)) ∧
          l = 1 - ω * (2 - ω) * (1 + 2 * (v ⬝ᵥ L₁ᵀ *ᵥ v)) /
            ((v + ω • L₁ᵀ *ᵥ v) ⬝ᵥ (v + ω • L₁ᵀ *ᵥ v)) := by
  intro D₁ L₁ G G₁
  have hD1 : D₁ * D₁ = Matrix.diagPart A := by
    change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal A.diag
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hd i).le
  have hD1u : IsUnit D₁.det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => (Real.sqrt_pos.2 (hd i)).ne'
  have hD1i : IsUnit D₁⁻¹ :=
    (Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 hD1u)
  have hD1iT : (D₁⁻¹)ᵀ = D₁⁻¹ := by rw [Matrix.transpose_nonsing_inv, Matrix.diagonal_transpose]
  have hDT : (Matrix.diagPart A)ᵀ = Matrix.diagPart A := by
    rw [Matrix.diagPart_transpose, hA.eq]
  have h : IsUnit (Matrix.diagPart A) := (Matrix.isUnit_diagPart_iff A).2 fun i => (hd i).ne'
  have hPu : IsUnit (Matrix.diagPart A + ω • Matrix.strictLower A) :=
    Matrix.isUnit_diagPart_add_smul_strictLower h ω
  have hL1T : L₁ᵀ = D₁⁻¹ * (Matrix.strictLower A)ᵀ * D₁⁻¹ := by
    change (D₁⁻¹ * Matrix.strictLower A * D₁⁻¹)ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hD1iT, Matrix.mul_assoc]
  -- the four conjugated factors
  have hX : D₁⁻¹ * (Matrix.diagPart A + ω • Matrix.strictLower A) * D₁⁻¹ = 1 + ω • L₁ := by
    rw [show Matrix.diagPart A + ω • Matrix.strictLower A =
      (1 : ℝ) • (D₁ * D₁) + ω • Matrix.strictLower A by rw [one_smul, hD1], conj_diag hD1u,
      one_smul]
  have hXT : D₁⁻¹ * (Matrix.diagPart A + ω • Matrix.strictLower A)ᵀ * D₁⁻¹ = 1 + ω • L₁ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, hDT,
      show Matrix.diagPart A + ω • (Matrix.strictLower A)ᵀ =
        (1 : ℝ) • (D₁ * D₁) + ω • (Matrix.strictLower A)ᵀ by rw [one_smul, hD1],
      conj_diag hD1u, one_smul, hL1T]
  have hY : D₁⁻¹ * ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ)ᵀ * D₁⁻¹ =
      (1 - ω) • 1 - ω • L₁ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, hDT,
      Matrix.transpose_transpose, sub_eq_add_neg, ← neg_smul, ← hD1, conj_diag hD1u, neg_smul,
      ← sub_eq_add_neg]
  have hYT : D₁⁻¹ * ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ) * D₁⁻¹ =
      (1 - ω) • 1 - ω • L₁ᵀ := by
    rw [sub_eq_add_neg, ← neg_smul, ← hD1, conj_diag hD1u, neg_smul, ← sub_eq_add_neg, hL1T]
  -- `G = P⁻ᵀ Qᵀ P⁻¹ Q`
  have hG : G = (Matrix.diagPart A + ω • Matrix.strictLower A)ᵀ⁻¹ *
      ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ)ᵀ *
      (Matrix.diagPart A + ω • Matrix.strictLower A)⁻¹ *
      ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ) := by
    have e1 : ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A =
        ω⁻¹ • (Matrix.diagPart A + ω • Matrix.strictLower A) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
    have e2 : (ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ =
        ω⁻¹ • ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ) := by
      rw [smul_sub, smul_smul, smul_smul, mul_sub, mul_one, inv_mul_cancel₀ hω, one_smul]
    change (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ) = _
    rw [e1, e2]
    exact ssorG_scale hω hPu _
  -- units and commutation
  have hXu : IsUnit (1 + ω • L₁) := by rw [← hX]; exact (hD1i.mul hPu).mul hD1i
  have hXTu : IsUnit (1 + ω • L₁ᵀ) := by
    rw [← hXT]; exact (hD1i.mul ((Matrix.isUnit_transpose _).2 hPu)).mul hD1i
  have hXd := (Matrix.isUnit_iff_isUnit_det _).1 hXu
  have hXTd := (Matrix.isUnit_iff_isUnit_det _).1 hXTu
  have hcomm : ((1 - ω) • 1 - ω • L₁) * (1 + ω • L₁)⁻¹ =
      (1 + ω • L₁)⁻¹ * ((1 - ω) • 1 - ω • L₁) := by
    have hYX : (1 - ω) • (1 : Matrix (Fin n) (Fin n) ℝ) - ω • L₁ = (2 - ω) • 1 - (1 + ω • L₁) := by
      module
    rw [hYX, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_nonsing_inv _ hXd, Matrix.nonsing_inv_mul _ hXd]
  have hG₁ : D₁ * G * D₁⁻¹ = G₁ := by
    rw [hG, conj_ssorG hD1u, hXT, hY, hX, hYT]
    change _ = (1 + ω • L₁ᵀ)⁻¹ * (1 + ω • L₁)⁻¹ * ((1 - ω) • 1 - ω • L₁) *
      ((1 - ω) • 1 - ω • L₁ᵀ)
    rw [Matrix.mul_assoc (1 + ω • L₁ᵀ)⁻¹, hcomm, ← Matrix.mul_assoc]
  refine ⟨hD1, hG₁, fun l v hv hv1 => ?_⟩
  -- the eigenvalue
  have hYT' : ((1 - ω) • (1 : Matrix (Fin n) (Fin n) ℝ) - ω • L₁)ᵀ = (1 - ω) • 1 - ω • L₁ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  have hXT' : (1 + ω • L₁)ᵀ = 1 + ω • L₁ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]
  have key : ((1 - ω) • 1 - ω • L₁) *ᵥ (((1 - ω) • 1 - ω • L₁ᵀ) *ᵥ v) =
      l • ((1 + ω • L₁) *ᵥ ((1 + ω • L₁ᵀ) *ᵥ v)) := by
    have h1 : ((1 + ω • L₁) * (1 + ω • L₁ᵀ)) *ᵥ (G₁ *ᵥ v) =
        ((1 - ω) • 1 - ω • L₁) *ᵥ (((1 - ω) • 1 - ω • L₁ᵀ) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      change (1 + ω • L₁) * (1 + ω • L₁ᵀ) * ((1 + ω • L₁ᵀ)⁻¹ * (1 + ω • L₁)⁻¹ *
        ((1 - ω) • 1 - ω • L₁) * ((1 - ω) • 1 - ω • L₁ᵀ)) = _
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hXTd,
        Matrix.mul_nonsing_inv_cancel_left _ _ hXd]
    rw [← h1, hv, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  set a := ((1 - ω) • (1 : Matrix (Fin n) (Fin n) ℝ) - ω • L₁ᵀ) *ᵥ v with ha
  set c := (1 + ω • L₁ᵀ) *ᵥ v with hc
  have hdot := congrArg (v ⬝ᵥ ·) key
  simp only [dotProduct_smul, dotProduct_mulVec_eq, hYT', hXT', smul_eq_mul] at hdot
  have ha' : a = (1 - ω) • v - ω • L₁ᵀ *ᵥ v := by
    rw [ha, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc' : c = v + ω • L₁ᵀ *ᵥ v := by
    rw [hc, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv1
  have hc0 : c ≠ 0 := by
    intro h0
    apply hv0
    rw [← Matrix.nonsing_inv_mulVec_mulVec hXTu v, ← hc, h0, Matrix.mulVec_zero]
  have hcc : c ⬝ᵥ c ≠ 0 := fun h0 => hc0 (dotProduct_self_eq_zero.1 h0)
  have hl : l = a ⬝ᵥ a / (c ⬝ᵥ c) := (eq_div_iff hcc).2 hdot.symm
  rw [← ha', ← hc']
  refine ⟨hl, ?_⟩
  set w := L₁ᵀ *ᵥ v
  have hwv : w ⬝ᵥ v = v ⬝ᵥ w := dotProduct_comm _ _
  have haa : a ⬝ᵥ a = c ⬝ᵥ c - ω * (2 - ω) * (1 + 2 * (v ⬝ᵥ w)) := by
    rw [ha', hc']
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hwv, hv1]
    ring
  rw [hl, haa, sub_div, div_self hcc]

/-! ### The Chebyshev semi-iterative method -/

/-- **Equation (11.2.28)** of [golub2013matrix]. For coefficients $\nu_0(k), \dots, \nu_k(k)$ and
vectors $x^{(0)}, x^{(1)}, \dots \in \mathbb{R}^n$, the **semi-iterative combination** is
$$y^{(k)} = \sum_{j=0}^{k} \nu_j(k) x^{(j)}.$$

In the source, the $x^{(j)}$ are the iterates of a splitting, and the coefficients are those of
the polynomial $p_k(z) = \sum_j \nu_j(k) z^j$. The definition accepts any sequence of vectors. -/
def semiIterativeCombination {k : ℕ} (ν : Fin (k + 1) → ℝ) (xs : ℕ → Fin n → ℝ) : Fin n → ℝ :=
  ∑ j : Fin (k + 1), ν j • xs j

/-- **Section 11.2.8** of [golub2013matrix]. Let $A = M - N$ be a splitting of
$A \in \mathbb{R}^{n \times n}$ with $M$ nonsingular, let $G = M^{-1} N$, let $Ax = b$, and let
$x^{(j)}$ be the iterates of the splitting from $x^{(0)}$. If $p_k(1) = \sum_j \nu_j(k) = 1$,
then the semi-iterative combination satisfies
$$y^{(k)} - x = p_k(G) (x^{(0)} - x).$$
-/
theorem semiIterative_sub_eq {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) {k : ℕ} (ν : Fin (k + 1) → ℝ)
    (hν : ∑ j, ν j = 1) :
    semiIterativeCombination ν (fun j => (s.mulVecStep b)^[j] x₀) - x =
      Polynomial.aeval s.iterationOperator (∑ j : Fin (k + 1), C (ν j) * X ^ (j : ℕ)) *ᵥ
        (x₀ - x) := by
  have hx' : x = ∑ j : Fin (k + 1), ν j • x := by rw [← Finset.sum_smul, hν, one_smul]
  rw [semiIterativeCombination]
  conv_lhs => rw [hx', ← Finset.sum_sub_distrib]
  simp only [← smul_sub, equation_11_2_7 s hx, map_sum, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    Matrix.one_mul, Matrix.smul_mulVec]

open scoped Matrix.Norms.L2Operator in
/-- **Equation (11.2.29)** of [golub2013matrix]. Let $A = M - N$ be a splitting of
$A \in \mathbb{R}^{n \times n}$ with $M$ nonsingular, let $G = M^{-1} N$, let $Ax = b$, let
$x^{(j)}$ be the iterates of the splitting from $x^{(0)}$, and let
$p_k(1) = \sum_j \nu_j(k) = 1$. Then the semi-iterative combination satisfies
$$\|y^{(k)} - x\|_2 \le \|p_k(G)\|_2 \, \|x^{(0)} - x\|_2.$$

The matrix norm $\|p_k(G)\|_2$ is the operator norm of `Matrix.Norms.L2Operator`. -/
theorem equation_11_2_29 {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) {k : ℕ} (ν : Fin (k + 1) → ℝ)
    (hν : ∑ j, ν j = 1) :
    ‖WithLp.toLp 2 (semiIterativeCombination ν (fun j => (s.mulVecStep b)^[j] x₀) - x)‖ ≤
      ‖Polynomial.aeval s.iterationOperator (∑ j : Fin (k + 1), C (ν j) * X ^ (j : ℕ))‖ *
        ‖WithLp.toLp 2 (x₀ - x)‖ := by
  rw [semiIterative_sub_eq s hx x₀ ν hν]
  exact Matrix.l2_opNorm_mulVec _ (WithLp.toLp 2 (x₀ - x))

/-- **Section 11.2.8** of [golub2013matrix], the Chebyshev polynomial of the semi-iterative method.
For $\alpha, \beta \in \mathbb{R}$ and $k \ge 0$,
$$p_k(z) = \frac{c_k\bigl(-1 + 2(z - \alpha)/(\beta - \alpha)\bigr)}{c_k(\mu)}, \qquad
  \mu = -1 + \frac{2(1 - \alpha)}{\beta - \alpha},$$
where $c_k$ is the Chebyshev polynomial of degree $k$.

The polynomial $c_k$ is `Polynomial.Chebyshev.T ℝ k`. Division by zero gives $0$: if
$c_k(\mu) = 0$, the definition gives $p_k = 0$, and if $\beta = \alpha$, every quotient by
$\beta - \alpha$ is $0$.

**Reading.** Same polynomial formula on its domain, with total real reciprocal outside it.
-/
noncomputable def chebyshevSemiIterativePoly (α β : ℝ) (k : ℕ) : ℝ[X] :=
  C ((Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α)))⁻¹ *
    (Chebyshev.T ℝ k).comp (C (2 / (β - α)) * X + C (-1 - 2 * α / (β - α)))

/-- The value of the Chebyshev polynomial of §11.2.8.

**Reading.** Requires a nondegenerate interval for substitution.
-/
private theorem eval_chebyshevSemiIterativePoly {α β : ℝ} (hαβ : α < β) (k : ℕ) (t : ℝ) :
    (chebyshevSemiIterativePoly α β k).eval t =
      ((Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α)))⁻¹ *
        (Chebyshev.T ℝ k).eval (-1 + 2 * (t - α) / (β - α)) := by
  have hba : β - α ≠ 0 := by linarith
  have hl : 2 / (β - α) * t + (-1 - 2 * α / (β - α)) = -1 + 2 * (t - α) / (β - α) := by
    field_simp
    ring
  simp only [chebyshevSemiIterativePoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, hl]

/-- The Chebyshev polynomial of §11.2.8 has degree at most `k`.

**Reading.** Uniform upper bound includes degenerate interval and zero polynomial.
-/
private theorem natDegree_chebyshevSemiIterativePoly_lt (α β : ℝ) (k : ℕ) :
    (chebyshevSemiIterativePoly α β k).natDegree < k + 1 := by
  have hT : (Chebyshev.T ℝ k).natDegree = k := by rw [Chebyshev.natDegree_T]; simp
  refine Nat.lt_succ_of_le ((natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_))
  calc (Chebyshev.T ℝ k).natDegree * (C (2 / (β - α)) * X + C (-1 - 2 * α / (β - α))).natDegree
      ≤ k * 1 := Nat.mul_le_mul hT.le natDegree_linear_le
    _ = k := mul_one k

/-- **Section 11.2.8** of [golub2013matrix], the Chebyshev bound. Let $A = M - N$ be a splitting of
$A \in \mathbb{R}^{n \times n}$ with $M$ nonsingular whose iteration matrix $G = M^{-1} N$ is
symmetric with eigenvalues in $[\alpha, \beta]$, where $-1 < \alpha < \beta < 1$, as in
(11.2.30). Let $Ax = b$, let $\mu$ and $p_k$ be as in
`GolubVanLoan.Chapter11.chebyshevSemiIterativePoly`, and let $y^{(k)}$ be the semi-iterative
combination of the iterates $x^{(0)}, \dots, x^{(k)}$ of the splitting with the coefficients of
$p_k$. Then $p_k(1) = 1$, $|p_k(t)| \le 1/|c_k(\mu)|$ for all $t \in [\alpha, \beta]$, and
$$\|y^{(k)} - x\|_2 \le \frac{\|x - x^{(0)}\|_2}{|c_k(\mu)|}.$$

**Typo.** The source writes $\lambda_i \in \lambda(A)$; it means the eigenvalues of $G$.

**Reading.** The affine rescaling divides by $\beta-\alpha$, so the spectral enclosure must
have positive length. The source's enclosure (11.2.30) permits equal endpoints.

Here $\mu = 1 + 2(1 - \beta)/(\beta - \alpha) > 1$. The eigenvalues of $G$ are
`Matrix.IsHermitian.eigenvalues`. -/
theorem chebyshevSemiIterative_norm_le {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    (hG : s.iterationOperator.IsHermitian) {α β : ℝ} (hα : -1 < α) (hαβ : α < β) (hβ : β < 1)
    (hGab : ∀ i, hG.eigenvalues i ∈ Set.Icc α β) {b x : Fin n → ℝ} (hx : A *ᵥ x = b)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    (chebyshevSemiIterativePoly α β k).eval 1 = 1 ∧
      (∀ t ∈ Set.Icc α β, |(chebyshevSemiIterativePoly α β k).eval t| ≤
        1 / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))|) ∧
      ‖WithLp.toLp 2 (semiIterativeCombination
          (fun j : Fin (k + 1) => (chebyshevSemiIterativePoly α β k).coeff j)
          (fun j => (s.mulVecStep b)^[j] x₀) - x)‖ ≤
        ‖WithLp.toLp 2 (x - x₀)‖ / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))| := by
  have hba : 0 < β - α := by linarith
  have hμ : 1 ≤ -1 + 2 * (1 - α) / (β - α) := by
    have : 2 ≤ 2 * (1 - α) / (β - α) := by
      rw [le_div_iff₀ hba]
      linarith
    linarith
  have hT := Chebyshev.one_le_eval_T hμ k
  have hT0 : (Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α)) ≠ 0 := by linarith
  set p := chebyshevSemiIterativePoly α β k with hp
  have h1 : p.eval 1 = 1 := by
    rw [hp, eval_chebyshevSemiIterativePoly hαβ]
    exact inv_mul_cancel₀ hT0
  have h2 : ∀ t ∈ Set.Icc α β, |p.eval t| ≤
      1 / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))| := by
    intro t ht
    rw [hp, eval_chebyshevSemiIterativePoly hαβ, abs_mul, abs_inv, ← div_eq_inv_mul]
    refine div_le_div_of_nonneg_right (Chebyshev.abs_eval_T_real_le_one _ ?_) (abs_nonneg _)
    rw [abs_le]
    constructor
    · have : 0 ≤ 2 * (t - α) / (β - α) := div_nonneg (by linarith [ht.1]) hba.le
      linarith
    · have : 2 * (t - α) / (β - α) ≤ 2 := by
        rw [div_le_iff₀ hba]; linarith [ht.2]
      linarith
  refine ⟨h1, h2, ?_⟩
  have hdeg := natDegree_chebyshevSemiIterativePoly_lt α β k
  have hν : ∑ j : Fin (k + 1), p.coeff j = 1 := by
    rw [← h1, eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * 1 ^ i)]
    simp
  have hpoly : ∑ j : Fin (k + 1), C (p.coeff j) * X ^ (j : ℕ) = p := by
    rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
    conv_rhs => rw [p.as_sum_range' _ hdeg]
    simp only [C_mul_X_pow_eq_monomial]
  rw [semiIterative_sub_eq s hx x₀ _ hν, hpoly, ← Matrix.toEuclideanLin_toLp,
    Matrix.toEuclideanLin_aeval]
  have hB := Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin hG hGab
  have hle := hB.norm_aeval_map_apply_le p (WithLp.toLp 2 (x₀ - x))
  rw [show p.map (algebraMap ℝ ℝ) = p by rw [Algebra.algebraMap_self, Polynomial.map_id]] at hle
  refine hle.trans ?_
  have hS : sSup ((fun t => |p.eval t|) '' Set.Icc α β) ≤
      1 / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))| :=
    csSup_le ((Set.nonempty_Icc.2 hαβ.le).image _) (Set.forall_mem_image.2 h2)
  have hn : ‖WithLp.toLp 2 (x₀ - x)‖ = ‖WithLp.toLp 2 (x - x₀)‖ := by
    rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
  calc sSup ((fun t => |p.eval t|) '' Set.Icc α β) * ‖WithLp.toLp 2 (x₀ - x)‖
      ≤ 1 / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))| * ‖WithLp.toLp 2 (x₀ - x)‖ :=
        mul_le_mul_of_nonneg_right hS (norm_nonneg _)
    _ = _ := by rw [hn, one_div, inv_mul_eq_div]

/-- **Section 11.2.8** of [golub2013matrix], the update
$$y^{(k+1)} = y^{(k-1)} + \omega \bigl(y^{(k)} + z^{(k)} - y^{(k-1)}\bigr)$$
of the Chebyshev semi-iterative method, computed entry by entry with every operation rounded.

**Reading.** Same vector recurrence with explicit rounded arithmetic.
-/
def chebyshevCombine {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) (yp y z : Fin n → ℝ) (ω : ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun w i => do
    let s₁ ← rnd (y i + z i)
    let s₂ ← rnd (s₁ - yp i)
    let s₃ ← rnd (ω * s₂)
    pure (Function.update w i (← rnd (yp i + s₃)))) y

/-- **Section 11.2.8** of [golub2013matrix], one pass of the `while` loop of the Chebyshev
semi-iterative method, on the state $(k, c_{k-1}, c_k, y^{(k-1)}, y^{(k)}, r^{(k)},
\text{done})$. If the state is done, the pass leaves it unchanged. If the computed
$\|r^{(k)}\|_2$ is at most the tolerance, the pass marks the state as done. Otherwise it
computes $c_{k+1} = (2/\beta) c_k - c_{k-1}$ and $\omega_{k+1} = 1 + c_{k-1}/c_{k+1}$, solves
$M z^{(k)} = r^{(k)}$, forms $y^{(k+1)}$ by `GolubVanLoan.Chapter11.chebyshevCombine`, and
computes the residual $r^{(k+1)} = b - A y^{(k+1)}$.

**Reading.** Same scalar/vector recurrence, callback solve, rounded arithmetic and stop flag.
-/
noncomputable def chebyshevSemiIterativeStep {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (β tol : ℝ) (st : ℕ × ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × Bool) :
    M (ℕ × ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × Bool) := do
  let (k, cp, c, yp, y, r, done) := st
  if done then pure st else do
    let rr ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd r r
    let nr ← rnd (Real.sqrt rr)
    if nr ≤ tol then pure (k, cp, c, yp, y, r, true) else do
      let tb ← rnd (2 / β)
      let tc ← rnd (tb * c)
      let c' ← rnd (tc - cp)
      let q ← rnd (cp / c')
      let ω ← rnd (1 + q)
      let z ← solveM r
      let y' ← chebyshevCombine rnd yp y z ω
      let Ay' ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A y' 0
      let r' ← Chapter01.vecSub rnd b Ay'
      pure (k + 1, c, c', y, y', r', false)

/-- **Section 11.2.8** of [golub2013matrix], the Chebyshev semi-iterative method in the case
$\alpha = -\beta$, which accelerates the iteration $M x^{(j+1)} = N x^{(j)} + b$. The program
sets $c_0 = 1$, $c_1 = 1/\beta$ and $y^{(0)} = x^{(0)}$, solves $M y^{(1)} = N y^{(0)} + b$, and
sets $r^{(1)} = b - A y^{(1)}$ and $k = 1$. Then, while $\|r^{(k)}\|_2 > \mathrm{tol}$, it
computes
$$c_{k+1} = (2/\beta) c_k - c_{k-1}, \qquad \omega_{k+1} = 1 + c_{k-1}/c_{k+1}, \qquad
  M z^{(k)} = r^{(k)},$$
$$y^{(k+1)} = y^{(k-1)} + \omega_{k+1} \bigl(y^{(k)} + z^{(k)} - y^{(k-1)}\bigr),$$
increases $k$ by $1$ and sets $r^{(k)} = b - A y^{(k)}$. It returns the state $(k, c_{k-1}, c_k,
y^{(k-1)}, y^{(k)}, r^{(k)}, \text{done})$.

The solves with $M$ are a routine `solveM`, whose exact meaning is $M^{-1}$. The products with
$N$ and $A$ are the gaxpy `GolubVanLoan.Chapter01.algorithm_1_1_3`, and the test compares the
computed $\mathrm{fl}(\sqrt{\mathrm{fl}(r^T r)})$, with $r^T r$ from the dot product
`GolubVanLoan.Chapter01.algorithm_1_1_1`, with the tolerance. The loop makes at most `fuel`
passes.

**Reading.** Same compulsory first step then finite-fuel recurrence with stop checks.
-/
noncomputable def chebyshevSemiIterative {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (A N : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (β tol : ℝ) (fuel : ℕ) :
    M (ℕ × ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × Bool) := do
  let rhs ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd N x₀ b
  let y₁ ← solveM rhs
  let Ay₁ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A y₁ 0
  let r₁ ← Chapter01.vecSub rnd b Ay₁
  let c₁ ← rnd (1 / β)
  (List.range fuel).foldlM (fun st _ => chebyshevSemiIterativeStep rnd solveM A b β tol st)
    (1, 1, c₁, x₀, y₁, r₁, false)

/-- **Section 11.2.8** of [golub2013matrix], the polynomial of the case $\alpha = -\beta$:
$$p_k(z) = \frac{c_k(z/\beta)}{c_k(1/\beta)}.$$

Division by zero gives $0$: for $\beta = 0$ the quotients $z/\beta$ and $1/\beta$ are $0$, and
if $c_k(1/\beta) = 0$, the definition gives $p_k = 0$.

**Reading.** Totalized normalized symmetric-interval polynomial.
-/
noncomputable def chebyshevSymmetricPoly (β : ℝ) (k : ℕ) : ℝ[X] :=
  C ((Chebyshev.T ℝ k).eval (1 / β))⁻¹ * (Chebyshev.T ℝ k).comp (C (1 / β) * X)

/-- In exact arithmetic, the update is $y^{(k-1)} + \omega (y^{(k)} + z^{(k)} - y^{(k-1)})$. -/
private theorem chebyshevCombine_id (yp y z : Fin n → ℝ) (ω : ℝ) :
    Id.run (chebyshevCombine pure yp y z ω) = yp + ω • (y + z - yp) := by
  have hrun : Id.run (chebyshevCombine pure yp y z ω) = (List.finRange n).foldl
      (fun w i => Function.update w i (yp i + ω * (y i + z i - yp i))) y := List.idRun_foldlM
  rw [hrun]
  funext i
  exact List.foldl_update_apply_of_pairwise_rel (· < ·) (fun _ _ h h' => lt_asymm h h')
    (fun i _ => yp i + ω * (y i + z i - yp i)) (List.pairwise_lt_finRange n) y
    (List.mem_finRange i)

/-- The exact pass of the Chebyshev loop when the solve with $M$ is multiplication by a matrix.

**Reading.** Exact active update or explicit tolerance stop.
-/
private theorem chebyshevSemiIterativeStep_id (Minv A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (β tol : ℝ) (k : ℕ) (cp c : ℝ) (yp y r : Fin n → ℝ) :
    Id.run (chebyshevSemiIterativeStep pure (fun r => pure (Minv *ᵥ r)) A b β tol
        (k, cp, c, yp, y, r, false)) =
      if Real.sqrt (r ⬝ᵥ r) ≤ tol then (k, cp, c, yp, y, r, true) else
        (k + 1, c, 2 / β * c - cp, y,
          yp + (1 + cp / (2 / β * c - cp)) • (y + Minv *ᵥ r - yp),
          b - A *ᵥ (yp + (1 + cp / (2 / β * c - cp)) • (y + Minv *ᵥ r - yp)), false) := by
  have h : Id.run (chebyshevSemiIterativeStep pure (fun r => pure (Minv *ᵥ r)) A b β tol
      (k, cp, c, yp, y, r, false)) =
      if Real.sqrt (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_1 pure r r)) ≤ tol then
        (k, cp, c, yp, y, r, true) else
        (k + 1, c, 2 / β * c - cp, y,
          Id.run (chebyshevCombine pure yp y (Minv *ᵥ r) (1 + cp / (2 / β * c - cp))),
          Id.run (Chapter01.vecSub pure b (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A
            (Id.run (chebyshevCombine pure yp y (Minv *ᵥ r) (1 + cp / (2 / β * c - cp)))) 0))),
          false) := rfl
  rw [h, GolubVanLoan.Chapter01.algorithm_1_1_1_spec, chebyshevCombine_id,
    GolubVanLoan.Chapter01.algorithm_1_1_3_spec, Chapter01.vecSub_spec, zero_add]

/-- The values $c_j(1/\beta)$ of the Chebyshev polynomials. -/
private noncomputable def chebC (β : ℝ) (j : ℕ) : ℝ := (Chebyshev.T ℝ j).eval (1 / β)

/-- The three-term recurrence $c_{j+2}(1/\beta) = (2/\beta) c_{j+1}(1/\beta) - c_j(1/\beta)$.

**Reading.** Recurrence under total division for every beta.
-/
private theorem chebC_add_two (β : ℝ) (j : ℕ) :
    chebC β (j + 2) = 2 / β * chebC β (j + 1) - chebC β j := by
  have h := Chebyshev.T_add_two ℝ (j : ℤ)
  simp only [chebC]
  push_cast
  rw [h, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat]
  ring

/-- $c_j(1/\beta) \ge 1$ when $0 < \beta < 1$. -/
private theorem one_le_chebC {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (j : ℕ) : 1 ≤ chebC β j :=
  Chebyshev.one_le_eval_T (by rw [le_div_iff₀ hβ0]; linarith) j

/-- The vectors $c_j(G/\beta) e$. -/
private noncomputable def chebV (G : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (e : Fin n → ℝ) (j : ℕ) :
    Fin n → ℝ :=
  Polynomial.aeval G ((Chebyshev.T ℝ j).comp (C (1 / β) * X)) *ᵥ e

/-- The three-term recurrence of the vectors $c_j(G/\beta) e$. -/
private theorem chebV_add_two (G : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (e : Fin n → ℝ) (j : ℕ) :
    chebV G β e (j + 2) = (2 / β) • (G *ᵥ chebV G β e (j + 1)) - chebV G β e j := by
  have h := Chebyshev.T_add_two ℝ (j : ℤ)
  simp only [chebV]
  push_cast
  rw [h]
  simp only [sub_comp, mul_comp, ofNat_comp, X_comp, map_sub, map_mul, aeval_C,
    aeval_X, Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [map_natCast, show ((2 : ℕ) : Matrix (Fin n) (Fin n) ℝ) = (2 : ℝ) • 1 by
    rw [Nat.cast_ofNat, two_smul, one_add_one_eq_two]]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  module

/-- $p_j(G) e = c_j(1/\beta)^{-1} c_j(G/\beta) e$. -/
private theorem aeval_chebyshevSymmetricPoly (G : Matrix (Fin n) (Fin n) ℝ) (β : ℝ)
    (e : Fin n → ℝ) (j : ℕ) :
    Polynomial.aeval G (chebyshevSymmetricPoly β j) *ᵥ e = (chebC β j)⁻¹ • chebV G β e j := by
  simp only [chebyshevSymmetricPoly, chebV, chebC, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec]

/-- The scalar identity behind the three-term recurrence of the Chebyshev method. -/
private theorem cheb_combine {β a b c ω : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hrec : c = 2 / β * b - a) (hω : ω = 1 + a / c) (u w : Fin n → ℝ) :
    (1 - ω) • (a⁻¹ • u) + ω • (b⁻¹ • w) = c⁻¹ • ((2 / β) • w - u) := by
  have hca : c + a = 2 / β * b := by linarith
  have h1 : (1 - ω) * a⁻¹ = -c⁻¹ := by
    rw [hω, show (1 : ℝ) - (1 + a / c) = -(a / c) by ring, neg_mul, div_mul_eq_mul_div,
      mul_inv_cancel₀ ha, one_div]
  have h2 : ω * b⁻¹ = c⁻¹ * (2 / β) := by
    calc ω * b⁻¹ = (c + a) / c * b⁻¹ := by rw [hω, add_div, div_self hc]
      _ = 2 / β * b / c * b⁻¹ := by rw [hca]
      _ = c⁻¹ * (2 / β) := by
        rw [div_mul_eq_mul_div, mul_assoc, mul_inv_cancel₀ hb, mul_one, div_eq_inv_mul]
  rw [smul_smul, smul_smul, h1, h2]
  module

/-- **Section 11.2.8** of [golub2013matrix], the exact semantics of the Chebyshev semi-iterative
method. Let $A = M - N$ be a splitting of $A \in \mathbb{R}^{n \times n}$ with $M$ nonsingular,
let $G = M^{-1} N$, let $Ax = b$, and let $0 < \beta < 1$. Run
`GolubVanLoan.Chapter11.chebyshevSemiIterative` in exact arithmetic, with the solve $M^{-1}$,
from $x^{(0)}$, with any tolerance and any fuel. If the final state has the counter $k$ and the
iterate $y^{(k)}$, then
$$y^{(k)} - x = p_k(G) (x^{(0)} - x), \qquad p_k(z) = \frac{c_k(z/\beta)}{c_k(1/\beta)}.$$

The polynomial $p_k$ is `GolubVanLoan.Chapter11.chebyshevSymmetricPoly`, the case
$\alpha = -\beta$ of the polynomial of `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le`
(`GolubVanLoan.Chapter11.chebyshevSymmetricPoly_eq`). So the bound there applies; see
`GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le'`.

**Reading.** Vector polynomial identity for actual finite attained count, with 0<beta<1.
-/
theorem chebyshevSemiIterative_spec {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (tol : ℝ) (fuel : ℕ) :
    let st := Id.run (chebyshevSemiIterative pure (fun r => pure (s.m⁻¹ *ᵥ r)) A s.n b x₀ β tol
      fuel)
    st.2.2.2.2.1 - x =
      Polynomial.aeval s.iterationOperator (chebyshevSymmetricPoly β st.1) *ᵥ (x₀ - x) := by
  intro st
  set G := s.iterationOperator
  set e := x₀ - x
  have hCpos : ∀ j, chebC β j ≠ 0 := fun j => by linarith [one_le_chebC hβ0 hβ1 j]
  -- the invariant
  let Inv : ℕ × ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × Bool → Prop := fun st =>
    ∃ j, st.1 = j + 1 ∧ st.2.1 = chebC β j ∧ st.2.2.1 = chebC β (j + 1) ∧
      st.2.2.2.1 - x = (chebC β j)⁻¹ • chebV G β e j ∧
      st.2.2.2.2.1 - x = (chebC β (j + 1))⁻¹ • chebV G β e (j + 1) ∧
      st.2.2.2.2.2.1 = b - A *ᵥ st.2.2.2.2.1
  have hstep : ∀ st, Inv st → Inv (Id.run
      (chebyshevSemiIterativeStep pure (fun r => pure (s.m⁻¹ *ᵥ r)) A b β tol st)) := by
    rintro ⟨k, cp, c, yp, y, r, d⟩ ⟨j, hk, hcp, hc, hyp, hy, hr⟩
    dsimp only at hk hcp hc hyp hy hr
    cases d with
    | true => exact ⟨j, hk, hcp, hc, hyp, hy, hr⟩
    | false =>
      rw [chebyshevSemiIterativeStep_id]
      split_ifs
      · exact ⟨j, hk, hcp, hc, hyp, hy, hr⟩
      · have hc' : 2 / β * c - cp = chebC β (j + 2) := by rw [hcp, hc, chebC_add_two]
        refine ⟨j + 1, by rw [hk], hc, hc', hy, ?_, rfl⟩
        dsimp only
        rw [hc']
        have hz : y + s.m⁻¹ *ᵥ r - x = G *ᵥ (y - x) := by
          rw [hr, ← Stationary.Splitting.mulVecStep_eq_add_inv_mulVec]
          exact mulVecStep_sub s hx y
        have e1 : yp + (1 + cp / chebC β (j + 2)) • (y + s.m⁻¹ *ᵥ r - yp) - x =
            (1 - (1 + cp / chebC β (j + 2))) • (yp - x) +
              (1 + cp / chebC β (j + 2)) • (y + s.m⁻¹ *ᵥ r - x) := by
          module
        rw [e1, hz, hyp, hy, Matrix.mulVec_smul, hcp, chebV_add_two]
        exact cheb_combine (hCpos j) (hCpos (j + 1)) (hCpos (j + 2))
          (chebC_add_two β j) rfl _ _
  have hinv : ∀ (l : List ℕ) st, Inv st → Inv (l.foldl (fun st _ => Id.run
      (chebyshevSemiIterativeStep pure (fun r => pure (s.m⁻¹ *ᵥ r)) A b β tol st)) st) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons a l ih => exact fun st h => ih _ (hstep st h)
  have hinit : Inv (1, 1, 1 / β, x₀, s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀),
      b - A *ᵥ (s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀)), false) := by
    refine ⟨0, rfl, ?_, ?_, ?_, ?_, rfl⟩
    · simp [chebC]
    · simp [chebC]
    · simp [chebC, chebV, e]
    · have h1 : s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀) = s.mulVecStep b x₀ := by
        change _ = s.m⁻¹ *ᵥ (s.n *ᵥ x₀ + b); rw [add_comm]
      dsimp only
      rw [h1, mulVecStep_sub s hx]
      simp only [chebV, chebC, zero_add, Nat.cast_one, Chebyshev.T_one, X_comp, eval_X,
        map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_mulVec, smul_smul]
      rw [one_div, inv_inv, mul_inv_cancel₀ hβ0.ne', one_smul]
  have hst : st = (List.range fuel).foldl (fun st _ => Id.run
      (chebyshevSemiIterativeStep pure (fun r => pure (s.m⁻¹ *ᵥ r)) A b β tol st))
      (1, 1, 1 / β, x₀, s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀),
        b - A *ᵥ (s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀)), false) := by
    have h : st = (List.range fuel).foldl (fun st _ => Id.run
        (chebyshevSemiIterativeStep pure (fun r => pure (s.m⁻¹ *ᵥ r)) A b β tol st))
        (1, 1, 1 / β, x₀,
          s.m⁻¹ *ᵥ Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure s.n x₀ b),
          Id.run (Chapter01.vecSub pure b (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A
            (s.m⁻¹ *ᵥ Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure s.n x₀ b)) 0))),
          false) := List.idRun_foldlM
    rw [h, GolubVanLoan.Chapter01.algorithm_1_1_3_spec, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
      Chapter01.vecSub_spec, zero_add]
  have hfin := hinv (List.range fuel) _ hinit
  rw [← hst] at hfin
  obtain ⟨j, hk, -, -, -, hy, -⟩ := hfin
  rw [hk, aeval_chebyshevSymmetricPoly]
  exact hy

/-- For $\beta \ne 0$, the polynomial $c_k(z/\beta)/c_k(1/\beta)$ is the polynomial
`GolubVanLoan.Chapter11.chebyshevSemiIterativePoly` at $\alpha = -\beta$, because
$-1 + 2(z + \beta)/(2\beta) = z/\beta$ and $\mu = 1/\beta$. -/
theorem chebyshevSymmetricPoly_eq {β : ℝ} (hβ : β ≠ 0) (k : ℕ) :
    chebyshevSymmetricPoly β k = chebyshevSemiIterativePoly (-β) β k := by
  have hb2 : β - -β = 2 * β := by ring
  have h1 : -1 + 2 * (1 - -β) / (β - -β) = 1 / β := by
    rw [hb2]; field_simp; ring
  have h2 : 2 / (β - -β) = 1 / β := by
    rw [hb2]; field_simp
  have h3 : -1 - 2 * -β / (β - -β) = 0 := by
    rw [hb2]; field_simp; ring
  rw [chebyshevSemiIterativePoly, h1, h2, h3, C_0, add_zero, chebyshevSymmetricPoly]

/-- The Chebyshev bound of §11.2.8 of [golub2013matrix] for the program. Let $A = M - N$ be a
splitting of $A \in \mathbb{R}^{n \times n}$ with $M$ nonsingular whose iteration matrix $G$ is
symmetric with eigenvalues in $[-\beta, \beta]$, where $0 < \beta < 1$, and let $Ax = b$. If the
exact run of `GolubVanLoan.Chapter11.chebyshevSemiIterative` from $x^{(0)}$, with any tolerance
and any fuel, ends with the counter $k$ and the iterate $y^{(k)}$, then
$$\|y^{(k)} - x\|_2 \le \frac{\|x - x^{(0)}\|_2}{|c_k(1/\beta)|}.$$
This is `GolubVanLoan.Chapter11.chebyshevSemiIterative_norm_le` at $\alpha = -\beta$, through
`GolubVanLoan.Chapter11.chebyshevSemiIterative_spec` and
`GolubVanLoan.Chapter11.chebyshevSymmetricPoly_eq`.

**Reading.** Bound for actual attained finite iterate under symmetric spectral enclosure.
-/
theorem chebyshevSemiIterative_norm_le' {A : Matrix (Fin n) (Fin n) ℝ}
    (s : Stationary.Splitting A) (hG : s.iterationOperator.IsHermitian) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hGab : ∀ i, hG.eigenvalues i ∈ Set.Icc (-β) β) {b x : Fin n → ℝ}
    (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) (tol : ℝ) (fuel : ℕ) :
    let st := Id.run (chebyshevSemiIterative pure (fun r => pure (s.m⁻¹ *ᵥ r)) A s.n b x₀ β tol
      fuel)
    ‖WithLp.toLp 2 (st.2.2.2.2.1 - x)‖ ≤
      ‖WithLp.toLp 2 (x - x₀)‖ / |(Chebyshev.T ℝ st.1).eval (1 / β)| := by
  intro st
  have hspec : st.2.2.2.2.1 - x =
      Polynomial.aeval s.iterationOperator (chebyshevSymmetricPoly β st.1) *ᵥ (x₀ - x) :=
    chebyshevSemiIterative_spec s hx x₀ hβ0 hβ1 tol fuel
  have hμ : -1 + 2 * (1 - -β) / (β - -β) = 1 / β := by
    rw [show β - -β = 2 * β by ring]; field_simp; ring
  have h2 := (chebyshevSemiIterative_norm_le s hG (by linarith) (by linarith) hβ1 hGab hx x₀
    st.1).2.1
  rw [hμ] at h2
  rw [hspec, chebyshevSymmetricPoly_eq hβ0.ne', ← Matrix.toEuclideanLin_toLp,
    Matrix.toEuclideanLin_aeval]
  set p := chebyshevSemiIterativePoly (-β) β st.1
  have hB := Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin hG hGab
  have hle := hB.norm_aeval_map_apply_le p (WithLp.toLp 2 (x₀ - x))
  rw [show p.map (algebraMap ℝ ℝ) = p by rw [Algebra.algebraMap_self, Polynomial.map_id]] at hle
  refine hle.trans ?_
  have hS : sSup ((fun t => |p.eval t|) '' Set.Icc (-β) β) ≤
      1 / |(Chebyshev.T ℝ st.1).eval (1 / β)| :=
    csSup_le ((Set.nonempty_Icc.2 (by linarith)).image _) (Set.forall_mem_image.2 h2)
  have hn : ‖WithLp.toLp 2 (x₀ - x)‖ = ‖WithLp.toLp 2 (x - x₀)‖ := by
    rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
  calc sSup ((fun t => |p.eval t|) '' Set.Icc (-β) β) * ‖WithLp.toLp 2 (x₀ - x)‖
      ≤ 1 / |(Chebyshev.T ℝ st.1).eval (1 / β)| * ‖WithLp.toLp 2 (x₀ - x)‖ :=
        mul_le_mul_of_nonneg_right hS (norm_nonneg _)
    _ = _ := by rw [hn, one_div, inv_mul_eq_div]

end GolubVanLoan.Chapter11
