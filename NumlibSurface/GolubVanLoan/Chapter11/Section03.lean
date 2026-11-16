/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Sturm
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.NormalEquations
import Numlib.Krylov.Singular
import Numlib.LinearAlgebra.Matrix.LU
import Numlib.Projection.OneDimensional
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter04.Section03
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub and Van Loan, Section 11.3: The conjugate gradient method

This module formalizes §11.3 of [golub2013matrix], the conjugate gradient (CG) method for a
symmetric positive definite system $Ax = b$, $A \in \mathbb{R}^{n \times n}$. Solving the system is
minimizing $\phi(x) = \tfrac12 x^TAx - x^Tb$, and the error is measured in the $A$-norm
$\|v\|_A = \sqrt{v^TAv}$, with $x_* = A^{-1}b$ and $\kappa_2(A) =
\lambda_{\max}(A)/\lambda_{\min}(A)$. The module treats steepest descent with exact line search and
its rate $(1 - 1/\kappa_2(A))^{1/2}$ per step (Algorithm 11.3.1), the minimization of $\phi$ over
nested subspaces and the choice of the Krylov subspaces $\mathcal{K}(A, r_0, k) =
\operatorname{span}\{r_0, Ar_0, \dots, A^{k-1}r_0\}$, CG as the Galerkin method on these subspaces
(Theorems 11.3.1 and 11.3.3, Corollary 11.3.2), CG derived from the Lanczos process and an $LDL^T$
factorization of the tridiagonal $T_k$ (Algorithm 11.3.2, Theorems 11.3.4–11.3.5), the
Hestenes–Stiefel form (Algorithm 11.3.3) and its practical loop (11.3.26), error estimates, and CG
on the normal equations (CGNR and CGNE, Figure 11.3.1). The grade $k_*$ of $r_0 = b - Ax_0$ is the
dimension of $\operatorname{span}\{A^ir_0 : i \ge 0\}$, the smallest $A$-invariant subspace that
contains $r_0$; exact CG reaches $x_*$ after $k_*$ steps.

The proofs specialize the backbone modules `Numlib.Krylov.CG`, `Numlib.Krylov.Lanczos`,
`Numlib.Krylov.Arnoldi`, `Numlib.Krylov.Hessenberg`, `Numlib.Krylov.NormalEquations`,
`Numlib.Krylov.Convergence.CG`, `Numlib.Projection.OneDimensional` and
`Numlib.Analysis.InnerProductSpace.Energy`, and the programs reuse Algorithms 1.1.1–1.1.3, Algorithm
4.3.6 and Algorithm 10.1.1.

## Main definitions

* Algorithm 11.3.1, `GolubVanLoan.Chapter11.algorithm_11_3_1`: steepest descent with exact line
  search.
* Equation (11.3.14), `GolubVanLoan.Chapter11.preliminaryCG`: the preliminary CG method, built on
  the Lanczos loop of Algorithm 10.1.1 and the tridiagonal solver of Algorithm 4.3.6.
* Equation (11.3.15), `GolubVanLoan.Chapter11.ldlTridiag`: the recurrence for the $LDL^T$ factors of
  a symmetric tridiagonal matrix.
* Equation (11.3.16), `GolubVanLoan.Chapter11.cgLDLv`: the vector $v_k$ with
  $L_kD_kv_k = \beta_0e_1$.
* Equation (11.3.17), `GolubVanLoan.Chapter11.cgLDLC`: the matrix $C_k$ with $C_kL_k^T = Q_k$.
* Algorithm 11.3.2, `GolubVanLoan.Chapter11.algorithm_11_3_2`: conjugate gradients, Lanczos version.
* Algorithm 11.3.3, `GolubVanLoan.Chapter11.algorithm_11_3_3`: conjugate gradients, Hestenes–Stiefel
  version.
* Equation (11.3.26), `GolubVanLoan.Chapter11.practicalCG`: the practical CG loop with the stopping
  test $\|r\|_2 \le \mathrm{tol} \cdot \|b\|_2$.
* Figure 11.3.1, `GolubVanLoan.Chapter11.cgnr` and `GolubVanLoan.Chapter11.cgne`: the CGNR and CGNE
  loops.

## Main results

* Equation (11.3.2), `GolubVanLoan.Chapter11.equation_11_3_2`: $x$ solves $Ax = b$ if and only if
  $x$ minimizes $\phi$.
* §11.3.1, `GolubVanLoan.Chapter11.gradient_energyFunctional`: $\phi$ is convex with gradient
  $Ax - b$.
* Equation (11.3.5), `GolubVanLoan.Chapter11.equation_11_3_5`:
  $\phi(x) = \tfrac12\|x - x_*\|_A^2 + \phi(x_*)$ and $\phi(x_*) = -\tfrac12 b^TA^{-1}b$.
* Equation (11.3.6), `GolubVanLoan.Chapter11.steepestDescent_mu_eq`: the exact line search along
  $-g_c$ has the unique minimizer $\mu_c = g_c^Tg_c/g_c^TAg_c$.
* Equation (11.3.7), `GolubVanLoan.Chapter11.equation_11_3_7`: the decrease of $\phi$ in one
  steepest-descent step.
* Equation (11.3.8), `GolubVanLoan.Chapter11.equation_11_3_8`: the decrease of $\phi$ in terms of
  $\kappa_c$.
* §11.3.2, `GolubVanLoan.Chapter11.kappa_c_le`: $\kappa_c \le \kappa_2(A)$.
* Equation (11.3.9), `GolubVanLoan.Chapter11.equation_11_3_9`: one steepest-descent step reduces
  $\|x - x_*\|_A^2$ by the factor $1 - 1/\kappa_2(A)$.
* §11.3.2, `GolubVanLoan.Chapter11.steepestDescent_rate`: steepest descent converges globally, with
  rate $(1 - 1/\kappa_2(A))^{k/2}$.
* Algorithm 11.3.1, `GolubVanLoan.Chapter11.algorithm_11_3_1_spec`: in exact arithmetic the
  algorithm makes steepest-descent steps, and for $\tau > 0$ it stops with $\|Ax - b\|_2 \le \tau$.
* Equations (11.3.10)–(11.3.11), `GolubVanLoan.Chapter11.equation_11_3_11`: minimization over nested
  subspaces is at least as good as steepest descent, decreases $\phi$, and solves the system when
  the subspace is $\mathbb{R}^n$.
* §11.3.3, `GolubVanLoan.Chapter11.gradient_mem_krylov`: the Krylov subspaces contain the next
  gradient and the steepest-descent point.
* Equations (11.3.12)–(11.3.13), `GolubVanLoan.Chapter11.equation_11_3_13`: the Lanczos relation
  $AQ_k = Q_kT_k + r_ke_k^T$.
* §11.3.4, `GolubVanLoan.Chapter11.lanczos_tridiag_posDef`: $T_k$ is positive definite below the
  grade.
* §11.3.4, `GolubVanLoan.Chapter11.cg_lanczos_coordinates`: $x_0 + Q_ky$ is the Galerkin iterate if
  and only if $T_ky = \beta_0e_1$.
* Equation (11.3.14), `GolubVanLoan.Chapter11.equation_11_3_14`: in exact arithmetic the preliminary
  CG method computes the Galerkin iterates and stops at the grade.
* Theorem 11.3.1, `GolubVanLoan.Chapter11.theorem_11_3_1`: the preliminary CG method terminates
  after $k_*$ steps with $x_{k_*} = x_*$.
* Corollary 11.3.2, `GolubVanLoan.Chapter11.corollary_11_3_2`: if $A = I + UDU^T$ with
  $U \in \mathbb{R}^{n \times r}$, CG needs at most $r + 1$ steps.
* Theorem 11.3.3, `GolubVanLoan.Chapter11.theorem_11_3_3`: one CG step reduces $\|x - x_*\|_A$ by
  the factor $(1 - 1/\kappa_2(A))^{1/2}$.
* Equation (11.3.15), `GolubVanLoan.Chapter11.equation_11_3_15`: the recurrence gives
  $T_k = L_kD_kL_k^T$.
* Equation (11.3.18), `GolubVanLoan.Chapter11.equation_11_3_18`: $x_0 + Q_ky = x_0 + C_k(L_k^Ty)$.
* Equation (11.3.19), `GolubVanLoan.Chapter11.equation_11_3_19`: the entries $\nu_i$ solve
  $L_kD_kv_k = \beta_0e_1$, and $v_{k+1} = [v_k; \nu_{k+1}]$.
* Equation (11.3.20), `GolubVanLoan.Chapter11.equation_11_3_20`: the recurrence for $\nu_k$.
* Equations (11.3.21)–(11.3.22), `GolubVanLoan.Chapter11.equation_11_3_21`:
  $C_{k+1} = [C_k | c_{k+1}]$, and the columns solve $C_kL_k^T = Q_k$.
* Equation (11.3.22), `GolubVanLoan.Chapter11.equation_11_3_22`: the recurrence for $c_k$.
* §11.3.5, `GolubVanLoan.Chapter11.cgLDL_x_succ`: $x_k = x_{k-1} + \nu_kc_k$.
* Algorithm 11.3.2, `GolubVanLoan.Chapter11.algorithm_11_3_2_spec`: in exact arithmetic the
  algorithm computes the CG iterates, with its quantities identified with the Lanczos and the CG
  quantities.
* Theorem 11.3.4, `GolubVanLoan.Chapter11.theorem_11_3_4`: the gradients of Algorithm 11.3.2 are
  mutually orthogonal, and $g_k = \nu_kr_k$.
* Theorem 11.3.5, `GolubVanLoan.Chapter11.theorem_11_3_5`: the directions $c_i$ are $A$-conjugate,
  with $c_j^TAc_j = d_j$.
* Equation (11.3.23), `GolubVanLoan.Chapter11.equation_11_3_23`: the recurrence
  $p_k = g_{k-1} + \tau_{k-1}p_{k-1}$ of the Hestenes–Stiefel directions, which are multiples of the
  $c_k$.
* Equations (11.3.24)–(11.3.25), `GolubVanLoan.Chapter11.equation_11_3_24`: the formula for
  $\tau_{k-1}$ and $p_k^TAg_{k-1} = p_k^TAp_k$.
* Equation (11.3.25), `GolubVanLoan.Chapter11.equation_11_3_25`: $p_k^TAg_{k-1} = p_k^TAp_k$.
* §11.3.7, `GolubVanLoan.Chapter11.hestenesStiefel_coeffs`: the Hestenes–Stiefel formulas for $x_k$,
  $\mu_k$ and $\tau_{k-1}$.
* Algorithm 11.3.3, `GolubVanLoan.Chapter11.algorithm_11_3_3_spec`: in exact arithmetic the
  algorithm computes the CG iterates and stops at the grade with $Ax = b$.
* Equation (11.3.26), `GolubVanLoan.Chapter11.equation_11_3_26`: in exact arithmetic the practical
  loop computes the CG iterates and stops with $\|b - Ax\|_2 \le \mathrm{tol} \cdot \|b\|_2$.
* §11.3.8, `GolubVanLoan.Chapter11.cg_relativeError_le`: a small residual gives $\|x_c - x_*\|_2 \le
  \mathrm{tol} \cdot \kappa_2(A)\|x_*\|_2$.
* Equation (11.3.27), `GolubVanLoan.Chapter11.equation_11_3_27`: the bound $\|x_* - x_k\|_A \le
  2\|x_* - x_0\|_A((\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1))^k$.
* §11.3.9, `GolubVanLoan.Chapter11.energyFunctional_normalEquations`: the quadratics of $A^TA$ and
  $BB^T$ in terms of residual norms.
* Equation (11.3.28), `GolubVanLoan.Chapter11.equation_11_3_28`: CGNR minimizes $\|b - Ax\|_2$ over
  $x_0 + \mathcal{K}(A^TA, A^Tr_0, k)$.
* §11.3.9, `GolubVanLoan.Chapter11.cgne_isMinError`: CGNE minimizes $\|x - x_*\|_2$ over the same
  affine space.
* §11.3.9, remark after Figure 11.3.1, `GolubVanLoan.Chapter11.cgnr_isMinResidual_of_injective` and
  `GolubVanLoan.Chapter11.cgne_isMinError_of_injective_transpose`: the two optimality properties for
  a rectangular $A$ of full column rank, and of full row rank with a consistent system.
* Figure 11.3.1, `GolubVanLoan.Chapter11.cgnr_spec` and `GolubVanLoan.Chapter11.cgne_spec`: in exact
  arithmetic the two loops compute the backbone CGNR and CGNE iterates.

## Notation

* `𝔼 n`: the Euclidean space `EuclideanSpace ℝ (Fin n)` (local notation).

## Conventions

* The matrix $A$ is `A : Matrix (Fin n) (Fin n) ℝ`, and "symmetric positive definite" is `A.PosDef`.
  Statements about subspaces, the $A$-norm or the Krylov iteration are made for the operator
  `Matrix.toEuclideanLin A` on `EuclideanSpace ℝ (Fin n)`; vectors move between `Fin n → ℝ` and
  `EuclideanSpace ℝ (Fin n)` by `WithLp.toLp 2` and `WithLp.ofLp`.
* The function $\phi$ is `energyFunctional (Matrix.toEuclideanLin A) b`, and $\|v\|_A$ is
  `energyNorm (Matrix.toEuclideanLin A) v`. The condition number $\kappa_2(A)$ is
  `NormedRing.condNumber A` for the scoped matrix $2$-norm `Matrix.Norms.L2Operator`; it equals the
  eigenvalue ratio by `Matrix.PosDef.condNumber_l2_eq_div_eigenvalues`.
* The source's gradient is $g = Ax - b$ and its residual is $r = b - Ax$. The backbone's CG state
  `CG.iterate` carries the residual. Its iterate $x_k$ and residual $r_k$ agree with those of the
  source, and the Hestenes–Stiefel $p_k$ and $\mu_k$ of the source ($k \ge 1$) are the backbone's
  direction $p_{k-1}$ and step length `CG.alpha` at step $k - 1$.
* The Lanczos quantities $q_j$, $\alpha_j$, $\beta_j$ of the source ($j \ge 1$) are the backbone's
  `Arnoldi.vec T r₀ (j - 1)`, `Lanczos.alpha T r₀ (j - 1)` and `Lanczos.beta T r₀ (j - 1)` for
  `T := Matrix.toEuclideanLin A`. The grade $k_*$ is `Krylov.grade`.

## Implementation notes

* Algorithms 11.3.1, 11.3.2 and 11.3.3, the loops (11.3.14) and (11.3.26), and the two columns of
  Figure 11.3.1 are monadic programs over a rounding hook `rnd : ℝ → M ℝ`, in the operation order of
  the source, built from Algorithms 1.1.1 (dot product), 1.1.2 (saxpy) and 1.1.3 (gaxpy). A `while`
  loop is a `List.foldlM` over `List.range fuel` with a `done` flag, and `fuel` is the last
  argument. The source analyses no rounding error in this section (§11.3.8 says only that
  orthogonality is lost), so each program has only an exact specification: its exact run (`M := Id`,
  `rnd := pure`) is the backbone recurrence `CG.iterate`, `Krylov.CGNR.iterate`,
  `Krylov.CGNE.iterate` or `Projection.steepestDescentStep`.
* Algorithm 11.3.3 and (11.3.26) share the body `GolubVanLoan.Chapter11.cgUpdate` and its exact
  specification `GolubVanLoan.Chapter11.cgUpdate_run`.
* Algorithm 11.3.2 is identified with the Hestenes–Stiefel CG through the backbone's dictionary
  between the Lanczos and the CG coefficients (`CG.arnoldi_vec_eq`, `CG.lanczos_alpha_zero_eq`,
  `CG.lanczos_alpha_succ_eq`, `CG.lanczos_beta_eq`). After $k = i + 1$ steps its $q_k$, $r_k$,
  $\alpha_k$ and $\beta_k$ are the Lanczos quantities of $r_0$, its pivot $d_k$ is the $LDL^T$ pivot
  of $T_k$ and equals $1/\alpha^{CG}_i$, $\nu_k = (-1)^i\|r_i\|\alpha^{CG}_i$ and
  $c_k = (-1)^i\|r_i\|^{-1}p_i$, so that the update $x_k = x_{k-1} + \nu_kc_k$ is the CG update
  $x_{i+1} = x_i + \alpha^{CG}_ip_i$.
* The $LDL^T$ recurrence (11.3.15) is the backbone's Thomas algorithm (`Matrix.thomasAlpha`,
  `Matrix.isLU_tridiagonal_thomas`) for the symmetric tridiagonal matrix.
* The loop (11.3.14) reuses the Lanczos loop of Algorithm 10.1.1 unchanged. That loop normalizes its
  first vector again by its $\beta_0 = 1$, so in the rounded model $q_1 = r_0/\beta_0$ gets one
  rounding per entry more than in the source.

## Deviations from the source

* **Corollary 11.3.2** (generalization). The source assumes that $D$ is symmetric and that $r < n$;
  neither is needed. See `GolubVanLoan.Chapter11.corollary_11_3_2`.
* **Equation (11.3.14)** (correction). The source prints $x_k = Q_ky_k$, which holds only for
  $x_0 = 0$; the method computes $x_k = x_0 + Q_ky_k$. See `GolubVanLoan.Chapter11.preliminaryCG`.
* **Equation (11.3.19)** (typo). The source prints the garbled
  $v_k = [\nu_1; \dots; \nu_{k-1}/\nu_k]$ for $v_k = [v_{k-1}; \nu_k]$. See
  `GolubVanLoan.Chapter11.equation_11_3_19`.
* **Theorem 11.3.4** (generalization). The orthogonality $g_i^Tg_j = 0$ holds for $0 \le i < j$, not
  only for $1 \le i < j$. See `GolubVanLoan.Chapter11.theorem_11_3_4`.
* **Theorem 11.3.5** (typo). The source prints the range $1 \le i < j \le k$, which excludes the
  case $i = j$ of its own statement; the range is $1 \le i, j \le k$. See
  `GolubVanLoan.Chapter11.theorem_11_3_5`.

## Not formalized

* **The operation counts and storage of §11.3.5 and §11.3.8** (the "13n flops" and the four arrays).
  Operation counts are out of scope for the library.
* **The uniqueness claim of §11.3.3** that the only way to satisfy the requirement of (11.3.11) is
  $S_k = \mathcal{K}(A, g_0, k)$. It has no precise statement.
* **The Problems of §11.3.** Problems are out of scope for the library.
* **The Notes and References of §11.3.** They are out of scope for the library.
-/

open Matrix Krylov Filter Topology
open scoped RealInnerProductSpace

namespace GolubVanLoan.Chapter11

/-- The Euclidean space $\mathbb{R}^n$, `EuclideanSpace ℝ (Fin n)`, on which the Krylov statements
of this module are made. -/
local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The backbone CG states `CG.iterate` of $A$, for the data $b$ and $x_0$ given in coordinates. -/
local notation "cgIt" A:max b:max x₀:max j:max =>
  CG.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) j

/-- The initial residual $r_0 = b - Ax_0$ in `EuclideanSpace ℝ (Fin n)`, for the data $b$ and $x_0$
given in coordinates. -/
local notation "cgR" A:max b:max x₀:max =>
  WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)

/-! ### Helpers: matrices acting on Euclidean space -/

section Helpers

/-- The Euclidean inner product of two coordinate vectors $u$ and $v$ is their dot product $u^Tv$.
-/
private theorem inner_toLp (u v : Fin n → ℝ) :
    ⟪(WithLp.toLp 2 u : 𝔼 n), WithLp.toLp 2 v⟫ = u ⬝ᵥ v :=
  EuclideanSpace.inner_toLp_toLp_real u v

/-- For a coordinate vector $u$, $\sqrt{u^Tu} = \|u\|_2$. -/
private theorem sqrt_dotProduct_self (u : Fin n → ℝ) :
    √(u ⬝ᵥ u) = ‖(WithLp.toLp 2 u : 𝔼 n)‖ := by
  rw [← inner_toLp, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- For a coordinate vector $u$, $u^Tu = 0$ if and only if $u = 0$. -/
private theorem dotProduct_self_eq_zero_iff (u : Fin n → ℝ) : u ⬝ᵥ u = 0 ↔ u = 0 := by
  rw [← inner_toLp, inner_self_eq_zero, WithLp.toLp_eq_zero]

/-- For nonsingular $A$ and every $v \in \mathbb{R}^n$, $A^{-1}(Av) = v$. -/
private theorem inv_apply_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (v : 𝔼 n) :
    toEuclideanLin A⁻¹ (toEuclideanLin A v) = v := by
  have h := (isUnit_iff_isUnit_det A).1 hA
  simp only [toEuclideanLin_apply, mulVec_mulVec, nonsing_inv_mul _ h,
    one_mulVec, WithLp.toLp_ofLp]

/-- For nonsingular $A$ and every $v \in \mathbb{R}^n$, $A(A^{-1}v) = v$. -/
private theorem apply_inv_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (v : 𝔼 n) :
    toEuclideanLin A (toEuclideanLin A⁻¹ v) = v := by
  have h := (isUnit_iff_isUnit_det A).1 hA
  simp only [toEuclideanLin_apply, mulVec_mulVec, mul_nonsing_inv _ h,
    one_mulVec, WithLp.toLp_ofLp]

/-- For a symmetric positive definite $A$ with $n \ge 1$, there are numbers
$0 < \lambda_{\min} \le \lambda_{\max}$ with $\lambda_{\min}\|v\|^2 \le v^TAv \le
\lambda_{\max}\|v\|^2$ for all $v$ and $\kappa_2(A) = \lambda_{\max}/\lambda_{\min}$. -/
private theorem posDef_bounds {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) [Nonempty (Fin n)] :
    ∃ lmin lmax : ℝ, 0 < lmin ∧ lmin ≤ lmax ∧
      (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax ∧
      (open scoped Matrix.Norms.L2Operator in NormedRing.condNumber A) = lmax / lmin := by
  have hbddA : BddAbove (Set.range hA.1.eigenvalues) := (Set.finite_range _).bddAbove
  have hbddB : BddBelow (Set.range hA.1.eigenvalues) := (Set.finite_range _).bddBelow
  obtain ⟨imin, himin⟩ := exists_eq_ciInf_of_finite (f := hA.1.eigenvalues)
  refine ⟨⨅ i, hA.1.eigenvalues i, ⨆ i, hA.1.eigenvalues i, ?_, ?_, ?_, ?_⟩
  · rw [← himin]; exact hA.eigenvalues_pos imin
  · exact (ciInf_le hbddB imin).trans (le_ciSup hbddA imin)
  · exact hA.1.isSymmetricBoundedBy_toEuclideanLin fun i =>
      ⟨ciInf_le hbddB i, le_ciSup hbddA i⟩
  · exact hA.condNumber_l2_eq_div_eigenvalues

open scoped Matrix.Norms.L2Operator in
/-- For every matrix $M$ and vector $v$, $\|Mv\|_2 \le \|M\|_2\|v\|_2$. -/
private theorem norm_toEuclideanLin_apply_le (M : Matrix (Fin n) (Fin n) ℝ) (v : 𝔼 n) :
    ‖toEuclideanLin M v‖ ≤ ‖M‖ * ‖v‖ := by
  rw [l2_opNorm_eq_norm_toEuclideanLin]
  exact (LinearMap.toContinuousLinearMap (toEuclideanLin M)).le_opNorm v

/-- For $0 < \lambda_{\min} \le \lambda_{\max}$ and $\kappa = \lambda_{\max}/\lambda_{\min}$, the
Kantorovich factor satisfies $((\kappa - 1)/(\kappa + 1))^2 \le 1 - 1/\kappa$, so the
steepest-descent rate is better than the rate of the source. -/
private theorem kantorovich_sq_le {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax) :
    ((lmax - lmin) / (lmax + lmin)) ^ 2 ≤ 1 - 1 / (lmax / lmin) := by
  have hL : 0 < lmax := hl.trans_le hll
  rw [one_div_div, div_pow, div_le_iff₀ (by positivity),
    show 1 - lmin / lmax = (lmax - lmin) / lmax by field_simp, div_mul_eq_mul_div,
    le_div_iff₀ hL]
  nlinarith [mul_nonneg (sub_nonneg.2 hll) hl.le]

end Helpers

/-! ### §11.3.1: an optimization problem -/

section Optimization

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- For symmetric $A$, $g = Ax - b$ and every $\mu \in \mathbb{R}$, $\phi(x - \mu g) = \phi(x) - \mu
g^Tg + \tfrac12\mu^2 g^TAg$. -/
private theorem energyFunctional_sub_smul (hA : (toEuclideanLin A).IsSymmetric) {b x g : 𝔼 n}
    (hg : toEuclideanLin A x - b = g) (μ : ℝ) :
    energyFunctional (toEuclideanLin A) b (x - μ • g) =
      energyFunctional (toEuclideanLin A) b x - μ * ⟪g, g⟫ +
        μ ^ 2 * ⟪toEuclideanLin A g, g⟫ / 2 := by
  have h := energyFunctional_add_smul hA b x g (-μ)
  rw [show x - μ • g = x + (-μ) • g by rw [neg_smul, sub_eq_add_neg], h,
    show b - toEuclideanLin A x = -g by rw [← hg]; abel]
  simp only [inner_neg_left, RCLike.re_to_real, Real.norm_eq_abs, sq_abs]
  ring

/-- For positive definite $A$, the vector $A^{-1}b$ solves $Ax = b$. -/
private theorem apply_inv_eq (hA : A.PosDef) (b : 𝔼 n) :
    toEuclideanLin A (toEuclideanLin A⁻¹ b) = b :=
  apply_inv_apply hA.isUnit b

/-- **Equation (11.3.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b \in \mathbb{R}^n$, and let $\phi(x) = \tfrac12 x^TAx - x^Tb$. Then for
every $x \in \mathbb{R}^n$
$$Ax = b \iff \phi(x) \le \phi(y) \text{ for all } y \in \mathbb{R}^n.$$

The source states, in (11.3.1)–(11.3.3), that solving $Ax = b$ is equivalent to the problem
$\min \phi(x)$. The function $\phi$ is `energyFunctional (Matrix.toEuclideanLin A) b`. -/
theorem equation_11_3_2 (hA : A.PosDef) (b x : 𝔼 n) :
    toEuclideanLin A x = b ↔
      ∀ y, energyFunctional (toEuclideanLin A) b x ≤ energyFunctional (toEuclideanLin A) b y := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  constructor
  · intro hx y
    have h := hT.energyFunctional_sub_eq hx y
    have := sq_nonneg (energyNorm (toEuclideanLin A) (y - x))
    linarith
  · intro h
    have hs := apply_inv_eq hA b
    have h1 := hT.energyFunctional_sub_eq hs x
    have h2 := h (toEuclideanLin A⁻¹ b)
    have h3 : energyNorm (toEuclideanLin A) (x - toEuclideanLin A⁻¹ b) = 0 := by
      nlinarith [energyNorm_nonneg (toEuclideanLin A) (x - toEuclideanLin A⁻¹ b)]
    rw [hT.energyNorm_eq_zero_iff, sub_eq_zero] at h3
    rw [h3, hs]

/-- **Section 11.3.1** of [golub2013matrix], gradient and convexity of $\phi$. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and $b \in \mathbb{R}^n$. Then
$\phi(x) = \tfrac12 x^TAx - x^Tb$ has the gradient $\nabla\phi(x) = Ax - b$ at every $x$, and
$\phi$ is convex on $\mathbb{R}^n$.

The gradient is `HasGradientAt` for the Euclidean inner product. -/
theorem gradient_energyFunctional (hA : A.PosDef) (b : 𝔼 n) :
    (∀ x, HasGradientAt (energyFunctional (toEuclideanLin A) b) (toEuclideanLin A x - b) x) ∧
      ConvexOn ℝ Set.univ (energyFunctional (toEuclideanLin A) b) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  refine ⟨fun x => hasGradientAt_energyFunctional_of_finiteDimensional hT.isSymmetric b x,
    convex_univ, fun x _ y _ a c ha hc hac => ?_⟩
  -- `a φ x + c φ y − φ(a x + c y) = ½ a c ‖x − y‖²_A ≥ 0`
  have hsym : ⟪toEuclideanLin A y, x⟫ = ⟪toEuclideanLin A x, y⟫ := by
    rw [hT.isSymmetric y x, real_inner_comm]
  have hq : 0 ≤ ⟪toEuclideanLin A (x - y), x - y⟫ := by
    have := hT.isPositive.re_inner_nonneg_left (x - y)
    simpa only [RCLike.re_to_real] using this
  have hc' : c = 1 - a := by linarith
  subst hc'
  simp only [energyFunctional, RCLike.re_to_real, smul_eq_mul, map_add, map_smul, map_sub,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, conj_trivial] at hq ⊢
  rw [hsym] at hq ⊢
  nlinarith [mul_nonneg ha hc]

/-- **Equation (11.3.5)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, $b \in \mathbb{R}^n$ and $x_* = A^{-1}b$. Then for every
$x_c \in \mathbb{R}^n$
$$\phi(x_c) = \tfrac12\|x_c - x_*\|_A^2 + \phi(x_*), \qquad \phi(x_*) = -\tfrac12 b^TA^{-1}b.$$

The $A$-norm $\|v\|_A = \sqrt{v^TAv}$ is `energyNorm (Matrix.toEuclideanLin A) v`. -/
theorem equation_11_3_5 (hA : A.PosDef) (b x : 𝔼 n) :
    energyFunctional (toEuclideanLin A) b x =
        energyNorm (toEuclideanLin A) (x - toEuclideanLin A⁻¹ b) ^ 2 / 2 +
          energyFunctional (toEuclideanLin A) b (toEuclideanLin A⁻¹ b) ∧
      energyFunctional (toEuclideanLin A) b (toEuclideanLin A⁻¹ b) =
        -⟪b, toEuclideanLin A⁻¹ b⟫ / 2 := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  refine ⟨?_, ?_⟩
  · have h := hT.energyFunctional_sub_eq (apply_inv_eq hA b) x
    linarith
  · simp only [energyFunctional, apply_inv_eq hA b, RCLike.re_to_real]
    ring

end Optimization

/-! ### §11.3.2: steepest descent -/

section SteepestDescent

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Equation (11.3.6)** of [golub2013matrix] and the line after it. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $b, x_c \in \mathbb{R}^n$,
and let $g_c = Ax_c - b \neq 0$. A number $\mu_0$ minimizes $\mu \mapsto \phi(x_c - \mu g_c)$
over $\mathbb{R}$ if and only if
$$\mu_0 = \mu_c = \frac{g_c^Tg_c}{g_c^TAg_c},$$
and the point $x_c - \mu_cg_c$ is the steepest-descent step from $x_c$.

The steepest-descent step is `Projection.steepestDescentStep (Matrix.toEuclideanLin A) b x`, the
one-dimensional Galerkin step along the residual $r_c = -g_c$. -/
theorem steepestDescent_mu_eq (hA : A.PosDef) {b x g : 𝔼 n} (hg : toEuclideanLin A x - b = g)
    (hg0 : g ≠ 0) :
    (∀ μ₀ : ℝ, (∀ μ : ℝ, energyFunctional (toEuclideanLin A) b (x - μ₀ • g) ≤
        energyFunctional (toEuclideanLin A) b (x - μ • g)) ↔
        μ₀ = ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) ∧
      x - (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) • g =
        Projection.steepestDescentStep (toEuclideanLin A) b x := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hq : 0 < ⟪toEuclideanLin A g, g⟫ := by
    simpa only [RCLike.re_to_real] using hT.isCoercive.inner_self_pos hg0
  have hq' : ⟪g, toEuclideanLin A g⟫ = ⟪toEuclideanLin A g, g⟫ := real_inner_comm _ _
  have hquad := energyFunctional_sub_smul hT.isSymmetric hg
  -- `φ(x − μg) = φ(x − μ_c g) + ½ gᵀAg (μ − μ_c)²`
  have hsq : ∀ μ : ℝ, energyFunctional (toEuclideanLin A) b (x - μ • g) =
      energyFunctional (toEuclideanLin A) b (x - (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) • g) +
        ⟪toEuclideanLin A g, g⟫ / 2 * (μ - ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) ^ 2 := by
    intro μ
    rw [hquad, hquad, hq']
    field_simp
    ring
  refine ⟨fun μ₀ => ⟨fun h => ?_, fun h μ => ?_⟩, ?_⟩
  · have h1 := h (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫)
    rw [hsq μ₀] at h1
    have h2 : (μ₀ - ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) ^ 2 ≤ 0 := by
      have := mul_nonneg (div_nonneg hq.le zero_le_two)
        (sq_nonneg (μ₀ - ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫))
      nlinarith
    have h3 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
    linarith
  · rw [h, hsq μ]
    have := mul_nonneg (div_nonneg hq.le zero_le_two)
      (sq_nonneg (μ - ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫))
    linarith
  · have hr : b - toEuclideanLin A x = -g := by rw [← hg]; abel
    rw [Projection.steepestDescentStep, Projection.step1, hr, map_neg, inner_neg_neg,
      inner_neg_neg, smul_neg, ← sub_eq_add_neg]

/-- **Equation (11.3.7)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b, x_c \in \mathbb{R}^n$ with $g_c = Ax_c - b \neq 0$, and let
$x_+ = x_c - \mu_cg_c$ with $\mu_c = g_c^Tg_c/g_c^TAg_c$. Then
$$\phi(x_+) = \phi(x_c) - \frac12\,\frac{(g_c^Tg_c)^2}{g_c^TAg_c}.$$

The source writes the denominator as $r_c^TAr_c$ with $r_c = -g_c$, which is equal to
$g_c^TAg_c$. -/
theorem equation_11_3_7 (hA : A.PosDef) {b x g : 𝔼 n} (hg : toEuclideanLin A x - b = g)
    (hg0 : g ≠ 0) :
    energyFunctional (toEuclideanLin A) b (x - (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) • g) =
      energyFunctional (toEuclideanLin A) b x - ⟪g, g⟫ ^ 2 / ⟪g, toEuclideanLin A g⟫ / 2 := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hq : 0 < ⟪toEuclideanLin A g, g⟫ := by
    simpa only [RCLike.re_to_real] using hT.isCoercive.inner_self_pos hg0
  rw [energyFunctional_sub_smul hT.isSymmetric hg, real_inner_comm g (toEuclideanLin A g)]
  field_simp
  ring

/-- **Equation (11.3.8)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b, x_c \in \mathbb{R}^n$ with $g_c = Ax_c - b \neq 0$, let
$x_+ = x_c - \mu_cg_c$ with $\mu_c = g_c^Tg_c/g_c^TAg_c$, and let
$$\kappa_c = \frac{g_c^TAg_c}{g_c^Tg_c} \cdot \frac{g_c^TA^{-1}g_c}{g_c^Tg_c}.$$
Then $g_c^TA^{-1}g_c = 2\phi(x_c) + b^TA^{-1}b$ and
$$\phi(x_+) = \phi(x_c) - \frac{1}{\kappa_c}\Bigl(\phi(x_c) + \frac12 b^TA^{-1}b\Bigr).$$
-/
theorem equation_11_3_8 (hA : A.PosDef) {b x g : 𝔼 n} (hg : toEuclideanLin A x - b = g)
    (hg0 : g ≠ 0) :
    ⟪g, toEuclideanLin A⁻¹ g⟫ =
        2 * energyFunctional (toEuclideanLin A) b x + ⟪b, toEuclideanLin A⁻¹ b⟫ ∧
      energyFunctional (toEuclideanLin A) b (x - (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) • g) =
        energyFunctional (toEuclideanLin A) b x -
          1 / ((⟪g, toEuclideanLin A g⟫ / ⟪g, g⟫) * (⟪g, toEuclideanLin A⁻¹ g⟫ / ⟪g, g⟫)) *
            (energyFunctional (toEuclideanLin A) b x + ⟪b, toEuclideanLin A⁻¹ b⟫ / 2) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hu := hA.isUnit
  have hinv : toEuclideanLin A⁻¹ g = x - toEuclideanLin A⁻¹ b := by
    rw [← hg, map_sub, inv_apply_apply hu]
  have hsym : ⟪g, toEuclideanLin A⁻¹ b⟫ = ⟪toEuclideanLin A x, toEuclideanLin A⁻¹ b⟫ -
      ⟪b, toEuclideanLin A⁻¹ b⟫ := by rw [← hg, inner_sub_left]
  have hAx : ⟪toEuclideanLin A x, toEuclideanLin A⁻¹ b⟫ = ⟪x, b⟫ := by
    rw [hT.isSymmetric, apply_inv_apply hu]
  have h1 : ⟪g, toEuclideanLin A⁻¹ g⟫ =
      2 * energyFunctional (toEuclideanLin A) b x + ⟪b, toEuclideanLin A⁻¹ b⟫ := by
    rw [hinv, inner_sub_right, hsym, hAx, energyFunctional, RCLike.re_to_real, RCLike.re_to_real,
      ← hg, inner_sub_left, real_inner_comm x b]
    ring
  refine ⟨h1, ?_⟩
  have hgg : 0 < ⟪g, g⟫ := real_inner_self_pos.2 hg0
  have hq : 0 < ⟪g, toEuclideanLin A g⟫ := by
    rw [real_inner_comm]
    simpa only [RCLike.re_to_real] using hT.isCoercive.inner_self_pos hg0
  have hinvpos : 0 < ⟪g, toEuclideanLin A⁻¹ g⟫ := by
    have hne : toEuclideanLin A⁻¹ g ≠ 0 := fun h0 => hg0 (by
      rw [← apply_inv_apply hu g, h0, map_zero])
    have := hT.isCoercive.inner_self_pos hne
    rw [apply_inv_apply hu, RCLike.re_to_real] at this
    exact this
  rw [equation_11_3_7 hA hg hg0,
    show energyFunctional (toEuclideanLin A) b x + ⟪b, toEuclideanLin A⁻¹ b⟫ / 2 =
      ⟪g, toEuclideanLin A⁻¹ g⟫ / 2 by rw [h1]; ring]
  field_simp

open scoped Matrix.Norms.L2Operator in
/-- **Section 11.3.2** of [golub2013matrix], the bound on $\kappa_c$. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let $g \in \mathbb{R}^n$ be
nonzero. Then
$$\kappa_c = \frac{g^TAg}{g^Tg} \cdot \frac{g^TA^{-1}g}{g^Tg} \le
  \frac{\lambda_{\max}(A)}{\lambda_{\min}(A)} = \kappa_2(A).$$

The number $\kappa_2(A)$ is `NormedRing.condNumber A` for the matrix $2$-norm
`Matrix.Norms.L2Operator`. -/
theorem kappa_c_le (hA : A.PosDef) {g : 𝔼 n} (hg0 : g ≠ 0) :
    (⟪g, toEuclideanLin A g⟫ / ⟪g, g⟫) * (⟪g, toEuclideanLin A⁻¹ g⟫ / ⟪g, g⟫) ≤
      NormedRing.condNumber A := by
  have : Nonempty (Fin n) := by
    by_contra h
    exact hg0 (Subsingleton.elim (h := by
      rw [not_nonempty_iff] at h
      infer_instance) g 0)
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  rw [hκ]
  have hu := hA.isUnit
  set h := toEuclideanLin A⁻¹ g with hh
  have hAh : toEuclideanLin A h = g := apply_inv_apply hu g
  have hgg : 0 < ⟪g, g⟫ := real_inner_self_pos.2 hg0
  have hgg' : ⟪g, g⟫ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  have hup : ⟪g, toEuclideanLin A g⟫ ≤ lmax * ‖g‖ ^ 2 := by
    have := hB.re_inner_le g
    rwa [RCLike.re_to_real, real_inner_comm] at this
  have hlow : 0 ≤ ⟪g, toEuclideanLin A g⟫ := by
    have := hB.le_re_inner g
    rw [RCLike.re_to_real, real_inner_comm] at this
    nlinarith [sq_nonneg ‖g‖]
  -- `gᵀA⁻¹g = hᵀAh ≥ λ_min ‖h‖²` and `gᵀA⁻¹g = gᵀh ≤ ‖g‖‖h‖`, so `gᵀA⁻¹g ≤ ‖g‖²/λ_min`
  have hlow' : lmin * ‖h‖ ^ 2 ≤ ⟪g, h⟫ := by
    have := hB.le_re_inner h
    rwa [RCLike.re_to_real, hAh] at this
  have hcs : ⟪g, h⟫ ≤ ‖g‖ * ‖h‖ := real_inner_le_norm g h
  have hnh : lmin * ‖h‖ ≤ ‖g‖ := by
    rcases (norm_nonneg h).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg g
    · nlinarith
  have hinv_le : ⟪g, h⟫ ≤ ‖g‖ ^ 2 / lmin := by
    rw [le_div_iff₀ hl]
    nlinarith [norm_nonneg g, norm_nonneg h]
  have hinv_nonneg : 0 ≤ ⟪g, h⟫ := le_trans (by positivity) hlow'
  rw [hgg']
  have hg2 : 0 < ‖g‖ ^ 2 := by rw [← hgg']; exact hgg
  calc (⟪g, toEuclideanLin A g⟫ / ‖g‖ ^ 2) * (⟪g, h⟫ / ‖g‖ ^ 2)
      ≤ (lmax * ‖g‖ ^ 2 / ‖g‖ ^ 2) * (‖g‖ ^ 2 / lmin / ‖g‖ ^ 2) := by
        gcongr
        exact div_nonneg (mul_nonneg (hl.le.trans hll) hg2.le) hg2.le
    _ = lmax / lmin := by field_simp

/-- If $n = 0$, every vector of $\mathbb{R}^n$ is zero. -/
private theorem eq_zero_of_isEmpty [IsEmpty (Fin n)] (v : 𝔼 n) : v = 0 :=
  Subsingleton.elim v 0

open scoped Matrix.Norms.L2Operator in
/-- **Equation (11.3.9)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b \in \mathbb{R}^n$, and let $x_*$ satisfy $Ax_* = b$. For every
$x_c \in \mathbb{R}^n$, the steepest-descent step $x_+$ from $x_c$ satisfies
$$\|x_+ - x_*\|_A^2 \le \Bigl(1 - \frac{1}{\kappa_2(A)}\Bigr)\|x_c - x_*\|_A^2.$$

The proof uses the sharper Kantorovich factor $((\kappa - 1)/(\kappa + 1))^2 \le 1 - 1/\kappa$
of `Projection.energyNorm_steepestDescentStep_le`. -/
theorem equation_11_3_9 (hA : A.PosDef) {b xs : 𝔼 n} (hxs : toEuclideanLin A xs = b) (x : 𝔼 n) :
    energyNorm (toEuclideanLin A) (Projection.steepestDescentStep (toEuclideanLin A) b x - xs) ^ 2 ≤
      (1 - 1 / NormedRing.condNumber A) * energyNorm (toEuclideanLin A) (x - xs) ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [eq_zero_of_isEmpty (x - xs), eq_zero_of_isEmpty (_ - xs)]
    simp [energyNorm]
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  rw [hκ, energyNorm_sub_comm, energyNorm_sub_comm _ x]
  have h := Projection.energyNorm_steepestDescentStep_le hl hB hxs x
  have hc : 0 ≤ (lmax - lmin) / (lmax + lmin) :=
    div_nonneg (sub_nonneg.2 hll) (by linarith)
  calc energyNorm (toEuclideanLin A)
          (xs - Projection.steepestDescentStep (toEuclideanLin A) b x) ^ 2
      ≤ ((lmax - lmin) / (lmax + lmin) * energyNorm (toEuclideanLin A) (xs - x)) ^ 2 :=
        pow_le_pow_left₀ (energyNorm_nonneg _ _) h 2
    _ = ((lmax - lmin) / (lmax + lmin)) ^ 2 * energyNorm (toEuclideanLin A) (xs - x) ^ 2 := by
        ring
    _ ≤ (1 - 1 / (lmax / lmin)) * energyNorm (toEuclideanLin A) (xs - x) ^ 2 :=
        mul_le_mul_of_nonneg_right (kantorovich_sq_le hl hll) (sq_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- **Section 11.3.2** of [golub2013matrix], global convergence of steepest descent. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $b \in \mathbb{R}^n$, let
$x_*$ satisfy $Ax_* = b$, and let $x_k$ be the $k$-th steepest-descent iterate from
$x_0 \in \mathbb{R}^n$. Then for every $k$
$$\|x_k - x_*\|_A \le \Bigl(1 - \frac{1}{\kappa_2(A)}\Bigr)^{k/2}\|x_0 - x_*\|_A,$$
and $x_k \to x_*$.

The source says that the method of steepest descent with exact line search is globally
convergent, with a rate characterized by $(1 - 1/\kappa_2(A))^{k/2}$. The iterate $x_k$ is the
$k$-fold iterate of `Projection.steepestDescentStep`. -/
theorem steepestDescent_rate (hA : A.PosDef) {b xs : 𝔼 n} (hxs : toEuclideanLin A xs = b)
    (x₀ : 𝔼 n) :
    (∀ k : ℕ, energyNorm (toEuclideanLin A)
        ((Projection.steepestDescentStep (toEuclideanLin A) b)^[k] x₀ - xs) ≤
          √(1 - 1 / NormedRing.condNumber A) ^ k * energyNorm (toEuclideanLin A) (x₀ - xs)) ∧
      Tendsto (fun k => (Projection.steepestDescentStep (toEuclideanLin A) b)^[k] x₀) atTop
        (𝓝 xs) := by
  set T := toEuclideanLin A
  set c := √(1 - 1 / NormedRing.condNumber A)
  have hstep : ∀ x, energyNorm T (Projection.steepestDescentStep T b x - xs) ≤
      c * energyNorm T (x - xs) := by
    intro x
    have h := equation_11_3_9 hA hxs x
    rw [← Real.sqrt_sq (energyNorm_nonneg T _), ← Real.sqrt_sq (energyNorm_nonneg T (x - xs)),
      ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_sqrt h
  have hrate : ∀ k : ℕ, energyNorm T ((Projection.steepestDescentStep T b)^[k] x₀ - xs) ≤
      c ^ k * energyNorm T (x₀ - xs) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ, mul_comm (c ^ k) c, mul_assoc]
      exact (hstep _).trans (mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg _))
  refine ⟨hrate, ?_⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp only [eq_zero_of_isEmpty _]
    exact tendsto_const_nhds
  obtain ⟨lmin, lmax, hl, -, hB, -⟩ := posDef_bounds hA
  exact Projection.tendsto_iterate_steepestDescentStep hl hB hxs x₀

end SteepestDescent

/-! ### Algorithm 11.3.1 -/

section Algorithm1

variable {M : Type → Type} [Monad M]

/-- The state of Algorithm 11.3.1: the step count $k$, the iterate $x$, the gradient $g = Ax - b$,
and the flag `done`, which records that the `while` test has failed. -/
structure SteepestDescentState (n : ℕ) where
  /-- The number of completed steps. -/
  k : ℕ
  /-- The iterate $x$. -/
  x : Fin n → ℝ
  /-- The gradient $g = Ax - b$, recomputed after each step. -/
  g : Fin n → ℝ
  /-- The flag that records that the `while` test $\|g\|_2 > \tau$ has failed. -/
  done : Bool

/-- One pass of the `while` body of Algorithm 11.3.1. It does nothing once `done` is set. Otherwise
it computes $\mathrm{fl}(\sqrt{\mathrm{fl}(g^Tg)})$ and compares it exactly with $\tau$; if the
norm is at most $\tau$ it sets `done`, and else it computes $\mu = (g^Tg)/(g^TAg)$,
$x = x - \mu g$ and $g = Ax - b$. -/
noncomputable def steepestDescentBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (τ : ℝ) (s : SteepestDescentState n) : M (SteepestDescentState n) :=
  if s.done then pure s else do
    let gg ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.g s.g
    let nrm ← rnd (√gg)
    if nrm ≤ τ then pure { s with done := true } else do
      let Ag ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A s.g 0
      let gAg ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.g Ag
      let μ ← rnd (gg / gAg)
      let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-μ) s.g s.x
      let g ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A x (-b)
      pure ⟨s.k + 1, x, g, false⟩

/-- **Algorithm 11.3.1** of [golub2013matrix] (steepest descent with exact line search). Given a
symmetric positive definite $A \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^n$, a starting
vector $x_0$ with $Ax_0 \approx b$, and a termination tolerance $\tau$, the algorithm produces
$x \in \mathbb{R}^n$ with $\|Ax - b\|_2 \le \tau$.
```
x = x₀, g = Ax − b
while ‖g‖₂ > τ
    μ = (gᵀg)/(gᵀAg), x = x − μg, g = Ax − b
end
```
The dot products, the matrix-vector products and the vector updates are Algorithms 1.1.1, 1.1.3
and 1.1.2, and every arithmetic result is rounded.

The `while` loop runs at most `fuel` times, with the body
`GolubVanLoan.Chapter11.steepestDescentBody`. The program makes no check on $A$. -/
noncomputable def algorithm_11_3_1 (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : Fin n → ℝ) (τ : ℝ) (fuel : ℕ) : M (SteepestDescentState n) := do
  let g₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A x₀ (-b)
  (List.range fuel).foldlM (fun s _ => steepestDescentBody rnd A b τ s) ⟨0, x₀, g₀, false⟩

/-- The steepest-descent step of the backbone in coordinates: from $x$ it goes to $x - \mu g$, where
$g = Ax - b$ and $\mu = g^Tg/g^TAg$. -/
private theorem steepestDescentStep_toLp (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x) =
      WithLp.toLp 2 (x + (-((A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b) /
        ((A *ᵥ x - b) ⬝ᵥ (A *ᵥ (A *ᵥ x - b))))) • (A *ᵥ x - b)) := by
  have hr : (WithLp.toLp 2 b : 𝔼 n) - toEuclideanLin A (WithLp.toLp 2 x) =
      WithLp.toLp 2 (-(A *ᵥ x - b)) := by
    rw [toEuclideanLin_toLp, ← WithLp.toLp_sub, neg_sub]
  rw [Projection.steepestDescentStep, Projection.step1, hr, toEuclideanLin_toLp, inner_toLp,
    inner_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_dotProduct, dotProduct_neg, neg_neg, neg_neg,
    smul_neg, neg_smul]

/-- The exact run of one pass of the loop body of Algorithm 11.3.1. -/
private theorem steepestDescentBody_run (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (τ : ℝ)
    (s : SteepestDescentState n) :
    Id.run (steepestDescentBody pure A b τ s) =
      if s.done then s else
        if ‖(WithLp.toLp 2 s.g : 𝔼 n)‖ ≤ τ then { s with done := true } else
          ⟨s.k + 1, s.x + (-(s.g ⬝ᵥ s.g / (s.g ⬝ᵥ (A *ᵥ s.g)))) • s.g,
            A *ᵥ (s.x + (-(s.g ⬝ᵥ s.g / (s.g ⬝ᵥ (A *ᵥ s.g)))) • s.g) - b, false⟩ := by
  unfold steepestDescentBody
  by_cases hd : s.done
  · simp [hd]
  · simp only [hd, Bool.false_eq_true, ite_false, Id.run_bind, Id.run_pure]
    rw [GolubVanLoan.Chapter01.algorithm_1_1_1_spec, ← sqrt_dotProduct_self]
    by_cases ht : √(s.g ⬝ᵥ s.g) ≤ τ
    · simp [ht]
    · simp only [ht, ite_false, Id.run_bind, Id.run_pure,
        GolubVanLoan.Chapter01.algorithm_1_1_3_spec, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
        GolubVanLoan.Chapter01.algorithm_1_1_2_spec, zero_add]
      rw [neg_add_eq_sub]

/-- The exact run of Algorithm 11.3.1 with no pass of the loop gives $k = 0$, $x = x_0$ and
$g = Ax_0 - b$. -/
private theorem algorithm_11_3_1_run_zero (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (τ : ℝ) : Id.run (algorithm_11_3_1 pure A b x₀ τ 0) = ⟨0, x₀, A *ᵥ x₀ - b, false⟩ := by
  simp only [algorithm_11_3_1, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
    List.range_zero, List.foldlM_nil, Id.run_pure]
  rw [neg_add_eq_sub]

/-- The exact run of Algorithm 11.3.1 with $m + 1$ passes is one pass of the body after the run with
$m$ passes. -/
private theorem algorithm_11_3_1_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (τ : ℝ) (m : ℕ) : Id.run (algorithm_11_3_1 pure A b x₀ τ (m + 1)) =
      Id.run (steepestDescentBody pure A b τ (Id.run (algorithm_11_3_1 pure A b x₀ τ m))) := by
  simp only [algorithm_11_3_1, Id.run_bind]
  exact List.idRun_foldlM_range_succ _ _ _

/-- The loop invariant of the exact run of Algorithm 11.3.1 after `fuel` passes: the state holds the
$k$-th steepest-descent iterate for some $k \le$ `fuel` and its gradient, `done` implies
$\|g\|_2 \le \tau$, and if `done` is not set then $k$ equals `fuel`. -/
@[reducible] private def SDInv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (τ : ℝ)
    (fuel : ℕ) (s : SteepestDescentState n) : Prop :=
  s.k ≤ fuel ∧
    WithLp.toLp 2 s.x =
      (Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b))^[s.k]
        (WithLp.toLp 2 x₀) ∧
    s.g = A *ᵥ s.x - b ∧ (s.done = true → ‖(WithLp.toLp 2 s.g : 𝔼 n)‖ ≤ τ) ∧
    (s.done = false → s.k = fuel)

/-- The exact run of Algorithm 11.3.1 satisfies the loop invariant above. -/
private theorem algorithm_11_3_1_inv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (τ : ℝ)
    (fuel : ℕ) : SDInv A b x₀ τ fuel (Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)) := by
  induction fuel with
  | zero =>
    rw [algorithm_11_3_1_run_zero]
    exact ⟨le_rfl, rfl, rfl, fun h => by simp at h, fun _ => rfl⟩
  | succ fuel ih =>
    rw [algorithm_11_3_1_run_succ, steepestDescentBody_run]
    set s := Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)
    obtain ⟨hk, hx, hg, hdone, hnd⟩ := ih
    by_cases hd : s.done
    · simp only [hd, ↓reduceIte]
      exact ⟨hk.trans (Nat.le_succ _), hx, hg, fun _ => hdone hd,
        fun h => absurd (hd.symm.trans h) (by decide)⟩
    · have hkf : s.k = fuel := hnd (by simpa using hd)
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      by_cases ht : ‖(WithLp.toLp 2 s.g : 𝔼 n)‖ ≤ τ
      · simp only [ht, ↓reduceIte]
        exact ⟨hk.trans (Nat.le_succ _), hx, hg, fun _ => ht, fun h => by simp at h⟩
      · simp only [ht, ↓reduceIte]
        refine ⟨show s.k + 1 ≤ fuel + 1 by omega, ?_, rfl, fun h => by simp at h,
          fun _ => show s.k + 1 = fuel + 1 by omega⟩
        change WithLp.toLp 2 (s.x + (-(s.g ⬝ᵥ s.g / (s.g ⬝ᵥ (A *ᵥ s.g)))) • s.g) =
          (Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b))^[s.k + 1]
            (WithLp.toLp 2 x₀)
        rw [Function.iterate_succ_apply', ← hx, steepestDescentStep_toLp, ← hg]

/-- **Algorithm 11.3.1** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive definite, $b, x_0 \in \mathbb{R}^n$ and $\tau \in \mathbb{R}$. For every
`fuel`, the exact run returns a state whose step count $k$ is at most `fuel`, with the $k$-th
steepest-descent iterate $x$ from $x_0$ and $g = Ax - b$; if the `while` test has failed then
$\|g\|_2 \le \tau$, and otherwise $k$ equals `fuel`. Moreover, if $\tau > 0$, there is $N$ such
that for every `fuel` at least $N$ the output satisfies $\|Ax - b\|_2 \le \tau$.

The second part is the claim of the source that the algorithm produces $x$ with
$\|Ax - b\|_2 \le \tau$. The exact run is the run with `M := Id` and `rnd := pure`, and the
steepest-descent iterate is the $k$-fold iterate of `Projection.steepestDescentStep`. -/
theorem algorithm_11_3_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (τ : ℝ) :
    (∀ fuel : ℕ,
      let s := Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)
      s.k ≤ fuel ∧
        WithLp.toLp 2 s.x =
          (Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b))^[s.k]
            (WithLp.toLp 2 x₀) ∧
        s.g = A *ᵥ s.x - b ∧ (s.done = true → ‖(WithLp.toLp 2 s.g : 𝔼 n)‖ ≤ τ) ∧
        (s.done = false → s.k = fuel)) ∧
      (0 < τ → ∃ N, ∀ fuel ≥ N,
        ‖(WithLp.toLp 2 (A *ᵥ (Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)).x - b) : 𝔼 n)‖ ≤
          τ) := by
  refine ⟨fun fuel => algorithm_11_3_1_inv A b x₀ τ fuel, fun hτ => ?_⟩
  have hconv := (steepestDescent_rate hA (apply_inv_eq hA (WithLp.toLp 2 b))
    (WithLp.toLp 2 x₀)).2
  -- `‖A x_k − b‖₂ → 0`
  have hres : Tendsto (fun k => toEuclideanLin A
      ((Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b))^[k]
        (WithLp.toLp 2 x₀)) - WithLp.toLp 2 b) atTop (𝓝 0) := by
    have hc : Continuous (toEuclideanLin A) :=
      LinearMap.continuous_of_finiteDimensional (toEuclideanLin A)
    have := ((hc.tendsto _).comp hconv).sub_const (WithLp.toLp 2 b)
    rwa [Function.comp_def, apply_inv_eq hA, sub_self] at this
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hres) τ hτ
  refine ⟨N, fun fuel hfuel => ?_⟩
  obtain ⟨_, hx, hg, hdone, hnd⟩ := algorithm_11_3_1_inv A b x₀ τ fuel
  rw [← hg]
  cases hd : (Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)).done
  · have hk := hnd hd
    have := hN (Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)).k (by rw [hk]; exact hfuel)
    rw [dist_zero_right, ← hx, toEuclideanLin_toLp, ← WithLp.toLp_sub, ← hg] at this
    exact this.le
  · exact hdone hd

end Algorithm1

/-! ### §11.3.3: a subspace strategy -/

section Subspace

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Equations (11.3.10)–(11.3.11)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite, let $b, \bar x \in \mathbb{R}^n$, let
$S_0 \subseteq S_1 \subseteq \cdots$ be nested subspaces of $\mathbb{R}^n$, and for each
$k \ge 0$ let $x_k$ minimize $\phi$ over the affine space $\bar x + S_k$. Then:

* if $S_{k+1}$ contains $x_k - \bar x$ and $g_k = Ax_k - b$, then
  $\phi(x_{k+1}) \le \phi(x_k - \mu g_k)$ for every $\mu \in \mathbb{R}$;
* $\phi(x_0) \ge \phi(x_1) \ge \phi(x_2) \ge \cdots$;
* if $S_m = \mathbb{R}^n$, then $Ax_m = b$.

The source writes the starting point $\bar x$ as $x_0$ and states the chain from $\phi(x_1)$.
Here the starting point is the argument `x₀`, and the minimizer $x_0$ over $\bar x + S_0$ is
`x 0`; the two agree when $S_0 = \{0\}$. The last part is the remark of the source that, since
$S_n = \mathbb{R}^n$, the method ultimately obtains $x_* = A^{-1}b$. -/
theorem equation_11_3_11 (hA : A.PosDef) (b x₀ : 𝔼 n) {S : ℕ → Submodule ℝ (𝔼 n)}
    (hS : Monotone S) {x : ℕ → 𝔼 n}
    (hx : ∀ k, x k - x₀ ∈ S k ∧ ∀ y, y - x₀ ∈ S k →
      energyFunctional (toEuclideanLin A) b (x k) ≤ energyFunctional (toEuclideanLin A) b y) :
    (∀ k, x k - x₀ ∈ S (k + 1) → toEuclideanLin A (x k) - b ∈ S (k + 1) → ∀ μ : ℝ,
      energyFunctional (toEuclideanLin A) b (x (k + 1)) ≤
        energyFunctional (toEuclideanLin A) b (x k - μ • (toEuclideanLin A (x k) - b))) ∧
      Antitone (fun k => energyFunctional (toEuclideanLin A) b (x k)) ∧
      (∀ m, S m = ⊤ → toEuclideanLin A (x m) = b) := by
  refine ⟨fun k h1 h2 μ => (hx (k + 1)).2 _ ?_, fun k l hkl => (hx l).2 _ ?_,
    fun m hm => (equation_11_3_2 hA b (x m)).2 fun y => (hx m).2 y (by rw [hm]; trivial)⟩
  · rw [sub_right_comm]
    exact (S (k + 1)).sub_mem h1 ((S (k + 1)).smul_mem μ h2)
  · exact hS hkl (hx k).1

/-- **Section 11.3.3** of [golub2013matrix], the Krylov subspaces meet the requirement of (11.3.11).
Let $A \in \mathbb{R}^{n \times n}$, $b, x_0 \in \mathbb{R}^n$ and $g_0 = Ax_0 - b$, and let
$x_k \in \mathbb{R}^n$ satisfy $x_k - x_0 \in \mathcal{K}(A, g_0, k)$. Then the gradient
$g_k = Ax_k - b$ lies in $\mathcal{K}(A, g_0, k + 1)$, and $x_k - \mu g_k - x_0 \in
\mathcal{K}(A, g_0, k + 1)$ for every $\mu \in \mathbb{R}$. -/
theorem gradient_mem_krylov (b x₀ : 𝔼 n) {k : ℕ} {xk : 𝔼 n}
    (hxk : xk - x₀ ∈ Krylov.subspace (toEuclideanLin A) (toEuclideanLin A x₀ - b) k) :
    toEuclideanLin A xk - b ∈ Krylov.subspace (toEuclideanLin A) (toEuclideanLin A x₀ - b) (k + 1) ∧
      ∀ μ : ℝ, xk - μ • (toEuclideanLin A xk - b) - x₀ ∈
        Krylov.subspace (toEuclideanLin A) (toEuclideanLin A x₀ - b) (k + 1) := by
  set T := toEuclideanLin A
  -- `𝒦(A, −v, k) = 𝒦(A, v, k)`
  have hneg : ∀ (v : 𝔼 n) m, Krylov.subspace T (-v) m = Krylov.subspace T v m := fun v m =>
    le_antisymm (by simpa using Krylov.subspace_smul T v (-1 : ℝ) m)
      (by simpa using Krylov.subspace_smul T (-v) (-1 : ℝ) m)
  have hg0 : T x₀ - b = -(b - T x₀) := by abel
  rw [hg0, hneg] at hxk ⊢
  have hr := Krylov.residual_mem_subspace_succ hxk
  have hg : T xk - b ∈ Krylov.subspace T (b - T x₀) (k + 1) := by
    rw [show T xk - b = -(b - T xk) by abel]; exact Submodule.neg_mem _ hr
  refine ⟨hg, fun μ => ?_⟩
  rw [sub_right_comm]
  exact Submodule.sub_mem _ (Krylov.subspace_mono T _ (Nat.le_succ k) hxk)
    (Submodule.smul_mem _ μ hg)

end Subspace

/-! ### §11.3.4: termination and the rate of one CG step -/

section CGTheorems

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Corollary 11.3.2** of [golub2013matrix]. Let $U \in \mathbb{R}^{n \times r}$ and
$D \in \mathbb{R}^{r \times r}$, and suppose that $A = I_n + UDU^T$ is positive definite. Let
$b, x_0 \in \mathbb{R}^n$ and $r_0 = b - Ax_0$. Then the grade of $r_0$ is at most $r + 1$, and
the CG iterate $x_{r+1}$ satisfies $Ax_{r+1} = b$: at most $r + 1$ iterations are required to
compute $x_*$.

**Generalization.** The source also assumes that $D$ is symmetric and that $r < n$. Neither
assumption is needed.

The grade is `Krylov.grade`, and the CG iterates are `CG.iterate`. The proof bounds the grade by
$\operatorname{rank}(A - I) + 1$ instead of counting the distinct eigenvalues of $A$. -/
theorem corollary_11_3_2 {r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (D : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (hAUD : A = 1 + U * D * Uᵀ) (b x₀ : 𝔼 n) :
    Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ r + 1 ∧
      toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ (r + 1)).x = b := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hgrade : Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ r + 1 := by
    refine (Krylov.grade_le_finrank_range_sub_algebraMap_add_one (toEuclideanLin A)
      (b - toEuclideanLin A x₀) 1).trans ?_
    have hsub : toEuclideanLin A - algebraMap ℝ (Module.End ℝ (𝔼 n)) 1 =
        toEuclideanLin (U * D * Uᵀ) := by
      rw [map_one, Module.End.one_eq_id, ← toEuclideanLin_one (n := Fin n) (𝕜 := ℝ),
        ← map_sub, hAUD, add_sub_cancel_left]
    rw [hsub, toEuclideanLin_eq_toLin_orthonormal, ← rank_eq_finrank_range_toLin]
    have : (U * D * Uᵀ).rank ≤ r := by
      rw [Matrix.mul_assoc]
      exact (rank_mul_le_left _ _).trans (rank_le_width U)
    omega
  exact ⟨hgrade, (CG.isGalerkinIterate b x₀ hT (r + 1)).apply_eq_of_grade_le hgrade⟩

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 11.3.3** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b \in \mathbb{R}^n$, let $x_*$ satisfy $Ax_* = b$, and let $x_k$ be the
CG iterates from $x_0 \in \mathbb{R}^n$. Then for every $k \ge 0$
$$\|x_{k+1} - x_*\|_A \le \Bigl(1 - \frac{1}{\kappa_2(A)}\Bigr)^{1/2}\|x_k - x_*\|_A.$$

The CG iterates are `CG.iterate`, the Galerkin iterates over $x_0 + \mathcal{K}(A, r_0, k)$. -/
theorem theorem_11_3_3 (hA : A.PosDef) {b xs : 𝔼 n} (hxs : toEuclideanLin A xs = b) (x₀ : 𝔼 n)
    (k : ℕ) :
    energyNorm (toEuclideanLin A) ((CG.iterate (toEuclideanLin A) b x₀ (k + 1)).x - xs) ≤
      √(1 - 1 / NormedRing.condNumber A) *
        energyNorm (toEuclideanLin A) ((CG.iterate (toEuclideanLin A) b x₀ k).x - xs) := by
  set T := toEuclideanLin A
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [eq_zero_of_isEmpty (_ - xs), eq_zero_of_isEmpty (_ - xs)]
    simp [energyNorm]
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  have h := Krylov.IsGalerkinIterate.energyNorm_error_succ_le hl hB
    (CG.isGalerkinIterate b x₀ hT k) (CG.isGalerkinIterate b x₀ hT (k + 1)) hxs
  rw [energyNorm_sub_comm, energyNorm_sub_comm _ _ xs, hκ]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (energyNorm_nonneg _ _))
  rw [← Real.sqrt_sq (div_nonneg (sub_nonneg.2 hll) (by linarith : (0 : ℝ) ≤ lmax + lmin))]
  exact Real.sqrt_le_sqrt (kantorovich_sq_le hl hll)

end CGTheorems

/-! ### §11.3.4: the Lanczos view of CG -/

section LanczosView

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Equations (11.3.12)–(11.3.13)** of [golub2013matrix], recalled from §10.1. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $r_0 \in \mathbb{R}^n$. After $k$ steps of the
Lanczos iteration from $r_0$ there are $Q_k = [q_1 | \cdots | q_k]$ with orthonormal columns, a
tridiagonal $T_k$ and $r_k \perp \operatorname{ran}(Q_k)$ with $AQ_k = Q_kT_k + r_ke_k^T$. Here
this is stated after $k + 1$ steps and applied to a vector $y \in \mathbb{R}^{k+1}$:
$$A(Q_{k+1}y) = Q_{k+1}(T_{k+1}y) + \beta_{k+1}y_{k+1}q_{k+2},$$
and $q_{k+2}$ is orthogonal to $q_1, \dots, q_{k+1}$.

The vector $q_{j+1}$ is `Arnoldi.vec (Matrix.toEuclideanLin A) r₀ j`, and the matrix
$T_{k+1}$ is `Lanczos.tridiag`. The number $\beta_{k+1}$ is
`Lanczos.beta (Matrix.toEuclideanLin A) r₀ k`, so that $r_{k+1} = \beta_{k+1}q_{k+2}$. -/
theorem equation_11_3_13 (hA : A.IsSymm) (r₀ : 𝔼 n) (k : ℕ) (y : Fin (k + 1) → ℝ) :
    toEuclideanLin A (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) =
      ∑ i : Fin (k + 1), (Lanczos.tridiag (toEuclideanLin A) r₀ (k + 1) *ᵥ y) i •
          Arnoldi.vec (toEuclideanLin A) r₀ i +
        (Lanczos.beta (toEuclideanLin A) r₀ k * y (Fin.last k)) •
          Arnoldi.vec (toEuclideanLin A) r₀ (k + 1) ∧
      ∀ i ≤ k, ⟪Arnoldi.vec (toEuclideanLin A) r₀ i,
        Arnoldi.vec (toEuclideanLin A) r₀ (k + 1)⟫ = 0 := by
  refine ⟨?_, fun i hi => Arnoldi.inner_vec_eq_zero _ _ (by omega)⟩
  have h := Lanczos.apply_sum r₀ hA.isSymmetric_toEuclideanLin k y
  have hmap : (Lanczos.tridiag (toEuclideanLin A) r₀ (k + 1)).map (algebraMap ℝ ℝ) =
      Lanczos.tridiag (toEuclideanLin A) r₀ (k + 1) := by
    ext; simp
  rw [hmap] at h
  simpa using h

/-- For symmetric $A$, the Lanczos tridiagonal matrix $T_k$ is the square Hessenberg matrix $H_k$ of
the Arnoldi process. -/
private theorem tridiag_eq_hessenbergSq (hA : A.IsSymm) (r₀ : 𝔼 n) (k : ℕ) :
    Lanczos.tridiag (toEuclideanLin A) r₀ k = Arnoldi.hessenbergSq (toEuclideanLin A) r₀ k := by
  rw [Lanczos.hessenbergSq_eq_map_tridiag r₀ hA.isSymmetric_toEuclideanLin]
  ext; simp

/-- **Section 11.3.4** of [golub2013matrix], positive definiteness of $T_k$. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $r_0 \in \mathbb{R}^n$, and
let $k$ be at most the grade of $r_0$. Then the Lanczos tridiagonal matrix $T_k = Q_k^TAQ_k$ of
$r_0$ is positive definite. -/
theorem lanczos_tridiag_posDef (hA : A.PosDef) (r₀ : 𝔼 n) {k : ℕ}
    (hk : k ≤ Krylov.grade (toEuclideanLin A) r₀) :
    (Lanczos.tridiag (toEuclideanLin A) r₀ k).PosDef := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.1 hA.isHermitian
  -- `yᵀT_ky = ⟪Q_ky, AQ_ky⟫`
  have hq : ∀ y : Fin k → ℝ, y ⬝ᵥ (Lanczos.tridiag (toEuclideanLin A) r₀ k *ᵥ y) =
      ⟪∑ i, y i • Arnoldi.vec (toEuclideanLin A) r₀ i,
        toEuclideanLin A (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j)⟫ := by
    intro y
    rw [tridiag_eq_hessenbergSq hsymm]
    simp only [dotProduct, mulVec, Finset.mul_sum, map_sum, map_smul, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, Arnoldi.hessenbergSq, Arnoldi.coeff,
      of_apply]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  -- `Q_k` has orthonormal columns, so `Q_ky = 0` forces `y = 0`
  have hv : ∀ y : Fin k → ℝ, (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) = 0 → y = 0 := by
    intro y h0
    funext i
    have h1 := congrArg (fun v => ⟪Arnoldi.vec (toEuclideanLin A) r₀ i, v⟫) h0
    simp only [inner_sum, real_inner_smul_right, inner_zero_right] at h1
    rw [Finset.sum_eq_single i (fun j _ hji => by
        rw [Arnoldi.inner_vec_eq_zero _ _ (fun h => hji (Fin.ext h.symm)), mul_zero])
      (by simp), real_inner_self_eq_norm_sq,
      Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (i.2.trans_le hk), one_pow, mul_one] at h1
    exact h1
  refine posDef_iff_dotProduct_mulVec.2 ⟨isHermitian_iff_isSymm.2
    (Lanczos.tridiag_isSymm _ _ _), fun y hy => ?_⟩
  rw [star_trivial, hq]
  have hne : (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) ≠ 0 := fun h => hy (hv y h)
  have := hT.isCoercive.inner_self_pos hne
  rwa [RCLike.re_to_real, real_inner_comm] at this

/-- **Section 11.3.4** of [golub2013matrix], CG in Lanczos coordinates. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $b, x_0 \in \mathbb{R}^n$,
$r_0 = b - Ax_0$ and $\beta_0 = \|r_0\|_2$, and let $k$ be at most the grade of $r_0$. For
$y \in \mathbb{R}^k$, the vector $x_0 + Q_ky$ is the Galerkin iterate of step $k$ if and only if
$$T_ky = \beta_0e_1.$$

The source argues that the columns of $Q_k$ span $\mathcal{K}(A, r_0, k)$, so that minimizing
$\phi$ over $x_0 + \mathcal{K}(A, r_0, k)$ is minimizing $\phi(x_0 + Q_ky)$ over
$y \in \mathbb{R}^k$, and that the minimizer $y_k$ satisfies $T_ky_k = Q_k^Tr_0 = \beta_0e_1$.
The Galerkin iterate is `Krylov.IsGalerkinIterate`: $x \in x_0 + \mathcal{K}(A, r_0, k)$ and
$b - Ax \perp \mathcal{K}(A, r_0, k)$. It is the minimizer of $\phi$ over
$x_0 + \mathcal{K}(A, r_0, k)$ by `IsGalerkin.energyFunctional_le`. -/
theorem cg_lanczos_coordinates (hA : A.PosDef) (b x₀ : 𝔼 n) {k : ℕ}
    (hk : k ≤ Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) (y : Fin k → ℝ) :
    Krylov.IsGalerkinIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ↔
      Lanczos.tridiag (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ y =
        Krylov.firstVec ‖b - toEuclideanLin A x₀‖ k := by
  rw [Krylov.isGalerkinIterate_iff_mulVec_eq hk,
    ← tridiag_eq_hessenbergSq (isHermitian_iff_isSymm.1 hA.isHermitian)]
  exact Iff.rfl

end LanczosView

/-! ### (11.3.14): the preliminary CG, and Theorem 11.3.1 -/

section PreliminaryCG

/-- The state of the preliminary CG method (11.3.14): the state of the Lanczos loop of Algorithm
10.1.1 (the step count $k$, the vectors $q_j$, the coefficients $\alpha_j$ and $\beta_j$, the
residual $r_k$ and the `done` flag of the `while` test), together with the iterate $x_k$. -/
structure PreliminaryCGState (n : ℕ) where
  /-- The state of the Lanczos loop. -/
  lanczos : GolubVanLoan.Chapter10.LanczosState n
  /-- The iterate $x_k$. -/
  x : Fin n → ℝ

/-- The $n \times k$ matrix $Q_k = [q_1 | \cdots | q_k]$ of the Lanczos vectors of a Lanczos state
with step count $k$. -/
def lanczosBasis (L : GolubVanLoan.Chapter10.LanczosState n) : Matrix (Fin n) (Fin L.k) ℝ :=
  of fun i j => L.q j i

/-- The $k \times k$ symmetric tridiagonal matrix $T_k$ of a Lanczos state with step count $k$, with
diagonal $\alpha_1, \dots, \alpha_k$ and off-diagonal $\beta_1, \dots, \beta_{k-1}$. -/
def lanczosTridiag (L : GolubVanLoan.Chapter10.LanczosState n) :
    Matrix (Fin L.k) (Fin L.k) ℝ :=
  tridiagonalOfNat L.alpha (fun i => L.beta (i - 1)) L.beta L.k

variable {M : Type → Type} [Monad M]

/-- The solve $T_ky = c$ of (11.3.14), for the symmetric tridiagonal $T_k$ with diagonal $\alpha$
and off-diagonal $\beta$ (0-based). For $k \ge 1$ it is Algorithm 4.3.6,
`GolubVanLoan.Chapter04.algorithm_4_3_6`; for $k = 0$ there is nothing to solve, and it returns
$c$. -/
noncomputable def tridiagSolve (rnd : ℝ → M ℝ) :
    (k : ℕ) → (α β : ℕ → ℝ) → (Fin k → ℝ) → M (Fin k → ℝ)
  | 0, _, _, c => pure c
  | N + 1, α, β, c =>
    Chapter04.algorithm_4_3_6 rnd (fun i : Fin (N + 1) => α i) (fun i : Fin N => β i) c

/-- If the symmetric tridiagonal matrix $T_k$ with diagonal $\alpha$ and off-diagonal $\beta$ is
positive definite, then the exact run of `GolubVanLoan.Chapter11.tridiagSolve` returns the
solution $y$ of $T_ky = c$. This follows from `GolubVanLoan.Chapter04.algorithm_4_3_6_spec`. -/
theorem tridiagSolve_spec (k : ℕ) (α β : ℕ → ℝ)
    (hT : (tridiagonalOfNat α (fun i => β (i - 1)) β k).PosDef) (c : Fin k → ℝ) :
    tridiagonalOfNat α (fun i => β (i - 1)) β k *ᵥ Id.run (tridiagSolve pure k α β c) = c := by
  cases k with
  | zero => ext i; exact i.elim0
  | succ N =>
    have h : tridiagonalOfNat α (fun i => β (i - 1)) β (N + 1) =
        tridiagonalOf (fun i : Fin N => β i) (fun i : Fin (N + 1) => α i)
          (fun i : Fin N => β i) := by
      rw [tridiagonalOfNat_eq_tridiagonalOf]
      simp only [Nat.add_sub_cancel]
    rw [h] at hT ⊢
    exact Chapter04.algorithm_4_3_6_spec _ _ hT c

/-- One pass of the `while` loop of (11.3.14), which does nothing once `done` is set. It makes one
pass of the Lanczos loop of Algorithm 10.1.1 ($q_{k+1} = r_k/\beta_k$, $k = k + 1$,
$\alpha_k = q_k^TAq_k$, $r_k = (A - \alpha_kI)q_k - \beta_{k-1}q_{k-1}$, $\beta_k = \|r_k\|_2$),
then solves $T_ky_k = \beta_0e_1$ by Algorithm 4.3.6 (`GolubVanLoan.Chapter11.tridiagSolve`) and
computes $x_k = x_0 + Q_ky_k$ by the gaxpy of Algorithm 1.1.3. -/
noncomputable def preliminaryCGBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (β₀ : ℝ) (x₀ : Fin n → ℝ) (s : PreliminaryCGState n) : M (PreliminaryCGState n) :=
  if s.lanczos.done then pure s else do
    let L ← GolubVanLoan.Chapter10.lanczosStep rnd A s.lanczos
    let y ← tridiagSolve rnd L.k L.alpha L.beta (Krylov.firstVec β₀ L.k)
    let x ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd (lanczosBasis L) y x₀
    pure ⟨L, x⟩

/-- **Equation (11.3.14)** of [golub2013matrix] (the preliminary CG method). Given a symmetric
positive definite $A \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^n$ and
$x_0 \in \mathbb{R}^n$, the method builds on Algorithm 10.1.1:
```
k = 0, r₀ = b − Ax₀, β₀ = ‖r₀‖₂, q₀ = 0
while β_k ≠ 0
  q_{k+1} = r_k/β_k,  k = k + 1,  α_k = q_kᵀAq_k
  T_k y_k = β₀e₁,  x_k = x₀ + Q_k y_k
  r_k = (A − α_kI)q_k − β_{k−1}q_{k−1},  β_k = ‖r_k‖₂
end
x_* = x_k
```
The Lanczos part is Algorithm 10.1.1 started from $q_1 = r_0/\beta_0$, through its loop body
`GolubVanLoan.Chapter10.lanczosStep`. The solve $T_ky_k = \beta_0e_1$ is Algorithm 4.3.6
(`GolubVanLoan.Chapter11.tridiagSolve`); $T_k$ is positive definite while $k$ is at most the
grade of $r_0$.

**Correction.** The source prints $x_k = Q_ky_k$, which is correct only for $x_0 = 0$. The
derivation above it gives $x_k = x_0 + Q_ky_k$, and the program computes this.

The `while` loop runs at most `fuel` times. The first normalization of Chapter 10's loop divides
again by its $\beta_0 = 1$, so in the rounded model $q_1$ is
$\mathrm{fl}(\mathrm{fl}(r_0/\beta_0)/1)$: one rounding per entry more than the single division
of the source. This keeps Chapter 10's loop unchanged. -/
noncomputable def preliminaryCG (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    M (PreliminaryCGState n) := do
  let r₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let β₀ ← GolubVanLoan.Chapter10.vecNorm rnd r₀
  let q₁ ← GolubVanLoan.Chapter10.vecDiv rnd r₀ β₀
  (List.range fuel).foldlM (fun s _ => preliminaryCGBody rnd A β₀ x₀ s)
    ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0, q₁, decide (β₀ = 0)⟩, x₀⟩

/-- The exact number $\beta_0 = \|b - Ax_0\|_2$. -/
private noncomputable def pcgBeta₀ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 (b - A *ᵥ x₀) : 𝔼 n)‖

/-- The exact initial Lanczos state of (11.3.14). -/
private noncomputable def pcgInit (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    GolubVanLoan.Chapter10.LanczosState n :=
  ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, (pcgBeta₀ A b x₀)⁻¹ • (b - A *ᵥ x₀),
    decide (pcgBeta₀ A b x₀ = 0)⟩

/-- The exact run of (11.3.14) is a fold of the exact loop body. -/
private theorem preliminaryCG_run (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (t : ℕ) :
    Id.run (preliminaryCG pure A b x₀ t) =
      (List.range t).foldl
        (fun s _ => Id.run (preliminaryCGBody pure A (pcgBeta₀ A b x₀) x₀ s))
        ⟨pcgInit A b x₀, x₀⟩ := by
  simp only [preliminaryCG, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
    GolubVanLoan.Chapter10.vecNorm_spec, GolubVanLoan.Chapter10.vecDiv_spec, List.idRun_foldlM,
    mulVec_neg, ← sub_eq_add_neg]
  rfl

/-- The Lanczos part of an exact pass of (11.3.14) is an exact pass of the loop of Algorithm 10.1.1.
-/
private theorem preliminaryCGBody_lanczos (A : Matrix (Fin n) (Fin n) ℝ)
    (β₀ : ℝ)
    (x₀ : Fin n → ℝ) (s : PreliminaryCGState n) :
    (Id.run (preliminaryCGBody pure A β₀ x₀ s)).lanczos =
      Id.run (GolubVanLoan.Chapter10.lanczosStep pure A s.lanczos) := by
  unfold preliminaryCGBody
  cases h : s.lanczos.done
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [↓reduceIte, GolubVanLoan.Chapter10.lanczosStep, h]
    rfl

/-- After an exact pass of (11.3.14), the iterate is $x_k = x_0 + Q_kT_k^{-1}(\beta_0e_1)$ for the
new Lanczos state, computed by the tridiagonal solve; once `done` is set, it is unchanged. -/
private theorem preliminaryCGBody_x (A : Matrix (Fin n) (Fin n) ℝ)
    (β₀ : ℝ)
    (x₀ : Fin n → ℝ) (s : PreliminaryCGState n) :
    (Id.run (preliminaryCGBody pure A β₀ x₀ s)).x =
      if s.lanczos.done then s.x else
        x₀ + lanczosBasis (Id.run (preliminaryCGBody pure A β₀ x₀ s)).lanczos *ᵥ
          Id.run (tridiagSolve pure (Id.run (preliminaryCGBody pure A β₀ x₀ s)).lanczos.k
            (Id.run (preliminaryCGBody pure A β₀ x₀ s)).lanczos.alpha
            (Id.run (preliminaryCGBody pure A β₀ x₀ s)).lanczos.beta
            (Krylov.firstVec β₀ (Id.run (preliminaryCGBody pure A β₀ x₀ s)).lanczos.k)) := by
  unfold preliminaryCGBody
  cases h : s.lanczos.done
  · simp only [Bool.false_eq_true, ↓reduceIte, Id.run_bind,
      GolubVanLoan.Chapter01.algorithm_1_1_3_spec]
    rfl
  · simp only [↓reduceIte]
    rfl

/-- The exact run of Algorithm 10.1.1 with $t + 1$ passes is one pass of its loop body after the run
with $t$ passes. -/
private theorem algorithm_10_1_1_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ)
    (t : ℕ) : Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ (t + 1)) =
      Id.run (GolubVanLoan.Chapter10.lanczosStep pure A
        (Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ t))) := by
  simp only [GolubVanLoan.Chapter10.algorithm_10_1_1, List.range_succ, List.foldlM_append,
    List.foldlM_cons, List.foldlM_nil, bind_pure, Id.run_bind]

/-- In the exact run of Algorithm 10.1.1, the flag `done` is set if and only if at least one step
was made and the last computed $\beta$ is zero. -/
private theorem algorithm_10_1_1_done (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (t : ℕ) :
    (Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ t)).done = true ↔
      0 < (Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ t)).k ∧
        (Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ t)).beta
          ((Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ t)).k - 1) = 0 := by
  induction t with
  | zero => simp [GolubVanLoan.Chapter10.algorithm_10_1_1]
  | succ t ih =>
    rw [algorithm_10_1_1_run_succ]
    set L := Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ t)
    cases h : L.done
    · simp only [GolubVanLoan.Chapter10.lanczosStep, h, Bool.false_eq_true, ↓reduceIte,
        Id.run_bind, Id.run_pure, decide_eq_true_eq, Nat.add_sub_cancel,
        Function.update_self]
      simp
    · simp only [GolubVanLoan.Chapter10.lanczosStep, h, ↓reduceIte, Id.run_pure]
      exact ⟨fun _ => ih.1 h, fun _ => trivial⟩

/-- For symmetric $A$, after the exact run of (11.3.14) the Lanczos state has made
$k = \min(\mathrm{fuel}, k_*)$ steps, where $k_*$ is the grade of $r_0$; its vectors and
coefficients are the Lanczos vectors and coefficients of $r_0$; and `done` is set if and only if
$k_* \le k$. -/
private theorem preliminaryCG_lanczos_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.k =
        min fuel (Krylov.grade (toEuclideanLin A) (cgR A b x₀)) ∧
      (∀ j < (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.k,
        WithLp.toLp 2 ((Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.q j) =
            Arnoldi.vec (toEuclideanLin A) (cgR A b x₀) j ∧
          (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.alpha j =
            Lanczos.alpha (toEuclideanLin A) (cgR A b x₀) j ∧
          (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.beta j =
            Lanczos.beta (toEuclideanLin A) (cgR A b x₀) j) ∧
      ((Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.done = true ↔
        Krylov.grade (toEuclideanLin A) (cgR A b x₀) ≤
          (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.k) := by
  have hT : (toEuclideanLin A).IsSymmetric := hA.isSymmetric_toEuclideanLin
  have hr₀ : cgR A b x₀ = WithLp.toLp 2 (b - A *ᵥ x₀) := by
    rw [toEuclideanLin_toLp, ← WithLp.toLp_sub]
  have hβ₀ : pcgBeta₀ A b x₀ = ‖cgR A b x₀‖ := by rw [hr₀]; rfl
  rw [preliminaryCG_run]
  by_cases h0 : pcgBeta₀ A b x₀ = 0
  · -- `r₀ = 0`: the loop does nothing
    have hr0 : cgR A b x₀ = 0 := by rw [← norm_eq_zero, ← hβ₀, h0]
    have hfix : ∀ t, (List.range t).foldl
        (fun s _ => Id.run (preliminaryCGBody pure A (pcgBeta₀ A b x₀) x₀ s))
        ⟨pcgInit A b x₀, x₀⟩ = ⟨pcgInit A b x₀, x₀⟩ := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
        simp [preliminaryCGBody, pcgInit, h0]
    rw [hfix, hr0, Krylov.grade_zero]
    simp [pcgInit, h0]
  · -- `r₀ ≠ 0`: the Lanczos part is Algorithm 10.1.1 from `q₁ = r₀/β₀`
    set q₁ := (pcgBeta₀ A b x₀)⁻¹ • (b - A *ᵥ x₀) with hq₁
    have hrun : ∀ t, ((List.range t).foldl
        (fun s _ => Id.run (preliminaryCGBody pure A (pcgBeta₀ A b x₀) x₀ s))
        ⟨pcgInit A b x₀, x₀⟩).lanczos =
          Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ t) := by
      intro t
      induction t with
      | zero => simp [pcgInit, h0, GolubVanLoan.Chapter10.algorithm_10_1_1, q₁]
      | succ t ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          preliminaryCGBody_lanczos, ih, algorithm_10_1_1_run_succ]
    rw [hrun]
    have hβpos : 0 < pcgBeta₀ A b x₀ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hq : WithLp.toLp 2 q₁ = (pcgBeta₀ A b x₀)⁻¹ • cgR A b x₀ := by
      rw [hr₀, hq₁, WithLp.toLp_smul]
    have hqn : ‖(WithLp.toLp 2 q₁ : 𝔼 n)‖ = 1 := by
      rw [hq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hβpos.le), ← hβ₀,
        inv_mul_cancel₀ h0]
    obtain ⟨hk, hvec, -⟩ := GolubVanLoan.Chapter10.algorithm_10_1_1_spec hA hqn fuel
    have hvs : Arnoldi.vec (toEuclideanLin A) (WithLp.toLp 2 q₁) =
        Arnoldi.vec (toEuclideanLin A) (cgR A b x₀) := by
      rw [hq]; simpa using Arnoldi.vec_smul_of_pos (toEuclideanLin A) _ (inv_pos.2 hβpos)
    have hgr : Krylov.grade (toEuclideanLin A) (WithLp.toLp 2 q₁) =
        Krylov.grade (toEuclideanLin A) (cgR A b x₀) := by
      rw [hq]; exact Krylov.grade_smul (toEuclideanLin A) _ (inv_ne_zero h0)
    have hal : ∀ j, Lanczos.alpha (toEuclideanLin A) (WithLp.toLp 2 q₁) j =
        Lanczos.alpha (toEuclideanLin A) (cgR A b x₀) j :=
      fun j => by simp only [Lanczos.alpha, Arnoldi.coeff, hvs]
    have hbe : ∀ j, Lanczos.beta (toEuclideanLin A) (WithLp.toLp 2 q₁) j =
        Lanczos.beta (toEuclideanLin A) (cgR A b x₀) j :=
      fun j => by simp only [Lanczos.beta, Arnoldi.w, Arnoldi.coeff, hvs]
    set L := Id.run (GolubVanLoan.Chapter10.algorithm_10_1_1 pure A q₁ fuel)
    have hk' : L.k = min fuel (Krylov.grade (toEuclideanLin A) (cgR A b x₀)) := by
      rw [← hgr]; exact hk
    refine ⟨hk', fun j hj => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hvec j hj
      refine ⟨?_, by rw [h2, hal], by rw [h3, hbe]⟩
      rw [h1, WithLp.toLp_ofLp, hvs]
    · have hgpos : 0 < Krylov.grade (toEuclideanLin A) (cgR A b x₀) :=
        Krylov.grade_pos_of_ne_zero _ _ fun h => h0 (by rw [hβ₀, h, norm_zero])
      have hd : L.done = true ↔ 0 < L.k ∧ L.beta (L.k - 1) = 0 :=
        algorithm_10_1_1_done A q₁ fuel
      rw [hd]
      constructor
      · rintro ⟨hpos, hb⟩
        obtain ⟨-, -, h3⟩ := hvec (L.k - 1) (by omega)
        have h4 : Lanczos.beta (toEuclideanLin A) (cgR A b x₀) (L.k - 1) = 0 := by
          rw [← hbe, ← h3, hb]
        rw [Lanczos.beta_eq_zero_iff (cgR A b x₀)] at h4
        omega
      · intro hle
        have hpos : 0 < L.k := by omega
        refine ⟨hpos, ?_⟩
        obtain ⟨-, -, h3⟩ := hvec (L.k - 1) (by omega)
        rw [h3, hbe, Lanczos.beta_eq_zero_iff (cgR A b x₀)]
        omega

/-- After the exact run of (11.3.14), the iterate is $x_0 + Q_kT_k^{-1}(\beta_0e_1)$ for the final
Lanczos state, computed by the tridiagonal solve. -/
private theorem preliminaryCG_x (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    (Id.run (preliminaryCG pure A b x₀ fuel)).x =
      x₀ + lanczosBasis (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos *ᵥ
        Id.run (tridiagSolve pure (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.k
          (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.alpha
          (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.beta
          (Krylov.firstVec (pcgBeta₀ A b x₀)
            (Id.run (preliminaryCG pure A b x₀ fuel)).lanczos.k)) := by
  rw [preliminaryCG_run]
  induction fuel with
  | zero =>
    have h0 : ∀ (L : GolubVanLoan.Chapter10.LanczosState n) (y : Fin L.k → ℝ), L.k = 0 →
        lanczosBasis L *ᵥ y = 0 := by
      intro L y hL
      ext i
      simp only [mulVec, dotProduct, Pi.zero_apply]
      exact Finset.sum_eq_zero fun j _ => absurd j.2 (by omega)
    rw [List.range_zero, List.foldl_nil, h0 (pcgInit A b x₀) _ rfl, add_zero]
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      preliminaryCGBody_x]
    split_ifs with h
    · have hfix := preliminaryCGBody_lanczos A (pcgBeta₀ A b x₀) x₀
        ((List.range t).foldl
          (fun s _ => Id.run (preliminaryCGBody pure A (pcgBeta₀ A b x₀) x₀ s))
          ⟨pcgInit A b x₀, x₀⟩)
      simp only [GolubVanLoan.Chapter10.lanczosStep, h, ↓reduceIte, Id.run_pure] at hfix
      rw [hfix]
      exact ih
    · rfl

/-- **Equation (11.3.14)** of [golub2013matrix], exact semantics. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $b, x_0 \in \mathbb{R}^n$
and $r_0 = b - Ax_0$, and let $k_*$ be the grade of $r_0$. The exact run of the preliminary CG
method with `fuel` passes returns a state with the following properties.

* The step count is $k = \min(\mathrm{fuel}, k_*)$.
* The iterate $x_k$ is the Galerkin iterate of step $k$, the minimizer of $\phi$ over
  $x_0 + \mathcal{K}(A, r_0, k)$.
* For $j < k$, the stored $q_{j+1}$, $\alpha_{j+1}$ and $\beta_{j+1}$ are the Lanczos vector and
  the Lanczos coefficients of $r_0$.
* The test $\beta_k \neq 0$ has failed if and only if $k_* \le k$.

The Lanczos vectors are `Arnoldi.vec (Matrix.toEuclideanLin A) r₀ j` and the coefficients are
`Lanczos.alpha` and `Lanczos.beta`, all 0-based. The proof applies
`GolubVanLoan.Chapter10.algorithm_10_1_1_spec` to $q_1 = r_0/\beta_0$,
`GolubVanLoan.Chapter11.cg_lanczos_coordinates` to the iterate, and `Lanczos.beta_eq_zero_iff`
to the test. -/
theorem equation_11_3_14 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    let s := Id.run (preliminaryCG pure A b x₀ fuel)
    let T := toEuclideanLin A
    let r₀ : 𝔼 n := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
    s.lanczos.k = min fuel (Krylov.grade T r₀) ∧
      Krylov.IsGalerkinIterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.lanczos.k
        (WithLp.toLp 2 s.x) ∧
      (∀ j < s.lanczos.k, WithLp.toLp 2 (s.lanczos.q j) = Arnoldi.vec T r₀ j ∧
        s.lanczos.alpha j = Lanczos.alpha T r₀ j ∧ s.lanczos.beta j = Lanczos.beta T r₀ j) ∧
      (s.lanczos.done = true ↔ Krylov.grade T r₀ ≤ s.lanczos.k) := by
  intro s T r₀
  have hsym : A.IsSymm := isHermitian_iff_isSymm.1 hA.isHermitian
  obtain ⟨hk, hvec, hdone⟩ := preliminaryCG_lanczos_spec hsym b x₀ fuel
  refine ⟨hk, ?_, hvec, hdone⟩
  set L := s.lanczos with hL
  have hkg : L.k ≤ Krylov.grade T r₀ := by rw [hk]; exact min_le_right _ _
  -- `T_k` is the Lanczos tridiagonal of `r₀`
  have htri : lanczosTridiag L = Lanczos.tridiag T r₀ L.k := by
    ext i j
    rw [Lanczos.tridiag_apply]
    simp only [lanczosTridiag, tridiagonalOfNat, of_apply]
    split_ifs <;> first
      | rfl
      | (exfalso; omega)
      | exact (hvec _ i.2).2.1
      | exact (hvec _ i.2).2.2
      | exact (hvec _ j.2).2.2
      | (rw [show (i : ℕ) - 1 = (j : ℕ) by omega]; exact (hvec _ j.2).2.2)
  set y := Id.run (tridiagSolve pure L.k L.alpha L.beta (Krylov.firstVec (pcgBeta₀ A b x₀) L.k))
  have hy : Lanczos.tridiag T r₀ L.k *ᵥ y = Krylov.firstVec ‖r₀‖ L.k := by
    have hβ₀ : pcgBeta₀ A b x₀ = ‖r₀‖ := by
      simp only [r₀, T, toEuclideanLin_toLp, ← WithLp.toLp_sub]
      rfl
    have hpd : (lanczosTridiag L).PosDef := by rw [htri]; exact lanczos_tridiag_posDef hA r₀ hkg
    rw [← htri, ← hβ₀]
    exact tridiagSolve_spec L.k L.alpha L.beta hpd _
  have hx : WithLp.toLp 2 s.x =
      WithLp.toLp 2 x₀ + ∑ j, y j • Arnoldi.vec T r₀ j := by
    rw [preliminaryCG_x, WithLp.toLp_add]
    congr 1
    have hq : ∀ j : Fin L.k, Arnoldi.vec T r₀ j = WithLp.toLp 2 (L.q j) :=
      fun j => ((hvec j j.2).1).symm
    simp_rw [hq, ← WithLp.toLp_smul, ← WithLp.toLp_sum]
    congr 1
    ext i
    simp [lanczosBasis, mulVec, dotProduct, Finset.sum_apply, mul_comm, y, L, s]
  rw [hx]
  exact (cg_lanczos_coordinates hA (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hkg y).2 hy

/-- **Theorem 11.3.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b, x_0 \in \mathbb{R}^n$ and $r_0 = b - Ax_0$, and let $k_*$ be the
dimension of the smallest invariant subspace of $A$ that contains $r_0$. Then the conjugate
gradient iteration (11.3.14) terminates with $x_{k_*} = x_*$. Precisely, the space
$\mathcal{K}_\infty = \operatorname{span}\{A^ir_0 : i \ge 0\}$ is invariant under $A$, contains
$r_0$, and is contained in every invariant subspace of $A$ that contains $r_0$; and if `fuel`
$\ge k_* = \dim \mathcal{K}_\infty$, then the exact run of (11.3.14) stops after exactly $k_*$
passes, through its test, with $Ax = b$.

The space $\mathcal{K}_\infty$ is `Krylov.fullSubspace (Matrix.toEuclideanLin A) r₀`, and the
invariant subspaces are `Module.End.invtSubmodule`. The proof combines
`GolubVanLoan.Chapter11.equation_11_3_14` with `Krylov.IsGalerkinIterate.apply_eq_of_grade_le`. -/
theorem theorem_11_3_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {fuel : ℕ}
    (hfuel : Module.finrank ℝ (Krylov.fullSubspace (toEuclideanLin A)
      (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))) ≤ fuel) :
    let s := Id.run (preliminaryCG pure A b x₀ fuel)
    let T := toEuclideanLin A
    let r₀ : 𝔼 n := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
    (Krylov.fullSubspace T r₀ ∈ Module.End.invtSubmodule T ∧ r₀ ∈ Krylov.fullSubspace T r₀ ∧
      ∀ W ∈ Module.End.invtSubmodule T, r₀ ∈ W → Krylov.fullSubspace T r₀ ≤ W) ∧
      s.lanczos.k = Module.finrank ℝ (Krylov.fullSubspace T r₀) ∧ s.lanczos.done = true ∧
      A *ᵥ s.x = b := by
  intro s T r₀
  obtain ⟨hk, hgal, -, hdone⟩ := equation_11_3_14 hA b x₀ fuel
  have hk' : s.lanczos.k = Krylov.grade T r₀ := by
    rw [hk]; exact min_eq_right hfuel
  refine ⟨⟨Krylov.fullSubspace_mem_invtSubmodule T r₀,
    Submodule.subset_span ⟨0, by simp⟩,
    fun W hW hr => Krylov.fullSubspace_le_of_mem_invtSubmodule T r₀ hW hr⟩, hk',
    hdone.2 hk'.ge, ?_⟩
  have h := hgal.apply_eq_of_grade_le hk'.ge
  rw [toEuclideanLin_toLp] at h
  exact WithLp.toLp_injective 2 h

end PreliminaryCG

/-! ### §11.3.5: the $LDL^T$ recurrences -/

section LDL

/-- **Equation (11.3.15)** of [golub2013matrix], as a definition. For real sequences $\alpha$ and
$\beta$, the $LDL^T$ factors of the symmetric tridiagonal matrix with diagonal $\alpha$ and
off-diagonal $\beta$ are given by
$$d_1 = \alpha_1, \qquad \ell_{i-1} = \beta_{i-1}/d_{i-1}, \quad d_i = \alpha_i -
  \ell_{i-1}\beta_{i-1} \quad (i = 2, \dots, k).$$
The definition returns the pair $(d, \ell)$ of sequences.

The sequences are indexed by `ℕ` from $0$, and they do not depend on $k$. The pivots are the
backbone's Thomas recurrence `Matrix.thomasAlpha` for the tridiagonal matrix with sub- and
superdiagonal $\beta$. A zero pivot $d_{i-1}$ gives $\ell_{i-1} = 0$, by the convention
$x/0 = 0$. -/
noncomputable def ldlTridiag (α β : ℕ → ℝ) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (Matrix.thomasAlpha α (fun i => β (i - 1)) β,
    fun i => β i / Matrix.thomasAlpha α (fun i => β (i - 1)) β i)

/-- The first pivot of (11.3.15) is $d_1 = \alpha_1$. -/
theorem ldlTridiag_fst_zero (α β : ℕ → ℝ) : (ldlTridiag α β).1 0 = α 0 := rfl

/-- For every $i \ge 1$, the pivots of (11.3.15) satisfy $d_{i+1} = \alpha_{i+1} - \ell_i\beta_i$.
-/
theorem ldlTridiag_fst_succ (α β : ℕ → ℝ) (i : ℕ) :
    (ldlTridiag α β).1 (i + 1) = α (i + 1) - (ldlTridiag α β).2 i * β i := rfl

/-- For every $i \ge 1$, the multipliers of (11.3.15) satisfy $\ell_i = \beta_i/d_i$. -/
theorem ldlTridiag_snd (α β : ℕ → ℝ) (i : ℕ) :
    (ldlTridiag α β).2 i = β i / (ldlTridiag α β).1 i := rfl

/-- **Equation (11.3.15)** of [golub2013matrix]. Let $\alpha$ and $\beta$ be real sequences and
$k \in \mathbb{N}$, let $T_k$ be the $k \times k$ symmetric tridiagonal matrix with diagonal
$\alpha_1, \dots, \alpha_k$ and off-diagonal $\beta_1, \dots, \beta_{k-1}$, and let $d$ and
$\ell$ be given by the recurrence (11.3.15). If the pivots $d_1, \dots, d_{k-1}$ are nonzero,
then
$$T_k = L_kD_kL_k^T,$$
where $L_k$ is unit lower bidiagonal with subdiagonal $\ell_1, \dots, \ell_{k-1}$ and
$D_k = \operatorname{diag}(d_1, \dots, d_k)$.

The source obtains (11.3.15) by comparing coefficients in $T_k = L_kD_kL_k^T$. The matrix $T_k$
is `Matrix.symmTridiagonalOf α β k`, and the Lanczos $T_k$ is `Lanczos.tridiag`, of this form
with the Lanczos coefficients. The factorization is `Matrix.IsLDM`, and the proof is
`GolubVanLoan.Chapter04.tridiagonal_ldlt` (§4.3.6, the same recurrence). For positive definite
$T_k$ the pivots are positive (`Matrix.IsLDM.diag_pos_of_posDef`) and the factorization is
unique (`Matrix.IsLDM.eq_of_isSymm`). -/
theorem equation_11_3_15 (α β : ℕ → ℝ) (k : ℕ)
    (hd : ∀ i, i + 1 < k → (ldlTridiag α β).1 i ≠ 0) :
    Matrix.IsLDM (Matrix.symmTridiagonalOf α β k)
      (Matrix.lowerBidiagonalOf (fun i => (ldlTridiag α β).2 (i - 1)) k)
      (Matrix.diagonal fun i : Fin k => (ldlTridiag α β).1 i)
      (Matrix.lowerBidiagonalOf (fun i => (ldlTridiag α β).2 (i - 1)) k) := by
  have hL : Matrix.lowerBidiagonalOf (fun i => (ldlTridiag α β).2 (i - 1)) k =
      Matrix.thomasLower α (fun i => β (i - 1)) β k := by
    ext i j
    simp only [Matrix.lowerBidiagonalOf, Matrix.thomasLower, Matrix.of_apply]
    split_ifs with h1 h2
    · rfl
    · rw [← h2]; rfl
    · rfl
  have hA' : Matrix.symmTridiagonalOf α β k =
      Matrix.tridiagonalOfNat α (fun i => β (i - 1)) β k := by
    ext i j
    simp only [Matrix.symmTridiagonalOf, Matrix.tridiagonalOfNat, Matrix.of_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
  rw [hL, hA']
  exact Chapter04.tridiagonal_ldlt α β k hd

/-- The entries $\nu_1, \nu_2, \dots$ of the vectors $v_k$, by the recurrence (11.3.20):
$\nu_1 = \beta_0/d_1$, and $\nu_k = -d_{k-1}\ell_{k-1}\nu_{k-1}/d_k$ for $k > 1$. The sequence
is indexed from $0$. -/
noncomputable def cgLDLnu (α β : ℕ → ℝ) (β₀ : ℝ) : ℕ → ℝ
  | 0 => β₀ / (ldlTridiag α β).1 0
  | i + 1 => -((ldlTridiag α β).1 i * (ldlTridiag α β).2 i * cgLDLnu α β β₀ i) /
      (ldlTridiag α β).1 (i + 1)

/-- **Equation (11.3.16)** of [golub2013matrix]. The vector
$v_k = (\nu_1, \dots, \nu_k) \in \mathbb{R}^k$ with $L_kD_kv_k = \beta_0e_1$, given by its
entries.

The entries are `GolubVanLoan.Chapter11.cgLDLnu`, which is forward substitution on the lower
bidiagonal matrix $L_kD_k$. That they solve the system is
`GolubVanLoan.Chapter11.equation_11_3_19`. -/
noncomputable def cgLDLv (α β : ℕ → ℝ) (β₀ : ℝ) (k : ℕ) : Fin k → ℝ :=
  fun i => cgLDLnu α β β₀ i

/-- **Equation (11.3.19)** of [golub2013matrix]. Let $\alpha$ and $\beta$ be real sequences and
$\beta_0 \in \mathbb{R}$, let $d_i$ and $\ell_i$ be the pivots and multipliers of (11.3.15), and
let $\nu_i$ be the entries of (11.3.20). Then the entries satisfy the rows of the lower
bidiagonal system $L_kD_kv_k = \beta_0e_1$ of (11.3.16):
$$d_1\nu_1 = \beta_0 \text{ if } d_1 \neq 0, \qquad d_i\ell_i\nu_i + d_{i+1}\nu_{i+1} = 0 \text{
  if } d_{i+1} \neq 0 \quad (i \ge 1).$$
Moreover, $v_{k+1} = [v_k; \nu_{k+1}]$ for every $k \ge 0$.

**Typo.** The source prints the conclusion as $v_k = [\nu_1; \dots; \nu_{k-1}/\nu_k]$, which is
garbled. The intended statement is $v_k = [v_{k-1}; \nu_k]$.

The source illustrates the system for $k = 4$. The extension $v_{k+1} = [v_k; \nu_{k+1}]$ holds
because forward substitution does not change the earlier entries when the system grows. -/
theorem equation_11_3_19 (α β : ℕ → ℝ) (β₀ : ℝ) (k : ℕ) :
    ((ldlTridiag α β).1 0 ≠ 0 → (ldlTridiag α β).1 0 * cgLDLnu α β β₀ 0 = β₀) ∧
      (∀ i, (ldlTridiag α β).1 (i + 1) ≠ 0 →
        (ldlTridiag α β).1 i * (ldlTridiag α β).2 i * cgLDLnu α β β₀ i +
          (ldlTridiag α β).1 (i + 1) * cgLDLnu α β β₀ (i + 1) = 0) ∧
      cgLDLv α β β₀ (k + 1) = Fin.snoc (cgLDLv α β β₀ k) (cgLDLnu α β β₀ k) := by
  refine ⟨fun h => ?_, fun i h => ?_, ?_⟩
  · simp only [cgLDLnu]
    field_simp
  · simp only [cgLDLnu]
    field_simp
    ring
  · funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [cgLDLv]
    · simp [cgLDLv]

/-- **Equation (11.3.20)** of [golub2013matrix]. Let $\alpha$ and $\beta$ be real sequences and
$\beta_0 \in \mathbb{R}$. For $k \ge 1$ the last entry of $v_k$ is $\nu_k$, and
$$\nu_k = \begin{cases} \beta_0/d_1 & k = 1, \\ -d_{k-1}\ell_{k-1}\nu_{k-1}/d_k & k > 1.
  \end{cases}$$
If moreover $d_{k-1} \neq 0$, then $\nu_k = -\beta_{k-1}\nu_{k-1}/d_k$, which is the form that
Algorithm 11.3.2 uses.

The last form follows from $d_{k-1}\ell_{k-1} = \beta_{k-1}$. -/
theorem equation_11_3_20 (α β : ℕ → ℝ) (β₀ : ℝ) (k : ℕ) :
    cgLDLv α β β₀ (k + 1) (Fin.last k) = cgLDLnu α β β₀ k ∧
      cgLDLnu α β β₀ 0 = β₀ / (ldlTridiag α β).1 0 ∧
      (∀ i, cgLDLnu α β β₀ (i + 1) = -((ldlTridiag α β).1 i * (ldlTridiag α β).2 i *
        cgLDLnu α β β₀ i) / (ldlTridiag α β).1 (i + 1)) ∧
      ∀ i, (ldlTridiag α β).1 i ≠ 0 →
        cgLDLnu α β β₀ (i + 1) = -(β i * cgLDLnu α β β₀ i) / (ldlTridiag α β).1 (i + 1) := by
  refine ⟨rfl, rfl, fun i => rfl, fun i h => ?_⟩
  rw [cgLDLnu, ldlTridiag_snd, mul_div_cancel₀ _ h]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The columns $c_1, c_2, \dots$ of $C_k$, by the recurrence (11.3.22): $c_1 = q_1$, and
$c_k = q_k - \ell_{k-1}c_{k-1}$ for $k > 1$. The sequence is indexed from $0$, and its vectors
lie in any real vector space. -/
noncomputable def cgLDLc (q : ℕ → E) (ℓ : ℕ → ℝ) : ℕ → E
  | 0 => q 0
  | i + 1 => q (i + 1) - ℓ i • cgLDLc q ℓ i

/-- **Equation (11.3.17)** of [golub2013matrix]. The matrix $C_k \in \mathbb{R}^{n \times k}$ with
$C_kL_k^T = Q_k$, given as its family of columns $c_1, \dots, c_k$ from the recurrence
(11.3.22).

The matrix $Q_k = [q_1 | \cdots | q_k]$ is given by its columns $q$, for CG the Lanczos vectors
`Arnoldi.vec (Matrix.toEuclideanLin A) r₀`, and $L_k$ is given by its subdiagonal $\ell$. That
the columns satisfy $C_kL_k^T = Q_k$, column by column $c_j + \ell_{j-1}c_{j-1} = q_j$, is
`GolubVanLoan.Chapter11.equation_11_3_21`. -/
noncomputable def cgLDLC (q : ℕ → E) (ℓ : ℕ → ℝ) (k : ℕ) : Fin k → E :=
  fun j => cgLDLc q ℓ j

/-- **Equation (11.3.18)** of [golub2013matrix]. Let $E$ be a real vector space, let
$q_1, q_2, \dots \in E$, let $\ell$ and $y$ be real sequences, let $x_0 \in E$ and
$k \in \mathbb{N}$, and let $c_j$ be the columns of $C_k$ from (11.3.22). Then
$$x_0 + Q_ky = x_0 + C_k(L_k^Ty),$$
where $(L_k^Ty)_j = y_j + \ell_jy_{j+1}$ for $j < k$ and $(L_k^Ty)_k = y_k$.

The source states that if $C_kL_k^T = Q_k$, then $x_k = x_0 + Q_ky_k = x_0 + C_kL_k^Ty_k = x_0 +
C_kv_k$. With $y = y_k$, the solution of $T_ky = \beta_0e_1$
(`GolubVanLoan.Chapter11.cg_lanczos_coordinates`), and $v_k = L_k^Ty_k$, the left side is the
Galerkin iterate. The products are finite sums over the indices $0, \dots, k - 1$. -/
theorem equation_11_3_18 (q : ℕ → E) (ℓ : ℕ → ℝ) (x₀ : E) (y : ℕ → ℝ) (k : ℕ) :
    x₀ + ∑ j ∈ Finset.range k, y j • q j =
      x₀ + ∑ j ∈ Finset.range k,
        (y j + if j + 1 < k then ℓ j * y (j + 1) else 0) • cgLDLc q ℓ j := by
  congr 1
  -- `∑_{j ≤ m} y_j q_j = ∑_{j ≤ m} y_j c_j + ∑_{j < m} ℓ_j y_{j+1} c_j`
  have key : ∀ m, ∑ j ∈ Finset.range (m + 1), y j • q j =
      ∑ j ∈ Finset.range (m + 1), y j • cgLDLc q ℓ j +
        ∑ j ∈ Finset.range m, (ℓ j * y (j + 1)) • cgLDLc q ℓ j := by
    intro m
    induction m with
    | zero => simp [cgLDLc]
    | succ m ih =>
      have hq : q (m + 1) = cgLDLc q ℓ (m + 1) + ℓ m • cgLDLc q ℓ m := by
        rw [cgLDLc, sub_add_cancel]
      rw [Finset.sum_range_succ (fun j => y j • q j) (m + 1), ih,
        Finset.sum_range_succ (fun j => y j • cgLDLc q ℓ j) (m + 1),
        Finset.sum_range_succ (fun j => (ℓ j * y (j + 1)) • cgLDLc q ℓ j) m, hq, smul_add,
        smul_smul, mul_comm (y (m + 1)) (ℓ m)]
      abel
  rcases k with _ | m
  · simp
  · rw [key, Finset.sum_congr rfl fun j _ => add_smul _ _ _, Finset.sum_add_distrib,
      Finset.sum_range_succ (fun j => (if j + 1 < m + 1 then ℓ j * y (j + 1) else 0) •
        cgLDLc q ℓ j)]
    simp only [show ¬(m + 1 < m + 1) from lt_irrefl _, ↓reduceIte, zero_smul, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 < m + 1 := by have := Finset.mem_range.1 hj; omega
    simp only [hj', ↓reduceIte]

/-- **Equations (11.3.21)–(11.3.22)** of [golub2013matrix]. Let $E$ be a real vector space, let
$q_1, q_2, \dots \in E$, let $\ell$ be a real sequence, and let $c_j$ be given by (11.3.22).
Then $C_{k+1} = [C_k | c_{k+1}]$ for every $k \ge 0$, and the columns solve $C_kL_k^T = Q_k$
column by column:
$$c_1 = q_1, \qquad c_{j+1} + \ell_jc_j = q_{j+1} \quad (j \ge 1).$$

The source concludes from (11.3.21) that $C_k = [C_{k-1} | c_k]$. -/
theorem equation_11_3_21 (q : ℕ → E) (ℓ : ℕ → ℝ) (k : ℕ) :
    cgLDLC q ℓ (k + 1) = Fin.snoc (cgLDLC q ℓ k) (cgLDLc q ℓ k) ∧
      cgLDLc q ℓ 0 = q 0 ∧ ∀ j, cgLDLc q ℓ (j + 1) + ℓ j • cgLDLc q ℓ j = q (j + 1) := by
  refine ⟨?_, rfl, fun j => by rw [cgLDLc, sub_add_cancel]⟩
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [cgLDLC]
  · simp [cgLDLC]

/-- **Equation (11.3.22)** of [golub2013matrix]. Let $E$ be a real vector space, let
$q_1, q_2, \dots \in E$, and let $\ell$ be a real sequence. The columns $c_k$ satisfy
$$c_k = \begin{cases} q_1 & k = 1, \\ q_k - \ell_{k-1}c_{k-1} & k > 1. \end{cases}$$
-/
theorem equation_11_3_22 (q : ℕ → E) (ℓ : ℕ → ℝ) :
    cgLDLc q ℓ 0 = q 0 ∧ ∀ i, cgLDLc q ℓ (i + 1) = q (i + 1) - ℓ i • cgLDLc q ℓ i :=
  ⟨rfl, fun _ => rfl⟩

/-- **Section 11.3.5** of [golub2013matrix], the update of $x_k$. Let $E$ be a real vector space,
let $\alpha$ and $\beta$ be real sequences, $\beta_0 \in \mathbb{R}$, $q_1, q_2, \dots \in E$
and $x_0 \in E$, and let $x_k = x_0 + C_kv_k$, with $v_k$ from (11.3.16) and $C_k$ from
(11.3.17) for the multipliers $\ell$ of (11.3.15). Then for every $k \ge 0$
$$x_{k+1} = x_k + \nu_{k+1}c_{k+1}.$$

The source derives $x_k = x_0 + C_kv_k = x_0 + C_{k-1}v_{k-1} + \nu_kc_k = x_{k-1} + \nu_kc_k$
from (11.3.19) and (11.3.21). The product $C_kv_k$ is the sum $\sum_{j \le k} \nu_jc_j$. -/
theorem cgLDL_x_succ (α β : ℕ → ℝ) (β₀ : ℝ) (q : ℕ → E) (x₀ : E) (k : ℕ) :
    x₀ + ∑ j ∈ Finset.range (k + 1),
        cgLDLnu α β β₀ j • cgLDLc q (ldlTridiag α β).2 j =
      (x₀ + ∑ j ∈ Finset.range k, cgLDLnu α β β₀ j • cgLDLc q (ldlTridiag α β).2 j) +
        cgLDLnu α β β₀ k • cgLDLc q (ldlTridiag α β).2 k := by
  rw [Finset.sum_range_succ, add_assoc]

end LDL

/-! ### Algorithm 11.3.2: CG, Lanczos version -/

section LanczosCG

variable {M : Type → Type} [Monad M]

/-- The exact run of Chapter 10's `GolubVanLoan.Chapter10.vecDiv`, the source's $r/\beta$, divides
each entry by $\beta$. -/
private theorem vecDiv_run (v : Fin n → ℝ) (β : ℝ) :
    Id.run (GolubVanLoan.Chapter10.vecDiv pure v β) = fun i => v i / β := by
  rw [GolubVanLoan.Chapter10.vecDiv_spec]
  funext i
  simp [div_eq_inv_mul]

/-- The state of Algorithm 11.3.2: the step count $k$, the iterate $x_k$, the Lanczos vector $q_k$
($0$ before the first step), the Lanczos residual $r_k$ and $\beta_k = \|r_k\|_2$, the last
$\alpha_k$, the last pivot $d_k$, the last $\nu_k$, the direction $c_k$, and the flag `done` of
the `while` test. -/
structure LanczosCGState (n : ℕ) where
  /-- The number of completed steps. -/
  k : ℕ
  /-- The iterate $x_k$. -/
  x : Fin n → ℝ
  /-- The Lanczos vector $q_k$. -/
  q : Fin n → ℝ
  /-- The Lanczos residual $r_k = Aq_k - \alpha_kq_k - \beta_{k-1}q_{k-1}$. -/
  r : Fin n → ℝ
  /-- The number $\beta_k = \|r_k\|_2$. -/
  β : ℝ
  /-- The coefficient $\alpha_k = q_k^TAq_k$. -/
  α : ℝ
  /-- The pivot $d_k$. -/
  d : ℝ
  /-- The coefficient $\nu_k$ of the update $x_k = x_{k-1} + \nu_kc_k$. -/
  ν : ℝ
  /-- The direction $c_k$. -/
  c : Fin n → ℝ
  /-- The flag that records that the `while` test $\beta_k \neq 0$ has failed. -/
  done : Bool

/-- The `if k = 1 … else … end` block of Algorithm 11.3.2. From $\alpha_k$, $\beta_{k-1}$,
$d_{k-1}$, $\nu_{k-1}$, $c_{k-1}$ and $q_k$ it computes the new $(d_k, \nu_k, c_k)$: in the
first step $d_1 = \alpha_1$, $\nu_1 = \beta_0/d_1$ and $c_1 = q_1$; otherwise
$\ell_{k-1} = \beta_{k-1}/d_{k-1}$, $d_k = \alpha_k - \beta_{k-1}\ell_{k-1}$,
$\nu_k = -\beta_{k-1}\nu_{k-1}/d_k$ and $c_k = q_k - \ell_{k-1}c_{k-1}$. -/
noncomputable def lanczosCGUpdate (rnd : ℝ → M ℝ) (first : Bool) (α β d ν : ℝ)
    (c q : Fin n → ℝ) : M (ℝ × ℝ × (Fin n → ℝ)) :=
  if first then do
    let ν' ← rnd (β / α)
    pure (α, ν', q)
  else do
    let ℓ ← rnd (β / d)
    let t ← rnd (β * ℓ)
    let d' ← rnd (α - t)
    let u ← rnd (β * ν)
    let ν' ← rnd (-u / d')
    let c' ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-ℓ) c q
    pure (d', ν', c')

/-- One pass of the `while` body of Algorithm 11.3.2. It does nothing once `done` is set, sets
`done` if the computed $\beta_k$ is zero, and otherwise makes one step of the algorithm. -/
noncomputable def lanczosCGBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s : LanczosCGState n) : M (LanczosCGState n) :=
  if s.done then pure s else
    if s.β = 0 then pure { s with done := true } else do
      let q ← GolubVanLoan.Chapter10.vecDiv rnd s.r s.β
      let Aq ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A q 0
      let α ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd q Aq
      let o ← lanczosCGUpdate rnd (decide (s.k = 0)) α s.β s.d s.ν s.c q
      let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd o.2.1 o.2.2 s.x
      let r₁ ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-α) q Aq
      let r ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-s.β) s.q r₁
      let β ← GolubVanLoan.Chapter10.vecNorm rnd r
      pure ⟨s.k + 1, x, q, r, β, α, o.1, o.2.1, o.2.2, false⟩

/-- **Algorithm 11.3.2** of [golub2013matrix] (conjugate gradients, Lanczos version). If
$A \in \mathbb{R}^{n \times n}$ is symmetric positive definite, $b \in \mathbb{R}^n$ and
$Ax_0 \approx b$, the algorithm computes $x_* \in \mathbb{R}^n$ with $Ax_* = b$.
```
k = 0, r₀ = b − Ax₀, β₀ = ‖r₀‖₂, q₀ = 0, c₀ = 0
while β_k ≠ 0
    q_{k+1} = r_k/β_k
    k = k + 1
    α_k = q_kᵀAq_k
    if k = 1
        d₁ = α₁, ν₁ = β₀/d₁
        c_k = q₁
    else
        ℓ_{k−1} = β_{k−1}/d_{k−1}, d_k = α_k − β_{k−1}ℓ_{k−1}, ν_k = −β_{k−1}ν_{k−1}/d_k
        c_k = q_k − ℓ_{k−1}c_{k−1}
    end
    x_k = x_{k−1} + ν_kc_k
    r_k = Aq_k − α_kq_k − β_{k−1}q_{k−1}
    β_k = ‖r_k‖₂
end
x_* = x_k
```
The norms and the divisions $r_k/\beta_k$ are Chapter 10's `GolubVanLoan.Chapter10.vecNorm` and
`GolubVanLoan.Chapter10.vecDiv`, the other vector operations are Algorithms 1.1.1–1.1.3, and
every arithmetic result is rounded.

The `while` loop runs at most `fuel` times, with the body
`GolubVanLoan.Chapter11.lanczosCGBody`. The program makes no check on $A$. -/
noncomputable def algorithm_11_3_2 (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : Fin n → ℝ) (fuel : ℕ) : M (LanczosCGState n) := do
  let r₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let β₀ ← GolubVanLoan.Chapter10.vecNorm rnd r₀
  (List.range fuel).foldlM (fun s _ => lanczosCGBody rnd A s) ⟨0, x₀, 0, r₀, β₀, 0, 0, 0, 0, false⟩

/-- The exact run of the `if k = 1 … else … end` block of Algorithm 11.3.2. -/
private theorem lanczosCGUpdate_run (first : Bool) (α β d ν : ℝ) (c q : Fin n → ℝ) :
    Id.run (lanczosCGUpdate pure first α β d ν c q) =
      if first then (α, β / α, q)
      else (α - β * (β / d), -(β * ν) / (α - β * (β / d)), q + (-(β / d)) • c) := by
  cases first <;>
    simp [lanczosCGUpdate, GolubVanLoan.Chapter01.algorithm_1_1_2_spec]

/-- The new Lanczos vector $q_{k+1} = r_k/\beta_k$ of an exact step. -/
private noncomputable def lcgQ (s : LanczosCGState n) : Fin n → ℝ := fun i => s.r i / s.β

/-- The new coefficient $\alpha_{k+1} = q_{k+1}^TAq_{k+1}$ of an exact step. -/
private noncomputable def lcgAlpha (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) : ℝ :=
  lcgQ s ⬝ᵥ (A *ᵥ lcgQ s)

/-- The new pivot $d_{k+1}$ of an exact step. -/
private noncomputable def lcgD (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) : ℝ :=
  if s.k = 0 then lcgAlpha A s else lcgAlpha A s - s.β * (s.β / s.d)

/-- The new coefficient $\nu_{k+1}$ of an exact step. -/
private noncomputable def lcgNu (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) : ℝ :=
  if s.k = 0 then s.β / lcgAlpha A s else -(s.β * s.ν) / lcgD A s

/-- The new direction $c_{k+1}$ of an exact step. -/
private noncomputable def lcgC (s : LanczosCGState n) : Fin n → ℝ :=
  if s.k = 0 then lcgQ s else lcgQ s + (-(s.β / s.d)) • s.c

/-- The new Lanczos residual $r_{k+1}$ of an exact step. -/
private noncomputable def lcgR (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) :
    Fin n → ℝ :=
  A *ᵥ lcgQ s + (-lcgAlpha A s) • lcgQ s + (-s.β) • s.q

/-- One exact step of Algorithm 11.3.2, for $\beta_k \neq 0$. -/
private noncomputable def lanczosCGStep (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) :
    LanczosCGState n :=
  ⟨s.k + 1, s.x + lcgNu A s • lcgC s, lcgQ s, lcgR A s, √(lcgR A s ⬝ᵥ lcgR A s), lcgAlpha A s,
    lcgD A s, lcgNu A s, lcgC s, false⟩

/-- The exact run of one pass of the body of Algorithm 11.3.2. -/
private theorem lanczosCGBody_run (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) :
    Id.run (lanczosCGBody pure A s) =
      if s.done then s else if s.β = 0 then { s with done := true } else lanczosCGStep A s := by
  unfold lanczosCGBody
  by_cases hd : s.done
  · simp only [hd, ↓reduceIte, Id.run_pure]
  · by_cases h0 : s.β = 0
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_pure]
    · by_cases hk : s.k = 0
      · simp only [hd, h0, hk, Bool.false_eq_true, ↓reduceIte, decide_true, Id.run_bind,
          Id.run_pure, vecDiv_run, lanczosCGUpdate_run, GolubVanLoan.Chapter10.vecNorm,
          GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
          GolubVanLoan.Chapter01.algorithm_1_1_2_spec, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
          zero_add, lanczosCGStep, lcgD, lcgNu, lcgC]
        rfl
      · simp only [hd, h0, hk, Bool.false_eq_true, ↓reduceIte, decide_false, Id.run_bind,
          Id.run_pure, vecDiv_run, lanczosCGUpdate_run, GolubVanLoan.Chapter10.vecNorm,
          GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
          GolubVanLoan.Chapter01.algorithm_1_1_2_spec, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
          zero_add, lanczosCGStep, lcgD, lcgNu, lcgC]
        rfl

/-- The exact run of Algorithm 11.3.2 with no pass of the loop. -/
private theorem algorithm_11_3_2_run_zero (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    Id.run (algorithm_11_3_2 pure A b x₀ 0) =
      ⟨0, x₀, 0, b - A *ᵥ x₀, √((b - A *ᵥ x₀) ⬝ᵥ (b - A *ᵥ x₀)), 0, 0, 0, 0, false⟩ := by
  simp only [algorithm_11_3_2, GolubVanLoan.Chapter10.vecNorm, Id.run_bind, Id.run_pure,
    GolubVanLoan.Chapter01.algorithm_1_1_3_spec, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
    List.range_zero, List.foldlM_nil, mulVec_neg, ← sub_eq_add_neg]

/-- The exact run of Algorithm 11.3.2 with $m + 1$ passes is one pass of the body after the run with
$m$ passes. -/
private theorem algorithm_11_3_2_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (m : ℕ) : Id.run (algorithm_11_3_2 pure A b x₀ (m + 1)) =
      Id.run (lanczosCGBody pure A (Id.run (algorithm_11_3_2 pure A b x₀ m))) := by
  simp only [algorithm_11_3_2, GolubVanLoan.Chapter10.vecNorm, Id.run_bind, Id.run_pure,
    GolubVanLoan.Chapter01.algorithm_1_1_1_spec]
  exact List.idRun_foldlM_range_succ _ _ _

/-- The data of the state of Algorithm 11.3.2 after step $i + 1$, in backbone terms: the Lanczos
vector, residual and coefficients of $r_0$, the $LDL^T$ pivot, and the relations
$d = 1/\alpha^{CG}_i$, $\nu = (-1)^i\|r_i\|\alpha^{CG}_i$ and $c = (-1)^i\|r_i\|^{-1}p_i$ to the
CG quantities. -/
@[reducible] private def LCGData (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (i : ℕ)
    (s : LanczosCGState n) : Prop :=
  WithLp.toLp 2 s.q = Arnoldi.vec (toEuclideanLin A) (cgR A b x₀) i ∧
    WithLp.toLp 2 s.r = Arnoldi.w (toEuclideanLin A) (cgR A b x₀) i ∧
    s.β = Lanczos.beta (toEuclideanLin A) (cgR A b x₀) i ∧
    s.α = Lanczos.alpha (toEuclideanLin A) (cgR A b x₀) i ∧
    s.d = (ldlTridiag (Lanczos.alpha (toEuclideanLin A) (cgR A b x₀))
      (Lanczos.beta (toEuclideanLin A) (cgR A b x₀))).1 i ∧
    s.d = (CG.alpha (toEuclideanLin A) (cgIt A b x₀ i))⁻¹ ∧
    s.ν = (-1) ^ i * ‖(cgIt A b x₀ i).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ i) ∧
    WithLp.toLp 2 s.c = ((-1) ^ i * ‖(cgIt A b x₀ i).r‖⁻¹) • (cgIt A b x₀ i).p

/-- The state of Algorithm 11.3.2 after $j$ steps, in backbone terms. -/
@[reducible] private def LCGInv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (j : ℕ)
    (s : LanczosCGState n) : Prop :=
  s.k = j ∧ WithLp.toLp 2 s.x = (cgIt A b x₀ j).x ∧
    (j = 0 → s.q = 0 ∧ WithLp.toLp 2 s.r = cgR A b x₀ ∧ s.β = ‖cgR A b x₀‖) ∧
    ∀ i, j = i + 1 → LCGData A b x₀ i s

/-- For positive definite $A$, the CG step length $\alpha_j$ is positive while the residual $r_j$ is
nonzero. -/
private theorem cg_alpha_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {j : ℕ} (hr : (cgIt A b x₀ j).r ≠ 0) : 0 < CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have h1 := CG.re_inner_apply_direction_pos (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT hr
  rw [RCLike.re_to_real] at h1
  exact div_pos (real_inner_self_pos.2 hr) h1

/-- For the CG states of a positive definite $A$, $\alpha_j\,p_j^TAp_j = \|r_j\|^2$. -/
private theorem cg_alpha_mul {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (j : ℕ) : CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
      ⟪toEuclideanLin A (cgIt A b x₀ j).p, (cgIt A b x₀ j).p⟫ = ‖(cgIt A b x₀ j).r‖ ^ 2 := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  rw [CG.alpha, ← real_inner_self_eq_norm_sq]
  by_cases hr : (cgIt A b x₀ j).r = 0
  · rw [hr, inner_zero_left, zero_div, zero_mul]
  · have h1 := CG.re_inner_apply_direction_pos (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT hr
    rw [RCLike.re_to_real] at h1
    exact div_mul_cancel₀ _ h1.ne'

/-- Below the grade of $r_0$, the state before one exact step of Algorithm 11.3.2 has
$\beta_k \neq 0$, and the step preserves the invariant. -/
private theorem lanczosCGStep_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x₀ : Fin n → ℝ) {j : ℕ} {s : LanczosCGState n} (hs : LCGInv A b x₀ j s)
    (hj : j < Krylov.grade (toEuclideanLin A) (cgR A b x₀)) :
    s.β ≠ 0 ∧ LCGInv A b x₀ (j + 1) (lanczosCGStep A s) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hsym := hT.isSymmetric
  obtain ⟨hk, hx, h0, hsucc⟩ := hs
  have hrj : (cgIt A b x₀ j).r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ hj
  have hαj : 0 < CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) := cg_alpha_pos hA b x₀ hrj
  have hρj : ‖(cgIt A b x₀ j).r‖ ≠ 0 := norm_ne_zero_iff.2 hrj
  have hQdiv : lcgQ s = s.β⁻¹ • s.r := by funext t; simp [lcgQ, div_eq_inv_mul]
  -- `β_j ≠ 0`, and `q_{j+1}` is the next Lanczos vector
  have hβq : s.β ≠ 0 ∧
      WithLp.toLp 2 (lcgQ s) = Arnoldi.vec (toEuclideanLin A) (cgR A b x₀) j := by
    rcases j with _ | i
    · obtain ⟨-, hr, hb⟩ := h0 rfl
      have hR : cgR A b x₀ ≠ 0 := hrj
      refine ⟨by rw [hb]; exact norm_ne_zero_iff.2 hR, ?_⟩
      have hv := Arnoldi.vec_zero (toEuclideanLin A) (cgR A b x₀) hR
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hv
      rw [hv, hQdiv, WithLp.toLp_smul, hr, hb]
    · obtain ⟨-, hr, hb, -⟩ := hsucc i rfl
      refine ⟨fun h => (not_le.2 hj) ((Lanczos.beta_eq_zero_iff _ _).1 (hb.symm.trans h)),
        ?_⟩
      have hv := Arnoldi.vec_succ_eq (toEuclideanLin A) (cgR A b x₀) i
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hv
      rw [hv, hQdiv, WithLp.toLp_smul, hr, hb]
      rfl
  obtain ⟨hβne, hqv⟩ := hβq
  have hα : lcgAlpha A s = Lanczos.alpha (toEuclideanLin A) (cgR A b x₀) j := by
    rw [lcgAlpha, ← inner_toLp, ← toEuclideanLin_toLp, hqv, Lanczos.alpha, Arnoldi.coeff,
      RCLike.re_to_real]
  have hr' : WithLp.toLp 2 (lcgR A s) = Arnoldi.w (toEuclideanLin A) (cgR A b x₀) j := by
    rw [lcgR, WithLp.toLp_add, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul,
      ← toEuclideanLin_toLp, hqv, hα]
    rcases j with _ | i
    · have hc := Lanczos.coe_alpha (cgR A b x₀) hsym 0
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hc
      rw [(h0 rfl).1, WithLp.toLp_zero, smul_zero, add_zero, Arnoldi.w, zero_add,
        Finset.sum_range_one, ← hc, neg_smul, ← sub_eq_add_neg]
    · obtain ⟨hq, -, hb, -⟩ := hsucc i rfl
      have hw := Lanczos.w_succ_eq (cgR A b x₀) hsym i
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hw
      rw [hq, hb, hw, neg_smul, neg_smul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  have hβ' : √(lcgR A s ⬝ᵥ lcgR A s) = Lanczos.beta (toEuclideanLin A) (cgR A b x₀) j := by
    rw [sqrt_dotProduct_self, hr']
    rfl
  -- the `LDLᵀ` and CG data of the new state
  have hnew : lcgD A s = (ldlTridiag (Lanczos.alpha (toEuclideanLin A) (cgR A b x₀))
        (Lanczos.beta (toEuclideanLin A) (cgR A b x₀))).1 j ∧
      lcgD A s = (CG.alpha (toEuclideanLin A) (cgIt A b x₀ j))⁻¹ ∧
      lcgNu A s = (-1) ^ j * ‖(cgIt A b x₀ j).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) ∧
      WithLp.toLp 2 (lcgC s) =
        ((-1) ^ j * ‖(cgIt A b x₀ j).r‖⁻¹) • (cgIt A b x₀ j).p := by
    rcases j with _ | i
    · have hk0 : s.k = 0 := hk
      obtain ⟨-, -, hb⟩ := h0 rfl
      have hR : cgR A b x₀ ≠ 0 := hrj
      have hla0 := CG.lanczos_alpha_zero_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT hrj
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hla0
      have hv0 := Arnoldi.vec_zero (toEuclideanLin A) (cgR A b x₀) hR
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hv0
      have hR0 : (cgIt A b x₀ 0).r = cgR A b x₀ := rfl
      have hP0 : (cgIt A b x₀ 0).p = cgR A b x₀ := rfl
      have hd : lcgD A s = (CG.alpha (toEuclideanLin A) (cgIt A b x₀ 0))⁻¹ := by
        simp only [lcgD, hk0, ↓reduceIte]
        rw [hα, hla0]
      refine ⟨?_, hd, ?_, ?_⟩
      · simp only [lcgD, hk0, ↓reduceIte]
        rw [hα, ldlTridiag_fst_zero]
      · simp only [lcgNu, hk0, ↓reduceIte]
        rw [hR0, hb, hα, hla0, div_inv_eq_mul, pow_zero, one_mul]
      · simp only [lcgC, hk0, ↓reduceIte]
        rw [hqv, hR0, hP0, pow_zero, one_mul, hv0]
    · have hk' : s.k ≠ 0 := by omega
      obtain ⟨-, -, hb, -, hd1, hd2, hν, hc⟩ := hsucc i rfl
      have hri : (cgIt A b x₀ i).r ≠ 0 :=
        CG.residual_ne_zero_of_lt_grade _ _ (Nat.lt_of_succ_lt hj)
      have hαi : 0 < CG.alpha (toEuclideanLin A) (cgIt A b x₀ i) := cg_alpha_pos hA b x₀ hri
      have hρi : ‖(cgIt A b x₀ i).r‖ ≠ 0 := norm_ne_zero_iff.2 hri
      have hlb := CG.lanczos_beta_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (k := i) hrj
      rw [RCLike.re_to_real] at hlb
      have hla := CG.lanczos_alpha_succ_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (k := i) hrj
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hla
      have hbeta : CG.beta (toEuclideanLin A) (cgIt A b x₀ i) =
          ‖(cgIt A b x₀ (i + 1)).r‖ ^ 2 / ‖(cgIt A b x₀ i).r‖ ^ 2 := by
        rw [CG.beta_iterate, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      have hd : lcgD A s = (CG.alpha (toEuclideanLin A) (cgIt A b x₀ (i + 1)))⁻¹ := by
        simp only [lcgD, hk', ↓reduceIte]
        rw [hα, hb, hd2, hla, hbeta, hlb]
        field_simp
        ring
      refine ⟨?_, hd, ?_, ?_⟩
      · simp only [lcgD, hk', ↓reduceIte]
        rw [hα, hb, hd1, ldlTridiag_fst_succ, ldlTridiag_snd]
        ring
      · have hdd := hd
        simp only [lcgNu, hk', ↓reduceIte]
        rw [hdd, hb, hν, hlb]
        field_simp
        ring
      · have hv := CG.arnoldi_vec_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (i + 1) hrj
        simp only [RCLike.ofReal_real_eq_id, id_eq] at hv
        simp only [lcgC, hk', ↓reduceIte]
        rw [WithLp.toLp_add, WithLp.toLp_smul, hqv, hv, hc, hb, hd2, hlb, CG.iterate_succ_p,
          hbeta, smul_add, smul_smul, smul_smul]
        congr 2
        field_simp
        ring
  obtain ⟨hd1, hd2, hν, hc⟩ := hnew
  have hsgn : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  refine ⟨hβne, show s.k + 1 = j + 1 by rw [hk], ?_, fun h => absurd h (Nat.succ_ne_zero j),
    fun i hi => ?_⟩
  · change WithLp.toLp 2 (s.x + lcgNu A s • lcgC s) = _
    rw [WithLp.toLp_add, WithLp.toLp_smul, hx, hc, hν, smul_smul, CG.iterate_succ_x]
    congr 2
    rw [show (-1 : ℝ) ^ j * ‖(cgIt A b x₀ j).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
        ((-1) ^ j * ‖(cgIt A b x₀ j).r‖⁻¹) = ((-1) ^ j * (-1) ^ j) *
          (‖(cgIt A b x₀ j).r‖ * ‖(cgIt A b x₀ j).r‖⁻¹) *
          CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) by ring,
      hsgn, mul_inv_cancel₀ hρj, one_mul, one_mul]
  · obtain rfl : i = j := by omega
    exact ⟨hqv, hr', hβ', hα, hd1, hd2, hν, hc⟩

/-- The loop invariant of the exact run of Algorithm 11.3.2: after $m$ passes the state is the state
after $\min(m, k_*)$ steps, where $k_*$ is the grade of $r_0$, and `done` is set if and only if
$k_* < m$. -/
private theorem algorithm_11_3_2_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x₀ : Fin n → ℝ) (m : ℕ) :
    LCGInv A b x₀ (min m (Krylov.grade (toEuclideanLin A) (cgR A b x₀)))
        (Id.run (algorithm_11_3_2 pure A b x₀ m)) ∧
      (Id.run (algorithm_11_3_2 pure A b x₀ m)).done =
        decide (Krylov.grade (toEuclideanLin A) (cgR A b x₀) < m) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  set g := Krylov.grade (toEuclideanLin A) (cgR A b x₀)
  induction m with
  | zero =>
    rw [algorithm_11_3_2_run_zero, Nat.zero_min]
    refine ⟨⟨rfl, rfl, fun _ => ⟨rfl, ?_, ?_⟩, fun i h => absurd h (by omega)⟩,
      (decide_eq_false (Nat.not_lt_zero g)).symm⟩
    · change WithLp.toLp 2 (b - A *ᵥ x₀) = _
      rw [WithLp.toLp_sub, ← toEuclideanLin_toLp]
    · change √((b - A *ᵥ x₀) ⬝ᵥ (b - A *ᵥ x₀)) = _
      rw [sqrt_dotProduct_self, WithLp.toLp_sub, ← toEuclideanLin_toLp]
  | succ m ih =>
    obtain ⟨hinv, hd⟩ := ih
    rw [algorithm_11_3_2_run_succ, lanczosCGBody_run]
    set s := Id.run (algorithm_11_3_2 pure A b x₀ m)
    rcases lt_or_ge g m with hgm | hmg
    · -- the loop had already stopped
      have hdone : s.done = true := hd.trans (decide_eq_true hgm)
      simp only [hdone, ↓reduceIte]
      rw [min_eq_right hgm.le] at hinv
      rw [min_eq_right (by omega : g ≤ m + 1)]
      exact ⟨hinv, (decide_eq_true (by omega)).symm⟩
    · have hdone : s.done = false := hd.trans (decide_eq_false (by omega))
      rcases hmg.eq_or_lt with hmg | hmg
      · -- the test fails at the grade
        rw [hmg, min_self] at hinv
        have hβ : s.β = 0 := by
          obtain ⟨-, -, h0, hsucc⟩ := hinv
          rcases Nat.eq_zero_or_eq_succ_pred g with hg0 | hg1
          · rw [(h0 hg0).2.2, norm_eq_zero]
            have := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
              (k := 0) (by omega)
            exact this
          · rw [(hsucc (g - 1) hg1).2.2.1]
            exact (Lanczos.beta_eq_zero_iff _ _).2 (by omega)
        simp only [hdone, Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_left hβ, min_eq_right (by omega : g ≤ m + 1)]
        exact ⟨hinv, (decide_eq_true (by omega : g < m + 1)).symm⟩
      · -- a step
        rw [min_eq_left hmg.le] at hinv
        obtain ⟨hβ, hstep⟩ := lanczosCGStep_inv hA b x₀ hinv hmg
        simp only [hdone, hβ, Bool.false_eq_true, ↓reduceIte]
        rw [min_eq_left (by omega : m + 1 ≤ g)]
        exact ⟨hstep, (decide_eq_false (by omega)).symm⟩

/-- **Algorithm 11.3.2** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive definite, let $b, x_0 \in \mathbb{R}^n$ and $r_0 = b - Ax_0$, and let
$k_*$ be the grade of $r_0$. Let $x^{CG}_i$, $r_i$, $p_i$ and $\alpha^{CG}_i$ be the iterate,
residual, direction and step length of the CG state after $i$ steps. The exact run with `fuel`
passes returns a state with the following properties.

* The step count is $k = \min(\mathrm{fuel}, k_*)$, and the iterate is $x_k = x^{CG}_k$.
* If $k = i + 1 \ge 1$, then $q_k$ is the Lanczos vector $q_{i+1}$ of $r_0$, $r_k$ is the
  Lanczos residual, $\alpha_k$ and $\beta_k$ are the Lanczos coefficients, $d_k$ is the pivot of
  (11.3.15) for the Lanczos $T_k$, and $d_k = 1/\alpha^{CG}_i$,
  $\nu_k = (-1)^i\|r_i\|\alpha^{CG}_i$ and $c_k = (-1)^i\|r_i\|^{-1}p_i$.
* If the loop exits through its test, then $Ax = b$.

In particular $\nu_kc_k = \alpha^{CG}_ip_i$, so the update $x_k = x_{k-1} + \nu_kc_k$ is the CG
update $x^{CG}_{i+1} = x^{CG}_i + \alpha^{CG}_ip_i$. The CG states are `CG.iterate` (0-based),
the Lanczos vector is `Arnoldi.vec`, the Lanczos residual is `Arnoldi.w`, and the coefficients
are `Lanczos.alpha` and `Lanczos.beta`. The identification uses the dictionary
`CG.arnoldi_vec_eq`, `CG.lanczos_alpha_zero_eq`, `CG.lanczos_alpha_succ_eq` and
`CG.lanczos_beta_eq`. -/
theorem algorithm_11_3_2_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    let s := Id.run (algorithm_11_3_2 pure A b x₀ fuel)
    let T := toEuclideanLin A
    let r₀ : 𝔼 n := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
    let it := CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
    s.k = min fuel (Krylov.grade T r₀) ∧ WithLp.toLp 2 s.x = (it s.k).x ∧
      (∀ i, s.k = i + 1 →
        WithLp.toLp 2 s.q = Arnoldi.vec T r₀ i ∧ WithLp.toLp 2 s.r = Arnoldi.w T r₀ i ∧
        s.β = Lanczos.beta T r₀ i ∧ s.α = Lanczos.alpha T r₀ i ∧
        s.d = (ldlTridiag (Lanczos.alpha T r₀) (Lanczos.beta T r₀)).1 i ∧
        s.d = (CG.alpha T (it i))⁻¹ ∧ s.ν = (-1) ^ i * ‖(it i).r‖ * CG.alpha T (it i) ∧
        WithLp.toLp 2 s.c = ((-1) ^ i * ‖(it i).r‖⁻¹) • (it i).p) ∧
      (s.done = true → A *ᵥ s.x = b) := by
  intro s T r₀ it
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  obtain ⟨⟨hk, hx, -, hsucc⟩, hd⟩ := algorithm_11_3_2_inv hA b x₀ fuel
  refine ⟨hk, by rw [hk]; exact hx, fun i hi => hsucc i (hk.symm.trans hi), fun hdone => ?_⟩
  have hgf : Krylov.grade (toEuclideanLin A) (cgR A b x₀) < fuel :=
    of_decide_eq_true (hd.symm.trans hdone)
  have hr0 := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
    (k := min fuel (Krylov.grade (toEuclideanLin A) (cgR A b x₀))) (by omega)
  have h0 : WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 s.x) = 0 := by
    rw [hx, ← CG.residual_eq, hr0]
  rw [toEuclideanLin_toLp, ← WithLp.toLp_sub, WithLp.toLp_eq_zero, sub_eq_zero] at h0
  exact h0.symm

/-- For every $j \in \mathbb{N}$, $(-1)^j(-1)^j = 1$. -/
private theorem neg_one_pow_mul_self (j : ℕ) : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by
  rw [← mul_pow]; norm_num

/-- The gradient of the $m$-th CG iterate is minus its residual: $g_m = Ax_m - b = -r_m$. -/
private theorem cg_gradient_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (m : ℕ) :
    toEuclideanLin A (cgIt A b x₀ m).x - WithLp.toLp 2 b = -(cgIt A b x₀ m).r := by
  rw [CG.residual_eq, neg_sub]

/-- **Theorem 11.3.4** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b, x_0 \in \mathbb{R}^n$, and let $k_*$ be the grade of
$r_0 = b - Ax_0$. For $i \le k_*$, let $x_i$ be the iterate of Algorithm 11.3.2 after $i$ steps
and $g_i = Ax_i - b$. If $0 \le i < j \le k_*$, then
$$g_i^Tg_j = 0,$$
and $g_j = \nu_jr_j$, where $\nu_j$ and $r_j$ are computed by the algorithm.

**Generalization.** The source states the orthogonality for $1 \le i < j \le k$. It holds also
for $i = 0$.

The iterate after $i$ steps is the output of the exact run with `fuel` $= i$; for $i \le k_*$
this run makes exactly $i$ steps (`GolubVanLoan.Chapter11.algorithm_11_3_2_spec`). -/
theorem theorem_11_3_4 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {i j : ℕ} (hij : i < j) (hj : j ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀)) :
    (A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ i)).x - b) ⬝ᵥ
        (A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ j)).x - b) = 0 ∧
      A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ j)).x - b =
        (Id.run (algorithm_11_3_2 pure A b x₀ j)).ν •
          (Id.run (algorithm_11_3_2 pure A b x₀ j)).r := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  -- `toLp (Ax_m − b) = −r_m` for `m ≤ grade`
  have hg : ∀ m, m ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀) →
      WithLp.toLp 2 (A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ m)).x - b) =
        -(cgIt A b x₀ m).r := by
    intro m hm
    obtain ⟨⟨-, hx, -, -⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ m
    rw [min_eq_left hm] at hx
    rw [WithLp.toLp_sub, ← toEuclideanLin_toLp, hx, cg_gradient_eq]
  refine ⟨?_, ?_⟩
  · rw [← inner_toLp, hg i (hij.le.trans hj), hg j hj, inner_neg_neg]
    exact CG.inner_residual_eq_zero _ _ hT hij.ne
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    obtain ⟨⟨-, -, -, hsucc⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ (m + 1)
    rw [min_eq_left hj] at hsucc
    obtain ⟨-, hr, -, -, -, -, hν, -⟩ := hsucc m rfl
    apply WithLp.toLp_injective 2
    rw [hg _ hj, WithLp.toLp_smul, hr, hν]
    -- `w_m = β_m q_{m+1}`
    have hw := Arnoldi.vec_succ_eq (toEuclideanLin A) (cgR A b x₀) m
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hw
    have hwn : Arnoldi.w (toEuclideanLin A) (cgR A b x₀) m =
        Lanczos.beta (toEuclideanLin A) (cgR A b x₀) m •
          Arnoldi.vec (toEuclideanLin A) (cgR A b x₀) (m + 1) := by
      by_cases h0 : Arnoldi.w (toEuclideanLin A) (cgR A b x₀) m = 0
      · rw [h0, Lanczos.beta, h0, norm_zero, zero_smul]
      · rw [hw, smul_smul, Lanczos.beta, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
    rcases hj.lt_or_eq with hlt | heq
    · have hrm1 : (cgIt A b x₀ (m + 1)).r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ hlt
      have hrm : (cgIt A b x₀ m).r ≠ 0 :=
        CG.residual_ne_zero_of_lt_grade _ _ (Nat.lt_of_succ_lt hlt)
      have hαm := cg_alpha_pos hA b x₀ hrm
      have hρm : ‖(cgIt A b x₀ m).r‖ ≠ 0 := norm_ne_zero_iff.2 hrm
      have hρm1 : ‖(cgIt A b x₀ (m + 1)).r‖ ≠ 0 := norm_ne_zero_iff.2 hrm1
      have hlb := CG.lanczos_beta_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (k := m) hrm1
      rw [RCLike.re_to_real] at hlb
      have hv := CG.arnoldi_vec_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (m + 1) hrm1
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hv
      rw [hwn, hv, hlb, smul_smul, smul_smul, ← neg_one_smul ℝ (cgIt A b x₀ (m + 1)).r]
      congr 1
      rw [show (-1 : ℝ) ^ m * ‖(cgIt A b x₀ m).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ m) *
          (‖(cgIt A b x₀ (m + 1)).r‖ /
            (‖(cgIt A b x₀ m).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ m))) *
          ((-1) ^ (m + 1) * ‖(cgIt A b x₀ (m + 1)).r‖⁻¹) =
          -((-1) ^ m * (-1) ^ m) *
            ((‖(cgIt A b x₀ m).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ m)) /
              (‖(cgIt A b x₀ m).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ m))) *
            (‖(cgIt A b x₀ (m + 1)).r‖ * ‖(cgIt A b x₀ (m + 1)).r‖⁻¹) by ring,
        neg_one_pow_mul_self, div_self (mul_ne_zero hρm hαm.ne'), mul_inv_cancel₀ hρm1]
      ring
    · have hβ0 : Lanczos.beta (toEuclideanLin A) (cgR A b x₀) m = 0 :=
        (Lanczos.beta_eq_zero_iff _ _).2 heq.ge
      have hr0 := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
        (k := m + 1) heq.ge
      rw [hwn, hβ0, zero_smul, smul_zero, hr0, neg_zero]

/-- **Theorem 11.3.5** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b, x_0 \in \mathbb{R}^n$, and let $k_*$ be the grade of
$r_0 = b - Ax_0$. For $1 \le i \le k_*$, let $c_i$ and $d_i$ be the direction and the pivot that
Algorithm 11.3.2 computes in step $i$. Then for $1 \le i, j \le k_*$
$$c_i^TAc_j = \begin{cases} d_j & i = j, \\ 0 & i \neq j. \end{cases}$$

**Typo.** The source states the range $1 \le i < j \le k$, which excludes the case $i = j$ that
its statement covers. The range here is $1 \le i, j \le k$.

The quantities $c_i$ and $d_j$ are read off the exact runs with `fuel` $= i$ and `fuel` $= j$. -/
theorem theorem_11_3_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hig : i ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀))
    (hjg : j ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀)) :
    (Id.run (algorithm_11_3_2 pure A b x₀ i)).c ⬝ᵥ
        (A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ j)).c) =
      if i = j then (Id.run (algorithm_11_3_2 pure A b x₀ j)).d else 0 := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨⟨-, -, -, hsi⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ (i' + 1)
  obtain ⟨⟨-, -, -, hsj⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ (j' + 1)
  rw [min_eq_left hig] at hsi
  rw [min_eq_left hjg] at hsj
  obtain ⟨-, -, -, -, -, hdj, -, hcj⟩ := hsj j' rfl
  obtain ⟨-, -, -, -, -, -, -, hci⟩ := hsi i' rfl
  rw [← inner_toLp, ← toEuclideanLin_toLp, hci, hcj, map_smul, real_inner_smul_left,
    real_inner_smul_right]
  split_ifs with hij
  · obtain rfl : i' = j' := by omega
    have hr : (cgIt A b x₀ i').r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ (by omega)
    have hα := cg_alpha_pos hA b x₀ hr
    have hρ : ‖(cgIt A b x₀ i').r‖ ≠ 0 := norm_ne_zero_iff.2 hr
    have hX : ⟪(cgIt A b x₀ i').p, toEuclideanLin A (cgIt A b x₀ i').p⟫ =
        ‖(cgIt A b x₀ i').r‖ ^ 2 / CG.alpha (toEuclideanLin A) (cgIt A b x₀ i') := by
      rw [real_inner_comm, eq_div_iff hα.ne', mul_comm, cg_alpha_mul hA b x₀ i']
    rw [hX, hdj, show (-1 : ℝ) ^ i' * ‖(cgIt A b x₀ i').r‖⁻¹ *
        ((-1) ^ i' * ‖(cgIt A b x₀ i').r‖⁻¹ *
          (‖(cgIt A b x₀ i').r‖ ^ 2 / CG.alpha (toEuclideanLin A) (cgIt A b x₀ i'))) =
        ((-1) ^ i' * (-1) ^ i') * (‖(cgIt A b x₀ i').r‖⁻¹ * ‖(cgIt A b x₀ i').r‖) ^ 2 *
          (CG.alpha (toEuclideanLin A) (cgIt A b x₀ i'))⁻¹ by ring,
      neg_one_pow_mul_self, inv_mul_cancel₀ hρ, one_pow, one_mul, one_mul]
  · have hne : i' ≠ j' := fun h => hij (by rw [h])
    rw [← hT.isSymmetric, CG.inner_apply_direction_eq_zero _ _ hT hne, mul_zero, mul_zero]

/-- **Equation (11.3.23)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b, x_0 \in \mathbb{R}^n$, and let $k_*$ be the grade of
$r_0 = b - Ax_0$. Let $x_j$, $p^{CG}_j$ and $\beta^{CG}_j$ be the iterates, search directions
and update coefficients of CG, indexed from $0$, let $g_j = Ax_j - b$, and let the
Hestenes–Stiefel directions be $p_{j+1} = -p^{CG}_j$. Then $p_1 = g_0$,
$$p_{j+2} = g_{j+1} + \tau_{j+1}p_{j+1} \quad \text{with } \tau_{j+1} = \beta^{CG}_j \quad (j
  \ge 0),$$
and, if $k + 1 \le k_*$, then $p_{k+1} = \sigma c_{k+1}$ for some $\sigma \neq 0$, where
$c_{k+1}$ is the direction of Algorithm 11.3.2 after $k + 1$ steps.

The source writes the recurrence as $p_k = g_{k-1} + \tau_{k-1}p_{k-1}$, and argues that $p_k$
is a multiple of $c_k$ because $q_k$ is a multiple of $g_{k-1}$. The minus sign in
$p_{j+1} = -p^{CG}_j$ appears because the backbone's directions carry the sign of the residual. -/
theorem equation_11_3_23 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {k : ℕ} (hk : k + 1 ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀)) :
    -(cgIt A b x₀ 0).p = toEuclideanLin A (cgIt A b x₀ 0).x - WithLp.toLp 2 b ∧
      (∀ j, -(cgIt A b x₀ (j + 1)).p =
        (toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b) +
          CG.beta (toEuclideanLin A) (cgIt A b x₀ j) • -(cgIt A b x₀ j).p) ∧
      ∃ σ : ℝ, σ ≠ 0 ∧
        -(cgIt A b x₀ k).p =
          σ • WithLp.toLp 2 (Id.run (algorithm_11_3_2 pure A b x₀ (k + 1))).c := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  refine ⟨by rw [cg_gradient_eq]; rfl, fun j => ?_, ?_⟩
  · rw [cg_gradient_eq, CG.iterate_succ_p, neg_add, smul_neg]
  · obtain ⟨⟨-, -, -, hs⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ (k + 1)
    rw [min_eq_left hk] at hs
    obtain ⟨-, -, -, -, -, -, -, hc⟩ := hs k rfl
    have hr : (cgIt A b x₀ k).r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ (by omega)
    have hρ : ‖(cgIt A b x₀ k).r‖ ≠ 0 := norm_ne_zero_iff.2 hr
    refine ⟨-((-1) ^ k * ‖(cgIt A b x₀ k).r‖),
      neg_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hρ), ?_⟩
    rw [hc, smul_smul, show -((-1 : ℝ) ^ k * ‖(cgIt A b x₀ k).r‖) *
        ((-1) ^ k * ‖(cgIt A b x₀ k).r‖⁻¹) =
        -(((-1) ^ k * (-1) ^ k) * (‖(cgIt A b x₀ k).r‖ * ‖(cgIt A b x₀ k).r‖⁻¹)) by ring,
      neg_one_pow_mul_self, mul_inv_cancel₀ hρ, mul_one, neg_smul, one_smul]

/-- **Equations (11.3.24)–(11.3.25)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite and $b, x_0 \in \mathbb{R}^n$, with the Hestenes–Stiefel directions
$p_{j+1} = -p^{CG}_j$, the gradients $g_j = Ax_j - b$ and the coefficients
$\tau_{j+1} = \beta^{CG}_j$ of (11.3.23). For every $j \ge 0$: if the residual $r_j$ is nonzero,
then
$$\tau_{j+1} = -\frac{p_{j+1}^TAg_{j+1}}{p_{j+1}^TAp_{j+1}};$$
and $p_{j+2}^TAg_{j+1} = p_{j+2}^TAp_{j+2}$.

The source obtains both from $Ap_k = Ag_{k-1} + \tau_{k-1}Ap_{k-1}$ and Theorem 11.3.5. In its
indices they read $\tau_{k-1} = -p_{k-1}^TAg_{k-1}/p_{k-1}^TAp_{k-1}$ and
$p_k^TAg_{k-1} = p_k^TAp_k$. The coefficient $\tau_{j+1}$ is `CG.beta` at step $j$. -/
theorem equation_11_3_24 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (j : ℕ) :
    ((cgIt A b x₀ j).r ≠ 0 → CG.beta (toEuclideanLin A) (cgIt A b x₀ j) =
      -⟪-(cgIt A b x₀ j).p,
          toEuclideanLin A (toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b)⟫ /
        ⟪-(cgIt A b x₀ j).p, toEuclideanLin A (-(cgIt A b x₀ j).p)⟫) ∧
      ⟪-(cgIt A b x₀ (j + 1)).p,
          toEuclideanLin A (toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b)⟫ =
        ⟪-(cgIt A b x₀ (j + 1)).p, toEuclideanLin A (-(cgIt A b x₀ (j + 1)).p)⟫ := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hsym := hT.isSymmetric
  simp only [cg_gradient_eq, map_neg, inner_neg_neg]
  refine ⟨fun hj => ?_, ?_⟩
  · have hpos := CG.re_inner_apply_direction_pos (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT hj
    rw [RCLike.re_to_real] at hpos
    have hconj := CG.inner_apply_direction_eq_zero (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
      (i := j) (j := j + 1) (by omega)
    rw [CG.iterate_succ_p, inner_add_right, real_inner_smul_right] at hconj
    rw [← hsym, ← hsym, eq_div_iff hpos.ne']
    linarith
  · have hconj := CG.inner_apply_direction_eq_zero (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
      (i := j + 1) (j := j) (by omega)
    have hexp : toEuclideanLin A (cgIt A b x₀ (j + 1)).p =
        toEuclideanLin A (cgIt A b x₀ (j + 1)).r +
          CG.beta (toEuclideanLin A) (cgIt A b x₀ j) • toEuclideanLin A (cgIt A b x₀ j).p := by
      rw [CG.iterate_succ_p, map_add, map_smul]
    rw [hexp, inner_add_right, real_inner_smul_right,
      ← hsym (cgIt A b x₀ (j + 1)).p (cgIt A b x₀ j).p, hconj, mul_zero, add_zero]

/-- **Equation (11.3.25)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite and $b, x_0 \in \mathbb{R}^n$, with the Hestenes–Stiefel directions
$p_{j+1} = -p^{CG}_j$ and the gradients $g_j = Ax_j - b$ of (11.3.23). Then for every $j \ge 0$,
$p_{j+2}^TAg_{j+1} = p_{j+2}^TAp_{j+2}$; in the indices of the source,
$p_k^TAg_{k-1} = p_k^TAp_k$.

This is the second part of `GolubVanLoan.Chapter11.equation_11_3_24`. -/
theorem equation_11_3_25 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (j : ℕ) :
    ⟪-(cgIt A b x₀ (j + 1)).p,
        toEuclideanLin A (toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b)⟫ =
      ⟪-(cgIt A b x₀ (j + 1)).p, toEuclideanLin A (-(cgIt A b x₀ (j + 1)).p)⟫ :=
  (equation_11_3_24 hA b x₀ j).2

/-- **Section 11.3.7** of [golub2013matrix], the Hestenes–Stiefel coefficients. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and $b, x_0 \in \mathbb{R}^n$,
with the Hestenes–Stiefel directions $p_{j+1} = -p^{CG}_j$ and the gradients $g_j = Ax_j - b$ of
(11.3.23), and let $\mu_{j+1} = \alpha^{CG}_j$ and $\tau_{j+1} = \beta^{CG}_j$ be the CG step
length and update coefficient. Then for every $j \ge 0$
$$x_{j+1} = x_j - \mu_{j+1}p_{j+1}, \qquad \mu_{j+1} = \frac{g_j^Tg_j}{p_{j+1}^TAp_{j+1}},
  \qquad \tau_{j+1} = \frac{g_{j+1}^Tg_{j+1}}{g_j^Tg_j},$$
$$g_{j+1}^Tg_{j+1} = -\mu_{j+1}g_{j+1}^TAp_{j+1}, \qquad g_j^Tg_j =
  \mu_{j+1}p_{j+1}^TAp_{j+1}.$$

In the indices of the source these are $x_k = x_{k-1} - \mu_kp_k$,
$\mu_k = g_{k-1}^Tg_{k-1}/p_k^TAp_k$, $\tau_{k-1} = g_{k-1}^Tg_{k-1}/g_{k-2}^Tg_{k-2}$,
$g_{k-1}^Tg_{k-1} = -\mu_{k-1}g_{k-1}^TAp_{k-1}$ and
$g_{k-2}^Tg_{k-2} = \mu_{k-1}p_{k-1}^TAp_{k-1}$. The step length is `CG.alpha`, and the
coefficient is `CG.beta`. -/
theorem hestenesStiefel_coeffs {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (j : ℕ) :
    (cgIt A b x₀ (j + 1)).x =
        (cgIt A b x₀ j).x - CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) • -(cgIt A b x₀ j).p ∧
      CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) =
        ⟪toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b,
            toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b⟫ /
          ⟪-(cgIt A b x₀ j).p, toEuclideanLin A (-(cgIt A b x₀ j).p)⟫ ∧
      CG.beta (toEuclideanLin A) (cgIt A b x₀ j) =
        ⟪toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b,
            toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b⟫ /
          ⟪toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b,
            toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b⟫ ∧
      ⟪toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b,
          toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b⟫ =
        -CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
          ⟪toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b,
            toEuclideanLin A (-(cgIt A b x₀ j).p)⟫ ∧
      ⟪toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b,
          toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b⟫ =
        CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
          ⟪-(cgIt A b x₀ j).p, toEuclideanLin A (-(cgIt A b x₀ j).p)⟫ := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  simp only [cg_gradient_eq, map_neg, inner_neg_neg]
  have hcomm : ⟪(cgIt A b x₀ j).p, toEuclideanLin A (cgIt A b x₀ j).p⟫ =
      ⟪toEuclideanLin A (cgIt A b x₀ j).p, (cgIt A b x₀ j).p⟫ := real_inner_comm _ _
  refine ⟨by rw [CG.iterate_succ_x, smul_neg, sub_neg_eq_add], by rw [hcomm]; rfl,
    CG.beta_iterate _ _ _ j, ?_, ?_⟩
  · have horth := CG.inner_residual_eq_zero (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
      (i := j + 1) (j := j) (by omega)
    have h2 : ⟪(cgIt A b x₀ (j + 1)).r, (cgIt A b x₀ (j + 1)).r⟫ =
        ⟪(cgIt A b x₀ (j + 1)).r, (cgIt A b x₀ j).r⟫ -
          CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
            ⟪(cgIt A b x₀ (j + 1)).r, toEuclideanLin A (cgIt A b x₀ j).p⟫ := by
      nth_rewrite 2 [CG.iterate_succ_r]
      rw [inner_sub_right, real_inner_smul_right]
    rw [h2, horth]
    ring
  · rw [hcomm, cg_alpha_mul hA b x₀ j, real_inner_self_eq_norm_sq]

end LanczosCG

/-! ### Algorithm 11.3.3 and the practical loop (11.3.26) -/

section HestenesStiefel

variable {M : Type → Type} [Monad M]

/-- The update shared by Algorithm 11.3.3 and (11.3.26). Given $\rho = r_{k-1}^Tr_{k-1}$, and after
the first step also the previous $\rho_- = r_{k-2}^Tr_{k-2}$ and direction $p_{k-1}$, it forms
the direction $p_k = r_{k-1}$ in the first step or $p_k = r_{k-1} + \tau_{k-1}p_{k-1}$ with
$\tau_{k-1} = \rho/\rho_-$, then $w = Ap_k$, $\mu_k = \rho/p_k^Tw$, $x_k = x_{k-1} + \mu_kp_k$
and $r_k = r_{k-1} - \mu_kw$. It returns $(x_k, r_k, p_k)$. -/
noncomputable def cgUpdate (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (first : Bool)
    (ρ ρprev : ℝ) (x r p : Fin n → ℝ) : M ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) := do
  let p ← if first then pure r else do
    let τ ← rnd (ρ / ρprev)
    GolubVanLoan.Chapter01.algorithm_1_1_2 rnd τ p r
  let w ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A p 0
  let pw ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd p w
  let μ ← rnd (ρ / pw)
  let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd μ p x
  let r ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-μ) w r
  pure (x, r, p)

/-- The direction that `GolubVanLoan.Chapter11.cgUpdate` forms in exact arithmetic. -/
private noncomputable def cgDir (first : Bool) (ρ ρprev : ℝ) (r p : Fin n → ℝ) : Fin n → ℝ :=
  if first then r else r + (ρ / ρprev) • p

/-- The exact run of `GolubVanLoan.Chapter11.cgUpdate`, in closed form. -/
private theorem cgUpdate_run_eq (A : Matrix (Fin n) (Fin n) ℝ) (first : Bool) (ρ ρprev : ℝ)
    (x r p : Fin n → ℝ) :
    Id.run (cgUpdate pure A first ρ ρprev x r p) =
      (x + (ρ / (cgDir first ρ ρprev r p ⬝ᵥ (A *ᵥ cgDir first ρ ρprev r p))) •
          cgDir first ρ ρprev r p,
        r + (-(ρ / (cgDir first ρ ρprev r p ⬝ᵥ (A *ᵥ cgDir first ρ ρprev r p)))) •
          (A *ᵥ cgDir first ρ ρprev r p),
        cgDir first ρ ρprev r p) := by
  cases first <;>
    simp [cgUpdate, cgDir, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
      GolubVanLoan.Chapter01.algorithm_1_1_2_spec, GolubVanLoan.Chapter01.algorithm_1_1_3_spec]

/-- The exact run of `GolubVanLoan.Chapter11.cgUpdate` is one step of the backbone CG recurrence.
Suppose that $(x, r)$ is the CG iterate and residual after $j$ steps, that $\rho = r^Tr$, and
that either the flag `first` is set and $j = 0$, or `first` is not set, $j = i + 1$, $p$ is the
CG direction $p_i$ and $\rho_- = r_i^Tr_i$. Then the output is $(x_{j+1}, r_{j+1}, p_j)$. -/
theorem cgUpdate_run (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (j : ℕ) (first : Bool)
    (ρ ρprev : ℝ) (x r p : Fin n → ℝ) (hx : WithLp.toLp 2 x = (cgIt A b x₀ j).x)
    (hr : WithLp.toLp 2 r = (cgIt A b x₀ j).r) (hρ : ρ = r ⬝ᵥ r)
    (hdir : (first = true ∧ j = 0) ∨
      (first = false ∧ ∃ i, j = i + 1 ∧ WithLp.toLp 2 p = (cgIt A b x₀ i).p ∧
        ρprev = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫)) :
    WithLp.toLp 2 (Id.run (cgUpdate pure A first ρ ρprev x r p)).1 = (cgIt A b x₀ (j + 1)).x ∧
      WithLp.toLp 2 (Id.run (cgUpdate pure A first ρ ρprev x r p)).2.1 =
        (cgIt A b x₀ (j + 1)).r ∧
      WithLp.toLp 2 (Id.run (cgUpdate pure A first ρ ρprev x r p)).2.2 = (cgIt A b x₀ j).p := by
  rw [cgUpdate_run_eq]
  have hdirp : WithLp.toLp 2 (cgDir first ρ ρprev r p) = (cgIt A b x₀ j).p := by
    rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, i, rfl, hp, hρp⟩
    · change WithLp.toLp 2 r = _
      rw [hr]
      rfl
    · change WithLp.toLp 2 (r + (ρ / ρprev) • p) = _
      rw [CG.iterate_succ_p, CG.beta_iterate, WithLp.toLp_add, WithLp.toLp_smul, hr, hp, hρ,
        hρp, ← inner_toLp, hr]
  have hρ' : ρ = ⟪(cgIt A b x₀ j).r, (cgIt A b x₀ j).r⟫ := by rw [hρ, ← inner_toLp, hr]
  have halpha : ρ / (cgDir first ρ ρprev r p ⬝ᵥ (A *ᵥ cgDir first ρ ρprev r p)) =
      CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) := by
    rw [CG.alpha, ← hρ', ← hdirp, toEuclideanLin_toLp, inner_toLp, dotProduct_comm]
  refine ⟨?_, ?_, hdirp⟩
  · change WithLp.toLp 2 (x + (ρ / (cgDir first ρ ρprev r p ⬝ᵥ (A *ᵥ cgDir first ρ ρprev r p))) •
      cgDir first ρ ρprev r p) = _
    rw [halpha, CG.iterate_succ_x, WithLp.toLp_add, WithLp.toLp_smul, hx, hdirp]
  · change WithLp.toLp 2 (r + (-(ρ / (cgDir first ρ ρprev r p ⬝ᵥ
      (A *ᵥ cgDir first ρ ρprev r p)))) • (A *ᵥ cgDir first ρ ρprev r p)) = _
    rw [halpha, CG.iterate_succ_r, WithLp.toLp_add, WithLp.toLp_smul, hr, ← hdirp,
      toEuclideanLin_toLp, neg_smul, ← sub_eq_add_neg]

/-- The state of Algorithm 11.3.3: the step count $k$, the iterate $x_k$, the residual $r_k$, the
last direction $p_k$, the last $\rho = r_{k-1}^Tr_{k-1}$, and the flag `done` of the `while`
test. -/
structure HestenesStiefelState (n : ℕ) where
  /-- The number of completed steps. -/
  k : ℕ
  /-- The iterate $x_k$. -/
  x : Fin n → ℝ
  /-- The residual $r_k = b - Ax_k$. -/
  r : Fin n → ℝ
  /-- The last search direction $p_k$. -/
  p : Fin n → ℝ
  /-- The number $r_{k-1}^Tr_{k-1}$, the numerator of the last step. -/
  ρ : ℝ
  /-- The flag that records that the `while` test $\|r_k\|_2 > 0$ has failed. -/
  done : Bool

/-- One pass of the `while` body of Algorithm 11.3.3. It does nothing once `done` is set. Otherwise
it computes $\rho = \mathrm{fl}(r_k^Tr_k)$; if $\rho = 0$ it sets `done`, which is the test
$\|r_k\|_2 > 0$ on the computed value, and else it makes the update
`GolubVanLoan.Chapter11.cgUpdate`. -/
noncomputable def hestenesStiefelBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s : HestenesStiefelState n) : M (HestenesStiefelState n) :=
  if s.done then pure s else do
    let ρ ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.r s.r
    if ρ = 0 then pure { s with done := true } else do
      let o ← cgUpdate rnd A (decide (s.k = 0)) ρ s.ρ s.x s.r s.p
      pure ⟨s.k + 1, o.1, o.2.1, o.2.2, ρ, false⟩

/-- **Algorithm 11.3.3** of [golub2013matrix] (conjugate gradients, Hestenes–Stiefel version). If
$A \in \mathbb{R}^{n \times n}$ is symmetric positive definite, $b \in \mathbb{R}^n$ and
$Ax_0 \approx b$, the algorithm computes $x_* \in \mathbb{R}^n$ with $Ax_* = b$.
```
k = 0, r₀ = b − Ax₀
while ‖r_k‖₂ > 0
    k = k + 1
    if k = 1
        p_k = r₀
    else
        τ_{k−1} = (r_{k−1}ᵀr_{k−1})/(r_{k−2}ᵀr_{k−2}),  p_k = r_{k−1} + τ_{k−1}p_{k−1}
    end
    μ_k = (r_{k−1}ᵀr_{k−1})/(p_kᵀAp_k),  x_k = x_{k−1} + μ_kp_k,  r_k = r_{k−1} − μ_kAp_k
end
x_* = x_k
```
The dot products, the matrix-vector products and the vector updates are Algorithms 1.1.1–1.1.3,
and every arithmetic result is rounded.

The `while` loop runs at most `fuel` times, with the body
`GolubVanLoan.Chapter11.hestenesStiefelBody`. The program makes no check on $A$. -/
noncomputable def algorithm_11_3_3 (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : Fin n → ℝ) (fuel : ℕ) : M (HestenesStiefelState n) := do
  let r₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  (List.range fuel).foldlM (fun s _ => hestenesStiefelBody rnd A s) ⟨0, x₀, r₀, r₀, 0, false⟩

/-- The exact initial residual $b + A(-x_0) = b - Ax_0$, computed by Algorithm 1.1.3, is the
residual of the initial CG state. -/
private theorem initial_residual (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    WithLp.toLp 2 (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b)) =
      (cgIt A b x₀ 0).r := by
  rw [GolubVanLoan.Chapter01.algorithm_1_1_3_spec, mulVec_neg, ← sub_eq_add_neg, CG.iterate_zero,
    CG.init_r, toEuclideanLin_toLp, WithLp.toLp_sub]

/-- The exact run of one pass of the body of Algorithm 11.3.3. -/
private theorem hestenesStiefelBody_run (A : Matrix (Fin n) (Fin n) ℝ)
    (s : HestenesStiefelState n) :
    Id.run (hestenesStiefelBody pure A s) =
      if s.done then s else if s.r ⬝ᵥ s.r = 0 then { s with done := true } else
        ⟨s.k + 1, (Id.run (cgUpdate pure A (decide (s.k = 0)) (s.r ⬝ᵥ s.r) s.ρ s.x s.r s.p)).1,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) (s.r ⬝ᵥ s.r) s.ρ s.x s.r s.p)).2.1,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) (s.r ⬝ᵥ s.r) s.ρ s.x s.r s.p)).2.2,
          s.r ⬝ᵥ s.r, false⟩ := by
  unfold hestenesStiefelBody
  by_cases hd : s.done
  · simp only [hd, ↓reduceIte, Id.run_pure]
  · by_cases h0 : s.r ⬝ᵥ s.r = 0
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
        GolubVanLoan.Chapter01.algorithm_1_1_1_spec]
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
        GolubVanLoan.Chapter01.algorithm_1_1_1_spec]

/-- The exact run of Algorithm 11.3.3 with no pass of the loop. -/
private theorem algorithm_11_3_3_run_zero (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    Id.run (algorithm_11_3_3 pure A b x₀ 0) =
      ⟨0, x₀, Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b),
        Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b), 0, false⟩ :=
  rfl

/-- The exact run of Algorithm 11.3.3 with $m + 1$ passes is one pass of the body after the run with
$m$ passes. -/
private theorem algorithm_11_3_3_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (m : ℕ) : Id.run (algorithm_11_3_3 pure A b x₀ (m + 1)) =
      Id.run (hestenesStiefelBody pure A (Id.run (algorithm_11_3_3 pure A b x₀ m))) := by
  simp only [algorithm_11_3_3, Id.run_bind]
  exact List.idRun_foldlM_range_succ _ _ _

/-- The state of Algorithm 11.3.3 after $j$ steps agrees with the CG state of the backbone after $j$
steps. -/
@[reducible] private def HSInv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (j : ℕ)
    (s : HestenesStiefelState n) : Prop :=
  s.k = j ∧ WithLp.toLp 2 s.x = (cgIt A b x₀ j).x ∧ WithLp.toLp 2 s.r = (cgIt A b x₀ j).r ∧
    ∀ i, j = i + 1 → WithLp.toLp 2 s.p = (cgIt A b x₀ i).p ∧
      s.ρ = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫

/-- The loop invariant of the exact run of Algorithm 11.3.3: after $m$ passes the state is the CG
state after $\min(m, k_*)$ steps, where $k_*$ is the grade of $r_0$, and `done` is set if and
only if $k_* < m$. -/
private theorem algorithm_11_3_3_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x₀ : Fin n → ℝ) (m : ℕ) :
    HSInv A b x₀ (min m (Krylov.grade (toEuclideanLin A)
        (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))))
        (Id.run (algorithm_11_3_3 pure A b x₀ m)) ∧
      (Id.run (algorithm_11_3_3 pure A b x₀ m)).done =
        decide (Krylov.grade (toEuclideanLin A)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) < m) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  set g := Krylov.grade (toEuclideanLin A) (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))
  induction m with
  | zero =>
    rw [algorithm_11_3_3_run_zero, Nat.zero_min]
    exact ⟨⟨rfl, rfl, initial_residual A b x₀, fun i h => absurd h (by omega)⟩,
      (decide_eq_false (Nat.not_lt_zero g)).symm⟩
  | succ m ih =>
    obtain ⟨⟨hk, hx, hr, hp⟩, hd⟩ := ih
    rw [algorithm_11_3_3_run_succ, hestenesStiefelBody_run]
    set s := Id.run (algorithm_11_3_3 pure A b x₀ m)
    rcases lt_or_ge g m with hgm | hmg
    · -- the loop had already stopped
      have hdone : s.done = true := hd.trans (decide_eq_true hgm)
      simp only [hdone, ↓reduceIte]
      rw [min_eq_right hgm.le] at hk hx hr hp
      rw [min_eq_right (by omega : g ≤ m + 1)]
      exact ⟨⟨hk, hx, hr, hp⟩, (decide_eq_true (by omega)).symm⟩
    · have hdone : s.done = false := hd.trans (decide_eq_false (by omega))
      rcases hmg.eq_or_lt with hmg | hmg
      · -- the test fails at the grade
        rw [hmg, min_self] at hk hx hr hp
        have hr0 : s.r = 0 := by
          have h0 := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
            (k := g) le_rfl
          exact (WithLp.toLp_eq_zero 2).1 (hr.trans h0)
        have hc : s.r ⬝ᵥ s.r = 0 := by rw [hr0, dotProduct_zero]
        simp only [hdone, hc, Bool.false_eq_true, ↓reduceIte]
        rw [min_eq_right (by omega : g ≤ m + 1)]
        exact ⟨⟨hk, hx, hr, hp⟩, (decide_eq_true (by omega : g < m + 1)).symm⟩
      · -- a step
        rw [min_eq_left hmg.le] at hk hx hr hp
        have hne : (cgIt A b x₀ m).r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ hmg
        have hc : ¬ s.r ⬝ᵥ s.r = 0 := by
          rw [dotProduct_self_eq_zero_iff]
          rintro h0
          exact hne (by rw [← hr, h0, WithLp.toLp_zero])
        simp only [hdone, hc, Bool.false_eq_true, ↓reduceIte]
        rw [min_eq_left (by omega : m + 1 ≤ g)]
        have hdir : (decide (s.k = 0) = true ∧ m = 0) ∨ (decide (s.k = 0) = false ∧
            ∃ i, m = i + 1 ∧ WithLp.toLp 2 s.p = (cgIt A b x₀ i).p ∧
              s.ρ = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫) := by
          rcases Nat.eq_zero_or_eq_succ_pred m with h0 | h1
          · exact Or.inl ⟨by rw [hk, h0]; rfl, h0⟩
          · exact Or.inr ⟨by rw [hk]; exact decide_eq_false (by omega), m - 1, h1,
              hp (m - 1) h1⟩
        obtain ⟨h1, h2, h3⟩ := cgUpdate_run A b x₀ m _ _ s.ρ s.x s.r s.p hx hr rfl hdir
        refine ⟨⟨show s.k + 1 = m + 1 by omega, h1, h2, fun i hi => ?_⟩,
          (decide_eq_false (by omega)).symm⟩
        obtain rfl : i = m := by omega
        exact ⟨h3, show s.r ⬝ᵥ s.r = _ by rw [← inner_toLp, hr]⟩

/-- **Algorithm 11.3.3** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive definite, let $b, x_0 \in \mathbb{R}^n$ and $r_0 = b - Ax_0$, and let
$k_*$ be the grade of $r_0$. The exact run with `fuel` passes makes
$k = \min(\mathrm{fuel}, k_*)$ steps; its $x$ and $r$ are the CG iterate and residual after $k$
steps; and if the loop exits through its test, then $Ax = b$.

The CG states are `CG.iterate`, indexed from $0$: the direction $p_k$ of the source is the
backbone's $p_{k-1}$. The backbone's `CG.alpha` and `CG.beta` are the coefficients $\mu$ and
$\tau$ of the source. -/
theorem algorithm_11_3_3_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    let s := Id.run (algorithm_11_3_3 pure A b x₀ fuel)
    let T := toEuclideanLin A
    let r₀ : 𝔼 n := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
    s.k = min fuel (Krylov.grade T r₀) ∧
      WithLp.toLp 2 s.x = (CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).x ∧
      WithLp.toLp 2 s.r = (CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).r ∧
      (s.done = true → A *ᵥ s.x = b) := by
  intro s T r₀
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  obtain ⟨⟨hk, hx, hr, -⟩, hd⟩ := algorithm_11_3_3_inv hA b x₀ fuel
  refine ⟨hk, by rw [hk]; exact hx, by rw [hk]; exact hr, fun hdone => ?_⟩
  have hgf : Krylov.grade (toEuclideanLin A)
      (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) < fuel :=
    of_decide_eq_true (hd.symm.trans hdone)
  have hr0 := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
    (k := min fuel (Krylov.grade (toEuclideanLin A)
      (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)))) (by omega)
  have h0 : WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 s.x) = 0 := by
    rw [hx, ← CG.residual_eq, hr0]
  rw [toEuclideanLin_toLp, ← WithLp.toLp_sub, WithLp.toLp_eq_zero, sub_eq_zero] at h0
  exact h0.symm

/-- The state of the practical CG loop (11.3.26): the step count, $x$, $r$, $p$, the current
$\rho_c = r^Tr$, the previous $\rho_-$, and the flag of the `while` test. -/
structure PracticalCGState (n : ℕ) where
  /-- The number of completed steps. -/
  k : ℕ
  /-- The iterate $x$. -/
  x : Fin n → ℝ
  /-- The residual $r = b - Ax$. -/
  r : Fin n → ℝ
  /-- The search direction $p$. -/
  p : Fin n → ℝ
  /-- The number $\rho_c = r^Tr$. -/
  ρc : ℝ
  /-- The previous value $\rho_-$ of $\rho_c$. -/
  ρm : ℝ
  /-- The flag that records that the `while` test $\sqrt{\rho_c} > \delta$ has failed. -/
  done : Bool

/-- One pass of the `while` body of (11.3.26). It does nothing once `done` is set. Otherwise it
computes $\mathrm{fl}(\sqrt{\rho_c})$ and compares it exactly with $\delta$; if the root is at
most $\delta$ it sets `done`, and else it makes the update `GolubVanLoan.Chapter11.cgUpdate` and
sets $\rho_- = \rho_c$ and $\rho_c = r^Tr$. -/
noncomputable def practicalCGBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (s : PracticalCGState n) : M (PracticalCGState n) :=
  if s.done then pure s else do
    let nrm ← rnd (√s.ρc)
    if nrm ≤ δ then pure { s with done := true } else do
      let o ← cgUpdate rnd A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p
      let ρ ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd o.2.1 o.2.1
      pure ⟨s.k + 1, o.1, o.2.1, o.2.2, ρ, s.ρc, false⟩

/-- **Equation (11.3.26)** of [golub2013matrix], the practical version of Algorithm 11.3.3 with the
stopping test $\|r\|_2 \le \mathrm{tol} \cdot \|b\|_2$.
```
k = 0, x = x₀, r = b − Ax, ρ_c = rᵀr, δ = tol · ‖b‖₂
while √ρ_c > δ
    k = k + 1
    if k = 1
        p = r
    else
        τ = ρ_c/ρ₋,  p = r + τp
    end
    w = Ap
    μ = ρ_c/pᵀw,  x = x + μp,  r = r − μw,  ρ₋ = ρ_c,  ρ_c = rᵀr
end
```
The arithmetic that feeds the test ($\|b\|_2 = \sqrt{b^Tb}$, $\delta$ and $\sqrt{\rho_c}$) is
rounded, and the comparison is exact.

The `while` loop runs at most `fuel` times, with the body
`GolubVanLoan.Chapter11.practicalCGBody`. -/
noncomputable def practicalCG (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (tol : ℝ) (fuel : ℕ) : M (PracticalCGState n) := do
  let r ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let ρ ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd r r
  let bb ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd b b
  let nb ← rnd (√bb)
  let δ ← rnd (tol * nb)
  (List.range fuel).foldlM (fun s _ => practicalCGBody rnd A δ s) ⟨0, x₀, r, r, ρ, 0, false⟩

/-- The exact run of one pass of the body of (11.3.26). -/
private theorem practicalCGBody_run (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (s : PracticalCGState n) :
    Id.run (practicalCGBody pure A δ s) =
      if s.done then s else if √s.ρc ≤ δ then { s with done := true } else
        ⟨s.k + 1, (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).1,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).2.1,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).2.2,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).2.1 ⬝ᵥ
            (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).2.1,
          s.ρc, false⟩ := by
  unfold practicalCGBody
  by_cases hd : s.done
  · simp only [hd, ↓reduceIte, Id.run_pure]
  · by_cases h0 : √s.ρc ≤ δ
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure]
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
        GolubVanLoan.Chapter01.algorithm_1_1_1_spec]

/-- The exact run of (11.3.26) with no pass of the loop. -/
private theorem practicalCG_run_zero (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (tol : ℝ) : Id.run (practicalCG pure A b x₀ tol 0) =
      ⟨0, x₀, Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b),
        Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b),
        Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b) ⬝ᵥ
          Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b), 0, false⟩ := by
  simp only [practicalCG, Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
    List.range_zero, List.foldlM_nil]

/-- The exact run of (11.3.26) with $m + 1$ passes is one pass of the body, with
$\delta = \mathrm{tol}\sqrt{b^Tb}$, after the run with $m$ passes. -/
private theorem practicalCG_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (tol : ℝ) (m : ℕ) : Id.run (practicalCG pure A b x₀ tol (m + 1)) =
      Id.run (practicalCGBody pure A (tol * √(b ⬝ᵥ b))
        (Id.run (practicalCG pure A b x₀ tol m))) := by
  simp only [practicalCG, Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_1_spec]
  exact List.idRun_foldlM_range_succ _ _ _

/-- The loop invariant of the exact run of (11.3.26) after $m$ passes, for the threshold $\delta$:
the state is the CG state after $k \le m$ steps, every earlier residual has norm greater than
$\delta$, if `done` is set then $\|r_k\| \le \delta$, and if it is not set then $k = m$. -/
@[reducible] private def PCGInv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (δ : ℝ)
    (m : ℕ) (s : PracticalCGState n) : Prop :=
  (WithLp.toLp 2 s.x = (cgIt A b x₀ s.k).x ∧ WithLp.toLp 2 s.r = (cgIt A b x₀ s.k).r ∧
    s.ρc = s.r ⬝ᵥ s.r ∧
    ∀ i, s.k = i + 1 → WithLp.toLp 2 s.p = (cgIt A b x₀ i).p ∧
      s.ρm = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫) ∧
  s.k ≤ m ∧ (∀ j < s.k, δ < ‖(cgIt A b x₀ j).r‖) ∧
  (s.done = true → ‖(cgIt A b x₀ s.k).r‖ ≤ δ) ∧ (s.done = false → s.k = m)

/-- The exact run of (11.3.26) satisfies the loop invariant above with
$\delta = \mathrm{tol}\sqrt{b^Tb}$. -/
private theorem practicalCG_inv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (tol : ℝ)
    (m : ℕ) : PCGInv A b x₀ (tol * √(b ⬝ᵥ b)) m (Id.run (practicalCG pure A b x₀ tol m)) := by
  induction m with
  | zero =>
    rw [practicalCG_run_zero]
    exact ⟨⟨rfl, initial_residual A b x₀, rfl,
        fun i h => absurd (show 0 = i + 1 from h) (by omega)⟩,
      le_rfl, fun j hj => absurd (show j < 0 from hj) (Nat.not_lt_zero j),
      fun h => by simp at h, fun _ => rfl⟩
  | succ m ih =>
    rw [practicalCG_run_succ, practicalCGBody_run]
    set s := Id.run (practicalCG pure A b x₀ tol m)
    obtain ⟨⟨hx, hr, hρc, hp⟩, hkm, hlt, hdone, hnd⟩ := ih
    have hnorm : √s.ρc = ‖(cgIt A b x₀ s.k).r‖ := by rw [hρc, sqrt_dotProduct_self, hr]
    by_cases hd : s.done
    · simp only [hd, ↓reduceIte]
      exact ⟨⟨hx, hr, hρc, hp⟩, hkm.trans (Nat.le_succ m), hlt, hdone,
        fun h => absurd (hd.symm.trans h) (by decide)⟩
    · have hkm' : s.k = m := hnd (by simpa using hd)
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      by_cases ht : √s.ρc ≤ tol * √(b ⬝ᵥ b)
      · simp only [ht, ↓reduceIte]
        exact ⟨⟨hx, hr, hρc, hp⟩, hkm.trans (Nat.le_succ m), hlt,
          fun _ => by rw [← hnorm]; exact ht, fun h => by simp at h⟩
      · simp only [ht, ↓reduceIte]
        have hdir : (decide (s.k = 0) = true ∧ s.k = 0) ∨ (decide (s.k = 0) = false ∧
            ∃ i, s.k = i + 1 ∧ WithLp.toLp 2 s.p = (cgIt A b x₀ i).p ∧
              s.ρm = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫) := by
          rcases Nat.eq_zero_or_eq_succ_pred s.k with h0 | h1
          · exact Or.inl ⟨by rw [h0]; rfl, h0⟩
          · exact Or.inr ⟨decide_eq_false (by omega), s.k - 1, h1, hp (s.k - 1) h1⟩
        obtain ⟨h1, h2, h3⟩ := cgUpdate_run A b x₀ s.k _ _ s.ρm s.x s.r s.p hx hr hρc hdir
        refine ⟨⟨h1, h2, rfl, fun i hi => ?_⟩, show s.k + 1 ≤ m + 1 by omega, fun j hj => ?_,
          fun h => by simp at h, fun _ => show s.k + 1 = m + 1 by omega⟩
        · obtain rfl : i = s.k := by
            have hi' : s.k + 1 = i + 1 := hi
            omega
          exact ⟨h3, show s.ρc = _ by rw [hρc, ← inner_toLp, hr]⟩
        · have hj' : j < s.k + 1 := hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj | rfl
          · exact hlt j hj
          · rw [← hnorm]; exact lt_of_not_ge ht

/-- **Equation (11.3.26)** of [golub2013matrix], exact semantics. Let
$A \in \mathbb{R}^{n \times n}$, $b, x_0 \in \mathbb{R}^n$ and $\mathrm{tol} \in \mathbb{R}$.
The exact run with `fuel` passes returns a state whose step count $k$ is at most `fuel`, with
the following properties.

* Its $x$ and $r$ are the CG iterate and residual after $k$ steps.
* Every earlier residual failed the test: $\|r_j\|_2 > \mathrm{tol} \cdot \|b\|_2$ for $j < k$.
* If $k <$ `fuel`, then the loop stopped through its test.
* On exit through the test, $\|b - Ax\|_2 \le \mathrm{tol} \cdot \|b\|_2$.

The statement has no hypothesis on $A$. The CG states are `CG.iterate`, indexed from $0$. -/
theorem equation_11_3_26 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (tol : ℝ)
    (fuel : ℕ) :
    let s := Id.run (practicalCG pure A b x₀ tol fuel)
    let T := toEuclideanLin A
    s.k ≤ fuel ∧
      WithLp.toLp 2 s.x = (CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).x ∧
      WithLp.toLp 2 s.r = (CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).r ∧
      (∀ j < s.k, tol * ‖(WithLp.toLp 2 b : 𝔼 n)‖ <
        ‖(CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) j).r‖) ∧
      (s.k < fuel → s.done = true) ∧
      (s.done = true →
        ‖(WithLp.toLp 2 (b - A *ᵥ s.x) : 𝔼 n)‖ ≤ tol * ‖(WithLp.toLp 2 b : 𝔼 n)‖) := by
  intro s T
  obtain ⟨⟨hx, hr, -, -⟩, hkm, hlt, hdone, hnd⟩ := practicalCG_inv A b x₀ tol fuel
  rw [sqrt_dotProduct_self] at hlt hdone
  refine ⟨hkm, hx, hr, hlt, fun h => ?_, fun h => ?_⟩
  · cases hd : s.done
    · exact absurd (hnd hd) (Nat.ne_of_lt h)
    · rfl
  · have := hdone h
    rwa [CG.residual_eq, ← hx, toEuclideanLin_toLp, ← WithLp.toLp_sub] at this

end HestenesStiefel

/-! ### §11.3.8: error estimates -/

section Estimates

variable {A : Matrix (Fin n) (Fin n) ℝ}

open scoped Matrix.Norms.L2Operator in
/-- **Section 11.3.8** of [golub2013matrix], the error bound after (11.3.26). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b \in \mathbb{R}^n$, let $x_*$ satisfy
$Ax_* = b$, and let $\mathrm{tol} \ge 0$. If $x_c \in \mathbb{R}^n$ satisfies
$\|b - Ax_c\|_2 \le \mathrm{tol} \cdot \|b\|_2$, then
$$\|x_c - x_*\|_2 \le \mathrm{tol} \cdot \|A^{-1}\|_2\|b\|_2 \le \mathrm{tol} \cdot
  \kappa_2(A)\|x_*\|_2.$$

The source applies this to the final iterate $x_c$ of (11.3.26), and writes the first step as
$\|x_c - x_*\| = \|A^{-1}(b - Ax_c)\|_2$. The matrix norm is `Matrix.Norms.L2Operator`. -/
theorem cg_relativeError_le (hA : IsUnit A) {b xs xc : 𝔼 n} (hxs : toEuclideanLin A xs = b)
    {tol : ℝ} (htol : 0 ≤ tol) (h : ‖b - toEuclideanLin A xc‖ ≤ tol * ‖b‖) :
    ‖xc - xs‖ ≤ tol * ‖A⁻¹‖ * ‖b‖ ∧ tol * ‖A⁻¹‖ * ‖b‖ ≤ tol * NormedRing.condNumber A * ‖xs‖ := by
  have he : xc - xs = toEuclideanLin A⁻¹ (-(b - toEuclideanLin A xc)) := by
    rw [neg_sub, map_sub, inv_apply_apply hA, ← hxs, inv_apply_apply hA]
  refine ⟨?_, ?_⟩
  · rw [he]
    refine (norm_toEuclideanLin_apply_le _ _).trans ?_
    rw [norm_neg]
    calc ‖A⁻¹‖ * ‖b - toEuclideanLin A xc‖ ≤ ‖A⁻¹‖ * (tol * ‖b‖) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = tol * ‖A⁻¹‖ * ‖b‖ := by ring
  · rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse]
    have hb : ‖b‖ ≤ ‖A‖ * ‖xs‖ := by rw [← hxs]; exact norm_toEuclideanLin_apply_le A xs
    calc tol * ‖A⁻¹‖ * ‖b‖ ≤ tol * ‖A⁻¹‖ * (‖A‖ * ‖xs‖) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg htol (norm_nonneg _))
      _ = tol * (‖A‖ * ‖A⁻¹‖) * ‖xs‖ := by ring

open scoped Matrix.Norms.L2Operator in
/-- **Equation (11.3.27)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $b \in \mathbb{R}^n$, let $x_*$ satisfy $Ax_* = b$, and let $x_k$ be the
CG iterates from $x_0 \in \mathbb{R}^n$. Then for every $k$
$$\|x_* - x_k\|_A \le 2\|x_* - x_0\|_A\left(\frac{\sqrt{\kappa_2(A)} - 1}{\sqrt{\kappa_2(A)} +
  1}\right)^k.$$

The source quotes this bound from Trefethen and Bau. The CG iterates are `CG.iterate`. -/
theorem equation_11_3_27 (hA : A.PosDef) {b xs : 𝔼 n} (hxs : toEuclideanLin A xs = b) (x₀ : 𝔼 n)
    (k : ℕ) :
    energyNorm (toEuclideanLin A) (xs - (CG.iterate (toEuclideanLin A) b x₀ k).x) ≤
      2 * energyNorm (toEuclideanLin A) (xs - x₀) *
        ((√(NormedRing.condNumber A) - 1) / (√(NormedRing.condNumber A) + 1)) ^ k := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [eq_zero_of_isEmpty (xs - _), eq_zero_of_isEmpty (xs - x₀)]
    simp [energyNorm]
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  rw [hκ]
  have h := Krylov.IsGalerkinIterate.energyNorm_error_le hl hll hB
    (CG.isGalerkinIterate b x₀ hT k) hxs
  linarith

end Estimates

/-! ### §11.3.9: CG on $A^TA$ and $AA^T$ -/

section NormalEquations

/-- For a matrix $C$ and vectors $u$ and $v$, $\langle C^Tu, v\rangle = \langle u, Cv\rangle$. -/
private theorem inner_transpose_apply {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℝ) (u : 𝔼 p)
    (v : 𝔼 q) : ⟪toEuclideanLin Cᵀ u, v⟫ = ⟪u, toEuclideanLin C v⟫ :=
  toEuclideanLin_transpose_inner_left C v u

/-- **Section 11.3.9** of [golub2013matrix], the quadratics of the normal equations. Let
$A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$. For every $x \in \mathbb{R}^n$
$$\phi_{A^TA}(x) = \tfrac12 x^T(A^TA)x - x^T(A^Tb) = \tfrac12\|Ax - b\|_2^2 - \tfrac12 b^Tb.$$
For every nonsingular $B \in \mathbb{R}^{n \times n}$ and all $c, y \in \mathbb{R}^n$
$$\phi_{BB^T}(y) = \tfrac12 y^TBB^Ty - y^Tc = \tfrac12\|B^Ty - B^{-1}c\|_2^2 - \tfrac12
  c^T(BB^T)^{-1}c.$$

The source writes $A$ for the matrix $B$ of the second identity. The quadratic $\phi_M$ with
right-hand side $d$ is `energyFunctional M d`. -/
theorem energyFunctional_normalEquations {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : 𝔼 m)
    (x : 𝔼 n) :
    energyFunctional (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ b) x =
        ‖toEuclideanLin A x - b‖ ^ 2 / 2 - ‖b‖ ^ 2 / 2 ∧
      ∀ (B : Matrix (Fin n) (Fin n) ℝ), IsUnit B → ∀ (c y : 𝔼 n),
        energyFunctional (toEuclideanLin B ∘ₗ toEuclideanLin Bᵀ) c y =
          ‖toEuclideanLin Bᵀ y - toEuclideanLin B⁻¹ c‖ ^ 2 / 2 -
            ⟪c, toEuclideanLin (B * Bᵀ)⁻¹ c⟫ / 2 := by
  refine ⟨?_, fun B hB c y => ?_⟩
  · simp only [energyFunctional, RCLike.re_to_real, LinearMap.comp_apply]
    rw [inner_transpose_apply A (toEuclideanLin A x) x, inner_transpose_apply A b x,
      @norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_comm b (toEuclideanLin A x)]
    ring
  · -- with `w = B⁻¹c`: `(BBᵀ)⁻¹c = B⁻ᵀw` and `⟪c, (BBᵀ)⁻¹c⟫ = ‖w‖²`
    have hBT : IsUnit Bᵀ := (isUnit_transpose B).2 hB
    obtain ⟨w, hw⟩ : ∃ w, w = toEuclideanLin B⁻¹ c := ⟨_, rfl⟩
    have hcw : toEuclideanLin B w = c := by rw [hw]; exact apply_inv_apply hB c
    have hinv : toEuclideanLin (B * Bᵀ)⁻¹ c = toEuclideanLin Bᵀ⁻¹ w := by
      rw [hw, Matrix.mul_inv_rev]
      simp only [toEuclideanLin_apply, mulVec_mulVec]
    have hq : ⟪c, toEuclideanLin (B * Bᵀ)⁻¹ c⟫ = ‖w‖ ^ 2 := by
      have h1 := inner_transpose_apply Bᵀ w (toEuclideanLin Bᵀ⁻¹ w)
      rw [transpose_transpose, apply_inv_apply hBT] at h1
      rw [hinv, ← hcw, h1, real_inner_self_eq_norm_sq]
    rw [hq, ← hw]
    simp only [energyFunctional, RCLike.re_to_real, LinearMap.comp_apply]
    rw [real_inner_comm y (toEuclideanLin B (toEuclideanLin Bᵀ y)),
      ← inner_transpose_apply B y (toEuclideanLin Bᵀ y), ← hcw,
      real_inner_comm y (toEuclideanLin B w), ← inner_transpose_apply B y w, @norm_sub_sq_real,
      real_inner_self_eq_norm_sq]
    ring

/-- **Section 11.3.9** of [golub2013matrix], CGNR on a rectangular system. Let
$A \in \mathbb{R}^{m \times n}$ have full column rank, let $b \in \mathbb{R}^m$ and
$x_0 \in \mathbb{R}^n$, and let $r_0 = b - Ax_0$. Then the iterate $x_k$ of CG applied to
$A^TAx = A^Tb$ from $x_0$ minimizes $\|b - Ax\|_2$ over the affine space
$x_0 + \mathcal{K}(A^TA, A^Tr_0, k)$ of (11.3.28).

This is the remark after Figure 11.3.1 that the CGNR method can be applied if $A$ is
rectangular, and so provides a normal equation framework for sparse, full rank least squares
problems. Full column rank is the injectivity of $x \mapsto Ax$, and the minimization is
`IsMinResidual`. -/
theorem cgnr_isMinResidual_of_injective {m : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : Function.Injective (toEuclideanLin A)) (b : 𝔼 m) (x₀ : 𝔼 n) (k : ℕ) :
    IsMinResidual (toEuclideanLin A) b x₀
      (Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A)
        (toEuclideanLin Aᵀ (b - toEuclideanLin A x₀)) k)
      (CG.iterate (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ b) x₀ k).x := by
  have hadj := LinearMap.isAdjointPair_inner_iff.2 (inner_transpose_apply A)
  have hS := Krylov.adjoint_comp_isSymmetricCoercive_of_injective hadj hA
  exact (Krylov.isGalerkinIterate_adjoint_comp_iff_isMinResidual hadj b x₀ k _).1
    (CG.isGalerkinIterate _ x₀ hS k)

/-- **Equation (11.3.28)** of [golub2013matrix] (CGNR). Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, let $b, x_0 \in \mathbb{R}^n$, and let $r_0 = b - Ax_0$. Then the $k$-th iterate
$x_k$ of CG applied to $A^TAx = A^Tb$ from $x_0$ minimizes $\phi_{A^TA}(x) = \tfrac12\|Ax -
b\|_2^2 - \tfrac12 b^Tb$, that is $\|b - Ax\|_2$, over the affine space
$$S_k = x_0 + \mathcal{K}(A^TA, A^Tr_0, k).$$

The minimization is `IsMinResidual`. The rectangular case is
`GolubVanLoan.Chapter11.cgnr_isMinResidual_of_injective`. -/
theorem equation_11_3_28 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b x₀ : 𝔼 n) (k : ℕ) :
    IsMinResidual (toEuclideanLin A) b x₀
      (Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A)
        (toEuclideanLin Aᵀ (b - toEuclideanLin A x₀)) k)
      (CG.iterate (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ b) x₀ k).x :=
  cgnr_isMinResidual_of_injective (fun u v h => by
    rw [← inv_apply_apply hA u, h, inv_apply_apply hA]) b x₀ k

/-- **Section 11.3.9** of [golub2013matrix], CGNE on a rectangular system. Let
$A \in \mathbb{R}^{m \times n}$ have full row rank, let $b \in \mathbb{R}^m$, and let
$x_* \in \mathbb{R}^n$ satisfy $Ax_* = b$. Let $y_k$ be the CG iterates for $AA^Ty = b$ from
$y_0 \in \mathbb{R}^m$, and let $x_k = A^Ty_k$. Then $x_k$ minimizes $\|x - x_*\|_2$ over the
affine space $x_0 + \mathcal{K}(A^TA, A^Tr_0, k)$ of (11.3.28), where $x_0 = A^Ty_0$ and
$r_0 = b - Ax_0$.

This is the remark after Figure 11.3.1 that the CGNE method can also be applied to rectangular
problems, but the underlying system must be consistent. Full row rank is the injectivity of
$y \mapsto A^Ty$, which makes $AA^T$ positive definite, so that CG on the $y$-problem is the
method of this section. The minimization is `IsMinError`. -/
theorem cgne_isMinError_of_injective_transpose {m : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : Function.Injective (toEuclideanLin Aᵀ)) {b : 𝔼 m} {xs : 𝔼 n}
    (hxs : toEuclideanLin A xs = b) (y₀ : 𝔼 m) (k : ℕ) :
    IsMinError xs (toEuclideanLin Aᵀ y₀)
      (Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A)
        (toEuclideanLin Aᵀ (b - toEuclideanLin A (toEuclideanLin Aᵀ y₀))) k)
      (toEuclideanLin Aᵀ (CG.iterate (toEuclideanLin A ∘ₗ toEuclideanLin Aᵀ) b y₀ k).x) := by
  have hadj := LinearMap.isAdjointPair_inner_iff.2 (inner_transpose_apply A)
  -- `AAᵀ` is symmetric positive definite: `(Aᵀ)ᵀ = A` is the adjoint of `Aᵀ`
  have hadj' : ∀ (u : 𝔼 n) (v : 𝔼 m), ⟪toEuclideanLin A u, v⟫ = ⟪u, toEuclideanLin Aᵀ v⟫ :=
    fun u v => by
      have := inner_transpose_apply Aᵀ u v
      rwa [transpose_transpose] at this
  have hS := Krylov.adjoint_comp_isSymmetricCoercive_of_injective
    (LinearMap.isAdjointPair_inner_iff.2 hadj') hA
  have h := Krylov.isMinError_of_isGalerkinIterate_comp_adjoint hadj b (toEuclideanLin Aᵀ y₀)
    rfl hxs (CG.isGalerkinIterate b y₀ hS k)
  rwa [← map_add, add_sub_cancel] at h

/-- **Section 11.3.9** of [golub2013matrix], CGNE (Craig's method). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b \in \mathbb{R}^n$, and let $x_*$ satisfy
$Ax_* = b$. Let $y_k$ be the CG iterates for the $y$-problem $AA^Ty = b$ from
$y_0 \in \mathbb{R}^n$, and let $x_k = A^Ty_k$. Then $x_k$ minimizes $\|x - x_*\|_2$ over the
affine space $x_0 + \mathcal{K}(A^TA, A^Tr_0, k)$ of (11.3.28), where $x_0 = A^Ty_0$ and
$r_0 = b - Ax_0$.

The minimization is `IsMinError`. The rectangular case is
`GolubVanLoan.Chapter11.cgne_isMinError_of_injective_transpose`. -/
theorem cgne_isMinError {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {b xs : 𝔼 n}
    (hxs : toEuclideanLin A xs = b) (y₀ : 𝔼 n) (k : ℕ) :
    IsMinError xs (toEuclideanLin Aᵀ y₀)
      (Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A)
        (toEuclideanLin Aᵀ (b - toEuclideanLin A (toEuclideanLin Aᵀ y₀))) k)
      (toEuclideanLin Aᵀ (CG.iterate (toEuclideanLin A ∘ₗ toEuclideanLin Aᵀ) b y₀ k).x) := by
  have hBT : IsUnit Aᵀ := (isUnit_transpose A).2 hA
  exact cgne_isMinError_of_injective_transpose (fun u v h => by
    rw [← inv_apply_apply hBT u, h, inv_apply_apply hBT]) hxs y₀ k

variable {M : Type → Type} [Monad M]

/-- The state of the CGNR loop: the iterate $x$, the residual $r = b - Ax$, the vector $z = A^Tr$,
and the search direction $p$. -/
structure CGNRState (m n : ℕ) where
  /-- The iterate $x_c$. -/
  x : Fin n → ℝ
  /-- The residual $r_c = b - Ax_c$. -/
  r : Fin m → ℝ
  /-- The vector $z_c = A^Tr_c$. -/
  z : Fin n → ℝ
  /-- The search direction $p_c$. -/
  p : Fin n → ℝ

/-- **Figure 11.3.1** of [golub2013matrix], the CGNR column. For $A \in \mathbb{R}^{m \times n}$,
$b \in \mathbb{R}^m$ and $x_0 \in \mathbb{R}^n$, the program sets $r_c = b - Ax_0$,
$z_c = A^Tr_c$ and $p_c = z_c$, and then repeats `fuel` times the update
$$\mu = \frac{z_c^Tz_c}{(Ap_c)^T(Ap_c)}, \quad x_+ = x_c + \mu p_c, \quad r_+ = r_c - \mu Ap_c,
  \quad z_+ = A^Tr_+, \quad \tau = \frac{z_+^Tz_+}{z_c^Tz_c}, \quad p_+ = z_+ + \tau p_c.$$

The matrix $A$ may be rectangular. The products and the updates are Algorithms 1.1.1–1.1.3, and
every arithmetic result is rounded. The loop has no stopping test. -/
noncomputable def cgnr {m : ℕ} (rnd : ℝ → M ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) (fuel : ℕ) : M (CGNRState m n) := do
  let r ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let z ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd Aᵀ r 0
  (List.range fuel).foldlM (fun s _ => do
    let Ap ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A s.p 0
    let zz ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.z s.z
    let ApAp ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd Ap Ap
    let μ ← rnd (zz / ApAp)
    let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd μ s.p s.x
    let r ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.r
    let z ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd Aᵀ r 0
    let zz' ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd z z
    let τ ← rnd (zz' / zz)
    let p ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd τ s.p z
    pure (⟨x, r, z, p⟩ : CGNRState m n)) ⟨x₀, r, z, z⟩

/-- One exact CGNR step. -/
private noncomputable def cgnrStep {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s : CGNRState m n) :
    CGNRState m n :=
  ⟨s.x + (s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p))) • s.p,
    s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p),
    Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p)),
    Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p)) +
      ((Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p))) ⬝ᵥ
          (Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p))) /
        (s.z ⬝ᵥ s.z)) • s.p⟩

/-- The exact run of the CGNR loop with no step. -/
private theorem cgnr_run_zero {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) : Id.run (cgnr pure A b x₀ 0) =
      ⟨x₀, b - A *ᵥ x₀, Aᵀ *ᵥ (b - A *ᵥ x₀), Aᵀ *ᵥ (b - A *ᵥ x₀)⟩ := by
  simp only [cgnr, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec, List.range_zero,
    List.foldlM_nil, Id.run_pure, zero_add, mulVec_neg, ← sub_eq_add_neg]

/-- The exact run of the CGNR loop with $k + 1$ steps is one exact step after the run with $k$
steps. -/
private theorem cgnr_run_succ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    Id.run (cgnr pure A b x₀ (k + 1)) = cgnrStep A (Id.run (cgnr pure A b x₀ k)) := by
  simp only [cgnr, Id.run_bind]
  rw [List.idRun_foldlM_range_succ]
  simp only [Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
    GolubVanLoan.Chapter01.algorithm_1_1_1_spec, GolubVanLoan.Chapter01.algorithm_1_1_2_spec,
    zero_add, cgnrStep]

/-- **Figure 11.3.1** of [golub2013matrix], exact semantics of CGNR. For
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $x_0 \in \mathbb{R}^n$, the exact run
with $k$ passes returns the state of the backbone CGNR iteration after $k$ steps, and its $z$ is
$A^Tr$.

The backbone iteration is `Krylov.CGNR.iterate`, which makes one product with $A$ and one with
$A^T$ per step. Its iterates are those of CG on the normal equations, as in (11.3.28). -/
theorem cgnr_spec {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    let s := Id.run (cgnr pure A b x₀ k)
    let it := Krylov.CGNR.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    WithLp.toLp 2 s.x = it.x ∧ WithLp.toLp 2 s.r = it.r ∧ WithLp.toLp 2 s.p = it.p ∧
      s.z = Aᵀ *ᵥ s.r := by
  induction k with
  | zero =>
    rw [cgnr_run_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp, hz⟩ := ih
    rw [cgnr_run_succ]
    intro s' it'
    simp only [s', it']
    set s := Id.run (cgnr pure A b x₀ k)
    set it := Krylov.CGNR.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    have hAr : toEuclideanLin Aᵀ it.r = WithLp.toLp 2 s.z := by
      rw [← hr, toEuclideanLin_toLp, hz]
    have hAp : toEuclideanLin A it.p = WithLp.toLp 2 (A *ᵥ s.p) := by
      rw [← hp, toEuclideanLin_toLp]
    have halpha : s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)) =
        Krylov.CGNR.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) it := by
      rw [Krylov.CGNR.alpha, hAr, hAp, inner_toLp, inner_toLp]
    have hr' : WithLp.toLp 2
        (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p)) =
        (Krylov.CGNR.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
          (WithLp.toLp 2 x₀) (k + 1)).r := by
      rw [Krylov.CGNR.iterate_succ, Krylov.CGNR.step_r, ← halpha, hAp, ← hr, neg_smul,
        ← sub_eq_add_neg, WithLp.toLp_sub, WithLp.toLp_smul]
    refine ⟨?_, hr', ?_, rfl⟩
    · change WithLp.toLp 2 (s.x + (s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p))) • s.p) = _
      rw [Krylov.CGNR.iterate_succ, Krylov.CGNR.step_x, ← halpha, ← hx, ← hp, WithLp.toLp_add,
        WithLp.toLp_smul]
    · change WithLp.toLp 2
        (Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p)) +
          ((Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p))) ⬝ᵥ
              (Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p))) /
            (s.z ⬝ᵥ s.z)) • s.p) = _
      rw [Krylov.CGNR.iterate_succ, Krylov.CGNR.step_p, Krylov.CGNR.beta,
        ← Krylov.CGNR.iterate_succ, ← hr', hAr, toEuclideanLin_toLp, inner_toLp, inner_toLp,
        ← hp, WithLp.toLp_add, WithLp.toLp_smul]

/-- The state of the CGNE loop: the iterate $x$, the residual $r = b - Ax$, and the search direction
$p$. -/
structure CGNEState (m n : ℕ) where
  /-- The iterate $x_c$. -/
  x : Fin n → ℝ
  /-- The residual $r_c = b - Ax_c$. -/
  r : Fin m → ℝ
  /-- The search direction $p_c$. -/
  p : Fin n → ℝ

/-- **Figure 11.3.1** of [golub2013matrix], the CGNE column. For $A \in \mathbb{R}^{m \times n}$,
$b \in \mathbb{R}^m$ and $x_0 \in \mathbb{R}^n$, the program sets $x_c = x_0$, $r_c = b - Ax_c$
and $p_c = A^Tr_c$, and then repeats `fuel` times the update
$$\mu = \frac{r_c^Tr_c}{p_c^Tp_c}, \quad x_+ = x_c + \mu p_c, \quad r_+ = r_c - \mu Ap_c, \quad
  \tau = \frac{r_+^Tr_+}{r_c^Tr_c}, \quad p_+ = A^Tr_+ + \tau p_c.$$

The matrix $A$ may be rectangular. The products and the updates are Algorithms 1.1.1–1.1.3, and
every arithmetic result is rounded. The loop has no stopping test. -/
noncomputable def cgne {m : ℕ} (rnd : ℝ → M ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) (fuel : ℕ) : M (CGNEState m n) := do
  let r ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let p ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd Aᵀ r 0
  (List.range fuel).foldlM (fun s _ => do
    let rr ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.r s.r
    let pp ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.p s.p
    let μ ← rnd (rr / pp)
    let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd μ s.p s.x
    let Ap ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A s.p 0
    let r ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.r
    let rr' ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd r r
    let τ ← rnd (rr' / rr)
    let Atr ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd Aᵀ r 0
    let p ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd τ s.p Atr
    pure (⟨x, r, p⟩ : CGNEState m n)) ⟨x₀, r, p⟩

/-- One exact CGNE step. -/
private noncomputable def cgneStep {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s : CGNEState m n) :
    CGNEState m n :=
  ⟨s.x + (s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p)) • s.p,
    s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p),
    Aᵀ *ᵥ (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) +
      ((s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) ⬝ᵥ
          (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) / (s.r ⬝ᵥ s.r)) • s.p⟩

/-- The exact run of the CGNE loop with no step. -/
private theorem cgne_run_zero {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) : Id.run (cgne pure A b x₀ 0) =
      ⟨x₀, b - A *ᵥ x₀, Aᵀ *ᵥ (b - A *ᵥ x₀)⟩ := by
  simp only [cgne, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec, List.range_zero,
    List.foldlM_nil, Id.run_pure, zero_add, mulVec_neg, ← sub_eq_add_neg]

/-- The exact run of the CGNE loop with $k + 1$ steps is one exact step after the run with $k$
steps. -/
private theorem cgne_run_succ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    Id.run (cgne pure A b x₀ (k + 1)) = cgneStep A (Id.run (cgne pure A b x₀ k)) := by
  simp only [cgne, Id.run_bind]
  rw [List.idRun_foldlM_range_succ]
  simp only [Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
    GolubVanLoan.Chapter01.algorithm_1_1_1_spec, GolubVanLoan.Chapter01.algorithm_1_1_2_spec,
    zero_add, cgneStep]

/-- **Figure 11.3.1** of [golub2013matrix], exact semantics of CGNE. For
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $x_0 \in \mathbb{R}^n$, the exact run
with $k$ passes returns the state of the backbone CGNE iteration after $k$ steps.

The backbone iteration is `Krylov.CGNE.iterate`, which is $A^T$ applied to CG on $AA^Ty = b$
(`Krylov.CGNE.iterate_eq`). So for a consistent system $Ax = b$ its iterates are those of
`GolubVanLoan.Chapter11.cgne_isMinError`. -/
theorem cgne_spec {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    let s := Id.run (cgne pure A b x₀ k)
    let it := Krylov.CGNE.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    WithLp.toLp 2 s.x = it.x ∧ WithLp.toLp 2 s.r = it.r ∧ WithLp.toLp 2 s.p = it.p := by
  induction k with
  | zero =>
    rw [cgne_run_zero]
    exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    rw [cgne_run_succ]
    intro s' it'
    simp only [s', it']
    set s := Id.run (cgne pure A b x₀ k)
    set it := Krylov.CGNE.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    have halpha : s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p) = (Krylov.CGNE.alpha it : ℝ) := by
      rw [Krylov.CGNE.alpha, ← hr, ← hp, inner_toLp, inner_toLp]
    have hAp : toEuclideanLin A it.p = WithLp.toLp 2 (A *ᵥ s.p) := by
      rw [← hp, toEuclideanLin_toLp]
    have hr' : WithLp.toLp 2 (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) =
        (Krylov.CGNE.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
          (WithLp.toLp 2 x₀) (k + 1)).r := by
      rw [Krylov.CGNE.iterate_succ, Krylov.CGNE.step_r, ← halpha, hAp, ← hr, neg_smul,
        ← sub_eq_add_neg, WithLp.toLp_sub, WithLp.toLp_smul]
    refine ⟨?_, hr', ?_⟩
    · change WithLp.toLp 2 (s.x + (s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p)) • s.p) = _
      rw [Krylov.CGNE.iterate_succ, Krylov.CGNE.step_x, ← halpha, ← hx, ← hp, WithLp.toLp_add,
        WithLp.toLp_smul]
    · change WithLp.toLp 2
        (Aᵀ *ᵥ (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) +
          ((s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) ⬝ᵥ
              (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) / (s.r ⬝ᵥ s.r)) • s.p) = _
      rw [Krylov.CGNE.iterate_succ, Krylov.CGNE.step_p, Krylov.CGNE.beta,
        ← Krylov.CGNE.iterate_succ, ← hr', ← hr, inner_toLp, inner_toLp, toEuclideanLin_toLp,
        ← hp, WithLp.toLp_add, WithLp.toLp_smul]

end NormalEquations

end GolubVanLoan.Chapter11
