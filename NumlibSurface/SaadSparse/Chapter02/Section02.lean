/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.Polynomial.Chebyshev
import Numlib.Analysis.SpecialFunctions.Chebyshev
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 2.2: Finite difference methods

This module formalizes §2.2 of [saad2003iterative], the finite difference discretization of elliptic
problems. It proves the truncation errors of the difference formulas of §2.2.1–2.2.2, among them the
five-point and nine-point approximations of the Laplacean. It defines the one-dimensional model
matrix $\frac{1}{h^2}\operatorname{tridiag}(-1, 2, -1)$ of §2.2.3, solves the convection–diffusion
problem of §2.2.4 exactly and by the centered scheme, and compares the centered and the upwind
matrices. It defines the two-dimensional five-point matrix of §2.2.5, and proves the spectral facts
of §2.2.6 on which the fast Poisson solver rests and the polynomial form of the block cyclic
reduction of §2.2.7.

The section states no numbered result, so the definitions matter most:
`SaadSparse.Chapter02.laplacian1D`, `SaadSparse.Chapter02.laplacian2D` and the block
`SaadSparse.Chapter02.blockB` of (2.27) are used in Chapters 4, 6, 10, 12 and 13. The spectral
results specialize `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`, which gives the eigenpairs of
$\operatorname{tridiag}(a, b, a)$ and the orthogonality of the discrete sine basis, and
`Numlib.LinearAlgebra.Matrix.KroneckerSum`, which gives the eigenvalues of a Kronecker sum. The
source gives the eigenvalues of $B = \operatorname{tridiag}(-1, 4, -1)$ of (2.27) here and
treats the spectra of the model matrices in §13.2 with unscaled matrices.

## Main definitions

* §2.2.2, `SaadSparse.Chapter02.diffX` and `SaadSparse.Chapter02.diffY`: the centred second
  difference quotients $\delta_x^2 u$ and $\delta_y^2 u$.
* Figure 2.3(b), `SaadSparse.Chapter02.diagonalStencil`: the five-point stencil on the two diagonal
  lines.
* Figure 2.4(c) and (d), `SaadSparse.Chapter02.ninePointC` and `SaadSparse.Chapter02.ninePointD`:
  the two nine-point stencils.
* §2.2.3, `SaadSparse.Chapter02.dirichletExt`: a grid vector extended by the boundary values
  $u_0 = u_{n+1} = 0$.
* §2.2.3, `SaadSparse.Chapter02.laplacian1D`: the one-dimensional model matrix
  $\frac{1}{h^2}\operatorname{tridiag}(-1, 2, -1)$.
* Equation (2.20), `SaadSparse.Chapter02.convDiffExact`: the exact solution $(1 - e^{Rx})/(1 - e^R)$
  of the convection–diffusion problem.
* Equation (2.21), `SaadSparse.Chapter02.convDiffRatio` and `SaadSparse.Chapter02.convDiffDiscrete`:
  the root $\sigma = (1 + c)/(1 - c)$ and the solution $(1 - \sigma^i)/(1 - \sigma^{n+1})$ of the
  centered scheme.
* §2.2.4, `SaadSparse.Chapter02.convDiffCentered` and `SaadSparse.Chapter02.convDiffUpwind`: the
  matrices of the centered and the upwind schemes.
* §2.2.5, `SaadSparse.Chapter02.laplacian2D`: the two-dimensional five-point matrix.
* Equation (2.27), `SaadSparse.Chapter02.blockB`, `SaadSparse.Chapter02.blockEigenvalue` and
  `SaadSparse.Chapter02.sineMatrix`: the block $B = \operatorname{tridiag}(-1, 4, -1)$, its
  eigenvalues $\lambda_j$ and the orthogonal matrix $Q$ of normalized sine vectors.
* Algorithm 2.1, `SaadSparse.Chapter02.sineCoeff`: the coefficients of a grid function in the sine
  basis of the within-block index.
* Equation (2.33), `SaadSparse.Chapter02.cyclicReduction`: the sequence
  $B^{(r+1)} = (B^{(r)})^2 - 2I$.

## Main results

* Equations (2.9)–(2.10), `SaadSparse.Chapter02.equation_2_10`: the forward difference approximates
  $u'$ to first order.
* Equation (2.12), `SaadSparse.Chapter02.equation_2_12`: the centered second difference approximates
  $u''$ with error $\frac{h^2}{12} u^{(4)}(\xi)$.
* Equation (2.13), `SaadSparse.Chapter02.equation_2_13`: the centered first difference approximates
  $u'$ with error $\frac{h^2}{6} u'''(\xi)$.
* Problem P-2.6, `SaadSparse.Chapter02.equation_2_16_symm`: the conservative difference is
  $\delta^-(a_{i+1/2}\delta^+ u)$.
* Equation (2.16) and Problem P-2.7, `SaadSparse.Chapter02.equation_2_16`: the conservative
  difference approximates $(a u')'$ to second order.
* Equation (2.17), `SaadSparse.Chapter02.equation_2_17`: the five-point approximation of $\Delta u$
  and its truncation error.
* Figure 2.4, `SaadSparse.Chapter02.diagonalStencil_eq`, `SaadSparse.Chapter02.ninePointC_eq` and
  `SaadSparse.Chapter02.ninePointD_eq`: the diagonal and the nine-point stencils are $\delta_x^2 +
  \delta_y^2 + \alpha h^2 \delta_x^2 \delta_y^2$ with $\alpha = 1/2, 1/3, 1/6$.
* Figure 2.4(d) and (c), `SaadSparse.Chapter02.ninePointD_error` and
  `SaadSparse.Chapter02.ninePointC_error`: both nine-point stencils approximate $\Delta u$ to second
  order.
* §2.2.3, `SaadSparse.Chapter02.laplacian1D_mulVec_apply`: the rows of the model matrix are the
  difference equations $(-v_{i-1} + 2v_i - v_{i+1})/h^2$.
* §2.2.3 and §13.2: `SaadSparse.Chapter02.laplacian1D_mulVec_sineVec`,
  `SaadSparse.Chapter02.laplacian1D_isSymmetricBoundedBy`, `SaadSparse.Chapter02.laplacian1D_posDef`
  and `SaadSparse.Chapter02.laplacian1D_lambdaMax_div_lambdaMin`: the eigenpairs, the sharp spectral
  bounds, the positive definiteness and the ratio of the extreme eigenvalues of the model matrix.
* Equation (2.20), `SaadSparse.Chapter02.equation_2_20`: the exact solution is the only solution of
  $-au'' + bu' = 0$, $u(0) = 0$, $u(1) = 1$.
* §2.2.4, `SaadSparse.Chapter02.convDiffExact_pos` and
  `SaadSparse.Chapter02.convDiffExact_strictMono`: for $R > 0$ the exact solution is positive for
  $x > 0$ and strictly increasing.
* Equation (2.21), `SaadSparse.Chapter02.equation_2_21`: the discrete solution is the only solution
  of the centered scheme.
* §2.2.4, `SaadSparse.Chapter02.equation_2_21_oscillates` and
  `SaadSparse.Chapter02.equation_2_21_strictMono`: the discrete solution oscillates for $c > 1$ and
  increases for $0 < c < 1$.
* §2.2.4, `SaadSparse.Chapter02.convDiffCentered_not_isMMatrix`,
  `SaadSparse.Chapter02.convDiffCentered_not_diagDominant` and
  `SaadSparse.Chapter02.convDiffUpwind_diagDominant`: for $c > 1$ the centered matrix is neither an
  M-matrix nor weakly diagonally dominant, and for $c \ge 0$ the upwind matrix is a weakly
  diagonally dominant matrix with nonpositive off-diagonal entries.
* Equations (2.22)–(2.23), `SaadSparse.Chapter02.equation_2_23`: the upwind approximation of $b u'$
  in one formula for both signs of $b$.
* Equation (13.12), `SaadSparse.Chapter02.laplacian2D_eq_kroneckerSum` and
  `SaadSparse.Chapter02.laplacian2D_smul`: the five-point matrix is a Kronecker sum of
  one-dimensional model matrices, with the mesh scaling of §2.2.5 made explicit.
* Equation (2.26), `SaadSparse.Chapter02.laplacian2D_block_apply`: the block tridiagonal form of the
  scaled five-point matrix.
* §13.2 and §2.2.5, `SaadSparse.Chapter02.laplacian2D_mulVec_kroneckerVec` and
  `SaadSparse.Chapter02.laplacian2D_posDef`: the eigenpairs and the positive definiteness of the
  five-point matrix.
* Equation (2.27), `SaadSparse.Chapter02.sineMatrix_transpose_mul_self`,
  `SaadSparse.Chapter02.blockB_mulVec_sineVec` and `SaadSparse.Chapter02.equation_2_27_spectrum`:
  $Q$ is orthogonal and $Q^T B Q = \operatorname{diag}(\lambda_1, \dots, \lambda_p)$.
* Equations (2.28)–(2.29) and Algorithm 2.1, `SaadSparse.Chapter02.equation_2_29`: the sine
  transform decouples the model problem into $p$ tridiagonal systems.
* Equation (2.33), `SaadSparse.Chapter02.equation_2_33`: the cyclic reduction sequence is
  $B^{(r)} = C_{2^r}(B)$ for the Vieta–Lucas polynomial $C_{2^r}$.
* Equation (2.36), `SaadSparse.Chapter02.cyclicReduction_mulVec_of_mulVec_eq_smul` and
  `SaadSparse.Chapter02.equation_2_36`: the action of $B^{(r)}$ on an eigenvector of $B$, and the
  factorization of $B^{(r)}$ into $2^r$ linear factors.

## Conventions

* The model matrices carry the scaling $1/h^2$, as the displays of §2.2.3 and §2.2.5 do. §2.2.6
  scales it away, and `SaadSparse.Chapter02.laplacian2D_smul` relates the two conventions.
* The source numbers the eigenvalues and the discrete sine vectors from $1$. A Lean index
  `k : Fin n` stands for the book's $k + 1$.
* The positive and negative parts of the source, $z^+ = (z + |z|)/2$ and $z^- = (z - |z|)/2$, are
  `max z 0` and `min z 0` (`SaadSparse.max_zero_eq_half`, `SaadSparse.min_zero_eq_half`). They are
  shared with the finite volume fluxes of §2.5, whose (2.53) is the same algebraic fact as the
  upwind combination (2.22).
* A function of two variables is curried, `u : ℝ → ℝ → ℝ`, and $\partial_1^k u(x, y)$ is
  `iteratedDeriv k (fun t => u t y) x`. The regularity hypotheses are stated along each grid line
  separately.

## Implementation notes

* The two-dimensional grid is indexed by `Fin n₁ × Fin n₂` for the two coordinate directions.
  The first coordinate is the $x_1$ direction with mesh size $h_1$. The source orders horizontal
  lines by $x_2$. The block formula here fixes $x_1$ and uses vertical lines, which amounts to
  swapping the two coordinates before applying the source's block convention.
* Each truncation error statement names the intermediate point at which the Lagrange remainder is
  evaluated, as the displays of the source do.
* Every difference quotient and every model matrix is defined for all step sizes $h$. At $h = 0$ it
  is $0$, by the Lean convention $x / 0 = 0$, and the theorems assume $h > 0$ or $h \neq 0$.

## Deviations from the source

* **Equations (2.9)–(2.13)** (reading). The difference estimates use global regularity.
  The first derivative formulas give exact Lagrange remainders. See
  `SaadSparse.Chapter02.equation_2_10`, `SaadSparse.Chapter02.equation_2_12` and
  `SaadSparse.Chapter02.equation_2_13`.
* **Equation (2.16) and Problems P-2.6–P-2.7** (reading). The staggered difference identity is
  unscaled, and the accuracy result gives an exact remainder for globally $C^4$ functions.
  See `SaadSparse.Chapter02.equation_2_16_symm` and `SaadSparse.Chapter02.equation_2_16`.
* **Equation (2.17), Figure 2.4 and Problem P-2.4** (reading). The error formulas evaluate
  the relevant derivatives at intermediate points, under separate regularity hypotheses.
  See `SaadSparse.Chapter02.equation_2_17`, `SaadSparse.Chapter02.ninePointC_error` and
  `SaadSparse.Chapter02.ninePointD_error`.
* **§2.2.2, stencil definitions** (reading). The uniform-grid quotients extend to all real
  step sizes and have value $0$ at step size zero. See `SaadSparse.Chapter02.diffX`,
  `SaadSparse.Chapter02.diffY`, `SaadSparse.Chapter02.diagonalStencil`,
  `SaadSparse.Chapter02.ninePointC` and `SaadSparse.Chapter02.ninePointD`.
* **§2.2.3, grid and stencil** (reading and generalization). The scalar equation has $h^2 f_i$
  on the right, and the matrix display carries $1/h^2$. The surface matrix uses the latter
  convention for any size and step, with zero padding outside the interior.
  See `SaadSparse.Chapter02.dirichletExt`, `SaadSparse.Chapter02.dirichletExt_of_gt`,
  `SaadSparse.Chapter02.laplacian1D`, `SaadSparse.Chapter02.laplacian1D_apply` and
  `SaadSparse.Chapter02.laplacian1D_mulVec_apply`.
* **Equations (13.7)–(13.8), eigenpairs of the 1-D model matrix** (reading). The eigenvalues
  here carry the $1/h^2$ scaling of §2.2.3.
  See `SaadSparse.Chapter02.laplacian1D_mulVec_sineVec`.
* **Equation (2.20)** (reading). The exponential formula is totalized at $R=0$. The
  uniqueness theorem uses nonzero denominators and derivative hypotheses on $[0,1]$.
  See `SaadSparse.Chapter02.convDiffExact` and `SaadSparse.Chapter02.equation_2_20`.
* **Equation (2.21)** (reading). The closed forms are totalized at zero denominators.
  The uniqueness statement on the grid excludes the degenerate roots at $c=0,1$.
  See `SaadSparse.Chapter02.convDiffRatio`, `SaadSparse.Chapter02.convDiffDiscrete` and
  `SaadSparse.Chapter02.equation_2_21`.
* **§2.2.4, positivity, monotonicity and oscillation** (generalization). The continuous and
  discrete formulas have these properties beyond the source's grid interval under the stated
  parameter conditions. See `SaadSparse.Chapter02.convDiffExact_pos`,
  `SaadSparse.Chapter02.convDiffExact_strictMono`, `SaadSparse.Chapter02.equation_2_21_oscillates`
  and `SaadSparse.Chapter02.equation_2_21_strictMono`.
* **§2.2.4, centered and backward upwind matrices** (generalization). The six-point
  displays extend to arbitrary matrix sizes and independent parameters. The sign and
  dominance results use explicit size and parameter ranges.
  See `SaadSparse.Chapter02.convDiffCentered`, `SaadSparse.Chapter02.convDiffCentered_apply`,
  `SaadSparse.Chapter02.convDiffUpwind`, `SaadSparse.Chapter02.convDiffUpwind_apply`,
  `SaadSparse.Chapter02.convDiffCentered_not_isMMatrix`,
  `SaadSparse.Chapter02.convDiffCentered_not_diagDominant` and
  `SaadSparse.Chapter02.convDiffUpwind_diagDominant`.
* **Equation (2.23)** (reading). The two upwind expressions are equal for all steps,
  including zero by totalized division. See `SaadSparse.Chapter02.equation_2_23`.
* **§2.2.5, the interior index ranges** (typo). The source omits the last interior index in
  each direction. The formal grid has $n_1$ by $n_2$ interior points.
  See `SaadSparse.Chapter02.laplacian2D` and `SaadSparse.Chapter02.laplacian2D_apply`.
* **§2.2.5 and Equations (2.26), (13.12), (13.14)** (reading and generalization). The
  scaled matrix formulas use independent step sizes for the two grid directions.
  The block form fixes the first coordinate, giving vertical blocks.
  See `SaadSparse.Chapter02.laplacian2D`, `SaadSparse.Chapter02.laplacian2D_apply`,
  `SaadSparse.Chapter02.laplacian2D_eq_kroneckerSum`, `SaadSparse.Chapter02.laplacian2D_smul`,
  `SaadSparse.Chapter02.laplacian2D_block_apply` and
  `SaadSparse.Chapter02.laplacian2D_mulVec_kroneckerVec`.
* **Equation (2.29)** (typo). The source prints the two indices transposed, which gives systems of
  the wrong size. The library states $p$ systems of size $m$, as line 2 of Algorithm 2.1 says. See
  `SaadSparse.Chapter02.equation_2_29`.
* **Equations (2.33) and (2.36)** (generalization). The cyclic reduction recurrence,
  its polynomial form, and the factorization apply to arbitrary square real matrices.
  See `SaadSparse.Chapter02.cyclicReduction`, `SaadSparse.Chapter02.equation_2_33` and
  `SaadSparse.Chapter02.equation_2_36`.
* **Equation (2.36)** (typo). The product for the block solve uses $B$ in place of the
  printed $A$. See `SaadSparse.Chapter02.equation_2_36`.

## Not formalized

* **§2.2.2, the sixth-order accuracy of the nine-point stencil (d) on harmonic functions.** It needs
  the equality of mixed partial derivatives for a curried function
  $u : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$, which Mathlib does not have; the second-order
  accuracy of both nine-point stencils is formalized.
* **§2.2.3, the asymptotic $4/(\pi^2 h^2)$ of the condition number of the one-dimensional model
  matrix.**
* **§2.2.6, the fast Fourier transform and the operation count of Algorithm 2.1.** These are
  implementation, not statements.
* **§2.2.7, the stability of block cyclic reduction compared with Buneman's variant.** The source
  asserts it with no analysis.
-/

open Finset Matrix Polynomial
open scoped Kronecker Matrix Real

namespace SaadSparse.Chapter02

/-!
### §2.2.1–2.2.2 Truncation errors of the difference formulas

The derivations of the source are Taylor expansions with a Lagrange remainder, so each statement
below names the intermediate point at which the remainder is evaluated, as the displays of the
source do.
-/

section Truncation

/-- **Taylor's theorem** with the Lagrange remainder: if $u$ is of class $C^{k+1}$ and $t \neq 0$,
there is $\xi$ strictly between $x$ and $x + t$ with $u(x + t) = \sum_{i=0}^{k} \frac{t^i}{i!}
u^{(i)}(x) + \frac{t^{k+1}}{(k+1)!} u^{(k+1)}(\xi)$. -/
private theorem exists_taylor {u : ℝ → ℝ} {k : ℕ} (hu : ContDiff ℝ (k + 1 : ℕ) u) (x : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    ∃ ξ ∈ Set.uIoo x (x + t),
      u (x + t) = (∑ i ∈ Finset.range (k + 1), t ^ i / (Nat.factorial i : ℝ) * iteratedDeriv i u x)
        + t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) * iteratedDeriv (k + 1) u ξ := by
  have hne : x ≠ x + t := fun he => ht (by linarith)
  have hUD : UniqueDiffOn ℝ (Set.uIcc x (x + t)) := uniqueDiffOn_Icc (inf_lt_sup.2 hne)
  have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_succ k
  have hwithin : ∀ (m : ℕ), m ≤ k + 1 → ∀ y ∈ Set.uIcc x (x + t),
      iteratedDerivWithin m u (Set.uIcc x (x + t)) y = iteratedDeriv m u y := fun m hm y hy =>
    iteratedDerivWithin_eq_iteratedDeriv hUD
      (hu.of_le (by exact_mod_cast hm)).contDiffAt hy
  have hcd : ContDiffOn ℝ (k : ℕ) u (Set.uIcc x (x + t)) := (hu.of_le hle).contDiffOn
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin k u (Set.uIcc x (x + t)))
      (Set.uIoo x (x + t)) :=
    ((hu.differentiable_iteratedDeriv' k).differentiableOn).congr fun y hy =>
      hwithin k (Nat.le_succ k) y (Set.Ioo_subset_Icc_self hy)
  obtain ⟨ξ, hξ, hval⟩ := taylor_mean_remainder_lagrange hne hcd hdiff
  refine ⟨ξ, hξ, ?_⟩
  rw [taylor_within_apply] at hval
  have hsum : ∑ i ∈ Finset.range (k + 1),
      ((Nat.factorial i : ℝ)⁻¹ * (x + t - x) ^ i) • iteratedDerivWithin i u (Set.uIcc x (x + t)) x
      = ∑ i ∈ Finset.range (k + 1), t ^ i / (Nat.factorial i : ℝ) * iteratedDeriv i u x := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k + 1 := Finset.mem_range.1 hi
    rw [hwithin i (by omega) x Set.left_mem_uIcc, smul_eq_mul, add_sub_cancel_left]
    ring
  rw [hsum, hwithin (k + 1) le_rfl ξ (Set.Ioo_subset_Icc_self hξ), add_sub_cancel_left] at hval
  have hfin : t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) * iteratedDeriv (k + 1) u ξ
      = iteratedDeriv (k + 1) u ξ * t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by ring
  rw [hfin]
  linarith

/-- If $u$ is of class $C^m$, $a \in (x - h, x)$ and $b \in (x, x + h)$, then
$u^{(m)}(\xi) = (u^{(m)}(b) + u^{(m)}(a))/2$ for some $\xi \in [x - h, x + h]$, by the
intermediate value theorem. -/
private theorem exists_mid {u : ℝ → ℝ} {m : ℕ} (hu : ContDiff ℝ (m : ℕ) u) {a b x h : ℝ}
    (ha : a ∈ Set.Ioo (x - h) x) (hb : b ∈ Set.Ioo x (x + h)) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h),
      iteratedDeriv m u ξ = (iteratedDeriv m u b + iteratedDeriv m u a) / 2 := by
  have hcont : Continuous (iteratedDeriv m u) := hu.continuous_iteratedDeriv m le_rfl
  have havg : (iteratedDeriv m u b + iteratedDeriv m u a) / 2
      ∈ Set.uIcc (iteratedDeriv m u a) (iteratedDeriv m u b) := by
    rcases le_total (iteratedDeriv m u a) (iteratedDeriv m u b) with hle | hle
    · rw [Set.uIcc_of_le hle]; constructor <;> linarith
    · rw [Set.uIcc_of_ge hle]; constructor <;> linarith
  obtain ⟨ξ, hmem, hveq⟩ := intermediate_value_uIcc hcont.continuousOn havg
  refine ⟨ξ, ?_, hveq⟩
  rcases Set.mem_uIcc.1 hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩

/-- **Equations (2.9)–(2.10)** of [saad2003iterative]: the forward difference is a first-order
approximation of the derivative. Let $u : \mathbb{R} \to \mathbb{R}$ be of class $C^3$, let
$x \in \mathbb{R}$ and let $h > 0$. Then there is $\xi \in (x, x + h)$ with
$$\frac{u(x + h) - u(x)}{h} = u'(x) + \frac{h}{2} u''(x) + \frac{h^2}{6} u'''(\xi).$$
In particular the error is $\frac{h}{2} u''(x) + O(h^2)$, which is of first order in $h$.

**Reading.** The source starts with a local $C^4$ Taylor expansion in (2.9) and writes an
$O(h^2)$ remainder in (2.10). This theorem uses global $C^3$ regularity and gives the
forward-difference remainder as an exact third-derivative term at an intermediate point. -/
theorem equation_2_10 {u : ℝ → ℝ} (hu : ContDiff ℝ 3 u) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Ioo x (x + h),
      (u (x + h) - u x) / h
        = deriv u x + h / 2 * iteratedDeriv 2 u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ := by
  have hu3 : ContDiff ℝ ((2 : ℕ) + 1 : ℕ) u := by exact_mod_cast hu
  obtain ⟨ξ, hξ, hval⟩ := exists_taylor hu3 x (ne_of_gt hh)
  rw [Set.uIoo_of_le (by linarith)] at hξ
  refine ⟨ξ, hξ, ?_⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hval
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at hval
  norm_num [Nat.factorial] at hval
  rw [div_eq_iff (ne_of_gt hh)]
  linear_combination hval

/-- **Equation (2.12)** of [saad2003iterative], the centered second difference. Let
$u : \mathbb{R} \to \mathbb{R}$ be of class $C^4$, let $x \in \mathbb{R}$ and let $h > 0$. Then
there is $\xi \in [x - h, x + h]$ with
$$\frac{u(x + h) - 2u(x) + u(x - h)}{h^2} = u''(x) + \frac{h^2}{12} u^{(4)}(\xi).$$
This is the truncation error of the model problem, and the reason that the scheme is of second
order.

**Reading.** The source uses the two local Taylor expansions around $x$. The Lean theorem
assumes $u$ is $C^4$ on all of $\mathbb{R}$ and gives the same fourth-derivative remainder
with $\xi$ in the full stencil interval. -/
theorem equation_2_12 {u : ℝ → ℝ} (hu : ContDiff ℝ 4 u) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h),
      (u (x + h) - 2 * u x + u (x - h)) / h ^ 2
        = iteratedDeriv 2 u x + h ^ 2 / 12 * iteratedDeriv 4 u ξ := by
  have hu4 : ContDiff ℝ ((3 : ℕ) + 1 : ℕ) u := by exact_mod_cast hu
  obtain ⟨b, hb, hvb⟩ := exists_taylor hu4 x (ne_of_gt hh)
  obtain ⟨a, ha, hva⟩ := exists_taylor hu4 x (neg_ne_zero.2 (ne_of_gt hh))
  rw [Set.uIoo_of_le (by linarith)] at hb
  rw [Set.uIoo_of_ge (by linarith), show x + -h = x - h by ring] at ha
  rw [show x + -h = x - h by ring] at hva
  obtain ⟨ξ, hξ, hmid⟩ := exists_mid (m := 4) (by exact_mod_cast hu) ha hb
  refine ⟨ξ, hξ, ?_⟩
  simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at hvb hva
  norm_num [Nat.factorial] at hvb hva
  rw [hmid, div_eq_iff (by positivity : (h : ℝ) ^ 2 ≠ 0)]
  linear_combination hvb + hva

/-- **Equation (2.13)** of [saad2003iterative], the centered first difference. Let
$u : \mathbb{R} \to \mathbb{R}$ be of class $C^3$, let $x \in \mathbb{R}$ and let $h > 0$. Then
there is $\xi \in [x - h, x + h]$ with
$$\frac{u(x + h) - u(x - h)}{2h} = u'(x) + \frac{h^2}{6} u'''(\xi).$$
So the centered formula is of second order, while the forward difference (2.8) is of first order
(`SaadSparse.Chapter02.equation_2_10`).

**Reading.** The source states second-order accuracy. The theorem uses a globally $C^3$
function and gives the exact Lagrange remainder. -/
theorem equation_2_13 {u : ℝ → ℝ} (hu : ContDiff ℝ 3 u) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h),
      (u (x + h) - u (x - h)) / (2 * h) = deriv u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ := by
  have hu3 : ContDiff ℝ ((2 : ℕ) + 1 : ℕ) u := by exact_mod_cast hu
  obtain ⟨b, hb, hvb⟩ := exists_taylor hu3 x (ne_of_gt hh)
  obtain ⟨a, ha, hva⟩ := exists_taylor hu3 x (neg_ne_zero.2 (ne_of_gt hh))
  rw [Set.uIoo_of_le (by linarith)] at hb
  rw [Set.uIoo_of_ge (by linarith), show x + -h = x - h by ring] at ha
  rw [show x + -h = x - h by ring] at hva
  obtain ⟨ξ, hξ, hmid⟩ := exists_mid (m := 3) (by exact_mod_cast hu) ha hb
  refine ⟨ξ, hξ, ?_⟩
  simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at hvb hva
  norm_num [Nat.factorial] at hvb hva
  rw [hmid, div_eq_iff (by positivity : (2 : ℝ) * h ≠ 0)]
  linear_combination hvb - hva

/-- **Problem P-2.6** of [saad2003iterative]: the conservative difference of (2.16) is the backward
difference of the staggered forward difference, $\delta^-(a_{i+1/2} \delta^+ u)$. Let
$a, u : \mathbb{R} \to \mathbb{R}$ and $x, h \in \mathbb{R}$, and let
$g(t) = a(t + h/2)(u(t + h) - u(t))$ be the staggered flux. Then
$$a(x + h/2)(u(x + h) - u(x)) - a(x - h/2)(u(x) - u(x - h)) = g(x) - g(x - h).$$

**Reading.** The exercise includes the factor $1/h^2$ on each side. The theorem gives
the unscaled identity, from which the exercise follows by multiplying by $1/h^2$.
-/
theorem equation_2_16_symm (a u : ℝ → ℝ) (x h : ℝ) :
    a (x + h / 2) * (u (x + h) - u x) - a (x - h / 2) * (u x - u (x - h))
      = (fun t => a (t + h / 2) * (u (t + h) - u t)) x
        - (fun t => a (t + h / 2) * (u (t + h) - u t)) (x - h) := by
  simp only
  ring_nf

/-- If $a$ and $u$ are of class $C^4$, then $(a u')'(x) = a'(x) u'(x) + a(x) u''(x)$. -/
private theorem deriv_mul_deriv {a u : ℝ → ℝ} (ha : ContDiff ℝ 4 a) (hu : ContDiff ℝ 4 u)
    (x : ℝ) : deriv (fun t => a t * deriv u t) x
      = deriv a x * deriv u x + a x * iteratedDeriv 2 u x := by
  have hda : DifferentiableAt ℝ a x := (ha.differentiable (by norm_num)).differentiableAt
  have hdu : DifferentiableAt ℝ (deriv u) x := by
    have hd := (hu.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt (x := x)
    rwa [iteratedDeriv_one] at hd
  have hm : HasDerivAt (fun t => a t * deriv u t)
      (deriv a x * deriv u x + a x * deriv (deriv u) x) x := hda.hasDerivAt.mul hdu.hasDerivAt
  rw [hm.deriv, iteratedDeriv_succ, iteratedDeriv_one]

/-- **Equation (2.16)** and **Problem P-2.7** of [saad2003iterative]: the conservative difference
approximates the divergence form $(a u')'$ to second order. Let
$a, u : \mathbb{R} \to \mathbb{R}$ be of class $C^4$, let $x \in \mathbb{R}$ and let $h > 0$.
Then there are $\zeta, \zeta', \xi, \xi' \in [x - h, x + h]$ with
$$\frac{a(x + \frac{h}{2})(u(x + h) - u(x)) - a(x - \frac{h}{2})(u(x) - u(x - h))}{h^2} - (a
  u')'(x) = h^2 \Big( \frac{a(x) u^{(4)}(\xi)}{12} + \frac{(a''(x) + \frac{h^2}{48}
  a^{(4)}(\zeta))(u''(x) + \frac{h^2}{12} u^{(4)}(\xi))}{8} + \frac{a'(x) u'''(\xi')}{6} +
  \frac{a'''(\zeta')(u'(x) + \frac{h^2}{6} u'''(\xi'))}{24} \Big).$$
The bracket is a fixed polynomial in values of $a$, $u$ and their derivatives at these points
and at $x$, so it is bounded independently of $h$ on any bounded range of steps.

**Reading.** The source states an $O(h^2)$ remainder and asks for second-order accuracy.
The theorem gives the exact remainder under global $C^4$ assumptions on $a$ and $u$.

The proof splits the difference into the average and the half difference of the two staggered
coefficients. The average multiplies the centered second difference of $u$, and the half
difference multiplies the centered first difference. All four differences are expanded by
`SaadSparse.Chapter02.equation_2_12` and `SaadSparse.Chapter02.equation_2_13`, at step $h/2$ for
$a$ and at step $h$ for $u$. -/
theorem equation_2_16 {a u : ℝ → ℝ} (ha : ContDiff ℝ 4 a) (hu : ContDiff ℝ 4 u) (x : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ∃ ζ ∈ Set.Icc (x - h) (x + h), ∃ ζ' ∈ Set.Icc (x - h) (x + h),
      ∃ ξ ∈ Set.Icc (x - h) (x + h), ∃ ξ' ∈ Set.Icc (x - h) (x + h),
      (a (x + h / 2) * (u (x + h) - u x) - a (x - h / 2) * (u x - u (x - h))) / h ^ 2
          - deriv (fun t => a t * deriv u t) x
        = h ^ 2 * (a x * iteratedDeriv 4 u ξ / 12
            + (iteratedDeriv 2 a x + h ^ 2 / 48 * iteratedDeriv 4 a ζ)
              * (iteratedDeriv 2 u x + h ^ 2 / 12 * iteratedDeriv 4 u ξ) / 8
            + deriv a x * iteratedDeriv 3 u ξ' / 6
            + iteratedDeriv 3 a ζ' * (deriv u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ') / 24) := by
  have hk : (0 : ℝ) < h / 2 := by linarith
  have hkne : (h / 2 : ℝ) ^ 2 ≠ 0 := by positivity
  have hkne' : (2 : ℝ) * (h / 2) ≠ 0 := by positivity
  have hhne : (h : ℝ) ^ 2 ≠ 0 := by positivity
  have hhne' : (2 : ℝ) * h ≠ 0 := by positivity
  obtain ⟨ζ, hζ, hA2⟩ := equation_2_12 ha x hk
  obtain ⟨ζ', hζ', hA1⟩ := equation_2_13 (ha.of_le (by norm_num)) x hk
  obtain ⟨ξ, hξ, hU2⟩ := equation_2_12 hu x hh
  obtain ⟨ξ', hξ', hU1⟩ := equation_2_13 (hu.of_le (by norm_num)) x hh
  rw [div_eq_iff hkne] at hA2
  rw [div_eq_iff hkne'] at hA1
  rw [div_eq_iff hhne] at hU2
  rw [div_eq_iff hhne'] at hU1
  refine ⟨ζ, ⟨by linarith [hζ.1], by linarith [hζ.2]⟩,
    ζ', ⟨by linarith [hζ'.1], by linarith [hζ'.2]⟩, ξ, hξ, ξ', hξ', ?_⟩
  have hAp : a (x + h / 2)
      = a x + h ^ 2 / 8 * (iteratedDeriv 2 a x + h ^ 2 / 48 * iteratedDeriv 4 a ζ)
        + h / 2 * (deriv a x + h ^ 2 / 24 * iteratedDeriv 3 a ζ') := by
    linear_combination (1 / 2 : ℝ) * hA2 + (1 / 2 : ℝ) * hA1
  have hAm : a (x - h / 2)
      = a x + h ^ 2 / 8 * (iteratedDeriv 2 a x + h ^ 2 / 48 * iteratedDeriv 4 a ζ)
        - h / 2 * (deriv a x + h ^ 2 / 24 * iteratedDeriv 3 a ζ') := by
    linear_combination (1 / 2 : ℝ) * hA2 - (1 / 2 : ℝ) * hA1
  have hUp : u (x + h) - u x
      = h ^ 2 / 2 * (iteratedDeriv 2 u x + h ^ 2 / 12 * iteratedDeriv 4 u ξ)
        + h * (deriv u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ') := by
    linear_combination (1 / 2 : ℝ) * hU2 + (1 / 2 : ℝ) * hU1
  have hUm : u x - u (x - h)
      = h * (deriv u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ')
        - h ^ 2 / 2 * (iteratedDeriv 2 u x + h ^ 2 / 12 * iteratedDeriv 4 u ξ) := by
    linear_combination (-1 / 2 : ℝ) * hU2 + (1 / 2 : ℝ) * hU1
  rw [hAp, hAm, hUp, hUm, deriv_mul_deriv ha hu]
  field_simp
  ring

/-- **Equation (2.17)** of [saad2003iterative], the five-point centered approximation of the
Laplacean on a uniform mesh, with its truncation error. Let $u : \mathbb{R}^2 \to \mathbb{R}$ be
of class $C^4$ in each variable separately, let $(x_1, x_2) \in \mathbb{R}^2$ and let $h > 0$.
Then there are $\xi \in [x_1 - h, x_1 + h]$ and $\eta \in [x_2 - h, x_2 + h]$ with
$$\frac{u(x_1 + h, x_2) + u(x_1 - h, x_2) + u(x_1, x_2 + h) + u(x_1, x_2 - h) - 4u(x_1,
  x_2)}{h^2} = \Delta u(x_1, x_2) + \frac{h^2}{12} \big( \partial_1^4 u(\xi, x_2) + \partial_2^4
  u(x_1, \eta) \big).$$

**Reading.** The source expands the leading error at $(x_1,x_2)$ and writes an
$O(h^3)$ remainder. The theorem gives exact fourth-derivative terms at intermediate
points and assumes global $C^4$ regularity on coordinate lines separately. -/
theorem equation_2_17 {u : ℝ → ℝ → ℝ} (h₁ : ∀ y, ContDiff ℝ 4 fun t => u t y)
    (h₂ : ∀ x, ContDiff ℝ 4 fun t => u x t) (x₁ x₂ : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x₁ - h) (x₁ + h), ∃ η ∈ Set.Icc (x₂ - h) (x₂ + h),
      (u (x₁ + h) x₂ + u (x₁ - h) x₂ + u x₁ (x₂ + h) + u x₁ (x₂ - h) - 4 * u x₁ x₂) / h ^ 2
        = iteratedDeriv 2 (fun t => u t x₂) x₁ + iteratedDeriv 2 (fun t => u x₁ t) x₂
          + h ^ 2 / 12 * (iteratedDeriv 4 (fun t => u t x₂) ξ
            + iteratedDeriv 4 (fun t => u x₁ t) η) := by
  obtain ⟨ξ, hξ, hv1⟩ := equation_2_12 (h₁ x₂) x₁ hh
  obtain ⟨η, hη, hv2⟩ := equation_2_12 (h₂ x₁) x₂ hh
  refine ⟨ξ, hξ, η, hη, ?_⟩
  rw [div_eq_iff (by positivity : (h : ℝ) ^ 2 ≠ 0)]
  rw [div_eq_iff (by positivity : (h : ℝ) ^ 2 ≠ 0)] at hv1 hv2
  linear_combination hv1 + hv2

/-!
### §2.2.2 The nine-point stencils of Figure 2.4

The two nine-point formulas combine the five-point stencil (2.17) with the diagonal stencil, which
is the same five-point pattern on the two diagonal lines. Problem P-2.4 gives the recipe: $1/3$ of
one plus $2/3$ of the other, and the reverse combination. The coefficients below are the ones that
this recipe gives.

The analysis rests on one exact identity among the nine values,
`SaadSparse.Chapter02.diagonalStencil_eq`: the diagonal stencil is $\delta_x^2 + \delta_y^2 +
\frac{h^2}{2} \delta_x^2 \delta_y^2$. So each nine-point formula is the five-point formula plus a
multiple of $h^2$ times the product of the two one-dimensional second differences. No two-variable
Taylor expansion is needed: every error term comes from `SaadSparse.Chapter02.equation_2_12` applied
along a grid line.

The source also says that (d) is sixth order accurate on harmonic functions, and this is not
formalized. The expansion continues as $\Delta u + \frac{h^2}{12} \Delta^2 u + \frac{h^4}{360}
\Delta(\partial_1^4 + 4 \partial_1^2 \partial_2^2 + \partial_2^4) u + O(h^6)$, and both correction
terms vanish when $\Delta u$ vanishes identically. To bring the terms of the expansion into this
form, one needs the equality of the mixed partial derivatives $\partial_1^2 \partial_2^2 u =
\partial_2^2 \partial_1^2 u$. Mathlib has the symmetry of the second Fréchet derivative of a
function on a normed space (`second_derivative_symmetric`), but nothing that transports it to the
iterated partial derivatives of a curried function $u : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$,
and the sixth-order clause would need that bridge iterated to order six.
-/

/-- **Section 2.2.2** of [saad2003iterative], the centred second difference quotient in the first
variable:
$$\delta_x^2 u(x, y) = \frac{u(x + h, y) - 2u(x, y) + u(x - h, y)}{h^2}.$$

**Reading.** The source uses a positive mesh size. This uniform-grid quotient also
accepts signed $h$, with value $0$ at $h=0$ by totalized division. -/
noncomputable def diffX (u : ℝ → ℝ → ℝ) (h : ℝ) : ℝ → ℝ → ℝ :=
  fun x y => (u (x + h) y - 2 * u x y + u (x - h) y) / h ^ 2

/-- **Section 2.2.2** of [saad2003iterative], the centred second difference quotient in the second
variable:
$$\delta_y^2 u(x, y) = \frac{u(x, y + h) - 2u(x, y) + u(x, y - h)}{h^2}.$$

**Reading.** The source uses a positive mesh size. This uniform-grid quotient also
accepts signed $h$, with value $0$ at $h=0$ by totalized division.
-/
noncomputable def diffY (u : ℝ → ℝ → ℝ) (h : ℝ) : ℝ → ℝ → ℝ :=
  fun x y => (u x (y + h) - 2 * u x y + u x (y - h)) / h ^ 2

/-- **Figure 2.3(b)** of [saad2003iterative], the diagonal (skewed) stencil: the five-point pattern
taken on the two diagonal lines through $(x, y)$,
$$\frac{u(x + h, y + h) + u(x + h, y - h) + u(x - h, y + h) + u(x - h, y - h) - 4u(x,
  y)}{2h^2}.$$
The mesh spacing along a diagonal line is $h\sqrt{2}$ for $h>0$.

**Reading.** The source uses a positive mesh size. The definition is total and gives
$0$ at $h=0$. -/
noncomputable def diagonalStencil (u : ℝ → ℝ → ℝ) (h x y : ℝ) : ℝ :=
  (u (x + h) (y + h) + u (x + h) (y - h) + u (x - h) (y + h) + u (x - h) (y - h)
    - 4 * u x y) / (2 * h ^ 2)

/-- **Figure 2.4(c)** of [saad2003iterative], the nine-point stencil
$$\frac{1}{3h^2} \big[ (N + S + E + W) + (NE + NW + SE + SW) - 8C \big],$$
where $C = u(x, y)$, the letters $N, S, E, W$ stand for the values of $u$ at the four neighbours
$(x, y \pm h)$ and $(x \pm h, y)$, and $NE, NW, SE, SW$ stand for the values at the four
diagonal neighbours $(x \pm h, y \pm h)$. It is $1/3$ of the five-point formula (2.17) plus
$2/3$ of the diagonal stencil.

**Reading.** The source uses a positive mesh size. The definition is total and gives
$0$ at $h=0$. -/
noncomputable def ninePointC (u : ℝ → ℝ → ℝ) (h x y : ℝ) : ℝ :=
  (u (x + h) y + u (x - h) y + u x (y + h) + u x (y - h)
    + (u (x + h) (y + h) + u (x + h) (y - h) + u (x - h) (y + h) + u (x - h) (y - h))
    - 8 * u x y) / (3 * h ^ 2)

/-- **Figure 2.4(d)** of [saad2003iterative], the nine-point stencil
$$\frac{1}{6h^2} \big[ 4(N + S + E + W) + (NE + NW + SE + SW) - 20C \big],$$
with the notation of `SaadSparse.Chapter02.ninePointC`. It is $2/3$ of the five-point formula
(2.17) plus $1/3$ of the diagonal stencil.

**Reading.** The source uses a positive mesh size. The definition is total and gives
$0$ at $h=0$. -/
noncomputable def ninePointD (u : ℝ → ℝ → ℝ) (h x y : ℝ) : ℝ :=
  (4 * (u (x + h) y + u (x - h) y + u x (y + h) + u x (y - h))
    + (u (x + h) (y + h) + u (x + h) (y - h) + u (x - h) (y + h) + u (x - h) (y - h))
    - 20 * u x y) / (6 * h ^ 2)

/-- The diagonal stencil of Figure 2.3(b) of [saad2003iterative] is a corrected five-point formula.
Let $u : \mathbb{R}^2 \to \mathbb{R}$ be any function, let $h \neq 0$ and let
$(x, y) \in \mathbb{R}^2$. Then the diagonal stencil at $(x, y)$ is
$$\delta_x^2 u(x, y) + \delta_y^2 u(x, y) + \frac{h^2}{2} \delta_x^2 \delta_y^2 u(x, y).$$

This is an identity among the nine grid values, with no hypothesis on $u$. Grouping the four
diagonal points into the two second differences in $y$ at $x \pm h$ produces the product term. -/
theorem diagonalStencil_eq (u : ℝ → ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (x y : ℝ) :
    diagonalStencil u h x y
      = diffX u h x y + diffY u h x y + h ^ 2 / 2 * diffX (diffY u h) h x y := by
  simp only [diagonalStencil, diffX, diffY]
  field_simp
  ring

/-- **Figure 2.4(c)** of [saad2003iterative] as a corrected five-point formula. Let
$u : \mathbb{R}^2 \to \mathbb{R}$ be any function, let $h \neq 0$ and let
$(x, y) \in \mathbb{R}^2$. Then the nine-point stencil (c) at $(x, y)$ is
$$\delta_x^2 u(x, y) + \delta_y^2 u(x, y) + \frac{h^2}{3} \delta_x^2 \delta_y^2 u(x, y).$$
-/
theorem ninePointC_eq (u : ℝ → ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (x y : ℝ) :
    ninePointC u h x y
      = diffX u h x y + diffY u h x y + h ^ 2 / 3 * diffX (diffY u h) h x y := by
  simp only [ninePointC, diffX, diffY]
  field_simp
  ring

/-- **Figure 2.4(d)** of [saad2003iterative] as a corrected five-point formula. Let
$u : \mathbb{R}^2 \to \mathbb{R}$ be any function, let $h \neq 0$ and let
$(x, y) \in \mathbb{R}^2$. Then the nine-point stencil (d) at $(x, y)$ is
$$\delta_x^2 u(x, y) + \delta_y^2 u(x, y) + \frac{h^2}{6} \delta_x^2 \delta_y^2 u(x, y).$$
-/
theorem ninePointD_eq (u : ℝ → ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (x y : ℝ) :
    ninePointD u h x y
      = diffX u h x y + diffY u h x y + h ^ 2 / 6 * diffX (diffY u h) h x y := by
  simp only [ninePointD, diffX, diffY]
  field_simp
  ring

/-- If $w$ is of class $C^2$ and $h > 0$, then $(w(t + h) - 2w(t) + w(t - h))/h^2 = w''(\theta)$ for
some $\theta \in [t - h, t + h]$. -/
private theorem exists_secondDifference {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (t : ℝ) {h : ℝ}
    (hh : 0 < h) :
    ∃ θ ∈ Set.Icc (t - h) (t + h),
      (w (t + h) - 2 * w t + w (t - h)) / h ^ 2 = iteratedDeriv 2 w θ := by
  have hw2 : ContDiff ℝ ((1 : ℕ) + 1 : ℕ) w := by exact_mod_cast hw
  obtain ⟨b, hb, hvb⟩ := exists_taylor hw2 t (ne_of_gt hh)
  obtain ⟨a, ha, hva⟩ := exists_taylor hw2 t (neg_ne_zero.2 (ne_of_gt hh))
  rw [Set.uIoo_of_le (by linarith)] at hb
  rw [Set.uIoo_of_ge (by linarith), show t + -h = t - h by ring] at ha
  rw [show t + -h = t - h by ring] at hva
  obtain ⟨θ, hθ, hmid⟩ := exists_mid (m := 2) (by exact_mod_cast hw) ha hb
  refine ⟨θ, hθ, ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero,
    iteratedDeriv_one] at hvb hva
  norm_num [Nat.factorial] at hvb hva
  rw [hmid, div_eq_iff (by positivity : (h : ℝ) ^ 2 ≠ 0)]
  linear_combination hvb + hva

/-- If $f$, $g$ and $k$ are of class $C^2$, the second derivative of $(f - 2g + k)/c$ at $t$ is
$(f''(t) - 2g''(t) + k''(t))/c$. -/
private theorem iteratedDeriv_two_comb {f g k : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hk : ContDiff ℝ 2 k) (c : ℝ) (t : ℝ) :
    iteratedDeriv 2 (fun s => (f s - 2 * g s + k s) / c) t
      = (iteratedDeriv 2 f t - 2 * iteratedDeriv 2 g t + iteratedDeriv 2 k t) / c := by
  have hg2 : ContDiff ℝ 2 fun s => 2 * g s := contDiff_const.mul hg
  have hfg : ContDiff ℝ 2 fun s => f s - 2 * g s := hf.sub hg2
  rw [iteratedDeriv_div_const, iteratedDeriv_fun_add hfg.contDiffAt hk.contDiffAt,
    iteratedDeriv_fun_sub hf.contDiffAt hg2.contDiffAt, iteratedDeriv_const_mul 2 hg.contDiffAt]

/-- If $t \mapsto u(t, y)$ is of class $C^4$ for every $y$, $s \mapsto \partial_1^2 u(t, s)$ is of
class $C^2$ for every $t$, and $h > 0$, then $\delta_x^2 \delta_y^2 u(x, y) = \partial_2^2
\partial_1^2 u(\theta, \zeta)$ for some $\theta \in [x - h, x + h]$ and
$\zeta \in [y - h, y + h]$. -/
private theorem exists_diffX_diffY {u : ℝ → ℝ → ℝ} (h₁ : ∀ y, ContDiff ℝ 4 fun t => u t y)
    (h₁₂ : ∀ t, ContDiff ℝ 2 fun s => iteratedDeriv 2 (fun r => u r s) t)
    (x y : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ θ ∈ Set.Icc (x - h) (x + h), ∃ ζ ∈ Set.Icc (y - h) (y + h),
      diffX (diffY u h) h x y
        = iteratedDeriv 2 (fun s => iteratedDeriv 2 (fun r => u r s) θ) ζ := by
  have hle : (2 : WithTop ℕ∞) ≤ 4 := by norm_num
  have hv : ContDiff ℝ 2 fun t => diffY u h t y := by
    simp only [diffY]
    exact ((((h₁ (y + h)).of_le hle).sub (contDiff_const.mul ((h₁ y).of_le hle))).add
      ((h₁ (y - h)).of_le hle)).div_const _
  obtain ⟨θ, hθ, hveq⟩ := exists_secondDifference hv x hh
  obtain ⟨ζ, hζ, hzeq⟩ := exists_secondDifference (h₁₂ θ) y hh
  refine ⟨θ, hθ, ζ, hζ, ?_⟩
  have hcomb : iteratedDeriv 2 (fun t => diffY u h t y) θ
      = (iteratedDeriv 2 (fun t => u t (y + h)) θ - 2 * iteratedDeriv 2 (fun t => u t y) θ
        + iteratedDeriv 2 (fun t => u t (y - h)) θ) / h ^ 2 := by
    simp only [diffY]
    exact iteratedDeriv_two_comb ((h₁ (y + h)).of_le hle) ((h₁ y).of_le hle)
      ((h₁ (y - h)).of_le hle) _ θ
  rw [show diffX (diffY u h) h x y
      = ((fun t => diffY u h t y) (x + h) - 2 * (fun t => diffY u h t y) x
        + (fun t => diffY u h t y) (x - h)) / h ^ 2 from rfl, hveq, hcomb, ← hzeq]

/-- **Figure 2.4(d)** of [saad2003iterative]: the nine-point formula (d) is second order accurate.
Let $u : \mathbb{R}^2 \to \mathbb{R}$ be such that $t \mapsto u(t, y)$ and $t \mapsto u(x, t)$
are of class $C^4$ for all $x, y$, and $s \mapsto \partial_1^2 u(t, s)$ is of class $C^2$ for
every $t$. Let $(x, y) \in \mathbb{R}^2$ and $h > 0$. Then there are
$\xi, \theta \in [x - h, x + h]$ and $\eta, \zeta \in [y - h, y + h]$ with
$$(d) - \Delta u(x, y) = h^2 \Big( \frac{\partial_1^4 u(\xi, y)}{12} + \frac{\partial_2^4 u(x,
  \eta)}{12} + \frac{\partial_2^2 \partial_1^2 u(\theta, \zeta)}{6} \Big),$$
where $(d)$ is the stencil `SaadSparse.Chapter02.ninePointD` at $(x, y)$.

**Reading.** The source asserts second-order accuracy. The theorem gives an exact
remainder with pure and mixed derivatives at intermediate points. Local boundedness
of those derivatives, as for a jointly $C^4$ function, gives the asymptotic bound. -/
theorem ninePointD_error {u : ℝ → ℝ → ℝ} (h₁ : ∀ y, ContDiff ℝ 4 fun t => u t y)
    (h₂ : ∀ x, ContDiff ℝ 4 fun t => u x t)
    (h₁₂ : ∀ t, ContDiff ℝ 2 fun s => iteratedDeriv 2 (fun r => u r s) t)
    (x y : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h), ∃ η ∈ Set.Icc (y - h) (y + h),
      ∃ θ ∈ Set.Icc (x - h) (x + h), ∃ ζ ∈ Set.Icc (y - h) (y + h),
      ninePointD u h x y
          - (iteratedDeriv 2 (fun t => u t y) x + iteratedDeriv 2 (fun t => u x t) y)
        = h ^ 2 * (iteratedDeriv 4 (fun t => u t y) ξ / 12
            + iteratedDeriv 4 (fun t => u x t) η / 12
            + iteratedDeriv 2 (fun s => iteratedDeriv 2 (fun r => u r s) θ) ζ / 6) := by
  obtain ⟨ξ, hξ, hx2⟩ := equation_2_12 (h₁ y) x hh
  obtain ⟨η, hη, hy2⟩ := equation_2_12 (h₂ x) y hh
  obtain ⟨θ, hθ, ζ, hζ, hxy⟩ := exists_diffX_diffY h₁ h₁₂ x y hh
  refine ⟨ξ, hξ, η, hη, θ, hθ, ζ, hζ, ?_⟩
  rw [ninePointD_eq u hh.ne' x y, hxy, show diffX u h x y
      = ((fun t => u t y) (x + h) - 2 * (fun t => u t y) x + (fun t => u t y) (x - h)) / h ^ 2
      from rfl, hx2, show diffY u h x y
      = ((fun t => u x t) (y + h) - 2 * (fun t => u x t) y + (fun t => u x t) (y - h)) / h ^ 2
      from rfl, hy2]
  ring

/-- **Figure 2.4(c)** of [saad2003iterative]: the nine-point formula (c) is second order accurate.
Under the hypotheses of `SaadSparse.Chapter02.ninePointD_error`, there are
$\xi, \theta \in [x - h, x + h]$ and $\eta, \zeta \in [y - h, y + h]$ with
$$(c) - \Delta u(x, y) = h^2 \Big( \frac{\partial_1^4 u(\xi, y)}{12} + \frac{\partial_2^4 u(x,
  \eta)}{12} + \frac{\partial_2^2 \partial_1^2 u(\theta, \zeta)}{3} \Big),$$
where $(c)$ is the stencil `SaadSparse.Chapter02.ninePointC` at $(x, y)$.

**Reading.** The source asserts second-order accuracy. The theorem gives an exact
remainder with pure and mixed derivatives at intermediate points. Local boundedness of
those derivatives, as for a jointly $C^4$ function, gives the asymptotic bound. -/
theorem ninePointC_error {u : ℝ → ℝ → ℝ} (h₁ : ∀ y, ContDiff ℝ 4 fun t => u t y)
    (h₂ : ∀ x, ContDiff ℝ 4 fun t => u x t)
    (h₁₂ : ∀ t, ContDiff ℝ 2 fun s => iteratedDeriv 2 (fun r => u r s) t)
    (x y : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h), ∃ η ∈ Set.Icc (y - h) (y + h),
      ∃ θ ∈ Set.Icc (x - h) (x + h), ∃ ζ ∈ Set.Icc (y - h) (y + h),
      ninePointC u h x y
          - (iteratedDeriv 2 (fun t => u t y) x + iteratedDeriv 2 (fun t => u x t) y)
        = h ^ 2 * (iteratedDeriv 4 (fun t => u t y) ξ / 12
            + iteratedDeriv 4 (fun t => u x t) η / 12
            + iteratedDeriv 2 (fun s => iteratedDeriv 2 (fun r => u r s) θ) ζ / 3) := by
  obtain ⟨ξ, hξ, hx2⟩ := equation_2_12 (h₁ y) x hh
  obtain ⟨η, hη, hy2⟩ := equation_2_12 (h₂ x) y hh
  obtain ⟨θ, hθ, ζ, hζ, hxy⟩ := exists_diffX_diffY h₁ h₁₂ x y hh
  refine ⟨ξ, hξ, η, hη, θ, hθ, ζ, hζ, ?_⟩
  rw [ninePointC_eq u hh.ne' x y, hxy, show diffX u h x y
      = ((fun t => u t y) (x + h) - 2 * (fun t => u t y) x + (fun t => u t y) (x - h)) / h ^ 2
      from rfl, hx2, show diffY u h x y
      = ((fun t => u x t) (y + h) - 2 * (fun t => u x t) y + (fun t => u x t) (y - h)) / h ^ 2
      from rfl, hy2]
  ring

end Truncation

/-! ### §2.2.3 The one-dimensional model problem -/

section OneDimensional

variable {n : ℕ}

/-- **Section 2.2.3** of [saad2003iterative], the homogeneous Dirichlet boundary values. A vector
$v = (v_1, \dots, v_n)$ of values at the $n$ interior grid points is extended to all grid
indices $k \in \mathbb{N}$ by $v_k$ for $1 \le k \le n$ and by $0$ otherwise, so that
$v_0 = v_{n+1} = 0$.

In Lean `dirichletExt v (i + 1) = v i` for an interior index `i : Fin n`. The definition is the
backbone's zero padding `Matrix.padZero`.

**Reading.** The source gives values on the interior and the two endpoints of the grid.
This definition extends by zero on all natural indices outside the interior. -/
def dirichletExt (v : Fin n → ℝ) : ℕ → ℝ :=
  Matrix.padZero v

/-- The Dirichlet extension vanishes at the boundary index $0$. -/
@[simp]
theorem dirichletExt_zero (v : Fin n → ℝ) : dirichletExt v 0 = 0 := rfl

/-- The Dirichlet extension at the grid index $k + 1$ is the entry of $v$ with Lean index $k$ if
$k < n$, and $0$ otherwise. -/
theorem dirichletExt_succ (v : Fin n → ℝ) (k : ℕ) :
    dirichletExt v (k + 1) = if hk : k < n then v ⟨k, hk⟩ else 0 := rfl

/-- The Dirichlet extension at the grid index $i + 1$ is the entry of $v$ with Lean index $i$, for
every `i : Fin n`. -/
@[simp]
theorem dirichletExt_coe_succ (v : Fin n → ℝ) (i : Fin n) :
    dirichletExt v ((i : ℕ) + 1) = v i :=
  Matrix.padZero_val_succ v i

/-- The Dirichlet extension vanishes at every grid index $k > n$.

**Generalization.** The source imposes the right boundary value at $k=n+1$. The zero
extension has value $0$ at all indices beyond $n$. -/
theorem dirichletExt_of_gt (v : Fin n → ℝ) {k : ℕ} (hk : n < k) : dirichletExt v k = 0 :=
  Matrix.padZero_of_lt v hk

/-- **Section 2.2.3** of [saad2003iterative], the one-dimensional model matrix. For
$n \in \mathbb{N}$ and $h \in \mathbb{R}$ it is
$$A = \frac{1}{h^2} \operatorname{tridiag}(-1, 2, -1) \in \mathbb{R}^{n \times n},$$
the matrix of $-u'' = f$ on $(0, 1)$ with homogeneous Dirichlet boundary conditions, discretized
on the uniform grid $x_i = ih$.

**Reading.** The scalar equation in the source has $h^2 f_i$ on its right side. The
displayed matrix instead carries $1/h^2$, which is the convention used here.

**Generalization.** The source displays the matrix at $n=6$ for $h=1/(n+1)$. The
definition accepts every size and free step $h$, with value $0$ at $h=0$. -/
noncomputable def laplacian1D (n : ℕ) (h : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (h ^ 2)⁻¹ • Matrix.symmTridiagonalToeplitz n (-1) 2

/-- The entries of the one-dimensional model matrix: $a_{ii} = 2/h^2$, $a_{ij} = -1/h^2$ if
$|i - j| = 1$, and $a_{ij} = 0$ otherwise.

**Generalization.** The source displays the six-point matrix of §2.2.3 for its grid spacing.
The entry formula holds for every size and free step, with value $0$ at $h=0$. -/
theorem laplacian1D_apply (h : ℝ) (i j : Fin n) :
    laplacian1D n h i j =
      (h ^ 2)⁻¹ * (if (i : ℕ) = j then 2 else
        if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0) := by
  rw [laplacian1D, Matrix.smul_apply, smul_eq_mul, Matrix.symmTridiagonalToeplitz_apply']

/-- If the quadratic form of $A$ lies between $\lambda_{\min}$ and $\lambda_{\max}$ in the sense of
`LinearMap.IsSymmetricBoundedBy`, and $c > 0$, then the quadratic form of $cA$ lies between
$c \lambda_{\min}$ and $c \lambda_{\max}$. -/
private theorem isSymmetricBoundedBy_smul {A : Matrix (Fin n) (Fin n) ℝ} {lmin lmax c : ℝ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetricBoundedBy lmin lmax) (hc : 0 < c) :
    (Matrix.toEuclideanLin (c • A)).IsSymmetricBoundedBy (c * lmin) (c * lmax) := by
  have hmul : ∀ x : EuclideanSpace ℝ (Fin n),
      Matrix.toEuclideanLin (c • A) x = c • Matrix.toEuclideanLin A x := by
    intro x
    change WithLp.toLp 2 ((c • A) *ᵥ WithLp.ofLp x) = _
    rw [Matrix.smul_mulVec]
    rfl
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hmul, hmul, real_inner_smul_left, real_inner_smul_right, hA.isSymmetric x y]
  · have h := hA.isCoerciveWith x
    rw [hmul, RCLike.re_to_real, real_inner_smul_left, mul_assoc]
    rw [RCLike.re_to_real] at h
    exact mul_le_mul_of_nonneg_left h hc.le
  · have h := hA.re_inner_le x
    rw [hmul, RCLike.re_to_real, real_inner_smul_left, mul_assoc]
    rw [RCLike.re_to_real] at h
    exact mul_le_mul_of_nonneg_left h hc.le

/-- **Section 2.2.3** of [saad2003iterative], the difference equations of the model problem. Let
$h \in \mathbb{R}$ and $v = (v_1, \dots, v_n) \in \mathbb{R}^n$, and set $v_0 = v_{n+1} = 0$.
Then for $i = 1, \dots, n$ the $i$-th entry of $Av$ is
$$(Av)_i = \frac{-v_{i-1} + 2v_i - v_{i+1}}{h^2}.$$

The boundary values are supplied by `SaadSparse.Chapter02.dirichletExt`, and the Lean row
`i : Fin n` is the book's row $i + 1$.

**Reading.** The source writes the scalar stencil equation with $h^2 f_i$ on the right.
The identity uses the scaled operator on the left as in the displayed matrix. It
holds for a free step and arbitrary interior values. -/
theorem laplacian1D_mulVec_apply (h : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (laplacian1D n h *ᵥ v) i
      = (-dirichletExt v (i : ℕ) + 2 * dirichletExt v ((i : ℕ) + 1)
          - dirichletExt v ((i : ℕ) + 2)) / h ^ 2 := by
  rw [laplacian1D, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    Matrix.symmTridiagonalToeplitz_mulVec_apply]
  simp only [dirichletExt]
  field_simp
  ring

/-- The eigenpairs of the one-dimensional model matrix $A$ of §2.2.3 of [saad2003iterative]. Let
$h \in \mathbb{R}$ and $k \in \{1, \dots, n\}$, and let $w_k \in \mathbb{R}^n$ be the discrete
sine vector with entries $\sin(jk\pi/(n + 1))$, $j = 1, \dots, n$. Then
$$A w_k = \frac{4}{h^2} \sin^2\Big(\frac{k\pi}{2(n + 1)}\Big) w_k.$$

**Reading.** Equations (13.7)–(13.8) give the eigenpairs for the unscaled matrix.
This form uses the $1/h^2$ scaling of §2.2.3 and includes $h=0$ by totalized division.

The vector $w_k$ is `Matrix.sineVec n k`, and the Lean index `k : Fin n` stands for the book's
$k + 1$. -/
theorem laplacian1D_mulVec_sineVec (h : ℝ) (k : Fin n) :
    laplacian1D n h *ᵥ Matrix.sineVec n k
      = (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2)
        • Matrix.sineVec n k := by
  rw [laplacian1D, Matrix.smul_mulVec, Matrix.symmTridiagonalToeplitz_mulVec_sineVec, smul_smul]
  congr 1
  have h2 := (Real.two_sub_two_mul_cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))).symm
  rw [show (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1) / 2
      = (((k : ℕ) : ℝ) + 1) * π / (2 * ((n : ℝ) + 1)) by
    rw [div_div, mul_comm ((n : ℝ) + 1) 2]] at h2
  rw [h2]
  ring

/-- The extreme eigenvalues of the one-dimensional model matrix $A$ of §2.2.3 of
[saad2003iterative], as quadratic-form bounds. Let $h \neq 0$. Then $A$ is symmetric, and every
$x \in \mathbb{R}^n$ satisfies
$$\frac{4}{h^2} \sin^2\Big(\frac{\pi}{2(n + 1)}\Big) \|x\|^2 \le (Ax, x) \le \frac{4}{h^2}
  \cos^2\Big(\frac{\pi}{2(n + 1)}\Big) \|x\|^2.$$
The source does not state this.

For $n\ge 1$ both bounds are eigenvalues, at $k=1$ and $k=n$, so the interval is sharp.
The statement is `LinearMap.IsSymmetricBoundedBy` for
`Matrix.toEuclideanLin A`. -/
theorem laplacian1D_isSymmetricBoundedBy (n : ℕ) {h : ℝ} (hh : h ≠ 0) :
    (Matrix.toEuclideanLin (laplacian1D n h)).IsSymmetricBoundedBy
      (4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2)
      (4 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2) := by
  have hpos : (0 : ℝ) < (h ^ 2)⁻¹ :=
    inv_pos.2 (lt_of_le_of_ne (sq_nonneg h) (Ne.symm (pow_ne_zero 2 hh)))
  have hhalf : π / ((n : ℝ) + 1) / 2 = π / (2 * ((n : ℝ) + 1)) := by
    rw [div_div, mul_comm ((n : ℝ) + 1) 2]
  have hlo := Real.two_sub_two_mul_cos (π / ((n : ℝ) + 1))
  have hhi := Real.two_add_two_mul_cos (π / ((n : ℝ) + 1))
  rw [hhalf] at hlo hhi
  have key := isSymmetricBoundedBy_smul
    (Matrix.isSymmetricBoundedBy_symmTridiagonalToeplitz n (-1) 2) hpos
  have e1 : (h ^ 2)⁻¹ * (2 - 2 * |(-1 : ℝ)| * Real.cos (π / ((n : ℝ) + 1)))
      = 4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2 := by
    rw [abs_neg, abs_one, show (2 : ℝ) - 2 * 1 * Real.cos (π / ((n : ℝ) + 1))
      = 2 - 2 * Real.cos (π / ((n : ℝ) + 1)) by ring, hlo]
    ring
  have e2 : (h ^ 2)⁻¹ * (2 + 2 * |(-1 : ℝ)| * Real.cos (π / ((n : ℝ) + 1)))
      = 4 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2 := by
    rw [abs_neg, abs_one, show (2 : ℝ) + 2 * 1 * Real.cos (π / ((n : ℝ) + 1))
      = 2 + 2 * Real.cos (π / ((n : ℝ) + 1)) by ring, hhi]
    ring
  rw [e1, e2] at key
  exact key

/-- For $h \neq 0$ the one-dimensional model matrix of §2.2.3 of [saad2003iterative] is symmetric
positive definite. The source does not state this in Chapter 2, where it gives the spectrum only
for the block $B$ of (2.27), but Chapters 4, 6 and 10 use it.

The diagonal dominance of the matrix is not strict, so the proof uses the sharp bound
$\cos(\pi/(n + 1)) < 1$ of `Matrix.posDef_symmTridiagonalToeplitz_neg_one_two`. -/
theorem laplacian1D_posDef (n : ℕ) {h : ℝ} (hh : h ≠ 0) : (laplacian1D n h).PosDef :=
  (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two n).smul
    (inv_pos.2 (lt_of_le_of_ne (sq_nonneg h) (Ne.symm (pow_ne_zero 2 hh))))

/-- The ratio of the extreme eigenvalues of the one-dimensional model matrix of §2.2.3 of
[saad2003iterative]. For $h \neq 0$ the two bounds of
`SaadSparse.Chapter02.laplacian1D_isSymmetricBoundedBy` satisfy
$$\frac{4 \cos^2(\pi/(2(n + 1)))/h^2}{4 \sin^2(\pi/(2(n + 1)))/h^2} =
  \cot^2\Big(\frac{\pi}{2(n + 1)}\Big).$$
For $n\ge 1$ this ratio is the $2$-norm condition number of the matrix. It is independent of
the scaling step $h$. The theorem states the exact algebraic ratio of the bounds.

Since $h = 1/(n + 1)$ in the source, the ratio is asymptotically $4/(\pi^2 h^2)$. This is the
origin of every remark in the source that the condition number grows like $h^{-2}$. The
asymptotic is not formalized. -/
theorem laplacian1D_lambdaMax_div_lambdaMin (n : ℕ) {h : ℝ} (hh : h ≠ 0) :
    (4 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2)
        / (4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2)
      = (Real.cos (π / (2 * ((n : ℝ) + 1))) / Real.sin (π / (2 * ((n : ℝ) + 1)))) ^ 2 := by
  have hh2 : (h : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hh
  rw [div_pow]
  rcases eq_or_ne (Real.sin (π / (2 * ((n : ℝ) + 1)))) 0 with hs | hs
  · simp [hs]
  · field_simp

end OneDimensional

/-! ### §2.2.4 The convection–diffusion problem -/

section ConvectionDiffusion

/-- **Equation (2.20)** of [saad2003iterative], the exact solution of the convection–diffusion model
problem. For the Péclet number $R \in \mathbb{R}$ and $x \in \mathbb{R}$,
$$u(x) = \frac{1 - e^{Rx}}{1 - e^R}.$$
For $R=b/a\ne 0$ with $a\ne 0$, it solves $-a u'' + b u' = 0$ on $(0,1)$ with
$u(0)=0$ and $u(1)=1$.

**Reading.** The displayed quotient in the source requires $R\ne 0$. The totalized
definition gives $0$ at $R=0$. For $a\ne 0$ and $b=0$, the boundary value problem itself
has the solution $u(x)=x$. -/
noncomputable def convDiffExact (R x : ℝ) : ℝ := (1 - Real.exp (R * x)) / (1 - Real.exp R)

/-- The exact solution (2.20) of [saad2003iterative] has the derivative $-R e^{Rx}/(1 - e^R)$ at
every $x \in \mathbb{R}$. -/
theorem convDiffExact_hasDerivAt (R x : ℝ) :
    HasDerivAt (convDiffExact R) (-(R * Real.exp (R * x)) / (1 - Real.exp R)) x := by
  have hE : HasDerivAt (fun t : ℝ => Real.exp (R * t)) (Real.exp (R * x) * R) x := by
    simpa using ((hasDerivAt_id x).const_mul R).exp
  have h4 : HasDerivAt (fun t : ℝ => (1 - Real.exp (R * t)) / (1 - Real.exp R))
      (-(Real.exp (R * x) * R) / (1 - Real.exp R)) x := (hE.const_sub 1).div_const _
  rw [show -(R * Real.exp (R * x)) = -(Real.exp (R * x) * R) by ring]
  exact h4

/-- A function whose derivative vanishes on $[0, 1]$ is constant on $[0, 1]$. -/
private theorem eq_of_deriv_eq_zero {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hz : ∀ x ∈ Set.Icc (0 : ℝ) 1, f' x = 0) : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = f 0 := by
  refine constant_of_has_deriv_right_zero (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    fun x hx => ?_
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hd := hf x hx'
  rw [hz x hx'] at hd
  exact hd.hasDerivWithinAt

/-- If $R \neq 0$ and $u$ satisfies $u'' = R u'$ on $[0, 1]$ with $u(0) = 0$ and $u(1) = 1$, then
$u$ is the exact solution (2.20) on $[0, 1]$. -/
private theorem convDiffExact_unique {R : ℝ} (hR : R ≠ 0) {u u' u'' : ℝ → ℝ}
    (hu : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u' (u'' x) x)
    (heq : ∀ x ∈ Set.Icc (0 : ℝ) 1, u'' x = R * u' x) (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x = convDiffExact R x := by
  have hexp1 : Real.exp R ≠ 1 := fun he => hR ((Real.exp_eq_one_iff R).1 he)
  have hden : Real.exp R - 1 ≠ 0 := sub_ne_zero.2 hexp1
  -- `u' x exp(-R x)` is constant, so `u' x = u'(0) exp(R x)`.
  have hg : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      u' x * Real.exp (-(R * x)) = u' 0 * Real.exp (-(R * 0)) := by
    refine eq_of_deriv_eq_zero (f' := fun x => (u'' x - R * u' x) * Real.exp (-(R * x)))
      (fun x hx => ?_) fun x hx => by rw [heq x hx]; ring
    have hE : HasDerivAt (fun t : ℝ => Real.exp (-(R * t))) (Real.exp (-(R * x)) * -R) x := by
      simpa using (((hasDerivAt_id x).const_mul R).neg).exp
    have hp := (hu' x hx).mul hE
    rw [show u'' x * Real.exp (-(R * x)) + u' x * (Real.exp (-(R * x)) * -R)
      = (u'' x - R * u' x) * Real.exp (-(R * x)) by ring] at hp
    exact hp
  have hu'x : ∀ x ∈ Set.Icc (0 : ℝ) 1, u' x = u' 0 * Real.exp (R * x) := by
    intro x hx
    have hgx := hg x hx
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hgx
    have hmul : u' x * Real.exp (-(R * x)) * Real.exp (R * x) = u' 0 * Real.exp (R * x) := by
      rw [hgx]
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
  -- Integrating once more, `u x = u'(0) (exp(R x) - 1)/R`.
  have hk : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      u x - u' 0 * (Real.exp (R * x) - 1) / R = u 0 - u' 0 * (Real.exp (R * 0) - 1) / R := by
    refine eq_of_deriv_eq_zero (f' := fun x => u' x - u' 0 * Real.exp (R * x)) (fun x hx => ?_)
      fun x hx => by rw [hu'x x hx]; ring
    have hE : HasDerivAt (fun t : ℝ => Real.exp (R * t)) (Real.exp (R * x) * R) x := by
      simpa using ((hasDerivAt_id x).const_mul R).exp
    have h2 : HasDerivAt (fun t : ℝ => u' 0 * (Real.exp (R * t) - 1) / R)
        (u' 0 * Real.exp (R * x)) x := by
      have hq := ((hE.sub_const 1).const_mul (u' 0)).div_const R
      rw [show u' 0 * (Real.exp (R * x) * R) / R = u' 0 * Real.exp (R * x) by
        field_simp] at hq
      exact hq
    exact (hu x hx).sub h2
  have hux : ∀ y ∈ Set.Icc (0 : ℝ) 1, u y = u' 0 * (Real.exp (R * y) - 1) / R := by
    intro y hy
    have hky := hk y hy
    rw [h0] at hky
    norm_num at hky
    linarith
  have hval := hux 1 (by norm_num)
  rw [h1, mul_one] at hval
  have hu0 : u' 0 = R / (Real.exp R - 1) := by
    field_simp at hval ⊢
    linarith
  have hR2 : (1 : ℝ) - Real.exp R ≠ 0 := sub_ne_zero.2 (Ne.symm hexp1)
  intro x hx
  rw [hux x hx, hu0, convDiffExact]
  field_simp
  ring

/-- **Equation (2.20)** of [saad2003iterative]: the exact solution is the only solution of the
two-point boundary value problem. Let $a, b \in \mathbb{R}$ with $a \neq 0$ and $b/a \neq 0$,
and let $u, u', u'' : \mathbb{R} \to \mathbb{R}$ be such that $u$ has the derivative $u'$ and
$u'$ has the derivative $u''$ at every point of $[0, 1]$. If
$$-a u''(x) + b u'(x) = 0 \quad (x \in [0, 1]), \qquad u(0) = 0, \qquad u(1) = 1,$$
then $u(x) = (1 - e^{Rx})/(1 - e^R)$ for every $x \in [0, 1]$, where $R = b/a$.

**Reading.** The source states the differential equation on $(0,1)$ and presents the
exponential formula as a solution. The theorem assumes the derivative and equation
hypotheses on $[0,1]$, makes the nonzero denominators explicit and states that any
solution equals the formula there. -/
theorem equation_2_20 {a b : ℝ} (ha : a ≠ 0) (hR : b / a ≠ 0) {u u' u'' : ℝ → ℝ}
    (hu : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u' (u'' x) x)
    (heq : ∀ x ∈ Set.Icc (0 : ℝ) 1, -a * u'' x + b * u' x = 0)
    (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x = convDiffExact (b / a) x :=
  convDiffExact_unique hR hu hu'
    (fun x hx => by
      have hx' := heq x hx
      field_simp
      linarith) h0 h1

/-- For $t > 0$, $e^t > 1$. -/
private theorem one_lt_exp_of_pos {t : ℝ} (ht : 0 < t) : 1 < Real.exp t := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.2 ht

/-- **Section 2.2.4** of [saad2003iterative]: for a positive Péclet number the exact solution is
positive. Let $R > 0$ and $x > 0$. Then $(1 - e^{Rx})/(1 - e^R) > 0$.

**Generalization.** The source states positivity on the interior of the unit interval.
The expression is positive at every $x>0$ when $R>0$. -/
theorem convDiffExact_pos {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : 0 < x) : 0 < convDiffExact R x := by
  have h1 := one_lt_exp_of_pos (mul_pos hR hx)
  have h2 := one_lt_exp_of_pos hR
  rw [convDiffExact, show (1 - Real.exp (R * x)) / (1 - Real.exp R)
      = (Real.exp (R * x) - 1) / (Real.exp R - 1) by
    rw [← neg_sub (Real.exp (R * x)) 1, ← neg_sub (Real.exp R) 1, neg_div_neg_eq]]
  exact div_pos (by linarith) (by linarith)

/-- **Section 2.2.4** of [saad2003iterative]: for a positive Péclet number $R > 0$ the exact
solution $x \mapsto (1 - e^{Rx})/(1 - e^R)$ is strictly increasing on $\mathbb{R}$.

**Generalization.** The source describes monotonicity on $[0,1]$. The formula is
strictly increasing on the whole real line. -/
theorem convDiffExact_strictMono {R : ℝ} (hR : 0 < R) : StrictMono (convDiffExact R) := by
  intro x y hxy
  have h2 := one_lt_exp_of_pos hR
  have hexp : Real.exp (R * x) < Real.exp (R * y) :=
    Real.exp_lt_exp.2 (by nlinarith)
  have hd : 1 - Real.exp R < 0 := by linarith
  rw [convDiffExact, convDiffExact, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_neg_right (by linarith) (inv_lt_zero.2 hd)

/-- **Equation (2.21)** of [saad2003iterative]: for $c \in \mathbb{R}$, the number
$$\sigma = \frac{1 + c}{1 - c}.$$
For $c \neq 1$ the characteristic equation $(1 - c) r^2 - 2r + (1 + c) = 0$ of the centered
difference scheme has the two roots $1$ and $\sigma$. In the scheme $c = Rh/2$.

**Reading.** The source's ratio requires $c\ne1$. The totalized definition gives $0$
at $c=1$, where the characteristic equation is linear. -/
noncomputable def convDiffRatio (c : ℝ) : ℝ := (1 + c) / (1 - c)

/-- **Equation (2.21)** of [saad2003iterative], the solution of the centered difference scheme: for
$c \in \mathbb{R}$ and $n, i \in \mathbb{N}$,
$$u_i = \frac{1 - \sigma^i}{1 - \sigma^{n+1}}, \qquad \sigma = \frac{1 + c}{1 - c}.$$

**Reading.** The source gives the quotient on the finite grid in the case of distinct
characteristic roots. This definition accepts all $i$, gives $0$ at $c=0$, and uses
the totalized ratio at $c=1$. The solution theorem treats $c\notin\{0,1\}$. -/
noncomputable def convDiffDiscrete (c : ℝ) (n i : ℕ) : ℝ :=
  (1 - convDiffRatio c ^ i) / (1 - convDiffRatio c ^ (n + 1))

/-- For $c \neq 1$, the number $\sigma = (1 + c)/(1 - c)$ is a root of
$(1 - c) r^2 - 2r + (1 + c) = 0$. -/
private theorem convDiffRatio_char {c : ℝ} (hc1 : c ≠ 1) :
    (1 - c) * convDiffRatio c ^ 2 - 2 * convDiffRatio c + (1 + c) = 0 := by
  have hcne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  rw [convDiffRatio]
  field_simp
  ring

private theorem convDiffRatio_ne_one {c : ℝ} (hc1 : c ≠ 1) (hc0 : c ≠ 0) :
    convDiffRatio c ≠ 1 := by
  have hcne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  intro h
  rw [convDiffRatio, div_eq_iff hcne] at h
  exact hc0 (by linarith)

private theorem convDiffRatio_ne_neg_one {c : ℝ} (hc1 : c ≠ 1) : convDiffRatio c ≠ -1 := by
  have hcne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  intro h
  rw [convDiffRatio, div_eq_iff hcne] at h
  linarith

/-- For $c \neq 0$ and $c \neq 1$, $\sigma^{n+1} \neq 1$, because $\sigma \neq 1$ and
$\sigma \neq -1$; so the denominator of (2.21) does not vanish. -/
private theorem convDiffRatio_pow_ne_one {c : ℝ} (hc1 : c ≠ 1) (hc0 : c ≠ 0) (n : ℕ) :
    convDiffRatio c ^ (n + 1) ≠ 1 := by
  intro h
  have habs : |convDiffRatio c| ^ (n + 1) = 1 := by rw [← abs_pow, h, abs_one]
  have h1 := (pow_eq_one_iff_of_nonneg (abs_nonneg _) (Nat.succ_ne_zero n)).1 habs
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h1 with h' | h'
  · exact convDiffRatio_ne_one hc1 hc0 h'
  · exact convDiffRatio_ne_neg_one hc1 h'

/-- **Equation (2.21)** of [saad2003iterative]: every solution of the centered difference
scheme agrees with the closed form on the grid. Let $n \in \mathbb{N}$ and $c \in \mathbb{R}$
with $c \neq 1$ and $c \neq 0$, and let
$(u_i)_{i \in \mathbb{N}}$ satisfy
$$-(1 - c) u_{i+1} + 2u_i - (1 + c) u_{i-1} = 0 \quad (1 \le i \le n), \qquad u_0 = 0, \qquad
  u_{n+1} = 1.$$
Then for $0 \le i \le n + 1$
$$u_i = \frac{1 - \sigma^i}{1 - \sigma^{n+1}}, \qquad \sigma = \frac{1 + c}{1 - c}.$$

**Reading.** The source gives the closed-form solution via the two characteristic roots.
The statement spells out $c\ne 1$ and $c\ne 0$ for this derivation and proves the uniqueness
direction on the grid. -/
theorem equation_2_21 {n : ℕ} {c : ℝ} (hc1 : c ≠ 1) (hc0 : c ≠ 0) {u : ℕ → ℝ}
    (hrec : ∀ i, 1 ≤ i → i ≤ n → -(1 - c) * u (i + 1) + 2 * u i - (1 + c) * u (i - 1) = 0)
    (h0 : u 0 = 0) (h1 : u (n + 1) = 1) :
    ∀ i ≤ n + 1, u i = convDiffDiscrete c n i := by
  have hcne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  have hσne : (1 : ℝ) - convDiffRatio c ≠ 0 :=
    sub_ne_zero.2 (Ne.symm (convDiffRatio_ne_one hc1 hc0))
  have hpow : (1 : ℝ) - convDiffRatio c ^ (n + 1) ≠ 0 :=
    sub_ne_zero.2 (Ne.symm (convDiffRatio_pow_ne_one hc1 hc0 n))
  -- The particular solution `(1 - σ^i)/(1 - σ)` satisfies the recurrence.
  have hnum : ∀ i : ℕ, -(1 - c) * (1 - convDiffRatio c ^ (i + 2))
      + 2 * (1 - convDiffRatio c ^ (i + 1)) - (1 + c) * (1 - convDiffRatio c ^ i) = 0 := by
    intro i
    have hexp : -(1 - c) * (1 - convDiffRatio c ^ (i + 2))
        + 2 * (1 - convDiffRatio c ^ (i + 1)) - (1 + c) * (1 - convDiffRatio c ^ i)
        = convDiffRatio c ^ i
          * ((1 - c) * convDiffRatio c ^ 2 - 2 * convDiffRatio c + (1 + c)) := by ring
    rw [hexp, convDiffRatio_char hc1, mul_zero]
  -- Shooting from `u 0 = 0`: every value is `u 1` times the particular solution.
  have key : ∀ i, i ≤ n →
      u i = u 1 * ((1 - convDiffRatio c ^ i) / (1 - convDiffRatio c)) ∧
        u (i + 1) = u 1 * ((1 - convDiffRatio c ^ (i + 1)) / (1 - convDiffRatio c)) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨by rw [h0]; norm_num, ?_⟩
      rw [pow_one]
      field_simp
    | succ i ih =>
      intro hi
      obtain ⟨hA, hB⟩ := ih (by omega)
      refine ⟨hB, ?_⟩
      have hr := hrec (i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hr
      have hT : -(1 - c) * ((1 - convDiffRatio c ^ (i + 2)) / (1 - convDiffRatio c))
          + 2 * ((1 - convDiffRatio c ^ (i + 1)) / (1 - convDiffRatio c))
          - (1 + c) * ((1 - convDiffRatio c ^ i) / (1 - convDiffRatio c)) = 0 := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination (1 - convDiffRatio c)⁻¹ * hnum i
      rw [hA, hB] at hr
      refine mul_left_cancel₀ hcne ?_
      show (1 - c) * u (i + 1 + 1)
        = (1 - c) * (u 1 * ((1 - convDiffRatio c ^ (i + 1 + 1)) / (1 - convDiffRatio c)))
      linear_combination (-1 : ℝ) * hr + u 1 * hT
  have hcand : ∀ i, i ≤ n + 1 →
      u i = u 1 * ((1 - convDiffRatio c ^ i) / (1 - convDiffRatio c)) := by
    intro i hi
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (key i (by omega)).1
    · have hin : i = n + 1 := by omega
      subst hin
      exact (key n le_rfl).2
  intro i hi
  have hval := hcand (n + 1) le_rfl
  rw [h1] at hval
  have hu1 : u 1 = (1 - convDiffRatio c) / (1 - convDiffRatio c ^ (n + 1)) := by
    field_simp at hval ⊢
    linarith
  rw [hcand i hi, hu1, convDiffDiscrete]
  field_simp

/-- **Section 2.2.4** of [saad2003iterative], the oscillation criterion. Let $c > 1$, that is
$h > 2/R$ for $c = Rh/2$. Then $\sigma < 0$, and the discrete solution (2.21) alternates in
sign: for every $n$ and every $i \ge 1$,
$$u_i u_{i+1} < 0.$$
The exact solution of (2.20) is positive and increasing
(`SaadSparse.Chapter02.convDiffExact_pos`, `SaadSparse.Chapter02.convDiffExact_strictMono`).

**Generalization.** The source discusses the computed values on the grid. The extension
of the closed form to all natural indices also alternates in sign for $i\ge 1$. -/
theorem equation_2_21_oscillates {n : ℕ} {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 1 ≤ i) :
    convDiffDiscrete c n i * convDiffDiscrete c n (i + 1) < 0 := by
  have hc1 : c ≠ 1 := ne_of_gt hc
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; linarith
  have hcneg : (1 : ℝ) - c < 0 := by linarith
  have hσ : convDiffRatio c < -1 := by
    rw [convDiffRatio, div_lt_iff_of_neg hcneg]
    linarith
  have habs : 1 < |convDiffRatio c| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hev : ∀ k : ℕ, Even k → k ≠ 0 → 1 < convDiffRatio c ^ k := by
    intro k hk hk0
    rw [← hk.pow_abs]
    exact one_lt_pow₀ habs hk0
  have hod : ∀ k : ℕ, Odd k → convDiffRatio c ^ k < 0 := fun k hk =>
    hk.pow_neg_iff.2 (by linarith)
  have hne : (1 : ℝ) - convDiffRatio c ^ (n + 1) ≠ 0 :=
    sub_ne_zero.2 (Ne.symm (convDiffRatio_pow_ne_one hc1 hc0 n))
  have hden : (0 : ℝ) < (1 - convDiffRatio c ^ (n + 1)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  rw [convDiffDiscrete, convDiffDiscrete, div_mul_div_comm, ← pow_two]
  refine div_neg_of_neg_of_pos ?_ hden
  rcases Nat.even_or_odd i with he | ho
  · have hb1 : 1 < convDiffRatio c ^ i := hev i he (by omega)
    have hb2 : convDiffRatio c ^ (i + 1) < 0 := hod _ he.add_one
    nlinarith
  · have hb1 : convDiffRatio c ^ i < 0 := hod i ho
    have hb2 : 1 < convDiffRatio c ^ (i + 1) := hev _ ho.add_one (by omega)
    nlinarith

/-- **Section 2.2.4** of [saad2003iterative]: let $0 < c < 1$, that is $h < 2/R$ for $c = Rh/2$.
Then $\sigma > 1$, and the discrete solution (2.21) is strictly increasing along the grid, as
the exact solution is: $u_i < u_{i+1}$ for every $n$ and every $i \in \mathbb{N}$.

**Generalization.** The source compares the discrete and continuous solutions on the
grid. The theorem proves the strict inequality for the closed form at every natural
index under $0<c<1$. -/
theorem equation_2_21_strictMono {n : ℕ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (i : ℕ) :
    convDiffDiscrete c n i < convDiffDiscrete c n (i + 1) := by
  have hcpos : (0 : ℝ) < 1 - c := by linarith
  have hσ : 1 < convDiffRatio c := by
    rw [convDiffRatio, lt_div_iff₀ hcpos]
    linarith
  have hpos : (0 : ℝ) < convDiffRatio c ^ i := pow_pos (by linarith) i
  have hmono : convDiffRatio c ^ i < convDiffRatio c ^ (i + 1) := by
    rw [pow_succ]
    nlinarith
  have hdenneg : (1 : ℝ) - convDiffRatio c ^ (n + 1) < 0 := by
    have hgt : 1 < convDiffRatio c ^ (n + 1) := one_lt_pow₀ hσ (Nat.succ_ne_zero n)
    linarith
  rw [convDiffDiscrete, convDiffDiscrete, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_neg_right (by linarith) (inv_lt_zero.2 hdenneg)

/-- **Section 2.2.4** of [saad2003iterative], the matrix of the centered difference scheme. For
$n \in \mathbb{N}$ and $h, c \in \mathbb{R}$ it is the tridiagonal matrix
$$\frac{1}{h^2} \operatorname{tridiag}(-1 - c, 2, -1 + c) \in \mathbb{R}^{n \times n},$$
with diagonal $2$, subdiagonal $-1 - c$ and superdiagonal $-1 + c$, all scaled by $1/h^2$.

**Generalization.** The source displays the six-point matrix with $c=Rh/2$ and a
positive mesh size. The definition allows all sizes and independent real $h,c$,
with value $0$ at $h=0$. -/
noncomputable def convDiffCentered (n : ℕ) (h c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (h ^ 2)⁻¹ • Matrix.of fun i j : Fin n =>
    if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j then -1 + c
      else if (j : ℕ) + 1 = i then -1 - c else 0

/-- **Section 2.2.4** of [saad2003iterative], the matrix of the upwind difference scheme for
$b > 0$. For $n \in \mathbb{N}$ and $h, c \in \mathbb{R}$ it is the tridiagonal matrix
$$\frac{1}{h^2} \operatorname{tridiag}(-1 - c, 2 + c, -1) \in \mathbb{R}^{n \times n},$$
with diagonal $2 + c$, subdiagonal $-1 - c$ and superdiagonal $-1$, all scaled by $1/h^2$.

**Generalization.** The source displays the six-point backward stencil with $c=Rh$
for $b>0$. The definition extends that formula to all sizes and real parameters,
with value $0$ at $h=0$. For $b<0$ the upwind scheme in the source uses a forward stencil. -/
noncomputable def convDiffUpwind (n : ℕ) (h c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (h ^ 2)⁻¹ • Matrix.of fun i j : Fin n =>
    if (i : ℕ) = j then 2 + c else if (i : ℕ) + 1 = j then -1
      else if (j : ℕ) + 1 = i then -1 - c else 0

/-- The entries of the centered matrix: $1/h^2$ times $2$ on the diagonal, $-1 + c$ on the
superdiagonal, $-1 - c$ on the subdiagonal, and $0$ elsewhere.

**Generalization.** The six-point centered display gives the same entries when
$c=Rh/2$. The formula holds for the extended matrix at all sizes and free parameters. -/
theorem convDiffCentered_apply (n : ℕ) (h c : ℝ) (i j : Fin n) :
    convDiffCentered n h c i j =
      (h ^ 2)⁻¹ * (if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j then -1 + c
        else if (j : ℕ) + 1 = i then -1 - c else 0) := rfl

/-- The entries of the upwind matrix: $1/h^2$ times $2 + c$ on the diagonal, $-1$ on the
superdiagonal, $-1 - c$ on the subdiagonal, and $0$ elsewhere.

**Generalization.** The six-point backward upwind display gives the same entries when
$c=Rh$ and $b>0$. The formula holds for the extended matrix at all sizes and free parameters. -/
theorem convDiffUpwind_apply (n : ℕ) (h c : ℝ) (i j : Fin n) :
    convDiffUpwind n h c i j =
      (h ^ 2)⁻¹ * (if (i : ℕ) = j then 2 + c else if (i : ℕ) + 1 = j then -1
        else if (j : ℕ) + 1 = i then -1 - c else 0) := rfl

/-- For $h \neq 0$, $1/h^2 > 0$. -/
private theorem inv_sq_pos {h : ℝ} (hh : h ≠ 0) : (0 : ℝ) < (h ^ 2)⁻¹ :=
  inv_pos.2 (lt_of_le_of_ne (sq_nonneg h) (Ne.symm (pow_ne_zero 2 hh)))

/-- **Section 2.2.4** of [saad2003iterative]: for $c > 1$ the centered matrix is not an M-matrix.
Let $n \ge 2$, $h \neq 0$ and $c > 1$. Then the matrix $\frac{1}{h^2}
\operatorname{tridiag}(-1 - c, 2, -1 + c)$ is not an M-matrix, because its superdiagonal entry
$(-1 + c)/h^2$ is positive, so that it is not even a Z-matrix.

**Generalization.** The source discusses the six-point matrix. A positive
superdiagonal gives the conclusion already for $n\ge 2$ and any $h\ne 0$. -/
theorem convDiffCentered_not_isMMatrix {n : ℕ} (hn : 2 ≤ n) {h c : ℝ} (hh : h ≠ 0) (hc : 1 < c) :
    ¬ (convDiffCentered n h c).IsMMatrix := by
  intro hM
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have hle := hM.offDiag_nonpos ⟨0, h0⟩ ⟨1, h1⟩ (by simp [Fin.ext_iff])
  have hval : convDiffCentered n h c ⟨0, h0⟩ ⟨1, h1⟩ = (h ^ 2)⁻¹ * (-1 + c) := by
    rw [convDiffCentered_apply]
    norm_num
  rw [hval] at hle
  nlinarith [inv_sq_pos hh]

/-- **Section 2.2.4** of [saad2003iterative]: for $c > 1$ the centered matrix is not weakly
diagonally dominant by rows. Let $n \ge 3$, $h \neq 0$ and $c > 1$. Then it is false that
$\sum_{j \neq i} |a_{ij}| \le |a_{ii}|$ for every row $i$, because an interior row has
$|-1 - c| + |-1 + c| = 2c > 2$, before the scaling by $1/h^2$.

**Generalization.** The source discusses the six-point centered matrix. An interior
row gives failure of weak diagonal dominance for every $n\ge 3$ and $h\ne 0$. -/
theorem convDiffCentered_not_diagDominant {n : ℕ} (hn : 3 ≤ n) {h c : ℝ} (hh : h ≠ 0)
    (hc : 1 < c) :
    ¬ ∀ i : Fin n, ∑ j ∈ univ.erase i, |convDiffCentered n h c i j|
        ≤ |convDiffCentered n h c i i| := by
  intro hd
  have hpos := inv_sq_pos (h := h) hh
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have h2 : (2 : ℕ) < n := by omega
  have hsub : ({⟨0, h0⟩, ⟨2, h2⟩} : Finset (Fin n)) ⊆ univ.erase ⟨1, h1⟩ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_erase, Fin.ext_iff]
  have hle := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ => abs_nonneg _)).trans (hd ⟨1, h1⟩)
  rw [Finset.sum_pair (by simp [Fin.ext_iff])] at hle
  have e0 : convDiffCentered n h c ⟨1, h1⟩ ⟨0, h0⟩ = (h ^ 2)⁻¹ * (-1 - c) := by
    rw [convDiffCentered_apply]; norm_num
  have e2 : convDiffCentered n h c ⟨1, h1⟩ ⟨2, h2⟩ = (h ^ 2)⁻¹ * (-1 + c) := by
    rw [convDiffCentered_apply]; norm_num
  have ed : convDiffCentered n h c ⟨1, h1⟩ ⟨1, h1⟩ = (h ^ 2)⁻¹ * 2 := by
    rw [convDiffCentered_apply]; norm_num
  rw [e0, e2, ed, abs_of_nonpos (by nlinarith), abs_of_nonneg (by nlinarith),
    abs_of_nonneg (by nlinarith)] at hle
  nlinarith

/-- If row $i$ of $A$ has $a_{ii} \ge 0$, $a_{ij} \le 0$ for $j \neq i$ and $\sum_j a_{ij} \ge 0$,
then $\sum_{j \neq i} |a_{ij}| \le |a_{ii}|$. -/
private theorem diagDominant_of_rowSum_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {i : Fin n}
    (hd : 0 ≤ A i i) (hoff : ∀ j, j ≠ i → A i j ≤ 0) (hrow : 0 ≤ ∑ j, A i j) :
    ∑ j ∈ univ.erase i, |A i j| ≤ |A i i| := by
  have h1 : ∑ j ∈ univ.erase i, |A i j| = -∑ j ∈ univ.erase i, A i j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => abs_of_nonpos (hoff j (Finset.mem_erase.1 hj).1)
  have h2 : ∑ j ∈ univ.erase i, A i j = (∑ j, A i j) - A i i :=
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  rw [h1, h2, abs_of_nonneg hd]
  linarith

/-- The Dirichlet extension of the constant vector $1$ takes its values in $[0, 1]$: it is $1$ at an
interior index and $0$ elsewhere. -/
private theorem dirichletExt_one_mem_Icc {n : ℕ} (k : ℕ) :
    0 ≤ dirichletExt (fun _ : Fin n => (1 : ℝ)) k ∧
      dirichletExt (fun _ : Fin n => (1 : ℝ)) k ≤ 1 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [dirichletExt_succ]
    split_ifs <;> norm_num

/-- The row sums of a tridiagonal matrix with constant subdiagonal $s$, diagonal $d$ and
superdiagonal $t$: row $i$ sums to $s \varepsilon_i + d + t \varepsilon_{i+2}$, where
$\varepsilon$ is the Dirichlet extension of the constant vector $1$, so that the first and the
last row each lose one neighbour. -/
private theorem tridiag_row_sum {n : ℕ} (sub diag sup : ℝ) (i : Fin n) :
    ∑ j : Fin n, (if (i : ℕ) = j then diag else if (i : ℕ) + 1 = j then sup
        else if (j : ℕ) + 1 = i then sub else 0)
      = sub * dirichletExt (fun _ : Fin n => (1 : ℝ)) (i : ℕ) + diag
        + sup * dirichletExt (fun _ : Fin n => (1 : ℝ)) ((i : ℕ) + 2) := by
  have hsplit : ∀ j : Fin n, (if (i : ℕ) = j then diag else if (i : ℕ) + 1 = j then sup
        else if (j : ℕ) + 1 = i then sub else 0)
      = (if (j : ℕ) + 1 = (i : ℕ) then sub * (1 : ℝ) else 0)
        + (if (j : ℕ) = (i : ℕ) then diag * (1 : ℝ) else 0)
        + (if (j : ℕ) = (i : ℕ) + 1 then sup * (1 : ℝ) else 0) := by
    intro j
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [dirichletExt]
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Matrix.sum_ite_val_add_one_eq_mul_padZero, Matrix.sum_ite_val_eq_mul_padZero,
    Matrix.sum_ite_val_eq_mul_padZero, Matrix.padZero_val_succ, mul_one]

/-- **Section 2.2.4** of [saad2003iterative]: the upwind matrix has the sign structure that the
theorems of Chapter 4 need. Let $h \neq 0$ and $c \ge 0$. Then the matrix $A = \frac{1}{h^2}
\operatorname{tridiag}(-1 - c, 2 + c, -1)$ has a positive diagonal, nonpositive off-diagonal
entries, and is weakly diagonally dominant by rows:
$$a_{ii} > 0, \qquad a_{ij} \le 0 \quad (i \neq j), \qquad \sum_{j \neq i} |a_{ij}| \le |a_{ii}|
  \quad \text{for every row } i.$$

**Generalization.** The source uses the six-point backward stencil for positive
convection. The same signs and dominance hold for all sizes, $c\ge 0$ and $h\ne 0$.
-/
theorem convDiffUpwind_diagDominant {n : ℕ} {h c : ℝ} (hh : h ≠ 0) (hc : 0 ≤ c) :
    (∀ i : Fin n, 0 < convDiffUpwind n h c i i) ∧
      (∀ i j : Fin n, i ≠ j → convDiffUpwind n h c i j ≤ 0) ∧
      (∀ i : Fin n, ∑ j ∈ univ.erase i, |convDiffUpwind n h c i j|
        ≤ |convDiffUpwind n h c i i|) := by
  have hpos := inv_sq_pos (h := h) hh
  have hdiag : ∀ i : Fin n, convDiffUpwind n h c i i = (h ^ 2)⁻¹ * (2 + c) := fun i => by
    rw [convDiffUpwind_apply, ite_eq_left rfl]
  have hoff : ∀ i j : Fin n, i ≠ j → convDiffUpwind n h c i j ≤ 0 := by
    intro i j hij
    rw [convDiffUpwind_apply, ite_eq_right fun hE => hij (Fin.ext hE)]
    split_ifs <;> nlinarith
  refine ⟨fun i => ?_, hoff, fun i => ?_⟩
  · rw [hdiag i]; nlinarith
  · refine diagDominant_of_rowSum_nonneg (by rw [hdiag i]; nlinarith)
      (fun j hj => hoff i j (Ne.symm hj)) ?_
    have hrow : ∑ j : Fin n, convDiffUpwind n h c i j
        = (h ^ 2)⁻¹ * ((-1 - c) * dirichletExt (fun _ : Fin n => (1 : ℝ)) (i : ℕ) + (2 + c)
            + (-1) * dirichletExt (fun _ : Fin n => (1 : ℝ)) ((i : ℕ) + 2)) := by
      rw [← tridiag_row_sum (-1 - c) (2 + c) (-1) i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => convDiffUpwind_apply n h c i j
    rw [hrow]
    obtain ⟨hl0, hu0⟩ := dirichletExt_one_mem_Icc (n := n) (i : ℕ)
    obtain ⟨hl2, hu2⟩ := dirichletExt_one_mem_Icc (n := n) ((i : ℕ) + 2)
    refine mul_nonneg hpos.le ?_
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 + c by linarith)
      (show (0 : ℝ) ≤ 1 - dirichletExt (fun _ : Fin n => (1 : ℝ)) (i : ℕ) by linarith)]

/-- **Equations (2.22)–(2.23)** of [saad2003iterative], the upwind approximation of $b(x) u'(x_i)$.
For all real numbers $b$, $u_{i-1}$, $u_i$, $u_{i+1}$ and $h$,
$$\frac{b^+ (u_i - u_{i-1}) + b^- (u_{i+1} - u_i)}{h} = \frac{-b^+ u_{i-1} + |b| u_i + b^-
  u_{i+1}}{h},$$
where $b^+ = \max(b, 0)$ and $b^- = \min(b, 0)$. The three coefficients satisfy $|b| \ge 0$,
$-b^+ \le 0$, $b^- \le 0$ and $-b^+ + |b| + b^- = 0$.

The left side takes the backward difference where $b > 0$ and the forward difference where
$b < 0$.

**Reading.** The source presents a discretization with positive spacing. This theorem
states the exact algebraic equality between its two stencil expressions, including
$h=0$ by totalized division. -/
theorem equation_2_23 (b uprev ucur unext h : ℝ) :
    (max b 0 * (ucur - uprev) + min b 0 * (unext - ucur)) / h
        = (-(max b 0) * uprev + |b| * ucur + min b 0 * unext) / h ∧
      0 ≤ |b| ∧ -(max b 0) ≤ 0 ∧ min b 0 ≤ 0 ∧ -(max b 0) + |b| + min b 0 = 0 := by
  refine ⟨?_, abs_nonneg b, neg_nonpos.2 (le_max_right b 0), min_le_right b 0, ?_⟩
  · rw [max_zero_eq_half, min_zero_eq_half]; ring
  · rw [max_zero_eq_half, min_zero_eq_half]; ring

end ConvectionDiffusion

/-! ### §2.2.5–2.2.6 The two-dimensional model problem -/

section TwoDimensional

variable {n₁ n₂ : ℕ}

/-- **Section 2.2.5** of [saad2003iterative], the two-dimensional five-point matrix. For
$n_1, n_2 \in \mathbb{N}$ and mesh sizes $h_1, h_2 \in \mathbb{R}$, it is the matrix of the
five-point discretization of $-\Delta u$ on an $n_1 \times n_2$ interior grid with homogeneous
Dirichlet boundary conditions, indexed by the pairs $(i, j)$. The diagonal entry is
$2/h_1^2 + 2/h_2^2$, a neighbour $(i \pm 1, j)$ in the $x$ direction contributes $-1/h_1^2$, a
neighbour $(i, j \pm 1)$ in the $y$ direction contributes $-1/h_2^2$, and all other entries are
$0$.

**Typo.** The source prints $0<i<n_1$ and $0<j<n_2$. The interior grid includes $i=n_1$
and $j=n_2$ because the endpoint indices are $0$ and $n_k+1$ in direction $k$.

**Reading.** The source chooses the spacings from the side lengths of the rectangle.
The parameters are free in Lean, with a zero contribution from a direction at step size zero.

The source displays the matrix without an equation number, and numbers the scaled copy
(2.26)–(2.27). The index type is `Fin n₁ × Fin n₂`, whose first coordinate is the $x$ direction.
The natural row-wise ordering of the source is a reindexing of this product. -/
noncomputable def laplacian2D (n₁ n₂ : ℕ) (h₁ h₂ : ℝ) :
    Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  Matrix.of fun p q =>
    if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 then 2 * (h₁ ^ 2)⁻¹ + 2 * (h₂ ^ 2)⁻¹
    else if (p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) then -(h₁ ^ 2)⁻¹
    else if (p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2) then -(h₂ ^ 2)⁻¹
    else 0

/-- The entries of the five-point matrix: $2/h_1^2 + 2/h_2^2$ on the diagonal, $-1/h_1^2$ between
neighbours in the first coordinate, $-1/h_2^2$ between neighbours in the second coordinate, and
$0$ elsewhere.

**Reading.** The definition includes the last interior row and column of the grid and accepts
all real spacings. At zero spacing one direction contributes zero by totalized division. -/
theorem laplacian2D_apply (n₁ n₂ : ℕ) (h₁ h₂ : ℝ) (p q : Fin n₁ × Fin n₂) :
    laplacian2D n₁ n₂ h₁ h₂ p q =
      if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 then 2 * (h₁ ^ 2)⁻¹ + 2 * (h₂ ^ 2)⁻¹
      else if (p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) then -(h₁ ^ 2)⁻¹
      else if (p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2) then -(h₂ ^ 2)⁻¹
      else 0 := rfl

/-- **Equation (2.27)** of [saad2003iterative]: the diagonal block
$$B = \operatorname{tridiag}(-1, 4, -1) \in \mathbb{R}^{p \times p}$$
of the block form (2.26) of the scaled five-point matrix. -/
noncomputable def blockB (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.symmTridiagonalToeplitz p (-1) 4

/-- **Equation (2.27)** of [saad2003iterative]: the eigenvalues of the block $B$,
$$\lambda_j = 4 - 2\cos\Big(\frac{j\pi}{p + 1}\Big), \qquad j = 1, \dots, p.$$

The Lean index `j : Fin p` stands for the book's $j + 1$. -/
noncomputable def blockEigenvalue (p : ℕ) (j : Fin p) : ℝ :=
  4 - 2 * Real.cos ((((j : ℕ) : ℝ) + 1) * π / ((p : ℝ) + 1))

/-- The five-point matrix of §2.2.5 of [saad2003iterative] is the Kronecker sum of two
one-dimensional model matrices, one for each coordinate direction:
$$A_{2D}(n_1, n_2, h_1, h_2) = A_{1D}(n_1, h_1) \otimes I + I \otimes A_{1D}(n_2, h_2),$$
where $A_{1D}$ is `SaadSparse.Chapter02.laplacian1D` and $A_{2D}$ is
`SaadSparse.Chapter02.laplacian2D`.

**Generalization.** Equation (13.12) gives the tensor sum for unscaled matrices and equal
spacings. The same identity holds for separate scales after reindexing the two directions. -/
theorem laplacian2D_eq_kroneckerSum (n₁ n₂ : ℕ) (h₁ h₂ : ℝ) :
    laplacian2D n₁ n₂ h₁ h₂ = laplacian1D n₁ h₁ ⊕ₖ laplacian1D n₂ h₂ := by
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  rw [Matrix.kroneckerSum_apply, laplacian1D_apply, laplacian1D_apply, laplacian2D_apply]
  simp only [← Fin.val_eq_val]
  split_ifs <;> first | (exfalso; omega) | ring

/-- The two conventions of §2.2.3 and §2.2.6 of [saad2003iterative]. Let $h \neq 0$. Scaling the
five-point matrix with $h_1 = h_2 = h$ by $h^2$ removes the mesh size:
$$h^2 A_{2D}(n_1, n_2, h, h) = T_{n_1} \otimes I + I \otimes T_{n_2}, \qquad T_m =
  \operatorname{tridiag}(-1, 2, -1) \in \mathbb{R}^{m \times m}.$$
**Reading.** The right side is the tensor sum of (13.12) in the scaling of (2.26).
This version orders indices as $(x_1,x_2)$. The source's horizontal-line blocks order
them as $(x_2,x_1)$. -/
theorem laplacian2D_smul (n₁ n₂ : ℕ) {h : ℝ} (hh : h ≠ 0) :
    h ^ 2 • laplacian2D n₁ n₂ h h
      = Matrix.symmTridiagonalToeplitz n₁ (-1) 2 ⊕ₖ Matrix.symmTridiagonalToeplitz n₂ (-1) 2 := by
  rw [laplacian2D_eq_kroneckerSum, ← Matrix.kroneckerSum_smul, laplacian1D, laplacian1D,
    smul_smul, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hh), one_smul, one_smul]

/-- **Equation (2.26)** of [saad2003iterative], the block form of the scaled five-point matrix. Let
$h \neq 0$, and take the blocks indexed by the first coordinate. Then the block $(i_1, j_1)$ of
$h^2 A_{2D}(n_1, n_2, h, h)$ is
$$\begin{cases} B = \operatorname{tridiag}(-1, 4, -1), & i_1 = j_1, \\ -I, & |i_1 - j_1| = 1, \\
  0, & \text{otherwise}, \end{cases}$$
where $B$ and $I$ are of order $n_2$.

The block $B$ is `SaadSparse.Chapter02.blockB`. The statement is entrywise.

**Reading.** The source fixes $x_2$ for each horizontal block and uses blocks of order $n_1$.
This version fixes $x_1$ and uses vertical blocks of order $n_2$. The formulas agree after
swapping the two coordinates. -/
theorem laplacian2D_block_apply (n₁ n₂ : ℕ) {h : ℝ} (hh : h ≠ 0) (i₁ j₁ : Fin n₁)
    (i₂ j₂ : Fin n₂) :
    (h ^ 2 • laplacian2D n₁ n₂ h h) (i₁, i₂) (j₁, j₂)
      = if (i₁ : ℕ) = j₁ then blockB n₂ i₂ j₂
        else if (i₁ : ℕ) + 1 = j₁ ∨ (j₁ : ℕ) + 1 = i₁ then -(1 : Matrix (Fin n₂) (Fin n₂) ℝ) i₂ j₂
        else 0 := by
  rw [laplacian2D_smul n₁ n₂ hh, Matrix.kroneckerSum_apply, blockB,
    Matrix.symmTridiagonalToeplitz_apply', Matrix.symmTridiagonalToeplitz_apply',
    Matrix.symmTridiagonalToeplitz_apply', Matrix.one_apply]
  simp only [← Fin.val_eq_val]
  split_ifs <;> ring

/-- The eigenpairs of the five-point matrix of §2.2.5 of [saad2003iterative]. Let
$h_1, h_2 \in \mathbb{R}$, $k \in \{1, \dots, n_1\}$ and $l \in \{1, \dots, n_2\}$, and let
$w_k$ and $w_l$ be the discrete sine vectors of
`SaadSparse.Chapter02.laplacian1D_mulVec_sineVec`. Then
$$A_{2D} (w_k \otimes w_l) = \Big( \frac{4}{h_1^2} \sin^2\frac{k\pi}{2(n_1 + 1)} +
  \frac{4}{h_2^2} \sin^2\frac{l\pi}{2(n_2 + 1)} \Big) w_k \otimes w_l.$$

**Generalization.** Equation (13.14) and the adjoining display give the eigenpairs for the
unscaled equal-step matrix. This version weights the two eigenvalues separately by $1/h_i^2$
and orders the tensor vector by the first coordinate followed by the second.

The tensor product $w_k \otimes w_l$ is `Matrix.kroneckerVec`, and the Lean indices `k : Fin n₁`
and `l : Fin n₂` stand for the book's $k + 1$ and $l + 1$. -/
theorem laplacian2D_mulVec_kroneckerVec (h₁ h₂ : ℝ) (k : Fin n₁) (l : Fin n₂) :
    laplacian2D n₁ n₂ h₁ h₂ *ᵥ Matrix.kroneckerVec (Matrix.sineVec n₁ k) (Matrix.sineVec n₂ l)
      = (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * π / (2 * ((n₁ : ℝ) + 1))) ^ 2 / h₁ ^ 2
          + 4 * Real.sin ((((l : ℕ) : ℝ) + 1) * π / (2 * ((n₂ : ℝ) + 1))) ^ 2 / h₂ ^ 2)
        • Matrix.kroneckerVec (Matrix.sineVec n₁ k) (Matrix.sineVec n₂ l) := by
  rw [laplacian2D_eq_kroneckerSum]
  exact Matrix.kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul
    (laplacian1D_mulVec_sineVec h₁ k) (laplacian1D_mulVec_sineVec h₂ l)

/-- For $h_1 \neq 0$ and $h_2 \neq 0$ the five-point matrix of §2.2.5 of [saad2003iterative] is
symmetric positive definite.

The proof uses that positive definiteness adds under a Kronecker sum,
`Matrix.posDef_kroneckerSum`. -/
theorem laplacian2D_posDef (n₁ n₂ : ℕ) {h₁ h₂ : ℝ} (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0) :
    (laplacian2D n₁ n₂ h₁ h₂).PosDef := by
  rw [laplacian2D_eq_kroneckerSum]
  exact Matrix.posDef_kroneckerSum (laplacian1D_posDef n₁ h₁0) (laplacian1D_posDef n₂ h₂0)

/-! ### §2.2.6 The fast Poisson solver -/

/-- **Equation (2.27)** of [saad2003iterative]: the matrix $Q = [q_1, \dots, q_p] \in \mathbb{R}^{p
\times p}$ whose $j$-th column is the normalized discrete sine vector
$$q_j = \sqrt{\frac{2}{p + 1}} \, w_j, \qquad (w_j)_i = \sin\Big(\frac{ij\pi}{p + 1}\Big), \quad
  i, j = 1, \dots, p.$$

The vector $w_j$ is `Matrix.sineVec p j`. -/
noncomputable def sineMatrix (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => Real.sqrt (2 / ((p : ℝ) + 1)) * Matrix.sineVec p j i

/-- The entries of $Q$: $Q_{ij} = \sqrt{2/(p + 1)} \, (w_j)_i$. -/
theorem sineMatrix_apply (p : ℕ) (i j : Fin p) :
    sineMatrix p i j = Real.sqrt (2 / ((p : ℝ) + 1)) * Matrix.sineVec p j i := rfl

/-- The $j$-th column of $Q$ is the vector $\sqrt{2/(p + 1)} \, w_j$. -/
private theorem sineMatrix_col (p : ℕ) (j : Fin p) :
    (fun i => sineMatrix p i j) = Real.sqrt (2 / ((p : ℝ) + 1)) • Matrix.sineVec p j := by
  funext i
  rw [sineMatrix_apply, Pi.smul_apply, smul_eq_mul]

/-- **Equation (2.27)** of [saad2003iterative]: the matrix $Q$ is orthogonal, $Q^T Q = I$. -/
theorem sineMatrix_transpose_mul_self (p : ℕ) : (sineMatrix p)ᵀ * sineMatrix p = 1 := by
  have hp : ((p : ℝ) + 1) ≠ 0 := by positivity
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ i : Fin p, (sineMatrix p)ᵀ j i * sineMatrix p i k
      = 2 / ((p : ℝ) + 1) * (Matrix.sineVec p j i * Matrix.sineVec p k i) := by
    intro i
    rw [Matrix.transpose_apply, sineMatrix_apply, sineMatrix_apply,
      show Real.sqrt (2 / ((p : ℝ) + 1)) * Matrix.sineVec p j i
          * (Real.sqrt (2 / ((p : ℝ) + 1)) * Matrix.sineVec p k i)
        = Real.sqrt (2 / ((p : ℝ) + 1)) * Real.sqrt (2 / ((p : ℝ) + 1))
          * (Matrix.sineVec p j i * Matrix.sineVec p k i) by ring,
      Real.mul_self_sqrt (by positivity)]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  have hdot : ∑ i : Fin p, Matrix.sineVec p j i * Matrix.sineVec p k i
      = if j = k then ((p : ℝ) + 1) / 2 else 0 := Matrix.dotProduct_sineVec j k
  rw [hdot]
  split_ifs
  · field_simp
  · ring

/-- **Equation (2.27)** of [saad2003iterative]: the discrete sine vectors are eigenvectors of the
block $B = \operatorname{tridiag}(-1, 4, -1)$. For $j = 1, \dots, p$,
$$B w_j = \lambda_j w_j, \qquad \lambda_j = 4 - 2\cos\Big(\frac{j\pi}{p + 1}\Big).$$
So the columns of $Q$ are eigenvectors of $B$. -/
theorem blockB_mulVec_sineVec (p : ℕ) (j : Fin p) :
    blockB p *ᵥ Matrix.sineVec p j = blockEigenvalue p j • Matrix.sineVec p j := by
  rw [blockB, Matrix.symmTridiagonalToeplitz_mulVec_sineVec, blockEigenvalue]
  congr 1
  ring

/-- **Equation (2.27)** of [saad2003iterative]: the orthogonal matrix $Q$ of the normalized discrete
sine vectors diagonalizes the block $B = \operatorname{tridiag}(-1, 4, -1)$,
$$Q^T B Q = \operatorname{diag}(\lambda_1, \dots, \lambda_p), \qquad \lambda_j = 4 -
  2\cos\Big(\frac{j\pi}{p + 1}\Big).$$
This is the only spectral statement of the section, and the source states it without proof. -/
theorem equation_2_27_spectrum (p : ℕ) :
    (sineMatrix p)ᵀ * blockB p * sineMatrix p = Matrix.diagonal (blockEigenvalue p) := by
  have hcol : blockB p * sineMatrix p = sineMatrix p * Matrix.diagonal (blockEigenvalue p) := by
    ext i j
    have h1 : (blockB p * sineMatrix p) i j
        = (blockB p *ᵥ fun k => sineMatrix p k j) i := rfl
    rw [h1, sineMatrix_col, Matrix.mulVec_smul, blockB_mulVec_sineVec, Matrix.mul_diagonal,
      sineMatrix_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [Matrix.mul_assoc, hcol, ← Matrix.mul_assoc, sineMatrix_transpose_mul_self, Matrix.one_mul]

/-- **Algorithm 2.1** of [saad2003iterative], line 1: the coefficients of a grid function $u$ on the
$m \times p$ grid in the sine basis of the second (within-block) index,
$$\bar u_i(j) = \sum_{k=1}^{p} Q_{ki} \, u(j, k), \qquad j = 1, \dots, m,$$
so that $\bar u_i \in \mathbb{R}^m$ for each $i = 1, \dots, p$. -/
noncomputable def sineCoeff {m p : ℕ} (u : Fin m × Fin p → ℝ) (i : Fin p) : Fin m → ℝ :=
  fun j => ∑ k, sineMatrix p k i * u (j, k)

/-- The coefficients in the sine basis are $\bar u_i(j) = \sum_k Q_{ki} \, u(j, k)$. -/
theorem sineCoeff_apply {m p : ℕ} (u : Fin m × Fin p → ℝ) (i : Fin p) (j : Fin m) :
    sineCoeff u i j = ∑ k, sineMatrix p k i * u (j, k) := rfl

/-- Shifting the diagonal of a symmetric tridiagonal Toeplitz matrix: $\operatorname{tridiag}(a, b +
c, a) = \operatorname{tridiag}(a, b, a) + cI$. -/
private theorem symmTridiagonalToeplitz_add_diag (m : ℕ) (a b c : ℝ) :
    Matrix.symmTridiagonalToeplitz m a (b + c)
      = Matrix.symmTridiagonalToeplitz m a b + c • 1 := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.symmTridiagonalToeplitz_apply', Matrix.symmTridiagonalToeplitz_apply']
  simp only [← Fin.val_eq_val]
  split_ifs <;> ring

/-- The $(j, k)$ entry of $(A \otimes I + I \otimes B) v$ is $\sum_{j'} a_{jj'} v(j', k) + \sum_{k'}
b_{kk'} v(j, k')$. -/
private theorem kroneckerSum_mulVec_apply {m p : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin p) (Fin p) ℝ) (v : Fin m × Fin p → ℝ) (j : Fin m) (k : Fin p) :
    ((A ⊕ₖ B) *ᵥ v) (j, k) = (∑ j', A j j' * v (j', k)) + ∑ k', B k k' * v (j, k') := by
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_prod_type]
  have hterm : ∀ (j' : Fin m) (k' : Fin p), (A ⊕ₖ B) (j, k) (j', k') * v (j', k')
      = (if k = k' then A j j' * v (j', k') else 0)
        + if j = j' then B k k' * v (j', k') else 0 := by
    intro j' k'
    rw [Matrix.kroneckerSum_apply]
    split_ifs <;> ring
  simp only [hterm]
  rw [Finset.sum_congr rfl fun j' _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.sum_ite_eq Finset.univ k fun k' => A j j' * v (j', k')]
    simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.sum_ite_eq Finset.univ j fun j' => B k k' * v (j', k')]
    simp

/-- **Equations (2.28)–(2.29)** and **Algorithm 2.1** of [saad2003iterative], the fast Poisson
solver. Let $u$ and $b$ be grid functions on the $m \times p$ grid that satisfy
$$(T_m \otimes I + I \otimes T_p) u = b, \qquad T_k = \operatorname{tridiag}(-1, 2, -1) \in
  \mathbb{R}^{k \times k}.$$
Then for each $i = 1, \dots, p$ the sine coefficients $\bar u_i, \bar b_i \in \mathbb{R}^m$
satisfy the tridiagonal system of size $m$
$$\operatorname{tridiag}(-1, \lambda_i, -1) \, \bar u_i = \bar b_i, \qquad \lambda_i = 4 -
  2\cos\Big(\frac{i\pi}{p + 1}\Big).$$

**Typo.** The source prints the indices of (2.29) transposed, which gives systems of the wrong
size. The statement here gives $p$ systems of size $m$, as line 2 of Algorithm 2.1 says.

Conjugating the scaled five-point matrix by $Q$ in the within-block index replaces the block $B$
by $\operatorname{diag}(\lambda_1, \dots, \lambda_p)$, and the system decouples. The sine
coefficients are `SaadSparse.Chapter02.sineCoeff`. The fast Fourier transform that computes
$Q^T u$, and the operation count, are implementation, not statements. -/
theorem equation_2_29 {m p : ℕ} {u b : Fin m × Fin p → ℝ}
    (hub : (Matrix.symmTridiagonalToeplitz m (-1) 2 ⊕ₖ Matrix.symmTridiagonalToeplitz p (-1) 2)
      *ᵥ u = b) (i : Fin p) :
    Matrix.symmTridiagonalToeplitz m (-1) (blockEigenvalue p i) *ᵥ sineCoeff u i
      = sineCoeff b i := by
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, blockEigenvalue p i = 2 + μ := ⟨blockEigenvalue p i - 2, by ring⟩
  have hμ' : μ = 2 + 2 * (-1) * Real.cos ((((i : ℕ) : ℝ) + 1) * π / ((p : ℝ) + 1)) := by
    rw [blockEigenvalue] at hμ; linarith
  have hsymm : ∀ k k' : Fin p, Matrix.symmTridiagonalToeplitz p (-1) 2 k k'
      = Matrix.symmTridiagonalToeplitz p (-1) 2 k' k := by
    intro k k'
    rw [Matrix.symmTridiagonalToeplitz_apply', Matrix.symmTridiagonalToeplitz_apply']
    split_ifs <;> first | rfl | (exfalso; omega)
  -- The `i`-th column of `Q` is a left eigenvector of `T_p` for `μ = λ_i - 2`.
  have hcol : ∀ k' : Fin p,
      ∑ k : Fin p, sineMatrix p k i * Matrix.symmTridiagonalToeplitz p (-1) 2 k k'
        = μ * sineMatrix p k' i := by
    intro k'
    have h1 : ∑ k : Fin p, sineMatrix p k i * Matrix.symmTridiagonalToeplitz p (-1) 2 k k'
        = (Matrix.symmTridiagonalToeplitz p (-1) 2 *ᵥ fun k => sineMatrix p k i) k' := by
      rw [Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hsymm k k', mul_comm]
    rw [h1, sineMatrix_col, Matrix.mulVec_smul,
      Matrix.symmTridiagonalToeplitz_mulVec_sineVec, sineMatrix_apply, hμ']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hstep : ∀ (j : Fin m) (k : Fin p), sineMatrix p k i
        * ((Matrix.symmTridiagonalToeplitz m (-1) 2 ⊕ₖ Matrix.symmTridiagonalToeplitz p (-1) 2)
          *ᵥ u) (j, k)
      = (∑ j' : Fin m, sineMatrix p k i * (Matrix.symmTridiagonalToeplitz m (-1) 2 j j'
          * u (j', k)))
        + ∑ k' : Fin p, sineMatrix p k i * (Matrix.symmTridiagonalToeplitz p (-1) 2 k k'
          * u (j, k')) := by
    intro j k
    rw [kroneckerSum_mulVec_apply, mul_add, Finset.mul_sum, Finset.mul_sum]
  funext j
  have hrhs : sineCoeff b i j
      = (∑ j' : Fin m, Matrix.symmTridiagonalToeplitz m (-1) 2 j j' * sineCoeff u i j')
        + μ * sineCoeff u i j := by
    rw [← hub, sineCoeff_apply, Finset.sum_congr rfl fun k _ => hstep j k,
      Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [sineCoeff_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · rw [Finset.sum_comm, sineCoeff_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      have hin : ∑ k : Fin p, sineMatrix p k i
            * (Matrix.symmTridiagonalToeplitz p (-1) 2 k k' * u (j, k'))
          = (∑ k : Fin p, sineMatrix p k i * Matrix.symmTridiagonalToeplitz p (-1) 2 k k')
            * u (j, k') := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hin, hcol k']
      ring
  rw [hrhs, hμ, symmTridiagonalToeplitz_add_diag, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum]

/-! ### §2.2.7 Block cyclic reduction -/

/-- **Equation (2.33)** of [saad2003iterative], the block cyclic reduction sequence: for
$B \in \mathbb{R}^{p \times p}$,
$$B^{(0)} = B, \qquad B^{(r+1)} = (B^{(r)})^2 - 2I.$$

The numeral `2` in the Lean code is the matrix $2I$.

**Generalization.** The source starts with the Poisson block and obtains the recurrence
while eliminating rows. The definition iterates that recurrence for any square matrix. -/
noncomputable def cyclicReduction {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) : ℕ →
    Matrix (Fin p) (Fin p) ℝ
  | 0 => B
  | r + 1 => cyclicReduction B r ^ 2 - 2

/-- The duplication formula $C_{2k} = C_k^2 - 2$ of the Vieta–Lucas polynomials, for
$k \in \mathbb{Z}$. -/
private theorem chebyshevC_two_mul (k : ℤ) :
    Polynomial.Chebyshev.C ℝ (2 * k) = Polynomial.Chebyshev.C ℝ k ^ 2 - 2 := by
  have hC := Polynomial.Chebyshev.C_mul_C ℝ k k
  rw [sub_self, Polynomial.Chebyshev.C_zero, show k + k = 2 * k by ring] at hC
  linear_combination -hC

/-- **Equation (2.33)** of [saad2003iterative]: the block cyclic reduction sequence is a polynomial
in $B$. For $B \in \mathbb{R}^{p \times p}$ and $r \in \mathbb{N}$,
$$B^{(r)} = C_{2^r}(B),$$
where $C_m$ is the Vieta–Lucas polynomial, $C_m(2\cos\theta) = 2\cos(m\theta)$. Since
$C_m(x) = 2T_m(x/2)$ for the Chebyshev polynomial $T_m$, this gives $B^{(r)} = 2T_{2^r}(B/2)$.

The polynomial $C_m$ is `Polynomial.Chebyshev.C ℝ m`, evaluated at $B$ by `Polynomial.aeval B`.
The induction step is the duplication formula $C_{2k} = C_k^2 - 2$. The factorization of
$C_{2^r}$ into linear factors gives (2.36), `SaadSparse.Chapter02.equation_2_36`.

**Generalization.** The source identifies the polynomial for the block from (2.27).
The polynomial identity holds for any square real matrix. -/
theorem equation_2_33 {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (r : ℕ) :
    cyclicReduction B r = Polynomial.aeval B (Polynomial.Chebyshev.C ℝ ((2 : ℤ) ^ r)) := by
  induction r with
  | zero => simp [cyclicReduction, Polynomial.Chebyshev.C_one]
  | succ r ih =>
    have hpow : (2 : ℤ) ^ (r + 1) = 2 * (2 : ℤ) ^ r := by ring
    rw [show cyclicReduction B (r + 1) = cyclicReduction B r ^ 2 - 2 from rfl, ih, hpow,
      chebyshevC_two_mul, map_sub, map_pow, map_ofNat]

/-- **Equation (2.36)** of [saad2003iterative], read on the eigenvectors of $B$. Let
$B \in \mathbb{R}^{p \times p}$, $v \in \mathbb{R}^p$ and $\mu \in \mathbb{R}$ with
$Bv = \mu v$. Then for every $r \in \mathbb{N}$
$$B^{(r)} v = C_{2^r}(\mu) \, v.$$
So the cyclic reduction sequence acts on the eigenvectors of $B$ by the scalar recurrence
$\mu \mapsto \mu^2 - 2$, and its eigenvalues are $C_{2^r}(\lambda_j)$ for the eigenvalues
$\lambda_j$ of $B$. -/
theorem cyclicReduction_mulVec_of_mulVec_eq_smul {p : ℕ} {B : Matrix (Fin p) (Fin p) ℝ}
    {v : Fin p → ℝ} {μ : ℝ} (hv : B *ᵥ v = μ • v) (r : ℕ) :
    cyclicReduction B r *ᵥ v = Polynomial.eval μ (Polynomial.Chebyshev.C ℝ ((2 : ℤ) ^ r)) • v := by
  induction r with
  | zero => simpa [cyclicReduction, Polynomial.Chebyshev.C_one] using hv
  | succ r ih =>
    have hpow : (2 : ℤ) ^ (r + 1) = 2 * (2 : ℤ) ^ r := by ring
    have htwo : ((2 : Matrix (Fin p) (Fin p) ℝ)) *ᵥ v = (2 : ℝ) • v := by
      simp [two_smul]
    have hev : Polynomial.eval μ (Polynomial.Chebyshev.C ℝ ((2 : ℤ) ^ r) ^ 2 - 2)
        = Polynomial.eval μ (Polynomial.Chebyshev.C ℝ ((2 : ℤ) ^ r)) ^ 2 - 2 := by simp
    rw [show cyclicReduction B (r + 1) = cyclicReduction B r ^ 2 - 2 from rfl, hpow,
      chebyshevC_two_mul, Matrix.sub_mulVec, pow_two (cyclicReduction B r),
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, ih, htwo, hev]
    module

/-- Evaluating $\prod_{k < m} (X - c_k)$ at a matrix $B$ gives the ordered product
$\prod_{k < m} (B - c_k I)$, written as a `List.prod`. -/
private theorem aeval_prod_X_sub_C {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (c : ℕ → ℝ) (m : ℕ) :
    Polynomial.aeval B (∏ k ∈ Finset.range m, (Polynomial.X - Polynomial.C (c k)))
      = ((List.range m).map fun k => B - c k • (1 : Matrix (Fin p) (Fin p) ℝ)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, map_mul, ih, List.range_succ, List.map_append, List.prod_append]
    simp [Algebra.algebraMap_eq_smul_one]

/-- **Equation (2.36)** of [saad2003iterative], the factorization of the cyclic reduction operator.
Let $B \in \mathbb{R}^{p \times p}$, $r \in \mathbb{N}$ and $h = 2^r$. Then
$$B^{(r)} = \prod_{i=1}^{h} \big( B - \lambda_i^{(r)} I \big), \qquad \lambda_i^{(r)} =
  2\cos\Big(\frac{(2i - 1)\pi}{2h}\Big).$$
So the solves with $B^{(r)}$ on lines 5 and 14 of Algorithm 2.2 split into $h$ tridiagonal
solves.

**Typo.** Equation (2.36) prints $A-\lambda_i^{(r)}I$ in the product. The preceding
factorization uses $B-\lambda_i^{(r)}I$, the coefficient matrix for those solves.

**Generalization.** The statement gives the factorization of the operator on its own,
for every square real $B$, independently of the number of grid blocks or right-hand sides.

The Lean product runs over $i = 0, \dots, h - 1$ and writes the node as
$2\cos((2i + 1)\pi/(2h))$, which is the list of the source with the index shifted by one. It is
an ordered `List.prod`, because matrix multiplication is not commutative, although these factors
commute. The proof carries the backbone's `Polynomial.Chebyshev.C_natCast_eq_prod` across the
algebra map `Polynomial.aeval B` by (2.33): the Vieta–Lucas polynomial $C_h$ is monic of degree
$h$, with the $h$ distinct real roots above. -/
theorem equation_2_36 {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (r : ℕ) :
    cyclicReduction B r = ((List.range (2 ^ r)).map fun i : ℕ =>
        B - (2 * Real.cos ((2 * i + 1) * π / (2 * 2 ^ r))) •
          (1 : Matrix (Fin p) (Fin p) ℝ)).prod := by
  have hne : (2 : ℕ) ^ r ≠ 0 := (Nat.two_pow_pos r).ne'
  have hcast : ((2 ^ r : ℕ) : ℤ) = (2 : ℤ) ^ r := by push_cast; ring
  rw [equation_2_33, ← hcast, Polynomial.Chebyshev.C_natCast_eq_prod hne, aeval_prod_X_sub_C]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  have hnode : Polynomial.Chebyshev.rootNode (2 ^ r) k
      = 2 * Real.cos ((2 * k + 1) * π / (2 * 2 ^ r)) := by
    rw [Polynomial.Chebyshev.rootNode]
    push_cast
    ring_nf
  rw [hnode]

end TwoDimensional

end SaadSparse.Chapter02
