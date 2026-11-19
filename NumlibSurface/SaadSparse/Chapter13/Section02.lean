/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import NumlibSurface.SaadSparse.Chapter04.Section02

/-!
# Saad, Section 13.2: The model problems and the spectra of the smoothers

This module formalizes Section 13.2 of [saad2003iterative]: the one- and two-dimensional discrete
Laplaceans on which the multigrid chapter is built, their eigenvalues and eigenvectors, and the
spectra of Richardson's iteration (Section 13.2.1), weighted Jacobi (Section 13.2.2) and
Gauss–Seidel (Section 13.2.3) on them. The one-dimensional matrix is $A = \operatorname{tridiag}(-1,
2, -1) \in \mathbb{R}^{n \times n}$, with the eigenvalues $\lambda_k = 4 \sin^2(\theta_k/2)$,
$\theta_k = k\pi/(n+1)$, and the discrete sine vectors as eigenvectors. The two-dimensional
five-point matrix is a tensor sum of two such matrices. The sine eigenbasis comes from
`Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`, the tensor eigenbasis from
`Numlib.LinearAlgebra.Matrix.KroneckerSum`, and the Gauss–Seidel spectrum from Young's theorem,
Theorem 4.16 (`SaadSparse.Chapter04.theorem_4_16_mpr`), since a tridiagonal matrix is consistently
ordered.

The chapter rests on two conclusions. First, the spectral radius of each smoother is $1 - O(h^2)$,
so none of them is a good solver (`SaadSparse.Chapter13.richardson_factor_le`,
`SaadSparse.Chapter13.equation_13_22`). Second, on the oscillatory half of the spectrum, $k > n/2$,
each damping factor is bounded away from $1$ independently of $h$: this is the smoothing property
(`SaadSparse.Chapter13.richardson_factor_le_half_of_oscillatory`,
`SaadSparse.Chapter13.smoothingFactor_two_thirds`,
`SaadSparse.Chapter13.smoothingFactor2D_four_fifths`).

## Main definitions

* Equation (13.4), `SaadSparse.Chapter13.laplacian1D`: the one-dimensional model matrix
  $\operatorname{tridiag}(-1, 2, -1)$.
* Equation (13.6), `SaadSparse.Chapter13.theta`: the angle $\theta_k = k\pi/(n+1)$.
* Equation (13.7), `SaadSparse.Chapter13.eigenvalue1D`: the eigenvalue
  $\lambda_k = 4 \sin^2(\theta_k/2)$.
* Equations (13.11)–(13.12), `SaadSparse.Chapter13.laplacian2D`: the two-dimensional five-point
  matrix.
* Section 13.2.3, `SaadSparse.Chapter13.gaussSeidel1D`: the Gauss–Seidel iteration matrix of the
  one-dimensional model problem.
* Equation (13.29), `SaadSparse.Chapter13.gaussSeidelVec`: the vector with components
  $(\cos\theta_k)^j \sin(j\theta_k)$.

## Main results

* Section 13.2, `SaadSparse.Chapter13.laplacian1D_posDef`: the one-dimensional model matrix is
  symmetric positive definite.
* Equation (13.8), `SaadSparse.Chapter13.laplacian1D_mulVec_sineVec`: the discrete sine vector $w_k$
  is an eigenvector for $\lambda_k$.
* Equation (13.9), `SaadSparse.Chapter13.sineVec_eq_sin_grid`: the components of $w_k$ are the grid
  values $\sin(k\pi x_j)$.
* Equations (13.6)–(13.9), `SaadSparse.Chapter13.equation_13_7`: the eigenvalues of the
  one-dimensional model matrix are exactly the $\lambda_k$.
* Equation (13.12), `SaadSparse.Chapter13.laplacian2D_eq_kroneckerSum`: the five-point matrix is the
  tensor sum of two one-dimensional model matrices.
* Equation (13.11), `SaadSparse.Chapter13.laplacian2D_block_apply`: the block tridiagonal form of
  the five-point matrix.
* Section 13.2, `SaadSparse.Chapter13.laplacian2D_posDef`: the five-point matrix is symmetric
  positive definite.
* Equation (13.13), `SaadSparse.Chapter13.laplacian2D_mulVec_kroneckerVec`: $w_k \otimes v_l$ is an
  eigenvector of the five-point matrix for $\lambda_k + \mu_l$.
* Equation (13.13), `SaadSparse.Chapter13.kroneckerVec_sineVec_eq_sin_grid`: the grid values of
  $w_k \otimes v_l$ are $\sin(k\pi x_i)\sin(l\pi y_j)$.
* Equations (13.13)–(13.14), `SaadSparse.Chapter13.equation_13_14`: the eigenvalues of the
  five-point matrix are exactly the sums $\lambda_k + \mu_l$.
* Equations (13.15)–(13.16), `SaadSparse.Chapter13.richardson_reduction`: Richardson's iteration
  multiplies the $w_k$-component of the error by $1 - \lambda_k/\gamma$ in each step.
* Section 13.2.1, `SaadSparse.Chapter13.richardson_factor_eq_cos_sq`: with $\gamma = 4$ the
  reduction factor is $\cos^2(\theta_k/2)$.
* Section 13.2.1, `SaadSparse.Chapter13.richardson_factor_le`: with $\gamma = 4$ every reduction
  factor is at most $1 - \sin^2(\pi/(2(n+1)))$.
* Section 13.2.1, `SaadSparse.Chapter13.richardson_factor_le_half_of_oscillatory`: with $\gamma = 4$
  the reduction factor of an oscillatory mode is at most $1/2$.
* Equation (13.21), `SaadSparse.Chapter13.equation_13_21`: the eigenvalues of the weighted Jacobi
  iteration matrix in one dimension are $1 - 2\omega\sin^2(\theta_k/2)$.
* Equation (13.21) in two dimensions, `SaadSparse.Chapter13.equation_13_21_two`: the eigenvalues in
  two dimensions are $1 - \omega(\sin^2(\theta_k/2) + \sin^2(\theta_l/2))$.
* Equation (13.22), `SaadSparse.Chapter13.equation_13_22`: for $0 < \omega \le 1$ the weighted
  Jacobi eigenvalues have absolute value at most $1 - 2\omega\sin^2(\pi/(2(n+1)))$.
* Equation (13.23), `SaadSparse.Chapter13.weightedJacobi_eigenvalue_mem_Ioc`: on an oscillatory mode
  the one-dimensional weighted Jacobi eigenvalue lies in $(1 - 2\omega, 1 - \omega]$.
* Section 13.2.2, `SaadSparse.Chapter13.smoothingFactor_one_half`: the one-dimensional smoothing
  factor at $\omega = 1/2$ is at most $1/2$.
* Section 13.2.2, `SaadSparse.Chapter13.smoothingFactor_two_thirds`: the one-dimensional smoothing
  factor at $\omega = 2/3$ is at most $1/3$.
* Equation (13.25), `SaadSparse.Chapter13.weightedJacobi2D_eigenvalue_mem_Ioc`: on an oscillatory
  mode the two-dimensional weighted Jacobi eigenvalue lies in $(1 - 2\omega, 1 - \omega/2]$.
* Section 13.2.2, `SaadSparse.Chapter13.smoothingFactor2D_one_half`: the two-dimensional smoothing
  factor at $\omega = 1/2$ is at most $3/4$.
* Equation (13.25), `SaadSparse.Chapter13.smoothingFactor2D_four_fifths`: the two-dimensional
  smoothing factor at $\omega = 4/5$ is at most $3/5$.
* Equation (13.29), `SaadSparse.Chapter13.equation_13_29`: the vector $u_k$ is an eigenvector of the
  Gauss–Seidel iteration matrix for $\cos^2\theta_k$.
* Section 13.2.3, `SaadSparse.Chapter13.jacobi1D_hasEigenvalue_iff`: the eigenvalues of the Jacobi
  iteration matrix are exactly the $\cos\theta_k$.
* Section 13.2.3, `SaadSparse.Chapter13.gaussSeidel_eigenvalues`: every $\cos^2\theta_k$ is an
  eigenvalue of the Gauss–Seidel iteration matrix.

## Conventions

* The matrices of this section are unscaled: `SaadSparse.Chapter13.laplacian1D n` is
  $\operatorname{tridiag}(-1, 2, -1)$, which is $h^2$ times the discretization of $-u''$ on the grid
  $x_i = ih$, $h = 1/(n+1)$. Section 2.2.3 writes the same matrix with the factor $1/h^2$; that
  matrix is `SaadSparse.Chapter02.laplacian1D n h`, and `SaadSparse.Chapter02.laplacian2D_smul`
  relates the two.
* Interior points are numbered from $0$: the index `k : Fin n` is the book's $k + 1$, and
  `SaadSparse.Chapter13.theta n k` is the book's $\theta_{k+1}$. The book's oscillatory condition
  $k > n/2$ is `n + 1 ≤ 2 * (k + 1)` for a $0$-based `k`.
* The two-dimensional matrix is indexed by the product type `Fin n × Fin m`, never by `Fin (n * m)`.
  This is the indexing of `Numlib.LinearAlgebra.Matrix.KroneckerSum`, so the tensor sum (13.12) is
  literally `laplacian1D n ⊕ₖ laplacian1D m`, and the first coordinate indexes the blocks of the
  block tridiagonal form.
* The statement "$\mu$ is an eigenvalue of $A$" is `Module.End.HasEigenvalue (toEuclideanLin A) μ`.
  The discrete sine vector $w_k$ is `Matrix.sineVec n k`, and $w_k \otimes v_l$ is
  `Matrix.kroneckerVec (Matrix.sineVec n k) (Matrix.sineVec m l)`.

## Implementation notes

* The lists of eigenvalues in (13.7) and (13.14) are complete, not only lists of eigenvectors. The
  normalized sine vectors form the orthonormal basis `Matrix.sineOrthonormalBasis n`, and their
  tensor products form the orthonormal basis `Matrix.kroneckerOrthonormalBasis`, so the eigenvalues
  are exhausted even where two sums $\lambda_k + \mu_l$ coincide.
* The weighted Jacobi iteration matrix is the iteration operator of `Matrix.jorSplitting`, and the
  Gauss–Seidel iteration matrix is the iteration operator of `Matrix.gaussSeidelSplitting`.

## Deviations from the source

* **§13.2, grid values after (13.14)** (reading).
  `SaadSparse.Chapter13.kroneckerVec_sineVec_eq_sin_grid` uses normalized coordinates. On the
  earlier rectangle with side lengths $l_1,l_2$, the physical coordinates must be divided by the
  respective side lengths.
* **(13.15)–(13.16)** (convention and generalization).
  `SaadSparse.Chapter13.richardson_reduction` uses the iterate minus the solution and allows any
  $\gamma$, with total division. The source uses the solution minus the iterate and chooses a
  positive spectral upper bound.
* **(13.19)–(13.22)** (scope). The weighted Jacobi eigenpair statements use a splitting with
  nonzero weight. `SaadSparse.Chapter13.equation_13_22` gives an absolute-value bound for
  $0<\omega\le1$ where the printed display states signed endpoint bounds.
* **Text before (13.23)** (correction). The sine-square estimate uses $\theta_k/2$, as in
  `SaadSparse.Chapter13.sin_sq_theta_div_two_ge_half` and the factor in (13.21). The printed
  prose omits the half angle.
* **Smoothing factors in §13.2.2** (scope). The theorem at weight $2/3$ in one dimension and the
  theorem at weight $4/5$ in two dimensions give the stated bounds at those weights. The
  optimality comparisons across weights are omitted.
* **(13.25)** (scope). `SaadSparse.Chapter13.weightedJacobi2D_eigenvalue_mem_Ioc` assumes an
  oscillatory mode in at least one coordinate and proves the simple interval bounds. The source
  also gives a sharper finite-grid lower bound.
* **§13.2.3, Gauss–Seidel spectrum** (correction and scope).
  `SaadSparse.Chapter13.gaussSeidel_eigenvalues` asserts membership of the cosine-square values.
  The list misses zero for even positive $n$, which
  `SaadSparse.Chapter13.gaussSeidel1D_mulVec_single` supplies. In the corrected eigenvector
  formula the vectors from paired modes $k$ and $n+1-k$ differ only by a sign, so the family
  cannot furnish the basis suggested by the text.
* **Equation (13.23)** (generalization). The book prints the upper bound $1 - \omega/2$ for the
  oscillatory weighted Jacobi eigenvalues in one dimension; the sharp bound $1 - \omega$ is proved.
  See `SaadSparse.Chapter13.weightedJacobi_eigenvalue_mem_Ioc`.
* **Smoothing factor at $\omega = 1/2$, Section 13.2.2** (generalization). The book gives $3/4$ in
  one dimension; the sharp value $1/2$ is proved. See
  `SaadSparse.Chapter13.smoothingFactor_one_half`.
* **The sentence after (13.25)** (typo). The book says that $\omega = 3/5$ gives the smoothing
  factor $4/5$; the two numbers are transposed, and $\omega = 4/5$ gives $3/5$. See
  `SaadSparse.Chapter13.smoothingFactor2D_four_fifths`.
* **Equation (13.29)** (correction). The book prints $|\cos\theta_k|^j$; the eigenvector has the
  signed power $(\cos\theta_k)^j$. See `SaadSparse.Chapter13.gaussSeidelVec`.
-/

open Finset Matrix Stationary
open scoped Kronecker Matrix Real

namespace SaadSparse.Chapter13

/-! ### The one-dimensional model problem, (13.4)–(13.9) -/

section OneDimensional

variable {n : ℕ}

/-- **Equation (13.4)** of [saad2003iterative]. The one-dimensional **model matrix** is $A =
\operatorname{tridiag}(-1, 2, -1) \in \mathbb{R}^{n \times n}$, the discretization of $-u'' = f$
on $(0, 1)$ with homogeneous Dirichlet conditions on the uniform grid $x_i = ih$, $h = 1/(n+1)$.

This is the unscaled matrix of Chapter 13, in which the factor $h^2$ is on the right-hand side.
The matrix `SaadSparse.Chapter02.laplacian1D n h` is the same matrix scaled by $1/h^2$, as
Section 2.2.3 displays it. The definition is `Matrix.symmTridiagonalToeplitz n (-1) 2`. -/
def laplacian1D (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := symmTridiagonalToeplitz n (-1) 2

/-- The one-dimensional model matrix is the backbone matrix $\operatorname{tridiag}(-1, 2, -1)$,
`Matrix.symmTridiagonalToeplitz n (-1) 2`. -/
theorem laplacian1D_eq (n : ℕ) : laplacian1D n = symmTridiagonalToeplitz n (-1) 2 := rfl

/-- The entries of the one-dimensional model matrix: $a_{ii} = 2$, $a_{ij} = -1$ if $|i - j| = 1$,
and $a_{ij} = 0$ otherwise. -/
theorem laplacian1D_apply (n : ℕ) (i j : Fin n) :
    laplacian1D n i j =
      if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0 :=
  symmTridiagonalToeplitz_apply' (-1) 2 i j

/-- The one-dimensional model matrix is symmetric. -/
theorem laplacian1D_isSymm (n : ℕ) : (laplacian1D n).IsSymm :=
  symmTridiagonalToeplitz_isSymm (-1) 2

/-- The one-dimensional model matrix is Hermitian. -/
theorem laplacian1D_isHermitian (n : ℕ) : (laplacian1D n).IsHermitian :=
  symmTridiagonalToeplitz_isHermitian (-1) 2

/-- The one-dimensional model matrix is tridiagonal. This makes it consistently ordered in Section
13.2.3. -/
theorem laplacian1D_isTridiagonal (n : ℕ) : (laplacian1D n).IsTridiagonal :=
  symmTridiagonalToeplitz_isTridiagonal (-1) 2

/-- **Section 13.2** of [saad2003iterative], positive definiteness of the model matrix. The
one-dimensional model matrix $\operatorname{tridiag}(-1, 2, -1) \in \mathbb{R}^{n \times n}$ is
symmetric positive definite. -/
theorem laplacian1D_posDef (n : ℕ) : (laplacian1D n).PosDef :=
  posDef_symmTridiagonalToeplitz_neg_one_two n

/-- The diagonal of the one-dimensional model matrix is $D = 2I$. Therefore $D^{-1}A = A/2$, which
makes weighted Jacobi elementary in Section 13.2.2. -/
theorem diagPart_laplacian1D (n : ℕ) : diagPart (laplacian1D n) = (2 : ℝ) • 1 := by
  ext i j
  rw [diagPart_apply, laplacian1D_eq, symmTridiagonalToeplitz_apply_self, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The diagonal $D = 2I$ of the one-dimensional model matrix is invertible. -/
theorem isUnit_diagPart_laplacian1D (n : ℕ) : IsUnit (diagPart (laplacian1D n)) :=
  (isUnit_diagPart_iff _).2 fun i => by
    rw [laplacian1D_eq, symmTridiagonalToeplitz_apply_self]; norm_num

/-- **Equation (13.6)** of [saad2003iterative]. The angle $\theta_k = k\pi/(n+1)$, for
$k = 1, \dots, n$.

The index is $0$-based: `k : Fin n` is the book's $k + 1$, so `theta n k` is
$(k + 1)\pi/(n + 1)$. -/
noncomputable def theta (n : ℕ) (k : Fin n) : ℝ := (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)

/-- The angle is positive: $\theta_k > 0$. -/
theorem theta_pos (n : ℕ) (k : Fin n) : 0 < theta n k := angle_pos n k

/-- The angle is less than $\pi$: $\theta_k < \pi$. This is why the $n$ eigenvalues are distinct. -/
theorem theta_lt_pi (n : ℕ) (k : Fin n) : theta n k < π := angle_lt_pi n k

/-- The sine of the angle is positive: $\sin\theta_k > 0$. So the sine eigenvectors are nonzero. -/
theorem sin_theta_pos (n : ℕ) (k : Fin n) : 0 < Real.sin (theta n k) :=
  Real.sin_pos_of_pos_of_lt_pi (theta_pos n k) (theta_lt_pi n k)

/-- The half angle written out: $\theta_k/2 = k\pi/(2(n+1))$, with the $0$-based index `k` standing
for the book's $k + 1$. -/
theorem theta_div_two (n : ℕ) (k : Fin n) :
    theta n k / 2 = (((k : ℕ) : ℝ) + 1) * π / (2 * ((n : ℝ) + 1)) := by
  rw [theta, div_div, mul_comm ((n : ℝ) + 1) 2]

/-- The half angle lies in the interval on which the sine is increasing and positive:
$0 < \theta_k/2 < \pi/2$. -/
theorem theta_div_two_mem_Ioo (n : ℕ) (k : Fin n) : theta n k / 2 ∈ Set.Ioo 0 (π / 2) :=
  Set.mem_Ioo.2 ⟨by linarith [theta_pos n k], by linarith [theta_lt_pi n k]⟩

/-- The sine of the half angle is positive: $\sin(\theta_k/2) > 0$. -/
theorem sin_theta_div_two_pos (n : ℕ) (k : Fin n) : 0 < Real.sin (theta n k / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (theta_div_two_mem_Ioo n k).1
    (lt_trans (theta_div_two_mem_Ioo n k).2 (by linarith [Real.pi_pos]))

/-- The cosine of the half angle is positive: $\cos(\theta_k/2) > 0$. -/
theorem cos_theta_div_two_pos (n : ℕ) (k : Fin n) : 0 < Real.cos (theta n k / 2) :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(theta_div_two_mem_Ioo n k).1, Real.pi_pos], (theta_div_two_mem_Ioo n k).2⟩

/-- Since $\theta_k/2 < \pi/2$, the squared sine of the half angle is less than one:
$\sin^2(\theta_k/2) < 1$. -/
theorem sin_sq_theta_div_two_lt_one (n : ℕ) (k : Fin n) : Real.sin (theta n k / 2) ^ 2 < 1 := by
  have h := Real.sin_sq_add_cos_sq (theta n k / 2)
  nlinarith [cos_theta_div_two_pos n k]

/-- **Equation (13.7)** of [saad2003iterative]. The eigenvalue $\lambda_k = 4\sin^2(\theta_k/2)$ of
the one-dimensional model matrix. -/
noncomputable def eigenvalue1D (n : ℕ) (k : Fin n) : ℝ := 4 * Real.sin (theta n k / 2) ^ 2

/-- The eigenvalue in the form of (13.6)–(13.7) of [saad2003iterative]:
$\lambda_k = 2(1 - \cos\theta_k)$. -/
theorem eigenvalue1D_eq (n : ℕ) (k : Fin n) :
    eigenvalue1D n k = 2 - 2 * Real.cos (theta n k) := by
  rw [eigenvalue1D, Real.two_sub_two_mul_cos]

/-- The eigenvalues of the one-dimensional model matrix are positive: $\lambda_k > 0$. -/
theorem eigenvalue1D_pos (n : ℕ) (k : Fin n) : 0 < eigenvalue1D n k := by
  rw [eigenvalue1D]
  nlinarith [sin_theta_div_two_pos n k]

/-- The eigenvalues of the one-dimensional model matrix are less than $4$: $\lambda_k < 4$. The
number $\gamma = 4$ is the Gershgorin bound that Section 13.2.1 uses for Richardson's iteration. -/
theorem eigenvalue1D_lt_four (n : ℕ) (k : Fin n) : eigenvalue1D n k < 4 := by
  rw [eigenvalue1D]
  linarith [sin_sq_theta_div_two_lt_one n k]

/-- **Equation (13.8)** of [saad2003iterative]. The discrete sine vector $w_k \in \mathbb{R}^n$ with
components $(w_k)_j = \sin(j\theta_k)$ is an eigenvector of the one-dimensional model matrix for
the eigenvalue $\lambda_k = 4\sin^2(\theta_k/2)$:
$$A w_k = \lambda_k w_k.$$

The vector $w_k$ is `Matrix.sineVec n k`. -/
theorem laplacian1D_mulVec_sineVec (n : ℕ) (k : Fin n) :
    laplacian1D n *ᵥ sineVec n k = eigenvalue1D n k • sineVec n k := by
  rw [laplacian1D_eq, symmTridiagonalToeplitz_mulVec_sineVec]
  congr 1
  rw [eigenvalue1D_eq, theta]
  ring

/-- **Equation (13.9)** of [saad2003iterative]. The components of the discrete sine vector are the
values of a sine at the grid points: $(w_k)_j = \sin(k\pi x_j)$ with $x_j = jh$ and
$h = 1/(n+1)$.

With $0$-based indices, the component `j` of `Matrix.sineVec n k` is
$\sin((k + 1)\pi \, (j + 1) h)$. -/
theorem sineVec_eq_sin_grid (n : ℕ) (k j : Fin n) :
    sineVec n k j =
      Real.sin ((((k : ℕ) : ℝ) + 1) * π * ((((j : ℕ) : ℝ) + 1) * (1 / ((n : ℝ) + 1)))) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [sineVec_apply]
  congr 1
  field_simp

/-- **Equations (13.6)–(13.9)** of [saad2003iterative]. A real number $\mu$ is an eigenvalue of the
one-dimensional model matrix $A = \operatorname{tridiag}(-1, 2, -1) \in \mathbb{R}^{n \times n}$
if and only if
$$\mu = \lambda_k = 2(1 - \cos\theta_k) = 4\sin^2(\theta_k/2), \qquad \theta_k =
  \frac{k\pi}{n+1},$$
for some $k \in \{1, \dots, n\}$.

The eigenvectors are the discrete sine vectors $w_k$ of (13.8)
(`SaadSparse.Chapter13.laplacian1D_mulVec_sineVec`), whose components are the grid values of
(13.9) (`SaadSparse.Chapter13.sineVec_eq_sin_grid`). The list is complete because the normalized
$w_k$ form the orthonormal basis `Matrix.sineOrthonormalBasis n`. -/
theorem equation_13_7 (n : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue (toEuclideanLin (laplacian1D n)) μ ↔
      ∃ k : Fin n, μ = eigenvalue1D n k := by
  rw [laplacian1D_eq, symmTridiagonalToeplitz_hasEigenvalue_iff]
  refine exists_congr fun k => ?_
  rw [eigenvalue1D_eq, theta]
  constructor <;> intro h <;> linarith

/-! ### Monotonicity of the eigenvalues in $k$ -/

/-- The largest of the numbers $\cos\theta_k$ is the one at $k = 1$:
$\cos\theta_k \le \cos(\pi/(n+1))$ for every $k$. -/
theorem cos_theta_le (n : ℕ) (k : Fin n) :
    Real.cos (theta n k) ≤ Real.cos (π / ((n : ℝ) + 1)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk1 : π / ((n : ℝ) + 1) ≤ theta n k := by
    rw [theta, div_le_div_iff_of_pos_right hn]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (theta_lt_pi n k).le hk1

/-- The smallest of the numbers $\cos\theta_k$ is the one at $k = n$, where it is
$-\cos(\pi/(n+1))$: $-\cos(\pi/(n+1)) \le \cos\theta_k$ for every $k$. -/
theorem neg_cos_le_cos_theta (n : ℕ) (k : Fin n) :
    -Real.cos (π / ((n : ℝ) + 1)) ≤ Real.cos (theta n k) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk2 : theta n k ≤ π - π / ((n : ℝ) + 1) := by
    have hkn : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast k.isLt
    have hrw : π - π / ((n : ℝ) + 1) = (n : ℝ) * π / ((n : ℝ) + 1) := by field_simp; ring
    rw [theta, hrw, div_le_div_iff_of_pos_right hn]
    nlinarith [Real.pi_pos]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (theta_pos n k).le
    (by linarith [div_nonneg Real.pi_pos.le hn.le] : π - π / ((n : ℝ) + 1) ≤ π) hk2
  rwa [Real.cos_pi_sub] at h

/-- The smallest half angle is the one at $k = 1$: $\sin^2(\pi/(2(n+1))) \le \sin^2(\theta_k/2)$ for
every $k$. -/
theorem sin_sq_theta_div_two_ge (n : ℕ) (k : Fin n) :
    Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 ≤ Real.sin (theta n k / 2) ^ 2 := by
  have h1 := Real.two_sub_two_mul_cos (theta n k)
  have h2 := Real.two_sub_two_mul_cos (π / ((n : ℝ) + 1))
  rw [show π / ((n : ℝ) + 1) / 2 = π / (2 * ((n : ℝ) + 1)) by
    rw [div_div, mul_comm ((n : ℝ) + 1) 2]] at h2
  linarith [cos_theta_le n k]

/-- The largest half angle is the one at $k = n$, where $\sin^2(\theta_n/2) = \cos^2(\pi/(2(n+1))) =
1 - \sin^2(\pi/(2(n+1)))$: so $\sin^2(\theta_k/2) \le 1 - \sin^2(\pi/(2(n+1)))$ for every $k$. -/
theorem sin_sq_theta_div_two_le (n : ℕ) (k : Fin n) :
    Real.sin (theta n k / 2) ^ 2 ≤ 1 - Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  have h1 := Real.two_sub_two_mul_cos (theta n k)
  have h2 := Real.two_sub_two_mul_cos (π / ((n : ℝ) + 1))
  rw [show π / ((n : ℝ) + 1) / 2 = π / (2 * ((n : ℝ) + 1)) by
    rw [div_div, mul_comm ((n : ℝ) + 1) 2]] at h2
  linarith [neg_cos_le_cos_theta n k]

/-- The oscillatory half of the spectrum: if $k > n/2$, then $\theta_k \ge \pi/2$, that is,
$\sin^2(\theta_k/2) \ge 1/2$.

With the $0$-based index `k`, the condition $k > n/2$ reads `n + 1 ≤ 2 * (k + 1)`. This one
inequality is behind every mesh-independent smoothing factor of Section 13.2.

**Correction.** Correct uses half angle, whereas source sentence omits half angle.
-/
theorem sin_sq_theta_div_two_ge_half (n : ℕ) {k : Fin n} (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) :
    1 / 2 ≤ Real.sin (theta n k / 2) ^ 2 := by
  have hk' : (n : ℝ) + 1 ≤ 2 * (((k : ℕ) : ℝ) + 1) := by exact_mod_cast hk
  have hcos : Real.cos (theta n k) ≤ 0 := by
    refine Real.cos_nonpos_of_pi_div_two_le_of_le ?_ (by linarith [theta_lt_pi n k, Real.pi_pos])
    rw [theta, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith [Real.pi_pos]
  linarith [Real.two_sub_two_mul_cos (theta n k)]

end OneDimensional

/-! ### The two-dimensional model problem, (13.10)–(13.14) -/

section TwoDimensional

variable {n m : ℕ}

/-- **Equations (13.11)–(13.12)** of [saad2003iterative]. The two-dimensional **model matrix** on a
grid of $n \times m$ interior points is the five-point discretization of $-\Delta u = f$ on the
unit square with homogeneous Dirichlet conditions. Its diagonal entries are $4$, the entry is
$-1$ between two grid points that are neighbours in one coordinate direction, and all other
entries are $0$.

The matrix is indexed by the product type `Fin n × Fin m`. It is block tridiagonal with the
diagonal blocks $B = \operatorname{tridiag}(-1, 4, -1)$ and the blocks $-I$ next to the diagonal
(`SaadSparse.Chapter13.laplacian2D_block_apply`). Equivalently, it is the tensor sum
$A = I \otimes T_x + T_y \otimes I$ of (13.12)
(`SaadSparse.Chapter13.laplacian2D_eq_kroneckerSum`). It is unscaled, as everywhere in Section
13.2. -/
def laplacian2D (n m : ℕ) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ :=
  Matrix.of fun p q =>
    if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 then 4
    else if (p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) then -1
    else if (p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2) then -1
    else 0

/-- The entries of the two-dimensional model matrix: $4$ on the diagonal, $-1$ at each of the four
grid neighbours, and $0$ otherwise. -/
theorem laplacian2D_apply (n m : ℕ) (p q : Fin n × Fin m) :
    laplacian2D n m p q =
      if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 then 4
      else if (p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) then -1
      else if (p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2) then -1
      else 0 :=
  rfl

/-- **Equation (13.12)** of [saad2003iterative]. The five-point matrix is the tensor sum
$$A = I \otimes T_x + T_y \otimes I$$
of two one-dimensional model matrices, one for each coordinate direction.

The tensor sum is `laplacian1D n ⊕ₖ laplacian1D m` of
`Numlib.LinearAlgebra.Matrix.KroneckerSum`. -/
theorem laplacian2D_eq_kroneckerSum (n m : ℕ) :
    laplacian2D n m = laplacian1D n ⊕ₖ laplacian1D m := by
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  rw [Matrix.kroneckerSum_apply, laplacian1D_apply, laplacian1D_apply, laplacian2D_apply]
  simp only [← Fin.val_eq_val]
  split_ifs <;> first | (exfalso; omega) | ring

/-- **Equation (13.11)** of [saad2003iterative]. The block form of the five-point matrix: with the
blocks indexed by the first coordinate, the diagonal blocks are $B = \operatorname{tridiag}(-1,
4, -1) \in \mathbb{R}^{m \times m}$, the blocks next to the diagonal are $-I$, and all other
blocks are $0$. -/
theorem laplacian2D_block_apply (n m : ℕ) (i₁ j₁ : Fin n) (i₂ j₂ : Fin m) :
    laplacian2D n m (i₁, i₂) (j₁, j₂) =
      if (i₁ : ℕ) = j₁ then symmTridiagonalToeplitz m (-1) 4 i₂ j₂
      else if (i₁ : ℕ) + 1 = j₁ ∨ (j₁ : ℕ) + 1 = i₁ then
        -(1 : Matrix (Fin m) (Fin m) ℝ) i₂ j₂
      else 0 := by
  rw [laplacian2D_eq_kroneckerSum, Matrix.kroneckerSum_apply, laplacian1D_apply,
    laplacian1D_apply, symmTridiagonalToeplitz_apply', Matrix.one_apply]
  simp only [← Fin.val_eq_val]
  split_ifs <;> ring

/-- The diagonal entries of the two-dimensional model matrix are $4$. -/
theorem laplacian2D_apply_self (n m : ℕ) (p : Fin n × Fin m) : laplacian2D n m p p = 4 := by
  rw [laplacian2D_apply, ite_eq_left ⟨rfl, rfl⟩]

/-- The diagonal of the two-dimensional model matrix is $D = 4I$. -/
theorem diagPart_laplacian2D (n m : ℕ) : diagPart (laplacian2D n m) = (4 : ℝ) • 1 := by
  ext p q
  rw [diagPart_apply, laplacian2D_apply_self, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The diagonal $D = 4I$ of the two-dimensional model matrix is invertible. -/
theorem isUnit_diagPart_laplacian2D (n m : ℕ) : IsUnit (diagPart (laplacian2D n m)) :=
  (isUnit_diagPart_iff _).2 fun p => by rw [laplacian2D_apply_self]; norm_num

/-- **Section 13.2** of [saad2003iterative], positive definiteness of the five-point matrix. The
two-dimensional model matrix is symmetric positive definite.

The proof uses that positive definiteness is preserved by a tensor sum. -/
theorem laplacian2D_posDef (n m : ℕ) : (laplacian2D n m).PosDef := by
  rw [laplacian2D_eq_kroneckerSum]
  exact Matrix.posDef_kroneckerSum (laplacian1D_posDef n) (laplacian1D_posDef m)

/-- **Equation (13.13)** of [saad2003iterative]. Let $w_k \in \mathbb{R}^n$ and
$v_l \in \mathbb{R}^m$ be discrete sine vectors. Their tensor product
$z_{k,l} = w_k \otimes v_l$ is an eigenvector of the two-dimensional model matrix for the
eigenvalue $\lambda_k + \mu_l$, where $\lambda_k$ and $\mu_l$ are the eigenvalues of the
one-dimensional model matrices of sizes $n$ and $m$:
$$A z_{k,l} = (\lambda_k + \mu_l) \, z_{k,l}.$$
-/
theorem laplacian2D_mulVec_kroneckerVec (n m : ℕ) (k : Fin n) (l : Fin m) :
    laplacian2D n m *ᵥ kroneckerVec (sineVec n k) (sineVec m l) =
      (eigenvalue1D n k + eigenvalue1D m l) • kroneckerVec (sineVec n k) (sineVec m l) := by
  rw [laplacian2D_eq_kroneckerSum]
  exact Matrix.kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul
    (laplacian1D_mulVec_sineVec n k) (laplacian1D_mulVec_sineVec m l)

/-- **Equation (13.13)** of [saad2003iterative], the grid values. The eigenvector
$z_{k,l} = w_k \otimes v_l$ has the value $\sin(k\pi x_i)\sin(l\pi y_j)$ at the grid point
$(x_i, y_j)$, where $x_i = i/(n+1)$ and $y_j = j/(m+1)$.

All indices are $0$-based in the Lean statement, each standing for the book's index plus one.

**Reading.** The two coordinate arguments are normalized grid positions. If $x_i$ and $y_j$ are
physical coordinates on the earlier rectangle with side lengths $l_1,l_2$, the sine factors use
$x_i/l_1$ and $y_j/l_2$. -/
theorem kroneckerVec_sineVec_eq_sin_grid (n m : ℕ) (k : Fin n) (l : Fin m)
    (p : Fin n × Fin m) :
    kroneckerVec (sineVec n k) (sineVec m l) p =
      Real.sin ((((k : ℕ) : ℝ) + 1) * π * ((((p.1 : ℕ) : ℝ) + 1) * (1 / ((n : ℝ) + 1)))) *
        Real.sin ((((l : ℕ) : ℝ) + 1) * π * ((((p.2 : ℕ) : ℝ) + 1) * (1 / ((m : ℝ) + 1)))) := by
  obtain ⟨i, j⟩ := p
  rw [Matrix.kroneckerVec_apply, sineVec_eq_sin_grid, sineVec_eq_sin_grid]

/-- If $Av = \mu v$, then every scalar multiple of $v$, viewed in Euclidean space, is mapped by $A$
to $\mu$ times itself. -/
private theorem toEuclideanLin_toLp_smul_eq {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℝ} {v : N → ℝ} {μ : ℝ} (h : A *ᵥ v = μ • v) (c : ℝ) :
    toEuclideanLin A (WithLp.toLp 2 (c • v)) = μ • WithLp.toLp 2 (c • v) := by
  rw [Matrix.toEuclideanLin_toLp, Matrix.mulVec_smul, h, smul_comm]
  rfl

/-- A symmetric operator with an orthonormal basis of eigenvectors $b_i$, $T b_i = \nu_i b_i$, has
exactly the eigenvalues $\nu_i$. -/
private theorem hasEigenvalue_iff_of_orthonormalBasis {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) {ν : ι → ℝ} (hb : ∀ i, T (b i) = ν i • b i) (μ : ℝ) :
    Module.End.HasEigenvalue T μ ↔ ∃ i, μ = ν i := by
  refine ⟨fun hμ => ?_, ?_⟩
  · by_contra hne
    push Not at hne
    obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hx
    have hzero : ∀ i, inner ℝ (b i) x = 0 := by
      intro i
      have h1 : inner ℝ (b i) (T x) = μ * inner ℝ (b i) x := by rw [hx, real_inner_smul_right]
      have h2 : inner ℝ (b i) (T x) = ν i * inner ℝ (b i) x := by
        rw [← hT (b i) x, hb i, real_inner_smul_left]
      have h3 : (μ - ν i) * inner ℝ (b i) x = 0 := by rw [sub_mul, ← h1, h2, sub_self]
      rcases mul_eq_zero.1 h3 with h' | h'
      · exact absurd (by linarith : μ = ν i) (hne i)
      · exact h'
    refine hx0 ?_
    rw [← b.sum_repr' x]
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_smul]
  · rintro ⟨i, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (hb i), b.orthonormal.ne_zero i⟩

/-- **Equations (13.13)–(13.14)** of [saad2003iterative]. A real number $\mu$ is an eigenvalue of
the two-dimensional model matrix on an $n \times m$ grid if and only if
$$\mu = \lambda_{k,l} = 4\left(\sin^2\frac{k\pi}{2(n+1)} + \sin^2\frac{l\pi}{2(m+1)}\right)$$
for some $k \in \{1, \dots, n\}$ and $l \in \{1, \dots, m\}$.

The eigenvectors are the tensor products $z_{k,l} = w_k \otimes v_l$ of
`SaadSparse.Chapter13.laplacian2D_mulVec_kroneckerVec`. The list is complete even where two of
the sums coincide, because the normalized $w_k \otimes v_l$ form the orthonormal basis
`Matrix.kroneckerOrthonormalBasis` of the whole space. -/
theorem equation_13_14 (n m : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue (toEuclideanLin (laplacian2D n m)) μ ↔
      ∃ (k : Fin n) (l : Fin m), μ = eigenvalue1D n k + eigenvalue1D m l := by
  have hsymm : (toEuclideanLin (laplacian2D n m)).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.2 (by
      rw [laplacian2D_eq_kroneckerSum]
      exact isHermitian_kroneckerSum (laplacian1D_isHermitian n) (laplacian1D_isHermitian m))
  have hb : ∀ q : Fin n × Fin m,
      toEuclideanLin (laplacian2D n m)
          (kroneckerOrthonormalBasis (sineOrthonormalBasis n) (sineOrthonormalBasis m) q) =
        (fun q : Fin n × Fin m => eigenvalue1D n q.1 + eigenvalue1D m q.2) q •
          kroneckerOrthonormalBasis (sineOrthonormalBasis n) (sineOrthonormalBasis m) q := by
    intro q
    have hform :
        kroneckerOrthonormalBasis (sineOrthonormalBasis n) (sineOrthonormalBasis m) q =
          WithLp.toLp 2 ((Real.sqrt (2 / ((n : ℝ) + 1)) * Real.sqrt (2 / ((m : ℝ) + 1))) •
            kroneckerVec (sineVec n q.1) (sineVec m q.2)) := by
      rw [kroneckerOrthonormalBasis_apply, sineOrthonormalBasis_apply, sineOrthonormalBasis_apply,
        WithLp.ofLp_smul, WithLp.ofLp_smul, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
        Matrix.kroneckerVec_smul_left, Matrix.kroneckerVec_smul_right, smul_smul]
    rw [hform]
    exact toEuclideanLin_toLp_smul_eq (laplacian2D_mulVec_kroneckerVec n m q.1 q.2) _
  rw [hasEigenvalue_iff_of_orthonormalBasis _ hsymm _ hb μ]
  exact ⟨fun ⟨q, hq⟩ => ⟨q.1, q.2, hq⟩, fun ⟨k, l, h⟩ => ⟨(k, l), h⟩⟩

end TwoDimensional

/-! ### Section 13.2.1: Richardson's iteration, (13.15)–(13.16) -/

section Richardson

variable {n : ℕ}

/-- If $M$ is symmetric and $Mw = cw$, then $w^T (M^j v) = c^j \, w^T v$ for every vector $v$ and
every $j \ge 0$. -/
private theorem dotProduct_pow_mulVec {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm)
    {w : Fin n → ℝ} {c : ℝ} (hw : M *ᵥ w = c • w) (v : Fin n → ℝ) (j : ℕ) :
    w ⬝ᵥ ((M ^ j) *ᵥ v) = c ^ j * (w ⬝ᵥ v) := by
  have hstep : ∀ u : Fin n → ℝ, w ⬝ᵥ (M *ᵥ u) = c * (w ⬝ᵥ u) := by
    intro u
    rw [dotProduct_mulVec, ← hM.eq, vecMul_transpose, hw, smul_dotProduct, smul_eq_mul]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ← mulVec_mulVec, hstep, ih]
    ring

/-- The Richardson iteration matrix $M_\omega = I - \omega A$ of (13.15) of [saad2003iterative] has
the discrete sine vectors as eigenvectors: $M_\omega w_k = (1 - \omega\lambda_k) w_k$. -/
theorem richardson_iterationMatrix_mulVec_sineVec (n : ℕ) (ω : ℝ) (k : Fin n) :
    (1 - ω • laplacian1D n) *ᵥ sineVec n k = (1 - ω * eigenvalue1D n k) • sineVec n k := by
  rw [sub_mulVec, one_mulVec, Matrix.smul_mulVec, laplacian1D_mulVec_sineVec, smul_smul, sub_smul,
    one_smul]

/-- **Equations (13.15)–(13.16)** of [saad2003iterative]. Let $A$ be the one-dimensional model
matrix, let $\gamma \in \mathbb{R}$, let $b \in \mathbb{R}^n$, and let $x_*$ satisfy
$A x_* = b$. Let $x_j$ be the $j$-th iterate of Richardson's iteration
$x \leftarrow x + \gamma^{-1}(b - Ax)$ from $x_0$. Then the $w_k$-component of the error is
multiplied by $\eta_k = 1 - \lambda_k/\gamma$ in each step:
$$w_k^T (x_j - x_*) = \left(1 - \frac{\lambda_k}{\gamma}\right)^j w_k^T (x_0 - x_*).$$

No hypothesis on $\gamma$ is needed. At $\gamma = 0$, Lean sets $\gamma^{-1} = 0$ and
$\lambda_k/\gamma = 0$, so the iteration does nothing and the factor is $1$. With $\gamma = 4$,
the Gershgorin bound and an upper bound for the spectrum
(`SaadSparse.Chapter13.eigenvalue1D_lt_four`), the factor is $\eta_k = \cos^2(\theta_k/2)$
(`SaadSparse.Chapter13.richardson_factor_eq_cos_sq`). It is at most
$1 - \sin^2(\pi/(2(n+1))) = 1 - O(h^2)$ (`SaadSparse.Chapter13.richardson_factor_le`), so the
iteration is a very slow solver. On the oscillatory half $k > n/2$ of the spectrum it is at most
$1/2$ for every mesh (`SaadSparse.Chapter13.richardson_factor_le_half_of_oscillatory`). The
iteration step is `SaadSparse.Chapter04.richardsonStep`.

**Reading.** Uses the negative of the source error convention and takes any real gamma with total
inverse.
-/
theorem richardson_reduction (n : ℕ) (γ : ℝ) (b x₀ xstar : Fin n → ℝ)
    (hxstar : laplacian1D n *ᵥ xstar = b) (k : Fin n) (j : ℕ) :
    sineVec n k ⬝ᵥ ((Chapter04.richardsonStep (laplacian1D n) γ⁻¹ b)^[j] x₀ - xstar) =
      (1 - eigenvalue1D n k / γ) ^ j * (sineVec n k ⬝ᵥ (x₀ - xstar)) := by
  have hfix : Chapter04.affineStep (1 - γ⁻¹ • laplacian1D n) (γ⁻¹ • b) xstar = xstar := by
    rw [Chapter04.affineStep_fixed_iff, sub_sub_cancel, Matrix.smul_mulVec, hxstar]
  have hsymm : (1 - γ⁻¹ • laplacian1D n).IsSymm :=
    Matrix.isSymm_one.sub ((laplacian1D_isSymm n).smul γ⁻¹)
  have heig : (1 - γ⁻¹ • laplacian1D n) *ᵥ sineVec n k =
      (1 - eigenvalue1D n k / γ) • sineVec n k := by
    rw [richardson_iterationMatrix_mulVec_sineVec, div_eq_inv_mul]
  rw [Chapter04.richardsonStep_eq_affine, Chapter04.affineStep_iterate_sub hfix,
    dotProduct_pow_mulVec hsymm heig]

/-- **Section 13.2.1** of [saad2003iterative], the closing display. With $\gamma = 4$ the Richardson
reduction factor is
$$\eta_k = 1 - \frac{\lambda_k}{4} = \cos^2\frac{\theta_k}{2}.$$
-/
theorem richardson_factor_eq_cos_sq (n : ℕ) (k : Fin n) :
    1 - eigenvalue1D n k / 4 = Real.cos (theta n k / 2) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (theta n k / 2)
  rw [eigenvalue1D]
  linarith

/-- **Section 13.2.1** of [saad2003iterative], slow convergence. With $\gamma = 4$, every Richardson
reduction factor satisfies
$$1 - \frac{\lambda_k}{4} \le 1 - \sin^2\frac{\pi}{2(n+1)},$$
with equality at $k = 1$.

Since $\sin(\pi/(2(n+1))) \approx \pi h/2$, the bound is $1 - O(h^2)$, and the iteration
converges slowly. The Lean statement gives the inequality for every $k$; the equality at $k = 1$
is not part of it. -/
theorem richardson_factor_le (n : ℕ) (k : Fin n) :
    1 - eigenvalue1D n k / 4 ≤ 1 - Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  have h := sin_sq_theta_div_two_ge n k
  rw [eigenvalue1D]
  linarith

/-- **Section 13.2.1** of [saad2003iterative], the smoothing property of Richardson's iteration.
With $\gamma = 4$, if $k > n/2$, then the reduction factor satisfies $1 - \lambda_k/4 \le 1/2$.
The bound does not depend on the mesh size.

With the $0$-based index `k`, the condition $k > n/2$ reads `n + 1 ≤ 2 * (k + 1)`. -/
theorem richardson_factor_le_half_of_oscillatory (n : ℕ) {k : Fin n}
    (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) : 1 - eigenvalue1D n k / 4 ≤ 1 / 2 := by
  have h := sin_sq_theta_div_two_ge_half n hk
  rw [eigenvalue1D]
  linarith

end Richardson

/-! ### Section 13.2.2: Weighted Jacobi, (13.17)–(13.25) -/

section WeightedJacobi

variable {n m : ℕ} {ω : ℝ}

/-- The weighted Jacobi iteration matrix of (13.19)–(13.20) of [saad2003iterative]: for a square
matrix $A$ with invertible diagonal $D$ and $\omega \neq 0$, the iteration operator of
`Matrix.jorSplitting`, whose matrix $M$ is $\omega^{-1} D$, is $J_\omega = I - \omega D^{-1} A$.

**Reading.** Requires nonzero omega for representation by a splitting.
-/
theorem jorSplitting_iterationOperator_eq {N : Type*} [Fintype N] [DecidableEq N]
    (A : Matrix N N ℝ) (h : IsUnit (diagPart A)) (hω : ω ≠ 0) :
    (jorSplitting A h hω).iterationOperator = 1 - ω • ((diagPart A)⁻¹ * A) := by
  have h1 : (jorSplitting A h hω).iterationOperator =
      1 - Ring.inverse (ω⁻¹ • diagPart A) * A := rfl
  have hinv : (ω⁻¹ • diagPart A)⁻¹ = ω • (diagPart A)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hω, one_smul,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp h)]
  rw [h1, ← nonsing_inv_eq_ringInverse, hinv, Matrix.smul_mul]

/-- If the diagonal of $A$ is $cI$ with $c \neq 0$, then the weighted Jacobi iteration matrix is
$J_\omega = I - (\omega/c) A$.

**Reading.** General scalar diagonal formula, with explicit invertibility and nonzero weights.
-/
private theorem jorSplitting_of_diagPart_eq {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℝ} {c : ℝ} (hc : c ≠ 0) (hA : diagPart A = c • 1)
    (h : IsUnit (diagPart A)) (hω : ω ≠ 0) :
    (jorSplitting A h hω).iterationOperator = 1 - (ω / c) • A := by
  have hinv : (c • (1 : Matrix N N ℝ))⁻¹ = c⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, Matrix.one_mul, one_smul]
  rw [jorSplitting_iterationOperator_eq A h hω, hA, hinv, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, ← div_eq_mul_inv]

/-- Since $D = 2I$ for the one-dimensional model matrix, weighted Jacobi on it has the iteration
matrix $J_\omega = I - (\omega/2) A$, for $\omega \neq 0$.

**Reading.** Uses omega nonzero for the built splitting.
-/
theorem jorSplitting_laplacian1D (n : ℕ) (hω : ω ≠ 0) :
    (jorSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n) hω).iterationOperator =
      1 - (ω / 2) • laplacian1D n :=
  jorSplitting_of_diagPart_eq two_ne_zero (diagPart_laplacian1D n) _ hω

/-- Since $D = 4I$ for the two-dimensional model matrix, weighted Jacobi on it has the iteration
matrix $J_\omega = I - (\omega/4) A$, for $\omega \neq 0$.

**Reading.** Uses omega nonzero for the built splitting.
-/
theorem jorSplitting_laplacian2D (n m : ℕ) (hω : ω ≠ 0) :
    (jorSplitting (laplacian2D n m) (isUnit_diagPart_laplacian2D n m) hω).iterationOperator =
      1 - (ω / 4) • laplacian2D n m :=
  jorSplitting_of_diagPart_eq (by norm_num) (diagPart_laplacian2D n m) _ hω

/-- **Equation (13.21)** of [saad2003iterative]. Let $\omega \neq 0$. The weighted Jacobi iteration
matrix $J_\omega$ of the one-dimensional model problem has the discrete sine vectors as
eigenvectors:
$$J_\omega w_k = \mu_k(\omega) \, w_k, \qquad \mu_k(\omega) = 1 -
  2\omega\sin^2\frac{k\pi}{2(n+1)}.$$

The hypothesis $\omega \neq 0$ is needed to define the splitting `Matrix.jorSplitting`.

**Reading.** Exact eigenrelation through nonzero-weight splitting.
-/
theorem equation_13_21 (n : ℕ) (hω : ω ≠ 0) (k : Fin n) :
    (jorSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n) hω).iterationOperator *ᵥ
        sineVec n k =
      (1 - 2 * ω * Real.sin (theta n k / 2) ^ 2) • sineVec n k := by
  rw [jorSplitting_laplacian1D n hω, sub_mulVec, one_mulVec, Matrix.smul_mulVec,
    laplacian1D_mulVec_sineVec, smul_smul, eigenvalue1D,
    show ω / 2 * (4 * Real.sin (theta n k / 2) ^ 2) = 2 * ω * Real.sin (theta n k / 2) ^ 2 by
      ring,
    sub_smul, one_smul]

/-- **Equation (13.21)** of [saad2003iterative] in two dimensions. Let $\omega \neq 0$. The weighted
Jacobi iteration matrix $J_\omega$ of the two-dimensional model problem has the eigenvectors
$w_k \otimes v_l$:
$$J_\omega (w_k \otimes v_l) = \mu_{k,l}(\omega) \, (w_k \otimes v_l), \qquad
  \mu_{k,l}(\omega) = 1 - \omega\left(\sin^2\frac{k\pi}{2(n+1)} +
  \sin^2\frac{l\pi}{2(m+1)}\right).$$

**Correction.** Correct product mode with nonzero-weight splitting.
-/
theorem equation_13_21_two (n m : ℕ) (hω : ω ≠ 0) (k : Fin n) (l : Fin m) :
    (jorSplitting (laplacian2D n m) (isUnit_diagPart_laplacian2D n m) hω).iterationOperator *ᵥ
        kroneckerVec (sineVec n k) (sineVec m l) =
      (1 - ω * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2)) •
        kroneckerVec (sineVec n k) (sineVec m l) := by
  rw [jorSplitting_laplacian2D n m hω, sub_mulVec, one_mulVec, Matrix.smul_mulVec,
    laplacian2D_mulVec_kroneckerVec, smul_smul, eigenvalue1D, eigenvalue1D,
    show ω / 4 * (4 * Real.sin (theta n k / 2) ^ 2 + 4 * Real.sin (theta m l / 2) ^ 2) =
        ω * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2) by ring,
    sub_smul, one_smul]

/-- **Equation (13.22)** of [saad2003iterative]. Let $0 < \omega \le 1$. Every eigenvalue of the
weighted Jacobi iteration matrix of the one-dimensional model problem satisfies
$$|\mu_k(\omega)| = \left|1 - 2\omega\sin^2\frac{\theta_k}{2}\right| \le 1 -
  2\omega\sin^2\frac{\pi}{2(n+1)} \approx 1 - \frac{\omega\pi^2h^2}{2}.$$

The book states that the spectral radius equals this bound, which is attained at $k = 1$; the
Lean statement gives the bound for every $k$. So $\omega = 1$ is the best choice for the
iteration as a solver, and every choice converges slowly.

**Scope.** The theorem gives the absolute-value estimate used in the following spectral-radius
discussion, for $0<\omega\le1$. The numbered display itself gives two signed bounds. -/
theorem equation_13_22 (n : ℕ) (hω0 : 0 < ω) (hω1 : ω ≤ 1) (k : Fin n) :
    |1 - 2 * ω * Real.sin (theta n k / 2) ^ 2| ≤
      1 - 2 * ω * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  have h1 := sin_sq_theta_div_two_ge n k
  have h2 := sin_sq_theta_div_two_le n k
  rw [abs_le]
  constructor <;> nlinarith

/-- **Equation (13.23)** of [saad2003iterative]. Let $\omega > 0$ and $k > n/2$. Then the weighted
Jacobi eigenvalue of the one-dimensional model problem lies in an interval that does not depend
on the mesh:
$$1 - 2\omega < \mu_k(\omega) = 1 - 2\omega\sin^2\frac{\theta_k}{2} \le 1 - \omega.$$

**Generalization.** The book prints the upper bound $1 - \omega/2$, which is true but not sharp.
On the oscillatory half, $\sin^2(\theta_k/2) \ge 1/2$, so $\mu_k(\omega) \le 1 - \omega$, which
is proved here. The conclusion of the book two lines later, that $\omega = 2/3$ gives
eigenvalues between $-1/3$ and $1/3$, needs $1 - \omega$; the bound $1 - \omega/2$ would give
$2/3$. The bound $1 - \omega/2$ is the correct one in two dimensions, where it is (13.25).

With the $0$-based index `k`, the condition $k > n/2$ reads `n + 1 ≤ 2 * (k + 1)`. -/
theorem weightedJacobi_eigenvalue_mem_Ioc (n : ℕ) (hω : 0 < ω) {k : Fin n}
    (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) :
    1 - 2 * ω * Real.sin (theta n k / 2) ^ 2 ∈ Set.Ioc (1 - 2 * ω) (1 - ω) := by
  have h1 := sin_sq_theta_div_two_ge_half n hk
  have h2 := sin_sq_theta_div_two_lt_one n k
  exact Set.mem_Ioc.2 ⟨by nlinarith, by nlinarith⟩

/-- **Section 13.2.2** of [saad2003iterative], the smoothing factor at $\omega = 1/2$ in one
dimension. If $k > n/2$, then
$$\left|1 - 2 \cdot \tfrac12 \sin^2\frac{\theta_k}{2}\right| \le \frac12.$$

**Generalization.** The book gives the smoothing factor $3/4$, which it reads off the bound
$1 - \omega/2$ of (13.23). The sharp value $1/2$ is proved here. -/
theorem smoothingFactor_one_half (n : ℕ) {k : Fin n} (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) :
    |1 - 2 * (1 / 2 : ℝ) * Real.sin (theta n k / 2) ^ 2| ≤ 1 / 2 := by
  have h := Set.mem_Ioc.1 (weightedJacobi_eigenvalue_mem_Ioc (ω := 1 / 2) n (by norm_num) hk)
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

/-- **Section 13.2.2** of [saad2003iterative], the optimal smoothing factor in one dimension. The
mesh-independent smoothing factor of weighted Jacobi is smallest at $\omega = 2/3$: if
$k > n/2$, then
$$\left|1 - 2 \cdot \tfrac23 \sin^2\frac{\theta_k}{2}\right| \le \frac13.$$

**Reading.** Proves upper bound 1/3 for chosen weight; no minimax optimality assertion.
-/
theorem smoothingFactor_two_thirds (n : ℕ) {k : Fin n} (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) :
    |1 - 2 * (2 / 3 : ℝ) * Real.sin (theta n k / 2) ^ 2| ≤ 1 / 3 := by
  have h := Set.mem_Ioc.1 (weightedJacobi_eigenvalue_mem_Ioc (ω := 2 / 3) n (by norm_num) hk)
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

/-- **Equation (13.25)** of [saad2003iterative]. Let $\omega > 0$. In two dimensions a mode $(k, l)$
is oscillatory when $k > n/2$ or $l > m/2$. For an oscillatory mode, the weighted Jacobi
eigenvalue satisfies
$$1 - 2\omega < \mu_{k,l}(\omega) = 1 - \omega\left(\sin^2\frac{\theta_k}{2} +
  \sin^2\frac{\theta_l}{2}\right) \le 1 - \frac{\omega}{2}.$$

Here the bound $1 - \omega/2$ of the book is sharp; the two ends have the same absolute value at
$\omega = 4/5$.

**Reading.** Defines high frequency in at least one coordinate and uses simple strict lower endpoint
without the sharper finite-grid additive term.
-/
theorem weightedJacobi2D_eigenvalue_mem_Ioc (n m : ℕ) (hω : 0 < ω) {k : Fin n} {l : Fin m}
    (hkl : n + 1 ≤ 2 * ((k : ℕ) + 1) ∨ m + 1 ≤ 2 * ((l : ℕ) + 1)) :
    1 - ω * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2) ∈
      Set.Ioc (1 - 2 * ω) (1 - ω / 2) := by
  have hk2 := sin_sq_theta_div_two_lt_one n k
  have hl2 := sin_sq_theta_div_two_lt_one m l
  have hk1 := sin_theta_div_two_pos n k
  have hl1 := sin_theta_div_two_pos m l
  have hhalf : 1 / 2 ≤ Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2 := by
    rcases hkl with h | h
    · nlinarith [sin_sq_theta_div_two_ge_half n h]
    · nlinarith [sin_sq_theta_div_two_ge_half m h]
  exact Set.mem_Ioc.2 ⟨by nlinarith, by nlinarith⟩

/-- **Equation (13.25)** of [saad2003iterative] and the sentence after it: in two dimensions, the
smoothing factor at $\omega = 1/2$ is $3/4$. If $k > n/2$ or $l > m/2$, then
$$\left|1 - \tfrac12\left(\sin^2\frac{\theta_k}{2} + \sin^2\frac{\theta_l}{2}\right)\right| \le
  \frac34.$$
-/
theorem smoothingFactor2D_one_half (n m : ℕ) {k : Fin n} {l : Fin m}
    (hkl : n + 1 ≤ 2 * ((k : ℕ) + 1) ∨ m + 1 ≤ 2 * ((l : ℕ) + 1)) :
    |1 - (1 / 2 : ℝ) * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2)| ≤
      3 / 4 := by
  have h := Set.mem_Ioc.1
    (weightedJacobi2D_eigenvalue_mem_Ioc (ω := 1 / 2) n m (by norm_num) hkl)
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

/-- **Equation (13.25)** of [saad2003iterative], the optimal smoothing factor in two dimensions. The
smoothing factor is smallest at $\omega = 4/5$, where the two ends $|1 - 2\omega|$ and
$1 - \omega/2$ of the interval of `SaadSparse.Chapter13.weightedJacobi2D_eigenvalue_mem_Ioc` are
both $3/5$: if $k > n/2$ or $l > m/2$, then
$$\left|1 - \tfrac45\left(\sin^2\frac{\theta_k}{2} + \sin^2\frac{\theta_l}{2}\right)\right| \le
  \frac35.$$

**Typo.** The book says that $\omega = 3/5$ gives a smoothing factor of $4/5$, which transposes
the two numbers: at $\omega = 3/5$ the factor is $7/10$, and $\omega = 4/5$ gives $3/5$. The
next sentence of the book, that $\omega = 4/5$ is the best choice, is right. -/
theorem smoothingFactor2D_four_fifths (n m : ℕ) {k : Fin n} {l : Fin m}
    (hkl : n + 1 ≤ 2 * ((k : ℕ) + 1) ∨ m + 1 ≤ 2 * ((l : ℕ) + 1)) :
    |1 - (4 / 5 : ℝ) * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2)| ≤
      3 / 5 := by
  have h := Set.mem_Ioc.1
    (weightedJacobi2D_eigenvalue_mem_Ioc (ω := 4 / 5) n m (by norm_num) hkl)
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

end WeightedJacobi

/-! ### Section 13.2.3: Gauss–Seidel, (13.26)–(13.29) -/

section GaussSeidel

variable {n : ℕ}

/-- **Section 13.2.3** of [saad2003iterative]. The **Gauss–Seidel iteration matrix**
$G = (D - E)^{-1} F$ of the one-dimensional model problem, where $A = D - E - F$ is the
splitting into the diagonal, the strictly lower and the strictly upper part.

The definition is the iteration operator of `Matrix.gaussSeidelSplitting` for the model matrix. -/
noncomputable def gaussSeidel1D (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (gaussSeidelSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n)).iterationOperator

/-- The Gauss–Seidel iteration matrix in the form (4.20) of [saad2003iterative]:
$G = I - (D - E)^{-1} A$, where $D - E$ is the lower bidiagonal part of the model matrix. -/
theorem gaussSeidel1D_eq (n : ℕ) :
    gaussSeidel1D n =
      1 - (diagPart (laplacian1D n) + strictLower (laplacian1D n))⁻¹ * laplacian1D n := by
  have h1 : gaussSeidel1D n =
      1 - Ring.inverse (diagPart (laplacian1D n) + strictLower (laplacian1D n)) *
        laplacian1D n := rfl
  rw [h1, nonsing_inv_eq_ringInverse]

/-- **Equation (13.29)** of [saad2003iterative]. The vector $u_k \in \mathbb{R}^n$ with the
components
$$(u_k)_j = (\cos\theta_k)^j \sin(j\theta_k), \qquad j = 1, \dots, n.$$

**Correction.** The book prints $|\cos\theta_k|^j$. With the absolute value, the vector is not
an eigenvector of the Gauss–Seidel iteration matrix whenever $\cos\theta_k < 0$: at $n = 2$ and
$k = 2$ it is proportional to $(2, -1)$, while the eigenvector is proportional to $(2, 1)$. The
derivation of Section 13.2.3 gives the signed power: the difference equation
$u_{j+1} = \lambda(2u_j - u_{j-1})$ forces the ratio to be $\cos\theta_k$ itself.

With the $0$-based index `j`, the component `j` is $(\cos\theta_k)^{j+1}\sin((j+1)\theta_k)$. -/
noncomputable def gaussSeidelVec (n : ℕ) (k : Fin n) : Fin n → ℝ :=
  fun j => Real.cos (theta n k) ^ ((j : ℕ) + 1) * Real.sin ((((j : ℕ) : ℝ) + 1) * theta n k)

/-- A vector on `Fin n` extended to all of $\mathbb{N}$ by the homogeneous Dirichlet boundary values
$0$, so that the three-term rows of the model matrix and of its triangular parts have one
formula. -/
private def pad (v : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => if h : j < n then v ⟨j, h⟩ else 0

/-- The extended vector is $0$ at the lower boundary. -/
private theorem pad_zero (v : Fin n → ℝ) : pad v 0 = 0 := rfl

/-- The value of the extended vector at a successor index $j + 1$ is $v_j$ if $j < n$, and $0$
otherwise. -/
private theorem pad_succ (v : Fin n → ℝ) (j : ℕ) :
    pad v (j + 1) = if h : j < n then v ⟨j, h⟩ else 0 := rfl

/-- The value of the extended vector at the index $i + 1$ of an interior point $i$ is $v_i$. -/
private theorem pad_val_succ (v : Fin n → ℝ) (i : Fin n) : pad v ((i : ℕ) + 1) = v i := by
  rw [pad_succ, dite_eq_left i.isLt]

/-- The extended vector is $0$ past the upper boundary, at every index $j > n$.

**Generalization.** Upper boundary and all larger natural indices extend by zero.
-/
private theorem pad_of_gt (v : Fin n → ℝ) {j : ℕ} (hj : n < j) : pad v j = 0 := by
  cases j with
  | zero => rfl
  | succ j => rw [pad_succ, dite_eq_right (by omega)]

/-- The sum $\sum_i [i = j] \, c \, v_i$ is $c$ times the extended vector at the index $j + 1$. -/
private theorem sum_ite_pad (c : ℝ) (v : Fin n → ℝ) (j : ℕ) :
    ∑ i : Fin n, (if (i : ℕ) = j then c * v i else 0) = c * pad v (j + 1) := by
  have h : ∀ i : Fin n, (if (i : ℕ) = j then c * v i else 0) =
      if (i : ℕ) = j then c * pad v ((i : ℕ) + 1) else 0 := by
    intro i; rw [pad_val_succ]
  rw [Finset.sum_congr rfl fun i _ => h i,
    Fin.sum_univ_eq_sum_range fun i => if i = j then c * pad v (i + 1) else 0,
    Finset.sum_ite_eq' (Finset.range n) j fun i => c * pad v (i + 1)]
  by_cases hj : j < n
  · rw [ite_eq_left (Finset.mem_range.2 hj)]
  · rw [ite_eq_right fun hmem => hj (Finset.mem_range.1 hmem), pad_of_gt v (by omega), mul_zero]

/-- The sum $\sum_i [i + 1 = j] \, c \, v_i$ is $c$ times the extended vector at the index $j$. -/
private theorem sum_ite_succ_pad (c : ℝ) (v : Fin n → ℝ) (j : ℕ) :
    ∑ i : Fin n, (if (i : ℕ) + 1 = j then c * v i else 0) = c * pad v j := by
  cases j with
  | zero => simp [pad_zero]
  | succ j =>
    have h : ∀ i : Fin n, ((i : ℕ) + 1 = j + 1) = ((i : ℕ) = j) := fun i => by simp
    simp only [h]
    exact sum_ite_pad c v j

/-- Each row of the one-dimensional model matrix, the first and the last row included, is
$(Av)_i = -v_{i-1} + 2v_i - v_{i+1}$ in terms of the extended vector. -/
private theorem laplacian1D_mulVec_apply (v : Fin n → ℝ) (i : Fin n) :
    (laplacian1D n *ᵥ v) i = -pad v (i : ℕ) + 2 * pad v ((i : ℕ) + 1) - pad v ((i : ℕ) + 2) := by
  have hsplit : ∀ j : Fin n, laplacian1D n i j * v j =
      (if (j : ℕ) + 1 = (i : ℕ) then -1 * v j else 0) +
        (if (j : ℕ) = (i : ℕ) then 2 * v j else 0) +
        (if (j : ℕ) = (i : ℕ) + 1 then -1 * v j else 0) := by
    intro j
    rw [laplacian1D_apply]
    split_ifs <;> first | (exfalso; omega) | ring
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_succ_pad, sum_ite_pad, sum_ite_pad,
    show (i : ℕ) + 1 + 1 = (i : ℕ) + 2 by omega]
  ring

/-- Each row of the lower bidiagonal factor $D - E$ of the Gauss–Seidel splitting is
$((D - E)v)_i = 2v_i - v_{i-1}$ in terms of the extended vector. -/
private theorem gsLower_mulVec_apply (v : Fin n → ℝ) (i : Fin n) :
    ((diagPart (laplacian1D n) + strictLower (laplacian1D n)) *ᵥ v) i =
      2 * pad v ((i : ℕ) + 1) - pad v (i : ℕ) := by
  have hsplit : ∀ j : Fin n,
      (diagPart (laplacian1D n) + strictLower (laplacian1D n)) i j * v j =
        (if (j : ℕ) + 1 = (i : ℕ) then -1 * v j else 0) +
          (if (j : ℕ) = (i : ℕ) then 2 * v j else 0) := by
    intro j
    simp only [Matrix.add_apply, diagPart_apply, strictLower_apply, laplacian1D_apply,
      ← Fin.val_eq_val, Fin.lt_def]
    split_ifs <;> first | (exfalso; omega) | ring
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, sum_ite_succ_pad, sum_ite_pad]
  ring

/-- The extended Gauss–Seidel vector is $(\cos\theta_k)^j \sin(j\theta_k)$ at every index
$j \le n + 1$: the values $0$ at both ends are $\sin 0 = 0$ and $\sin((n+1)\theta_k) = 0$.

**Reading.** Signed cosine expression on the padded domain, including zero endpoints.
-/
private theorem pad_gaussSeidelVec (n : ℕ) (k : Fin n) {j : ℕ} (hj : j ≤ n + 1) :
    pad (gaussSeidelVec n k) j =
      Real.cos (theta n k) ^ j * Real.sin ((j : ℝ) * theta n k) := by
  cases j with
  | zero => simp [pad_zero]
  | succ j =>
    rw [pad_succ]
    by_cases h : j < n
    · rw [dite_eq_left h]
      simp only [gaussSeidelVec]
      push_cast
      ring
    · rw [dite_eq_right h]
      have hjn : j = n := by omega
      subst hjn
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      have hrw : (((j : ℕ) : ℝ) + 1) * theta j k = (((k : ℕ) : ℤ) + 1 : ℤ) * π := by
        rw [theta]; field_simp; push_cast; ring
      push_cast
      rw [hrw, Real.sin_int_mul_pi, mul_zero]

/-- **Equation (13.29)** of [saad2003iterative]. The vector $u_k$ with components
$(\cos\theta_k)^j\sin(j\theta_k)$ satisfies
$$G u_k = \cos^2\theta_k \, u_k,$$
where $G$ is the Gauss–Seidel iteration matrix of the one-dimensional model problem.

At $\cos\theta_k = 0$, that is for $n$ odd and $k = (n+1)/2$, where the eigenvalue is $0$, the
vector $u_k$ is zero and the identity says nothing. There the eigenvector is $e_1$
(`SaadSparse.Chapter13.gaussSeidel1D_mulVec_single`). The vector $u_k$ is nonzero when
$\cos\theta_k \neq 0$ (`SaadSparse.Chapter13.gaussSeidelVec_ne_zero`).

**Reading.** Exact eigenrelation using signed formula, admitting zero vector when cosine is zero.
-/
theorem equation_13_29 (n : ℕ) (k : Fin n) :
    gaussSeidel1D n *ᵥ gaussSeidelVec n k = (Real.cos (theta n k) ^ 2) • gaussSeidelVec n k := by
  have key : laplacian1D n *ᵥ gaussSeidelVec n k =
      (1 - Real.cos (theta n k) ^ 2) •
        ((diagPart (laplacian1D n) + strictLower (laplacian1D n)) *ᵥ gaussSeidelVec n k) := by
    funext i
    have hi : (i : ℕ) < n := i.isLt
    rw [laplacian1D_mulVec_apply, Pi.smul_apply, gsLower_mulVec_apply, smul_eq_mul,
      pad_gaussSeidelVec n k (by omega), pad_gaussSeidelVec n k (by omega),
      pad_gaussSeidelVec n k (by omega)]
    have e0 : ((i : ℕ) : ℝ) * theta n k = (((i : ℕ) : ℝ) + 1) * theta n k - theta n k := by ring
    have e2 : (((i : ℕ) : ℝ) + 2) * theta n k =
        (((i : ℕ) : ℝ) + 1) * theta n k + theta n k := by ring
    push_cast
    rw [e0, e2, Real.sin_sub, Real.sin_add]
    ring
  rw [gaussSeidel1D_eq, sub_mulVec, one_mulVec, ← mulVec_mulVec, key, Matrix.mulVec_smul,
    nonsing_inv_mulVec_mulVec (isUnit_diagPart_add_strictLower (isUnit_diagPart_laplacian1D n))]
  module

/-- The Gauss–Seidel vector $u_k$ of (13.29) is nonzero if $\cos\theta_k \neq 0$. -/
theorem gaussSeidelVec_ne_zero (n : ℕ) {k : Fin n} (hk : Real.cos (theta n k) ≠ 0) :
    gaussSeidelVec n k ≠ 0 := by
  intro h
  have h0 : gaussSeidelVec n k ⟨0, k.pos⟩ = 0 := by rw [h]; rfl
  simp only [gaussSeidelVec] at h0
  norm_num at h0
  rcases h0 with h' | h'
  · exact hk h'
  · exact absurd h' (sin_theta_pos n k).ne'

/-- The degenerate case of (13.29) in Section 13.2.3 of [saad2003iterative]: for $n \ge 1$, the
first unit vector $e_1$ satisfies $G e_1 = 0$, so it is an eigenvector of the Gauss–Seidel
iteration matrix for the eigenvalue $0$. This replaces (13.29) at the eigenvalue $0$, where that
formula gives the zero vector.

**Reading.** Shows e₁ zero eigenvector for all positive sizes, including even n when no cosine is
zero.
-/
theorem gaussSeidel1D_mulVec_single (n : ℕ) (hn : 0 < n) :
    gaussSeidel1D n *ᵥ (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) = 0 := by
  have hkey : laplacian1D n *ᵥ (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) =
      (diagPart (laplacian1D n) + strictLower (laplacian1D n)) *ᵥ
        (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) := by
    funext i
    have h2 : pad (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ)) ((i : ℕ) + 2) = 0 := by
      rw [pad_succ]
      by_cases h : (i : ℕ) + 1 < n
      · rw [dite_eq_left h]
        exact Pi.single_eq_of_ne (fun hh => by simpa using congrArg Fin.val hh) 1
      · rw [dite_eq_right h]
    rw [laplacian1D_mulVec_apply, gsLower_mulVec_apply, h2]
    ring
  rw [gaussSeidel1D_eq, sub_mulVec, one_mulVec, ← mulVec_mulVec, hkey,
    nonsing_inv_mulVec_mulVec (isUnit_diagPart_add_strictLower (isUnit_diagPart_laplacian1D n)),
    sub_self]

/-- The Jacobi iteration matrix of the one-dimensional model problem is
$\operatorname{tridiag}(1/2, 0, 1/2)$, whose eigenvalues are the numbers $\cos\theta_k$. -/
theorem jacobiSplitting_laplacian1D_iterationOperator (n : ℕ) :
    (jacobiSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n)).iterationOperator =
      symmTridiagonalToeplitz n (1 / 2) 0 := by
  have h1 : (jacobiSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n)).iterationOperator =
      1 - Ring.inverse (diagPart (laplacian1D n)) * laplacian1D n := rfl
  have hinv : ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = (2 : ℝ)⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (two_ne_zero (α := ℝ)), Matrix.one_mul, one_smul]
  rw [h1, ← nonsing_inv_eq_ringInverse, diagPart_laplacian1D, hinv, Matrix.smul_mul,
    Matrix.one_mul]
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, laplacian1D_apply,
    symmTridiagonalToeplitz_apply', smul_eq_mul]
  simp only [← Fin.val_eq_val]
  split_ifs <;> ring

/-- **Section 13.2.3** of [saad2003iterative], the Jacobi spectrum. A real number $\mu$ is an
eigenvalue of the Jacobi iteration matrix $D^{-1}(E + F)$ of the one-dimensional model problem
if and only if $\mu = \cos\theta_k$ for some $k \in \{1, \dots, n\}$. -/
theorem jacobi1D_hasEigenvalue_iff (n : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue
        (toEuclideanLin
          (jacobiSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n)).iterationOperator)
        μ ↔
      ∃ k : Fin n, μ = Real.cos (theta n k) := by
  rw [jacobiSplitting_laplacian1D_iterationOperator, symmTridiagonalToeplitz_hasEigenvalue_iff]
  refine exists_congr fun k => ?_
  rw [theta]
  constructor <;> intro h <;> linarith

/-- If $Av = \mu v$ with $v \neq 0$ for a real matrix $A$, then $\mu$ is in the spectrum of $A$
viewed as a complex matrix. -/
private theorem ofReal_mem_spectrum_complexify_of_mulVec {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {v : Fin N → ℝ} {μ : ℝ} (hv : A *ᵥ v = μ • v) (hv0 : v ≠ 0) :
    ((μ : ℝ) : ℂ) ∈ spectrum ℂ (complexify A) := by
  rw [Matrix.ofReal_mem_spectrum_complexify_iff, ← Matrix.hasEigenvalue_toEuclideanLin_iff]
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := WithLp.toLp 2 v) ⟨Module.End.mem_eigenspace_iff.2 ?_, fun h => hv0 ?_⟩
  · change WithLp.toLp 2 (A *ᵥ v) = _
    rw [hv]
    rfl
  · simpa using congrArg WithLp.ofLp h

/-- **Section 13.2.3** of [saad2003iterative], the Gauss–Seidel spectrum. For every
$k \in \{1, \dots, n\}$, the number $\cos^2\theta_k$ is an eigenvalue of the Gauss–Seidel
iteration matrix $G$ of the one-dimensional model problem, as a complex matrix.

This is the argument of the book: the model matrix is tridiagonal, hence consistently ordered,
so Young's theorem (Theorem 4.16, `SaadSparse.Chapter04.theorem_4_16_mpr`) says that the
eigenvalues of SOR at $\omega = 1$ are the squares of the Jacobi eigenvalues, and these are the
numbers $\cos\theta_k$. The eigenvectors are given by (13.29),
`SaadSparse.Chapter13.equation_13_29`. The smallest of these eigenvalues are those with $k$ near
$n/2$, so Gauss–Seidel damps the middle of the spectrum fastest. This is not the same as damping
the oscillatory modes, and it is why Section 13.2.3 ends without a smoothing factor. The
statement is membership in `spectrum ℂ (complexify (gaussSeidel1D n))`.

**Scope.** These values belong to the spectrum. For even positive $n$ the zero eigenvalue also
occurs, as `SaadSparse.Chapter13.gaussSeidel1D_mulVec_single` shows. The signed vectors from
paired modes $k$ and $n+1-k$ in source indexing are negatives of each other, so this family
cannot give the basis suggested after (13.29). -/
theorem gaussSeidel_eigenvalues (n : ℕ) (k : Fin n) :
    ((Real.cos (theta n k) ^ 2 : ℝ) : ℂ) ∈ spectrum ℂ (complexify (gaussSeidel1D n)) := by
  by_cases hc : Real.cos (theta n k) = 0
  · have h0 : ((Real.cos (theta n k) ^ 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by rw [hc]; norm_num
    rw [h0]
    refine ofReal_mem_spectrum_complexify_of_mulVec
      (v := Pi.single ⟨0, k.pos⟩ 1) ?_ ?_
    · rw [gaussSeidel1D_mulVec_single n k.pos, zero_smul]
    · intro h
      simpa using congrFun h ⟨0, k.pos⟩
  · exact ofReal_mem_spectrum_complexify_of_mulVec (equation_13_29 n k)
      (gaussSeidelVec_ne_zero n hc)

end GaussSeidel

end SaadSparse.Chapter13
