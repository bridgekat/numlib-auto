/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.Frobenius
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Normed.Module.NormEquivalence
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.EpsilonNorm
import Numlib.LinearAlgebra.Matrix.Order
import Numlib.LinearAlgebra.Matrix.SVD

/-!
# Matrix norms induced by vector norms

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $1 \le p \le \infty$, and let
$A \in \mathbb{K}^{m \times n}$, where $m$ and $n$ also denote the numbers of rows and columns. The
matrix $A$ acts as the operator $x \mapsto Ax$ from $\mathbb{K}^n$ to $\mathbb{K}^m$, both with the
vector $p$-norm, and the operator norm
$$\|A\|_p = \sup_{x \neq 0} \frac{\|Ax\|_p}{\|x\|_p}$$
is the matrix norm induced by the vector $p$-norm ([saad2003iterative], §1.5, (1.7);
[quarteroni2000numerical], §1.11, (1.19)–(1.20)). More generally, a vector norm $p$ on
$\mathbb{K}^n$ and a vector norm $q$ on $\mathbb{K}^m$ (in these results, $p$ and $q$ are vector
norms, not exponents) induce the matrix norm
$\|A\|_{q,p} = \sup \{ q(Ax) : p(x) \le 1 \}$, and a matrix norm $N$ is consistent with $q$ and $p$
if $q(Ax) \le N(A)\, p(x)$ for all $A$ and $x$ ([quarteroni2000numerical], Definition 1.20). This
module proves that the induced norms are norms, consistent and submultiplicative, with $\|I\| = 1$;
that $\|A\|_1$ and $\|A\|_\infty$ are the largest absolute column and row sums; the comparison of
the $p$-norms with constants that depend on $m$ and $n$; the properties of the condition number
$\kappa_p(A) = \|A\|_p \|A^{-1}\|_p$; the bounds $\rho(A) \le N(A)$ for a consistent norm $N$ and
$\rho(A) = \inf \|A\|$ over the induced norms; and the Neumann bounds for $(I - A)^{-1}$ when
$\|A\| < 1$.

The module also collects facts about the spectral norm $\|A\|_2$ and the Frobenius norm $\|A\|_F$:
$\|A\|_2^2 = \rho(A^H A)$, $\|A\|_2 = \rho(A)$ for a normal matrix, the unitary invariance of both
norms, $\|A\|_2 \le \|A\|_F \le \sqrt{\operatorname{rank} A}\, \|A\|_2$,
$\|A\|_F^2 = \sum_i \sigma_i^2$, $\|A\|_2^2 \le \|A\|_1 \|A\|_\infty$, and
$\kappa_2(A) = \lambda_{\max} / \lambda_{\min}$ for a positive definite $A$. The last part shows
that the $\infty$-norm and the Frobenius norm are monotone in the absolute values of the entries,
which turns entrywise error bounds into normwise bounds.

## Main definitions

* `Matrix.lpCLM`: the operator $x \mapsto Ax$ from $\ell^p(\mathbb{K}^n)$ to $\ell^p(\mathbb{K}^m)$.
* `Matrix.lpOpNorm`: the induced matrix norm $\|A\|_p$, the operator norm of `Matrix.lpCLM`.
* `Matrix.condNumberLp`: the condition number $\kappa_p(A) = \|A\|_p \|A^{-1}\|_p$ of a square
  matrix, which is $0$ for a singular $A$.
* `Matrix.lpEquiv`: an invertible matrix as a continuous linear equivalence of
  $\ell^p(\mathbb{K}^n)$.
* `Matrix.IsConsistent`: a matrix norm $N$ is consistent with vector norms $q$ and $p$ if
  $q(Ax) \le N(A)\, p(x)$ for all $A$ and $x$.
* `Matrix.inducedNorm`: the matrix norm $\|A\|_{q,p} = \sup \{ q(Ax) : p(x) \le 1 \}$ induced by two
  vector norms.
* `Matrix.inducedSeminorm` and `Matrix.inducedAlgebraNorm`: the induced norm as a seminorm on
  rectangular matrices and as an algebra norm on square matrices.
* `Matrix.lpSeminorm`: the vector $p$-norm as a seminorm on $\mathbb{K}^n$.

## Main results

* `Matrix.lpOpNorm_mul_le`: the induced $p$-norms are submultiplicative,
  $\|AB\|_p \le \|A\|_p \|B\|_p$.
* `Matrix.lpOpNorm_one_eq_sup_sum_norm`: $\|A\|_1$ is the largest absolute column sum.
* `Matrix.lpOpNorm_top`: $\|A\|_\infty$ is the largest absolute row sum.
* `Matrix.lpOpNorm_submatrix_le`: a submatrix has at most the induced $p$-norm of the matrix.
* `Matrix.lpOpNorm_blockDiagonal'`: the induced $p$-norm of a block diagonal matrix is the largest
  induced $p$-norm of a block.
* `Matrix.complexSpectralRadius_le_lpOpNorm`: $\rho(A) \le \|A\|_p$ for a real square matrix.
* `Matrix.isUnit_lpCLM_iff` and `Matrix.ringInverse_lpCLM`: the operator $x \mapsto Ax$ is
  invertible if and only if $A$ is, and its ring inverse is the operator of $A^{-1}$.
* `Matrix.one_le_condNumberLp`: $\kappa_p(A) \ge 1$ for an invertible $A$.
* `Matrix.le_inducedNorm_mul`, `Matrix.isConsistent_inducedNorm`: the induced norm is consistent
  with the vector norms that induce it.
* `Matrix.inducedNorm_le_of_isConsistent`: the induced norm is the least consistent matrix norm.
* `Matrix.inducedNorm_eq_iSup_div` and `Matrix.exists_inducedNorm_eq`:
  $\|A\|_{q,p} = \sup_{x \neq 0} q(Ax)/p(x)$, and the supremum is attained on the unit sphere of
  $p$.
* `Matrix.inducedNorm_mul_le` and `Matrix.inducedNorm_one`: the induced norms are submultiplicative,
  and the identity has induced norm $1$.
* `Matrix.lpOpNorm_eq_inducedNorm`: $\|A\|_p$ is the norm induced by the vector $p$-norm.
* `Matrix.lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le` and
  `Matrix.lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge`: for $p \le q$,
  $\|A\|_p \le m^{1/p - 1/q} \|A\|_q$ and $\|A\|_q \le n^{1/p - 1/q} \|A\|_p$.
* `Matrix.condNumberLp_le_card_rpow_mul_condNumberLp`: the condition numbers $\kappa_p$ and
  $\kappa_q$ agree up to the factor $n^{2(1/p - 1/q)}$.
* `Matrix.spectralRadius_le_of_isConsistent` and `Matrix.complexSpectralRadius_le_of_isConsistent`:
  a matrix norm that is consistent with a vector norm is at least the spectral radius.
* `Matrix.exists_inducedNorm_le_spectralRadius_add` and
  `Matrix.exists_inducedNorm_le_complexSpectralRadius_add`: for every $\varepsilon > 0$ some induced
  norm has $\|A\| \le \rho(A) + \varepsilon$.
* `Matrix.complexSpectralRadius_eq_iInf_inducedNorm`: $\rho(A)$ is the infimum of the induced norms
  of $A$.
* `Matrix.exists_isConsistent_of_mul_le`: a submultiplicative matrix norm $N$ is consistent with the
  vector norm $x \mapsto N(x y^H)$.
* `Matrix.inducedNorm_inv_one_sub_le` and `Matrix.one_div_one_add_le_inducedNorm_inv_one_sub`: if
  $\|A\| < 1$, then $1/(1 + \|A\|) \le \|(I - A)^{-1}\| \le 1/(1 - \|A\|)$.
* `Matrix.hasSum_pow_of_inducedNorm_lt_one`: if $\|F\| < 1$, then $\sum_k F^k = (I - F)^{-1}$.
* `Matrix.l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self`: $\|A\|_2^2 = \rho(A^H A)$.
* `Matrix.l2_opNorm_eq_spectralRadius_of_isStarNormal`: $\|A\|_2 = \rho(A)$ for a normal complex
  matrix.
* `Matrix.l2_opNorm_unitary_mul_mul_unitary` and `Matrix.frobenius_norm_unitary_mul_mul_unitary`:
  $\|UAV\| = \|A\|$ for unitary $U$ and $V$, in the spectral and the Frobenius norm.
* `Matrix.l2_opNorm_le_frobenius_norm` and `Matrix.frobenius_norm_le_sqrt_rank_mul_l2_opNorm`:
  $\|A\|_2 \le \|A\|_F \le \sqrt{\operatorname{rank} A}\, \|A\|_2$.
* `Matrix.frobenius_norm_sq_eq_sum_sq_colSingularValues`: $\|A\|_F^2$ is the sum of the squared
  singular values.
* `Matrix.frobenius_norm_mul_le_lpOpNorm_two_mul`: $\|XY\|_F \le \|X\|_2 \|Y\|_F$.
* `Matrix.l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm`: $\|A\|_2^2 \le \|A\|_1 \|A\|_\infty$.
* `Matrix.linfty_opNorm_le_of_abs_entrywiseLE` and `Matrix.frobenius_norm_le_of_abs_entrywiseLE`:
  $|A| \le |B|$ entrywise implies $\|A\|_\infty \le \|B\|_\infty$ and $\|A\|_F \le \|B\|_F$.
* `Matrix.PosDef.condNumber_l2_eq_div_eigenvalues`: $\kappa_2(A) = \lambda_{\max} / \lambda_{\min}$
  for a positive definite $A$.

## Implementation notes

* Mathlib provides the induced matrix norm only for $p = \infty$ (`Matrix.Norms.Operator`) and
  $p = 2$ (`Matrix.Norms.L2Operator`), each as a scoped `NormedAddCommGroup` instance. A further
  instance on the same type is not possible for the other values of $p$, so the general induced norm
  is the function `Matrix.lpOpNorm p A` and not an instance. `Matrix.lpOpNorm_two` and
  `Matrix.lpOpNorm_top` identify it with the two scoped norms.
* The matrices are rectangular, `A : Matrix m n 𝕜`, wherever the statement makes sense. The results
  about the operator algebra ($\|I\| = 1$, invertibility, the condition number) are for square
  matrices.
* A vector norm on $\mathbb{K}^n$ is a `Seminorm 𝕜 (n → 𝕜)` together with the hypothesis
  `∀ x, p x = 0 → x = 0` that it is definite, as in `Numlib.Analysis.Normed.Module.NormEquivalence`
  and `Numlib.LinearAlgebra.Matrix.EpsilonNorm`. The induced norm `Matrix.inducedNorm q p` is a
  function `Matrix m n 𝕜 → ℝ`. It is bundled on demand as `Matrix.inducedSeminorm` or
  `Matrix.inducedAlgebraNorm`, the form that `spectralRadius_le_algebraNorm` and the `AlgebraNorm`
  lemmas of `Numlib.Analysis.Normed.Algebra.SpectralRadius` take.
* The supremum in `Matrix.inducedNorm` is over the closed unit ball of $p$, not the unit sphere, so
  that the index type is nonempty: it contains $0$.
* Mathlib's matrix inverse is $A^{-1} = 0$ for a singular $A$, so `Matrix.condNumberLp p A = 0`
  then. This agrees with the value of `NormedRing.condNumber` at a non-unit, and
  `Matrix.condNumberLp_eq_condNumber` identifies $\kappa_p(A)$ with
  `NormedRing.condNumber (Matrix.lpCLM p A)`.
* The spectral radius of a real matrix is the spectral radius of its complexification,
  `Matrix.complexSpectralRadius` of `Numlib.LinearAlgebra.Matrix.Complexify`. For `𝕜 = ℝ`,
  `spectralRadius ℝ A` is the spectral radius of the real spectrum.
* In the sections on the spectral norm, the Frobenius norm and the $\infty$-norm, `‖A‖` is the norm
  of the scoped instance `Matrix.Norms.L2Operator`, `Matrix.Norms.Frobenius` or
  `Matrix.Norms.Operator`. Where the Frobenius instance is in scope, the spectral norm is written
  `Matrix.lpOpNorm 2`.
* The case $p = 2$ of `Matrix.lpOpNorm_submatrix_le` for the scoped spectral norm is
  `Matrix.l2_opNorm_submatrix_le` in `Numlib.Analysis.Matrix.SpectralNorm`.
* The basic identities of the Frobenius norm are in `Numlib.Analysis.Matrix.Frobenius`: the trace
  form $\|A\|_F^2 = \operatorname{tr}(A^H A)$ of (1.18) of [quarteroni2000numerical]
  (`Matrix.frobenius_norm_sq_eq_trace`), its row and column forms
  (`Matrix.frobenius_norm_sq_eq_sum_norm_sq_row`, `Matrix.frobenius_norm_sq_eq_sum_norm_sq_col`),
  and the bound $|a_{ij}| \le \|A\|_F$ (`Matrix.norm_entry_le_frobenius_norm`).
-/

open Finset

open scoped ENNReal NNReal NormedRing

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-! ### The operator $x \mapsto Ax$ on $\ell^p$ -/

section CLM

variable [DecidableEq n]

/-- Let $1 \le p \le \infty$ and $A \in \mathbb{K}^{m \times n}$. This is the continuous linear
operator $x \mapsto Ax$ from $\mathbb{K}^n$ to $\mathbb{K}^m$, both with the vector $p$-norm.
Its operator norm is the induced matrix norm $\|A\|_p$, `Matrix.lpOpNorm`.

The spaces are `PiLp p (fun _ : n => 𝕜)` and `PiLp p (fun _ : m => 𝕜)`, and the operator is
`Matrix.toLpLin p p A` made continuous. -/
noncomputable def lpCLM (A : Matrix m n 𝕜) :
    PiLp p (fun _ : n => 𝕜) →L[𝕜] PiLp p (fun _ : m => 𝕜) :=
  LinearMap.toContinuousLinearMap (toLpLin p p A)

/-- The operator `Matrix.lpCLM p A` maps $x$ to $Ax$. -/
@[simp]
theorem lpCLM_apply (A : Matrix m n 𝕜) (x : PiLp p (fun _ : n => 𝕜)) :
    lpCLM p A x = WithLp.toLp p (A *ᵥ WithLp.ofLp x) := rfl

/-- The operator of the identity matrix is the identity operator. -/
theorem lpCLM_one : lpCLM p (1 : Matrix n n 𝕜) = 1 := by
  ext x i; simp

/-- Matrix multiplication is composition of the operators: for $A \in \mathbb{K}^{l \times m}$ and
$B \in \mathbb{K}^{m \times n}$, the operator of $AB$ is the operator of $A$ composed with the
operator of $B$. -/
theorem lpCLM_mul_eq_comp [DecidableEq m] (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    lpCLM p (A * B) = (lpCLM p A).comp (lpCLM p B) := by
  ext x i; simp [← mulVec_mulVec]

/-- For square matrices $A$ and $B$, the operator of $AB$ is the product of the operators of $A$ and
$B$ in the operator algebra of $\ell^p(\mathbb{K}^n)$. This is the square case of
`Matrix.lpCLM_mul_eq_comp`. -/
theorem lpCLM_mul (A B : Matrix n n 𝕜) : lpCLM p (A * B) = lpCLM p A * lpCLM p B :=
  lpCLM_mul_eq_comp p A B

/-- The operator of $A + B$ is the sum of the operators of $A$ and $B$. -/
theorem lpCLM_add (A B : Matrix m n 𝕜) : lpCLM p (A + B) = lpCLM p A + lpCLM p B := by
  ext x i; simp [add_mulVec]

/-- The operator of $cA$ is $c$ times the operator of $A$. -/
theorem lpCLM_smul (c : 𝕜) (A : Matrix m n 𝕜) : lpCLM p (c • A) = c • lpCLM p A := by
  ext x i; simp [smul_mulVec]

/-- The operator of the zero matrix is zero. -/
@[simp]
theorem lpCLM_zero : lpCLM p (0 : Matrix m n 𝕜) = 0 := by
  ext x i; simp

/-- The operator of $-A$ is the negative of the operator of $A$. -/
theorem lpCLM_neg (A : Matrix m n 𝕜) : lpCLM p (-A) = -lpCLM p A := by
  ext x i; simp [neg_mulVec]

/-- The operator of $A - B$ is the difference of the operators of $A$ and $B$. -/
theorem lpCLM_sub (A B : Matrix m n 𝕜) : lpCLM p (A - B) = lpCLM p A - lpCLM p B := by
  ext x i; simp [sub_mulVec]

/-- The map $A \mapsto (x \mapsto Ax)$ as a linear equivalence from $\mathbb{K}^{m \times n}$ onto
the continuous linear operators from $\ell^p(\mathbb{K}^n)$ to $\ell^p(\mathbb{K}^m)$: every
such operator is the operator of exactly one matrix. -/
noncomputable def lpCLMEquiv :
    Matrix m n 𝕜 ≃ₗ[𝕜] (PiLp p (fun _ : n => 𝕜) →L[𝕜] PiLp p (fun _ : m => 𝕜)) :=
  (toLpLin p p).trans LinearMap.toContinuousLinearMap

/-- The linear equivalence `Matrix.lpCLMEquiv p` maps $A$ to the operator `Matrix.lpCLM p A`. -/
@[simp]
theorem lpCLMEquiv_apply (A : Matrix m n 𝕜) : lpCLMEquiv p A = lpCLM p A := rfl

/-! ### The induced norm $\|A\|_p$ -/

/-- Let $1 \le p \le \infty$ and $A \in \mathbb{K}^{m \times n}$. The **matrix norm induced by the
vector $p$-norm** is
$$\|A\|_p = \sup_{x \neq 0} \frac{\|Ax\|_p}{\|x\|_p},$$
the operator norm of $x \mapsto Ax$ from $\ell^p(\mathbb{K}^n)$ to $\ell^p(\mathbb{K}^m)$. This
is (1.7) of [saad2003iterative], §1.5, with equal exponents on both sides, and (1.19) of
[quarteroni2000numerical], §1.11.

The definition is the operator norm of `Matrix.lpCLM p A`. -/
noncomputable def lpOpNorm (A : Matrix m n 𝕜) : ℝ := ‖lpCLM p A‖

/-- The zero matrix has induced $p$-norm $0$. -/
@[simp]
theorem lpOpNorm_zero : lpOpNorm p (0 : Matrix m n 𝕜) = 0 := by
  rw [lpOpNorm, lpCLM_zero, norm_zero]

/-- Let $1 \le p \le \infty$, let $A \in \mathbb{K}^{n \times n}$, and let $\mu \in \mathbb{K}$ be
an eigenvalue of $A$ with eigenvector $x \neq 0$, that is, $Ax = \mu x$. Then
$|\mu| \le \|A\|_p$. -/
theorem norm_le_lpOpNorm_of_mulVec_eq_smul {A : Matrix n n 𝕜} {μ : 𝕜} {x : n → 𝕜} (hx : x ≠ 0)
    (h : A *ᵥ x = μ • x) : ‖μ‖ ≤ lpOpNorm p A := by
  have hle := (lpCLM p A).le_opNorm (WithLp.toLp p x)
  rw [lpCLM_apply, WithLp.ofLp_toLp, h, WithLp.toLp_smul, norm_smul] at hle
  exact le_of_mul_le_mul_right hle (norm_pos_iff.2 (by simpa using hx))

/-- The induced $p$-norm is nonnegative. -/
theorem lpOpNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ lpOpNorm p A := norm_nonneg _

/-- The induced $p$-norm is absolutely homogeneous: $\|cA\|_p = |c|\, \|A\|_p$ for
$c \in \mathbb{K}$. -/
theorem lpOpNorm_smul (c : 𝕜) (A : Matrix m n 𝕜) : lpOpNorm p (c • A) = ‖c‖ * lpOpNorm p A := by
  rw [lpOpNorm, lpCLM_smul, norm_smul, lpOpNorm]

/-- The induced $p$-norm of $-A$ is that of $A$. -/
@[simp]
theorem lpOpNorm_neg (A : Matrix m n 𝕜) : lpOpNorm p (-A) = lpOpNorm p A := by
  rw [lpOpNorm, lpCLM_neg, norm_neg, lpOpNorm]

/-- The triangle inequality for the induced $p$-norm: $\|A + B\|_p \le \|A\|_p + \|B\|_p$. -/
theorem lpOpNorm_add_le (A B : Matrix m n 𝕜) :
    lpOpNorm p (A + B) ≤ lpOpNorm p A + lpOpNorm p B := by
  rw [lpOpNorm, lpCLM_add]
  exact norm_add_le _ _

/-- Let $1 \le p \le \infty$, $A \in \mathbb{K}^{l \times m}$ and $B \in \mathbb{K}^{m \times n}$.
The induced $p$-norm is submultiplicative:
$$\|AB\|_p \le \|A\|_p \|B\|_p.$$
This is stated in [quarteroni2000numerical], §1.11, after Theorem 1.3. -/
theorem lpOpNorm_mul_le [DecidableEq m] (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    lpOpNorm p (A * B) ≤ lpOpNorm p A * lpOpNorm p B := by
  rw [lpOpNorm, lpCLM_mul_eq_comp]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- For a square matrix $A$ and $k \in \mathbb{N}$, $\|A^k\|_p \le \|A\|_p^k$. -/
theorem lpOpNorm_pow_le (A : Matrix n n 𝕜) (k : ℕ) : lpOpNorm p (A ^ k) ≤ lpOpNorm p A ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, lpOpNorm, lpCLM_one]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (lpOpNorm_mul_le p _ _).trans (mul_le_mul_of_nonneg_right ih (lpOpNorm_nonneg _ _))

open scoped Matrix.Norms.L2Operator in
/-- For $p = 2$, the induced norm $\|A\|_2$ is the spectral norm of Mathlib's scoped instance
`Matrix.Norms.L2Operator`. -/
theorem lpOpNorm_two (A : Matrix m n 𝕜) : lpOpNorm 2 A = ‖A‖ :=
  (l2_opNorm_def A).symm

/-- Let $A \in \mathbb{K}^{m \times n}$. The induced $1$-norm is the largest absolute column sum:
$$\|A\|_1 = \max_j \sum_i |a_{ij}|,$$
and $\|A\|_1 = 0$ if $A$ has no columns. This is (1.13) of [saad2003iterative], §1.5, and the
"column sum norm" of [quarteroni2000numerical], §1.11.

The maximum is `Finset.sup` over the columns in `ℝ≥0`, which is $0$ for an empty index set.
Mathlib has only the row-sum formula for the $\infty$-norm (`Matrix.linfty_opNorm_def`), so the
proof uses the definition of the operator norm on `PiLp 1`: the upper bound is the triangle
inequality column by column, and the bound is attained at the standard basis vector of the
largest column. -/
theorem lpOpNorm_one_eq_sup_sum_norm (A : Matrix m n 𝕜) :
    lpOpNorm 1 A = ↑(univ.sup fun j => ∑ i, ‖A i j‖₊) := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _
      (univ.sup fun j => ∑ i, ‖A i j‖₊).coe_nonneg fun x => ?_
    rw [lpCLM_apply, PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
    calc ∑ i, ‖(A *ᵥ WithLp.ofLp x) i‖
        ≤ ∑ i, ∑ j, ‖A i j‖ * ‖WithLp.ofLp x j‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mulVec_apply_eq_sum]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_mul_le _ _)
      _ = ∑ j, (∑ i, ‖A i j‖) * ‖WithLp.ofLp x j‖ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ j, ((univ.sup fun j => ∑ i, ‖A i j‖₊ : ℝ≥0) : ℝ) * ‖WithLp.ofLp x j‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          gcongr
          have h : (∑ i, ‖A i j‖₊) ≤ univ.sup fun j => ∑ i, ‖A i j‖₊ :=
            Finset.le_sup (f := fun j => ∑ i, ‖A i j‖₊) (mem_univ j)
          have h' := NNReal.coe_le_coe.mpr h
          push_cast at h'
          exact h'
      _ = _ := by rw [Finset.mul_sum]
  · have key : ∀ j : n, ((∑ i, ‖A i j‖₊ : ℝ≥0) : ℝ) ≤ ‖lpCLM 1 A‖ := by
      intro j
      have hx : ‖(WithLp.toLp 1 (Pi.single j (1 : 𝕜)) : PiLp 1 fun _ : n => 𝕜)‖ = 1 := by
        rw [PiLp.norm_eq_of_L1]
        simp [Pi.single_apply, apply_ite (‖·‖ : 𝕜 → ℝ), Finset.sum_ite_eq']
      have hle := (lpCLM 1 A).le_opNorm
        (WithLp.toLp 1 (Pi.single j (1 : 𝕜)) : PiLp 1 fun _ : n => 𝕜)
      rw [hx, mul_one, lpCLM_apply, PiLp.norm_eq_of_L1] at hle
      simp only [mulVec_single_one, col_apply] at hle
      push_cast
      exact hle
    have hsup : (univ.sup fun j => ∑ i, ‖A i j‖₊) ≤ ‖lpCLM 1 A‖₊ :=
      Finset.sup_le fun j _ => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact key j
    rw [lpOpNorm, ← coe_nnnorm]
    exact_mod_cast hsup

/-- Let $A \in \mathbb{K}^{m \times n}$ and $C \ge 0$. If every absolute column sum satisfies
$\sum_i |a_{ij}| \le C$, then $\|A\|_1 \le C$. -/
theorem lpOpNorm_one_le_of_forall_sum_le {A : Matrix m n 𝕜} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j, ∑ i, ‖A i j‖ ≤ C) : lpOpNorm 1 A ≤ C := by
  rw [lpOpNorm_one_eq_sup_sum_norm]
  have hle : (univ.sup fun j => ∑ i, ‖A i j‖₊) ≤ ⟨C, hC⟩ := Finset.sup_le fun j _ =>
    NNReal.coe_le_coe.mp (show ((∑ i, ‖A i j‖₊ : NNReal) : ℝ) ≤ C by push_cast; exact h j)
  exact NNReal.coe_le_coe.mpr hle

/-- Let $1 \le p \le \infty$ and $A \in \mathbb{R}^{n \times n}$. The spectral radius of $A$ is at
most its induced $p$-norm:
$$\rho(A) \le \|A\|_p,$$
where $\rho(A)$ is the spectral radius of $A$ as a complex matrix. This is the case of the
induced norms in [saad2003iterative], §1.5, and in Theorem 1.4 of [quarteroni2000numerical].

The spectral radius is `Matrix.complexSpectralRadius A`, a value in `ℝ≥0∞`. The induced norms
are submultiplicative, absolutely homogeneous and positive definite, which are the three
hypotheses of `Matrix.complexSpectralRadius_le_of_norm`. Only positive definiteness needs an
argument, through the columns $Ae_j$. -/
theorem complexSpectralRadius_le_lpOpNorm (A : Matrix n n ℝ) :
    A.complexSpectralRadius ≤ ENNReal.ofReal (lpOpNorm p A) := by
  have hzero : ∀ B : Matrix n n ℝ, ‖lpCLM p B‖₊ = 0 → B = 0 := by
    intro B hB
    have h : lpCLM p B = 0 := by simpa using hB
    ext i j
    have h2 : (lpCLM p B) (WithLp.toLp p (Pi.single j (1 : ℝ))) = 0 := by simp [h]
    have h3 := congrArg (fun y : PiLp p (fun _ : n => ℝ) => (WithLp.ofLp y : n → ℝ) i) h2
    simpa [mulVec_single_one, col_apply] using h3
  have hle := complexSpectralRadius_le_of_norm (fun B : Matrix n n ℝ => ‖lpCLM p B‖₊) A
    (fun B C => by rw [lpCLM_mul]; exact nnnorm_mul_le _ _)
    (fun r B => by rw [lpCLM_smul]; exact nnnorm_smul _ _) hzero
  rwa [lpOpNorm, ofReal_norm, enorm_eq_nnnorm]

end CLM

/-! ### Submatrices -/

section Submatrix

variable [DecidableEq n]

/-- Let $1 \le p \le \infty$, let $A \in \mathbb{K}^{m \times n}$, and let $f$ and $g$ be injective
maps into the row and the column indices of $A$. The submatrix $A(f, g)$ with the entries
$a_{f(i) g(j)}$ satisfies
$$\|A(f, g)\|_p \le \|A\|_p.$$
This is (2.3.13) and Problem P2.3.2 of [golub2013matrix].

The submatrix is `A.submatrix f g`. The proof applies $A$ to the vector extended by zero along
$g$ (`PiLp.norm_toLp_extend`) and drops the coordinates outside the range of $f$
(`PiLp.norm_toLp_comp_le`). -/
theorem lpOpNorm_submatrix_le {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (A : Matrix m n 𝕜) {f : m' → m} (hf : Function.Injective f) {g : n' → n}
    (hg : Function.Injective g) : lpOpNorm p (A.submatrix f g) ≤ lpOpNorm p A := by
  refine ContinuousLinearMap.opNorm_le_bound _ (lpOpNorm_nonneg p A) fun x => ?_
  rw [lpCLM_apply]
  exact norm_toLp_submatrix_mulVec_le p hf hg (C := lpOpNorm p A)
    (fun y => (lpCLM p A).le_opNorm (WithLp.toLp p y)) (WithLp.ofLp x)

end Submatrix

/-! ### Block diagonal and diagonal matrices -/

section BlockDiagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m' n' : ι → Type*} [∀ i, Fintype (m' i)]
  [∀ i, Fintype (n' i)] [∀ i, DecidableEq (n' i)]

/-- Let $1 \le p \le \infty$, and let $M_i$ be a family of rectangular matrices indexed by a finite
set $\iota$. The induced $p$-norm of the block diagonal matrix with the blocks $M_i$ is the
largest induced $p$-norm of a block:
$$\|\operatorname{diag}(M_1, \dots, M_k)\|_p = \max_i \|M_i\|_p,$$
and it is $0$ if $\iota$ is empty.

The block diagonal matrix is `Matrix.blockDiagonal' M`, and the maximum is the real supremum
`⨆ i`. The lower bound is `Matrix.lpOpNorm_submatrix_le` for each block. The upper bound reads
the $\ell^p$ norm on the sigma type block by block (`LinearIsometryEquiv.piLpCurry`). -/
theorem lpOpNorm_blockDiagonal' (M : ∀ i, Matrix (m' i) (n' i) 𝕜) :
    lpOpNorm p (blockDiagonal' M) = ⨆ i, lpOpNorm p (M i) := by
  have hS : 0 ≤ ⨆ i, lpOpNorm p (M i) := Real.iSup_nonneg fun i => lpOpNorm_nonneg p _
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hS fun x => ?_)
    (Real.iSup_le (fun i => ?_) (lpOpNorm_nonneg p _))
  · rw [lpCLM_apply, ← (LinearIsometryEquiv.piLpCurry 𝕜 p fun i (_ : m' i) => 𝕜).norm_map,
      ← (LinearIsometryEquiv.piLpCurry 𝕜 p fun i (_ : n' i) => 𝕜).norm_map x,
      LinearIsometryEquiv.piLpCurry_apply, LinearIsometryEquiv.piLpCurry_apply]
    refine PiLp.norm_toLp_le_mul_norm_toLp p hS fun i => ?_
    have hx : (WithLp.toLp p (Sigma.curry (γ := fun _ _ => 𝕜) (WithLp.ofLp (WithLp.toLp p
        (blockDiagonal' M *ᵥ WithLp.ofLp x))) i) : PiLp p fun _ : m' i => 𝕜)
        = lpCLM p (M i) (WithLp.toLp p fun b => WithLp.ofLp x ⟨i, b⟩) := by
      ext a
      simp [Sigma.curry, blockDiagonal'_mulVec]
    rw [hx]
    calc ‖lpCLM p (M i) (WithLp.toLp p fun b => WithLp.ofLp x ⟨i, b⟩)‖
        ≤ lpOpNorm p (M i) * ‖(WithLp.toLp p fun b => WithLp.ofLp x ⟨i, b⟩
          : PiLp p fun _ : n' i => 𝕜)‖ := (lpCLM p (M i)).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (le_ciSup (Finite.bddAbove_range fun i => lpOpNorm p (M i)) i) (norm_nonneg _)
  · have h := lpOpNorm_submatrix_le p (blockDiagonal' M) (sigma_mk_injective (i := i))
      (sigma_mk_injective (i := i))
    rwa [blockDiagonal'_submatrix_sigma_mk] at h

/-- Let $1 \le p \le \infty$ and $d \in \mathbb{K}^n$. The induced $p$-norm of the diagonal matrix
with the diagonal $d$ is the largest modulus of a diagonal entry:
$$\|\operatorname{diag}(d)\|_p = \max_i |d_i|,$$
and it is $0$ if $n = 0$.

Mathlib has the cases $p = 2$ (`Matrix.l2_opNorm_diagonal`) and $p = \infty$
(`Matrix.linfty_opNorm_diagonal`). -/
theorem lpOpNorm_diagonal [DecidableEq n] (d : n → 𝕜) :
    lpOpNorm p (diagonal d) = ⨆ i, ‖d i‖ := by
  have hS : 0 ≤ ⨆ i, ‖d i‖ := Real.iSup_nonneg fun i => norm_nonneg _
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hS fun x => ?_)
    (Real.iSup_le (fun i => ?_) (lpOpNorm_nonneg p _))
  · rw [lpCLM_apply]
    refine PiLp.norm_toLp_le_mul_norm_toLp p hS fun i => ?_
    rw [mulVec_diagonal, norm_mul]
    exact mul_le_mul_of_nonneg_right (le_ciSup (Finite.bddAbove_range fun i => ‖d i‖) i)
      (norm_nonneg _)
  · have h := (lpCLM p (diagonal d)).le_opNorm (PiLp.single p i (1 : 𝕜))
    rwa [lpCLM_apply, PiLp.norm_single, norm_one, mul_one, ← lpOpNorm, PiLp.ofLp_single,
      diagonal_mulVec_single, mul_one, PiLp.toLp_single, PiLp.norm_single] at h

/-- Let $d \in \mathbb{K}^n$ and $c \ge 0$. If $|d_i| \le c$ for every $i$, then
$\|\operatorname{diag}(d)\|_p \le c$. -/
theorem lpOpNorm_diagonal_le [DecidableEq n] {d : n → 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (hd : ∀ i, ‖d i‖ ≤ c) : lpOpNorm p (diagonal d) ≤ c := by
  rw [lpOpNorm_diagonal]
  exact Real.iSup_le hd hc

open scoped Matrix.Norms.L2Operator in
/-- Let $M_i$ be a family of rectangular matrices indexed by a finite set $\iota$. The spectral norm
of the block diagonal matrix with the blocks $M_i$ is the largest spectral norm of a block:
$$\|\operatorname{diag}(M_1, \dots, M_k)\|_2 = \max_i \|M_i\|_2,$$
and it is $0$ if $\iota$ is empty.

The norm is the scoped instance `Matrix.Norms.L2Operator`. This is
`Matrix.lpOpNorm_blockDiagonal'` at $p = 2$. -/
theorem l2_opNorm_blockDiagonal' (M : ∀ i, Matrix (m' i) (n' i) 𝕜) :
    ‖blockDiagonal' M‖ = ⨆ i, ‖M i‖ := by
  simpa only [lpOpNorm_two] using lpOpNorm_blockDiagonal' 2 M

end BlockDiagonal

/-! ### Invertible matrices, and the condition number $\kappa_p(A)$ -/

section Square

variable [DecidableEq n]

/-- Let $1 \le p \le \infty$ and $A \in \mathbb{K}^{n \times n}$. The **condition number** of $A$ in
the induced $p$-norm is
$$\kappa_p(A) = \|A\|_p \|A^{-1}\|_p.$$
If $A$ is singular, then $\kappa_p(A) = 0$. This is the condition number of [saad2003iterative],
§1.13.2, and (3.4) of [quarteroni2000numerical], §3.1.1.

Mathlib's inverse `A⁻¹` is $0$ for a singular $A$, which gives the value $0$. This agrees with
the value of `NormedRing.condNumber` at a non-unit. -/
noncomputable def condNumberLp (A : Matrix n n 𝕜) : ℝ :=
  lpOpNorm p A * lpOpNorm p A⁻¹

/-- Let $1 \le p \le \infty$ and let $A \in \mathbb{K}^{n \times n}$ be invertible. This is
$x \mapsto Ax$ as a continuous linear equivalence of $\ell^p(\mathbb{K}^n)$, with the inverse
$x \mapsto A^{-1} x$. -/
noncomputable def lpEquiv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    PiLp p (fun _ : n => 𝕜) ≃L[𝕜] PiLp p (fun _ : n => 𝕜) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (toLpLin p p A) (toLpLin p p A⁻¹)
      (by rw [← toLpLin_mul_same, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA),
        toLpLin_one])
      (by rw [← toLpLin_mul_same, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA),
        toLpLin_one]))

/-- The equivalence `Matrix.lpEquiv p hA` maps $x$ to $Ax$. -/
@[simp]
theorem lpEquiv_apply {A : Matrix n n 𝕜} (hA : IsUnit A) (x : PiLp p (fun _ : n => 𝕜)) :
    lpEquiv p hA x = WithLp.toLp p (A *ᵥ WithLp.ofLp x) := rfl

/-- The inverse of the equivalence `Matrix.lpEquiv p hA` maps $x$ to $A^{-1} x$. -/
@[simp]
theorem lpEquiv_symm_apply {A : Matrix n n 𝕜} (hA : IsUnit A) (x : PiLp p (fun _ : n => 𝕜)) :
    (lpEquiv p hA).symm x = WithLp.toLp p (A⁻¹ *ᵥ WithLp.ofLp x) := rfl

/-- As a continuous linear map, the equivalence `Matrix.lpEquiv p hA` is the operator
`Matrix.lpCLM p A`. -/
theorem coe_lpEquiv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    ((lpEquiv p hA : PiLp p (fun _ : n => 𝕜) →L[𝕜] PiLp p (fun _ : n => 𝕜))) = lpCLM p A := by
  ext x i; simp

/-- As a continuous linear map, the inverse of `Matrix.lpEquiv p hA` is the operator
`Matrix.lpCLM p A⁻¹`. -/
theorem coe_lpEquiv_symm {A : Matrix n n 𝕜} (hA : IsUnit A) :
    (((lpEquiv p hA).symm : PiLp p (fun _ : n => 𝕜) →L[𝕜] PiLp p (fun _ : n => 𝕜))) =
      lpCLM p A⁻¹ := by
  ext x i; simp

/-- For an invertible $A$, the condition number `ContinuousLinearEquiv.condNumber` of the
equivalence `Matrix.lpEquiv p hA` is $\kappa_p(A)$. -/
theorem condNumber_lpEquiv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    (lpEquiv p hA).condNumber = condNumberLp p A := by
  rw [ContinuousLinearEquiv.condNumber, coe_lpEquiv, coe_lpEquiv_symm]
  rfl

/-- Let $1 \le p \le \infty$ and $M \in \mathbb{K}^{n \times n}$. The operator $x \mapsto Mx$ on
$\ell^p(\mathbb{K}^n)$ is invertible if and only if $M$ is invertible.

If $M$ is singular, a nonzero vector in the kernel of $M$ is in the kernel of the operator. If
$M$ is invertible, `Matrix.lpEquiv` gives the inverse operator. -/
theorem isUnit_lpCLM_iff (M : Matrix n n 𝕜) : IsUnit (lpCLM p M) ↔ IsUnit M := by
  refine ⟨fun hu => ?_, fun hM => ?_⟩
  · by_contra hM
    have hdet : M.det = 0 := by
      by_contra h
      exact hM ((isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 h))
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hinj := (ContinuousLinearMap.isHomeomorph_of_isUnit hu).bijective.injective
    have h0 : lpCLM p M (WithLp.toLp p v) = lpCLM p M 0 := by simp [hv]
    exact hv0 (by simpa using congrArg WithLp.ofLp (hinj h0))
  · rw [← coe_lpEquiv p hM]
    exact ⟨(lpEquiv p hM).toUnit, rfl⟩

/-- Let $1 \le p \le \infty$ and $M \in \mathbb{K}^{n \times n}$. The ring inverse of the operator
$x \mapsto Mx$ on $\ell^p(\mathbb{K}^n)$ is the operator $x \mapsto M^{-1} x$.

This holds also for a singular $M$: then `Ring.inverse` of the operator is $0$, and Mathlib's
`M⁻¹` is $0$. -/
theorem ringInverse_lpCLM (M : Matrix n n 𝕜) : Ring.inverse (lpCLM p M) = lpCLM p M⁻¹ := by
  by_cases hM : IsUnit M
  · have hdet : IsUnit M.det := (isUnit_iff_isUnit_det M).1 hM
    exact Ring.inverse_unit ⟨lpCLM p M, lpCLM p M⁻¹,
      by rw [← lpCLM_mul, mul_nonsing_inv _ hdet, lpCLM_one],
      by rw [← lpCLM_mul, nonsing_inv_mul _ hdet, lpCLM_one]⟩
  · rw [Ring.inverse_non_unit _ ((isUnit_lpCLM_iff p M).not.2 hM),
      nonsing_inv_apply_not_isUnit _ fun h => hM ((isUnit_iff_isUnit_det _).2 h), lpCLM_zero]

/-- The condition number $\kappa_p(A)$ is the condition number `NormedRing.condNumber` of the
operator $x \mapsto Ax$ in the operator algebra of $\ell^p(\mathbb{K}^n)$. -/
theorem condNumberLp_eq_condNumber (A : Matrix n n 𝕜) : condNumberLp p A = κ (lpCLM p A) := by
  rw [condNumberLp, NormedRing.condNumber, ringInverse_lpCLM, lpOpNorm, lpOpNorm]

/-- The condition number is invariant under scaling: $\kappa_p(cA) = \kappa_p(A)$ for $c \neq 0$. -/
theorem condNumberLp_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix n n 𝕜) :
    condNumberLp p (c • A) = condNumberLp p A := by
  rw [condNumberLp_eq_condNumber, condNumberLp_eq_condNumber, lpCLM_smul,
    NormedRing.condNumber_smul hc]

/-- For $n \ge 1$ and an invertible $A \in \mathbb{K}^{n \times n}$, $\kappa_p(A) \ge 1$. -/
theorem one_le_condNumberLp [Nonempty n] {A : Matrix n n 𝕜} (hA : IsUnit A) :
    1 ≤ condNumberLp p A := by
  rw [condNumberLp_eq_condNumber]
  exact NormedRing.one_le_condNumber ((isUnit_lpCLM_iff p A).2 hA)

/-- For $n \ge 1$ and $c \neq 0$, $\kappa_p(cI) = 1$, although $\det(cI) = c^n$. Thus the
determinant does not measure the conditioning of a matrix. -/
theorem condNumberLp_smul_one [Nonempty n] {c : 𝕜} (hc : c ≠ 0) :
    condNumberLp p (c • (1 : Matrix n n 𝕜)) = 1 := by
  rw [condNumberLp_smul p hc, condNumberLp, lpOpNorm, lpOpNorm, inv_one, lpCLM_one, norm_one,
    mul_one]

end Square

/-! ### Consistency and the norm induced by a pair of vector norms -/

section Induced

/-- Let $N$ be a function on $\mathbb{K}^{m \times n}$, let $q$ be a seminorm on $\mathbb{K}^m$, and
let $p$ be a seminorm on $\mathbb{K}^n$. The matrix norm $N$ is **consistent** (compatible) with
the vector norms $q$ and $p$ if
$$q(Ax) \le N(A)\, p(x) \quad \text{for all } A \in \mathbb{K}^{m \times n} \text{ and } x \in
  \mathbb{K}^n.$$
For square matrices one takes $q = p$. This is Definition 1.20 of [quarteroni2000numerical]. -/
def IsConsistent (N : Matrix m n 𝕜 → ℝ) (q : Seminorm 𝕜 (m → 𝕜)) (p : Seminorm 𝕜 (n → 𝕜)) :
    Prop :=
  ∀ A x, q (A *ᵥ x) ≤ N A * p x

/-- Let $p$ be a seminorm on $\mathbb{K}^n$ and $q$ a seminorm on $\mathbb{K}^m$. The **matrix norm
induced** by $p$ on the domain and $q$ on the codomain is
$$\|A\|_{q,p} = \sup \{ q(Ax) : p(x) \le 1 \}$$
for $A \in \mathbb{K}^{m \times n}$. This is (1.20) of [quarteroni2000numerical].

The supremum is over the closed unit ball of $p$, not the unit sphere, so that the index type is
nonempty: it contains $0$. The supremum is the real `iSup`, which is $0$ if the set is unbounded
above. The set is bounded when $p$ is definite (`Matrix.bddAbove_range_inducedNorm`). -/
noncomputable def inducedNorm (q : Seminorm 𝕜 (m → 𝕜)) (p : Seminorm 𝕜 (n → 𝕜))
    (A : Matrix m n 𝕜) : ℝ :=
  ⨆ x : {x : n → 𝕜 // p x ≤ 1}, q (A *ᵥ x)

variable (q : Seminorm 𝕜 (m → 𝕜)) (p : Seminorm 𝕜 (n → 𝕜))

instance : Nonempty {x : n → 𝕜 // p x ≤ 1} := ⟨⟨0, by simp⟩⟩

omit [Fintype m] in
open scoped Matrix.Norms.Operator in
/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$, let $q$ be a seminorm on $\mathbb{K}^m$, and
let $A \in \mathbb{K}^{m \times n}$. Then the set $\{ q(Ax) : p(x) \le 1 \}$ is bounded above,
so the supremum that defines `Matrix.inducedNorm` is a true supremum.

The unit ball of $p$ is bounded in norm, and $q(Ax) \le C \|Ax\| \le C \|A\| \|x\|$. -/
theorem bddAbove_range_inducedNorm [Finite m] (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) :
    BddAbove (Set.range fun x : {x : n → 𝕜 // p x ≤ 1} => q (A *ᵥ x)) := by
  cases nonempty_fintype m
  obtain ⟨c, C, hc, -, hcp⟩ := p.exists_bounds_rclike hp
  obtain ⟨Cq, hCq0, hCq⟩ := (q.restrictScalars ℝ).exists_le_mul_norm
  refine ⟨Cq * ‖A‖ * c⁻¹, ?_⟩
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  have hxle : ‖x‖ ≤ c⁻¹ := by
    have h1 : c * ‖x‖ ≤ 1 := (hcp x).1.trans hx
    calc ‖x‖ = c⁻¹ * (c * ‖x‖) := by field_simp
      _ ≤ c⁻¹ * 1 := by gcongr
      _ = c⁻¹ := mul_one _
  calc q (A *ᵥ x) ≤ Cq * ‖A *ᵥ x‖ := hCq (A *ᵥ x)
    _ ≤ Cq * (‖A‖ * ‖x‖) := by gcongr; exact linfty_opNorm_mulVec A x
    _ ≤ Cq * (‖A‖ * c⁻¹) := by gcongr
    _ = Cq * ‖A‖ * c⁻¹ := by ring

variable {q p}

omit [Fintype m] in
/-- Let $p$ and $q$ be seminorms on $\mathbb{K}^n$ and $\mathbb{K}^m$. The induced norm
$\|A\|_{q,p}$ is nonnegative. -/
theorem inducedNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ inducedNorm q p A :=
  Real.iSup_nonneg fun _ => apply_nonneg _ _

omit [Fintype m] in
/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$, let $q$ be a seminorm on $\mathbb{K}^m$, and
let $A \in \mathbb{K}^{m \times n}$. If $p(x) \le 1$, then $q(Ax) \le \|A\|_{q,p}$. -/
theorem le_inducedNorm [Finite m] (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) {x : n → 𝕜}
    (hx : p x ≤ 1) : q (A *ᵥ x) ≤ inducedNorm q p A :=
  le_ciSup (bddAbove_range_inducedNorm q p hp A) ⟨x, hx⟩

omit [Fintype m] in
/-- Let $p$ and $q$ be seminorms on $\mathbb{K}^n$ and $\mathbb{K}^m$, let
$A \in \mathbb{K}^{m \times n}$, and let $M \ge 0$. If $q(Ax) \le M$ for every $x$ with
$p(x) \le 1$, then $\|A\|_{q,p} \le M$. -/
theorem inducedNorm_le (A : Matrix m n 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x, p x ≤ 1 → q (A *ᵥ x) ≤ M) : inducedNorm q p A ≤ M :=
  Real.iSup_le (fun x => h x.1 x.2) hM

omit [Fintype n] in
/-- For a definite seminorm $p$ and $x \neq 0$, $p(x / p(x)) = 1$. -/
private theorem apply_smul_inv (hp : ∀ x, p x = 0 → x = 0) {x : n → 𝕜} (hx : x ≠ 0) :
    p ((RCLike.ofReal (p x)⁻¹ : 𝕜) • x) = 1 := by
  have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx (hp x h.symm)
  rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hpx), inv_mul_cancel₀ hpx.ne']

omit [Fintype m] in
/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$, let $q$ be a seminorm on $\mathbb{K}^m$, and
let $A \in \mathbb{K}^{m \times n}$. Then for every $x \in \mathbb{K}^n$,
$$q(Ax) \le \|A\|_{q,p}\, p(x).$$
This is item 1 of Theorem 1.3 of [quarteroni2000numerical]: the induced norm is consistent with
$q$ and $p$. The bundled form is `Matrix.isConsistent_inducedNorm`. -/
theorem le_inducedNorm_mul [Finite m] (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜)
    (x : n → 𝕜) :
    q (A *ᵥ x) ≤ inducedNorm q p A * p x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx (hp x h.symm)
  have h := le_inducedNorm (q := q) hp A (apply_smul_inv hp hx).le
  rw [mulVec_smul, map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hpx),
    inv_mul_le_iff₀ hpx, mul_comm] at h
  exact h

omit [Fintype m] in
/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$ and $q$ a seminorm on $\mathbb{K}^m$. The
induced norm $\|\cdot\|_{q,p}$ is consistent with $q$ and $p$. This is item 1 of Theorem 1.3 of
[quarteroni2000numerical]. -/
theorem isConsistent_inducedNorm [Finite m] (hp : ∀ x, p x = 0 → x = 0) :
    IsConsistent (inducedNorm q p) q p :=
  fun A x => le_inducedNorm_mul hp A x

omit [Fintype m] in
/-- Let $p$ and $q$ be seminorms on $\mathbb{K}^n$ and $\mathbb{K}^m$, and let $N$ be a function on
$\mathbb{K}^{m \times n}$ that is consistent with $q$ and $p$. If $N(A) \ge 0$, then
$$\|A\|_{q,p} \le N(A).$$
So the induced norm is the least consistent matrix norm. -/
theorem inducedNorm_le_of_isConsistent {N : Matrix m n 𝕜 → ℝ} (hN : IsConsistent N q p)
    (A : Matrix m n 𝕜) (hNA : 0 ≤ N A) : inducedNorm q p A ≤ N A :=
  inducedNorm_le A hNA fun x hx =>
    (hN A x).trans (by simpa using mul_le_mul_of_nonneg_left hx hNA)

omit [Fintype m] in
/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$, let $q$ be a seminorm on $\mathbb{K}^m$, and
let $A \in \mathbb{K}^{m \times n}$. Then
$$\|A\|_{q,p} = \sup_{x \neq 0} \frac{q(Ax)}{p(x)},$$
and both sides are $0$ if $n = 0$. This is Theorem 1.1 of [quarteroni2000numerical]: the
definitions (1.19) and (1.20) give the same norm. -/
theorem inducedNorm_eq_iSup_div [Finite m] (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) :
    inducedNorm q p A = ⨆ x : {x : n → 𝕜 // x ≠ 0}, q (A *ᵥ x) / p x := by
  have hbdd : BddAbove (Set.range fun x : {x : n → 𝕜 // x ≠ 0} => q (A *ᵥ x) / p x) := by
    refine ⟨inducedNorm q p A, ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx (hp x h.symm)
    exact (div_le_iff₀ hpx).2 (le_inducedNorm_mul hp A x)
  refine le_antisymm (inducedNorm_le A (Real.iSup_nonneg fun x => by positivity)
    fun x hx => ?_) (Real.iSup_le (fun x => ?_) (inducedNorm_nonneg A))
  · rcases eq_or_ne x 0 with rfl | hx0
    · simpa using Real.iSup_nonneg (f := fun x : {x : n → 𝕜 // x ≠ 0} => q (A *ᵥ x) / p x)
        fun x => by positivity
    have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx0 (hp x h.symm)
    calc q (A *ᵥ x) ≤ q (A *ᵥ x) / p x := by
          rw [le_div_iff₀ hpx]
          exact mul_le_of_le_one_right (apply_nonneg _ _) hx
      _ ≤ _ := le_ciSup hbdd ⟨x, hx0⟩
  · obtain ⟨x, hx⟩ := x
    have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) fun h => hx (hp x h.symm)
    exact (div_le_iff₀ hpx).2 (le_inducedNorm_mul hp A x)

omit [Fintype m] in
/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$ with $n \ge 1$, let $q$ be a seminorm on
$\mathbb{K}^m$, and let $A \in \mathbb{K}^{m \times n}$. Then there is an $x$ with $p(x) = 1$
and
$$\|A\|_{q,p} = q(Ax).$$
That is, the supremum that defines the induced norm is attained on the unit sphere of $p$.

This is the step "$= \|Aw\|$ with $\|w\| = 1$" of the proof of Theorem 1.1 of
[quarteroni2000numerical]. The unit sphere of $p$ is compact, and $x \mapsto q(Ax)$ is
continuous. -/
theorem exists_inducedNorm_eq [Finite m] [Nonempty n] (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix m n 𝕜) : ∃ x, p x = 1 ∧ inducedNorm q p A = q (A *ᵥ x) := by
  classical
  cases nonempty_fintype m
  obtain ⟨c, C, hc, -, hcp⟩ := p.exists_bounds_rclike hp
  -- the unit sphere of `p` is compact and nonempty
  have hclosed : IsClosed {x : n → 𝕜 | p x = 1} :=
    isClosed_eq p.continuous_rclike continuous_const
  have hbdd : Bornology.IsBounded {x : n → 𝕜 | p x = 1} := by
    refine (Metric.isBounded_closedBall (x := (0 : n → 𝕜)) (r := c⁻¹)).subset fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : c * ‖x‖ ≤ 1 := (hcp x).1.trans (le_of_eq hx)
    calc ‖x‖ = c⁻¹ * (c * ‖x‖) := by field_simp
      _ ≤ c⁻¹ * 1 := by gcongr
      _ = c⁻¹ := mul_one _
  have hcompact : IsCompact {x : n → 𝕜 | p x = 1} :=
    Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : ({x : n → 𝕜 | p x = 1} : Set (n → 𝕜)).Nonempty := by
    have h0 : (Pi.single (Classical.arbitrary n) (1 : 𝕜) : n → 𝕜) ≠ 0 := by
      intro h
      have := congrFun h (Classical.arbitrary n)
      simp at this
    exact ⟨_, apply_smul_inv hp h0⟩
  have hcont : Continuous fun x : n → 𝕜 => q (A *ᵥ x) :=
    q.continuous_rclike.comp (mulVecLin A).continuous_of_finiteDimensional
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  refine ⟨x, hx, le_antisymm (inducedNorm_le A (apply_nonneg _ _) fun y hy => ?_)
    (le_inducedNorm hp A hx.le)⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hpy : 0 < p y := lt_of_le_of_ne (apply_nonneg p y) fun h => hy0 (hp y h.symm)
  have hmem : (RCLike.ofReal (p y)⁻¹ : 𝕜) • y ∈ {x : n → 𝕜 | p x = 1} := apply_smul_inv hp hy0
  have h := hmax hmem
  simp only [Set.mem_ofPred_eq, mulVec_smul, map_smul_eq_mul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.2 hpy)] at h
  calc q (A *ᵥ y) = p y * ((p y)⁻¹ * q (A *ᵥ y)) := by field_simp
    _ ≤ 1 * q (A *ᵥ x) := by gcongr
    _ = q (A *ᵥ x) := one_mul _

/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$ and $q$ a seminorm on $\mathbb{K}^m$. The
induced norm $A \mapsto \|A\|_{q,p}$ is a seminorm on $\mathbb{K}^{m \times n}$: it is
absolutely homogeneous and subadditive. This is items 2 and 3 of Theorem 1.1 of
[quarteroni2000numerical]. -/
noncomputable def inducedSeminorm (q : Seminorm 𝕜 (m → 𝕜)) (p : Seminorm 𝕜 (n → 𝕜))
    (hp : ∀ x, p x = 0 → x = 0) : Seminorm 𝕜 (Matrix m n 𝕜) where
  toFun := inducedNorm q p
  map_zero' := by simp [inducedNorm]
  add_le' A B := inducedNorm_le (A + B) (add_nonneg (inducedNorm_nonneg A) (inducedNorm_nonneg B))
    fun x hx => by
      rw [add_mulVec]
      exact (map_add_le_add q _ _).trans
        (add_le_add (le_inducedNorm hp A hx) (le_inducedNorm hp B hx))
  neg' A := by simp [inducedNorm, neg_mulVec]
  smul' c A := by
    change (⨆ x : {x : n → 𝕜 // p x ≤ 1}, q ((c • A) *ᵥ x))
      = ‖c‖ * ⨆ x : {x : n → 𝕜 // p x ≤ 1}, q (A *ᵥ x)
    simp_rw [smul_mulVec, map_smul_eq_mul]
    exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm

/-- The seminorm `Matrix.inducedSeminorm q p hp` maps $A$ to $\|A\|_{q,p}$. -/
@[simp]
theorem inducedSeminorm_apply (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) :
    inducedSeminorm q p hp A = inducedNorm q p A := rfl

omit [Fintype m] in
/-- Let $p$ and $q$ be definite seminorms on $\mathbb{K}^n$ and $\mathbb{K}^m$, and let
$A \in \mathbb{K}^{m \times n}$. Then $\|A\|_{q,p} = 0$ if and only if $A = 0$. This is item 1
of Theorem 1.1 of [quarteroni2000numerical]: the induced norm is definite. -/
theorem inducedNorm_eq_zero_iff [Finite m] (hq : ∀ y, q y = 0 → y = 0)
    (hp : ∀ x, p x = 0 → x = 0) (A : Matrix m n 𝕜) : inducedNorm q p A = 0 ↔ A = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => by simp [h, inducedNorm]⟩
  ext i j
  have hle := le_inducedNorm_mul (q := q) hp A (Pi.single j (1 : 𝕜))
  rw [h, zero_mul] at hle
  have hcol : A *ᵥ Pi.single j 1 = 0 := hq _ (le_antisymm hle (apply_nonneg _ _))
  simpa [mulVec_single_one] using congrFun hcol i

variable (r : Seminorm 𝕜 (l → 𝕜))

omit [Fintype l] in
/-- Let $p$, $q$ and $r$ be seminorms on $\mathbb{K}^n$, $\mathbb{K}^m$ and $\mathbb{K}^l$, with $p$
and $q$ definite, and let $A \in \mathbb{K}^{l \times m}$ and $B \in \mathbb{K}^{m \times n}$.
Then the induced norms are submultiplicative:
$$\|AB\|_{r,p} \le \|A\|_{r,q} \|B\|_{q,p}.$$
This is item 3 of Theorem 1.3 of [quarteroni2000numerical], for rectangular matrices. -/
theorem inducedNorm_mul_le [Finite l] (hp : ∀ x, p x = 0 → x = 0) (hq : ∀ y, q y = 0 → y = 0)
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    inducedNorm r p (A * B) ≤ inducedNorm r q A * inducedNorm q p B :=
  inducedNorm_le (A * B) (mul_nonneg (inducedNorm_nonneg A) (inducedNorm_nonneg B)) fun x hx =>
    calc r ((A * B) *ᵥ x) = r (A *ᵥ (B *ᵥ x)) := by rw [mulVec_mulVec]
      _ ≤ inducedNorm r q A * q (B *ᵥ x) := le_inducedNorm_mul hq A _
      _ ≤ inducedNorm r q A * inducedNorm q p B := by
          gcongr
          · exact inducedNorm_nonneg A
          · exact le_inducedNorm hp B hx

variable {r}

/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$ with $n \ge 1$. The identity matrix has the
induced norm $\|I\|_{p,p} = 1$. This is item 2 of Theorem 1.3 of [quarteroni2000numerical]. -/
theorem inducedNorm_one [DecidableEq n] [Nonempty n] (hp : ∀ x, p x = 0 → x = 0) :
    inducedNorm p p (1 : Matrix n n 𝕜) = 1 := by
  refine le_antisymm (inducedNorm_le 1 zero_le_one fun x hx => by simpa using hx) ?_
  have h0 : (Pi.single (Classical.arbitrary n) (1 : 𝕜) : n → 𝕜) ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary n)
    simp at this
  have h := le_inducedNorm (q := p) hp (1 : Matrix n n 𝕜) (apply_smul_inv hp h0).le
  rwa [one_mulVec, apply_smul_inv hp h0] at h

/-- Let $N$ be a function on $\mathbb{K}^{n \times n}$ that is submultiplicative,
$N(AB) \le N(A) N(B)$ for all $A$ and $B$, and let $N(I) \ge 0$ and $N(I) \neq 0$. Then
$N(I) \ge 1$.

This is the remark after Theorem 1.3 of [quarteroni2000numerical]: submultiplicativity alone
gives only $\|I\| \ge 1$, not $\|I\| = 1$. -/
theorem one_le_of_mul_le [DecidableEq n] {N : Matrix n n 𝕜 → ℝ}
    (hmul : ∀ A B, N (A * B) ≤ N A * N B)
    (h0 : 0 ≤ N 1) (h1 : N 1 ≠ 0) : 1 ≤ N 1 := by
  have h := hmul 1 1
  rw [mul_one] at h
  nlinarith [lt_of_le_of_ne h0 (Ne.symm h1)]

/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$. The induced norm $A \mapsto \|A\|_{p,p}$ is an
algebra norm on $\mathbb{K}^{n \times n}$: a submultiplicative, definite seminorm. This combines
Theorems 1.1 and 1.3 of [quarteroni2000numerical].

In this form, `spectralRadius_le_algebraNorm`, `tendsto_pow_of_algebraNorm_lt_one` and the
`AlgebraNorm` lemmas of `Numlib.Analysis.Normed.Algebra.SpectralRadius` apply to it. -/
noncomputable def inducedAlgebraNorm [DecidableEq n] (p : Seminorm 𝕜 (n → 𝕜))
    (hp : ∀ x, p x = 0 → x = 0) : AlgebraNorm 𝕜 (Matrix n n 𝕜) :=
  { inducedSeminorm p p hp with
    mul_le' := inducedNorm_mul_le p hp hp
    eq_zero_of_map_eq_zero' := fun A h => (inducedNorm_eq_zero_iff hp hp A).1 h }

/-- The algebra norm `Matrix.inducedAlgebraNorm p hp` maps $A$ to $\|A\|_{p,p}$. -/
@[simp]
theorem inducedAlgebraNorm_apply [DecidableEq n] (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix n n 𝕜) : inducedAlgebraNorm p hp A = inducedNorm p p A := rfl

end Induced

/-! ### The vector $p$-norms as seminorms, and $\|A\|_p$ as an induced norm -/

section LpSeminorm

variable (r : ℝ≥0∞) [Fact (1 ≤ r)]

/-- Let $1 \le r \le \infty$. The **vector $r$-norm** on $\mathbb{K}^n$,
$$\|x\|_r = \Big( \sum_i |x_i|^r \Big)^{1/r},$$
with $\|x\|_\infty = \max_i |x_i|$, as a seminorm on $\mathbb{K}^n$. This is (1.13) of
[quarteroni2000numerical].

The seminorm acts on plain functions `n → 𝕜`, and `Matrix.lpSeminorm r x` is `‖WithLp.toLp r x‖`
by definition. -/
noncomputable def lpSeminorm : Seminorm 𝕜 (n → 𝕜) :=
  (normSeminorm 𝕜 (PiLp r fun _ : n => 𝕜)).comp (WithLp.linearEquiv r 𝕜 (n → 𝕜)).symm.toLinearMap

/-- The seminorm `Matrix.lpSeminorm r` maps $x$ to the norm of $x$ in `PiLp r`. -/
@[simp]
theorem lpSeminorm_apply (x : n → 𝕜) : lpSeminorm r x = ‖WithLp.toLp r x‖ := rfl

/-- Let $1 \le r \le \infty$ and $x \in \mathbb{K}^n$. Then $\|x\|_r = 0$ if and only if $x = 0$. -/
theorem lpSeminorm_eq_zero_iff (x : n → 𝕜) : lpSeminorm r x = 0 ↔ x = 0 := by
  rw [lpSeminorm_apply, norm_eq_zero, WithLp.toLp_eq_zero]

/-- Let $1 \le r \le \infty$. The vector $r$-norm is definite: $\|x\|_r = 0$ implies $x = 0$. This
is the form of the hypothesis that the lemmas on induced norms take. -/
theorem lpSeminorm_definite : ∀ x : n → 𝕜, lpSeminorm r x = 0 → x = 0 :=
  fun x => (lpSeminorm_eq_zero_iff r x).1

variable [DecidableEq n]

/-- Let $1 \le r \le \infty$ and $A \in \mathbb{K}^{m \times n}$. The matrix norm $\|A\|_r$ is the
norm induced by the vector $r$-norm:
$$\|A\|_r = \|A\|_{r,r} = \sup \{ \|Ax\|_r : \|x\|_r \le 1 \}.$$

The left side is `Matrix.lpOpNorm r A`, the operator norm on `PiLp r`. The right side is
`Matrix.inducedNorm` of `Matrix.lpSeminorm r`. -/
theorem lpOpNorm_eq_inducedNorm (A : Matrix m n 𝕜) :
    lpOpNorm r A = inducedNorm (lpSeminorm r) (lpSeminorm r) A := by
  rw [lpOpNorm, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm, inducedNorm, iSup]
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨WithLp.ofLp y, by simpa [Metric.mem_closedBall] using hy⟩, by simp⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨WithLp.toLp r x, by simpa [Metric.mem_closedBall] using hx, by simp⟩

/-- Let $1 \le r \le \infty$, $A \in \mathbb{K}^{m \times n}$ and $x \in \mathbb{K}^n$. Then
$$\|Ax\|_r \le \|A\|_r \|x\|_r.$$
-/
theorem lpSeminorm_mulVec_le (A : Matrix m n 𝕜) (x : n → 𝕜) :
    lpSeminorm r (A *ᵥ x) ≤ lpOpNorm r A * lpSeminorm r x := by
  have h := (lpCLM r A).le_opNorm (WithLp.toLp r x)
  rwa [lpCLM_apply, WithLp.ofLp_toLp] at h

/-- Let $1 \le r \le \infty$. The matrix norm $\|\cdot\|_r$ on $\mathbb{K}^{m \times n}$ is
consistent with the vector $r$-norms on $\mathbb{K}^m$ and $\mathbb{K}^n$. -/
theorem isConsistent_lpOpNorm :
    IsConsistent (fun A : Matrix m n 𝕜 => lpOpNorm r A) (lpSeminorm r) (lpSeminorm r) :=
  fun A x => lpSeminorm_mulVec_le r A x

open scoped Matrix.Norms.Operator in
/-- Let $A \in \mathbb{K}^{m \times n}$. The induced $\infty$-norm $\|A\|_\infty$ is the norm of
Mathlib's scoped instance `Matrix.Norms.Operator`, which is the largest absolute row sum
$$\|A\|_\infty = \max_i \sum_j |a_{ij}|$$
by `Matrix.linfty_opNorm_def`. This is the "row sum norm" of [quarteroni2000numerical], §1.11. -/
theorem lpOpNorm_top (A : Matrix m n 𝕜) : lpOpNorm ⊤ A = ‖A‖ := by
  rw [linfty_opNorm_eq_opNorm, lpOpNorm]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_)
  · rw [lpCLM_apply, PiLp.norm_toLp, ← PiLp.norm_ofLp x]
    exact (ContinuousLinearMap.mk (mulVecLin A)
      (mulVecLin A).continuous_of_finiteDimensional).le_opNorm (WithLp.ofLp x)
  · have h := (lpCLM ⊤ A).le_opNorm (WithLp.toLp ⊤ v)
    rwa [lpCLM_apply, PiLp.norm_toLp, PiLp.norm_toLp, WithLp.ofLp_toLp] at h

open scoped Matrix.Norms.Operator in
/-- Let $A \in \mathbb{K}^{m \times n}$. Then $\|A\|_1 = \|A^T\|_\infty$: the column sum norm of $A$
is the row sum norm of its transpose. This is stated in [quarteroni2000numerical], §1.11.

The right side is the norm of the scoped instance `Matrix.Norms.Operator`. -/
theorem lpOpNorm_one_eq_linfty_opNorm_transpose (A : Matrix m n 𝕜) : lpOpNorm 1 A = ‖Aᵀ‖ := by
  rw [lpOpNorm_one_eq_sup_sum_norm, linfty_opNorm_def]
  simp only [transpose_apply]

open scoped Matrix.Norms.Operator in
/-- Let $A \in \mathbb{K}^{m \times n}$. Then $\|A\|_1 = \|A^H\|_\infty$, because conjugation does
not change the absolute row sums.

The right side is the norm of the scoped instance `Matrix.Norms.Operator`. -/
theorem lpOpNorm_one_eq_linfty_opNorm_conjTranspose (A : Matrix m n 𝕜) :
    lpOpNorm 1 A = ‖Aᴴ‖ := by
  rw [lpOpNorm_one_eq_sup_sum_norm, linfty_opNorm_def]
  simp only [conjTranspose_apply, nnnorm_star]

open scoped Matrix.Norms.Operator in
/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian. Then $\|A\|_1 = \|A\|_\infty$. This is stated
in [quarteroni2000numerical], §1.11.

The right side is the norm of the scoped instance `Matrix.Norms.Operator`. -/
theorem IsHermitian.lpOpNorm_one_eq_linfty_opNorm {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    lpOpNorm 1 A = ‖A‖ := by
  rw [lpOpNorm_one_eq_linfty_opNorm_conjTranspose, hA.eq]

end LpSeminorm

/-! ### Comparison of the induced $p$-norms -/

section Compare

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [DecidableEq n]

/-- Let $1 \le p \le q \le \infty$ and $A \in \mathbb{K}^{m \times n}$. Then
$$\|A\|_p \le m^{1/p - 1/q} \|A\|_q.$$

Here $1/\infty = 0$: the exponent is written with `ENNReal.toReal`, which maps $\infty$ to $0$,
and $1/0 = 0$ in Lean. The proof uses the vector comparison `PiLp.norm_le_card_rpow_mul_norm` on
the codomain and `PiLp.norm_le_norm_of_le` on the domain. -/
theorem lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le (hpq : p ≤ q) (A : Matrix m n 𝕜) :
    lpOpNorm p A ≤ (Fintype.card m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * lpOpNorm q A := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (lpOpNorm_nonneg q A))
    fun x => ?_
  rw [lpCLM_apply]
  calc ‖WithLp.toLp p (A *ᵥ WithLp.ofLp x)‖
      ≤ (Fintype.card m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
          ‖WithLp.toLp q (A *ᵥ WithLp.ofLp x)‖ := PiLp.norm_le_card_rpow_mul_norm hpq _
    _ ≤ (Fintype.card m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
          (lpOpNorm q A * ‖WithLp.toLp q (WithLp.ofLp x)‖) := by
        gcongr
        have h := (lpCLM q A).le_opNorm (WithLp.toLp q (WithLp.ofLp x))
        rwa [lpCLM_apply, WithLp.ofLp_toLp] at h
    _ ≤ (Fintype.card m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * (lpOpNorm q A * ‖x‖) := by
        gcongr
        · exact lpOpNorm_nonneg q A
        · simpa using PiLp.norm_le_norm_of_le hpq (WithLp.ofLp x)
    _ = _ := by ring

/-- Let $1 \le p \le q \le \infty$ and $A \in \mathbb{K}^{m \times n}$. Then
$$\|A\|_q \le n^{1/p - 1/q} \|A\|_p.$$

Here $1/\infty = 0$, as in `Matrix.lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le`. The proof uses the
vector comparison `PiLp.norm_le_norm_of_le` on the codomain and
`PiLp.norm_le_card_rpow_mul_norm` on the domain. -/
theorem lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge (hpq : p ≤ q) (A : Matrix m n 𝕜) :
    lpOpNorm q A ≤ (Fintype.card n : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * lpOpNorm p A := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (lpOpNorm_nonneg p A))
    fun x => ?_
  rw [lpCLM_apply]
  calc ‖WithLp.toLp q (A *ᵥ WithLp.ofLp x)‖
      ≤ ‖WithLp.toLp p (A *ᵥ WithLp.ofLp x)‖ := PiLp.norm_le_norm_of_le hpq _
    _ ≤ lpOpNorm p A * ‖WithLp.toLp p (WithLp.ofLp x)‖ := by
        have h := (lpCLM p A).le_opNorm (WithLp.toLp p (WithLp.ofLp x))
        rwa [lpCLM_apply, WithLp.ofLp_toLp] at h
    _ ≤ lpOpNorm p A * ((Fintype.card n : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖) := by
        gcongr
        · exact lpOpNorm_nonneg p A
        · simpa using PiLp.norm_le_card_rpow_mul_norm hpq (WithLp.ofLp x)
    _ = _ := by ring

/-- Let $A \in \mathbb{K}^{m \times n}$. Then
$$\|A\|_2 \le \sqrt{m}\, \|A\|_\infty \quad \text{and} \quad \|A\|_\infty \le \sqrt{n}\,
  \|A\|_2.$$
For a square matrix of order $n$ this gives $n^{-1/2} \|A\|_\infty \le \|A\|_2 \le n^{1/2}
\|A\|_\infty$, as stated in [quarteroni2000numerical], §1.11. -/
theorem l2_opNorm_le_sqrt_card_mul_linfty_opNorm (A : Matrix m n 𝕜) :
    lpOpNorm 2 A ≤ √(Fintype.card m : ℝ) * lpOpNorm ⊤ A ∧
      lpOpNorm ⊤ A ≤ √(Fintype.card n : ℝ) * lpOpNorm 2 A := by
  have h2 : (1 / (2 : ℝ≥0∞).toReal - 1 / (⊤ : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
  constructor
  · have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le (p := 2) (q := ⊤) le_top A
    rwa [h2, ← Real.sqrt_eq_rpow] at h
  · have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge (p := 2) (q := ⊤) le_top A
    rwa [h2, ← Real.sqrt_eq_rpow] at h

/-- Let $A \in \mathbb{K}^{m \times n}$. Then
$$\|A\|_1 \le \sqrt{m}\, \|A\|_2 \quad \text{and} \quad \|A\|_2 \le \sqrt{n}\, \|A\|_1.$$
For a square matrix of order $n$ this gives $n^{-1/2} \|A\|_1 \le \|A\|_2 \le n^{1/2} \|A\|_1$,
as stated in [quarteroni2000numerical], §1.11. -/
theorem l2_opNorm_le_sqrt_card_mul_lpOpNorm_one (A : Matrix m n 𝕜) :
    lpOpNorm 1 A ≤ √(Fintype.card m : ℝ) * lpOpNorm 2 A ∧
      lpOpNorm 2 A ≤ √(Fintype.card n : ℝ) * lpOpNorm 1 A := by
  have h2 : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
  constructor
  · have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le (p := 1) (q := 2) (by norm_num) A
    rwa [h2, ← Real.sqrt_eq_rpow] at h
  · have h := lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge (p := 1) (q := 2) (by norm_num) A
    rwa [h2, ← Real.sqrt_eq_rpow] at h

/-- Let $1 \le p \le q \le \infty$, let $A \in \mathbb{K}^{n \times n}$, and let
$c = n^{2(1/p - 1/q)}$. The condition numbers in the two induced norms are equivalent:
$$\kappa_p(A) \le c\, \kappa_q(A) \quad \text{and} \quad \kappa_q(A) \le c\, \kappa_p(A).$$
The constant $c$ is $n$ for $(p, q) = (1, 2)$ and for $(p, q) = (2, \infty)$, and $n^2$ for
$(p, q) = (1, \infty)$. This is (2.6.8) of [golub2013matrix].

Here $1/\infty = 0$, as in `Matrix.lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le`. The proof
multiplies the one-sided comparisons `Matrix.lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le` and
`Matrix.lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge` for $A$ and $A^{-1}$. -/
theorem condNumberLp_le_card_rpow_mul_condNumberLp (hpq : p ≤ q) (A : Matrix n n 𝕜) :
    condNumberLp p A ≤ (Fintype.card n : ℝ) ^ (2 * (1 / p.toReal - 1 / q.toReal)) *
        condNumberLp q A ∧
      condNumberLp q A ≤ (Fintype.card n : ℝ) ^ (2 * (1 / p.toReal - 1 / q.toReal)) *
        condNumberLp p A := by
  set k := (Fintype.card n : ℝ) ^ (1 / p.toReal - 1 / q.toReal)
  have hk : 0 ≤ k := by positivity
  have hc : (Fintype.card n : ℝ) ^ (2 * (1 / p.toReal - 1 / q.toReal)) = k * k := by
    rw [mul_comm, Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_two, sq]
  rw [hc]
  constructor
  · calc condNumberLp p A = lpOpNorm p A * lpOpNorm p A⁻¹ := rfl
      _ ≤ (k * lpOpNorm q A) * (k * lpOpNorm q A⁻¹) :=
          mul_le_mul (lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le hpq A)
            (lpOpNorm_le_card_rpow_mul_lpOpNorm_of_le hpq A⁻¹) (lpOpNorm_nonneg _ _)
            (mul_nonneg hk (lpOpNorm_nonneg _ _))
      _ = k * k * condNumberLp q A := by rw [condNumberLp]; ring
  · calc condNumberLp q A = lpOpNorm q A * lpOpNorm q A⁻¹ := rfl
      _ ≤ (k * lpOpNorm p A) * (k * lpOpNorm p A⁻¹) :=
          mul_le_mul (lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge hpq A)
            (lpOpNorm_le_card_rpow_mul_lpOpNorm_of_ge hpq A⁻¹) (lpOpNorm_nonneg _ _)
            (mul_nonneg hk (lpOpNorm_nonneg _ _))
      _ = k * k * condNumberLp p A := by rw [condNumberLp]; ring

end Compare

/-! ### The spectral radius and the induced norms -/

section SpectralRadius

variable [DecidableEq n] {p : Seminorm 𝕜 (n → 𝕜)}

omit [DecidableEq n] in
/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$, and let $N$ be a function on
$\mathbb{K}^{n \times n}$ that is consistent with $p$. Then for every
$A \in \mathbb{K}^{n \times n}$,
$$\rho(A) \le N(A),$$
where $\rho(A)$ is the spectral radius of $A$ over $\mathbb{K}$. This is Theorem 1.4 of
[quarteroni2000numerical].

The spectral radius is `spectralRadius 𝕜 A`, a value in `ℝ≥0∞`. The proof is the one of the
source: for an eigenpair $Av = \lambda v$, $|\lambda|\, p(v) = p(Av) \le N(A)\, p(v)$ with
$p(v) > 0$. It does not use submultiplicativity of $N$, which distinguishes it from
`spectralRadius_le_algebraNorm`. For `𝕜 = ℝ` the statement is about the real spectrum. The
complex spectral radius of a real matrix is in
`Matrix.complexSpectralRadius_le_of_isConsistent`. -/
theorem spectralRadius_le_of_isConsistent {N : Matrix n n 𝕜 → ℝ} (hp : ∀ x, p x = 0 → x = 0)
    (hN : IsConsistent N p p) (A : Matrix n n 𝕜) :
    spectralRadius 𝕜 A ≤ ENNReal.ofReal (N A) := by
  classical
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨x, hx, hx0⟩ := ((hasEigenvalue_toEuclideanLin_iff A μ).mpr hμ).exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff, toEuclideanLin_apply] at hx
  have hv : A *ᵥ WithLp.ofLp x = μ • WithLp.ofLp x := by
    simpa using congrArg WithLp.ofLp hx
  have hv0 : WithLp.ofLp x ≠ 0 := fun h => hx0 (by simpa using congrArg (WithLp.toLp 2) h)
  have hpv : 0 < p (WithLp.ofLp x) :=
    lt_of_le_of_ne (apply_nonneg _ _) fun h => hv0 (hp _ h.symm)
  have h := hN A (WithLp.ofLp x)
  rw [hv, map_smul_eq_mul] at h
  have hle : ‖μ‖ ≤ N A := le_of_mul_le_mul_right h hpv
  calc (‖μ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖μ‖ := (ofReal_norm μ).symm
    _ ≤ ENNReal.ofReal (N A) := ENNReal.ofReal_le_ofReal hle

omit [DecidableEq n] in
/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$ and $A \in \mathbb{K}^{n \times n}$. Then
$\rho(A) \le \|A\|_{p,p}$, where $\rho(A)$ is the spectral radius of $A$ over $\mathbb{K}$. This
is Theorem 1.4 of [quarteroni2000numerical] for the induced norms.

The spectral radius is `spectralRadius 𝕜 A`. -/
theorem spectralRadius_le_inducedNorm (hp : ∀ x, p x = 0 → x = 0) (A : Matrix n n 𝕜) :
    spectralRadius 𝕜 A ≤ ENNReal.ofReal (inducedNorm p p A) := by
  classical
  exact
    spectralRadius_le_of_isConsistent hp (isConsistent_inducedNorm hp) A

omit [DecidableEq n] in
/-- Let $p$ be a definite seminorm on $\mathbb{R}^n$ and $A \in \mathbb{R}^{n \times n}$. Then
$\rho(A) \le \|A\|_{p,p}$, where $\rho(A)$ is the spectral radius of $A$ as a complex matrix.
This is Theorem 1.4 of [quarteroni2000numerical] for the induced norms of a real matrix.

The spectral radius is `Matrix.complexSpectralRadius A`. The proof goes through
`Matrix.inducedAlgebraNorm` and `Matrix.complexSpectralRadius_le_algebraNorm`. -/
theorem complexSpectralRadius_le_inducedNorm {p : Seminorm ℝ (n → ℝ)} (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix n n ℝ) : complexSpectralRadius A ≤ ENNReal.ofReal (inducedNorm p p A) := by
  classical
  exact
    complexSpectralRadius_le_algebraNorm (inducedAlgebraNorm p hp) A

omit [DecidableEq n] in
/-- Let $p$ be a definite seminorm on $\mathbb{R}^n$, and let $N$ be a function on
$\mathbb{R}^{n \times n}$ that is consistent with $p$. Then for every
$A \in \mathbb{R}^{n \times n}$,
$$\rho(A) \le N(A),$$
where $\rho(A)$ is the spectral radius of $A$ as a complex matrix. This is Theorem 1.4 of
[quarteroni2000numerical] for a real matrix and a real consistent norm.

The spectral radius is `Matrix.complexSpectralRadius A`. The eigenvector proof of the source
does not apply, because the eigenvector can be complex. Instead, $N$ dominates the induced norm
$\|\cdot\|_{p,p}$, which is an algebra norm. -/
theorem complexSpectralRadius_le_of_isConsistent {N : Matrix n n ℝ → ℝ} {p : Seminorm ℝ (n → ℝ)}
    (hp : ∀ x, p x = 0 → x = 0) (hN : IsConsistent N p p) (A : Matrix n n ℝ) :
    complexSpectralRadius A ≤ ENNReal.ofReal (N A) := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Subsingleton (Matrix n n ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    simp [complexSpectralRadius]
  have hNA : 0 ≤ N A := by
    have h0 : (Pi.single (Classical.arbitrary n) (1 : ℝ) : n → ℝ) ≠ 0 := by
      intro h
      have := congrFun h (Classical.arbitrary n)
      simp at this
    have hpx : 0 < p (Pi.single (Classical.arbitrary n) 1) :=
      lt_of_le_of_ne (apply_nonneg _ _) fun h => h0 (hp _ h.symm)
    have h := (apply_nonneg p _).trans (hN A (Pi.single (Classical.arbitrary n) 1))
    exact nonneg_of_mul_nonneg_left h hpx
  exact (complexSpectralRadius_le_inducedNorm hp A).trans
    (ENNReal.ofReal_le_ofReal (inducedNorm_le_of_isConsistent hN A hNA))

omit [DecidableEq n] in
/-- Let $A \in \mathbb{R}^{n \times n}$ and $\varepsilon > 0$. Then there is a definite seminorm $p$
on $\mathbb{R}^n$ with
$$\|A\|_{p,p} \le \rho(A) + \varepsilon,$$
where $\rho(A)$ is the spectral radius of $A$ as a complex matrix. This is Property 1.13 of
[quarteroni2000numerical] for a real matrix, stated with induced norms.

The spectral radius is `Matrix.complexSpectralRadius A`, converted to a real number. The norm
$p$ is the one of `Matrix.exists_seminorm_forall_mulVec_le`. -/
theorem exists_inducedNorm_le_complexSpectralRadius_add (A : Matrix n n ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Seminorm ℝ (n → ℝ), (∀ x, p x = 0 → x = 0) ∧
      inducedNorm p p A ≤ (complexSpectralRadius A).toReal + ε := by
  classical
  obtain ⟨p, hle, -, hA⟩ := exists_seminorm_forall_mulVec_le A hε
  have hp : ∀ x, p x = 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 ((hle x).trans hx.le)
  refine ⟨p, hp, inducedNorm_le A (by positivity) fun x hx => (hA x).trans ?_⟩
  simpa using mul_le_mul_of_nonneg_left hx (by positivity)

omit [DecidableEq n] in
/-- Let $A \in \mathbb{C}^{n \times n}$ and $\varepsilon > 0$. Then there is a definite seminorm $p$
on $\mathbb{C}^n$ with
$$\|A\|_{p,p} \le \rho(A) + \varepsilon.$$
This is Property 1.13 of [quarteroni2000numerical], stated with induced norms.

The spectral radius is `spectralRadius ℂ A`, converted to a real number. The norm $p$ is the one
of `Matrix.exists_seminorm_forall_mulVec_le_complex`. -/
theorem exists_inducedNorm_le_spectralRadius_add (A : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Seminorm ℂ (n → ℂ), (∀ x, p x = 0 → x = 0) ∧
      inducedNorm p p A ≤ (spectralRadius ℂ A).toReal + ε := by
  classical
  obtain ⟨p, hle, -, hA⟩ := exists_seminorm_forall_mulVec_le_complex A hε
  have hp : ∀ x, p x = 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 ((hle x).trans hx.le)
  refine ⟨p, hp, inducedNorm_le A (by positivity) fun x hx => (hA x).trans ?_⟩
  simpa using mul_le_mul_of_nonneg_left hx (by positivity)

omit [DecidableEq n] in
/-- Let $A \in \mathbb{R}^{n \times n}$. The spectral radius of $A$ as a complex matrix is the
infimum of the norms of $A$ induced by the definite seminorms $p$ on $\mathbb{R}^n$:
$$\rho(A) = \inf_p \|A\|_{p,p}.$$
This is (1.23) of [quarteroni2000numerical].

The source takes the infimum over all consistent norms. Every consistent norm is at least
$\rho(A)$ (`Matrix.complexSpectralRadius_le_of_isConsistent`), and the induced norms are
consistent, so the value is the same. -/
theorem complexSpectralRadius_eq_iInf_inducedNorm (A : Matrix n n ℝ) :
    (complexSpectralRadius A).toReal =
      ⨅ p : {p : Seminorm ℝ (n → ℝ) // ∀ x, p x = 0 → x = 0}, inducedNorm p.1 p.1 A := by
  classical
  have hne : Nonempty {p : Seminorm ℝ (n → ℝ) // ∀ x, p x = 0 → x = 0} :=
    ⟨⟨normSeminorm ℝ (n → ℝ), fun x hx => norm_eq_zero.1 hx⟩⟩
  have hlow : ∀ p : {p : Seminorm ℝ (n → ℝ) // ∀ x, p x = 0 → x = 0},
      (complexSpectralRadius A).toReal ≤ inducedNorm p.1 p.1 A := fun p =>
    ENNReal.toReal_le_of_le_ofReal (inducedNorm_nonneg A)
      (complexSpectralRadius_le_inducedNorm p.2 A)
  refine le_antisymm (le_ciInf hlow) (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨p, hp, hle⟩ := exists_inducedNorm_le_complexSpectralRadius_add A hε
  exact (ciInf_le ⟨_, Set.forall_mem_range.2 hlow⟩ ⟨p, hp⟩).trans hle

end SpectralRadius

/-! ### A submultiplicative norm has a consistent vector norm -/

section Submultiplicative

/-- The linear map $x \mapsto x y^H$ from $\mathbb{K}^n$ to $\mathbb{K}^{n \times n}$. -/
private def vecMulVecStarₗ (y : n → 𝕜) : (n → 𝕜) →ₗ[𝕜] Matrix n n 𝕜 where
  toFun x := vecMulVec x (star y)
  map_add' x₁ x₂ := add_vecMulVec x₁ x₂ (star y)
  map_smul' c x := by
    ext i j
    simp [vecMulVec_apply, mul_assoc]

/-- Let $N$ be a seminorm on $\mathbb{K}^{n \times n}$ that is submultiplicative,
$N(AB) \le N(A) N(B)$ for all $A$ and $B$, and let $y \in \mathbb{K}^n$ be nonzero. Then there
is a seminorm $p$ on $\mathbb{K}^n$ such that $N$ is consistent with $p$, that is,
$p(Ax) \le N(A)\, p(x)$ for all $A$ and $x$, and $p$ is definite if $N$ is definite. This is
stated in [quarteroni2000numerical], §1.11, after Definition 1.21.

The seminorm is $p(x) = N(x y^H)$, where $x y^H$ is the rank-one matrix
`Matrix.vecMulVec x (star y)`. -/
theorem exists_isConsistent_of_mul_le (N : Seminorm 𝕜 (Matrix n n 𝕜))
    (hmul : ∀ A B, N (A * B) ≤ N A * N B) {y : n → 𝕜} (hy : y ≠ 0) :
    ∃ p : Seminorm 𝕜 (n → 𝕜), IsConsistent N p p ∧
      ((∀ B, N B = 0 → B = 0) → ∀ x, p x = 0 → x = 0) := by
  refine ⟨N.comp (vecMulVecStarₗ y), fun A x => ?_, fun hN x hx => ?_⟩
  · simp only [Seminorm.comp_apply, vecMulVecStarₗ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← mul_vecMulVec]
    exact hmul _ _
  · have h0 : vecMulVec x (star y) = 0 := hN _ hx
    rw [vecMulVec_eq_zero] at h0
    rcases h0 with h | h
    · exact h
    · exact absurd (star_eq_zero.1 h) hy

end Submultiplicative

/-!
### The Neumann bounds for an induced norm

This section proves the bounds (1.26) of [quarteroni2000numerical] on $\|(I - A)^{-1}\|$, and the
Neumann series.
-/

section Neumann

variable [DecidableEq n] {p : Seminorm 𝕜 (n → 𝕜)}

/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$, and let $A \in \mathbb{K}^{n \times n}$ with
$\|A\|_{p,p} < 1$. Then $I - A$ is invertible. This is Theorem 1.5 of [quarteroni2000numerical]
together with Remark 1.1. -/
theorem isUnit_one_sub_of_inducedNorm_lt_one (hp : ∀ x, p x = 0 → x = 0) {A : Matrix n n 𝕜}
    (hA : inducedNorm p p A < 1) : IsUnit (1 - A) :=
  isUnit_one_sub_of_algebraNorm_lt_one (inducedAlgebraNorm p hp) hA

/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$ with $n \ge 1$, and let
$A \in \mathbb{K}^{n \times n}$ with $\|A\| < 1$, where $\|\cdot\|$ is the induced norm
$\|\cdot\|_{p,p}$. Then
$$\|(I - A)^{-1}\| \le \frac{1}{1 - \|A\|}.$$
This is the upper bound of (1.26) of [quarteroni2000numerical]. -/
theorem inducedNorm_inv_one_sub_le [Nonempty n] (hp : ∀ x, p x = 0 → x = 0) {A : Matrix n n 𝕜}
    (hA : inducedNorm p p A < 1) : inducedNorm p p (1 - A)⁻¹ ≤ 1 / (1 - inducedNorm p p A) := by
  rw [nonsing_inv_eq_ringInverse]
  exact (inducedAlgebraNorm p hp).norm_inverse_one_sub_le_of_lt_one (inducedNorm_one hp) hA

/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$ with $n \ge 1$, and let
$A \in \mathbb{K}^{n \times n}$ with $\|A\| < 1$, where $\|\cdot\|$ is the induced norm
$\|\cdot\|_{p,p}$. Then
$$\frac{1}{1 + \|A\|} \le \|(I - A)^{-1}\|.$$
This is the lower bound of (1.26) of [quarteroni2000numerical]. -/
theorem one_div_one_add_le_inducedNorm_inv_one_sub [Nonempty n] (hp : ∀ x, p x = 0 → x = 0)
    {A : Matrix n n 𝕜} (hA : inducedNorm p p A < 1) :
    1 / (1 + inducedNorm p p A) ≤ inducedNorm p p (1 - A)⁻¹ := by
  rw [nonsing_inv_eq_ringInverse]
  exact (inducedAlgebraNorm p hp).one_div_one_add_le_norm_inverse_one_sub (inducedNorm_one hp) hA

/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$, and let $F \in \mathbb{K}^{n \times n}$ with
$\|F\| < 1$, where $\|\cdot\|$ is the induced norm $\|\cdot\|_{p,p}$. Then
$$\|(I - F)^{-1} - I\| \le \frac{\|F\|}{1 - \|F\|}.$$
This is stated in [golub2013matrix], §2.3.4, after Lemma 2.3.3.

The proof uses $(I - F)^{-1} - I = F (I - F)^{-1}$. The companion bound on $\|(I - F)^{-1}\|$ is
`Matrix.inducedNorm_inv_one_sub_le`. -/
theorem inducedNorm_inv_one_sub_sub_one_le (hp : ∀ x, p x = 0 → x = 0) {F : Matrix n n 𝕜}
    (hF : inducedNorm p p F < 1) :
    inducedNorm p p ((1 - F)⁻¹ - 1) ≤ inducedNorm p p F / (1 - inducedNorm p p F) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim ((1 - F)⁻¹ - 1) 0, show inducedNorm p p (0 : Matrix n n 𝕜) = 0 from
      (inducedNorm_eq_zero_iff hp hp 0).2 rfl]
    exact div_nonneg (inducedNorm_nonneg F) (by linarith)
  have hu : IsUnit (1 - F) := isUnit_one_sub_of_inducedNorm_lt_one hp hF
  have hkey : (1 - F)⁻¹ - 1 = F * (1 - F)⁻¹ := by
    have h := mul_nonsing_inv (1 - F) ((isUnit_iff_isUnit_det _).1 hu)
    calc (1 - F)⁻¹ - 1 = (1 - F)⁻¹ - (1 - F) * (1 - F)⁻¹ := by rw [h]
      _ = F * (1 - F)⁻¹ := by noncomm_ring
  rw [hkey]
  calc inducedNorm p p (F * (1 - F)⁻¹) ≤ inducedNorm p p F * inducedNorm p p (1 - F)⁻¹ :=
        inducedNorm_mul_le p hp hp F _
    _ ≤ inducedNorm p p F * (1 / (1 - inducedNorm p p F)) :=
        mul_le_mul_of_nonneg_left (inducedNorm_inv_one_sub_le hp hF) (inducedNorm_nonneg F)
    _ = inducedNorm p p F / (1 - inducedNorm p p F) := by ring

/-- Let $p$ be a definite seminorm on $\mathbb{K}^n$, and let $F \in \mathbb{K}^{n \times n}$ with
$\|F\|_{p,p} < 1$. Then the **Neumann series** converges to the inverse of $I - F$:
$$\sum_{k=0}^\infty F^k = (I - F)^{-1}.$$
This is Lemma 2.3.3 of [golub2013matrix].

The series converges in the entrywise topology of `Matrix n n 𝕜`. All norms on the
finite-dimensional space of matrices are equivalent (`Seminorm.exists_mul_norm_le`), so the
geometric bound $\|F^k\| \le \|F\|^k$ in the induced norm makes the series absolutely summable
in the $\infty$-operator norm, whose topology is the entrywise one. -/
theorem hasSum_pow_of_inducedNorm_lt_one (hp : ∀ x, p x = 0 → x = 0) {F : Matrix n n 𝕜}
    (hF : inducedNorm p p F < 1) : HasSum (fun k => F ^ k) (1 - F)⁻¹ := by
  let _ : NormedRing (Matrix n n 𝕜) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.linftyOpNormedAlgebra
  set N := inducedAlgebraNorm p hp
  obtain ⟨c, hc, hcN⟩ := ((inducedSeminorm p p hp).restrictScalars ℝ).exists_mul_norm_le
    fun X hX => eq_zero_of_map_eq_zero N hX
  have hbound : ∀ k, k ≠ 0 → ‖F ^ k‖ ≤ c⁻¹ * N F ^ k := fun k hk => by
    have h1 := hcN (F ^ k)
    have h2 : N (F ^ k) ≤ N F ^ k := map_pow_le_pow N F hk
    change c * ‖F ^ k‖ ≤ N (F ^ k) at h1
    rw [le_inv_mul_iff₀ hc]
    exact h1.trans h2
  have hs : Summable fun k => F ^ k := by
    refine Summable.of_norm_bounded_eventually
      ((summable_geometric_of_lt_one (apply_nonneg N F) hF).mul_left c⁻¹) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with k hk
    exact hbound k hk
  have hinv : (1 - F)⁻¹ = ∑' k, F ^ k :=
    inv_eq_right_inv hs.one_sub_mul_tsum_pow
  rw [hinv]
  exact hs.hasSum

end Neumann

/-!
### The spectral norm $\|A\|_2$

In this section, `‖A‖` is the spectral norm of the scoped instance `Matrix.Norms.L2Operator`.
-/

section L2Operator

open scoped Matrix.Norms.L2Operator

variable [DecidableEq n]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $x \in \mathbb{K}^n$. Then
$\|Ax\|_2 \le \|A\|_2 \|x\|_2$.

The vector $Ax$ is written `Matrix.toEuclideanLin A x`, with $x$ in `EuclideanSpace 𝕜 n`. -/
theorem norm_toEuclideanLin_apply_le (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ := by
  rw [l2_opNorm_def]
  exact ((toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A).le_opNorm x

/-- Let $A \in \mathbb{K}^{m \times n}$ and $M \ge 0$. If $\|Ax\|_2 \le M \|x\|_2$ for every
$x \in \mathbb{K}^n$, then $\|A\|_2 \le M$.

The vector $Ax$ is written `Matrix.toEuclideanLin A x`, with $x$ in `EuclideanSpace 𝕜 n`. -/
theorem l2_opNorm_le_of_forall_norm_toEuclideanLin_le (A : Matrix m n 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : EuclideanSpace 𝕜 n, ‖toEuclideanLin A x‖ ≤ M * ‖x‖) : ‖A‖ ≤ M := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hM h

section Unitary

variable [DecidableEq m]

/-- Let $n \ge 1$, and let $U \in \mathbb{K}^{n \times n}$ be unitary. Then $\|U\|_2 = 1$. This is
the last statement of Theorem 1.2 of [quarteroni2000numerical]. -/
theorem l2_opNorm_of_mem_unitaryGroup [Nonempty n] {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : ‖U‖ = 1 := by
  refine le_antisymm (l2_opNorm_le_of_forall_norm_toEuclideanLin_le U zero_le_one fun x => by
    rw [norm_toEuclideanLin_apply_of_mem_unitaryGroup hU, one_mul]) ?_
  have h := norm_toEuclideanLin_apply_le U (EuclideanSpace.single (Classical.arbitrary n) (1 : 𝕜))
  rwa [norm_toEuclideanLin_apply_of_mem_unitaryGroup hU, PiLp.norm_single, norm_one,
    mul_one] at h

/-- Let $U \in \mathbb{K}^{m \times m}$ and $V \in \mathbb{K}^{n \times n}$ be unitary, and let
$A \in \mathbb{K}^{m \times n}$. Then $\|UAV\|_2 \le \|A\|_2$. -/
theorem l2_opNorm_unitary_mul_mul_unitary_le {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜)
    (A : Matrix m n 𝕜) {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) : ‖U * A * V‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ (norm_nonneg _) fun x => ?_
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    norm_toEuclideanLin_apply_of_mem_unitaryGroup hU]
  calc ‖toEuclideanLin A (toEuclideanLin V x)‖ ≤ ‖A‖ * ‖toEuclideanLin V x‖ :=
        norm_toEuclideanLin_apply_le A _
    _ = ‖A‖ * ‖x‖ := by rw [norm_toEuclideanLin_apply_of_mem_unitaryGroup hV]

/-- Let $U \in \mathbb{K}^{m \times m}$ and $V \in \mathbb{K}^{n \times n}$ be unitary, and let
$A \in \mathbb{K}^{m \times n}$. The spectral norm is **unitarily invariant**:
$$\|UAV\|_2 = \|A\|_2.$$
-/
theorem l2_opNorm_unitary_mul_mul_unitary {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜)
    (A : Matrix m n 𝕜) {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) : ‖U * A * V‖ = ‖A‖ := by
  refine le_antisymm (l2_opNorm_unitary_mul_mul_unitary_le hU A hV) ?_
  have hU' : star U ∈ unitaryGroup m 𝕜 := Unitary.star_mem hU
  have hV' : star V ∈ unitaryGroup n 𝕜 := Unitary.star_mem hV
  have h := l2_opNorm_unitary_mul_mul_unitary_le hU' (U * A * V) hV'
  have hUU : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hVV : V * star V = 1 := mem_unitaryGroup_iff.mp hV
  have heq : star U * (U * A * V) * star V = A := by
    calc star U * (U * A * V) * star V = (star U * U) * A * (V * star V) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [hUU, hVV, Matrix.one_mul, Matrix.mul_one]
  rwa [heq] at h

/-- Let $U \in \mathbb{K}^{m \times m}$ be unitary and $A \in \mathbb{K}^{m \times n}$. Then
$\|UA\|_2 = \|A\|_2$. -/
theorem l2_opNorm_unitary_mul {U : Matrix m m 𝕜} (hU : U ∈ unitaryGroup m 𝕜) (A : Matrix m n 𝕜) :
    ‖U * A‖ = ‖A‖ := by
  simpa using l2_opNorm_unitary_mul_mul_unitary hU A (unitaryGroup n 𝕜).one_mem

omit [DecidableEq m] in
/-- Let $A \in \mathbb{K}^{m \times n}$ and let $V \in \mathbb{K}^{n \times n}$ be unitary. Then
$\|AV\|_2 = \|A\|_2$. -/
theorem l2_opNorm_mul_unitary (A : Matrix m n 𝕜) {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) :
    ‖A * V‖ = ‖A‖ := by
  classical
  simpa using l2_opNorm_unitary_mul_mul_unitary (unitaryGroup m 𝕜).one_mem A hV

/-- Let $n \ge 1$, and let $U \in \mathbb{K}^{n \times n}$ be unitary. Then the spectral condition
number of $U$ is $\kappa_2(U) = 1$. This is stated in [quarteroni2000numerical], §3.1.1: "if $A$
is orthogonal, $K_2(A) = 1$".

The condition number is `NormedRing.condNumber` for the spectral norm. -/
theorem condNumber_l2_of_mem_unitaryGroup [Nonempty n] {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : κ U = 1 := by
  rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse, l2_opNorm_of_mem_unitaryGroup hU,
    one_mul]
  have hinv : U⁻¹ = star U := inv_eq_left_inv (mem_unitaryGroup_iff'.mp hU)
  rw [hinv]
  exact l2_opNorm_of_mem_unitaryGroup (Unitary.star_mem hU)

/-- Let $Q \in \mathbb{K}^{n \times n}$ be unitary and $R \in \mathbb{K}^{n \times n}$. Then the
spectral condition numbers satisfy
$$\kappa_2(QR) = \kappa_2(R).$$
This is Exercise 14 of [quarteroni2000numerical], §3.11, which states $K_2(A) = K_2(R)$ for a QR
factorization $A = QR$.

The condition number is `NormedRing.condNumber` for the spectral norm. If $R$ is singular, both
sides are $0$. -/
theorem condNumber_l2_unitary_mul {Q : Matrix n n 𝕜} (hQ : Q ∈ unitaryGroup n 𝕜)
    (R : Matrix n n 𝕜) : κ (Q * R) = κ R := by
  rw [NormedRing.condNumber, NormedRing.condNumber, ← nonsing_inv_eq_ringInverse,
    ← nonsing_inv_eq_ringInverse, Matrix.mul_inv_rev, l2_opNorm_unitary_mul hQ]
  have hinv : Q⁻¹ = star Q := inv_eq_left_inv (mem_unitaryGroup_iff'.mp hQ)
  rw [hinv, l2_opNorm_mul_unitary _ (Unitary.star_mem hQ)]

end Unitary

/-- Let $W \in \mathbb{K}^{m \times l}$ have orthonormal columns, $W^H W = I$. Then
$\|Wx\|_2 = \|x\|_2$ for every $x \in \mathbb{K}^l$.

The vector $Wx$ is written `Matrix.toEuclideanLin W x`, with $x$ in `EuclideanSpace 𝕜 l`. -/
theorem norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one [DecidableEq l]
    {W : Matrix m l 𝕜} (hW : Wᴴ * W = 1) (x : EuclideanSpace 𝕜 l) :
    ‖toEuclideanLin W x‖ = ‖x‖ := by
  classical
  have h : inner 𝕜 (toEuclideanLin W x) (toEuclideanLin W x) = inner 𝕜 x x := by
    rw [← LinearMap.adjoint_inner_left, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← toEuclideanLin_mul_apply, hW, toEuclideanLin_one, LinearMap.id_apply]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← RCLike.ofReal_inj (K := 𝕜),
    RCLike.ofReal_pow, RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K,
    ← inner_self_eq_norm_sq_to_K, h]

/-- Let $W \in \mathbb{K}^{m \times l}$ have orthonormal columns, $W^H W = I$, and let
$M \in \mathbb{K}^{l \times n}$. Then
$$\|WM\|_2 = \|M\|_2.$$

The matrix $W$ is an isometry of the Euclidean spaces. The square case is
`Matrix.l2_opNorm_unitary_mul`. -/
theorem l2_opNorm_mul_of_conjTranspose_mul_self_eq_one [DecidableEq l] {W : Matrix m l 𝕜}
    (hW : Wᴴ * W = 1) (M : Matrix l n 𝕜) : ‖W * M‖ = ‖M‖ := by
  refine le_antisymm (l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ (norm_nonneg _) fun x => ?_)
    (l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ (norm_nonneg _) fun x => ?_)
  · rw [toEuclideanLin_mul_apply, norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hW]
    exact norm_toEuclideanLin_apply_le M x
  · rw [← norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hW,
      ← toEuclideanLin_mul_apply]
    exact norm_toEuclideanLin_apply_le _ x

/-- Let $W \in \mathbb{K}^{n \times l}$ have orthonormal columns, $W^H W = I$, and let
$M \in \mathbb{K}^{m \times l}$. Then
$$\|M W^H\|_2 = \|M\|_2.$$
This is the adjoint form of `Matrix.l2_opNorm_mul_of_conjTranspose_mul_self_eq_one`. -/
theorem l2_opNorm_mul_conjTranspose_of_conjTranspose_mul_self_eq_one [DecidableEq l]
    {W : Matrix n l 𝕜} (hW : Wᴴ * W = 1) (M : Matrix m l 𝕜) :
    ‖M * Wᴴ‖ = ‖M‖ := by
  classical
  rw [← l2_opNorm_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
    l2_opNorm_mul_of_conjTranspose_mul_self_eq_one hW, l2_opNorm_conjTranspose]

/-- Let $W \in \mathbb{K}^{m \times l}$ have orthonormal columns, $W^H W = I$. Then $\|W\|_2 \le 1$.

This is the rectangular form of `Matrix.l2_opNorm_of_mem_unitaryGroup`. Equality holds when $W$
has at least one column (`Matrix.l2_opNorm_of_conjTranspose_mul_self_eq_one`). -/
theorem l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one [DecidableEq l] {W : Matrix m l 𝕜}
    (hW : Wᴴ * W = 1) : ‖W‖ ≤ 1 :=
  l2_opNorm_le_of_forall_norm_toEuclideanLin_le W zero_le_one fun x => by
    rw [norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hW, one_mul]

/-- Let $l \ge 1$, and let $W \in \mathbb{K}^{m \times l}$ have orthonormal columns, $W^H W = I$.
Then $\|W\|_2 = 1$. -/
theorem l2_opNorm_of_conjTranspose_mul_self_eq_one [DecidableEq l] [Nonempty l]
    {W : Matrix m l 𝕜} (hW : Wᴴ * W = 1) : ‖W‖ = 1 := by
  have h := l2_opNorm_mul_of_conjTranspose_mul_self_eq_one hW (1 : Matrix l l 𝕜)
  rwa [Matrix.mul_one, l2_opNorm_of_mem_unitaryGroup (one_mem _)] at h

/-- Let $A \in \mathbb{K}^{m \times n}$. Every entry satisfies $|a_{ij}| \le \|A\|_2$. This is the
lower half of the first estimate in [quarteroni2000numerical], §1.11, after Theorem 1.2. -/
theorem norm_entry_le_l2_opNorm (A : Matrix m n 𝕜) (i : m) (j : n) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h := norm_toEuclideanLin_apply_le A (EuclideanSpace.single j (1 : 𝕜))
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le (toEuclideanLin A (EuclideanSpace.single j (1 : 𝕜))) i
  simpa [toEuclideanLin_apply, mulVec_single_one] using h2

/-- Let $A \in \mathbb{K}^{m \times n}$. Every singular value of $A$ is at most $\|A\|_2$.

The singular values are `Matrix.colSingularValues A`, indexed by the columns of $A$. -/
theorem colSingularValues_le_l2_opNorm (A : Matrix m n 𝕜) (i : n) :
    A.colSingularValues i ≤ ‖A‖ := by
  have h := norm_toEuclideanLin_apply_le A (A.rightSingularBasis i)
  rwa [norm_toEuclideanLin_rightSingularBasis, A.rightSingularBasis.orthonormal.1 i,
    mul_one] at h

/-- Let $A \in \mathbb{K}^{m \times n}$. Every singular value of $A$ is at most $\|A\|_2$, here
written `Matrix.lpOpNorm 2 A`.

The singular values are `Matrix.colSingularValues A`, indexed by the columns of $A$. -/
theorem colSingularValues_le_lpOpNorm_two (A : Matrix m n 𝕜) (i : n) :
    A.colSingularValues i ≤ lpOpNorm 2 A := by
  rw [lpOpNorm_two]
  exact colSingularValues_le_l2_opNorm A i

/-- Let $A \in \mathbb{K}^{m \times n}$. Then $\|A A^H\|_2 = \|A\|_2^2$. This is the C⋆-identity on
the other side, with the spectral norm written `Matrix.lpOpNorm 2`. -/
theorem lpOpNorm_two_mul_conjTranspose_self [DecidableEq m] (A : Matrix m n 𝕜) :
    lpOpNorm 2 (A * Aᴴ) = lpOpNorm 2 A ^ 2 := by
  rw [lpOpNorm_two, lpOpNorm_two]
  have h := l2_opNorm_conjTranspose_mul_self Aᴴ
  rw [conjTranspose_conjTranspose] at h
  rw [h, l2_opNorm_conjTranspose, sq]

/-- Let $A \in \mathbb{K}^{m \times n}$. Then $\|A^H\|_2 = \|A\|_2$, with the spectral norm written
`Matrix.lpOpNorm 2`. -/
theorem lpOpNorm_two_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) :
    lpOpNorm 2 Aᴴ = lpOpNorm 2 A := by
  rw [lpOpNorm_two, lpOpNorm_two, l2_opNorm_conjTranspose]

/-- Let $N \in \mathbb{K}^{n \times n}$ be an orthogonal projector, that is, Hermitian and
idempotent: $N = N^H = N^2$. Then $\|N\|_2 \le 1$.

The spectral norm is written `Matrix.lpOpNorm 2`. The proof is Mathlib's
`IsStarProjection.norm_le` in the C⋆-algebra `Matrix n n 𝕜`. -/
theorem lpOpNorm_two_le_one_of_isStarProjection {N : Matrix n n 𝕜} (hN : IsStarProjection N) :
    lpOpNorm 2 N ≤ 1 := by
  rw [lpOpNorm_two]
  exact IsStarProjection.norm_le N hN

/-- Let $A \in \mathbb{C}^{m \times n}$. Then
$$\|A\|_2^2 = \rho(A^H A).$$
This is the first equality of (1.21) in Theorem 1.2 of [quarteroni2000numerical].

Here $\rho$ is `spectralRadius ℂ`, and both sides are values in `ℝ≥0∞`. In the C⋆-algebra
`Matrix n n ℂ`, $\rho(A^H A) = \|A^H A\|_2$ because $A^H A$ is self-adjoint, and
$\|A^H A\|_2 = \|A\|_2^2$ is the C⋆-identity. -/
theorem l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self (A : Matrix m n ℂ) :
    (‖A‖₊ : ℝ≥0∞) ^ 2 = spectralRadius ℂ (Aᴴ * A) := by
  rw [IsSelfAdjoint.spectralRadius_eq_nnnorm (isHermitian_conjTranspose_mul_self A).isSelfAdjoint,
    l2_opNNNorm_conjTranspose_mul_self, ENNReal.coe_mul, sq]

/-- Let $A \in \mathbb{C}^{m \times n}$. Then
$$\|A\|_2^2 = \rho(A A^H).$$
This is the second equality of (1.21) in Theorem 1.2 of [quarteroni2000numerical].

Here $\rho$ is `spectralRadius ℂ`, and both sides are values in `ℝ≥0∞`. -/
theorem l2_opNorm_sq_eq_spectralRadius_self_mul_conjTranspose
    (A : Matrix m n ℂ) : (‖A‖₊ : ℝ≥0∞) ^ 2 = spectralRadius ℂ (A * Aᴴ) := by
  classical
  have h := l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self Aᴴ
  rwa [conjTranspose_conjTranspose, l2_opNNNorm_conjTranspose] at h

/-- Let $A \in \mathbb{R}^{n \times n}$. The spectral norm of $A$ as a complex matrix is the
spectral norm of $A$.

The norms are the `nnnorm`s of the scoped instance `Matrix.Norms.L2Operator` over $\mathbb{C}$
and over $\mathbb{R}$. -/
theorem l2_opNNNorm_complexify (A : Matrix n n ℝ) : ‖complexify A‖₊ = ‖A‖₊ :=
  Subtype.ext (l2_opNorm_complexify A)

/-- Let $A \in \mathbb{R}^{n \times n}$. Then
$$\|A\|_2^2 = \rho(A^T A),$$
where $\rho$ is the spectral radius of a real matrix as a complex matrix. This is (1.21) of
Theorem 1.2 of [quarteroni2000numerical] for a real square matrix.

Here $\rho$ is `Matrix.complexSpectralRadius`, and both sides are values in `ℝ≥0∞`. -/
theorem l2_opNorm_sq_eq_complexSpectralRadius_conjTranspose_mul_self
    (A : Matrix n n ℝ) : (‖A‖₊ : ℝ≥0∞) ^ 2 = complexSpectralRadius (Aᴴ * A) := by
  rw [complexSpectralRadius, complexify_mul, complexify_conjTranspose,
    ← l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self, l2_opNNNorm_complexify]

/-- Let $A \in \mathbb{C}^{n \times n}$ be Hermitian. Then the spectral norm of $A$ is its spectral
radius, $\|A\|_2 = \rho(A)$. This is (1.22) of Theorem 1.2 of [quarteroni2000numerical].

Here $\rho$ is `spectralRadius ℂ`, and both sides are values in `ℝ≥0∞`. -/
theorem IsHermitian.l2_opNorm_eq_spectralRadius {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (‖A‖₊ : ℝ≥0∞) = spectralRadius ℂ A :=
  (IsSelfAdjoint.spectralRadius_eq_nnnorm hA.isSelfAdjoint).symm

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric. Then $\|A\|_2 = \rho(A)$, where $\rho(A)$ is
the spectral radius of $A$ as a complex matrix. This is (1.22) of [quarteroni2000numerical] for
a real symmetric matrix.

Here $\rho$ is `Matrix.complexSpectralRadius`, and both sides are values in `ℝ≥0∞`. The form with
real numbers is `Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`. -/
theorem IsHermitian.l2_opNNNorm_eq_complexSpectralRadius {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : (‖A‖₊ : ℝ≥0∞) = complexSpectralRadius A := by
  rw [complexSpectralRadius, ← ((isHermitian_complexify_iff A).mpr hA).l2_opNorm_eq_spectralRadius,
    l2_opNNNorm_complexify]

/-- Let $A \in \mathbb{C}^{n \times n}$ be normal. Then the spectral norm of $A$ is its spectral
radius, $\|A\|_2 = \rho(A)$.

Here $\rho$ is `spectralRadius ℂ`, and both sides are values in `ℝ≥0∞`. The proof is Mathlib's
`IsStarNormal.spectralRadius_eq_nnnorm` in the C⋆-algebra `Matrix n n ℂ`. -/
theorem l2_opNorm_eq_spectralRadius_of_isStarNormal (A : Matrix n n ℂ)
    [IsStarNormal A] : (‖A‖₊ : ℝ≥0∞) = spectralRadius ℂ A :=
  (IsStarNormal.spectralRadius_eq_nnnorm A).symm

/-- Let $S \in \mathbb{R}^{n \times n}$ be skew-symmetric, $S^T = -S$. Then the spectral radius of
$S$ as a complex matrix is its spectral norm, $\rho(S) = \|S\|_2$. The matrix $S$ is normal, and
its eigenvalues $\pm i\mu$ are imaginary. -/
theorem complexSpectralRadius_toReal_eq_lpOpNorm_two_of_transpose_eq_neg {S : Matrix n n ℝ}
    (hS : Sᵀ = -S) : (complexSpectralRadius S).toReal = lpOpNorm 2 S := by
  have hstar : star (complexify S) = -complexify S := by
    rw [star_eq_conjTranspose, ← complexify_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      hS, complexify_neg]
  have : IsStarNormal (complexify S) := ⟨by rw [hstar]; exact (Commute.refl _).neg_left⟩
  rw [complexSpectralRadius, ← l2_opNorm_eq_spectralRadius_of_isStarNormal,
    l2_opNNNorm_complexify, ENNReal.coe_toReal, coe_nnnorm, lpOpNorm_two]

/-- Let $A \in \mathbb{C}^{n \times n}$ be normal, and let $1 \le r \le \infty$. Then the spectral
norm is the smallest of the induced $r$-norms of $A$:
$$\|A\|_2 \le \|A\|_r.$$

The proof uses $\|A\|_2 = \rho(A)$ and $\rho(A) \le \|A\|_r$ by consistency.
[quarteroni2000numerical], §1.11, states the bound for $r \ge 2$; it holds for every $r \ge 1$. -/
theorem l2_opNorm_le_lpOpNorm_of_isStarNormal (A : Matrix n n ℂ) [IsStarNormal A]
    (r : ℝ≥0∞) [Fact (1 ≤ r)] : lpOpNorm 2 A ≤ lpOpNorm r A := by
  have h := spectralRadius_le_of_isConsistent (lpSeminorm_definite r) (isConsistent_lpOpNorm r) A
  rw [← l2_opNorm_eq_spectralRadius_of_isStarNormal, ← enorm_eq_nnnorm, ← ofReal_norm,
    ENNReal.ofReal_le_ofReal_iff (lpOpNorm_nonneg r A)] at h
  rwa [lpOpNorm_two]

end L2Operator

/-!
### The Frobenius norm

In this section, `‖A‖` is the Frobenius norm of the scoped instance `Matrix.Norms.Frobenius`.
-/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- Let $X, Y \in \mathbb{K}^{m \times n}$. The **Cauchy–Schwarz inequality for the Frobenius inner
product** is
$$\operatorname{Re} \operatorname{tr}(Y^H X) \le \|Y\|_F \|X\|_F.$$

The pairing $\operatorname{tr}(Y^H X)$ is the inner product of
`PiLp 2 (fun _ : m => EuclideanSpace 𝕜 n)`, whose norm is the Frobenius norm. -/
theorem re_trace_conjTranspose_mul_le (Y X : Matrix m n 𝕜) :
    RCLike.re (trace (Yᴴ * X)) ≤ ‖Y‖ * ‖X‖ := by
  let Φ : Matrix m n 𝕜 → PiLp 2 (fun _ : m => EuclideanSpace 𝕜 n) :=
    fun X => WithLp.toLp 2 fun i => WithLp.toLp 2 (X i)
  have hΦ : ∀ X, ‖Φ X‖ = ‖X‖ := fun X => rfl
  have hinner : inner 𝕜 (Φ Y) (Φ X) = trace (Yᴴ * X) := by
    simp only [Φ, PiLp.inner_apply, RCLike.inner_apply, trace, diag_apply, Matrix.mul_apply,
      conjTranspose_apply, RCLike.star_def]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [← hinner, ← hΦ Y, ← hΦ X]
  exact re_inner_le_norm _ _

/-- Let $X, Y \in \mathbb{K}^{m \times n}$ with $\operatorname{tr}(X^H Y) = 0$. Then the
**Pythagorean identity** holds for the Frobenius norm:
$$\|X + Y\|_F^2 = \|X\|_F^2 + \|Y\|_F^2.$$
-/
theorem frobenius_norm_add_sq_of_trace_eq_zero {X Y : Matrix m n 𝕜}
    (h : trace (Xᴴ * Y) = 0) : ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  have h' : trace (Yᴴ * X) = 0 := by
    rw [← conjTranspose_conjTranspose X, ← conjTranspose_mul, trace_conjTranspose, h, star_zero]
  have key : ((‖X + Y‖ ^ 2 : ℝ) : 𝕜) = ((‖X‖ ^ 2 + ‖Y‖ ^ 2 : ℝ) : 𝕜) := by
    rw [frobenius_norm_sq_eq_trace, RCLike.ofReal_add, frobenius_norm_sq_eq_trace,
      frobenius_norm_sq_eq_trace, conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, trace_add, trace_add, trace_add, h, h']
    ring
  exact_mod_cast key

/-- Let $X, Y \in \mathbb{K}^{m \times n}$ with $X^H Y = 0$, that is, every column of $X$ is
orthogonal to every column of $Y$. Then $\|X + Y\|_F^2 = \|X\|_F^2 + \|Y\|_F^2$. This is the
case of `Matrix.frobenius_norm_add_sq_of_trace_eq_zero` with a zero Gram block. -/
theorem frobenius_norm_add_sq_of_conjTranspose_mul_eq_zero {X Y : Matrix m n 𝕜}
    (h : Xᴴ * Y = 0) : ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 :=
  frobenius_norm_add_sq_of_trace_eq_zero (by rw [h, trace_zero])

/-- Let $Q \in \mathbb{K}^{m \times n}$ have orthonormal columns, $Q^H Q = I$, and let
$Z \in \mathbb{K}^{n \times l}$. Then $\|QZ\|_F = \|Z\|_F$. This is the one-sided form of
`Matrix.frobenius_norm_unitary_mul_mul_unitary`. -/
theorem frobenius_norm_mul_of_conjTranspose_mul_self_eq_one [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : Qᴴ * Q = 1) (Z : Matrix n l 𝕜) : ‖Q * Z‖ = ‖Z‖ := by
  have := frobenius_norm_sq_eq_trace (Q * Z)
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ, Matrix.one_mul,
    ← frobenius_norm_sq_eq_trace] at this
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by exact_mod_cast this)

/-- Let $A \in \mathbb{K}^{m \times m}$, let $Q \in \mathbb{K}^{m \times n}$ have orthonormal
columns, $Q^H Q = I$, and let $S \in \mathbb{K}^{n \times n}$. Then the block residual $AQ - QS$
splits orthogonally:
$$\|AQ - QS\|_F^2 = \|Q^H A Q - S\|_F^2 + \|(I - Q Q^H) A Q\|_F^2.$$
The two terms are the components of the residual in the range of $Q$ and orthogonal to it. This
identity appears in the proof of Theorem 8.1.14 of [golub2013matrix]. -/
theorem frobenius_norm_mul_sub_mul_sq [DecidableEq m] [DecidableEq n] (A : Matrix m m 𝕜)
    {Q : Matrix m n 𝕜} (hQ : Qᴴ * Q = 1) (S : Matrix n n 𝕜) :
    ‖A * Q - Q * S‖ ^ 2 = ‖Qᴴ * A * Q - S‖ ^ 2 + ‖(1 - Q * Qᴴ) * A * Q‖ ^ 2 := by
  have hdec : A * Q - Q * S = (1 - Q * Qᴴ) * A * Q + Q * (Qᴴ * A * Q - S) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
    abel
  have horth : ((1 - Q * Qᴴ) * A * Q)ᴴ * (Q * (Qᴴ * A * Q - S)) = 0 := by
    have hPQ : (1 - Q * Qᴴ)ᴴ * Q = 0 := by
      rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQ, Matrix.mul_one, sub_self]
    rw [conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ Q, hPQ, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  rw [hdec, frobenius_norm_add_sq_of_conjTranspose_mul_eq_zero horth,
    frobenius_norm_mul_of_conjTranspose_mul_self_eq_one hQ, add_comm]

/-- Let $u \in \mathbb{K}^m$ and $w \in \mathbb{K}^n$. The rank-one matrix $u w^T$ has the Frobenius
norm $\|u w^T\|_F = \|u\|_2 \|w\|_2$. -/
theorem frobenius_norm_vecMulVec (u : m → 𝕜) (w : n → 𝕜) :
    ‖vecMulVec u w‖ = ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 m)‖ *
      ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 n)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [vecMulVec_apply, norm_mul, mul_pow]

/-- Let $u \in \mathbb{K}^m$ and $w \in \mathbb{K}^n$. The rank-one matrix $u w^H$ has the Frobenius
norm $\|u w^H\|_F = \|u\|_2 \|w\|_2$. -/
theorem frobenius_norm_vecMulVec_star (u : m → 𝕜) (w : n → 𝕜) :
    ‖vecMulVec u (star w)‖ = ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 m)‖ *
      ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 n)‖ := by
  rw [frobenius_norm_vecMulVec]
  congr 1
  simp [EuclideanSpace.norm_eq]

/-- Let $u \in \mathbb{K}^m$ and $w \in \mathbb{K}^n$. Then $\|u w^T\|_F \le \|u\|_2 \|w\|_2$.

Equality holds by `Matrix.frobenius_norm_vecMulVec`. -/
theorem frobenius_norm_vecMulVec_le (u : m → 𝕜) (w : n → 𝕜) :
    ‖vecMulVec u w‖ ≤ ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 w‖ :=
  (frobenius_norm_vecMulVec u w).le

/-- The squared Frobenius norm of a $2 \times 2$ block matrix is the sum of the squared Frobenius
norms of its four blocks. -/
theorem frobenius_norm_fromBlocks_sq {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c]
    [Fintype d] (M₁₁ : Matrix a c 𝕜) (M₁₂ : Matrix a d 𝕜) (M₂₁ : Matrix b c 𝕜)
    (M₂₂ : Matrix b d 𝕜) :
    ‖fromBlocks M₁₁ M₁₂ M₂₁ M₂₂‖ ^ 2 = ‖M₁₁‖ ^ 2 + ‖M₁₂‖ ^ 2 + ‖M₂₁‖ ^ 2 + ‖M₂₂‖ ^ 2 := by
  simp only [frobenius_norm_sq_eq_sum_sq, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

/-- The squared Frobenius norm of the matrix $\begin{bmatrix} P \\ Q \end{bmatrix}$ is
$\|P\|_F^2 + \|Q\|_F^2$. -/
theorem frobenius_norm_fromRows_sq {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (P : Matrix a c 𝕜) (Q : Matrix b c 𝕜) : ‖fromRows P Q‖ ^ 2 = ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
  simp only [frobenius_norm_sq_eq_sum_sq, Fintype.sum_sum_type, fromRows_apply_inl,
    fromRows_apply_inr]

/-- The squared Frobenius norm of the matrix $\begin{bmatrix} P & Q \end{bmatrix}$ is
$\|P\|_F^2 + \|Q\|_F^2$. -/
theorem frobenius_norm_fromCols_sq {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (P : Matrix c a 𝕜) (Q : Matrix c b 𝕜) : ‖fromCols P Q‖ ^ 2 = ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
  simp only [frobenius_norm_sq_eq_sum_sq, Fintype.sum_sum_type, fromCols_apply_inl,
    fromCols_apply_inr, Finset.sum_add_distrib]

/-- Swapping the two row blocks does not change the Frobenius norm: $\left\| \begin{bmatrix} Q \\ P
\end{bmatrix} \right\|_F = \left\| \begin{bmatrix} P \\ Q \end{bmatrix} \right\|_F$. -/
theorem frobenius_norm_fromRows_comm {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (P : Matrix a c 𝕜) (Q : Matrix b c 𝕜) : ‖fromRows Q P‖ = ‖fromRows P Q‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frobenius_norm_fromRows_sq, frobenius_norm_fromRows_sq, add_comm]

/-- Each row block of the matrix $M = \begin{bmatrix} P \\ Q \end{bmatrix}$ has at most its
Frobenius norm: $\|P\|_F \le \|M\|_F$ and $\|Q\|_F \le \|M\|_F$. -/
theorem frobenius_norm_le_fromRows {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (P : Matrix a c 𝕜) (Q : Matrix b c 𝕜) : ‖P‖ ≤ ‖fromRows P Q‖ ∧ ‖Q‖ ≤ ‖fromRows P Q‖ := by
  have h := frobenius_norm_fromRows_sq P Q
  constructor <;>
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_ <;>
    rw [h] <;> linarith [sq_nonneg ‖P‖, sq_nonneg ‖Q‖]

/-- Swapping the two column blocks does not change the Frobenius norm: $\|\begin{bmatrix} Q & P
\end{bmatrix}\|_F = \|\begin{bmatrix} P & Q \end{bmatrix}\|_F$. -/
theorem frobenius_norm_fromCols_comm {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (P : Matrix c a 𝕜) (Q : Matrix c b 𝕜) : ‖fromCols Q P‖ = ‖fromCols P Q‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frobenius_norm_fromCols_sq, frobenius_norm_fromCols_sq, add_comm]

/-- Each column block of the matrix $M = \begin{bmatrix} P & Q \end{bmatrix}$ has at most its
Frobenius norm: $\|P\|_F \le \|M\|_F$ and $\|Q\|_F \le \|M\|_F$. -/
theorem frobenius_norm_le_fromCols {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (P : Matrix c a 𝕜) (Q : Matrix c b 𝕜) : ‖P‖ ≤ ‖fromCols P Q‖ ∧ ‖Q‖ ≤ ‖fromCols P Q‖ := by
  rw [← frobenius_norm_transpose (fromCols P Q), transpose_fromCols, ← frobenius_norm_transpose P,
    ← frobenius_norm_transpose Q]
  exact frobenius_norm_le_fromRows Pᵀ Qᵀ

/-- Let $M = \begin{bmatrix} M_{11} & M_{12} \\ M_{21} & M_{22} \end{bmatrix}$. Then
$\|M_{11}\|_F \le \|M\|_F$, $\|M_{22}\|_F \le \|M\|_F$, and
$\|M_{12}\|_F^2 + \|M_{21}\|_F^2 \le \|M\|_F^2$. -/
theorem frobenius_norm_toBlocks_le {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c]
    [Fintype d] (M : Matrix (a ⊕ b) (c ⊕ d) 𝕜) :
    ‖M.toBlocks₁₁‖ ≤ ‖M‖ ∧ ‖M.toBlocks₂₂‖ ≤ ‖M‖ ∧
      ‖M.toBlocks₁₂‖ ^ 2 + ‖M.toBlocks₂₁‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  have h := frobenius_norm_fromBlocks_sq M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
  rw [fromBlocks_toBlocks] at h
  have h₁₁ := sq_nonneg ‖M.toBlocks₁₁‖
  have h₁₂ := sq_nonneg ‖M.toBlocks₁₂‖
  have h₂₁ := sq_nonneg ‖M.toBlocks₂₁‖
  have h₂₂ := sq_nonneg ‖M.toBlocks₂₂‖
  refine ⟨?_, ?_, by linarith⟩ <;>
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_ <;>
    linarith

/-- Let $E \in \mathbb{K}^{m \times n}$, and let $f$ and $g$ be injective maps into the row and the
column indices of $E$. The submatrix $E(f, g)$ with the entries $e_{f(i) g(j)}$ satisfies
$$\|E(f, g)\|_F \le \|E\|_F.$$
This is the Frobenius form of `Matrix.lpOpNorm_submatrix_le`. -/
theorem frobenius_norm_submatrix_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (E : Matrix m n 𝕜) {f : m' → m} {g : n' → n} (hf : Function.Injective f)
    (hg : Function.Injective g) : ‖E.submatrix f g‖ ≤ ‖E‖ := by
  classical
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq]
  calc ∑ i, ∑ j, ‖E.submatrix f g i j‖ ^ 2 ≤ ∑ i, ∑ t, ‖E (f i) t‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum_of_injOn g hg.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
            fun _ _ _ => sq_nonneg _
    _ ≤ ∑ s, ∑ t, ‖E s t‖ ^ 2 :=
        Finset.sum_le_sum_of_injOn f hf.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
          fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Reindexing the rows and the columns by bijections does not change the Frobenius norm. -/
theorem frobenius_norm_submatrix_equiv {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m n 𝕜) (e : m' ≃ m) (f : n' ≃ n) : ‖A.submatrix e f‖ = ‖A‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq]
  simp only [submatrix_apply]
  rw [← e.sum_comp (fun i => ∑ j, ‖A i j‖ ^ 2)]
  exact Finset.sum_congr rfl fun i _ => f.sum_comp (fun j => ‖A (e i) j‖ ^ 2)

/-- Let $U \in \mathbb{K}^{m \times m}$ and $V \in \mathbb{K}^{n \times n}$ be unitary, and let
$A \in \mathbb{K}^{m \times n}$. The Frobenius norm is **unitarily invariant**:
$$\|UAV\|_F = \|A\|_F.$$

The proof uses $\|A\|_F^2 = \operatorname{tr}(A^H A)$ and the cyclicity of the trace. -/
theorem frobenius_norm_unitary_mul_mul_unitary [DecidableEq m] [DecidableEq n] {U : Matrix m m 𝕜}
    (hU : U ∈ unitaryGroup m 𝕜) (A : Matrix m n 𝕜) {V : Matrix n n 𝕜}
    (hV : V ∈ unitaryGroup n 𝕜) : ‖U * A * V‖ = ‖A‖ := by
  have hUU : Uᴴ * U = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  have hVV : V * Vᴴ = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hV
  have htr : trace ((U * A * V)ᴴ * (U * A * V)) = trace (Aᴴ * A) := by
    calc trace ((U * A * V)ᴴ * (U * A * V)) = trace (Vᴴ * (Aᴴ * (Uᴴ * U) * A) * V) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = trace (Vᴴ * (Aᴴ * A) * V) := by rw [hUU, Matrix.mul_one]
      _ = trace (V * Vᴴ * (Aᴴ * A)) := trace_mul_cycle _ _ _
      _ = trace (Aᴴ * A) := by rw [hVV, Matrix.one_mul]
  have hsq : ‖U * A * V‖ ^ 2 = ‖A‖ ^ 2 := by
    have h := frobenius_norm_sq_eq_trace (U * A * V)
    rw [htr, ← frobenius_norm_sq_eq_trace] at h
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- Let $A \in \mathbb{K}^{m \times n}$ and $x \in \mathbb{K}^n$. Then
$$\|Ax\|_2 \le \|A\|_F \|x\|_2,$$
that is, the Frobenius norm is consistent with the Euclidean vector norm. This is Example 1.7 of
[quarteroni2000numerical]. -/
theorem frobenius_norm_mulVec_le (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖ := by
  rw [← frobenius_norm_replicateCol (ι := Fin 1), ← frobenius_norm_replicateCol (ι := Fin 1),
    replicateCol_mulVec]
  exact frobenius_norm_mul A _

/-- The identity matrix of order $n$ has the Frobenius norm $\|I\|_F = \sqrt{n}$. This is stated in
Example 1.7 of [quarteroni2000numerical]. -/
theorem frobenius_norm_one [DecidableEq n] : ‖(1 : Matrix n n 𝕜)‖ = √(Fintype.card n : ℝ) := by
  have h := frobenius_nnnorm_one (n := n) (α := 𝕜)
  rw [← NNReal.coe_inj, coe_nnnorm, NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_natCast,
    coe_nnnorm, (norm_one : ‖(1 : 𝕜)‖ = 1), mul_one] at h
  exact h

/-- Let $A \in \mathbb{K}^{m \times n}$. The spectral norm is at most the Frobenius norm:
$$\|A\|_2 \le \|A\|_F.$$
This is the constant $c_{2F} = 1$ of Exercise 17 of [quarteroni2000numerical].

The spectral norm is written `Matrix.lpOpNorm 2`, because the two norms are scoped instances on
the same type. -/
theorem l2_opNorm_le_frobenius_norm [DecidableEq n] (A : Matrix m n 𝕜) : lpOpNorm 2 A ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [lpCLM_apply]
    simpa using frobenius_norm_mulVec_le A (WithLp.ofLp x)

/-- Let $A \in \mathbb{K}^{m \times n}$ with the singular values $\sigma_i$. Then
$$\|A\|_F^2 = \sum_i \sigma_i^2.$$
This is Exercise 16 of [quarteroni2000numerical].

The singular values are `Matrix.colSingularValues A`, indexed by the columns of $A$. The proof
uses that $\operatorname{tr}(A^H A)$ is the sum of the eigenvalues of $A^H A$. -/
theorem frobenius_norm_sq_eq_sum_sq_colSingularValues [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i, A.colSingularValues i ^ 2 := by
  have h := frobenius_norm_sq_eq_trace A
  rw [(isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues] at h
  simp_rw [sq_colSingularValues]
  exact_mod_cast h

/-- Let $A \in \mathbb{K}^{m \times n}$. Then
$$\|A\|_F \le \sqrt{\operatorname{rank} A}\, \|A\|_2.$$
Since $\operatorname{rank} A \le n$, this gives the constant $C_{F2} = \sqrt{n}$ of Exercise 17
of [quarteroni2000numerical].

The spectral norm is written `Matrix.lpOpNorm 2`. Each nonzero singular value is at most
$\|A\|_2$, and there are $\operatorname{rank} A$ of them. -/
theorem frobenius_norm_le_sqrt_rank_mul_l2_opNorm [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A‖ ≤ √(A.rank : ℝ) * lpOpNorm 2 A := by
  have hσ : ∀ i, A.colSingularValues i ≤ lpOpNorm 2 A := colSingularValues_le_lpOpNorm_two A
  have hfilter : univ.filter (fun i => A.colSingularValues i ^ 2 ≠ 0)
      = univ.filter (fun i => A.colSingularValues i ≠ 0) := by
    ext i
    simp [pow_eq_zero_iff]
  have hsq : ‖A‖ ^ 2 ≤ (A.rank : ℝ) * lpOpNorm 2 A ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_sq_colSingularValues, ← card_colSingularValues_ne_zero,
      Fintype.card_subtype, ← Finset.sum_filter_ne_zero, hfilter]
    calc ∑ i ∈ univ.filter (fun i => A.colSingularValues i ≠ 0), A.colSingularValues i ^ 2
        ≤ ∑ i ∈ univ.filter (fun i => A.colSingularValues i ≠ 0), lpOpNorm 2 A ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact pow_le_pow_left₀ (A.colSingularValues_nonneg i) (hσ i) 2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hr : 0 ≤ √(A.rank : ℝ) * lpOpNorm 2 A :=
    mul_nonneg (Real.sqrt_nonneg _) (lpOpNorm_nonneg 2 A)
  refine le_of_sq_le_sq ?_ hr
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact hsq

/-- Let $A \in \mathbb{K}^{m \times n}$ and $M \ge 0$. If $|a_{ij}| \le M$ for all $i$ and $j$, then
$$\|A\|_2 \le \sqrt{mn}\, M.$$
For a square matrix of order $n$ this is $\|A\|_2 \le nM$. This is the upper half of the first
estimate in [quarteroni2000numerical], §1.11, after Theorem 1.2.

The spectral norm is written `Matrix.lpOpNorm 2`. The proof goes through the Frobenius norm. -/
theorem l2_opNorm_le_sqrt_card_mul_of_forall_norm_le [DecidableEq n] (A : Matrix m n 𝕜) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i j, ‖A i j‖ ≤ M) :
    lpOpNorm 2 A ≤ √((Fintype.card m : ℝ) * Fintype.card n) * M := by
  refine (l2_opNorm_le_frobenius_norm A).trans (le_of_sq_le_sq ?_ (by positivity))
  rw [mul_pow, Real.sq_sqrt (by positivity), frobenius_norm_sq_eq_sum_sq]
  calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : m, ∑ _j : n, M ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (Fintype.card m : ℝ) * Fintype.card n * M ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, mul_assoc]

/-!
### Products of a Frobenius norm and a spectral norm

The spectral norms are written `Matrix.lpOpNorm 2`, which is `‖·‖` under the scoped instance
`Matrix.Norms.L2Operator` (`Matrix.lpOpNorm_two`), since the Frobenius instance is the one in scope
here.
-/

/-- Let $X \in \mathbb{K}^{m \times n}$ and $Y \in \mathbb{K}^{n \times o}$. Then
$$\|XY\|_F \le \|X\|_2 \|Y\|_F.$$

The proof bounds the product column by column. -/
theorem frobenius_norm_mul_le_lpOpNorm_two_mul [DecidableEq n] {o : Type*} [Fintype o]
    (X : Matrix m n 𝕜) (Y : Matrix n o 𝕜) : ‖X * Y‖ ≤ lpOpNorm 2 X * ‖Y‖ := by
  classical
  set c := lpOpNorm 2 X with hc
  have hcol : ∀ j : o, ∑ i, ‖(X * Y) i j‖ ^ 2 ≤ c ^ 2 * ∑ k, ‖Y k j‖ ^ 2 := by
    intro j
    have h1 : ‖lpCLM 2 X (WithLp.toLp 2 fun k => Y k j)‖
        ≤ c * ‖(WithLp.toLp 2 fun k => Y k j : EuclideanSpace 𝕜 n)‖ :=
      (lpCLM 2 X).le_opNorm _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, lpCLM_apply, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
    simpa [mulVec, dotProduct, Matrix.mul_apply] using h2
  have hsq : ‖X * Y‖ ^ 2 ≤ (c * ‖Y‖) ^ 2 := by
    rw [mul_pow, frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, Finset.sum_comm,
      Finset.sum_comm (f := fun k j => ‖Y k j‖ ^ 2), Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hcol j
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (lpOpNorm_nonneg 2 X) (norm_nonneg _)) two_ne_zero).1 hsq

/-- Let $X \in \mathbb{K}^{m \times n}$ and $Y \in \mathbb{K}^{n \times o}$. Then
$$\|XY\|_F \le \|X\|_F \|Y\|_2.$$

This follows from `Matrix.frobenius_norm_mul_le_lpOpNorm_two_mul` by the conjugate transpose. -/
theorem frobenius_norm_mul_le_mul_lpOpNorm_two {o : Type*} [Fintype o] [DecidableEq o]
    (X : Matrix m n 𝕜) (Y : Matrix n o 𝕜) : ‖X * Y‖ ≤ ‖X‖ * lpOpNorm 2 Y := by
  classical
  rw [← frobenius_norm_conjTranspose (X * Y), conjTranspose_mul, mul_comm,
    ← frobenius_norm_conjTranspose X, ← lpOpNorm_two_conjTranspose Y]
  exact frobenius_norm_mul_le_lpOpNorm_two_mul Yᴴ Xᴴ

/-! ### Real matrices: outer products and the projection off a line -/

section Real

open WithLp

variable [DecidableEq n]

/-- For $A \in \mathbb{R}^{n \times n}$, $\|A\|_F^2 = \operatorname{tr}(A^T A)$. -/
theorem frobenius_norm_sq_eq_trace_transpose (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 = trace (Aᵀ * A) := by
  have h := frobenius_norm_sq_eq_trace (𝕜 := ℝ) A
  simpa [conjTranspose_eq_transpose_of_trivial] using h

/-- Let $A \in \mathbb{R}^{n \times n}$, let $s \in \mathbb{R}^n$ be nonzero, and let
$P = s s^T / (s^T s)$ be the orthogonal projector onto the line spanned by $s$. Then
$$\|A (I - P)\|_F^2 + \|AP\|_F^2 = \|A\|_F^2.$$

The proof uses the trace form $\|M\|_F^2 = \operatorname{tr}(M^T M)$ and that $P$ is symmetric
and idempotent. -/
theorem frobenius_norm_sq_mul_one_sub_add_sq_mul (A : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) :
    ‖A * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)‖ ^ 2 + ‖A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)‖ ^ 2
      = ‖A‖ ^ 2 := by
  set P : Matrix n n ℝ := (1 / (s ⬝ᵥ s)) • vecMulVec s s with hPdef
  have hss : s ⬝ᵥ s ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (by simpa using hs))
  have hPt : Pᵀ = P := by
    rw [hPdef, transpose_smul, transpose_vecMulVec]
  have hPP : P * P = P := by
    rw [hPdef, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, vecMulVec_smul,
      smul_smul, smul_smul]
    congr 1
    field_simp
  have hQt : (1 - P)ᵀ = 1 - P := by rw [transpose_sub, transpose_one, hPt]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hPP]
    abel
  have h1 : ‖A * (1 - P)‖ ^ 2 = trace (Aᵀ * A * (1 - P)) := by
    rw [frobenius_norm_sq_eq_trace_transpose, transpose_mul, hQt, Matrix.mul_assoc,
      trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, ← Matrix.mul_assoc]
  have h2 : ‖A * P‖ ^ 2 = trace (Aᵀ * A * P) := by
    rw [frobenius_norm_sq_eq_trace_transpose, transpose_mul, hPt, Matrix.mul_assoc,
      trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hPP, ← Matrix.mul_assoc]
  have h3 : ‖A‖ ^ 2 = trace (Aᵀ * A) := frobenius_norm_sq_eq_trace_transpose A
  rw [h1, h2, h3, ← trace_add, ← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]

/-- Let $A \in \mathbb{R}^{n \times n}$, let $s \in \mathbb{R}^n$ be nonzero, and let
$P = s s^T / (s^T s)$ be the orthogonal projector onto the line spanned by $s$. Then
$$\|A (I - P)\|_F \le \|A\|_F.$$

This follows from the Pythagorean identity `Matrix.frobenius_norm_sq_mul_one_sub_add_sq_mul`. -/
theorem frobenius_norm_mul_one_sub_le (A : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) :
    ‖A * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)‖ ≤ ‖A‖ := by
  have hsum := frobenius_norm_sq_mul_one_sub_add_sq_mul A hs
  have hle : ‖A * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    nlinarith [sq_nonneg ‖A * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)‖]
  exact le_of_sq_le_sq hle (norm_nonneg _)

omit [DecidableEq n] in
/-- Let $s \in \mathbb{R}^n$ be nonzero, and let $P = s s^T / (s^T s)$. Then $Ps = s$. -/
theorem smul_vecMulVec_mulVec_self {s : n → ℝ} (hs : s ≠ 0) :
    ((1 / (s ⬝ᵥ s)) • vecMulVec s s) *ᵥ s = s := by
  have hss : s ⬝ᵥ s ≠ 0 := by
    rw [dotProduct_self_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (by simpa using hs))
  rw [smul_mulVec, vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul, smul_smul, one_div,
    inv_mul_cancel₀ hss, one_smul]

/-- Let $A \in \mathbb{R}^{n \times n}$. The operator norm of $A$ on $\mathbb{R}^n$ with the
Euclidean norm is at most the Frobenius norm of $A$.

The operator is `Matrix.toEuclideanCLM A`. -/
theorem norm_toEuclideanCLM_le_frobenius_norm (A : Matrix n n ℝ) :
    ‖toEuclideanCLM (𝕜 := ℝ) A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have h := frobenius_norm_mulVec_le A (ofLp x)
  rwa [toLp_ofLp] at h

/-- Let $A \in \mathbb{R}^{n \times n}$. The Frobenius norm of $A$ is at most $\sqrt{n}$ times the
operator norm of $A$ on $\mathbb{R}^n$ with the Euclidean norm.

The operator is `Matrix.toEuclideanCLM A`. -/
theorem frobenius_norm_le_sqrt_card_mul_norm_toEuclideanCLM (A : Matrix n n ℝ) :
    ‖A‖ ≤ √(Fintype.card n : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) A‖ := by
  have h1 := frobenius_norm_le_sqrt_rank_mul_l2_opNorm A
  have h2 : lpOpNorm 2 A = ‖toEuclideanCLM (𝕜 := ℝ) A‖ := by
    rw [lpOpNorm]
    congr 1
  have h3 : (A.rank : ℝ) ≤ Fintype.card n := by exact_mod_cast A.rank_le_card_width
  calc ‖A‖ ≤ √(A.rank : ℝ) * lpOpNorm 2 A := h1
    _ ≤ √(Fintype.card n : ℝ) * ‖toEuclideanCLM (𝕜 := ℝ) A‖ := by
        rw [h2]
        gcongr

end Real

end Frobenius

/-! ### The bound $\|A\|_2 \le \sqrt{\|A\|_1 \|A\|_\infty}$ -/

section OneInfty

variable [DecidableEq n]

/-- Let $A \in \mathbb{K}^{m \times n}$. Every absolute row sum satisfies
$\sum_j |a_{ij}| \le \|A\|_\infty$. -/
theorem sum_norm_le_lpOpNorm_top (A : Matrix m n 𝕜) (i : m) : ∑ j, ‖A i j‖ ≤ lpOpNorm ⊤ A := by
  open scoped Matrix.Norms.Operator in
  rw [lpOpNorm_top, linfty_opNorm_def]
  have h : (∑ j, ‖A i j‖₊) ≤ univ.sup fun i => ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  push_cast at h'
  exact h'

/-- Let $A \in \mathbb{K}^{m \times n}$. Every absolute column sum satisfies
$\sum_i |a_{ij}| \le \|A\|_1$. -/
theorem sum_norm_le_lpOpNorm_one (A : Matrix m n 𝕜) (j : n) : ∑ i, ‖A i j‖ ≤ lpOpNorm 1 A := by
  rw [lpOpNorm_one_eq_sup_sum_norm]
  have h : (∑ i, ‖A i j‖₊) ≤ univ.sup fun j => ∑ i, ‖A i j‖₊ :=
    Finset.le_sup (f := fun j => ∑ i, ‖A i j‖₊) (mem_univ j)
  have h' := NNReal.coe_le_coe.mpr h
  push_cast at h'
  exact h'

/-- Let $A \in \mathbb{K}^{m \times n}$. Then
$$\|A\|_2^2 \le \|A\|_1 \|A\|_\infty,$$
that is, $\|A\|_2 \le \sqrt{\|A\|_1 \|A\|_\infty}$. This is stated in [quarteroni2000numerical],
§1.11.

Row by row, the weighted Cauchy–Schwarz inequality $(\sum_j |a_{ij}| |x_j|)^2 \le (\sum_j
|a_{ij}|)(\sum_j |a_{ij}| |x_j|^2)$ bounds $\|Ax\|_2^2$ by $\|A\|_\infty \sum_j |x_j|^2 \sum_i
|a_{ij}| \le \|A\|_\infty \|A\|_1 \|x\|_2^2$. No spectral theory is needed, so the statement
holds over $\mathbb{R}$ and over $\mathbb{C}$. -/
theorem l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm (A : Matrix m n 𝕜) :
    lpOpNorm 2 A ^ 2 ≤ lpOpNorm 1 A * lpOpNorm ⊤ A := by
  set C := lpOpNorm 1 A with hC
  set R := lpOpNorm ⊤ A with hR
  have hC0 : 0 ≤ C := lpOpNorm_nonneg 1 A
  have hR0 : 0 ≤ R := lpOpNorm_nonneg ⊤ A
  have hCR : 0 ≤ √(C * R) := Real.sqrt_nonneg _
  have key : lpOpNorm 2 A ≤ √(C * R) := by
    refine ContinuousLinearMap.opNorm_le_bound _ hCR fun x => ?_
    rw [lpCLM_apply]
    set v : n → 𝕜 := WithLp.ofLp x with hv
    have hx : ‖x‖ = ‖WithLp.toLp 2 v‖ := rfl
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hC0 hR0), hx, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    -- row by row
    have hrow : ∀ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := by
      intro i
      have h1 : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
        rw [mulVec_apply_eq_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_mul_le _ _)
      have h2 : (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => √‖A i j‖)
          (fun j => √‖A i j‖ * ‖v j‖)
        have e1 : ∀ j, √‖A i j‖ * (√‖A i j‖ * ‖v j‖) = ‖A i j‖ * ‖v j‖ := fun j => by
          rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
        have e2 : ∀ j, (√‖A i j‖) ^ 2 = ‖A i j‖ := fun j => Real.sq_sqrt (norm_nonneg _)
        have e3 : ∀ j, (√‖A i j‖ * ‖v j‖) ^ 2 = ‖A i j‖ * ‖v j‖ ^ 2 := fun j => by
          rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
        simpa only [e1, e2, e3] using hcs
      calc ‖(A *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 := h2
        _ ≤ R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (sum_norm_le_lpOpNorm_top A i)
              (Finset.sum_nonneg fun j _ => by positivity)
    calc ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ ∑ i, R * ∑ j, ‖A i j‖ * ‖v j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = R * ∑ j, (∑ i, ‖A i j‖) * ‖v j‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp_rw [Finset.sum_mul]
      _ ≤ R * ∑ j, C * ‖v j‖ ^ 2 := by
          gcongr with j
          exact sum_norm_le_lpOpNorm_one A j
      _ = C * R * ∑ j, ‖v j‖ ^ 2 := by rw [← Finset.mul_sum]; ring
  calc lpOpNorm 2 A ^ 2 ≤ (√(C * R)) ^ 2 := pow_le_pow_left₀ (lpOpNorm_nonneg 2 A) key 2
    _ = C * R := Real.sq_sqrt (mul_nonneg hC0 hR0)

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian. Then $\|A\|_2 \le \|A\|_\infty$. See
[cartis2022evaluation], §9.3.1.

The proof uses $\|A\|_1 = \|A\|_\infty$ (`Matrix.IsHermitian.lpOpNorm_one_eq_linfty_opNorm`), so
$\|A\|_2^2 \le \|A\|_1 \|A\|_\infty = \|A\|_\infty^2$. -/
theorem IsHermitian.l2_opNorm_le_linfty_opNorm {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    lpOpNorm 2 A ≤ lpOpNorm ⊤ A := by
  have h := l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm A
  rw [hA.lpOpNorm_one_eq_linfty_opNorm, ← lpOpNorm_top, ← sq] at h
  exact (pow_le_pow_iff_left₀ (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _) two_ne_zero).1 h

end OneInfty

/-!
### The maximum-row-sum norm and the entrywise order

In this section, `‖A‖` is the $\infty$-norm of a matrix (the scoped instance
`Matrix.Norms.Operator`), and `‖v‖` is the maximum norm of a vector. For a real matrix $A$, $|A|$ is
the matrix of the absolute values of the entries (`Matrix.abs`), and $A \le B$ entrywise is written
`A ≤ₑ B`.
-/

section EntrywiseLE

open scoped Matrix.Norms.Operator

/-- Let $A, B \in \mathbb{R}^{m \times n}$ with $|a_{ij}| \le |b_{ij}|$ for all $i$ and $j$. Then
$\|A\|_\infty \le \|B\|_\infty$, because the absolute row sums are monotone. This turns an
entrywise backward-error bound into a normwise one, as in (3.25), (3.65) and (3.67) of
[quarteroni2000numerical]. -/
theorem linfty_opNorm_le_of_abs_entrywiseLE {A B : Matrix m n ℝ} (h : A.abs ≤ₑ B.abs) :
    ‖A‖ ≤ ‖B‖ := by
  rw [linfty_opNorm_def, linfty_opNorm_def, NNReal.coe_le_coe]
  refine Finset.sup_mono_fun fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h i j

/-- For $A \in \mathbb{R}^{m \times n}$, $\||A|\|_\infty = \|A\|_\infty$. -/
theorem linfty_opNorm_abs (A : Matrix m n ℝ) : ‖A.abs‖ = ‖A‖ := by
  rw [linfty_opNorm_def, linfty_opNorm_def]
  simp only [Matrix.abs_apply, Real.nnnorm_abs]

/-- Let $A, B \in \mathbb{R}^{m \times n}$ and $c \ge 0$. If $|a_{ij}| \le c\, |b_{ij}|$ for all $i$
and $j$, then $\|A\|_\infty \le c \|B\|_\infty$. -/
theorem linfty_opNorm_le_mul_of_abs_entrywiseLE {A B : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : A.abs ≤ₑ c • B.abs) : ‖A‖ ≤ c * ‖B‖ := by
  have hle : A.abs.abs ≤ₑ (c • B.abs).abs := fun i j => by
    simp only [Matrix.abs_apply, Matrix.smul_apply, smul_eq_mul, abs_abs, abs_mul,
      abs_of_nonneg hc]
    exact h i j
  calc ‖A‖ = ‖A.abs‖ := (linfty_opNorm_abs A).symm
    _ ≤ ‖c • B.abs‖ := linfty_opNorm_le_of_abs_entrywiseLE hle
    _ = c * ‖B‖ := by rw [norm_smul, Real.norm_of_nonneg hc, linfty_opNorm_abs]

/-! ### Row sums, entries, and maximum norms of real vectors -/

/-- Let $B \in \mathbb{R}^{m \times n}$ and $c \ge 0$. If every absolute row sum satisfies
$\sum_j |b_{ij}| \le c$, then $\|B\|_\infty \le c$. -/
theorem linfty_opNorm_le_of_forall_sum_le {B : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |B i j| ≤ c) : ‖B‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def, ← NNReal.coe_mk c hc, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_mk]
  simpa only [coe_nnnorm, Real.norm_eq_abs] using h i

/-- Let $B \in \mathbb{R}^{m \times n}$. Every absolute row sum satisfies
$\sum_j |b_{ij}| \le \|B\|_\infty$. -/
theorem sum_abs_apply_le_linfty_opNorm (B : Matrix m n ℝ) (i : m) :
    ∑ j, |B i j| ≤ ‖B‖ := by
  rw [Matrix.linfty_opNorm_def]
  have := Finset.le_sup (f := fun i : m => ∑ j : n, ‖B i j‖₊) (Finset.mem_univ i)
  rw [← NNReal.coe_le_coe, NNReal.coe_sum] at this
  simpa only [coe_nnnorm, Real.norm_eq_abs] using this

/-- Let $B \in \mathbb{R}^{m \times n}$. Every entry satisfies $|b_{ij}| \le \|B\|_\infty$. -/
theorem abs_apply_le_linfty_opNorm (B : Matrix m n ℝ) (i : m) (j : n) :
    |B i j| ≤ ‖B‖ :=
  (Finset.single_le_sum (f := fun j => |B i j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)).trans (Matrix.sum_abs_apply_le_linfty_opNorm B i)

/-- Let $v, w \in \mathbb{R}^n$ with $|v_i| \le w_i$ for every $i$. Then
$\|v\|_\infty \le \|w\|_\infty$. -/
theorem norm_le_norm_of_abs_le {v w : n → ℝ} (h : |v| ≤ w) : ‖v‖ ≤ ‖w‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg w)]
  intro i
  calc ‖v i‖ = |v i| := Real.norm_eq_abs _
    _ ≤ w i := h i
    _ ≤ ‖w i‖ := le_abs_self _
    _ ≤ ‖w‖ := norm_le_pi_norm w i

/-- For $v \in \mathbb{R}^n$, the vector $|v|$ of the absolute values of the entries has the maximum
norm $\||v|\|_\infty = \|v\|_\infty$. -/
theorem norm_abs_eq (v : n → ℝ) : ‖|v|‖ = ‖v‖ := by
  rw [Pi.norm_def, Pi.norm_def]
  congr 1
  refine congrArg _ (funext fun i => ?_)
  simp [Pi.abs_apply, Real.nnnorm_abs]

/-- Let $M \in \mathbb{R}^{n \times n}$ have nonnegative entries, and let $\mathbf{1}$ be the vector
of ones. Then the largest absolute row sum of $M$ is the maximum norm of the vector of its row
sums:
$$\|M \mathbf{1}\|_\infty = \|M\|_\infty.$$
-/
theorem norm_mulVec_one_of_entrywiseNonneg {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg) :
    ‖M *ᵥ (1 : n → ℝ)‖ = ‖M‖ := by
  rw [Pi.norm_def, linfty_opNorm_def]
  congr 1
  refine congrArg _ (funext fun i => ?_)
  rw [← NNReal.coe_inj, coe_nnnorm, NNReal.coe_sum, Real.norm_eq_abs]
  simp only [coe_nnnorm, Real.norm_eq_abs]
  rw [mulVec, dotProduct]
  simp only [Pi.one_apply, mul_one]
  rw [Finset.abs_sum_of_nonneg fun j _ => hM.apply i j]
  exact Finset.sum_congr rfl fun j _ => (abs_of_nonneg (hM.apply i j)).symm

/-- Let $E \in \mathbb{R}^{m \times n}$, $B \in \mathbb{R}^{m' \times n}$, $\gamma \ge 0$, and let
$e$ be a map from the row indices of $E$ to the row indices of $B$. If
$|E_{ij}| \le \gamma\, B_{e(i) j}$ for all $i$ and $j$, then
$$\|E\|_\infty \le \gamma \|B\|_\infty.$$
This is the normwise form of the backward error of Gaussian elimination with pivoting, where $e$
is the pivot permutation.

The hypothesis is `E.abs ≤ₑ γ • B.submatrix e id`, with the entries of $B$ and not their
absolute values on the right. -/
theorem linfty_opNorm_le_of_abs_le_smul_submatrix {m' : Type*} [Fintype m'] {E : Matrix m n ℝ}
    {B : Matrix m' n ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (e : m → m') (h : E.abs ≤ₑ γ • B.submatrix e id) :
    ‖E‖ ≤ γ * ‖B‖ := by
  refine linfty_opNorm_le_of_forall_sum_le (mul_nonneg hγ (norm_nonneg _)) fun i => ?_
  calc ∑ j, |E i j| ≤ ∑ j, γ * |B (e i) j| := Finset.sum_le_sum fun j _ => by
        have := h i j
        simp only [Matrix.abs_apply, Matrix.smul_apply, submatrix_apply, id, smul_eq_mul] at this
        exact this.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hγ)
    _ = γ * ∑ j, |B (e i) j| := by rw [Finset.mul_sum]
    _ ≤ γ * ‖B‖ := mul_le_mul_of_nonneg_left (sum_abs_apply_le_linfty_opNorm B (e i)) hγ

/-- Let $B \in \mathbb{R}^{m \times n}$ and $c \ge 0$. If $|b_{ij}| \le c$ for all $i$ and $j$, then
$\|B\|_\infty \le nc$, where $n$ is the number of columns. -/
theorem linfty_opNorm_le_card_mul_of_abs_le {B : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |B i j| ≤ c) : ‖B‖ ≤ Fintype.card n * c :=
  linfty_opNorm_le_of_forall_sum_le (by positivity) fun i =>
    (Finset.sum_le_sum fun j _ => h i j).trans (by simp)

end EntrywiseLE

/-! ### The Frobenius norm and the entrywise order -/

section EntrywiseLEFrobenius

open scoped Matrix.Norms.Frobenius

/-- Let $B \in \mathbb{R}^{m \times n}$. Every entry satisfies $|b_{ij}| \le \|B\|_F$. This is the
real form of `Matrix.norm_entry_le_frobenius_norm`, and the Frobenius form of
`Matrix.abs_apply_le_linfty_opNorm`. -/
theorem abs_apply_le_frobenius_norm (B : Matrix m n ℝ) (i : m) (j : n) : |B i j| ≤ ‖B‖ := by
  rw [← Real.norm_eq_abs]
  exact norm_entry_le_frobenius_norm B i j

/-- For $A \in \mathbb{R}^{m \times n}$, the matrix $|A|$ of the absolute values of the entries has
the Frobenius norm $\||A|\|_F = \|A\|_F$. -/
theorem frobenius_norm_abs (A : Matrix m n ℝ) : ‖A.abs‖ = ‖A‖ :=
  frobenius_norm_map_eq A _ fun a => by simp

/-- Let $A$ and $B$ be $m \times n$ matrices with entries in two seminormed groups. If
$\|a_{ij}\| \le \|b_{ij}\|$ for all $i$ and $j$, then $\|A\|_F \le \|B\|_F$. For example, $A$
can be a complex matrix that is bounded entrywise by a real matrix $B$. -/
theorem frobenius_norm_le_of_forall_norm_le {α β : Type*} [SeminormedAddCommGroup α]
    [SeminormedAddCommGroup β] {A : Matrix m n α} {B : Matrix m n β}
    (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) : ‖A‖ ≤ ‖B‖ := by
  rw [frobenius_norm_def, frobenius_norm_def]
  gcongr with i _ j _
  exact h i j

/-- Let $A, B \in \mathbb{R}^{m \times n}$ with $|a_{ij}| \le |b_{ij}|$ for all $i$ and $j$. Then
$\|A\|_F \le \|B\|_F$. This is the Frobenius form of
`Matrix.linfty_opNorm_le_of_abs_entrywiseLE`. -/
theorem frobenius_norm_le_of_abs_entrywiseLE {A B : Matrix m n ℝ} (h : A.abs ≤ₑ B.abs) :
    ‖A‖ ≤ ‖B‖ :=
  frobenius_norm_le_of_forall_norm_le fun i j => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact h i j

/-- Let $A, B \in \mathbb{R}^{m \times n}$ and $c \ge 0$. If $|a_{ij}| \le c\, |b_{ij}|$ for all $i$
and $j$, then $\|A\|_F \le c \|B\|_F$. -/
theorem frobenius_norm_le_of_forall_abs_le {A B : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) : ‖A‖ ≤ c * ‖B‖ := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2

/-- Let $A, B \in \mathbb{R}^{m \times n}$ and $c \ge 0$. If $|A| \le c\, |B|$ entrywise, then
$\|A\|_F \le c \|B\|_F$. This is the Frobenius form of
`Matrix.linfty_opNorm_le_mul_of_abs_entrywiseLE`. -/
theorem frobenius_norm_le_mul_of_abs_entrywiseLE {A B : Matrix m n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : A.abs ≤ₑ c • B.abs) : ‖A‖ ≤ c * ‖B‖ :=
  frobenius_norm_le_of_forall_abs_le hc fun i j => by simpa using h i j

end EntrywiseLEFrobenius

/-! ### The spectral condition number of a positive definite matrix -/

section PosDef

open scoped Matrix.Norms.L2Operator ComplexOrder

variable [DecidableEq n] [Nonempty n]

/-- Let $n \ge 1$, and let $A \in \mathbb{K}^{n \times n}$ be positive definite, with the
eigenvalues $\lambda_i > 0$. Then the spectral condition number of $A$ is
$$\kappa_2(A) = \frac{\lambda_{\max}}{\lambda_{\min}}.$$
This is (3.5) of [quarteroni2000numerical].

The condition number is `NormedRing.condNumber` for the spectral norm. The eigenvalues are
`hA.1.eigenvalues`, Mathlib's eigenvalues of a Hermitian matrix, in no particular order;
$\lambda_{\max}$ and $\lambda_{\min}$ are their supremum and infimum. -/
theorem PosDef.condNumber_l2_eq_div_eigenvalues {A : Matrix n n 𝕜} (hA : A.PosDef) :
    κ A = (⨆ i, hA.1.eigenvalues i) / ⨅ i, hA.1.eigenvalues i := by
  have hbddA : BddAbove (Set.range hA.1.eigenvalues) := (Set.finite_range _).bddAbove
  have hbddB : BddBelow (Set.range hA.1.eigenvalues) := (Set.finite_range _).bddBelow
  have hpos : ∀ i, 0 < hA.1.eigenvalues i := hA.eigenvalues_pos
  obtain ⟨imax, himax⟩ := exists_eq_ciSup_of_finite (f := hA.1.eigenvalues)
  obtain ⟨imin, himin⟩ := exists_eq_ciInf_of_finite (f := hA.1.eigenvalues)
  have hmin_pos : 0 < ⨅ i, hA.1.eigenvalues i := himin ▸ hpos imin
  -- the eigenvalues of `toEuclideanLin A` are `hA.1.eigenvalues`
  have heig : ∀ μ : 𝕜, Module.End.HasEigenvalue (toEuclideanLin A) μ ↔
      ∃ i, (hA.1.eigenvalues i : 𝕜) = μ := fun μ => hA.1.hasEigenvalue_toEuclideanLin_iff μ
  have hnorm : ‖A‖ = ⨆ i, hA.1.eigenvalues i := by
    refine hA.1.l2_opNorm_eq (fun μ hμ => ?_) ⟨hA.1.eigenvalues imax, (heig _).2 ⟨imax, rfl⟩, ?_⟩
    · obtain ⟨i, rfl⟩ := (heig μ).1 hμ
      rw [RCLike.ofReal_re, abs_of_pos (hpos i)]
      exact le_ciSup hbddA i
    · rw [RCLike.ofReal_re, abs_of_pos (hpos imax), himax]
  have hinv : ‖A⁻¹‖ = (⨅ i, hA.1.eigenvalues i)⁻¹ := by
    refine hA.1.l2_opNorm_inv_eq hmin_pos (fun μ hμ => ?_)
      ⟨hA.1.eigenvalues imin, (heig _).2 ⟨imin, rfl⟩, ?_⟩
    · obtain ⟨i, rfl⟩ := (heig μ).1 hμ
      rw [RCLike.ofReal_re, abs_of_pos (hpos i)]
      exact ciInf_le hbddB i
    · rw [RCLike.ofReal_re, abs_of_pos (hpos imin), himin]
  rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse, hnorm, hinv, div_eq_mul_inv]

end PosDef

end Matrix
