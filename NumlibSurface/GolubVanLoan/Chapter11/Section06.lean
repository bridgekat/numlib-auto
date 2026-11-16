/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Multigrid.Basic
import Numlib.Multigrid.ModelProblem
import NumlibSurface.GolubVanLoan.Chapter11.Section02

/-!
# Golub and Van Loan, Section 11.6: The multigrid framework

This module formalizes §11.6 of [golub2013matrix], the two-grid analysis of multigrid for the
one-dimensional model problem. The fine grid has $n = 2m + 1$ interior points with mesh width
$h = 1/(n + 1)$, and the coarse grid has $m$ points with mesh width $2h$. The model matrix is
$A^h = h^{-2}\,\mathrm{tridiag}(-1, 2, -1)$, whose eigenvectors are the discrete sine vectors $q_j$.
The module states this eigen-decomposition ((11.6.2)–(11.6.10)), weighted Jacobi as a smoother
((11.6.11)–(11.6.12) and the choice $\omega = 2/3$, §11.6.2), the restriction $R^{2h}_h$ and the
prolongation $P^h_{2h}$ ((11.6.13)–(11.6.15)), the two-grid cycle and its error operator
$E^h = I - P^h_{2h} (A^{2h})^{-1} R^{2h}_h A^h$ ((11.6.16)–(11.6.19)), Lemma 11.6.1 and Theorem
11.6.2, and the damping of the error mode by mode ((11.6.20)–(11.6.22), §11.6.3).

The analysis of the source is an exact computation in the sine eigenbasis, and so is this module. It
uses the discrete sine vectors `Matrix.sineVec` of `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`
and the mode identities of `Numlib.Multigrid.ModelProblem`, which describe how linear interpolation,
full weighting and the exact coarse-grid correction act on a fine mode $j$, its alias $n - j + 1$
and the middle mode $m + 1$. The bridge `GolubVanLoan.Chapter11.twoGridError_eq_coarseCorrection`
connects the section to the abstract two-grid theory of `Numlib.Multigrid.Basic`: $E^h$ is the
$A^h$-orthogonal coarse-grid correction `Multigrid.coarseCorrection` of the prolongation.

## Main definitions

* Equation (11.6.3), `GolubVanLoan.Chapter11.modelA`: the model matrix
  $A^h = h^{-2}\,\mathrm{tridiag}(-1, 2, -1)$.
* Equation (11.6.5), `GolubVanLoan.Chapter11.modelAEigenvalues`: the eigenvalues $\lambda_j^h$ of
  $A^h$.
* Equation (11.6.6), `GolubVanLoan.Chapter11.modelq` and `GolubVanLoan.Chapter11.modelQ`: the
  normalized sine vectors $q_j$ and the matrix $Q^h$.
* Equations (11.6.7)–(11.6.8), `GolubVanLoan.Chapter11.modelS` and `GolubVanLoan.Chapter11.modelC`:
  the diagonal matrices $S^h$ and $C^h$.
* §11.6.2, `GolubVanLoan.Chapter11.weightedJacobiTau`: the eigenvalues $\tau_j^{h,\omega}$ of the
  weighted Jacobi iteration matrix.
* §11.6.2, `GolubVanLoan.Chapter11.highFreqDamping` and `GolubVanLoan.Chapter11.optimalOmega`: the
  high-frequency damping factor $\mu(\omega)$ and its minimizer $\omega_*$.
* Equation (11.6.14), `GolubVanLoan.Chapter11.restrictionMatrix` and
  `GolubVanLoan.Chapter11.prolongationMatrix`: the restriction $R^{2h}_h$ and the prolongation
  $P^h_{2h}$.
* Equation (11.6.15), `GolubVanLoan.Chapter11.modelB`: the matrix $B^h = \mathrm{tridiag}(1, 2, 1)$.
* Equation (11.6.16), `GolubVanLoan.Chapter11.twoGridCycle` and
  `GolubVanLoan.Chapter11.coarseGridCorrection`: the two-grid cycle and its coarse-grid correction
  steps.
* Equation (11.6.18), `GolubVanLoan.Chapter11.twoGridErrorOperator`: the two-grid error operator
  $E^h$.
* Equation (11.6.20), `GolubVanLoan.Chapter11.transferBlock`: the block matrix of Lemma 11.6.1.
* Equation (11.6.21), `GolubVanLoan.Chapter11.twoGridBlock`: the block matrix of Theorem 11.6.2.

## Main results

* Equation (11.6.4), `GolubVanLoan.Chapter11.equation_11_6_4`: $Q^h$ is orthogonal and
  $(Q^h)^T A^h Q^h = \Lambda^h$.
* Equation (11.6.9), `GolubVanLoan.Chapter11.equation_11_6_9`: the eigenvalues of $A^h$ in terms of
  $S^h$ and $C^h$.
* Equation (11.6.10), `GolubVanLoan.Chapter11.equation_11_6_10`: the even rows of $Q^h$ are scaled
  copies of $Q^{2h}$.
* Equation (11.6.11), `GolubVanLoan.Chapter11.equation_11_6_11`: weighted Jacobi is the splitting
  with $M = \omega^{-1} D$, and $G^{h,\omega} = I - (\omega h^2/2) A^h$.
* Equation (11.6.12), `GolubVanLoan.Chapter11.equation_11_6_12`: weighted Jacobi damps the sine
  coefficient $j$ by $\tau_j^{h,\omega}$ per step.
* §11.6.2, `GolubVanLoan.Chapter11.weightedJacobi_tau_mem`: for $0 < \omega \le 1$ the
  $\tau_j^{h,\omega}$ decrease and lie in $(-1, 1)$.
* §11.6.2, `GolubVanLoan.Chapter11.weightedJacobi_twoThirds`: for $\omega = 2/3$ the high-frequency
  damping factor is $1/3$.
* §11.6.2, `GolubVanLoan.Chapter11.weightedJacobi_optimalOmega`: the optimal $\omega$ for the high
  frequencies, and its limit $2/3$.
* Equation (11.6.14), `GolubVanLoan.Chapter11.restrictionMatrix_eq`,
  `GolubVanLoan.Chapter11.prolongationMatrix_eq` and
  `GolubVanLoan.Chapter11.restrictionMatrix_eq_half_transpose`: the restriction is full weighting,
  the prolongation is linear interpolation, and $R = \frac12 P^T$.
* §11.6.3, `GolubVanLoan.Chapter11.restriction_prolongation_apply`: the action of the transfer
  operators on vectors.
* `GolubVanLoan.Chapter11.galerkin_coarse_eq`: $R^{2h}_h A^h P^h_{2h} = A^{2h}$.
* Equation (11.6.17), `GolubVanLoan.Chapter11.equation_11_6_17`: the coarse-grid correction
  multiplies the error by $E^h$.
* Equation (11.6.19), `GolubVanLoan.Chapter11.equation_11_6_19`: the two-grid cycle multiplies the
  error by $(G^h)^{p_2} E^h (G^h)^{p_1}$.
* Lemma 11.6.1, `GolubVanLoan.Chapter11.lemma_11_6_1`: the transfer operators in the sine bases.
* Theorem 11.6.2, `GolubVanLoan.Chapter11.theorem_11_6_2`: $E^h Q^h = Q^h \cdot$ the block matrix of
  (11.6.21).
* Equation (11.6.22), `GolubVanLoan.Chapter11.equation_11_6_22`: the action of $E^h$ on the sine
  vectors.
* `GolubVanLoan.Chapter11.twoGridError_eq_coarseCorrection`: $E^h$ is the coarse-grid correction of
  the backbone.
* §11.6.3, `GolubVanLoan.Chapter11.twoGrid_error_coeffs` and
  `GolubVanLoan.Chapter11.twoGrid_damping_bounds`: the error of one cycle, mode by mode, and the
  bounds that damp it.

## Conventions

* The source takes $n = 2^k - 1$, $m = 2^{k-1} - 1$ and $h = 1/2^k$. The module is indexed by the
  coarse size $m$, and the fine grid is `Fin (2 * m + 1)`. A matrix of a grid of $n$ points has mesh
  width $h = 1/(n + 1)$, so `GolubVanLoan.Chapter11.modelA n` is the source's $A^h$ for $n = 2m + 1$
  and its $A^{2h}$ for $n = m$.
* Indices are 0-based. The source's $q_j$, $j = 1{:}n$, is `modelq n (j - 1)`. For a coarse index
  $j$, the fine mode $j$ is `Multigrid.fineIndex j`, the source's alias $q_{n-j+1}$ is
  `Multigrid.aliasIndex j` (0-based $2m - j$), the source's middle mode $q_{m+1}$ is
  `Multigrid.middleIndex m`, and the source's even fine point $2j$ is
  `GolubVanLoan.Chapter11.evenIndex j` (0-based $2j + 1$).
* The block matrices of (11.6.9), (11.6.20) and (11.6.21) are indexed in the source by $m + 1 + m$
  rows. They are stated entry by entry on the three kinds of indices above. The exchange permutation
  $\mathcal{E}_m$ of the source is what turns the source's block index into `Multigrid.aliasIndex`.
* The angles are $\theta_j = (j + 1)\pi/(2m + 2)$ (0-based), `Multigrid.modeAngle m j`, and
  $s_j = \sin(\theta_j/2)$, $c_j = \cos(\theta_j/2)$.

## Implementation notes

* The two-grid cycle (11.6.16) is a program over a rounding hook, built from the gaxpy Algorithm
  1.1.3 and the entrywise `GolubVanLoan.Chapter01.vecSub` and `GolubVanLoan.Chapter01.vecAdd`. The
  smoother and the coarse solve are routine arguments, because the source delegates both: the
  weighted Jacobi iteration to §11.6.2, the coarse system to recursion. Their exact semantics are
  the weighted Jacobi step and $(A^{2h})^{-1}$.

## Deviations from the source

* **Grid sizes** (generalization). The source takes $n = 2^k - 1$. Everything it proves uses only
  $n = 2m + 1$, and the results hold for every $m$. See `GolubVanLoan.Chapter11.modelA`.
* **Equation (11.6.16)** (typo). The source updates $u_c$ instead of $u_{p_1}$ in the coarse-grid
  correction. See `GolubVanLoan.Chapter11.coarseGridCorrection`.
* **§11.6.2**, the optimal $\omega$ (reading). The source says that the minimization of the
  high-frequency damping factor "is essentially solved by $\omega_{\mathrm{opt}} = 2/3$"; the
  statement gives the exact minimizer and its limit $2/3$. See
  `GolubVanLoan.Chapter11.weightedJacobi_optimalOmega`.

## Not formalized

* **Equation (11.6.1)**, the differential equation and the discretization claim.
* **Equation (11.6.13)**, the example matrices for $n = 7$.
* **Equation (11.6.21)**, the instance for $n = 7$, which the source prints with a row missing.
* **The V-cycle `mgV`, full multigrid and §11.6.5.** The text states no property of them beyond flop
  counts and the heuristic that the rate of convergence is independent of $n$.
* The Problems.
-/

open Matrix Finset
open scoped Matrix

namespace GolubVanLoan.Chapter11

open Multigrid

/-! ### The model problem and its eigen-decomposition -/

/-- **Equation (11.6.3)** of [golub2013matrix]. For a grid of $n$ interior points with mesh width
$h = 1/(n + 1)$, the model matrix is
$$A^h = h^{-2}\,\mathrm{tridiag}(-1, 2, -1) \in \mathbb{R}^{n \times n}.$$
It is the source's $A^h$ for $n = 2m + 1$ and its coarse matrix $A^{2h}$ for $n = m$.

**Generalization.** The source takes $n = 2^k - 1$ and $m = 2^{k-1} - 1$. The results of this
module use only $n = 2m + 1$ and hold for every $m$.

The matrix is `(n + 1)^2 • GolubVanLoan.Chapter11.modelT n`. -/
noncomputable def modelA (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (((n : ℝ) + 1) ^ 2) • modelT n

/-- The model matrix $A^h$ is $(n + 1)^2$ times `Matrix.symmTridiagonalToeplitz n (-1) 2`. -/
private theorem modelA_eq (n : ℕ) :
    modelA n = (((n : ℝ) + 1) ^ 2) • symmTridiagonalToeplitz n (-1) 2 := rfl

/-- **Equation (11.6.5)** of [golub2013matrix]. The eigenvalues of $A^h$ are
$$\lambda_j^h = \frac{4}{h^2} \sin^2\Big(\frac{j\pi}{2(n + 1)}\Big), \qquad j = 1{:}n.$$

The index is 0-based: entry $j$ uses $j + 1$ in place of $j$. -/
noncomputable def modelAEigenvalues (n : ℕ) : Fin n → ℝ := fun j =>
  4 * ((n : ℝ) + 1) ^ 2 * Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ^ 2

/-- **Equation (11.6.6)** of [golub2013matrix], one column. The normalized sine vector
$$q_j = \sqrt{\frac{2}{n + 1}}\, (\sin \theta_j, \sin 2\theta_j, \dots, \sin n\theta_j)^T,
  \qquad \theta_j = \frac{j\pi}{n + 1}.$$

The index is 0-based, and the vector is a multiple of `Matrix.sineVec n j`. -/
noncomputable def modelq (n : ℕ) (j : Fin n) : Fin n → ℝ :=
  Real.sqrt (2 / ((n : ℝ) + 1)) • sineVec n j

/-- **Equation (11.6.6)** of [golub2013matrix]. The matrix $Q^h = [q_1 \cdots q_n] \in \mathbb{R}^{n
\times n}$ of the normalized sine vectors. -/
noncomputable def modelQ (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => modelq n j i

/-- **Equation (11.6.7)** of [golub2013matrix]. For $n = 2m + 1$, the diagonal matrix
$$S^h = \mathrm{diag}(s_1^2, \dots, s_m^2), \qquad s_j = \sin\Big(\frac{j\pi}{2(n + 1)}\Big).$$

The angle is half the fine mode angle `Multigrid.modeAngle m j`, which is $(j + 1)\pi/(2m + 2)$
0-based. -/
noncomputable def modelS (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  diagonal fun j => Real.sin (modeAngle m j / 2) ^ 2

/-- **Equation (11.6.8)** of [golub2013matrix]. For $n = 2m + 1$, the diagonal matrix
$$C^h = \mathrm{diag}(c_1^2, \dots, c_m^2), \qquad c_j = \cos\Big(\frac{j\pi}{2(n + 1)}\Big).$$
It is the twin of $S^h$: $S^h + C^h = I$. -/
noncomputable def modelC (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  diagonal fun j => Real.cos (modeAngle m j / 2) ^ 2

/-- The columns of $Q^h$ are orthonormal: $q_k^T q_l = 1$ if $k = l$ and $0$ otherwise. -/
private theorem modelq_dotProduct (n : ℕ) (k l : Fin n) :
    modelq n k ⬝ᵥ modelq n l = if k = l then 1 else 0 := by
  rw [modelq, modelq, smul_dotProduct, dotProduct_smul, dotProduct_sineVec, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
  split_ifs
  · field_simp
  · simp

/-- The matrix $Q^h$ satisfies $(Q^h)^T Q^h = I$. -/
theorem modelQ_transpose_mul (n : ℕ) : (modelQ n)ᵀ * modelQ n = 1 := by
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply, ← modelq_dotProduct]
  rfl

/-- The matrix $Q^h$ satisfies $Q^h (Q^h)^T = I$. -/
private theorem modelQ_mul_transpose (n : ℕ) : modelQ n * (modelQ n)ᵀ = 1 :=
  mul_eq_one_comm.1 (modelQ_transpose_mul n)

/-- The matrix $Q^h$ is nonsingular, with inverse $(Q^h)^T$. -/
private theorem inv_modelQ (n : ℕ) : (modelQ n)⁻¹ = (modelQ n)ᵀ :=
  inv_eq_left_inv (modelQ_transpose_mul n)

/-- The matrix $Q^h$ is nonsingular. -/
private theorem isUnit_modelQ (n : ℕ) : IsUnit (modelQ n) :=
  (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (modelQ_transpose_mul n))

/-- Each $q_j$ is an eigenvector of $A^h$ with eigenvalue $\lambda_j^h$:
$A^h q_j = \lambda_j^h q_j$.

These are the scaled Dirichlet–Dirichlet eigenpairs of §4.8.6,
`GolubVanLoan.Chapter04.dd_eigen`. -/
theorem modelA_mulVec_modelq (n : ℕ) (j : Fin n) :
    modelA n *ᵥ modelq n j = modelAEigenvalues n j • modelq n j := by
  have h := (GolubVanLoan.Chapter04.dd_eigen n).1 j
  rw [show (fun k => dst1 n k j) = sineVec n j from funext fun k => dst1_apply_eq_sineVec k j]
    at h
  rw [modelA_eq, modelq, smul_mulVec, mulVec_smul, h, smul_smul, smul_smul, smul_smul,
    modelAEigenvalues]
  congr 1
  ring

/-- The matrix $A^h$ satisfies $A^h Q^h = Q^h \Lambda^h$ with $\Lambda^h =
\mathrm{diag}(\lambda_1^h, \dots, \lambda_n^h)$. -/
private theorem modelA_mul_modelQ (n : ℕ) :
    modelA n * modelQ n = modelQ n * diagonal (modelAEigenvalues n) := by
  ext i j
  rw [mul_diagonal]
  change (modelA n *ᵥ modelq n j) i = modelq n j i * _
  rw [modelA_mulVec_modelq, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **Equation (11.6.4)** of [golub2013matrix]. The matrix $A^h$ has the known Schur decomposition
$$(Q^h)^T A^h Q^h = \Lambda^h = \mathrm{diag}(\lambda_1^h, \dots, \lambda_n^h),$$
with $Q^h$ orthogonal: $(Q^h)^T Q^h = I$. -/
theorem equation_11_6_4 (n : ℕ) :
    (modelQ n)ᵀ * modelQ n = 1 ∧
      (modelQ n)ᵀ * modelA n * modelQ n = diagonal (modelAEigenvalues n) := by
  refine ⟨modelQ_transpose_mul n, ?_⟩
  rw [Matrix.mul_assoc, modelA_mul_modelQ, ← Matrix.mul_assoc, modelQ_transpose_mul,
    Matrix.one_mul]

/-- For $n = 2m + 1$, $\sqrt{2/(n + 1)} = \sqrt{2/(m + 1)}/\sqrt{2}$: the normalizations of the fine
and the coarse sine bases. -/
private theorem sqrt_fine (m : ℕ) :
    Real.sqrt (2 / (((2 * m + 1 : ℕ) : ℝ) + 1)) = Real.sqrt (2 / ((m : ℝ) + 1)) / Real.sqrt 2 := by
  rw [eq_div_iff (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  push_cast
  field_simp
  ring

/-- **Equation (11.6.9)** of [golub2013matrix]. Let $n = 2m + 1$ and $h = 1/(n + 1)$. Then
$$\Lambda^h = \frac{4}{h^2}\, \mathrm{diag}\big(S^h, \tfrac12, \mathcal{E}_m C^h
  \mathcal{E}_m\big),$$
stated entry by entry: for $j = 1{:}m$, the eigenvalue at the fine mode $j$ is $(4/h^2) s_j^2$,
the eigenvalue at the middle mode $m + 1$ is $(4/h^2) \cdot \frac12$, and the eigenvalue at the
alias $n - j + 1$ is $(4/h^2) c_j^2$.

The source leaves the proof to Problem P11.6.1. The alias is 0-based $2m - j$. -/
theorem equation_11_6_9 (m : ℕ) (j : Fin m) :
    modelAEigenvalues (2 * m + 1) (fineIndex j) =
        4 * (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2 * modelS m j j ∧
      modelAEigenvalues (2 * m + 1) (middleIndex m) =
        4 * (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2 * (1 / 2) ∧
      modelAEigenvalues (2 * m + 1) (aliasIndex j) =
        4 * (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2 * modelC m j j := by
  have hj : (j : ℕ) ≤ 2 * m := by have := j.isLt; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [modelAEigenvalues, modelS, diagonal_apply_eq]
    congr 3
    rw [fineIndex, modeAngle]
    push_cast
    field_simp
    ring
  · rw [modelAEigenvalues]
    have e : (((middleIndex m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
        Real.pi / 4 := by
      rw [middleIndex]
      push_cast
      field_simp
      ring
    rw [e, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
    ring
  · rw [modelAEigenvalues, modelC, diagonal_apply_eq]
    have e : (((aliasIndex j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
        Real.pi / 2 - modeAngle m j / 2 := by
      rw [aliasIndex, Fin.val_mk, Nat.cast_sub hj, modeAngle]
      push_cast
      field_simp
      ring
    rw [e, Real.sin_pi_div_two_sub]

/-- The fine grid point of the coarse point $j$: the source's even fine point $2j$, which is
$2j + 1$ 0-based. -/
def evenIndex {m : ℕ} (j : Fin m) : Fin (2 * m + 1) := ⟨2 * j + 1, by omega⟩

/-- **Equation (11.6.10)** of [golub2013matrix]. Let $n = 2m + 1$. The even rows of $Q^h$ are scaled
copies of $Q^{2h}$:
$$Q^h(2{:}2{:}2m, :) = \frac{1}{\sqrt{2}} \big[\, Q^{2h} \mid 0 \mid -Q^{2h} \mathcal{E}_m
  \,\big],$$
stated entry by entry: for coarse indices $q$ and $l$, the entry of $Q^h$ in the even row of $q$
is $Q^{2h}_{ql}/\sqrt{2}$ in the column of the fine mode $l$, $0$ in the column of the middle
mode, and $-Q^{2h}_{ql}/\sqrt{2}$ in the column of the alias of $l$.

The source leaves the proof to Problem P11.6.1. -/
theorem equation_11_6_10 (m : ℕ) (q l : Fin m) :
    modelQ (2 * m + 1) (evenIndex q) (fineIndex l) = modelQ m q l / Real.sqrt 2 ∧
      modelQ (2 * m + 1) (evenIndex q) (middleIndex m) = 0 ∧
      modelQ (2 * m + 1) (evenIndex q) (aliasIndex l) = -modelQ m q l / Real.sqrt 2 := by
  have hfine : sineVec (2 * m + 1) (fineIndex l) (evenIndex q) = sineVec m l q := by
    rw [sineVec_fineIndex, sineVec_coarse, evenIndex]
    congr 1
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [modelQ, of_apply, modelq, Pi.smul_apply, smul_eq_mul, hfine, sqrt_fine]
    ring
  · simp only [modelQ, of_apply, modelq, Pi.smul_apply, smul_eq_mul, sineVec_middleIndex,
      evenIndex]
    have e : ((((2 * (q : ℕ) + 1 : ℕ) : ℕ) : ℝ) + 1) * (Real.pi / 2) =
        (((q : ℕ) + 1 : ℕ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [e, Real.sin_nat_mul_pi, mul_zero]
  · have hsign : (-1 : ℝ) ^ ((evenIndex q : Fin (2 * m + 1)) : ℕ) = -1 := by
      rw [evenIndex]
      dsimp only
      rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    simp only [modelQ, of_apply, modelq, Pi.smul_apply, smul_eq_mul, sineVec_aliasIndex, hsign,
      hfine, sqrt_fine]
    ring

/-! ### Weighted Jacobi as a smoother -/

/-- The diagonal of $A^h$ is $(2/h^2) I$. -/
private theorem diagPart_modelA (n : ℕ) :
    diagPart (modelA n) = (2 * ((n : ℝ) + 1) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rw [diagPart_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [modelA_eq, Matrix.smul_apply, symmTridiagonalToeplitz_apply_self, smul_eq_mul, smul_eq_mul]
    ring
  · simp

/-- The diagonal of the model matrix $A^h$ is nonsingular. -/
theorem isUnit_diagPart_modelA (n : ℕ) : IsUnit (diagPart (modelA n)) := by
  rw [isUnit_diagPart_iff]
  intro i
  have := congrFun (congrFun (diagPart_modelA n) i) i
  rw [diagPart_apply, ite_eq_left rfl, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
    mul_one] at this
  rw [this]
  positivity

/-- For $c \neq 0$ and a nonsingular matrix $B$, $(cB)^{-1} = c^{-1} B^{-1}$. -/
private theorem inv_smul_of_isUnit' {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : c ≠ 0)
    {B : Matrix ι ι ℝ} (hB : IsUnit B) : (c • B)⁻¹ = c⁻¹ • B⁻¹ :=
  inv_eq_left_inv (by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hB), one_smul])

/-- **Equation (11.6.11)** of [golub2013matrix]. Let $\omega \neq 0$. For every
$A \in \mathbb{R}^{n \times n}$ with nonsingular diagonal $D$, the weighted Jacobi step
$$u^{(k)} = G u^{(k-1)} + c, \qquad G = (1 - \omega) I - \omega D^{-1}(L + U), \quad c = \omega
  D^{-1} b,$$
is the step of the splitting with $M = \omega^{-1} D$, where $L$ and $U$ are the strictly lower
and strictly upper parts of $A$. For the model matrix the iteration matrix is
$$G^{h,\omega} = I - \frac{\omega h^2}{2} A^h, \qquad h = \frac{1}{n + 1}.$$

The splitting is `Matrix.jorSplitting`, and its step is `Stationary.Splitting.mulVecStep`. -/
theorem equation_11_6_11 {n : ℕ} {ω : ℝ} (hω : ω ≠ 0) :
    (∀ (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (diagPart A)) (b u : Fin n → ℝ),
      (jorSplitting A h hω).mulVecStep b u =
        ((1 - ω) • 1 - ω • ((diagPart A)⁻¹ * (strictLower A + strictUpper A))) *ᵥ u +
          (ω • (diagPart A)⁻¹) *ᵥ b) ∧
      (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator =
        1 - (ω * (1 / ((n : ℝ) + 1)) ^ 2 / 2) • modelA n := by
  refine ⟨fun A h b u => ?_, ?_⟩
  · have hm : (jorSplitting A h hω).m = ω⁻¹ • diagPart A := rfl
    rw [Stationary.Splitting.mulVecStep_eq_iterationOperator_mulVec_add,
      jorSplitting_iterationOperator, jacobiSplitting_iterationOperator, hm,
      inv_smul_of_isUnit' (inv_ne_zero hω) h, inv_inv]
    congr 2
    rw [neg_mul, smul_neg, ← sub_eq_add_neg]
  · rw [jorSplitting_iterationOperator_eq_one_sub, diagPart_modelA,
      inv_smul_of_isUnit' (by positivity) isUnit_one, inv_one, smul_mul, Matrix.one_mul, smul_smul]
    congr 2
    field_simp

/-- The eigenvalues of the weighted Jacobi iteration matrix $G^{h,\omega}$:
$$\tau_j^{h,\omega} = 1 - 2\omega \sin^2\Big(\frac{j\pi}{2(n + 1)}\Big), \qquad j = 1{:}n.$$

The index is 0-based: entry $j$ uses $j + 1$ in place of $j$. -/
noncomputable def weightedJacobiTau (n : ℕ) (ω : ℝ) : Fin n → ℝ := fun j =>
  1 - 2 * ω * Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ^ 2

/-- The weighted Jacobi iteration matrix satisfies $G^{h,\omega} Q^h = Q^h
\,\mathrm{diag}(\tau^{h,\omega})$. -/
private theorem weightedJacobi_mul_modelQ (n : ℕ) {ω : ℝ} (hω : ω ≠ 0) :
    (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator * modelQ n =
      modelQ n * diagonal (weightedJacobiTau n ω) := by
  rw [(equation_11_6_11 hω).2, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    modelA_mul_modelQ]
  have hd : diagonal (weightedJacobiTau n ω) =
      1 - (ω * (1 / ((n : ℝ) + 1)) ^ 2 / 2) • diagonal (modelAEigenvalues n) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [diagonal_apply_eq, Matrix.sub_apply, one_apply_eq, Matrix.smul_apply, smul_eq_mul,
        weightedJacobiTau, modelAEigenvalues]
      field_simp
      ring
    · simp [h, one_apply_ne h]
  rw [hd, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]

/-- For every $p$, $(G^{h,\omega})^p Q^h = Q^h \,\mathrm{diag}(\tau^{h,\omega})^p$. -/
private theorem weightedJacobi_pow_mul_modelQ (n : ℕ) {ω : ℝ} (hω : ω ≠ 0) (p : ℕ) :
    (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator ^ p * modelQ n =
      modelQ n * diagonal fun j => weightedJacobiTau n ω j ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, weightedJacobi_mul_modelQ n hω,
      Matrix.mul_assoc, diagonal_mul_diagonal]
    congr 2
    funext j
    ring

/-- For every $p$ and $v$, $(G^{h,\omega})^p (Q^h v) = Q^h (\tau^p \odot v)$: weighted Jacobi
multiplies the sine coefficient $j$ by $\tau_j^{h,\omega}$ per step. -/
private theorem weightedJacobi_pow_mulVec_modelQ (n : ℕ) {ω : ℝ} (hω : ω ≠ 0) (p : ℕ)
    (v : Fin n → ℝ) :
    (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator ^ p *ᵥ
        (modelQ n *ᵥ v) = modelQ n *ᵥ fun j => weightedJacobiTau n ω j ^ p * v j := by
  rw [mulVec_mulVec, weightedJacobi_pow_mul_modelQ, ← mulVec_mulVec]
  congr 1
  funext j
  exact mulVec_diagonal _ _ j

/-- **Equation (11.6.12)** of [golub2013matrix]. Let $\omega \neq 0$. Then
$$(Q^h)^T G^{h,\omega} Q^h = \mathrm{diag}(\tau_1^{h,\omega}, \dots, \tau_n^{h,\omega}), \qquad
  \tau_j^{h,\omega} = 1 - 2\omega \sin^2\Big(\frac{j\pi}{2(n + 1)}\Big).$$
Hence the error expansion after (11.6.12) holds: let $A^h u = b$, let
$u_0 - u = \sum_j \alpha_j q_j$, and let $u_p$ be the iterates of weighted Jacobi for
$A^h u = b$ from $u_0$. Then for every $p$,
$$u_p - u = (G^{h,\omega})^p (u_0 - u) = \sum_j \alpha_j (\tau_j^{h,\omega})^p q_j.$$
-/
theorem equation_11_6_12 (n : ℕ) {ω : ℝ} (hω : ω ≠ 0) :
    (modelQ n)ᵀ * (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).iterationOperator *
        modelQ n = diagonal (weightedJacobiTau n ω) ∧
      ∀ (b u u₀ α : Fin n → ℝ), modelA n *ᵥ u = b → u₀ - u = modelQ n *ᵥ α → ∀ p : ℕ,
        ((jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω).mulVecStep b)^[p] u₀ - u =
          modelQ n *ᵥ fun j => weightedJacobiTau n ω j ^ p * α j := by
  refine ⟨by rw [Matrix.mul_assoc, weightedJacobi_mul_modelQ n hω, ← Matrix.mul_assoc,
    modelQ_transpose_mul, Matrix.one_mul], fun b u u₀ α hu hα p => ?_⟩
  rw [equation_11_2_7 _ hu, hα, weightedJacobi_pow_mulVec_modelQ]

/-- For $j = 1{:}n$, $0 < j\pi/(2(n + 1)) < \pi/2$. -/
private theorem halfAngle_mem (n : ℕ) (j : Fin n) :
    0 < (((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1)) ∧
      (((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1)) < Real.pi / 2 := by
  have hj : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
  refine ⟨by positivity, ?_⟩
  rw [div_lt_div_iff₀ (by positivity) two_pos]
  nlinarith [Real.pi_pos]

/-- For $j = 1{:}n$, $s = \sin(j\pi/(2(n + 1)))$ satisfies $0 < s < 1$. -/
private theorem sin_halfAngle_mem (n : ℕ) (j : Fin n) :
    0 < Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ∧
      Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) < 1 := by
  obtain ⟨h0, h1⟩ := halfAngle_mem n j
  refine ⟨Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos]), ?_⟩
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl h1
  rwa [Real.sin_pi_div_two] at h

/-- A real diagonal matrix whose entries lie in $(-1, 1)$ has spectral radius less than $1$. -/
private theorem complexSpectralRadius_diagonal_lt_one {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, |d i| < 1) : (diagonal d).complexSpectralRadius < 1 := by
  rw [complexSpectralRadius_diagonal]
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · rw [iSup_of_empty]
    exact zero_lt_one
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖d i‖₊
    refine lt_of_le_of_lt (iSup_le fun i => ENNReal.coe_le_coe.2 (hi₀ i)) ?_
    rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact hd i₀

/-- **Section 11.6.2** of [golub2013matrix], convergence of weighted Jacobi. Let $0 < \omega \le 1$.
Then
$$-1 < \tau_n^{h,\omega} < \dots < \tau_1^{h,\omega} < 1,$$
that is, the $\tau_j^{h,\omega}$ strictly decrease in $j$ and lie in $(-1, 1)$. Hence
$\rho(G^{h,\omega}) < 1$. -/
theorem weightedJacobi_tau_mem (n : ℕ) {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) :
    StrictAnti (weightedJacobiTau n ω) ∧ (∀ j, -1 < weightedJacobiTau n ω j ∧
      weightedJacobiTau n ω j < 1) ∧
      Matrix.complexSpectralRadius
        (jorSplitting (modelA n) (isUnit_diagPart_modelA n) hω0.ne').iterationOperator < 1 := by
  have hmem : ∀ j, -1 < weightedJacobiTau n ω j ∧ weightedJacobiTau n ω j < 1 := fun j => by
    obtain ⟨h0, h1⟩ := sin_halfAngle_mem n j
    have hs0 := pow_pos h0 2
    have hs1 : Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ^ 2 < 1 := by
      nlinarith
    simp only [weightedJacobiTau]
    constructor <;> nlinarith
  refine ⟨fun j k hjk => ?_, hmem, ?_⟩
  · simp only [weightedJacobiTau]
    have hs : Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) <
        Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) := by
      refine Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [(halfAngle_mem n j).1, Real.pi_pos])
        (halfAngle_mem n k).2.le ?_
      have hjk' : ((j : ℕ) : ℝ) < (k : ℕ) := by exact_mod_cast hjk
      exact div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) (by positivity)
    have := pow_lt_pow_left₀ hs (sin_halfAngle_mem n j).1.le two_ne_zero
    nlinarith
  · rw [← complexSpectralRadius_conj (isUnit_modelQ n), inv_modelQ,
      (equation_11_6_12 n hω0.ne').1]
    exact complexSpectralRadius_diagonal_lt_one _ fun j => abs_lt.2 (hmem j)

/-- The high-frequency part of a vector of sine coefficients on the fine grid: it keeps the
components $j \ge m + 1$ and sets the others to zero.

The index is 0-based, so the kept components are $j \ge m$. -/
def highPart {m : ℕ} (v : Fin (2 * m + 1) → ℝ) : Fin (2 * m + 1) → ℝ :=
  fun j => if m ≤ (j : ℕ) then v j else 0

/-- Multiplication by the orthogonal matrix $Q^h$ preserves the Euclidean norm:
$\|Q^h v\|_2 = \|v\|_2$. -/
private theorem norm_modelQ_mulVec (n : ℕ) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 (modelQ n *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  have h : ‖WithLp.toLp 2 (modelQ n *ᵥ v)‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp,
      EuclideanSpace.inner_toLp_toLp, star_trivial, star_trivial, dotProduct_mulVec,
      ← mulVec_transpose, mulVec_mulVec, modelQ_transpose_mul, one_mulVec]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- On the high frequencies $j \ge m + 1$ of the fine grid, $s = \sin(j\pi/(2(n + 1)))$ satisfies
$1/2 \le s^2 < 1$. -/
private theorem sin_sq_high_mem (m : ℕ) (j : Fin (2 * m + 1)) (hj : m ≤ (j : ℕ)) :
    1 / 2 ≤ Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2 ∧
      Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2 < 1 := by
  obtain ⟨h0, h1⟩ := sin_halfAngle_mem (2 * m + 1) j
  have hq : Real.pi / 4 ≤ (((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
    have hj' : (m : ℝ) ≤ (j : ℕ) := by exact_mod_cast hj
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    push_cast
    nlinarith [Real.pi_pos]
  have hs : Real.sqrt 2 / 2 ≤
      Real.sin ((((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) := by
    rw [← Real.sin_pi_div_four]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (halfAngle_mem (2 * m + 1) j).2.le hq
  refine ⟨?_, by nlinarith⟩
  have := pow_le_pow_left₀ (by positivity) hs 2
  rw [div_pow, Real.sq_sqrt (by norm_num)] at this
  linarith

/-- At the middle mode, $\tau_{m+1}^{h,\omega} = 1 - \omega$, because $s^2 = \sin^2(\pi/4) = 1/2$.
-/
private theorem weightedJacobiTau_middleIndex (m : ℕ) (ω : ℝ) :
    weightedJacobiTau (2 * m + 1) ω (middleIndex m) = 1 - ω := by
  have e : (((middleIndex m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
      Real.pi / 4 := by
    rw [middleIndex]
    push_cast
    field_simp
    ring
  simp only [weightedJacobiTau]
  rw [e, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  ring

/-- **Section 11.6.2** of [golub2013matrix], the choice $\omega = 2/3$. Let $n = 2m + 1$. Then the
high-frequency damping factor of $\omega = 2/3$ is $1/3$:
* $|\tau_j^{h,2/3}| \le 1/3$ for every high frequency $j \ge m + 1$, with equality at
  $j = m + 1$, where $\tau_{m+1}^{h,2/3} = 1/3$;
* for every $p$ and every vector of coefficients $\alpha$, $\|Q^h P_{\mathrm{high}}(\tau^p \odot
  \alpha)\|_2 \le (1/3)^p \|Q^h P_{\mathrm{high}}\, \alpha\|_2$, where $P_{\mathrm{high}}$ keeps
  the components $j \ge m + 1$.

By `GolubVanLoan.Chapter11.equation_11_6_12`, if $u_0 - u = Q^h \alpha$, then
$u_p - u = Q^h(\tau^p \odot \alpha)$. So the high-frequency part of the error after $p$ weighted
Jacobi steps is at most $(1/3)^p$ times the initial one. The map $P_{\mathrm{high}}$ is
`GolubVanLoan.Chapter11.highPart`. -/
theorem weightedJacobi_twoThirds (m : ℕ) :
    (∀ j : Fin (2 * m + 1), m ≤ (j : ℕ) → |weightedJacobiTau (2 * m + 1) (2 / 3) j| ≤ 1 / 3) ∧
      weightedJacobiTau (2 * m + 1) (2 / 3) (middleIndex m) = 1 / 3 ∧
      ∀ (p : ℕ) (α : Fin (2 * m + 1) → ℝ),
        ‖WithLp.toLp 2 (modelQ (2 * m + 1) *ᵥ
            highPart fun j => weightedJacobiTau (2 * m + 1) (2 / 3) j ^ p * α j)‖ ≤
          (1 / 3) ^ p * ‖WithLp.toLp 2 (modelQ (2 * m + 1) *ᵥ highPart α)‖ := by
  have hhigh : ∀ j : Fin (2 * m + 1), m ≤ (j : ℕ) →
      |weightedJacobiTau (2 * m + 1) (2 / 3) j| ≤ 1 / 3 := by
    intro j hj
    obtain ⟨hs2, hs1⟩ := sin_sq_high_mem m j hj
    simp only [weightedJacobiTau]
    rw [abs_le]
    constructor <;> nlinarith
  have hmid : weightedJacobiTau (2 * m + 1) (2 / 3) (middleIndex m) = 1 / 3 := by
    rw [weightedJacobiTau_middleIndex]
    norm_num
  refine ⟨hhigh, hmid, fun p α => ?_⟩
  rw [norm_modelQ_mulVec, norm_modelQ_mulVec]
  have hnorm : ∀ v : Fin (2 * m + 1) → ℝ, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i * v i := fun v => by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
    rfl
  have hsq : ‖WithLp.toLp 2 (highPart fun j => weightedJacobiTau (2 * m + 1) (2 / 3) j ^ p * α j)‖
      ^ 2 ≤ ((1 / 3) ^ p * ‖WithLp.toLp 2 (highPart α)‖) ^ 2 := by
    rw [mul_pow, hnorm, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [highPart]
    split_ifs with hj
    · set τ := weightedJacobiTau (2 * m + 1) (2 / 3) j
      have hτ : τ * τ ≤ 1 / 3 * (1 / 3) := by
        have := hhigh j hj
        rw [abs_le] at this
        nlinarith
      have hp : (τ * τ) ^ p ≤ (1 / 3 * (1 / 3)) ^ p :=
        pow_le_pow_left₀ (mul_self_nonneg τ) hτ p
      calc τ ^ p * α j * (τ ^ p * α j) = (τ * τ) ^ p * (α j * α j) := by rw [mul_pow]; ring
        _ ≤ (1 / 3 * (1 / 3)) ^ p * (α j * α j) :=
          mul_le_mul_of_nonneg_right hp (mul_self_nonneg _)
        _ = ((1 / 3) ^ p) ^ 2 * (α j * α j) := by rw [mul_pow, sq]
    · simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Section 11.6.2** of [golub2013matrix], the high-frequency damping factor. For $n = 2m + 1$,
$$\mu(\omega) = \max\{|\tau_{m+1}^{h,\omega}|, \dots, |\tau_n^{h,\omega}|\}.$$

The index is 0-based: the maximum is over the modes $j \ge m$. -/
noncomputable def highFreqDamping (m : ℕ) (ω : ℝ) : ℝ :=
  (Finset.univ.filter fun j : Fin (2 * m + 1) => m ≤ (j : ℕ)).sup'
    ⟨middleIndex m, by simp [middleIndex]⟩ fun j => |weightedJacobiTau (2 * m + 1) ω j|

/-- **Section 11.6.2** of [golub2013matrix], the minimizer of the high-frequency damping factor:
$$\omega_* = \frac{2}{1 + 2 s_n^2}, \qquad s_n = \sin\Big(\frac{n\pi}{2(n + 1)}\Big), \quad n =
  2m + 1.$$
-/
noncomputable def optimalOmega (m : ℕ) : ℝ :=
  2 / (1 + 2 * Real.sin ((((2 * m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2)

/-- **Section 11.6.2** of [golub2013matrix], the optimal $\omega$. For every $m$, let $n = 2m + 1$
and $a = s_n^2$. Then:
* for $0 < \omega \le 1$, $\mu(\omega) = \max\{|1 - \omega|, |1 - 2\omega a|\}$, because $\tau$
  decreases in $j$, $\tau_{m+1} = 1 - \omega$ and $\tau_n = 1 - 2\omega a$;
* $\omega_* = 2/(1 + 2a)$ lies in $(0, 1]$;
* $\tau_{m+1}^{h,\omega_*} = -\tau_n^{h,\omega_*}$, which is the equation of the source;
* $\mu(\omega_*) = (2a - 1)/(2a + 1)$;
* $\mu(\omega_*) \le \mu(\omega)$ for every $\omega \in (0, 1]$;
* $(2a - 1)/(2a + 1) < 1/3$.

Moreover $\omega_* \to 2/3$ as $m \to \infty$, since $s_n \to 1$ as the grid is refined.

**Reading.** The source says that this minimization "is essentially solved by
$\omega_{\mathrm{opt}} = 2/3$". The statement gives the exact minimizer over $(0, 1]$ and its
limit $2/3$.

The index of $\tau_n$ is $2m$ 0-based. -/
theorem weightedJacobi_optimalOmega :
    (∀ m : ℕ,
      let a := Real.sin ((((2 * m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2
      (∀ ω, 0 < ω → ω ≤ 1 → highFreqDamping m ω = max |1 - ω| |1 - 2 * ω * a|) ∧
      (0 < optimalOmega m ∧ optimalOmega m ≤ 1) ∧
      weightedJacobiTau (2 * m + 1) (optimalOmega m) (middleIndex m) =
        -weightedJacobiTau (2 * m + 1) (optimalOmega m) ⟨2 * m, by omega⟩ ∧
      highFreqDamping m (optimalOmega m) = (2 * a - 1) / (2 * a + 1) ∧
      (∀ ω, 0 < ω → ω ≤ 1 → highFreqDamping m (optimalOmega m) ≤ highFreqDamping m ω) ∧
      (2 * a - 1) / (2 * a + 1) < 1 / 3) ∧
    Filter.Tendsto optimalOmega Filter.atTop (nhds (2 / 3)) := by
  refine ⟨fun m => ?_, ?_⟩
  · intro a
    obtain ⟨ha1, ha2⟩ : 1 / 2 ≤ a ∧ a < 1 := sin_sq_high_mem m ⟨2 * m, by omega⟩
      (by change m ≤ 2 * m; omega)
    have hlast : ∀ ω, weightedJacobiTau (2 * m + 1) ω ⟨2 * m, by omega⟩ = 1 - 2 * ω * a :=
      fun ω => rfl
    have hμ : ∀ ω, 0 < ω → ω ≤ 1 → highFreqDamping m ω = max |1 - ω| |1 - 2 * ω * a| := by
      intro ω hω0 hω1
      have hanti := (weightedJacobi_tau_mem (2 * m + 1) hω0 hω1).1.antitone
      have hmem : ∀ j ∈ (Finset.univ.filter fun j : Fin (2 * m + 1) => m ≤ (j : ℕ)),
          |weightedJacobiTau (2 * m + 1) ω j| ≤ max |1 - ω| |1 - 2 * ω * a| := by
        intro j hj
        have hj' : m ≤ (j : ℕ) := (Finset.mem_filter.1 hj).2
        have hup : weightedJacobiTau (2 * m + 1) ω j ≤ 1 - ω := by
          rw [← weightedJacobiTau_middleIndex m ω]
          exact hanti (show middleIndex m ≤ j from hj')
        have hlo : 1 - 2 * ω * a ≤ weightedJacobiTau (2 * m + 1) ω j := by
          rw [← hlast ω]
          exact hanti (show j ≤ ⟨2 * m, by omega⟩ from by
            change (j : ℕ) ≤ 2 * m
            have := j.isLt
            omega)
        rw [abs_le]
        constructor
        · have := neg_abs_le (1 - 2 * ω * a)
          have := le_max_right |1 - ω| |1 - 2 * ω * a|
          linarith
        · have := le_abs_self (1 - ω)
          have := le_max_left |1 - ω| |1 - 2 * ω * a|
          linarith
      refine le_antisymm (Finset.sup'_le _ _ hmem) (max_le ?_ ?_)
      · rw [← weightedJacobiTau_middleIndex m ω]
        exact Finset.le_sup' (fun j => |weightedJacobiTau (2 * m + 1) ω j|)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [middleIndex]⟩)
      · rw [← hlast ω]
        exact Finset.le_sup' (fun j => |weightedJacobiTau (2 * m + 1) ω j|)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, by change m ≤ 2 * m; omega⟩)
    have hω : optimalOmega m = 2 / (1 + 2 * a) := rfl
    have hpos : 0 < 1 + 2 * a := by linarith
    have hω0 : 0 < optimalOmega m := by rw [hω]; positivity
    have hω1 : optimalOmega m ≤ 1 := by rw [hω, div_le_one hpos]; linarith
    have e1 : 1 - optimalOmega m = (2 * a - 1) / (2 * a + 1) := by
      rw [hω]; field_simp; ring
    have e2 : 1 - 2 * optimalOmega m * a = -((2 * a - 1) / (2 * a + 1)) := by
      rw [hω]; field_simp; ring
    have hnn : 0 ≤ (2 * a - 1) / (2 * a + 1) := div_nonneg (by linarith) (by linarith)
    have hval : highFreqDamping m (optimalOmega m) = (2 * a - 1) / (2 * a + 1) := by
      rw [hμ _ hω0 hω1, e1, e2, abs_neg, abs_of_nonneg hnn, max_self]
    refine ⟨hμ, ⟨hω0, hω1⟩, ?_, hval, fun ω h0 h1 => ?_, ?_⟩
    · rw [weightedJacobiTau_middleIndex, hlast, e1, e2, neg_neg]
    · rw [hval, hμ ω h0 h1]
      by_cases hle : ω ≤ optimalOmega m
      · refine le_trans ?_ (le_max_left _ _)
        rw [← e1]
        exact le_trans (by linarith) (le_abs_self _)
      · refine le_trans ?_ (le_max_right _ _)
        have hωa : optimalOmega m * a ≤ ω * a :=
          mul_le_mul_of_nonneg_right (le_of_not_ge hle) (by linarith)
        have : -(1 - 2 * optimalOmega m * a) ≤ -(1 - 2 * ω * a) := by linarith
        rw [e2, neg_neg] at this
        exact this.trans (neg_le_abs _)
    · rw [div_lt_iff₀ (by linarith)]
      linarith
  · have hang : ∀ m : ℕ, (((2 * m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
        Real.pi / 2 - Real.pi / 4 * (1 / ((m : ℝ) + 1)) := fun m => by
      push_cast
      field_simp
      ring
    have h1 : Filter.Tendsto (fun m : ℕ => Real.pi / 2 - Real.pi / 4 * (1 / ((m : ℝ) + 1)))
        Filter.atTop (nhds (Real.pi / 2 - Real.pi / 4 * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [mul_zero, sub_zero] at h1
    have h2 := ((Real.continuous_sin.pow 2).tendsto (Real.pi / 2)).comp h1
    simp only [Pi.pow_apply, Real.sin_pi_div_two, one_pow] at h2
    have h3 := (tendsto_const_nhds (x := (2 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := (2 : ℝ))).mul h2))
      (by norm_num)
    rw [show (2 : ℝ) / (1 + 2 * 1) = 2 / 3 by norm_num] at h3
    refine h3.congr fun m => ?_
    simp only [optimalOmega, Function.comp_apply, Pi.pow_apply, Pi.div_apply, hang]

/-! ### Restriction and prolongation -/

/-- **Equation (11.6.15)** of [golub2013matrix]. The matrix
$$B^h = 4 I_n - h^2 A^h = \mathrm{tridiag}(1, 2, 1), \qquad h = \frac{1}{n + 1}.$$
-/
noncomputable def modelB (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (4 : ℝ) • 1 - (1 / ((n : ℝ) + 1)) ^ 2 • modelA n

/-- The matrix $B^h$ is `Matrix.symmTridiagonalToeplitz n 1 2`, that is,
$\mathrm{tridiag}(1, 2, 1)$. -/
private theorem modelB_eq (n : ℕ) : modelB n = symmTridiagonalToeplitz n 1 2 := by
  ext i j
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [modelB, modelA, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    symmTridiagonalToeplitz_apply]
  split_ifs <;> field_simp <;> ring

/-- **Equation (11.6.14)** of [golub2013matrix], the restriction. For $n = 2m + 1$,
$$R^{2h}_h = \tfrac14 B^h(2{:}2{:}2m, :) \in \mathbb{R}^{m \times n}.$$

It is the full weighting of the backbone (`GolubVanLoan.Chapter11.restrictionMatrix_eq`). -/
noncomputable def restrictionMatrix (m : ℕ) : Matrix (Fin m) (Fin (2 * m + 1)) ℝ :=
  (1 / 4 : ℝ) • (modelB (2 * m + 1)).submatrix evenIndex id

/-- **Equation (11.6.14)** of [golub2013matrix], the prolongation. For $n = 2m + 1$,
$$P^h_{2h} = \tfrac12 B^h(:, 2{:}2{:}2m) \in \mathbb{R}^{n \times m}.$$

It is the linear interpolation of the backbone (`GolubVanLoan.Chapter11.prolongationMatrix_eq`). -/
noncomputable def prolongationMatrix (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin m) ℝ :=
  (1 / 2 : ℝ) • (modelB (2 * m + 1)).submatrix id evenIndex

/-- **Equation (11.6.14)** of [golub2013matrix], the restriction is full weighting: $R^{2h}_h$ is
`Multigrid.fullWeighting m`. -/
theorem restrictionMatrix_eq (m : ℕ) : restrictionMatrix m = fullWeighting m := by
  ext q i
  rw [restrictionMatrix, Matrix.smul_apply, submatrix_apply, modelB_eq,
    symmTridiagonalToeplitz_apply',
    fullWeighting_apply, evenIndex, id, smul_eq_mul]
  dsimp only
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Equation (11.6.14)** of [golub2013matrix], the prolongation is linear interpolation:
$P^h_{2h}$ is `Multigrid.linearInterpolation m`. -/
theorem prolongationMatrix_eq (m : ℕ) : prolongationMatrix m = linearInterpolation m := by
  ext i q
  rw [prolongationMatrix, Matrix.smul_apply, submatrix_apply, modelB_eq,
    symmTridiagonalToeplitz_apply',
    linearInterpolation_apply, evenIndex, id, smul_eq_mul]
  dsimp only
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Equation (11.6.14)** of [golub2013matrix], the restriction is half the transpose of the
prolongation: $R^{2h}_h = \frac12 (P^h_{2h})^T$. -/
theorem restrictionMatrix_eq_half_transpose (m : ℕ) :
    restrictionMatrix m = (1 / 2 : ℝ) • (prolongationMatrix m)ᵀ := by
  rw [restrictionMatrix_eq, prolongationMatrix_eq]
  rfl

/-- **Section 11.6.3** of [golub2013matrix], the action of the transfer operators. Let $n = 2m + 1$,
and use the boundary values $v_0 = v_{m+1} = 0$ for a coarse vector $v$. Then:
* restriction is the weighted average around each even fine point,
  $(R u)_i = (u_{2i-1} + 2u_{2i} + u_{2i+1})/4$;
* prolongation copies the coarse values at the even fine points, $(P v)_{2i} = v_i$;
* prolongation averages them at the odd fine points, $(P v)_{2i+1} = (v_i + v_{i+1})/2$;
* $R = \frac12 P^T$.

The indices above are those of the source. In 0-based indices, $(Ru)_i$ uses the fine points
$2i, 2i + 1, 2i + 2$ around `GolubVanLoan.Chapter11.evenIndex i`, and the fine point $2q$,
$q \le m$, gets the average of the coarse values $q - 1$ and $q$, a missing one counting as $0$. -/
theorem restriction_prolongation_apply (m : ℕ) :
    (∀ (u : Fin (2 * m + 1) → ℝ) (i : Fin m), (restrictionMatrix m *ᵥ u) i =
      (u ⟨2 * i, by omega⟩ + 2 * u (evenIndex i) + u ⟨2 * i + 2, by omega⟩) / 4) ∧
    (∀ (v : Fin m → ℝ) (i : Fin m), (prolongationMatrix m *ᵥ v) (evenIndex i) = v i) ∧
    (∀ (v : Fin m → ℝ) (q : ℕ) (hq : q ≤ m), (prolongationMatrix m *ᵥ v) ⟨2 * q, by omega⟩ =
      ((if h : 0 < q then v ⟨q - 1, by omega⟩ else 0) + (if h : q < m then v ⟨q, h⟩ else 0)) / 2) ∧
    restrictionMatrix m = (1 / 2 : ℝ) • (prolongationMatrix m)ᵀ := by
  refine ⟨fun u i => ?_, fun v i => ?_, fun v q hq => ?_, restrictionMatrix_eq_half_transpose m⟩
  · rw [restrictionMatrix_eq, fullWeighting_mulVec_apply]
    rfl
  · rw [prolongationMatrix_eq, mulVec, dotProduct, Finset.sum_eq_single i]
    · rw [linearInterpolation_apply, evenIndex, ite_eq_left rfl, one_mul]
    · intro j _ hji
      rw [linearInterpolation_apply, evenIndex]
      dsimp only
      have : (i : ℕ) ≠ j := fun h => hji (Fin.ext h.symm)
      split_ifs <;> first | (exfalso; omega) | simp
    · simp
  · simp only [prolongationMatrix_eq, mulVec, dotProduct]
    have hL : ∀ j : Fin m, linearInterpolation m ⟨2 * q, by omega⟩ j * v j =
        (if (j : ℕ) + 1 = q then v j / 2 else 0) + (if (j : ℕ) = q then v j / 2 else 0) := by
      intro j
      rw [linearInterpolation_apply]
      dsimp only
      split_ifs <;> first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl fun (j : Fin m) (_ : j ∈ Finset.univ) => hL j,
      Finset.sum_add_distrib, add_div]
    congr 1
    · split_ifs with h
      · rw [Finset.sum_eq_single ⟨q - 1, by omega⟩]
        · simp only [show q - 1 + 1 = q by omega, ite_true]
        · intro j _ hj
          refine ite_eq_right fun h' => hj (Fin.ext ?_)
          dsimp only
          omega
        · simp
      · rw [zero_div]
        refine Finset.sum_eq_zero fun j _ => ite_eq_right fun h' => ?_
        omega
    · split_ifs with h
      · rw [Finset.sum_eq_single ⟨q, h⟩]
        · simp
        · intro j _ hj
          exact ite_eq_right fun h' => hj (Fin.ext h')
        · simp
      · rw [zero_div]
        refine Finset.sum_eq_zero fun j _ => ite_eq_right fun h' => ?_
        have := j.isLt
        omega

/-- The coarse matrix is the Galerkin product of the fine one: for $n = 2m + 1$,
$$R^{2h}_h A^h P^h_{2h} = A^{2h}.$$

The source does not state this identity. It makes $E^h$ a projector and connects §11.6 to the
backbone. -/
theorem galerkin_coarse_eq (m : ℕ) :
    restrictionMatrix m * modelA (2 * m + 1) * prolongationMatrix m = modelA m := by
  rw [restrictionMatrix_eq, prolongationMatrix_eq, modelA_eq, modelA_eq, Matrix.mul_smul,
    Matrix.smul_mul, fullWeighting_mul_mul_linearInterpolation, smul_smul]
  congr 1
  push_cast
  ring

/-! ### The two-grid cycle -/

/-- **Equation (11.6.18)** of [golub2013matrix]. The two-grid error operator
$$E^h = I_n - P^h_{2h} (A^{2h})^{-1} R^{2h}_h A^h, \qquad n = 2m + 1.$$
-/
noncomputable def twoGridErrorOperator (m : ℕ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  1 - prolongationMatrix m * (modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)

/-- The two-grid error operator $E^h$ is the exact coarse-grid correction
`Multigrid.modelCoarseCorrection m` of the backbone. -/
private theorem twoGridErrorOperator_eq (m : ℕ) :
    twoGridErrorOperator m = modelCoarseCorrection m := by
  have hT : IsUnit (symmTridiagonalToeplitz m (-1) 2) :=
    (posDef_symmTridiagonalToeplitz_neg_one_two m).isUnit
  rw [twoGridErrorOperator, modelCoarseCorrection, restrictionMatrix_eq, prolongationMatrix_eq,
    modelA_eq, modelA_eq, inv_smul_of_isUnit' (by positivity) hT]
  congr 1
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  push_cast
  field_simp
  ring

/-- **Equation (11.6.16)** of [golub2013matrix], steps 1–5 of the two-grid cycle, from the
pre-smoothed iterate $u_{p_1}$:
* the fine-grid residual $r^h = b^h - A^h u_{p_1}$;
* the restriction $r^{2h} = R^{2h}_h r^h$;
* the coarse solve $A^{2h} z^{2h} = r^{2h}$;
* the prolongation $z^h = P^h_{2h} z^{2h}$;
* the update $u_+ = u_{p_1} + z^h$.

**Typo.** The source prints $u_+ = u_c + z^h$, which updates the input of the pre-smoothing
instead of $u_{p_1}$. The program uses $u_{p_1}$, as does the next display of the source.

The coarse solve is the routine argument `coarseSolve`, with exact semantics $(A^{2h})^{-1}$.
The products are Algorithm 1.1.3, and the subtraction and addition are
`GolubVanLoan.Chapter01.vecSub` and `GolubVanLoan.Chapter01.vecAdd`. -/
noncomputable def coarseGridCorrection {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m : ℕ}
    (coarseSolve : (Fin m → ℝ) → M (Fin m → ℝ)) (b u : Fin (2 * m + 1) → ℝ) :
    M (Fin (2 * m + 1) → ℝ) := do
  let Au ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd (modelA (2 * m + 1)) u 0
  let r ← Chapter01.vecSub rnd b Au
  let r₂ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd (restrictionMatrix m) r 0
  let z₂ ← coarseSolve r₂
  let z ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd (prolongationMatrix m) z₂ 0
  Chapter01.vecAdd rnd u z

/-- **Equation (11.6.16)** of [golub2013matrix], the two-grid cycle. From $u_c$, pre-smooth with
$p_1$ smoothing steps, $u_{p_1} = \mathrm{WJ}(p_1, u_c)$; correct on the coarse grid with
`GolubVanLoan.Chapter11.coarseGridCorrection`, which gives $u_+$; and post-smooth with $p_2$
smoothing steps, $u_{++} = \mathrm{WJ}(p_2, u_+)$.

The smoothing step is the routine argument `smooth`. Its exact semantics is one weighted Jacobi
step (11.6.11) with $\omega = 2/3$. -/
noncomputable def twoGridCycle {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m : ℕ}
    (smooth : (Fin (2 * m + 1) → ℝ) → M (Fin (2 * m + 1) → ℝ))
    (coarseSolve : (Fin m → ℝ) → M (Fin m → ℝ)) (b uc : Fin (2 * m + 1) → ℝ) (p₁ p₂ : ℕ) :
    M (Fin (2 * m + 1) → ℝ) := do
  let u₁ ← (List.range p₁).foldlM (fun v _ => smooth v) uc
  let uplus ← coarseGridCorrection rnd coarseSolve b u₁
  (List.range p₂).foldlM (fun v _ => smooth v) uplus

/-- An exact loop that applies the same map $f$ $p$ times computes the $p$-th iterate $f^{p}$. -/
private theorem idRun_foldlM_range_const {α : Type} (f : α → α) (p : ℕ) (x : α) :
    Id.run ((List.range p).foldlM (fun v _ => pure (f v)) x) = f^[p] x := by
  simp only [List.foldlM_pure, List.foldl_const, List.length_range, Id.run_pure]

/-- The exact coarse-grid correction maps $v$ to $v + P^h_{2h} (A^{2h})^{-1} R^{2h}_h (b - A^h v)$.
-/
private theorem coarseGridCorrection_id (m : ℕ) (b v : Fin (2 * m + 1) → ℝ) :
    Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b v) =
      v + prolongationMatrix m *ᵥ ((modelA m)⁻¹ *ᵥ
        (restrictionMatrix m *ᵥ (b - modelA (2 * m + 1) *ᵥ v))) := by
  change Id.run (Chapter01.vecAdd pure v (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure
    (prolongationMatrix m) ((modelA m)⁻¹ *ᵥ Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure
      (restrictionMatrix m) (Id.run (Chapter01.vecSub pure b (Id.run
        (GolubVanLoan.Chapter01.algorithm_1_1_3 pure (modelA (2 * m + 1)) v 0)))) 0)) 0))) = _
  simp only [GolubVanLoan.Chapter01.algorithm_1_1_3_spec, Chapter01.vecSub_spec,
    Chapter01.vecAdd_spec, zero_add]

/-- **Equation (11.6.17)** of [golub2013matrix] and the display before it. Let $n = 2m + 1$, let
$A^h u = b^h$, and let $u_+$ be the result of the exact coarse-grid correction of
`GolubVanLoan.Chapter11.coarseGridCorrection` applied to $u_{p_1}$, with the coarse solve
$(A^{2h})^{-1}$. Then
$$u_+ = u_{p_1} + P^h_{2h} (A^{2h})^{-1} R^{2h}_h A^h (u - u_{p_1}), \qquad u_+ - u = E^h
  (u_{p_1} - u).$$
-/
theorem equation_11_6_17 (m : ℕ) {b u : Fin (2 * m + 1) → ℝ} (hu : modelA (2 * m + 1) *ᵥ u = b)
    (v : Fin (2 * m + 1) → ℝ) :
    Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b v) =
        v + (prolongationMatrix m * (modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)) *ᵥ
          (u - v) ∧
      Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b v) - u =
        twoGridErrorOperator m *ᵥ (v - u) := by
  have h1 : Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b v) =
      v + (prolongationMatrix m * (modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)) *ᵥ
        (u - v) := by
    rw [coarseGridCorrection_id, ← hu, ← mulVec_sub]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨h1, ?_⟩
  rw [h1, twoGridErrorOperator, sub_mulVec, one_mulVec, ← neg_sub u v, mulVec_neg]
  abel

/-- The weighted Jacobi splitting of the model matrix $A^h$ with $\omega = 2/3$. Its iteration
matrix is $G^h = G^{h,2/3}$. -/
noncomputable abbrev twoThirdsJacobi (n : ℕ) : Stationary.Splitting (modelA n) :=
  jorSplitting (modelA n) (isUnit_diagPart_modelA n) (by norm_num : (2 / 3 : ℝ) ≠ 0)

/-- **Equation (11.6.19)** of [golub2013matrix]. Let $n = 2m + 1$ and $A^h u = b^h$. Run the
two-grid cycle in exact arithmetic with the weighted Jacobi step with $\omega = 2/3$ as smoother
and the exact coarse solve $(A^{2h})^{-1}$, from $u_c$ with $p_1$ pre-smoothing and $p_2$
post-smoothing steps. Then the result $u_{++}$ satisfies
$$u_{++} - u = (G^h)^{p_2} E^h (G^h)^{p_1} (u_c - u), \qquad G^h = G^{h,2/3}.$$
-/
theorem equation_11_6_19 (m : ℕ) {b u : Fin (2 * m + 1) → ℝ} (hu : modelA (2 * m + 1) *ᵥ u = b)
    (uc : Fin (2 * m + 1) → ℝ) (p₁ p₂ : ℕ) :
    Id.run (twoGridCycle pure (fun v => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v))
        (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b uc p₁ p₂) - u =
      ((twoThirdsJacobi (2 * m + 1)).iterationOperator ^ p₂ * twoGridErrorOperator m *
        (twoThirdsJacobi (2 * m + 1)).iterationOperator ^ p₁) *ᵥ (uc - u) := by
  have hrun : Id.run (twoGridCycle pure
      (fun v => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v))
      (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b uc p₁ p₂) =
      ((twoThirdsJacobi (2 * m + 1)).mulVecStep b)^[p₂]
        (Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b
          (((twoThirdsJacobi (2 * m + 1)).mulVecStep b)^[p₁] uc))) := by
    change Id.run ((List.range p₂).foldlM
      (fun v _ => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v))
      (Id.run (coarseGridCorrection pure (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b
        (Id.run ((List.range p₁).foldlM
          (fun v _ => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v)) uc))))) = _
    rw [idRun_foldlM_range_const, idRun_foldlM_range_const]
  rw [hrun, equation_11_2_7 _ hu, (equation_11_6_17 m hu _).2, equation_11_2_7 _ hu,
    mulVec_mulVec, mulVec_mulVec]

/-! ### The two-grid error operator in the sine basis -/

/-- **Equation (11.6.22)** of [golub2013matrix]. Let $n = 2m + 1$. For $j = 1{:}m$,
$$E^h q_j = s_j^2 (q_j + q_{n-j+1}), \qquad E^h q_{m+1} = q_{m+1}, \qquad E^h q_{n-j+1} = c_j^2
  (q_j + q_{n-j+1}),$$
with $s_j = \sin(\theta_j/2)$, $c_j = \cos(\theta_j/2)$ and $\theta_j$ =
`Multigrid.modeAngle m j`.

These are the columns of (11.6.21). In 0-based indices the vectors are the fine mode $j$, the
middle mode $m$ and the alias $2m - j$. The identities are the mode identities of the exact
coarse-grid correction of the backbone. -/
theorem equation_11_6_22 (m : ℕ) (j : Fin m) :
    twoGridErrorOperator m *ᵥ modelq (2 * m + 1) (fineIndex j) =
        Real.sin (modeAngle m j / 2) ^ 2 •
          (modelq (2 * m + 1) (fineIndex j) + modelq (2 * m + 1) (aliasIndex j)) ∧
      twoGridErrorOperator m *ᵥ modelq (2 * m + 1) (middleIndex m) =
        modelq (2 * m + 1) (middleIndex m) ∧
      twoGridErrorOperator m *ᵥ modelq (2 * m + 1) (aliasIndex j) =
        Real.cos (modeAngle m j / 2) ^ 2 •
          (modelq (2 * m + 1) (fineIndex j) + modelq (2 * m + 1) (aliasIndex j)) := by
  simp only [twoGridErrorOperator_eq, modelq, mulVec_smul, modelCoarseCorrection_mulVec_sineVec,
    modelCoarseCorrection_mulVec_sineVec_middleIndex,
    modelCoarseCorrection_mulVec_sineVec_aliasIndex,
    ← smul_add, smul_comm (Real.sqrt _) (_ ^ 2 : ℝ), and_self]

/-- The weights of the block matrix of (11.6.21), indexed by the fine mode $k$:
$$\sigma_k = \sin^2\Big(\frac{(k + 1)\pi}{2(n + 1)}\Big), \qquad n = 2m + 1,$$
with $k$ 0-based. This is $s_j^2$ at the fine mode $j$, $c_j^2$ at its alias $2m - j$, and $1/2$
at the middle mode: (11.6.9) read the other way. -/
noncomputable def twoGridSigma (m : ℕ) (k : Fin (2 * m + 1)) : ℝ :=
  Real.sin ((((k : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))) ^ 2

/-- The partner `Fin.rev` of the fine mode $j$ is its alias $2m - j$. -/
private theorem rev_fineIndex {m : ℕ} (j : Fin m) : Fin.rev (fineIndex j) = aliasIndex j :=
  Fin.ext (by simp only [Fin.val_rev, fineIndex, aliasIndex]; omega)

/-- The partner `Fin.rev` of the alias of $j$ is the fine mode $j$. -/
private theorem rev_aliasIndex {m : ℕ} (j : Fin m) : Fin.rev (aliasIndex j) = fineIndex j := by
  rw [← rev_fineIndex, Fin.rev_rev]

/-- The middle mode is its own partner under `Fin.rev`. -/
private theorem rev_middleIndex (m : ℕ) : Fin.rev (middleIndex m) = middleIndex m :=
  Fin.ext (by simp only [Fin.val_rev, middleIndex]; omega)

/-- The weight $\sigma$ at the fine mode $j$ is $s_j^2$. -/
private theorem sigma_fineIndex {m : ℕ} (j : Fin m) :
    twoGridSigma m (fineIndex j) = Real.sin (modeAngle m j / 2) ^ 2 := by
  rw [twoGridSigma]
  congr 2
  rw [fineIndex, modeAngle]
  push_cast
  field_simp
  ring

/-- The weight $\sigma$ at the alias $2m - j$ is $c_j^2$. -/
private theorem sigma_aliasIndex {m : ℕ} (j : Fin m) :
    twoGridSigma m (aliasIndex j) = Real.cos (modeAngle m j / 2) ^ 2 := by
  have hj : (j : ℕ) ≤ 2 * m := by have := j.isLt; omega
  have e : (((aliasIndex j : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
      Real.pi / 2 - modeAngle m j / 2 := by
    rw [aliasIndex, Fin.val_mk, Nat.cast_sub hj, modeAngle]
    push_cast
    field_simp
    ring
  rw [twoGridSigma, e, Real.sin_pi_div_two_sub]

/-- The weight $\sigma$ at the middle mode is $1/2$. -/
private theorem sigma_middleIndex (m : ℕ) : twoGridSigma m (middleIndex m) = 1 / 2 := by
  have e : (((middleIndex m : ℕ) : ℝ) + 1) * Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
      Real.pi / 4 := by
    rw [middleIndex]
    push_cast
    field_simp
    ring
  rw [twoGridSigma, e, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Equation (11.6.22) for every fine mode at once: $E^h q_k = \sigma_k (q_k + q_{2m - k})$ for
every 0-based $k$; at the middle mode $2m - m = m$ and $\sigma_m = 1/2$, which gives
$E^h q_{m+1} = q_{m+1}$. -/
private theorem twoGridErrorOperator_mulVec_modelq (m : ℕ) (k : Fin (2 * m + 1)) :
    twoGridErrorOperator m *ᵥ modelq (2 * m + 1) k =
      twoGridSigma m k • (modelq (2 * m + 1) k + modelq (2 * m + 1) (Fin.rev k)) := by
  by_cases hk : (k : ℕ) < m
  · obtain ⟨j, rfl⟩ : ∃ j : Fin m, k = fineIndex j := ⟨⟨k, hk⟩, Fin.ext rfl⟩
    rw [rev_fineIndex, sigma_fineIndex]
    exact (equation_11_6_22 m j).1
  · by_cases hk' : m < (k : ℕ)
    · have hk2 := k.isLt
      obtain ⟨j, rfl⟩ : ∃ j : Fin m, k = aliasIndex j :=
        ⟨⟨2 * m - k, by omega⟩, Fin.ext (by simp only [aliasIndex, Fin.val_mk]; omega)⟩
      rw [rev_aliasIndex, sigma_aliasIndex, add_comm (modelq _ (aliasIndex j))]
      exact (equation_11_6_22 m j).2.2
    · obtain rfl : k = middleIndex m := Fin.ext (by simp only [middleIndex]; omega)
      rw [rev_middleIndex, sigma_middleIndex, twoGridErrorOperator_eq, modelq, mulVec_smul,
        modelCoarseCorrection_mulVec_sineVec_middleIndex, ← two_smul ℝ, smul_smul]
      norm_num

/-- **Equation (11.6.21)** of [golub2013matrix], the block matrix
$$\begin{bmatrix} S^h & 0 & C^h \mathcal{E}_m \\ 0 & 1 & 0 \\ \mathcal{E}_m S^h & 0 &
  \mathcal{E}_m C^h \mathcal{E}_m \end{bmatrix},$$
given column by column: the column of the fine mode $k$ carries $\sigma_k$ in the rows $k$ and
$2m - k$ (0-based). So the column of a fine mode $j < m$ carries $s_j^2$ in the rows $j$ and
$2m - j$, the column of its alias carries $c_j^2$ in the same two rows, and the middle column is
the unit vector, since $2\sigma_m = 1$. -/
noncomputable def twoGridBlock (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  Matrix.of fun i k =>
    twoGridSigma m k * ((if i = k then 1 else 0) + (if i = Fin.rev k then 1 else 0))

/-- Column $k$ of $Q^h B$ is $\sum_i B_{ik} q_i$. -/
private theorem modelQ_mul_apply {n : ℕ} {p : Type*} (B : Matrix (Fin n) p ℝ)
    (i : Fin n) (k : p) : (modelQ n * B) i k = ∑ j, modelq n j i * B j k := by
  rw [Matrix.mul_apply]
  rfl

/-- **Theorem 11.6.2** of [golub2013matrix]. Let $n = 2m + 1$. Then
$$E^h Q^h = Q^h \begin{bmatrix} S^h & 0 & C^h \mathcal{E}_m \\ 0 & 1 & 0 \\ \mathcal{E}_m S^h &
  0 & \mathcal{E}_m C^h \mathcal{E}_m \end{bmatrix}.$$

The proof of the source prints the value $(Q^{2h})^T A^{2h} Q^{2h} = (1/(2h^2))(I_m -
\sqrt{C^h})$, which is wrong: the coarse eigenvalues are $(4/h^2) S^h C^h$. The theorem itself
is correct. Here it is the action of the exact coarse-grid correction of the backbone on the
sine modes (`GolubVanLoan.Chapter11.equation_11_6_22`), assembled column by column. The source
leaves this to Problem P11.6.2. The block matrix is `GolubVanLoan.Chapter11.twoGridBlock`. -/
theorem theorem_11_6_2 (m : ℕ) :
    twoGridErrorOperator m * modelQ (2 * m + 1) = modelQ (2 * m + 1) * twoGridBlock m := by
  ext i k
  rw [modelQ_mul_apply]
  change (twoGridErrorOperator m *ᵥ modelq (2 * m + 1) k) i = _
  rw [twoGridErrorOperator_mulVec_modelq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  simp only [twoGridBlock, of_apply, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **Equation (11.6.20)** of [golub2013matrix], the block matrix
$$\begin{bmatrix} C^h \\ 0 \\ -\mathcal{E}_m S^h \end{bmatrix}$$
of Lemma 11.6.1, given column by column: the column of the coarse mode $l$ carries $c_l^2$ in
the row of the fine mode $l$ and $-s_l^2$ in the row of its alias $2m - l$ (0-based). -/
noncomputable def transferBlock (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin m) ℝ :=
  Matrix.of fun i l =>
    Real.cos (modeAngle m l / 2) ^ 2 * (if i = fineIndex l then 1 else 0) -
      Real.sin (modeAngle m l / 2) ^ 2 * (if i = aliasIndex l then 1 else 0)

/-- The prolongation satisfies $P^h_{2h} Q^{2h} = \sqrt{2}\, Q^h [C^h; 0; -\mathcal{E}_m S^h]$. -/
private theorem prolongation_mul_modelQ (m : ℕ) :
    prolongationMatrix m * modelQ m = modelQ (2 * m + 1) * (Real.sqrt 2 • transferBlock m) := by
  ext i l
  rw [Matrix.mul_smul, Matrix.smul_apply, modelQ_mul_apply]
  change (prolongationMatrix m *ᵥ modelq m l) i = _
  simp only [transferBlock, of_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [prolongationMatrix_eq, modelq, mulVec_smul, linearInterpolation_mulVec_sineVec]
  simp only [modelq, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sqrt_fine]
  field_simp

/-- **Lemma 11.6.1** of [golub2013matrix] (equation (11.6.20)). Let $n = 2m + 1$. Then
$$(Q^h)^T P^h_{2h} Q^{2h} = \sqrt{2} \begin{bmatrix} C^h \\ 0 \\ -\mathcal{E}_m S^h
  \end{bmatrix}, \qquad (Q^{2h})^T R^{2h}_h Q^h = \sqrt{\tfrac12} \begin{bmatrix} C^h \\ 0 \\
  -\mathcal{E}_m S^h \end{bmatrix}^T.$$

The block matrix is `GolubVanLoan.Chapter11.transferBlock m`. The proof of the source goes
through $(Q^h)^T B^h Q^h$ and (11.6.10); the proof here reads the columns off the backbone's
interpolation of a coarse sine mode. -/
theorem lemma_11_6_1 (m : ℕ) :
    (modelQ (2 * m + 1))ᵀ * prolongationMatrix m * modelQ m = Real.sqrt 2 • transferBlock m ∧
      (modelQ m)ᵀ * restrictionMatrix m * modelQ (2 * m + 1) =
        Real.sqrt (1 / 2) • (transferBlock m)ᵀ := by
  have h1 : (modelQ (2 * m + 1))ᵀ * prolongationMatrix m * modelQ m =
      Real.sqrt 2 • transferBlock m := by
    rw [Matrix.mul_assoc, prolongation_mul_modelQ, ← Matrix.mul_assoc, modelQ_transpose_mul,
      Matrix.one_mul]
  refine ⟨h1, ?_⟩
  have h2 : (modelQ m)ᵀ * restrictionMatrix m * modelQ (2 * m + 1) =
      (1 / 2 : ℝ) • ((modelQ (2 * m + 1))ᵀ * prolongationMatrix m * modelQ m)ᵀ := by
    rw [restrictionMatrix_eq_half_transpose, transpose_mul, transpose_mul, transpose_transpose,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [h2, h1, transpose_smul, smul_smul]
  congr 1
  have h2' : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

/-- The two-grid error operator as the coarse-grid correction of the backbone. Let $n = 2m + 1$ and
$p_1, p_2 \in \mathbb{N}$. Then $E^h$ is the coarse-grid correction `Multigrid.coarseCorrection`
of $A^h$ and the prolongation $P^h_{2h}$, that is, $I$ minus the $A^h$-orthogonal projector onto
the range of $P^h_{2h}$. The error operator $(G^h)^{p_2} E^h (G^h)^{p_1}$ of (11.6.19) is
`Multigrid.twoGridOperator` with the weighted Jacobi smoother $G^h = G^{h,2/3}$ and $p_1$
pre-smoothing and $p_2$ post-smoothing steps.

Hence the results of `Numlib.Multigrid.Basic` apply to $E^h$; for example, $E^h$ is idempotent
and self-adjoint in the $A^h$-inner product. The operators are compared as linear maps of
Euclidean space, through `Matrix.toEuclideanLin`, and $A^h$ is coercive because it is positive
definite. -/
theorem twoGridError_eq_coarseCorrection (m : ℕ) (p₁ p₂ : ℕ) :
    let hA : (toEuclideanLin (modelA (2 * m + 1))).IsSymmetricCoercive :=
      ((posDef_symmTridiagonalToeplitz_neg_one_two (2 * m + 1)).smul (by positivity :
        (0 : ℝ) < (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2)).isSymmetricCoercive_toEuclideanLin
    toEuclideanLin (twoGridErrorOperator m) =
        coarseCorrection (toEuclideanLin (modelA (2 * m + 1))) hA
          (toEuclideanLin (prolongationMatrix m)) ∧
      toEuclideanLin ((twoThirdsJacobi (2 * m + 1)).iterationOperator ^ p₂ *
          twoGridErrorOperator m * (twoThirdsJacobi (2 * m + 1)).iterationOperator ^ p₁) =
        twoGridOperator (toEuclideanLin (modelA (2 * m + 1))) hA
          (toEuclideanLin (prolongationMatrix m))
          (toEuclideanLin (twoThirdsJacobi (2 * m + 1)).iterationOperator) p₁ p₂ := by
  intro hA
  have hPT : (prolongationMatrix m)ᵀ = (2 : ℝ) • restrictionMatrix m := by
    rw [restrictionMatrix_eq_half_transpose, smul_smul]
    norm_num
  have hAm : IsUnit (modelA m).det := by
    rw [← isUnit_iff_isUnit_det]
    exact ((posDef_symmTridiagonalToeplitz_neg_one_two m).smul
      (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)).isUnit
  have key : (2 : ℝ) • restrictionMatrix m * (modelA (2 * m + 1) * (prolongationMatrix m *
      ((modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)))) =
      (2 : ℝ) • restrictionMatrix m * modelA (2 * m + 1) := by
    simp only [Matrix.smul_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, galerkin_coarse_eq, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, mul_nonsing_inv _ hAm, Matrix.one_mul]
  have hE : toEuclideanLin (twoGridErrorOperator m) = coarseCorrection
      (toEuclideanLin (modelA (2 * m + 1))) hA (toEuclideanLin (prolongationMatrix m)) := by
    ext1 x
    rw [coarseCorrection_apply]
    have hy : galerkinCoarse (toEuclideanLin (modelA (2 * m + 1)))
        (toEuclideanLin (prolongationMatrix m))
        (toEuclideanLin ((modelA m)⁻¹ * restrictionMatrix m * modelA (2 * m + 1)) x) =
        LinearMap.adjoint (toEuclideanLin (prolongationMatrix m))
          (toEuclideanLin (modelA (2 * m + 1)) x) := by
      rw [galerkinCoarse_apply, ← toEuclideanLin_conjTranspose_eq_adjoint,
        conjTranspose_eq_transpose_of_trivial, hPT]
      simp only [← toEuclideanLin_mul_apply]
      rw [key]
    rw [coarseProjection_apply_eq _ hA _ hy, ← toEuclideanLin_mul_apply, twoGridErrorOperator,
      map_sub, toEuclideanLin_one, LinearMap.sub_apply, LinearMap.id_apply]
    simp only [Matrix.mul_assoc]
  refine ⟨hE, ?_⟩
  ext1 x
  rw [twoGridOperator_apply, ← hE]
  simp only [toEuclideanLin_mul_apply, toEuclideanLin_pow]

/-! ### The error of one cycle, mode by mode -/

/-- For the block matrix $B$ of (11.6.21), $(B\gamma)_i = \sigma_i \gamma_i + \sigma_{2m - i}
\gamma_{2m - i}$ (0-based). -/
private theorem twoGridBlock_mulVec (m : ℕ) (γ : Fin (2 * m + 1) → ℝ) (i : Fin (2 * m + 1)) :
    (twoGridBlock m *ᵥ γ) i =
      twoGridSigma m i * γ i + twoGridSigma m (Fin.rev i) * γ (Fin.rev i) := by
  have hrev : ∀ k : Fin (2 * m + 1), (i = Fin.rev k) = (k = Fin.rev i) := fun k =>
    propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp only [mulVec, dotProduct, twoGridBlock, of_apply, hrev, mul_add, add_mul, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- **Section 11.6.3** of [golub2013matrix], the error of one cycle, mode by mode. Let $n = 2m + 1$,
let $A^h u = b^h$, and let $u_c - u = \sum_j \alpha_j q_j$. Run the exact two-grid cycle of
`GolubVanLoan.Chapter11.equation_11_6_19` from $u_c$ with $p_1$ pre-smoothing and $p_2$
post-smoothing steps. Then $u_{++} - u = \sum_j \tilde\alpha_j q_j$, where, with
$\tau = \tau^{h,2/3}$ and for $j = 1{:}m$,
$$\tilde\alpha_j = \big(\alpha_j \tau_j^{p_1} s_j^2 + \alpha_{n-j+1} \tau_{n-j+1}^{p_1}
  c_j^2\big) \tau_j^{p_2},$$
$$\tilde\alpha_{n-j+1} = \big(\alpha_j \tau_j^{p_1} s_j^2 + \alpha_{n-j+1} \tau_{n-j+1}^{p_1}
  c_j^2\big) \tau_{n-j+1}^{p_2},$$
$$\tilde\alpha_{m+1} = \alpha_{m+1} \tau_{m+1}^{p_1 + p_2}.$$

In 0-based indices the three cases are the fine mode $j$, the alias $2m - j$ and the middle mode
$m$. -/
theorem twoGrid_error_coeffs (m : ℕ) {b u : Fin (2 * m + 1) → ℝ}
    (hu : modelA (2 * m + 1) *ᵥ u = b) (uc α : Fin (2 * m + 1) → ℝ)
    (hα : uc - u = modelQ (2 * m + 1) *ᵥ α) (p₁ p₂ : ℕ) :
    ∃ α' : Fin (2 * m + 1) → ℝ,
      Id.run (twoGridCycle pure (fun v => pure ((twoThirdsJacobi (2 * m + 1)).mulVecStep b v))
        (fun r => pure ((modelA m)⁻¹ *ᵥ r)) b uc p₁ p₂) - u = modelQ (2 * m + 1) *ᵥ α' ∧
      (∀ j : Fin m,
        α' (fineIndex j) = (α (fineIndex j) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (fineIndex j) ^ p₁ *
            Real.sin (modeAngle m j / 2) ^ 2 + α (aliasIndex j) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (aliasIndex j) ^ p₁ *
            Real.cos (modeAngle m j / 2) ^ 2) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (fineIndex j) ^ p₂ ∧
        α' (aliasIndex j) = (α (fineIndex j) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (fineIndex j) ^ p₁ *
            Real.sin (modeAngle m j / 2) ^ 2 + α (aliasIndex j) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (aliasIndex j) ^ p₁ *
            Real.cos (modeAngle m j / 2) ^ 2) *
            weightedJacobiTau (2 * m + 1) (2 / 3) (aliasIndex j) ^ p₂) ∧
      α' (middleIndex m) =
        α (middleIndex m) * weightedJacobiTau (2 * m + 1) (2 / 3) (middleIndex m) ^ (p₁ + p₂) := by
  set τ := weightedJacobiTau (2 * m + 1) (2 / 3)
  set β : Fin (2 * m + 1) → ℝ := fun k => τ k ^ p₁ * α k
  refine ⟨fun k => τ k ^ p₂ * (twoGridBlock m *ᵥ β) k, ?_, fun j => ⟨?_, ?_⟩, ?_⟩
  · have h2 : twoGridErrorOperator m *ᵥ (modelQ (2 * m + 1) *ᵥ β) =
        modelQ (2 * m + 1) *ᵥ (twoGridBlock m *ᵥ β) := by
      rw [mulVec_mulVec, theorem_11_6_2, ← mulVec_mulVec]
    rw [equation_11_6_19 m hu, hα, ← mulVec_mulVec, ← mulVec_mulVec,
      weightedJacobi_pow_mulVec_modelQ, h2, weightedJacobi_pow_mulVec_modelQ]
  · simp only [twoGridBlock_mulVec, rev_fineIndex, sigma_fineIndex, sigma_aliasIndex, β]
    ring
  · simp only [twoGridBlock_mulVec, rev_aliasIndex, sigma_fineIndex, sigma_aliasIndex, β]
    ring
  · simp only [twoGridBlock_mulVec, rev_middleIndex, sigma_middleIndex, β]
    ring

/-- **Section 11.6.3** of [golub2013matrix], the bounds on which the conclusion rests. Let
$n = 2m + 1$. For $j = 1{:}m$,
$$|\tau_{n-j+1}^{h,2/3}| \le \frac13, \qquad s_j^2 \le \frac12,$$
and both bounds are independent of $n$. In `GolubVanLoan.Chapter11.twoGrid_error_coeffs` each of
the two terms of $\tilde\alpha_j$ and of $\tilde\alpha_{n-j+1}$ carries a factor $s_j^2$ or
$\tau_{n-j+1}^{p_1}$, and $\tilde\alpha_{m+1}$ carries the factor
$\tau_{m+1}^{p_1 + p_2} = (1/3)^{p_1 + p_2}$: the smoother damps the high-frequency
coefficients, and the coarse grid damps the low-frequency ones. -/
theorem twoGrid_damping_bounds (m : ℕ) (j : Fin m) :
    |weightedJacobiTau (2 * m + 1) (2 / 3) (aliasIndex j)| ≤ 1 / 3 ∧
      Real.sin (modeAngle m j / 2) ^ 2 ≤ 1 / 2 := by
  refine ⟨(weightedJacobi_twoThirds m).1 _ (by simp only [aliasIndex, Fin.val_mk]; omega), ?_⟩
  have h0 := modeAngle_pos j
  have h1 := modeAngle_lt_pi_div_two j
  have hs : Real.sin (modeAngle m j / 2) ≤ Real.sqrt 2 / 2 := by
    rw [← Real.sin_pi_div_four]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by linarith)
  have hs0 : 0 ≤ Real.sin (modeAngle m j / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have := pow_le_pow_left₀ hs0 hs 2
  rw [div_pow, Real.sq_sqrt (by norm_num)] at this
  linarith

end GolubVanLoan.Chapter11
