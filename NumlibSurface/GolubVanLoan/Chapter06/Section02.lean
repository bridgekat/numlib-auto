/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares.Constrained
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter06.Section01

/-!
# Golub and Van Loan, Section 6.2: Constrained least squares

This module formalizes §6.2 of [golub2013matrix], least-squares problems with constraints. The LSQI
problem minimizes $\|Ax - b\|_2$ subject to $\|Bx - d\|_2 \le \alpha$. Over a sphere ($B = I$,
$d = 0$), the solution is $x_{LS}$ if $\|x_{LS}\|_2 \le \alpha$. Otherwise the solution lies on the
boundary, and it is the ridge solution $x(\lambda_+)$, where $\lambda_+$ is the unique positive root
of the secular equation $\|x(\lambda)\|_2^2 = \alpha^2$ ((6.2.1)–(6.2.4) and Algorithm 6.2.1). Over
an ellipsoid, the GSVD transforms the problem into a diagonal one ((6.2.6)–(6.2.8)). The LSE problem
minimizes $\|Ax - b\|_2$ subject to $Bx = d$. The module solves it through the QR factorization of
$B^T$ (the derivation of Algorithm 6.2.2), through the augmented system (6.2.10), through the GSVD
((6.2.11)–(6.2.12)), and as the limit of weighted problems ((6.2.13)–(6.2.14)).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.LeastSquares.Constrained`,
`Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized` and `Numlib.LinearAlgebra.Matrix.GSVD`, and
they use Algorithms 1.1.2–1.1.3 of Chapter 1 and the results of §6.1.

## Main definitions

* §6.2.1, `GolubVanLoan.Chapter06.IsSphereLSQISolution`: $x$ minimizes $\|Ax - b\|_2$ subject to
  $\|x\|_2 \le \alpha$.
* Algorithm 6.2.1, `GolubVanLoan.Chapter06.algorithm_6_2_1`: least squares over a sphere by the SVD.
* Algorithm 6.2.2, `GolubVanLoan.Chapter06.algorithm_6_2_2`: least squares with linear equality
  constraints by the QR factorization of $B^T$.

## Main results

* §6.2.1, `GolubVanLoan.Chapter06.isLSQISolution_pinv`: if $\|x_{LS}\|_2 \le \alpha$, then $x_{LS}$
  solves (6.2.1).
* Equation (6.2.3), `GolubVanLoan.Chapter06.equation_6_2_3`: $x_{LS}$ and $\|x_{LS}\|_2^2$ in terms
  of an SVD.
* §6.2.1, `GolubVanLoan.Chapter06.IsSphereLSQISolution.norm_eq`: if $\|x_{LS}\|_2 > \alpha$, every
  solution lies on the sphere $\|x\|_2 = \alpha$.
* §6.2.1, `GolubVanLoan.Chapter06.secular_existsUnique`: the secular function
  $\|x(\lambda)\|_2^2 - \alpha^2$ is strictly decreasing and has exactly one positive root.
* Equation (6.2.4), `GolubVanLoan.Chapter06.equation_6_2_4`: the residual $\|Ax(\lambda) - b\|_2^2$
  in terms of an SVD.
* §6.2.1, `GolubVanLoan.Chapter06.isSphereLSQISolution_tikhonov`: if $\|x(\lambda)\|_2 = \alpha$ for
  some $\lambda > 0$, then $x(\lambda)$ solves (6.2.1).
* Algorithm 6.2.1, `GolubVanLoan.Chapter06.algorithm_6_2_1_spec`: in exact arithmetic, the output
  solves (6.2.1).
* Equation (6.2.6), `GolubVanLoan.Chapter06.equation_6_2_6`: the GSVD transforms the LSQI problem
  into a diagonal one.
* Equation (6.2.7), `GolubVanLoan.Chapter06.equation_6_2_7`: $\|D_A y - \tilde b\|_2^2$ in
  coordinates.
* Equation (6.2.8), `GolubVanLoan.Chapter06.equation_6_2_8`: $\|D_B y - \tilde d\|_2^2$ in
  coordinates.
* §6.2.3, `GolubVanLoan.Chapter06.isLSQISolution_zero_iff`: the LSE problem is the LSQI problem with
  $\alpha = 0$.
* §6.2.3, `GolubVanLoan.Chapter06.isLSESolution_qr`: the solution of the LSE problem from the QR
  factorization of $B^T$.
* §6.2.3, `GolubVanLoan.Chapter06.isLSESolution_not_unique`: if $d \in \operatorname{ran}(B)$, an
  LSE solution exists, and it is determined only up to $\operatorname{null}(A) \cap
  \operatorname{null}(B)$.
* Algorithm 6.2.2, `GolubVanLoan.Chapter06.algorithm_6_2_2_spec`: in exact arithmetic, the output is
  the unique solution of the LSE problem.
* Equation (6.2.10), `GolubVanLoan.Chapter06.equation_6_2_10`: a solution of the augmented system
  gives an LSE solution.
* §6.2.4, `GolubVanLoan.Chapter06.equation_6_2_10_isUnit`: the augmented system is nonsingular if
  $A$ and $B$ have full rank.
* Equation (6.2.11), `GolubVanLoan.Chapter06.equation_6_2_11`: the GSVD transforms the LSE problem
  into a diagonal one.
* Equation (6.2.12), `GolubVanLoan.Chapter06.equation_6_2_12`: the LSE solution in GSVD coordinates.
* Equation (6.2.13), `GolubVanLoan.Chapter06.equation_6_2_13`: the method of weighting is a stacked
  least-squares problem.
* Equation (6.2.14), `GolubVanLoan.Chapter06.equation_6_2_14`: the difference $x(\lambda) - x$ in
  GSVD coordinates.
* §6.2.6, `GolubVanLoan.Chapter06.tendsto_penaltyLSE_solution`: $x(\lambda) \to x$ as
  $\lambda \to \infty$.

## Conventions

* Matrices are real and indices are 0-based. Vectors of a least-squares statement are in
  `EuclideanSpace ℝ (Fin n)`, where a matrix acts through `Matrix.toEuclideanLin`. The parameter
  $\lambda$ of the source is written `μ` in Lean.
* The LSQI problem $\min \|Ax - b\|_2$ subject to $\|Bx - d\|_2 \le \alpha$ is
  `Matrix.IsLSQISolution A b B d α`. The sphere problem (6.2.1) is its case $B = I$, $d = 0$,
  `GolubVanLoan.Chapter06.IsSphereLSQISolution`. The LSE problem is `Matrix.IsLSESolution A b B d`.
* An SVD is `Matrix.IsSVD A U σ V`. Its sums run over $i \le \min(m, n)$; the terms with
  $\sigma_i = 0$, which are those after the rank, vanish.
* A GSVD is `Matrix.IsGSVD A B U₁ U₂ X α β`, in the block order of Theorem 6.1.1.

## Implementation notes

* Algorithm 6.2.1 follows the algorithm conventions of `NumlibSurface.GolubVanLoan`: every
  arithmetic result passes through the rounding hook `rnd`. The steps "Compute the SVD" and "Find
  $\lambda_+ > 0$ such that …" are monadic parameters `svd` and `root`, because the SVD algorithm of
  the source is in Chapter 8 and the source names no root finder. The specification assumes their
  specifications. The gaxpy $\tilde b = U^T b$ is Algorithm 1.1.3, and each update
  $x \leftarrow x + c v_i$ is the saxpy Algorithm 1.1.2.

## Deviations from the source

* **§6.2.1, the secular equation** (reading). The source's $f(0) > 0$ is read as
  $f(0^+) = \|x_{LS}\|_2^2 - \alpha^2 > 0$, because $x(\lambda)$ is $x_{LS}$ only in the limit. See
  `GolubVanLoan.Chapter06.secular_existsUnique`.
* **Algorithm 6.2.1** (generalization). The source assumes $m \ge n$; the correctness statement
  holds for all $m$ and $n$. See `GolubVanLoan.Chapter06.algorithm_6_2_1_spec`.
* **Equation (6.2.6)** (typo). The source cites "(6.2.23)" for (6.1.23). See
  `GolubVanLoan.Chapter06.equation_6_2_6`.
* **Equation (6.2.7)** (reading). The source prints it in the block order of the GSVD of the third
  edition, which is inconsistent with Theorem 6.1.1. The library uses the block order of Theorem
  6.1.1. See `GolubVanLoan.Chapter06.equation_6_2_7`.
* **Equation (6.2.8)** (correction). The source prints it in the block order of the third edition,
  and its second sum, over $\tilde d_i$ for $i = m_2 + 1, \dots, n_1$, is meaningless. See
  `GolubVanLoan.Chapter06.equation_6_2_8`.
* **§6.2.3, non-uniqueness of the LSE solution** (reading). The printed sentence is garbled. The
  library states that an LSE solution exists for $d \in \operatorname{ran}(B)$ and stays a solution
  after adding a vector of $\operatorname{null}(A) \cap \operatorname{null}(B)$. See
  `GolubVanLoan.Chapter06.isLSESolution_not_unique`.
* **Algorithm 6.2.2** (generalization). The source assumes $m_2 < n_1$; the correctness statement
  allows $m_2 \le n_1$. See `GolubVanLoan.Chapter06.algorithm_6_2_2_spec`.
* **Equation (6.2.12)** (correction). The source prints it in the block order of the third edition.
  See `GolubVanLoan.Chapter06.equation_6_2_12`.
* **Equation (6.2.14)** (correction). The source prints it in the block order of the third edition,
  with $\lambda^2$ for $\lambda$, $u_i^T b$ and $v_i^T d$ for $\tilde b_i$ and $\tilde d_i$, and the
  range $1{:}p$. See `GolubVanLoan.Chapter06.equation_6_2_14`.

## Not formalized

* **Equation (6.2.2).** It recalls the SVD.
* **Equations (6.2.5) and (6.2.9).** They define the problems, which are the backbone predicates
  `Matrix.IsLSQISolution` and `Matrix.IsLSESolution`.
* **The Lagrange-multiplier arguments of §6.2.1, §6.2.2 and §6.2.4.**
* **The remark that there may not be a solution if $\operatorname{rank}(B) < m_2$.**
* **The numerical precautions of Powell and Reid.**
* **The flop counts.** Operation counts are out of scope for the library.
-/

open Matrix Finset Filter Topology

namespace GolubVanLoan.Chapter06

variable {m n : ℕ}

/-! ### §6.2.1 Least squares minimization over a sphere -/

/-- **§6.2.1** of [golub2013matrix], the LSQI problem (6.2.1). "Given
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, and a positive $\alpha \in \mathbb{R}$,
we consider the problem $\min_{\|x\|_2 \le \alpha} \|Ax - b\|_2$." A vector $x \in \mathbb{R}^n$
**solves the problem** if $\|x\|_2 \le \alpha$ and $\|Ax - b\|_2 \le \|Ay - b\|_2$ for every $y$
with $\|y\|_2 \le \alpha$.

The definition is `Matrix.IsLSQISolution` with $B = I$ and $d = 0$. It does not require
$\alpha > 0$. -/
def IsSphereLSQISolution (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) (α : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  Matrix.IsLSQISolution A b (1 : Matrix (Fin n) (Fin n) ℝ) 0 α x

/-- **§6.2.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and
$\alpha \in \mathbb{R}$. "If the unconstrained minimum norm solution $x_{LS}$ satisfies
$\|x_{LS}\|_2 \le \alpha$, then it obviously solves (6.2.1)": if $\|A^+ b\|_2 \le \alpha$, then
$x_{LS} = A^+ b$ solves (6.2.1). -/
theorem isLSQISolution_pinv (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m)) {α : ℝ}
    (h : ‖toEuclideanLin A.pinv b‖ ≤ α) : IsSphereLSQISolution A b α (toEuclideanLin A.pinv b) := by
  unfold IsSphereLSQISolution
  exact isLSQISolution_of_isLeastSquaresSolution (isLeastSquaresSolution_pinv A b)
    (by rw [toEuclideanLin_one_apply, sub_zero]; exact h)

/-- On real Euclidean space, $\langle u, b \rangle = u^T b$. -/
private theorem inner_toLp_eq_dotProduct (u : Fin m → ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (WithLp.toLp 2 u) b = u ⬝ᵥ WithLp.ofLp b := by
  change inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 (WithLp.ofLp b)) = _
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

/-- **Equation (6.2.3)** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$, and let $b \in \mathbb{R}^m$. Then $x_{LS} = A^+ b$ satisfies
$$x_{LS} = \sum_{i=1}^{\min(m, n)} \frac{u_i^T b}{\sigma_i} v_i, \qquad \|x_{LS}\|_2^2 =
  \sum_{i=1}^{\min(m, n)} \left(\frac{u_i^T b}{\sigma_i}\right)^2.$$
A term with $\sigma_i = 0$ is zero, because division by zero gives zero in Lean. So these are
the sums to $r = \operatorname{rank}(A)$ of the source. -/
theorem equation_6_2_3 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) (b : EuclideanSpace ℝ (Fin m)) :
    toEuclideanLin A.pinv b = ∑ i : Fin (min m n),
      (Uᵀ (Fin.castLE (min_le_left m n) i) ⬝ᵥ WithLp.ofLp b / σ i) •
        (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)) : EuclideanSpace ℝ (Fin n)) ∧
    ‖toEuclideanLin A.pinv b‖ ^ 2 = ∑ i : Fin (min m n),
      (Uᵀ (Fin.castLE (min_le_left m n) i) ⬝ᵥ WithLp.ofLp b / σ i) ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [toEuclideanLin_pinv_eq_sum_of_isSVD h b]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_smul, inner_toLp_eq_dotProduct, RCLike.ofReal_real_eq_id, id_eq, inv_mul_eq_div]
  · rw [norm_sq_toEuclideanLin_pinv_eq_sum_of_isSVD h b]
    refine sum_congr rfl fun i _ => ?_
    rw [inner_toLp_eq_dotProduct, div_pow, div_pow, Real.norm_eq_abs, sq_abs]

/-- **§6.2.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and
$\alpha \in \mathbb{R}$. "Otherwise, $\|x_{LS}\|_2^2 = \sum (u_i^T b / \sigma_i)^2 > \alpha^2$,
and it follows that the solution to (6.2.1) is on the boundary of the constraint sphere": if
$\alpha^2 < \|A^+ b\|_2^2$, then every solution $x$ of (6.2.1) has $\|x\|_2 = \alpha$. -/
theorem IsSphereLSQISolution.norm_eq {A : Matrix (Fin m) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin m)}
    {α : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hLS : α ^ 2 < ‖toEuclideanLin A.pinv b‖ ^ 2) (h : IsSphereLSQISolution A b α x) : ‖x‖ = α :=
  Matrix.IsLSQISolution.norm_eq_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hLS)
    (show Matrix.IsLSQISolution A b (1 : Matrix (Fin n) (Fin n) ℝ) 0 α x from h)

/-- $(s|a|/c)^2 = (sa/c)^2$ for real $s$, $a$ and $c$. -/
private theorem sq_mul_abs_div (s a c : ℝ) : (s * |a| / c) ^ 2 = (s * a / c) ^ 2 := by
  rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]

/-- **§6.2.1** of [golub2013matrix], the secular equation. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$, let $b \in \mathbb{R}^m$, and let $0 < \alpha < \|x_{LS}\|_2$,
where $x_{LS} = A^+ b$. Let $x(\lambda) = (A^T A + \lambda I)^{-1} A^T b$ and
$$f(\lambda) = \|x(\lambda)\|_2^2 - \alpha^2.$$
Then for every $\lambda > 0$
$$f(\lambda) = \sum_{k=1}^{\min(m, n)} \left(\frac{\sigma_k u_k^T b}{\sigma_k^2 +
  \lambda}\right)^2 - \alpha^2,$$
the function $f$ is strictly decreasing on $\lambda > 0$, and $f$ has exactly one positive root
$\lambda_+$. The source argues: "Since $f'(\lambda) < 0$ for $\lambda \ge 0$, it follows that
$f$ has a unique positive root $\lambda_+$".

**Reading.** The source uses $f(0) > 0$. Because $x(\lambda)$ is equal to $x_{LS}$ only in the
limit $\lambda \to 0^+$, this is read as $f(0^+) = \|x_{LS}\|_2^2 - \alpha^2 > 0$.

The ridge solution $x(\lambda)$ is `Matrix.tikhonov` of $A$ at $\lambda$, applied to $b$. -/
theorem secular_existsUnique {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {b : EuclideanSpace ℝ (Fin m)}
    {α : ℝ} (hα0 : 0 < α) (hα : α < ‖toEuclideanLin A.pinv b‖) :
    (∀ μ, 0 < μ → ‖toEuclideanLin (A.tikhonov μ) b‖ ^ 2 - α ^ 2 = ∑ i : Fin (min m n),
      (σ i * (Uᵀ (Fin.castLE (min_le_left m n) i) ⬝ᵥ WithLp.ofLp b) / (σ i ^ 2 + μ)) ^ 2 -
        α ^ 2) ∧
    StrictAntiOn (fun μ => ‖toEuclideanLin (A.tikhonov μ) b‖ ^ 2 - α ^ 2) (Set.Ioi 0) ∧
    ∃! μ, 0 < μ ∧ ‖toEuclideanLin (A.tikhonov μ) b‖ ^ 2 - α ^ 2 = 0 := by
  refine ⟨fun μ hμ => ?_, ?_, ?_⟩
  · rw [norm_sq_toEuclideanLin_tikhonov_eq_sum_of_isSVD h hμ b]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [inner_toLp_eq_dotProduct, Real.norm_eq_abs, sq_mul_abs_div]
  · -- `Aᵀb ≠ 0`: otherwise every `x(λ)` vanishes and so does their limit `x_LS`
    have hb : toEuclideanLin Aᴴ b ≠ 0 := by
      intro hb
      have h0 : ∀ μ, toEuclideanLin (A.tikhonov μ) b = 0 := fun μ => by
        rw [tikhonov_def, toEuclideanLin_mul_apply, hb, map_zero]
      have hlim := tendsto_ridge_leastSquares A b
      simp only [h0] at hlim
      have := tendsto_nhds_unique hlim tendsto_const_nhds
      rw [this, norm_zero] at hα
      linarith
    intro μ hμ ν hν hμν
    have := strictAntiOn_norm_toEuclideanLin_tikhonov A hb hμ hν hμν
    simp only at this ⊢
    have h0 := norm_nonneg (toEuclideanLin (A.tikhonov ν) b)
    nlinarith
  · obtain ⟨μ, ⟨hμ, hμα⟩, huniq⟩ := existsUnique_norm_toEuclideanLin_tikhonov_eq hα0 hα
    refine ⟨μ, ⟨hμ, by rw [hμα, sub_self]⟩, fun ν ⟨hν, hνα⟩ => huniq ν ⟨hν, ?_⟩⟩
    have h2 : ‖toEuclideanLin (A.tikhonov ν) b‖ ^ 2 = α ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) hα0.le two_ne_zero).1 h2

/-- **Equation (6.2.4)** of [golub2013matrix]. Let $U^T A V = \Sigma$ be an SVD of
$A \in \mathbb{R}^{m \times n}$, let $\lambda > 0$, and let $b \in \mathbb{R}^m$. Then
$$\rho(\lambda) = \|A x(\lambda) - b\|_2^2 = \|A x_{LS} - b\|_2^2 + \sum_{\sigma_i \neq 0}
  \left(\frac{\lambda u_i^T b}{\sigma_i^2 + \lambda}\right)^2,$$
where $x_{LS} = A^+ b$ and the sum runs over the indices $i \le \min(m, n)$ with
$\sigma_i \neq 0$, which are $i = 1, \dots, r$ in the source. -/
theorem equation_6_2_4 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {μ : ℝ} (hμ : 0 < μ)
    (b : EuclideanSpace ℝ (Fin m)) :
    ‖toEuclideanLin A (toEuclideanLin (A.tikhonov μ) b) - b‖ ^ 2 =
      ‖toEuclideanLin A (toEuclideanLin A.pinv b) - b‖ ^ 2 +
        ∑ i ∈ univ.filter (fun i : Fin (min m n) => σ i ≠ 0),
          (μ * (Uᵀ (Fin.castLE (min_le_left m n) i) ⬝ᵥ WithLp.ofLp b) / (σ i ^ 2 + μ)) ^ 2 := by
  rw [norm_sq_toEuclideanLin_tikhonov_sub_eq_sum_of_isSVD h hμ b]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [inner_toLp_eq_dotProduct, Real.norm_eq_abs, sq_mul_abs_div]

/-- **§6.2.1** of [golub2013matrix]. "It follows that $x(\lambda_+)$ solves (6.2.1)": let
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$, $\lambda > 0$ and
$\alpha \in \mathbb{R}$. If $\|x(\lambda)\|_2 = \alpha$, then $x(\lambda)$ solves the problem
(6.2.1) with radius $\alpha$. -/
theorem isSphereLSQISolution_tikhonov {A : Matrix (Fin m) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin m)}
    {μ : ℝ} (hμ : 0 < μ) {α : ℝ} (hn : ‖toEuclideanLin (A.tikhonov μ) b‖ = α) :
    IsSphereLSQISolution A b α (toEuclideanLin (A.tikhonov μ) b) := by
  unfold IsSphereLSQISolution
  exact Matrix.isLSQISolution_tikhonov hμ hn

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.2.1** of [golub2013matrix]. "Given $A \in \mathbb{R}^{m \times n}$ with $m \ge n$,
$b \in \mathbb{R}^m$, and $\alpha > 0$, the following algorithm computes a vector
$x \in \mathbb{R}^n$ such that $\|Ax - b\|_2$ is minimum subject to the constraint that
$\|x\|_2 \le \alpha$":
```
Compute the SVD A = UΣVᵀ, save V = [v₁ | ⋯ | v_n], form b̃ = Uᵀb, and determine r = rank(A).
if ∑_{i=1}^r (b̃_i/σ_i)² > α²
    Find λ₊ > 0 such that ∑_{i=1}^r (σ_i b̃_i/(σ_i² + λ₊))² = α².
    x = ∑_{i=1}^r (σ_i b̃_i/(σ_i² + λ₊)) v_i
else
    x = ∑_{i=1}^r (b̃_i/σ_i) v_i
end
```
The program does not assume $m \ge n$.

"Compute the SVD" is the parameter `svd`, which returns $(U, \sigma, V)$. "Find $\lambda_+$" is
the parameter `root`, which receives the secular function of the computed data. The indices
$i = 1{:}r$ are the indices $i \le \min(m, n)$ with $\sigma_i \neq 0$; for sorted singular
values these are the first $r$. -/
noncomputable def algorithm_6_2_1
    (svd : Matrix (Fin m) (Fin n) ℝ →
      M (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (root : (ℝ → ℝ) → M ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (α : ℝ) :
    M (Fin n → ℝ) := do
  let USV ← svd A
  let U := USV.1
  let σ := USV.2.1
  let V := USV.2.2
  let bt ← Chapter01.algorithm_1_1_3 rnd Uᵀ b 0
  let I := (List.finRange (min m n)).filter fun i : Fin (min m n) => σ i ≠ 0
  let s ← I.foldlM (fun s (i : Fin (min m n)) => do
    let q ← rnd (bt (Fin.castLE (min_le_left m n) i) / σ i)
    let q2 ← rnd (q * q)
    rnd (s + q2)) 0
  let α2 ← rnd (α * α)
  if α2 < s then
    let lam ← root fun t =>
      (I.map fun i : Fin (min m n) =>
        (σ i * bt (Fin.castLE (min_le_left m n) i) / (σ i ^ 2 + t)) ^ 2).sum - α ^ 2
    I.foldlM (fun x (i : Fin (min m n)) => do
      let num ← rnd (σ i * bt (Fin.castLE (min_le_left m n) i))
      let s2 ← rnd (σ i * σ i)
      let den ← rnd (s2 + lam)
      let c ← rnd (num / den)
      Chapter01.algorithm_1_1_2 rnd c (fun j => V j (Fin.castLE (min_le_right m n) i)) x) 0
  else
    I.foldlM (fun x (i : Fin (min m n)) => do
      let c ← rnd (bt (Fin.castLE (min_le_left m n) i) / σ i)
      Chapter01.algorithm_1_1_2 rnd c (fun j => V j (Fin.castLE (min_le_right m n) i)) x) 0

end Programs

/-- If the terms that a filter drops vanish, the sum over the filtered list of the indices of
`Fin k` is the full sum. -/
private theorem sum_map_filter_finRange' {k : ℕ} {β : Type*} [AddCommMonoid β] (p : Fin k → Prop)
    [DecidablePred p] (g : Fin k → β) (hg : ∀ i, ¬ p i → g i = 0) :
    (((List.finRange k).filter fun i => decide (p i)).map g).sum = ∑ i, g i := by
  rw [List.sum_map_filter_finRange, Finset.sum_filter_of_ne fun i _ h => not_not.1 (mt (hg i) h)]

/-- **Algorithm 6.2.1** of [golub2013matrix], correctness in exact arithmetic. Let
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $\alpha > 0$. Assume that the
subroutine `svd` returns an SVD of every matrix, and that the subroutine `root`, given a
function with exactly one positive root, returns a positive root of that function. Then the
output $x$ of Algorithm 6.2.1 in exact arithmetic solves the LSQI problem (6.2.1).

**Generalization.** The source assumes $m \ge n$. The statement holds for all $m$ and $n$.

The first branch computes $x(\lambda_+)$ (`GolubVanLoan.Chapter06.equation_6_1_14`,
`GolubVanLoan.Chapter06.secular_existsUnique`,
`GolubVanLoan.Chapter06.isSphereLSQISolution_tikhonov`), and the second branch computes $x_{LS}$
(`GolubVanLoan.Chapter06.equation_6_2_3`, `GolubVanLoan.Chapter06.isLSQISolution_pinv`). -/
theorem algorithm_6_2_1_spec
    (svd : Matrix (Fin m) (Fin n) ℝ →
      Id (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (hsvd : ∀ A', IsSVD A' (Id.run (svd A')).1 (Id.run (svd A')).2.1 (Id.run (svd A')).2.2)
    (root : (ℝ → ℝ) → Id ℝ)
    (hroot : ∀ f : ℝ → ℝ, (∃! t, 0 < t ∧ f t = 0) →
      0 < Id.run (root f) ∧ f (Id.run (root f)) = 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {α : ℝ} (hα : 0 < α) :
    IsSphereLSQISolution A (WithLp.toLp 2 b) α
      (WithLp.toLp 2 (Id.run (algorithm_6_2_1 pure svd root A b α))) := by
  have hs := hsvd A
  have h112 : ∀ (c : ℝ) (v x : Fin n → ℝ),
      Chapter01.algorithm_1_1_2 (M := Id) pure c v x = pure (x + c • v) := fun c v x => by
    rw [← Chapter01.algorithm_1_1_2_spec]
    rfl
  have h113 : ∀ C : Matrix (Fin m) (Fin m) ℝ,
      Chapter01.algorithm_1_1_3 (M := Id) pure C b 0 = pure (C *ᵥ b) := fun C => by
    rw [← zero_add (C *ᵥ b), ← Chapter01.algorithm_1_1_3_spec]
    rfl
  simp only [algorithm_6_2_1, Id.run_bind, h113, h112, List.idRun_foldlM, Id.run_pure]
  set U := (Id.run (svd A)).1 with hU
  set σ := (Id.run (svd A)).2.1 with hσ
  set V := (Id.run (svd A)).2.2 with hV
  set I := (List.finRange (min m n)).filter (fun i : Fin (min m n) => decide (σ i ≠ 0)) with hI
  have hLS := equation_6_2_3 hs (WithLp.toLp 2 b)
  -- the sums over `I = {i : σ_i ≠ 0}` are the full sums, the dropped terms vanishing
  have hsum : ∀ {β : Type} [AddCommMonoid β] (g : Fin (min m n) → β),
      (∀ i : Fin (min m n), σ i = 0 → g i = 0) →
        ∀ a, I.foldl (fun s i => s + g i) a = a + ∑ i, g i :=
    fun g hg a => by
      rw [List.foldl_add_eq_add_sum_map, hI,
        sum_map_filter_finRange' _ g fun i hi => hg i (not_not.1 hi)]
  have hlist : ∀ g : Fin (min m n) → ℝ, (∀ i : Fin (min m n), σ i = 0 → g i = 0) →
      (I.map g).sum = ∑ i, g i := fun g hg => by
    rw [hI, sum_map_filter_finRange' _ g fun i hi => hg i (not_not.1 hi)]
  rw [hsum _ (fun i hi => by simp [hi]), zero_add]
  have hs2 : ∑ i : Fin (min m n), (Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) / σ i *
      ((Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) / σ i) =
      ‖toEuclideanLin A.pinv (WithLp.toLp 2 b)‖ ^ 2 := by
    rw [hLS.2]
    refine sum_congr rfl fun i _ => ?_
    rw [sq]
    rfl
  rw [hs2]
  split_ifs with hc
  · simp only [Id.run_bind, List.idRun_foldlM, Id.run_pure]
    have hαLS : α < ‖toEuclideanLin A.pinv (WithLp.toLp 2 b)‖ :=
      lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by rwa [sq])
    obtain ⟨hf1, -, hf3⟩ := secular_existsUnique hs hα hαLS
    suffices key : ∀ F : ℝ → ℝ, (∀ t, 0 < t →
        F t = ‖toEuclideanLin (A.tikhonov t) (WithLp.toLp 2 b)‖ ^ 2 - α ^ 2) →
        IsSphereLSQISolution A (WithLp.toLp 2 b) α (WithLp.toLp 2 (List.foldl
          (fun x (i : Fin (min m n)) =>
          x + (σ i * (Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) /
            (σ i * σ i + Id.run (root F))) • fun j => V j (Fin.castLE (min_le_right m n) i))
          0 I)) by
      refine key _ fun t ht => ?_
      rw [hf1 t ht, hlist _ (fun i hi => by simp [hi])]
      rfl
    intro F hF
    have hex : ∃! t, 0 < t ∧ F t = 0 := by
      obtain ⟨t, ⟨ht, hft⟩, hu⟩ := hf3
      refine ⟨t, ⟨ht, by rw [hF t ht, hft]⟩, fun t' ⟨ht', hft'⟩ => hu t' ⟨ht', ?_⟩⟩
      rw [← hF t' ht', hft']
    obtain ⟨hlam, hflam⟩ := hroot F hex
    rw [hsum _ (fun i hi => by simp [hi]), zero_add, WithLp.toLp_sum]
    have hx : ∑ i : Fin (min m n), WithLp.toLp 2
        ((σ i * (Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) / (σ i * σ i + Id.run (root F))) •
          fun j => V j (Fin.castLE (min_le_right m n) i)) =
        toEuclideanLin (A.tikhonov (Id.run (root F))) (WithLp.toLp 2 b) := by
      rw [equation_6_1_14 hs hlam]
      refine sum_congr rfl fun i _ => ?_
      rw [WithLp.toLp_smul, inner_toLp_eq_dotProduct, WithLp.ofLp_toLp, sq]
      rfl
    rw [hx]
    refine isSphereLSQISolution_tikhonov hlam ?_
    have h2 := hF _ hlam
    rw [hflam] at h2
    exact (pow_left_inj₀ (norm_nonneg _) hα.le two_ne_zero).1 (by linarith)
  · simp only [Id.run_bind, List.idRun_foldlM, Id.run_pure]
    rw [hsum _ (fun i hi => by simp [hi]), zero_add, WithLp.toLp_sum]
    have hx : ∑ i : Fin (min m n), WithLp.toLp 2 (((Uᵀ *ᵥ b) (Fin.castLE (min_le_left m n) i) /
        σ i) • fun j => V j (Fin.castLE (min_le_right m n) i)) =
        toEuclideanLin A.pinv (WithLp.toLp 2 b) := by
      rw [hLS.1]
      refine sum_congr rfl fun i _ => ?_
      rw [WithLp.toLp_smul]
      rfl
    rw [hx]
    refine isLSQISolution_pinv A _ ?_
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hα.le two_ne_zero).1 ?_
    rw [sq α]
    exact not_lt.1 hc

/-! ### §6.2.2 More general quadratic constraints -/

/-- **Equation (6.2.6)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m_1 \times n}$ and
$B \in \mathbb{R}^{m_2 \times n}$, and let $U_1^T A X = D_A$, $U_2^T B X = D_B$ be a GSVD of
$(A, B)$ as in (6.1.22)–(6.1.23). Let $b \in \mathbb{R}^{m_1}$, $d \in \mathbb{R}^{m_2}$,
$\alpha \in \mathbb{R}$ and $x \in \mathbb{R}^n$, and let $\tilde b = U_1^T b$,
$\tilde d = U_2^T d$ and $y = X^{-1} x$. Then $x$ solves the LSQI problem (6.2.5), minimize
$\|Ax - b\|_2$ subject to $\|Bx - d\|_2 \le \alpha$, if and only if $y$ solves the problem
$$\text{minimize } \|D_A y - \tilde b\|_2 \text{ subject to } \|D_B y - \tilde d\|_2 \le
  \alpha.$$

**Typo.** The source cites "(6.1.22) and (6.2.23)" for the GSVD. The second reference is
(6.1.23).

The GSVD numbers are named `α'` and `β'` in Lean, because `α` is the radius. -/
theorem equation_6_2_6 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ} {B : Matrix (Fin m₂) (Fin n) ℝ}
    {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ} {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} {α' β' : ℕ → ℝ} (h : IsGSVD A B U₁ U₂ X α' β')
    {b : EuclideanSpace ℝ (Fin m₁)} {d : EuclideanSpace ℝ (Fin m₂)} {α : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    Matrix.IsLSQISolution A b B d α x ↔
      Matrix.IsLSQISolution (rectDiagonal α') (toEuclideanLin U₁ᵀ b)
        (shiftedRectDiagonal ((fromRows A B).rank - m₂) β') (toEuclideanLin U₂ᵀ d) α
        (toEuclideanLin X⁻¹ x) := by
  have e₁ := h.star_mul_mul₁
  have e₂ := h.star_mul_mul₂
  simp only [RCLike.ofReal_real_eq_id, id_eq] at e₁ e₂
  rw [isLSQISolution_iff_of_isGSVD h, e₁, e₂, star_eq_conjTranspose, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, conjTranspose_eq_transpose_of_trivial]

/-- **Equation (6.2.7)** of [golub2013matrix], in the block order of Theorem 6.1.1. Let
$D_A \in \mathbb{R}^{m_1 \times n_1}$ have the diagonal $\alpha_1, \alpha_2, \dots$ and zeros
elsewhere, and let $y \in \mathbb{R}^{n_1}$ and $\tilde b \in \mathbb{R}^{m_1}$. Then
$$\|D_A y - \tilde b\|_2^2 = \sum_{i=1}^{\min(m_1, n_1)} (\alpha_i y_i - \tilde b_i)^2 +
  \sum_{i=n_1+1}^{m_1} \tilde b_i^2.$$
For $m_1 \ge n_1$ the first sum runs to $n_1$, as in the source.

**Reading.** The source prints the equations of §6.2.2 in the block order of the GSVD of the
third edition, which is inconsistent with Theorem 6.1.1. This statement uses the block order of
Theorem 6.1.1.

The matrix $D_A$ is `Matrix.rectDiagonal α`. -/
theorem equation_6_2_7 {m₁ : ℕ} (α : ℕ → ℝ) (y : Fin n → ℝ) (bt : Fin m₁ → ℝ) :
    ‖WithLp.toLp 2 ((rectDiagonal α : Matrix (Fin m₁) (Fin n) ℝ) *ᵥ y - bt)‖ ^ 2 =
      ∑ i : Fin m₁, if h : (i : ℕ) < n then (α i * y ⟨i, h⟩ - bt i) ^ 2 else bt i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, WithLp.ofLp_toLp, Pi.sub_apply]
  split_ifs with hi
  · rw [rectDiagonal_mulVec α y i hi]
  · rw [rectDiagonal_mulVec_of_le α y i (not_lt.1 hi), zero_sub, neg_sq]

/-- The $i$-th entry of $D_B y$, for $D_B$ with the entry $\beta_{j+p}$ at the position
$(j, j + p)$, is $\beta_{i+p} y_{i+p}$ if $i + p < n$ and $0$ otherwise (0-based). -/
private theorem shiftedRectDiagonal_mulVec {m₂ : ℕ} (p : ℕ) (β : ℕ → ℝ) (y : Fin n → ℝ)
    (i : Fin m₂) :
    ((shiftedRectDiagonal p β : Matrix (Fin m₂) (Fin n) ℝ) *ᵥ y) i =
      if h : (i : ℕ) + p < n then β ((i : ℕ) + p) * y ⟨i + p, h⟩ else 0 := by
  rw [mulVec, dotProduct]
  split_ifs with h
  · rw [sum_eq_single ⟨i + p, h⟩]
    · rw [shiftedRectDiagonal_apply, ite_eq_left rfl]
    · intro j _ hj
      rw [shiftedRectDiagonal_apply, ite_eq_right (fun hj' => hj (Fin.ext hj')), zero_mul]
    · exact fun h' => absurd (mem_univ _) h'
  · refine sum_eq_zero fun j _ => ?_
    rw [shiftedRectDiagonal_apply,
      ite_eq_right (fun (hj : (j : ℕ) = i + p) => h (hj ▸ j.isLt)), zero_mul]

/-- **Equation (6.2.8)** of [golub2013matrix], in the block order of Theorem 6.1.1. Let $p \ge 0$,
let $D_B \in \mathbb{R}^{m_2 \times n_1}$ have the entry $\beta_{i+p}$ at the position
$(i, i + p)$ and zeros elsewhere, and let $y \in \mathbb{R}^{n_1}$ and
$\tilde d \in \mathbb{R}^{m_2}$. Then
$$\|D_B y - \tilde d\|_2^2 = \sum_{i \le n_1 - p} (\beta_{i+p} y_{i+p} - \tilde d_i)^2 +
  \sum_{i > n_1 - p} \tilde d_i^2,$$
where $i$ runs over $1, \dots, m_2$.

**Correction.** The source prints "$\sum_{i=1}^{m_2} (\beta_i y_i - \tilde d_i)^2 +
\sum_{i=m_2+1}^{n_1} \tilde d_i^2 \le \alpha^2$". This is the block order of the third edition,
which is inconsistent with Theorem 6.1.1, and its second sum, of $\tilde d_i$ for $i > m_2$, is
meaningless because $\tilde d \in \mathbb{R}^{m_2}$.

The matrix $D_B$ is `Matrix.shiftedRectDiagonal p β`. -/
theorem equation_6_2_8 {m₂ : ℕ} (p : ℕ) (β : ℕ → ℝ) (y : Fin n → ℝ) (dt : Fin m₂ → ℝ) :
    ‖WithLp.toLp 2 ((shiftedRectDiagonal p β : Matrix (Fin m₂) (Fin n) ℝ) *ᵥ y - dt)‖ ^ 2 =
      ∑ i : Fin m₂, if h : (i : ℕ) + p < n then (β ((i : ℕ) + p) * y ⟨i + p, h⟩ - dt i) ^ 2
        else dt i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, WithLp.ofLp_toLp, Pi.sub_apply, shiftedRectDiagonal_mulVec]
  split_ifs
  · rfl
  · rw [zero_sub, neg_sq]

/-! ### §6.2.3 Least squares with equality constraints -/

/-- **§6.2.3** of [golub2013matrix]. "By setting $\alpha = 0$ in (6.2.5) we see that the LSE problem
is a special case of the LSQI problem": let $A \in \mathbb{R}^{m_1 \times n}$,
$B \in \mathbb{R}^{m_2 \times n}$, $b \in \mathbb{R}^{m_1}$, $d \in \mathbb{R}^{m_2}$ and
$x \in \mathbb{R}^n$. Then $x$ solves the LSQI problem with $\alpha = 0$ if and only if it
solves the LSE problem $\min_{Bx = d} \|Ax - b\|_2$. -/
theorem isLSQISolution_zero_iff {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin m₁)}
    {d : EuclideanSpace ℝ (Fin m₂)} {x : EuclideanSpace ℝ (Fin n)} :
    Matrix.IsLSQISolution A b B d 0 x ↔ IsLSESolution A b B d x :=
  Matrix.isLSQISolution_zero_iff

/-- **§6.2.3** of [golub2013matrix], the derivation of Algorithm 6.2.2. Let
$A \in \mathbb{R}^{m_1 \times n_1}$ and $b \in \mathbb{R}^{m_1}$, let
$B \in \mathbb{R}^{m_2 \times n_1}$ have full row rank $m_2 \le n_1$, and let
$d \in \mathbb{R}^{m_2}$. Let $B^T = QR$ be a QR factorization, with $Q = [Q_1\ Q_2]$,
$Q_1 \in \mathbb{R}^{n_1 \times m_2}$ and $R_1 = R(1{:}m_2, 1{:}m_2)$. Let $y = R_1^{-T} d$, so
that $R_1^T y = d$, and let $z \in \mathbb{R}^{n_1 - m_2}$ minimize
$\|A Q_2 z - (b - A Q_1 y)\|_2$. Then
$$x = Q_1 y + Q_2 z = Q \begin{bmatrix} y \\ z \end{bmatrix}$$
solves the LSE problem $\min_{Bx = d} \|Ax - b\|_2$. If moreover $A$ has full column rank, then
the LSE problem has exactly one solution.

In the source: "Let $Q^T B^T = [R; 0]$ be the QR factorization of $B^T$ and set
$AQ = [A_1\ A_2]$, $Q^T x = [y; z]$. … Thus, $y$ is determined from the constraint equation
$R^T y = d$ and the vector $z$ is obtained by solving the unconstrained LS problem
$\min \|A_2 z - (b - A_1 y)\|_2$."

The block $Q_1$ is `Matrix.firstColumns Q`, $Q_2$ is the remaining columns, and $R_1$ is
`Matrix.firstRows R`. Full row rank of $B$ is `LinearIndependent ℝ B`. -/
theorem isLSESolution_qr {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {b : EuclideanSpace ℝ (Fin m₁)} {B : Matrix (Fin m₂) (Fin n) ℝ}
    {d : EuclideanSpace ℝ (Fin m₂)} (hpn : m₂ ≤ n) (hB : LinearIndependent ℝ B)
    {Q : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin n) (Fin m₂) ℝ} (hQR : IsQR Bᵀ Q R)
    {z : EuclideanSpace ℝ (Fin (n - m₂))}
    (hz : IsLeastSquaresSolution
      (A * Q.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂))
      (b - toEuclideanLin (A * Q.firstColumns hpn) (toEuclideanLin ((R.firstRows hpn)ᵀ)⁻¹ d)) z) :
    IsLSESolution A b B d
        (toEuclideanLin (Q.firstColumns hpn) (toEuclideanLin ((R.firstRows hpn)ᵀ)⁻¹ d) +
          toEuclideanLin (Q.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂))
            z) ∧
      (LinearIndependent ℝ Aᵀ → ∃! x, IsLSESolution A b B d x) := by
  have hQR' : IsQR Bᴴ Q R := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hL : Q.lastColumns (Nat.sub_le n m₂) =
      Q.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂) :=
    lastColumns_eq_submatrix Q _ fun j => by simp; omega
  have hsol := isLSESolution_of_isQR hpn hB hQR' (by
    rw [hL]; rwa [conjTranspose_eq_transpose_of_trivial])
  rw [conjTranspose_eq_transpose_of_trivial, hL] at hsol
  refine ⟨hsol, fun hA => ⟨_, hsol, fun x' hx' => hsol.eq_of_ker_inf_ker_eq_bot hx' ?_⟩⟩
  have hker : LinearMap.ker A.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.2 (mulVec_injective_of_linearIndependent_transpose hA)
  rw [hker, bot_inf_eq]

/-- **§6.2.3** of [golub2013matrix]. Let $A \in \mathbb{R}^{m_1 \times n}$,
$B \in \mathbb{R}^{m_2 \times n}$, $b \in \mathbb{R}^{m_1}$ and $d \in \operatorname{ran}(B)$.
Then the LSE problem $\min_{Bx = d} \|Ax - b\|_2$ has a solution, and if $x$ is a solution and
$z \in \operatorname{null}(A) \cap \operatorname{null}(B)$, then $x + z$ is also a solution.
Hence the LSE solution is not unique if $\operatorname{null}(A) \cap \operatorname{null}(B) \neq
\{0\}$.

**Reading.** The sentence of the source about the non-uniqueness of the LSE solution when
$\operatorname{null}(A) \cap \operatorname{null}(B) \neq \{0\}$ and
$d \in \operatorname{ran}(B)$ is garbled in print. The statement fixes this reading of it. -/
theorem isLSESolution_not_unique {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {b : EuclideanSpace ℝ (Fin m₁)} {B : Matrix (Fin m₂) (Fin n) ℝ}
    {d : EuclideanSpace ℝ (Fin m₂)} (hd : d ∈ LinearMap.range (toEuclideanLin B)) :
    (∃ x, IsLSESolution A b B d x) ∧
      ∀ x, IsLSESolution A b B d x →
        ∀ z ∈ LinearMap.ker (toEuclideanLin A) ⊓ LinearMap.ker (toEuclideanLin B),
          IsLSESolution A b B d (x + z) :=
  ⟨(existsUnique_isLSESolution hd).1, fun _ hx _ hz => hx.add_of_mem hz⟩

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.2.2** of [golub2013matrix]. "Suppose $A \in \mathbb{R}^{m_1 \times n_1}$,
$B \in \mathbb{R}^{m_2 \times n_1}$, $b \in \mathbb{R}^{m_1}$, and $d \in \mathbb{R}^{m_2}$. If
$\operatorname{rank}(A) = n_1$ and $\operatorname{rank}(B) = m_2 < n_1$, then the following
algorithm minimizes $\|Ax - b\|_2$ subject to the constraint $Bx = d$":
```
Compute the QR factorization Bᵀ = QR.
Solve R(1:m₂, 1:m₂)ᵀ · y = d for y.
A = AQ
Find z so ‖A(:, m₂+1:n₁) z − (b − A(:, 1:m₂) · y)‖₂ is minimized.
x = Q(:, 1:m₂) · y + Q(:, m₂+1:n₁) · z
```
The program assumes $m_2 \le n_1$.

In Lean, $m_1$ is `m` and $n_1$ is `n`. "Compute the QR factorization" is Householder QR
(Algorithm 5.2.1), with the explicit factor $Q$ formed by forward accumulation of the reflectors
that it returned. The triangular solve is forward substitution (Algorithm 3.1.1) on
$R(1{:}m_2, 1{:}m_2)^T$, and the product $AQ$ is Algorithm 1.1.5. The residual
$b - A(:, 1{:}m_2) y$ and the two products that form $x$ are gaxpys (Algorithm 1.1.3), and the
negation is exact. "Find $z$" names no method, so it is the parameter `ls`. -/
noncomputable def algorithm_6_2_2 {m₂ : ℕ} (hpn : m₂ ≤ n)
    (ls : Matrix (Fin m) (Fin (n - m₂)) ℝ → (Fin m → ℝ) → M (Fin (n - m₂) → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m₂) (Fin n) ℝ) (b : Fin m → ℝ)
    (d : Fin m₂ → ℝ) : M (Fin n → ℝ) := do
  let Aβ ← Chapter05.algorithm_5_2_1 rnd Bᵀ
  let Q ← Chapter05.forwardAccumulation rnd (Chapter05.storedReflectors Aβ.1 Aβ.2)
  let R := Chapter05.upperPart Aβ.1
  let y ← Chapter03.algorithm_3_1_1 rnd (R.firstRows hpn)ᵀ d
  let AQ ← Chapter01.algorithm_1_1_5 rnd A Q 0
  let c ← Chapter01.algorithm_1_1_3 rnd (-AQ.firstColumns hpn) y b
  let z ← ls (AQ.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂)) c
  let x₁ ← Chapter01.algorithm_1_1_3 rnd (Q.firstColumns hpn) y 0
  Chapter01.algorithm_1_1_3 rnd (Q.submatrix id (Fin.cast (Nat.add_sub_cancel' hpn) ∘
    Fin.natAdd m₂)) z x₁

end Programs

/-- **Algorithm 6.2.2** of [golub2013matrix], correctness in exact arithmetic. Let
$A \in \mathbb{R}^{m_1 \times n_1}$ have full column rank $n_1$, let
$B \in \mathbb{R}^{m_2 \times n_1}$ have full row rank $m_2$ with $m_2 \le n_1$, and let
$b \in \mathbb{R}^{m_1}$ and $d \in \mathbb{R}^{m_2}$. Assume that the subroutine `ls` returns a
least-squares solution for every matrix and right-hand side. Then the output $x$ of Algorithm
6.2.2 in exact arithmetic solves the LSE problem $\min_{Bx = d} \|Ax - b\|_2$, and every
solution of this problem is equal to $x$.

**Generalization.** The source assumes $m_2 < n_1$. The statement also allows $m_2 = n_1$.

Householder QR of $B^T$ with the returned $\beta$ is a QR factorization with no condition
(`GolubVanLoan.Chapter05.algorithm_5_2_1_spec`,
`GolubVanLoan.Chapter05.forwardAccumulation_spec`). The block $R(1{:}m_2, 1{:}m_2)$ has a
nonzero diagonal because $B^T$ has full column rank, and the rest is
`GolubVanLoan.Chapter06.isLSESolution_qr`. -/
theorem algorithm_6_2_2_spec {m₂ : ℕ} (hpn : m₂ ≤ n)
    (ls : Matrix (Fin m) (Fin (n - m₂)) ℝ → (Fin m → ℝ) → Id (Fin (n - m₂) → ℝ))
    (hls : ∀ C c, IsLeastSquaresSolution C (WithLp.toLp 2 c) (WithLp.toLp 2 (Id.run (ls C c))))
    {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin m₂) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (hB : LinearIndependent ℝ B) (b : Fin m → ℝ) (d : Fin m₂ → ℝ) :
    IsLSESolution A (WithLp.toLp 2 b) B (WithLp.toLp 2 d)
        (WithLp.toLp 2 (Id.run (algorithm_6_2_2 pure hpn ls A B b d))) ∧
      ∀ x, IsLSESolution A (WithLp.toLp 2 b) B (WithLp.toLp 2 d) x →
        x = WithLp.toLp 2 (Id.run (algorithm_6_2_2 pure hpn ls A B b d)) := by
  have h113 : ∀ {r s : ℕ} (C : Matrix (Fin r) (Fin s) ℝ) (v : Fin s → ℝ) (w : Fin r → ℝ),
      Chapter01.algorithm_1_1_3 (M := Id) pure C v w = pure (w + C *ᵥ v) := fun C v w => by
    rw [← Chapter01.algorithm_1_1_3_spec]
    rfl
  have h115 : ∀ {r s t : ℕ} (C : Matrix (Fin r) (Fin s) ℝ) (D : Matrix (Fin s) (Fin t) ℝ),
      Chapter01.algorithm_1_1_5 (M := Id) pure C D 0 = pure (C * D) := fun C D => by
    rw [← zero_add (C * D), ← Chapter01.algorithm_1_1_5_spec]
    rfl
  have hfa : ∀ data : List ((Fin n → ℝ) × ℝ),
      Chapter05.forwardAccumulation (M := Id) pure data =
        pure (Chapter05.householderProduct data) := fun data => by
    rw [← Chapter05.forwardAccumulation_spec]
    rfl
  obtain ⟨hqr, -⟩ := Chapter05.algorithm_5_2_1_spec hpn Bᵀ
  set Aβ := Id.run (Chapter05.algorithm_5_2_1 pure Bᵀ) with hAβ
  set Q := Chapter05.factoredQ Aβ.2 Aβ.1 with hQ
  set R := Chapter05.upperPart Aβ.1 with hR
  set e : Fin (n - m₂) → Fin n := Fin.cast (Nat.add_sub_cancel' hpn) ∘ Fin.natAdd m₂ with he
  have hBT : LinearIndependent ℝ (Bᵀ)ᵀ := by rwa [transpose_transpose]
  -- the triangular solve
  set R₁ := R.firstRows hpn with hR₁
  have hL : R₁ᵀ.IsLowerTriangular := (hqr.isUpperTriangular_firstRows hpn).transpose
  have hdiag : ∀ i, R₁ᵀ i i ≠ 0 := fun i =>
    hqr.firstRows_diag_ne_zero_of_linearIndependent hpn hBT i
  set y := Id.run (Chapter03.algorithm_3_1_1 pure R₁ᵀ d) with hy
  have hRy : R₁ᵀ *ᵥ y = d := Chapter03.algorithm_3_1_1_spec hL hdiag d
  have hR₁u : IsUnit R₁ᵀ :=
    (isUnit_transpose _).2 (hqr.isUnit_firstRows_of_linearIndependent hpn hBT)
  have hy' : y = R₁ᵀ⁻¹ *ᵥ d := by
    rw [← hRy, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hR₁u), one_mulVec]
  have hAQ₁ : (A * Q).firstColumns hpn = A * Q.firstColumns hpn := by
    ext i j
    simp [firstColumns, Matrix.mul_apply]
  have hAQ₂ : (A * Q).submatrix id e = A * Q.submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  set z := Id.run (ls (A * Q.submatrix id e) (b + -(A * Q.firstColumns hpn) *ᵥ y)) with hz
  have hzLS := hls (A * Q.submatrix id e) (b + -(A * Q.firstColumns hpn) *ᵥ y)
  have hout : Id.run (algorithm_6_2_2 pure hpn ls A B b d) =
      0 + Q.firstColumns hpn *ᵥ y + Q.submatrix id e *ᵥ z := by
    simp only [algorithm_6_2_2, Id.run_bind, hfa, h115, h113, Id.run_pure]
    rw [← hAβ, ← Chapter05.factoredQ, ← hQ, ← hR, ← hR₁, ← hy, hAQ₁, hAQ₂, ← hz]
  have hsol := (isLSESolution_qr (b := WithLp.toLp 2 b) (d := WithLp.toLp 2 d) hpn hB
    (Q := Q) (R := R) (by rwa [← conjTranspose_eq_transpose_of_trivial]) (z := WithLp.toLp 2 z)
    (by
      convert hzLS using 2
      rw [hy']
      change b - (A * Q.firstColumns hpn) *ᵥ (R₁ᵀ⁻¹ *ᵥ d) =
        b + -(A * Q.firstColumns hpn) *ᵥ (R₁ᵀ⁻¹ *ᵥ d)
      rw [neg_mulVec, sub_eq_add_neg]))
  have hx : WithLp.toLp 2 (Id.run (algorithm_6_2_2 pure hpn ls A B b d)) =
      toEuclideanLin (Q.firstColumns hpn) (toEuclideanLin (R₁ᵀ)⁻¹ (WithLp.toLp 2 d)) +
        toEuclideanLin (Q.submatrix id e) (WithLp.toLp 2 z) := by
    rw [hout, zero_add, hy']
    rfl
  rw [hx]
  refine ⟨hsol.1, fun x hx' => ?_⟩
  obtain ⟨x₀, -, hu⟩ := hsol.2 hA
  rw [hu x hx', hu _ hsol.1]

/-! ### §6.2.4 LSE solution using the augmented system -/

/-- **Equation (6.2.10)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m_1 \times n}$,
$B \in \mathbb{R}^{m_2 \times n}$, $x \in \mathbb{R}^n$, $r, b \in \mathbb{R}^{m_1}$ and
$\lambda, d \in \mathbb{R}^{m_2}$. If $(x, r, \lambda)$ solves "the symmetric indefinite linear
system"
$$\begin{bmatrix} 0 & A^T & B^T \\ A & I & 0 \\ B & 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ r
  \\ \lambda \end{bmatrix} = \begin{bmatrix} 0 \\ b \\ d \end{bmatrix},$$
then $x$ solves the LSE problem $\min_{Bx = d} \|Ax - b\|_2$.

The matrix is `Matrix.augmentedLSE A B`, indexed by `Fin n ⊕ (Fin m₁ ⊕ Fin m₂)`, and the vector
$\lambda$ of multipliers is `l`. -/
theorem equation_6_2_10 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {x : Fin n → ℝ} {r b : Fin m₁ → ℝ} {l d : Fin m₂ → ℝ}
    (h : augmentedLSE A B *ᵥ Sum.elim x (Sum.elim r l) =
      Sum.elim (0 : Fin n → ℝ) (Sum.elim b d)) :
    IsLSESolution A (WithLp.toLp 2 b) B (WithLp.toLp 2 d) (WithLp.toLp 2 x) :=
  isLSESolution_of_augmented h

/-- **§6.2.4** of [golub2013matrix]. "This system is nonsingular if both $A$ and $B$ have full
rank": if $A \in \mathbb{R}^{m_1 \times n}$ has full column rank and
$B \in \mathbb{R}^{m_2 \times n}$ has full row rank, then the matrix of (6.2.10) is nonsingular. -/
theorem equation_6_2_10_isUnit {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ) (hB : LinearIndependent ℝ B) :
    IsUnit (augmentedLSE A B) :=
  isUnit_augmentedLSE hA hB

/-! ### §6.2.5 LSE solution using the GSVD -/

/-- **Equation (6.2.11)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m_1 \times n}$ and
$B \in \mathbb{R}^{m_2 \times n}$, and let $U_1^T A X = D_A$, $U_2^T B X = D_B$ be a GSVD of
$(A, B)$ as in (6.1.22)–(6.1.23). Let $b \in \mathbb{R}^{m_1}$, $d \in \mathbb{R}^{m_2}$ and
$x \in \mathbb{R}^n$, and let $\tilde b = U_1^T b$, $\tilde d = U_2^T d$ and $y = X^{-1} x$.
Then $x$ solves the LSE problem $\min_{Bx = d} \|Ax - b\|_2$ if and only if $y$ solves
$$\min_{D_B y = \tilde d} \|D_A y - \tilde b\|_2.$$
-/
theorem equation_6_2_11 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ} {X : Matrix (Fin n) (Fin n) ℝ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U₁ U₂ X α β) {b : EuclideanSpace ℝ (Fin m₁)} {d : EuclideanSpace ℝ (Fin m₂)}
    {x : EuclideanSpace ℝ (Fin n)} :
    IsLSESolution A b B d x ↔
      IsLSESolution (rectDiagonal α) (toEuclideanLin U₁ᵀ b)
        (shiftedRectDiagonal ((fromRows A B).rank - m₂) β) (toEuclideanLin U₂ᵀ d)
        (toEuclideanLin X⁻¹ x) := by
  rw [← Matrix.isLSQISolution_zero_iff, ← Matrix.isLSQISolution_zero_iff]
  exact equation_6_2_6 h

/-- **Equation (6.2.12)** of [golub2013matrix], in the block order of Theorem 6.1.1. Let
$A \in \mathbb{R}^{m_1 \times n_1}$ with $m_1 \ge n_1$, let $B \in \mathbb{R}^{m_2 \times n_1}$
have full row rank $m_2$, and assume that $\operatorname{null}(A) \cap \operatorname{null}(B) =
\{0\}$. Let $U_1^T A X = D_A$, $U_2^T B X = D_B$ be a GSVD of $(A, B)$, with columns
$x_1, \dots, x_{n_1}$ of $X$, let $b \in \mathbb{R}^{m_1}$ and $d \in \mathbb{R}^{m_2}$, and let
$\tilde b = U_1^T b$, $\tilde d = U_2^T d$ and $p = n_1 - m_2$. Then
$$x = \sum_{i=1}^{p} \tilde b_i x_i + \sum_{i=p+1}^{n_1} \frac{\tilde d_{i-p}}{\beta_i} x_i$$
solves the LSE problem $\min_{Bx = d} \|Ax - b\|_2$. Under these hypotheses
$\operatorname{rank}([A; B]) = n_1$, so $p$ is the $p$ of Theorem 6.1.1 and
$(\alpha_i, \beta_i) = (1, 0)$ for $i \le p$.

**Correction.** The source states that "$x = \sum (\tilde d_i / \beta_i) x_i + \sum (\tilde b_i
/ \alpha_i) x_i$ solves the LSE problem" in the block order of the GSVD of the third edition,
which is inconsistent with Theorem 6.1.1. The formula here uses the block order of Theorem
6.1.1.

The sums are 0-based in Lean: the first is over $i < n_1 - m_2$, and the second is over
$i \ge n_1 - m_2$ with $\tilde d_{i - (n_1 - m_2)}$. -/
theorem equation_6_2_12 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ} {X : Matrix (Fin n) (Fin n) ℝ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) (hB : LinearIndependent ℝ B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace ℝ (Fin m₁)) (d : EuclideanSpace ℝ (Fin m₂)) :
    IsLSESolution A b B d (WithLp.toLp 2 (∑ i : Fin n,
      (if hi : (i : ℕ) < n - m₂ then (U₁ᵀ *ᵥ WithLp.ofLp b) ⟨i, lt_of_lt_of_le i.isLt hnm⟩
        else (U₂ᵀ *ᵥ WithLp.ofLp d) ⟨(i : ℕ) - (n - m₂), by have := i.isLt; omega⟩ / β i) •
        X.col i)) := by
  have e := isLSESolution_sum_of_isGSVD h hnm hB hAB b d
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at e
  exact e

/-! ### §6.2.6 LSE solution using weights -/

/-- **Equation (6.2.13)** of [golub2013matrix], the method of weighting. Let
$A \in \mathbb{R}^{m_1 \times n}$, $B \in \mathbb{R}^{m_2 \times n}$, $b \in \mathbb{R}^{m_1}$,
$d \in \mathbb{R}^{m_2}$, $\lambda \ge 0$ and $x \in \mathbb{R}^n$. Then
$$\left\| \begin{bmatrix} A \\ \sqrt{\lambda} B \end{bmatrix} x - \begin{bmatrix} b \\
  \sqrt{\lambda} d \end{bmatrix} \right\|_2^2 = \|Ax - b\|_2^2 + \lambda \|Bx - d\|_2^2,$$
so $x$ is a least-squares solution of the stacked problem if and only if it minimizes
$\|Ax - b\|_2^2 + \lambda \|Bx - d\|_2^2$. If $\lambda > 0$ and $\operatorname{null}(A) \cap
\operatorname{null}(B) = \{0\}$, then $A^T A + \lambda B^T B$ is positive definite.

The solution $x(\lambda)$ of the normal equations $(A^T A + \lambda B^T B) x = A^T b + \lambda
B^T d$ is `Matrix.penaltyLSE`. -/
theorem equation_6_2_13 {m₁ m₂ : ℕ} (A : Matrix (Fin m₁) (Fin n) ℝ) (B : Matrix (Fin m₂) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m₁)) (d : EuclideanSpace ℝ (Fin m₂)) {μ : ℝ} (hμ : 0 ≤ μ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (‖toEuclideanLin (fromRows A (Real.sqrt μ • B)) x -
        WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) (Real.sqrt μ • WithLp.ofLp d))‖ ^ 2 =
      ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x - d‖ ^ 2) ∧
    (IsLeastSquaresSolution (fromRows A (Real.sqrt μ • B))
        (WithLp.toLp 2 (Sum.elim (WithLp.ofLp b) (Real.sqrt μ • WithLp.ofLp d))) x ↔
      ∀ y, ‖toEuclideanLin A x - b‖ ^ 2 + μ * ‖toEuclideanLin B x - d‖ ^ 2 ≤
        ‖toEuclideanLin A y - b‖ ^ 2 + μ * ‖toEuclideanLin B y - d‖ ^ 2) ∧
    (0 < μ → LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥ →
      (Aᵀ * A + μ • (Bᵀ * B)).PosDef) := by
  refine ⟨?_, ?_, fun hμ' hAB => ?_⟩
  · rw [norm_fromRows_sub_sq, WithLp.toLp_ofLp]
    have e : toEuclideanLin (Real.sqrt μ • B) x - WithLp.toLp 2 (Real.sqrt μ • WithLp.ofLp d) =
        Real.sqrt μ • (toEuclideanLin B x - d) := by
      rw [toEuclideanLin_smul_apply, WithLp.toLp_smul, WithLp.toLp_ofLp, smul_sub]
    rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hμ]
  · have h := isLeastSquaresSolution_fromRows_iff A B (WithLp.ofLp b) (WithLp.ofLp d) hμ x
    simp only [WithLp.toLp_ofLp, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h
  · have h := (posDef_gram_add_smul_gram_iff A B hμ').2 hAB
    simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h

/-- **Equation (6.2.14)** of [golub2013matrix], corrected, in the block order of Theorem 6.1.1. Let
$A$, $B$, the GSVD, $b$, $d$ and $p = n_1 - m_2$ be as in
`GolubVanLoan.Chapter06.equation_6_2_12`, with the same hypotheses, and let $x$ be the LSE
solution given there. Let $\lambda > 0$ and $x(\lambda) = (A^T A + \lambda B^T B)^{-1} (A^T b +
\lambda B^T d)$. Then
$$x(\lambda) - x = \sum_{i=p+1}^{n_1} \frac{\alpha_i (\beta_i \tilde b_i - \alpha_i \tilde
  d_{i-p})}{\beta_i (\alpha_i^2 + \lambda \beta_i^2)} x_i.$$

**Correction.** The source prints "$x(\lambda) - x = \sum_{i=1}^{p} (\alpha_i /
\beta_i)((\beta_i u_i^T b - \alpha_i v_i^T d) / (\alpha_i^2 + \lambda^2 \beta_i^2)) x_i$" in the
block order of the third edition. It has $\lambda^2$ for $\lambda$, $u_i^T b$ and $v_i^T d$ for
$\tilde b_i$ and $\tilde d_i$, and the range $1{:}p$.

The vector $x(\lambda)$ is `Matrix.penaltyLSE A B b d μ`. -/
theorem equation_6_2_14 {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ}
    {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ} {X : Matrix (Fin n) (Fin n) ℝ} {α β : ℕ → ℝ}
    (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) (hB : LinearIndependent ℝ B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (b : EuclideanSpace ℝ (Fin m₁)) (d : EuclideanSpace ℝ (Fin m₂)) {μ : ℝ} (hμ : 0 < μ) :
    penaltyLSE A B b d μ - WithLp.toLp 2 (∑ i : Fin n,
      (if hi : (i : ℕ) < n - m₂ then (U₁ᵀ *ᵥ WithLp.ofLp b) ⟨i, lt_of_lt_of_le i.isLt hnm⟩
        else (U₂ᵀ *ᵥ WithLp.ofLp d) ⟨(i : ℕ) - (n - m₂), by have := i.isLt; omega⟩ / β i) •
        X.col i) =
      WithLp.toLp 2 (∑ i : Fin n,
        (if hi : (i : ℕ) < n - m₂ then 0
          else α i * (β i * (U₁ᵀ *ᵥ WithLp.ofLp b) ⟨i, lt_of_lt_of_le i.isLt hnm⟩ -
              α i * (U₂ᵀ *ᵥ WithLp.ofLp d) ⟨(i : ℕ) - (n - m₂), by have := i.isLt; omega⟩) /
            (β i * (α i ^ 2 + μ * β i ^ 2))) • X.col i) := by
  have e := penaltyLSE_sub_eq_sum_of_isGSVD h hnm hB hAB b d hμ
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at e
  exact e

/-- **§6.2.6** of [golub2013matrix]. Let $A \in \mathbb{R}^{m_1 \times n_1}$ with $m_1 \ge n_1$, let
$B \in \mathbb{R}^{m_2 \times n_1}$ have full row rank, assume that $\operatorname{null}(A) \cap
\operatorname{null}(B) = \{0\}$, let $b \in \mathbb{R}^{m_1}$ and $d \in \mathbb{R}^{m_2}$, and
let $x$ solve the LSE problem $\min_{Bx = d} \|Ax - b\|_2$. Then "$x(\lambda) \to x$ as
$\lambda \to \infty$", where $x(\lambda) = (A^T A + \lambda B^T B)^{-1} (A^T b + \lambda B^T
d)$.

The vector $x(\lambda)$ is `Matrix.penaltyLSE A B b d μ`. -/
theorem tendsto_penaltyLSE_solution {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} (hnm : n ≤ m₁) (hB : LinearIndependent ℝ B)
    (hAB : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {b : EuclideanSpace ℝ (Fin m₁)} {d : EuclideanSpace ℝ (Fin m₂)} {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsLSESolution A b B d x) : Tendsto (penaltyLSE A B b d) atTop (𝓝 x) :=
  Matrix.tendsto_penaltyLSE hnm hB hAB hx

end GolubVanLoan.Chapter06
