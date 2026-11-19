/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.GolubVanLoan.Chapter02.Section02

/-!
# Golub and Van Loan, Section 2.3: Matrix norms

This module formalizes §2.3 of [golub2013matrix] on norms of matrices
$A \in \mathbb{R}^{m \times n}$. A matrix norm is a vector norm on $\mathbb{R}^{m \times n}$. The
two main examples are the Frobenius norm $\|A\|_F = (\sum_{i,j} |a_{ij}|^2)^{1/2}$ (2.3.1) and the
$p$-norms $\|A\|_p = \sup_{x \neq 0} \|Ax\|_p / \|x\|_p$ (2.3.2), and more generally the subordinate
norms $\|A\|_{\alpha,\beta}$ of (2.3.5). The module proves that the $p$-norms are consistent
(2.3.3), gives the counterexample $\|A\|_\Delta = \max |a_{ij}|$ to consistency, proves the
comparisons (2.3.7)–(2.3.13) between the norms, and shows that convergence of a matrix sequence does
not depend on the norm. It then characterizes $\|A\|_2$ through $A^T A$ (Theorem 2.3.1, Corollary
2.3.2), proves the Neumann series bound for $(I - F)^{-1}$ (Lemma 2.3.3) and the perturbation bound
for the inverse (Theorem 2.3.4), and proves the orthogonal invariance (2.3.14)–(2.3.15) of the
Frobenius norm and the 2-norm.

The proofs specialize the backbone modules `Numlib.Analysis.Matrix.OperatorNorm` (the comparison
constants and the Neumann series), `Numlib.Analysis.Normed.Ring.Inverse` (Theorem 2.3.4 in a normed
ring) and `Numlib.LinearAlgebra.Matrix.SVD` (the singular values behind the 2-norm).

## Main definitions

* §2.3.1, `GolubVanLoan.Chapter02.IsMatrixNorm`: a function on $\mathbb{R}^{m \times n}$ is a matrix
  norm if it satisfies the three vector norm axioms.

## Main results

* Equation (2.3.1), `GolubVanLoan.Chapter02.equation_2_3_1`: the Frobenius norm is
  $\|A\|_F = (\sum_{i,j} |a_{ij}|^2)^{1/2}$, and it is a matrix norm.
* Equation (2.3.2), `GolubVanLoan.Chapter02.equation_2_3_2`: $\|A\|_p$ is the supremum of
  $\|Ax\|_p / \|x\|_p$, it is attained on the unit sphere, and it is a matrix norm.
* Equation (2.3.3), `GolubVanLoan.Chapter02.equation_2_3_3`: $\|AB\|_p \le \|A\|_p \|B\|_p$.
* §2.3.1, `GolubVanLoan.Chapter02.maxAbs_not_consistent`: the norm $\|A\|_\Delta = \max |a_{ij}|$ is
  not consistent.
* §2.3.1, `GolubVanLoan.Chapter02.norm_mulVec_le`: $\|Ax\|_p \le \|A\|_p \|x\|_p$.
* Equation (2.3.5), `GolubVanLoan.Chapter02.equation_2_3_5`: the subordinate norm
  $\|A\|_{\alpha,\beta}$ satisfies $\|Ax\|_\beta \le \|A\|_{\alpha,\beta} \|x\|_\alpha$.
* Equation (2.3.6), `GolubVanLoan.Chapter02.equation_2_3_6`: the supremum that defines
  $\|A\|_{\alpha,\beta}$ is attained.
* Equations (2.3.7)–(2.3.12), `GolubVanLoan.Chapter02.equation_2_3_7` to
  `GolubVanLoan.Chapter02.equation_2_3_12`: the comparisons between $\|A\|_2$, $\|A\|_F$,
  $\max |a_{ij}|$, $\|A\|_1$ and $\|A\|_\infty$, and the column sum and row sum formulas for
  $\|A\|_1$ and $\|A\|_\infty$.
* Equation (2.3.13), `GolubVanLoan.Chapter02.equation_2_3_13`: a submatrix has a $p$-norm at most
  $\|A\|_p$.
* §2.3.2, `GolubVanLoan.Chapter02.tendsto_iff_of_isMatrixNorm`: a matrix sequence converges if and
  only if it converges in any one matrix norm.
* Theorem 2.3.1, `GolubVanLoan.Chapter02.theorem_2_3_1`: there is a unit vector $z$ with
  $A^T A z = \mu^2 z$, $\mu = \|A\|_2$.
* §2.3.3, `GolubVanLoan.Chapter02.l2_opNorm_eq_sqrt_lambdaMax`:
  $\|A\|_2 = \sqrt{\lambda_{\max}(A^T A)}$.
* Corollary 2.3.2, `GolubVanLoan.Chapter02.corollary_2_3_2`:
  $\|A\|_2 \le \sqrt{\|A\|_1 \|A\|_\infty}$.
* Lemma 2.3.3, `GolubVanLoan.Chapter02.lemma_2_3_3`: if $\|F\|_p < 1$, then $I - F$ is nonsingular,
  $(I - F)^{-1} = \sum_k F^k$ and $\|(I - F)^{-1}\|_p \le 1/(1 - \|F\|_p)$.
* §2.3.4, `GolubVanLoan.Chapter02.norm_inv_one_sub_sub_one_le`: $\|(I - F)^{-1} - I\|_p \le \|F\|_p
  / (1 - \|F\|_p)$.
* Theorem 2.3.4, `GolubVanLoan.Chapter02.theorem_2_3_4`: the perturbation bound $\|(A + E)^{-1} -
  A^{-1}\|_p \le \|E\|_p \|A^{-1}\|_p^2 / (1 - r)$.
* Equations (2.3.14)–(2.3.15), `GolubVanLoan.Chapter02.equation_2_3_14` and
  `GolubVanLoan.Chapter02.equation_2_3_15`: $\|QAZ\|_F = \|A\|_F$ and $\|QAZ\|_2 = \|A\|_2$ for
  orthogonal $Q$ and $Z$.

## Proof outline

The proofs that the source leaves as exercises (Problems P2.3.1–P2.3.6) are the backbone lemmas that
the declarations cite. Theorem 2.3.1 is proved through the right singular vector of the largest
singular value, not through the gradient computation of the source. Theorem 2.3.4 is proved through
the factorization $A + E = A(I + A^{-1}E)$. The proof in the source factors $A + E = (I + F)A$ with
$F = -EA^{-1}$ and claims $\|F\|_p = r = \|A^{-1}E\|_p$, which is false in general; the statement is
not affected.

## Conventions

* A matrix norm, `GolubVanLoan.Chapter02.IsMatrixNorm`, is the vector norm predicate
  `GolubVanLoan.Chapter02.IsVectorNorm` of §2.2 on $\mathbb{R}^{m \times n}$, as in the source.
* The matrix $p$-norm $\|A\|_p$ is `Matrix.lpOpNorm p A` for `p : ℝ≥0∞` with `[Fact (1 ≤ p)]`, which
  is the condition $1 \le p \le \infty$ of the source. It is defined for rectangular matrices.
* The subordinate norm $\|A\|_{\alpha,\beta}$ of (2.3.5) is `Matrix.inducedNorm β α A` for seminorms
  $\alpha$ and $\beta$ with $\alpha$ definite. A vector norm is such a seminorm by
  `GolubVanLoan.Chapter02.IsVectorNorm.exists_seminorm`.
* The Frobenius norm is the scoped norm `Matrix.Norms.Frobenius` of Mathlib, and $\|\cdot\|_\Delta$
  is the scoped norm `Matrix.Norms.Elementwise`. Each is opened only in the sections that use it.
* The 1-based block $A(i_1{:}i_2, j_1{:}j_2)$ of the source is the 0-based `A.submatrix` on
  consecutive indices.

## Deviations from the source

* **Equation (2.3.2), attainment** (reading). The unit-vector conclusion requires positive
  input dimension. See `GolubVanLoan.Chapter02.equation_2_3_2`.
* **Equations (2.3.5)–(2.3.6)** (generalization and reading). The target need only carry a
  seminorm. Attainment requires a nonempty unit sphere. See
  `GolubVanLoan.Chapter02.equation_2_3_5` and `GolubVanLoan.Chapter02.equation_2_3_6`.
* **Equations (2.3.8)–(2.3.12)** (reading). Empty maxima and division by a zero square root
  evaluate to zero. See `GolubVanLoan.Chapter02.equation_2_3_8`,
  `GolubVanLoan.Chapter02.equation_2_3_9`, `GolubVanLoan.Chapter02.equation_2_3_10`,
  `GolubVanLoan.Chapter02.equation_2_3_11` and `GolubVanLoan.Chapter02.equation_2_3_12`.
* **Theorem 2.3.1 and its spectral formula** (reading). The source has no column-count
  hypothesis. A unit vector and a largest eigenvalue require positive column count. See
  `GolubVanLoan.Chapter02.theorem_2_3_1` and `GolubVanLoan.Chapter02.l2_opNorm_eq_sqrt_lambdaMax`.
* **Proof of Theorem 2.3.4** (correction). The proof uses right factorization to control the
  perturbation by the stated $\|A^{-1}E\|_p$. See `GolubVanLoan.Chapter02.theorem_2_3_4`.

## Not formalized

* **Equation (2.3.4)**, the definition of a consistent family of norms. The source uses it only in
  prose.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal

namespace GolubVanLoan.Chapter02

variable {m n : ℕ}

/-! ### §2.3.1 Definitions -/

/-- **Section 2.3.1** of [golub2013matrix], definition of a matrix norm. A function
$f : \mathbb{R}^{m \times n} \to \mathbb{R}$ is a **matrix norm** if it satisfies the three
vector norm properties on $\mathbb{R}^{m \times n}$: $f(A) \ge 0$, with $f(A) = 0$ if and only
if $A = 0$; $f(A + B) \le f(A) + f(B)$; and $f(\alpha A) = |\alpha| f(A)$ for
$\alpha \in \mathbb{R}$.

The definition is `GolubVanLoan.Chapter02.IsVectorNorm` on the vector space
`Matrix (Fin m) (Fin n) ℝ`. -/
def IsMatrixNorm (f : Matrix (Fin m) (Fin n) ℝ → ℝ) : Prop :=
  IsVectorNorm f

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Equation (2.3.1)** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$, the **Frobenius
norm** is
$$\|A\|_F = \Big( \sum_{i=1}^m \sum_{j=1}^n |a_{ij}|^2 \Big)^{1/2},$$
and $\|\cdot\|_F$ is a matrix norm.

The Frobenius norm is the scoped norm `Matrix.Norms.Frobenius` of Mathlib. -/
theorem equation_2_3_1 (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = √(∑ i, ∑ j, |A i j| ^ 2) ∧ IsMatrixNorm (fun B : Matrix (Fin m) (Fin n) ℝ => ‖B‖) := by
  refine ⟨?_, isVectorNorm_norm⟩
  simp_rw [← Real.norm_eq_abs]
  rw [← frobenius_norm_sq_eq_sum_sq, Real.sqrt_sq (norm_nonneg _)]

end Frobenius

/-- The matrix $p$-norm is a matrix norm, because it is the seminorm induced by the vector $p$-norm,
which is definite. -/
private theorem isMatrixNorm_lpOpNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsMatrixNorm (lpOpNorm p : Matrix (Fin m) (Fin n) ℝ → ℝ) :=
  IsVectorNorm.exists_seminorm.2
    ⟨inducedSeminorm (lpSeminorm p) (lpSeminorm p) (lpSeminorm_definite p),
      funext fun A => by simp [lpOpNorm_eq_inducedNorm],
      fun A hA => (inducedNorm_eq_zero_iff (lpSeminorm_definite p) (lpSeminorm_definite p) A).1
        hA⟩

/-- **Equation (2.3.2)** of [golub2013matrix]. Let $1 \le p \le \infty$ and
$A \in \mathbb{R}^{m \times n}$. The **$p$-norm** of $A$ satisfies
$$\|A\|_p = \sup_{x \neq 0} \frac{\|Ax\|_p}{\|x\|_p}.$$
If $n \ge 1$, the supremum is attained on the unit sphere: $\|A\|_p = \|Ax\|_p$ for some $x$
with $\|x\|_p = 1$. Moreover $\|\cdot\|_p$ is a matrix norm.

**Reading.** The source leaves the positive dimension implicit in the unit-vector statement.
In dimension zero there is no unit vector and the operator norm is zero.

The second part is the display after (2.3.2) in the source. The $p$-norm is
`Matrix.lpOpNorm p A`, and the vector $p$-norm $\|x\|_p$ is `‖WithLp.toLp p x‖`. For $n = 0$
both sides of the first equation are $0$. -/
theorem equation_2_3_2 (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm p A = ⨆ x : {x : Fin n → ℝ // x ≠ 0},
        ‖WithLp.toLp p (A *ᵥ (x : Fin n → ℝ))‖ / ‖WithLp.toLp p (x : Fin n → ℝ)‖ ∧
      (0 < n → ∃ x : Fin n → ℝ, ‖WithLp.toLp p x‖ = 1 ∧
        lpOpNorm p A = ‖WithLp.toLp p (A *ᵥ x)‖) ∧
      IsMatrixNorm (lpOpNorm p : Matrix (Fin m) (Fin n) ℝ → ℝ) := by
  refine ⟨?_, fun hn => ?_, isMatrixNorm_lpOpNorm p⟩
  · rw [lpOpNorm_eq_inducedNorm, inducedNorm_eq_iSup_div (lpSeminorm_definite p)]
    rfl
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [lpOpNorm_eq_inducedNorm]
    exact exists_inducedNorm_eq (lpSeminorm_definite p) A

/-- **Equation (2.3.3)** of [golub2013matrix]. Let $1 \le p \le \infty$,
$A \in \mathbb{R}^{m \times n}$ and $B \in \mathbb{R}^{n \times q}$. Then
$$\|AB\|_p \le \|A\|_p \|B\|_p.$$

This is an inequality between three different norms, on $\mathbb{R}^{m \times q}$,
$\mathbb{R}^{m \times n}$ and $\mathbb{R}^{n \times q}$. -/
theorem equation_2_3_3 {q : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin q) ℝ) : lpOpNorm p (A * B) ≤ lpOpNorm p A * lpOpNorm p B :=
  lpOpNorm_mul_le p A B

section Elementwise

open scoped Matrix.Norms.Elementwise

/-- **Section 2.3.1** of [golub2013matrix], after (2.3.4): not every matrix norm is consistent. The
function $\|A\|_\Delta = \max_{i,j} |a_{ij}|$ is a matrix norm on $\mathbb{R}^{2 \times 2}$. For
$$A = B = \begin{bmatrix} 1 & 1 \\ 1 & 1 \end{bmatrix}$$
it gives $\|AB\|_\Delta = 2$ and $\|A\|_\Delta \|B\|_\Delta = 1$, so
$\|AB\|_\Delta > \|A\|_\Delta \|B\|_\Delta$.

The norm $\|\cdot\|_\Delta$ is the scoped norm `Matrix.Norms.Elementwise` of Mathlib. -/
theorem maxAbs_not_consistent :
    IsMatrixNorm (fun A : Matrix (Fin 2) (Fin 2) ℝ => ‖A‖) ∧
      ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1]‖ = 2 ∧
      ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 ∧
      ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ * ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖
        < ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1]‖ := by
  have hA : ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
    refine le_antisymm ((norm_le_iff zero_le_one).2 fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp
    · simpa using norm_apply_le_norm (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        (i := 0) (j := 0)
  have hmul : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hAA : ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1]‖ = 2 := by
    rw [hmul]
    refine le_antisymm ((norm_le_iff zero_le_two).2 fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp
    · simpa using norm_apply_le_norm (!![2, 2; 2, 2] : Matrix (Fin 2) (Fin 2) ℝ)
        (i := 0) (j := 0)
  refine ⟨isVectorNorm_norm, hAA, hA, ?_⟩
  rw [hAA, hA]
  norm_num

end Elementwise

/-- **Section 2.3.1** of [golub2013matrix], consistency with the vector norms. Let
$1 \le p \le \infty$, $A \in \mathbb{R}^{m \times n}$ and $x \in \mathbb{R}^n$. Then
$$\|Ax\|_p \le \|A\|_p \|x\|_p.$$
-/
theorem norm_mulVec_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : ‖WithLp.toLp p (A *ᵥ x)‖ ≤ lpOpNorm p A * ‖WithLp.toLp p x‖ :=
  lpSeminorm_mulVec_le p A x

/-- **Equation (2.3.5)** of [golub2013matrix], subordinate norms. Let $\|\cdot\|_\alpha$ be a vector
norm on $\mathbb{R}^n$ and let $\|\cdot\|_\beta$ be a seminorm on $\mathbb{R}^m$. For
$A \in \mathbb{R}^{m \times n}$, the subordinate norm satisfies
$$\|A\|_{\alpha,\beta} = \sup_{x \neq 0} \frac{\|Ax\|_\beta}{\|x\|_\alpha},$$
and $\|Ax\|_\beta \le \|A\|_{\alpha,\beta} \|x\|_\alpha$ for every $x \in \mathbb{R}^n$.

**Generalization.** The book takes both vector norms to be definite. The ratio only requires
definiteness of the input norm, so the target may be a seminorm.

The value is `Matrix.inducedNorm β α A`, the supremum of $\|Ax\|_\beta$ over
$\|x\|_\alpha \le 1$. -/
theorem equation_2_3_5 (α : Seminorm ℝ (Fin n → ℝ)) (β : Seminorm ℝ (Fin m → ℝ))
    (hα : ∀ x, α x = 0 → x = 0) (A : Matrix (Fin m) (Fin n) ℝ) :
    inducedNorm β α A = ⨆ x : {x : Fin n → ℝ // x ≠ 0}, β (A *ᵥ (x : Fin n → ℝ)) / α x ∧
      ∀ x, β (A *ᵥ x) ≤ inducedNorm β α A * α x :=
  ⟨inducedNorm_eq_iSup_div hα A, le_inducedNorm_mul hα A⟩

/-- **Equation (2.3.6)** of [golub2013matrix]. Let $\|\cdot\|_\alpha$ be a vector norm on
$\mathbb{R}^n$ with $n \ge 1$, let $\|\cdot\|_\beta$ be a seminorm on $\mathbb{R}^m$, and let
$A \in \mathbb{R}^{m \times n}$. Then the supremum (2.3.5) is attained: there is
$x_* \in \mathbb{R}^n$ with $\|x_*\|_\alpha = 1$ and
$$\|A\|_{\alpha,\beta} = \|A x_*\|_\beta.$$

**Generalization.** The target may be a seminorm because continuity on the input unit sphere
is enough for attainment.

**Reading.** The input dimension is positive so the unit sphere is nonempty. -/
theorem equation_2_3_6 (α : Seminorm ℝ (Fin n → ℝ)) (β : Seminorm ℝ (Fin m → ℝ))
    (hα : ∀ x, α x = 0 → x = 0) (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    ∃ x : Fin n → ℝ, α x = 1 ∧ inducedNorm β α A = β (A *ᵥ x) :=
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exists_inducedNorm_eq hα A

/-! ### §2.3.2 Some matrix norm properties -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Equation (2.3.7)** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$,
$$\|A\|_2 \le \|A\|_F \le \sqrt{\min\{m, n\}} \, \|A\|_2.$$
-/
theorem equation_2_3_7 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 A ≤ ‖A‖ ∧ ‖A‖ ≤ √((min m n : ℕ) : ℝ) * lpOpNorm 2 A := by
  refine ⟨l2_opNorm_le_frobenius_norm A, (frobenius_norm_le_sqrt_rank_mul_l2_opNorm A).trans ?_⟩
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (lpOpNorm_nonneg _ _)
  exact_mod_cast le_min A.rank_le_height A.rank_le_width

end Frobenius

/-- **Equation (2.3.8)** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$,
$$\max_{i,j} |a_{ij}| \le \|A\|_2 \le \sqrt{mn} \, \max_{i,j} |a_{ij}|.$$

**Reading.** The book writes a maximum. The supremum convention gives $0$ when either index
set is empty. -/
theorem equation_2_3_8 (A : Matrix (Fin m) (Fin n) ℝ) :
    (⨆ i, ⨆ j, |A i j|) ≤ lpOpNorm 2 A ∧
      lpOpNorm 2 A ≤ √((m : ℝ) * n) * ⨆ i, ⨆ j, |A i j| := by
  have hM : 0 ≤ ⨆ i, ⨆ j, |A i j| :=
    Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => abs_nonneg _
  refine ⟨Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) (lpOpNorm_nonneg _ _))
    (lpOpNorm_nonneg _ _), ?_⟩
  · rw [lpOpNorm_two, ← Real.norm_eq_abs]
    exact norm_entry_le_l2_opNorm A i j
  · have h := l2_opNorm_le_sqrt_card_mul_of_forall_norm_le A hM fun i j => by
      rw [Real.norm_eq_abs]
      exact (le_ciSup (Set.finite_range fun j => |A i j|).bddAbove j).trans
        (le_ciSup (Set.finite_range fun i => ⨆ j, |A i j|).bddAbove i)
    simpa using h

/-- **Equation (2.3.9)** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$, the 1-norm is
the largest column sum of $|A|$:
$$\|A\|_1 = \max_{1 \le j \le n} \sum_{i=1}^m |a_{ij}|.$$

**Reading.** If there are no columns, the supremum is zero. -/
theorem equation_2_3_9 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 1 A = ⨆ j, ∑ i, |A i j| := by
  rw [lpOpNorm_one_eq_sup_sum_norm, Finset.sup_univ_eq_ciSup, NNReal.coe_iSup]
  simp [Real.norm_eq_abs]

section Operator

open scoped Matrix.Norms.Operator

/-- **Equation (2.3.10)** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$, the
$\infty$-norm is the largest row sum of $|A|$:
$$\|A\|_\infty = \max_{1 \le i \le m} \sum_{j=1}^n |a_{ij}|.$$

**Reading.** If there are no rows, the supremum is zero. -/
theorem equation_2_3_10 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm ∞ A = ⨆ i, ∑ j, |A i j| := by
  rw [lpOpNorm_top, linfty_opNorm_def, Finset.sup_univ_eq_ciSup, NNReal.coe_iSup]
  simp [Real.norm_eq_abs]

end Operator

/-- If $b \ge 0$ and $a \le \sqrt{c}\, b$, then $(1/\sqrt{c})\, a \le b$, also in the degenerate
case $c = 0$, where $1/\sqrt{0} = 0$. -/
private theorem one_div_sqrt_mul_le {a b c : ℝ} (hb : 0 ≤ b) (h : a ≤ √c * b) :
    1 / √c * a ≤ b := by
  rcases (Real.sqrt_nonneg c).eq_or_lt with hc | hc
  · rw [← hc, div_zero, zero_mul]
    exact hb
  · rw [one_div, inv_mul_le_iff₀ hc]
    exact h

/-- **Equation (2.3.11)** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$,
$$\frac{1}{\sqrt{n}} \|A\|_\infty \le \|A\|_2 \le \sqrt{m} \, \|A\|_\infty.$$

**Reading.** The book's denominator presupposes $n>0$. For $n=0$, Lean gives
$1/\sqrt{n}=0$ and both operator norms vanish. -/
theorem equation_2_3_11 (A : Matrix (Fin m) (Fin n) ℝ) :
    1 / √(n : ℝ) * lpOpNorm ∞ A ≤ lpOpNorm 2 A ∧ lpOpNorm 2 A ≤ √(m : ℝ) * lpOpNorm ∞ A := by
  obtain ⟨h1, h2⟩ := l2_opNorm_le_sqrt_card_mul_linfty_opNorm A
  simp only [Fintype.card_fin] at h1 h2
  exact ⟨one_div_sqrt_mul_le (lpOpNorm_nonneg _ _) h2, h1⟩

/-- **Equation (2.3.12)** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$,
$$\frac{1}{\sqrt{m}} \|A\|_1 \le \|A\|_2 \le \sqrt{n} \, \|A\|_1.$$

**Reading.** The book's denominator presupposes $m>0$. For $m=0$, Lean gives
$1/\sqrt{m}=0$ and both operator norms vanish. -/
theorem equation_2_3_12 (A : Matrix (Fin m) (Fin n) ℝ) :
    1 / √(m : ℝ) * lpOpNorm 1 A ≤ lpOpNorm 2 A ∧ lpOpNorm 2 A ≤ √(n : ℝ) * lpOpNorm 1 A := by
  obtain ⟨h1, h2⟩ := l2_opNorm_le_sqrt_card_mul_lpOpNorm_one A
  simp only [Fintype.card_fin] at h1 h2
  exact ⟨one_div_sqrt_mul_le (lpOpNorm_nonneg _ _) h1, h2⟩

/-- **Equation (2.3.13)** of [golub2013matrix]. Let $1 \le p \le \infty$ and
$A \in \mathbb{R}^{m \times n}$. For $1 \le i_1 \le i_2 \le m$ and $1 \le j_1 \le j_2 \le n$,
the submatrix $A(i_1{:}i_2, j_1{:}j_2)$ satisfies
$$\|A(i_1{:}i_2, j_1{:}j_2)\|_p \le \|A\|_p.$$

The indices are 0-based in Lean: the hypotheses are $i_1 \le i_2 < m$ and $j_1 \le j_2 < n$, and
the submatrix has the rows $i_1, \dots, i_2$ and the columns $j_1, \dots, j_2$. -/
theorem equation_2_3_13 (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin m) (Fin n) ℝ)
    {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂) (hi₂ : i₂ < m) (hj : j₁ ≤ j₂) (hj₂ : j₂ < n) :
    lpOpNorm p (A.submatrix (fun k : Fin (i₂ - i₁ + 1) => (⟨i₁ + k, by omega⟩ : Fin m))
        (fun k : Fin (j₂ - j₁ + 1) => (⟨j₁ + k, by omega⟩ : Fin n))) ≤ lpOpNorm p A :=
  lpOpNorm_submatrix_le p A (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))

/-- **Section 2.3.2** of [golub2013matrix], convergence of matrix sequences. Let $f$ be a matrix
norm on $\mathbb{R}^{m \times n}$, let $A^{(k)} \in \mathbb{R}^{m \times n}$ for $k \ge 0$, and
let $A \in \mathbb{R}^{m \times n}$. Then $f(A^{(k)} - A) \to 0$ if and only if $A^{(k)} \to A$.
So the choice of norm does not matter for convergence.

The convergence $A^{(k)} \to A$ is in the topology of Mathlib on `Matrix (Fin m) (Fin n) ℝ`,
which is entrywise convergence. -/
theorem tendsto_iff_of_isMatrixNorm {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : IsMatrixNorm f)
    (A : ℕ → Matrix (Fin m) (Fin n) ℝ) (A₀ : Matrix (Fin m) (Fin n) ℝ) :
    Tendsto (fun k => f (A k - A₀)) atTop (𝓝 0) ↔ Tendsto A atTop (𝓝 A₀) := by
  let _ : NormedAddCommGroup (Matrix (Fin m) (Fin n) ℝ) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix (Fin m) (Fin n) ℝ) := Matrix.normedSpace
  exact tendsto_iff_of_isVectorNorm hf A A₀

/-! ### §2.3.3 The matrix 2-norm -/

/-- For $n \ge 1$, the 2-norm of $A \in \mathbb{R}^{m \times n}$ is one of its column-indexed
singular values, and it is at least each of them. -/
private theorem exists_colSingularValues_eq_lpOpNorm_two (A : Matrix (Fin m) (Fin n) ℝ)
    (hn : 0 < n) :
    ∃ i, A.colSingularValues i = lpOpNorm 2 A ∧ ∀ j, A.colSingularValues j ≤ lpOpNorm 2 A := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := A.colSingularValues)
  exact ⟨i₀, by rw [lpOpNorm_two, l2_opNorm_eq_iSup_colSingularValues, hi₀],
    colSingularValues_le_lpOpNorm_two A⟩

/-- **Theorem 2.3.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ with $n \ge 1$, and
let $\mu = \|A\|_2$. Then there is $z \in \mathbb{R}^n$ with $\|z\|_2 = 1$ and
$$A^T A z = \mu^2 z.$$

**Reading.** The source leaves the positive column count implicit. The hypothesis is
needed because the zero-dimensional vector space has no unit vector. -/
theorem theorem_2_3_1 (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    ∃ z : Fin n → ℝ, ‖WithLp.toLp 2 z‖ = 1 ∧ (Aᵀ * A) *ᵥ z = lpOpNorm 2 A ^ 2 • z := by
  obtain ⟨i, hi, -⟩ := exists_colSingularValues_eq_lpOpNorm_two A hn
  refine ⟨WithLp.ofLp (A.rightSingularBasis i), by
    rw [WithLp.toLp_ofLp, (A.rightSingularBasis).norm_eq_one], ?_⟩
  have h := congrArg WithLp.ofLp (A.toEuclideanLin_conjTranspose_mul_self_rightSingularBasis i)
  simpa [toEuclideanLin_apply, conjTranspose_eq_transpose_of_trivial, hi] using h

/-- **Section 2.3.3** of [golub2013matrix], after Theorem 2.3.1. Let $A \in \mathbb{R}^{m \times n}$
with $n \ge 1$. Then
$$\|A\|_2 = \sqrt{\lambda_{\max}(A^T A)},$$
and $\|A\|_2^2$ is a zero of the polynomial $p(\lambda) = \det(A^T A - \lambda I)$.

**Reading.** The Gram matrix has positive order so that a largest eigenvalue exists.

The eigenvalue $\lambda_{\max}(A^T A)$ is the first sorted eigenvalue
`Matrix.IsHermitian.sortedEigenvalues` at index $0$, as in §2.1. The Hermitian matrix is
$A^H A$, which is $A^T A$ over $\mathbb{R}$. -/
theorem l2_opNorm_eq_sqrt_lambdaMax (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    lpOpNorm 2 A = √((isHermitian_conjTranspose_mul_self A).sortedEigenvalues ⟨0, hn⟩) ∧
      (Aᵀ * A - lpOpNorm 2 A ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).det = 0 := by
  have hG := isHermitian_conjTranspose_mul_self A
  set k₀ : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using hn⟩
  obtain ⟨i₀, hi₀, hmax⟩ := exists_colSingularValues_eq_lpOpNorm_two A hn
  set e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have heig : ∀ j, hG.eigenvalues j = hG.eigenvalues₀ (e.symm j) := fun j => rfl
  have hsq : lpOpNorm 2 A ^ 2 = hG.eigenvalues₀ k₀ := by
    refine le_antisymm ?_ ?_
    · rw [← hi₀, sq_colSingularValues, heig]
      exact hG.eigenvalues₀_antitone (Fin.le_def.2 (Nat.zero_le _))
    · have h := sq_colSingularValues A (e k₀)
      rw [heig, Equiv.symm_apply_apply] at h
      rw [← h]
      exact pow_le_pow_left₀ (A.colSingularValues_nonneg _) (hmax _) 2
  refine ⟨by
    rw [IsHermitian.sortedEigenvalues_apply]
    exact (by rw [← hsq, Real.sqrt_sq (lpOpNorm_nonneg _ _)] :
      lpOpNorm 2 A = √(hG.eigenvalues₀ k₀)),
    ?_⟩
  obtain ⟨z, hz1, hz⟩ := theorem_2_3_1 A hn
  refine exists_mulVec_eq_zero_iff.1 ⟨z, fun h0 => by simp [h0] at hz1, ?_⟩
  rw [sub_mulVec, hz, smul_mulVec, one_mulVec, sub_self]

/-- **Corollary 2.3.2** of [golub2013matrix]. For $A \in \mathbb{R}^{m \times n}$,
$$\|A\|_2 \le \sqrt{\|A\|_1 \|A\|_\infty}.$$
-/
theorem corollary_2_3_2 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 A ≤ √(lpOpNorm 1 A * lpOpNorm ∞ A) :=
  (le_abs_self _).trans (Real.abs_le_sqrt (l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm A))

/-! ### §2.3.4 Perturbations and the inverse -/

/-- **Lemma 2.3.3** of [golub2013matrix]. Let $1 \le p \le \infty$ and
$F \in \mathbb{R}^{n \times n}$ with $\|F\|_p < 1$. Then $I - F$ is nonsingular,
$$(I - F)^{-1} = \sum_{k=0}^\infty F^k, \qquad \|(I - F)^{-1}\|_p \le \frac{1}{1 - \|F\|_p}.$$

The series is a `HasSum` statement in the topology of matrices. -/
theorem lemma_2_3_3 (p : ℝ≥0∞) [Fact (1 ≤ p)] {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : lpOpNorm p F < 1) :
    IsUnit (1 - F) ∧ HasSum (fun k => F ^ k) (1 - F)⁻¹ ∧
      lpOpNorm p (1 - F)⁻¹ ≤ 1 / (1 - lpOpNorm p F) := by
  have hp := lpSeminorm_definite (𝕜 := ℝ) (n := Fin n) p
  simp only [lpOpNorm_eq_inducedNorm] at hF ⊢
  refine ⟨isUnit_one_sub_of_inducedNorm_lt_one hp hF, hasSum_pow_of_inducedNorm_lt_one hp hF, ?_⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Subsingleton.elim (1 - F)⁻¹ 0, show inducedNorm (lpSeminorm p) (lpSeminorm p)
      (0 : Matrix (Fin n) (Fin n) ℝ) = 0 from (inducedNorm_eq_zero_iff hp hp 0).2 rfl]
    exact div_nonneg zero_le_one (by linarith)
  · exact inducedNorm_inv_one_sub_le hp hF

/-- **Section 2.3.4** of [golub2013matrix], after Lemma 2.3.3. Let $1 \le p \le \infty$ and
$F \in \mathbb{R}^{n \times n}$ with $\|F\|_p < 1$. Then
$$\|(I - F)^{-1} - I\|_p \le \frac{\|F\|_p}{1 - \|F\|_p}.$$
So a perturbation of order $\epsilon$ of the identity gives a perturbation of order $\epsilon$
of its inverse. -/
theorem norm_inv_one_sub_sub_one_le (p : ℝ≥0∞) [Fact (1 ≤ p)] {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : lpOpNorm p F < 1) :
    lpOpNorm p ((1 - F)⁻¹ - 1) ≤ lpOpNorm p F / (1 - lpOpNorm p F) := by
  simp only [lpOpNorm_eq_inducedNorm] at hF ⊢
  exact inducedNorm_inv_one_sub_sub_one_le (lpSeminorm_definite p) hF

/-- **Theorem 2.3.4** of [golub2013matrix]. Let $1 \le p \le \infty$, let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $E \in \mathbb{R}^{n \times n}$, and let
$r = \|A^{-1}E\|_p < 1$. Then $A + E$ is nonsingular and
$$\|(A + E)^{-1} - A^{-1}\|_p \le \frac{\|E\|_p \|A^{-1}\|_p^2}{1 - r}.$$

**Correction.** The printed proof uses $A+E=(I+F)A$ with $F=-EA^{-1}$ and equates
$\|F\|_p$ with $\|A^{-1}E\|_p$. With $A=\operatorname{diag}(1,2)$ and $E=e_1e_2^T/2$,
these norms are $1/4$ and $1/2$. The proof uses $A+E=A(I+A^{-1}E)$, which yields the
printed bound with its stated $r$. -/
theorem theorem_2_3_4 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A E : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hr : lpOpNorm p (A⁻¹ * E) < 1) :
    IsUnit (A + E) ∧
      lpOpNorm p ((A + E)⁻¹ - A⁻¹) ≤
        lpOpNorm p E * lpOpNorm p A⁻¹ ^ 2 / (1 - lpOpNorm p (A⁻¹ * E)) := by
  have ha : IsUnit (lpCLM p A) := (isUnit_lpCLM_iff p A).2 hA
  have hinv : Ring.inverse (lpCLM p A) = lpCLM p A⁻¹ := ringInverse_lpCLM p A
  have hr' : ‖Ring.inverse (lpCLM p A) * lpCLM p E‖ < 1 := by
    rw [hinv, ← lpCLM_mul]
    exact hr
  refine ⟨?_, ?_⟩
  · have h := NormedRing.isUnit_add_of_norm_inverse_mul_lt_one ha hr'
    rwa [← lpCLM_add, isUnit_lpCLM_iff] at h
  · have h := (NormedRing.norm_inverse_add_sub_le_of_norm_inverse_mul_lt_one ha hr').2
    rw [← lpCLM_add, ringInverse_lpCLM, hinv, ← lpCLM_mul, ← lpCLM_sub] at h
    exact h

/-! ### §2.3.5 Orthogonal invariance -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Equation (2.3.14)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, and let
$Q \in \mathbb{R}^{m \times m}$ and $Z \in \mathbb{R}^{n \times n}$ be orthogonal. Then
$$\|QAZ\|_F = \|A\|_F.$$
-/
theorem equation_2_3_14 {Q : Matrix (Fin m) (Fin m) ℝ} {Z : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : ‖Q * A * Z‖ = ‖A‖ :=
  frobenius_norm_unitary_mul_mul_unitary hQ A hZ

end Frobenius

/-- **Equation (2.3.15)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$, and let
$Q \in \mathbb{R}^{m \times m}$ and $Z \in \mathbb{R}^{n \times n}$ be orthogonal. Then
$$\|QAZ\|_2 = \|A\|_2.$$
-/
theorem equation_2_3_15 {Q : Matrix (Fin m) (Fin m) ℝ} {Z : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : lpOpNorm 2 (Q * A * Z) = lpOpNorm 2 A := by
  rw [lpOpNorm_two, lpOpNorm_two]
  exact l2_opNorm_unitary_mul_mul_unitary hQ A hZ

end GolubVanLoan.Chapter02
