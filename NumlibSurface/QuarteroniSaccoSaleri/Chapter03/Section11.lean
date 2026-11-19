/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.ConditionEstimation
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section10

/-!
# Quarteroni, Sacco and Saleri, Section 3.11: An approximate computation of $K(A)$

This module formalizes Section 3.11 of [quarteroni2000numerical]. Computing the condition number
$K(A) = \|A\|\|A^{-1}\|$ exactly needs $A^{-1}$, which is expensive. Since
$\|A^{-1}d\|/\|d\| \le \|A^{-1}\|$ for every vector $d$, a well-chosen probe vector $d$ gives a
cheap lower estimate. With the triangular systems $R^T x = d$ and $Ry = x$ of (3.70), or
$(LU)^T x = d$ and $LUy = x$ of (3.72), the estimate is $\hat K(A) = \|A\|\|y\|/\|x\|$, and it never
exceeds $K(A)$. The module also states that $K_2(A) = K_2(R)$ for a QR factorization $A = QR$.
Exercise 15, which the text cites, is formalized in
`NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section15`.

The proofs specialize the backbone modules `Numlib.Direct.ConditionEstimation` (the basic inequality
$\|A^{-1}d\|/\|d\| \le \|A^{-1}\|$ and the condition estimate `condEstimate` on a Hilbert space) and
`Numlib.Analysis.Matrix.OperatorNorm` (the identity $K_2(QR) = K_2(R)$).

## Main definitions

* Section 3.11, `QuarteroniSaccoSaleri.Chapter03.condEstimate`: the estimate
  $\hat K_p(A) = \|A\|_p\|y\|_p/\|x\|_p$ from a probe vector $d$.

## Main results

* (3.70), `QuarteroniSaccoSaleri.Chapter03.equation_3_70`: $\|A^{-1}d\|/\|d\| \le \|A^{-1}\|$, and
  $\|y\|/\|x\| \le \|A^{-1}\|$ for the solutions of $A^T x = d$, $Ay = x$.
* Section 3.11, `QuarteroniSaccoSaleri.Chapter03.condEstimate_two_eq`: for $p = 2$ the estimate is
  the Hilbert-space estimate of the backbone.
* Section 3.11, `QuarteroniSaccoSaleri.Chapter03.condEstimate_le`: $\hat K_p(A) \le K_p(A)$.
* Section 3.11, `QuarteroniSaccoSaleri.Chapter03.condNumber_two_eq_of_qr`: $K_2(A) = K_2(R)$ for
  $A = QR$ with $Q$ orthogonal.

## Conventions

* Norms are the induced $p$-norms of Section 3.1: $\|A\|_p$ is `Matrix.lpOpNorm p A`, $\|x\|_p$ is
  the norm of `toLp p x`, and $K_p(A)$ is `QuarteroniSaccoSaleri.Chapter03.condNumber p A`. The
  book's $\hat K_1(A)$ is the case $p = 1$, and its discussion of $\|\cdot\|_2$ is the case $p = 2$.
* The systems $R^T x = d$, $Ry = x$ of (3.70), or $(LU)^T x = d$, $LUy = x$ of (3.72) with $A = LU$,
  are solved as $x = A^{-T} d$ and $y = A^{-1} x$ for a nonsingular $A$.

## Implementation notes

* The backbone's `condEstimate` is defined on a Hilbert space, where the adjoint replaces the
  transpose. It is the case $p = 2$ (`QuarteroniSaccoSaleri.Chapter03.condEstimate_two_eq`). The
  book's estimate in the $1$-norm needs the matrix form
  `QuarteroniSaccoSaleri.Chapter03.condEstimate`.

## Deviations from the source

* **Equation (3.70) and the condition estimate** (scope). The source uses the $1$-norm and
  $2$-norm with a triangular factor or an LU solve. The statements allow any induced $p$-norm
  and use inverses of the input matrix directly. A zero probe gives a zero ratio.

## Not formalized

* **The lookahead heuristic (3.71)** for the signs of $d$, which states no theorem.
* **Program 14**, which states no theorem.
* **Example 3.9**, which states no theorem.
-/

open Finset Matrix WithLp
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **Equation (3.70)** of [quarteroni2000numerical], with the basic inequality of Section 3.11. Let
$1 \le p \le \infty$, let $A \in \mathbb{R}^{n \times n}$ be nonsingular, and let
$d \in \mathbb{R}^n$. Then the solution $y$ of $Ay = d$ satisfies
$$\gamma(d) = \frac{\|y\|_p}{\|d\|_p} \le \|A^{-1}\|_p.$$
Moreover, the solutions $x$ of $A^T x = d$ and $y$ of $Ay = x$ satisfy
$\|y\|_p / \|x\|_p \le \|A^{-1}\|_p$.

The book writes $R$ for $A$ in (3.70), and it assumes $d \neq 0$; for $d = 0$ the quotient is
$0$ by Lean's division. The bound follows from the definition of the induced norm. The proof
uses `norm_apply_div_le_norm_inverse`.

**Scope.** The source discusses the $2$-norm and $1$-norm with a triangular factor, then
an LU solve. This bound applies to any induced $p$-norm and invertible matrix. The quotient
at a zero probe is interpreted as zero. -/
theorem equation_3_70 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (d : Fin n → ℝ) :
    ‖toLp p (A⁻¹ *ᵥ d)‖ / ‖toLp p d‖ ≤ lpOpNorm p A⁻¹ ∧
      ‖toLp p (A⁻¹ *ᵥ (Aᵀ⁻¹ *ᵥ d))‖ / ‖toLp p (Aᵀ⁻¹ *ᵥ d)‖ ≤ lpOpNorm p A⁻¹ := by
  have key : ∀ v : Fin n → ℝ, ‖toLp p (A⁻¹ *ᵥ v)‖ / ‖toLp p v‖ ≤ lpOpNorm p A⁻¹ := fun v => by
    have h := norm_apply_div_le_norm_inverse (lpEquiv p hA) (toLp p v)
    rwa [lpEquiv_symm_apply, ofLp_toLp, coe_lpEquiv_symm] at h
  exact ⟨key d, key _⟩

/-- **Section 3.11** of [quarteroni2000numerical], the **condition estimate** from a probe vector
$d$. Let $A \in \mathbb{R}^{n \times n}$ and $d \in \mathbb{R}^n$, let $x$ solve $A^T x = d$ and
let $y$ solve $Ay = x$. Then
$$\hat K_p(A) = \frac{\|A\|_p \|y\|_p}{\|x\|_p}.$$

The systems are the book's $R^T x = d$, $Ry = x$ of (3.70) and $(LU)^T x = d$, $LUy = x$ of
(3.72). The case $p = 1$ is the book's $\hat K_1(A)$. The quality of the estimate depends on the
heuristic choice of $d$, and its one provable property is $\hat K_p(A) \le K_p(A)$
(`QuarteroniSaccoSaleri.Chapter03.condEstimate_le`). The vectors are $x = A^{-T} d$ and
$y = A^{-1} x$ with Lean's matrix inverse, and the estimate is $0$ when $x = 0$.

**Scope.** The definition uses any invertible input matrix and induced $p$-norm in the
source's condition estimate. The quotient at a zero probe is interpreted as zero. -/
noncomputable def condEstimate (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ℝ :=
  lpOpNorm p A * ‖toLp p (A⁻¹ *ᵥ (Aᵀ⁻¹ *ᵥ d))‖ / ‖toLp p (Aᵀ⁻¹ *ᵥ d)‖

/-- The adjoint of the map $x \mapsto Mx$ on `EuclideanSpace ℝ (Fin n)` is the map
$x \mapsto M^T x$. -/
private theorem adjoint_lpCLM_two (M : Matrix (Fin n) (Fin n) ℝ) :
    ContinuousLinearMap.adjoint (lpCLM 2 M) = lpCLM 2 Mᵀ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [lpCLM_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- **Section 3.11** of [quarteroni2000numerical], the case $p = 2$. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular and $d \in \mathbb{R}^n$. Then $\hat K_2(A)$
equals the backbone's Hilbert-space estimate `condEstimate` for the operator $x \mapsto Ax$ on
$\mathbb{R}^n$ with the Euclidean norm, whose adjoint $(A^{-1})^*$ is $(A^{-1})^T = (A^T)^{-1}$.

The operator is `Matrix.lpEquiv 2 hA`. -/
theorem condEstimate_two_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (d : Fin n → ℝ) :
    condEstimate 2 A d = _root_.condEstimate (lpEquiv 2 hA) (toLp 2 d) := by
  rw [condEstimate, _root_.condEstimate, coe_lpEquiv, coe_lpEquiv_symm, adjoint_lpCLM_two,
    lpEquiv_symm_apply, lpCLM_apply, ofLp_toLp, ofLp_toLp, transpose_nonsing_inv]
  rfl

/-- **Section 3.11** of [quarteroni2000numerical], $\hat K_p(A) \le K_p(A)$. Let
$1 \le p \le \infty$, let $A \in \mathbb{R}^{n \times n}$ be nonsingular, and let
$d \in \mathbb{R}^n$ be any probe vector. Then the estimate never exceeds the condition number:
$$\hat K_p(A) \le K_p(A).$$

The reason is that $\|y\|/\|x\| = \|A^{-1}x\|/\|x\| \le \|A^{-1}\|$. The theorem is the matrix
form of the backbone's `condEstimate_le_condNumber`.

**Reading.** Explicit lower-bound theorem for any induced p-norm.
-/
theorem condEstimate_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (d : Fin n → ℝ) :
    condEstimate p A d ≤ condNumber p A := by
  rw [condEstimate, condNumber, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (equation_3_70 p hA d).2 (lpOpNorm_nonneg _ _)

open scoped Matrix.Norms.L2Operator in
/-- **Section 3.11** of [quarteroni2000numerical], the identity $K_2(A) = K_2(R)$, "due to Property
1.8" (Exercise 14). Let $A, Q, R \in \mathbb{R}^{n \times n}$ with $Q$ orthogonal and $A = QR$.
Then the spectral condition numbers agree:
$$K_2(A) = K_2(R).$$

The reason is that $\|QR\|_2 = \|R\|_2$ and $\|(QR)^{-1}\|_2 = \|R^{-1}Q^T\|_2 = \|R^{-1}\|_2$.
No nonsingularity is assumed: for a singular $R$, Lean's matrix inverse is $0$, and both sides
are $0$. The proof uses `Matrix.condNumber_l2_unitary_mul`. -/
theorem condNumber_two_eq_of_qr {A Q R : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hA : A = Q * R) : condNumber 2 A = condNumber 2 R := by
  rw [condNumber_two_eq, condNumber_two_eq, hA]
  exact condNumber_l2_unitary_mul hQ R

end QuarteroniSaccoSaleri.Chapter03
