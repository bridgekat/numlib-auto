/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# Condition estimation

A condition estimator for a nonsingular system $Ax = b$ solves a system $Ay = d$ with a right-hand
side $d$ that a heuristic chooses, and estimates $\|A^{-1}\|$ by $\|y\| / \|d\|$. This module proves
the one property that holds for every choice of $d$: the estimate is a lower bound,
$$\frac{\|y\|}{\|d\|} \le \|A^{-1}\|, \qquad \frac{\|A\| \, \|y\|}{\|d\|} \le \kappa(A) = \|A\| \,
  \|A^{-1}\|.$$
At $p = \infty$ this is the implication $Ay = d \Rightarrow \|A^{-1}\|_\infty \ge \|y\|_\infty /
\|d\|_\infty$ of Cline, Moler, Stewart and Wilkinson in [golub2013matrix], §3.5.4. The presentation
also follows [quarteroni2000numerical], §3.11, and [higham2002accuracy], Chapter 15.

The results are first stated for a continuous linear equivalence $A$ of a normed space, and then for
a square matrix $A \in \mathbb{K}^{n \times n}$, $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, in the
norms $\|\cdot\|_p$ induced by the vector $p$-norms, $1 \le p \le \infty$. How good the lower bound
is depends on the choice of $d$, and no theorem describes this.

## Main definitions

* `condEstimate`: the estimate $\hat K(A) = \|A\| \, \|y\| / \|x\|$ of [quarteroni2000numerical]
  (3.70), with $A^* x = d$ and $Ay = x$, on a Hilbert space.
* `Matrix.lpCondEstimate`: the estimate $\|A\|_p \, \|A^{-1} r\|_p / \|r\|_p$ of a square matrix
  from a probe vector $r$.

## Main results

* `norm_apply_div_le_norm_inverse`: the basic inequality $\|A^{-1} d\| / \|d\| \le \|A^{-1}\|$ for a
  continuous linear equivalence $A$ of a normed space.
* `condEstimate_le_condNumber`: $\hat K(A) \le \kappa(A)$.
* `Matrix.norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec`: $\|y\|_p \le \|A^{-1}\|_p \, \|Ay\|_p$ for a
  nonsingular matrix $A$.
* `Matrix.lpCondEstimate_le_condNumberLp`: the matrix estimate is at most $\kappa_p(A)$.
* `Matrix.linfty_opNorm_mul_norm_le_condNumberLp_top_of_mulVec_eq`: the sign-vector estimate
  $\|T\|_\infty \|y\|_\infty$ of [golub2013matrix] (3.5.6) and Algorithm 3.5.1 is at most
  $\kappa_\infty(T)$.
* `Matrix.one_le_lpOpNorm_top_inv_mul_norm_mulVec_inv_norm_smul`: for $y \neq 0$, $\|T (y /
  \|y\|_\infty)\|_\infty \ge 1 / \|T^{-1}\|_\infty$.
* `pi_norm_eq_one_of_forall_norm_eq_one`: a vector whose entries all have norm $1$ has sup norm $1$.

## Implementation notes

* The estimate `condEstimate` uses the adjoint, so it is stated on a complete inner product space
  over `RCLike 𝕜`.
* The matrix statements are instances of the operator statements, through the continuous linear
  equivalence `Matrix.lpEquiv p hA` of `PiLp p` that a nonsingular matrix $A$ defines. The vector
  norm $\|\cdot\|_p$ is `Matrix.lpSeminorm p`, and the matrix norm $\|\cdot\|_p$ is
  `Matrix.lpOpNorm p`, both of `Numlib.Analysis.Matrix.OperatorNorm`.
* The heuristics that choose $d$ are algorithms, and they are not formalized here: the LINPACK
  look-ahead of [golub2013matrix] Algorithm 3.5.1, the greedy choice of signs $\pm 1$ in
  [golub2013matrix] (3.5.6), and the look-ahead of [quarteroni2000numerical] (3.71)–(3.72).
-/

open NormedRing
open scoped ENNReal

/-! ### The operator statements -/

section CondEstimate

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **basic inequality of condition estimation**. Let $E$ be a normed space over a nontrivially
normed field, and let $A : E \to E$ be a continuous linear equivalence. Then for every
$d \in E$,
$$\frac{\|A^{-1} d\|}{\|d\|} \le \|A^{-1}\|.$$
This is in [quarteroni2000numerical], §3.11.

With $y = A^{-1} d$, the left side is the quantity $\gamma(d) = \|y\| / \|d\|$, and the
estimators look for a $d$ that makes $\gamma(d)$ as large as possible. At $d = 0$ the left side
is $0$, by the convention $t / 0 = 0$. -/
theorem norm_apply_div_le_norm_inverse (A : E ≃L[𝕜] E) (d : E) :
    ‖A.symm d‖ / ‖d‖ ≤ ‖(A.symm : E →L[𝕜] E)‖ := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  rw [div_le_iff₀ (norm_pos_iff.2 hd)]
  exact (A.symm : E →L[𝕜] E).le_opNorm d

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The **condition estimate** of [quarteroni2000numerical], §3.11, (3.70). Let $E$ be a Hilbert
space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $A : E \to E$ be a continuous linear
equivalence, and let $d \in E$ be a probe vector. Solve $A^* x = d$ and $Ay = x$, that is, put
$x = (A^{-1})^* d$ and $y = A^{-1} x$. The estimate of the condition number $K(A)$ is
$$\hat K(A) = \frac{\|A\| \, \|y\|}{\|x\|}.$$

The book solves $R^T x = d$, or $(LU)^T x = d$ in (3.72); here $A^*$ is the adjoint in the
Hilbert space $E$. The value is $0$ when $x = 0$, that is, when $d = 0$. The only property of
the estimate that holds for every $d$ is $\hat K(A) \le K(A)$, which is
`condEstimate_le_condNumber`. Its quality depends on the heuristic choice of $d$. -/
noncomputable def condEstimate (A : E ≃L[𝕜] E) (d : E) : ℝ :=
  ‖(A : E →L[𝕜] E)‖ * ‖A.symm (ContinuousLinearMap.adjoint (A.symm : E →L[𝕜] E) d)‖ /
    ‖ContinuousLinearMap.adjoint (A.symm : E →L[𝕜] E) d‖

/-- The **condition estimate never exceeds the condition number**. Let $E$ be a Hilbert space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $A : E \to E$ be a continuous linear
equivalence. Then for every probe vector $d \in E$, the estimate `condEstimate` satisfies
$$\hat K(A) \le K(A) = \|A\| \, \|A^{-1}\|.$$

The reason is $\|y\| / \|x\| = \|A^{-1} x\| / \|x\| \le \|A^{-1}\|$. The condition number is
`NormedRing.condNumber` of $A$ as an element of the ring of continuous linear maps $E \to E$.
The book's estimate $\hat K_1(A) = \|R\|_1 \|y\|_1 / \|x\|_1$ in the $1$-norm does not come from
an inner product; the matrix form `Matrix.lpCondEstimate_le_condNumberLp` at $p = 1$ covers it. -/
theorem condEstimate_le_condNumber (A : E ≃L[𝕜] E) (d : E) :
    condEstimate A d ≤ condNumber (A : E →L[𝕜] E) := by
  rw [condEstimate, A.condNumber_eq, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_apply_div_le_norm_inverse A _) (norm_nonneg _)

end CondEstimate

/-- Let $\iota$ be a finite nonempty index set, let $E$ be a seminormed group, and let
$f : \iota \to E$ satisfy $\|f_i\| = 1$ for every $i$. Then the sup norm of $f$ is $\|f\| = 1$.

The use is the sign vectors $d \in \{\pm 1\}^n$ of [golub2013matrix] (3.5.6) and Algorithm
3.5.1. Mathlib has the case of a constant vector, `pi_norm_const'`. -/
theorem pi_norm_eq_one_of_forall_norm_eq_one {ι E : Type*} [Fintype ι] [Nonempty ι]
    [SeminormedAddCommGroup E] {f : ι → E} (hf : ∀ i, ‖f i‖ = 1) : ‖f‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (hf i).le) ?_
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (hf i).symm.le.trans (norm_le_pi_norm f i)

/-! ### The matrix statements in the induced $p$-norms -/

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **basic inequality of condition estimation** in the induced $p$-norm. Let
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $1 \le p \le \infty$, and let
$A \in \mathbb{K}^{n \times n}$ be nonsingular. Then for every $y \in \mathbb{K}^n$,
$$\|y\|_p \le \|A^{-1}\|_p \, \|Ay\|_p.$$
With $d = Ay \neq 0$ this is $\|A^{-1}\|_p \ge \|y\|_p / \|d\|_p$, which at $p = \infty$ is the
form of [golub2013matrix], §3.5.4.

The vector norm is `Matrix.lpSeminorm p`, and the matrix norm is `Matrix.lpOpNorm p`; at
$p = \infty$ the latter is the norm of Mathlib, by `Matrix.lpOpNorm_top`. The proof applies
`norm_apply_div_le_norm_inverse` to `Matrix.lpEquiv p hA`. -/
theorem norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec {A : Matrix n n 𝕜} (hA : IsUnit A)
    (y : n → 𝕜) : lpSeminorm p y ≤ lpOpNorm p A⁻¹ * lpSeminorm p (A *ᵥ y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hAy : A *ᵥ y ≠ 0 := fun h =>
    hy (mulVec_injective_iff_isUnit.2 hA (h.trans (mulVec_zero A).symm))
  have h := norm_apply_div_le_norm_inverse (lpEquiv p hA) (WithLp.toLp p (A *ᵥ y))
  rw [lpEquiv_symm_apply, WithLp.ofLp_toLp, mulVec_mulVec,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hA), one_mulVec, coe_lpEquiv_symm,
    div_le_iff₀ (norm_pos_iff.2 ((WithLp.toLp_eq_zero p).not.2 hAy))] at h
  simpa [lpOpNorm] using h

/-- The **condition estimate from a probe vector**. Let $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
let $1 \le p \le \infty$, let $A \in \mathbb{K}^{n \times n}$ and let $r \in \mathbb{K}^n$. With
$z = A^{-1} r$, the estimate is
$$\frac{\|A\|_p \, \|z\|_p}{\|r\|_p}.$$
This is Step 3 of [golub2013matrix], §3.5.4, at $p = \infty$, and [quarteroni2000numerical]
(3.70) with the probe already transformed.

The value is $0$ when $r = 0$. The inverse is Mathlib's `A⁻¹`, which is $0$ for a singular $A$,
so the value is also $0$ then. -/
noncomputable def lpCondEstimate (A : Matrix n n 𝕜) (r : n → 𝕜) : ℝ :=
  lpOpNorm p A * lpSeminorm p (A⁻¹ *ᵥ r) / lpSeminorm p r

/-- The **condition estimate never exceeds the condition number**. Let $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, let $1 \le p \le \infty$, and let $A \in \mathbb{K}^{n \times n}$ be nonsingular.
Then for every probe vector $r \in \mathbb{K}^n$, with $z = A^{-1} r$,
$$\frac{\|A\|_p \, \|z\|_p}{\|r\|_p} \le \kappa_p(A) = \|A\|_p \, \|A^{-1}\|_p.$$

This is the matrix form of `condEstimate_le_condNumber`. The condition number $\kappa_p$ is
`Matrix.condNumberLp`. The estimate is `Matrix.lpCondEstimate`. The proof applies
`Matrix.norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec` to $y = A^{-1} r$. -/
theorem lpCondEstimate_le_condNumberLp {A : Matrix n n 𝕜} (hA : IsUnit A) (r : n → 𝕜) :
    lpCondEstimate p A r ≤ condNumberLp p A := by
  have hn : 0 ≤ lpOpNorm p A := norm_nonneg _
  rcases eq_or_ne r 0 with rfl | hr
  · rw [lpCondEstimate, map_zero, div_zero, condNumberLp]
    exact mul_nonneg hn (norm_nonneg _)
  have h := norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec p hA (A⁻¹ *ᵥ r)
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).1 hA), one_mulVec,
    ← div_le_iff₀ (by simpa using hr)] at h
  rw [lpCondEstimate, condNumberLp, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h hn

/-- The **sign-vector estimate is a lower bound for $\kappa_\infty$**. Let $\mathbb{K} = \mathbb{R}$
or $\mathbb{C}$, let $n \ge 1$, and let $T \in \mathbb{K}^{n \times n}$ be nonsingular. Let
$y, d \in \mathbb{K}^n$ satisfy $Ty = d$ and $|d_i| = 1$ for every $i$. Then
$$\|T\|_\infty \, \|y\|_\infty \le \kappa_\infty(T).$$
This is the estimate $\hat\kappa_\infty = \|T\|_\infty \|y\|_\infty$ of [golub2013matrix],
§3.5.4, (3.5.6) and Algorithm 3.5.1, where $d_i = \pm 1$.

The vector norm $\|y\|_\infty$ is the sup norm of Mathlib on `n → 𝕜`. The condition number
$\kappa_\infty$ is `Matrix.condNumberLp ⊤`. The matrix norm is `Matrix.lpOpNorm ⊤`. -/
theorem linfty_opNorm_mul_norm_le_condNumberLp_top_of_mulVec_eq [Nonempty n]
    {T : Matrix n n 𝕜} (hT : IsUnit T) {y d : n → 𝕜} (hy : T *ᵥ y = d)
    (hd : ∀ i, ‖d i‖ = 1) : lpOpNorm ⊤ T * ‖y‖ ≤ condNumberLp ⊤ T := by
  have h := norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec ⊤ hT y
  rw [lpSeminorm_apply, lpSeminorm_apply, PiLp.norm_toLp, PiLp.norm_toLp, hy,
    pi_norm_eq_one_of_forall_norm_eq_one hd, mul_one] at h
  rw [condNumberLp]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- The **normalized output of Algorithm 3.5.1** of [golub2013matrix]. Let $\mathbb{K} = \mathbb{R}$
or $\mathbb{C}$, and let $T \in \mathbb{K}^{n \times n}$ be nonsingular. Then for every
$y \in \mathbb{K}^n$ with $y \neq 0$,
$$\Bigl\| T \frac{y}{\|y\|_\infty} \Bigr\|_\infty \ge \frac{1}{\|T^{-1}\|_\infty}.$$
This is the rigorous half of the book's statement $\|Ty\|_\infty \approx 1 / \|T^{-1}\|_\infty$
for the normalized output $y$.

The inequality is stated without division, as $1 \le \|T^{-1}\|_\infty \, \|T (y /
\|y\|_\infty)\|_\infty$. The vector norm is the sup norm of Mathlib, and the matrix norm is
`Matrix.lpOpNorm ⊤`. -/
theorem one_le_lpOpNorm_top_inv_mul_norm_mulVec_inv_norm_smul {T : Matrix n n 𝕜}
    (hT : IsUnit T) {y : n → 𝕜} (hy : y ≠ 0) :
    1 ≤ lpOpNorm ⊤ T⁻¹ * ‖T *ᵥ ((‖y‖⁻¹ : 𝕜) • y)‖ := by
  have h := norm_le_lpOpNorm_inv_mul_lpSeminorm_mulVec ⊤ hT ((‖y‖⁻¹ : 𝕜) • y)
  rwa [lpSeminorm_apply, lpSeminorm_apply, PiLp.norm_toLp, PiLp.norm_toLp, norm_smul,
    norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)] at h

end Matrix
