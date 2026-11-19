/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.Multiplier
import Numlib.Optimization.Subproblem.SecularIteration
import NumlibSurface.CartisGouldToint.Chapter08.Section01

/-!
# Cartis, Gould and Toint, Section 8.2: A digression on all things secular

This module formalizes Section 8.2 of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$, let
$H \in \mathbb{R}^{n \times n}$ be symmetric, and let $M \in \mathbb{R}^{n \times n}$ be symmetric
positive definite. For a shift $\lambda$ the step $s(\lambda)$ solves $(H + \lambda M) s = -g$
(8.2.2), and the secular function is $\pi(\lambda) = \|s(\lambda)\|_M^2$ (8.2.4). Let $\lambda_1$ be
the least eigenvalue of the pencil $(H, M)$ and $\lambda_s = \max(0, -\lambda_1)$. On
$(\lambda_s, \infty)$ the matrix $H + \lambda M$ is positive definite, and $\pi$ has the spectral
form (8.2.6)–(8.2.7). The section proves that the secular equation $\pi(\lambda) = \tau(\lambda)$
has a unique root for suitable targets $\tau$ (Lemma 8.2.1), Taylor bounds for $\pi$ (Theorem
8.2.2), the signs of the derivatives of the transformed secular function
$\pi(\lambda; \beta) = \pi(\lambda)^\beta$ and its monotonicity and convexity (Lemma 8.2.3,
Corollary 8.2.4), first-order Taylor bounds for $\pi(\lambda; \beta)$ (Theorem 8.2.5), a formula for
the derivatives of $\pi$ (Theorem 8.2.6), and the global optimality conditions of the trust-region
subproblem (8.1.2) and the regularization subproblem (8.1.3) (Theorems 8.2.7 and 8.2.8).

All proofs transport the operator backbone `Numlib.Optimization.Subproblem` through the $M$-inner
product space `Subproblem.ScaledSpace`. There, $\pi$ is the operator secular function of $M^{-1} g$
and $M^{-1} H$ for every $\lambda$ (`CartisGouldToint.Chapter08.secularFn_eq_secular`).

## Main definitions

* Equation (8.2.2), `CartisGouldToint.Chapter08.stepOf`: the step
  $s(\lambda) = -(H + \lambda M)^{-1} g$.
* Equation (8.2.4), `CartisGouldToint.Chapter08.secularFn`: the secular function $\pi(\lambda) =
  \langle s(\lambda), M s(\lambda) \rangle$.
* Equation (8.2.5), `CartisGouldToint.Chapter08.leftmostPencil`: the least eigenvalue $\lambda_1$ of
  the pencil $(H, M)$.
* Lemma 8.2.1, `CartisGouldToint.Chapter08.lambdaS`: the threshold
  $\lambda_s = \max(0, -\lambda_1)$.
* Lemma 8.2.1, `CartisGouldToint.Chapter08.IsAdmissibleTarget`: the hypotheses of Lemma 8.2.1 on a
  target $\tau$.
* Equation (8.2.12), `CartisGouldToint.Chapter08.secularTaylorPoly`: the Taylor polynomial
  $t_k(\delta)$ of $\pi$.
* Equation (8.2.29), `CartisGouldToint.Chapter08.secularDerivVec`: the vectors $s^{(k)}(\lambda)$.
* Equation (8.2.30), `CartisGouldToint.Chapter08.alphaCoeff`: the coefficients $\alpha_k$.
* Theorem 8.2.7, `CartisGouldToint.Chapter08.IsTrustRegionKKT`: the multiplier conditions
  (8.2.31)–(8.2.32) of the trust-region subproblem.

## Main results

* Equation (8.2.5), `CartisGouldToint.Chapter08.exists_pencil_eigenbasis`: there are $V$ and
  $\Lambda$ with $H V = M V \Lambda$ and $V^T M V = I$.
* Equations (8.2.6)–(8.2.7), `CartisGouldToint.Chapter08.secularFn_eq_sum`: $\pi(\lambda) = \sum_i
  (\gamma_i / (\lambda + \lambda_i))^2$ with $\gamma = V^T g$.
* Lemma 8.2.1, `CartisGouldToint.Chapter08.lemma_8_2_1` and
  `CartisGouldToint.Chapter08.IsAdmissibleTarget.lemma_8_2_1`: the secular equation
  $\pi(\lambda) = \tau(\lambda)$ has a unique root $\lambda_* > \lambda_s$.
* Equation (8.2.9), `CartisGouldToint.Chapter08.tau_admissible_8_2_9`: the targets $\Delta^2$ and
  $(\lambda / \sigma)^{2/(r-2)}$ satisfy the hypotheses of Lemma 8.2.1.
* Theorem 8.2.2, `CartisGouldToint.Chapter08.theorem_8_2_2` and
  `CartisGouldToint.Chapter08.theorem_8_2_2_strict`: the Taylor polynomials of $\pi$ are alternately
  upper and lower bounds (8.2.13)–(8.2.14).
* Lemma 8.2.3, `CartisGouldToint.Chapter08.lemma_8_2_3` and
  `CartisGouldToint.Chapter08.lemma_8_2_3_strict`: the signs of the first two derivatives of
  $\pi(\lambda; \beta)$.
* Corollary 8.2.4, `CartisGouldToint.Chapter08.corollary_8_2_4` and
  `CartisGouldToint.Chapter08.corollary_8_2_4_tendsto_lambdaS`: monotonicity, convexity and limits
  of $\pi(\lambda; \beta)$.
* Theorem 8.2.5, `CartisGouldToint.Chapter08.theorem_8_2_5` and
  `CartisGouldToint.Chapter08.theorem_8_2_5_strict`: the first-order Taylor bounds (8.2.20)–(8.2.21)
  for $\pi(\lambda; \beta)$.
* Theorem 8.2.6, `CartisGouldToint.Chapter08.theorem_8_2_6`: the derivatives (8.2.27)–(8.2.28) of
  $\pi$.
* Theorem 8.2.7, `CartisGouldToint.Chapter08.theorem_8_2_7`: a global minimizer of the trust-region
  subproblem has a multiplier, and it is unique if $H + \lambda_* M$ is positive definite.
* Theorem 8.2.8, `CartisGouldToint.Chapter08.theorem_8_2_8`: the same for the regularization
  subproblem, with $\lambda_* = \sigma \|s_*\|_M^{r-2}$.
* `CartisGouldToint.Chapter08.lambdaS_lt_iff`: for $n \ge 1$, $\lambda > \lambda_s$ if and only if
  $\lambda > 0$ and $H + \lambda M$ is positive definite.
* `CartisGouldToint.Chapter08.isTrustRegionSolution_of_kkt` and
  `CartisGouldToint.Chapter08.isRegularizationSolution_of_shifted`: the optimality conditions of
  Theorems 8.2.7 and 8.2.8 are also sufficient.

## Conventions

* "$H$ is symmetric" is `H.IsHermitian`, and "$M$ is positive definite" is `M.PosDef`.
* The eigenvalues of the pencil $(H, M)$ are `Matrix.pencilEigenvalues`. A generalized eigenvector
  $v$ of $(H, M)$ satisfies $H v = c M v$ for some $c \in \mathbb{R}$.
* The transformed secular function $\pi(\lambda; \beta)$ of (8.2.17) is `secularFn g H M λ ^ β`,
  with the real power `Real.rpow`.

## Implementation notes

* The step $s(\lambda)$ and $\pi(\lambda)$ are defined for every $\lambda$. Where $H + \lambda M$ is
  singular, the inverse is $0$ by the Mathlib convention, so that $s(\lambda) = 0$ and
  $\pi(\lambda) = 0$. These junk values occur at the poles of $\pi$.
* For $n = 0$ the least pencil eigenvalue $\lambda_1$ is $0$.

## Deviations from the source

* **Equations (8.2.2), (8.2.4) and (8.2.29)** (generalization). The inverse-based
  step, secular function and derivative-vector recursion all give zero at a singular
  shift. The results about the secular equation use nonsingular shifts or right limits.
  See `CartisGouldToint.Chapter08.stepOf` and `CartisGouldToint.Chapter08.secularDerivVec`.
* **Lemma 8.2.1** (reading). The hypothesis $\pi(\lambda_s) > \tau(\lambda_s)$ is read as
  $\pi(\lambda) \ge c > \tau(\lambda_s)$ for $\lambda$ near $\lambda_s$ from the right, and $\tau$
  is assumed right-continuous at $\lambda_s$. See `CartisGouldToint.Chapter08.lemma_8_2_1`.
* **Theorem 8.2.2** (generalization). The source states it for $k > 0$. It holds for every
  $k \ge 0$. See `CartisGouldToint.Chapter08.theorem_8_2_2`.
* **Lemma 8.2.3** (correction). The second derivative can vanish with $g\ne0$ at
  $\beta=-1/2$ when $g = M v$ for a generalized eigenvector $v$. See
  `CartisGouldToint.Chapter08.lemma_8_2_3_strict`.
* **Corollary 8.2.4** (correction). The statement needs $g \neq 0$; for $g = 0$ the function
  $\pi(\lambda; \beta)$ is constant. See `CartisGouldToint.Chapter08.corollary_8_2_4`.
* **Corollary 8.2.4** (reading). The starting value "$\pi(\lambda_s; \beta)$" is the right limit at
  $\lambda_s$, which can be $+\infty$. See
  `CartisGouldToint.Chapter08.corollary_8_2_4_tendsto_lambdaS`.
* **Theorem 8.2.5** (correction). The strict inequalities fail for $\delta = 0$, and
  (8.2.21) is an equality for $\beta = -1/2$ when $g = M v$ for a generalized eigenvector $v$. See
  `CartisGouldToint.Chapter08.theorem_8_2_5_strict`.
* **Section 8.2.2, transformed secular equations** (correction). The interval following
  (8.2.17) should start at $\lambda_s$, as in Lemma 8.2.3. For $\gamma<0$ the
  concavity assertion for $-\lambda^\gamma$ uses $\lambda>0$. The endpoint
  $\lambda_s=0$ is allowed for the convex case $\gamma\in(0,1]$.
* **Theorem 8.2.8, uniqueness proof** (correction). Positive definiteness of the shifted
  matrix can hold at $\lambda_*=\lambda_s=0$, for example when $g=0$ and $H$ is positive
  definite. The Lean uniqueness proof includes this case.
-/

open Matrix Set Filter Topology
open Finset (range)
open scoped Nat RealInnerProductSpace

namespace CartisGouldToint.Chapter08

open Subproblem

variable {n : ℕ}

/-! ### The step and the secular function -/

/-- **Equation (8.2.2)** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$,
$H, M \in \mathbb{R}^{n \times n}$ and $\lambda \in \mathbb{R}$. The **step** is
$$s(\lambda) = (H + \lambda M)^{-1} (-g).$$
If $H + \lambda M$ is nonsingular, $s(\lambda)$ is the solution of $(H + \lambda M) s = -g$.

If $H + \lambda M$ is singular, the Mathlib convention $A^{-1} = 0$ gives $s(\lambda) = 0$.

**Reading.** Uses the inverse solution formula and assigns zero at singular shifts, where the source
equation can be underdetermined or inconsistent.
-/
noncomputable def stepOf (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin (H + lam • M)⁻¹ (-g)

/-- The definition of the step, unfolded: $s(\lambda) = (H + \lambda M)^{-1} (-g)$.

**Reading.** Unfolds the same totalized inverse step.
-/
theorem stepOf_def (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    stepOf g H M lam = toEuclideanLin (H + lam • M)⁻¹ (-g) :=
  rfl

/-- **Equation (8.2.4)** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$,
$H, M \in \mathbb{R}^{n \times n}$ and $\lambda \in \mathbb{R}$. The **secular function** is
$$\pi(\lambda) = \langle s(\lambda), M s(\lambda) \rangle,$$
which is $\|s(\lambda)\|_M^2$ for a positive definite $M$.

The transformed secular function $\pi(\lambda; \beta)$ of (8.2.17) is
`CartisGouldToint.Chapter08.secularFn g H M λ ^ β`. Where $H + \lambda M$ is singular,
$s(\lambda) = 0$ and so $\pi(\lambda) = 0$.

**Reading.** Matches the inner-product secular formula and assigns zero at singular shifts under the
matrix inverse convention.
-/
noncomputable def secularFn (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) : ℝ :=
  ⟪stepOf g H M lam, toEuclideanLin M (stepOf g H M lam)⟫

/-- The definition of the secular function, unfolded: $\pi(\lambda) = \langle s(\lambda), M
s(\lambda) \rangle$.

**Generalization.** Unfolds the secular form over the generalized domain.
-/
theorem secularFn_def (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    secularFn g H M lam = ⟪stepOf g H M lam, toEuclideanLin M (stepOf g H M lam)⟫ :=
  rfl

/-- **Equation (8.2.5)** of [cartis2022evaluation], the leftmost eigenvalue. Let $H$ be symmetric
and $M$ be positive definite. The **leftmost eigenvalue** $\lambda_1$ of the pencil $(H, M)$ is
the least of the eigenvalues `Matrix.pencilEigenvalues`, that is, the least $\lambda$ with
$H v = \lambda M v$ for some $v \neq 0$.

For $n = 0$ the value is $0$, the infimum of the empty family in Mathlib.

**Reading.** Same least eigenvalue for positive dimension; the empty family is assigned infimum
zero.
-/
noncomputable def leftmostPencil {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian)
    (hM : M.PosDef) : ℝ :=
  ⨅ i, pencilEigenvalues hH hM i

/-- **Lemma 8.2.1** of [cartis2022evaluation], the threshold. Let $H$ be symmetric and $M$ be
positive definite, with leftmost pencil eigenvalue $\lambda_1$. The **threshold** is
$$\lambda_s = \max(0, -\lambda_1).$$

**Reading.** Same maximum of zero and the negative least eigenvalue, including the totalized
zero-dimensional value.
-/
noncomputable def lambdaS {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian)
    (hM : M.PosDef) : ℝ :=
  max 0 (-leftmostPencil hH hM)

/-- The definition of the threshold, unfolded: $\lambda_s = \max(0, -\lambda_1)$.

**Reading.** Unfolds the same threshold for all dimensions.
-/
theorem lambdaS_def {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) (hM : M.PosDef) :
    lambdaS hH hM = max 0 (-leftmostPencil hH hM) :=
  rfl

variable {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The leftmost eigenvalue of the pencil $(H, M)$ is the leftmost eigenvalue `Subproblem.leftmost`
of the scaled operator $M^{-1} H$ on the $M$-inner product space.

**Reading.** Identifies the least pencil eigenvalue with the least scaled-operator eigenvalue, also
with the empty infimum convention.
-/
theorem leftmostPencil_eq (hH : H.IsHermitian) (hM : M.PosDef) :
    leftmostPencil hH hM = leftmost (isSymmetric_scaledOp (hM := hM) hH) :=
  (leftmost_scaledOp hH).symm

/-- The threshold $\lambda_s$ is the shift threshold `Subproblem.shiftThreshold` of the scaled
operator $M^{-1} H$ on the $M$-inner product space.

**Generalization.** Identifies the generalized threshold with its scaled-operator counterpart.
-/
theorem lambdaS_eq (hH : H.IsHermitian) (hM : M.PosDef) :
    lambdaS hH hM = shiftThreshold (isSymmetric_scaledOp (hM := hM) hH) := by
  rw [lambdaS, shiftThreshold, leftmostPencil_eq]

/-- The threshold is nonnegative: $\lambda_s \ge 0$. -/
theorem lambdaS_nonneg (hH : H.IsHermitian) (hM : M.PosDef) : 0 ≤ lambdaS hH hM :=
  le_max_left _ _

/-- The threshold is at least $-\lambda_1$: $-\lambda_1 \le \lambda_s$. -/
theorem neg_leftmostPencil_le_lambdaS (hH : H.IsHermitian) (hM : M.PosDef) :
    -leftmostPencil hH hM ≤ lambdaS hH hM :=
  le_max_right _ _

/-- If $\lambda > \lambda_s$, then $\lambda > -\lambda_1$, where $\lambda_1$ is the leftmost
eigenvalue of the scaled operator $M^{-1} H$. -/
theorem neg_leftmost_lt_of_lambdaS_lt (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (h : lambdaS hH hM < lam) : -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam := by
  rw [lambdaS_eq] at h
  exact (neg_leftmost_le_shiftThreshold).trans_lt h

/-- Let $n \ge 1$, let $H$ be symmetric and let $M$ be positive definite. Then for every
$\lambda \in \mathbb{R}$,
$$\lambda > \lambda_s \iff \lambda > 0 \text{ and } H + \lambda M \text{ is positive
  definite}.$$
-/
theorem lambdaS_lt_iff [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ} :
    lambdaS hH hM < lam ↔ 0 < lam ∧ (H + lam • M).PosDef := by
  rw [lambdaS, max_lt_iff, (posDef_add_smul_iff_scaled hH lam).2, leftmostPencil_eq]

/-- Let $M$ be positive definite. For every $\lambda \in \mathbb{R}$, the step $s(\lambda)$, carried
into the $M$-inner product space, is the operator step `Subproblem.step` of $M^{-1} g$ and
$M^{-1} H$ at $\lambda$. This holds also where $H + \lambda M$ is singular, since both steps are
then $0$.

**Reading.** Rewrites the same solution in the scaled space, including the totalized inverse at
singularity.
-/
theorem toScaled_stepOf (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (lam : ℝ) :
    toScaled hM (stepOf g H M lam) = step (scaledGrad hM g) (scaledOp H hM) lam :=
  toScaled_step g lam

/-- Let $M$ be positive definite. As functions of $\lambda$ on all of $\mathbb{R}$, the secular
function $\pi$ equals the operator secular function `Subproblem.secular` of $M^{-1} g$ and
$M^{-1} H$ in the $M$-inner product space.

This is the bridge through which every result of this module is proved from the operator
backbone.

**Reading.** Rewrites the same secular inner product in the scaled space using totalized inverse.
-/
theorem secularFn_eq_secular (hM : M.PosDef) :
    secularFn g H M = secular (scaledGrad hM g) (scaledOp H hM) := by
  funext lam
  rw [secular_scaled g lam, secularFn, stepOf, real_inner_comm]

/-- Let $M$ be positive definite. For every $\lambda$, $\|s(\lambda)\|_M^2 = \pi(\lambda)$.

**Reading.** Matches the squared-norm identity for positive-definite M even where the inverse step
is totalized.
-/
theorem mNorm_stepOf_sq (hM : M.PosDef) (lam : ℝ) :
    mNorm M (stepOf g H M lam) ^ 2 = secularFn g H M lam :=
  mNorm_sq hM _

/-- Let $M$ be positive definite. Then $\pi(\lambda) \ge 0$ for every $\lambda$.

**Reading.** Proves nonnegativity, allowing zero at g=0 and at singular shifts.
-/
theorem secularFn_nonneg (hM : M.PosDef) (lam : ℝ) : 0 ≤ secularFn g H M lam := by
  rw [← mNorm_stepOf_sq hM]; positivity

/-- Let $H$ be symmetric and $M$ be positive definite. If $\lambda > -\lambda_1$, where $\lambda_1$
is the leftmost eigenvalue of the scaled operator $M^{-1} H$, then the step solves (8.2.2):
$(H + \lambda M) s(\lambda) = -g$. -/
theorem add_smul_stepOf (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hlam : -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam) :
    toEuclideanLin (H + lam • M) (stepOf g H M lam) = -g := by
  have := (step_spec (hH := isSymmetric_scaledOp (hM := hM) hH) (g := scaledGrad hM g) hlam).1
  rw [← toScaled_stepOf hM] at this
  exact (add_smul_scaledOp_toScaled_eq_neg_iff lam g _).1 this

/-- For $n = 0$ the secular function is identically $0$. -/
theorem secularFn_of_isEmpty [IsEmpty (Fin n)] : secularFn g H M = fun _ => 0 := by
  funext lam
  rw [secularFn, Subsingleton.elim (stepOf g H M lam) 0, inner_zero_left]

/-- Let $n \ge 1$, let $H$ be symmetric and let $M$ be positive definite. If $H + \lambda M$ is
positive definite, then $\lambda > -\lambda_1$, where $\lambda_1$ is the leftmost eigenvalue of
the scaled operator $M^{-1} H$. -/
theorem neg_leftmost_lt_of_posDef [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (h : (H + lam • M).PosDef) : -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam :=
  ((posDef_add_smul_iff_scaled hH lam).2).1 h

/-! ### The spectral form (8.2.6)–(8.2.7) -/

/-- **Equations (8.2.6)–(8.2.7)** of [cartis2022evaluation]. Let $H \in \mathbb{R}^{n \times n}$,
let $M$ be positive definite, and let $V \in \mathbb{R}^{n \times n}$ and $\mu \in \mathbb{R}^n$
satisfy
$$H V = M V \operatorname{diag}(\mu), \qquad V^T M V = I$$
as in (8.2.5). Let $\gamma = V^T g$. If $\lambda + \mu_i \neq 0$ for every $i$, then
$$(V^T M s(\lambda))_i = -\frac{\gamma_i}{\lambda + \mu_i} \quad \text{for every } i, \qquad
  \pi(\lambda) = \sum_i \left(\frac{\gamma_i}{\lambda + \mu_i}\right)^2.$$

The source writes $\Lambda = \operatorname{diag}(\mu)$ and $\lambda_i$ for $\mu_i$. The
statement does not need $H$ to be symmetric;
`CartisGouldToint.Chapter08.exists_pencil_eigenbasis` gives $V$ and $\mu$ when it is. -/
theorem secularFn_eq_sum (hM : M.PosDef) {V : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hV : H * V = M * V * diagonal μ) (hVM : Vᵀ * M * V = 1) {lam : ℝ}
    (hlam : ∀ i, lam + μ i ≠ 0) :
    (∀ i, toEuclideanLin (Vᵀ * M) (stepOf g H M lam) i =
        -(toEuclideanLin Vᵀ g i) / (lam + μ i)) ∧
      secularFn g H M lam = ∑ i, (toEuclideanLin Vᵀ g i / (lam + μ i)) ^ 2 := by
  set Dinv : Matrix (Fin n) (Fin n) ℝ := diagonal fun i => (lam + μ i)⁻¹
  have hMt : Mᵀ = M := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hM.isHermitian.eq
  have hV1 : V * (Vᵀ * M) = 1 := mul_eq_one_comm.1 hVM
  have hMVV : M * V * Vᵀ = 1 := by
    have := congrArg transpose hV1
    rwa [transpose_mul, transpose_mul, transpose_transpose, hMt, transpose_one] at this
  have hd : (diagonal μ + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) * Dinv = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Dinv, add_comm (μ i), hlam i]
    · simp [Dinv, h]
  have hX : (H + lam • M) * (V * Dinv * Vᵀ) = 1 := by
    calc (H + lam • M) * (V * Dinv * Vᵀ)
        = (H * V + lam • (M * V)) * Dinv * Vᵀ := by
          simp only [add_mul, smul_mul_assoc, mul_assoc]
      _ = M * V * ((diagonal μ + lam • 1) * Dinv) * Vᵀ := by
          rw [hV]; simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            one_mul, mul_assoc]
      _ = 1 := by rw [hd, mul_one, hMVV]
  have hinv : (H + lam • M)⁻¹ = V * Dinv * Vᵀ := inv_eq_right_inv hX
  -- the coordinates `y = Vᵀ M s(λ)`
  set y := toEuclideanLin (Vᵀ * M) (stepOf g H M lam) with hy
  have hy' : y = toEuclideanLin Dinv (toEuclideanLin Vᵀ (-g)) := by
    rw [hy, stepOf, hinv, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      show Vᵀ * M * (V * Dinv * Vᵀ) = Vᵀ * M * V * Dinv * Vᵀ by simp only [mul_assoc],
      hVM, one_mul]
  have hyi : ∀ i, y i = -(toEuclideanLin Vᵀ g i) / (lam + μ i) := fun i => by
    rw [hy', map_neg, map_neg]
    simp [Dinv, toEuclideanLin_apply, -mulVec_mulVec, mulVec_diagonal, div_eq_inv_mul]
  refine ⟨hyi, ?_⟩
  have hs : stepOf g H M lam = toEuclideanLin V y := by
    rw [hy, ← toEuclideanLin_mul_apply, hV1, toEuclideanLin_one_apply]
  have hsec : secularFn g H M lam = ⟪y, y⟫ := by
    rw [secularFn, hs, ← toEuclideanLin_transpose_inner_right, ← toEuclideanLin_mul_apply,
      ← toEuclideanLin_mul_apply, hVM, toEuclideanLin_one_apply]
  rw [hsec, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hyi, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, neg_div, neg_sq]

/-- **Equation (8.2.5)** of [cartis2022evaluation], existence of the generalized eigenvectors. Let
$H$ be symmetric and $M$ be positive definite. Then there are $V \in \mathbb{R}^{n \times n}$
and $\mu \in \mathbb{R}^n$ with
$$H V = M V \operatorname{diag}(\mu), \qquad V^T M V = I.$$

With these, `CartisGouldToint.Chapter08.secularFn_eq_sum` applies. -/
theorem exists_pencil_eigenbasis (hH : H.IsHermitian) (hM : M.PosDef) :
    ∃ (V : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ),
      H * V = M * V * diagonal μ ∧ Vᵀ * M * V = 1 := by
  obtain ⟨V, d, -, h1, h2, -⟩ := Matrix.exists_simultaneous_diagonalization hH hM
  have hs : star V = Vᵀ := by rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hs] at h1 h2
  have hMt : Mᵀ = M := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hM.isHermitian.eq
  have hV1 : V * (Vᵀ * M) = 1 := mul_eq_one_comm.1 h1
  have hMVV : M * V * Vᵀ = 1 := by
    have := congrArg transpose hV1
    rwa [transpose_mul, transpose_mul, transpose_transpose, hMt, transpose_one] at this
  refine ⟨V, d, ?_, h1⟩
  calc H * V = M * V * Vᵀ * H * V := by rw [hMVV, one_mul]
    _ = M * V * (Vᵀ * H * V) := by simp only [mul_assoc]
    _ = M * V * diagonal d := by rw [h2]; rfl

/-- The interval $(\lambda_s, \infty)$ is contained in $(-\lambda_1, \infty)$, where $\lambda_1$ is
the leftmost eigenvalue of the scaled operator $M^{-1} H$. -/
theorem Ioi_lambdaS_subset (hH : H.IsHermitian) (hM : M.PosDef) :
    Ioi (lambdaS hH hM) ⊆ Ioi (-leftmost (isSymmetric_scaledOp (hM := hM) hH)) :=
  fun _ h => neg_leftmost_lt_of_lambdaS_lt hH hM h

/-! ### The root of the secular equation -/

/-- **Lemma 8.2.1** of [cartis2022evaluation] (root of the secular equation). Let
$g \in \mathbb{R}^n$, let $H$ be symmetric and let $M$ be positive definite. Let
$\tau : \mathbb{R} \to \mathbb{R}$ be nonnegative, nondecreasing and continuous on
$(\lambda_s, \infty)$, not identically zero there, and right-continuous at $\lambda_s$. Suppose
that there is $c > \tau(\lambda_s)$ with $\pi(\lambda) \ge c$ for all $\lambda > \lambda_s$ near
$\lambda_s$. Then the secular equation
$$\pi(\lambda) = \tau(\lambda) \qquad (8.2.8)$$
has exactly one root $\lambda_* > \lambda_s$.

**Reading.** The source assumes $\pi(\lambda_s) > \tau(\lambda_s)$. Since $\lambda_s$ can be a
pole of $\pi$, where the inverse convention sets `CartisGouldToint.Chapter08.secularFn` to zero,
this is read as the bound on $\pi$ near $\lambda_s$ from the right. The source assumes continuity of
$\tau$ only on $(\lambda_s, \infty)$ but uses $\tau(\lambda_s)$; the statement assumes
right-continuity at $\lambda_s$, which also gives $\tau(\lambda_s) \ge 0$.
For $H=M=g=1$, the threshold is $0$ and $\pi(\lambda)=(1+\lambda)^{-2}$.
The source's strict endpoint comparison holds with $\tau(0)=0$ and $\tau(\lambda)=2$
for $\lambda>0$, although the equation has no root on $(0,\infty)$. -/
theorem lemma_8_2_1 (hH : H.IsHermitian) (hM : M.PosDef) {τ : ℝ → ℝ}
    (hτ0 : ∀ lam ∈ Ioi (lambdaS hH hM), 0 ≤ τ lam) (hτm : MonotoneOn τ (Ioi (lambdaS hH hM)))
    (hτc : ContinuousOn τ (Ioi (lambdaS hH hM)))
    (hτne : ∃ lam ∈ Ioi (lambdaS hH hM), τ lam ≠ 0)
    (hτs : ContinuousWithinAt τ (Ici (lambdaS hH hM)) (lambdaS hH hM))
    (hπ : ∃ c > τ (lambdaS hH hM), ∀ᶠ lam in 𝓝[>] (lambdaS hH hM), c ≤ secularFn g H M lam) :
    ∃! lamStar, lambdaS hH hM < lamStar ∧ secularFn g H M lamStar = τ lamStar := by
  obtain ⟨c, hc, hev⟩ := hπ
  have hτlt : ∀ᶠ lam in 𝓝[>] (lambdaS hH hM), τ lam < c :=
    (hτs.mono Ioi_subset_Ici_self).eventually (gt_mem_nhds hc)
  have hleft := (hτlt.and hev).mono fun lam h => h.1.trans_le h.2
  rw [secularFn_eq_secular hM] at hleft ⊢
  rw [lambdaS_eq] at hτ0 hτm hτc hτne hleft ⊢
  obtain ⟨lamStar, hgt, heq, -, -, huniq⟩ := existsUnique_secular_root hτc hτm hτ0 hτne hleft
  exact ⟨lamStar, ⟨hgt, heq⟩, fun lam h => huniq lam h.1 h.2⟩

/-- The hypotheses of Lemma 8.2.1 on a target $\tau : \mathbb{R} \to \mathbb{R}$ with threshold $a$,
which stands for $\lambda_s$. The target $\tau$ is **admissible** if it is nonnegative,
nondecreasing and continuous on $[a, \infty)$, and not identically zero on $(a, \infty)$.

Continuity on the closed half-line contains the right-continuity at $a$ that
`CartisGouldToint.Chapter08.lemma_8_2_1` needs. The structure is the hypothesis of
`CartisGouldToint.Chapter08.IsAdmissibleTarget.lemma_8_2_1`.

**Reading.** Requires continuity on the closed half-line to include the needed right endpoint
behavior.
-/
structure IsAdmissibleTarget (a : ℝ) (τ : ℝ → ℝ) : Prop where
  /-- The target is nonnegative on $[a, \infty)$. -/
  nonneg : ∀ lam ∈ Ici a, 0 ≤ τ lam
  /-- The target is nondecreasing on $[a, \infty)$. -/
  monotoneOn : MonotoneOn τ (Ici a)
  /-- The target is continuous on $[a, \infty)$, and so right-continuous at $a$. -/
  continuousOn : ContinuousOn τ (Ici a)
  /-- The target is not identically zero on $(a, \infty)$. -/
  exists_ne_zero : ∃ lam ∈ Ioi a, τ lam ≠ 0

/-- **Equation (8.2.9)** of [cartis2022evaluation]. Let $H$ be symmetric and $M$ be positive
definite. For every $\Delta > 0$ the trust-region target $\tau(\lambda) = \Delta^2$, and for
every $\sigma > 0$ and $r > 2$ the regularization target
$$\tau(\lambda) = \left(\frac{\lambda}{\sigma}\right)^{2/(r-2)},$$
are admissible targets with threshold $\lambda_s$
(`CartisGouldToint.Chapter08.IsAdmissibleTarget`). The shift-to-norm exponent in the
regularization example requires $r>2$. The comparison with the data-dependent $\pi$ at
the left endpoint is a separate hypothesis of Lemma 8.2.1.

**Reading.** Establishes shape and right continuity for the two targets with r>2 in the
regularization case; the endpoint domination condition remains separate.
-/
theorem tau_admissible_8_2_9 (hH : H.IsHermitian) (hM : M.PosDef) :
    (∀ Δ : ℝ, 0 < Δ → IsAdmissibleTarget (lambdaS hH hM) fun _ => Δ ^ 2) ∧
      ∀ σ r : ℝ, 0 < σ → 2 < r →
        IsAdmissibleTarget (lambdaS hH hM) fun lam => (lam / σ) ^ (2 / (r - 2)) := by
  refine ⟨fun Δ hΔ => ⟨fun _ _ => sq_nonneg Δ, monotoneOn_const, continuousOn_const,
    ⟨lambdaS hH hM + 1, by simp, by positivity⟩⟩, fun σ r hσ hr => ?_⟩
  have hp : 0 ≤ 2 / (r - 2) := div_nonneg zero_le_two (sub_pos.2 hr).le
  have hs := lambdaS_nonneg hH hM
  refine ⟨fun lam hlam => Real.rpow_nonneg (div_nonneg (hs.trans hlam) hσ.le) _,
    (monotoneOn_regTarget hσ hr).mono fun x hx => hs.trans hx,
    ((continuous_id.div_const σ).rpow_const fun _ => Or.inr hp).continuousOn,
    ⟨lambdaS hH hM + 1, by simp, (Real.rpow_pos_of_pos (by positivity) _).ne'⟩⟩

/-- **Lemma 8.2.1** of [cartis2022evaluation], for an admissible target. Let $g \in \mathbb{R}^n$,
let $H$ be symmetric and let $M$ be positive definite. Let $\tau$ be an admissible target with
threshold $\lambda_s$, for example one of the targets (8.2.9). Suppose that there is
$c > \tau(\lambda_s)$ with $\pi(\lambda) \ge c$ for all $\lambda > \lambda_s$ near $\lambda_s$.
Then the secular equation $\pi(\lambda) = \tau(\lambda)$ has exactly one root
$\lambda_* > \lambda_s$.

**Reading.** As in `CartisGouldToint.Chapter08.lemma_8_2_1`, the hypothesis
$\pi(\lambda_s) > \tau(\lambda_s)$ of the source is read as a bound on $\pi$ near $\lambda_s$
from the right. -/
theorem IsAdmissibleTarget.lemma_8_2_1 (hH : H.IsHermitian) (hM : M.PosDef) {τ : ℝ → ℝ}
    (hτ : IsAdmissibleTarget (lambdaS hH hM) τ)
    (hπ : ∃ c > τ (lambdaS hH hM), ∀ᶠ lam in 𝓝[>] (lambdaS hH hM), c ≤ secularFn g H M lam) :
    ∃! lamStar, lambdaS hH hM < lamStar ∧ secularFn g H M lamStar = τ lamStar :=
  CartisGouldToint.Chapter08.lemma_8_2_1 hH hM (fun lam h => hτ.nonneg lam (mem_Ici_of_Ioi h))
    (hτ.monotoneOn.mono Ioi_subset_Ici_self) (hτ.continuousOn.mono Ioi_subset_Ici_self)
    hτ.exists_ne_zero (hτ.continuousOn _ (mem_Ici.2 le_rfl)) hπ

/-! ### Taylor estimates -/

/-- **Equation (8.2.12)** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$,
$H, M \in \mathbb{R}^{n \times n}$, $k \in \mathbb{N}$ and $\lambda_c \in \mathbb{R}$. The
$k$-th order **Taylor polynomial of the secular function** at $\lambda_c$ is
$$t_k(\delta) = \sum_{j=0}^{k} \frac{\pi^{(j)}(\lambda_c)}{j!} \delta^j.$$

The derivatives are `iteratedDeriv` of `CartisGouldToint.Chapter08.secularFn`. -/
noncomputable def secularTaylorPoly (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (lamc δ : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), iteratedDeriv j (secularFn g H M) lamc / j ! * δ ^ j

/-- Let $M$ be positive definite. The Taylor polynomial $t_k(\delta)$ of $\pi$ is the Taylor
polynomial `Subproblem.secularTaylor` of the operator secular function of $M^{-1} g$ and
$M^{-1} H$. -/
theorem secularTaylorPoly_eq (hM : M.PosDef) (k : ℕ) (lamc δ : ℝ) :
    secularTaylorPoly g H M k lamc δ =
      secularTaylor (scaledGrad hM g) (scaledOp H hM) k lamc δ := by
  rw [secularTaylorPoly, secularTaylor, secularFn_eq_secular hM]

/-- **Theorem 8.2.2** of [cartis2022evaluation] (lower and upper Taylor estimates of $\pi$). Let
$g \in \mathbb{R}^n$, let $H$ be symmetric, let $M$ be positive definite, let
$\lambda_c > \lambda_s$, and let $k \in \mathbb{N}$. For every $\delta > 0$,
$$\pi(\lambda_c + \delta) \le t_k(\delta) \text{ if } k \text{ is even}, \qquad \pi(\lambda_c +
  \delta) \ge t_k(\delta) \text{ if } k \text{ is odd}. \qquad (8.2.13)$$
For every $\delta$ with $\lambda_s - \lambda_c < \delta < 0$,
$$\pi(\lambda_c + \delta) \ge t_{k+1}(\delta) \ge t_k(\delta). \qquad (8.2.14)$$

**Generalization.** The source states the theorem for $k > 0$. It holds for $k = 0$ as well.

The strict form for $g \neq 0$ is `CartisGouldToint.Chapter08.theorem_8_2_2_strict`. -/
theorem theorem_8_2_2 (hH : H.IsHermitian) (hM : M.PosDef) {lamc : ℝ}
    (hc : lambdaS hH hM < lamc) (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secularFn g H M (lamc + δ) ≤ secularTaylorPoly g H M k lamc δ) ∧
      (Odd k → secularTaylorPoly g H M k lamc δ ≤ secularFn g H M (lamc + δ))) ∧
    (∀ δ, lambdaS hH hM - lamc < δ → δ < 0 →
      secularTaylorPoly g H M k lamc δ ≤ secularTaylorPoly g H M (k + 1) lamc δ ∧
        secularTaylorPoly g H M (k + 1) lamc δ ≤ secularFn g H M (lamc + δ)) := by
  have h := secular_taylor_bounds (g := scaledGrad hM g) (neg_leftmost_lt_of_lambdaS_lt hH hM hc) k
  simp only [secularTaylorPoly, secularFn_eq_secular hM]
  exact ⟨h.1, fun δ hδ1 hδ2 => h.2 δ hδ2 (neg_leftmost_lt_of_lambdaS_lt hH hM (by linarith))⟩

/-- **Theorem 8.2.2** of [cartis2022evaluation], strict form. Let $g \neq 0$, let $H$ be symmetric,
let $M$ be positive definite, let $\lambda_c > \lambda_s$, and let $k \in \mathbb{N}$. Then the
inequalities (8.2.13) and (8.2.14) are strict: for every $\delta > 0$,
$\pi(\lambda_c + \delta) < t_k(\delta)$ if $k$ is even and
$\pi(\lambda_c + \delta) > t_k(\delta)$ if $k$ is odd; for every $\delta$ with
$\lambda_s - \lambda_c < \delta < 0$, $\pi(\lambda_c + \delta) > t_{k+1}(\delta) > t_k(\delta)$.

**Reading.** Matches strict estimates for a nonzero gradient and also proves them at degree zero.
-/
theorem theorem_8_2_2_strict (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {lamc : ℝ}
    (hc : lambdaS hH hM < lamc) (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secularFn g H M (lamc + δ) < secularTaylorPoly g H M k lamc δ) ∧
      (Odd k → secularTaylorPoly g H M k lamc δ < secularFn g H M (lamc + δ))) ∧
    (∀ δ, lambdaS hH hM - lamc < δ → δ < 0 →
      secularTaylorPoly g H M k lamc δ < secularTaylorPoly g H M (k + 1) lamc δ ∧
        secularTaylorPoly g H M (k + 1) lamc δ < secularFn g H M (lamc + δ)) := by
  have h := secular_taylor_bounds_strict (scaledGrad_ne_zero (hM := hM) hg)
    (neg_leftmost_lt_of_lambdaS_lt hH hM hc) k
  simp only [secularTaylorPoly, secularFn_eq_secular hM]
  exact ⟨h.1, fun δ hδ1 hδ2 => h.2 δ hδ2 (neg_leftmost_lt_of_lambdaS_lt hH hM (by linarith))⟩

/-! ### The transformed secular function -/

/-- **Lemma 8.2.3** of [cartis2022evaluation] (derivatives of $\pi(\lambda; \beta)$). Let
$g \in \mathbb{R}^n$, let $H$ be symmetric, let $M$ be positive definite, let
$\lambda > \lambda_s$, and let $\beta \in \mathbb{R}$. Write $\pi^{(j)}(\lambda; \beta)$ for the
$j$-th derivative of $\pi(\cdot; \beta) = \pi(\cdot)^\beta$. Then:

* (i) $\pi^{(1)}(\lambda; \beta) \le 0$ if $\beta > 0$, and $\pi^{(1)}(\lambda; \beta) \ge 0$ if
  $\beta < 0$;
* (ii) $\pi^{(2)}(\lambda; \beta) \ge 0$ if $\beta > 0$, and $\pi^{(2)}(\lambda; \beta) \le 0$
  if $\beta \in [-1/2, 0)$.

The strict form is `CartisGouldToint.Chapter08.lemma_8_2_3_strict`. -/
theorem lemma_8_2_3 (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hlam : lambdaS hH hM < lam) (β : ℝ) :
    (0 < β → deriv (fun t => secularFn g H M t ^ β) lam ≤ 0) ∧
    (β < 0 → 0 ≤ deriv (fun t => secularFn g H M t ^ β) lam) ∧
    (0 < β → 0 ≤ iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam) ∧
    (β ∈ Ico (-1 / 2) 0 → iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam ≤ 0) := by
  rw [secularFn_eq_secular hM]
  rcases eq_or_ne g 0 with rfl | hg
  · have h1 : deriv (fun t => secular 0 (scaledOp H hM) t ^ β) lam = 0 := by
      rw [← iteratedDeriv_one]; exact secular_rpow_zero_left _ β lam 0
    have h2 : iteratedDeriv 2 (fun t => secular 0 (scaledOp H hM) t ^ β) lam = 0 :=
      secular_rpow_zero_left _ β lam 1
    rw [scaledGrad_zero, h1, h2]
    exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := secular_rpow_deriv_sign (scaledGrad_ne_zero (hM := hM) hg)
      (neg_leftmost_lt_of_lambdaS_lt hH hM hlam) β
    exact ⟨fun h => (h1 h).le, fun h => (h2 h).le, fun h => (h3 h).le, h4⟩

/-- **Lemma 8.2.3** of [cartis2022evaluation], strict form. Let $g \neq 0$, let $H$ be symmetric,
let $M$ be positive definite, let $\lambda > \lambda_s$, and let $\beta \in \mathbb{R}$. Then
$\pi^{(1)}(\lambda; \beta) < 0$ if $\beta > 0$, $\pi^{(1)}(\lambda; \beta) > 0$ if $\beta < 0$,
and $\pi^{(2)}(\lambda; \beta) > 0$ if $\beta > 0$. For $\beta \in [-1/2, 0)$: if
$\beta \neq -1/2$, or if there is no generalized eigenvector $v$ of $(H, M)$ with $M v = g$,
then $\pi^{(2)}(\lambda; \beta) < 0$; if $\beta = -1/2$ and $M v = g$ for a generalized
eigenvector $v$, then $\pi^{(2)}(\lambda; \beta) = 0$.

**Correction.** The source claims that all the inequalities of the lemma are strict. This fails
for $g = 0$, where $\pi(\lambda; \beta)$ is constant. It also fails for $\beta = -1/2$ when
$g = M v$ for a generalized eigenvector $v$ of $(H, M)$, because $\pi(\lambda; -1/2)$ is then
affine in $\lambda$: for $n = 1$, $H = 0$, $M = 1$ and $g = 1$, $\pi(\lambda; -1/2) = \lambda$.
The statement excludes these cases and identifies the second one exactly.

A generalized eigenvector is encoded as a vector $v$ and a scalar $c$ with $H v = c M v$. -/
theorem lemma_8_2_3_strict (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {lam : ℝ}
    (hlam : lambdaS hH hM < lam) (β : ℝ) :
    (0 < β → deriv (fun t => secularFn g H M t ^ β) lam < 0) ∧
    (β < 0 → 0 < deriv (fun t => secularFn g H M t ^ β) lam) ∧
    (0 < β → 0 < iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam) ∧
    (β ∈ Ico (-1 / 2) 0 → (β ≠ -1 / 2 ∨ ¬ ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
        toEuclideanLin M v = g ∧ toEuclideanLin H v = c • toEuclideanLin M v) →
      iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam < 0) ∧
    (β = -1 / 2 → (∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
        toEuclideanLin M v = g ∧ toEuclideanLin H v = c • toEuclideanLin M v) →
      iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam = 0) := by
  rw [secularFn_eq_secular hM, ← exists_scaledOp_scaledGrad_eq_iff (hM := hM)]
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := secular_rpow_deriv_sign (scaledGrad_ne_zero (hM := hM) hg)
    (neg_leftmost_lt_of_lambdaS_lt hH hM hlam) β
  exact ⟨h1, h2, h3, h5, h6⟩

/-- **Corollary 8.2.4** of [cartis2022evaluation] (monotonicity of the transformed secular
function). Let $g \neq 0$, let $H$ be symmetric, let $M$ be positive definite, and let
$\beta \in \mathbb{R}$. On $(\lambda_s, \infty)$:

* if $\beta > 0$, then $\pi(\lambda; \beta)$ is strictly decreasing and strictly convex, and
  $\pi(\lambda; \beta) \to 0$ as $\lambda \to +\infty$;
* if $\beta \in [-1/2, 0)$, then $\pi(\lambda; \beta)$ is strictly increasing and concave, and
  $\pi(\lambda; \beta) \to +\infty$ as $\lambda \to +\infty$.

**Correction.** The source does not assume $g \neq 0$. For $g = 0$ the function
$\pi(\lambda; \beta)$ is constant, and the strict monotonicity fails.

**Reading.** The source says that $\pi(\lambda; \beta)$ decreases or increases "from
$\pi(\lambda_s; \beta)$". This value is read as the right limit of $\pi(\lambda; \beta)$ at
$\lambda_s$, which can be infinite and need not be $\pi(\lambda_s)^\beta$, because the value of
`CartisGouldToint.Chapter08.secularFn` at a pole is a junk value. The limit is
`CartisGouldToint.Chapter08.corollary_8_2_4_tendsto_lambdaS`. -/
theorem corollary_8_2_4 (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) (β : ℝ) :
    (0 < β → StrictAntiOn (fun t => secularFn g H M t ^ β) (Ioi (lambdaS hH hM)) ∧
      StrictConvexOn ℝ (Ioi (lambdaS hH hM)) (fun t => secularFn g H M t ^ β) ∧
      Tendsto (fun t => secularFn g H M t ^ β) atTop (𝓝 0)) ∧
    (β ∈ Ico (-1 / 2) 0 → StrictMonoOn (fun t => secularFn g H M t ^ β) (Ioi (lambdaS hH hM)) ∧
      ConcaveOn ℝ (Ioi (lambdaS hH hM)) (fun t => secularFn g H M t ^ β) ∧
      Tendsto (fun t => secularFn g H M t ^ β) atTop atTop) := by
  rw [secularFn_eq_secular hM]
  obtain ⟨-, -, -, -, -, hpos, hneg⟩ := secular_shape (scaledGrad_ne_zero (hM := hM) hg) β
    (hH := isSymmetric_scaledOp (hM := hM) hH)
  have hsub := Ioi_lambdaS_subset hH hM
  refine ⟨fun hβ => ?_, fun hβ => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hpos hβ
    exact ⟨h1.mono hsub, h2.subset hsub (convex_Ioi _), h3⟩
  · obtain ⟨h1, h2, h3⟩ := hneg hβ
    exact ⟨h1.mono hsub, h2.subset hsub (convex_Ioi _), h3⟩

/-- **Corollary 8.2.4** of [cartis2022evaluation], the starting values. Let $g \neq 0$, let $H$ be
symmetric and let $M$ be positive definite. The right limit of $\pi(\lambda; \beta)$ at
$\lambda_s$ is as follows.

* If $\lambda_s > -\lambda_1$, then for every $\beta$,
  $\pi(\lambda; \beta) \to \pi(\lambda_s)^\beta$ as $\lambda \to \lambda_s^+$.
* Either $\pi(\lambda)$ has a finite right limit $L > 0$ at $\lambda_s$, and then
  $\pi(\lambda; \beta) \to L^\beta$ as $\lambda \to \lambda_s^+$ for every $\beta$; or
  $\lambda_s = -\lambda_1$ and $\pi(\lambda) \to +\infty$ as $\lambda \to \lambda_s^+$, and then
  $\pi(\lambda; \beta) \to +\infty$ for $\beta > 0$ and $\pi(\lambda; \beta) \to 0$ for
  $\beta < 0$.

**Reading.** This identifies the value "$\pi(\lambda_s; \beta)$" of the source, from which
$\pi(\lambda; \beta)$ decreases ($\beta > 0$) or increases ($\beta < 0$) on
$(\lambda_s, \infty)$, as a right limit.

The case $\lambda_s > -\lambda_1$ means $\lambda_1 > 0$ and $\lambda_s = 0$; it falls under the
first alternative. When $\lambda_s = -\lambda_1$, the first alternative occurs exactly when $g$
is orthogonal to $\ker(H + \lambda_s M)$, that is, when $(H + \lambda_s M) s = -g$ is
consistent, and $L$ is then the squared $M$-norm of its solution of least $M$-norm; see
`Subproblem.tendsto_secular_rpow_threshold`. When $\lambda_s = -\lambda_1$ the matrix
$H + \lambda_s M$ is singular, the value $\pi(\lambda_s)$ is a junk value, and only the limit is
meaningful. -/
theorem corollary_8_2_4_tendsto_lambdaS (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) :
    (∀ β : ℝ, -leftmostPencil hH hM < lambdaS hH hM →
      Tendsto (fun t => secularFn g H M t ^ β) (𝓝[>] (lambdaS hH hM))
        (𝓝 (secularFn g H M (lambdaS hH hM) ^ β))) ∧
    ((∃ L, 0 < L ∧ Tendsto (secularFn g H M) (𝓝[>] (lambdaS hH hM)) (𝓝 L) ∧
        ∀ β : ℝ, Tendsto (fun t => secularFn g H M t ^ β) (𝓝[>] (lambdaS hH hM)) (𝓝 (L ^ β))) ∨
      (lambdaS hH hM = -leftmostPencil hH hM ∧
        Tendsto (secularFn g H M) (𝓝[>] (lambdaS hH hM)) atTop ∧
        ∀ β : ℝ, (0 < β → Tendsto (fun t => secularFn g H M t ^ β) (𝓝[>] (lambdaS hH hM)) atTop) ∧
          (β < 0 → Tendsto (fun t => secularFn g H M t ^ β) (𝓝[>] (lambdaS hH hM)) (𝓝 0)))) := by
  rw [secularFn_eq_secular hM, lambdaS_eq, leftmostPencil_eq]
  set hT := isSymmetric_scaledOp (hM := hM) hH
  have hg' := scaledGrad_ne_zero (hM := hM) hg
  have hcont : -leftmost hT < shiftThreshold hT → ∀ β : ℝ,
      Tendsto (fun t => secular (scaledGrad hM g) (scaledOp H hM) t ^ β)
        (𝓝[>] (shiftThreshold hT))
        (𝓝 (secular (scaledGrad hM g) (scaledOp H hM) (shiftThreshold hT) ^ β)) := fun h β =>
    (((Real.continuousAt_rpow_const _ β (Or.inl (secular_pos (hH := hT) hg' h).ne')).comp
      (hasDerivAt_secular (hH := hT) h).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
  refine ⟨fun β h => hcont h β, ?_⟩
  rcases (neg_leftmost_le_shiftThreshold (hH := hT)).lt_or_eq with hlt | heq
  · exact Or.inl ⟨_, secular_pos (hH := hT) hg' hlt,
      ((hasDerivAt_secular (hH := hT) hlt).continuousAt.tendsto).mono_left nhdsWithin_le_nhds,
      hcont hlt⟩
  rw [← heq]
  by_cases hK : scaledGrad hM g ∈ (LinearMap.ker ((scaledOp H hM + (-leftmost hT) • 1 :
      ScaledSpace hM →L[ℝ] ScaledSpace hM) : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM))ᗮ
  · have hp : particular hT (scaledGrad hM g) (-leftmost hT) ≠ 0 := fun h0 => hg' (by
      have := ((particular_spec (hH := hT) (g := scaledGrad hM g) _).2.1 hK).1
      rw [h0, map_zero, eq_comm, neg_eq_zero] at this
      exact this)
    exact Or.inl ⟨_, pow_pos (norm_pos_iff.2 hp) 2,
      ((tendsto_step_threshold (hH := hT) (g := scaledGrad hM g)).1 hK).2,
      fun β => (tendsto_secular_rpow_threshold (hH := hT) β).1 hK (Or.inl hp)⟩
  · exact Or.inr ⟨rfl, (tendsto_step_threshold (hH := hT) (g := scaledGrad hM g)).2 hK,
      fun β => (tendsto_secular_rpow_threshold (hH := hT) β).2 hK⟩

/-- **Theorem 8.2.5** of [cartis2022evaluation] (lower and upper first-order Taylor estimates of
$\pi(\lambda; \beta)$). Let $g \in \mathbb{R}^n$, let $H$ be symmetric, let $M$ be positive
definite, let $\lambda_c > \lambda_s$ and $\delta > \lambda_s - \lambda_c$, and let
$\beta \in \mathbb{R}$. Write $t_1(\delta; \beta) = \pi(\lambda_c; \beta) + \pi^{(1)}(\lambda_c;
\beta) \delta$. Then
$$\pi(\lambda_c + \delta; \beta) \ge t_1(\delta; \beta) \text{ if } \beta > 0 \qquad (8.2.20)$$
and
$$\pi(\lambda_c + \delta; \beta) \le t_1(\delta; \beta) \text{ if } \beta \in [-1/2, 0). \qquad
  (8.2.21)$$

The strict form is `CartisGouldToint.Chapter08.theorem_8_2_5_strict`. -/
theorem theorem_8_2_5 (hH : H.IsHermitian) (hM : M.PosDef) {lamc δ : ℝ}
    (hc : lambdaS hH hM < lamc) (hδ : lambdaS hH hM - lamc < δ) (β : ℝ) :
    (0 < β → secularFn g H M lamc ^ β + deriv (fun t => secularFn g H M t ^ β) lamc * δ ≤
      secularFn g H M (lamc + δ) ^ β) ∧
    (β ∈ Ico (-1 / 2) 0 → secularFn g H M (lamc + δ) ^ β ≤
      secularFn g H M lamc ^ β + deriv (fun t => secularFn g H M t ^ β) lamc * δ) := by
  rw [secularFn_eq_secular hM]
  rcases eq_or_ne g 0 with rfl | hg
  · simp [secular_zero_left]
  · obtain ⟨h1, -, h3, -, -⟩ := secular_rpow_tangent (scaledGrad_ne_zero (hM := hM) hg)
      (neg_leftmost_lt_of_lambdaS_lt hH hM hc)
      (neg_leftmost_lt_of_lambdaS_lt hH hM (by linarith)) β
    exact ⟨h1, h3⟩

/-- **Theorem 8.2.5** of [cartis2022evaluation], strict form. Let $g \neq 0$, let $H$ be symmetric,
let $M$ be positive definite, let $\lambda_c > \lambda_s$ and $\delta > \lambda_s - \lambda_c$,
and let $\beta \in \mathbb{R}$. If $\beta > 0$ and $\delta \neq 0$, then (8.2.20) is strict. If
$\beta \in [-1/2, 0)$ and $\delta \neq 0$, and either $\beta \neq -1/2$ or there is no
generalized eigenvector $v$ of $(H, M)$ with $M v = g$, then (8.2.21) is strict. If
$\beta = -1/2$ and $M v = g$ for a generalized eigenvector $v$, then (8.2.21) is an equality.

**Correction.** The source claims strict inequalities whenever $g \neq 0$. For $\delta = 0$ both
sides are equal. For $\beta = -1/2$ and $g = M v$ with $v$ a generalized eigenvector,
$\pi(\lambda; -1/2)$ is affine (see `CartisGouldToint.Chapter08.lemma_8_2_3_strict`), and
(8.2.21) is an equality. -/
theorem theorem_8_2_5_strict (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {lamc δ : ℝ}
    (hc : lambdaS hH hM < lamc) (hδ : lambdaS hH hM - lamc < δ) (β : ℝ) :
    (0 < β → δ ≠ 0 → secularFn g H M lamc ^ β +
      deriv (fun t => secularFn g H M t ^ β) lamc * δ < secularFn g H M (lamc + δ) ^ β) ∧
    (β ∈ Ico (-1 / 2) 0 → δ ≠ 0 → (β ≠ -1 / 2 ∨ ¬ ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
        toEuclideanLin M v = g ∧ toEuclideanLin H v = c • toEuclideanLin M v) →
      secularFn g H M (lamc + δ) ^ β <
        secularFn g H M lamc ^ β + deriv (fun t => secularFn g H M t ^ β) lamc * δ) ∧
    (β = -1 / 2 → (∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
        toEuclideanLin M v = g ∧ toEuclideanLin H v = c • toEuclideanLin M v) →
      secularFn g H M (lamc + δ) ^ β =
        secularFn g H M lamc ^ β + deriv (fun t => secularFn g H M t ^ β) lamc * δ) := by
  rw [secularFn_eq_secular hM, ← exists_scaledOp_scaledGrad_eq_iff (hM := hM)]
  obtain ⟨-, h2, -, h4, h5⟩ := secular_rpow_tangent (scaledGrad_ne_zero (hM := hM) hg)
    (neg_leftmost_lt_of_lambdaS_lt hH hM hc) (neg_leftmost_lt_of_lambdaS_lt hH hM (by linarith)) β
  exact ⟨h2, h4, h5⟩

/-! ### Derivatives of the secular function -/

/-- **Equation (8.2.29)** of [cartis2022evaluation]. Let $g \in \mathbb{R}^n$,
$H, M \in \mathbb{R}^{n \times n}$ and $\lambda \in \mathbb{R}$. The **derivative vectors**
$s^{(k)}(\lambda)$ are defined by $s^{(0)}(\lambda) = s(\lambda)$ and
$$(H + \lambda M) s^{(k+1)}(\lambda) = -(k + 1) M s^{(k)}(\lambda),$$
solved with $(H + \lambda M)^{-1}$.

They are the derivatives of $s(\lambda)$ for $\lambda > -\lambda_1$
(`CartisGouldToint.Chapter08.toScaled_secularDerivVec`). Where $H + \lambda M$ is singular, the
Mathlib convention $A^{-1} = 0$ gives $s^{(k)}(\lambda) = 0$.

**Reading.** Implements the exact negative-sign recursion with zero fallback at singular shifts.
-/
noncomputable def secularDerivVec (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => stepOf g H M lam
  | k + 1 => toEuclideanLin (H + lam • M)⁻¹
      (-((k + 1 : ℝ) • toEuclideanLin M (secularDerivVec g H M lam k)))

/-- The derivative vector of order $0$ is the step: $s^{(0)}(\lambda) = s(\lambda)$.

**Generalization.** The same step definition with the generalized singular inverse convention.
-/
theorem secularDerivVec_zero (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) : secularDerivVec g H M lam 0 = stepOf g H M lam :=
  rfl

/-- The recursion of the derivative vectors: $s^{(k+1)}(\lambda) = (H + \lambda M)^{-1}
\bigl(-(k + 1) M s^{(k)}(\lambda)\bigr)$.

**Reading.** Solves the source shifted recurrence using the total inverse.
-/
theorem secularDerivVec_succ (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (k : ℕ) :
    secularDerivVec g H M lam (k + 1) = toEuclideanLin (H + lam • M)⁻¹
      (-((k + 1 : ℝ) • toEuclideanLin M (secularDerivVec g H M lam k))) :=
  rfl

/-- **Equation (8.2.30)** of [cartis2022evaluation]. The coefficients $\alpha_k$ are defined by
$$\alpha_0 = 1, \qquad \alpha_{k+1} = \frac{2 (2k + 3)}{k + 1} \alpha_k.$$
-/
noncomputable def alphaCoeff : ℕ → ℝ
  | 0 => 1
  | k + 1 => 2 * (2 * k + 3) / (k + 1) * alphaCoeff k

/-- The coefficients (8.2.30) have the closed form $\alpha_k = (2k + 1)! / (k!)^2$, which is
`Subproblem.secularCoeff k`. -/
theorem alphaCoeff_eq_secularCoeff (k : ℕ) : alphaCoeff k = secularCoeff k := by
  induction k with
  | zero => simp [alphaCoeff, secularCoeff_zero]
  | succ k ih => rw [alphaCoeff, secularCoeff_succ, ih]

/-- Let $H$ be symmetric and $M$ be positive definite, and let $\lambda > -\lambda_1$, where
$\lambda_1$ is the leftmost eigenvalue of the scaled operator $M^{-1} H$. For every $k$, the
vector $s^{(k)}(\lambda)$ of (8.2.29), carried into the $M$-inner product space, is the $k$-th
derivative `Subproblem.stepDeriv` of the operator step of $M^{-1} g$ and $M^{-1} H$ at
$\lambda$. -/
theorem toScaled_secularDerivVec (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hlam : -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam) (k : ℕ) :
    toScaled hM (secularDerivVec g H M lam k) =
      stepDeriv (scaledGrad hM g) (scaledOp H hM) k lam := by
  have hu : IsUnit (H + lam • M) :=
    isUnit_of_isUnit_add_smul_scaledOp (hM := hM)
      (isUnit_add_smul (hH := isSymmetric_scaledOp hH) hlam)
  induction k with
  | zero => rw [stepDeriv_zero, ← toScaled_stepOf hM]; rfl
  | succ k ih =>
    refine stepDeriv_succ_unique (hH := isSymmetric_scaledOp hH) hlam k ?_
    rw [secularDerivVec, add_smul_scaledOp_toScaled, toEuclideanLin_mul_nonsing_inv_apply hu,
      map_neg, map_smul, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit, map_neg, map_smul, ih]

/-- **Theorem 8.2.6** of [cartis2022evaluation] (derivatives of the secular function). Let
$g \in \mathbb{R}^n$, let $H$ be symmetric, let $M$ be positive definite, and let $\lambda$ be
such that $H + \lambda M$ is positive definite. Then for every $k = 0, 1, \ldots$,
$$\pi^{(2k+1)}(\lambda) = 2 \alpha_k \langle s^{(k)}(\lambda), M s^{(k+1)}(\lambda) \rangle
  \qquad (8.2.27)$$
and
$$\pi^{(2k+2)}(\lambda) = \alpha_{k+1} \langle s^{(k+1)}(\lambda), M s^{(k+1)}(\lambda) \rangle,
  \qquad (8.2.28)$$
with the vectors $s^{(k)}(\lambda)$ of (8.2.29) and the coefficients $\alpha_k$ of (8.2.30). -/
theorem theorem_8_2_6 (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hpd : (H + lam • M).PosDef) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (secularFn g H M) lam = 2 * alphaCoeff k *
        ⟪secularDerivVec g H M lam k, toEuclideanLin M (secularDerivVec g H M lam (k + 1))⟫ ∧
      iteratedDeriv (2 * k + 2) (secularFn g H M) lam = alphaCoeff (k + 1) *
        ⟪secularDerivVec g H M lam (k + 1),
          toEuclideanLin M (secularDerivVec g H M lam (k + 1))⟫ := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp only [secularFn_of_isEmpty, Subsingleton.elim _ (0 : EuclideanSpace ℝ (Fin n)),
      inner_zero_left, mul_zero]
    exact ⟨by rw [iteratedDeriv_succ']; simp, by rw [iteratedDeriv_succ']; simp⟩
  · have : NeZero n := ⟨fun h => by subst h; exact (not_isEmpty_of_nonempty (Fin 0)) inferInstance⟩
    have hlam := neg_leftmost_lt_of_posDef hH hM hpd
    have hMs := isSymmetric_toEuclideanLin_iff.2 hM.isHermitian
    obtain ⟨h1, h2⟩ := iteratedDeriv_secular (g := scaledGrad hM g) hlam k
    rw [secularFn_eq_secular hM, h1, h2, ← toScaled_secularDerivVec hH hM hlam,
      ← toScaled_secularDerivVec hH hM hlam, ← real_inner_self_eq_norm_sq, inner_toScaled,
      inner_toScaled, alphaCoeff_eq_secularCoeff, alphaCoeff_eq_secularCoeff,
      ← hMs, ← hMs]
    exact ⟨rfl, rfl⟩

/-! ### Global optimality of the subproblems -/

/-- Let $M$ be positive definite. A number $\mu$ is a trust-region multiplier
(`Subproblem.IsTrustRegionMultiplier`) of $s$ for the scaled data $M^{-1} g$, $M^{-1} H$ and
radius $\Delta$ in the $M$-inner product space if and only if $\mu \ge 0$, $(H + \mu M) s = -g$,
$H + \mu M$ is positive semidefinite, and $\mu (\|s\|_M - \Delta) = 0$. -/
theorem isTrustRegionMultiplier_scaled_iff (hM : M.PosDef) {Δ μ : ℝ}
    {s : EuclideanSpace ℝ (Fin n)} :
    IsTrustRegionMultiplier (scaledGrad hM g) (scaledOp H hM) Δ (toScaled hM s) μ ↔
      0 ≤ μ ∧ toEuclideanLin (H + μ • M) s = -g ∧ (H + μ • M).PosSemidef ∧
        μ * (mNorm M s - Δ) = 0 := by
  rw [mNorm_eq_norm_toScaled hM, ← add_smul_scaledOp_toScaled_eq_neg_iff (hM := hM),
    posSemidef_add_smul_iff_isPositive (hM := hM)]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- Complementarity in squared form. Let $M \in \mathbb{R}^{n \times n}$ and $\Delta > 0$. For every
$\mu$ and $s$,
$$\mu (\|s\|_M - \Delta) = 0 \iff \mu (\|s\|_M^2 - \Delta^2) = 0.$$
-/
theorem mul_mNorm_sub_eq_zero_iff (M : Matrix (Fin n) (Fin n) ℝ) {Δ μ : ℝ} (hΔ : 0 < Δ)
    (s : EuclideanSpace ℝ (Fin n)) :
    μ * (mNorm M s - Δ) = 0 ↔ μ * (mNorm M s ^ 2 - Δ ^ 2) = 0 := by
  have h0 := mNorm_nonneg M s
  have hfac : mNorm M s ^ 2 - Δ ^ 2 = (mNorm M s - Δ) * (mNorm M s + Δ) := by ring
  rw [hfac, ← mul_assoc, mul_eq_zero (a := μ * _), or_iff_left (by positivity)]

/-- **Theorem 8.2.7** of [cartis2022evaluation], the multiplier conditions. Let
$g \in \mathbb{R}^n$, $H, M \in \mathbb{R}^{n \times n}$, $\Delta \in \mathbb{R}$,
$s \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$. Then $\lambda$ is a **multiplier** of the
step $s$ of the trust-region subproblem (8.1.2) if $\lambda \ge 0$,
$$(H + \lambda M) s = -g, \qquad (8.2.31)$$
$H + \lambda M$ is positive semidefinite, and
$$\lambda (\|s\|_M^2 - \Delta^2) = 0. \qquad (8.2.32)$$
-/
structure IsTrustRegionKKT (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : Prop where
  /-- The multiplier is nonnegative: $\lambda \ge 0$. -/
  nonneg : 0 ≤ lam
  /-- The step solves the shifted system (8.2.31): $(H + \lambda M) s = -g$. -/
  shifted : toEuclideanLin (H + lam • M) s = -g
  /-- The shifted matrix $H + \lambda M$ is positive semidefinite. -/
  posSemidef : (H + lam • M).PosSemidef
  /-- Complementarity (8.2.32): $\lambda (\|s\|_M^2 - \Delta^2) = 0$. -/
  complementarity : lam * (mNorm M s ^ 2 - Δ ^ 2) = 0

/-- Let $M$ be positive definite and $\Delta > 0$. Then $\mu$ is a multiplier of $s$ in the sense of
`CartisGouldToint.Chapter08.IsTrustRegionKKT` if and only if $\mu$ is a trust-region multiplier
(`Subproblem.IsTrustRegionMultiplier`) of $s$ for the scaled data $M^{-1} g$, $M^{-1} H$ and
radius $\Delta$ in the $M$-inner product space. -/
theorem isTrustRegionKKT_iff_scaled (hM : M.PosDef) {Δ μ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} :
    IsTrustRegionKKT g H M Δ s μ ↔
      IsTrustRegionMultiplier (scaledGrad hM g) (scaledOp H hM) Δ (toScaled hM s) μ := by
  rw [isTrustRegionMultiplier_scaled_iff hM, mul_mNorm_sub_eq_zero_iff M hΔ s]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- **Theorem 8.2.7** of [cartis2022evaluation] (trust-region subproblem global optimality). Let
$g \in \mathbb{R}^n$, let $H$ be symmetric, let $M$ be positive definite, and let $\Delta > 0$.
Let $s_*$ be a global minimizer of the trust-region subproblem (8.1.2). Then there is
$\lambda_*$ such that $\lambda_* \ge 0$,
$$(H + \lambda_* M) s_* = -g \quad (8.2.31), \qquad \lambda_* (\|s_*\|_M^2 - \Delta^2) = 0 \quad
  (8.2.32),$$
and $H + \lambda_* M$ is positive semidefinite. If moreover $H + \lambda_* M$ is positive
definite, then $s_*$ is the only global minimizer of (8.1.2).

The conditions on $\lambda_*$ are `CartisGouldToint.Chapter08.IsTrustRegionKKT`. -/
theorem theorem_8_2_7 (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsTrustRegionSolution g H M Δ s) :
    ∃ lamStar, IsTrustRegionKKT g H M Δ s lamStar ∧
      ((H + lamStar • M).PosDef → ∀ u, IsTrustRegionSolution g H M Δ u → u = s) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  obtain ⟨hn, hmin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hs
  obtain ⟨μ, hμ⟩ := (isMinOn_closedBall_iff hT hΔ hn).1 hmin
  refine ⟨μ, (isTrustRegionKKT_iff_scaled hM hΔ).2 hμ, fun hpd u hu => ?_⟩
  obtain ⟨hun, humin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hu
  have hc := ((posDef_add_smul_iff_isSymmetricCoercive (hM := hM) μ).1 hpd).isCoercive
  exact (toScaled hM).injective (eq_of_isMinOn_closedBall_of_posDef hT hμ hn hc hun humin)

/-- **Theorem 8.2.8** of [cartis2022evaluation] (regularization subproblem global optimality). Let
$g \in \mathbb{R}^n$, let $H$ be symmetric, let $M$ be positive definite, and let $\sigma > 0$
and $r > 2$. Let $s_*$ be a global minimizer of the regularization subproblem (8.1.3), and let
$\lambda_* = \sigma \|s_*\|_M^{r-2}$ (8.2.33). Then
$$(H + \lambda_* M) s_* = -g \qquad (8.2.31)$$
and $H + \lambda_* M$ is positive semidefinite. If moreover $H + \lambda_* M$ is positive
definite, then $s_*$ is the only global minimizer of (8.1.3).

The source's uniqueness argument assumes $\lambda_*>\lambda_s$ after invoking positive
definiteness. The Lean proof also covers $\lambda_*=\lambda_s=0$, which occurs for $g=0$
and positive definite $H$. -/
theorem theorem_8_2_8 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsRegularizationSolution g H M σ r s) :
    toEuclideanLin (H + (σ * mNorm M s ^ (r - 2)) • M) s = -g ∧
      (H + (σ * mNorm M s ^ (r - 2)) • M).PosSemidef ∧
      ((H + (σ * mNorm M s ^ (r - 2)) • M).PosDef →
        ∀ u, IsRegularizationSolution g H M σ r u → u = s) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  obtain ⟨h1, h2⟩ := (isMinOn_regModel_iff hT hσ hr).1 hmin
  rw [mNorm_eq_norm_toScaled hM]
  refine ⟨(add_smul_scaledOp_toScaled_eq_neg_iff _ g s).1 h1,
    (posSemidef_add_smul_iff_isPositive _).2 h2, fun hpd u hu => ?_⟩
  have hc := ((posDef_add_smul_iff_isSymmetricCoercive (hM := hM) _).1 hpd).isCoercive
  exact (toScaled hM).injective (eq_of_isMinOn_regModel_of_posDef hT hσ hr hmin hc
    ((isRegularizationSolution_iff_scaled hM).1 hu))

/-! ### Sufficiency of the optimality conditions -/

section Sufficiency

/-- Sufficiency of the multiplier conditions for (8.1.2). Let $H$ be symmetric, let $M$ be positive
definite, and let $\Delta > 0$. If $\lambda$ is a multiplier of $s$
(`CartisGouldToint.Chapter08.IsTrustRegionKKT`) and $\|s\|_M \le \Delta$, then $s$ is a global
minimizer of the trust-region subproblem.

**Reading.** Adds sufficient optimality for a feasible step satisfying the source multiplier
conditions.
-/
theorem isTrustRegionSolution_of_kkt (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam : ℝ}
    (hΔ : 0 < Δ) {s : EuclideanSpace ℝ (Fin n)} (h : IsTrustRegionKKT g H M Δ s lam)
    (hs : mNorm M s ≤ Δ) : IsTrustRegionSolution g H M Δ s := by
  rw [isTrustRegionSolution_iff_scaled hM]
  rw [mNorm_eq_norm_toScaled hM] at hs
  exact ⟨hs, ((isTrustRegionKKT_iff_scaled hM hΔ).1 h).isMinOn (isSymmetric_scaledOp hH)⟩

/-- Sufficiency of the optimality conditions for (8.1.3). Let $H$ be symmetric, let $M$ be positive
definite, and let $\sigma > 0$ and $r > 2$. Let $\lambda = \sigma \|s\|_M^{r-2}$. If
$(H + \lambda M) s = -g$ and $H + \lambda M$ is positive semidefinite, then $s$ is a global
minimizer of the regularization subproblem.

**Reading.** Adds sufficient optimality from the source shifted equation and semidefiniteness.
-/
theorem isRegularizationSolution_of_shifted (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)}
    (h1 : toEuclideanLin (H + (σ * mNorm M s ^ (r - 2)) • M) s = -g)
    (h2 : (H + (σ * mNorm M s ^ (r - 2)) • M).PosSemidef) :
    IsRegularizationSolution g H M σ r s := by
  rw [isRegularizationSolution_iff_scaled hM, isMinOn_regModel_iff (isSymmetric_scaledOp hH) hσ hr]
  rw [mNorm_eq_norm_toScaled hM] at h1 h2
  exact ⟨(add_smul_scaledOp_toScaled_eq_neg_iff _ g s).2 h1,
    (posSemidef_add_smul_iff_isPositive _).1 h2⟩

/-- Uniqueness for (8.1.2). Let $H$ be symmetric, let $M$ be positive definite, and let
$\Delta > 0$. If $\lambda$ is a multiplier of $s$
(`CartisGouldToint.Chapter08.IsTrustRegionKKT`), $\|s\|_M \le \Delta$ and $H + \lambda M$ is
positive definite, then every global minimizer $u$ of the trust-region subproblem equals $s$. -/
theorem eq_of_isTrustRegionKKT_of_posDef (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam : ℝ}
    (hΔ : 0 < Δ) {s : EuclideanSpace ℝ (Fin n)} (h : IsTrustRegionKKT g H M Δ s lam)
    (hs : mNorm M s ≤ Δ) (hpd : (H + lam • M).PosDef) {u : EuclideanSpace ℝ (Fin n)}
    (hu : IsTrustRegionSolution g H M Δ u) : u = s := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  obtain ⟨hun, humin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hu
  have hc := ((posDef_add_smul_iff_isSymmetricCoercive (hM := hM) lam).1 hpd).isCoercive
  rw [mNorm_eq_norm_toScaled hM] at hs
  exact (toScaled hM).injective (eq_of_isMinOn_closedBall_of_posDef hT
    ((isTrustRegionKKT_iff_scaled hM hΔ).1 h) hs hc hun humin)

end Sufficiency

end CartisGouldToint.Chapter08
