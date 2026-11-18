/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter06.Section06
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Numlib.Optimization.LogBarrier
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Conn, Gould and Toint, Section 13.12: Coleman–Li scaling

This module formalizes the Coleman–Li affine-scaling trust-region method of [conn2000trust], Section
13.12, for minimizing $f$ over the nonnegative orthant of $\mathbb{R}^\iota$. At a point $x$ with
gradient $g$, the scaling vector (13.12.1) is $v_i = x_i$ if $g_i \ge 0$ and $v_i = -1$ if
$g_i < 0$, and the scaling matrix (13.12.2) is $S = \operatorname{diag}(|v_i|^{1/2})$. With
$\bar G = \operatorname{diag}(\max\{g_i, 0\})$, the scaled model (13.12.7) has gradient $S g$ and
Hessian $\hat H = S H S + \bar G$. At a strictly positive point, the change of variables $s = S w$
turns it into the unscaled model (13.12.8) with Hessian $H + \operatorname{diag}(\max\{g_i, 0\} /
|v_i|)$. Theorems 13.12.1 and 13.12.2 characterize first-order and weak second-order criticality on
the orthant by the scaled quantities.

Algorithm 13.12.1 is a trust-region method in the norm $\|S^{-1} s\|$ with a fraction-to-boundary
test, and Algorithm 13.12.2 changes its acceptance ratio to (13.12.24). Theorems 13.12.3 and 13.12.5
bound the model decrease at the constrained scaled Cauchy point and eigenpoint. Theorem 13.12.4
proves convergence of the scaled gradient for bounded interior runs, and Theorem 13.12.6 gives weak
second-order criticality at limit points. A counterexample refutes the printed form of Theorem
13.12.3. The last part shows that eliminating the slack variables of linear inequality constraints,
as in (13.12.28)–(13.12.35), preserves the model and the trust-region bound. The proofs reuse the
basic trust-region algorithm of Chapter 6 (`ConnGouldToint.Chapter06.BTRRun`).

## Main definitions

* Equation (13.12.1), `ConnGouldToint.Chapter13.scalingVector`: the scaling vector $v(x, g)$.
* Equation (13.12.2), `ConnGouldToint.Chapter13.scalingMatrix`: the scaling matrix
  $S = \operatorname{diag}(|v_i|^{1/2})$.
* Equation (13.12.5), `ConnGouldToint.Chapter13.affineQuadraticModel`: the quadratic model in
  displacement coordinates.
* Equation (13.12.6), `ConnGouldToint.Chapter13.IsScaledNewtonStep`: the scaled Newton system
  $\hat H w = -S g$.
* Equation (13.12.7), `ConnGouldToint.Chapter13.scaledModel`: the scaled model.
* Equation (13.12.8), `ConnGouldToint.Chapter13.unscaledModel`: the corrected model in the original
  coordinates.
* Equation (13.12.11), `ConnGouldToint.Chapter13.scaledCauchyTimes` and
  `ConnGouldToint.Chapter13.IsScaledCauchyTime`: the feasible times and the constrained scaled
  Cauchy point.
* Equation (13.12.23), `ConnGouldToint.Chapter13.scaledEigenTimes` and
  `ConnGouldToint.Chapter13.IsScaledEigenTime`: the feasible times and the constrained scaled
  eigenpoint.
* Equation (13.12.24), `ConnGouldToint.Chapter13.colemanLiAcceptanceRatio`: the acceptance ratio of
  Algorithm 13.12.2.
* Algorithms 13.12.1 and 13.12.2, `ConnGouldToint.Chapter13.ColemanLiRun`: a run of either
  algorithm.
* Equation (13.12.25), `ConnGouldToint.Chapter13.ScaledHessianConsistency`: the scaled Hessian
  agreement condition.
* Equations (13.12.28)–(13.12.35), `ConnGouldToint.Chapter13.tramSlackStep`,
  `ConnGouldToint.Chapter13.tramModel` and `ConnGouldToint.Chapter13.tramNorm`: the slack step, the
  reduced model and the reduced trust-region norm.

## Main results

* Theorem 13.12.1, `ConnGouldToint.Chapter13.theorem_13_12_1`: at $x \ge 0$, first-order criticality
  is equivalent to $S^2 g = 0$ and to $S g = 0$.
* Theorem 13.12.2, `ConnGouldToint.Chapter13.theorem_13_12_2`: $S g = 0$ with $\hat H$ positive
  semidefinite is equivalent to weak second-order criticality.
* Theorem 13.12.3, `ConnGouldToint.Chapter13.theorem_13_12_3`: the decrease at the constrained
  scaled Cauchy point, with a fraction-to-boundary cap.
* Theorem 13.12.3, `ConnGouldToint.Chapter13.theorem_13_12_3_counterexample`: the printed decrease
  bound fails in dimension one.
* Theorem 13.12.4, `ConnGouldToint.Chapter13.theorem_13_12_4`: a bounded interior run converges in
  the scaled gradient norm, and its limit points are first-order critical.
* Theorem 13.12.5, `ConnGouldToint.Chapter13.theorem_13_12_5`: a positive decrease at the
  constrained scaled eigenpoint.
* Theorem 13.12.6, `ConnGouldToint.Chapter13.theorem_13_12_6`: vanishing negative scaled model
  curvature and the agreement (13.12.25) give weak second-order criticality at the limit.
* Theorem 13.12.6, `ConnGouldToint.Chapter13.theorem_13_12_6_version2`: the same conclusion for runs
  of Algorithm 13.12.2 with forced radius expansion.
* Equations (13.12.31)–(13.12.35), `ConnGouldToint.Chapter13.tramSubproblem_iff`: minimizers of the
  reduced subproblem are exactly the projections of minimizers of the subproblem with slacks.

## Implementation notes

* Vectors are functions `ι → ℝ` and matrices are `Matrix ι ι ℝ`. Euclidean norms are taken through
  `WithLp.toLp 2`, and matrix norms are the $\ell^2$ operator norms.
* The gradient and the Hessian at the base point enter as their coordinates $g$ and $H$. The
  diagonal $\bar G$ is defined even where $S$ is singular.

## Deviations from the source

* **Equation (13.12.12)** (correction). The curvature along the scaled Cauchy ray is that of
  $\hat H = S H S + \bar G$, including the positive-gradient diagonal. See
  `ConnGouldToint.Chapter13.unscaledModel_along_scaledRay`.
* **Algorithms 13.12.1 and 13.12.2** (correction). The printed boundary-distance test (13.12.9) also
  admits points outside the orthant, so the trial point must also be strictly positive. See
  `ConnGouldToint.Chapter13.ColemanLiRun` and
  `ConnGouldToint.Chapter13.colemanLi_unsigned_clearance_counterexample`.
* **Theorem 13.12.3** (correction). The decrease bound needs a fraction-to-boundary cap on the ray
  parameter. A one-dimensional example violates the printed bound for every positive criticality
  cap. See `ConnGouldToint.Chapter13.theorem_13_12_3` and
  `ConnGouldToint.Chapter13.theorem_13_12_3_counterexample`.
* **Theorem 13.12.5** (correction). The printed bound is stated at the Cauchy point and is negative.
  The corrected bound is positive and holds at the constrained scaled eigenpoint. See
  `ConnGouldToint.Chapter13.theorem_13_12_5`.
* **Equation (13.12.34)** (correction). Both terms of the reduced model are evaluated at the trial
  displacement. See `ConnGouldToint.Chapter13.tramModel`.
* **Equation (13.12.35)** (typo). The reduced trust-region bound uses the radius of (13.12.33),
  without the stray factor $n$ of the printed display. See
  `ConnGouldToint.Chapter13.tramNorm_le_iff_exists_slack`.
-/

open Matrix Metric Filter
open scoped BigOperators Topology

namespace ConnGouldToint.Chapter13

variable {ι : Type*}

/-- **Equation (13.12.1)** of [conn2000trust]. For $x, g \in \mathbb{R}^\iota$ the **scaling
vector** has the entries
$$v_i(x, g) = \begin{cases} x_i & \text{if } g_i \ge 0, \\ -1 & \text{if } g_i < 0.
  \end{cases}$$

This is the formula of the source for the bounds $0 \le x_i < \infty$. It is defined at every
$x$, including points on the boundary of the orthant. -/
noncomputable def scalingVector (x g : ι → ℝ) (i : ι) : ℝ :=
  if 0 ≤ g i then x i else -1

/-- **Equation (13.12.2)** of [conn2000trust]. The **Coleman–Li scaling matrix** is the diagonal
matrix
$$S(x, g) = \operatorname{diag}\big(|v_i(x, g)|^{1/2}\big).$$
-/
noncomputable def scalingMatrix [DecidableEq ι] (x g : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i ↦ Real.sqrt |scalingVector x g i|

/-- **First-order criticality** on the nonnegative orthant: for all $i$, $g_i \ge 0$, and $g_i = 0$
whenever $x_i > 0$.

The condition $x \ge 0$ is a separate hypothesis wherever it is needed. -/
def OrthantFirstOrder (x g : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ g i ∧ (0 < x i → g i = 0)

/-- A direction $d$ lies on the **active face** at $x$ if $d_i = 0$ whenever $x_i = 0$, that is, $d$
is in the nullspace of the active bound constraints. -/
def OrthantFaceDirection (x d : ι → ℝ) : Prop :=
  ∀ i, x i = 0 → d i = 0

section Finite

variable [Fintype ι] [DecidableEq ι]

/-- **Weak second-order criticality** on the nonnegative orthant: $x$ is first-order critical for
$g$, and $d^T H d \ge 0$ for every direction $d$ on the active face at $x$. -/
def OrthantWeakSecondOrder (x g : ι → ℝ) (H : Matrix ι ι ℝ) : Prop :=
  OrthantFirstOrder x g ∧ ∀ d, OrthantFaceDirection x d → 0 ≤ d ⬝ᵥ (H *ᵥ d)

/-- The **scaled gradient** $S(x, g)\, g$. -/
noncomputable def scaledGradient (x g : ι → ℝ) : ι → ℝ :=
  scalingMatrix x g *ᵥ g

/-- **Equation (13.12.4)** of [conn2000trust]. The vector $S^2 g$ of the stationarity system has the
continuous coordinate formula
$$(S(x, g)^2 g)_i = |x_i| \max\{g_i, 0\} + \min\{g_i, 0\},$$
although $S$ itself depends on the sign of $g_i$. -/
theorem scaledResidual_apply (x g : ι → ℝ) (i : ι) :
    ((scalingMatrix x g * scalingMatrix x g) *ᵥ g) i =
      |x i| * max (g i) 0 + min (g i) 0 := by
  rw [scalingMatrix, Matrix.diagonal_mul_diagonal, Matrix.mulVec_diagonal,
    Real.mul_self_sqrt (abs_nonneg _)]
  by_cases h : 0 ≤ g i
  · simp [scalingVector, h]
  · have h' := (lt_of_not_ge h).le
    simp [scalingVector, h, max_eq_right h', min_eq_left h']

/-- **Equation (13.12.4)** of [conn2000trust]. The map $(x, g) \mapsto S(x, g)^2 g$, the left side
of the stationarity system, is continuous. -/
theorem continuous_scaledResidual :
    Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦
      (scalingMatrix xg.1 xg.2 * scalingMatrix xg.1 xg.2) *ᵥ xg.2) := by
  apply continuous_pi
  intro i
  simp only [scaledResidual_apply]
  have hx : Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ xg.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hg : Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ xg.2 i) :=
    (continuous_apply i).comp continuous_snd
  exact (hx.abs.mul (hg.max continuous_const)).add (hg.min continuous_const)

/-- Feasibility along the scaled ray, used in the proof of Theorem 13.12.3 of [conn2000trust]. Let
$x \ge 0$, $t \ge 0$, $\sigma \le 1$ and $\kappa > 0$, and let $g_i \le \kappa$ for all $i$. If
$t \le (1 - \sigma) / \kappa$, then for every $i$
$$\sigma x_i \le x_i - t\, (S(x, g)^2 g)_i.$$
-/
theorem scaledRay_coordinate_lower_bound {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t κ σ : ℝ} (ht : 0 ≤ t) (hσ : σ ≤ 1) (hκ : 0 < κ)
    (hg : ∀ i, g i ≤ κ) (hlen : t ≤ (1 - σ) / κ) (i : ι) :
    σ * x i ≤ x i - t * ((scalingMatrix x g * scalingMatrix x g) *ᵥ g) i := by
  rw [scaledResidual_apply]
  by_cases hgi : 0 ≤ g i
  · rw [abs_of_nonneg (hx i), max_eq_left hgi, min_eq_right hgi, add_zero]
    have hmul : t * g i ≤ 1 - σ :=
      (mul_le_mul_of_nonneg_left (hg i) ht).trans ((le_div_iff₀ hκ).mp hlen)
    have h := mul_le_mul_of_nonneg_left hmul (hx i)
    nlinarith only [h]
  · have hgi' := (lt_of_not_ge hgi).le
    rw [max_eq_right hgi', min_eq_left hgi', mul_zero, zero_add]
    have h := mul_le_mul_of_nonneg_right hσ (hx i)
    linarith [mul_nonpos_of_nonneg_of_nonpos ht hgi']

/-- The diagonal matrix $\bar G = \operatorname{diag}(\max\{g_i, 0\})$ of the positive parts of the
gradient, written $\bar G$ in the source. -/
noncomputable def scaledCorrection (g : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i ↦ max (g i) 0

/-- The Hessian $\hat H = S H S + \bar G$ of the scaled model (13.12.7). -/
noncomputable def scaledHessian (x g : ι → ℝ) (H : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  scalingMatrix x g * H * scalingMatrix x g + scaledCorrection g

/-- **Equation (13.12.5)** of [conn2000trust]. The **quadratic model** with value $c$, gradient $g$
and Hessian $H$ at the displacement $s$ is
$$c + g^T s + \tfrac12 s^T H s.$$
-/
noncomputable def affineQuadraticModel (c : ℝ) (g : ι → ℝ) (H : Matrix ι ι ℝ)
    (s : ι → ℝ) : ℝ :=
  c + g ⬝ᵥ s + (1 / 2) * (s ⬝ᵥ (H *ᵥ s))

/-- **Equation (13.12.6)** of [conn2000trust]. A vector $w$ solves the **scaled Newton system** if
$$(S H S + \bar G)\, w = -S g.$$
-/
def IsScaledNewtonStep (x g : ι → ℝ) (H : Matrix ι ι ℝ) (w : ι → ℝ) : Prop :=
  scaledHessian x g H *ᵥ w = -scaledGradient x g

/-- **Equation (13.12.7)** of [conn2000trust]. The **scaled model** at the scaled displacement $w$
is the quadratic model with gradient $S g$ and Hessian $\hat H = S H S + \bar G$:
$$c + (S g)^T w + \tfrac12 w^T (S H S + \bar G) w.$$
-/
noncomputable def scaledModel (c : ℝ) (x g : ι → ℝ) (H : Matrix ι ι ℝ) (w : ι → ℝ) : ℝ :=
  affineQuadraticModel c (scaledGradient x g) (scaledHessian x g H) w

/-- The **model correction** in the original coordinates, the diagonal matrix
$$C(x, g) = \operatorname{diag}\Big(\frac{\max\{g_i, 0\}}{|v_i(x, g)|}\Big).$$

At a coordinate with $v_i = 0$, Lean's division gives the entry $0$. The congruence
$S C S = \bar G$ is used only at strictly positive points. -/
noncomputable def unscaledCorrection (x g : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i ↦ max (g i) 0 / |scalingVector x g i|

/-- **Equation (13.12.8)** of [conn2000trust]. The **corrected model** in the original displacement
coordinates is the quadratic model with gradient $g$ and Hessian $H + C(x, g)$:
$$c + g^T s + \tfrac12 s^T (H + C(x, g)) s.$$
-/
noncomputable def unscaledModel (c : ℝ) (x g : ι → ℝ) (H : Matrix ι ι ℝ) (s : ι → ℝ) : ℝ :=
  affineQuadraticModel c g (H + unscaledCorrection x g) s

private theorem vecMul_scalingMatrix (x g w : ι → ℝ) :
    w ᵥ* scalingMatrix x g = scalingMatrix x g *ᵥ w := by
  ext i
  simp [scalingMatrix, Matrix.vecMul_diagonal, Matrix.mulVec_diagonal, mul_comm]

private theorem scaling_pullback_form (x g w : ι → ℝ) (A : Matrix ι ι ℝ) :
    w ⬝ᵥ ((scalingMatrix x g * A * scalingMatrix x g) *ᵥ w) =
      (scalingMatrix x g *ᵥ w) ⬝ᵥ (A *ᵥ (scalingMatrix x g *ᵥ w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    vecMul_scalingMatrix]

/-- **Equation (13.12.8)** of [conn2000trust]. If $x_i > 0$ for all $i$, then
$S(x, g)\, C(x, g)\, S(x, g) = \bar G$. -/
theorem scaling_unscaledCorrection {x g : ι → ℝ} (hx : ∀ i, 0 < x i) :
    scalingMatrix x g * unscaledCorrection x g * scalingMatrix x g = scaledCorrection g := by
  unfold scalingMatrix unscaledCorrection scaledCorrection
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have hv : 0 < |scalingVector x g i| := by
    by_cases h : 0 ≤ g i
    · simpa [scalingVector, h, abs_of_pos (hx i)] using hx i
    · simp [scalingVector, h]
  have hs := Real.sq_sqrt hv.le
  field_simp
  rw [hs, mul_comm]

/-- **Equation (13.12.8)** of [conn2000trust]. If $x_i > 0$ for all $i$, the scaled and the
corrected models agree under the change of variables $s = S w$: the scaled model at $w$ equals
the corrected model at $S w$. -/
theorem scaledModel_eq_unscaledModel (c : ℝ) {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    (H : Matrix ι ι ℝ) (w : ι → ℝ) :
    scaledModel c x g H w = unscaledModel c x g H (scalingMatrix x g *ᵥ w) := by
  have hess : scalingMatrix x g * (H + unscaledCorrection x g) * scalingMatrix x g =
      scaledHessian x g H := by
    rw [Matrix.mul_add, Matrix.add_mul, scaling_unscaledCorrection hx, scaledHessian]
  have hlin : (scalingMatrix x g *ᵥ g) ⬝ᵥ w = g ⬝ᵥ (scalingMatrix x g *ᵥ w) := by
    rw [dotProduct_comm (scalingMatrix x g *ᵥ g), Matrix.dotProduct_mulVec, vecMul_scalingMatrix,
      dotProduct_comm]
  unfold scaledModel unscaledModel affineQuadraticModel scaledGradient
  rw [← hess, scaling_pullback_form, hlin]


omit [DecidableEq ι] in
/-- Let $x \ge 0$. Then $x$ is first-order critical for $g$ on the nonnegative orthant if and only
if
$$g^T (y - x) \ge 0 \quad \text{for all } y \ge 0,$$
the variational form of the first-order condition. -/
theorem orthantFirstOrder_iff_variational {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    OrthantFirstOrder x g ↔ ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → 0 ≤ g ⬝ᵥ (y - x) := by
  classical
  constructor
  · intro h y hy
    apply Finset.sum_nonneg
    intro i _
    change 0 ≤ g i * (y i - x i)
    rcases (hx i).eq_or_lt with hxi | hxi
    · rw [← hxi, sub_zero]
      exact mul_nonneg (h i).1 (hy i)
    · simp [(h i).2 hxi]
  · intro h i
    have hplus : ∀ j, 0 ≤ (x + Pi.single i (1 : ℝ) : ι → ℝ) j := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa using add_nonneg (hx i) zero_le_one
      · simpa [Pi.single_eq_of_ne hj] using hx j
    have hgi := h _ hplus
    rw [add_sub_cancel_left, dotProduct_single, mul_one] at hgi
    refine ⟨hgi, fun hxi ↦ ?_⟩
    have hminus : ∀ j, 0 ≤ (x + Pi.single i (-x i) : ι → ℝ) j := by
      intro j
      by_cases hj : j = i
      · subst j
        simp
      · simpa [Pi.single_eq_of_ne hj] using hx j
    have hgi' := h _ hminus
    rw [add_sub_cancel_left, dotProduct_single, mul_neg, neg_nonneg] at hgi'
    exact le_antisymm (nonpos_of_mul_nonpos_left hgi' hxi) hgi

private theorem scaledGradient_eq_zero_iff {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    scaledGradient x g = 0 ↔ OrthantFirstOrder x g := by
  constructor
  · intro h i
    have he := congrFun h i
    simp only [scaledGradient, scalingMatrix, Matrix.mulVec_diagonal, Pi.zero_apply] at he
    have hg : 0 ≤ g i := by
      by_contra! hgi
      have hz : g i = 0 := by simpa [scalingVector, not_le.mpr hgi] using he
      exact hgi.ne hz
    refine ⟨hg, fun hxi ↦ ?_⟩
    rw [scalingVector, ite_eq_left hg, abs_of_nonneg (hx i)] at he
    exact (mul_eq_zero.mp he).resolve_left (Real.sqrt_pos.2 hxi).ne'
  · intro h
    ext i
    rw [scaledGradient, scalingMatrix, Matrix.mulVec_diagonal, Pi.zero_apply,
      scalingVector, ite_eq_left (h i).1, abs_of_nonneg (hx i)]
    rcases (hx i).eq_or_lt with hxi | hxi
    · simp [← hxi]
    · simp [(h i).2 hxi]

/-- **Theorem 13.12.1** of [conn2000trust]. Let $x \ge 0$. Then $x$ is first-order critical for $g$
on the nonnegative orthant if and only if
$$S(x, g)^2 g = 0 \quad\text{and}\quad S(x, g)\, g = 0.$$
-/
theorem theorem_13_12_1 {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    OrthantFirstOrder x g ↔
      (scalingMatrix x g * scalingMatrix x g) *ᵥ g = 0 ∧ scaledGradient x g = 0 := by
  constructor
  · intro h
    have hg := (scaledGradient_eq_zero_iff hx).mpr h
    exact ⟨by rw [← Matrix.mulVec_mulVec, show scalingMatrix x g *ᵥ g = 0 from hg,
      Matrix.mulVec_zero], hg⟩
  · intro h
    exact (scaledGradient_eq_zero_iff hx).mp h.2

private theorem scale_apply_of_firstOrder {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hg : OrthantFirstOrder x g) (w : ι → ℝ) (i : ι) :
    (scalingMatrix x g *ᵥ w) i = Real.sqrt (x i) * w i := by
  simp [scalingMatrix, Matrix.mulVec_diagonal, scalingVector, (hg i).1, abs_of_nonneg (hx i)]

private theorem scaledHessian_isSymm (x g : ι → ℝ) {H : Matrix ι ι ℝ} (hH : H.IsSymm) :
    (scaledHessian x g H).IsSymm := by
  have hA : (scalingMatrix x g * H * scalingMatrix x g).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [scalingMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hH.apply i j]
    ring
  exact hA.add (Matrix.isSymm_diagonal _)

private theorem scaledHessian_form (x g w : ι → ℝ) (H : Matrix ι ι ℝ) :
    w ⬝ᵥ (scaledHessian x g H *ᵥ w) =
      (scalingMatrix x g *ᵥ w) ⬝ᵥ (H *ᵥ (scalingMatrix x g *ᵥ w)) +
        ∑ i, max (g i) 0 * (w i) ^ 2 := by
  rw [scaledHessian, Matrix.add_mulVec, dotProduct_add, scaling_pullback_form]
  congr 1
  unfold dotProduct scaledCorrection
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  ring

/-- **Theorem 13.12.2** of [conn2000trust]. Let $x \ge 0$ and let $H$ be symmetric. Then $S g = 0$
if and only if $x$ is first-order critical for $g$. Moreover,
$$S g = 0 \text{ and } S H S + \bar G \text{ is positive semidefinite}$$
if and only if $x$ is weakly second-order critical for $g$ and $H$.

The diagonal $\bar G$ is nonnegative and acts only on the coordinates with $g_i > 0$. For a
direction $d$ on the active face, the proof takes the preimage $w$ with $w_i = 0$ on the active
coordinates, where $\bar G$ vanishes. -/
theorem theorem_13_12_2 {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i) {H : Matrix ι ι ℝ}
    (hH : H.IsSymm) :
    (scaledGradient x g = 0 ↔ OrthantFirstOrder x g) ∧
    (scaledGradient x g = 0 ∧ (scaledHessian x g H).PosSemidef ↔
      OrthantWeakSecondOrder x g H) := by
  refine ⟨scaledGradient_eq_zero_iff hx, ?_⟩
  constructor
  · rintro ⟨hg, hp⟩
    have hfirst := (scaledGradient_eq_zero_iff hx).mp hg
    refine ⟨hfirst, fun d hd ↦ ?_⟩
    let w (i : ι) := d i / Real.sqrt (x i)
    have hw : scalingMatrix x g *ᵥ w = d := by
      ext i
      rw [scale_apply_of_firstOrder hx hfirst]
      by_cases hxi : x i = 0
      · simp [hxi, hd i hxi]
      · have hp := Real.sqrt_pos.mpr (lt_of_le_of_ne (hx i) (Ne.symm hxi))
        dsimp [w]
        field_simp [hp.ne']
    have hsum : (∑ i, max (g i) 0 * (w i) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hxi : x i = 0
      · simp [w, hxi]
      · simp [(hfirst i).2 (lt_of_le_of_ne (hx i) (Ne.symm hxi))]
    have hh := hp.dotProduct_mulVec_nonneg w
    have hstar : star w = w := by ext i; simp
    rwa [hstar, scaledHessian_form, hw, hsum, add_zero] at hh
  · rintro ⟨hg, hh⟩
    refine ⟨(scaledGradient_eq_zero_iff hx).mpr hg, Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_iff_isSymm.mpr (scaledHessian_isSymm x g hH), fun w ↦ ?_⟩⟩
    have hstar : star w = w := by ext i; simp
    rw [hstar, scaledHessian_form]
    apply add_nonneg
    · apply hh
      intro i hi
      rw [scale_apply_of_firstOrder hx hg, hi, Real.sqrt_zero, zero_mul]
    · exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (le_max_right _ _) (sq_nonneg _)

/-- The **scaled gradient norm** $\|S(x, g)\, g\|_2$, the Euclidean norm of the scaled gradient. -/
noncomputable def scaledGradientNorm (x g : ι → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (scaledGradient x g)‖

/-- Continuity of the scaled gradient, used in the proof of Theorem 13.12.4 of [conn2000trust]. The
map $(x, g) \mapsto S(x, g)\, g$ is continuous. The factor $g_i$ removes the discontinuity of
$S$ where $g_i$ changes sign. -/
theorem continuous_scaledGradient :
    Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ scaledGradient xg.1 xg.2) := by
  have hform (x g : ι → ℝ) (i : ι) :
      scaledGradient x g i = Real.sqrt |x i| * max (g i) 0 + min (g i) 0 := by
    rw [scaledGradient, scalingMatrix, Matrix.mulVec_diagonal]
    by_cases h : 0 ≤ g i
    · simp [scalingVector, h]
    · have h' := (lt_of_not_ge h).le
      simp [scalingVector, h, max_eq_right h', min_eq_left h']
  apply continuous_pi
  intro i
  simp only [hform]
  have hx : Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ xg.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hg : Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ xg.2 i) :=
    (continuous_apply i).comp continuous_snd
  exact (hx.abs.sqrt.mul (hg.max continuous_const)).add (hg.min continuous_const)

/-- **Theorem 13.12.4** of [conn2000trust], limit points. Let $x_k \to x_0$ and $g_k \to g_0$ along
a nontrivial filter, let $x_k \ge 0$ eventually, and let $\|S(x_k, g_k)\, g_k\| \to 0$. Then
$x_0$ is first-order critical for $g_0$ on the nonnegative orthant. -/
theorem orthantFirstOrder_of_tendsto_scaledGradientNorm {α : Type*} {l : Filter α} [l.NeBot]
    {x g : α → ι → ℝ} {x₀ g₀ : ι → ℝ} (hx : Tendsto x l (𝓝 x₀))
    (hg : Tendsto g l (𝓝 g₀)) (hfeas : ∀ᶠ k in l, ∀ i, 0 ≤ x k i)
    (hzero : Tendsto (fun k ↦ scaledGradientNorm (x k) (g k)) l (𝓝 0)) :
    OrthantFirstOrder x₀ g₀ := by
  have hfeas₀ (i : ι) : 0 ≤ x₀ i :=
    ge_of_tendsto ((continuous_apply i).continuousAt.tendsto.comp hx)
      (hfeas.mono fun _ hk ↦ hk i)
  have hsg := continuous_scaledGradient.continuousAt.tendsto.comp (hx.prodMk_nhds hg)
  have hcoord : Continuous (fun z : ι → ℝ ↦ ‖WithLp.toLp 2 z‖) :=
    continuous_norm.comp (PiLp.continuous_toLp _ _)
  have hlim := hcoord.continuousAt.tendsto.comp hsg
  have hz : scaledGradientNorm x₀ g₀ = 0 := tendsto_nhds_unique hlim hzero
  have hh : scaledGradient x₀ g₀ = 0 := by
    have hz' : WithLp.toLp 2 (scaledGradient x₀ g₀) = 0 := norm_eq_zero.mp hz
    exact congrArg (WithLp.ofLp) hz'
  exact (scaledGradient_eq_zero_iff hfeas₀).mp hh

/-- The **distance to the boundary** of the nonnegative orthant,
$$\inf \{\|x - y\|_2 : y \in \partial \mathbb{R}^\iota_{\ge 0}\}.$$

When the boundary is empty (for empty $\iota$), the infimum of the empty set is $0$ in Lean. -/
noncomputable def orthantBoundaryDistance (x : ι → ℝ) : ℝ :=
  sInf ((fun y : ι → ℝ ↦ ‖WithLp.toLp 2 (x - y)‖) ''
    frontier (Optimization.nonnegativeOrthant ι))

omit [DecidableEq ι] in
private theorem orthantBoundaryDistance_le_coordinate {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) (i : ι) : orthantBoundaryDistance x ≤ x i := by
  classical
  let y := Function.update x i 0
  have hy : y ∈ frontier (Optimization.nonnegativeOrthant ι) := by
    refine Optimization.mem_frontier_nonnegativeOrthant.mpr ⟨fun j ↦ ?_, i, by simp [y]⟩
    by_cases h : j = i
    · simp [y, h]
    · simpa [y, Function.update_of_ne h] using (hx j).le
  have hb : BddBelow ((fun z : ι → ℝ ↦ ‖WithLp.toLp 2 (x - z)‖) ''
      frontier (Optimization.nonnegativeOrthant ι)) :=
    ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
  have hsq : ‖WithLp.toLp 2 (x - y)‖ ^ 2 = (x i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_eq_single i]
    · simp [y]
    · intro j _ hj
      simp [y, Function.update_of_ne hj]
    · simp
  have hn := (sq_le_sq₀ (norm_nonneg _) (hx i).le).mp hsq.le
  exact (csInf_le hb ⟨y, hy, rfl⟩).trans hn

/-- **Equation (13.12.11)** of [conn2000trust]. The **feasible times** on the scaled Cauchy ray
$t \mapsto x - t S^2 g$ with radius $\Delta$ and fraction $\sigma$ are the $t \ge 0$ with
$$t \|S g\| \le \Delta \quad\text{and}\quad \sigma \operatorname{dist}(x, \partial
  \mathbb{R}^\iota_{\ge 0}) \le \operatorname{dist}(x - t S^2 g, \partial \mathbb{R}^\iota_{\ge
  0}).$$

At a strictly positive point, $\|S^{-1} (S^2 g)\| = \|S g\|$, so the first condition is the
trust-region bound in the scaled norm. -/
def scaledCauchyTimes (x g : ι → ℝ) (Δ σ : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t * scaledGradientNorm x g ≤ Δ ∧
    σ * orthantBoundaryDistance x ≤
      orthantBoundaryDistance (x - t • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g))}

/-- **Equation (13.12.11)** of [conn2000trust]. A time $t_C$ is a **constrained scaled Cauchy time**
if it is a feasible time and it minimizes $t \mapsto m(-t S^2 g)$ over the feasible times, where
$m$ is the corrected model (13.12.8). -/
def IsScaledCauchyTime (c : ℝ) (x g : ι → ℝ) (H : Matrix ι ι ℝ) (Δ σ tC : ℝ) : Prop :=
  tC ∈ scaledCauchyTimes x g Δ σ ∧
    IsMinOn (fun t : ℝ ↦ unscaledModel c x g H
      ((-t) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)))
      (scaledCauchyTimes x g Δ σ) tC

private theorem scaledGradientNorm_sq (x g : ι → ℝ) :
    scaledGradientNorm x g ^ 2 = scaledGradient x g ⬝ᵥ scaledGradient x g := by
  rw [scaledGradientNorm, EuclideanSpace.real_norm_sq_eq]
  unfold dotProduct
  simp only [pow_two]

/-- **Equation (13.12.12)** of [conn2000trust]. Let $x_i > 0$ for all $i$. Then for every $t$ the
corrected model along the scaled Cauchy ray is
$$m(-t S^2 g) = c - t \|S g\|^2 + \tfrac12 t^2 (S g)^T (S H S + \bar G)(S g).$$

**Correction.** The curvature along the ray is that of the scaled Hessian
$\hat H = S H S + \bar G$, which includes the positive-gradient diagonal $\bar G$. -/
theorem unscaledModel_along_scaledRay (c : ℝ) {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    (H : Matrix ι ι ℝ) (t : ℝ) :
    unscaledModel c x g H ((-t) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) =
      c - t * scaledGradientNorm x g ^ 2 +
        (1 / 2) * t ^ 2 * (scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g)) := by
  have hscale : scalingMatrix x g *ᵥ ((-t) • scaledGradient x g) =
      (-t) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g) := by
    rw [Matrix.mulVec_smul, scaledGradient, Matrix.mulVec_mulVec]
  rw [← hscale, ← scaledModel_eq_unscaledModel c hx, scaledModel, affineQuadraticModel]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    ← scaledGradientNorm_sq]
  ring

omit [DecidableEq ι] in
private theorem orthantBoundaryDistance_ge_of_coordinate_fraction [Nonempty ι]
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) {σ : ℝ} (hσ : 0 < σ)
    (hy : ∀ i, σ * x i ≤ y i) :
    σ * orthantBoundaryDistance x ≤ orthantBoundaryDistance y := by
  let C := Optimization.nonnegativeOrthant ι
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hfront : (frontier C).Nonempty :=
    ⟨0, Optimization.mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, i, rfl⟩⟩
  apply le_csInf (hfront.image (fun z : ι → ℝ ↦ ‖WithLp.toLp 2 (y - z)‖))
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨_, j, hj⟩ := Optimization.mem_frontier_nonnegativeOrthant.mp hz
  have hypos := (mul_pos hσ (hx j)).trans_le (hy j)
  calc
    σ * orthantBoundaryDistance x ≤ σ * x j :=
      mul_le_mul_of_nonneg_left (orthantBoundaryDistance_le_coordinate hx j) hσ.le
    _ ≤ y j := hy j
    _ = ‖(WithLp.toLp 2 (y - z) : EuclideanSpace ℝ ι) j‖ := by
      simp [hj, Real.norm_eq_abs, abs_of_pos hypos]
    _ ≤ ‖WithLp.toLp 2 (y - z)‖ := PiLp.norm_apply_le _ _

private theorem scaledCauchyTimes_of_cap [Nonempty ι] {x g : ι → ℝ}
    (hx : ∀ i, 0 < x i) {Δ σ t κ : ℝ} (hσ₀ : 0 < σ) (hσ : σ ≤ 1)
    (hκ : 0 < κ) (hg : ∀ i, g i ≤ κ) (ht : 0 ≤ t)
    (hΔ : t * scaledGradientNorm x g ≤ Δ) (hcap : t ≤ (1 - σ) / κ) :
    t ∈ scaledCauchyTimes x g Δ σ :=
  ⟨ht, hΔ, orthantBoundaryDistance_ge_of_coordinate_fraction hx hσ₀
    (scaledRay_coordinate_lower_bound (fun i ↦ (hx i).le) ht hσ hκ hg hcap)⟩

/-- **Theorem 13.12.3** of [conn2000trust]. Let $\iota$ be nonempty, $x_i > 0$ for all $i$,
$\Delta \ge 0$, $0 < \sigma < 1$, $\kappa > 0$ with $g_i \le \kappa$ for all $i$, and
$\beta > 0$ with
$$(S g)^T (S H S + \bar G)(S g) \le \beta \|S g\|^2.$$
If $t_C$ is a constrained scaled Cauchy time, then
$$c - m(-t_C S^2 g) \ge \tfrac12 \|S g\|^2 \min\Big\{\frac1\beta, \frac{\Delta}{\|S g\|},
  \frac{1 - \sigma}{\kappa}\Big\}.$$

**Correction.** The printed bound has no fraction-to-boundary term, and it fails: see
`ConnGouldToint.Chapter13.theorem_13_12_3_counterexample`. The fraction-to-boundary cap
$(1 - \sigma)/\kappa$ limits the ray parameter, so it enters the minimum before the
multiplication by $\|S g\|^2$.

The curvature hypothesis is the upper bound along the ray supplied by (8.1.22). If $S g = 0$,
Lean's division gives $\Delta / \|S g\| = 0$, and both sides are zero. -/
theorem theorem_13_12_3 [Nonempty ι] (c : ℝ) {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    (H : Matrix ι ι ℝ) {Δ σ κ β tC : ℝ} (hΔ : 0 ≤ Δ) (hσ₀ : 0 < σ) (hσ : σ < 1)
    (hκ : 0 < κ) (hg : ∀ i, g i ≤ κ) (hβ : 0 < β)
    (hcurv : scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g) ≤
      β * scaledGradientNorm x g ^ 2)
    (hmin : IsScaledCauchyTime c x g H Δ σ tC) :
    (1 / 2) * scaledGradientNorm x g ^ 2 *
      min (1 / β) (min (Δ / scaledGradientNorm x g) ((1 - σ) / κ)) ≤
      c - unscaledModel c x g H ((-tC) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) := by
  let n := scaledGradientNorm x g
  let t := min (1 / β) (min (Δ / n) ((1 - σ) / κ))
  have hn : 0 ≤ n := norm_nonneg _
  have ht : 0 ≤ t := le_min (div_nonneg zero_le_one hβ.le)
    (le_min (div_nonneg hΔ hn) (div_nonneg (sub_nonneg.mpr hσ.le) hκ.le))
  have htβ : t * β ≤ 1 := (le_div_iff₀ hβ).mp (min_le_left _ _)
  have htΔ : t * n ≤ Δ := by
    rcases hn.eq_or_lt with hn₀ | hn'
    · simpa [← hn₀] using hΔ
    · exact (le_div_iff₀ hn').mp ((min_le_right _ _).trans (min_le_left _ _))
  have hcap : t ≤ (1 - σ) / κ := (min_le_right _ _).trans (min_le_right _ _)
  have hfeas := scaledCauchyTimes_of_cap hx hσ₀ hσ.le hκ hg ht htΔ hcap
  have hcmp := isMinOn_iff.mp hmin.2 t hfeas
  change unscaledModel c x g H ((-tC) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) ≤
    unscaledModel c x g H ((-t) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) at hcmp
  rw [unscaledModel_along_scaledRay c hx H t] at hcmp
  have hq : t ^ 2 * (scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g)) ≤
      t * n ^ 2 := calc
    _ ≤ t ^ 2 * (β * n ^ 2) := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    _ = (t * β) * (t * n ^ 2) := by ring
    _ ≤ 1 * (t * n ^ 2) := mul_le_mul_of_nonneg_right htβ (mul_nonneg ht (sq_nonneg _))
    _ = _ := one_mul _
  change (1 / 2) * n ^ 2 * t ≤ _
  change _ ≤ c - t * n ^ 2 +
    (1 / 2) * t ^ 2 * (scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g)) at hcmp
  nlinarith only [hcmp, hq]

/-- Sufficient decrease at the constrained scaled Cauchy point, a hypothesis check for Theorem
13.12.4 of [conn2000trust]. Let the hypotheses of Theorem 13.12.3 hold with $\beta \ge 1$, and
let $0 < \alpha \le 1$ with $\alpha \le (1 - \sigma) / \kappa$. Then
$$c - m(-t_C S^2 g) \ge \frac\alpha2 \|S g\| \min\Big\{\frac{\|S g\|}{\beta}, \Delta\Big\}.$$

This is the sufficient decrease condition AA.1b in the scaled gradient norm, with the
coefficient $\alpha / 2$. -/
theorem scaledCauchyTime_sufficientDecrease [Nonempty ι] (c : ℝ)
    {x g : ι → ℝ} (hx : ∀ i, 0 < x i) (H : Matrix ι ι ℝ) {Δ σ κ β tC α : ℝ}
    (hΔ : 0 ≤ Δ) (hσ₀ : 0 < σ) (hσ : σ < 1) (hκ : 0 < κ)
    (hg : ∀ i, g i ≤ κ) (hβ : 1 ≤ β) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hcap : α ≤ (1 - σ) / κ)
    (hcurv : scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g) ≤
      β * scaledGradientNorm x g ^ 2)
    (hmin : IsScaledCauchyTime c x g H Δ σ tC) :
    (α / 2) * scaledGradientNorm x g * min (scaledGradientNorm x g / β) Δ ≤
      c - unscaledModel c x g H ((-tC) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) := by
  have hβ₀ : 0 < β := zero_lt_one.trans_le hβ
  have h := theorem_13_12_3 c hx H hΔ hσ₀ hσ hκ hg hβ₀ hcurv hmin
  let n := scaledGradientNorm x g
  let a := min (1 / β) (Δ / n)
  have hn : 0 ≤ n := norm_nonneg _
  have ha : 0 ≤ a := le_min (div_nonneg zero_le_one hβ₀.le) (div_nonneg hΔ hn)
  have ha₁ : a ≤ 1 := (min_le_left _ _).trans ((div_le_one hβ₀).mpr hβ)
  have hαa : α * a ≤ a := mul_le_of_le_one_left ha hα₁
  have hb : α * a ≤ min (1 / β) (min (Δ / n) ((1 - σ) / κ)) :=
    le_min (hαa.trans (min_le_left _ _)) (le_min (hαa.trans (min_le_right _ _))
      ((mul_le_of_le_one_right hα.le ha₁).trans hcap))
  have hl := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (sq_nonneg n))
  have he : (α / 2) * n * min (n / β) Δ = (1 / 2) * n ^ 2 * (α * a) := by
    rcases hn.eq_or_lt with hzero | hp
    · simp [← hzero]
    have he' : n * a = min (n / β) Δ := by
      unfold a
      rw [mul_min_of_nonneg _ _ hn]
      congr 1
      · ring
      · rw [mul_comm, div_mul_cancel₀ _ hp.ne']
    rw [← he']
    ring
  rw [he]
  exact hl.trans h

/-- **Equation (13.12.23)** of [conn2000trust]. For a unit vector $z$, the **feasible eigenpoint
times** are the $t$ with $0 \le t \le \Delta$ and
$$\sigma \operatorname{dist}(x, \partial \mathbb{R}^\iota_{\ge 0}) \le \operatorname{dist}(x - t
  S z, \partial \mathbb{R}^\iota_{\ge 0}).$$
-/
def scaledEigenTimes (x g z : ι → ℝ) (Δ σ : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t ≤ Δ ∧ σ * orthantBoundaryDistance x ≤
    orthantBoundaryDistance (x - t • (scalingMatrix x g *ᵥ z))}

/-- **Equation (13.12.23)** of [conn2000trust]. A time $t_C$ is a **constrained scaled eigenpoint
time** if it is a feasible eigenpoint time and it minimizes $t \mapsto m(-t S z)$ over these
times, where $m$ is the corrected model (13.12.8). -/
def IsScaledEigenTime (c : ℝ) (x g z : ι → ℝ) (H : Matrix ι ι ℝ) (Δ σ tC : ℝ) : Prop :=
  tC ∈ scaledEigenTimes x g z Δ σ ∧
    IsMinOn (fun t : ℝ ↦ unscaledModel c x g H ((-t) • (scalingMatrix x g *ᵥ z)))
      (scaledEigenTimes x g z Δ σ) tC

private theorem scaledEigen_coordinate_bound {x g z : ι → ℝ} {H : Matrix ι ι ℝ}
    {τ A K : ℝ} (hK : 0 ≤ K)
    (heig : scaledHessian x g H *ᵥ z = τ • z)
    (hH : ∀ i, |(H *ᵥ (scalingMatrix x g *ᵥ z)) i| ≤ K)
    (hscale : ∀ i, 0 < (scalingMatrix x g *ᵥ z) i →
      |scalingVector x g i| ≤ A * x i) (i : ι) :
    (-τ) * (scalingMatrix x g *ᵥ z) i ≤ A * K * x i ∨
      (scalingMatrix x g *ᵥ z) i ≤ 0 := by
  let a := Real.sqrt |scalingVector x g i|
  let q := (H *ᵥ (scalingMatrix x g *ᵥ z)) i
  let d := (scalingMatrix x g *ᵥ z) i
  rcases le_or_gt d 0 with hd | hd
  · exact Or.inr hd
  have hentry := congrFun heig i
  simp only [scaledHessian, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply,
    scalingMatrix, Matrix.mulVec_diagonal, scaledCorrection, Pi.smul_apply, smul_eq_mul] at hentry
  change a * q + max (g i) 0 * z i = τ * z i at hentry
  have hdform : d = a * z i := Matrix.mulVec_diagonal _ _ _
  have ha : a * a = |scalingVector x g i| := Real.mul_self_sqrt (abs_nonneg _)
  have hprod := congrArg (fun r : ℝ ↦ a * r) hentry
  have heq : (max (g i) 0 - τ) * d = -(|scalingVector x g i| * q) := by
    rw [hdform, ← ha]
    nlinarith only [hprod]
  left
  calc
    (-τ) * d ≤ (max (g i) 0 - τ) * d :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_right (g i) 0]) hd.le
    _ = -(|scalingVector x g i| * q) := heq
    _ = |scalingVector x g i| * (-q) := by ring
    _ ≤ |scalingVector x g i| * K :=
      mul_le_mul_of_nonneg_left ((neg_le_abs q).trans (hH i)) (abs_nonneg _)
    _ ≤ (A * x i) * K := mul_le_mul_of_nonneg_right (hscale i hd) hK
    _ = A * K * x i := by ring

private theorem scaledModel_onEigenRay (c : ℝ) {x g z : ι → ℝ} (hx : ∀ i, 0 < x i)
    {H : Matrix ι ι ℝ} {τ : ℝ} (heig : scaledHessian x g H *ᵥ z = τ • z)
    (hz : ‖WithLp.toLp 2 z‖ = 1) (t : ℝ) :
    unscaledModel c x g H ((-t) • (scalingMatrix x g *ᵥ z)) =
      c - t * (scaledGradient x g ⬝ᵥ z) + (1 / 2) * t ^ 2 * τ := by
  have hzz : z ⬝ᵥ z = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)
    rw [hz, one_pow] at h
    simpa only [dotProduct, pow_two] using h.symm
  rw [← Matrix.mulVec_smul, ← scaledModel_eq_unscaledModel c hx]
  simp only [scaledModel, affineQuadraticModel, Matrix.mulVec_smul, heig, dotProduct_smul,
    smul_dotProduct, hzz, smul_eq_mul]
  ring

/-- **Theorem 13.12.5** of [conn2000trust]. Let $\iota$ be nonempty, $x_i > 0$ for all $i$,
$\Delta \ge 0$ and $0 < \sigma < 1$. Let $z$ be a unit eigenvector of $\hat H = S H S + \bar G$
with eigenvalue $\tau < 0$, oriented so that $(S g)^T z \ge 0$. Let $A, K > 0$ satisfy
$|(H S z)_i| \le K$ for all $i$, and $|v_i(x, g)| \le A x_i$ for every $i$ with $(S z)_i > 0$.
If $t_C$ is a constrained scaled eigenpoint time, then
$$c - m(-t_C S z) \ge \tfrac12 (-\tau) \min\Big\{\Delta, \frac{(1 - \sigma)(-\tau)}{A
  K}\Big\}^2.$$

**Correction.** The source states the bound at the Cauchy point, with a negative lower bound.
The statement here uses the constrained scaled eigenpoint and gives a positive lower bound.

The bound on the scaling weights is needed on every coordinate that decreases along the ray
$-t S z$. It follows from the definition of $v$ on the coordinates with $g_i \ge 0$. -/
theorem theorem_13_12_5 [Nonempty ι] (c : ℝ) {x g z : ι → ℝ} (hx : ∀ i, 0 < x i)
    {H : Matrix ι ι ℝ} {τ A K Δ σ tC : ℝ} (hτ : τ < 0) (hA : 0 < A) (hK : 0 < K)
    (hΔ : 0 ≤ Δ) (hσ₀ : 0 < σ) (hσ : σ < 1)
    (heig : scaledHessian x g H *ᵥ z = τ • z) (hz : ‖WithLp.toLp 2 z‖ = 1)
    (hdescent : 0 ≤ scaledGradient x g ⬝ᵥ z)
    (hH : ∀ i, |(H *ᵥ (scalingMatrix x g *ᵥ z)) i| ≤ K)
    (hscale : ∀ i, 0 < (scalingMatrix x g *ᵥ z) i →
      |scalingVector x g i| ≤ A * x i)
    (hmin : IsScaledEigenTime c x g z H Δ σ tC) :
    (1 / 2) * (-τ) * (min Δ ((1 - σ) * (-τ) / (A * K))) ^ 2 ≤
      c - unscaledModel c x g H ((-tC) • (scalingMatrix x g *ᵥ z)) := by
  let t := min Δ ((1 - σ) * (-τ) / (A * K))
  have hτ' : 0 < -τ := neg_pos.mpr hτ
  have hAK := mul_pos hA hK
  have ht : 0 ≤ t := le_min hΔ
    (div_nonneg (mul_nonneg (sub_nonneg.mpr hσ.le) hτ'.le) hAK.le)
  have hcap : t * (A * K) ≤ (1 - σ) * (-τ) := (le_div_iff₀ hAK).mp (min_le_right _ _)
  have hcoord (i : ι) : σ * x i ≤ (x - t • (scalingMatrix x g *ᵥ z)) i := by
    change σ * x i ≤ x i - t * (scalingMatrix x g *ᵥ z) i
    rcases scaledEigen_coordinate_bound hK.le heig hH hscale i with hb | hb
    · have h₁ := mul_le_mul_of_nonneg_left hb ht
      have h₂ := mul_le_mul_of_nonneg_right hcap (hx i).le
      have h₃ : (-τ) * (t * (scalingMatrix x g *ᵥ z) i) ≤ (-τ) * ((1 - σ) * x i) := by
        nlinarith only [h₁, h₂]
      have h₄ := le_of_mul_le_mul_left h₃ hτ'
      nlinarith only [h₄]
    · have h₁ := mul_nonpos_of_nonneg_of_nonpos ht hb
      have h₂ := mul_le_mul_of_nonneg_right hσ.le (hx i).le
      linarith only [h₁, h₂]
  have hfeas : t ∈ scaledEigenTimes x g z Δ σ :=
    ⟨ht, min_le_left _ _, orthantBoundaryDistance_ge_of_coordinate_fraction hx hσ₀ hcoord⟩
  have hcmp := isMinOn_iff.mp hmin.2 t hfeas
  change unscaledModel c x g H ((-tC) • (scalingMatrix x g *ᵥ z)) ≤
    unscaledModel c x g H ((-t) • (scalingMatrix x g *ᵥ z)) at hcmp
  rw [scaledModel_onEigenRay c hx heig hz t] at hcmp
  change (1 / 2) * (-τ) * t ^ 2 ≤ _
  linarith [mul_nonneg ht hdescent]

/-- **Equation (13.12.24)** of [conn2000trust], the acceptance ratio of Algorithm 13.12.2. With the
corrected model $m$ of (13.12.8) at $x$,
$$\rho = \frac{f(x) - f(x + s) - \frac12 s^T C(x, g)\, s}{m(0) - m(s)}.$$
The numerator subtracts the same quadratic correction that the model adds. -/
noncomputable def colemanLiAcceptanceRatio (f : (ι → ℝ) → ℝ) (x g s : ι → ℝ)
    (H : Matrix ι ι ℝ) : ℝ :=
  (f x - f (x + s) - (1 / 2) * (s ⬝ᵥ (unscaledCorrection x g *ᵥ s))) /
    (unscaledModel (f x) x g H 0 - unscaledModel (f x) x g H s)

/-- **Equation (13.12.24)** of [conn2000trust]. If $m(0) - m(s) \neq 0$, then
$$\rho - 1 = \frac{q(s) - f(x + s)}{m(0) - m(s)},$$
where $q(s) = f(x) + g^T s + \frac12 s^T H s$ is the uncorrected model. So only the error of the
uncorrected model enters the ratio. -/
theorem colemanLiAcceptanceRatio_sub_one (f : (ι → ℝ) → ℝ) (x g s : ι → ℝ)
    (H : Matrix ι ι ℝ)
    (hp : unscaledModel (f x) x g H 0 - unscaledModel (f x) x g H s ≠ 0) :
    colemanLiAcceptanceRatio f x g s H - 1 =
      (affineQuadraticModel (f x) g H s - f (x + s)) /
        (unscaledModel (f x) x g H 0 - unscaledModel (f x) x g H s) := by
  rw [colemanLiAcceptanceRatio, div_sub_one hp]
  congr 1
  simp [unscaledModel, affineQuadraticModel, Matrix.add_mulVec, dotProduct_add]
  ring

/-- **Algorithms 13.12.1 and 13.12.2** of [conn2000trust]. The two versions of the Coleman–Li
algorithm. The second version changes the acceptance ratio to (13.12.24) and keeps the scaled
model, the step tests and the radius rules of the first. -/
inductive ColemanLiVersion
  /-- Algorithm 13.12.1, with the ordinary ratio (13.12.10). -/
  | first
  /-- Algorithm 13.12.2, with the corrected ratio (13.12.24). -/
  | second

/-- **Algorithm 13.12.1** of [conn2000trust], Step 1, trust-region norm. The **scaled norm** of a
step $s$ is
$$\|S(x, g)^{-1} s\|_2 = \Big(\sum_i \frac{s_i^2}{|v_i(x, g)|}\Big)^{1/2}.$$

It is the Euclidean norm of the vector of quotients $s_i / |v_i|^{1/2}$, which is $S^{-1} s$ at
a strictly positive point. -/
noncomputable def colemanLiScaledNorm (x g s : ι → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (fun i ↦ s i / Real.sqrt |scalingVector x g i|)‖

/-- **Equations (13.12.10) and (13.12.24)** of [conn2000trust]. The trial ratio of the given
version. The first version uses
$$\frac{f(x) - f(x + s)}{m(0) - m(s)},$$
and the second uses the corrected ratio (13.12.24). The denominator is the same in both
versions. -/
noncomputable def colemanLiTrialRatio (version : ColemanLiVersion)
    (f : (ι → ℝ) → ℝ) (x g s : ι → ℝ) (H : Matrix ι ι ℝ) : ℝ :=
  match version with
  | .first => (f x - f (x + s)) / (unscaledModel (f x) x g H 0 - unscaledModel (f x) x g H s)
  | .second => colemanLiAcceptanceRatio f x g s H

/-- **Algorithms 13.12.1 and 13.12.2** of [conn2000trust], Step 3. The next iterate is $x + s$ if
the trial ratio of the given version is at least $\eta_1$, and $x$ otherwise. -/
noncomputable def colemanLiAcceptedPoint (version : ColemanLiVersion) (P : Chapter06.BTRParams)
    (f : (ι → ℝ) → ℝ) (x g s : ι → ℝ) (H : Matrix ι ι ℝ) : ι → ℝ :=
  if P.η₁ ≤ colemanLiTrialRatio version f x g s H then x + s else x

private def colemanLiUnitDirections : Set (ι → ℝ) :=
  {w | ‖WithLp.toLp 2 w‖ = 1}

/-- **Algorithms 13.12.1 and 13.12.2** of [conn2000trust]. A run of the Coleman–Li algorithm in the
given version. It consists of iterates $x_k$, steps $s_k$, gradients $g_k = \nabla f(x_k)$,
symmetric model Hessians $H_k$, radii $\Delta_k$ and fractions $\sigma_k \in (0, \sigma_{\max}]$
with $\sigma_{\max} < 1$. The starting point is strictly positive and $\Delta_0 > 0$. Each step
satisfies the scaled trust-region bound $\|S_k^{-1} s_k\| \le \Delta_k$, the trial point
$x_k + s_k$ is strictly positive with
$$\sigma_k \operatorname{dist}(x_k, \partial \mathbb{R}^\iota_{\ge 0}) \le
  \operatorname{dist}(x_k + s_k, \partial \mathbb{R}^\iota_{\ge 0}),$$
and the predicted decrease $\mathrm{pred}_k$ of the corrected model is positive. With
$q(w) = w^T \hat H_k w$, $\beta_k = 1 + \sup_{\|w\| = 1} |q(w)|$,
$\tau_k = \inf_{\|w\| = 1} q(w)$ and $\pi_k = \min\{\|S_k g_k\|, \epsilon\}$, the steps satisfy
$$\kappa_{\mathrm{mdc}}\, \pi_k \min\Big\{\frac{\pi_k}{\beta_k}, \Delta_k\Big\} \le
  \mathrm{pred}_k,$$
and, if $\tau_k < 0$, also $\kappa_{\mathrm{sod}} |\tau_k| \min\{\tau_k^2, \Delta_k^2,
\bar\Delta^2\} \le \mathrm{pred}_k$ for a fixed cap $\bar\Delta > 0$. The iterates and radii
follow Step 3 and the radius rule (6.1.5) with the trial ratio of the version.

**Correction.** The boundary-distance test (13.12.9) alone also admits points outside the
orthant, since the distance is unsigned (see
`ConnGouldToint.Chapter13.colemanLi_unsigned_clearance_counterexample`). The run therefore also
requires that each trial point is strictly positive.

The Rayleigh quotients for AA.1b and AA.2b use Euclidean unit directions after scaling. -/
structure ColemanLiRun (version : ColemanLiVersion) (P : Chapter06.BTRParams)
    (f : (ι → ℝ) → ℝ) where
  /-- The iterates $x_k$. -/
  x : ℕ → ι → ℝ
  /-- The trial steps $s_k$. -/
  s : ℕ → ι → ℝ
  /-- The gradient coordinates $g_k$ at the iterates. -/
  g : ℕ → ι → ℝ
  /-- The model Hessians $H_k$. -/
  H : ℕ → Matrix ι ι ℝ
  /-- The trust-region radii $\Delta_k$. -/
  Δ : ℕ → ℝ
  /-- The fraction-to-boundary parameters $\sigma_k$. -/
  σ : ℕ → ℝ
  /-- The upper bound $\sigma_{\max}$ of the fraction-to-boundary parameters. -/
  σmax : ℝ
  /-- The cap $\epsilon$ on the criticality measure in the Cauchy decrease test. -/
  ε : ℝ
  /-- The constant $\kappa_{\mathrm{mdc}}$ of the Cauchy decrease test. -/
  κmdc : ℝ
  /-- The constant $\kappa_{\mathrm{sod}}$ of the second-order decrease test. -/
  κsod : ℝ
  /-- The cap $\bar\Delta$ on the radius in the second-order decrease test. -/
  cap : ℝ
  /-- The starting point is strictly positive. -/
  initial_interior : ∀ i, 0 < x 0 i
  /-- The initial radius is positive. -/
  initial_radius_pos : 0 < Δ 0
  /-- The largest fraction satisfies $0 < \sigma_{\max} < 1$. -/
  fraction_max : σmax ∈ Set.Ioo (0 : ℝ) 1
  /-- Each fraction satisfies $0 < \sigma_k \le \sigma_{\max}$. -/
  fraction : ∀ k, σ k ∈ Set.Ioc (0 : ℝ) σmax
  /-- The criticality cap $\epsilon$ is positive. -/
  epsilon_pos : 0 < ε
  /-- The Cauchy decrease constant satisfies $0 < \kappa_{\mathrm{mdc}} < 1$. -/
  cauchy_constant : κmdc ∈ Set.Ioo (0 : ℝ) 1
  /-- The second-order decrease constant satisfies $0 < \kappa_{\mathrm{sod}} < 1/2$. -/
  curvature_constant : κsod ∈ Set.Ioo (0 : ℝ) (1 / 2)
  /-- The radius cap of the second-order decrease test is positive. -/
  cap_pos : 0 < cap
  /-- The objective is differentiable at every iterate. -/
  objective_differentiable : ∀ k, DifferentiableAt ℝ f (x k)
  /-- The vector $g_k$ represents the derivative of $f$ at $x_k$: $f'(x_k) v = g_k^T v$. -/
  gradient_eq : ∀ k v, fderiv ℝ f (x k) v = g k ⬝ᵥ v
  /-- Each model Hessian $H_k$ is symmetric. -/
  hessian_symmetric : ∀ k, (H k).IsSymm
  /-- Each step satisfies the scaled trust-region bound $\|S_k^{-1} s_k\| \le \Delta_k$. -/
  trust_region : ∀ k, colemanLiScaledNorm (x k) (g k) (s k) ≤ Δ k
  /-- Each trial point $x_k + s_k$ is strictly positive. -/
  trial_interior : ∀ k i, 0 < (x k + s k) i
  /-- Each trial point satisfies the fraction-to-boundary test $\sigma_k \operatorname{dist}(x_k,
  \partial \mathbb{R}^\iota_{\ge 0}) \le \operatorname{dist}(x_k + s_k, \partial
  \mathbb{R}^\iota_{\ge 0})$. -/
  trial_clearance : ∀ k, σ k * orthantBoundaryDistance (x k) ≤
    orthantBoundaryDistance (x k + s k)
  /-- The predicted decrease $m_k(0) - m_k(s_k)$ of the corrected model is positive. -/
  predicted_pos : ∀ k, 0 < unscaledModel (f (x k)) (x k) (g k) (H k) 0 -
    unscaledModel (f (x k)) (x k) (g k) (H k) (s k)
  /-- Each step satisfies the Cauchy decrease test $\kappa_{\mathrm{mdc}} \pi_k \min\{\pi_k /
  \beta_k, \Delta_k\} \le \mathrm{pred}_k$ and, if $\tau_k < 0$, the second-order test
  $\kappa_{\mathrm{sod}} |\tau_k| \min\{\tau_k^2, \Delta_k^2, \bar\Delta^2\} \le
  \mathrm{pred}_k$. -/
  sufficient_decrease : ∀ k,
    let q := fun w ↦ w ⬝ᵥ (scaledHessian (x k) (g k) (H k) *ᵥ w)
    let β := 1 + sSup ((fun w ↦ |q w|) '' colemanLiUnitDirections)
    let τ := sInf (q '' colemanLiUnitDirections)
    let π := min (scaledGradientNorm (x k) (g k)) ε
    let pred := unscaledModel (f (x k)) (x k) (g k) (H k) 0 -
      unscaledModel (f (x k)) (x k) (g k) (H k) (s k)
    κmdc * π * min (π / β) (Δ k) ≤ pred ∧
      (τ < 0 → κsod * |τ| * min (min (τ ^ 2) (Δ k ^ 2)) (cap ^ 2) ≤ pred)
  /-- The next iterate follows Step 3 with the trial ratio of the version. -/
  iterate_update : ∀ k,
    x (k + 1) = colemanLiAcceptedPoint version P f (x k) (g k) (s k) (H k)
  /-- The radius follows the update rule (6.1.5) with the trial ratio of the version. -/
  radius_update : ∀ k, Chapter06.BTRRadiusUpdate P
    (colemanLiTrialRatio version f (x k) (g k) (s k) (H k)) (Δ k) (Δ (k + 1))

/-- **Algorithms 13.12.1 and 13.12.2** of [conn2000trust], strict feasibility. Every iterate $x_k$
of a Coleman–Li run is strictly positive. -/
theorem ColemanLiRun.interior_iterate {version : ColemanLiVersion} {P : Chapter06.BTRParams}
    {f : (ι → ℝ) → ℝ} (r : ColemanLiRun version P f) (k : ℕ) :
    ∀ i, 0 < r.x k i := by
  induction k with
  | zero => exact r.initial_interior
  | succ k ih =>
    rw [r.iterate_update, colemanLiAcceptedPoint]
    split
    · exact r.trial_interior k
    · exact ih

/-- **Algorithm 13.12.1** of [conn2000trust], Step 4. Every radius $\Delta_k$ of a Coleman–Li run is
positive. -/
theorem ColemanLiRun.radius_pos {version : ColemanLiVersion} {P : Chapter06.BTRParams}
    {f : (ι → ℝ) → ℝ} (r : ColemanLiRun version P f) (k : ℕ) : 0 < r.Δ k := by
  induction k with
  | zero => exact r.initial_radius_pos
  | succ k ih => exact (r.radius_update k).pos ih

/-- Counterexample for the boundary-distance test (13.12.9) of [conn2000trust]: the test does not
imply strict feasibility. There are $x, s \in \mathbb{R}^1$ with $x > 0$ and
$$\tfrac12 \operatorname{dist}(x, \partial \mathbb{R}_{\ge 0}) \le \operatorname{dist}(x + s,
  \partial \mathbb{R}_{\ge 0})$$
for which $x + s$ is not positive. In dimension one, reflection through zero preserves the
distance to the boundary. -/
theorem colemanLi_unsigned_clearance_counterexample :
    ∃ x s : Fin 1 → ℝ, (∀ i, 0 < x i) ∧
      (1 / 2 : ℝ) * orthantBoundaryDistance x ≤ orthantBoundaryDistance (x + s) ∧
      ¬ ∀ i, 0 < (x + s) i := by
  have hfront : frontier (Optimization.nonnegativeOrthant (Fin 1)) = {0} := by
    ext z
    constructor
    · intro hz
      obtain ⟨_, i, hi⟩ := Optimization.mem_frontier_nonnegativeOrthant.mp hz
      exact Set.mem_singleton_iff.mpr (funext fun j ↦ (congrArg z (Subsingleton.elim j i)).trans hi)
    · rintro hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Optimization.mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, 0, rfl⟩
  have hdist (a : ℝ) : orthantBoundaryDistance (fun _ : Fin 1 ↦ a) = |a| := by
    rw [orthantBoundaryDistance, hfront, Set.image_singleton, csInf_singleton, sub_zero]
    apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one, sq_abs]
  refine ⟨fun _ ↦ 1, fun _ ↦ -2, fun _ ↦ zero_lt_one, ?_, ?_⟩
  · change (1 / 2 : ℝ) * orthantBoundaryDistance (fun _ : Fin 1 ↦ 1) ≤
      orthantBoundaryDistance (fun _ : Fin 1 ↦ 1 + -2)
    rw [hdist, hdist]
    norm_num
  · intro h
    have hh := h 0
    change (0 : ℝ) < 1 + -2 at hh
    norm_num at hh

private theorem colemanLiCorrection_nonneg (x g s : ι → ℝ) :
    0 ≤ s ⬝ᵥ (unscaledCorrection x g *ᵥ s) := by
  unfold unscaledCorrection dotProduct
  apply Finset.sum_nonneg
  intro i _
  rw [Matrix.mulVec_diagonal]
  rw [show s i * (max (g i) 0 / |scalingVector x g i| * s i) =
    (max (g i) 0 / |scalingVector x g i|) * (s i) ^ 2 by ring]
  exact mul_nonneg (div_nonneg (le_max_right _ _) (abs_nonneg _)) (sq_nonneg _)

/-- **Algorithms 13.12.1 and 13.12.2** of [conn2000trust], accepted reductions. The objective values
$f(x_k)$ of a Coleman–Li run of either version are nonincreasing.

In the second version, the nonnegative correction $\frac12 s^T C s$ is subtracted before the
acceptance test, so an accepted step still decreases $f$. -/
theorem ColemanLiRun.objective_antitone {version : ColemanLiVersion} {P : Chapter06.BTRParams}
    {f : (ι → ℝ) → ℝ} (r : ColemanLiRun version P f) : Antitone (f ∘ r.x) := by
  apply antitone_nat_of_succ_le
  intro k
  change f (r.x (k + 1)) ≤ f (r.x k)
  rw [r.iterate_update, colemanLiAcceptedPoint]
  split
  · rename_i hacc
    have hpos := mul_pos P.eta₁_pos (r.predicted_pos k)
    cases version with
    | first =>
      have h := (le_div_iff₀ (r.predicted_pos k)).mp hacc
      linarith
    | second =>
      have h := (le_div_iff₀ (r.predicted_pos k)).mp hacc
      have hcorr := colemanLiCorrection_nonneg (r.x k) (r.g k) (r.s k)
      linarith
  · exact le_rfl

private noncomputable def colemanLiPullback (x g : ι → ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ))
    (Matrix.diagonal fun i ↦ (Real.sqrt |scalingVector x g i|)⁻¹)

private theorem colemanLiPullback_apply (x g : ι → ℝ) (v : EuclideanSpace ℝ ι) :
    colemanLiPullback x g v = WithLp.toLp 2 (fun i ↦ v i / Real.sqrt |scalingVector x g i|) := by
  change colemanLiPullback x g (WithLp.toLp 2 v.ofLp) = _
  rw [colemanLiPullback, Matrix.toEuclideanCLM_toLp]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]

omit [DecidableEq ι] in
private theorem colemanLiScaledNorm_eq_zero {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    {v : EuclideanSpace ℝ ι} (hv : colemanLiScaledNorm x g v.ofLp = 0) : v = 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  have h := congrArg (fun w : EuclideanSpace ℝ ι ↦ w i) (norm_eq_zero.mp hv)
  have hscale : 0 < |scalingVector x g i| := by
    by_cases hgi : 0 ≤ g i
    · simpa [scalingVector, hgi, abs_of_pos (hx i)] using hx i
    · simp [scalingVector, hgi]
  change v i / Real.sqrt |scalingVector x g i| = 0 at h
  exact (div_eq_zero_iff.mp h).resolve_right (Real.sqrt_pos.mpr hscale).ne'

private noncomputable def colemanLiRunModel (f : (ι → ℝ) → ℝ)
    (x g : ι → ℝ) (H : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  unscaledModel (f x) x g H (v.ofLp - x)

private theorem colemanLiRunModel_sub (f : (ι → ℝ) → ℝ) (x g s : ι → ℝ)
    (H : Matrix ι ι ℝ) :
    colemanLiRunModel f x g H (WithLp.toLp 2 x) -
      colemanLiRunModel f x g H (WithLp.toLp 2 x + WithLp.toLp 2 s) =
        unscaledModel (f x) x g H 0 - unscaledModel (f x) x g H s := by
  simp [colemanLiRunModel, WithLp.ofLp_add]

/-- **Algorithm 13.12.1** of [conn2000trust] as a run of the basic trust-region algorithm. A run of
the first version gives a `ConnGouldToint.Chapter06.BTRRun` for $f$ on `EuclideanSpace ℝ ι`,
with the scaled norm $\|S_k^{-1} \cdot\|$ as the trust-region norm, the corrected model, and the
ordinary acceptance and radius rules.

The sufficient decrease predicate of the resulting run is trivial. The decrease tests of the
algorithm remain available on the original run. -/
noncomputable def ColemanLiRun.toBTRRun {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ}
    (r : ColemanLiRun .first P f) :
    Chapter06.BTRRun (fun v : EuclideanSpace ℝ ι ↦ f v.ofLp) P (fun _ _ _ _ ↦ True) where
  x := fun k ↦ WithLp.toLp 2 (r.x k)
  s := fun k ↦ WithLp.toLp 2 (r.s k)
  Δ := r.Δ
  p := fun k ↦ (normSeminorm ℝ (EuclideanSpace ℝ ι)).comp
    (colemanLiPullback (r.x k) (r.g k)).toLinearMap
  norm_separates := fun k v hv ↦ by
    change ‖colemanLiPullback (r.x k) (r.g k) v‖ = 0 at hv
    rw [colemanLiPullback_apply] at hv
    exact colemanLiScaledNorm_eq_zero (r.interior_iterate k) hv
  model := fun k ↦ colemanLiRunModel f (r.x k) (r.g k) (r.H k)
  delta_initial_pos := r.initial_radius_pos
  feasible := fun k ↦ by
    rw [Chapter06.mem_trustRegion, add_sub_cancel_left]
    change ‖colemanLiPullback (r.x k) (r.g k) (WithLp.toLp 2 (r.s k))‖ ≤ r.Δ k
    rw [colemanLiPullback_apply]
    exact r.trust_region k
  sufficient_decrease := fun _ ↦ trivial
  predicted_pos := fun k ↦ by
    rw [colemanLiRunModel_sub]
    exact r.predicted_pos k
  iterate_update := fun k ↦ by
    rw [colemanLiRunModel_sub, r.iterate_update]
    by_cases h : P.η₁ ≤ colemanLiTrialRatio .first f (r.x k) (r.g k) (r.s k) (r.H k)
    all_goals
      simp only [colemanLiTrialRatio] at h
      simp [colemanLiAcceptedPoint, colemanLiTrialRatio, Optimization.acceptStep,
        Optimization.reductionRatio, WithLp.ofLp_add, h]
  radius_update := fun k ↦ by
    rw [Chapter06.btrRatio, colemanLiRunModel_sub]
    exact r.radius_update k

/-- **Algorithm 13.12.1** of [conn2000trust]. The trust-region norm at iteration $k$ of the run of
`ConnGouldToint.Chapter13.ColemanLiRun.toBTRRun` is the scaled norm $\|S_k^{-1} v\|$. -/
theorem ColemanLiRun.toBTRRun_norm {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ}
    (r : ColemanLiRun .first P f) (k : ℕ) (v : EuclideanSpace ℝ ι) :
    r.toBTRRun.p k v = colemanLiScaledNorm (r.x k) (r.g k) v.ofLp := by
  change ‖colemanLiPullback (r.x k) (r.g k) v‖ = _
  rw [colemanLiPullback_apply]
  rfl

/-- **Algorithm 13.12.1** of [conn2000trust]. The model at iteration $k$ of the run of
`ConnGouldToint.Chapter13.ColemanLiRun.toBTRRun`, evaluated at $x_k + v$, is the corrected model
(13.12.8) at the displacement $v$. -/
theorem ColemanLiRun.toBTRRun_model {P : Chapter06.BTRParams} {f : (ι → ℝ) → ℝ}
    (r : ColemanLiRun .first P f) (k : ℕ) (v : EuclideanSpace ℝ ι) :
    r.toBTRRun.model k (r.toBTRRun.x k + v) =
      unscaledModel (f (r.x k)) (r.x k) (r.g k) (r.H k) v.ofLp := by
  change colemanLiRunModel f (r.x k) (r.g k) (r.H k) (WithLp.toLp 2 (r.x k) + v) = _
  simp [colemanLiRunModel, WithLp.ofLp_add]

section OperatorNorm

open scoped Matrix.Norms.L2Operator

private theorem norm_scalingMatrix_le {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    {B : ℝ} (hB : 1 ≤ B) (hbound : ∀ i, x i ≤ B) :
    ‖scalingMatrix x g‖ ≤ Real.sqrt B := by
  rw [scalingMatrix, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  by_cases hg : 0 ≤ g i
  · simpa [scalingVector, hg, abs_of_nonneg (hx i)] using hbound i
  · simpa [scalingVector, hg] using hB

omit [DecidableEq ι] in
/-- Norm equivalence AN.1b for the scaled norm, a hypothesis check for Theorem 13.12.4 of
[conn2000trust]. Let $x_i > 0$ and $x_i \le B$ for all $i$, with $B \ge 1$. Then for every $s$
$$\|s\|_2 \le \sqrt{B}\, \|S(x, g)^{-1} s\|_2.$$

The vector $S^{-1} s$ is written as the vector of quotients $s_i / |v_i|^{1/2}$. -/
theorem norm_le_colemanLiScaledNorm {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    {B : ℝ} (hB : 1 ≤ B) (hbound : ∀ i, x i ≤ B) (s : ι → ℝ) :
    ‖WithLp.toLp 2 s‖ ≤ Real.sqrt B *
      ‖WithLp.toLp 2 (fun i ↦ s i / Real.sqrt |scalingVector x g i|)‖ := by
  classical
  let w : ι → ℝ := fun i ↦ s i / Real.sqrt |scalingVector x g i|
  have hw : scalingMatrix x g *ᵥ w = s := by
    funext i
    have hv : 0 < |scalingVector x g i| := by
      by_cases hg : 0 ≤ g i
      · simpa [scalingVector, hg, abs_of_pos (hx i)] using hx i
      · simp [scalingVector, hg]
    rw [scalingMatrix, Matrix.mulVec_diagonal]
    dsimp [w]
    rw [mul_comm, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hv).ne']
  have hnorm :=
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (scalingMatrix x g)).le_opNorm (WithLp.toLp 2 w)
  rw [Matrix.toEuclideanCLM_toLp, hw, ← Matrix.cstar_norm_def] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_right
    (norm_scalingMatrix_le (fun i ↦ (hx i).le) hB hbound) (norm_nonneg _))

/-- Model curvature bound AM.4b for the scaled Hessian, a hypothesis check for Theorem 13.12.4 of
[conn2000trust]. Let $x \ge 0$ with $x_i \le B$ for all $i$, $B \ge 1$, let $g_i \le G$ for all
$i$, with $G \ge 0$, and let $\|H\| \le K$. Then
$$\|S H S + \bar G\| \le B K + G.$$
-/
theorem norm_scaledHessian_le {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    {B K G : ℝ} (hB : 1 ≤ B) (hbound : ∀ i, x i ≤ B) (hG : 0 ≤ G)
    (hg : ∀ i, g i ≤ G) {H : Matrix ι ι ℝ} (hH : ‖H‖ ≤ K) :
    ‖scaledHessian x g H‖ ≤ B * K + G := by
  have hS := norm_scalingMatrix_le (g := g) hx hB hbound
  have hcorr : ‖scaledCorrection g‖ ≤ G := by
    rw [scaledCorrection, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (hg i) hG
  unfold scaledHessian
  calc
    _ ≤ ‖scalingMatrix x g * H * scalingMatrix x g‖ + ‖scaledCorrection g‖ := norm_add_le _ _
    _ ≤ (‖scalingMatrix x g‖ * ‖H‖) * ‖scalingMatrix x g‖ + G :=
      add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))) hcorr
    _ ≤ (Real.sqrt B * K) * Real.sqrt B + G := by
      have hK : 0 ≤ K := (norm_nonneg H).trans hH
      gcongr
    _ = _ := by
      rw [show Real.sqrt B * K * Real.sqrt B = (Real.sqrt B) ^ 2 * K by ring,
        Real.sq_sqrt (zero_le_one.trans hB)]

/-- **Equation (13.12.25)** of [conn2000trust]. The sequences $x_k$, $g_k$, $A_k$ and $H_k$ satisfy
the **scaled Hessian agreement** if
$$\|S(x_k, g_k)\, g_k\| \to 0 \implies \|S(x_k, g_k) (A_k - H_k) S(x_k, g_k)\| \to 0.$$
Here $A_k$ stands for the objective Hessian and $H_k$ for the model Hessian. -/
def ScaledHessianConsistency (x g : ℕ → ι → ℝ) (A H : ℕ → Matrix ι ι ℝ) : Prop :=
  Tendsto (fun k ↦ scaledGradientNorm (x k) (g k)) atTop (𝓝 0) →
    Tendsto (fun k ↦ ‖scalingMatrix (x k) (g k) * (A k - H k) *
      scalingMatrix (x k) (g k)‖) atTop (𝓝 0)

/-- **Equation (13.12.25)** of [conn2000trust]. The two scaled Hessians use the same diagonal
$\bar G$, so
$$(S A S + \bar G) - (S H S + \bar G) = S (A - H) S.$$
-/
theorem scaledHessian_sub_eq (x g : ι → ℝ) (A H : Matrix ι ι ℝ) :
    scaledHessian x g A - scaledHessian x g H =
      scalingMatrix x g * (A - H) * scalingMatrix x g := by
  classical
  simp [scaledHessian, Matrix.mul_sub, Matrix.sub_mul]

end OperatorNorm

section Convergence

open scoped Matrix.Norms.L2Operator

private theorem abs_matrix_quadratic_le (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    |v ⬝ᵥ (A *ᵥ v)| ≤ ‖A‖ * ‖WithLp.toLp 2 v‖ ^ 2 := by
  let V := WithLp.toLp 2 v
  have he : inner ℝ V ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) V) = v ⬝ᵥ (A *ᵥ v) := by
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_eq_star_dotProduct]
    simp [V, dotProduct_comm]
  rw [← he]
  calc
    _ ≤ ‖V‖ * ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) V‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖V‖ * (‖A‖ * ‖V‖) := mul_le_mul_of_nonneg_left
      (by rw [Matrix.cstar_norm_def];
          exact ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A)).le_opNorm V)
      (norm_nonneg _)
    _ = _ := by ring

private theorem scale_mulVec_div {x g : ι → ℝ} (hx : ∀ i, 0 < x i) (d : ι → ℝ) :
    scalingMatrix x g *ᵥ (fun i => d i / Real.sqrt |scalingVector x g i|) = d := by
  funext i
  have hv : 0 < |scalingVector x g i| := by
    by_cases hg : 0 ≤ g i
    · simpa [scalingVector, hg, abs_of_pos (hx i)] using hx i
    · simp [scalingVector, hg]
  rw [scalingMatrix, Matrix.mulVec_diagonal, mul_comm, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hv).ne']

/-- Curvature transfer, used in the proof of Theorem 13.12.6 of [conn2000trust]. Let
$e \in \mathbb{R}$ and suppose that $w^T (S H S + \bar G) w \ge -e \|w\|^2$. Then
$$(S w)^T A (S w) \ge -\big(e + \|S (A - H) S\|\big) \|w\|^2 - \sum_i \max\{g_i, 0\}\, w_i^2.$$
-/
theorem colemanLi_curvature_transfer (x g w : ι → ℝ) (A H : Matrix ι ι ℝ) {e : ℝ}
    (hmodel : -e * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (scaledHessian x g H *ᵥ w)) :
    -(e + ‖scalingMatrix x g * (A - H) * scalingMatrix x g‖) * ‖WithLp.toLp 2 w‖ ^ 2 -
      (∑ i, max (g i) 0 * (w i) ^ 2) ≤
      (scalingMatrix x g *ᵥ w) ⬝ᵥ (A *ᵥ (scalingMatrix x g *ᵥ w)) := by
  have herr := abs_matrix_quadratic_le (scaledHessian x g A - scaledHessian x g H) w
  rw [Matrix.sub_mulVec, dotProduct_sub, scaledHessian_sub_eq] at herr
  have herr' := (neg_le_neg herr).trans (neg_abs_le _)
  linarith only [hmodel, herr', scaledHessian_form x g w A]

/-- **Theorem 13.12.6** of [conn2000trust]. Let $x_k \to x_0$, $g_k \to g_0$ and $A_k \to A_0$, with
$x_k$ strictly positive, and let $\|S(x_k, g_k)\, g_k\| \to 0$. Suppose that the agreement
(13.12.25) holds for $A_k$ and the model Hessians $H_k$, and that there are $e_k \ge 0$ with
$e_k \to 0$ and
$$w^T (S_k H_k S_k + \bar G_k) w \ge -e_k \|w\|^2 \quad \text{for all } k \text{ and } w.$$
Then $x_0$ is weakly second-order critical for $g_0$ and $A_0$.

The hypothesis on $e_k$ says that the negative part of the scaled model curvature vanishes. For
a direction $d$ on the active face at $x_0$, the proof bounds the preimages $S_k^{-1} d$
uniformly and transfers the curvature by
`ConnGouldToint.Chapter13.colemanLi_curvature_transfer`. -/
theorem theorem_13_12_6 {x g : ℕ → ι → ℝ} {A H : ℕ → Matrix ι ι ℝ}
    {x₀ g₀ : ι → ℝ} {A₀ : Matrix ι ι ℝ}
    (hx : Tendsto x atTop (𝓝 x₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (hA : Tendsto A atTop (𝓝 A₀)) (hpos : ∀ k i, 0 < x k i)
    (hfirst : Tendsto (fun k => scaledGradientNorm (x k) (g k)) atTop (𝓝 0))
    (hcons : ScaledHessianConsistency x g A H)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (he₀ : ∀ k, 0 ≤ e k)
    (hcurv : ∀ k w, -e k * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      w ⬝ᵥ (scaledHessian (x k) (g k) (H k) *ᵥ w)) :
    OrthantWeakSecondOrder x₀ g₀ A₀ := by
  have hfo := orthantFirstOrder_of_tendsto_scaledGradientNorm hx hg
    (Eventually.of_forall fun k i => (hpos k i).le) hfirst
  refine ⟨hfo, fun d hd => ?_⟩
  let w (k : ℕ) (i : ι) := d i / Real.sqrt |scalingVector (x k) (g k) i|
  let D (i : ι) := |d i| / Real.sqrt (min 1 (x₀ i / 2))
  have hbound : ∀ᶠ k in atTop, ∀ i, |w k i| ≤ D i := by
    have hi (i : ι) : ∀ᶠ k in atTop, |w k i| ≤ D i := by
      by_cases hz : x₀ i = 0
      · exact Eventually.of_forall fun k => by simp [w, D, hd i hz]
      have hxi : 0 < x₀ i :=
        lt_of_le_of_ne (ge_of_tendsto ((continuous_apply i).continuousAt.tendsto.comp hx)
          (Eventually.of_forall fun k => (hpos k i).le)) (Ne.symm hz)
      filter_upwards [((continuous_apply i).continuousAt.tendsto.comp hx).eventually
        (lt_mem_nhds (half_lt_self hxi))] with k hk
      have hden : min 1 (x₀ i / 2) ≤ |scalingVector (x k) (g k) i| := by
        by_cases hgi : 0 ≤ g k i
        · simpa [scalingVector, hgi, abs_of_pos (hpos k i)] using
            (min_le_right (1 : ℝ) (x₀ i / 2)).trans hk.le
        · simp [scalingVector, hgi]
      rw [show |w k i| = |d i| / Real.sqrt |scalingVector (x k) (g k) i| by
        dsimp only [w]
        rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]]
      exact div_le_div_of_nonneg_left (abs_nonneg _)
        (Real.sqrt_pos.mpr (lt_min zero_lt_one (half_pos hxi))) (Real.sqrt_le_sqrt hden)
    exact Filter.eventually_all.mpr hi
  let B := ∑ i, (D i) ^ 2
  have hB : ∀ᶠ k in atTop, ‖WithLp.toLp 2 (w k)‖ ^ 2 ≤ B := by
    filter_upwards [hbound] with k hk
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hk i) 2
  have hterm (i : ι) :
      Tendsto (fun k => max (g k i) 0 * (w k i) ^ 2) atTop (𝓝 0) := by
    by_cases hz : x₀ i = 0
    · simp [w, hd i hz]
    have hxi : 0 < x₀ i :=
      lt_of_le_of_ne (ge_of_tendsto ((continuous_apply i).continuousAt.tendsto.comp hx)
        (Eventually.of_forall fun k => (hpos k i).le)) (Ne.symm hz)
    have hzero := (hfo i).2 hxi
    have hmax : Tendsto (fun k => max (g k i) 0) atTop (𝓝 0) := by
      simpa only [hzero, max_self, Function.comp_apply] using
        ((continuous_apply i).continuousAt.tendsto.comp hg).max (tendsto_const_nhds (x := (0 : ℝ)))
    apply squeeze_zero' (Eventually.of_forall fun k => mul_nonneg (le_max_right _ _) (sq_nonneg _))
      _ (by simpa only [zero_mul] using hmax.mul_const ((D i) ^ 2))
    filter_upwards [hbound] with k hk
    apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hk i) 2
  have hcorr : Tendsto (fun k => ∑ i, max (g k i) 0 * (w k i) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  let δ (k : ℕ) := ‖scalingMatrix (x k) (g k) * (A k - H k) * scalingMatrix (x k) (g k)‖
  have hδ : Tendsto δ atTop (𝓝 0) := hcons hfirst
  have hq : ∀ᶠ k in atTop, -(e k + δ k) * B -
      (∑ i, max (g k i) 0 * (w k i) ^ 2) ≤ d ⬝ᵥ (A k *ᵥ d) := by
    filter_upwards [hB] with k hk
    have hlow := mul_le_mul_of_nonpos_left hk
      (neg_nonpos.mpr (add_nonneg (he₀ k) (norm_nonneg _)) : -(e k + δ k) ≤ 0)
    have htransfer := colemanLi_curvature_transfer (x k) (g k) (w k) (A k) (H k) (hcurv k (w k))
    have hscale := scale_mulVec_div (hpos k) (g := g k) d
    change scalingMatrix (x k) (g k) *ᵥ w k = d at hscale
    rw [hscale] at htransfer
    exact (sub_le_sub_right hlow _).trans htransfer
  have hlim : Tendsto (fun k => -(e k + δ k) * B -
      (∑ i, max (g k i) 0 * (w k i) ^ 2)) atTop (𝓝 0) := by
    simpa only [add_zero, neg_zero, zero_mul, sub_zero] using
      (((he.add hδ).neg.mul_const B).sub hcorr)
  have hcont : Continuous (fun M : Matrix ι ι ℝ => d ⬝ᵥ (M *ᵥ d)) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact le_of_tendsto_of_tendsto hlim (hcont.continuousAt.tendsto.comp hA) hq

open ConnGouldToint.Chapter06 in
private theorem scalar_btr_criticality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : BTRParams} {f : E → ℝ} {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {a : ℕ → ℝ} {κ β C K : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hκ : 0 < κ) (hκ₁ : κ < 1) (hβ : 0 < β) (hβC : β ≤ C)
    (hK : 0 < K) (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, κ * a k * min (a k / β) (run.Δ k) ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ C * (run.Δ k) ^ 2)
    (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hcont : ∀ ε > 0, ∃ r > 0, ∀ i j, ‖run.x i - run.x j‖ < r → |a i - a j| < ε)
    (hlower : BddBelow (Set.range f)) :
    Tendsto a atTop (𝓝 0) := by
  let F (k : ℕ) := f (run.x k)
  have hFbound : BddBelow (Set.range F) := hlower.mono (Set.range_comp_subset_range run.x f)
  have hF := tendsto_atTop_ciInf run.objective_antitone hFbound
  have hdiff : Tendsto (fun k => F k - F (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hF.sub (hF.comp (tendsto_add_atTop_nat 1))
  have hC : 0 < C := hβ.trans_le hβC
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in atTop, a k < ε := by
    by_contra! hn
    obtain ⟨N, hN⟩ := eventually_atTop.mp hn
    let θ := κ * ε * (1 - P.η₂) / C
    let r := min (run.Δ N) (P.γ₁ * θ)
    have hr : 0 < r := lt_min (run.delta_pos N)
      (mul_pos P.gamma₁_pos (div_pos (mul_pos (mul_pos hκ hε) hη) hC))
    have hrad (k : ℕ) (hk : N ≤ k) : r ≤ run.Δ k := by
      have h := (run.tail N).delta_lower_bound (θ := θ) (fun j hj => ?_) (k - N)
      · change r ≤ run.Δ (N + (k - N)) at h
        simpa only [Nat.add_sub_of_le hk] using h
      · let i := N + j
        have hi := hN i (Nat.le_add_right N j)
        have hsmall : run.Δ i ≤ κ * a i * (1 - P.η₂) / C := by
          exact hj.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hκ.le) hη.le) hC.le)
        exact btrRatio_ge_eta₂_of_small_radius_of_decrease hβ hβC (run.delta_pos i)
          (hε.trans_le hi) hκ hκ₁ (hval i) (hdec i) (herr i) hsmall
    let b := P.η₁ * (κ * ε * min (ε / β) r)
    have hb : 0 < b := mul_pos P.eta₁_pos
      (mul_pos (mul_pos hκ hε) (lt_min (div_pos hε hβ) hr))
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hb))
    let L := max N J
    have hfail (k : ℕ) (hk : L ≤ k) : k ∉ run.successful := by
      intro hks
      have hkN := (le_max_left N J).trans hk
      have hmin := min_le_min (div_le_div_of_nonneg_right (hN k hkN) hβ.le) (hrad k hkN)
      have hlow := (mul_le_mul (mul_le_mul_of_nonneg_left (hN k hkN) hκ.le)
        hmin (le_min (div_nonneg hε.le hβ.le) hr.le) (mul_nonneg hκ.le (ha k))).trans (hdec k)
      exact (hJ k ((le_max_right N J).trans hk)).not_ge
        ((mul_le_mul_of_nonneg_left hlow P.eta₁_pos.le).trans
          (run.objective_drop_of_successful hks))
    have hγ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
    have hp (j : ℕ) : run.Δ (L + j) ≤ P.γ₂ ^ j * run.Δ L := by
      induction j with
      | zero => simp
      | succ j ih =>
        have hh := ((run.radius_update (L + j)).unsuccessful
          (lt_of_not_ge (hfail (L + j) (Nat.le_add_right _ _)))).2
        rw [Nat.add_succ, pow_succ, mul_comm (P.γ₂ ^ j), mul_assoc]
        exact hh.trans (mul_le_mul_of_nonneg_left ih hγ.le)
    have hlim : Tendsto (fun j : ℕ => P.γ₂ ^ j * run.Δ L) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const (run.Δ L)
    obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hr)).exists
    exact hj.not_ge ((hrad _ ((le_max_left N J).trans (Nat.le_add_right L j))).trans (hp j))
  apply tendsto_order.mpr
  refine ⟨fun b hb => Eventually.of_forall fun k => hb.trans_le (ha k), ?_⟩
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨r, hr, hnear⟩ := hcont δ hδ
  let c := P.η₁ * (κ * δ)
  have hc : 0 < c := mul_pos P.eta₁_pos (mul_pos hκ hδ)
  obtain ⟨N, hN⟩ :=
    eventually_atTop.mp (hdiff.eventually (gt_mem_nhds (mul_pos hc (div_pos hδ hβ))))
  have hKc : 0 < K / c := div_pos hK hc
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (hF.eventually (gt_mem_nhds (lt_add_of_pos_right _ (div_pos hr hKc))))
  apply eventually_atTop.mpr
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have hex : ∃ j, n ≤ j ∧ a j < δ := by
    obtain ⟨j, hj, hnj⟩ := ((hfreq δ hδ).and_eventually (eventually_ge_atTop n)).exists
    exact ⟨j, hnj, hj⟩
  classical
  let j := Nat.find hex
  obtain ⟨hnj, hj⟩ := Nat.find_spec hex
  have hmove (k : ℕ) (hkn : n ≤ k) (hkj : k < j) :
      ‖run.x k - run.x (k + 1)‖ ≤ (K / c) * (F k - F (k + 1)) := by
    by_cases hs : k ∈ run.successful
    · have hk : δ ≤ a k := le_of_not_gt (fun h => Nat.find_min hex hkj ⟨hkn, h⟩)
      have hmin := min_le_min (div_le_div_of_nonneg_right hk hβ.le) (le_refl (run.Δ k))
      have hm := (mul_le_mul (mul_le_mul_of_nonneg_left hk hκ.le) hmin
        (le_min (div_nonneg hδ.le hβ.le) (run.delta_pos k).le) (mul_nonneg hκ.le (ha k))).trans
          (hdec k)
      have hdrop : c * min (δ / β) (run.Δ k) ≤ F k - F (k + 1) := by
        simpa only [c, mul_assoc] using
          (mul_le_mul_of_nonneg_left hm P.eta₁_pos.le).trans (run.objective_drop_of_successful hs)
      have hrad : run.Δ k ≤ δ / β := by
        by_contra! hbad
        rw [min_eq_left hbad.le] at hdrop
        exact (hN k (hnN.trans hkn)).not_ge hdrop
      rw [min_eq_right hrad] at hdrop
      rw [run.iterate_update, Optimization.acceptStep_of_le hs, sub_add_cancel_left, norm_neg]
      apply (hstep k).trans
      have hh : run.Δ k ≤ (F k - F (k + 1)) / c := (le_div_iff₀ hc).mpr (by rwa [mul_comm])
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hh hK.le
    · simp [run.iterate_eq_of_unsuccessful hs, F]
  have hpath (t : ℕ) (ht : n + t ≤ j) :
      ‖run.x n - run.x (n + t)‖ ≤ (K / c) * (F n - F (n + t)) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hlt : n + t < j := by omega
      have hm := hmove (n + t) (Nat.le_add_right n t) hlt
      have hprev := ih hlt.le
      have htri : ‖run.x n - run.x (n + (t + 1))‖ ≤
          ‖run.x n - run.x (n + t)‖ + ‖run.x (n + t) - run.x (n + t + 1)‖ := by
        simpa only [sub_add_sub_cancel, Nat.add_assoc] using
          norm_add_le (run.x n - run.x (n + t)) (run.x (n + t) - run.x (n + t + 1))
      rw [← Nat.add_assoc]
      exact htri.trans (by linarith only [hprev, hm])
  have hnj' : n + (j - n) = j := Nat.add_sub_of_le hnj
  have hdist := hpath (j - n) hnj'.le
  rw [hnj'] at hdist
  have hgap : F n - F j < r / (K / c) := by
    have hh : F n < (⨅ k, F k) + r / (K / c) := hM n hnM
    linarith only [hh, ciInf_le hFbound j]
  have hd := hdist.trans_lt (by
    rw [mul_comm]
    exact (lt_div_iff₀ hKc).mp hgap)
  have hh := le_abs_self (a n - a j)
  have hj' : a j < δ := hj
  have hnear' := hnear n j hd
  dsimp [δ] at hj' hnear'
  linarith only [hnear', hh, hj']

open ConnGouldToint.Chapter06 in
/-- **Theorem 13.12.4** of [conn2000trust]. Let $\iota$ be nonempty, and let $f$ be a twice
continuously differentiable function on `EuclideanSpace ℝ ι`, bounded below, with
$\|\nabla^2 f(y)\| \le L$ for all $y$ and gradient coordinates $g(y)$ continuous in $y$. Let
$(x_k)$ be a run of the basic trust-region algorithm for $f$ whose iterates lie in a compact
set, with $0 < (x_k)_i \le B$ and $g(x_k)_i \le G$ for all $k$ and $i$. Suppose that its
trust-region norm is the scaled norm $\|S_k^{-1} \cdot\|$, its model is the corrected model
(13.12.8) with Hessian $H_k$, $\|H_k\| \le U$, and each step decreases the model at least as
much as some constrained scaled Cauchy time with fraction $\sigma$. Let $B \ge 1$, $G > 0$,
$U, L \ge 0$, $0 < \sigma < 1$ and $0 < \alpha \le \min\{1, (1 - \sigma) / G\}$. Then
$$\|S(x_k, g(x_k))\, g(x_k)\| \to 0,$$
and every limit $z$ of $x_{j(n)}$ with $j(n) \to \infty$ is first-order critical for $g(z)$.

The model decrease is compared with the constrained scaled Cauchy point through the corrected
bound of Theorem 13.12.3. -/
theorem theorem_13_12_4 [Nonempty ι]
    {f : EuclideanSpace ℝ ι → ℝ} {P : BTRParams}
    {sufficient : ℕ → (EuclideanSpace ℝ ι → ℝ) → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → Prop}
    (run : BTRRun f P sufficient)
    (g : EuclideanSpace ℝ ι → (ι → ℝ)) (H : ℕ → Matrix ι ι ℝ)
    (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hgrad : ∀ x v, fderiv ℝ f x v = g x ⬝ᵥ WithLp.ofLp v)
    (hlower : BddBelow (Set.range f))
    {S : Set (EuclideanSpace ℝ ι)} (hS : IsCompact S) (hxS : ∀ k, run.x k ∈ S)
    {B G U L σ α : ℝ} (hB : 1 ≤ B) (hG : 0 < G) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hσ : 0 < σ) (hσ₁ : σ < 1) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hcap : α ≤ (1 - σ) / G)
    (hx : ∀ k i, 0 < run.x k i) (hbound : ∀ k i, run.x k i ≤ B)
    (hgBound : ∀ k i, g (run.x k) i ≤ G) (hH : ∀ k, ‖H k‖ ≤ U)
    (hfH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ L)
    (hp : ∀ k (v : EuclideanSpace ℝ ι), run.p k v =
      ‖WithLp.toLp 2 (fun i => v i / Real.sqrt |scalingVector
        (WithLp.ofLp (run.x k)) (g (run.x k)) i|)‖)
    (hm : ∀ k (v : EuclideanSpace ℝ ι), run.model k (run.x k + v) =
      unscaledModel (f (run.x k)) (WithLp.ofLp (run.x k)) (g (run.x k)) (H k) (WithLp.ofLp v))
    (hCauchy : ∀ k, ∃ t, IsScaledCauchyTime (f (run.x k))
      (WithLp.ofLp (run.x k)) (g (run.x k)) (H k) (run.Δ k) σ t ∧
      run.model k (run.x k + run.s k) ≤
        unscaledModel (f (run.x k)) (WithLp.ofLp (run.x k)) (g (run.x k)) (H k)
          ((-t) • ((scalingMatrix (WithLp.ofLp (run.x k)) (g (run.x k)) *
            scalingMatrix (WithLp.ofLp (run.x k)) (g (run.x k))) *ᵥ g (run.x k)))) :
    Tendsto (fun k => scaledGradientNorm (WithLp.ofLp (run.x k)) (g (run.x k))) atTop (𝓝 0) ∧
      ∀ z (j : ℕ → ℕ), Tendsto j atTop atTop → Tendsto (run.x ∘ j) atTop (𝓝 z) →
        OrthantFirstOrder (WithLp.ofLp z) (g z) := by
  let a (x : EuclideanSpace ℝ ι) := scaledGradientNorm (WithLp.ofLp x) (g x)
  let β := 1 + B * U + G
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hβ : 1 ≤ β := by dsimp [β]; linarith [mul_nonneg hB₀ hU]
  have hβ₀ : 0 < β := zero_lt_one.trans_le hβ
  have hmodelH (k : ℕ) :
      ‖scaledHessian (WithLp.ofLp (run.x k)) (g (run.x k)) (H k)‖ ≤ β :=
    (norm_scaledHessian_le (fun i => (hx k i).le) hB (hbound k) hG.le (hgBound k) (hH k)).trans
      (by dsimp [β]; linarith)
  have hval (k : ℕ) : f (run.x k) = run.model k (run.x k) := by
    simpa [unscaledModel, affineQuadraticModel] using (hm k 0).symm
  have hdec (k : ℕ) : (α / 2) * a (run.x k) * min (a (run.x k) / β) (run.Δ k) ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k) := by
    obtain ⟨t, ht, hcmp⟩ := hCauchy k
    have hcurv := (le_abs_self _).trans (abs_matrix_quadratic_le
      (scaledHessian (WithLp.ofLp (run.x k)) (g (run.x k)) (H k))
      (scaledGradient (WithLp.ofLp (run.x k)) (g (run.x k))))
    have hcurv' : scaledGradient (WithLp.ofLp (run.x k)) (g (run.x k)) ⬝ᵥ
        (scaledHessian (WithLp.ofLp (run.x k)) (g (run.x k)) (H k) *ᵥ
          scaledGradient (WithLp.ofLp (run.x k)) (g (run.x k))) ≤ β * a (run.x k) ^ 2 :=
      hcurv.trans (mul_le_mul_of_nonneg_right (hmodelH k) (sq_nonneg _))
    have hh := scaledCauchyTime_sufficientDecrease (f (run.x k)) (hx k) (H k)
      (run.delta_pos k).le hσ hσ₁ hG (hgBound k) hβ hα hα₁ hcap hcurv' ht
    exact hh.trans (by rw [← hval k]; exact sub_le_sub_left hcmp _)
  have hfeas (k : ℕ) : run.p k (run.s k) ≤ run.Δ k := by
    have h := run.feasible k
    change run.p k (run.x k + run.s k - run.x k) ≤ run.Δ k at h
    rwa [add_sub_cancel_left] at h
  have hstep (k : ℕ) : ‖run.s k‖ ≤ Real.sqrt B * run.Δ k := by
    have h := norm_le_colemanLiScaledNorm (g := g (run.x k)) (hx k) hB (hbound k)
      (WithLp.ofLp (run.s k))
    rw [WithLp.toLp_ofLp, ← hp] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hfeas k) (Real.sqrt_nonneg _))
  have herror (k : ℕ) : |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      (β + L * B) * (run.Δ k) ^ 2 := by
    let x := run.x k
    let s := run.s k
    let w (i : ι) := s i / Real.sqrt |scalingVector (WithLp.ofLp x) (g x) i|
    let V := scalingMatrix (WithLp.ofLp x) (g x)
    have hw : V *ᵥ w = WithLp.ofLp s := scale_mulVec_div (hx k) _
    have hM : run.model k (x + s) = f x + fderiv ℝ f x s +
        (1 / 2) * (w ⬝ᵥ (scaledHessian (WithLp.ofLp x) (g x) (H k) *ᵥ w)) := by
      rw [hm, ← hw, ← scaledModel_eq_unscaledModel (f x) (hx k), scaledModel,
        affineQuadraticModel, scaledGradient, hgrad, ← hw, dotProduct_comm (V *ᵥ g x),
        Matrix.dotProduct_mulVec, vecMul_scalingMatrix, dotProduct_comm]
    have hDf := (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
      (by norm_num)
    have hrem := norm_sub_firstOrder_le_of_hessian_bound
      (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ ι)))
      (Set.mem_univ x) (Set.mem_univ (x + s))
      (fun z _ => hf.differentiable (by norm_num) z) (fun z _ => hDf z)
      (fun z _ => hfH z)
    rw [Real.norm_eq_abs] at hrem
    have hQ := (abs_matrix_quadratic_le (scaledHessian (WithLp.ofLp x) (g x) (H k)) w).trans
      (mul_le_mul_of_nonneg_right (hmodelH k) (sq_nonneg _))
    have hwΔ : ‖WithLp.toLp 2 w‖ ≤ run.Δ k := by
      exact ((hp k s).symm.le).trans (hfeas k)
    have hsΔ := pow_le_pow_left₀ (norm_nonneg _) (hstep k) 2
    rw [mul_pow, Real.sq_sqrt hB₀] at hsΔ
    have hQΔ := hQ.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hwΔ 2) hβ₀.le)
    have hremΔ := hrem.trans (mul_le_mul_of_nonneg_left hsΔ
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hL))
    rw [hM]
    obtain ⟨h₁, h₂⟩ := abs_le.mp hQΔ
    obtain ⟨h₃, h₄⟩ := abs_le.mp hremΔ
    apply abs_le.mpr
    constructor <;> nlinarith only [h₁, h₂, h₃, h₄,
      mul_nonneg (add_nonneg hβ₀.le (mul_nonneg hL hB₀)) (sq_nonneg (run.Δ k))]
  have ha : Continuous a := by
    have ho : Continuous (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) :=
      PiLp.continuous_ofLp _ _
    exact continuous_norm.comp ((PiLp.continuous_toLp _ _).comp
      (continuous_scaledGradient.comp (ho.prodMk hg)))
  have huc := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous ha.continuousOn)
  have hz : Tendsto (a ∘ run.x) atTop (𝓝 0) :=
    scalar_btr_criticality run (fun _ => norm_nonneg _) (half_pos hα)
      (by linarith) hβ₀ (le_add_of_nonneg_right (mul_nonneg hL hB₀))
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le hB)) hval hdec herror hstep
      (fun ε hε => by
        obtain ⟨r, hr, hh⟩ := huc ε hε
        refine ⟨r, hr, fun i j hij => ?_⟩
        simpa only [Real.dist_eq, Function.comp_apply] using hh (run.x i) (hxS i) (run.x j) (hxS j)
          (by simpa only [dist_eq_norm] using hij)) hlower
  refine ⟨hz, fun z j hj hjz => ?_⟩
  exact orthantFirstOrder_of_tendsto_scaledGradientNorm
    ((PiLp.continuous_ofLp _ _).continuousAt.tendsto.comp hjz)
    (hg.continuousAt.tendsto.comp hjz) (Eventually.of_forall fun k i => (hx (j k) i).le)
    (hz.comp hj)

open ConnGouldToint.Chapter06 in
/-- **Theorem 13.12.6** of [conn2000trust], for Algorithm 13.12.2. Let $f$ be bounded below, with
gradient coordinates $g$ and objective Hessian $A$ as functions of the point. Let $x_k$, $s_k$,
$\Delta_k > 0$, $H_k$ and $\tau_k$ satisfy: $x_k$ is strictly positive,
$\|s_k\| \le K \Delta_k$, $\|S_k g(x_k)\| \to 0$, the agreement (13.12.25) holds for $A(x_k)$
and $H_k$, and $w^T \hat H_k w \ge \tau_k \|w\|^2$ for all $w$. Let $x_{j(n)} \to z$ along a
strictly increasing $j$, with $g$ and $A$ continuous at $z$, and let
$\kappa, \bar\Delta, K > 0$, $1 < \gamma_3 \le \gamma_4$ and $\Delta_e > 0$. Let
$\mathrm{pred}_k$ be the predicted decrease of the corrected model and $\rho_k$ the ratio
(13.12.24). Suppose that

* $\mathrm{pred}_k > 0$ for all $k$, and $\kappa |\tau_k| \min\{\tau_k^2, \Delta_k^2,
  \bar\Delta^2\} \le \mathrm{pred}_k$ whenever $\tau_k < 0$;
* for every $\epsilon > 0$ there is $\delta > 0$ such that eventually $\Delta_k \le \delta$
  implies $|q_k(s_k) - f(x_k + s_k)| \le \epsilon \Delta_k^2$, where $q_k$ is the uncorrected
  model;
* $x_{k+1} = x_k + s_k$ if $\rho_k \ge \eta_1$, and $x_{k+1} = x_k$ otherwise, and the radii
  follow the rule (6.1.5) with $\rho_k$;
* if $\rho_k \ge \eta_2$ and $\Delta_k \le \Delta_e$, then $\gamma_3 \Delta_k \le \Delta_{k+1}
  \le \gamma_4 \Delta_k$.

Then $z$ is weakly second-order critical for $g(z)$ and $A(z)$.

The corrected ratio gives objective decrease, and the uncorrected model error makes small-radius
trials very successful. The forced expansion then excludes a negative curvature direction on the
active face at $z$. The first-order limit and the uniform small-radius agreement of the
uncorrected model are hypotheses. -/
theorem theorem_13_12_6_version2
    {P : BTRParams} (f : (ι → ℝ) → ℝ) (g : EuclideanSpace ℝ ι → (ι → ℝ))
    (A : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (H : ℕ → Matrix ι ι ℝ)
    (x s : ℕ → EuclideanSpace ℝ ι) (Δ τ : ℕ → ℝ) {z : EuclideanSpace ℝ ι}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (x ∘ j) atTop (𝓝 z))
    (hg : ContinuousAt g z) (hA : ContinuousAt A z)
    (hpos : ∀ k i, 0 < x k i)
    (hfirst : Tendsto (fun k => scaledGradientNorm (WithLp.ofLp (x k)) (g (x k))) atTop (𝓝 0))
    (hcons : ScaledHessianConsistency (fun k => WithLp.ofLp (x k))
      (g ∘ x) (A ∘ x) H)
    (hcurv : ∀ k w, τ k * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      w ⬝ᵥ (scaledHessian (WithLp.ofLp (x k)) (g (x k)) (H k) *ᵥ w))
    {κ cap K γ₃ γ₄ capExpand : ℝ}
    (hκ : 0 < κ) (hcap : 0 < cap) (hK : 0 < K)
    (hγ₃ : 1 < γ₃) (hγ₄ : γ₃ ≤ γ₄) (hcapExpand : 0 < capExpand)
    (hΔ : ∀ k, 0 < Δ k) (hstep : ∀ k, ‖s k‖ ≤ K * Δ k)
    (hlower : BddBelow (Set.range f)) :
    let y (k : ℕ) := WithLp.ofLp (x k)
    let v (k : ℕ) := WithLp.ofLp (s k)
    let pred (k : ℕ) := f (y k) - unscaledModel (f (y k)) (y k) (g (x k)) (H k) (v k)
    let ρ (k : ℕ) := colemanLiAcceptanceRatio f (y k) (g (x k)) (v k) (H k)
    (∀ k, 0 < pred k) →
    (∀ k, τ k < 0 → κ * |τ k| * min (min (τ k ^ 2) (Δ k ^ 2)) (cap ^ 2) ≤ pred k) →
    (∀ ε > 0, ∃ δ > 0, ∀ᶠ k in atTop, Δ k ≤ δ →
      |affineQuadraticModel (f (y k)) (g (x k)) (H k) (v k) - f (y k + v k)| ≤ ε * Δ k ^ 2) →
    (∀ k, x (k + 1) = if P.η₁ ≤ ρ k then x k + s k else x k) →
    (∀ k, BTRRadiusUpdate P (ρ k) (Δ k) (Δ (k + 1))) →
    (∀ k, P.η₂ ≤ ρ k → Δ k ≤ capExpand →
      γ₃ * Δ k ≤ Δ (k + 1) ∧ Δ (k + 1) ≤ γ₄ * Δ k) →
    OrthantWeakSecondOrder (WithLp.ofLp z) (g z) (A z) := by
  dsimp only
  intro hp hdec herr hupdate hrad hgrow
  let y (k : ℕ) := WithLp.ofLp (x k)
  let v (k : ℕ) := WithLp.ofLp (s k)
  let pred (k : ℕ) := f (y k) - unscaledModel (f (y k)) (y k) (g (x k)) (H k) (v k)
  let ρ (k : ℕ) := colemanLiAcceptanceRatio f (y k) (g (x k)) (v k) (H k)
  let S := {k | P.η₁ ≤ ρ k}
  let F (k : ℕ) := f (y k)
  have hf : ∀ k ∈ S, P.η₁ * pred k ≤ F k - F (k + 1) := by
    intro k hk
    have hcorr := colemanLiCorrection_nonneg (y k) (g (x k)) (v k)
    have hρ : P.η₁ ≤ ρ k := hk
    have he : ρ k = (F k - f (y k + v k) - (1 / 2) *
        (v k ⬝ᵥ (unscaledCorrection (y k) (g (x k)) *ᵥ v k))) / pred k := by
      simp [ρ, pred, F, colemanLiAcceptanceRatio, unscaledModel, affineQuadraticModel]
    rw [he] at hρ
    have hh := (le_div_iff₀ (hp k)).mp hρ
    have hxs : x (k + 1) = x k + s k := by rw [hupdate, ite_eq_left (show P.η₁ ≤ ρ k from hk)]
    have hy : F (k + 1) = f (y k + v k) := by dsimp [F, y, v]; rw [hxs]; rfl
    rw [hy]
    linarith
  have hstay (k : ℕ) (hk : k ∉ S) : x (k + 1) = x k := by
    rw [hupdate, ite_eq_right (show ¬ P.η₁ ≤ ρ k from hk)]
  have hmono : Antitone F := by
    apply antitone_nat_of_succ_le
    intro k
    by_cases hk : k ∈ S
    · exact sub_nonneg.mp ((mul_pos P.eta₁_pos (hp k)).le.trans (hf k hk))
    · change f (WithLp.ofLp (x (k + 1))) ≤ f (WithLp.ofLp (x k))
      rw [hstay k hk]
  have hFlim := tendsto_atTop_ciInf hmono
    (hlower.mono (show Set.range F ⊆ Set.range f from Set.range_comp_subset_range y f))
  have hdrop : Tendsto (fun k => F k - F (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using
      hFlim.sub (hFlim.comp (tendsto_add_atTop_nat 1))
  by_contra hnoncritical
  have hlocal : ∃ a > 0, ∃ r > 0, ∀ᶠ k in atTop, dist (x k) z < r → τ k ≤ -a := by
    by_contra hn
    let e (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
    have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hfq (n : ℕ) : ∃ᶠ k in atTop, dist (x k) z < e n ∧ -e n < τ k := by
      by_contra hbad
      have hev : ∀ᶠ k in atTop, ¬(dist (x k) z < e n ∧ -e n < τ k) := by
        simpa only [Filter.Frequently, not_not] using hbad
      exact hn ⟨e n, hepos n, e n, hepos n, hev.mono fun k hk hd =>
        not_lt.mp (fun ht => hk ⟨hd, ht⟩)⟩
    obtain ⟨i, hi, hib⟩ := extraction_forall_of_frequently hfq
    have hzi : Tendsto (x ∘ i) atTop (𝓝 z) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (he.eventually_lt_const hε)
      exact ⟨N, fun k hk => (hib k).1.trans (hN k hk)⟩
    have hco : ScaledHessianConsistency (y ∘ i) (g ∘ x ∘ i) (A ∘ x ∘ i) (H ∘ i) :=
      fun _ => (hcons hfirst).comp hi.tendsto_atTop
    have hzero := theorem_13_12_6
      ((PiLp.continuous_ofLp _ _).continuousAt.tendsto.comp hzi) (hg.tendsto.comp hzi)
      (hA.tendsto.comp hzi) (fun k => hpos (i k))
      (hfirst.comp hi.tendsto_atTop) hco he (fun k => (hepos k).le) (fun k w =>
        (mul_le_mul_of_nonneg_right (hib k).2.le (sq_nonneg _)).trans (hcurv (i k) w))
    exact hnoncritical hzero
  obtain ⟨a, ha, r, hr, hnear⟩ := hlocal
  let c := min a cap
  have hc : 0 < c := lt_min ha hcap
  have hpred (k : ℕ) (hk : τ k ≤ -a) :
      κ * a * min (c ^ 2) (Δ k ^ 2) ≤ pred k := by
    have hτ := hk.trans_lt (neg_lt_zero.mpr ha)
    have habs : a ≤ |τ k| := by rw [abs_of_neg hτ]; linarith
    have hmin : min (c ^ 2) (Δ k ^ 2) ≤ min (min (τ k ^ 2) (Δ k ^ 2)) (cap ^ 2) := by
      apply le_min
      · apply min_le_min _ le_rfl
        simpa only [sq_abs] using
          pow_le_pow_left₀ hc.le ((min_le_left a cap).trans habs) 2
      · exact (min_le_left _ _).trans (pow_le_pow_left₀ hc.le (min_le_right a cap) 2)
    exact (mul_le_mul (mul_le_mul_of_nonneg_left habs hκ.le) hmin
      (le_min (sq_nonneg _) (sq_nonneg _)) (mul_nonneg hκ.le (abs_nonneg _))).trans (hdec k hτ)
  let margin := (1 - P.η₂) * (κ * a)
  have hm : 0 < margin := mul_pos (sub_pos.mpr P.eta₂_lt_one) (mul_pos hκ ha)
  obtain ⟨δ, hδ, herror⟩ := herr margin hm
  have hvery : ∀ᶠ k in atTop, dist (x k) z < r → Δ k ≤ min δ c → P.η₂ ≤ ρ k := by
    filter_upwards [hnear, herror] with k hn he hdist hsmall
    have hlow := hpred k (hn hdist)
    rw [min_eq_right (pow_le_pow_left₀ (hΔ k).le (hsmall.trans (min_le_right _ _)) 2)] at hlow
    have heq := colemanLiAcceptanceRatio_sub_one f (y k) (g (x k)) (v k) (H k)
      (by simpa [unscaledModel, affineQuadraticModel] using (hp k).ne')
    have hupper := (neg_abs_le _).trans' (neg_le_neg (he (hsmall.trans (min_le_left _ _))))
    have hb := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr P.eta₂_lt_one.le)
    have hquot : -(1 - P.η₂) ≤
        (affineQuadraticModel (F k) (g (x k)) (H k) (v k) - f (y k + v k)) / pred k :=
      (le_div_iff₀ (hp k)).mpr (by dsimp [margin] at hupper; nlinarith only [hupper, hb])
    simp only [unscaledModel, affineQuadraticModel, Matrix.mulVec_zero, dotProduct_zero,
      mul_zero, add_zero] at heq
    change ρ k - 1 =
      (affineQuadraticModel (F k) (g (x k)) (H k) (v k) - f (y k + v k)) / pred k at heq
    rw [← heq] at hquot
    linarith
  have hsmall : ∀ ε > 0, ∀ᶠ k in atTop, dist (x k) z < r → k ∈ S → Δ k < ε := by
    intro ε hε
    let b := P.η₁ * (κ * a * min (c ^ 2) (ε ^ 2))
    have hb : 0 < b := mul_pos P.eta₁_pos (mul_pos (mul_pos hκ ha)
      (lt_min (sq_pos_of_pos hc) (sq_pos_of_pos hε)))
    filter_upwards [hnear, hdrop.eventually_lt_const hb] with k hn hd hk hs
    by_contra! hbad
    have hlow := (mul_le_mul_of_nonneg_left (min_le_min le_rfl
      (pow_le_pow_left₀ hε.le hbad 2)) (mul_nonneg hκ.le ha.le)).trans (hpred k (hn hk))
    exact hd.not_ge ((mul_le_mul_of_nonneg_left hlow P.eta₁_pos.le).trans (hf k hs))
  exact (false_of_local_radius_expansion hj hz
    (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂) P.gamma₂_lt_one hγ₃ hγ₄ hcapExpand hK
    hr (lt_min hδ hc) hΔ hstay
    (fun k hk => ((hrad k).unsuccessful (lt_of_not_ge hk)).2)
    (fun k hk => by
      have he : x (k + 1) = x k + s k := by rw [hupdate, ite_eq_left (show P.η₁ ≤ ρ k from hk)]
      rw [he, dist_eq_norm, add_sub_cancel_left]
      exact hstep k)
    (hvery.mono fun _ hk hr hd => P.eta₁_le_eta₂.trans (hk hr hd))
    (hvery.mono fun k hk hr hd hc => hgrow k (hk hr hd) hc) hsmall).elim

end Convergence

end Finite

/-!
### Counterexample to the printed Cauchy bound

A one-dimensional example shows that Theorem 13.12.3 fails without the fraction-to-boundary cap.
-/

/-- The scalar model $s + \frac12 \frac1x s^2$ of the counterexample to Theorem 13.12.3. For the
unit gradient and the zero objective-model Hessian, it is the corrected model (13.12.8) at a
positive point $x$. -/
noncomputable def scalarColemanLiModel (x s : ℝ) : ℝ :=
  s + (1 / 2) * (1 / x) * s ^ 2

/-- For $x > 0$, the scalar model $s + \frac12 \frac1x s^2$ equals the corrected model (13.12.8) on
$\mathbb{R}^1$ with value $0$, point $x$, gradient $1$ and Hessian $0$. -/
theorem scalarColemanLiModel_eq_unscaledModel {x : ℝ} (hx : 0 < x) (s : ℝ) :
    scalarColemanLiModel x s =
      unscaledModel 0 (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) 0 (fun _ ↦ s) := by
  simp [scalarColemanLiModel, unscaledModel, affineQuadraticModel, unscaledCorrection,
    scalingVector, abs_of_pos hx, dotProduct, Matrix.mulVec_diagonal]
  ring

/-- For $x > 0$, the scaled gradient of the scalar example has norm $\|S g\| = \sqrt{x}$. -/
theorem scalarColemanLiGradientNorm {x : ℝ} (hx : 0 < x) :
    scaledGradientNorm (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) = Real.sqrt x := by
  have h : scaledGradient (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) = fun _ ↦ Real.sqrt x := by
    funext i
    simp [scaledGradient, scalingMatrix, Matrix.mulVec_diagonal, scalingVector, abs_of_pos hx]
  rw [scaledGradientNorm, h, EuclideanSpace.norm_eq]
  simp

/-- For $x > 0$, $|x / \sqrt{x}| = \sqrt{x}$: the scaled norm of the ray direction $S^2 g = x$ of
the scalar example is $\sqrt{x}$. -/
theorem scalarColemanLiRayNorm {x : ℝ} (hx : 0 < x) :
    |x / Real.sqrt x| = Real.sqrt x := by
  have hs := Real.sqrt_pos.mpr hx
  rw [abs_of_nonneg (div_nonneg hx.le hs.le), div_eq_iff hs.ne']
  nlinarith [Real.sq_sqrt hx.le]

/-- For $x > 0$, $1 + |\sqrt{x} \cdot \frac1x \cdot \sqrt{x}| = 2$: the curvature constant of
(8.1.22) is $2$ in the scalar example, since the scaled correction has curvature one. -/
theorem scalarColemanLiCurvature {x : ℝ} (hx : 0 < x) :
    1 + |Real.sqrt x * (1 / x) * Real.sqrt x| = 2 := by
  have h : Real.sqrt x * (1 / x) * Real.sqrt x = 1 := by
    field_simp [hx.ne']
    rw [Real.sq_sqrt hx.le]
  rw [h, abs_one]
  norm_num

/-- The feasible times of (13.12.11) for the scalar example: the $t \ge 0$ with $t \sqrt{x} \le 1$
and
$$\tfrac{9}{10} \operatorname{dist}(x, \{0\}) \le \operatorname{dist}(x - t x, \{0\}),$$
where $\{0\}$ is the boundary of $[0, \infty)$. -/
def scalarColemanLiTimes (x : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t * Real.sqrt x ≤ 1 ∧
    (9 / 10) * infDist x (frontier (Set.Ici (0 : ℝ))) ≤
      infDist (x - t * x) (frontier (Set.Ici (0 : ℝ)))}

private theorem scalarColemanLiTimes_iff {x t : ℝ} (hx : 0 < x) :
    t ∈ scalarColemanLiTimes x ↔
      0 ≤ t ∧ t * Real.sqrt x ≤ 1 ∧ (9 / 10 : ℝ) ≤ |1 - t| := by
  change (0 ≤ t ∧ t * Real.sqrt x ≤ 1 ∧
    (9 / 10) * infDist x (frontier (Set.Ici (0 : ℝ))) ≤
      infDist (x - t * x) (frontier (Set.Ici (0 : ℝ)))) ↔ _
  rw [frontier_Ici, infDist_singleton, infDist_singleton, Real.dist_eq, Real.dist_eq,
    sub_zero, sub_zero, abs_of_pos hx, show x - t * x = (1 - t) * x by ring,
    abs_mul, abs_of_pos hx, mul_le_mul_iff_of_pos_right hx]

private theorem orthantBoundaryDistance_fin_one (x : ℝ) :
    orthantBoundaryDistance (fun _ : Fin 1 ↦ x) = |x| := by
  have hfront : frontier (Optimization.nonnegativeOrthant (Fin 1)) = {0} := by
    ext z
    simp only [Optimization.mem_frontier_nonnegativeOrthant, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, i, hi⟩
      funext j
      rw [Subsingleton.elim j i, hi, Pi.zero_apply]
    · rintro rfl
      exact ⟨fun _ ↦ le_rfl, 0, rfl⟩
  rw [orthantBoundaryDistance, hfront, Set.image_singleton, csInf_singleton,
    EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

private theorem scaledResidual_fin_one {x : ℝ} (hx : 0 < x) :
    (scalingMatrix (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) *
      scalingMatrix (fun _ : Fin 1 ↦ x) (fun _ ↦ 1)) *ᵥ (fun _ ↦ 1) =
    fun _ ↦ x := by
  funext i
  rw [scaledResidual_apply]
  norm_num [abs_of_pos hx]

/-- For $x > 0$, the scalar feasible times are the feasible times (13.12.11) of the one-coordinate
matrix model with point $x$, gradient $1$, radius $1$ and fraction $9/10$. -/
theorem scalarColemanLiTimes_eq_scaledCauchyTimes {x : ℝ} (hx : 0 < x) :
    scalarColemanLiTimes x =
      scaledCauchyTimes (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) 1 (9 / 10) := by
  ext t
  change (0 ≤ t ∧ t * Real.sqrt x ≤ 1 ∧
    (9 / 10) * infDist x (frontier (Set.Ici (0 : ℝ))) ≤
      infDist (x - t * x) (frontier (Set.Ici (0 : ℝ)))) ↔
    (0 ≤ t ∧ t * scaledGradientNorm (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) ≤ 1 ∧
      (9 / 10) * orthantBoundaryDistance (fun _ : Fin 1 ↦ x) ≤
        orthantBoundaryDistance ((fun _ : Fin 1 ↦ x) - t •
          ((scalingMatrix (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) *
            scalingMatrix (fun _ : Fin 1 ↦ x) (fun _ ↦ 1)) *ᵥ (fun _ ↦ 1))))
  rw [scaledResidual_fin_one hx, scalarColemanLiGradientNorm hx]
  have hvec : ((fun _ : Fin 1 ↦ x) - t • (fun _ : Fin 1 ↦ x)) =
      fun _ ↦ x - t * x := by
    funext i
    rfl
  rw [hvec, orthantBoundaryDistance_fin_one, orthantBoundaryDistance_fin_one, frontier_Ici,
    infDist_singleton, infDist_singleton, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]

private theorem scalarColemanLiModel_onRay {x : ℝ} (hx : 0 < x) (t : ℝ) :
    scalarColemanLiModel x (-t * x) = -(x * (t - t ^ 2 / 2)) := by
  unfold scalarColemanLiModel
  field_simp [hx.ne']
  ring

/-- Counterexample to the printed Theorem 13.12.3 of [conn2000trust]. For every $\kappa > 0$ there
are $x > 0$ and a feasible time $t$ of the scalar example with $x - t x > 0$, such that $t$
minimizes $u \mapsto m(-u x)$ over the feasible times and
$$m(0) - m(-t x) < \tfrac12 \pi \min\Big\{\frac\pi2, 1\Big\}, \qquad \pi = \min\{\sqrt{x},
  \kappa\},$$
where $m(s) = s + \frac12 \frac1x s^2$.

The right side is the printed bound with criticality cap $\kappa$, radius $1$ and curvature
constant $2$. The trial point $x - t x$ is strictly positive and the fraction is $9/10$. -/
theorem theorem_13_12_3_counterexample (κmsd : ℝ) (hκ : 0 < κmsd) :
    ∃ x t : ℝ, 0 < x ∧ t ∈ scalarColemanLiTimes x ∧ 0 < x - t * x ∧
      IsMinOn (fun u ↦ scalarColemanLiModel x (-u * x)) (scalarColemanLiTimes x) t ∧
      scalarColemanLiModel x 0 - scalarColemanLiModel x (-t * x) <
        (1 / 2) * min (Real.sqrt x) κmsd * min (min (Real.sqrt x) κmsd / 2) 1 := by
  let a := min 1 κmsd
  have ha : 0 < a := lt_min zero_lt_one hκ
  let x := a ^ 2
  have hx : 0 < x := pow_pos ha _
  have hsqrt : Real.sqrt x = a := Real.sqrt_sq ha.le
  have ha₁ : a ≤ 1 := min_le_left _ _
  have haκ : a ≤ κmsd := min_le_right _ _
  refine ⟨x, 1 / 10, hx, ?_, by linarith, ?_, ?_⟩
  · rw [scalarColemanLiTimes_iff hx, hsqrt]
    norm_num
    linarith
  · apply isMinOn_iff.mpr
    intro u hu
    rw [scalarColemanLiModel_onRay hx, scalarColemanLiModel_onRay hx]
    have hd := ((scalarColemanLiTimes_iff hx).mp hu).2.2
    have hs : (9 / 10 : ℝ) ^ 2 ≤ (1 - u) ^ 2 := by
      rw [← sq_abs (1 - u)]
      exact pow_le_pow_left₀ (by norm_num) hd _
    have hb : u - u ^ 2 / 2 ≤ 19 / 200 := by nlinarith
    have hc := mul_le_mul_of_nonneg_left hb hx.le
    nlinarith only [hc]
  · rw [scalarColemanLiModel_onRay hx, hsqrt, min_eq_left haκ,
      min_eq_left (show a / 2 ≤ 1 by linarith)]
    simp only [scalarColemanLiModel, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, zero_sub,
      neg_neg]
    dsimp [x] at hx ⊢
    nlinarith only [hx]

/-- Counterexample to the printed Theorem 13.12.3 of [conn2000trust], in matrix form. For every
$\kappa > 0$ there are $x > 0$ and a constrained scaled Cauchy time $t$ for the one-coordinate
problem with point $x$, gradient $1$, model Hessian $0$, radius $1$ and fraction $9/10$, such
that
$$m(0) - m(-t S^2 g) < \tfrac12 \pi \min\Big\{\frac\pi2, 1\Big\}, \qquad \pi = \min\{\|S g\|,
  \kappa\},$$
where $m$ is the corrected model (13.12.8) with value $0$.

The curvature constant is $2$ by `ConnGouldToint.Chapter13.scalarColemanLiCurvature`. -/
theorem theorem_13_12_3_matrix_counterexample (κmsd : ℝ) (hκ : 0 < κmsd) :
    ∃ x t : ℝ, 0 < x ∧
      let xv : Fin 1 → ℝ := fun _ ↦ x
      let gv : Fin 1 → ℝ := fun _ ↦ 1
      let π := min (scaledGradientNorm xv gv) κmsd
      IsScaledCauchyTime 0 xv gv 0 1 (9 / 10) t ∧
        unscaledModel 0 xv gv 0 0 -
          unscaledModel 0 xv gv 0 ((-t) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv)) <
        (1 / 2) * π * min (π / 2) 1 := by
  obtain ⟨x, t, hx, ht, _, hm, hlt⟩ := theorem_13_12_3_counterexample κmsd hκ
  let xv : Fin 1 → ℝ := fun _ ↦ x
  let gv : Fin 1 → ℝ := fun _ ↦ 1
  have hray (u : ℝ) : unscaledModel 0 xv gv 0
      ((-u) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv)) =
        scalarColemanLiModel x (-u * x) := by
    rw [show (scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv = xv from scaledResidual_fin_one hx]
    exact (scalarColemanLiModel_eq_unscaledModel hx (-u * x)).symm
  have htimes : scalarColemanLiTimes x = scaledCauchyTimes xv gv 1 (9 / 10) :=
    scalarColemanLiTimes_eq_scaledCauchyTimes hx
  refine ⟨x, t, hx, ⟨htimes ▸ ht, ?_⟩, ?_⟩
  · apply isMinOn_iff.mpr
    intro u hu
    change unscaledModel 0 xv gv 0
        ((-t) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv)) ≤
      unscaledModel 0 xv gv 0 ((-u) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv))
    rw [hray t, hray u]
    exact isMinOn_iff.mp hm u (htimes.symm ▸ hu)
  · change unscaledModel 0 xv gv 0 0 -
        unscaledModel 0 xv gv 0 ((-t) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv)) <
      (1 / 2) * min (scaledGradientNorm xv gv) κmsd *
        min (min (scaledGradientNorm xv gv) κmsd / 2) 1
    rw [hray, show scaledGradientNorm xv gv = Real.sqrt x from scalarColemanLiGradientNorm hx]
    exact (scalarColemanLiModel_eq_unscaledModel hx 0) ▸ hlt

/-!
### Elimination of slack variables

Linear inequality constraints with positive slacks $c \in \mathbb{R}^m$ are written with a slack
step $v$ that satisfies $C^{1/2} v = A s$, where $C = \operatorname{diag}(c)$. The results below
eliminate $v$ and reduce the subproblem in $(s, v)$ to a subproblem in $s$ alone.
-/

section TRAM

variable {m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

/-- **Equations (13.12.28) and (13.12.32)** of [conn2000trust]. For a matrix
$A \in \mathbb{R}^{m \times \iota}$, slacks $c$ and a step $s$, the **slack step** is
$$v_i = \frac{(A s)_i}{\sqrt{c_i}},$$
the solution of $C^{1/2} v = A s$ when $c > 0$. -/
noncomputable def tramSlackStep (A : Matrix m ι ℝ) (c : m → ℝ) (s : ι → ℝ) : m → ℝ :=
  fun i ↦ (A *ᵥ s) i / Real.sqrt (c i)

/-- **Equation (13.12.34)** of [conn2000trust]. The **model correction** is the matrix
$A^T C^{-1} Y A$, where $C = \operatorname{diag}(c)$ and $Y = \operatorname{diag}(y)$.

For the modified model, $y$ is the vector of absolute values of the multipliers. -/
noncomputable def tramCorrection (A : Matrix m ι ℝ) (c y : m → ℝ) : Matrix ι ι ℝ :=
  Aᵀ * Matrix.diagonal (fun i ↦ y i / c i) * A

/-- **Equation (13.12.34)** of [conn2000trust]. The **reduced model** at the displacement $s$ is
$$m_f(s) + \tfrac12 s^T A^T C^{-1} Y A\, s.$$

**Correction.** Both terms are evaluated at the trial displacement $s$, as the elimination of
the slack step from (13.12.31) gives. -/
noncomputable def tramModel (mf : (ι → ℝ) → ℝ) (A : Matrix m ι ℝ)
    (c y : m → ℝ) (s : ι → ℝ) : ℝ :=
  mf s + (1 / 2) * (s ⬝ᵥ (tramCorrection A c y *ᵥ s))

/-- **Equation (13.12.35)** of [conn2000trust]. The **reduced metric** is $I + A^T C^{-1} A$. -/
noncomputable def tramMetric (A : Matrix m ι ℝ) (c : m → ℝ) : Matrix ι ι ℝ :=
  1 + Aᵀ * Matrix.diagonal (fun i ↦ (c i)⁻¹) * A

/-- **Equation (13.12.35)** of [conn2000trust]. The **reduced trust-region norm** of $s$ is
$$\big(s^T (I + A^T C^{-1} A) s\big)^{1/2}.$$
-/
noncomputable def tramNorm (A : Matrix m ι ℝ) (c : m → ℝ) (s : ι → ℝ) : ℝ :=
  Real.sqrt (s ⬝ᵥ (tramMetric A c *ᵥ s))

omit [DecidableEq ι] in
/-- **Equation (13.12.32)** of [conn2000trust]. If $c_i > 0$ for all $i$, then for each step $s$ the
slack step is the unique solution $v$ of $C^{1/2} v = A s$. -/
theorem tramSlackStep_unique (A : Matrix m ι ℝ) {c : m → ℝ} (hc : ∀ i, 0 < c i)
    (s : ι → ℝ) (v : m → ℝ) :
    Matrix.diagonal (fun i ↦ Real.sqrt (c i)) *ᵥ v = A *ᵥ s ↔
      v = tramSlackStep A c s := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    rw [Matrix.mulVec_diagonal] at hi
    exact (eq_div_iff (Real.sqrt_pos.2 (hc i)).ne').2 (by simpa [mul_comm] using hi)
  · rintro rfl
    funext i
    rw [Matrix.mulVec_diagonal]
    exact mul_div_cancel₀ _ (Real.sqrt_pos.2 (hc i)).ne'

omit [DecidableEq ι] in
private theorem tramCorrection_quadratic (A : Matrix m ι ℝ) {c : m → ℝ} (hc : ∀ i, 0 < c i)
    (y : m → ℝ) (s : ι → ℝ) :
    s ⬝ᵥ (tramCorrection A c y *ᵥ s) = ∑ i, y i * (tramSlackStep A c s i) ^ 2 := by
  rw [tramCorrection, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  unfold tramSlackStep
  rw [div_pow, Real.sq_sqrt (hc i).le]
  ring

omit [DecidableEq ι] in
/-- Reduction from (13.12.31) to (13.12.34) in [conn2000trust]. If $c_i > 0$ for all $i$, the
reduced model is the model with slacks evaluated at the slack step $v$ of $s$:
$$m_f(s) + \tfrac12 s^T A^T C^{-1} Y A\, s = m_f(s) + \tfrac12 \sum_i y_i v_i^2.$$
-/
theorem tramModel_eq_slackModel (mf : (ι → ℝ) → ℝ) (A : Matrix m ι ℝ) {c : m → ℝ}
    (hc : ∀ i, 0 < c i) (y : m → ℝ) (s : ι → ℝ) :
    tramModel mf A c y s = mf s + (1 / 2) * ∑ i, y i * (tramSlackStep A c s i) ^ 2 := by
  rw [tramModel, tramCorrection_quadratic A hc]

private theorem tramNorm_eq_slackNorm (A : Matrix m ι ℝ) {c : m → ℝ} (hc : ∀ i, 0 < c i)
    (s : ι → ℝ) :
    tramNorm A c s = Real.sqrt ((∑ i, s i ^ 2) + ∑ i, (tramSlackStep A c s i) ^ 2) := by
  have hmetric : tramMetric A c = 1 + tramCorrection A c (fun _ ↦ 1) := by
    simp [tramMetric, tramCorrection, one_div]
  rw [tramNorm, hmetric, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
    tramCorrection_quadratic A hc]
  simp only [one_mul]
  congr 2
  simp only [dotProduct, pow_two]

/-- **Equations (13.12.33) and (13.12.35)** of [conn2000trust]. If $c_i > 0$ for all $i$, then
$\|s\|_{I + A^T C^{-1} A} \le \Delta$ if and only if there is $v$ with
$$C^{1/2} v = A s \quad\text{and}\quad \big(\|s\|^2 + \|v\|^2\big)^{1/2} \le \Delta.$$
So the reduced bound is equivalent to the Euclidean trust-region bound (13.12.33) on the joint
step $(s, v)$.

**Typo.** The printed display (13.12.35) contains a stray factor $n$. The reduced bound uses the
radius $\Delta$ of (13.12.33). -/
theorem tramNorm_le_iff_exists_slack (A : Matrix m ι ℝ) {c : m → ℝ} (hc : ∀ i, 0 < c i)
    (s : ι → ℝ) (Δ : ℝ) :
    tramNorm A c s ≤ Δ ↔ ∃ v : m → ℝ,
      Matrix.diagonal (fun i ↦ Real.sqrt (c i)) *ᵥ v = A *ᵥ s ∧
      Real.sqrt ((∑ i, s i ^ 2) + ∑ i, v i ^ 2) ≤ Δ := by
  simp only [tramSlackStep_unique A hc, tramNorm_eq_slackNorm A hc]
  exact ⟨fun h ↦ ⟨_, rfl, h⟩, fun ⟨_, rfl, h⟩ ↦ h⟩

/-- **Equations (13.12.31)–(13.12.35)** of [conn2000trust], slack elimination. Let $c_i > 0$ for all
$i$, and let $v(s)$ be the slack step of $s$. Then $s$ minimizes the reduced model over
$\{t : \|t\|_{I + A^T C^{-1} A} \le \Delta\}$ and lies in this set if and only if $(s, v(s))$
minimizes
$$M(t, w) = m_f(t) + \tfrac12 \sum_i y_i w_i^2$$
over $\{(t, w) : C^{1/2} w = A t,\ (\|t\|^2 + \|w\|^2)^{1/2} \le \Delta\}$ and lies in this set. -/
theorem tramSubproblem_iff (mf : (ι → ℝ) → ℝ) (A : Matrix m ι ℝ) {c : m → ℝ}
    (hc : ∀ i, 0 < c i) (y : m → ℝ) (s : ι → ℝ) (Δ : ℝ) :
    let S := {t | tramNorm A c t ≤ Δ}
    let V := {q : (ι → ℝ) × (m → ℝ) |
      Matrix.diagonal (fun i ↦ Real.sqrt (c i)) *ᵥ q.2 = A *ᵥ q.1 ∧
      Real.sqrt ((∑ i, q.1 i ^ 2) + ∑ i, q.2 i ^ 2) ≤ Δ}
    let M := fun q : (ι → ℝ) × (m → ℝ) ↦ mf q.1 + (1 / 2) * ∑ i, y i * (q.2 i) ^ 2
    (s ∈ S ∧ IsMinOn (tramModel mf A c y) S s) ↔
      ((s, tramSlackStep A c s) ∈ V ∧ IsMinOn M V (s, tramSlackStep A c s)) := by
  dsimp only
  have hfeas (t : ι → ℝ) :
      (t, tramSlackStep A c t) ∈ {q : (ι → ℝ) × (m → ℝ) |
        Matrix.diagonal (fun i ↦ Real.sqrt (c i)) *ᵥ q.2 = A *ᵥ q.1 ∧
        Real.sqrt ((∑ i, q.1 i ^ 2) + ∑ i, q.2 i ^ 2) ≤ Δ} ↔ tramNorm A c t ≤ Δ := by
    simp [tramSlackStep_unique A hc, tramNorm_eq_slackNorm A hc]
  constructor
  · intro ⟨hs, hmin⟩
    refine ⟨(hfeas s).2 hs, isMinOn_iff.mpr ?_⟩
    rintro ⟨t, v⟩ ⟨hv, hΔ⟩
    obtain rfl := (tramSlackStep_unique A hc t v).1 hv
    have ht := (tramNorm_eq_slackNorm A hc t).trans_le hΔ
    simpa only [tramModel_eq_slackModel mf A hc] using (isMinOn_iff.mp hmin t ht)
  · intro ⟨hs, hmin⟩
    refine ⟨(hfeas s).1 hs, isMinOn_iff.mpr ?_⟩
    intro t ht
    simpa only [tramModel_eq_slackModel mf A hc] using
      (isMinOn_iff.mp hmin (t, tramSlackStep A c t) ((hfeas t).2 ht))

end TRAM

end ConnGouldToint.Chapter13
