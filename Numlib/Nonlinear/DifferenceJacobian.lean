/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Normed.Lp.PiLp

/-!
# Difference approximations of the Jacobian matrix

Let $F : \mathbb{R}^n \to \mathbb{R}^n$, let $x \in \mathbb{R}^n$, and let $h_1, \dots, h_n$ be
nonzero increments. The **forward-difference Jacobian** $J_h$ of $F$ at $x$ is the matrix whose
column $j$ is the difference quotient along the canonical basis vector $e_j$,
$$(J_h)_j = \frac{F(x + h_j e_j) - F(x)}{h_j}.$$
This is (7.9) in §7.1.2 of [quarteroni2000numerical]. The module bounds the error of $J_h$ against
the derivative $F'(x)$. If $F'$ is $L$-Lipschitz around $x$, then column by column
$\|(J_h - F'(x)) e_j\| \le (L/2)|h_j|$, and in the operator norm
$$\|J_h - F'(x)\| \le \sqrt{n}\, \frac{L}{2} \max_j |h_j|.$$

The theorems on Newton-like iterations with approximate derivatives in `Numlib.Nonlinear.Newton`
(`Newton.norm_approxStep_sub_le`, `Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le`,
`Newton.norm_succ_sub_le_sq_of_norm_sub_fderiv_le_mul`) take an arbitrary approximation $B_k$ of
$F'(x_k)$. The matrix `Matrix.toEuclideanCLM (Matrix.differenceJacobian F (x k) (h k))` is an
instance of $B_k$. The convergence of the Newton method with difference Jacobians, Property 7.1 of
[quarteroni2000numerical], is the combination of these theorems with the bounds of this module.

## Main definitions

* `Matrix.differenceJacobian`: the forward-difference Jacobian $J_h$ of $F$ at $x$.

## Main results

* `Matrix.toEuclideanCLM_differenceJacobian_single`: $J_h e_j = (F(x + h_j e_j) - F(x))/h_j$.
* `Matrix.norm_differenceJacobian_col_sub_le`: $\|(J_h - F'(x)) e_j\| \le (L/2)|h_j|$.
* `Matrix.opNorm_toEuclideanCLM_differenceJacobian_sub_le`:
  $\|J_h - F'(x)\| \le \sqrt{n}\,(L/2)\,\eta$ when $|h_j| \le \eta$ for all $j$.

## Implementation notes

* The space is `EuclideanSpace ℝ ι`, and a matrix acts on it through `Matrix.toEuclideanCLM`. A
  difference Jacobian needs coordinates, and `Numlib.Nonlinear.Newton` works in Banach spaces with
  no basis.
* The column-wise bound is the sharp second-order mean value inequality
  `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le` of `Numlib.Analysis.Calculus.MeanValue`.
* [quarteroni2000numerical] states Property 7.1 in the norm $\|\cdot\|_1$. There the column-wise
  bound gives $\|J_h - F'(x)\|_1 \le (L/2) \max_j |h_j|$ with no factor that depends on the
  dimension. In the Euclidean norm of this module the factor $\sqrt{n}$ appears, from
  $\sum_j |v_j| \le \sqrt{n}\, \|v\|_2$. The factor does not change the convergence conclusions.
-/

open scoped InnerProductSpace

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **forward-difference Jacobian** of $F : \mathbb{R}^n \to \mathbb{R}^n$ at $x$ with
increments $h \in \mathbb{R}^n$. It is the matrix with entries
$$(J_h)_{ij} = \frac{F_i(x + h_j e_j) - F_i(x)}{h_j},$$
so that column $j$ is the difference quotient of $F$ along the $j$-th canonical basis vector
$e_j$. This is (7.9) of [quarteroni2000numerical].

An increment $h_j = 0$ gives the column $0$, because division by zero gives $0$ in Lean. -/
noncomputable def differenceJacobian (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (h : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (F (x + h j • EuclideanSpace.single j 1) i - F x i) / h j

omit [Fintype ι] in
/-- The entry $(i, j)$ of the difference Jacobian is $(F_i(x + h_j e_j) - F_i(x))/h_j$. -/
theorem differenceJacobian_apply (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (h : ι → ℝ) (i j : ι) :
    differenceJacobian F x h i j = (F (x + h j • EuclideanSpace.single j 1) i - F x i) / h j :=
  rfl

/-- Column $j$ of the difference Jacobian, read as the image of the basis vector $e_j$ under the
matrix acting on $\mathbb{R}^n$, is the difference quotient of $F$ along $e_j$:
$$J_h e_j = h_j^{-1} \bigl(F(x + h_j e_j) - F(x)\bigr).$$
This holds for every $h$; for $h_j = 0$ both sides are $0$. -/
theorem toEuclideanCLM_differenceJacobian_single (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (h : ι → ℝ) (j : ι) :
    toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) (EuclideanSpace.single j 1)
      = (h j)⁻¹ • (F (x + h j • EuclideanSpace.single j 1) - F x) := by
  ext i
  simp [ofLp_toEuclideanCLM, differenceJacobian, div_eq_inv_mul]

/-- **Column-wise error of the difference Jacobian.** Let $F : \mathbb{R}^n \to \mathbb{R}^n$, let
$x \in \mathbb{R}^n$ and $r, L \in \mathbb{R}$. Assume that $F$ has the derivative $F'(y)$ at
every $y$ in the open ball $B(x, r)$, with
$$\|F'(y) - F'(x)\| \le L \|y - x\| \quad \text{for } y \in B(x, r).$$
Let $h \in \mathbb{R}^n$ and $j$ an index with $h_j \neq 0$ and $|h_j| < r$. Then
$$\|(J_h - F'(x)) e_j\| \le \frac{L}{2} |h_j|.$$

The difference quotient along $e_j$ is within $(L/2)|h_j|$ of the directional derivative
$F'(x) e_j$, by the sharp second-order mean value inequality
`Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`. -/
theorem norm_differenceJacobian_col_sub_le {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {F' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {x : EuclideanSpace ℝ ι} {r L : ℝ} (hF : ∀ y ∈ Metric.ball x r, HasFDerivAt F (F' y) y)
    (hL : ∀ y ∈ Metric.ball x r, ‖F' y - F' x‖ ≤ L * ‖y - x‖) {h : ι → ℝ} {j : ι}
    (hj0 : h j ≠ 0) (hjr : |h j| < r) :
    ‖(toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) - F' x) (EuclideanSpace.single j 1)‖
      ≤ L / 2 * |h j| := by
  set v : EuclideanSpace ℝ ι := h j • EuclideanSpace.single j 1 with hv
  have hvn : ‖v‖ = |h j| := by
    rw [hv, norm_smul, Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hjr
  have hmem : x + v ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hvn]
    exact hjr
  have htay : ‖F (x + v) - F x - F' x (x + v - x)‖ ≤ L / 2 * ‖x + v - x‖ ^ 2 :=
    Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le (convex_ball x r) hF
      (Metric.mem_ball_self hr) hmem hL
  rw [add_sub_cancel_left, hvn] at htay
  have hkey : (toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) - F' x)
      (EuclideanSpace.single j 1) = (h j)⁻¹ • (F (x + v) - F x - F' x v) := by
    have hFv : F' x v = h j • F' x (EuclideanSpace.single j 1) := by rw [hv, map_smul]
    rw [_root_.sub_apply, toEuclideanCLM_differenceJacobian_single, ← hv, hFv]
    simp only [smul_sub]
    rw [smul_smul, inv_mul_cancel₀ hj0, one_smul]
  rw [hkey, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |h j|⁻¹ * ‖F (x + v) - F x - F' x v‖ ≤ |h j|⁻¹ * (L / 2 * |h j| ^ 2) := by gcongr
    _ = L / 2 * |h j| := by field_simp

/-- **Operator-norm error of the difference Jacobian.** Let $F : \mathbb{R}^n \to \mathbb{R}^n$, let
$x \in \mathbb{R}^n$ and $r, L \in \mathbb{R}$. Assume that $F$ has the derivative $F'(y)$ at
every $y$ in the open ball $B(x, r)$, with $\|F'(y) - F'(x)\| \le L \|y - x\|$ there. Let
$h \in \mathbb{R}^n$ with $h_j \neq 0$ and $|h_j| < r$ for every $j$, and let $|h_j| \le \eta$
for every $j$. Then, in the operator norm on Euclidean space,
$$\|J_h - F'(x)\| \le \sqrt{n}\, \frac{L}{2}\, \eta.$$

Here $n$ is the cardinality of the index type `ι`. The proof expands $v$ in the canonical basis,
uses $\|(J_h - F'(x)) v\| \le \sum_j |v_j| \|(J_h - F'(x)) e_j\| \le (L/2)\, \eta \sum_j |v_j|$,
and bounds $\sum_j |v_j| \le \sqrt{n}\, \|v\|$ with
`PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two`. In the norm $\|\cdot\|_1$ of Property 7.1
of [quarteroni2000numerical] the last step is an equality, and the factor $\sqrt{n}$ is absent. -/
theorem opNorm_toEuclideanCLM_differenceJacobian_sub_le
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {F' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {x : EuclideanSpace ℝ ι} {r L : ℝ} (hF : ∀ y ∈ Metric.ball x r, HasFDerivAt F (F' y) y)
    (hL : ∀ y ∈ Metric.ball x r, ‖F' y - F' x‖ ≤ L * ‖y - x‖) {h : ι → ℝ}
    (hj : ∀ j, h j ≠ 0 ∧ |h j| < r) {η : ℝ} (hη : ∀ j, |h j| ≤ η) :
    ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) - F' x‖
      ≤ √(Fintype.card ι : ℝ) * (L / 2) * η := by
  set D := toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) - F' x with hD
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hD0 : D = 0 := by
      ext v i
      exact isEmptyElim i
    rw [hD0, norm_zero, Fintype.card_eq_zero]
    simp
  obtain ⟨j₀⟩ := hι
  -- `L ≥ 0`, from the Lipschitz bound at one increment
  have hL0 : 0 ≤ L := by
    have hpos : 0 < |h j₀| := abs_pos.2 (hj j₀).1
    have hmem : x + h j₀ • EuclideanSpace.single j₀ 1 ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        PiLp.norm_single, norm_one, mul_one]
      exact (hj j₀).2
    have h1 := hL _ hmem
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, PiLp.norm_single, norm_one,
      mul_one] at h1
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h1) hpos
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη j₀)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hcol : ∀ i, ‖D (EuclideanSpace.single i 1)‖ ≤ L / 2 * η := fun i =>
    (norm_differenceJacobian_col_sub_le hF hL (hj i).1 (hj i).2).trans
      (mul_le_mul_of_nonneg_left (hη i) (by linarith))
  have hv : ∑ i, v i • EuclideanSpace.single i 1 = v := by
    conv_rhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hsum : ∑ i, |v i| ≤ √(Fintype.card ι : ℝ) * ‖v‖ := by
    have h1 := PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two (WithLp.ofLp v)
    rw [PiLp.norm_eq_of_L1] at h1
    simpa [Real.norm_eq_abs] using h1
  calc ‖D v‖ = ‖∑ i, v i • D (EuclideanSpace.single i 1)‖ := by
        conv_lhs => rw [← hv]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ i, ‖v i • D (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i, |v i| * ‖D (EuclideanSpace.single i 1)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |v i| * (L / 2 * η) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcol i) (abs_nonneg _)
    _ = L / 2 * η * ∑ i, |v i| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ L / 2 * η * (√(Fintype.card ι : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = √(Fintype.card ι : ℝ) * (L / 2) * η * ‖v‖ := by ring

end Matrix
