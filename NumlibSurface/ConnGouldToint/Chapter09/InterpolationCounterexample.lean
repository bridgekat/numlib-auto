/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter09.Section04
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Conn, Gould and Toint, Section 9.4: Incomplete quadratic blocks in Theorem 9.4.4

Theorem 9.4.4 of [conn2000trust] bounds the error of a Newton interpolation model (9.4.9) by bounds
on the Newton fundamental polynomials at the points of the next block and on the last block. This
module shows that these bounds do not control the model error when the quadratic block is
incomplete. On $\mathbb{R}^3$, the objective $f(x) = \cos(x_0 - x_1) - \cos(x_0 + x_1) = 2 \sin x_0
\sin x_1$ has globally bounded first and second derivatives. For each radius $\delta \in (0, 1/2]$,
five interpolation points in the ball of radius $\delta$ form a complete affine block and a
quadratic block with a single point. The data are poised and satisfy the Newton conditions (9.4.4)
and the bounds (9.4.18)–(9.4.20) with the constant $3$. For every proposed constant $C > 0$ there is
such a radius $\delta$ at which the model error at the point $(0, 0, \delta)$ exceeds
$C \max\{\delta^2, \delta^3\}$. The corrected error estimate, with affine reproduction and uniform
bounds on all Newton blocks on the ball, is
`ConnGouldToint.Chapter09.theorem_9_4_4_of_uniform_newton_bound`.

## Main definitions

* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticObjective`: the objective
  $f(x) = \cos(x_0 - x_1) - \cos(x_0 + x_1)$.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticBlockSize`: the block sizes $1$, $3$
  and $1$.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticPoints`: the interpolation points for
  the radius $\delta$.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticNewton`: the Newton fundamental
  polynomials of degrees $0$, $1$ and $2$.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticFlatPoints`: the five points in block
  order.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticFlatNewton`: the five Newton
  polynomials in block order.

## Main results

* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticObjective_bounds`: $f$ is $C^2$,
  bounded below by $-2$, and has uniformly bounded first and second derivatives.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticNewton_isPolynomial`: each Newton
  function of block $l \le 2$ is a polynomial of degree at most $l$.
* Equation (9.4.4), `ConnGouldToint.Chapter09.incompleteQuadraticFundamental`: the points and
  polynomials satisfy the Newton conditions.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.incompleteQuadraticPoised`: the five points are poised
  for the five polynomials.
* Equations (9.4.18)–(9.4.20), `ConnGouldToint.Chapter09.incompleteQuadraticPrintedBounds`: the
  points lie in the ball, and the adjacent-block and last-block bounds hold with the constant $3$.
* Theorem 9.4.4, `ConnGouldToint.Chapter09.theorem_9_4_4_incompleteQuadratic_counterexample`: for
  every $C > 0$ some radius violates the error bound (9.4.21).

## Conventions

* Points of $\mathbb{R}^3$ are elements of `EuclideanSpace ℝ (Fin 3)`, with coordinates
  $x_0, x_1, x_2$.
* The interpolation data are indexed by blocks: `incompleteQuadraticPoints δ l i` is the $i$-th
  point of block $l$, and `incompleteQuadraticNewton δ l i` is the matching Newton polynomial. The
  model is `ConnGouldToint.Chapter09.newtonInterpolationModel` of degree $2$.

## Deviations from the source

* **Theorem 9.4.4** (correction). For an incomplete quadratic block, the printed adjacent-block and
  last-block bounds do not imply the error bound (9.4.21). See
  `ConnGouldToint.Chapter09.theorem_9_4_4_incompleteQuadratic_counterexample`.
-/

namespace ConnGouldToint.Chapter09

local notation "V" => EuclideanSpace ℝ (Fin 3)

private noncomputable def xyz (x y z : ℝ) : V := WithLp.toLp 2 ![x, y, z]

@[simp] private theorem xyz_zero (x y z : ℝ) : xyz x y z 0 = x := rfl
@[simp] private theorem xyz_one (x y z : ℝ) : xyz x y z 1 = y := rfl
@[simp] private theorem xyz_two (x y z : ℝ) : xyz x y z 2 = z := rfl

private noncomputable def coord (i : Fin 3) : V →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i

/-- **Theorem 9.4.4** of [conn2000trust], objective of the counterexample. On $\mathbb{R}^3$, the
objective is
$$f(x) = \cos(x_0 - x_1) - \cos(x_0 + x_1) = 2 \sin x_0 \sin x_1.$$
-/
noncomputable def incompleteQuadraticObjective (x : V) : ℝ :=
  Real.cos ((coord 0 - coord 1) x) - Real.cos ((coord 0 + coord 1) x)

private theorem objective_xyz (x y z : ℝ) :
    incompleteQuadraticObjective (xyz x y z) = Real.cos (x - y) - Real.cos (x + y) := rfl

private theorem fderiv_cos_clm (L : V →L[ℝ] ℝ) (x : V) :
    fderiv ℝ (fun y ↦ Real.cos (L y)) x = (-Real.sin (L x)) • L :=
  L.hasFDerivAt.cos.fderiv

private theorem fderiv_fderiv_cos_clm (L : V →L[ℝ] ℝ) (x : V) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (L y))) x =
      (-Real.cos (L x)) • L.smulRight L := by
  rw [show fderiv ℝ (fun y ↦ Real.cos (L y)) = fun y ↦ (-Real.sin (L y)) • L from
    funext (fderiv_cos_clm L)]
  convert (L.hasFDerivAt.sin.neg.smul_const L).fderiv using 1
  ext y z
  simp [ContinuousLinearMap.smulRight_apply, mul_assoc]

private theorem norm_fderiv_cos_clm (L : V →L[ℝ] ℝ) (x : V) :
    ‖fderiv ℝ (fun y ↦ Real.cos (L y)) x‖ ≤ ‖L‖ := by
  rw [fderiv_cos_clm, norm_smul, norm_neg, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

private theorem norm_fderiv_fderiv_cos_clm (L : V →L[ℝ] ℝ) (x : V) :
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (L y))) x‖ ≤ ‖L‖ ^ 2 := by
  rw [fderiv_fderiv_cos_clm]
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro y
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, Real.norm_eq_abs,
    abs_mul, abs_neg]
  have hy : |L y| ≤ ‖L‖ * ‖y‖ := by simpa only [Real.norm_eq_abs] using L.le_opNorm y
  have hz : |L z| ≤ ‖L‖ * ‖z‖ := by simpa only [Real.norm_eq_abs] using L.le_opNorm z
  calc
    _ ≤ |L y| * |L z| :=
      mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.abs_cos_le_one _)
    _ ≤ (‖L‖ * ‖y‖) * (‖L‖ * ‖z‖) := mul_le_mul hy hz (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- **Theorem 9.4.4** of [conn2000trust], AF.1, AF.3 and AF.5 for the counterexample. The objective
$f$ is $C^2$, satisfies $f(x) \ge -2$ for every $x$, and there is $B > 0$ with
$$\|\nabla f(x)\| \le B \qquad \text{and} \qquad \|\nabla^2 f(x)\| \le B \qquad \text{for every
  } x \in \mathbb{R}^3.$$

The constants are independent of the radius and of the interpolation set. -/
theorem incompleteQuadraticObjective_bounds :
    ContDiff ℝ 2 incompleteQuadraticObjective ∧
    (∀ x, -2 ≤ incompleteQuadraticObjective x) ∧
    ∃ B > 0, ∀ x : V, ‖fderiv ℝ incompleteQuadraticObjective x‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ incompleteQuadraticObjective) x‖ ≤ B := by
  let Lminus := coord 0 - coord 1
  let Lplus := coord 0 + coord 1
  let gminus (x : V) := Real.cos (Lminus x)
  let gplus (x : V) := Real.cos (Lplus x)
  have hminus : ContDiff ℝ 2 gminus := Lminus.contDiff.cos
  have hplus : ContDiff ℝ 2 gplus := Lplus.contDiff.cos
  have hdiffminus : Differentiable ℝ gminus := hminus.differentiable (by norm_num)
  have hdiffplus : Differentiable ℝ gplus := hplus.differentiable (by norm_num)
  have hddiffminus : Differentiable ℝ (fderiv ℝ gminus) :=
    (hminus.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hddiffplus : Differentiable ℝ (fderiv ℝ gplus) :=
    (hplus.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hf : incompleteQuadraticObjective = fun x ↦ gminus x - gplus x := rfl
  refine ⟨hminus.sub hplus, ?_,
    1 + ‖Lminus‖ + ‖Lplus‖ + ‖Lminus‖ ^ 2 + ‖Lplus‖ ^ 2, by positivity, ?_⟩
  · intro x
    rw [hf]
    dsimp [gminus, gplus]
    linarith [Real.neg_one_le_cos (Lminus x), Real.cos_le_one (Lplus x)]
  · intro x
    have hfirst : fderiv ℝ incompleteQuadraticObjective =
        fun x ↦ fderiv ℝ gminus x - fderiv ℝ gplus x := by
      funext x
      rw [hf, fderiv_fun_sub (hdiffminus x) (hdiffplus x)]
    rw [hfirst, fderiv_fun_sub (hddiffminus x) (hddiffplus x)]
    have h1 := (norm_sub_le (fderiv ℝ gminus x) (fderiv ℝ gplus x)).trans
      (add_le_add (norm_fderiv_cos_clm Lminus x) (norm_fderiv_cos_clm Lplus x))
    have h2 := (norm_sub_le (fderiv ℝ (fderiv ℝ gminus) x) (fderiv ℝ (fderiv ℝ gplus) x)).trans
      (add_le_add (norm_fderiv_fderiv_cos_clm Lminus x) (norm_fderiv_fderiv_cos_clm Lplus x))
    exact ⟨by linarith [sq_nonneg ‖Lminus‖, sq_nonneg ‖Lplus‖],
      by linarith [norm_nonneg Lminus, norm_nonneg Lplus]⟩

/-- **Theorem 9.4.4** of [conn2000trust], block sizes of the counterexample. Block $0$ has one
point, block $1$ has three points, block $2$ has one point, and all later blocks are empty.

The affine blocks are complete, and the quadratic block has a single point. -/
abbrev incompleteQuadraticBlockSize : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 1
  | _ => 0

/-- **Theorem 9.4.4** of [conn2000trust], interpolation points of the counterexample. For the radius
$\delta$, block $0$ is the point $0$, block $1$ consists of
$$(\delta/2, 0, 0), \qquad (0, \delta/2, 0), \qquad (\delta/2, \delta/2, \delta^2),$$
and block $2$ is the point $(-\delta/2, 0, 0)$.

The third point of block $1$ lies only $\delta^2$ away from the plane through the first three
points. -/
noncomputable def incompleteQuadraticPoints (δ : ℝ) :
    (l : ℕ) → Fin (incompleteQuadraticBlockSize l) → V
  | 0, _ => 0
  | 1, i => ![xyz (δ / 2) 0 0, xyz 0 (δ / 2) 0, xyz (δ / 2) (δ / 2) (δ ^ 2)] i
  | 2, _ => xyz (-(δ / 2)) 0 0
  | _ + 3, i => Fin.elim0 i

/-- **Theorem 9.4.4** of [conn2000trust], Newton polynomials of the counterexample. For the radius
$\delta$, block $0$ is the constant $1$, block $1$ consists of
$$\frac{x_0}{\delta/2} - \frac{x_2}{\delta^2}, \qquad \frac{x_1}{\delta/2} -
  \frac{x_2}{\delta^2}, \qquad \frac{x_2}{\delta^2},$$
and block $2$ is
$$\frac{1}{2} \cdot \frac{x_0}{\delta/2} \Big(\frac{x_0}{\delta/2} - 1\Big).$$
-/
noncomputable def incompleteQuadraticNewton (δ : ℝ) :
    (l : ℕ) → Fin (incompleteQuadraticBlockSize l) → V → ℝ
  | 0, _ => fun _ ↦ 1
  | 1, i => fun x ↦ ![x 0 / (δ / 2) - x 2 / δ ^ 2,
      x 1 / (δ / 2) - x 2 / δ ^ 2, x 2 / δ ^ 2] i
  | 2, _ => fun x ↦ (x 0 / (δ / 2)) * (x 0 / (δ / 2) - 1) / 2
  | _ + 3, i => Fin.elim0 i

private noncomputable def scaledCoordinatePolynomial (i : Fin 3) (a : ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C a⁻¹ * MvPolynomial.X i

private theorem eval_scaledCoordinatePolynomial (i : Fin 3) (a : ℝ) (x : V) :
    MvPolynomial.eval (fun j ↦ x j) (scaledCoordinatePolynomial i a) = x i / a := by
  simp [scaledCoordinatePolynomial, div_eq_inv_mul]

private theorem totalDegree_scaledCoordinatePolynomial (i : Fin 3) (a : ℝ) :
    (scaledCoordinatePolynomial i a).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp

/-- **Theorem 9.4.4** of [conn2000trust], polynomial degrees in the counterexample. For every
$\delta$, every block $l \le 2$ and every index $i$ in it, the Newton function $N_{l,i}$ is the
evaluation of a polynomial in $x_0, x_1, x_2$ of total degree at most $l$. -/
theorem incompleteQuadraticNewton_isPolynomial (δ : ℝ) (l : ℕ) (hl : l ≤ 2)
    (i : Fin (incompleteQuadraticBlockSize l)) :
    ∃ q : MvPolynomial (Fin 3) ℝ, q.totalDegree ≤ l ∧
      ∀ x : V, MvPolynomial.eval (fun j ↦ x j) q = incompleteQuadraticNewton δ l i x := by
  let X := scaledCoordinatePolynomial 0 (δ / 2)
  let Y := scaledCoordinatePolynomial 1 (δ / 2)
  let Z := scaledCoordinatePolynomial 2 (δ ^ 2)
  have hx : X.totalDegree ≤ 1 := totalDegree_scaledCoordinatePolynomial _ _
  have hy : Y.totalDegree ≤ 1 := totalDegree_scaledCoordinatePolynomial _ _
  have hz : Z.totalDegree ≤ 1 := totalDegree_scaledCoordinatePolynomial _ _
  interval_cases l
  · exact ⟨1, by simp, by simp [incompleteQuadraticNewton]⟩
  · fin_cases i
    · exact ⟨X - Z, (MvPolynomial.totalDegree_sub _ _).trans (max_le hx hz), fun x ↦ by
        simp [X, Z, eval_scaledCoordinatePolynomial, incompleteQuadraticNewton]⟩
    · exact ⟨Y - Z, (MvPolynomial.totalDegree_sub _ _).trans (max_le hy hz), fun x ↦ by
        simp [Y, Z, eval_scaledCoordinatePolynomial, incompleteQuadraticNewton]⟩
    · exact ⟨Z, hz, fun x ↦ by
        simp [Z, eval_scaledCoordinatePolynomial, incompleteQuadraticNewton]⟩
  · refine ⟨X * (X - 1) * MvPolynomial.C (1 / 2), ?_, fun x ↦ ?_⟩
    · have hsub : (X - 1).totalDegree ≤ 1 :=
        (MvPolynomial.totalDegree_sub _ _).trans (max_le hx (by simp))
      have hprod : (X * (X - 1)).totalDegree ≤ 2 :=
        (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hx hsub)
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hprod)
    · simp [X, eval_scaledCoordinatePolynomial, incompleteQuadraticNewton, div_eq_mul_inv]

/-- **Equation (9.4.4)** of [conn2000trust], in the counterexample. For $\delta > 0$, the five
points and the Newton polynomials satisfy the Newton conditions up to degree $2$:
$N_{l,i}(y_{l,j}) = 1$ if $i = j$ and $0$ otherwise, and $N_{l,i}(y_{j,k}) = 0$ for every
earlier block $j < l$. -/
theorem incompleteQuadraticFundamental {δ : ℝ} (hδ : 0 < δ) :
    IsNewtonFundamentalFamily (incompleteQuadraticPoints δ) (incompleteQuadraticNewton δ) 2 := by
  have hh : δ / 2 ≠ 0 := (half_pos hδ).ne'
  have hd : δ ^ 2 ≠ 0 := pow_ne_zero _ hδ.ne'
  constructor
  · intro l hl i j
    interval_cases l <;> fin_cases i <;> fin_cases j <;>
      norm_num [incompleteQuadraticPoints, incompleteQuadraticNewton,
        Matrix.cons_val_zero', Matrix.cons_val_succ', hh, hd]
  · intro l hl j hj i k
    interval_cases l <;> interval_cases j <;> fin_cases i <;> fin_cases k <;>
      norm_num [incompleteQuadraticPoints, incompleteQuadraticNewton,
        Matrix.cons_val_zero', Matrix.cons_val_succ', hh, hd]

/-- **Theorem 9.4.4** of [conn2000trust], the five points of the counterexample in block order:
$y_{0,0}$, $y_{1,0}$, $y_{1,1}$, $y_{1,2}$ and $y_{2,0}$. -/
noncomputable def incompleteQuadraticFlatPoints (δ : ℝ) : Fin 5 → V :=
  ![incompleteQuadraticPoints δ 0 0, incompleteQuadraticPoints δ 1 0,
    incompleteQuadraticPoints δ 1 1, incompleteQuadraticPoints δ 1 2,
    incompleteQuadraticPoints δ 2 0]

/-- **Theorem 9.4.4** of [conn2000trust], the five Newton polynomials of the counterexample in block
order: $N_{0,0}$, $N_{1,0}$, $N_{1,1}$, $N_{1,2}$ and $N_{2,0}$. -/
noncomputable def incompleteQuadraticFlatNewton (δ : ℝ) : Fin 5 → V → ℝ :=
  ![incompleteQuadraticNewton δ 0 0, incompleteQuadraticNewton δ 1 0,
    incompleteQuadraticNewton δ 1 1, incompleteQuadraticNewton δ 1 2,
    incompleteQuadraticNewton δ 2 0]

/-- **Theorem 9.4.4** of [conn2000trust], poised data in the counterexample. For $\delta > 0$, the
$5 \times 5$ evaluation matrix $\big(N_j(y_i)\big)$ of the five polynomials at the five points
in block order is invertible.

In the graded Newton basis this matrix is lower triangular with unit diagonal. -/
theorem incompleteQuadraticPoised {δ : ℝ} (hδ : 0 < δ) :
    IsPoised (incompleteQuadraticFlatPoints δ) (incompleteQuadraticFlatNewton δ) := by
  let A := interpolationMatrix (incompleteQuadraticFlatPoints δ) (incompleteQuadraticFlatNewton δ)
  have hh : δ / 2 ≠ 0 := (half_pos hδ).ne'
  have hd : δ ^ 2 ≠ 0 := pow_ne_zero _ hδ.ne'
  have hlo : A.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals norm_num [A, interpolationMatrix, incompleteQuadraticFlatPoints,
      incompleteQuadraticFlatNewton, incompleteQuadraticPoints, incompleteQuadraticNewton,
      Matrix.cons_val_zero', Matrix.cons_val_succ', hh, hd]
  have hdiag (i : Fin 5) : A i i = 1 := by
    fin_cases i <;> norm_num [A, interpolationMatrix, incompleteQuadraticFlatPoints,
      incompleteQuadraticFlatNewton, incompleteQuadraticPoints, incompleteQuadraticNewton,
      Matrix.cons_val_zero', Matrix.cons_val_succ', hh, hd]
  change A.det ≠ 0
  rw [Matrix.det_of_isLowerTriangular A hlo]
  simp [hdiag]

private theorem xyz_mem_closedBall {δ x y z : ℝ} (hδ : 0 ≤ δ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 ≤ δ ^ 2) : xyz x y z ∈ Metric.closedBall (0 : V) δ := by
  rw [Metric.mem_closedBall, dist_zero_right, ← sq_le_sq₀ (norm_nonneg _) hδ,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simpa only [xyz_zero, xyz_one, xyz_two] using h

private theorem point_mem_closedBall {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∀ l ≤ 2, ∀ i, incompleteQuadraticPoints δ l i ∈ Metric.closedBall (0 : V) δ := by
  intro l hl i
  interval_cases l
  · simpa [incompleteQuadraticPoints] using Metric.mem_closedBall_self (x := (0 : V)) hδ.le
  · fin_cases i
    · apply xyz_mem_closedBall hδ.le
      norm_num
      nlinarith only [sq_nonneg δ]
    · apply xyz_mem_closedBall hδ.le
      norm_num
      nlinarith only [sq_nonneg δ]
    · apply xyz_mem_closedBall hδ.le
      have hd : δ ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.2 hδ')]
      nlinarith only [mul_le_mul_of_nonneg_right hd (sq_nonneg δ), sq_nonneg δ]
  · apply xyz_mem_closedBall hδ.le
    norm_num
    nlinarith only [sq_nonneg δ]

/-- **Equations (9.4.18)–(9.4.20)** of [conn2000trust], in the counterexample. Let
$0 < \delta \le 1/2$. Then every interpolation point lies in the closed ball of radius $\delta$
about $0$, the Newton polynomials of blocks $l < 2$ satisfy $|N_{l,i}(y_{l+1,j})| \le 3$ at the
points of the next block, and the polynomial of block $2$ satisfies $|N_{2,i}(x)| \le 3$ on the
ball.

The adjacent-block and last-block bounds hold with the same constant $3$ for every radius. -/
theorem incompleteQuadraticPrintedBounds {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (∀ l ≤ 2, ∀ i, incompleteQuadraticPoints δ l i ∈ Metric.closedBall (0 : V) δ) ∧
    (∀ l < 2, ∀ i j, |incompleteQuadraticNewton δ l i
      (incompleteQuadraticPoints δ (l + 1) j)| ≤ 3) ∧
    ∀ i x, x ∈ Metric.closedBall (0 : V) δ → |incompleteQuadraticNewton δ 2 i x| ≤ 3 := by
  have hh : 0 < δ / 2 := half_pos hδ
  refine ⟨point_mem_closedBall hδ hδ', ?_, ?_⟩
  · intro l hl i j
    interval_cases l <;> fin_cases i <;> fin_cases j <;>
      norm_num [incompleteQuadraticNewton, incompleteQuadraticPoints,
        Matrix.cons_val_zero', Matrix.cons_val_succ', hh.ne']
  · intro i x hx
    have hcoord : |x 0| ≤ δ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0 :
        |x 0| ≤ ‖x‖).trans hx
    let u := x 0 / (δ / 2)
    have hu : |u| ≤ 2 := by
      dsimp [u]
      rw [abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).2 (by linarith only [hcoord])
    have hu' : |u - 1| ≤ 3 := (abs_sub u 1).trans (by norm_num; linarith)
    change |u * (u - 1) / 2| ≤ 3
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact (mul_le_mul hu hu' (abs_nonneg _) (by norm_num)).trans (by norm_num)

private theorem objective_at_test (δ : ℝ) :
    incompleteQuadraticObjective (xyz 0 0 δ) = 0 := by simp [objective_xyz]

private theorem model_at_test {δ : ℝ} (hδ : 0 < δ) :
    newtonInterpolationModel incompleteQuadraticObjective (incompleteQuadraticPoints δ)
      (incompleteQuadraticNewton δ) 2 (xyz 0 0 δ) =
      (1 - Real.cos δ) / δ := by
  have hh : δ / 2 ≠ 0 := (half_pos hδ).ne'
  have hd : δ ^ 2 ≠ 0 := pow_ne_zero _ hδ.ne'
  have hf0 : incompleteQuadraticObjective (0 : V) = 0 := by
    simp [incompleteQuadraticObjective]
  have hf₁ : incompleteQuadraticObjective (xyz (δ / 2) (δ / 2) (δ ^ 2)) =
      1 - Real.cos δ := by
    rw [objective_xyz, sub_self, Real.cos_zero, add_halves]
  norm_num [newtonInterpolationModel, Finset.sum_range_succ, Fin.sum_univ_three,
    newtonInterpolationCoefficient, generalizedFiniteDifference, incompleteQuadraticPoints,
    incompleteQuadraticNewton,
    hf₁, hf0, objective_xyz, Real.cos_neg, hh, hd]
  change (∑ i : Fin 3, incompleteQuadraticObjective
    (![xyz (δ / 2) 0 0, xyz 0 (δ / 2) 0, xyz (δ / 2) (δ / 2) (δ ^ 2)] i) *
    ![-(δ / δ ^ 2), -(δ / δ ^ 2), δ / δ ^ 2] i) = _
  rw [Fin.sum_univ_three]
  norm_num [objective_xyz, Real.cos_neg, hf₁]
  field_simp

private theorem cos_deficit_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    δ ^ 2 / 8 ≤ 1 - Real.cos δ := by
  have hπ := Real.pi_pos
  have habs : |δ| ≤ Real.pi := by rw [abs_of_pos hδ]; linarith [Real.pi_gt_three]
  have hcos := Real.cos_le_one_sub_mul_cos_sq habs
  have hcoef : (1 / 8 : ℝ) ≤ 2 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hπ)).2
    nlinarith only [Real.pi_lt_four, hπ,
      mul_nonneg (sub_nonneg.2 Real.pi_lt_four.le) (show 0 ≤ Real.pi + 4 by positivity)]
  have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg δ)
  linarith only [hcos, h]

/-- **Theorem 9.4.4** of [conn2000trust], counterexample for an incomplete quadratic block. For
every $C > 0$ there is $\delta$ with $0 < \delta \le 1/2$ such that the five points and
polynomials of radius $\delta$ satisfy the Newton conditions (9.4.4), are poised, and satisfy
the bounds (9.4.18)–(9.4.20) with the constant $3$, and there is $x$ with $\|x\| \le \delta$ and
$$C \max\{\delta^2, \delta^3\} < |f(x) - m(x)|,$$
where $m$ is the Newton interpolation model (9.4.9) of $f$ of degree $2$.

**Correction.** The printed theorem bounds the model error by a uniform constant times this
quantity under the adjacent-block and last-block bounds. The example, with five points in
dimension three, a complete affine block and fixed constants for the objective and the geometry,
shows that these bounds are not enough when the quadratic block is incomplete.

At $x = (0, 0, \delta)$ the objective vanishes and the model equals
$(1 - \cos \delta) / \delta \ge \delta / 8$. -/
theorem theorem_9_4_4_incompleteQuadratic_counterexample {C : ℝ} (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      IsNewtonFundamentalFamily (incompleteQuadraticPoints δ) (incompleteQuadraticNewton δ) 2 ∧
      IsPoised (incompleteQuadraticFlatPoints δ) (incompleteQuadraticFlatNewton δ) ∧
      (∀ l ≤ 2, ∀ i, incompleteQuadraticPoints δ l i ∈ Metric.closedBall (0 : V) δ) ∧
      (∀ l < 2, ∀ i j, |incompleteQuadraticNewton δ l i
        (incompleteQuadraticPoints δ (l + 1) j)| ≤ 3) ∧
      (∀ i x, x ∈ Metric.closedBall (0 : V) δ → |incompleteQuadraticNewton δ 2 i x| ≤ 3) ∧
      ∃ x ∈ Metric.closedBall (0 : V) δ,
        C * max (δ ^ 2) (δ ^ 3) <
          |incompleteQuadraticObjective x -
            newtonInterpolationModel incompleteQuadraticObjective (incompleteQuadraticPoints δ)
              (incompleteQuadraticNewton δ) 2 x| := by
  let δ := min (1 / 2) (1 / (16 * (C + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ' : δ ≤ 1 / 2 := min_le_left _ _
  have hCδ : C * δ < 1 / 8 := by
    have h := (le_div_iff₀ (show 0 < 16 * (C + 1) by positivity)).1
      (show δ ≤ 1 / (16 * (C + 1)) from min_le_right _ _)
    nlinarith only [h, hδ]
  have hge := cos_deficit_ge hδ hδ'
  have herror : δ / 8 ≤ (1 - Real.cos δ) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith only [hge]
  have hmax : max (δ ^ 2) (δ ^ 3) = δ ^ 2 := by
    apply max_eq_left
    rw [pow_succ]
    exact mul_le_of_le_one_right (sq_nonneg δ) (by linarith only [hδ'])
  have hp := incompleteQuadraticPoised hδ
  obtain ⟨hball, hadj, htop⟩ := incompleteQuadraticPrintedBounds hδ hδ'
  refine ⟨δ, hδ, hδ', incompleteQuadraticFundamental hδ, hp, hball, hadj, htop,
    xyz 0 0 δ, xyz_mem_closedBall hδ.le (by simp), ?_⟩
  rw [hmax, objective_at_test, model_at_test hδ, zero_sub, abs_neg,
    abs_of_nonneg (le_trans (by positivity : 0 ≤ δ / 8) herror)]
  exact (show C * δ ^ 2 < δ / 8 by
    nlinarith only [mul_lt_mul_of_pos_right hCδ hδ]).trans_le herror

end ConnGouldToint.Chapter09
