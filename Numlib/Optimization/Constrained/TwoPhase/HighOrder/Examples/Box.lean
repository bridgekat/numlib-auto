/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.Sqrt
import Numlib.Optimization.Constrained.TargetResidual
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Plane

/-!
# A two-dimensional problem on a square

This file defines the data of the examples of runs of high-order target-following methods in
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.BoxBadIter` and
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.BoxARqp`. On $\mathbb{R}^2$ the simple
constraint set is the square $X = [-1, 1]^2$, the objectives are $f_a(x) = x_1 - a x_2$, and the
equality constraint is $c(x) = x_1^2/2 \in \mathbb{R}^1$. The first-order Taylor decrement of the
merit function $\mu(\cdot, t) = \frac12 \|r(\cdot, t)\|^2$ is explicit
(`Constrained.TwoPhaseExample.Box.taylorDecrement_one`). It gives an upper bound on the first-order
measure by the Cauchy–Schwarz inequality, and a lower bound along the direction $-e_1$.

## Main definitions

* `Constrained.TwoPhaseExample.Box.square`: the square $[-1, 1]^2$.
* `Constrained.TwoPhaseExample.Box.obj`: the objective $x \mapsto x_1 - a x_2$.
* `Constrained.TwoPhaseExample.Box.con`: the constraint $x \mapsto x_1^2/2$.

## Implementation notes

* The coordinates $x_1$ and $x_2$ of $x \in \mathbb{R}^2$ are `x 0` and `x 1`, and the point
  $(u, v)$ is `Constrained.TwoPhaseExample.pt u v`.
* The constraint takes values in `EuclideanSpace ℝ (Fin 1)`, as a multiple of the unit vector
  `Constrained.TwoPhaseExample.unitVec`.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace Constrained.TwoPhaseExample.Box

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The simple constraint set, the **square** $X = [-1, 1]^2 = \{x \in \mathbb{R}^2 \mid |x_1| \le
1,\ |x_2| \le 1\}$. -/
def square : Set ℝ² := {x | |x 0| ≤ 1 ∧ |x 1| ≤ 1}

/-- The **objective** $f_a(x) = x_1 - a x_2$ on $\mathbb{R}^2$, the linear objective
`Constrained.TwoPhaseExample.linObj` with coefficients $1$ and $-a$. -/
def obj (a : ℝ) : ℝ² → ℝ := linObj 1 (-a)

/-- The **constraint** $c(x) = x_1^2/2$, with values in $\mathbb{R}^1$. -/
noncomputable def con : ℝ² → ℝ¹ := fun x => (x 0 ^ 2 / 2) • unitVec

/-- The objective is $f_a(y) = y_1 - a y_2$. -/
theorem obj_apply (a : ℝ) (y : ℝ²) : obj a y = y 0 - a * y 1 := by simp [obj, linObj]; ring

/-- At the point $(u, v)$ the objective is $f_a(u, v) = u - a v$. -/
theorem obj_pt (a u v : ℝ) : obj a (pt u v) = u - a * v := by simp [obj_apply]

/-- The objective $f_1$ satisfies $f_1(u, v) = u - v$. -/
theorem obj_one_pt (a b : ℝ) : obj 1 (pt a b) = a - b := by rw [obj_pt]; ring

/-- The point $(u, v)$ lies in $X$ if $|u| \le 1$ and $|v| \le 1$. -/
theorem pt_mem_square {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : pt a b ∈ square := by
  simp only [square, mem_ofPred_eq, pt_zero, pt_one]; exact ⟨ha, hb⟩

/-- The norm of the constraint is $\|c(y)\| = y_1^2/2$. -/
theorem norm_con (y : ℝ²) : ‖con y‖ = y 0 ^ 2 / 2 := by
  rw [con, norm_smul_unitVec, abs_of_nonneg (by positivity)]

/-- The derivative of $c$ at $y$ is the linear map $d \mapsto y_1 d_1 e$, where $e$ is the unit
vector of $\mathbb{R}^1$. -/
theorem hasFDerivAt_con (y : ℝ²) :
    HasFDerivAt con ((y 0 • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)).smulRight unitVec)
      y := by
  have h1 : HasFDerivAt (fun x : ℝ² => x 0 ^ 2 / 2)
      (y 0 • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)) y := by
    have := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).pow 2).mul_const (1 / 2 : ℝ)
    convert this using 1
    · funext x; ring
    · ext d; simp; ring
  exact h1.smul_const unitVec

/-- The first-order Taylor decrement of $\mu(\cdot, t)$ at $y$ for the objective $f_a$: for every
$d \in \mathbb{R}^2$,
$$-\nabla_x \mu(y, t)[d] = -\Bigl(\frac{y_1^3}{2} + f_a(y) - t\Bigr) d_1 + a (f_a(y) - t) d_2.$$
-/
theorem taylorDecrement_one (a : ℝ) (y : ℝ²) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (targetMerit (obj a) con t) y).taylorDecrement 1 d =
      -(y 0 ^ 3 / 2 + (obj a y - t)) * d 0 + a * (obj a y - t) * d 1 := by
  rw [taylorDecrement_one_targetMerit (f := obj a) (hasFDerivAt_linObj _ _ y)
    (hasFDerivAt_con y), obj_apply]
  simp [con, unitVec, inner_smul_left, inner_smul_right]
  ring

/-- An upper bound on the first-order measure with radius $1$, by the Cauchy–Schwarz inequality. For
the objective $f_1$ and every set $S \subseteq \mathbb{R}^2$ of displacements with $0 \in S$,
$$\phi^1_{\mu, S, 1}(y, t) \le \sqrt{\Bigl(\frac{y_1^3}{2} + f_1(y) - t\Bigr)^2 + (f_1(y) -
  t)^2}.$$
-/
theorem taylorMeasure_le (y : ℝ²) (t : ℝ) {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit (obj 1) con t) y) 1 1 S ≤
      √((y 0 ^ 3 / 2 + (obj 1 y - t)) ^ 2 + (obj 1 y - t) ^ 2) := by
  have := decrementMeasure_lin_le_sqrt (a := -(y 0 ^ 3 / 2 + (obj 1 y - t))) (b := obj 1 y - t)
    (Δ := (ftaylorSeries ℝ (targetMerit (obj 1) con t) y).taylorDecrement 1)
    (fun d => by rw [taylorDecrement_one, one_mul]) h0
  rwa [neg_sq] at this

/-- A lower bound on the first-order measure with radius $1$, along the displacement $d = -e_1$. For
the objective $f_1$ and every set $S \subseteq \mathbb{R}^2$ of displacements with $-e_1 \in S$,
$$\frac{y_1^3}{2} + f_1(y) - t \le \phi^1_{\mu, S, 1}(y, t).$$
-/
theorem le_taylorMeasure (y : ℝ²) (t : ℝ) {S : Set ℝ²} (hS : EuclideanSpace.single 0 (-1) ∈ S) :
    y 0 ^ 3 / 2 + (obj 1 y - t) ≤
      Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit (obj 1) con t) y) 1 1
        S := by
  have := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (targetMerit (obj 1) con t) y) 1 (δ := 1)
    (d := EuclideanSpace.single 0 (-1)) ⟨by simp, hS⟩
  rw [taylorDecrement_one] at this
  simpa using this

/-- The squared residual is $\|r(y, t)\|^2 = (y_1^2/2)^2 + (f_a(y) - t)^2$. -/
theorem targetResidual_sq (a : ℝ) (y : ℝ²) (t : ℝ) :
    targetResidual (obj a) con t y ^ 2 = (y 0 ^ 2 / 2) ^ 2 + (obj a y - t) ^ 2 := by
  rw [Constrained.targetResidual_sq, norm_con]

/-- The square $X$ is closed. -/
theorem isClosed_square : IsClosed square :=
  (isClosed_le (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous)
    continuous_const).inter
  (isClosed_le (continuous_abs.comp (EuclideanSpace.proj (1 : Fin 2)).continuous)
    continuous_const)

/-- The square $X$ is convex. -/
theorem convex_square : Convex ℝ square := by
  have e : square = (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ) ⁻¹' Icc (-1) 1 ∩
      (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ) ⁻¹' Icc (-1) 1 := by
    ext x; simp [square, abs_le]
  rw [e]
  exact ((convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap).inter
    ((convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap)

/-- The square $X$ lies in the open ball $B(0, 2)$. -/
theorem square_subset_ball : square ⊆ ball 0 2 := by
  intro x hx
  obtain ⟨h0, h1⟩ := hx
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_lt' (by norm_num)]
  simp only [Real.norm_eq_abs, sq_abs]
  have := abs_le.1 h0
  have := abs_le.1 h1
  nlinarith

/-- The constraint $c$ is smooth. -/
theorem contDiff_con : ContDiff ℝ ⊤ con := by
  have h : ContDiff ℝ ⊤ (fun x : ℝ² => x 0 ^ 2 / 2) :=
    ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))).pow 2).div_const 2
  exact h.smul contDiff_const

/-- The objective $f_a$ is smooth. -/
theorem contDiff_obj (a : ℝ) : ContDiff ℝ ⊤ (obj a) := contDiff_linObj _ _

/-- For $|a| \le 1$, the first derivative of $f_a$ satisfies $\|\nabla f_a(y)\| \le 2$ at every $y$.
-/
theorem norm_iteratedFDeriv_obj_le {a : ℝ} (ha : |a| ≤ 1) (y : ℝ²) :
    ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i (obj a) y‖ ≤ 2 := fun i hi =>
  (norm_iteratedFDeriv_linObj_le 1 (-a) y i hi).trans (by rw [abs_one, abs_neg]; linarith)


/-- For $|a| \le 1$, the objective satisfies $-2 \le f_a(x) \le 2$ for every $x \in X$. -/
theorem obj_mem_Icc {a : ℝ} (ha : |a| ≤ 1) {x : ℝ²} (hx : x ∈ square) :
    -2 ≤ obj a x ∧ obj a x ≤ 2 := by
  obtain ⟨h0, h1⟩ := hx
  have h2 : |a * x 1| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg (x 1)]
  have := abs_le.1 h0
  have := abs_le.1 h2
  rw [obj_apply]
  constructor <;> linarith

end Constrained.TwoPhaseExample.Box
