/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import Numlib.Analysis.InnerProductSpace.HalfNormSqDeriv
import Numlib.Optimization.Complexity.SlowExample.TRq
import Numlib.Optimization.Complexity.SlowExample.TRqSaddle
import Numlib.Optimization.Constrained.TargetMeritTaylor
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Plane
import Numlib.Optimization.ModelBased.HighOrder.TRqCall

/-!
# Long runs of TRq on a slowly decaying least-squares function

On $\mathbb{R}^2$, consider the map $c(v) = (1, v_1^{-1/8}, v_2) \in \mathbb{R}^3$ on the closed
half-plane $X = \{v : v_1 \ge 1\}$. Its least-squares function is
$$\nu(v) = \tfrac12 \|c(v)\|^2 = \tfrac12 + \tfrac12 v_1^{-1/4} + \tfrac12 v_2^2.$$
Along the first axis, $\nu$ has the slope $A(v_1) = v_1^{-5/4}/8$ and the curvature
$B(v_1) = 5 v_1^{-9/4}/32$, which both tend to $0$. Across the axis, $\nu$ has unit curvature. This
file builds runs of the trust-region method TRq with a feasible set ([cartis2022evaluation],
Algorithm 12.2.1 with feasible displacements) on $\nu$ that make many successful iterations before
they terminate. The parameters are fixed, and the threshold is $\vartheta = 1$. A run has three
phases:

* a *travel* phase of first-order steps $(1/2, 0)$ along the axis, while the slope exceeds
  $\varepsilon_1$;
* a *shrinking* phase of first-order failures across the axis, where the curvature is $1$, which
  drives the radius down to $y = 2^{-N}$;
* a *slow* phase of second-order steps $(y, 0)$ along the axis, each of which decreases $\nu$ by
  about $Ay$, as long as $\varepsilon_2 y < 4A$.

With $\varepsilon_1 = 2^{-10M}/2$ and $\varepsilon_2 = 2^{-5M}/2$, the run makes at least
$2^{22M} - 2^{18M} - 2^{10M}$ successful iterations before it can terminate. The file also treats
the variant $c_2(v) = (v_1^{-1/8}, v_2)$, whose target merit functions differ from $\nu$ by
constants on $X$, and the bounds on the derivatives of $t \mapsto t^{-1/8}$ that give the smoothness
of $c$ and $c_2$.

## Main definitions

* `Constrained.TwoPhaseExample.SlowDecay.con`, `Constrained.TwoPhaseExample.SlowDecay.con₂`,
  `Constrained.TwoPhaseExample.SlowDecay.halfPlane` and
  `Constrained.TwoPhaseExample.SlowDecay.openHalfPlane`: the constraints $c$ and $c_2$, the feasible
  set $X$ and the open set $X_0 = \{v : v_1 > 1/2\}$.
* `Constrained.TwoPhaseExample.SlowDecay.slope` and `Constrained.TwoPhaseExample.SlowDecay.curv`:
  the slope $A$ and the curvature $B$ of $\nu$ along the axis.
* `Constrained.TwoPhaseExample.SlowDecay.params`: the trust-region parameters.
* `Constrained.TwoPhaseExample.SlowDecay.tol`: the tolerances $\varepsilon_1 = 2^{-10M}$,
  $\varepsilon_2 = 2^{-5M}$, and $\varepsilon_j = 1$ otherwise.

## Main results

* `Constrained.TwoPhaseExample.SlowDecay.taylorDecrement_one` and
  `Constrained.TwoPhaseExample.SlowDecay.taylorDecrement_two`: the first- and second-order Taylor
  decrements of $\nu$.
* `Constrained.TwoPhaseExample.SlowDecay.exists_run_travel`,
  `Constrained.TwoPhaseExample.SlowDecay.exists_run_shrink` and
  `Constrained.TwoPhaseExample.SlowDecay.exists_run_axis`: the three phases, each followed by an
  arbitrary run.
* `Constrained.TwoPhaseExample.SlowDecay.exists_long_run`: a run that makes at least
  $2^{22M} - 2^{18M} - 2^{10M}$ successful iterations before it can terminate.

## Implementation notes

* A point $v \in \mathbb{R}^2$ is an element of `EuclideanSpace ℝ (Fin 2)`, with $v_1$ = `v 0` and
  $v_2$ = `v 1`. The point $(a, b)$ is `Constrained.TwoPhaseExample.pt a b`.
* Powers with real exponents are Mathlib's `Real.rpow`. The formulas hold on $v_1 > 0$, and $\nu$ is
  `Constrained.TwoPhaseExample.SlowDecay.nu` there.
-/

open Set Metric Filter
open scoped Nat ContDiff Topology
open Optimization (halfSq iteratedDeriv_halfSq_one iteratedDeriv_halfSq_two contDiff_halfSq
  contDiff_halfSq_comp_apply)

namespace Constrained.TwoPhaseExample.SlowDecay

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ### The function $t^{-1/4}$ -/

section OneDim

/-- The function $p(t) = t^{-1/4}$. -/
noncomputable def quarterPow : ℝ → ℝ := fun t => t ^ (-(1 / 4 : ℝ))

/-- The $k$-th derivative of $p(t) = t^{-1/4}$ is
$$p^{(k)}(t) = \left(-\tfrac14\right)\left(-\tfrac14 - 1\right) \cdots \left(-\tfrac14 - k +
  1\right) t^{-1/4 - k},$$
where the product is the descending Pochhammer symbol at $-1/4$. -/
theorem iteratedDeriv_quarterPow (k : ℕ) (t : ℝ) :
    iteratedDeriv k quarterPow t =
      (descPochhammer ℝ k).eval (-(1 / 4 : ℝ)) * t ^ (-(1 / 4 : ℝ) - k) := by
  rw [iteratedDeriv_eq_iterate]; exact Real.iter_deriv_rpow_const _ _ _

/-- The first derivative of $p(t) = t^{-1/4}$ is $p'(t) = -t^{-5/4}/4$. -/
theorem iteratedDeriv_one_quarterPow (t : ℝ) :
    iteratedDeriv 1 quarterPow t = -(t ^ (-(5 / 4 : ℝ)) / 4) := by
  rw [iteratedDeriv_quarterPow]
  norm_num
  ring

/-- The second derivative of $p(t) = t^{-1/4}$ is $p''(t) = 5 t^{-9/4}/16$. -/
theorem iteratedDeriv_two_quarterPow (t : ℝ) :
    iteratedDeriv 2 quarterPow t = 5 * t ^ (-(9 / 4 : ℝ)) / 16 := by
  rw [iteratedDeriv_quarterPow]
  norm_num [descPochhammer_succ_right]
  ring

/-- The function $p(t) = t^{-1/4}$ is smooth on $(0, \infty)$. -/
theorem contDiffOn_quarterPow : ContDiffOn ℝ ∞ quarterPow (Ioi 0) := fun _ hx =>
  (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt

end OneDim

/-! ### The constraint and its least-squares function -/

section Problem

/-- The function $g(t) = t^{-1/8}$, the second component of the constraint. -/
noncomputable def eighthPow : ℝ → ℝ := fun t => t ^ (-(1 / 8 : ℝ))

/-- For $t \ge 0$, $g(t)^2 = p(t)$, that is, $(t^{-1/8})^2 = t^{-1/4}$. -/
theorem eighthPow_sq {t : ℝ} (ht : 0 ≤ t) : eighthPow t ^ 2 = quarterPow t := by
  rw [eighthPow, quarterPow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/-- The constraint $c : \mathbb{R}^2 \to \mathbb{R}^3$, $c(v) = (1, v_1^{-1/8}, v_2)$. -/
noncomputable def con : ℝ² → ℝ³ := fun v => WithLp.toLp 2 ![1, eighthPow (v 0), v 1]

/-- For every $v \in \mathbb{R}^2$, $\|c(v)\|^2 = 1 + g(v_1)^2 + v_2^2$. -/
theorem norm_con_sq (v : ℝ²) : ‖con v‖ ^ 2 = 1 + eighthPow (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [con, sq_abs]

/-- For every $v \in \mathbb{R}^2$, $\|c(v)\| \ge 1$. -/
theorem one_le_norm_con (v : ℝ²) : 1 ≤ ‖con v‖ := by
  have h := norm_con_sq v
  have : 1 ≤ ‖con v‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg (eighthPow (v 0)), sq_nonneg (v 1)]
  nlinarith [norm_nonneg (con v)]

/-- The infeasibility measure $\nu = \tfrac12 \|c\|^2$, written in a form that is smooth near the
half-plane $v_1 > 0$:
$$\nu(w) = \tfrac12 + \tfrac12 p(w_1) + \tfrac12 w_2^2.$$
-/
noncomputable def nu : ℝ² → ℝ := fun w => 1 / 2 + quarterPow (w 0) / 2 + halfSq (w 1)

/-- For $v_1 \ge 0$, $\tfrac12 \|c(v)\|^2 = \nu(v)$. -/
theorem halfSqNorm_con_eq {v : ℝ²} (hv : 0 ≤ v 0) : halfSqNorm con v = nu v := by
  rw [halfSqNorm_apply, norm_con_sq, eighthPow_sq hv, nu, halfSq]
  ring

/-- For $a \ge 0$ and $b \in \mathbb{R}$,
$$\tfrac12 \|c(a, b)\|^2 = \tfrac12 + \tfrac12 a^{-1/4} + \tfrac12 b^2.$$
-/
theorem halfSqNorm_con_pt {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    halfSqNorm con (pt a b) = 1 / 2 + a ^ (-(1 / 4 : ℝ)) / 2 + b ^ 2 / 2 := by
  rw [halfSqNorm_con_eq (by simpa using ha)]
  simp [nu, quarterPow, halfSq]

/-- The functions $\nu$ and $\tfrac12 \|c\|^2$ agree on a neighbourhood of every point $v$ with
$v_1 > 0$. -/
theorem halfSqNorm_con_eventuallyEq {v : ℝ²} (hv : 0 < v 0) : halfSqNorm con =ᶠ[𝓝 v] nu := by
  have hU : IsOpen {w : ℝ² | 0 < w 0} :=
    isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  filter_upwards [hU.mem_nhds hv] with w hw
  exact halfSqNorm_con_eq (le_of_lt hw)

/-- At a point $v$ with $v_1 > 0$, the Taylor series of $\tfrac12 \|c\|^2$ is that of $\nu$. -/
theorem ftaylorSeries_halfSqNorm_con {v : ℝ²} (hv : 0 < v 0) :
    ftaylorSeries ℝ (halfSqNorm con) v = ftaylorSeries ℝ nu v :=
  ((halfSqNorm_con_eventuallyEq hv).ftaylorSeries ℝ).eq_of_nhds

/-- The function $\nu$ is $C^n$ near every point $v$ with $v_1 > 0$, for every $n \in \mathbb{N}$.
-/
theorem contDiffAt_nu {v : ℝ²} (hv : 0 < v 0) (n : ℕ) : ContDiffAt ℝ n nu v := by
  have h2 : ContDiffAt ℝ n (fun w : ℝ² => quarterPow (w 0) / 2) v :=
    ((Real.contDiffAt_rpow_const_of_ne hv.ne').comp v
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).contDiff.contDiffAt).div_const 2
  have h3 : ContDiffAt ℝ n (fun w : ℝ² => halfSq (w 1)) v :=
    (contDiff_halfSq_comp_apply 1).contDiffAt.of_le (by exact_mod_cast le_top)
  exact (contDiffAt_const.add h2).add h3

/-- Let $v_1 > 0$ and $k \ge 1$. The $k$-th derivative of $\nu$ at $v$ in the direction
$s \in \mathbb{R}^2$ is
$$\nabla^k \nu(v)[s]^k = \tfrac12 p^{(k)}(v_1)\, s_1^k + h^{(k)}(v_2)\, s_2^k, \qquad h(t) =
  t^2/2.$$
-/
theorem iteratedFDeriv_nu_apply {v : ℝ²} (hv : 0 < v 0) {k : ℕ} (hk : k ≠ 0) (s : ℝ²) :
    iteratedFDeriv ℝ k nu v (fun _ => s) =
      iteratedDeriv k quarterPow (v 0) / 2 * (s 0) ^ k + iteratedDeriv k halfSq (v 1) * (s 1) ^ k
        := by
  have e : nu =
      ((fun _ => (1 / 2 : ℝ)) + fun w : ℝ² => quarterPow (w 0) / 2) + fun w => halfSq (w 1) := by
    funext w; rfl
  have h1 : ContDiffAt ℝ k (fun _ : ℝ² => (1 / 2 : ℝ)) v := contDiffAt_const
  have h2 : ContDiffAt ℝ k (fun w : ℝ² => quarterPow (w 0) / 2) v :=
    ((Real.contDiffAt_rpow_const_of_ne hv.ne').comp v
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).contDiff.contDiffAt).div_const 2
  have h3 : ContDiffAt ℝ k (fun w : ℝ² => halfSq (w 1)) v :=
    (contDiff_halfSq_comp_apply 1).contDiffAt.of_le (by exact_mod_cast le_top)
  have h12 : ContDiffAt ℝ k ((fun _ : ℝ² => (1 / 2 : ℝ)) + fun w : ℝ² => quarterPow (w 0) / 2) v :=
    h1.add h2
  rw [e, iteratedFDeriv_add_apply h12 h3, iteratedFDeriv_add_apply h1 h2,
    iteratedFDeriv_const_of_ne hk]
  simp only [Pi.zero_apply, add_apply, zero_add]
  have hP : ContDiffAt ℝ k (fun t => quarterPow t / 2) (v 0) :=
    ((contDiffOn_quarterPow.div_const 2).contDiffAt (isOpen_Ioi.mem_nhds hv)).of_le
      (by exact_mod_cast le_top)
  rw [ContDiffAt.iteratedFDeriv_comp_coord_apply_const 0 hP s,
    iteratedDeriv_div_const, ContDiffAt.iteratedFDeriv_comp_coord_apply_const 1
      (contDiff_halfSq.contDiffAt.of_le (by exact_mod_cast le_top)) s]

/-- The slope of $\nu$ along the first axis, $A(t) = t^{-5/4}/8$. This is $|\partial_1 \nu|$ at a
point with $v_1 = t > 0$. -/
noncomputable def slope (t : ℝ) : ℝ := t ^ (-(5 / 4 : ℝ)) / 8

/-- The curvature of $\nu$ along the first axis, $B(t) = 5 t^{-9/4}/32$. This is $\partial_1^2 \nu$
at a point with $v_1 = t > 0$. -/
noncomputable def curv (t : ℝ) : ℝ := 5 * t ^ (-(9 / 4 : ℝ)) / 32

/-- The first-order Taylor decrement of $\nu = \tfrac12 \|c\|^2$: for $v_1 > 0$ and
$s \in \mathbb{R}^2$,
$$\Delta T_1(v, s) = A(v_1)\, s_1 - v_2 s_2.$$
-/
theorem taylorDecrement_one {v : ℝ²} (hv : 0 < v 0) (s : ℝ²) :
    (ftaylorSeries ℝ (halfSqNorm con) v).taylorDecrement 1 s = slope (v 0) * s 0 - v 1 * s 1 := by
  rw [ftaylorSeries_halfSqNorm_con hv, FormalMultilinearSeries.taylorDecrement_one_apply]
  change -(iteratedFDeriv ℝ 1 nu v (fun _ => s)) = _
  rw [iteratedFDeriv_nu_apply hv one_ne_zero, iteratedDeriv_one_quarterPow,
    iteratedDeriv_halfSq_one, slope]
  ring

/-- The second-order Taylor decrement of $\nu = \tfrac12 \|c\|^2$: for $v_1 > 0$ and
$s \in \mathbb{R}^2$,
$$\Delta T_2(v, s) = A(v_1)\, s_1 - v_2 s_2 - \tfrac12 \bigl(B(v_1)\, s_1^2 + s_2^2\bigr).$$
-/
theorem taylorDecrement_two {v : ℝ²} (hv : 0 < v 0) (s : ℝ²) :
    (ftaylorSeries ℝ (halfSqNorm con) v).taylorDecrement 2 s =
      slope (v 0) * s 0 - v 1 * s 1 - (curv (v 0) * (s 0) ^ 2 + (s 1) ^ 2) / 2 := by
  rw [ftaylorSeries_halfSqNorm_con hv, FormalMultilinearSeries.taylorDecrement_two]
  change -(iteratedFDeriv ℝ 1 nu v (fun _ => s)) -
    2⁻¹ * iteratedFDeriv ℝ 2 nu v (fun _ => s) = _
  rw [iteratedFDeriv_nu_apply hv one_ne_zero, iteratedFDeriv_nu_apply hv two_ne_zero,
    iteratedDeriv_one_quarterPow, iteratedDeriv_two_quarterPow, iteratedDeriv_halfSq_one,
    iteratedDeriv_halfSq_two, slope, curv]
  ring

end Problem

/-! ### Properties of the slope and the curvature -/

section Scalar

/-- For $t > 0$, the slope is positive: $A(t) > 0$. -/
theorem slope_pos {t : ℝ} (ht : 0 < t) : 0 < slope t := by
  unfold slope; positivity

/-- For $t > 0$, the curvature is nonnegative: $B(t) \ge 0$. -/
theorem curv_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ curv t := by
  unfold curv; positivity

/-- The slope $A$ is nonincreasing on $(0, \infty)$: $A(t) \le A(s)$ for $0 < s \le t$. -/
theorem slope_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : slope t ≤ slope s := by
  unfold slope
  have := Real.rpow_le_rpow_of_nonpos hs hst (by norm_num : (-(5 / 4 : ℝ)) ≤ 0)
  linarith

/-- For $t > 0$, $B(t) = \tfrac54 A(t)/t$. -/
theorem curv_eq {t : ℝ} (ht : 0 < t) : curv t = 5 / 4 * slope t / t := by
  unfold curv slope
  have : t ^ (-(9 / 4 : ℝ)) = t ^ (-(5 / 4 : ℝ)) * t ^ (-1 : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  rw [this, Real.rpow_neg_one]
  field_simp
  ring

/-- For $t \ge 2$ and $\delta \le 1$, $B(t)\,\delta \le A(t)$. -/
theorem curv_mul_le {t δ : ℝ} (ht : 2 ≤ t) (hδ1 : δ ≤ 1) :
    curv t * δ ≤ slope t := by
  have ht0 : 0 < t := by linarith
  rw [curv_eq ht0, div_mul_eq_mul_div, div_le_iff₀ ht0]
  have := slope_pos ht0
  nlinarith

/-- For $t \ge 2$ and $0 \le h \le 1/2$, $A(t) \le 2 A(t + h)$. -/
theorem slope_le_two_mul {t h : ℝ} (ht : 2 ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2) :
    slope t ≤ 2 * slope (t + h) := by
  have ht0 : 0 < t := by linarith
  have h1 : slope (5 / 4 * t) ≤ slope (t + h) := slope_anti (by linarith) (by linarith)
  have h2 : slope (5 / 4 * t) = (5 / 4 : ℝ) ^ (-(5 / 4 : ℝ)) * slope t := by
    unfold slope
    rw [Real.mul_rpow (by norm_num) ht0.le]
    ring
  have h3 : (16 / 25 : ℝ) ≤ (5 / 4 : ℝ) ^ (-(5 / 4 : ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5 / 4)
      (by norm_num : (-2 : ℝ) ≤ -(5 / 4 : ℝ))
    have e : (5 / 4 : ℝ) ^ (-2 : ℝ) = 16 / 25 := by
      rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    linarith
  have := slope_pos ht0
  nlinarith

/-- For $t > 0$, the derivative of $x \mapsto x^{-1/4}$ at $t$ is $-2A(t)$. -/
theorem hasDerivAt_quarterPow {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (-(2 * slope t)) t := by
  have := Real.hasDerivAt_rpow_const (p := -(1 / 4 : ℝ)) (Or.inl ht.ne')
  convert this using 1
  unfold slope
  norm_num
  ring

/-- **The decrease along the first axis.** For $t \ge 2$ and $0 \le h \le 1/2$,
$$\tfrac12 t^{-1/4} - \tfrac12 (t + h)^{-1/4} \ge \tfrac12 A(t)\, h.$$
-/
theorem slope_mul_le_sub {t h : ℝ} (ht : 2 ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2) :
    slope t * h / 2 ≤ t ^ (-(1 / 4 : ℝ)) / 2 - (t + h) ^ (-(1 / 4 : ℝ)) / 2 := by
  have ht0 : 0 < t := by linarith
  rcases hh0.eq_or_lt with rfl | hpos
  · simp
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (-(1 / 4 : ℝ)))
    (fun x => -(2 * slope x)) (by linarith : t < t + h)
    (fun x hx =>
      (Real.continuousAt_rpow_const x _ (Or.inl (by linarith [hx.1]))).continuousWithinAt)
    (fun x hx => hasDerivAt_quarterPow (by linarith [hx.1]))
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have hA : slope (t + h) ≤ slope ξ := slope_anti hξ0 hξ.2.le
  have hA2 := slope_le_two_mul ht hh0 hh
  simp only [add_sub_cancel_left] at hξd
  rw [eq_div_iff hpos.ne'] at hξd
  nlinarith

end Scalar

/-! ### Trust-region iterations -/

section Iterations

/-- The trust-region parameters of the example: $\Delta_0 = \Delta_{\max} = 1$, $\eta_1 = 1/4$,
$\eta_2 = 3/4$, $\gamma_1 = 1/4$, $\gamma_2 = 1/2$, $\gamma_3 = 2$ and $\varsigma = 1/4$. -/
noncomputable def params : Optimization.TRqParams where
  Δ₀ := 1
  η₁ := 1 / 4
  η₂ := 3 / 4
  γ₁ := 1 / 4
  γ₂ := 1 / 2
  γ₃ := 2
  Δ₀_pos := one_pos
  η₁_pos := by norm_num
  η₁_le_η₂ := by norm_num
  η₂_lt_one := by norm_num
  γ₁_pos := by norm_num
  γ₁_le_γ₂ := by norm_num
  γ₂_lt_one := by norm_num
  one_le_γ₃ := by norm_num
  Δmax := 1
  ς := 1 / 4
  Δ₀_le_Δmax := le_rfl
  ς_pos := by norm_num
  ς_le_one := by norm_num

/-- The feasible set, the closed half-plane $X = \{v \in \mathbb{R}^2 : v_1 \ge 1\}$. -/
def halfPlane : Set ℝ² := {v | 1 ≤ v 0}

/-- The open half-plane $X_0 = \{v \in \mathbb{R}^2 : v_1 > 1/2\}$, which contains $X$ and is the
open set of the smoothness assumptions. -/
def openHalfPlane : Set ℝ² := {v | 1 / 2 < v 0}

/-- If $a + c \ge 1$, then $(a, b) + (c, d) \in X$. -/
theorem pt_add_pt_mem {a b c d : ℝ} (h : 1 ≤ a + c) : pt a b + pt c d ∈ halfPlane := by
  rw [pt_add_pt]; exact h

/-- With the parameters of the example, a successful iteration (ratio $\rho \ge \eta_1$, with
$x' = x + s$) keeps the radius: $\Delta' = \Delta$. -/
theorem trAcceptance_succ {E : Type*} [NormedAddCommGroup E] {ρ Δ : ℝ} {x s x' : E}
    (hΔ : 0 ≤ Δ) (hρ : params.η₁ ≤ ρ) (hx : x' = x + s) :
    Optimization.TRAcceptance params.toTRParams ρ x s x' Δ Δ := by
  refine ⟨by rw [ite_eq_left hρ]; exact hx, ⟨fun _ => ⟨le_rfl, ?_⟩, fun _ _ => ⟨?_, le_rfl⟩,
    fun h => absurd h (not_lt.2 hρ)⟩⟩
  · change Δ ≤ 2 * Δ; linarith
  · change 1 / 2 * Δ ≤ Δ; linarith

/-- With the parameters of the example, an unsuccessful iteration (ratio $\rho < \eta_1$) keeps the
iterate and halves the radius: $\Delta' = \Delta/2$. -/
theorem trAcceptance_unsucc {E : Type*} [NormedAddCommGroup E] {ρ Δ : ℝ} {x s : E}
    (hΔ : 0 ≤ Δ) (hρ : ρ < params.η₁) :
    Optimization.TRAcceptance params.toTRParams ρ x s x Δ (Δ / 2) := by
  have hρ' : ρ < 1 / 4 := hρ
  refine ⟨(ite_eq_right (not_le.2 hρ)).symm, ⟨fun h => absurd h (not_le.2 (hρ'.trans (by
    norm_num : (1 : ℝ) / 4 < 3 / 4))), fun h => absurd h (not_le.2 hρ), fun _ => ⟨?_, ?_⟩⟩⟩
  · change 1 / 4 * Δ ≤ Δ / 2; linarith
  · change Δ / 2 ≤ 1 / 2 * Δ; linarith

/-- If the predicted decrease is positive and the actual decrease $F(x) - F(x + s)$ is at least a
quarter of it, then the reduction ratio is at least $\eta_1 = 1/4$. -/
theorem η₁_le_reductionRatio {E : Type*} [NormedAddCommGroup E] {F : E → ℝ} {x s : E}
    {pred : ℝ} (hp : 0 < pred)
    (h : pred / 4 ≤ F x - F (x + s)) :
    params.η₁ ≤ Optimization.reductionRatio F x s pred := by
  change (1 / 4 : ℝ) ≤ _
  rw [Optimization.reductionRatio_def, le_div_iff₀ hp]; linarith

/-- If the predicted decrease is positive and the actual decrease $F(x) - F(x + s)$ is less than a
quarter of it, then the reduction ratio is less than $\eta_1 = 1/4$. -/
theorem reductionRatio_lt_η₁ {E : Type*} [NormedAddCommGroup E] {F : E → ℝ} {x s : E}
    {pred : ℝ} (hp : 0 < pred)
    (h : F x - F (x + s) < pred / 4) :
    Optimization.reductionRatio F x s pred < params.η₁ := by
  change _ < (1 / 4 : ℝ)
  rw [Optimization.reductionRatio_def, div_lt_iff₀ hp]; linarith

/-- At $v = (a, b)$ with $a > 0$, for every $d$ with $\|d\| \le \delta$,
$\Delta T_1(v, d) \le (A(a) + |b|)\,\delta$. -/
theorem taylorDecrement_one_le {a b δ : ℝ} (ha : 0 < a) {d : ℝ²} (hd : ‖d‖ ≤ δ) :
    (ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement 1 d ≤
      (slope a + |b|) * δ := by
  rw [taylorDecrement_one (by simpa using ha)]
  simp only [pt_zero, pt_one]
  have h0 := (EuclideanSpace.abs_apply_le_norm d 0).trans hd
  have h1 := (EuclideanSpace.abs_apply_le_norm d 1).trans hd
  have hA := (slope_pos ha).le
  have e0 : slope a * d 0 ≤ slope a * δ :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hA).trans (mul_le_mul_of_nonneg_left h0 hA)
  have e1 : -(b * d 1) ≤ |b| * δ := by
    have := neg_abs_le (b * d 1)
    rw [abs_mul] at this
    nlinarith [abs_nonneg b]
  nlinarith

/-- At $v = (a, b)$ with $a > 0$, $\Delta T_2(v, d) \le \Delta T_1(v, d)$ for every $d$, because the
Hessian of $\nu$ is positive semidefinite. -/
theorem taylorDecrement_two_le_one {a b : ℝ} (ha : 0 < a) (d : ℝ²) :
    (ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement 1 d := by
  rw [taylorDecrement_one (by simpa using ha), taylorDecrement_two (by simpa using ha)]
  have := curv_nonneg (t := (pt a b) 0) (by simpa using ha)
  nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

/-- At $v = (a, b)$ with $a > 0$, for every $d$ with $\|d\| \le \delta$,
$\Delta T_2(v, d) \le A(a)\,\delta + b^2/2$. -/
theorem taylorDecrement_two_le {a b δ : ℝ} (ha : 0 < a) {d : ℝ²} (hd : ‖d‖ ≤ δ) :
    (ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement 2 d ≤
      slope a * δ + b ^ 2 / 2 := by
  rw [taylorDecrement_two (by simpa using ha)]
  simp only [pt_zero, pt_one]
  have h0 := (EuclideanSpace.abs_apply_le_norm d 0).trans hd
  have hA := (slope_pos ha).le
  have hB := curv_nonneg ha
  have e0 : slope a * d 0 ≤ slope a * δ :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hA).trans (mul_le_mul_of_nonneg_left h0 hA)
  nlinarith [sq_nonneg (d 1 + b), mul_nonneg hB (sq_nonneg (d 0))]

/-- The bound behind the Step-1 displacements. Let $a \ge 1$, $\delta \ge 0$, and let $d$ satisfy
$\|d\| \le \delta$ and $a + d_1 \ge 1$. If $\Delta T_j((a, b), e) \le B$ for every $e$ with
$\|e\| \le \delta$, and $\Delta T_j((a, b), d) \ge B/4$, then $d$ is an approximate optimality
displacement of order $j$ with radius $\delta$ and fraction $\varsigma = 1/4$ for the feasible
displacements of $X$ (`Optimization.IsApproxMeasureStep`). -/
theorem isApproxMeasureStep_of_le {a b δ B : ℝ} (ha : 1 ≤ a) (hδ : 0 ≤ δ) {j : ℕ} {d : ℝ²}
    (hdδ : ‖d‖ ≤ δ) (hdX : 1 ≤ a + d 0)
    (hB : ∀ e : ℝ², ‖e‖ ≤ δ →
      (ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement j e ≤ B)
    (hd : B / 4 ≤ (ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement j d) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement j) δ
      {e | pt a b + e ∈ halfPlane} params.ς d := by
  have hd' : d = pt (d 0) (d 1) := by ext i; fin_cases i <;> rfl
  refine ⟨⟨mem_closedBall_zero_iff.2 hdδ, ?_⟩, ?_⟩
  · change pt a b + d ∈ halfPlane
    rw [hd']; exact pt_add_pt_mem hdX
  · have hm : Optimization.decrementMeasure
        ((ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement j) δ
        {e | pt a b + e ∈ halfPlane} ≤ B :=
      Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, by
        change pt a b + 0 ∈ halfPlane
        rw [add_zero]; exact ha⟩ fun e he => hB e (mem_closedBall_zero_iff.1 he.1)
    change 1 / 4 * _ ≤ _
    linarith

end Iterations

/-! ### Steps of TRq -/

section Steps

/-- For $a > 0$, $\Delta T_1((a, b), (\sigma, \tau)) = A(a)\,\sigma - b\tau$. -/
theorem taylorDecrement_one_pt {a : ℝ} (ha : 0 < a) (b σ τ : ℝ) :
    (ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement 1 (pt σ τ) =
      slope a * σ - b * τ := by
  rw [taylorDecrement_one (by simpa using ha)]; simp

/-- For $a > 0$, $\Delta T_2((a, b), (\sigma, \tau)) = A(a)\,\sigma - b\tau - \tfrac12
(B(a)\,\sigma^2 + \tau^2)$. -/
theorem taylorDecrement_two_pt {a : ℝ} (ha : 0 < a) (b σ τ : ℝ) :
    (ftaylorSeries ℝ (halfSqNorm con) (pt a b)).taylorDecrement 2 (pt σ τ) =
      slope a * σ - b * τ - (curv a * σ ^ 2 + τ ^ 2) / 2 := by
  rw [taylorDecrement_two (by simpa using ha)]; simp

/-- For the orders that the runs do not use: there is a choice $W(y, \delta, j)$ of an approximate
optimality displacement of order $j$ with radius $\delta$ at every $y \in X$ and every
$\delta \ge 0$. -/
theorem exists_witness : ∃ W : ℝ² → ℝ → ℕ → ℝ², ∀ (y : ℝ²) (δ : ℝ) (j : ℕ),
    y ∈ halfPlane → 0 ≤ δ → Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) y).taylorDecrement j) δ {e | y + e ∈ halfPlane}
        params.ς (W y δ j) := by
  have hX : IsClosed halfPlane :=
    isClosed_le continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  have hW : ∀ (y : ℝ²) (δ : ℝ) (j : ℕ), ∃ w : ℝ², y ∈ halfPlane → 0 ≤ δ →
      Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (halfSqNorm con) y).taylorDecrement j) δ
        {e | y + e ∈ halfPlane} params.ς w := by
    intro y δ j
    by_cases h : y ∈ halfPlane ∧ 0 ≤ δ
    · obtain ⟨w, hw⟩ := Optimization.exists_isApproxMeasureStep_taylorDecrement
        (ftaylorSeries ℝ (halfSqNorm con) y) j (hX.preimage (continuous_const.add continuous_id))
        (by change y + 0 ∈ halfPlane; rw [add_zero]; exact h.1) h.2 params.ς_le_one
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose W hW using hW
  exact ⟨W, hW⟩

/-- On the axis, at $(a, 0)$ with $a \ge 2$ and for $\delta \ge 0$, the displacement $(\delta/4, 0)$
is an approximate first-order optimality displacement with radius $\delta$. -/
theorem isApproxMeasureStep_axis_one {a δ : ℝ} (ha : 2 ≤ a) (hδ : 0 ≤ δ) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) (pt a 0)).taylorDecrement 1) δ
      {e | pt a 0 + e ∈ halfPlane} params.ς (pt (δ / 4) 0) := by
  have ha0 : 0 < a := by linarith
  refine isApproxMeasureStep_of_le (B := slope a * δ) (by linarith) hδ
    ((norm_pt_le_add _ _).trans (by rw [abs_of_nonneg (by linarith), abs_zero]; linarith))
    (by simp; linarith) (fun e he => (taylorDecrement_one_le ha0 he).trans_eq (by simp)) ?_
  rw [taylorDecrement_one_pt ha0]; ring_nf; rfl

/-- On the axis, at $(a, 0)$ with $a \ge 2$ and for $0 \le \delta \le 1$, the displacement
$(\delta, 0)$ is an approximate second-order optimality displacement with radius $\delta$. -/
theorem isApproxMeasureStep_axis_two {a δ : ℝ} (ha : 2 ≤ a) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) (pt a 0)).taylorDecrement 2) δ
      {e | pt a 0 + e ∈ halfPlane} params.ς (pt δ 0) := by
  have ha0 : 0 < a := by linarith
  refine isApproxMeasureStep_of_le (B := slope a * δ) (by linarith) hδ
    ((norm_pt_le_add _ _).trans (by rw [abs_of_nonneg hδ, abs_zero, add_zero]))
    (by simp; linarith) (fun e he => ((taylorDecrement_two_le_one ha0 e).trans
      (taylorDecrement_one_le ha0 he)).trans_eq (by simp)) ?_
  rw [taylorDecrement_two_pt ha0]
  have := curv_mul_le ha hδ1
  have := (slope_pos ha0).le
  nlinarith

/-- At $(a, y)$ with $a \ge 2$, $y \ge 0$ and $A(a) \le y$, and for $\delta \ge 0$, the displacement
$(0, -\delta)$ is an approximate first-order optimality displacement with radius $\delta$. -/
theorem isApproxMeasureStep_shrink_one {a y δ : ℝ} (ha : 2 ≤ a) (hy : 0 ≤ y) (hAy : slope a ≤ y)
    (hδ : 0 ≤ δ) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) (pt a y)).taylorDecrement 1) δ
      {e | pt a y + e ∈ halfPlane} params.ς (pt 0 (-δ)) := by
  have ha0 : 0 < a := by linarith
  refine isApproxMeasureStep_of_le (B := (slope a + |y|) * δ) (by linarith) hδ
    ((norm_pt_le_add _ _).trans (by rw [abs_zero, abs_neg, abs_of_nonneg hδ, zero_add]))
    (by simp; linarith) (fun e he => taylorDecrement_one_le ha0 he) ?_
  rw [taylorDecrement_one_pt ha0, abs_of_nonneg hy]
  nlinarith

/-- At $(a, y)$ with $a \ge 2$ and $0 \le y \le \delta \le 1$, the displacement
$(\delta/2, -\min(y, \delta/2))$ is an approximate second-order optimality displacement with
radius $\delta$. -/
theorem isApproxMeasureStep_shrink_two {a y δ : ℝ} (ha : 2 ≤ a) (hy : 0 ≤ y) (hyδ : y ≤ δ)
    (hδ1 : δ ≤ 1) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) (pt a y)).taylorDecrement 2) δ
      {e | pt a y + e ∈ halfPlane} params.ς (pt (δ / 2) (-min y (δ / 2))) := by
  have ha0 : 0 < a := by linarith
  have hδ : 0 ≤ δ := hy.trans hyδ
  have hb0 : 0 ≤ min y (δ / 2) := le_min hy (by linarith)
  have hb1 : min y (δ / 2) ≤ y := min_le_left _ _
  have hb2 : min y (δ / 2) ≤ δ / 2 := min_le_right _ _
  have hb3 : y / 2 ≤ min y (δ / 2) := le_min (by linarith) (by linarith)
  have hn : ‖pt (δ / 2) (-min y (δ / 2))‖ ≤ δ := by
    refine (norm_pt_le_add _ _).trans ?_
    rw [abs_neg, abs_of_nonneg hb0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ δ / 2)]
    linarith
  refine isApproxMeasureStep_of_le (B := slope a * δ + y ^ 2 / 2) (by linarith) hδ hn
    (by simp; linarith) (fun e he => taylorDecrement_two_le ha0 he) ?_
  rw [taylorDecrement_two_pt ha0]
  have hB := curv_mul_le ha hδ1
  have hA := (slope_pos ha0).le
  have hB0 := curv_nonneg ha0
  set b := min y (δ / 2)
  have h1 : curv a * (δ / 2) ^ 2 ≤ slope a * δ / 4 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hb1) (sub_nonneg.2 hb3)]

/-- **A first-order step on the axis.** Let $q \ge 1$, $a \ge 2$, $\delta > 0$ and
$\varepsilon_1 < A(a)$. At $(a, 0)$ with the Step-1 displacement $d_1 = (\delta/4, 0)$, the
first-order test fails, and every $(h, \tau)$ with $h \ge \delta/4$ and
$\|(h, \tau)\| \le \Delta$ is a valid TRq step of order $1$ (`Optimization.IsTRqStep`). -/
theorem isTRqStep_axis_one {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a δ Δ h τ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hε : ε 1 < slope a) (hh : δ / 4 ≤ h) (hs : ‖pt h τ‖ ≤ Δ)
    {d : ℕ → ℝ²} (hd1 : d 1 = pt (δ / 4) 0) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (halfSqNorm con) (pt a 0))
      {e | pt a 0 + e ∈ halfPlane} params.ς q ε δ Δ d 1 (pt h τ) := by
  have ha0 : 0 < a := by linarith
  have hA := slope_pos ha0
  refine ⟨Finset.mem_Icc.2 ⟨le_rfl, hq⟩, ?_, fun i hi hi1 => absurd hi1
    (by have := (Finset.mem_Icc.1 hi).1; omega), ⟨mem_closedBall_zero_iff.2 hs,
      pt_add_pt_mem (by linarith)⟩, ?_⟩
  · rw [hd1, taylorDecrement_one_pt ha0]
    change (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ) < _
    norm_num
    nlinarith
  · rw [hd1, taylorDecrement_one_pt ha0, taylorDecrement_one_pt ha0]
    nlinarith

/-- **A second-order step on the axis.** Let $q \ge 2$, $a \ge 2$, $0 < \delta \le 1$,
$\delta \le \Delta$, $A(a) \le \varepsilon_1$ and $\varepsilon_2 \delta < 4A(a)$. At $(a, 0)$
with the Step-1 displacements $d_1 = (\delta/4, 0)$ and $d_2 = (\delta, 0)$, the first-order
test passes, the second-order test fails, and $(\delta, 0)$ is a valid TRq step of order $2$. -/
theorem isTRqStep_axis_two {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a δ Δ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδΔ : δ ≤ Δ) (hε1 : slope a ≤ ε 1)
    (hε2 : ε 2 * δ < 4 * slope a) {d : ℕ → ℝ²} (hd1 : d 1 = pt (δ / 4) 0)
    (hd2 : d 2 = pt δ 0) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (halfSqNorm con) (pt a 0))
      {e | pt a 0 + e ∈ halfPlane} params.ς q ε δ Δ d 2 (pt δ 0) := by
  have ha0 : 0 < a := by linarith
  have hA := slope_pos ha0
  have hB := curv_mul_le ha hδ1
  refine ⟨Finset.mem_Icc.2 ⟨by norm_num, hq⟩, ?_, fun i hi hi2 => ?_, ⟨mem_closedBall_zero_iff.2
    ((norm_pt_le_add _ _).trans (by rw [abs_of_pos hδ, abs_zero, add_zero]; exact hδΔ)),
      pt_add_pt_mem (by linarith)⟩, by rw [hd2]⟩
  · rw [hd2, taylorDecrement_two_pt ha0]
    change (1 / 4 : ℝ) * ε 2 * δ ^ 2 / ((2 : ℕ)! : ℝ) < _
    norm_num [Nat.factorial]
    nlinarith
  · have hi1 : i = 1 := by have := (Finset.mem_Icc.1 hi).1; omega
    subst hi1
    rw [hd1, taylorDecrement_one_pt ha0]
    change _ ≤ (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ)
    norm_num
    nlinarith

/-- **A first-order step off the axis.** Let $q \ge 1$, $a \ge 2$, $0 < \delta \le \Delta$ and
$\varepsilon_1 < 4y$. At $(a, y)$ with the Step-1 displacement $d_1 = (0, -\delta)$, the
first-order test fails, and $(0, -\delta)$ is a valid TRq step of order $1$. -/
theorem isTRqStep_shrink {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a y δ Δ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) (hε : ε 1 < 4 * y) {d : ℕ → ℝ²} (hd1 : d 1 = pt 0 (-δ)) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (halfSqNorm con) (pt a y))
      {e | pt a y + e ∈ halfPlane} params.ς q ε δ Δ d 1 (pt 0 (-δ)) := by
  have ha0 : 0 < a := by linarith
  refine ⟨Finset.mem_Icc.2 ⟨le_rfl, hq⟩, ?_, fun i hi hi1 => absurd hi1
    (by have := (Finset.mem_Icc.1 hi).1; omega), ⟨mem_closedBall_zero_iff.2
      ((norm_pt_le_add _ _).trans (by rw [abs_zero, abs_neg, abs_of_pos hδ, zero_add]; exact hδΔ)),
      pt_add_pt_mem (by linarith)⟩, by rw [hd1]⟩
  rw [hd1, taylorDecrement_one_pt ha0]
  change (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ) < _
  norm_num
  nlinarith

/-- A step $(h, \tau)$ from the axis point $(a, 0)$, $a \ge 2$, with $0 \le h \le 1/2$,
$\tau^2 \le A(a)\,h/4$ and predicted decrease $\mathrm{pred} \in (0, A(a)\,h]$, is successful:
its reduction ratio is at least $\eta_1$. -/
theorem η₁_le_ratio_axis {a h τ pred : ℝ} (ha : 2 ≤ a) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2)
    (hp0 : 0 < pred) (hp : pred ≤ slope a * h) (hτ : τ ^ 2 ≤ slope a * h / 4) :
    params.η₁ ≤ Optimization.reductionRatio (halfSqNorm con) (pt a 0) (pt h τ) pred
      := by
  refine η₁_le_reductionRatio hp0 ?_
  rw [pt_add_pt, halfSqNorm_con_pt (by linarith), halfSqNorm_con_pt (by linarith)]
  have := slope_mul_le_sub ha hh0 hh
  simp only [zero_add]
  nlinarith

/-- For $a \ge 0$, $y > 0$ and $2y \le \delta$, the step $(0, -\delta)$ from $(a, y)$ with predicted
decrease $y\delta$ is unsuccessful: its reduction ratio is less than $\eta_1$. -/
theorem ratio_shrink_lt_η₁ {a y δ : ℝ} (ha : 0 ≤ a) (hy : 0 < y) (hyδ : 2 * y ≤ δ) :
    Optimization.reductionRatio (halfSqNorm con) (pt a y) (pt 0 (-δ)) (y * δ) <
      params.η₁ := by
  refine reductionRatio_lt_η₁ (by nlinarith) ?_
  rw [pt_add_pt, halfSqNorm_con_pt ha, halfSqNorm_con_pt (by linarith)]
  simp only [add_zero]
  nlinarith

/-- For $a \ge 0$ and $y > 0$, the step $(0, -y)$ from $(a, y)$ with predicted decrease $y^2$ is
successful: its reduction ratio is at least $\eta_1$. -/
theorem η₁_le_ratio_shrink {a y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) :
    params.η₁ ≤
      Optimization.reductionRatio (halfSqNorm con) (pt a y) (pt 0 (-y)) (y * y) := by
  refine η₁_le_reductionRatio (by nlinarith) ?_
  rw [pt_add_pt, halfSqNorm_con_pt ha, halfSqNorm_con_pt (by linarith)]
  simp only [add_zero]
  nlinarith

end Steps

/-! ### The three phases of a long run -/

section Phases

/-- The parameters `Constrained.TwoPhaseExample.SlowDecay.params` with the initial radius
$\Delta_0 = r \in (0, 1]$. -/
noncomputable abbrev paramsAt (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) : Optimization.TRqParams :=
  params.withΔ₀ r h0 h1

/-- The feasible set $X$ is closed. -/
theorem isClosed_halfPlane : IsClosed halfPlane :=
  isClosed_le continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)

/-- For $a \ge 1$, $(a, b) \in X$. -/
theorem pt_mem_halfPlane {a b : ℝ} (ha : 1 ≤ a) : pt a b ∈ halfPlane := ha

open Classical in
/-- **The slow phase.** Let $q \ge 2$, $a \ge 2$, $0 < \delta \le 1/2$ and $A(a) \le \varepsilon_1$,
and let $\varepsilon_2 \delta < 4A(a + k\delta)$ for every $k < K$. Then there is a run of TRq
with a feasible set on $\nu$ and $X$ from $(a, 0)$, with the parameters of the example, initial
radius $\delta$ and threshold $\vartheta = 1$, such that the termination test fails at each of
the first $K$ iterations and all of these $K$ iterations are successful.

The $K$ iterations are the second-order steps $(\delta, 0)$. Any run of TRq can follow them. -/
theorem exists_run_axis {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a δ : ℝ} (ha : 2 ≤ a) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (hε1 : slope a ≤ ε 1) {K : ℕ}
    (hK : ∀ k < K, ε 2 * δ < 4 * slope (a + k * δ)) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = pt a 0 ∧
      Optimization.IsTRqRun (halfSqNorm con) (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k))
        (fun k => {e | x k + e ∈ halfPlane}) (paramsAt δ hδ0 (by linarith)) q ε 1 x s Δ jk d ∧
      (∀ k < K, ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k))
        (paramsAt δ hδ0 (by linarith)) q ε 1 Δ d k) ∧
      K ≤ ((Finset.range K).filter fun k =>
        (paramsAt δ hδ0 (by linarith)).η₁ ≤ Optimization.trqRatio (halfSqNorm con)
        (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k)) x s jk k).card
        := by
  obtain ⟨W, hW⟩ := exists_witness
  have hδ1' : δ ≤ 1 := by linarith
  set P := paramsAt δ hδ0 hδ1' with hP
  have hak : ∀ k : ℕ, 2 ≤ a + k * δ := fun k => by
    have : 0 ≤ (k : ℝ) * δ := by positivity
    linarith
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k = pt (a + k * δ) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then pt (δ / 4) 0
      else if j = 2 then pt δ 0 else W (xp k) δ j := ⟨_, fun _ => rfl⟩
  have hmin : min δ 1 = δ := min_eq_left hδ1'
  have hstep : ∀ k < K, Optimization.IsTRqStep (ftaylorSeries ℝ (halfSqNorm con) (xp k))
      {e | xp k + e ∈ halfPlane} P.ς q ε (min ((fun _ => δ) k) 1) ((fun _ => δ) k) (dp k)
      ((fun _ => 2) k) ((fun _ => pt δ 0) k) := fun k hk => by
    simp only [hmin, hxp]
    have hle : a ≤ a + k * δ := by have : 0 ≤ (k : ℝ) * δ := by positivity
                                   linarith
    exact isTRqStep_axis_two hq (hak k) hδ0 hδ1' le_rfl
      ((slope_anti (by linarith) hle).trans hε1) (hK k hk)
      (by rw [hdp]; simp) (by rw [hdp]; simp)
  have hpred : ∀ k, 0 < (ftaylorSeries ℝ (halfSqNorm con) (xp k)).taylorDecrement 2 (pt δ 0) ∧
      (ftaylorSeries ℝ (halfSqNorm con) (xp k)).taylorDecrement 2 (pt δ 0) ≤
        slope (a + k * δ) * δ := fun k => by
    have h0 : 0 < a + k * δ := by linarith [hak k]
    rw [hxp, taylorDecrement_two_pt h0]
    have := curv_mul_le (hak k) hδ1'
    have := slope_pos h0
    have := curv_nonneg h0
    constructor <;> nlinarith
  have hacc : ∀ k < K, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (halfSqNorm con) (xp k) ((fun _ => pt δ 0) k)
        ((ftaylorSeries ℝ (halfSqNorm con) (xp k)).taylorDecrement ((fun _ => 2) k)
          ((fun _ => pt δ 0) k)))
      (xp k) ((fun _ => pt δ 0) k) (xp (k + 1)) ((fun _ => δ) k) ((fun _ => δ) (k + 1)) :=
    fun k _ => by
    refine trAcceptance_succ hδ0.le ?_ (by rw [hxp, hxp, pt_add_pt]; push_cast; ring_nf)
    have := hpred k
    rw [hxp] at this ⊢
    have hA := (slope_pos (by linarith [hak k] : (0 : ℝ) < a + k * δ)).le
    exact η₁_le_ratio_axis (hak k) hδ0.le hδ1 this.1 this.2 (by
      rw [zero_pow two_ne_zero]; positivity)
  have hwit : ∀ k < K, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) (xp k)).taylorDecrement j) (min ((fun _ => δ) k) 1)
      {e | xp k + e ∈ halfPlane} P.ς (dp k j) := fun k _ j _ => by
    simp only [hmin]
    rw [hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]; rw [hxp]; exact isApproxMeasureStep_axis_one (hak k) hδ0.le
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]; rw [hxp]
        exact isApproxMeasureStep_axis_two (hak k) hδ0.le hδ1'
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ (by rw [hxp]; exact pt_mem_halfPlane (by linarith [hak k])) hδ0.le
  obtain ⟨y, sy, Δy, jy, dy, hy0, hy⟩ := Optimization.exists_isTRqRun_feasible
    isClosed_halfPlane (halfSqNorm con) (P.withΔ₀ δ hδ0 hδ1') q ε zero_le_one
    (show xp K ∈ halfPlane by rw [hxp]; exact pt_mem_halfPlane (by linarith [hak K]))
  obtain ⟨x, s, Δ, jk, d, hx0, hrun, hns, hcount, -, -⟩ := Optimization.exists_isTRqRun_append
    (T := K) (T' := 0) (c := 0) (P := P) (f := halfSqNorm con)
    (D := ftaylorSeries ℝ (halfSqNorm con)) (S := fun y => {e | y + e ∈ halfPlane}) (q := q)
    (ε := ε) (ϑ := 1) (xp := xp)
    (sp := fun _ => pt δ 0) (Δp := fun _ => δ) (jp := fun _ => 2) (dp := dp) rfl rfl hδ0
    hδ1' hstep hacc hwit (fun _ _ => hδ1') hy0 hy (fun _ h => absurd h (Nat.not_lt_zero _))
    (Nat.zero_le _)
  refine ⟨x, s, Δ, jk, d, by rw [hx0, hxp]; simp, hrun, hns, le_trans ?_ hcount⟩
  rw [add_zero]
  refine le_of_eq ?_
  rw [Finset.filter_true_of_mem fun k hk => ?_, Finset.card_range]
  have := hpred k
  rw [hxp] at this ⊢
  have hA := (slope_pos (by linarith [hak k] : (0 : ℝ) < a + k * δ)).le
  exact η₁_le_ratio_axis (hak k) hδ0.le hδ1 this.1 this.2 (by
    rw [zero_pow two_ne_zero]; positivity)

open Classical in
/-- **The shrinking phase.** Let $q \ge 2$, $a \ge 2$, $y = 2^{-N} \in (0, 1]$, $A(a) \le y$ and
$\varepsilon_1 < 4y$. Let a run of TRq from $(a, 0)$ with initial radius $y$ be given whose
termination test fails at each of its first $T'$ iterations, of which at least $c$ are
successful. Then there is a run of TRq from $(a, y)$ with initial radius $1$ whose termination
test fails at each of its first $N + 1 + T'$ iterations, of which at least $c$ are successful.

The new run starts with $N$ unsuccessful first-order iterations $(0, -\Delta)$, which halve the
radius down to $y$, and one successful iteration to $(a, 0)$, which keeps the radius $y$. Then
it continues with the given run. -/
theorem exists_run_shrink {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a y : ℝ} {N : ℕ} (ha : 2 ≤ a)
    (hyN : y = (1 / 2) ^ N) (hy0 : 0 < y) (hy1 : y ≤ 1) (hAy : slope a ≤ y)
    (hε : ε 1 < 4 * y) {xt st : ℕ → ℝ²} {Δt : ℕ → ℝ} {jt : ℕ → ℕ} {dt : ℕ → ℕ → ℝ²}
    (hxt0 : xt 0 = pt a 0)
    (hrun : Optimization.IsTRqRun (halfSqNorm con)
      (fun k => ftaylorSeries ℝ (halfSqNorm con) (xt k))
      (fun k => {e | xt k + e ∈ halfPlane}) (paramsAt y hy0 hy1) q ε 1 xt st Δt jt dt)
    {T' c : ℕ}
    (hns : ∀ k < T', ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ (halfSqNorm con) (xt k))
      (paramsAt y hy0 hy1) q ε 1 Δt dt k)
    (hc : c ≤ ((Finset.range T').filter fun k =>
      (paramsAt y hy0 hy1).η₁ ≤ Optimization.trqRatio (halfSqNorm con)
        (fun k => ftaylorSeries ℝ (halfSqNorm con) (xt k)) xt st jt k).card) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = pt a y ∧
      Optimization.IsTRqRun (halfSqNorm con) (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k))
        (fun k => {e | x k + e ∈ halfPlane}) (paramsAt 1 one_pos le_rfl) q ε 1 x s Δ jk d ∧
      (∀ k < N + 1 + T', ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k))
        (paramsAt 1 one_pos le_rfl) q ε 1 Δ d k) ∧
      c ≤ ((Finset.range (N + 1 + T')).filter fun k =>
        (paramsAt 1 one_pos le_rfl).η₁ ≤ Optimization.trqRatio (halfSqNorm con)
        (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k)) x s jk k).card
        := by
  obtain ⟨W, hW⟩ := exists_witness
  set P := paramsAt 1 one_pos le_rfl with hP
  have ha0 : 0 < a := by linarith
  have hmemy : pt a y ∈ halfPlane := pt_mem_halfPlane (by linarith)
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k = if k ≤ N then pt a y else pt a 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Δp, hΔp⟩ : ∃ Δp : ℕ → ℝ, ∀ k, Δp k = (1 / 2 : ℝ) ^ (min k N) := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then
      pt 0 (-(1 / 2 : ℝ) ^ k) else if j = 2 then
      pt ((1 / 2 : ℝ) ^ k / 2) (-min y ((1 / 2 : ℝ) ^ k / 2))
      else W (pt a y) ((1 / 2 : ℝ) ^ k) j := ⟨_, fun _ => rfl⟩
  have hxpl : ∀ k < N + 1, xp k = pt a y := fun k hk => by
    rw [hxp, ite_eq_left (by omega)]
  have hΔpl : ∀ k < N + 1, Δp k = (1 / 2 : ℝ) ^ k := fun k hk => by
    rw [hΔp, min_eq_left (by omega)]
  have hpow0 : ∀ k : ℕ, 0 < (1 / 2 : ℝ) ^ k := fun k => by positivity
  have hpow1 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hyk : ∀ k < N + 1, y ≤ (1 / 2 : ℝ) ^ k := fun k hk => by
    rw [hyN]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hstep : ∀ k < N + 1, Optimization.IsTRqStep (ftaylorSeries ℝ (halfSqNorm con) (xp k))
      {e | xp k + e ∈ halfPlane} P.ς q ε (min (Δp k) 1) (Δp k) (dp k) ((fun _ => 1) k)
      ((fun k => pt 0 (-(1 / 2 : ℝ) ^ k)) k) := fun k hk => by
    rw [hxpl k hk, hΔpl k hk, min_eq_left (hpow1 k)]
    exact isTRqStep_shrink (by omega) ha (hpow0 k) le_rfl hε (by rw [hdp]; simp)
  have hacc : ∀ k < N + 1, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (halfSqNorm con) (xp k) ((fun k => pt 0 (-(1 / 2 : ℝ) ^ k)) k)
        ((ftaylorSeries ℝ (halfSqNorm con) (xp k)).taylorDecrement ((fun _ => 1) k)
          ((fun k => pt 0 (-(1 / 2 : ℝ) ^ k)) k)))
      (xp k) ((fun k => pt 0 (-(1 / 2 : ℝ) ^ k)) k) (xp (k + 1)) (Δp k) (Δp (k + 1)) :=
    fun k hk => by
    simp only
    rw [hxpl k hk, taylorDecrement_one_pt ha0, hΔpl k hk]
    have hpred : slope a * 0 - y * -(1 / 2 : ℝ) ^ k = y * (1 / 2 : ℝ) ^ k := by ring
    rw [hpred]
    rcases Nat.lt_or_ge k N with hkN | hkN
    · rw [hxpl (k + 1) (by omega), hΔpl (k + 1) (by omega), pow_succ, ← div_eq_mul_one_div]
      refine trAcceptance_unsucc (hpow0 k).le (ratio_shrink_lt_η₁ ha0.le hy0 ?_)
      have := hyk (k + 1) (by omega)
      rw [pow_succ] at this
      linarith
    · have hkN' : k = N := by omega
      subst hkN'
      have e1 : xp (k + 1) = pt a 0 := by rw [hxp, ite_eq_right (by omega)]
      have e2 : Δp (k + 1) = (1 / 2 : ℝ) ^ k := by rw [hΔp, min_eq_right (by omega)]
      rw [e1, e2, ← hyN]
      exact trAcceptance_succ hy0.le (η₁_le_ratio_shrink ha0.le hy0)
        (by rw [pt_add_pt]; simp)
  have hwit : ∀ k < N + 1, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) (xp k)).taylorDecrement j) (min (Δp k) 1)
      {e | xp k + e ∈ halfPlane} P.ς (dp k j) := fun k hk j _ => by
    rw [hxpl k hk, hΔpl k hk, min_eq_left (hpow1 k), hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]
      exact isApproxMeasureStep_shrink_one ha hy0.le hAy (hpow0 k).le
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]
        exact isApproxMeasureStep_shrink_two ha hy0.le (hyk k hk) (hpow1 k)
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ hmemy (hpow0 k).le
  have hr : Δp (N + 1) = y := by rw [hΔp, min_eq_right (by omega), hyN]
  obtain ⟨x, s, Δ, jk, d, hx0, hrun', hns', hcount, -, -⟩ :=
    Optimization.exists_isTRqRun_append (T := N + 1) (T' := T') (c := c)
    (P := P) (f := halfSqNorm con)
    (D := ftaylorSeries ℝ (halfSqNorm con)) (S := fun y => {e | y + e ∈ halfPlane}) (q := q)
    (ε := ε) (ϑ := 1) (xp := xp)
    (sp := fun k => pt 0 (-(1 / 2 : ℝ) ^ k)) (Δp := Δp) (jp := fun _ => 1) (dp := dp)
    (by rw [hΔp]; simp; rfl) hr hy0 hy1 hstep hacc hwit
    (fun k _ => by rw [hΔp]; exact hpow1 _)
    (by rw [hxt0, hxp, ite_eq_right (by omega)]) hrun hns hc
  exact ⟨x, s, Δ, jk, d, by rw [hx0, hxpl 0 (by omega)], hrun', hns', le_trans (le_add_self) hcount⟩

open Classical in
/-- **The travel phase.** Let $q \ge 1$, $a_0 \ge 2$, and $\varepsilon_1 < A(a_0 + k/2)$ for every
$k \le k_0$. Let $0 \le y \le 1/2$ with $y^2 \le \varepsilon_1/8$. Let a run of TRq from
$(a_0 + (k_0 + 1)/2, y)$ with initial radius $1$ be given whose termination test fails at each
of its first $T'$ iterations, of which at least $c$ are successful. Then there is a run of TRq
from $(a_0, 0)$ with the parameters of the example whose termination test fails at each of its
first $k_0 + 1 + T'$ iterations, of which at least $c$ are successful.

The new run starts with $k_0 + 1$ successful first-order steps $(1/2, 0)$, the last one
$(1/2, y)$. Then it continues with the given run. -/
theorem exists_run_travel {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a₀ y : ℝ} (ha₀ : 2 ≤ a₀) {k₀ : ℕ}
    (hA : ∀ k ≤ k₀, ε 1 < slope (a₀ + k / 2)) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hy2 : y ^ 2 ≤ ε 1 / 8) {xt st : ℕ → ℝ²} {Δt : ℕ → ℝ} {jt : ℕ → ℕ} {dt : ℕ → ℕ → ℝ²}
    (hxt0 : xt 0 = pt (a₀ + (k₀ + 1) / 2) y)
    (hrun : Optimization.IsTRqRun (halfSqNorm con)
      (fun k => ftaylorSeries ℝ (halfSqNorm con) (xt k))
      (fun k => {e | xt k + e ∈ halfPlane}) (paramsAt 1 one_pos le_rfl) q ε 1 xt st Δt jt dt)
    {T' c : ℕ}
    (hns : ∀ k < T', ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ (halfSqNorm con) (xt k))
      (paramsAt 1 one_pos le_rfl) q ε 1 Δt dt k)
    (hc : c ≤ ((Finset.range T').filter fun k =>
      (paramsAt 1 one_pos le_rfl).η₁ ≤ Optimization.trqRatio (halfSqNorm con)
        (fun k => ftaylorSeries ℝ (halfSqNorm con) (xt k)) xt st jt k).card) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = pt a₀ 0 ∧
      Optimization.IsTRqRun (halfSqNorm con) (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k))
        (fun k => {e | x k + e ∈ halfPlane}) params q ε 1 x s Δ jk d ∧
      (∀ k < k₀ + 1 + T', ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k))
        params q ε 1 Δ d k) ∧
      c ≤ ((Finset.range (k₀ + 1 + T')).filter fun k =>
        params.η₁ ≤ Optimization.trqRatio (halfSqNorm con)
        (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k)) x s jk k).card := by
  obtain ⟨W, hW⟩ := exists_witness
  set P := params with hP
  have hak : ∀ k : ℕ, 2 ≤ a₀ + (k : ℝ) / 2 := fun k => by
    have : 0 ≤ (k : ℝ) / 2 := by positivity
    linarith
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k =
      if k ≤ k₀ then pt (a₀ + k / 2) 0 else pt (a₀ + (k₀ + 1) / 2) y := ⟨_, fun _ => rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ sp : ℕ → ℝ², ∀ k, sp k =
      if k < k₀ then pt (1 / 2) 0 else pt (1 / 2) y := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then pt (1 / 4) 0
      else if j = 2 then pt 1 0 else W (xp k) 1 j := ⟨_, fun _ => rfl⟩
  have hxpl : ∀ k < k₀ + 1, xp k = pt (a₀ + k / 2) 0 := fun k hk => by
    rw [hxp, ite_eq_left (by omega)]
  have hspτ : ∀ k < k₀ + 1, ∃ τ, sp k = pt (1 / 2) τ ∧ 0 ≤ τ ∧ τ ≤ y := fun k _ => by
    rw [hsp]
    split_ifs
    · exact ⟨0, rfl, le_rfl, hy0⟩
    · exact ⟨y, rfl, hy0, le_rfl⟩
  have hnext : ∀ k < k₀ + 1, xp (k + 1) = xp k + sp k := fun k hk => by
    rw [hxpl k hk, hsp]
    rcases Nat.lt_or_ge k k₀ with hkN | hkN
    · rw [hxpl (k + 1) (by omega), ite_eq_left hkN, pt_add_pt]
      push_cast; ring_nf
    · have hkN' : k = k₀ := by omega
      subst hkN'
      rw [hxp, ite_eq_right (by omega), ite_eq_right (by omega), pt_add_pt]
      ring_nf
  have hstep : ∀ k < k₀ + 1, Optimization.IsTRqStep (ftaylorSeries ℝ (halfSqNorm con) (xp k))
      {e | xp k + e ∈ halfPlane} P.ς q ε (min ((fun _ => (1 : ℝ)) k) 1) ((fun _ => (1 : ℝ)) k)
      (dp k) ((fun _ => 1) k) (sp k) := fun k hk => by
    obtain ⟨τ, hτ, hτ0, hτy⟩ := hspτ k hk
    simp only [min_self]
    rw [hxpl k hk, hτ]
    refine isTRqStep_axis_one hq (hak k) one_pos (hA k (by omega)) (by norm_num)
      ((norm_pt_le_add _ _).trans ?_) (by rw [hdp]; simp)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg hτ0]
    linarith
  have hacc : ∀ k < k₀ + 1, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (halfSqNorm con) (xp k) (sp k)
        ((ftaylorSeries ℝ (halfSqNorm con) (xp k)).taylorDecrement ((fun _ => 1) k) (sp k)))
      (xp k) (sp k) (xp (k + 1)) ((fun _ => (1 : ℝ)) k) ((fun _ => (1 : ℝ)) (k + 1)) :=
    fun k hk => by
    refine trAcceptance_succ zero_le_one ?_ (hnext k hk)
    obtain ⟨τ, hτ, hτ0, hτy⟩ := hspτ k hk
    have ha0 : 0 < a₀ + (k : ℝ) / 2 := by linarith [hak k]
    have hA0 := slope_pos ha0
    have hAk := hA k (by omega)
    simp only
    rw [hxpl k hk, hτ, taylorDecrement_one_pt ha0]
    have hτ2 : τ ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hτ0 hτy 2
    exact η₁_le_ratio_axis (hak k) (by norm_num) le_rfl (by nlinarith) (by nlinarith)
      (by nlinarith)
  have hwit : ∀ k < k₀ + 1, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (halfSqNorm con) (xp k)).taylorDecrement j) (min ((fun _ => (1 : ℝ)) k) 1)
      {e | xp k + e ∈ halfPlane} P.ς (dp k j) := fun k hk j _ => by
    simp only [min_self]
    rw [hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]; rw [hxpl k hk]
      exact isApproxMeasureStep_axis_one (hak k) zero_le_one
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]; rw [hxpl k hk]
        exact isApproxMeasureStep_axis_two (hak k) zero_le_one le_rfl
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ (by rw [hxpl k hk]; exact pt_mem_halfPlane (by linarith [hak k]))
          zero_le_one
  obtain ⟨x, s, Δ, jk, d, hx0, hrun', hns', hcount, -, -⟩ := Optimization.exists_isTRqRun_append
    (T := k₀ + 1) (T' := T') (c := c) (P := P) (f := halfSqNorm con)
    (D := ftaylorSeries ℝ (halfSqNorm con)) (S := fun y => {e | y + e ∈ halfPlane}) (q := q)
    (ε := ε) (ϑ := 1) (xp := xp)
    (sp := sp) (Δp := fun _ => 1) (jp := fun _ => 1) (dp := dp) rfl rfl one_pos le_rfl hstep hacc
    hwit (fun _ _ => le_rfl) (by rw [hxt0, hxp, ite_eq_right (by omega)])
    hrun hns hc
  exact ⟨x, s, Δ, jk, d, by rw [hx0, hxpl 0 (by omega)]; norm_num, hrun', hns',
    le_trans (le_add_self) hcount⟩

end Phases

/-! ### The long run -/

section LongRun

/-- For $n \in \mathbb{N}$, $A(2^{4n}) = 2^{-5n}/8$. -/
theorem slope_two_pow (n : ℕ) : slope ((2 : ℝ) ^ (4 * n)) = (1 / 2) ^ (5 * n) / 8 := by
  unfold slope
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have e : ((4 * n : ℕ) : ℝ) * (-(5 / 4 : ℝ)) = -((5 * n : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div_pow, one_div]

/-- For $x \ge 2^{4n}$, $A(x) \le 2^{-5n}/8$. -/
theorem slope_le_of_ge (n : ℕ) {x : ℝ} (hx : (2 : ℝ) ^ (4 * n) ≤ x) :
    slope x ≤ (1 / 2) ^ (5 * n) / 8 :=
  (slope_anti (by positivity) hx).trans_eq (slope_two_pow n)

/-- For $0 < x < 2^{4n}$, $A(x) > 2^{-5n}/8$. -/
theorem lt_slope_of_lt (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx : x < (2 : ℝ) ^ (4 * n)) :
    (1 / 2) ^ (5 * n) / 8 < slope x := by
  rw [← slope_two_pow n]
  unfold slope
  have := Real.rpow_lt_rpow_of_neg hx0 hx (by norm_num : (-(5 / 4 : ℝ)) < 0)
  linarith

/-- For $m, k \in \mathbb{N}$, $2^{m+k}\, 2^{-k} = 2^m$. -/
theorem two_pow_add_mul_half_pow (m k : ℕ) :
    (2 : ℝ) ^ (m + k) * (1 / 2) ^ k = 2 ^ m := by
  rw [pow_add, mul_assoc, ← mul_pow]; norm_num

/-- **A long run of TRq.** Let $q \ge 2$ and $M \ge 1$, let the tolerances satisfy
$\varepsilon_1 = 2^{-10M}/2$ and $\varepsilon_2 = 2^{-5M}/2$, and let $a_0 \ge 2$ with
$\varepsilon_1 < A(a_0)$. Then there are a run of TRq with a feasible set on
$\nu = \tfrac12 \|c\|^2$ and $X$ from $(a_0, 0)$, with the parameters of the example and
threshold $\vartheta = 1$, and a number $T$, such that the termination test fails at each of the
first $T$ iterations and at least
$$2^{22M} - 2^{18M} - 2^{10M}$$
of these iterations are successful.

The run consists of the travel, shrinking and slow phases
(`Constrained.TwoPhaseExample.SlowDecay.exists_run_travel`,
`Constrained.TwoPhaseExample.SlowDecay.exists_run_shrink` and
`Constrained.TwoPhaseExample.SlowDecay.exists_run_axis`) with $y = 2^{-10M}$ and
$K = 2^{22M} - 2^{18M} - 2^{10M}$ slow steps. The difference is in natural numbers. -/
theorem exists_long_run {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 1 ≤ M) {ε : ℕ → ℝ}
    (h1 : ε 1 = (1 / 2) ^ (10 * M) / 2) (h2 : ε 2 = (1 / 2) ^ (5 * M) / 2) {a₀ : ℝ}
    (ha₀ : 2 ≤ a₀) (hA₀ : ε 1 < slope a₀) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²) (T : ℕ), x 0 = pt a₀ 0 ∧
      Optimization.IsTRqRun (halfSqNorm con) (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k))
        (fun k => {e | x k + e ∈ halfPlane}) params q ε 1 x s Δ jk d ∧
      (∀ k < T, ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k))
        params q ε 1 Δ d k) ∧
      2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) ≤ ((Finset.range T).filter fun k =>
        params.η₁ ≤ Optimization.trqRatio (halfSqNorm con)
        (fun k => ftaylorSeries ℝ (halfSqNorm con) (x k)) x s jk k).card := by
  classical
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = (1 / 2) ^ (10 * M) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hy16 : y ≤ 1 / 16 := by
    rw [hydef]
    calc ((1 : ℝ) / 2) ^ (10 * M) ≤ (1 / 2) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have hy1 : y ≤ 1 := by linarith
  have hy10 : y ≤ 1 / 1024 := by
    rw [hydef]
    calc ((1 : ℝ) / 2) ^ (10 * M) ≤ (1 / 2) ^ 10 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 1024 := by norm_num
  have hE : ε 1 = y / 2 := by rw [h1, hydef]
  have hy8 : (1 / 2 : ℝ) ^ (5 * (2 * M)) / 8 = y / 8 := by
    rw [hydef, show 5 * (2 * M) = 10 * M by ring]
  -- the end of the travel phase
  have hex : ∃ k : ℕ, slope (a₀ + ((k : ℝ) + 1) / 2) ≤ ε 1 := by
    refine ⟨2 * 2 ^ (8 * M), (slope_le_of_ge (2 * M) ?_).trans ?_⟩
    · rw [show 4 * (2 * M) = 8 * M by ring]
      push_cast
      have : (0 : ℝ) ≤ 2 ^ (8 * M) := by positivity
      linarith
    · rw [hy8, hE]; linarith
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ = Nat.find hex := ⟨_, rfl⟩
  have hAs : slope (a₀ + ((k₀ : ℝ) + 1) / 2) ≤ ε 1 := hk₀ ▸ Nat.find_spec hex
  have hAk : ∀ k ≤ k₀, ε 1 < slope (a₀ + (k : ℝ) / 2) := fun k hk => by
    rcases k with _ | m
    · simpa using hA₀
    · have := Nat.find_min hex (show m < Nat.find hex by omega)
      push Not at this
      push_cast
      exact this
  -- `a_s < 2^{8M} + 1`
  have has : a₀ + ((k₀ : ℝ) + 1) / 2 < 2 ^ (8 * M) + 1 := by
    by_contra hcon
    push Not at hcon
    have h := hAk k₀ le_rfl
    have h' := slope_le_of_ge (2 * M) (x := a₀ + (k₀ : ℝ) / 2) (by
      rw [show 4 * (2 * M) = 8 * M by ring]; linarith)
    rw [hy8, hE] at *
    linarith
  set as := a₀ + ((k₀ : ℝ) + 1) / 2 with has_def
  have has2 : 2 ≤ as := by
    have : 0 ≤ ((k₀ : ℝ) + 1) / 2 := by positivity
    linarith
  -- the slow phase
  set K := 2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) with hKdef
  have hKle : 2 ^ (18 * M) + 2 ^ (10 * M) ≤ 2 ^ (22 * M) := by
    have a1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ (22 * M) = 2 * 2 ^ (22 * M - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hKs1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKs2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M) - 2 ^ (18 * M) :=
    Nat.le_sub_of_add_le (by rw [add_comm]; exact hKle)
  have hKr : (K : ℝ) * y = 2 ^ (12 * M) - 2 ^ (8 * M) - 1 := by
    rw [hKdef, Nat.cast_sub hKs2, Nat.cast_sub hKs1, hydef]
    push_cast
    rw [sub_mul, sub_mul, show 22 * M = 12 * M + 10 * M by ring,
      show 18 * M = 8 * M + 10 * M by ring, two_pow_add_mul_half_pow,
      two_pow_add_mul_half_pow, ← mul_pow]
    norm_num
  have hK : ∀ k < K, ε 2 * y < 4 * slope (as + k * y) := fun k hk => by
    have hkK : (k : ℝ) * y ≤ (K : ℝ) * y := by
      have : (k : ℝ) ≤ K := by exact_mod_cast hk.le
      nlinarith
    have hx : as + k * y < (2 : ℝ) ^ (4 * (3 * M)) := by
      rw [show 4 * (3 * M) = 12 * M by ring]
      linarith
    have hpos : 0 < as + k * y := by
      have : 0 ≤ (k : ℝ) * y := by positivity
      linarith
    have := lt_slope_of_lt (3 * M) hpos hx
    have e : ε 2 * y = (1 / 2) ^ (5 * (3 * M)) / 2 := by
      rw [h2, hydef, show 5 * (3 * M) = 5 * M + 10 * M by ring, pow_add]; ring
    rw [e]
    linarith
  obtain ⟨x3, s3, Δ3, j3, d3, hx3, hrun3, hns3, hc3⟩ :=
    exists_run_axis hq has2 hy0 (by linarith) (hAs.trans_eq rfl) hK
  -- the shrinking phase
  obtain ⟨x2, s2, Δ2, j2, d2, hx2, hrun2, hns2, hc2⟩ :=
    exists_run_shrink (N := 10 * M) hq has2 hydef hy0 hy1 (by linarith) (by linarith) hx3
      hrun3 hns3 hc3
  -- the travel phase
  obtain ⟨x1, s1, Δ1, j1, d1, hx1, hrun1, hns1, hc1⟩ :=
    exists_run_travel (by omega) ha₀ hAk hy0.le (by linarith) (by rw [hE]; nlinarith) hx2 hrun2
      hns2 hc2
  exact ⟨x1, s1, Δ1, j1, d1, _, hx1, hrun1, hns1, hc1⟩

end LongRun


/-! ### Smoothness and the data of the two-phase examples -/

/-- The bound on the $k$-th derivative of $g(t) = t^{-1/8}$ on $t > 1/2$:
$$C_k = \left|\left(-\tfrac18\right)\left(-\tfrac18 - 1\right) \cdots \left(-\tfrac18 - k +
  1\right)\right| \left(\tfrac12\right)^{-1/8 - k} + 1.$$
-/
noncomputable def derivBound (k : ℕ) : ℝ :=
  |(descPochhammer ℝ k).eval (-(1 / 8 : ℝ))| * (1 / 2 : ℝ) ^ (-(1 / 8 : ℝ) - k) + 1

/-- For every $k$, the derivative bound satisfies $C_k \ge 1$. -/
theorem one_le_derivBound (k : ℕ) : 1 ≤ derivBound k := by
  unfold derivBound
  have : 0 ≤ |(descPochhammer ℝ k).eval (-(1 / 8 : ℝ))| * (1 / 2 : ℝ) ^ (-(1 / 8 : ℝ) - k) := by
    positivity
  linarith

/-- For $t > 1/2$, the $k$-th derivative of $g(t) = t^{-1/8}$ satisfies $|g^{(k)}(t)| \le C_k$. -/
theorem abs_iteratedDeriv_eighthPow_le (k : ℕ) {t : ℝ} (ht : 1 / 2 < t) :
    |iteratedDeriv k eighthPow t| ≤ derivBound k := by
  have e : eighthPow = fun t : ℝ => t ^ (-(1 / 8 : ℝ)) := rfl
  rw [iteratedDeriv_eq_iterate, e, Real.iter_deriv_rpow_const, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
  unfold derivBound
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) ht.le
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith : -(1 / 8 : ℝ) - k ≤ 0)
  have := abs_nonneg ((descPochhammer ℝ k).eval (-(1 / 8 : ℝ)))
  nlinarith

/-- The set $X_0 = \{v : v_1 > 1/2\}$ is open. -/
theorem isOpen_openHalfPlane : IsOpen openHalfPlane :=
  isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)

/-- The set $X_0 = \{v : v_1 > 1/2\}$ is convex. -/
theorem convex_openHalfPlane : Convex ℝ openHalfPlane :=
  convex_halfSpace_gt (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).isLinear _

/-- The feasible set lies in the open half-plane: $X \subseteq X_0$. -/
theorem halfPlane_subset : halfPlane ⊆ openHalfPlane := fun v hv => by
  change 1 ≤ v 0 at hv; change 1 / 2 < v 0; linarith


/-- For $M \ge 1$, $2^{-10M}/2 < A(2)$. -/
theorem tol_lt_slope_two {M : ℕ} (hM : 1 ≤ M) : (1 / 2 : ℝ) ^ (10 * M) / 2 < slope 2 := by
  have h2 := lt_slope_of_lt 1 (x := 2) (by norm_num) (by norm_num)
  have : (1 / 2 : ℝ) ^ (10 * M) ≤ (1 / 2) ^ 10 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at h2 this ⊢
  linarith

/-- The constant $\beta_1 = 1/(2\|c(x_0)\|)$ at $x_0 = (2, 0)$, so that $\beta_1 \|c(x_0)\| = 1/2$.
-/
noncomputable def phaseOneConst : ℝ := 1 / (2 * ‖con (pt 2 0)‖)

/-- At $x_0 = (2, 0)$, $\beta_1 \|c(x_0)\| = 1/2$. -/
theorem phaseOneConst_mul : phaseOneConst * ‖con (pt 2 0)‖ = 1 / 2 := by
  have := one_le_norm_con (pt 2 0)
  unfold phaseOneConst
  field_simp

/-- The constant $\beta_1$ is positive. -/
theorem phaseOneConst_pos : 0 < phaseOneConst := by
  have := one_le_norm_con (pt 2 0)
  unfold phaseOneConst; positivity

/-- The constant $\beta_1$ is less than $1$. -/
theorem phaseOneConst_lt_one : phaseOneConst < 1 := by
  have h := one_le_norm_con (pt 2 0)
  have h2 := phaseOneConst_mul
  have h3 := phaseOneConst_pos
  nlinarith

/-- The constraint $c_2 : \mathbb{R}^2 \to \mathbb{R}^2$, $c_2(v) = (v_1^{-1/8}, v_2)$. It is the
constraint $c$ without its constant component, so that $\|c_2(256, 0)\| = 1/2$. -/
noncomputable def con₂ (v : ℝ²) : ℝ² := pt (eighthPow (v 0)) (v 1)

/-- For every $v \in \mathbb{R}^2$, $\|c_2(v)\|^2 = g(v_1)^2 + v_2^2$. -/
theorem norm_con₂_sq (v : ℝ²) : ‖con₂ v‖ ^ 2 = eighthPow (v 0) ^ 2 + (v 1) ^ 2 :=
  norm_pt_sq _ _

/-- With the objective $f = 0$ and the constraint $c_2$, the target merit function is
$$\mu(v, t) = \tfrac12 \|c(v)\|^2 - \tfrac12 (1 - t^2).$$
-/
theorem targetMerit_con₂ (t : ℝ) (v : ℝ²) :
    targetMerit (fun _ => 0) con₂ t v = halfSqNorm con v - (1 - t ^ 2) / 2 := by
  rw [targetMerit_def, norm_con₂_sq, halfSqNorm_apply, norm_con_sq]; ring

/-- For every target $t$, every $v$ with $v_1 > 0$ and every order $j$, the Taylor decrements of
$\mu(\cdot, t)$, for the objective $f = 0$ and the constraint $c_2$, and of $\tfrac12 \|c\|^2$
at $v$ agree. -/
theorem taylorDecrement_targetMerit_con₂ (t : ℝ) {v : ℝ²} (hv : 0 < v 0) (j : ℕ) :
    (ftaylorSeries ℝ (targetMerit (fun _ => 0) con₂ t) v).taylorDecrement j =
      (ftaylorSeries ℝ (halfSqNorm con) v).taylorDecrement j := by
  have hU : IsOpen {w : ℝ² | 0 < w 0} :=
    isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  have hev : targetMerit (fun _ => 0) con₂ t =ᶠ[𝓝 v]
      fun w => nu w - (1 - t ^ 2) / 2 := by
    filter_upwards [hU.mem_nhds hv] with w hw
    rw [targetMerit_con₂ t w, halfSqNorm_con_eq (le_of_lt hw)]
  rw [(hev.ftaylorSeries ℝ).eq_of_nhds, ftaylorSeries_halfSqNorm_con hv]
  funext s
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  change iteratedFDeriv ℝ i (fun w => nu w - (1 - t ^ 2) / 2) v (fun _ => s) =
    iteratedFDeriv ℝ i nu v (fun _ => s)
  rw [iteratedFDeriv_sub_const_apply (by have := (Finset.mem_Icc.1 hi).1; omega)
    (contDiffAt_nu hv i)]

/-- $g(256) = 256^{-1/8} = 1/2$. -/
theorem eighthPow_256 : eighthPow 256 = 1 / 2 := by
  rw [eighthPow, show (256 : ℝ) = 2 ^ ((8 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- $\|c_2(256, 0)\| = 1/2$. -/
theorem norm_con₂_x₀ : ‖con₂ (pt 256 0)‖ = 1 / 2 := by
  have h := norm_con₂_sq (pt 256 0)
  simp only [pt_zero, pt_one, eighthPow_256] at h
  nlinarith [norm_nonneg (con₂ (pt 256 0))]

/-- For $M \ge 2$, $2^{-10M}/2 < A(256)$. -/
theorem tol_lt_slope_256 {M : ℕ} (hM : 2 ≤ M) :
    (1 / 2 : ℝ) ^ (10 * M) / 2 < slope 256 := by
  have h := slope_two_pow 2
  rw [show (2 : ℝ) ^ (4 * 2) = 256 by norm_num] at h
  rw [h]
  have : (1 / 2 : ℝ) ^ (10 * M) ≤ (1 / 2) ^ 20 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at this ⊢
  linarith

/-- The tolerances $\varepsilon_1 = 2^{-10M}$, $\varepsilon_2 = 2^{-5M}$, and $\varepsilon_j = 1$
for every other $j$, in particular $\varepsilon_0 = 1$. -/
noncomputable def tol (M : ℕ) : ℕ → ℝ := fun j =>
  if j = 1 then (1 / 2) ^ (10 * M) else if j = 2 then (1 / 2) ^ (5 * M) else 1

/-- For every $j$, the tolerance $\varepsilon_j$ of `Constrained.TwoPhaseExample.SlowDecay.tol M`
lies in $(0, 1]$. -/
theorem tol_mem (M : ℕ) (j : ℕ) : 0 < tol M j ∧ tol M j ≤ 1 := by
  unfold tol
  split_ifs
  · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  · exact ⟨one_pos, le_rfl⟩

/-- For $n, k \in \mathbb{N}$, $\bigl((1/2)^n\bigr)^{-k} = 2^{nk}$. -/
theorem half_pow_rpow_neg (n k : ℕ) : ((1 / 2 : ℝ) ^ n) ^ (-(k : ℝ)) = 2 ^ (n * k) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← pow_mul, one_div, inv_pow, inv_inv]

/-- For $\kappa \in \mathbb{R}$ and $M \in \mathbb{N}$ with $M > 20|\kappa| + 20$,
$$|\kappa|\,(1 + 10M)\, 2^{20M} < 2^{22M}/2.$$
-/
theorem mul_two_pow_lt {κ : ℝ} {M : ℕ} (hM : 20 * |κ| + 20 < M) :
    |κ| * (1 + 10 * M) * 2 ^ (20 * M) < (2 : ℝ) ^ (22 * M) / 2 := by
  have h2M : (M : ℝ) + 1 ≤ 2 ^ M := by exact_mod_cast Nat.lt_two_pow_self
  have e : (2 : ℝ) ^ (22 * M) = (2 ^ M) ^ 2 * 2 ^ (20 * M) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  rw [e]
  have hB : (0 : ℝ) < 2 ^ (20 * M) := by positivity
  have hκ := abs_nonneg κ
  have hsq : ((M : ℝ) + 1) ^ 2 ≤ (2 ^ M) ^ 2 := pow_le_pow_left₀ (by positivity) h2M 2
  have key : 2 * (|κ| * (1 + 10 * M)) < ((M : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith


end Constrained.TwoPhaseExample.SlowDecay
