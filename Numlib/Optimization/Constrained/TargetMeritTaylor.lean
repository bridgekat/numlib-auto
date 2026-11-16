/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TargetResidual

/-!
# Taylor decrements of the target merit function on the target

Let $f : E \to \mathbb{R}$ and $c : E \to F$, with $F$ a real inner product space. This file
compares the target merit function $\mu(x, t) = \frac12 (\|c(x)\|^2 + (f(x) - t)^2)$
(`Constrained.targetMerit`) with the feasibility merit function $\nu(x) = \frac12 \|c(x)\|^2$
(`Constrained.halfSqNorm`), which is the case $f = 0$, $t = 0$. At a point $x$ with $f(x) = t$ it
compares their Taylor decrements $\Delta T_j(d)$ and their Taylor measures $\varphi^\delta_j = \sup
\{\Delta T_j(d) : \|d\| \le \delta, d \in S\}$. This is the case $f(x_\varepsilon) = t_\varepsilon$
of Lemma 14.3.5 in §14.3.2.2 of [cartis2022evaluation].

The first-order measures agree. At orders $2$ and $3$ the decrements differ by terms in
$\nabla f(x)[d]$. So the measures agree on $S \cap \ker \nabla f(x)$, and on $S$ they differ by
explicit amounts.

## Main definitions

* `Constrained.halfSqNorm`: the feasibility merit function $\nu(x) = \frac12 \|c(x)\|^2$.

## Main results

* `Constrained.taylorMeasure_one_targetMerit_of_eq`: the first-order Taylor measures of
  $\mu(\cdot, t)$ and $\nu$ agree.
* `Constrained.taylorDecrement_two_targetMerit_of_eq`,
  `Constrained.taylorDecrement_three_targetMerit_of_eq`: the Taylor decrements of orders $2$ and $3$
  of $\mu(\cdot, t)$ in terms of those of $\nu$.
* `Constrained.taylorMeasure_halfSqNorm_two_le_of_eq`,
  `Constrained.taylorMeasure_halfSqNorm_three_le_of_eq`: bounds on the Taylor measures of $\nu$ of
  orders $2$ and $3$ from those of $\mu(\cdot, t)$.

## Notation

* $\Delta T_{\phi, j}(d)$: the Taylor decrement $T_{\phi,j}(x, 0) - T_{\phi,j}(x, d)$ of order $j$
  of $\phi$ at $x$, which is `FormalMultilinearSeries.taylorDecrement` of `ftaylorSeries ℝ φ x`.
* $\varphi^\delta_{\phi, j}(S)$: the Taylor measure `Optimization.taylorMeasure` of order $j$ of
  $\phi$ at $x$, the supremum of $\Delta T_{\phi, j}(d)$ over $\|d\| \le \delta$, $d \in S$.
-/

open Set Metric

namespace Constrained

section HalfSqNorm

variable {E F : Type*} [NormedAddCommGroup F]

/-- The **feasibility merit function** $\nu(x) = \frac12 \|c(x)\|^2$. This is $\Phi_2$ of (14.3.16)
of [cartis2022evaluation]. -/
noncomputable def halfSqNorm (c : E → F) (x : E) : ℝ := ‖c x‖ ^ 2 / 2

/-- The feasibility merit function at $x$ is $\|c(x)\|^2 / 2$. -/
theorem halfSqNorm_apply (c : E → F) (x : E) : halfSqNorm c x = ‖c x‖ ^ 2 / 2 := rfl

/-- The feasibility merit function $\nu$ is the target merit function of the zero objective with
target $t = 0$. -/
theorem halfSqNorm_eq_targetMerit (c : E → F) :
    halfSqNorm c = targetMerit (fun _ => (0 : ℝ)) c 0 := by
  funext z
  simp [halfSqNorm]

/-- The feasibility merit function is nonnegative. -/
theorem halfSqNorm_nonneg (c : E → F) (x : E) : 0 ≤ halfSqNorm c x := by
  rw [halfSqNorm_apply]; positivity

/-- For all $x$ and $y$: $\nu(y) \le \nu(x)$ if and only if $\|c(y)\| \le \|c(x)\|$. -/
theorem halfSqNorm_le_halfSqNorm_iff {c : E → F} {x y : E} :
    halfSqNorm c y ≤ halfSqNorm c x ↔ ‖c y‖ ≤ ‖c x‖ := by
  rw [halfSqNorm_apply, halfSqNorm_apply, div_le_div_iff_of_pos_right two_pos]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero

end HalfSqNorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

variable {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}

/-- Let $f$ and $c$ be differentiable at $x$, and let $f(x) = t$. Then for every $\delta$ and every
set $S$ of directions, the first-order Taylor measures of $\mu(\cdot, t)$ and $\nu$ at $x$
agree:
$$\varphi^\delta_{\mu, 1}(S) = \varphi^\delta_{\nu, 1}(S).$$
-/
theorem taylorMeasure_one_targetMerit_of_eq (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (ht : f x = t) (δ : ℝ) (S : Set E) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 1 δ S =
      Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 1 δ S := by
  simp only [Optimization.taylorMeasure_eq_sSup]
  congr 2
  funext d
  rw [FormalMultilinearSeries.taylorDecrement_one_apply,
    FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [fderiv_targetMerit_of_eq hf hc ht, halfSqNorm_eq_targetMerit,
    fderiv_targetMerit_of_eq (differentiableAt_const _) hc rfl]

/-- Let $f$ and $c$ be $C^2$ at $x$, and let $f(x) = t$. Then for every direction $d$, the
second-order Taylor decrements of $\mu(\cdot, t)$ and $\nu$ at $x$ satisfy
$$\Delta T_{\mu, 2}(d) = \Delta T_{\nu, 2}(d) - \tfrac12 (\nabla f(x)[d])^2.$$
-/
theorem taylorDecrement_two_targetMerit_of_eq (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : f x = t) (d : E) :
    (ftaylorSeries ℝ (targetMerit f c t) x).taylorDecrement 2 d =
      (ftaylorSeries ℝ (halfSqNorm c) x).taylorDecrement 2 d - (fderiv ℝ f x d) ^ 2 / 2 := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt two_ne_zero
  have hc1 : DifferentiableAt ℝ c x := hc.differentiableAt two_ne_zero
  rw [FormalMultilinearSeries.taylorDecrement_two, FormalMultilinearSeries.taylorDecrement_two]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [fderiv_targetMerit_of_eq hf1 hc1 ht, iteratedFDeriv_two_targetMerit_apply hf hc,
    halfSqNorm_eq_targetMerit, iteratedFDeriv_two_targetMerit_apply contDiffAt_const hc,
    fderiv_targetMerit_of_eq (differentiableAt_const _) hc1 rfl, ← ht]
  simp
  ring

/-- Let $f$ and $c$ be $C^3$ at $x$, and let $f(x) = t$. Then for every direction $d$, the
third-order Taylor decrements of $\mu(\cdot, t)$ and $\nu$ at $x$ satisfy
$$\Delta T_{\mu, 3}(d) = \Delta T_{\nu, 3}(d) - \tfrac12 (\nabla f(x)[d])^2 - \tfrac12 \nabla
  f(x)[d] \, \nabla^2 f(x)[d]^2.$$
-/
theorem taylorDecrement_three_targetMerit_of_eq (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : f x = t) (d : E) :
    (ftaylorSeries ℝ (targetMerit f c t) x).taylorDecrement 3 d =
      (ftaylorSeries ℝ (halfSqNorm c) x).taylorDecrement 3 d - (fderiv ℝ f x d) ^ 2 / 2 -
        fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) / 2 := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hc2 : ContDiffAt ℝ 2 c x := hc.of_le (by norm_num)
  have h2 := taylorDecrement_two_targetMerit_of_eq hf2 hc2 ht d
  rw [FormalMultilinearSeries.taylorDecrement_three, FormalMultilinearSeries.taylorDecrement_three]
  rw [FormalMultilinearSeries.taylorDecrement_two, FormalMultilinearSeries.taylorDecrement_two]
    at h2
  have h3 : iteratedFDeriv ℝ 3 (targetMerit f c t) x (fun _ => d) =
      iteratedFDeriv ℝ 3 (halfSqNorm c) x (fun _ => d) +
        3 * iteratedFDeriv ℝ 2 f x (fun _ => d) * fderiv ℝ f x d := by
    rw [iteratedFDeriv_three_targetMerit_apply hf hc, halfSqNorm_eq_targetMerit,
      iteratedFDeriv_three_targetMerit_apply contDiffAt_const hc, ← ht]
    simp
  simp only [ftaylorSeries] at h2 ⊢
  rw [h3]
  linarith

omit [InnerProductSpace ℝ F] in
private theorem abs_fderiv_le {d : E} {δ : ℝ} (hd : d ∈ closedBall (0 : E) δ) :
    |fderiv ℝ f x d| ≤ ‖fderiv ℝ f x‖ * δ := by
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
    (mem_closedBall_zero_iff.1 hd) (norm_nonneg _))

omit [InnerProductSpace ℝ F] in
private theorem abs_iteratedFDeriv_two_le {d : E} {δ : ℝ} (hd : d ∈ closedBall (0 : E) δ) :
    |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2 := by
  rw [← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ 2 f x).le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (mem_closedBall_zero_iff.1 hd) 2) (norm_nonneg _)

/-- Let $f$ and $c$ be $C^2$ at $x$, let $f(x) = t$, let $\delta \ge 0$, and let $S$ be a set of
directions with $0 \in S$. Suppose that the second-order Taylor measure of $\mu(\cdot, t)$ at
$x$ satisfies $\varphi^\delta_{\mu, 2}(S) \le B$. Then the second-order Taylor measure of $\nu$
at $x$ satisfies
$$\varphi^\delta_{\nu, 2}(S \cap \ker \nabla f(x)) \le B \quad\text{and}\quad
  \varphi^\delta_{\nu, 2}(S) \le B + \tfrac12 (\|\nabla f(x)\| \delta)^2.$$
-/
theorem taylorMeasure_halfSqNorm_two_le_of_eq {δ B : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : f x = t) (hδ : 0 ≤ δ) {S : Set E} (hS : (0 : E) ∈ S)
    (hμ : Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 2 δ S ≤ B) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 2 δ
        (S ∩ {d | fderiv ℝ f x d = 0}) ≤ B ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 2 δ S ≤
        B + (‖fderiv ℝ f x‖ * δ) ^ 2 / 2 := by
  constructor
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩
      fun d hd => ?_
    have h := taylorDecrement_two_targetMerit_of_eq hf hc ht d
    have hd0 : fderiv ℝ f x d = 0 := hd.2.2
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit f c t) x) 2 (S := S) ⟨hd.1, hd.2.1⟩
    rw [hd0] at h
    linarith
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS⟩ fun d hd => ?_
    have h := taylorDecrement_two_targetMerit_of_eq hf hc ht d
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit f c t) x) 2 (S := S) hd
    have hg : (fderiv ℝ f x d) ^ 2 ≤ (‖fderiv ℝ f x‖ * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_fderiv_le hd.1) 2
    linarith

/-- Let $f$ and $c$ be $C^3$ at $x$, let $f(x) = t$, let $\delta \ge 0$, and let $S$ be a set of
directions with $0 \in S$. Suppose that the third-order Taylor measure of $\mu(\cdot, t)$ at $x$
satisfies $\varphi^\delta_{\mu, 3}(S) \le B$. Then the third-order Taylor measure of $\nu$ at
$x$ satisfies $\varphi^\delta_{\nu, 3}(S \cap \ker \nabla f(x)) \le B$ and
$$\varphi^\delta_{\nu, 3}(S) \le B + \tfrac12 (\|\nabla f(x)\| \delta)^2 + \tfrac12 \|\nabla
  f(x)\| \delta \, \|\nabla^2 f(x)\| \delta^2.$$
-/
theorem taylorMeasure_halfSqNorm_three_le_of_eq {δ B : ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : f x = t) (hδ : 0 ≤ δ) {S : Set E} (hS : (0 : E) ∈ S)
    (hμ : Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 3 δ S ≤ B) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 3 δ
        (S ∩ {d | fderiv ℝ f x d = 0}) ≤ B ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 3 δ S ≤
        B + (‖fderiv ℝ f x‖ * δ) ^ 2 / 2 +
          ‖fderiv ℝ f x‖ * δ * (‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2) / 2 := by
  constructor
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩
      fun d hd => ?_
    have h := taylorDecrement_three_targetMerit_of_eq hf hc ht d
    have hd0 : fderiv ℝ f x d = 0 := hd.2.2
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit f c t) x) 3 (S := S) ⟨hd.1, hd.2.1⟩
    rw [hd0] at h
    linarith
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS⟩ fun d hd => ?_
    have h := taylorDecrement_three_targetMerit_of_eq hf hc ht d
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit f c t) x) 3 (S := S) hd
    have h1 := abs_fderiv_le (f := f) (x := x) hd.1
    have h2 := abs_iteratedFDeriv_two_le (f := f) (x := x) hd.1
    have hg : (fderiv ℝ f x d) ^ 2 ≤ (‖fderiv ℝ f x‖ * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hgh : fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) ≤
        ‖fderiv ℝ f x‖ * δ * (‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    linarith

end Constrained
