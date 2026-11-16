/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.Multiplier

/-!
# Early termination of the regularization subproblem

Let $H$ be an operator on a real inner product space, $g$ a vector, $\sigma > 0$ and $r > 2$, and
let
$$m^R(s) = \langle g, s \rangle + \tfrac12 \langle s, H s \rangle + \tfrac{\sigma}{r} \|s\|^r$$
be the regularized model. The adaptive-regularization methods of [cartis2022evaluation] need not
minimize $m^R$ exactly. They only require a step $s$ that satisfies the stopping rules (9.3.14) with
constants $\theta_1, \theta_2$:

* (9.3.14a) $m^R(s) \le m^R(0) = 0$;
* (9.3.14b) $\|\nabla m^R(s)\| \le \frac12 \theta_1 \|s\|^2$;
* (9.3.14c) $\lambda_{\min}[\nabla^2 m^R(s)] \ge -\theta_2 \|s\|$.

Theorem 9.3.2 of [cartis2022evaluation] gives a test, which uses only the secular function
$\pi(\lambda) = \|s(\lambda)\|^2$, under which the step $s(\lambda) = -(H + \lambda)^{-1} g$ of a
shift $\lambda \in \mathcal{F} = (\lambda_s, \infty)$ satisfies these rules. This file proves the
theorem, and proves that every global minimizer of $m^R$ satisfies the rules.

## Main definitions

* `Subproblem.RegStoppingRules`: the stopping rules (9.3.14) for a step $s$.

## Main results

* `Subproblem.RegStoppingRules.iff_gradient`: for symmetric $H$, the rules with the gradient of
  $m^R$ written as the Mathlib `gradient`.
* `Subproblem.regStoppingRules_of_shifted`: the rules hold at a solution of a shifted system
  $(H + \lambda) s = -g$ with $H + \lambda$ positive semidefinite, under the conditions on $\|s\|$
  of the proof of Theorem 9.3.2.
* `Subproblem.regStoppingRules_of_isMinOn`: global minimizers satisfy the rules.
* `Subproblem.regStoppingRules_step`: Theorem 9.3.2, the same in terms of $\pi(\lambda)$, with the
  conditions (9.3.15a)–(9.3.15c).

## Implementation notes

* The space $E$ carries the $M$-inner product of the source. So the dual norm $\|\cdot\|_{M^{-1}}$
  of the gradient becomes the norm of $E$, and the generalized eigenvalue
  $\lambda_{\min}[\nabla^2 m^R, M]$ becomes the least value of the quadratic form
  $\langle v, \nabla^2 m^R(s) v \rangle$ on unit vectors.
* The gradient in (9.3.14b) is written as the explicit expression $g + H s + \sigma \|s\|^{r-2} s$,
  which is the gradient of $m^R$ for symmetric $H$ (`Subproblem.hasGradientAt_regModel`).
-/

open Set
open scoped RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **stopping rules for the regularization subproblem**, (9.3.14) of [cartis2022evaluation]. A
step $s$ satisfies them, for $g$, $H$, $\sigma$, $r$ and constants $\theta_1, \theta_2$, if

* (9.3.14a) the model does not increase: $m^R(s) \le m^R(0)$;
* (9.3.14b) $\|g + H s + \sigma \|s\|^{r-2} s\| \le \frac12 \theta_1 \|s\|^2$;
* (9.3.14c) $\langle v, \nabla^2 m^R(s) v \rangle \ge -\theta_2 \|s\| \|v\|^2$ for all $v$, that
  is, the least eigenvalue of the Hessian is at least $-\theta_2 \|s\|$.

The model $m^R$ is `Subproblem.regModel g H σ r`, and the Hessian $\nabla^2 m^R(s)$ is
`Subproblem.regModelHessian H σ r s`. The vector in (9.3.14b) is the gradient of $m^R$ when $H$
is symmetric (`Subproblem.hasGradientAt_regModel`). -/
structure RegStoppingRules (g : E) (H : E →L[ℝ] E) (σ r θ₁ θ₂ : ℝ) (s : E) : Prop where
  /-- (9.3.14a): the model does not increase, $m^R(s) \le m^R(0)$. -/
  decrease : regModel g H σ r s ≤ regModel g H σ r 0
  /-- (9.3.14b): the gradient $g + H s + \sigma \|s\|^{r-2} s$ of the regularized model satisfies
  $\|g + H s + \sigma \|s\|^{r-2} s\| \le \frac12 \theta_1 \|s\|^2$. The form with the Mathlib
  `gradient` is `Subproblem.RegStoppingRules.iff_gradient`. -/
  gradient : ‖g + H s + (σ * ‖s‖ ^ (r - 2)) • s‖ ≤ (1 / 2) * θ₁ * ‖s‖ ^ 2
  /-- (9.3.14c): the Hessian is almost positive semidefinite, $\langle v, \nabla^2 m^R(s) v \rangle
  \ge -\theta_2 \|s\| \|v\|^2$ for all $v$. -/
  curvature : ∀ v, -(θ₂ * ‖s‖) * ‖v‖ ^ 2 ≤ ⟪v, regModelHessian H σ r s v⟫

variable {g : E} {H : E →L[ℝ] E} {σ r θ₁ θ₂ lam : ℝ} {s : E}

/-- The stopping rules with the Mathlib gradient. Let $E$ be complete, let $H$ be symmetric, and let
$r > 1$. Then $s$ satisfies the stopping rules (9.3.14) if and only if $m^R(s) \le m^R(0)$,
$\|\nabla m^R(s)\| \le \frac12 \theta_1 \|s\|^2$, and $\langle v, \nabla^2 m^R(s) v \rangle \ge
-\theta_2 \|s\| \|v\|^2$ for all $v$.

Here $\nabla m^R(s)$ is `_root_.gradient (Subproblem.regModel g H σ r) s`. The proof identifies
it with $g + H s + \sigma \|s\|^{r-2} s$ by `Subproblem.hasGradientAt_regModel`. -/
theorem RegStoppingRules.iff_gradient [CompleteSpace E] (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (hr : 1 < r) :
    RegStoppingRules g H σ r θ₁ θ₂ s ↔
      regModel g H σ r s ≤ regModel g H σ r 0 ∧
        ‖_root_.gradient (regModel g H σ r) s‖ ≤ (1 / 2) * θ₁ * ‖s‖ ^ 2 ∧
        ∀ v, -(θ₂ * ‖s‖) * ‖v‖ ^ 2 ≤ ⟪v, regModelHessian H σ r s v⟫ := by
  rw [(hasGradientAt_regModel hH σ hr s).gradient]
  exact ⟨fun h => ⟨h.decrease, h.gradient, h.curvature⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- **The stopping rules at a shifted solution.** Let $\sigma > 0$ and $r > 2$, and let $s$ solve
the shifted system $(H + \lambda) s = -g$, where $H + \lambda$ is positive semidefinite. Assume
that

* (a) $\frac{\sigma}{r} \|s\|^{r-2} \le \frac{\lambda}{2}$;
* (b) $\bigl|\sigma \|s\|^{r-2} - \lambda\bigr| \le \frac12 \theta_1 \|s\|$;
* (c) $\sigma \|s\|^{r-2} - \lambda \ge -\theta_2 \|s\|$.

Then $s$ satisfies the stopping rules (9.3.14). This is the argument of the proof of Theorem
9.3.2 of [cartis2022evaluation].

Positive semidefiniteness is `LinearMap.IsPositive`, which includes the symmetry of
$H + \lambda$. -/
theorem regStoppingRules_of_shifted (hσ : 0 < σ) (hr : 2 < r)
    (hs : (H + lam • (1 : E →L[ℝ] E)) s = -g)
    (hpos : ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive)
    (ha : σ / r * ‖s‖ ^ (r - 2) ≤ lam / 2) (hb : |σ * ‖s‖ ^ (r - 2) - lam| ≤ (1 / 2) * θ₁ * ‖s‖)
    (hc : -(θ₂ * ‖s‖) ≤ σ * ‖s‖ ^ (r - 2) - lam) : RegStoppingRules g H σ r θ₁ θ₂ s where
  decrease := by
    rw [regModel_eq_of_shifted_general σ r hs, regModel_zero g H σ (by linarith)]
    have h1 := ContinuousLinearMap.inner_apply_nonneg_of_isPositive hpos s
    have h2 : ‖s‖ ^ 2 * (σ / r * ‖s‖ ^ (r - 2) - lam / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
    linarith
  gradient := by
    have hgrad : g + H s + (σ * ‖s‖ ^ (r - 2)) • s = (σ * ‖s‖ ^ (r - 2) - lam) • s := by
      rw [add_apply_eq_of_shifted hs, sub_smul]; abel
    rw [hgrad, norm_smul, Real.norm_eq_abs]
    calc |σ * ‖s‖ ^ (r - 2) - lam| * ‖s‖ ≤ (1 / 2) * θ₁ * ‖s‖ * ‖s‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = (1 / 2) * θ₁ * ‖s‖ ^ 2 := by ring
  curvature v := by
    have h1 := inner_regModelHessian_ge H hσ.le hr.le s v
    have h2 := ContinuousLinearMap.inner_apply_nonneg_of_isPositive hpos v
    have h3 : ⟪v, (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) v⟫ =
        ⟪v, (H + lam • (1 : E →L[ℝ] E)) v⟫ + (σ * ‖s‖ ^ (r - 2) - lam) * ‖v‖ ^ 2 := by
      simp only [add_apply, smul_apply,
        one_apply_eq_self, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq]
      ring
    have h4 : -(θ₂ * ‖s‖) * ‖v‖ ^ 2 ≤ (σ * ‖s‖ ^ (r - 2) - lam) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    linarith

/-- For $x \ge 0$ and $a \in \mathbb{R}$, $(x^2)^{a/2} = x^a$. -/
private theorem sq_rpow_half (x : ℝ) (hx : 0 ≤ x) (a : ℝ) : (x ^ 2) ^ (a / 2) = x ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring

/-- **Global minimizers satisfy the stopping rules.** Let $H$ be symmetric, $\sigma > 0$, $r > 2$,
and $\theta_1, \theta_2 \ge 0$. Then every global minimizer of the regularized model $m^R$ on
$E$ satisfies the stopping rules (9.3.14). This is the remark after (9.3.14) in
[cartis2022evaluation]. -/
theorem regStoppingRules_of_isMinOn (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hσ : 0 < σ) (hr : 2 < r)
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hmin : IsMinOn (regModel g H σ r) univ s) :
    RegStoppingRules g H σ r θ₁ θ₂ s := by
  obtain ⟨hs, hpos⟩ := (isMinOn_regModel_iff hH hσ hr).1 hmin
  refine regStoppingRules_of_shifted hσ hr hs hpos ?_ ?_ ?_
  · have : σ / r ≤ σ / 2 := div_le_div_of_nonneg_left hσ.le two_pos hr.le
    have h0 : 0 ≤ ‖s‖ ^ (r - 2) := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  · simp only [sub_self, abs_zero]; positivity
  · simp only [sub_self]; nlinarith [norm_nonneg s]

variable [FiniteDimensional ℝ E] {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-- **Theorem 9.3.2** of [cartis2022evaluation] (a constructive early termination test). Let $E$ be
finite-dimensional and $H$ symmetric, let $\sigma > 0$ and $r > 2$, and let
$\lambda_c \in \mathcal{F}$, that is, $\lambda_c > \lambda_s = \max(0, -\lambda_1)$. Let
$s = s(\lambda_c)$ and $\pi = \pi(\lambda_c) = \|s\|^2$. If

* (9.3.15a) $\pi \le (r/2)^{2/(r-2)} (\lambda_c / \sigma)^{2/(r-2)}$,
* (9.3.15b) $\bigl|\pi^{(r-2)/2} - \lambda_c / \sigma\bigr| \le \frac{\theta_1}{2\sigma}
  \pi^{1/2}$, and
* (9.3.15c) $\pi^{(r-2)/2} - \lambda_c / \sigma \ge -\frac{\theta_2}{\sigma} \pi^{1/2}$,

then $s$ satisfies the stopping rules (9.3.14).

The step is `Subproblem.step g H lam`, where `lam` stands for $\lambda_c$. The secular function
is `Subproblem.secular`. The proof reduces the three conditions to those of
`Subproblem.regStoppingRules_of_shifted`, using $\pi^{a/2} = \|s\|^a$. -/
theorem regStoppingRules_step (hσ : 0 < σ) (hr : 2 < r) (hlam : shiftThreshold hH < lam)
    (ha : secular g H lam ≤ (r / 2) ^ (2 / (r - 2)) * (lam / σ) ^ (2 / (r - 2)))
    (hb : |secular g H lam ^ ((r - 2) / 2) - lam / σ| ≤
      θ₁ / (2 * σ) * secular g H lam ^ (1 / 2 : ℝ))
    (hc : -(θ₂ / σ) * secular g H lam ^ (1 / 2 : ℝ) ≤ secular g H lam ^ ((r - 2) / 2) - lam / σ) :
    RegStoppingRules g H σ r θ₁ θ₂ (step g H lam) := by
  set s := step g H lam
  have hlam0 : 0 ≤ lam := shiftThreshold_nonneg.trans hlam.le
  have hlam1 : -leftmost hH < lam := neg_leftmost_le_shiftThreshold.trans_lt hlam
  have hn := norm_nonneg s
  -- `π^{(r-2)/2} = ‖s‖^{r-2}` and `π^{1/2} = ‖s‖`
  have hπr : secular g H lam ^ ((r - 2) / 2) = ‖s‖ ^ (r - 2) := sq_rpow_half _ hn _
  have hπ1 : secular g H lam ^ (1 / 2 : ℝ) = ‖s‖ := by
    rw [secular, sq_rpow_half _ hn, Real.rpow_one]
  rw [hπr, hπ1] at hb hc
  refine regStoppingRules_of_shifted hσ hr (step_spec hlam1).1 (isPositive_add_smul_of_le hlam1.le)
    ?_ ?_ ?_
  · -- raise (9.3.15a) to the power `(r-2)/2`
    have hp : 0 < (r - 2) / 2 := by linarith
    have he : 2 / (r - 2) * ((r - 2) / 2) = 1 := by field_simp [show r - 2 ≠ 0 by linarith]
    have h := Real.rpow_le_rpow (sq_nonneg _) ha hp.le
    rw [sq_rpow_half _ hn,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (div_nonneg hlam0 hσ.le),
      he, Real.rpow_one, Real.rpow_one] at h
    have hr0 : 0 < r := by linarith
    calc σ / r * ‖s‖ ^ (r - 2) ≤ σ / r * (r / 2 * (lam / σ)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = lam / 2 := by field_simp
  · have : |σ * ‖s‖ ^ (r - 2) - lam| = σ * |‖s‖ ^ (r - 2) - lam / σ| := by
      rw [← abs_of_pos hσ, ← abs_mul, abs_of_pos hσ]; congr 1; field_simp
    rw [this]
    calc σ * |‖s‖ ^ (r - 2) - lam / σ| ≤ σ * (θ₁ / (2 * σ) * ‖s‖) :=
          mul_le_mul_of_nonneg_left hb hσ.le
      _ = (1 / 2) * θ₁ * ‖s‖ := by field_simp
  · have h := mul_le_mul_of_nonneg_left hc hσ.le
    have e1 : σ * (-(θ₂ / σ) * ‖s‖) = -(θ₂ * ‖s‖) := by field_simp
    have e2 : σ * (‖s‖ ^ (r - 2) - lam / σ) = σ * ‖s‖ ^ (r - 2) - lam := by field_simp
    rw [e1, e2] at h
    exact h

end Subproblem
