/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Conn, Gould and Toint, Section 17.1: Practical trust-region parameters

Section 17.1 of [conn2000trust] recommends values for the parameters of the basic trust-region
algorithm: the acceptance thresholds $\eta_1 = 0.05$ and $\eta_2 = 0.9$ for the ratio $\rho$ of
actual to predicted decrease, and the radius factors $\alpha_1 = 2.5$ and $\alpha_2 = 0.25$. After a
very unsuccessful step, the new radius uses a factor that comes from quadratic interpolation along
the step. Let $a$ be the common value and $l$ the common slope of the objective and the model at the
start of the step, and let $f_1$ and $m_1$ be the values of the objective and the model at its end.
The factor $t$ is chosen so that the quadratic interpolants of the objective and of the model along
the step have the ratio of decreases $\eta$ at $t$. This module formalizes these choices and the
practical radius update (17.1.4). The proofs are direct computations.

## Main definitions

* Equation (17.1.1), `ConnGouldToint.Chapter17.recommendedAcceptance`: the thresholds
  $(\eta_1, \eta_2) = (0.05, 0.9)$.
* Equation (17.1.2), `ConnGouldToint.Chapter17.recommendedRadiusFactors`: the factors
  $(\alpha_1, \alpha_2) = (2.5, 0.25)$.
* `ConnGouldToint.Chapter17.quadraticRayInterpolant`: the quadratic $a + l t + (b - a - l) t^2$ with
  value $a$ and slope $l$ at $0$ and value $b$ at $1$.
* Equation (17.1.3), `ConnGouldToint.Chapter17.interpolatedRadiusFactor`: the corrected
  interpolation factor $(1 - \eta) l / ((1 - \eta)(a + l) + \eta m_1 - f_1)$.
* Equation (17.1.4), `ConnGouldToint.Chapter17.practicalRadiusUpdate`: the four-branch radius
  update.

## Main results

* Equation (17.1.3), `ConnGouldToint.Chapter17.interpolatedRadiusFactor_hits_ratio`: at the
  corrected factor, the ratio of the interpolated decreases is $\eta$.
* `ConnGouldToint.Chapter17.printedInterpolation_counterexample`: the printed factor gives a
  different ratio.

## Deviations from the source

* **Equation (17.1.3)** (correction). The factor $1 - \eta_2$ in the denominator multiplies the
  common value and slope only, not the whole denominator. See
  `ConnGouldToint.Chapter17.printedInterpolation_counterexample`.
-/

namespace ConnGouldToint.Chapter17

/-- **Equation (17.1.1)** of [conn2000trust]. The recommended acceptance thresholds for the ratio
$\rho$ of actual to predicted decrease are $(\eta_1, \eta_2) = (0.05, 0.9)$. -/
noncomputable def recommendedAcceptance : ℝ × ℝ := (0.05, 0.9)

/-- **Equation (17.1.2)** of [conn2000trust]. The recommended radius factors are
$(\alpha_1, \alpha_2) = (2.5, 0.25)$. In `ConnGouldToint.Chapter17.practicalRadiusUpdate`,
$\alpha_1$ enlarges and $\alpha_2$ shrinks the step length. -/
noncomputable def recommendedRadiusFactors : ℝ × ℝ := (2.5, 0.25)

/-- Let $a, l, b \in \mathbb{R}$. The **quadratic ray interpolant** is
$$q(t) = a + l t + (b - a - l) t^2,$$
the unique quadratic with $q(0) = a$, $q'(0) = l$ and $q(1) = b$. It supports the interpolation
factor of equation (17.1.3). -/
def quadraticRayInterpolant (a l b t : ℝ) : ℝ :=
  a + l * t + (b - a - l) * t ^ 2

/-- **Equation (17.1.3)** of [conn2000trust], corrected. Let $\eta, a, l, f_1, m_1 \in \mathbb{R}$,
where $a$ and $l$ are the common value and slope of the objective and the model at the start of
the step, and $f_1$ and $m_1$ are the values of the objective and the model at the end of the
step. The **interpolated radius factor** is
$$t = \frac{(1 - \eta)\, l}{(1 - \eta)(a + l) + \eta m_1 - f_1}.$$

**Correction.** The printed formula multiplies the whole denominator $a + l + \eta m_1 - f_1$ by
$1 - \eta$. With that factor the ratio of the interpolated decreases is not $\eta$; see
`ConnGouldToint.Chapter17.printedInterpolation_counterexample`. Here the factor $1 - \eta$
multiplies only the common value $a$ and the slope $l$, and then
`ConnGouldToint.Chapter17.interpolatedRadiusFactor_hits_ratio` holds.

The source uses the threshold $\eta_2$ for $\eta$. When the denominator is $0$, the Lean
division gives $t = 0$. -/
noncomputable def interpolatedRadiusFactor (η a l f₁ m₁ : ℝ) : ℝ :=
  (1 - η) * l / ((1 - η) * (a + l) + η * m₁ - f₁)

/-- **Equation (17.1.3)** of [conn2000trust], the defining property of the corrected factor. Let
$\eta, a, l, f_1, m_1 \in \mathbb{R}$, let $t$ be the interpolated radius factor, and let $q_f$
and $q_m$ be the quadratic ray interpolants with value $a$ and slope $l$ at $0$ and values $f_1$
and $m_1$ at $1$. If the denominator $(1 - \eta)(a + l) + \eta m_1 - f_1$ is nonzero and
$a - q_m(t) \neq 0$, then
$$\frac{a - q_f(t)}{a - q_m(t)} = \eta.$$

The interpolants are `ConnGouldToint.Chapter17.quadraticRayInterpolant` and the factor is
`ConnGouldToint.Chapter17.interpolatedRadiusFactor`. -/
theorem interpolatedRadiusFactor_hits_ratio (η a l f₁ m₁ : ℝ)
    (hden : (1 - η) * (a + l) + η * m₁ - f₁ ≠ 0)
    (hpred : a - quadraticRayInterpolant a l m₁ (interpolatedRadiusFactor η a l f₁ m₁) ≠ 0) :
    let t := interpolatedRadiusFactor η a l f₁ m₁
    (a - quadraticRayInterpolant a l f₁ t) / (a - quadraticRayInterpolant a l m₁ t) = η := by
  let t := interpolatedRadiusFactor η a l f₁ m₁
  change (a - quadraticRayInterpolant a l f₁ t) /
    (a - quadraticRayInterpolant a l m₁ t) = η
  rw [div_eq_iff hpred]
  have ht : ((1 - η) * (a + l) + η * m₁ - f₁) * t = (1 - η) * l := by
    dsimp [t, interpolatedRadiusFactor]
    rw [mul_comm, div_mul_cancel₀ _ hden]
  unfold quadraticRayInterpolant
  linear_combination t * ht

/-- The printed form of equation (17.1.3) of [conn2000trust] does not give the target ratio. Take
$\eta = 1/2$, $a = 0$, $l = -1$, $f_1 = 1$ and $m_1 = -1$, and let $t = (1 - \eta) l / ((1 -
\eta)(a + l + \eta m_1 - f_1)) = 2/5$ be the printed factor. Then the ratio
$(a - q_f(t)) / (a - q_m(t))$ of the interpolated decreases is $1/5 \neq \eta$.

The interpolants $q_f$ and $q_m$ are `ConnGouldToint.Chapter17.quadraticRayInterpolant` with end
values $f_1$ and $m_1$. This shows the correction in
`ConnGouldToint.Chapter17.interpolatedRadiusFactor`. -/
theorem printedInterpolation_counterexample :
    let η : ℝ := 1 / 2
    let t : ℝ := ((1 - η) * (-1)) / ((1 - η) * (0 + (-1) + η * (-1) - 1))
    (0 - quadraticRayInterpolant 0 (-1) 1 t) / (0 - quadraticRayInterpolant 0 (-1) (-1) t) ≠ η := by
  norm_num [quadraticRayInterpolant]

/-- **Equation (17.1.4)** of [conn2000trust]. Let $\eta_1, \eta_2, \alpha_1, \alpha_2 \in
\mathbb{R}$ be the parameters, $\rho$ the ratio of actual to predicted decrease, $\Delta$ the
current radius, $\|s\|$ the step length and $\gamma_{\mathrm{bad}}$ the interpolated factor. The
**practical radius update** is
$$\Delta^+ = \begin{cases} \max\{\alpha_1 \|s\|, \Delta\} & \text{if } \rho \ge \eta_2, \\
  \Delta & \text{if } \eta_1 \le \rho < \eta_2, \\ \alpha_2 \|s\| & \text{if } 0 \le \rho <
  \eta_1, \\ \min\{\alpha_2 \|s\|, \max\{0.0625, \gamma_{\mathrm{bad}}\} \Delta\} & \text{if }
  \rho < 0. \end{cases}$$

The step length is the argument `length`. The branches are tested in this order, so the
definition needs no hypotheses on the parameters. -/
noncomputable def practicalRadiusUpdate (η₁ η₂ α₁ α₂ ρ Δ length γbad : ℝ) : ℝ :=
  if η₂ ≤ ρ then max (α₁ * length) Δ
  else if η₁ ≤ ρ then Δ
  else if 0 ≤ ρ then α₂ * length
  else min (α₂ * length) (max 0.0625 γbad * Δ)

end ConnGouldToint.Chapter17
