/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Optimality.Approximate
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Stability of approximate high-order minimizers

Let $E$ be a real normed space, let $f : E \to \mathbb{R}$, let $S \subseteq E$ be a set of
admissible displacements, and let
$$\phi^\delta_{f,S,j}(x) = \sup_{d \in S,\ \|d\| \le \delta} \bigl(T_j(x, 0) - T_j(x, d)\bigr)$$
be the Taylor-decrement measure, where $T_j(x, d)$ is the Taylor polynomial of $f$ of order $j$ at
$x$ evaluated at the displacement $d$. If $\nabla^j f$ is $L$-Lipschitz near $x$, a small value of
$\phi^\delta_{f,S,j}(x)$ bounds the decrease of $f$ on the displacements $d \in S$ with
$\|d\| \le \delta$. This is Theorem 12.1.8 of [cartis2022evaluation] for $S = E$ without slack, and
Theorem 14.2.1 for a feasible set and an additive slack $\eta$. Applied to the Lagrangian
$f - \langle y, c \rangle$ of an equality-constrained problem, it gives Theorem 14.3.2.

## Main results

* `Optimization.le_of_taylorMeasure_le`: the estimate (12.1.39), with the slack $\eta$.
* `Optimization.le_of_taylorMeasure_le_of_mul_le`: the estimate (14.2.6), and (12.1.35), under the
  radius condition $L \|d\| \le (j + 1) \varepsilon$.
* `Optimization.le_of_taylorMeasure_le_of_lipschitz_zero`: the estimate (14.2.7), and (12.1.36), for
  a constant $\nabla^j f$.
* `Optimization.le_of_lagrangian_taylorMeasure_le`: the estimate (14.3.10) of Theorem 14.3.2, with
  the variants `Optimization.le_of_lagrangian_taylorMeasure_le_of_eq` and
  `Optimization.le_of_lagrangian_taylorMeasure_le_of_eq_zero` for (14.3.12).

## Implementation notes

* The measure $\phi^\delta_{f,S,j}(x)$ is `Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ S`.
* The smoothness and Lipschitz hypotheses are local, on the closed ball of radius $\delta$ about
  $x$, in the form of `Numlib.Analysis.Calculus.MultivariateTaylor.Remainder`. The source assumes
  them on an open neighborhood of radius larger than $\delta_j$, which implies this form.
* The radius condition is written multiplicatively, $L \|d\| \le (j + 1) \varepsilon$, so that the
  case $L = 0$ needs no division.
* Theorem 14.3.2 of [cartis2022evaluation] assumes a "neighbourhood of diameter $\delta_j$". This is
  read as radius $\delta_j$, because otherwise displacements of norm $\delta_j$ leave the
  neighborhood.
* The componentwise Lipschitz constant $L_{c,j}$ of Theorem 14.3.2 is read as the Lipschitz constant
  of the vector-valued derivative $\nabla^j c$, with the operator norm into $F$. With componentwise
  constants an extra factor $\sqrt{m}$ would appear.
-/

open Metric
open scoped Nat InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Optimization

variable {f : E → ℝ} {x : E} {j : ℕ} {δ ε η L : ℝ} {S : Set E}

/-- **Stability of approximate minimizers**, the estimate (12.1.39) of [cartis2022evaluation] with
the slack $\eta$ of Theorem 14.2.1. Let $f$ be $j$ times continuously differentiable at every
point of the closed ball $\bar B(x, \delta)$, and let $\nabla^j f$ be $L$-Lipschitz on
$\bar B(x, \delta)$ with $L \ge 0$. Suppose that
$$\phi^\delta_{f,S,j}(x) \le \frac{\varepsilon \delta^j}{j!} + \eta.$$
Then for every $d \in S$ with $\|d\| \le \delta$,
$$f(x + d) \ge f(x) - \frac{L}{(j + 1)!} \|d\| \delta^j - \frac{\varepsilon \delta^j}{j!} -
  \eta.$$

The measure $\phi^\delta_{f,S,j}(x)$ is `Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ
S`. -/
theorem le_of_taylorMeasure_le (hf : ∀ y ∈ closedBall x δ, ContDiffAt ℝ j f y)
    (hL : IteratedFDerivLipschitzOn f j L (closedBall x δ)) (hL0 : 0 ≤ L)
    (h : taylorMeasure (ftaylorSeries ℝ f x) j δ S ≤ ε * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) :
    f x - L / (j + 1)! * ‖d‖ * δ ^ j - ε * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have hδ : 0 ≤ δ := (norm_nonneg d).trans hd
  have hx : x ∈ closedBall x δ := mem_closedBall_self hδ
  have hxd : x + d ∈ closedBall x δ := by simpa [dist_eq_norm] using hd
  have hrem := abs_sub_taylorPolynomial_le_of_lipschitz (convex_closedBall x δ) hf hL hx hxd
  have hdec := (taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ f x) j
    ⟨by simpa using hd, hdS⟩).trans h
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right] at hdec
  have hpow : ‖d‖ ^ (j + 1) ≤ ‖d‖ * δ ^ j := by
    rw [pow_succ, mul_comm]
    gcongr
  have : L / (j + 1)! * ‖d‖ ^ (j + 1) ≤ L / (j + 1)! * ‖d‖ * δ ^ j := by
    rw [mul_assoc]
    gcongr
  linarith [(abs_le.1 hrem).1]

/-- **Stability with a radius condition**, the estimate (14.2.6) of [cartis2022evaluation], and
(12.1.35) for $S = E$ and $\eta = 0$. Let $f$ be $j$ times continuously differentiable at every
point of $\bar B(x, \delta)$, let $\nabla^j f$ be $L$-Lipschitz on $\bar B(x, \delta)$ with
$L \ge 0$, and suppose that $\phi^\delta_{f,S,j}(x) \le \varepsilon \delta^j / j! + \eta$. Then
for every $d \in S$ with $\|d\| \le \delta$ and $L \|d\| \le (j + 1) \varepsilon$,
$$f(x + d) \ge f(x) - \frac{2 \varepsilon \delta^j}{j!} - \eta.$$

The radius condition is written as a product, so that $L = 0$ needs no division. -/
theorem le_of_taylorMeasure_le_of_mul_le (hf : ∀ y ∈ closedBall x δ, ContDiffAt ℝ j f y)
    (hL : IteratedFDerivLipschitzOn f j L (closedBall x δ)) (hL0 : 0 ≤ L)
    (h : taylorMeasure (ftaylorSeries ℝ f x) j δ S ≤ ε * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hLd : L * ‖d‖ ≤ (j + 1) * ε) :
    f x - 2 * ε * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have h1 := le_of_taylorMeasure_le hf hL hL0 h hdS hd
  have hδ : 0 ≤ δ := (norm_nonneg d).trans hd
  have hfs : ((j + 1)! : ℝ) = (j + 1) * j ! := by push_cast [Nat.factorial_succ]; ring
  have hf0 : (0 : ℝ) < j ! := by positivity
  have hq : L * ‖d‖ / (j + 1)! ≤ ε / j ! := by
    rw [hfs, div_le_div_iff₀ (by positivity) hf0]
    nlinarith
  have : L / (j + 1)! * ‖d‖ * δ ^ j ≤ ε * δ ^ j / j ! :=
    calc L / (j + 1)! * ‖d‖ * δ ^ j = L * ‖d‖ / (j + 1)! * δ ^ j := by ring
      _ ≤ ε / j ! * δ ^ j := by gcongr
      _ = ε * δ ^ j / j ! := by ring
  have e : 2 * ε * δ ^ j / j ! = ε * δ ^ j / j ! + ε * δ ^ j / j ! := by ring
  linarith

/-- **Stability with a constant $j$-th derivative**, the estimate (14.2.7) of
[cartis2022evaluation], and (12.1.36) for $S = E$ and $\eta = 0$. Let $f$ be $j$ times
continuously differentiable at every point of $\bar B(x, \delta)$, let $\nabla^j f$ be constant
on $\bar B(x, \delta)$ (Lipschitz with constant $0$), and suppose that $\phi^\delta_{f,S,j}(x)
\le \varepsilon \delta^j / j! + \eta$. Then for every $d \in S$ with $\|d\| \le \delta$,
$$f(x + d) \ge f(x) - \frac{\varepsilon \delta^j}{j!} - \eta.$$
-/
theorem le_of_taylorMeasure_le_of_lipschitz_zero
    (hf : ∀ y ∈ closedBall x δ, ContDiffAt ℝ j f y)
    (hL : IteratedFDerivLipschitzOn f j 0 (closedBall x δ))
    (h : taylorMeasure (ftaylorSeries ℝ f x) j δ S ≤ ε * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) :
    f x - ε * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  simpa using le_of_taylorMeasure_le hf hL le_rfl h hdS hd

section Lagrangian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {c : E → F} {y : F}
  {ε₀ Lf Lc : ℝ}

/-- For every real $a$, $1 + a \le \sqrt{2} \sqrt{1 + a^2}$; with $a = \|y\|$ this is
$\|(1, y)\| \ge (1 + \|y\|) / \sqrt{2}$. -/
private theorem one_add_le_sqrt_two_mul_sqrt (a : ℝ) : 1 + a ≤ √2 * √(1 + a ^ 2) := by
  rw [← Real.sqrt_mul zero_le_two]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (1 - a)]

/-- The stability estimate (14.3.13) of [cartis2022evaluation] for the Lagrangian, the main step of
Theorem 14.3.2. Let $F$ be a real inner product space, let $f : E \to \mathbb{R}$ and
$c : E \to F$ be $j$ times continuously differentiable at every point of $\bar B(x, \delta)$,
and let $\nabla^j f$ and $\nabla^j c$ be Lipschitz on $\bar B(x, \delta)$ with constants
$L_f \ge 0$ and $L_c \ge 0$. Let $\mathcal{L}(z) = f(z) - \langle y, c(z) \rangle$ and suppose
that
$$\phi^\delta_{\mathcal{L},S,j}(x) \le \frac{\varepsilon \sqrt{1 + \|y\|^2} \, \delta^j}{j!} +
  \eta.$$
Then for every $d \in S$ with $\|d\| \le \delta$ and $\sqrt{2} \max(L_f, L_c) \|d\| \le (j + 1)
\varepsilon$,
$$\mathcal{L}(x + d) \ge \mathcal{L}(x) - \frac{2 \varepsilon \sqrt{1 + \|y\|^2} \,
  \delta^j}{j!} - \eta.$$

The $j$-th derivative of $\mathcal{L}$ is $(L_f + \|y\| L_c)$-Lipschitz. -/
theorem lagrangian_le_of_taylorMeasure_le (hf : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall x δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall x δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (h : taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪y, c z⟫_ℝ) x) j δ S ≤
      ε * √(1 + ‖y‖ ^ 2) * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    f x - ⟪y, c x⟫_ℝ - 2 * ε * √(1 + ‖y‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤
      f (x + d) - ⟪y, c (x + d)⟫_ℝ := by
  set K := √(1 + ‖y‖ ^ 2)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hyc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j (innerSL ℝ y ∘ c) z := fun z hz =>
    (innerSL ℝ y).contDiff.contDiffAt.comp z (hc z hz)
  have hℒ : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j (fun z => f z - ⟪y, c z⟫_ℝ) z := fun z hz =>
    (hf z hz).sub (hyc z hz)
  have hLℒ : IteratedFDerivLipschitzOn (fun z => f z - ⟪y, c z⟫_ℝ) j (Lf + ‖y‖ * Lc)
      (closedBall x δ) := by
    have := hLf.sub ((hLc.continuousLinearMap_comp (innerSL ℝ y) hc)) hf hyc
    rwa [innerSL_apply_norm] at this
  have hMax : Lf + ‖y‖ * Lc ≤ (1 + ‖y‖) * max Lf Lc := by
    nlinarith [le_max_left Lf Lc, le_max_right Lf Lc, norm_nonneg y]
  have hrad : (Lf + ‖y‖ * Lc) * ‖d‖ ≤ (j + 1) * (ε * K) := by
    have h1 := one_add_le_sqrt_two_mul_sqrt ‖y‖
    have hm0 : 0 ≤ max Lf Lc := hLf0.trans (le_max_left _ _)
    calc (Lf + ‖y‖ * Lc) * ‖d‖ ≤ (1 + ‖y‖) * max Lf Lc * ‖d‖ := by gcongr
      _ ≤ √2 * K * max Lf Lc * ‖d‖ := by gcongr
      _ = K * (√2 * max Lf Lc * ‖d‖) := by ring
      _ ≤ K * ((j + 1) * ε) := by gcongr
      _ = (j + 1) * (ε * K) := by ring
  have := le_of_taylorMeasure_le_of_mul_le hℒ hLℒ (by positivity) (ε := ε * K)
    (by simpa [mul_assoc] using h) hdS hd hrad
  convert this using 2
  ring

/-- **Local sufficiency of the Lagrangian for approximate minimizers**, the estimate (14.3.10) of
Theorem 14.3.2 of [cartis2022evaluation]. Let $F$ be a real inner product space, let
$f : E \to \mathbb{R}$ and $c : E \to F$ be $j$ times continuously differentiable at every point
of $\bar B(x, \delta)$, and let $\nabla^j f$ and $\nabla^j c$ be Lipschitz on
$\bar B(x, \delta)$ with constants $L_f \ge 0$ and $L_c \ge 0$. Let
$\|c(x)\| \le \varepsilon_0$, let $\mathcal{L}(z) = f(z) - \langle y, c(z) \rangle$, and suppose
that
$$\phi^\delta_{\mathcal{L},S,j}(x) \le \frac{\varepsilon \|(1, y)\| \, \delta^j}{j!} + \eta,
  \qquad \|(1, y)\| = \sqrt{1 + \|y\|^2}.$$
Then for every $d \in S$ with $\|d\| \le \delta$, $\|c(x + d)\| \le \varepsilon_0$ and $\sqrt{2}
\max(L_f, L_c) \|d\| \le (j + 1) \varepsilon$ (the condition (14.3.11)),
$$f(x + d) \ge f(x) - 2 \varepsilon_0 \|y\| - \frac{2 \varepsilon \|(1, y)\| \, \delta^j}{j!} -
  \eta.$$

The neighborhood of "diameter $\delta_j$" in the source is read as the closed ball of radius
$\delta$, and the Lipschitz constant $L_c$ is that of the vector-valued $\nabla^j c$; see the
module doc comment. -/
theorem le_of_lagrangian_taylorMeasure_le (hf : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall x δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall x δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (hcx : ‖c x‖ ≤ ε₀)
    (h : taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪y, c z⟫_ℝ) x) j δ S ≤
      ε * √(1 + ‖y‖ ^ 2) * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hcd : ‖c (x + d)‖ ≤ ε₀)
    (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    f x - 2 * ε₀ * ‖y‖ - 2 * ε * √(1 + ‖y‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have h1 := lagrangian_le_of_taylorMeasure_le hf hc hLf hLc hLf0 hLc0 h hdS hd hLd
  have h2 : ⟪y, c x⟫_ℝ - ⟪y, c (x + d)⟫_ℝ ≤ 2 * ε₀ * ‖y‖ := by
    rw [← inner_sub_right]
    calc ⟪y, c x - c (x + d)⟫_ℝ ≤ ‖y‖ * ‖c x - c (x + d)‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * (ε₀ + ε₀) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hcx hcd)
      _ = 2 * ε₀ * ‖y‖ := by ring
  linarith

/-- The first case of (14.3.12) of [cartis2022evaluation]: under the hypotheses of
`Optimization.le_of_lagrangian_taylorMeasure_le`, but with $c(x + d) = c(x)$ in place of the
bounds $\|c(x)\| \le \varepsilon_0$ and $\|c(x + d)\| \le \varepsilon_0$,
$$f(x + d) \ge f(x) - \frac{2 \varepsilon \sqrt{1 + \|y\|^2} \, \delta^j}{j!} - \eta.$$
The $\varepsilon_0$ term of Theorem 14.3.2 is dropped. -/
theorem le_of_lagrangian_taylorMeasure_le_of_eq (hf : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall x δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall x δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (h : taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪y, c z⟫_ℝ) x) j δ S ≤
      ε * √(1 + ‖y‖ ^ 2) * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hcd : c (x + d) = c x)
    (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    f x - 2 * ε * √(1 + ‖y‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have h1 := lagrangian_le_of_taylorMeasure_le hf hc hLf hLc hLf0 hLc0 h hdS hd hLd
  rw [hcd] at h1
  linarith

/-- The second case of (14.3.12) of [cartis2022evaluation]: under the hypotheses of
`Optimization.le_of_lagrangian_taylorMeasure_le`, but with $c(x + d) = 0$ and
$\langle y, c(x) \rangle \le 0$ in place of the bounds $\|c(x)\| \le \varepsilon_0$ and
$\|c(x + d)\| \le \varepsilon_0$,
$$f(x + d) \ge f(x) - \frac{2 \varepsilon \sqrt{1 + \|y\|^2} \, \delta^j}{j!} - \eta.$$
The $\varepsilon_0$ term of Theorem 14.3.2 is dropped. -/
theorem le_of_lagrangian_taylorMeasure_le_of_eq_zero
    (hf : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall x δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall x δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (h : taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪y, c z⟫_ℝ) x) j δ S ≤
      ε * √(1 + ‖y‖ ^ 2) * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hcd : c (x + d) = 0) (hyc : ⟪y, c x⟫_ℝ ≤ 0)
    (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    f x - 2 * ε * √(1 + ‖y‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have h1 := lagrangian_le_of_taylorMeasure_le hf hc hLf hLc hLf0 hLc0 h hdS hd hLd
  rw [hcd, inner_zero_right] at h1
  linarith

end Lagrangian

end Optimization
