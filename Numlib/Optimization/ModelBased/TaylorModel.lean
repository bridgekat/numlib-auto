/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.PowRegularizedModel
import Numlib.Optimization.ModelBased.QuadraticModel

/-!
# Regularized Taylor models

Let $E$ be a real inner product space and let $D$ be derivative data on $E$: a sequence of
continuous multilinear forms $D_i$, where $D_i$ takes $i$ arguments in $E$. Its Taylor sum of degree
$p$ is $T_p(s) = \sum_{i \le p} \frac{1}{i!} D_i[s]^i$. For the exact jet of a function $f$ at $x$,
$T_p(s) = T_{f,p}(x, s)$ is the Taylor polynomial of $f$ at $x$; inexact derivative data give the
models of Chapter 13 of [cartis2022evaluation]. The adaptive-regularization methods AR1 (2.4.1), AR2
(3.3.1), ARp (4.1.2) and ARqp (12.2.23) of [cartis2022evaluation], and their inexact variants of
Chapter 13, minimize at each iteration the **regularized Taylor model**
$$m(s) = T_p(s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1}.$$
It is the case $r = p + 1$ of the model with a real exponent in
`Numlib.Optimization.ModelBased.PowRegularizedModel`.

All estimates here are for one iteration, with point $x$, weight $\sigma$ and step $s$, and with
explicit constants. They assume that $\nabla^p f$ is Lipschitz on a convex set $C$ that contains $x$
and $x + s$. They bound the reduction ratio, the gradient and the least curvature of $f$ at the
trial point $x + s$, and the difference between the derivatives of $f$ and of the model. In finite
dimension, the model has global minimizers.

## Main definitions

* `Optimization.regularizedModel`: the model $m(s) = T_p(s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1}$.

## Main results

* `Optimization.lt_taylorDecrement_of_regularizedModel_lt`: if $m(s) < m(0)$, then $T_p(0) -
  T_p(s) > \frac{\sigma}{(p+1)!} \|s\|^{p+1}$, as in Lemmas 3.3.1 and 4.1.1 of
  [cartis2022evaluation].
* `Optimization.abs_reductionRatio_sub_one_le_of_lipschitz` and
  `Optimization.le_reductionRatio_of_lipschitz`: the ratio estimate behind Lemmas 2.4.2, 3.3.2 and
  4.1.2 of [cartis2022evaluation]. A parameter $c$ enters through the decrease
  $T_p(0) - T_p(s) \ge c \sigma \|s\|^{p+1}$; Lemma 4.1.1 gives $c = 1/(p+1)!$, and the exact AR1
  step gives $c = 1$.
* `Optimization.norm_gradient_add_le_of_lipschitz`: $\|\nabla f(x + s)\| \le \frac{L}{2} \|s\|^2 +
  \|\nabla f(x) + \nabla^2 f(x) s\|$.
* `Optimization.norm_fderiv_le_of_regularizedModel` and
  `Optimization.minCurvature_ge_of_regularizedModel`: the step bounds of Lemmas 3.3.3, 3.3.8 and
  4.1.3 of [cartis2022evaluation], (4.1.24)–(4.1.29).
* `Optimization.abs_iteratedFDeriv_apply_le_of_regularizedModel`: the comparison (4.1.30), (6.2.23)
  of the derivatives of $f$ and of $m$ for every order $j \le p$.
* `Optimization.exists_isMinOn_regularizedModel`: in finite dimension, the model has a global
  minimizer.
* `Optimization.regularizedModel_two_eq_regModel`: for $p = 2$, the model is the cubic
  regularization model `Subproblem.regModel` of Chapters 8–10 of [cartis2022evaluation].

## Implementation notes

* The derivative data $D$ is a `FormalMultilinearSeries ℝ E ℝ`, and $T_p$ is
  `FormalMultilinearSeries.taylorSum D p`. The forms $D_i$ need not be symmetric. The exact jet of
  $f$ at $x$ is `ftaylorSeries ℝ f x`.
* The equality with the model of real exponent is
  `Optimization.regularizedModel_eq_powRegularizedModel`.
* The variants whose names end in `Anchored` or `_anchored` need $\nabla^p f$ to be Lipschitz only
  at $x$: $\|\nabla^p f(y) - \nabla^p f(x)\| \le L \|y - x\|$ for $y \in C$. This is the condition
  (14.2.9) of [cartis2022evaluation].
-/

open Set Filter
open scoped Nat RealInnerProductSpace

namespace Optimization

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **regularized Taylor model** of adaptive-regularization methods, (2.4.1), (3.3.1), (4.1.2)
and (12.2.23) of [cartis2022evaluation]:
$$m(s) = T_p(s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1},$$
where $T_p$ is the Taylor sum of degree $p$ of the derivative data $D$. -/
noncomputable def regularizedModel (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) (s : E) :
    ℝ :=
  D.taylorSum p s + σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)

variable (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ)

/-- The model is $m(s) = T_p(s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1}$. -/
theorem regularizedModel_def (s : E) :
    regularizedModel D p σ s = D.taylorSum p s + σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := rfl

/-- The model at the zero step is $m(0) = T_p(0)$. -/
@[simp]
theorem regularizedModel_zero_right : regularizedModel D p σ 0 = D.taylorSum p 0 := by
  simp [regularizedModel_def]

/-- For the exact jet of $f$ at $x$, the model at the zero step is $m(0) = f(x)$. -/
theorem regularizedModel_ftaylorSeries_zero_right (f : E → ℝ) (x : E) :
    regularizedModel (ftaylorSeries ℝ f x) p σ 0 = f x := by
  rw [regularizedModel_zero_right, ← taylorPolynomial_eq_taylorSum, taylorPolynomial_zero_right]

/-- The regularized Taylor model is the model with the real exponent $r = p + 1$,
`Optimization.powRegularizedModel D p σ (p + 1)`. -/
theorem regularizedModel_eq_powRegularizedModel :
    regularizedModel D p σ = powRegularizedModel D p σ ((p : ℝ) + 1) := by
  funext s
  rw [regularizedModel_def, powRegularizedModel_def, realFactorial_natCast_add_one,
    show ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]

/-- The model is the sum of the Taylor sum $T_p$ and the function
$s \mapsto \frac{\sigma}{(p+1)!} \|s\|^{p+1}$. -/
theorem regularizedModel_eq_add :
    regularizedModel D p σ =
      D.taylorSum p + fun s : E => (σ / ((p + 1)! : ℝ)) • ‖s‖ ^ (p + 1) := by
  funext s
  simp [regularizedModel_def, smul_eq_mul]

/-- The model is continuous. -/
theorem continuous_regularizedModel : Continuous (regularizedModel D p σ) :=
  ((D.contDiff_taylorSum p (n := 0)).continuous).add (continuous_const.mul (by fun_prop))

variable {D p σ}

/-- Lemmas 3.3.1 and 4.1.1 of [cartis2022evaluation], bound (4.1.18). If $m(s) \le m(0)$, then
$$T_p(0) - T_p(s) \ge \frac{\sigma}{(p+1)!} \|s\|^{p+1}.$$
-/
theorem taylorDecrement_ge_of_regularizedModel_le {s : E}
    (h : regularizedModel D p σ s ≤ regularizedModel D p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ D.taylorDecrement p s := by
  rw [regularizedModel_zero_right, regularizedModel_def] at h
  rw [FormalMultilinearSeries.taylorDecrement]
  linarith

/-- Lemmas 3.3.1 and 4.1.1 of [cartis2022evaluation], strict form. Let $D$ be derivative data on a
real inner product space, $p \in \mathbb{N}$ and $\sigma \in \mathbb{R}$. If the step $s$
strictly decreases the model, $m(s) < m(0)$, as in condition (4.1.10), then
$$T_p(0) - T_p(s) > \frac{\sigma}{(p+1)!} \|s\|^{p+1}.$$

The left side is `FormalMultilinearSeries.taylorDecrement D p s`. -/
theorem lt_taylorDecrement_of_regularizedModel_lt {s : E}
    (h : regularizedModel D p σ s < regularizedModel D p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) < D.taylorDecrement p s := by
  rw [regularizedModel_zero_right, regularizedModel_def] at h
  rw [FormalMultilinearSeries.taylorDecrement]
  linarith

/-- A step that strictly decreases the model is nonzero: if $m(s) < m(0)$, then $s \neq 0$. -/
theorem ne_zero_of_regularizedModel_lt {s : E}
    (h : regularizedModel D p σ s < regularizedModel D p σ 0) : s ≠ 0 := by
  rintro rfl
  exact lt_irrefl _ h

/-- On a real inner product space, the function $y \mapsto \|y\|^{p+1}$ is $j$ times continuously
differentiable at $s$ if $j \le p$ or $s \neq 0$. -/
theorem contDiffAt_norm_pow_succ {j : ℕ} {s : E} (hj : j ≤ p ∨ s ≠ 0) :
    ContDiffAt ℝ j (fun y : E => ‖y‖ ^ (p + 1)) s := by
  rcases hj with hj | hs
  · have := (contDiff_norm_pow (E := E) (r := p + 1) (by omega)).contDiffAt (x := s)
    rw [Nat.add_sub_cancel] at this
    exact this.of_le (by exact_mod_cast hj)
  · exact (contDiffAt_norm_pow (p + 1) hs).of_le le_top

/-- The model is $p$ times continuously differentiable. -/
theorem contDiff_regularizedModel : ContDiff ℝ p (regularizedModel D p σ) := by
  rw [regularizedModel_eq_add]
  have := contDiff_norm_pow (E := E) (r := p + 1) (by omega)
  rw [Nat.add_sub_cancel] at this
  exact (D.contDiff_taylorSum p).add (this.const_smul _)

/-- **Derivatives of the model**, from the proof of Lemma 4.1.3 of [cartis2022evaluation]. Let
$j \in \mathbb{N}$ and $s \in E$ with $j \le p$ or $s \neq 0$. Then
$$\nabla^j m(s) = \nabla^j T_p(s) + \frac{\sigma}{(p+1)!} \nabla^j
  \big(\|\cdot\|^{p+1}\big)(s).$$

The derivatives are `iteratedFDeriv`. -/
theorem iteratedFDeriv_regularizedModel {j : ℕ} {s : E} (hj : j ≤ p ∨ s ≠ 0) :
    iteratedFDeriv ℝ j (regularizedModel D p σ) s =
      iteratedFDeriv ℝ j (D.taylorSum p) s +
        (σ / ((p + 1)! : ℝ)) • iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ (p + 1)) s := by
  have hN := contDiffAt_norm_pow_succ (p := p) hj
  rw [regularizedModel_eq_add, iteratedFDeriv_add_apply (D.contDiff_taylorSum p).contDiffAt
    (hN.const_smul _), iteratedFDeriv_const_smul_apply' hN]

/-- The derivative of the model, (3.3.2) of [cartis2022evaluation] and the proof of Lemma 4.1.3. If
$p \ge 1$, then for every $s$ the model has the derivative
$$\nabla m(s) = \nabla T_p(s) + \frac{\sigma}{p!} \|s\|^{p-1} s,$$
where the vector $\|s\|^{p-1} s$ acts by the inner product. -/
theorem hasFDerivAt_regularizedModel (hp : 1 ≤ p) (s : E) :
    HasFDerivAt (regularizedModel D p σ)
      (fderiv ℝ (D.taylorSum p) s + (σ / (p ! : ℝ) * ‖s‖ ^ (p - 1)) • innerSL ℝ s) s := by
  rw [regularizedModel_eq_powRegularizedModel]
  have h := hasFDerivAt_powRegularizedModel (D := D) (p := p) (σ := σ)
    (r := (p : ℝ) + 1) (by have : (1 : ℝ) ≤ p := (by exact_mod_cast hp); linarith) s
  have h1 : (p : ℝ) + 1 - 1 = (p : ℕ) := by ring
  have h2 : (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp]; push_cast; ring
  rwa [h1, h2, realFactorial_natCast, Real.rpow_natCast] at h

/-- The **gradient of the model**, (3.3.2) and (4.1.26) of [cartis2022evaluation]. Let $D$ be
derivative data on a real inner product space, $\sigma \in \mathbb{R}$ and $p \ge 1$. Then for
every $s$,
$$\nabla m(s) = \nabla T_p(s) + \frac{\sigma}{p!} \|s\|^{p-1} s.$$

The statement is about the Fréchet derivative `fderiv`. The vector $\|s\|^{p-1} s$ acts by the
inner product, through `innerSL ℝ s`. -/
theorem fderiv_regularizedModel (hp : 1 ≤ p) (s : E) :
    fderiv ℝ (regularizedModel D p σ) s =
      fderiv ℝ (D.taylorSum p) s + (σ / (p ! : ℝ) * ‖s‖ ^ (p - 1)) • innerSL ℝ s :=
  (hasFDerivAt_regularizedModel hp s).fderiv

/-- Let $f$ be $p$ times continuously differentiable at $x$ with $p \ge 1$. For the exact jet of $f$
at $x$, the derivative of the model at the zero step is the derivative of $f$ at $x$:
$\nabla m(0) = \nabla f(x)$. -/
theorem fderiv_regularizedModel_ftaylorSeries_zero {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hp : 1 ≤ p) :
    fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) 0 = fderiv ℝ f x := by
  rw [fderiv_regularizedModel hp, map_zero, smul_zero, add_zero]
  ext v
  have h := congrArg (fun A => A (fun _ => v)) (iteratedFDeriv_taylorPolynomial_zero hf hp)
  simpa [iteratedFDeriv_one_apply, taylorPolynomial_eq_taylorSum] using h

/-- Let $f$ be $p$ times continuously differentiable at $x$ with $p \ge 2$. For the exact jet of $f$
at $x$, the second derivative of the model at the zero step is the second derivative of $f$ at
$x$: $\nabla^2 m(0) = \nabla^2 f(x)$.

The regularization term has second derivative $0$ at $0$, because $p + 1 > 2$. -/
theorem iteratedFDeriv_two_regularizedModel_ftaylorSeries_zero {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hp : 2 ≤ p) :
    iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) 0 =
      iteratedFDeriv ℝ 2 f x := by
  have h2 : ((2 : ℕ) : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hp
  rw [iteratedFDeriv_regularizedModel (Or.inl hp), ← taylorPolynomial_eq_taylorSum,
    iteratedFDeriv_taylorPolynomial_zero hf hp, NormPowIteratedFDeriv.norm_pow_eq_normRpow,
    iteratedFDeriv_normRpow_zero h2, smul_zero, add_zero]

end Model

section Estimates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {p : ℕ} {L σ : ℝ} {C : Set E} {x s : E}

/-- **The ratio estimate, with an anchored Lipschitz condition.** Let $E$ be a real inner product
space, $C \subseteq E$ convex with $x, x + s \in C$ and $s \neq 0$, and let
$f : E \to \mathbb{R}$ be $p$ times continuously differentiable at every point of $C$. Suppose
that $\nabla^p f$ is Lipschitz at $x$ on $C$ with constant $L$,
$$\|\nabla^p f(y) - \nabla^p f(x)\| \le L \|y - x\| \quad \text{for all } y \in C,$$
which is the condition (14.2.9) of [cartis2022evaluation]. Let $c > 0$ and $\sigma > 0$, and
suppose that the Taylor decrement satisfies $T_{f,p}(x, 0) - T_{f,p}(x, s) \ge c \sigma
\|s\|^{p+1}$. Then the ratio $\rho = (f(x) - f(x + s)) / (T_{f,p}(x, 0) - T_{f,p}(x, s))$
satisfies
$$|\rho - 1| \le \frac{L}{(p+1)! \, c \, \sigma}.$$

This is `Optimization.abs_reductionRatio_sub_one_le_of_lipschitz` with a weaker Lipschitz
condition. -/
theorem abs_reductionRatio_sub_one_le_of_lipschitzAnchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ L * ‖y - x‖) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : s ≠ 0) {c : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hdec : c * σ * ‖s‖ ^ (p + 1) ≤ (ftaylorSeries ℝ f x).taylorDecrement p s) :
    |reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) - 1| ≤
      L / ((p + 1)! * c * σ) := by
  set Δ := (ftaylorSeries ℝ f x).taylorDecrement p s
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs
  have hΔ : 0 < Δ := lt_of_lt_of_le (by positivity) hdec
  have hT : |f (x + s) - taylorPolynomial f p x s| ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
    rw [← Real.norm_eq_abs]
    exact norm_sub_taylorPolynomial_le_of_lipschitzAnchored hC hf hL hx hxs
  have hL0 : 0 ≤ L := nonneg_of_abs_le_div_mul_pow (by positivity) hspos hT
  refine abs_reductionRatio_sub_one_le hΔ ?_
  have heq : f (x + s) - (f x - Δ) = f (x + s) - taylorPolynomial f p x s := by
    simp only [Δ, FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
      taylorPolynomial_zero_right]
    ring
  rw [heq]
  calc |f (x + s) - taylorPolynomial f p x s| ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := hT
    _ = L / ((p + 1)! * c * σ) * (c * σ * ‖s‖ ^ (p + 1)) := by
        field_simp
    _ ≤ L / ((p + 1)! * c * σ) * Δ := by gcongr

/-- **The ratio estimate** behind Lemmas 2.4.2, 3.3.2 and 4.1.2 of [cartis2022evaluation]. Let $E$
be a real inner product space, $C \subseteq E$ convex with $x, x + s \in C$ and $s \neq 0$, and
let $f : E \to \mathbb{R}$ be $p$ times continuously differentiable at every point of $C$, with
$\nabla^p f$ Lipschitz on $C$ with constant $L$. Let $c > 0$ and $\sigma > 0$, and suppose that
the Taylor decrement satisfies
$$T_{f,p}(x, 0) - T_{f,p}(x, s) \ge c \sigma \|s\|^{p+1}.$$
Then the ratio $\rho = (f(x) - f(x + s)) / (T_{f,p}(x, 0) - T_{f,p}(x, s))$ satisfies
$$|\rho - 1| \le \frac{L}{(p+1)! \, c \, \sigma}.$$

Lemma 4.1.1 gives $c = 1/(p+1)!$, and then $|\rho - 1| \le L / \sigma$. The exact AR1 step gives
$c = 1$. The Lipschitz condition is `IteratedFDerivLipschitzOn f p L C`. -/
theorem abs_reductionRatio_sub_one_le_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : s ≠ 0) {c : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hdec : c * σ * ‖s‖ ^ (p + 1) ≤ (ftaylorSeries ℝ f x).taylorDecrement p s) :
    |reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) - 1| ≤
      L / ((p + 1)! * c * σ) :=
  abs_reductionRatio_sub_one_le_of_lipschitzAnchored hC hf
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hL y hy x hx) hx hxs hs hc hσ hdec

/-- **Very successful iterations, with an anchored Lipschitz condition.** Under the hypotheses of
`Optimization.abs_reductionRatio_sub_one_le_of_lipschitzAnchored`, in which $\nabla^p f$ is
Lipschitz only at $x$ as in the condition (14.2.9) of [cartis2022evaluation], let
$\eta \in \mathbb{R}$ with
$$L \le (p+1)! \, c \, \sigma \, (1 - \eta).$$
Then $\rho \ge \eta$. -/
theorem le_reductionRatio_of_lipschitzAnchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ L * ‖y - x‖) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : s ≠ 0) {c : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hdec : c * σ * ‖s‖ ^ (p + 1) ≤ (ftaylorSeries ℝ f x).taylorDecrement p s) {η : ℝ}
    (hη : L ≤ (p + 1)! * c * σ * (1 - η)) :
    η ≤ reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) := by
  have h := abs_reductionRatio_sub_one_le_of_lipschitzAnchored hC hf hL hx hxs hs hc hσ hdec
  have hpos : (0 : ℝ) < (p + 1)! * c * σ := by positivity
  have : L / ((p + 1)! * c * σ) ≤ 1 - η := by
    rw [div_le_iff₀ hpos]; linarith
  linarith [neg_abs_le (reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) - 1)]

/-- **Very successful iterations**, the step that forces a very successful iteration in Lemmas
2.4.2, 3.3.2 and 4.1.2 of [cartis2022evaluation]. Under the hypotheses of
`Optimization.abs_reductionRatio_sub_one_le_of_lipschitz`, let $\eta \in \mathbb{R}$ with
$$L \le (p+1)! \, c \, \sigma \, (1 - \eta).$$
Then $\rho \ge \eta$.

With $c = 1/(p+1)!$, the condition is $\sigma \ge L / (1 - \eta)$ when $\eta < 1$. -/
theorem le_reductionRatio_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : s ≠ 0) {c : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hdec : c * σ * ‖s‖ ^ (p + 1) ≤ (ftaylorSeries ℝ f x).taylorDecrement p s) {η : ℝ}
    (hη : L ≤ (p + 1)! * c * σ * (1 - η)) :
    η ≤ reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) :=
  le_reductionRatio_of_lipschitzAnchored hC hf
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hL y hy x hx) hx hxs hs hc hσ hdec hη

/-- The gradient at the trial point and the gradient of the Taylor polynomial, Lemma 3.3.7 of
[cartis2022evaluation] with the step condition (3.3.23) on $\nabla_s T_{f,p}$ instead of
$\nabla m$. Let $E$ be a real inner product space, $C \subseteq E$ convex with $x, x + s \in C$,
and let $f : E \to \mathbb{R}$ be $p$ times continuously differentiable at every point of $C$,
with $p \ge 1$ and $\nabla^p f$ Lipschitz on $C$ with constant $L$. Then
$$\|\nabla f(x + s)\| \le \frac{L}{p!} \|s\|^p + \|\nabla_s T_{f,p}(x, s)\|.$$

Both sides use the norms of the Fréchet derivatives `fderiv ℝ f (x + s)` and
`fderiv ℝ (taylorPolynomial f p x) s`. -/
theorem norm_fderiv_le_of_taylorPolynomial (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 1 ≤ p) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hxs : x + s ∈ C) :
    ‖fderiv ℝ f (x + s)‖ ≤ L / (p ! : ℝ) * ‖s‖ ^ p + ‖fderiv ℝ (taylorPolynomial f p x) s‖ := by
  have hT := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz hC hf hL hx hxs hp
  rw [norm_iteratedFDeriv_one_sub, Nat.sub_add_cancel hp] at hT
  calc ‖fderiv ℝ f (x + s)‖ = ‖(fderiv ℝ f (x + s) - fderiv ℝ (taylorPolynomial f p x) s) +
        fderiv ℝ (taylorPolynomial f p x) s‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (by gcongr)

/-- The gradient at the trial point for $p = 2$, in vector form. Let $E$ be a real Hilbert space,
$C \subseteq E$ convex with $x, x + s \in C$, and let $f : E \to \mathbb{R}$ be twice
continuously differentiable at every point of $C$, with $\nabla^2 f$ Lipschitz on $C$ with
constant $L$. Then
$$\|\nabla f(x + s)\| \le \frac{L}{2} \|s\|^2 + \|\nabla f(x) + \nabla^2 f(x) s\|.$$

This is the step bound behind Lemmas 3.4.3, 3.4.9 and 3.5.2 of [cartis2022evaluation]. The
Hessian $\nabla^2 f(x)$ is `Optimization.hessianOperator f x`. -/
theorem norm_gradient_add_le_of_lipschitz [CompleteSpace E] (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 2 f y) (hL : IteratedFDerivLipschitzOn f 2 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) :
    ‖gradient f (x + s)‖ ≤ L / 2 * ‖s‖ ^ 2 + ‖gradient f x + hessianOperator f x s‖ := by
  have hfx := hf x hx
  have h := norm_fderiv_le_of_taylorPolynomial hC hf (by norm_num : 1 ≤ 2) hL hx hxs
  have hT : taylorPolynomial f 2 x =
      fun s => f x + Subproblem.quadModel (gradient f x) (hessianOperator f x) s :=
    funext fun s => taylorPolynomial_two_eq_quadModel hfx s
  have hd : fderiv ℝ (taylorPolynomial f 2 x) s =
      innerSL ℝ (gradient f x + hessianOperator f x s) := by
    rw [hT]
    exact ((Subproblem.hasFDerivAt_quadModel (hessianOperator_isSymmetric hfx) s).const_add
      (f x)).fderiv
  rw [hd, innerSL_apply_norm, ← norm_gradient_eq] at h
  norm_num [Nat.factorial] at h
  rw [norm_gradient_eq]
  linarith [norm_gradient_eq f (x + s)]

/-- **Step bound, first order**, (4.1.24)–(4.1.26) and Lemma 3.3.3 of [cartis2022evaluation]. Let
$E$ be a real inner product space, $C \subseteq E$ convex with $x, x + s \in C$, and let
$f : E \to \mathbb{R}$ be $p$ times continuously differentiable at every point of $C$, with
$p \ge 1$ and $\nabla^p f$ Lipschitz on $C$ with constant $L$. Let $\sigma \ge 0$ and let $m$ be
the regularized Taylor model of $f$ at $x$. Then
$$\|\nabla f(x + s)\| \le \frac{L + \sigma}{p!} \|s\|^p + \|\nabla m(s)\|.$$

Both sides use the norms of Fréchet derivatives. -/
theorem norm_fderiv_le_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 1 ≤ p) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) :
    ‖fderiv ℝ f (x + s)‖ ≤ (L + σ) / (p ! : ℝ) * ‖s‖ ^ p +
      ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ := by
  have hp' : (1 : ℝ) < (p : ℝ) + 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h := norm_fderiv_le_of_powRegularizedModel hC hf hp zero_le_one hL.holderOn hx hxs hσ hp'
  rw [← regularizedModel_eq_powRegularizedModel] at h
  have h1 : holderFactorial (p - 1) 1 = (p ! : ℝ) := by
    rw [holderFactorial_one_right, Nat.sub_add_cancel hp]
  have h2 : ‖s‖ ^ (((p - 1 : ℕ) : ℝ) + 1) = ‖s‖ ^ p := by
    rw [show ((p - 1 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) by rw [Nat.cast_sub hp]; push_cast; ring,
      Real.rpow_natCast]
  have h3 : realFactorial ((p : ℝ) + 1 - 1) = (p ! : ℝ) := by
    rw [add_sub_cancel_right, realFactorial_natCast]
  have h4 : ‖s‖ ^ ((p : ℝ) + 1 - 1) = ‖s‖ ^ p := by
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [h1, h2, h3, h4] at h
  calc ‖fderiv ℝ f (x + s)‖ ≤ L / (p ! : ℝ) * ‖s‖ ^ p + σ / (p ! : ℝ) * ‖s‖ ^ p +
        ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ := h
    _ = _ := by ring

/-- **Step bound, second order**, (4.1.27)–(4.1.29) and Lemma 3.3.8 of [cartis2022evaluation]. Let
$E$ be a real inner product space, $C \subseteq E$ convex with $x, x + s \in C$, and let
$f : E \to \mathbb{R}$ be $p$ times continuously differentiable at every point of $C$, with
$p \ge 2$ and $\nabla^p f$ Lipschitz on $C$ with constant $L$. Let $\sigma \ge 0$ and let $m$ be
the regularized Taylor model of $f$ at $x$. Then
$$\lambda_{\min}[\nabla^2 f(x + s)] \ge \lambda_{\min}[\nabla^2 m(s)] - \frac{L +
  \sigma}{(p-1)!} \|s\|^{p-1}.$$

Here $\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d, d]$ is `minCurvature A` for a bilinear form $A$. -/
theorem minCurvature_ge_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 2 ≤ p) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) :
    minCurvature (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) -
        (L + σ) / ((p - 1)! : ℝ) * ‖s‖ ^ (p - 1) ≤
      minCurvature (iteratedFDeriv ℝ 2 f (x + s)) := by
  have hp' : (2 : ℝ) ≤ (p : ℝ) + 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h := minCurvature_ge_of_powRegularizedModel hC hf hp zero_le_one hL.holderOn hx hxs hσ hp'
  rw [← regularizedModel_eq_powRegularizedModel] at h
  have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h1 : holderFactorial (p - 2) 1 = ((p - 1)! : ℝ) := by
    rw [holderFactorial_one_right]; congr 2; omega
  have h2 : ‖s‖ ^ (((p - 2 : ℕ) : ℝ) + 1) = ‖s‖ ^ (p - 1) := by
    rw [show ((p - 2 : ℕ) : ℝ) + 1 = ((p - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub hp, hc]; push_cast; ring, Real.rpow_natCast]
  have h3 : realFactorial ((p : ℝ) + 1 - 2) = ((p - 1)! : ℝ) := by
    rw [show (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) by rw [hc]; ring, realFactorial_natCast]
  have h4 : ‖s‖ ^ ((p : ℝ) + 1 - 2) = ‖s‖ ^ (p - 1) := by
    rw [show (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) by rw [hc]; ring, Real.rpow_natCast]
  rw [h1, h2, h3, h4] at h
  have : (L + σ) / ((p - 1)! : ℝ) * ‖s‖ ^ (p - 1) =
      L / ((p - 1)! : ℝ) * ‖s‖ ^ (p - 1) + σ / ((p - 1)! : ℝ) * ‖s‖ ^ (p - 1) := by ring
  linarith

/-- **Derivatives of the model and of the function, with an anchored Lipschitz condition**, (4.1.30)
of [cartis2022evaluation]. Let $E$ be a real inner product space, $C \subseteq E$ convex with
$x, x + s \in C$, and let $f : E \to \mathbb{R}$ be $p$ times continuously differentiable at
every point of $C$, with $\|\nabla^p f(y) - \nabla^p f(x)\| \le L \|y - x\|$ for all $y \in C$.
Let $\sigma \ge 0$, let $m$ be the regularized Taylor model of $f$ at $x$, and let $j \le p$.
Then for every $d \in E$,
$$\big|\nabla^j f(x + s)[d]^j - \nabla^j m(s)[d]^j\big| \le \frac{L + \sigma}{(p - j + 1)!}
  \|s\|^{p-j+1} \|d\|^j.$$

This is `Optimization.abs_iteratedFDeriv_apply_le_of_regularizedModel` with a weaker Lipschitz
condition. -/
theorem abs_iteratedFDeriv_apply_le_of_regularizedModel_anchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ L * ‖y - x‖)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) (d : E) :
    |iteratedFDeriv ℝ j f (x + s) (fun _ => d) -
        iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j := by
  rw [iteratedFDeriv_regularizedModel (Or.inl hj)]
  have hT := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitzAnchored hC hf hL hx hxs hj
  set A := iteratedFDeriv ℝ j f (x + s)
  set T := iteratedFDeriv ℝ j ((ftaylorSeries ℝ f x).taylorSum p) s
  set N := iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ (p + 1)) s
  have hN := abs_iteratedFDeriv_norm_pow_apply_le (r := p + 1) (ℓ := j) (by omega)
    (s := s) (Or.inr (by omega)) d
  have hfac : (p + 1 - j) = p - j + 1 := by omega
  rw [hfac] at hN
  have hAT : |(A - T) (fun _ => d)| ≤ ‖A - T‖ * ‖d‖ ^ j := by
    rw [← Real.norm_eq_abs]
    refine ((A - T).le_opNorm _).trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsplit : A (fun _ => d) - (T + (σ / ((p + 1)! : ℝ)) • N) (fun _ => d) =
      (A - T) (fun _ => d) - σ / ((p + 1)! : ℝ) * N (fun _ => d) := by
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  have hc : 0 ≤ σ / ((p + 1)! : ℝ) := by positivity
  calc |(A - T) (fun _ => d) - σ / ((p + 1)! : ℝ) * N (fun _ => d)|
      ≤ |(A - T) (fun _ => d)| + σ / ((p + 1)! : ℝ) * |N (fun _ => d)| := by
        refine (abs_sub _ _).trans_eq ?_
        rw [abs_mul, abs_of_nonneg hc]
    _ ≤ L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j +
          σ / ((p + 1)! : ℝ) *
            (((p + 1)! : ℝ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j) := by
        exact add_le_add (hAT.trans (mul_le_mul_of_nonneg_right hT (by positivity)))
          (mul_le_mul_of_nonneg_left hN hc)
    _ = (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j := by
        field_simp

/-- **Derivatives of the model and of the function**, (4.1.30) and (6.2.20)–(6.2.23) of
[cartis2022evaluation]. Let $E$ be a real inner product space, $C \subseteq E$ convex with
$x, x + s \in C$, and let $f : E \to \mathbb{R}$ be $p$ times continuously differentiable at
every point of $C$, with $\nabla^p f$ Lipschitz on $C$ with constant $L$. Let $\sigma \ge 0$,
let $m$ be the regularized Taylor model of $f$ at $x$, and let $j \le p$. Then for every
$d \in E$,
$$\big|\nabla^j f(x + s)[d]^j - \nabla^j m(s)[d]^j\big| \le \frac{L + \sigma}{(p - j + 1)!}
  \|s\|^{p-j+1} \|d\|^j.$$

The proof uses the bound of Lemma B.4.1 of [cartis2022evaluation] on the diagonal values of the
derivatives of $\|\cdot\|^{p+1}$, which holds for natural exponents. -/
theorem abs_iteratedFDeriv_apply_le_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) (d : E) :
    |iteratedFDeriv ℝ j f (x + s) (fun _ => d) -
        iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j :=
  abs_iteratedFDeriv_apply_le_of_regularizedModel_anchored hC hf
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hL y hy x hx) hx hxs hσ hj d

end Estimates

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ : ℝ}

/-- **Global minimizers of the model**, Sections 3.3.1 and 4.1.1 of [cartis2022evaluation]. Let $E$
be a finite-dimensional real inner product space, $D$ derivative data on $E$, $\sigma > 0$ and
$p \ge 1$. Then the model $m$ has a global minimizer $s^*$, and at $s^*$
* $\nabla m(s^*) = 0$,
* $\lambda_{\min}[\nabla^2 m(s^*)] \ge 0$, and
* $m(s^*) < m(0)$, unless $0$ is also a global minimizer.

The model is bounded below because the regularization term dominates. The second derivative is
`iteratedFDeriv ℝ 2`, which is $0$ where the model is not twice differentiable. -/
theorem exists_isMinOn_regularizedModel [FiniteDimensional ℝ E] (hσ : 0 < σ) (hp : 1 ≤ p) :
    ∃ s, IsMinOn (regularizedModel D p σ) univ s ∧
      fderiv ℝ (regularizedModel D p σ) s = 0 ∧
      0 ≤ minCurvature (iteratedFDeriv ℝ 2 (regularizedModel D p σ) s) ∧
      (¬ IsMinOn (regularizedModel D p σ) univ 0 →
        regularizedModel D p σ s < regularizedModel D p σ 0) := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨s, hmin, hd, hc, hlt⟩ := exists_isMinOn_powRegularizedModel (D := D) (p := p)
    (σ := σ) (r := (p : ℝ) + 1) hσ (by linarith) (by linarith)
  rw [← regularizedModel_eq_powRegularizedModel] at hmin hd hc hlt
  exact ⟨s, hmin, hd, hc (by linarith), hlt⟩

/-- If the derivative of the model at $0$ is nonzero, then every global minimizer $s$ of the model
decreases it: $m(s) < m(0)$. -/
theorem regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero {s : E}
    (hmin : IsMinOn (regularizedModel D p σ) univ s)
    (h0 : fderiv ℝ (regularizedModel D p σ) 0 ≠ 0) :
    regularizedModel D p σ s < regularizedModel D p σ 0 := by
  refine lt_of_le_of_ne (hmin (mem_univ 0)) fun heq => h0 ?_
  refine IsLocalMin.fderiv_eq_zero (IsMinOn.isLocalMin (fun y _ => ?_) univ_mem)
  rw [← heq]
  exact hmin (mem_univ y)

/-- Let $p \ge 2$, so that the model is twice continuously differentiable. If the model has negative
curvature at $0$, $\lambda_{\min}[\nabla^2 m(0)] < 0$, then every global minimizer $s$ of the
model decreases it: $m(s) < m(0)$. -/
theorem regularizedModel_lt_of_isMinOn_of_minCurvature_neg {s : E} (hp : 2 ≤ p)
    (hmin : IsMinOn (regularizedModel D p σ) univ s)
    (h0 : minCurvature (iteratedFDeriv ℝ 2 (regularizedModel D p σ) 0) < 0) :
    regularizedModel D p σ s < regularizedModel D p σ 0 := by
  refine lt_of_le_of_ne (hmin (mem_univ 0)) fun heq => ?_
  have hmin0 : IsMinOn (regularizedModel D p σ) univ 0 := fun y _ => by
    rw [← heq]; exact hmin (mem_univ y)
  exact (not_le.2 h0) (IsLocalMin.minCurvature_iteratedFDeriv_two_nonneg
    (hmin0.isLocalMin univ_mem)
    ((contDiff_regularizedModel (D := D) (σ := σ)).contDiffAt.of_le (by exact_mod_cast hp)))

end Existence

section Cubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The AR2 model is the cubic regularization model**, (3.3.1) and Theorem 8.2.8 of
[cartis2022evaluation]. Let $E$ be a real Hilbert space and let $f : E \to \mathbb{R}$ be twice
continuously differentiable at $x$. Then for all $\sigma \in \mathbb{R}$ and $s \in E$,
$$m(s) = T_{f,2}(x, s) + \frac{\sigma}{6} \|s\|^3 = f(x) + \langle \nabla f(x), s \rangle +
  \tfrac12 \langle s, \nabla^2 f(x) s \rangle + \frac{\sigma / 2}{3} \|s\|^3.$$

The right side is `f x + Subproblem.regModel (gradient f x) (hessianOperator f x) (σ / 2) 3 s`.
The model `Subproblem.regModel` has the regularization term $\frac{\sigma'}{r} \|s\|^r$, here with
$\sigma' = \sigma/2$ and $r = 3$. This identity transfers the characterization of global
minimizers, `Subproblem.isMinOn_regModel_iff`, to the steps of AR2. -/
theorem regularizedModel_two_eq_regModel {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (σ : ℝ)
    (s : E) :
    regularizedModel (ftaylorSeries ℝ f x) 2 σ s =
      f x + Subproblem.regModel (gradient f x) (hessianOperator f x) (σ / 2) 3 s := by
  rw [regularizedModel_def, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_two_eq_quadModel hf, Subproblem.regModel_def,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num [Nat.factorial]
  ring

end Cubic

end Optimization
