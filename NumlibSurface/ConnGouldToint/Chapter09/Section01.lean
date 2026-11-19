/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Extr

/-!
# Conn, Gould and Toint, Section 9.1: Conditional models

Chapter 9 of [conn2000trust] treats trust-region methods whose models need not agree with the
objective to first order at the center. A model $m$ of $f : E \to \mathbb{R}$ is **valid** on the
closed ball $B(x, \delta)$ with constant $\kappa$ if $|f(z) - m(z)| \le \kappa \delta^2$ for all
$z \in B(x, \delta)$ (equations (9.1.1)–(9.1.2)). This module formalizes the validity condition, the
gradient error bound of Theorem 9.1.1 for a valid model, the acceptance ratio (9.1.5) of Algorithm
9.1.1 at a selected trial point, the successful iterations and the reference-radius resets (9.1.7),
and parts (i) and (iii) of Lemma 9.1.2. The proofs use the second-order Taylor estimate of
`Numlib.Analysis.Calculus.Taylor`.

## Main definitions

* Equations (9.1.1)–(9.1.2), `ConnGouldToint.Chapter09.modelValidOnBall`: the model error is at most
  $\kappa \delta^2$ on the ball $B(x, \delta)$.
* Equation (9.1.5), `ConnGouldToint.Chapter09.selectedTrialRatio`: the decrease of $f$ at the
  selected point divided by the model decrease at the original trial point.
* Section 9.1, `ConnGouldToint.Chapter09.conditionalSuccessful`: the successful iterations, where
  the selected ratio is at least $\eta_0$.
* Equation (9.1.7), `ConnGouldToint.Chapter09.referenceRadiusResets`: the iterations that are
  successful or have a valid model.

## Main results

* Theorem 9.1.1, `ConnGouldToint.Chapter09.theorem_9_1_1`: a model that is valid on a ball of radius
  $\delta > 0$ has a gradient error of order $\delta$ at the center.
* `ConnGouldToint.Chapter09.zero_radius_counterexample`: at radius $0$, validity gives no bound on
  the gradient error.
* Lemma 9.1.2(i), `ConnGouldToint.Chapter09.lemma_9_1_2_i`: if the original trial point passes the
  acceptance test and is a candidate, the selected minimizer passes the weaker test.
* Lemma 9.1.2(i), `ConnGouldToint.Chapter09.conditionalSuccessful_subset_referenceRadiusResets`:
  every successful iteration resets the reference radius.
* Lemma 9.1.2(iii), `ConnGouldToint.Chapter09.lemma_9_1_2_iii`: if the final criticality test fails
  at every refinement, the model gradients shrink geometrically to zero and the center is
  first-order critical.

## Conventions

* The gradient $\nabla f(x)$ is the Fréchet derivative `fderiv ℝ f x`, a continuous linear
  functional on $E$ with the operator norm. The Hessian bounds are bounds on the operator norm of
  `fderiv ℝ (fderiv ℝ f)`.
* All balls are closed balls `Metric.closedBall` for the norm of $E$.

## Implementation notes

* The radius update of Algorithm 9.1.1 and Lemma 9.1.2(ii) are in
  `NumlibSurface.ConnGouldToint.Chapter09.Section02`.

## Deviations from the source

* **(9.1.1)–(9.1.3)** (generalization). The model validity and slope estimate use a real
  normed space and the norm of the Fréchet derivative. The source works in Euclidean space.
* **(9.1.5)** (reading). The trial ratio is totalized at zero predicted decrease. The acceptance
  comparison in Lemma 9.1.2(i) assumes a strictly positive denominator.
* **Lemma 9.1.2(iii)** (restriction). The modeled refinement trace assumes strictly positive
  model gradient norms, so the prescribed refinement radius is positive throughout the trace.
* **Theorem 9.1.1** (correction). The radius of the ball must be positive. At radius $0$, validity
  at the center alone gives no gradient bound. See
  `ConnGouldToint.Chapter09.zero_radius_counterexample`.
-/

open Filter Topology

namespace ConnGouldToint.Chapter09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Equations (9.1.1)–(9.1.2)** of [conn2000trust]. Let $f, m : E \to \mathbb{R}$, $x \in E$ and
$\delta, \kappa \in \mathbb{R}$. The model $m$ is **valid** for $f$ on the ball $B(x, \delta)$
with constant $\kappa$ if
$$|f(z) - m(z)| \le \kappa \delta^2 \quad \text{for all } z \text{ with } \|z - x\| \le
  \delta.$$

**Reading.** Quadratic model-error condition on a ball of an arbitrary real normed space.
-/
def modelValidOnBall (f m : E → ℝ) (x : E) (δ κ : ℝ) : Prop :=
  ∀ z ∈ Metric.closedBall x δ, |f z - m z| ≤ κ * δ ^ 2

/-- **Proof of Theorem 9.1.1** of [conn2000trust].

**Reading.** Taylor remainder uses bounded iterated Fréchet derivative on a general real normed
space.
-/
private theorem abs_remainder_le {f : E → ℝ} (hf : Differentiable ℝ f)
    (hd : Differentiable ℝ (fderiv ℝ f)) {B : ℝ}
    (hB : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B) (x s : E) :
    |f (x + s) - (f x + fderiv ℝ f x s)| ≤ (1 / 2 : ℝ) * B * ‖s‖ ^ 2 := by
  rw [← Real.norm_eq_abs]
  exact norm_sub_firstOrder_le_of_hessian_bound
    (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ (x + s))
    (fun z _ ↦ hf z) (fun z _ ↦ hd z) (fun z _ ↦ hB z)

/-- **Theorem 9.1.1** of [conn2000trust]. Let $E$ be a real normed space, let $f : E \to \mathbb{R}$
be twice continuously differentiable, and let $m : E \to \mathbb{R}$ be differentiable with a
differentiable derivative. Let $\delta > 0$, $\kappa > 0$, $B_f \ge 0$ and $B_m \ge 0$, and
suppose that $\|\nabla^2 f(z)\| \le B_f$ and $\|\nabla^2 m(z)\| \le B_m$ for all $z \in E$. If
$m$ is valid for $f$ on $B(x, \delta)$ with constant $\kappa$, then
$$\|\nabla f(x) - \nabla m(x)\| \le \left(2 \kappa + \tfrac{1}{2}(B_f + B_m)\right) \delta.$$

**Correction.** The hypothesis $\delta > 0$ is necessary. At $\delta = 0$, validity only says
that $f(x) = m(x)$, which gives no bound on the gradient error. See
`ConnGouldToint.Chapter09.zero_radius_counterexample`.

Validity is `ConnGouldToint.Chapter09.modelValidOnBall`, and the gradients are `fderiv ℝ f x`
and `fderiv ℝ m x`. -/
theorem theorem_9_1_1 {f m : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hm : Differentiable ℝ m) (hDm : Differentiable ℝ (fderiv ℝ m))
    {x : E} {δ κ Bf Bm : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ z, ‖fderiv ℝ (fderiv ℝ m) z‖ ≤ Bm)
    (hv : modelValidOnBall f m x δ κ) :
    ‖fderiv ℝ f x - fderiv ℝ m x‖ ≤ (2 * κ + (Bf + Bm) / 2) * δ := by
  let D := fderiv ℝ f x - fderiv ℝ m x
  apply D.opNorm_le_bound (by positivity)
  intro d
  by_cases hd : d = 0
  · simp [hd]
  have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let s := (δ / ‖d‖) • d
  have hs : ‖s‖ = δ := by
    rw [show s = (δ / ‖d‖) • d from rfl, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    exact div_mul_cancel₀ _ hn.ne'
  have h₀ := abs_le.mp (hv x (Metric.mem_closedBall_self hδ.le))
  have h₁ := abs_le.mp (hv (x + s) (by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hs]))
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h₂ := abs_le.mp (abs_remainder_le (hf.differentiable (by norm_num))
    (hDf.differentiable (by norm_num)) hF x s)
  have h₃ := abs_le.mp (abs_remainder_le hm hDm hM x s)
  rw [hs] at h₂ h₃
  have hstep : ‖D s‖ ≤ (2 * κ + (Bf + Bm) / 2) * δ ^ 2 := by
    rw [Real.norm_eq_abs, abs_le]
    change -((2 * κ + (Bf + Bm) / 2) * δ ^ 2) ≤ fderiv ℝ f x s - fderiv ℝ m x s ∧
      fderiv ℝ f x s - fderiv ℝ m x s ≤ (2 * κ + (Bf + Bm) / 2) * δ ^ 2
    constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]
  rw [show s = (δ / ‖d‖) • d from rfl, map_smul, norm_smul,
    Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div] at hstep
  apply (mul_le_mul_iff_of_pos_left hδ).mp
  calc
    δ * ‖D d‖ ≤ ((2 * κ + (Bf + Bm) / 2) * δ ^ 2) * ‖d‖ := (div_le_iff₀ hn).mp hstep
    _ = _ := by ring

/-- Validity on a ball of radius $0$ gives no control of the gradient error. On $\mathbb{R}$, the
model $m = 0$ is valid for $f(x) = x$ on the ball $B(0, 0)$ with constant $1$, but
$f'(0) \neq m'(0)$. This shows that the hypothesis $\delta > 0$ of Theorem 9.1.1
(`ConnGouldToint.Chapter09.theorem_9_1_1`) is necessary.

**Reading.** Exhibits vanishing radius and differing derivatives, motivating the extra premise.
-/
theorem zero_radius_counterexample :
    modelValidOnBall (fun x : ℝ ↦ x) (fun _ ↦ 0) 0 0 1 ∧
      fderiv ℝ (fun x : ℝ ↦ x) 0 ≠ fderiv ℝ (fun _ : ℝ ↦ (0 : ℝ)) 0 := by
  constructor
  · intro z hz
    have hz₀ : z = 0 := by simpa using hz
    simp [hz₀]
  · change fderiv ℝ (id : ℝ → ℝ) 0 ≠ fderiv ℝ (Function.const ℝ (0 : ℝ)) 0
    rw [fderiv_id, fderiv_const]
    intro h
    have := DFunLike.congr_fun h (1 : ℝ)
    norm_num at this

/-- **Equation (9.1.5)** of [conn2000trust]. Let $f, m : E \to \mathbb{R}$, let $x$ be the center,
$x^+$ the original trial point and $\hat{x}$ the selected point. The **selected-trial ratio** is
$$\hat{\rho} = \frac{f(x) - f(\hat{x})}{m(x) - m(x^+)}.$$

The decrease of $f$ is measured at the selected point, and the model decrease at the original
trial point. The value is $0$ when $m(x) = m(x^+)$.

**Reading.** Same selected-step numerator and model-trial denominator, with totalized division.
-/
noncomputable def selectedTrialRatio (f m : E → ℝ) (x trial selected : E) : ℝ :=
  (f x - f selected) / (m x - m trial)

/-- **Section 9.1** of [conn2000trust], definition before (9.1.7). Given a threshold $\eta_0$ and
ratios $\hat{\rho}_k$, the set of **successful iterations** is
$\{k \in \mathbb{N} : \hat{\rho}_k \ge \eta_0\}$. -/
def conditionalSuccessful (η₀ : ℝ) (ρhat : ℕ → ℝ) : Set ℕ :=
  {k | η₀ ≤ ρhat k}

/-- **Equation (9.1.7)** of [conn2000trust]. Given a threshold $\eta_0$, ratios $\hat{\rho}_k$ and a
predicate "the model of iteration $k$ is valid", the set of **reference-radius resets** is the
set of $k$ with $\hat{\rho}_k \ge \eta_0$ or a valid model at iteration $k$. -/
def referenceRadiusResets (η₀ : ℝ) (ρhat : ℕ → ℝ) (valid : ℕ → Prop) : Set ℕ :=
  {k | η₀ ≤ ρhat k ∨ valid k}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **Lemma 9.1.2(i)** of [conn2000trust]. Let $f, m$ be real functions on a set $E$, let
$x, x^+, \hat{x} \in E$, let $C \subseteq E$ be a set of candidates, and let
$\eta_0 \le \eta_1$. Suppose that $m(x) - m(x^+) > 0$, that $\hat{x}$ minimizes $f$ on $C$, and
that $x^+ \in C$ whenever $\eta_1 \le \rho$, where $\rho = (f(x) - f(x^+)) / (m(x) - m(x^+))$.
If $\eta_1 \le \rho$, then the selected-trial ratio (9.1.5) satisfies
$$\eta_0 \le \frac{f(x) - f(\hat{x})}{m(x) - m(x^+)}.$$

Both ratios are `ConnGouldToint.Chapter09.selectedTrialRatio`, with selected point $x^+$ and
$\hat{x}$. -/
theorem lemma_9_1_2_i {f m : E → ℝ} {x trial selected : E} {candidates : Set E}
    {η₀ η₁ : ℝ} (hη : η₀ ≤ η₁) (hdec : 0 < m x - m trial)
    (hsel : IsMinOn f candidates selected)
    (htrial : η₁ ≤ selectedTrialRatio f m x trial trial → trial ∈ candidates)
    (hρ : η₁ ≤ selectedTrialRatio f m x trial trial) :
    η₀ ≤ selectedTrialRatio f m x trial selected := by
  exact hη.trans (hρ.trans
    (div_le_div_of_nonneg_right (sub_le_sub_left ((isMinOn_iff.mp hsel) trial (htrial hρ)) _)
      hdec.le))

/-- **Lemma 9.1.2(i)** of [conn2000trust], inclusion of sets. For every threshold $\eta_0$, ratios
$\hat{\rho}_k$ and validity predicate, every successful iteration is a reference-radius reset
(9.1.7). -/
theorem conditionalSuccessful_subset_referenceRadiusResets (η₀ : ℝ)
    (ρhat : ℕ → ℝ) (valid : ℕ → Prop) :
    conditionalSuccessful η₀ ρhat ⊆ referenceRadiusResets η₀ ρhat valid :=
  fun _ hk ↦ Or.inl hk

/-- **Lemma 9.1.2(iii)** of [conn2000trust]. Let $f : E \to \mathbb{R}$ be twice continuously
differentiable, and for each $k \in \mathbb{N}$ let $m_k : E \to \mathbb{R}$ be differentiable
with a differentiable derivative. Let $0 < \alpha < 1$, $\mu > 0$, $\kappa > 0$, $B_f \ge 0$ and
$B_m \ge 0$, with $\|\nabla^2 f(z)\| \le B_f$ and $\|\nabla^2 m_k(z)\| \le B_m$ for all $k$ and
$z$. Let $x \in E$ with $\nabla m_k(x) \neq 0$ for all $k$. Suppose that for every $k$:

* the model $m_{k+1}$ is valid for $f$ on $B(x, \alpha \mu \|\nabla m_k(x)\|)$ with constant
  $\kappa$, and
* the model $m_{k+1}$ is not valid on $B(x, r)$ with constant $\kappa$ for any $r$ with
  $0 < r \le \mu \|\nabla m_{k+1}(x)\|$ (the criticality test fails).

Then $\nabla f(x) = 0$ and $\|\nabla m_k(x)\| \to 0$.

The two conditions give $\|\nabla m_{k+1}(x)\| < \alpha \|\nabla m_k(x)\|$, so the model
gradients shrink geometrically. The proof then applies Theorem 9.1.1 to each model at the radius
at which it is valid.

**Reading.** Positive model derivative norms assumed along the infinite trace.
-/
theorem lemma_9_1_2_iii {f : E → ℝ} (hf : ContDiff ℝ 2 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k)) (hDm : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    {x : E} {α μ κ Bf Bm : ℝ} (hα : 0 < α) (hα₁ : α < 1) (hμ : 0 < μ)
    (hκ : 0 < κ) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ k z, ‖fderiv ℝ (fderiv ℝ (m k)) z‖ ≤ Bm)
    (hpos : ∀ k, 0 < ‖fderiv ℝ (m k) x‖)
    (hvalid : ∀ k, modelValidOnBall f (m (k + 1)) x (α * μ * ‖fderiv ℝ (m k) x‖) κ)
    (hfailed : ∀ k r, 0 < r → r ≤ μ * ‖fderiv ℝ (m (k + 1)) x‖ →
      ¬ modelValidOnBall f (m (k + 1)) x r κ) :
    fderiv ℝ f x = 0 ∧ Tendsto (fun k ↦ ‖fderiv ℝ (m k) x‖) atTop (𝓝 0) := by
  let g (k : ℕ) := ‖fderiv ℝ (m k) x‖
  have hstep (k : ℕ) : g (k + 1) ≤ α * g k := by
    by_contra! h
    have hle : α * μ * g k ≤ μ * g (k + 1) := by
      rw [mul_comm α μ, mul_assoc]
      exact mul_le_mul_of_nonneg_left h.le hμ.le
    exact hfailed k _ (mul_pos (mul_pos hα hμ) (hpos k)) hle (hvalid k)
  have hgeom (k : ℕ) : g k ≤ α ^ k * g 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      apply (hstep k).trans
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left ih hα.le
  have hpow : Tendsto (fun k : ℕ ↦ α ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα₁
  have hg : Tendsto g atTop (𝓝 0) := by
    refine squeeze_zero (fun k ↦ norm_nonneg _) hgeom ?_
    simpa only [zero_mul] using hpow.mul_const (g 0)
  refine ⟨norm_le_zero_iff.mp ?_, hg⟩
  let C := 2 * κ + (Bf + Bm) / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun k ↦ (C * (α * μ) + α) * g k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hg.const_mul (C * (α * μ) + α)
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
  intro k
  have he := theorem_9_1_1 hf (hm (k + 1)) (hDm (k + 1))
    (mul_pos (mul_pos hα hμ) (hpos k)) hκ hBf hBm hF (hM (k + 1)) (hvalid k)
  let a := fderiv ℝ f x
  let b := fderiv ℝ (m (k + 1)) x
  calc
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a - b) b
    _ ≤ C * (α * μ * g k) + α * g k := add_le_add he (hstep k)
    _ = _ := by ring

end ConnGouldToint.Chapter09
