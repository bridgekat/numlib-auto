/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.ODE.Cauchy
import Numlib.Analysis.ODE.Gronwall

/-!
# Quarteroni, Sacco and Saleri, Section 11.1: The Cauchy problem

This module formalizes Section 11.1 of [quarteroni2000numerical]. The scalar Cauchy problem (11.1)
asks for $y$ with $y'(t) = f(t, y(t))$ on an interval $I \ni t_0$ and $y(t_0) = y_0$. For a
continuous $f$ it is equivalent to the integral equation (11.2). The book recalls two existence and
uniqueness results: a local one, under the Lipschitz condition (11.3) on a box, for radii
$r_0 < \min(r_J, r_\Sigma/M)$, and a global one, under a uniform Lipschitz condition. The module
also states Liapunov stability (Definition 11.1, (11.5)) for the perturbed problem (11.4) and its
asymptotic form (11.6), the stability estimate $|y(t) - z(t)| \le (1 + |t - t_0|) \varepsilon
e^{L|t - t_0|}$ under a uniform Lipschitz condition with the constant $C = (1 + K_I) e^{L K_I}$ that
it gives, and Gronwall's lemma (Lemma 11.1).

All statements are the real case $E = \mathbb{R}$ of `Numlib.Analysis.ODE.Cauchy`
(`ODE.IsSolutionOn`, `ODE.IsLiapunovStable`, `ODE.IsAsymptoticallyStable`, the existence theorems
and the estimate `ODE.norm_sub_le_of_lipschitz`) and of `Numlib.Analysis.ODE.Gronwall`
(`Gronwall.le_mul_exp_integral`).

## Main definitions

* Equation (11.1), `QuarteroniSaccoSaleri.Chapter11.cauchyProblem`: $y$ solves the Cauchy problem on
  $I$.
* Definition 11.1, `QuarteroniSaccoSaleri.Chapter11.definition_11_1`: the Cauchy problem is stable
  in the sense of Liapunov on $I$.
* Definition 11.1, (11.6), `QuarteroniSaccoSaleri.Chapter11.definition_11_1_asymptotic`: the Cauchy
  problem is asymptotically stable.

## Main results

* Equation (11.2), `QuarteroniSaccoSaleri.Chapter11.equation_11_2`: for a continuous $f$, (11.1) on
  $[t_0, t_0 + T]$ is equivalent to the integral equation (11.2).
* Section 11.1, item 1, `QuarteroniSaccoSaleri.Chapter11.localExistenceUniqueness`: local existence
  and uniqueness under the Lipschitz condition (11.3).
* Section 11.1, item 2, `QuarteroniSaccoSaleri.Chapter11.globalExistenceUniqueness`: global
  existence and uniqueness under a uniform Lipschitz condition.
* Section 11.1, stability estimate,
  `QuarteroniSaccoSaleri.Chapter11.isLiapunovStable_of_lipschitz_estimate` and
  `QuarteroniSaccoSaleri.Chapter11.isLiapunovStable_of_lipschitz`: a uniform Lipschitz condition
  gives the estimate $|y(t) - z(t)| \le (1 + |t - t_0|) \varepsilon e^{L|t - t_0|}$ and Liapunov
  stability.
* Lemma 11.1, `QuarteroniSaccoSaleri.Chapter11.lemma_11_1` and
  `QuarteroniSaccoSaleri.Chapter11.lemma_11_1_continuous`: Gronwall's lemma, as printed and with a
  continuous weight.

## Conventions

* The field is `f : ℝ → ℝ → ℝ`. Continuity "with respect to both variables" is continuity of
  $(t, y) \mapsto f(t, y)$ on the strip $I \times \mathbb{R}$.
* A solution $y \in C^1(I)$ of (11.1) is a function with `HasDerivWithinAt y (f t (y t)) I t` at
  every $t \in I$, so the derivative is one-sided at the endpoints. The continuity of $y'$ follows
  from that of $f$.

## Deviations from the source

* **Equations (11.1) and (11.2), and global existence and uniqueness** (reading). The Cauchy
  problem predicate uses a within-set derivative and imposes neither joint continuity of $f$ nor
  $t_0\in I$. The integral equivalence and global existence theorem use the right closed
  interval $[t_0,t_0+T]$. The equivalence assumes continuity of $y$ in advance. The global
  theorem fixes $y=y_0$ outside the interval to express uniqueness as equality of total
  functions.
* **Section 11.1, item 1** (reading). `localExistenceUniqueness` uses an upper bound $M$ on the
  rectangle. It states existence and uniqueness among solutions with values in the rectangle,
  and compares those solutions only on the solution interval.
* **Definition 11.1 and equations (11.4)–(11.6)** (reading). The Liapunov bound uses one
  constant for every $\varepsilon>0$ and every pair of solutions that exists. The asymptotic
  definition uses all forward bounded intervals and a single positive perturbation tolerance for
  convergence on $[t_0,\infty)$. The Lipschitz stability results use forward closed finite
  intervals.
* **Lemma 11.1** (specialization). `lemma_11_1_continuous` gives the continuous-weight case with
  a nonnegative weight on the closed interval.
* **Section 11.1, item 1** (generalization). The book also requires $r_0 < 1/L$. This bound is not
  needed and is dropped. See `QuarteroniSaccoSaleri.Chapter11.localExistenceUniqueness`.
-/

open Set Filter Topology MeasureTheory

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ y₀ T : ℝ} {I : Set ℝ} {y z : ℝ → ℝ}

/-- **Equation (11.1)** of [quarteroni2000numerical], the Cauchy problem. Let $f : \mathbb{R} \times
\mathbb{R} \to \mathbb{R}$, $t_0, y_0 \in \mathbb{R}$ and $I \subseteq \mathbb{R}$. A function
$y : \mathbb{R} \to \mathbb{R}$ **solves the Cauchy problem** on $I$ if $y(t_0) = y_0$ and
$y'(t) = f(t, y(t))$ for every $t \in I$, where the derivative is taken within $I$.

The definition is `ODE.IsSolutionOn` at $E = \mathbb{R}$. The point $t_0$ need not lie in $I$.

**Generalization.** Uses the derivative within an arbitrary set and does not require joint
continuity of the field or membership of $t_0$ in the set. The source introduces the problem on
an interval containing $t_0$ with continuous field. -/
def cauchyProblem (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) (I : Set ℝ) (y : ℝ → ℝ) : Prop :=
  ODE.IsSolutionOn f t₀ y₀ I y

/-- **Equation (11.1)** of [quarteroni2000numerical], unfolded. A function $y$ solves the Cauchy
problem on $I$ if and only if $y(t_0) = y_0$ and $y$ has the derivative $f(t, y(t))$ within $I$
at every $t \in I$.

**Generalization.** Uses the derivative within an arbitrary set and does not require joint
continuity of the field or membership of $t_0$ in the set. The source introduces the problem on
an interval containing $t_0$ with continuous field. -/
theorem cauchyProblem_iff :
    cauchyProblem f t₀ y₀ I y ↔ y t₀ = y₀ ∧ ∀ t ∈ I, HasDerivWithinAt y (f t (y t)) I t :=
  Iff.rfl

/-- **Equation (11.2)** of [quarteroni2000numerical], the integral form. Let $T \ge 0$, let $f$ be
continuous on the strip $[t_0, t_0 + T] \times \mathbb{R}$, and let $y$ be continuous on
$[t_0, t_0 + T]$. Then $y$ solves the Cauchy problem (11.1) on $[t_0, t_0 + T]$ if and only if
$$y(t) - y_0 = \int_{t_0}^{t} f(\tau, y(\tau)) \, d\tau \qquad \text{for every } t \in [t_0,
  t_0 + T].$$

**Reading.** Uses a forward closed finite interval and assumes joint continuity of $f$ and
continuity of the candidate $y$. The source's converse obtains continuity of $y$ from its
integral representation. -/
theorem equation_11_2 (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T) ×ˢ univ))
    (hy : ContinuousOn y (Icc t₀ (t₀ + T))) :
    cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y ↔
      ∀ t ∈ Icc t₀ (t₀ + T), y t - y₀ = ∫ τ in t₀..t, f τ (y τ) := by
  rw [cauchyProblem, ODE.isSolutionOn_iff_integral (left_mem_Icc.2 (by linarith)) hf hy]
  exact forall₂_congr fun t _ => by rw [sub_eq_iff_eq_add']

/-- **Section 11.1** of [quarteroni2000numerical], item 1 (local existence and uniqueness). Let
$J = [t_0 - r_J, t_0 + r_J]$ and $\Sigma = [y_0 - r_\Sigma, y_0 + r_\Sigma]$ with
$r_\Sigma > 0$. Let $f$ be continuous on $J \times \Sigma$ and satisfy the Lipschitz condition
(11.3),
$$|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2| \qquad \text{for } t \in J, \ y_1, y_2 \in \Sigma,$$
with $L > 0$, and let $|f| \le M$ on $J \times \Sigma$. Then for every $r_0$ with
$0 < r_0 < \min(r_J, r_\Sigma/M)$ the Cauchy problem has a solution on $[t_0 - r_0, t_0 + r_0]$
with values in $\Sigma$, and every other solution on this interval with values in $\Sigma$
agrees with it there.

**Generalization.** The book also requires $r_0 < 1/L$. This bound is not needed.

The proof specializes `ODE.exists_isSolutionOn_of_lipschitzOnWith`.

**Reading.** Uses a bound $M$ on the rectangle, and expresses uniqueness on the interval among
solutions whose values are in that rectangle. -/
theorem localExistenceUniqueness {rJ rS r₀ L M : ℝ} (hL : 0 < L) (hrS : 0 < rS)
    (hf : ContinuousOn (Function.uncurry f) (Icc (t₀ - rJ) (t₀ + rJ) ×ˢ Icc (y₀ - rS) (y₀ + rS)))
    (hlip : ∀ t ∈ Icc (t₀ - rJ) (t₀ + rJ), ∀ y₁ ∈ Icc (y₀ - rS) (y₀ + rS),
      ∀ y₂ ∈ Icc (y₀ - rS) (y₀ + rS), |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hM : ∀ t ∈ Icc (t₀ - rJ) (t₀ + rJ), ∀ v ∈ Icc (y₀ - rS) (y₀ + rS), |f t v| ≤ M)
    (hr₀ : 0 < r₀) (hr₀' : r₀ < min rJ (rS / M)) :
    ∃ y : ℝ → ℝ, cauchyProblem f t₀ y₀ (Icc (t₀ - r₀) (t₀ + r₀)) y ∧
      (∀ t ∈ Icc (t₀ - r₀) (t₀ + r₀), y t ∈ Icc (y₀ - rS) (y₀ + rS)) ∧
      ∀ z : ℝ → ℝ, cauchyProblem f t₀ y₀ (Icc (t₀ - r₀) (t₀ + r₀)) z →
        (∀ t ∈ Icc (t₀ - r₀) (t₀ + r₀), z t ∈ Icc (y₀ - rS) (y₀ + rS)) →
        EqOn y z (Icc (t₀ - r₀) (t₀ + r₀)) := by
  have hrJ : r₀ ≤ rJ := (lt_min_iff.1 hr₀').1.le
  have hrM : r₀ < rS / M := (lt_min_iff.1 hr₀').2
  have hM0 : 0 ≤ M :=
    (abs_nonneg _).trans (hM t₀ ⟨by linarith, by linarith⟩ y₀ ⟨by linarith, by linarith⟩)
  have hMpos : 0 < M := lt_of_le_of_ne hM0 fun h => by rw [← h, div_zero] at hrM; linarith
  have hMr : M * r₀ ≤ rS := by
    have := (lt_div_iff₀ hMpos).1 hrM
    linarith
  have key := ODE.exists_isSolutionOn_of_lipschitzOnWith (f := f) (t₀ := t₀) (y₀ := y₀)
    (K := ⟨L, hL.le⟩) (rJ := rJ) (rS := rS) (r₀ := r₀) (M := M)
    (by rwa [Real.closedBall_eq_Icc]) (fun t ht => by
      rw [Real.closedBall_eq_Icc]
      exact LipschitzOnWith.of_dist_le_mul fun v₁ hv₁ v₂ hv₂ => by
        rw [Real.dist_eq, Real.dist_eq]
        exact hlip t ht v₁ hv₁ v₂ hv₂)
    (fun t ht v hv => by
      rw [Real.closedBall_eq_Icc] at hv
      rw [Real.norm_eq_abs]
      exact hM t ht v hv) hr₀ hrJ hrS.le hMr
  simpa only [Real.closedBall_eq_Icc, cauchyProblem] using key

/-- **Section 11.1** of [quarteroni2000numerical], item 2 (global existence and uniqueness). Let
$T \ge 0$ and $L \ge 0$. Let $f$ be continuous on the strip $[t_0, t_0 + T] \times \mathbb{R}$
and uniformly Lipschitz continuous with respect to $y$ there, that is (11.3) with
$J = [t_0, t_0 + T]$ and $\Sigma = \mathbb{R}$. Then the Cauchy problem has exactly one solution
on $[t_0, t_0 + T]$.

A solution is a function on $\mathbb{R}$, so for uniqueness the statement fixes it to be $y_0$
outside $[t_0, t_0 + T]$. The proof specializes `ODE.existsUnique_isSolutionOn_of_lipschitz`.

**Reading.** Uses $[t_0,t_0+T]$ and makes the joint continuity assumption explicit. Solutions
are extended by the same constant off the interval to express uniqueness. -/
theorem globalExistenceUniqueness {L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hf : ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T) ×ˢ univ))
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) :
    ∃! y : ℝ → ℝ, cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y ∧ ∀ t ∉ Icc t₀ (t₀ + T), y t = y₀ :=
  ODE.existsUnique_isSolutionOn_of_lipschitz (K := ⟨L, hL⟩) hT hf (fun t ht =>
    LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht v₁ v₂) y₀

/-- **Definition 11.1** of [quarteroni2000numerical] (Liapunov stability). Let $f : \mathbb{R}
\times \mathbb{R} \to \mathbb{R}$, $t_0, y_0 \in \mathbb{R}$ and $I \subseteq \mathbb{R}$. The
Cauchy problem (11.1) is **stable in the sense of Liapunov** on $I$ if there is a constant
$C > 0$, independent of $\varepsilon$, with the following property. For every $\varepsilon > 0$
and every perturbation $(\delta_0, \delta(t))$ with $|\delta_0| < \varepsilon$, $\delta$
continuous on $I$ and $|\delta(t)| < \varepsilon$ on $I$, every solution $y$ of (11.1) and every
solution $z$ of the perturbed problem (11.4),
$$z'(t) = f(t, z(t)) + \delta(t), \qquad z(t_0) = y_0 + \delta_0,$$
satisfy (11.5), $|y(t) - z(t)| < C\varepsilon$ for all $t \in I$.

The book takes $I$ bounded and restricts to $\varepsilon$ small enough for the perturbed
solution to exist. The definition quantifies over the solutions that exist, so it has no such
restriction. It is `ODE.IsLiapunovStable` at $E = \mathbb{R}$.

**Reading.** The positive constant is uniform over all positive tolerances and solution pairs
satisfying the perturbation bounds. Existence of the solutions is a premise. -/
def definition_11_1 (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) (I : Set ℝ) : Prop :=
  ODE.IsLiapunovStable f t₀ y₀ I

/-- **Definition 11.1** of [quarteroni2000numerical], unfolded. The Cauchy problem is stable in the
sense of Liapunov on $I$ if and only if there is $C > 0$ such that for all $\varepsilon > 0$,
all $\delta_0$ with $|\delta_0| < \varepsilon$, all $\delta$ continuous on $I$ with
$|\delta(t)| < \varepsilon$ on $I$, every solution $y$ of (11.1) on $I$ and every solution $z$
of the perturbed problem (11.4) on $I$, we have $|y(t) - z(t)| < C\varepsilon$ for all
$t \in I$.

**Reading.** The positive constant is uniform over all positive tolerances and solution pairs
satisfying the perturbation bounds. Existence of the solutions is a premise. -/
theorem definition_11_1_iff :
    definition_11_1 f t₀ y₀ I ↔ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ (δ₀ : ℝ) (δ : ℝ → ℝ),
      |δ₀| < ε → ContinuousOn δ I → (∀ t ∈ I, |δ t| < ε) →
        ∀ y z : ℝ → ℝ, cauchyProblem f t₀ y₀ I y →
          cauchyProblem (fun t v => f t v + δ t) t₀ (y₀ + δ₀) I z →
            ∀ t ∈ I, |y t - z t| < C * ε := by
  simp only [definition_11_1, ODE.IsLiapunovStable, Real.norm_eq_abs, cauchyProblem]

/-- **Definition 11.1** of [quarteroni2000numerical], asymptotic stability (11.6). The Cauchy
problem (11.1) is **asymptotically stable** if it is stable in the sense of Liapunov on every
interval $[t_0, t_0 + T]$ with $T > 0$, and if there is $\varepsilon > 0$ such that for every
perturbation with $|\delta_0| < \varepsilon$, $\delta$ continuous on $[t_0, \infty)$ and
$|\delta(t)| < \varepsilon$ there, every solution $y$ of (11.1) and every solution $z$ of (11.4)
on $[t_0, \infty)$ satisfy
$$|y(t) - z(t)| \to 0 \qquad \text{as } t \to +\infty.$$

The definition is `ODE.IsAsymptoticallyStable` at $E = \mathbb{R}$.

**Reading.** Uses forward bounded intervals and makes a positive perturbation radius explicit
for the right-half-line limit. -/
def definition_11_1_asymptotic (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) : Prop :=
  ODE.IsAsymptoticallyStable f t₀ y₀

/-- **Definition 11.1** of [quarteroni2000numerical], asymptotic stability unfolded. The Cauchy
problem is asymptotically stable if and only if it is stable in the sense of Liapunov on
$[t_0, t_0 + T]$ for every $T > 0$, and there is $\varepsilon > 0$ such that for all $\delta_0$
with $|\delta_0| < \varepsilon$, all $\delta$ continuous on $[t_0, \infty)$ with
$|\delta(t)| < \varepsilon$ there, every solution $y$ of (11.1) and every solution $z$ of (11.4)
on $[t_0, \infty)$, $|y(t) - z(t)| \to 0$ as $t \to +\infty$.

**Reading.** Uses forward bounded intervals and makes a positive perturbation radius explicit
for the right-half-line limit. -/
theorem definition_11_1_asymptotic_iff :
    definition_11_1_asymptotic f t₀ y₀ ↔
      (∀ T : ℝ, 0 < T → definition_11_1 f t₀ y₀ (Icc t₀ (t₀ + T))) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ (δ₀ : ℝ) (δ : ℝ → ℝ), |δ₀| < ε → ContinuousOn δ (Ici t₀) →
          (∀ t ∈ Ici t₀, |δ t| < ε) → ∀ y z : ℝ → ℝ, cauchyProblem f t₀ y₀ (Ici t₀) y →
            cauchyProblem (fun t v => f t v + δ t) t₀ (y₀ + δ₀) (Ici t₀) z →
              Tendsto (fun t => |y t - z t|) atTop (𝓝 0) := by
  simp only [definition_11_1_asymptotic, ODE.IsAsymptoticallyStable, definition_11_1,
    Real.norm_eq_abs, cauchyProblem]

/-- **Section 11.1** of [quarteroni2000numerical], the stability estimate. Let $L \ge 0$ and let $f$
be uniformly Lipschitz continuous with respect to $y$ on $[t_0, t_0 + T]$ with the constant $L$.
Let $|\delta_0| \le \varepsilon$ and $|\delta(t)| \le \varepsilon$ for $t \in [t_0, t_0 + T]$.
Let $y$ solve (11.1) and $z$ solve the perturbed problem (11.4) on $[t_0, t_0 + T]$. Then for
every $t \in [t_0, t_0 + T]$
$$|w(t)| = |z(t) - y(t)| \le (1 + |t - t_0|) \, \varepsilon \, e^{L|t - t_0|}.$$

The proof specializes `ODE.norm_sub_le_of_lipschitz`.

**Reading.** Uses the forward closed interval and the within-interval Cauchy problem. The
numerical estimate also allows weak perturbation inequalities. -/
theorem isLiapunovStable_of_lipschitz_estimate {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    {δ₀ ε : ℝ} {δ : ℝ → ℝ} (hδ₀ : |δ₀| ≤ ε) (hδ : ∀ t ∈ Icc t₀ (t₀ + T), |δ t| ≤ ε)
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hz : cauchyProblem (fun t v => f t v + δ t) t₀ (y₀ + δ₀) (Icc t₀ (t₀ + T)) z) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + T)) :
    |y t - z t| ≤ (1 + |t - t₀|) * ε * Real.exp (L * |t - t₀|) := by
  have hlip' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith ⟨L, hL⟩ (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht v₁ v₂
  have := ODE.norm_sub_le_of_lipschitz hlip' (δ₀ := δ₀) (δ := δ) (ε := ε)
    (by rwa [Real.norm_eq_abs]) (fun t ht => by rw [Real.norm_eq_abs]; exact hδ t ht) hy hz ht
  rw [abs_of_nonneg (sub_nonneg.2 ht.1)]
  exact this

/-- **Section 11.1** of [quarteroni2000numerical], Liapunov stability from a uniform Lipschitz
condition. Let $T \ge 0$, $L \ge 0$, and let $f$ be uniformly Lipschitz continuous with respect
to $y$ on $[t_0, t_0 + T]$ with the constant $L$. Then for every $y_0$ the Cauchy problem is
stable in the sense of Liapunov on $[t_0, t_0 + T]$.

The proof gives the constant $C = (1 + K_I) e^{L K_I}$ with
$K_I = \max_{t \in I} |t - t_0| = T$. It specializes `ODE.isLiapunovStable_of_lipschitz`.

**Reading.** Uses the forward closed interval and the within-interval Cauchy problem. The
numerical estimate also allows weak perturbation inequalities. -/
theorem isLiapunovStable_of_lipschitz {L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) (y₀ : ℝ) :
    definition_11_1 f t₀ y₀ (Icc t₀ (t₀ + T)) :=
  ODE.isLiapunovStable_of_lipschitz hT (L := ⟨L, hL⟩) (fun t ht =>
    LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht v₁ v₂) y₀

/-- **Lemma 11.1** of [quarteroni2000numerical] (Gronwall's lemma). Let $p$ be integrable on
$[t_0, t_0 + T]$ and nonnegative on $(t_0, t_0 + T)$. Let $g$ and $\varphi$ be continuous on
$[t_0, t_0 + T]$, with $g$ nondecreasing. If
$$\varphi(t) \le g(t) + \int_{t_0}^{t} p(\tau) \varphi(\tau) \, d\tau \qquad \text{for all } t
  \in [t_0, t_0 + T],$$
then
$$\varphi(t) \le g(t) \exp\Bigl(\int_{t_0}^{t} p(\tau) \, d\tau\Bigr) \qquad \text{for all } t
  \in [t_0, t_0 + T].$$

The continuity of $g$ is a hypothesis of the book that the proof does not use. The proof
specializes `Gronwall.le_mul_exp_integral` after it replaces $p$ by $\max(p, 0)$, which agrees
with $p$ almost everywhere. -/
theorem lemma_11_1 {p g φ : ℝ → ℝ} (hp : IntervalIntegrable p MeasureTheory.volume t₀ (t₀ + T))
    (hp0 : ∀ t ∈ Ioo t₀ (t₀ + T), 0 ≤ p t) (_hg : ContinuousOn g (Icc t₀ (t₀ + T)))
    (hgm : MonotoneOn g (Icc t₀ (t₀ + T))) (hφ : ContinuousOn φ (Icc t₀ (t₀ + T)))
    (h : ∀ t ∈ Icc t₀ (t₀ + T), φ t ≤ g t + ∫ τ in t₀..t, p τ * φ τ) :
    ∀ t ∈ Icc t₀ (t₀ + T), φ t ≤ g t * Real.exp (∫ τ in t₀..t, p τ) := by
  intro t ht
  -- the weight `max p 0` agrees with `p` on `(t₀, t₀ + T)`, hence almost everywhere on `(t₀, t]`
  have hae : ∀ t' ∈ Icc t₀ (t₀ + T), ∀ᵐ τ ∂MeasureTheory.volume, τ ∈ uIoc t₀ t' →
      max (p τ) 0 = p τ := by
    intro t' ht'
    have hne : ∀ᵐ τ ∂MeasureTheory.volume, τ ≠ t₀ + T := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with τ hτ hτI
    rw [uIoc_of_le ht'.1] at hτI
    exact max_eq_left (hp0 τ ⟨hτI.1, lt_of_le_of_ne (hτI.2.trans ht'.2) hτ⟩)
  have hint' : IntervalIntegrable (fun τ => max (p τ) 0) MeasureTheory.volume t₀ (t₀ + T) :=
    ⟨Integrable.sup hp.1 (integrable_zero _ _ _), Integrable.sup hp.2 (integrable_zero _ _ _)⟩
  have h1 : ∀ t' ∈ Icc t₀ (t₀ + T),
      ∫ τ in t₀..t', max (p τ) 0 * φ τ = ∫ τ in t₀..t', p τ * φ τ := fun t' ht' =>
    intervalIntegral.integral_congr_ae ((hae t' ht').mono fun τ hτ hτI => by rw [hτ hτI])
  have h2 : ∫ τ in t₀..t, max (p τ) 0 = ∫ τ in t₀..t, p τ :=
    intervalIntegral.integral_congr_ae ((hae t ht).mono fun τ hτ hτI => hτ hτI)
  rw [← h2]
  exact Gronwall.le_mul_exp_integral hint' (fun _ _ => le_max_right _ _) hgm hφ
    (fun t' ht' => by rw [h1 t' ht']; exact h t' ht') ht

/-- **Lemma 11.1** of [quarteroni2000numerical] with a continuous weight, the case that Section 11.1
uses. Let $p$ be continuous and nonnegative on $[t_0, t_0 + T]$, let $g$ and $\varphi$ be
continuous on $[t_0, t_0 + T]$, with $g$ nondecreasing. If
$\varphi(t) \le g(t) + \int_{t_0}^{t} p \varphi$ for all $t \in [t_0, t_0 + T]$, then
$\varphi(t) \le g(t) \exp\bigl(\int_{t_0}^{t} p\bigr)$ for all $t \in [t_0, t_0 + T]$.

The continuity of $g$ is not used. The proof specializes
`Gronwall.le_mul_exp_integral_of_continuousOn`.

**Specialization.** Assumes continuity and nonnegativity on the closed interval. The principal
form `lemma_11_1` allows the integrable weight of the source. -/
theorem lemma_11_1_continuous {p g φ : ℝ → ℝ} (hp : ContinuousOn p (Icc t₀ (t₀ + T)))
    (hp0 : ∀ t ∈ Icc t₀ (t₀ + T), 0 ≤ p t) (_hg : ContinuousOn g (Icc t₀ (t₀ + T)))
    (hgm : MonotoneOn g (Icc t₀ (t₀ + T))) (hφ : ContinuousOn φ (Icc t₀ (t₀ + T)))
    (h : ∀ t ∈ Icc t₀ (t₀ + T), φ t ≤ g t + ∫ τ in t₀..t, p τ * φ τ) :
    ∀ t ∈ Icc t₀ (t₀ + T), φ t ≤ g t * Real.exp (∫ τ in t₀..t, p τ) := fun _ ht =>
  Gronwall.le_mul_exp_integral_of_continuousOn hp hp0 hgm hφ h ht

end QuarteroniSaccoSaleri.Chapter11
