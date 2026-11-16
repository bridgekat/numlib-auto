/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Numlib.Analysis.ODE.PicardLindelof

/-!
# The Cauchy problem on a normed space

Let $E$ be a real normed space and let $f \colon \mathbb{R} \times E \to E$ be a time-dependent
field. The **Cauchy problem** is
$$y'(t) = f(t, y(t)), \qquad y(t_0) = y_0,$$
as the numerical-analysis texts state it ([quarteroni2000numerical], §11.1 and §11.9;
[kress1998numerical], §10.1). This file defines a solution on a set of times $I$, with the
derivative taken within $I$, and proves that for a continuous field it is equivalent to the integral
equation $y(t) = y_0 + \int_{t_0}^t f(\tau, y(\tau)) \, d\tau$. It defines the Liapunov stability
and the asymptotic stability of the problem under simultaneous perturbations of the datum and of the
source. For a field that is $L$-Lipschitz in the state it proves the estimate
$$\|y(t) - z(t)\| \le (1 + (t - t_0)) \, \varepsilon \, e^{L (t - t_0)}$$
between a solution $y$ and a solution $z$ of a problem perturbed by at most $\varepsilon$, and the
stability that follows.

The file also proves existence and uniqueness of solutions. For a field continuous on
$[a, b] \times E$ and uniformly Lipschitz in the state, a solution exists on the whole interval
$[a, b]$, and it is unique. For a field Lipschitz on a box, a unique local solution exists, with the
constants of [quarteroni2000numerical]. For a field Lipschitz in the state on $[t_0, \infty)$, a
unique solution exists on the whole half-line; this is the Cauchy–Lipschitz–Picard theorem, Theorem
7.3 of [brezis2011functional].

## Main definitions

* `ODE.IsSolutionOn`: $y$ solves the Cauchy problem on the set of times $I$.
* `ODE.IsLiapunovStable`: the Liapunov stability of the Cauchy problem on $I$.
* `ODE.IsAsymptoticallyStable`: the asymptotic stability of the Cauchy problem on $[t_0, \infty)$.
* `ODE.picardMap`: the Picard operator $\alpha \mapsto y_0 + \int_{t_0}^t f(\tau, \alpha(\tau)) \,
  d\tau$ on $C([a, b], E)$.

## Main results

* `ODE.isSolutionOn_iff_integral`: for a continuous field, a continuous curve solves the problem on
  $[a, b]$ if and only if it satisfies the integral equation.
* `ODE.norm_sub_le_of_lipschitz`: the stability estimate for a field that is Lipschitz in the state.
* `ODE.isLiapunovStable_of_lipschitz`: such a problem is Liapunov stable on every bounded interval
  $[t_0, t_0 + T]$.
* `ODE.isSolutionOn_unique_of_lipschitz`: two solutions on $[t_0, t_0 + T]$ agree.
* `ODE.dist_iterate_picardMap_le`: the $n$-th iterate of the Picard operator is Lipschitz with
  constant $(K (b - a))^n / n!$.
* `ODE.exists_isSolutionOn_of_lipschitz` and `ODE.existsUnique_isSolutionOn_of_lipschitz`: global
  existence, and existence with uniqueness, on a compact interval.
* `ODE.exists_isSolutionOn_of_lipschitzOnWith`: local existence and uniqueness for a field that is
  Lipschitz on a box.
* `ODE.exists_isSolutionOn_Ici_of_lipschitz`, `ODE.isSolutionOn_unique_of_lipschitz_Ici` and
  `ODE.existsUnique_isSolutionOn_Ici_of_lipschitz`: the Cauchy–Lipschitz–Picard theorem on the
  half-line.

## Proof outline

The stability estimate comes from the differential Gronwall inequality: $w = z - y$ has right
derivative of norm at most $L \|w\| + \varepsilon$. The texts derive the same estimate from the
integral form of Gronwall's lemma, which needs the integral equation and hence continuity of the
field; the differential route needs neither.

Global existence on $[a, b]$ follows the classical route. The Picard operator on the complete space
$C([a, b], E)$ has $n$-th iterate Lipschitz with constant $(K (b - a))^n / n!$, so some iterate is a
contraction, and the fixed point solves the problem. The solution on the half-line is glued from the
solutions on the intervals $[t_0, t_0 + n]$, which agree on overlaps by uniqueness.

## Implementation notes

* A solution on $I$ has its derivative taken within $I$, so on $[a, b]$ the endpoints carry
  one-sided derivatives and no case split is needed.
* Time sets are $[a, b]$ with $t_0 \in [a, b]$ where the argument is two-sided (the integral
  equation, existence), and $[t_0, t_0 + T]$ where it runs forward in time (the stability estimate,
  a right-derivative Gronwall argument). The interval $[t_0, t_0 + T]$ of the texts is the latter.
* Lipschitz constants are in `ℝ≥0`, as in Mathlib's `LipschitzWith`. Joint continuity of the field
  on $[a, b] \times E$ is `ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ)`.
* Mathlib has the two halves of the integral characterization, `ODE.hasDerivWithinAt_picard_Icc` and
  `ODE.picard_eq_of_hasDerivAt`, in `Mathlib.Analysis.ODE.PicardLindelof`. Local existence and
  uniqueness on a ball is `IsPicardLindelof` with
  `IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt` of
  `Numlib.Analysis.ODE.PicardLindelof`. The differential Gronwall inequality is
  `norm_le_gronwallBound_of_norm_deriv_right_le` of `Mathlib.Analysis.ODE.Gronwall`; the integral
  form is `Gronwall.le_mul_exp_of_le_add_integral` of `Numlib.Analysis.ODE.Gronwall`.
* Mathlib lacks global existence for a globally Lipschitz field. `IsPicardLindelof` bounds the
  length of the time interval by $a / L$, with $L$ a bound of the field on a ball of radius $a$. A
  globally $K$-Lipschitz field grows linearly on large balls, so the constraint caps the length of
  the interval at $1/K$. The texts carry the same artefact ($r_0 < 1/L$ in §11.1 of
  [quarteroni2000numerical]). The Picard operator on $C([a, b], E)$ removes it.
-/

open Set Filter Topology Metric Function
open scoped NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E → E} {t₀ a b T : ℝ} {y₀ : E} {I : Set ℝ} {y z : ℝ → E} {K : ℝ≥0}

/-! ### Solutions of the Cauchy problem -/

/-- A **solution of the Cauchy problem** $y' = f(t, y)$, $y(t_0) = y_0$ on the set of times
$I \subseteq \mathbb{R}$ is a curve $y \colon \mathbb{R} \to E$ with $y(t_0) = y_0$ such that,
at every $t \in I$, the derivative of $y$ within $I$ is $f(t, y(t))$. This is the problem (11.1)
and (11.78) of [quarteroni2000numerical].

At the endpoints of an interval the derivative is one-sided. The point $t_0$ need not lie in
$I$. -/
def IsSolutionOn (f : ℝ → E → E) (t₀ : ℝ) (y₀ : E) (I : Set ℝ) (y : ℝ → E) : Prop :=
  y t₀ = y₀ ∧ ∀ t ∈ I, HasDerivWithinAt y (f t (y t)) I t

/-- A solution satisfies $y(t_0) = y_0$. -/
theorem IsSolutionOn.apply_eq (h : IsSolutionOn f t₀ y₀ I y) : y t₀ = y₀ := h.1

/-- A solution on $I$ has derivative $f(t, y(t))$ within $I$ at every $t \in I$. -/
theorem IsSolutionOn.hasDerivWithinAt (h : IsSolutionOn f t₀ y₀ I y) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt y (f t (y t)) I t :=
  h.2 t ht

/-- A solution of the Cauchy problem on $I$ is continuous on $I$. -/
theorem IsSolutionOn.continuousOn (h : IsSolutionOn f t₀ y₀ I y) : ContinuousOn y I :=
  HasDerivWithinAt.continuousOn h.2

/-- A solution of the Cauchy problem on $I$ is a solution on every subset $J \subseteq I$. -/
theorem IsSolutionOn.mono (h : IsSolutionOn f t₀ y₀ I y) {J : Set ℝ} (hJ : J ⊆ I) :
    IsSolutionOn f t₀ y₀ J y :=
  ⟨h.1, fun t ht => (h.2 t (hJ ht)).mono hJ⟩

/-- Let $y$ solve the Cauchy problem on $I$, and let $z$ agree with $y$ on $I$ and satisfy
$z(t_0) = y_0$. Then $z$ solves the Cauchy problem on $I$.

Being a solution on $I$ depends only on the values on $I$ and at $t_0$. -/
theorem IsSolutionOn.congr (h : IsSolutionOn f t₀ y₀ I y) (hz : EqOn z y I) (hz₀ : z t₀ = y₀) :
    IsSolutionOn f t₀ y₀ I z :=
  ⟨hz₀, fun t ht => by rw [hz ht]; exact (h.2 t ht).congr hz (hz ht)⟩

/-- Let $y$ solve the Cauchy problem on $I$ for a field $f$ continuous on $I \times E$. Then
$t \mapsto f(t, y(t))$ is continuous on $I$.

So the derivative of $y$ is continuous: $y \in C^1(I)$ in the terms of the texts. -/
theorem IsSolutionOn.continuousOn_deriv (h : IsSolutionOn f t₀ y₀ I y)
    (hf : ContinuousOn (uncurry f) (I ×ˢ univ)) : ContinuousOn (fun t => f t (y t)) I :=
  continuousOn_comp hf h.continuousOn (mapsTo_univ _ _)

/-- The **integral form of the Cauchy problem**. Let $E$ be a Banach space, let $t_0 \in [a, b]$,
let $f$ be continuous on $[a, b] \times E$, and let $y$ be continuous on $[a, b]$. Then $y$
solves the Cauchy problem on $[a, b]$ if and only if
$$y(t) = y_0 + \int_{t_0}^t f(\tau, y(\tau)) \, d\tau \quad \text{for every } t \in [a, b].$$
This is (11.2) of [quarteroni2000numerical].

The forward direction is the fundamental theorem of calculus (`ODE.picard_eq_of_hasDerivAt`),
and the reverse direction is the differentiation of the primitive
(`ODE.hasDerivWithinAt_picard_Icc`). The continuity of $y$ enters only through the integrability
of $\tau \mapsto f(\tau, y(\tau))$, and the forward direction provides it. -/
theorem isSolutionOn_iff_integral [CompleteSpace E] (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (hy : ContinuousOn y (Icc a b)) :
    IsSolutionOn f t₀ y₀ (Icc a b) y ↔ ∀ t ∈ Icc a b, y t = y₀ + ∫ τ in t₀..t, f τ (y τ) := by
  constructor
  · intro h t ht
    have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ ht
    have := picard_eq_of_hasDerivAt (f := f) (u := univ) (hf.mono (prod_mono hsub subset_rfl))
      (fun t' ht' => (h.2 t' (hsub ht')).mono hsub) (mapsTo_univ _ _)
    rw [picard_apply, h.1] at this
    exact this.symm
  · intro h
    refine ⟨?_, fun t ht => ?_⟩
    · rw [h t₀ ht₀, intervalIntegral.integral_same, add_zero]
    · exact (hasDerivWithinAt_picard_Icc (f := f) (u := univ) ht₀ hf hy (fun _ _ => mem_univ _)
        y₀ ht).congr (fun t' ht' => h t' ht') (h t ht)

/-! ### Liapunov stability -/

/-- **Liapunov stability** of the Cauchy problem $y' = f(t, y)$, $y(t_0) = y_0$ on the set of times
$I$. The problem is Liapunov stable on $I$ if there is a constant $C > 0$ with the following
property. For every $\varepsilon > 0$ and every perturbation $(\delta_0, \delta)$ of the datum
and of the source with $\|\delta_0\| < \varepsilon$, $\delta$ continuous on $I$ and
$\|\delta(t)\| < \varepsilon$ on $I$, every solution $y$ of the problem on $I$ and every
solution $z$ on $I$ of the perturbed problem
$$z' = f(t, z) + \delta(t), \qquad z(t_0) = y_0 + \delta_0$$
satisfy $\|y(t) - z(t)\| < C \varepsilon$ for every $t \in I$. This is Definition 11.1 of
[quarteroni2000numerical], with the perturbed problem (11.4) and the bound (11.5).

The constant $C$ does not depend on $\varepsilon$. The source restricts to $\varepsilon$ small
enough for the perturbed solution to exist. The definition quantifies over the solutions that
exist, so the condition holds vacuously when none exists. -/
def IsLiapunovStable (f : ℝ → E → E) (t₀ : ℝ) (y₀ : E) (I : Set ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ (δ₀ : E) (δ : ℝ → E), ‖δ₀‖ < ε → ContinuousOn δ I →
    (∀ t ∈ I, ‖δ t‖ < ε) → ∀ y z : ℝ → E, IsSolutionOn f t₀ y₀ I y →
      IsSolutionOn (fun t v => f t v + δ t) t₀ (y₀ + δ₀) I z → ∀ t ∈ I, ‖y t - z t‖ < C * ε

/-- **Asymptotic stability** of the Cauchy problem. The problem is asymptotically stable if it is
Liapunov stable on every interval $[t_0, t_0 + T]$ with $T > 0$, and if there is
$\varepsilon > 0$ with the following property. For every perturbation with
$\|\delta_0\| < \varepsilon$, $\delta$ continuous on $[t_0, \infty)$ and
$\|\delta(t)\| < \varepsilon$ on $[t_0, \infty)$, every solution $y$ of the problem and every
solution $z$ of the perturbed problem on $[t_0, \infty)$ satisfy $\|y(t) - z(t)\| \to 0$ as
$t \to \infty$. This is (11.6) of [quarteroni2000numerical]. -/
def IsAsymptoticallyStable (f : ℝ → E → E) (t₀ : ℝ) (y₀ : E) : Prop :=
  (∀ T : ℝ, 0 < T → IsLiapunovStable f t₀ y₀ (Icc t₀ (t₀ + T))) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ₀ : E) (δ : ℝ → E), ‖δ₀‖ < ε → ContinuousOn δ (Ici t₀) →
      (∀ t ∈ Ici t₀, ‖δ t‖ < ε) → ∀ y z : ℝ → E, IsSolutionOn f t₀ y₀ (Ici t₀) y →
        IsSolutionOn (fun t v => f t v + δ t) t₀ (y₀ + δ₀) (Ici t₀) z →
          Tendsto (fun t => ‖y t - z t‖) atTop (𝓝 0)

/-- Let $K \ge 0$ and $\varepsilon \ge 0$. For every $s \in \mathbb{R}$, Mathlib's Gronwall bound
with $\delta = \varepsilon$ satisfies
$$\mathtt{gronwallBound}(\varepsilon, K, \varepsilon, s) \le (1 + s) \, \varepsilon \, e^{K
  s}.$$

Here $\mathtt{gronwallBound}(\delta, K, \varepsilon, s) = \delta e^{K s} + (\varepsilon /
K)(e^{K s} - 1)$ for $K \ne 0$ and $\delta + \varepsilon s$ for $K = 0$. For $K > 0$ the
inequality is $(e^{K s} - 1)/K \le s e^{K s}$, that is, $1 - K s \le e^{-K s}$. The right side
is the closed form of the texts. -/
theorem gronwallBound_le_mul_exp {K ε s : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound ε K ε s ≤ (1 + s) * ε * Real.exp (K * s) := by
  rcases eq_or_lt_of_le hK with rfl | hK
  · rw [gronwallBound_K0, zero_mul, Real.exp_zero]
    nlinarith
  · rw [gronwallBound_of_K_ne_0 hK.ne']
    have h1 : (1 - K * s) * Real.exp (K * s) ≤ 1 := by
      calc (1 - K * s) * Real.exp (K * s) ≤ Real.exp (-(K * s)) * Real.exp (K * s) := by
            gcongr
            linarith [Real.add_one_le_exp (-(K * s))]
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h2 : ε / K * (Real.exp (K * s) - 1) ≤ s * ε * Real.exp (K * s) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK]
      have : Real.exp (K * s) - 1 ≤ K * s * Real.exp (K * s) := by nlinarith
      calc ε * (Real.exp (K * s) - 1) ≤ ε * (K * s * Real.exp (K * s)) := by gcongr
        _ = s * ε * Real.exp (K * s) * K := by ring
    nlinarith

/-- The **stability estimate** of §11.1 of [quarteroni2000numerical]. Suppose that $f(t, \cdot)$ is
$L$-Lipschitz for every $t \in [t_0, t_0 + T]$. Let $\|\delta_0\| \le \varepsilon$ and
$\|\delta(t)\| \le \varepsilon$ for $t \in [t_0, t_0 + T]$. Let $y$ solve the Cauchy problem on
$[t_0, t_0 + T]$, and let $z$ solve the perturbed problem $z' = f(t, z) + \delta(t)$,
$z(t_0) = y_0 + \delta_0$ there. Then for every $t \in [t_0, t_0 + T]$,
$$\|y(t) - z(t)\| \le (1 + (t - t_0)) \, \varepsilon \, e^{L (t - t_0)}.$$

No continuity of $f$ or $\delta$ is needed. The difference $w = z - y$ has right derivative
$f(t, z) + \delta - f(t, y)$ of norm at most $L \|w\| + \varepsilon$. So Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le` bounds $\|w(t)\|$ by the Gronwall bound at
$t - t_0$, and `ODE.gronwallBound_le_mul_exp` bounds this by the closed form. The source applies
its integral Gronwall lemma (Lemma 11.1, here `Gronwall.le_mul_exp_of_le_add_integral`) to
$\|w(t)\| \le (1 + (t - t_0)) \varepsilon + L \int_{t_0}^t \|w\|$ instead, which needs the
integral equation and hence continuity of $f$. -/
theorem norm_sub_le_of_lipschitz {L : ℝ≥0} (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t))
    {δ₀ : E} {δ : ℝ → E} {ε : ℝ} (hδ₀ : ‖δ₀‖ ≤ ε) (hδ : ∀ t ∈ Icc t₀ (t₀ + T), ‖δ t‖ ≤ ε)
    (hy : IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hz : IsSolutionOn (fun t v => f t v + δ t) t₀ (y₀ + δ₀) (Icc t₀ (t₀ + T)) z) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + T)) :
    ‖y t - z t‖ ≤ (1 + (t - t₀)) * ε * Real.exp (L * (t - t₀)) := by
  have hwc : ContinuousOn (fun s => z s - y s) (Icc t₀ (t₀ + T)) :=
    hz.continuousOn.sub hy.continuousOn
  have hw' : ∀ s ∈ Ico t₀ (t₀ + T),
      HasDerivWithinAt (fun s => z s - y s) (f s (z s) + δ s - f s (y s)) (Ici s) s := fun s hs =>
    ((hz.hasDerivWithinAt (Ico_subset_Icc_self hs)).sub
      (hy.hasDerivWithinAt (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hw0 : ‖z t₀ - y t₀‖ ≤ ε := by rw [hz.1, hy.1, add_sub_cancel_left]; exact hδ₀
  have bound : ∀ s ∈ Ico t₀ (t₀ + T),
      ‖f s (z s) + δ s - f s (y s)‖ ≤ L * ‖z s - y s‖ + ε := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    calc ‖f s (z s) + δ s - f s (y s)‖ = ‖(f s (z s) - f s (y s)) + δ s‖ := by congr 1; abel
      _ ≤ ‖f s (z s) - f s (y s)‖ + ‖δ s‖ := norm_add_le _ _
      _ ≤ L * ‖z s - y s‖ + ε := add_le_add ((hf s hs').norm_sub_le _ _) (hδ s hs')
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hwc hw' hw0 bound t ht
  rw [norm_sub_rev]
  exact key.trans (gronwallBound_le_mul_exp L.coe_nonneg ((norm_nonneg _).trans hδ₀))

/-- A **Lipschitz field gives a Liapunov stable Cauchy problem**. Let $T \ge 0$ and suppose that
$f(t, \cdot)$ is $L$-Lipschitz for every $t \in [t_0, t_0 + T]$. Then for every datum $y_0$, the
Cauchy problem is Liapunov stable on $[t_0, t_0 + T]$. This is §11.1 of
[quarteroni2000numerical].

The constant is the one of the source, $C = (1 + K_I) e^{L K_I}$ with $K_I = T$. The strict
inequality comes from `ODE.norm_sub_le_of_lipschitz` applied with the maximum of $\|\delta_0\|$
and of $\|\delta\|$ on the compact interval, which is less than $\varepsilon$. -/
theorem isLiapunovStable_of_lipschitz (hT : 0 ≤ T) {L : ℝ≥0}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t)) (y₀ : E) :
    IsLiapunovStable f t₀ y₀ (Icc t₀ (t₀ + T)) := by
  refine ⟨(1 + T) * Real.exp (L * T), by positivity,
    fun ε hε δ₀ δ hδ₀ hδc hδ y z hy hz t ht => ?_⟩
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith))
    (continuous_norm.comp_continuousOn hδc)
  have hε' : max ‖δ₀‖ ‖δ s‖ < ε := max_lt hδ₀ (hδ s hs)
  have h1 : ‖δ₀‖ ≤ max ‖δ₀‖ ‖δ s‖ := le_max_left _ _
  have h2 : ∀ t ∈ Icc t₀ (t₀ + T), ‖δ t‖ ≤ max ‖δ₀‖ ‖δ s‖ := fun t ht =>
    (hmax ht : ‖δ t‖ ≤ ‖δ s‖).trans (le_max_right _ _)
  have hsT : t - t₀ ≤ T := by linarith [ht.2]
  calc ‖y t - z t‖ ≤ (1 + (t - t₀)) * max ‖δ₀‖ ‖δ s‖ * Real.exp (L * (t - t₀)) :=
        norm_sub_le_of_lipschitz hf h1 h2 hy hz ht
    _ ≤ (1 + T) * max ‖δ₀‖ ‖δ s‖ * Real.exp (L * T) := by gcongr
    _ = (1 + T) * Real.exp (L * T) * max ‖δ₀‖ ‖δ s‖ := by ring
    _ < (1 + T) * Real.exp (L * T) * ε := by gcongr

/-- **Uniqueness for a Lipschitz field**. Suppose that $f(t, \cdot)$ is $K$-Lipschitz for every
$t \in [t_0, t_0 + T]$. Then two solutions of the Cauchy problem on $[t_0, t_0 + T]$ agree on
$[t_0, t_0 + T]$.

This is the stability estimate with $\varepsilon = 0$. -/
theorem isSolutionOn_unique_of_lipschitz (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith K (f t))
    (hy : IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hz : IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + T)) z) : EqOn y z (Icc t₀ (t₀ + T)) := by
  intro t ht
  have hz' : IsSolutionOn (fun t v => f t v + (0 : ℝ → E) t) t₀ (y₀ + 0) (Icc t₀ (t₀ + T)) z := by
    simpa using hz
  have := norm_sub_le_of_lipschitz hf (δ₀ := 0) (ε := 0) (by simp) (fun _ _ => by simp) hy hz' ht
  rw [mul_zero, zero_mul] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-! ### Global existence: the Picard operator on $C([a, b], E)$ -/

section Existence

/-- Let $a \le b$, let $f$ be continuous on $[a, b] \times E$, and let $\alpha \in C([a, b], E)$,
extended to $\mathbb{R}$ by `Set.IccExtend`. Then $\tau \mapsto f(\tau, \alpha(\tau))$ is
continuous on $[a, b]$. -/
theorem continuousOn_comp_iccExtend (hab : a ≤ b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (α : C(Icc a b, E)) :
    ContinuousOn (fun τ => f τ (IccExtend hab α τ)) (Icc a b) :=
  continuousOn_comp hf α.continuous.Icc_extend'.continuousOn (mapsTo_univ _ _)

/-- Let $a \le b$, $t_0 \in [a, b]$, let $f$ be continuous on $[a, b] \times E$, and let
$\alpha \in C([a, b], E)$, extended to $\mathbb{R}$ by `Set.IccExtend`. Then
$\tau \mapsto f(\tau, \alpha(\tau))$ is interval integrable between $t_0$ and every
$t \in [a, b]$. -/
theorem intervalIntegrable_comp_iccExtend (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (α : C(Icc a b, E)) (t : Icc a b) :
    IntervalIntegrable (fun τ => f τ (IccExtend hab α τ)) MeasureTheory.volume t₀ t :=
  ((continuousOn_comp_iccExtend hab hf α).mono (uIcc_subset_Icc ht₀ t.2)).intervalIntegrable

/-- The **Picard operator** on $C([a, b], E)$. Let $a \le b$, $t_0 \in [a, b]$, and let $f$ be
continuous on $[a, b] \times E$. The Picard operator sends $\alpha \in C([a, b], E)$ to the
continuous function
$$t \mapsto y_0 + \int_{t_0}^t f(\tau, \alpha(\tau)) \, d\tau,$$
the right side of the integral equation (11.2) of [quarteroni2000numerical].

Inside the integral, $\alpha$ is extended to $\mathbb{R}$ by `Set.IccExtend`. The fixed points
are the solutions of the Cauchy problem on $[a, b]$, by `ODE.isSolutionOn_iff_integral`. -/
noncomputable def picardMap (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E) (α : C(Icc a b, E)) :
    C(Icc a b, E) where
  toFun t := y₀ + ∫ τ in t₀..t, f τ (IccExtend hab α τ)
  continuous_toFun := by
    have h : ContinuousOn (fun t : ℝ => y₀ + ∫ τ in t₀..t, f τ (IccExtend hab α τ)) (Icc a b) := by
      refine continuousOn_const.add ?_
      have := intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume)
        (f := fun τ => f τ (IccExtend hab α τ)) (b₁ := a) (b₂ := b)
        ((continuousOn_comp_iccExtend hab hf α).mono
          (uIcc_subset_Icc (left_mem_Icc.2 hab) (right_mem_Icc.2 hab))).intervalIntegrable
        (by rwa [uIcc_of_le hab])
      rwa [uIcc_of_le hab] at this
    exact h.comp_continuous continuous_subtype_val fun t => t.2

/-- The Picard operator sends $\alpha$ to $t \mapsto y_0 + \int_{t_0}^t f(\tau, \alpha(\tau)) \,
d\tau$, with $\alpha$ extended to $\mathbb{R}$ by `Set.IccExtend`. -/
theorem picardMap_apply (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E) (α : C(Icc a b, E))
    (t : Icc a b) :
    picardMap hab ht₀ hf y₀ α t = y₀ + ∫ τ in t₀..t, f τ (IccExtend hab α τ) :=
  rfl

/-- The **factorial estimate for the Picard iterates**, pointwise. Let $P$ be the Picard operator on
$C([a, b], E)$, and suppose that $f(t, \cdot)$ is $K$-Lipschitz for every $t \in [a, b]$. Then
for all $\alpha, \beta \in C([a, b], E)$, every $n \in \mathbb{N}$ and every $t \in [a, b]$,
$$\|P^n \alpha(t) - P^n \beta(t)\| \le \frac{(K |t - t_0|)^n}{n!} \, d(\alpha, \beta),$$
where $d$ is the supremum distance.

The proof is by induction on $n$, with $\int_{t_0}^t |\tau - t_0|^n \, d\tau = |t - t_0|^{n+1} /
(n + 1)$. This is the estimate of Mathlib's `ODE.FunSpace.dist_iterate_next_apply_le`, for the
Picard operator on all of $C([a, b], E)$, where the Lipschitz condition holds everywhere and no
ball is needed. -/
theorem dist_iterate_picardMap_apply_le (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E)
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t)) (α β : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist ((picardMap hab ht₀ hf y₀)^[n] α t) ((picardMap hab ht₀ hf y₀)^[n] β t) ≤
      (K * |(t : ℝ) - t₀|) ^ n / n.factorial * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dist_eq_norm, picardMap_apply,
      picardMap_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (intervalIntegrable_comp_iccExtend hab ht₀ hf _ t)
        (intervalIntegrable_comp_iccExtend hab ht₀ hf _ t)]
    calc
      _ ≤ ∫ τ in uIoc t₀ (t : ℝ), (K : ℝ) ^ (n + 1) * |τ - t₀| ^ n / n.factorial * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply (MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono
        intro τ hτ
        have hτ' : τ ∈ Icc a b := (uIcc_subset_Icc ht₀ t.2) (uIoc_subset_uIcc hτ)
        rw [← dist_eq_norm, IccExtend_of_mem _ _ hτ', IccExtend_of_mem _ _ hτ']
        calc dist (f τ ((picardMap hab ht₀ hf y₀)^[n] α ⟨τ, hτ'⟩))
              (f τ ((picardMap hab ht₀ hf y₀)^[n] β ⟨τ, hτ'⟩))
            ≤ K * dist ((picardMap hab ht₀ hf y₀)^[n] α ⟨τ, hτ'⟩)
                ((picardMap hab ht₀ hf y₀)^[n] β ⟨τ, hτ'⟩) := (hlip τ hτ').dist_le_mul _ _
          _ ≤ K * ((K * |τ - t₀|) ^ n / n.factorial * dist α β) := by
              gcongr
              exact ih ⟨τ, hτ'⟩
          _ = (K : ℝ) ^ (n + 1) * |τ - t₀| ^ n / n.factorial * dist α β := by
              rw [mul_pow, pow_succ]; ring
      _ ≤ (K * |(t : ℝ) - t₀|) ^ (n + 1) / (n + 1).factorial * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

/-- The **factorial estimate for the Picard iterates**. Let $P$ be the Picard operator on
$C([a, b], E)$, and suppose that $f(t, \cdot)$ is $K$-Lipschitz for every $t \in [a, b]$. Then
for all $\alpha, \beta \in C([a, b], E)$ and every $n \in \mathbb{N}$,
$$d(P^n \alpha, P^n \beta) \le \frac{(K (b - a))^n}{n!} \, d(\alpha, \beta),$$
where $d$ is the supremum distance of $C([a, b], E)$. -/
theorem dist_iterate_picardMap_le (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E)
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t)) (α β : C(Icc a b, E)) (n : ℕ) :
    dist ((picardMap hab ht₀ hf y₀)^[n] α) ((picardMap hab ht₀ hf y₀)^[n] β) ≤
      (K * (b - a)) ^ n / n.factorial * dist α β := by
  rw [ContinuousMap.dist_le (by positivity)]
  intro t
  refine (dist_iterate_picardMap_apply_le hab ht₀ hf y₀ hlip α β n t).trans ?_
  have habs : |(t : ℝ) - t₀| ≤ b - a := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [t.2.1, t.2.2, ht₀.1, ht₀.2]
  gcongr

/-- Suppose that $f(t, \cdot)$ is $K$-Lipschitz for every $t \in [a, b]$. Then some iterate $P^n$ of
the Picard operator is a contraction of $C([a, b], E)$, whatever the Lipschitz constant and the
length of the interval.

The reason is $(K (b - a))^n / n! \to 0$. -/
theorem exists_contractingWith_iterate_picardMap (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E)
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t)) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (picardMap hab ht₀ hf y₀)^[n] := by
  obtain ⟨n, hn⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * (b - a))).eventually
    (gt_mem_nhds zero_lt_one)).exists
  have h0 : (0 : ℝ) ≤ ((K : ℝ) * (b - a)) ^ n / n.factorial := by positivity
  exact ⟨n, ⟨_, h0⟩, hn, LipschitzWith.of_dist_le_mul fun α β =>
    dist_iterate_picardMap_le hab ht₀ hf y₀ hlip α β n⟩

variable [CompleteSpace E]

/-- **Global existence**. Let $E$ be a Banach space, let $t_0 \in [a, b]$, let $f$ be continuous on
$[a, b] \times E$, and suppose that $f(t, \cdot)$ is $K$-Lipschitz for every $t \in [a, b]$.
Then for every datum $y_0$, the Cauchy problem has a solution on the whole interval $[a, b]$.
This is item 2 of §11.1 of [quarteroni2000numerical] (Property 11.5).

The solution is the fixed point of the Picard operator on $C([a, b], E)$, some iterate of which
is a contraction (`ODE.exists_contractingWith_iterate_picardMap`). It solves the problem by
`ODE.isSolutionOn_iff_integral`. -/
theorem exists_isSolutionOn_of_lipschitz (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t))
    (y₀ : E) : ∃ y : ℝ → E, IsSolutionOn f t₀ y₀ (Icc a b) y := by
  have hab : a ≤ b := ht₀.1.trans ht₀.2
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_picardMap hab ht₀ hf y₀ hlip
  obtain ⟨α, hα⟩ : ∃ α, IsFixedPt (picardMap hab ht₀ hf y₀) α :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  refine ⟨IccExtend hab α, ?_⟩
  rw [isSolutionOn_iff_integral ht₀ hf α.continuous.Icc_extend'.continuousOn]
  intro t ht
  rw [IccExtend_of_mem _ _ ht]
  calc α ⟨t, ht⟩ = picardMap hab ht₀ hf y₀ α ⟨t, ht⟩ := by rw [hα]
    _ = y₀ + ∫ τ in t₀..t, f τ (IccExtend hab α τ) := rfl

/-- **Global existence and uniqueness**. Let $E$ be a Banach space, let $T \ge 0$, let $f$ be
continuous on $[t_0, t_0 + T] \times E$, and suppose that $f(t, \cdot)$ is $K$-Lipschitz for
every $t \in [t_0, t_0 + T]$. Then for every datum $y_0$ there is exactly one
$y \colon \mathbb{R} \to E$ that solves the Cauchy problem on $[t_0, t_0 + T]$ and equals $y_0$
outside this interval. This is item 2 of §11.1 of [quarteroni2000numerical] (Property 11.5).

The values outside the interval are fixed so that uniqueness of a function on $\mathbb{R}$ makes
sense. `ODE.IsSolutionOn.continuousOn_deriv` adds that $t \mapsto f(t, y(t))$ is continuous on
the interval, that is, $y \in C^1$. -/
theorem existsUnique_isSolutionOn_of_lipschitz (hT : 0 ≤ T)
    (hf : ContinuousOn (uncurry f) (Icc t₀ (t₀ + T) ×ˢ univ))
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith K (f t)) (y₀ : E) :
    ∃! y : ℝ → E, IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + T)) y ∧ ∀ t ∉ Icc t₀ (t₀ + T), y t = y₀ := by
  classical
  have ht₀ : t₀ ∈ Icc t₀ (t₀ + T) := left_mem_Icc.2 (by linarith)
  obtain ⟨y, hy⟩ := exists_isSolutionOn_of_lipschitz ht₀ hf hlip y₀
  refine ⟨fun t => if t ∈ Icc t₀ (t₀ + T) then y t else y₀,
    ⟨hy.congr (fun t ht => ite_eq_left ht) (by simp [ht₀, hy.1]), fun t ht => ite_eq_right ht⟩, ?_⟩
  rintro z ⟨hz, hz'⟩
  funext t
  by_cases ht : t ∈ Icc t₀ (t₀ + T)
  · rw [ite_eq_left ht]
    exact isSolutionOn_unique_of_lipschitz hlip hz hy ht
  · rw [ite_eq_right ht, hz' t ht]

/-- **Local existence and uniqueness**, with the constants of the source. Let $E$ be a Banach space,
let $J = [t_0 - r_J, t_0 + r_J]$ and $\Sigma = \bar B(y_0, r_\Sigma)$ with $r_\Sigma \ge 0$. Let
$f$ be continuous on $J \times \Sigma$, let $f(t, \cdot)$ be $K$-Lipschitz on $\Sigma$ for every
$t \in J$, and let $\|f(t, v)\| \le M$ for $t \in J$ and $v \in \Sigma$. Let $0 < r_0 \le r_J$
with $M r_0 \le r_\Sigma$. Then the Cauchy problem has a solution $y$ on
$[t_0 - r_0, t_0 + r_0]$ with values in $\Sigma$ there, and every solution $z$ on
$[t_0 - r_0, t_0 + r_0]$ with values in $\Sigma$ there agrees with $y$ on this interval. This is
item 1 of §11.1 of [quarteroni2000numerical].

The condition $M r_0 \le r_\Sigma$ is the condition $r_0 < r_\Sigma / M$ of the source. The
proof is Mathlib's Picard–Lindelöf theorem in the form
`IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt`. The third bound $r_0 < 1/L$ of
the source is an artefact of the proof by a contraction in the supremum norm, and is not needed. -/
theorem exists_isSolutionOn_of_lipschitzOnWith {rJ rS r₀ M : ℝ}
    (hf : ContinuousOn (uncurry f) (Icc (t₀ - rJ) (t₀ + rJ) ×ˢ closedBall y₀ rS))
    (hlip : ∀ t ∈ Icc (t₀ - rJ) (t₀ + rJ), LipschitzOnWith K (f t) (closedBall y₀ rS))
    (hM : ∀ t ∈ Icc (t₀ - rJ) (t₀ + rJ), ∀ v ∈ closedBall y₀ rS, ‖f t v‖ ≤ M)
    (hr₀ : 0 < r₀) (hrJ : r₀ ≤ rJ) (hrS : 0 ≤ rS) (hMr : M * r₀ ≤ rS) :
    ∃ y : ℝ → E, IsSolutionOn f t₀ y₀ (Icc (t₀ - r₀) (t₀ + r₀)) y ∧
      (∀ t ∈ Icc (t₀ - r₀) (t₀ + r₀), y t ∈ closedBall y₀ rS) ∧
      ∀ z : ℝ → E, IsSolutionOn f t₀ y₀ (Icc (t₀ - r₀) (t₀ + r₀)) z →
        (∀ t ∈ Icc (t₀ - r₀) (t₀ + r₀), z t ∈ closedBall y₀ rS) →
        EqOn y z (Icc (t₀ - r₀) (t₀ + r₀)) := by
  have hsub : Icc (t₀ - r₀) (t₀ + r₀) ⊆ Icc (t₀ - rJ) (t₀ + rJ) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have ht₀J : t₀ ∈ Icc (t₀ - rJ) (t₀ + rJ) := ⟨by linarith, by linarith⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ht₀J y₀ (mem_closedBall_self hrS))
  have hPL : IsPicardLindelof f (⟨t₀, by constructor <;> linarith⟩ : Icc (t₀ - r₀) (t₀ + r₀)) y₀
      ⟨rS, hrS⟩ 0 ⟨M, hM0⟩ K :=
    { lipschitzOnWith := fun t ht => hlip t (hsub ht)
      continuousOn := fun v hv =>
        hf.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨hsub ht, hv⟩
      norm_le := fun t ht v hv => hM t (hsub ht) v hv
      mul_max_le := by
        change M * max (t₀ + r₀ - t₀) (t₀ - (t₀ - r₀)) ≤ rS - 0
        rw [add_sub_cancel_left, sub_sub_cancel, max_self, sub_zero]
        exact hMr }
  obtain ⟨α, hα₀, hmem, hα, huniq⟩ := hPL.exists_unique_mem_closedBall_hasDerivWithinAt
    (x := y₀) (by simp) ⟨by linarith, by linarith⟩
  exact ⟨α, ⟨hα₀, hα⟩, hmem, fun z hz hzmem => huniq z hz.1 hzmem hz.2⟩

/-!
### The half-line: the Cauchy–Lipschitz–Picard theorem

Theorem 7.3 of [brezis2011functional] states that, for a field that is Lipschitz in the state on all
of $[t_0, \infty)$, the Cauchy problem has exactly one solution on the whole half-line. The source
runs the contraction in the weighted space $\{u \in C([0, \infty); E) : \sup_t e^{-kt} \|u(t)\| <
\infty\}$ with $k > L$. Here the solutions on the compact intervals $[t_0, t_0 + n]$ given by
`ODE.exists_isSolutionOn_of_lipschitz` are glued instead, since they agree on overlaps by
`ODE.isSolutionOn_unique_of_lipschitz`.
-/

/-- **Global existence on the half-line**. Let $E$ be a Banach space, let $f$ be continuous on
$[t_0, \infty) \times E$, and suppose that $f(t, \cdot)$ is $K$-Lipschitz for every $t \ge t_0$.
Then for every datum $y_0$ the Cauchy problem has a solution on $[t_0, \infty)$. This is the
existence part of Theorem 7.3 of [brezis2011functional] (Cauchy–Lipschitz–Picard).

The autonomous field $F \colon E \to E$ of the source is $f(t, v) = F(v)$. The solution is glued
from the solutions on the intervals $[t_0, t_0 + n]$. At $t$ it is the value of the solution on
$[t_0, t_0 + \lceil t - t_0 \rceil + 1]$, and it agrees with that solution on this whole
interval, which is a neighbourhood of $t$ within $[t_0, \infty)$. -/
theorem exists_isSolutionOn_Ici_of_lipschitz (hf : ContinuousOn (uncurry f) (Ici t₀ ×ˢ univ))
    (hlip : ∀ t ∈ Ici t₀, LipschitzWith K (f t)) (y₀ : E) :
    ∃ y : ℝ → E, IsSolutionOn f t₀ y₀ (Ici t₀) y := by
  -- the solutions on the compact intervals `[t₀, t₀ + n]`
  have hsol : ∀ n : ℕ, ∃ y : ℝ → E, IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + n)) y := fun n =>
    exists_isSolutionOn_of_lipschitz ⟨le_rfl, by linarith [n.cast_nonneg (α := ℝ)]⟩
      (hf.mono (prod_mono Icc_subset_Ici_self subset_rfl)) (fun t ht => hlip t ht.1) y₀
  choose Y hY using hsol
  -- they agree on their common interval
  have hagree : ∀ m n : ℕ, EqOn (Y m) (Y n) (Icc t₀ (t₀ + (min m n : ℕ))) := fun m n =>
    isSolutionOn_unique_of_lipschitz (T := (min m n : ℕ)) (fun t ht => hlip t ht.1)
      ((hY m).mono (Icc_subset_Icc_right (by gcongr; exact min_le_left m n)))
      ((hY n).mono (Icc_subset_Icc_right (by gcongr; exact min_le_right m n)))
  -- the index of the interval used at time `t`, and the glued function
  set N : ℝ → ℕ := fun t => ⌈t - t₀⌉₊ + 1 with hN
  have hlt : ∀ t, t < t₀ + (N t : ℕ) := fun t => by
    simp only [hN, Nat.cast_add, Nat.cast_one]
    linarith [Nat.le_ceil (t - t₀)]
  refine ⟨fun t => Y (N t) t, ?_, fun t ht => ?_⟩
  · exact (hY (N t₀)).1
  -- on `[t₀, t₀ + N t]` the glued function is the solution `Y (N t)`
  have hcongr : ∀ s ∈ Icc t₀ (t₀ + (N t : ℕ)), Y (N s) s = Y (N t) s := fun s hs =>
    hagree (N s) (N t) ⟨hs.1, by
      rcases min_choice (N s) (N t) with h | h <;> rw [h]
      · exact (hlt s).le
      · exact hs.2⟩
  have hmem : Icc t₀ (t₀ + (N t : ℕ)) ∈ 𝓝[Ici t₀] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (hlt t)))
  have ht' : t ∈ Icc t₀ (t₀ + (N t : ℕ)) := ⟨ht, (hlt t).le⟩
  refine HasDerivWithinAt.mono_of_mem_nhdsWithin ?_ hmem
  exact ((hY (N t)).2 t ht').congr hcongr (hcongr t ht')

omit [CompleteSpace E] in
/-- **Uniqueness on the half-line**. Suppose that $f(t, \cdot)$ is $K$-Lipschitz for every
$t \ge t_0$. Then two solutions of the Cauchy problem on $[t_0, \infty)$ agree on
$[t_0, \infty)$. This is the uniqueness part of Theorem 7.3 of [brezis2011functional].

The proof restricts both solutions to $[t_0, t]$ and applies
`ODE.isSolutionOn_unique_of_lipschitz`. -/
theorem isSolutionOn_unique_of_lipschitz_Ici (hlip : ∀ t ∈ Ici t₀, LipschitzWith K (f t))
    (hy : IsSolutionOn f t₀ y₀ (Ici t₀) y) (hz : IsSolutionOn f t₀ y₀ (Ici t₀) z) :
    EqOn y z (Ici t₀) := fun t ht =>
  isSolutionOn_unique_of_lipschitz (T := t - t₀) (fun s hs => hlip s hs.1)
    (hy.mono Icc_subset_Ici_self) (hz.mono Icc_subset_Ici_self) ⟨ht, by linarith⟩

/-- The **Cauchy–Lipschitz–Picard theorem**. Let $E$ be a Banach space, let $f$ be continuous on
$[t_0, \infty) \times E$, and suppose that $f(t, \cdot)$ is $K$-Lipschitz for every $t \ge t_0$.
Then for every datum $y_0$ there is exactly one $y \colon \mathbb{R} \to E$ that solves the
Cauchy problem on $[t_0, \infty)$ and equals $y_0$ for $t < t_0$. This is Theorem 7.3 of
[brezis2011functional].

The values before $t_0$ are fixed so that uniqueness of a function on $\mathbb{R}$ makes sense,
as in `ODE.existsUnique_isSolutionOn_of_lipschitz`. The condition $u \in C^1([0, \infty); E)$ of
the source is `ODE.IsSolutionOn.continuousOn_deriv`. -/
theorem existsUnique_isSolutionOn_Ici_of_lipschitz
    (hf : ContinuousOn (uncurry f) (Ici t₀ ×ˢ univ))
    (hlip : ∀ t ∈ Ici t₀, LipschitzWith K (f t)) (y₀ : E) :
    ∃! y : ℝ → E, IsSolutionOn f t₀ y₀ (Ici t₀) y ∧ ∀ t < t₀, y t = y₀ := by
  classical
  obtain ⟨y, hy⟩ := exists_isSolutionOn_Ici_of_lipschitz hf hlip y₀
  refine ⟨fun t => if t ∈ Ici t₀ then y t else y₀,
    ⟨hy.congr (fun t ht => ite_eq_left ht) (by simp [hy.1]),
      fun t ht => ite_eq_right (not_le.2 ht)⟩, ?_⟩
  rintro z ⟨hz, hz'⟩
  funext t
  by_cases ht : t ∈ Ici t₀
  · rw [ite_eq_left ht]
    exact isSolutionOn_unique_of_lipschitz_Ici hlip hz hy ht
  · rw [ite_eq_right ht, hz' t (not_le.1 ht)]

end Existence

end ODE
