/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`, beside the derivatives of `rpow`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The smooth regularization $(t^2 + \varepsilon^2)^{p/2} - \varepsilon^p$ of $|t|^p$

For $p = 1$ the function $t \mapsto |t|^p$ is not $C^1$ at the origin. For $\varepsilon > 0$ this
file studies its regularization
$$\varphi_\varepsilon(t) = (t^2 + \varepsilon^2)^{p/2} - \varepsilon^p.$$
The function $\varphi_\varepsilon$ is smooth and vanishes at the origin. For $p \ge 0$ it satisfies
$0 \le \varphi_\varepsilon(t) \le (|t| + \varepsilon)^p$, and for $p \ge 1$ it satisfies
$|\varphi_\varepsilon'(t)| \le p\,(|t| + \varepsilon)^{p-1}$. For $p > 0$,
$\varphi_\varepsilon(t) \to |t|^p$ as $\varepsilon \to 0^+$. This regularization makes Nečas's proof
of the trace inequality work at $p = 1$ (`Numlib.Analysis.Sobolev.Boundary.Trace`): the divergence
theorem is applied to $\varphi_\varepsilon(u)\, w$, and the bounds above survive the passage to the
limit.

The file also proves the mean value bound $A^q - B^q \le q A^{q-1} (A - B)$ for $q \ge 1$ and
$0 < B < A$, which sizes the panels of a graded mesh.

## Main definitions

* `Real.rpowReg`: the regularization $\varphi_\varepsilon(t) = (t^2 + \varepsilon^2)^{p/2} -
  \varepsilon^p$.

## Main results

* `Real.rpowReg_zero`, `Real.rpowReg_nonneg`, `Real.rpowReg_le`: $\varphi_\varepsilon(0) = 0$, and
  $0 \le \varphi_\varepsilon(t) \le (|t| + \varepsilon)^p$ for $p \ge 0$.
* `Real.hasDerivAt_rpowReg`, `Real.contDiff_rpowReg`: $\varphi_\varepsilon'(t) = p\,t\,(t^2 +
  \varepsilon^2)^{p/2 - 1}$, and $\varphi_\varepsilon$ is smooth.
* `Real.abs_deriv_rpowReg_le`: $|\varphi_\varepsilon'(t)| \le p\,(|t| + \varepsilon)^{p-1}$ for
  $p \ge 1$.
* `Real.tendsto_rpowReg`: $\varphi_\varepsilon(t) \to |t|^p$ as $\varepsilon \to 0^+$, for $p > 0$.
* `Real.rpow_sub_rpow_le`: $A^q - B^q \le q A^{q-1} (A - B)$ for $q \ge 1$ and $0 < B < A$.
-/

open Filter Topology

namespace Real

/-- The **regularization of $|t|^p$**: for real numbers $p$, $\varepsilon$ and $t$,
$$\varphi_\varepsilon(t) = (t^2 + \varepsilon^2)^{p/2} - \varepsilon^p.$$
For $\varepsilon > 0$ it is smooth in $t$ and $\varphi_\varepsilon(0) = 0$. Moreover $0 \le
\varphi_\varepsilon(t) \le (|t| + \varepsilon)^p$ for $p \ge 0$, $|\varphi_\varepsilon'(t)| \le
p\,(|t| + \varepsilon)^{p-1}$ for $p \ge 1$, and $\varphi_\varepsilon(t) \to |t|^p$ as
$\varepsilon \to 0^+$ for $p > 0$.

The powers are real powers `Real.rpow`. The regularization makes Nečas's proof of the trace
inequality work at $p = 1$, where $|t|^p$ is not $C^1$. -/
noncomputable def rpowReg (p ε t : ℝ) : ℝ := (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p

variable {p ε : ℝ}

/-- For $\varepsilon > 0$ and every $t \in \mathbb{R}$, $t^2 + \varepsilon^2 > 0$. -/
theorem sq_add_sq_pos (hε : 0 < ε) (t : ℝ) : 0 < t ^ 2 + ε ^ 2 := by positivity

/-- For $\varepsilon > 0$ and every real $p$, $\varphi_\varepsilon(0) = 0$. -/
theorem rpowReg_zero (hε : 0 < ε) : rpowReg p ε 0 = 0 := by
  have h : (0 : ℝ) ^ 2 + ε ^ 2 = ε ^ 2 := by ring
  unfold rpowReg
  rw [sub_eq_zero, h, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
  congr 1
  push_cast
  ring

/-- For $\varepsilon > 0$, $p \ge 0$ and every $t \in \mathbb{R}$, $\varphi_\varepsilon(t) \ge 0$.
-/
theorem rpowReg_nonneg (hε : 0 < ε) (hp : 0 ≤ p) (t : ℝ) : 0 ≤ rpowReg p ε t := by
  unfold rpowReg
  rw [sub_nonneg]
  calc ε ^ p = (ε ^ 2) ^ (p / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
        congr 1
        push_cast
        ring
    _ ≤ (t ^ 2 + ε ^ 2) ^ (p / 2) :=
        Real.rpow_le_rpow (by positivity) (le_add_of_nonneg_left (by positivity))
          (by positivity)

/-- For $\varepsilon > 0$, $p \ge 0$ and every $t \in \mathbb{R}$, $\varphi_\varepsilon(t) \le
(|t| + \varepsilon)^p$. -/
theorem rpowReg_le (hε : 0 < ε) (hp : 0 ≤ p) (t : ℝ) : rpowReg p ε t ≤ (|t| + ε) ^ p := by
  unfold rpowReg
  calc (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p ≤ (t ^ 2 + ε ^ 2) ^ (p / 2) :=
        sub_le_self _ (Real.rpow_nonneg hε.le _)
    _ ≤ ((|t| + ε) ^ 2) ^ (p / 2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        nlinarith [abs_nonneg t, sq_abs t]
    _ = (|t| + ε) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring

/-- For $\varepsilon > 0$, every real $p$ and every $t \in \mathbb{R}$, the function
$\varphi_\varepsilon$ has derivative
$$\varphi_\varepsilon'(t) = p\,t\,(t^2 + \varepsilon^2)^{p/2 - 1}$$
at $t$. -/
theorem hasDerivAt_rpowReg (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (rpowReg p ε) (p * t * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ t ^ 2 + ε ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_pow 2 t).add_const (ε ^ 2))
  have h2 := h1.rpow_const (p := p / 2) (Or.inl (sq_add_sq_pos hε t).ne')
  have h3 : HasDerivAt (fun t : ℝ ↦ (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p)
      (2 * t * (p / 2) * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)) t := h2.sub_const (ε ^ p)
  exact h3.congr_deriv (by ring)

/-- For $\varepsilon > 0$ and every real $p$, the function $\varphi_\varepsilon$ is of class $C^n$
for every $n$, including $n = \infty$ and the analytic class $n = \omega$. -/
theorem contDiff_rpowReg (hε : 0 < ε) {n : WithTop ℕ∞} : ContDiff ℝ n (rpowReg p ε) := by
  unfold rpowReg
  refine ContDiff.sub ?_ contDiff_const
  exact ((contDiff_id.pow 2).add contDiff_const).rpow_const_of_ne fun t ↦ (sq_add_sq_pos hε t).ne'

/-- For $\varepsilon > 0$, $p \ge 1$ and every $t \in \mathbb{R}$, the derivative of
$\varphi_\varepsilon$ satisfies
$$\bigl|p\,t\,(t^2 + \varepsilon^2)^{p/2 - 1}\bigr| \le p\,(|t| + \varepsilon)^{p-1}.$$
-/
theorem abs_deriv_rpowReg_le (hε : 0 < ε) (hp : 1 ≤ p) (t : ℝ) :
    |p * t * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)| ≤ p * (|t| + ε) ^ (p - 1) := by
  have hpos := sq_add_sq_pos hε t
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg (Real.rpow_nonneg hpos.le _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hp0
  have h1 : |t| ≤ (t ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))
  calc |t| * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)
      ≤ (t ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hpos.le _)
    _ = (t ^ 2 + ε ^ 2) ^ ((p - 1) / 2) := by
        rw [← Real.rpow_add hpos]
        ring_nf
    _ ≤ ((|t| + ε) ^ 2) ^ ((p - 1) / 2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
        nlinarith [abs_nonneg t, sq_abs t]
    _ = (|t| + ε) ^ (p - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring

/-- For $p > 0$ and every $t \in \mathbb{R}$, $\varphi_\varepsilon(t) \to |t|^p$ as
$\varepsilon \to 0^+$. -/
theorem tendsto_rpowReg (hp : 0 < p) (t : ℝ) :
    Tendsto (fun ε ↦ rpowReg p ε t) (𝓝[>] 0) (𝓝 (|t| ^ p)) := by
  have h1 : Tendsto (fun ε : ℝ ↦ (t ^ 2 + ε ^ 2) ^ (p / 2)) (𝓝[>] 0) (𝓝 ((t ^ 2) ^ (p / 2))) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x ^ (p / 2)) (t ^ 2) :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))
    have h : Tendsto (fun ε : ℝ ↦ t ^ 2 + ε ^ 2) (𝓝[>] 0) (𝓝 (t ^ 2)) := by
      have hc' : Continuous (fun ε : ℝ ↦ t ^ 2 + ε ^ 2) := by fun_prop
      have := (hc'.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    exact hc.tendsto.comp h
  have h2 : Tendsto (fun ε : ℝ ↦ ε ^ p) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.zero_rpow hp.ne'] using this
  have h3 : (t ^ 2 : ℝ) ^ (p / 2) = |t| ^ p := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
    congr 1
    push_cast
    ring
  have := h1.sub h2
  rw [sub_zero, h3] at this
  exact this

/-- The **mean value bound for a real power**: let $q \ge 1$ and $0 < B < A$. Then
$$A^q - B^q \le q A^{q-1} (A - B).$$

The hypothesis $B > 0$ makes $y \mapsto y^q$ differentiable on $[B, A]$. -/
theorem rpow_sub_rpow_le {A B q : ℝ} (hq : 1 ≤ q) (hB : 0 < B) (hBA : B < A) :
    A ^ q - B ^ q ≤ q * A ^ (q - 1) * (A - B) := by
  have hderiv : ∀ s ∈ Set.Icc B A, HasDerivAt (fun y : ℝ => y ^ q) (q * s ^ (q - 1)) s :=
    fun s _ => hasDerivAt_rpow_const (Or.inr hq)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ q)
    (fun s => q * s ^ (q - 1)) hBA
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => hderiv s (Set.Ioo_subset_Icc_self hs))
  have hsub : (0 : ℝ) < A - B := by linarith
  have hξA : ξ ^ (q - 1) ≤ A ^ (q - 1) :=
    rpow_le_rpow (hB.trans hξ.1).le hξ.2.le (by linarith)
  rw [eq_div_iff (ne_of_gt hsub)] at hξeq
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hkey : 0 ≤ q * (A ^ (q - 1) - ξ ^ (q - 1)) * (A - B) :=
    mul_nonneg (mul_nonneg hq0 (by linarith)) hsub.le
  linarith [hkey, hξeq]

end Real
