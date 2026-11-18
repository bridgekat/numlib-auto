/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.ReferenceDecrease
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Conn, Gould and Toint, Section 10.1: A nonmonotone trust-region method

This module formalizes the nonmonotone trust-region method of Section 10.1 of [conn2000trust]. The
method compares the trial value $f(x_k + s_k)$ with the value at a reference iteration $r_k \le k$,
and measures the predicted decrease by the model decreases $d_i$ accumulated over the accepted
iterations since $r_k$. The acceptance ratio (10.1.3) is
$$\rho_k = \max\left\{ \frac{f(x_{r_k}) - f(x_k + s_k)}{\sum_{i = r_k}^{k-1} [i \in S]\, d_i + d_k},
  \; \frac{f(x_k) - f(x_k + s_k)}{d_k} \right\},$$
where $S$ is the set of accepted iterations. The accepted decreases are bounded by the total
decrease of $f$ (Lemma 10.1.1), a small radius makes an iteration very successful (Theorem 10.1.2),
and the gradients have limit inferior zero (Theorem 10.1.3) and tend to zero (Theorem 10.1.4). The
module also formalizes the buffer of Algorithm 10.1.2, which updates the reference value with a
fixed amount of memory. The run uses the radius update `ConnGouldToint.Chapter06.BTRRadiusUpdate` of
`NumlibSurface.ConnGouldToint.Chapter06.Section01`, and the model error bounds come from Theorem
6.4.1 (`ConnGouldToint.Chapter06.theorem_6_4_1`).

## Main definitions

* Equation (10.1.1), `ConnGouldToint.Chapter10.logRosenbrock`: the logarithmically rescaled
  Rosenbrock function.
* Equation (10.1.2), `ConnGouldToint.Chapter10.IsReferenceSchedule`: reference indices $r_k \le k$
  whose objective value decreases strictly when the index changes.
* `ConnGouldToint.Chapter10.acceptedDecrease`: the decrease $d_k$ at an accepted iteration, and $0$
  otherwise.
* Equation (10.1.3), `ConnGouldToint.Chapter10.nonmonotoneRatio`: the maximum of the historical and
  the current ratio.
* Algorithm 10.1.2, `ConnGouldToint.Chapter10.ReferenceBuffer`: the values and counters kept between
  iterations.
* Algorithm 10.1.2, `ConnGouldToint.Chapter10.ReferenceBuffer.initial`: the buffer at the initial
  point.
* Algorithm 10.1.2, `ConnGouldToint.Chapter10.ReferenceBuffer.ratio`: the ratio of Step 3a with the
  running sum.
* Algorithm 10.1.2, `ConnGouldToint.Chapter10.ReferenceBuffer.step`: Steps 3a–3d of the algorithm.
* Algorithm 10.1.1, `ConnGouldToint.Chapter10.NonmonotoneRun`: an infinite run of the nonmonotone
  algorithm.
* Algorithm 10.1.1, `ConnGouldToint.Chapter10.NonmonotoneRun.predictedDecrease`: the model decrease
  $d_k$ at the trial step.
* Equation (10.1.3), `ConnGouldToint.Chapter10.NonmonotoneRun.ratio`: the ratio $\rho_k$ of the run.

## Main results

* Algorithm 10.1.2, `ConnGouldToint.Chapter10.ReferenceBuffer.ratio_eq_nonmonotoneRatio`: the ratio
  of the buffer is the ratio (10.1.3).
* Algorithm 10.1.2, `ConnGouldToint.Chapter10.ReferenceBuffer.step_preserves_bounds`: a step keeps
  the invariants of the buffer.
* Lemma 10.1.1, `ConnGouldToint.Chapter10.accepted_predicted_sum_le`: $\eta$ times the sum of the
  accepted predicted decreases is at most $f_0 - f_{k+1}$.
* Lemma 10.1.1, `ConnGouldToint.Chapter10.lemma_10_1_1`: under the decrease condition AA.1, the sum
  of the Cauchy decreases over the accepted iterations is bounded (10.1.4).
* Theorem 10.1.2, `ConnGouldToint.Chapter10.theorem_10_1_2`: a small radius makes the iteration very
  successful, and the radius does not decrease.
* `ConnGouldToint.Chapter10.NonmonotoneRun.delta_pos`: all radii of a run are positive.
* Equation (10.1.13), `ConnGouldToint.Chapter10.high_gradient_radius_sum_le`: a bound on the sum of
  the truncated radii of the accepted iterations with large gradient.
* Equation (10.1.11), `ConnGouldToint.Chapter10.successful_count_le`: a bound on the number of
  accepted iterations under lower bounds on the gradients and the radii.
* Equation (10.1.14), `ConnGouldToint.Chapter10.summable_high_gradient_radius`: the radii of the
  accepted iterations with large gradient are summable.
* Theorem 10.1.3, `ConnGouldToint.Chapter10.theorem_10_1_3_of_error_bound`: under a quadratic model
  error bound, $\liminf_k \|\nabla f(x_k)\| = 0$.
* Theorem 10.1.4, `ConnGouldToint.Chapter10.theorem_10_1_4_of_error_bound`: under a quadratic model
  error bound and a bounded Hessian, $\|\nabla f(x_k)\| \to 0$.
* Theorem 10.1.3, `ConnGouldToint.Chapter10.theorem_10_1_3`: the same conclusion under uniform
  Hessian bounds and first-order model agreement.
* Theorem 10.1.4, `ConnGouldToint.Chapter10.theorem_10_1_4`: the same conclusion under uniform
  Hessian bounds and first-order model agreement.

## Conventions

* The assumptions AF.1, AF.3, AN.1 and AM.1–AM.4 of the source appear as explicit hypotheses: the
  objective is twice continuously differentiable with a bounded Hessian, the model agrees with $f$
  to first order at the center, the model Hessian is bounded on the trust region, and
  $\|v\| \le K p_k(v)$ for the trust-region seminorms $p_k$.
* The gradient $\nabla f(x)$ is `gradient f x` in a real Hilbert space $E$.

## Implementation notes

* The historical sum in (10.1.3) is zero when no step was accepted since the reference iteration.
  The denominator of the historical ratio is still positive, because it includes the current
  predicted decrease $d_k > 0$.

## Deviations from the source

* **Equation (10.1.2)** (correction). The reference index may stay the same from one iteration to
  the next. The reference value must decrease strictly only when the reference index changes. See
  `ConnGouldToint.Chapter10.IsReferenceSchedule`.
* **Algorithm 10.1.2, Step 3d** (reading). The boxed algorithm tests whether the counter equals the
  window, while the prose before it says that the counter exceeds the window. The definition uses
  the equality test. See `ConnGouldToint.Chapter10.ReferenceBuffer.step`.
* **Equation (10.1.11)** (reading). The count of accepted iterations includes iteration $0$. See
  `ConnGouldToint.Chapter10.successful_count_le`.
-/

open Filter Topology
open scoped BigOperators

namespace ConnGouldToint.Chapter10

/-- **Equation (10.1.1)** of [conn2000trust]. The **logarithmically rescaled Rosenbrock function**
on $\mathbb{R}^2$ is
$$f(x) = \log\left(1 + 10^4 (x_2 - x_1^2)^2 + (1 - x_1)^2\right).$$
-/
noncomputable def logRosenbrock (x : ℝ × ℝ) : ℝ :=
  Real.log (1 + 10000 * (x.2 - x.1 ^ 2) ^ 2 + (1 - x.1) ^ 2)

/-- **Equation (10.1.2)** of [conn2000trust]. Let $f_k \in \mathbb{R}$ be the objective values of
the iterates and $r_k \in \mathbb{N}$ reference indices. They form a **reference schedule** if
$r_k \le k$ for all $k$, and $f_{r_{k+1}} < f_{r_k}$ whenever $r_{k+1} \neq r_k$.

**Correction.** The definition allows the same reference index to be kept, and requires a strict
decrease of the reference value only when the reference index changes. -/
def IsReferenceSchedule (f : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  (∀ k, r k ≤ k) ∧ ∀ k, r (k + 1) ≠ r k → f (r (k + 1)) < f (r k)

/-- Given a set $S \subseteq \mathbb{N}$ of accepted iterations and decreases $d_k$, the **accepted
decrease** at iteration $k$ is $d_k$ if $k \in S$ and $0$ otherwise. -/
noncomputable def acceptedDecrease (S : Set ℕ) (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  open Classical in if k ∈ S then d k else 0

/-- **Equation (10.1.3)** of [conn2000trust]. Let $S \subseteq \mathbb{N}$ be the accepted
iterations, $f_k$ the objective values of the iterates, $f^+_k$ the objective values of the
trial points, $d_k$ the predicted decreases, and $r \le k$ a reference index. The **nonmonotone
ratio** is
$$\rho_k = \max\left\{ \frac{f_r - f^+_k}{\sum_{i=r}^{k-1} [i \in S]\, d_i + d_k}, \;
  \frac{f_k - f^+_k}{d_k} \right\},$$
the maximum of the historical ratio and the current ratio.

A quotient with zero denominator is $0$ in Lean. -/
noncomputable def nonmonotoneRatio (S : Set ℕ) (f trial d : ℕ → ℝ) (r k : ℕ) : ℝ :=
  max ((f r - trial k) / ((∑ i ∈ Finset.Ico r k, acceptedDecrease S d i) + d k))
    ((f k - trial k) / d k)

/-- **Algorithm 10.1.2** of [conn2000trust], the buffer. A **reference buffer** consists of the best
value $f_{\min}$, the reference value $f_r$, the candidate value $f_c$, the accumulated
decreases $\sigma_r$ and $\sigma_c$ since the reference and the candidate, and the number $\ell$
of accepted iterations since the last new best value. -/
structure ReferenceBuffer where
  /-- The best objective value $f_{\min}$ found so far. -/
  bestValue : ℝ
  /-- The reference value $f_r$. -/
  referenceValue : ℝ
  /-- The candidate value $f_c$ for the next reference. -/
  candidateValue : ℝ
  /-- The decrease $\sigma_r$ accumulated since the reference iteration. -/
  referenceDecrease : ℝ
  /-- The decrease $\sigma_c$ accumulated since the candidate iteration. -/
  candidateDecrease : ℝ
  /-- The number $\ell$ of accepted iterations since the last new best value. -/
  sinceBest : ℕ

/-- **Algorithm 10.1.2** of [conn2000trust], initialization. The initial buffer for the value
$f(x_0)$ has $f_{\min} = f_r = f_c = f(x_0)$, $\sigma_r = \sigma_c = 0$ and $\ell = 0$. -/
def ReferenceBuffer.initial (value : ℝ) : ReferenceBuffer where
  bestValue := value
  referenceValue := value
  candidateValue := value
  referenceDecrease := 0
  candidateDecrease := 0
  sinceBest := 0

/-- **Algorithm 10.1.2** of [conn2000trust], Step 3a. For a buffer, the current value $f$, the trial
value $f^+$ and the predicted decrease $d$, the **buffered ratio** is
$$\max\left\{ \frac{f_r - f^+}{\sigma_r + d}, \; \frac{f - f^+}{d} \right\}.$$

The historical ratio uses the running sum $\sigma_r$ of the accepted decreases. -/
noncomputable def ReferenceBuffer.ratio (b : ReferenceBuffer) (value trial decrease : ℝ) : ℝ :=
  max ((b.referenceValue - trial) / (b.referenceDecrease + decrease))
    ((value - trial) / decrease)

/-- **Algorithm 10.1.2** of [conn2000trust], Steps 3a–3d. Given a buffer, a threshold $\eta$, a
window $w \in \mathbb{N}$, the objective $f$, the current point $x$, the trial point $x^+$ and
the predicted decrease $d$, one step returns a new point and a new buffer as follows.

* If the buffered ratio is less than $\eta$, the trial is rejected: the point stays $x$ and the
  buffer is unchanged.
* Otherwise $d$ is added to $\sigma_r$ and $\sigma_c$, and the new point is $x^+$. If
  $f(x^+) < f_{\min}$, then $f_{\min}$ and $f_c$ become $f(x^+)$, and $\sigma_c$ and $\ell$
  become $0$.
* Otherwise $\ell$ increases by $1$, and if $f_c < f(x^+)$, then $f_c$ becomes $f(x^+)$ and
  $\sigma_c$ becomes $0$. If then $\ell = w$, the reference is replaced by the candidate: $f_r$
  becomes $f_c$ and $\sigma_r$ becomes $\sigma_c$.

**Reading.** The boxed Step 3d tests whether the counter equals the window, while the prose
before it says that the counter exceeds the window. The definition uses the equality test.

The counter $\ell$ is reset only at a new best value. -/
noncomputable def ReferenceBuffer.step {E : Type*} (b : ReferenceBuffer)
    (η : ℝ) (window : ℕ) (f : E → ℝ) (current trial : E) (decrease : ℝ) :
    E × ReferenceBuffer :=
  let trialValue := f trial
  if b.ratio (f current) trialValue decrease < η then
    (current, b)
  else
    let accumulated := { b with
      referenceDecrease := b.referenceDecrease + decrease
      candidateDecrease := b.candidateDecrease + decrease }
    if trialValue < b.bestValue then
      (trial, { accumulated with
        bestValue := trialValue
        candidateValue := trialValue
        candidateDecrease := 0
        sinceBest := 0 })
    else
      let counted := { accumulated with sinceBest := b.sinceBest + 1 }
      let candidate :=
        if b.candidateValue < trialValue then
          { counted with candidateValue := trialValue, candidateDecrease := 0 }
        else counted
      if candidate.sinceBest = window then
        (trial, { candidate with
          referenceValue := candidate.candidateValue
          referenceDecrease := candidate.candidateDecrease })
      else (trial, candidate)

/-- **Algorithm 10.1.2** of [conn2000trust] and (10.1.3). If the reference value of the buffer is
$f_r$ for a reference index $r$, and $\sigma_r = \sum_{i=r}^{k-1} [i \in S]\, d_i$, then the
buffered ratio at iteration $k$ equals the nonmonotone ratio (10.1.3). -/
theorem ReferenceBuffer.ratio_eq_nonmonotoneRatio (b : ReferenceBuffer) (S : Set ℕ)
    (f trial d : ℕ → ℝ) (r k : ℕ) (hvalue : b.referenceValue = f r)
    (hsum : b.referenceDecrease = ∑ i ∈ Finset.Ico r k, acceptedDecrease S d i) :
    b.ratio (f k) (trial k) (d k) = nonmonotoneRatio S f trial d r k := by
  rw [ReferenceBuffer.ratio, nonmonotoneRatio, hvalue, hsum]

/-- **Algorithm 10.1.2** of [conn2000trust], invariants of a step. Let $\eta > 0$ and $d > 0$.
Suppose that $f(x) \le f_r$, $f(x) \le f_c$, $f_{\min} \le f(x)$, $\sigma_r \ge 0$ and
$\sigma_c \ge 0$. Then after one step with the new point $x'$ and the new buffer,
$f(x') \le f_r$, $f(x') \le f_c$, $\sigma_r \ge 0$ and $\sigma_c \ge 0$, and the new best value
is $\min\{f_{\min}, f(x')\}$. -/
theorem ReferenceBuffer.step_preserves_bounds {E : Type*} (b : ReferenceBuffer)
    {η : ℝ} (window : ℕ) (f : E → ℝ) (current trial : E) {decrease : ℝ}
    (hη : 0 < η) (hd : 0 < decrease) (hr : f current ≤ b.referenceValue)
    (hc : f current ≤ b.candidateValue) (hb : b.bestValue ≤ f current)
    (hsr : 0 ≤ b.referenceDecrease)
    (hsc : 0 ≤ b.candidateDecrease) :
    let next := b.step η window f current trial decrease
    f next.1 ≤ next.2.referenceValue ∧ f next.1 ≤ next.2.candidateValue ∧
      0 ≤ next.2.referenceDecrease ∧ 0 ≤ next.2.candidateDecrease ∧
      next.2.bestValue = min b.bestValue (f next.1) := by
  by_cases hreject : b.ratio (f current) (f trial) decrease < η
  · simp only [ReferenceBuffer.step, hreject, ite_true]
    exact ⟨hr, hc, hsr, hsc, (min_eq_left hb).symm⟩
  have htrial : f trial < b.referenceValue := by
    have hpositive := hη.trans_le (le_of_not_gt hreject)
    rw [ReferenceBuffer.ratio, lt_max_iff] at hpositive
    rcases hpositive with h | h
    · exact sub_pos.mp ((div_pos_iff_of_pos_right (add_pos_of_nonneg_of_pos hsr hd)).mp h)
    · exact (sub_pos.mp ((div_pos_iff_of_pos_right hd).mp h)).trans_le hr
  have hsr' := add_nonneg hsr hd.le
  have hsc' := add_nonneg hsc hd.le
  by_cases hbest : f trial < b.bestValue
  · simp [ReferenceBuffer.step, hreject, hbest, htrial.le, hsr', min_eq_right hbest.le]
  · have hmin := min_eq_left (le_of_not_gt hbest)
    by_cases hcandidate : b.candidateValue < f trial
    · by_cases hreset : b.sinceBest + 1 = window <;>
        simp [ReferenceBuffer.step, hreject, hbest, hcandidate, hreset, htrial.le, hsr', hmin]
    · by_cases hreset : b.sinceBest + 1 = window <;>
        simp [ReferenceBuffer.step, hreject, hbest, hcandidate, hreset,
          le_of_not_gt hcandidate, htrial.le, hsr', hsc', hmin]

/-- **Lemma 10.1.1** of [conn2000trust], sum of the accepted predicted decreases. Let
$S \subseteq \mathbb{N}$, objective values $f_k$, trial values $f^+_k$, predicted decreases
$d_k > 0$ and reference indices $r_k \le k$ be given. Suppose that $\eta \le \rho_k$ for every
$k \in S$, where $\rho_k$ is the nonmonotone ratio (10.1.3) with reference $r_k$, that
$f_{k+1} = f^+_k$ for $k \in S$, and that $f_{k+1} = f_k$ for $k \notin S$. Then for every $k$
$$\eta \sum_{i=0}^{k} [i \in S]\, d_i \le f_0 - f_{k+1}.$$

The same estimate is used for (11.3.1). -/
theorem accepted_predicted_sum_le (S : Set ℕ) (f trial d : ℕ → ℝ) (r : ℕ → ℕ)
    {η : ℝ} (hr : ∀ k, r k ≤ k) (hd : ∀ k, 0 < d k)
    (hs : ∀ k ∈ S, η ≤ nonmonotoneRatio S f trial d (r k) k)
    (haccept : ∀ k ∈ S, f (k + 1) = trial k)
    (hreject : ∀ k ∉ S, f (k + 1) = f k) (k : ℕ) :
    η * (∑ i ∈ Finset.range (k + 1), acceptedDecrease S d i) ≤ f 0 - f (k + 1) := by
  classical
  have hpos (a j : ℕ) :
      0 < (∑ i ∈ Finset.Ico a j, acceptedDecrease S d i) + d j := by
    apply add_pos_of_nonneg_of_pos _ (hd j)
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i ∈ S
    · simpa [acceptedDecrease, hi] using (hd i).le
    · simp [acceptedDecrease, hi]
  have hstep (j : ℕ) : ∃ a ≤ j,
      (∑ i ∈ Finset.Ico a (j + 1), η * acceptedDecrease S d i) ≤ f a - f (j + 1) := by
    by_cases hj : j ∈ S
    · have h := hs j hj
      rw [nonmonotoneRatio, le_max_iff] at h
      rcases h with hh | hc
      · refine ⟨r j, hr j, ?_⟩
        rw [← Finset.mul_sum, Finset.sum_Ico_succ_top (hr j), acceptedDecrease,
          ite_eq_left hj, haccept j hj]
        exact (le_div_iff₀ (hpos (r j) j)).mp hh
      · refine ⟨j, le_rfl, ?_⟩
        simpa [Nat.Ico_succ_singleton, acceptedDecrease, hj, haccept j hj] using
          (le_div_iff₀ (hd j)).mp hc
    · refine ⟨j, le_rfl, ?_⟩
      simp [Nat.Ico_succ_singleton, acceptedDecrease, hj, hreject j hj]
  have h := Optimization.reference_decrease_sum f (fun i ↦ η * acceptedDecrease S d i) hstep (k + 1)
  rwa [← Finset.mul_sum] at h

/-- **Lemma 10.1.1** of [conn2000trust] and (10.1.4). Let $S$, $f_k$, $f^+_k$, $d_k > 0$ and
$r_k \le k$ be as in `ConnGouldToint.Chapter10.accepted_predicted_sum_le`, with $\eta > 0$. Let
$g_k$ be the gradient norms, $\beta_k$ the curvature constants and $\Delta_k$ the radii, and
suppose the decrease condition AA.1:
$$\kappa\, g_k \min\{g_k / \beta_k, \Delta_k\} \le d_k \quad \text{for all } k.$$
Then for every $k$
$$\eta \kappa \sum_{i=0}^{k} [i \in S]\, g_i \min\{g_i / \beta_i, \Delta_i\} \le f_0 -
  f_{k+1}.$$
-/
theorem lemma_10_1_1 (S : Set ℕ) (f trial d g β Δ : ℕ → ℝ) (r : ℕ → ℕ)
    {η κ : ℝ} (hη : 0 < η) (hr : ∀ k, r k ≤ k) (hd : ∀ k, 0 < d k)
    (haa : ∀ k, κ * (g k * min (g k / β k) (Δ k)) ≤ d k)
    (hs : ∀ k ∈ S, η ≤ nonmonotoneRatio S f trial d (r k) k)
    (haccept : ∀ k ∈ S, f (k + 1) = trial k)
    (hreject : ∀ k ∉ S, f (k + 1) = f k) (k : ℕ) :
    η * κ * (∑ i ∈ Finset.range (k + 1),
      acceptedDecrease S (fun j ↦ g j * min (g j / β j) (Δ j)) i) ≤ f 0 - f (k + 1) := by
  classical
  have hcost (i : ℕ) :
      κ * acceptedDecrease S (fun j ↦ g j * min (g j / β j) (Δ j)) i ≤
        acceptedDecrease S d i := by
    by_cases hi : i ∈ S
    · simpa [acceptedDecrease, hi] using haa i
    · simp [acceptedDecrease, hi]
  rw [mul_assoc, Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hcost i)) hη.le).trans
    (accepted_predicted_sum_le S f trial d r hr hd hs haccept hreject k)

open Chapter06 in
/-- **Theorem 10.1.2** of [conn2000trust]. Let $E$ be a normed group, $f, m : E \to \mathbb{R}$,
$x, s, g \in E$ with $g \neq 0$, and let $P$ be the parameters of the basic trust-region
algorithm. Let $0 < \beta \le C$ and $\Delta > 0$. Let the values $f_k = f(x)$,
$f^+_k = f(x + s)$ and $d_k = m(x) - m(x + s)$ enter the nonmonotone ratio $\rho_k$ (10.1.3) at
iteration $k$. Suppose that $f(x) = m(x)$, that $s$ satisfies the sufficient model decrease
condition
$$\kappa \|g\| \min\{\|g\| / \beta, \Delta\} \le m(x) - m(x + s), \qquad 0 < \kappa < 1,$$
that $|f(x + s) - m(x + s)| \le C \Delta^2$, and that
$\Delta \le \kappa \|g\| (1 - \eta_2) / C$. If $\Delta'$ is a radius update (6.1.5) of $\Delta$
for the ratio $\rho_k$, then $\rho_k \ge \eta_2$ and $\Delta \le \Delta'$.

The nonmonotone ratio is at least the current ratio, so the estimate (6.4.12) for small radii,
`ConnGouldToint.Chapter06.btrRatio_ge_eta₂_of_small_radius`, applies. -/
theorem theorem_10_1_2 {E : Type*} [NormedAddCommGroup E] {P : BTRParams}
    {f m : E → ℝ} {x s g : E} {β Δ Δ' κ C : ℝ}
    (S : Set ℕ) (values trial d : ℕ → ℝ) (r k : ℕ)
    (hvalues : values k = f x) (htrial : trial k = f (x + s)) (hd : d k = m x - m (x + s))
    (hβ : 0 < β) (hβC : β ≤ C) (hΔ : 0 < Δ) (hg : g ≠ 0)
    (hval : f x = m x) (hdec : HasSufficientModelDecrease m x s g β Δ κ)
    (herr : |f (x + s) - m (x + s)| ≤ C * Δ ^ 2)
    (hsmall : Δ ≤ κ * ‖g‖ * (1 - P.η₂) / C)
    (hupdate : BTRRadiusUpdate P (nonmonotoneRatio S values trial d r k) Δ Δ') :
    P.η₂ ≤ nonmonotoneRatio S values trial d r k ∧ Δ ≤ Δ' := by
  have hcurrent : P.η₂ ≤ btrRatio f m x s :=
    btrRatio_ge_eta₂_of_small_radius hβ hβC hΔ hg hval hdec herr hsmall
  have hdom : btrRatio f m x s ≤ nonmonotoneRatio S values trial d r k := by
    simp only [nonmonotoneRatio, hvalues, htrial, hd, btrRatio, Optimization.reductionRatio]
    exact le_max_right _ _
  exact ⟨hcurrent.trans hdom, hupdate.very_successful (hcurrent.trans hdom)⟩

open Chapter06

/-- **Algorithm 10.1.1** of [conn2000trust], an infinite run. Let $E$ be a real normed space,
$f : E \to \mathbb{R}$, and $P$ the parameters of the basic trust-region algorithm. A
**nonmonotone run** consists of iterates $x_k$, steps $s_k$, radii $\Delta_k$, trust-region
seminorms $p_k$ that vanish only at $0$, models $m_k$, reference indices $r_k$ that form a
reference schedule (10.1.2) for the values $f(x_k)$, and a set $S$ of accepted iterations, such
that $\Delta_0 > 0$ and for every $k$:

* $p_k(s_k) \le \Delta_k$ and $m_k(x_k) - m_k(x_k + s_k) > 0$;
* $k \in S$ if and only if $\rho_k \ge \eta_1$, where $\rho_k$ is the nonmonotone ratio (10.1.3)
  with reference $r_k$;
* $x_{k+1} = x_k + s_k$ if $k \in S$, and $x_{k+1} = x_k$ otherwise;
* $\Delta_{k+1}$ is a radius update (6.1.5) of $\Delta_k$ for the ratio $\rho_k$.

The set $S$ is part of the run. The acceptance condition determines whether $k \in S$ from the
earlier accepted decreases and the current trial. The ratios are evaluated only for steps with
positive predicted decrease. -/
structure NonmonotoneRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (P : BTRParams) where
  /-- The iterate $x_k$. -/
  x : ℕ → E
  /-- The step $s_k$. -/
  s : ℕ → E
  /-- The radius $\Delta_k$. -/
  Δ : ℕ → ℝ
  /-- The trust-region seminorm $p_k$. -/
  p : ℕ → Seminorm ℝ E
  /-- Each seminorm $p_k$ vanishes only at $0$. -/
  norm_separates : ∀ k v, p k v = 0 → v = 0
  /-- The model $m_k$. -/
  model : ℕ → E → ℝ
  /-- The reference index $r_k$. -/
  reference : ℕ → ℕ
  /-- The reference indices form a reference schedule (10.1.2) for the values $f(x_k)$. -/
  reference_schedule : IsReferenceSchedule (fun k ↦ f (x k)) reference
  /-- The set $S$ of accepted iterations. -/
  successful : Set ℕ
  /-- The initial radius is positive. -/
  delta_initial_pos : 0 < Δ 0
  /-- The trial point lies in the trust region: $p_k(s_k) \le \Delta_k$. -/
  feasible : ∀ k, x k + s k ∈ trustRegion (p k) (x k) (Δ k)
  /-- The predicted decrease is positive: $m_k(x_k) - m_k(x_k + s_k) > 0$. -/
  predicted_pos : ∀ k, 0 < model k (x k) - model k (x k + s k)
  /-- Iteration $k$ is accepted if and only if the nonmonotone ratio (10.1.3) with reference $r_k$
  is at least $\eta_1$. -/
  accepted_iff : ∀ k, k ∈ successful ↔ P.η₁ ≤
    nonmonotoneRatio successful (fun j ↦ f (x j)) (fun j ↦ f (x j + s j))
      (fun j ↦ model j (x j) - model j (x j + s j)) (reference k) k
  /-- An accepted iteration moves to $x_k + s_k$. -/
  accepted_update : ∀ k ∈ successful, x (k + 1) = x k + s k
  /-- A rejected iteration keeps the iterate. -/
  rejected_update : ∀ k ∉ successful, x (k + 1) = x k
  /-- The radius $\Delta_{k+1}$ is a radius update (6.1.5) of $\Delta_k$ for the nonmonotone ratio.
  -/
  radius_update : ∀ k,
    BTRRadiusUpdate P
      (nonmonotoneRatio successful (fun j ↦ f (x j)) (fun j ↦ f (x j + s j))
        (fun j ↦ model j (x j) - model j (x j + s j)) (reference k) k)
      (Δ k) (Δ (k + 1))

namespace NonmonotoneRun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {P : BTRParams}

/-- **Algorithm 10.1.1** of [conn2000trust]. The **predicted decrease** of a run at iteration $k$ is
$d_k = m_k(x_k) - m_k(x_k + s_k)$. -/
noncomputable def predictedDecrease (run : NonmonotoneRun f P) (k : ℕ) : ℝ :=
  run.model k (run.x k) - run.model k (run.x k + run.s k)

/-- **Equation (10.1.3)** of [conn2000trust]. The **ratio** $\rho_k$ of a run is the nonmonotone
ratio with the values $f(x_j)$, the trial values $f(x_j + s_j)$, the predicted decreases and the
reference index $r_k$. Algorithm 10.1.1 uses it to update the iterate and the radius. -/
noncomputable def ratio (run : NonmonotoneRun f P) (k : ℕ) : ℝ :=
  nonmonotoneRatio run.successful (fun j ↦ f (run.x j)) (fun j ↦ f (run.x j + run.s j))
    run.predictedDecrease (run.reference k) k

/-- Every radius of a nonmonotone run is positive: $\Delta_k > 0$ for all $k$. -/
theorem delta_pos (run : NonmonotoneRun f P) (k : ℕ) : 0 < run.Δ k := by
  induction k with
  | zero => exact run.delta_initial_pos
  | succ k ih => exact (run.radius_update k).pos ih

private theorem radius_lower_bound (run : NonmonotoneRun f P) {N : ℕ} {θ : ℝ}
    (hforce : ∀ k ≥ N, run.Δ k ≤ θ → P.η₂ ≤ run.ratio k)
    (k : ℕ) (hk : N ≤ k) :
    min (run.Δ N) (P.γ₁ * θ) ≤ run.Δ k := by
  induction k, hk using Nat.le_induction with
  | base => exact min_le_left _ _
  | succ k hk ih =>
    have hupdate : BTRRadiusUpdate P (run.ratio k) (run.Δ k) (run.Δ (k + 1)) :=
      run.radius_update k
    by_cases h₂ : P.η₂ ≤ run.ratio k
    · exact ih.trans (hupdate.very_successful h₂)
    have hθ := lt_of_not_ge (fun hle ↦ h₂ (hforce k hk hle))
    have hstep : P.γ₁ * run.Δ k ≤ run.Δ (k + 1) := by
      by_cases h₁ : P.η₁ ≤ run.ratio k
      · exact (mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (run.delta_pos k).le).trans
          (hupdate.successful h₁ (lt_of_not_ge h₂)).1
      · exact (hupdate.unsuccessful (lt_of_not_ge h₁)).1
    exact (min_le_right _ _).trans
      ((mul_le_mul_of_nonneg_left hθ.le P.gamma₁_pos.le).trans hstep)

end NonmonotoneRun

namespace NonmonotoneRun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {P : BTRParams}

private noncomputable def decreaseCost (run : NonmonotoneRun f P) (β : ℕ → ℝ) : ℕ → ℝ :=
  acceptedDecrease run.successful (fun k ↦
    ‖gradient f (run.x k)‖ * min (‖gradient f (run.x k)‖ / β k) (run.Δ k))

private theorem decreaseCost_nonneg (run : NonmonotoneRun f P) (β : ℕ → ℝ)
    (hβ : ∀ k, 0 < β k) (k : ℕ) : 0 ≤ run.decreaseCost β k := by
  classical
  by_cases hk : k ∈ run.successful
  · simpa only [decreaseCost, acceptedDecrease, ite_eq_left hk] using
      mul_nonneg (norm_nonneg (gradient f (run.x k)))
        (le_min (div_nonneg (norm_nonneg _) (hβ k).le) (run.delta_pos k).le)
  · simp [decreaseCost, acceptedDecrease, hk]

private theorem cumulative_decreaseCost_le (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ : ℝ}
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ) (k : ℕ) :
    P.η₁ * κ * (∑ i ∈ Finset.range (k + 1), run.decreaseCost β i) ≤
      f (run.x 0) - f (run.x (k + 1)) :=
  lemma_10_1_1 run.successful (fun i ↦ f (run.x i)) (fun i ↦ f (run.x i + run.s i))
    run.predictedDecrease (fun i ↦ ‖gradient f (run.x i)‖) β run.Δ run.reference P.eta₁_pos
    run.reference_schedule.1 run.predicted_pos
    (fun i ↦ by simpa only [predictedDecrease, mul_assoc] using (hdec i).2)
    (fun i hi ↦ (run.accepted_iff i).mp hi)
    (fun i hi ↦ congrArg f (run.accepted_update i hi))
    (fun i hi ↦ congrArg f (run.rejected_update i hi)) k

private theorem summable_decreaseCost (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ : ℝ} (hβ : ∀ k, 0 < β k)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hlower : BddBelow (Set.range f)) : Summable (run.decreaseCost β) := by
  obtain ⟨lo, hlo⟩ := hlower
  have hscale : 0 < P.η₁ * κ := mul_pos P.eta₁_pos (hdec 0).1.1
  refine summable_of_sum_range_le (run.decreaseCost_nonneg β hβ)
    (c := (f (run.x 0) - lo) / (P.η₁ * κ)) ?_
  intro n
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg (sub_nonneg.mpr (hlo ⟨run.x 0, rfl⟩)) hscale.le
  | succ n =>
    have h := run.cumulative_decreaseCost_le β hdec n
    apply (le_div_iff₀ hscale).mpr
    rw [mul_comm]
    exact h.trans (sub_le_sub_left (hlo ⟨run.x (n + 1), rfl⟩) _)

private theorem truncated_radius_le_decreaseCost (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {C ε : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hε : 0 < ε) {k : ℕ} (hmem : k ∈ run.successful)
    (hgrad : ε ≤ ‖gradient f (run.x k)‖) :
    ε * min (ε / C) (run.Δ k) ≤ run.decreaseCost β k := by
  classical
  have hC : 0 < C := (hβ k).trans_le (hβC k)
  have hquot : ε / C ≤ ‖gradient f (run.x k)‖ / β k :=
    div_le_div₀ (norm_nonneg _) hgrad (hβ k) (hβC k)
  simpa only [decreaseCost, acceptedDecrease, ite_eq_left hmem] using
    mul_le_mul hgrad (min_le_min hquot le_rfl)
      (le_min (div_nonneg hε.le hC.le) (run.delta_pos k).le) (norm_nonneg _)

private theorem frequently_gradient_norm_lt (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hsum : Summable (run.decreaseCost β)) :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (run.x k)‖ < ε := by
  classical
  intro ε hε
  by_contra h
  have hevent : ∀ᶠ k in atTop, ε ≤ ‖gradient f (run.x k)‖ := by
    simpa only [Filter.Frequently, not_not, not_lt] using h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hC : 0 < C := (hβ 0).trans_le (hβC 0)
  have hκ : 0 < κ := (hdec 0).1.1
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  let θ := κ * ε * (1 - P.η₂) / C
  have hθ : 0 < θ := div_pos (mul_pos (mul_pos hκ hε) hη) hC
  have hforce (k : ℕ) (hk : N ≤ k) (hsmall : run.Δ k ≤ θ) : P.η₂ ≤ run.ratio k :=
    (theorem_10_1_2 run.successful (fun j ↦ f (run.x j)) (fun j ↦ f (run.x j + run.s j))
      run.predictedDecrease (run.reference k) k rfl rfl rfl (hβ k) (hβC k) (run.delta_pos k)
      (norm_pos_iff.mp (hε.trans_le (hN k hk))) (hval k) (hdec k) (herr k)
      (hsmall.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hN k hk) hκ.le) hη.le) hC.le))
      (run.radius_update k)).1
  let r := min (run.Δ N) (P.γ₁ * θ)
  have hr : 0 < r := lt_min (run.delta_pos N) (mul_pos P.gamma₁_pos hθ)
  let a := ε * min (ε / C) r
  have ha : 0 < a := mul_pos hε (lt_min (div_pos hε hC) hr)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds ha))
  let M := max N J
  have hfail (k : ℕ) (hk : M ≤ k) : run.ratio k < P.η₁ := by
    apply lt_of_not_ge
    intro haccepted
    have hmem := (run.accepted_iff k).mpr haccepted
    have hgrad := hN k ((le_max_left N J).trans hk)
    have hrk : r ≤ run.Δ k := run.radius_lower_bound hforce k ((le_max_left N J).trans hk)
    have hcost : a ≤ run.decreaseCost β k :=
      (mul_le_mul_of_nonneg_left (min_le_min le_rfl hrk) hε.le).trans
        (run.truncated_radius_le_decreaseCost β hβ hβC hε hmem hgrad)
    exact (hJ k ((le_max_right N J).trans hk)).not_ge hcost
  have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have hrad (j : ℕ) : run.Δ (M + j) ≤ P.γ₂ ^ j * run.Δ M := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hupdate : BTRRadiusUpdate P (run.ratio (M + j)) (run.Δ (M + j))
          (run.Δ (M + j + 1)) := run.radius_update (M + j)
      calc
        run.Δ (M + (j + 1)) ≤ P.γ₂ * run.Δ (M + j) :=
          (hupdate.unsuccessful (hfail _ (Nat.le_add_right _ _))).2
        _ ≤ P.γ₂ * (P.γ₂ ^ j * run.Δ M) := mul_le_mul_of_nonneg_left ih hγ.le
        _ = P.γ₂ ^ (j + 1) * run.Δ M := by rw [pow_succ]; ring
  have hlim : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * run.Δ M) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const (run.Δ M)
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hr)).exists
  have hjN : N ≤ M + j := (le_max_left N J).trans (Nat.le_add_right _ _)
  exact hj.not_ge ((run.radius_lower_bound hforce (M + j) hjN).trans (hrad j))

end NonmonotoneRun

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {P : BTRParams}

/-- **Equation (10.1.13)** of [conn2000trust]. Let a nonmonotone run in a real Hilbert space be
given, with curvature constants $0 < \beta_k \le C$, and suppose that every step satisfies the
sufficient model decrease condition $\kappa \|\nabla f(x_k)\| \min\{\|\nabla f(x_k)\| / \beta_k,
\Delta_k\} \le d_k$ with $0 < \kappa < 1$. Let $\varepsilon > 0$, and let $S_\varepsilon$ be the
set of accepted iterations $k$ with $\|\nabla f(x_k)\| \ge \varepsilon$. Then for every $k$
$$\eta_1 \kappa \varepsilon \sum_{i=0}^{k} [i \in S_\varepsilon] \min\{\varepsilon / C,
  \Delta_i\} \le f(x_0) - f(x_{k+1}).$$
-/
theorem high_gradient_radius_sum_le (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C ε : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hε : 0 < ε) (k : ℕ) :
    P.η₁ * κ * ε * (∑ i ∈ Finset.range (k + 1),
      acceptedDecrease {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖}
        (fun j ↦ min (ε / C) (run.Δ j)) i) ≤ f (run.x 0) - f (run.x (k + 1)) := by
  classical
  let S := {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖}
  have hcost (i : ℕ) :
      ε * acceptedDecrease S (fun j ↦ min (ε / C) (run.Δ j)) i ≤ run.decreaseCost β i := by
    by_cases hi : i ∈ S
    · change i ∈ run.successful ∧ ε ≤ ‖gradient f (run.x i)‖ at hi
      exact (by
        simp only [acceptedDecrease, ite_eq_left (show i ∈ S from hi)]
        exact run.truncated_radius_le_decreaseCost β hβ hβC hε hi.1 hi.2)
    · simpa only [acceptedDecrease, ite_eq_right hi, mul_zero] using
        run.decreaseCost_nonneg β hβ i
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (k + 1)) ↦ hcost i)
  rw [← Finset.mul_sum] at hsum
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hsum (mul_nonneg P.eta₁_pos.le (hdec 0).1.1.le)).trans
    (run.cumulative_decreaseCost_le β hdec k)

/-- **Equation (10.1.11)** of [conn2000trust]. Let a nonmonotone run be given with
$0 < \beta_k \le C$ and the sufficient model decrease condition as in
`ConnGouldToint.Chapter10.high_gradient_radius_sum_le`. Let $\varepsilon > 0$ and
$\delta \in \mathbb{R}$ with $\|\nabla f(x_k)\| \ge \varepsilon$ and $\Delta_k \ge \delta$ for
all $k$. If $N_k$ is the number of accepted iterations among $0, \dots, k$, then
$$\eta_1 \kappa \varepsilon N_k \min\{\varepsilon / C, \delta\} \le f(x_0) - f(x_{k+1}).$$

**Reading.** The count includes iteration $0$. -/
theorem successful_count_le (run : NonmonotoneRun f P) [DecidablePred (· ∈ run.successful)]
    (β : ℕ → ℝ) {κ C ε δ : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hε : 0 < ε) (hgrad : ∀ k, ε ≤ ‖gradient f (run.x k)‖)
    (hrad : ∀ k, δ ≤ run.Δ k) (k : ℕ) :
    P.η₁ * κ * ε * (((Finset.range (k + 1)).filter (· ∈ run.successful)).card *
      min (ε / C) δ) ≤ f (run.x 0) - f (run.x (k + 1)) := by
  have hS : {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖} = run.successful := by
    ext j
    simp [hgrad j]
  have hsum := high_gradient_radius_sum_le run β hβ hβC hdec hε k
  rw [hS] at hsum
  have hle :
      ((Finset.range (k + 1)).filter (· ∈ run.successful)).card * min (ε / C) δ ≤
        ∑ i ∈ Finset.range (k + 1),
          acceptedDecrease run.successful (fun j ↦ min (ε / C) (run.Δ j)) i := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    simpa only [Finset.sum_filter, acceptedDecrease] using
      (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.range (k + 1)).filter (· ∈ run.successful)) ↦
        min_le_min le_rfl (hrad i)))
  exact (mul_le_mul_of_nonneg_left hle (by positivity [P.eta₁_pos, (hdec 0).1.1])).trans hsum

/-- **Equation (10.1.14)** of [conn2000trust]. Let a nonmonotone run be given with
$0 < \beta_k \le C$ and the sufficient model decrease condition as in
`ConnGouldToint.Chapter10.high_gradient_radius_sum_le`, and let $f$ be bounded below. Then for
every $\varepsilon > 0$ the radii $\Delta_k$ of the accepted iterations with
$\|\nabla f(x_k)\| \ge \varepsilon$ have a finite sum.

The sum includes the initial iterations, which does not affect summability. -/
theorem summable_high_gradient_radius (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C ε : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hlower : BddBelow (Set.range f)) (hε : 0 < ε) :
    Summable (acceptedDecrease
      {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖} run.Δ) := by
  classical
  let S := {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖}
  have hC : 0 < C := (hβ 0).trans_le (hβC 0)
  have hsum := run.summable_decreaseCost β hβ hdec hlower
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds (mul_pos hε (div_pos hε hC))))
  change Summable (acceptedDecrease S run.Δ)
  apply (summable_nat_add_iff N).mp
  refine Summable.of_nonneg_of_le (f := fun j ↦ run.decreaseCost β (j + N) / ε) ?_ ?_
    (((summable_nat_add_iff N).mpr hsum).div_const ε)
  · intro j
    by_cases hj : j + N ∈ S
    · simpa only [acceptedDecrease, ite_eq_left hj] using (run.delta_pos (j + N)).le
    · simp only [acceptedDecrease, ite_eq_right hj, le_refl]
  · intro j
    by_cases hj : j + N ∈ S
    · have hmem : j + N ∈ run.successful ∧ ε ≤ ‖gradient f (run.x (j + N))‖ := hj
      have hcost := run.truncated_radius_le_decreaseCost β hβ hβC hε hmem.1 hmem.2
      have hrad : run.Δ (j + N) ≤ ε / C := by
        by_contra! hn
        rw [min_eq_left hn.le] at hcost
        exact (hN _ (Nat.le_add_left N j)).not_ge hcost
      rw [min_eq_right hrad] at hcost
      simpa only [acceptedDecrease, ite_eq_left hj] using
        (le_div_iff₀ hε).mpr ((mul_comm _ _).le.trans hcost)
    · simpa only [acceptedDecrease, ite_eq_right hj] using
        div_nonneg (run.decreaseCost_nonneg β hβ (j + N)) hε.le

/-- **Theorem 10.1.3** of [conn2000trust], form with a model error bound. Let a nonmonotone run in a
real Hilbert space be given, with curvature constants $0 < \beta_k \le C$. Suppose that for
every $k$, $f(x_k) = m_k(x_k)$, the step satisfies the sufficient model decrease condition with
the gradient $\nabla f(x_k)$, and
$$|f(x_k + s_k) - m_k(x_k + s_k)| \le C \Delta_k^2.$$
If $f$ is bounded below, then
$$\liminf_{k \to \infty} \|\nabla f(x_k)\| = 0.$$

The quadratic model error bound follows from AF.1, AF.3, AN.1 and AM.1–AM.4 by Theorem 6.4.1;
see `ConnGouldToint.Chapter10.theorem_10_1_3`. The proof excludes a positive lower bound on the
gradient norms on every tail, which is the condition that the limit inferior needs. -/
theorem theorem_10_1_3_of_error_bound (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hlower : BddBelow (Set.range f)) :
    liminf (fun k ↦ ‖gradient f (run.x k)‖) atTop = 0 := by
  let u (k : ℕ) := ‖gradient f (run.x k)‖
  have hfreq := run.frequently_gradient_norm_lt β hβ hβC hval hdec herr
    (run.summable_decreaseCost β hβ hdec hlower)
  have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) u :=
    ⟨0, show ∀ᶠ k in atTop, 0 ≤ u k from Eventually.of_forall fun _ ↦ norm_nonneg _⟩
  have hco : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) u := by
    refine ⟨1, fun b hb' ↦ ?_⟩
    obtain ⟨k, hk, hk'⟩ := ((hfreq 1 zero_lt_one).and_eventually hb').exists
    exact hk'.trans hk.le
  change liminf u atTop = 0
  refine le_antisymm ?_ (le_liminf_of_le hco (Eventually.of_forall fun _ ↦ norm_nonneg _))
  by_contra! hp
  have hlim := liminf_le_of_frequently_le ((hfreq _ (half_pos hp)).mono fun _ h ↦ h.le) hb
  linarith

/-- **Theorem 10.1.4** of [conn2000trust], form with a model error bound. Let a nonmonotone run in a
real Hilbert space be given, with the hypotheses of
`ConnGouldToint.Chapter10.theorem_10_1_3_of_error_bound`. Suppose also that $f$ is twice
continuously differentiable with $\|\nabla^2 f(x)\| \le L$ for all $x$, and that
$\|v\| \le K p_k(v)$ for all $k$ and $v$, with $K \ge 0$. Then
$$\|\nabla f(x_k)\| \to 0.$$

The bounded Hessian gives uniform continuity of the gradient. The proof bounds the motion of the
iterates on stretches with large gradient by a tail of the summable accepted decreases, so it
allows increases of the objective. -/
theorem theorem_10_1_4_of_error_bound (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C L K : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hlower : BddBelow (Set.range f))
    (hf : ContDiff ℝ 2 f) (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ L) (hK : 0 ≤ K)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v) :
    Tendsto (fun k ↦ ‖gradient f (run.x k)‖) atTop (𝓝 0) := by
  classical
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hH 0)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgrad (x y : E) : ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
    unfold gradient
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ ↦ hDf.differentiable (by norm_num) z)
      (fun z _ ↦ hH z) (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ y) (Set.mem_univ x)
  let u (k : ℕ) := ‖gradient f (run.x k)‖
  let cost := run.decreaseCost β
  let cumulative (k : ℕ) := ∑ i ∈ Finset.range k, cost i
  let total := ∑' i, cost i
  have hnonneg := run.decreaseCost_nonneg β hβ
  have hsum := run.summable_decreaseCost β hβ hdec hlower
  have hfreq := run.frequently_gradient_norm_lt β hβ hβC hval hdec herr hsum
  have htail : Tendsto (fun k ↦ total - cumulative k) atTop (𝓝 0) := by
    simpa only [total, cumulative, cost, sub_self] using
      (tendsto_const_nhds (x := total)).sub hsum.hasSum.tendsto_sum_nat
  have hC : 0 < C := (hβ 0).trans_le (hβC 0)
  have hLK : 0 ≤ L * K := mul_nonneg hL hK
  rw [Metric.tendsto_atTop]
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  have hLK₁ : 0 < L * K + 1 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds (mul_pos he (div_pos he hC))))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (htail.eventually (gt_mem_nhds (div_pos (mul_pos he he) hLK₁)))
  have hstep (i : ℕ) (hi : N ≤ i) (hu : e ≤ u i) :
      e * (u i - u (i + 1)) ≤ (L * K) * cost i := by
    by_cases hs : i ∈ run.successful
    · have hcost : e * min (e / C) (run.Δ i) ≤ cost i :=
        run.truncated_radius_le_decreaseCost β hβ hβC he hs hu
      have hrad : run.Δ i ≤ e / C := by
        by_contra! hn
        rw [min_eq_left hn.le] at hcost
        exact (hN i hi).not_ge hcost
      rw [min_eq_right hrad] at hcost
      have hdist : ‖run.x i - run.x (i + 1)‖ ≤ K * run.Δ i := by
        rw [run.accepted_update i hs, sub_add_cancel_left, norm_neg]
        exact (hnorm i _).trans (mul_le_mul_of_nonneg_left
          (by simpa [trustRegion] using run.feasible i) hK)
      have hgradstep : u i - u (i + 1) ≤ (L * K) * run.Δ i := by
        calc
          _ ≤ ‖gradient f (run.x i) - gradient f (run.x (i + 1))‖ := norm_sub_norm_le _ _
          _ ≤ L * ‖run.x i - run.x (i + 1)‖ := hgrad _ _
          _ ≤ L * (K * run.Δ i) := mul_le_mul_of_nonneg_left hdist hL
          _ = _ := by ring
      calc
        _ ≤ e * ((L * K) * run.Δ i) := mul_le_mul_of_nonneg_left hgradstep he.le
        _ = (L * K) * (e * run.Δ i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcost hLK
    · simp only [u, run.rejected_update i hs, sub_self, mul_zero, cost,
        NonmonotoneRun.decreaseCost, acceptedDecrease, ite_eq_right hs, le_refl]
  refine ⟨max N J, fun k hk ↦ ?_⟩
  have hkN := (le_max_left N J).trans hk
  have hkJ := (le_max_right N J).trans hk
  change dist (u k) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  by_contra! hhigh
  have hex : ∃ j, k ≤ j ∧ u j < e := frequently_atTop.mp (hfreq e he) k
  let j := Nat.find hex
  have hj : k ≤ j ∧ u j < e := Nat.find_spec hex
  have htel (i : ℕ) (hi : k ≤ i) : i ≤ j →
      e * (u k - u i) ≤ (L * K) * (cumulative i - cumulative k) := by
    induction i, hi using Nat.le_induction with
    | base => simp
    | succ i hi ih =>
      intro hij
      have hbelow : i < j := Nat.lt_of_succ_le hij
      have hui : e ≤ u i := le_of_not_gt fun hlt ↦ (Nat.find_min hex hbelow) ⟨hi, hlt⟩
      have hrec : cumulative (i + 1) = cumulative i + cost i := Finset.sum_range_succ _ _
      rw [hrec]
      linarith only [ih hbelow.le, hstep i (hkN.trans hi) hui]
  have hgap : e < u k - u j := by dsimp [e] at hj ⊢; linarith [hj.2]
  have hle : cumulative j ≤ total := Summable.sum_le_tsum _ (fun i _ ↦ hnonneg i) hsum
  have htail_nonneg : 0 ≤ total - cumulative k :=
    sub_nonneg.mpr (Summable.sum_le_tsum _ (fun i _ ↦ hnonneg i) hsum)
  have hbound : (L * K) * (cumulative j - cumulative k) < e * e := calc
    _ ≤ (L * K) * (total - cumulative k) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hle _) hLK
    _ ≤ (L * K + 1) * (total - cumulative k) := by gcongr; linarith
    _ < _ := by
      have hsmall := (lt_div_iff₀ hLK₁).mp (hJ k hkJ)
      simpa only [mul_comm] using hsmall
  exact hbound.not_ge ((mul_le_mul_of_nonneg_left hgap.le he.le).trans (htel j hj.1 le_rfl))

omit [CompleteSpace E] in
private theorem trial_error_of_uniform_hessian (run : NonmonotoneRun f P)
    {K κf κm : ℝ} (hK : 1 ≤ K) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ContDiff ℝ 2 f) (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k), DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hM : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      ‖fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ κm - 1)
    (hval : ∀ k, run.model k (run.x k) = f (run.x k))
    (hgrad : ∀ k, fderiv ℝ (run.model k) (run.x k) = fderiv ℝ f (run.x k)) (k : ℕ) :
    |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      uniformHessianConstant K κf κm * (run.Δ k) ^ 2 := by
  have hs : run.p k (run.s k) ≤ run.Δ k := by
    simpa [trustRegion] using run.feasible k
  exact (theorem_6_4_1 (run.p k) (run.norm_separates k) (run.delta_pos k).le hκm hs hf hF
    (hm k) (hDm k) (hM k) (hval k) (hgrad k)).2 K (zero_le_one.trans hK) (hnorm k)

private theorem le_uniformHessianConstant {K κf κm : ℝ} (hK : 1 ≤ K) (hκm : 1 ≤ κm) :
    κm ≤ uniformHessianConstant K κf κm := by
  have hK₂ : 1 ≤ K ^ 2 := by nlinarith
  calc
    κm ≤ max κf κm := le_max_right _ _
    _ ≤ K ^ 2 * max κf κm :=
      le_mul_of_one_le_left ((zero_le_one.trans hκm).trans (le_max_right _ _)) hK₂

/-- **Theorem 10.1.3** of [conn2000trust]. Let a nonmonotone run in a real Hilbert space be given,
with $K \ge 1$ and $\kappa_m \ge 1$, and with $\|v\| \le K p_k(v)$ for all $k$ and $v$. Let $f$
be twice continuously differentiable with $\|\nabla^2 f(z)\| \le \kappa_f$ for all $z$, and
bounded below. Suppose that for every $k$, the model $m_k$ and its derivative are differentiable
on the trust region $\{z : p_k(z - x_k) \le \Delta_k\}$ with
$\|\nabla^2 m_k(z)\| \le \kappa_m - 1$ there, that $m_k(x_k) = f(x_k)$ and
$\nabla m_k(x_k) = \nabla f(x_k)$, and that the step satisfies the sufficient model decrease
condition with curvature constant $0 < \beta_k \le \kappa_m$. Then
$$\liminf_{k \to \infty} \|\nabla f(x_k)\| = 0.$$

The bound $\beta_k \le \kappa_m$ on the curvature constants is the one of (6.3.2) and AM.4. The
model error bound comes from Theorem 6.4.1, and the proof applies
`ConnGouldToint.Chapter10.theorem_10_1_3_of_error_bound`. -/
theorem theorem_10_1_3 (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ K κf κm : ℝ} (hK : 1 ≤ K) (hκm : 1 ≤ κm)
    (hβ : ∀ k, 0 < β k) (hβm : ∀ k, β k ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ContDiff ℝ 2 f) (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k), DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hM : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      ‖fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ κm - 1)
    (hval : ∀ k, run.model k (run.x k) = f (run.x k))
    (hgrad : ∀ k, fderiv ℝ (run.model k) (run.x k) = fderiv ℝ f (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hlower : BddBelow (Set.range f)) :
    liminf (fun k ↦ ‖gradient f (run.x k)‖) atTop = 0 :=
  theorem_10_1_3_of_error_bound run β hβ
    (fun k ↦ (hβm k).trans (le_uniformHessianConstant hK hκm)) (fun k ↦ (hval k).symm) hdec
    (trial_error_of_uniform_hessian run hK hκm hnorm hf hF hm hDm hM hval hgrad) hlower

/-- **Theorem 10.1.4** of [conn2000trust]. Under the hypotheses of
`ConnGouldToint.Chapter10.theorem_10_1_3`,
$$\|\nabla f(x_k)\| \to 0.$$

The bounded objective Hessian gives the uniform gradient estimate along the iterates. The proof
applies `ConnGouldToint.Chapter10.theorem_10_1_4_of_error_bound`. -/
theorem theorem_10_1_4 (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ K κf κm : ℝ} (hK : 1 ≤ K) (hκm : 1 ≤ κm)
    (hβ : ∀ k, 0 < β k) (hβm : ∀ k, β k ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ContDiff ℝ 2 f) (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k), DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hM : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      ‖fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ κm - 1)
    (hval : ∀ k, run.model k (run.x k) = f (run.x k))
    (hgrad : ∀ k, fderiv ℝ (run.model k) (run.x k) = fderiv ℝ f (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hlower : BddBelow (Set.range f)) :
    Tendsto (fun k ↦ ‖gradient f (run.x k)‖) atTop (𝓝 0) :=
  theorem_10_1_4_of_error_bound run β hβ
    (fun k ↦ (hβm k).trans (le_uniformHessianConstant hK hκm)) (fun k ↦ (hval k).symm) hdec
    (trial_error_of_uniform_hessian run hK hκm hnorm hf hF hm hDm hM hval hgrad)
    hlower hf hF (zero_le_one.trans hK) hnorm

end Convergence

end ConnGouldToint.Chapter10
