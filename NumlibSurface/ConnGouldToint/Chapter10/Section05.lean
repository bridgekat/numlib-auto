/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter06.Section03
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Conn, Gould and Toint, Section 10.5: Alternative trust-region management

This module formalizes two alternative rules for the management of the trust-region radius from
Section 10.5 of [conn2000trust]. Algorithm 10.5.1 (internal doubling) follows a very successful
iteration whose new trial is also very successful by an inner loop: the radius is enlarged by a
factor $\gamma_3 > 1$ and the step is recomputed with the same model, as long as the ratio stays at
least $\eta_2$ and the step gets longer. A terminating inner loop yields one iteration of the basic
trust-region algorithm of Chapter 6 at the stored radius. The enlargement can be absorbed into the
preceding radius update, because it occurs only after a very successful iteration. The second rule,
(10.5.2)–(10.5.8), updates the radius from the length $\|s_k\|$ of the trial step instead of the
radius $\Delta_k$. Without a safeguard, this rule can force contraction at every iteration and
convergence to a noncritical point; the safeguards (10.5.7) and (10.5.8) compare the step with the
Cauchy step.

The basic algorithm is `ConnGouldToint.Chapter06.BTRRun`, with the radius update
`ConnGouldToint.Chapter06.BTRRadiusUpdate` (6.1.5) and the sufficient decrease condition AA.1,
`ConnGouldToint.Chapter06.HasSufficientModelDecrease`.

## Main definitions

* Algorithm 10.5.1, Step 0, `ConnGouldToint.Chapter10.InternalDoublingParams`: the parameters of the
  basic algorithm and a growth factor $\gamma_3 > 1$.
* Algorithm 10.5.1, Steps 2–3, `ConnGouldToint.Chapter10.InternalDoublingTrace`: a terminating inner
  loop of enlarged probes, with an optional finite budget.
* Algorithm 10.5.1, Step 3c, `ConnGouldToint.Chapter10.InternalDoublingTrace.storedIndex`,
  `ConnGouldToint.Chapter10.InternalDoublingTrace.storedRadius`,
  `ConnGouldToint.Chapter10.InternalDoublingTrace.storedStep` and
  `ConnGouldToint.Chapter10.InternalDoublingTrace.storedRatio`: the probe that the inner loop
  retains, with its radius, step and ratio.
* Algorithm 10.5.1, `ConnGouldToint.Chapter10.InternalDoublingRun`: an infinite outer run with a
  terminating inner loop at each iteration.
* Section 10.5.1, `ConnGouldToint.Chapter10.InternalDoublingRun.toBTRRun`: the outer run as a run of
  the basic trust-region algorithm.
* Equation (10.5.2), `ConnGouldToint.Chapter10.StepLengthRejection`: the new radius after a
  rejection lies between $\bar\gamma_1 \|s\|$ and $\bar\gamma_2 \|s\|$.
* Equation (10.5.6), `ConnGouldToint.Chapter10.StepLengthRadiusUpdate`: the three-case update
  (6.1.5) with the step length in place of the radius.
* Equation (10.5.7), `ConnGouldToint.Chapter10.CauchyStepLengthSafeguard`: the step is at least as
  long as the Cauchy step.
* Equation (10.5.8), `ConnGouldToint.Chapter10.CauchyBoundarySafeguard`: if the Cauchy step reaches
  the boundary, so does the step.

## Main results

* Algorithm 10.5.1, Step 3c,
  `ConnGouldToint.Chapter10.InternalDoublingTrace.storedRadius_ge_initial`: the stored radius is at
  least the initial radius.
* Algorithm 10.5.1, Steps 3a and 3c,
  `ConnGouldToint.Chapter10.InternalDoublingTrace.storedRadius_eq_initial_of_previous_not_very_successful`:
  after an iteration that is not very successful, there is no inner loop.
* Algorithm 10.5.1, Step 3c,
  `ConnGouldToint.Chapter10.InternalDoublingTrace.storedIndex_is_latest_acceptable`: the inner loop
  retains the latest acceptable probe.
* Algorithm 10.5.1, Step 3,
  `ConnGouldToint.Chapter10.InternalDoublingTrace.no_termination_of_always_continue`: probes that
  are always very successful and always longer are not the probes of a terminating inner loop.
* Algorithm 10.5.1, finite budget, `ConnGouldToint.Chapter10.exists_cappedInternalDoublingTrace`:
  with a finite budget, the inner loop terminates whenever the probes can be computed.
* Algorithm 10.5.1, nontermination,
  `ConnGouldToint.Chapter10.internalDoubling_unbounded_inner_counterexample`: without a budget, the
  inner loop can run forever for a smooth objective bounded below and exact models.
* Equations (10.5.2)–(10.5.3),
  `ConnGouldToint.Chapter10.rejected_trial_not_feasible_after_step_contraction`: after the
  step-length contraction, the rejected trial is outside the new trust region.
* Equation (10.5.4), `ConnGouldToint.Chapter10.rejected_trial_reusable`: a rejected trial that fits
  in a smaller radius keeps its sufficient model decrease there.
* Equation (10.5.4), `ConnGouldToint.Chapter10.exists_last_feasible_rejection`: in the geometric
  sequence of radii there is a last radius at which the rejected step fits.
* Equations (10.5.1), (10.5.2) and (10.5.5),
  `ConnGouldToint.Chapter10.step_length_rejection_simulated`: the step-length rejection interval
  lies in a rejection interval of the basic algorithm.
* Equation (10.5.5), `ConnGouldToint.Chapter10.step_length_rejection_compatible`: the factors of
  (10.5.5) exist only if $\gamma_1 \le \gamma_2^2$.
* Equations (10.5.7)–(10.5.8), `ConnGouldToint.Chapter10.CauchyStepLengthSafeguard.boundary`: for a
  feasible step, (10.5.7) implies (10.5.8).
* Equations (10.5.6)–(10.5.8),
  `ConnGouldToint.Chapter10.StepLengthRadiusUpdate.noncontract_of_cauchy_boundary`: with (10.5.8)
  and a Cauchy step on the boundary, a very successful iteration does not contract the radius.
* Example after (10.5.6), `ConnGouldToint.Chapter10.stepLengthRadiusUpdate_counterexample`: the
  step-length update can make the iterates converge to a noncritical point.

## Implementation notes

* The inner loop continues with the threshold $\eta_2$, as printed in Step 3c. The test for a longer
  step compares the norms of $E$.
* The model and the trust-region norm are fixed during the inner loop, and the model is evaluated on
  the enlarged regions.

## Deviations from the source

* **Algorithm 10.5.1** (correction). The printed inner loop can run forever, even for exact models.
  The trace records a terminating inner loop, and an optional finite budget of probes guarantees
  termination and keeps the reduction to the basic algorithm. See
  `ConnGouldToint.Chapter10.internalDoubling_unbounded_inner_counterexample` and
  `ConnGouldToint.Chapter10.exists_cappedInternalDoublingTrace`.
-/

namespace ConnGouldToint.Chapter10

open Chapter06

/-- **Algorithm 10.5.1** of [conn2000trust], Step 0. The parameters of internal doubling are the
parameters $\eta_1, \eta_2, \gamma_1, \gamma_2$ of the basic trust-region algorithm (6.1.3) and
a growth factor $\gamma_3 > 1$. -/
structure InternalDoublingParams extends BTRParams where
  /-- The growth factor $\gamma_3$ of the enlarged radii. -/
  γ₃ : ℝ
  /-- The growth factor is larger than one: $\gamma_3 > 1$. -/
  one_lt_gamma₃ : 1 < γ₃

/-! ### Internal doubling -/

section Doubling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Algorithm 10.5.1** of [conn2000trust], Steps 2–3. A terminating trace of the inner loop at a
center $x$, for an objective $f$, a model $m$, a trust-region seminorm $p$, the ratio
$\rho_{\mathrm{prev}}$ of the preceding iteration, a sufficient-decrease condition on pairs
(radius, step), and an optional budget $N$. It consists of a final index $J$, radii $\Delta_j$
and steps $s_j$ such that:
* $\Delta_0 > 0$, and $J > 0$ if and only if $\rho_{\mathrm{prev}} \ge \eta_2$ and the initial
  trial has ratio $\rho(s_0) \ge \eta_2$;
* for all $j \le J$, the step $s_j$ lies in the trust region $p(s_j) \le \Delta_j$, satisfies
  the sufficient-decrease condition at $\Delta_j$, and decreases the model;
* $\gamma_3 \Delta_j \le \Delta_{j+1}$ for $j < J$;
* each intermediate probe $0 < j < J$ continues the loop: $\rho(s_j) \ge \eta_2$ and
  $\|s_{j-1}\| < \|s_j\|$;
* with a budget $N$, $J \le N + 1$;
* if $J > 0$, the loop stops because the budget is exhausted ($J = N + 1$) or the continuation
  test fails at $J$.

Index $0$ is the initial trial of Step 2. A budget $N$ allows $N + 1$ enlarged probes, and
without a budget the loop is the printed one. The model and the seminorm are the same for every
probe. If the final probe is rejected, the preceding probe is retained. -/
structure InternalDoublingTrace (P : InternalDoublingParams) (f m : E → ℝ)
    (x : E) (p : Seminorm ℝ E) (previousRatio : ℝ) (sufficient : ℝ → E → Prop)
    (budget : Option ℕ := none) where
  /-- The index $J$ of the final probe. -/
  last : ℕ
  /-- The radii $\Delta_j$ of the probes. -/
  radius : ℕ → ℝ
  /-- The steps $s_j$ of the probes. -/
  step : ℕ → E
  /-- The initial radius is positive: $\Delta_0 > 0$. -/
  initial_radius_pos : 0 < radius 0
  /-- The inner loop runs ($J > 0$) if and only if the preceding iteration and the initial trial are
  very successful. -/
  enter : 0 < last ↔ P.η₂ ≤ previousRatio ∧ P.η₂ ≤ btrRatio f m x (step 0)
  /-- Every probe lies in its trust region: $p(s_j) \le \Delta_j$ for $j \le J$. -/
  feasible : ∀ j ≤ last, x + step j ∈ trustRegion p x (radius j)
  /-- Every probe satisfies the sufficient-decrease condition at its radius. -/
  sufficient_decrease : ∀ j ≤ last, sufficient (radius j) (step j)
  /-- Every probe decreases the model: $m(x) - m(x + s_j) > 0$ for $j \le J$. -/
  predicted_pos : ∀ j ≤ last, 0 < m x - m (x + step j)
  /-- The radii grow by at least the factor $\gamma_3$: $\gamma_3 \Delta_j \le \Delta_{j+1}$ for
  $j < J$. -/
  enlarge : ∀ j < last, P.γ₃ * radius j ≤ radius (j + 1)
  /-- Every intermediate probe passes the continuation test: $\rho(s_j) \ge \eta_2$ and
  $\|s_{j-1}\| < \|s_j\|$ for $0 < j < J$. -/
  continue_loop : ∀ j, 0 < j → j < last →
    P.η₂ ≤ btrRatio f m x (step j) ∧ ‖step (j - 1)‖ < ‖step j‖
  /-- With a budget $N$, the final index satisfies $J \le N + 1$. -/
  within_budget : ∀ N, budget = some N → last ≤ N + 1
  /-- If the loop runs, it stops because the budget is exhausted or because the continuation test
  fails at the final probe. -/
  stop : 0 < last → (∃ N, budget = some N ∧ last = N + 1) ∨
    ¬ (P.η₂ ≤ btrRatio f m x (step last) ∧ ‖step (last - 1)‖ < ‖step last‖)

namespace InternalDoublingTrace

variable {P : InternalDoublingParams} {f m : E → ℝ} {x : E} {p : Seminorm ℝ E}
  {previousRatio : ℝ} {sufficient : ℝ → E → Prop} {budget : Option ℕ}

/-- **Algorithm 10.5.1** of [conn2000trust], Step 3c. The index of the stored trial is $J$ if the
final probe is acceptable, $\rho(s_J) \ge \eta_1$, and $J - 1$ otherwise.

The subtraction is in the natural numbers, so the index is $0$ when $J = 0$. Thus without an
inner loop the initial trial is retained even if it fails the acceptance test. -/
noncomputable def storedIndex
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) : ℕ :=
  if P.η₁ ≤ btrRatio f m x (trace.step trace.last) then trace.last else trace.last - 1

/-- **Algorithm 10.5.1** of [conn2000trust], Step 3c. The radius $\Delta_{\mathrm{stored}}$ retained
together with the stored trial. -/
noncomputable def storedRadius
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) : ℝ :=
  trace.radius trace.storedIndex

/-- **Algorithm 10.5.1** of [conn2000trust], Step 3c. The step $s_{\mathrm{stored}}$ retained for
Step 4. -/
noncomputable def storedStep
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) : E :=
  trace.step trace.storedIndex

/-- **Algorithm 10.5.1** of [conn2000trust], Step 3c. The ratio of the achieved to the predicted
reduction at the stored step, $\rho(s_{\mathrm{stored}})$. -/
noncomputable def storedRatio
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) : ℝ :=
  btrRatio f m x trace.storedStep

private theorem storedIndex_le_last
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) :
    trace.storedIndex ≤ trace.last := by
  unfold storedIndex
  split
  · exact le_rfl
  · exact Nat.sub_le _ _

/-- **Algorithm 10.5.1** of [conn2000trust], Step 3c. The inner loop never reduces the radius:
$\Delta_0 \le \Delta_{\mathrm{stored}}$. -/
theorem storedRadius_ge_initial
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) :
    trace.radius 0 ≤ trace.storedRadius := by
  have h (j : ℕ) (hj : j ≤ trace.last) : trace.radius 0 ≤ trace.radius j := by
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      have hj' : j < trace.last := Nat.lt_of_succ_le hj
      have hprev := ih hj'.le
      exact hprev.trans ((le_mul_of_one_le_left
        (trace.initial_radius_pos.le.trans hprev) P.one_lt_gamma₃.le).trans
        (trace.enlarge j hj'))
  exact h _ trace.storedIndex_le_last

/-- **Algorithm 10.5.1** of [conn2000trust], Steps 3a and 3c. If the preceding iteration is not very
successful, $\rho_{\mathrm{prev}} < \eta_2$, then there is no inner loop and
$\Delta_{\mathrm{stored}} = \Delta_0$. -/
theorem storedRadius_eq_initial_of_previous_not_very_successful
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget)
    (h : previousRatio < P.η₂) : trace.storedRadius = trace.radius 0 := by
  have hlast : trace.last = 0 :=
    Nat.eq_zero_of_not_pos fun hpos ↦ h.not_ge (trace.enter.mp hpos).1
  simp [storedRadius, storedIndex, hlast]

/-- **Algorithm 10.5.1** of [conn2000trust], Step 3c. If the inner loop runs ($J > 0$), then the
stored ratio is acceptable, $\rho(s_{\mathrm{stored}}) \ge \eta_1$, and every probe $j \le J$
with $\rho(s_j) \ge \eta_1$ has an index at most the stored index.

So the loop retains the latest acceptable probe. If the final probe fails, all earlier probes
were very successful. -/
theorem storedIndex_is_latest_acceptable
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) (h : 0 < trace.last) :
    P.η₁ ≤ trace.storedRatio ∧
      ∀ j ≤ trace.last, P.η₁ ≤ btrRatio f m x (trace.step j) → j ≤ trace.storedIndex := by
  by_cases hfinal : P.η₁ ≤ btrRatio f m x (trace.step trace.last)
  · have hi : trace.storedIndex = trace.last := ite_eq_left hfinal
    exact ⟨by simpa only [storedRatio, storedStep, hi] using hfinal,
      fun j hj _ ↦ hi ▸ hj⟩
  · have hi : trace.storedIndex = trace.last - 1 := ite_eq_right hfinal
    constructor
    · have hprev : P.η₂ ≤ btrRatio f m x (trace.step (trace.last - 1)) := by
        by_cases hzero : trace.last - 1 = 0
        · rw [hzero]
          exact (trace.enter.mp h).2
        · exact (trace.continue_loop _ (Nat.pos_of_ne_zero hzero) (by omega)).1
      simpa only [storedRatio, storedStep, hi] using P.eta₁_le_eta₂.trans hprev
    · intro j hj hgood
      have hj' : j ≠ trace.last := fun he ↦ hfinal (he ▸ hgood)
      rw [hi]
      omega

/-- **Algorithm 10.5.1** of [conn2000trust], Step 3. Let the preceding iteration be very successful,
$\rho_{\mathrm{prev}} \ge \eta_2$, and let $(t_j)_{j \ge 0}$ be trial steps with
$\rho(t_j) \ge \eta_2$ and $\|t_j\| < \|t_{j+1}\|$ for all $j$. Then no terminating trace
without a budget has the steps $s_j = t_j$ for all $j \le J$. -/
theorem no_termination_of_always_continue
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient)
    (hprevious : P.η₂ ≤ previousRatio) (trials : ℕ → E)
    (hmatch : ∀ j ≤ trace.last, trace.step j = trials j)
    (hratio : ∀ j, P.η₂ ≤ btrRatio f m x (trials j))
    (hlength : ∀ j, ‖trials j‖ < ‖trials (j + 1)‖) : False := by
  have hstart : 0 < trace.last := trace.enter.mpr
    ⟨hprevious, by simpa only [hmatch 0 (Nat.zero_le _)] using hratio 0⟩
  have hstop := trace.stop hstart
  rcases hstop with ⟨N, hnone, _⟩ | hstop
  · simp at hnone
  apply hstop
  rw [hmatch _ le_rfl, hmatch _ (Nat.sub_le _ _)]
  exact ⟨hratio _, by simpa only [Nat.sub_add_cancel hstart] using hlength (trace.last - 1)⟩

end InternalDoublingTrace

/-- **Algorithm 10.5.1** of [conn2000trust]. An infinite outer run of internal doubling consists of
iterates $x_k$, trust-region seminorms $p_k$ that vanish only at $0$, models $m_k$, preceding
ratios $\rho_{\mathrm{prev},k}$, and a terminating inner trace at each iteration, such that
$\rho_{\mathrm{prev},0} = 1$, $\rho_{\mathrm{prev},k+1}$ is the stored ratio of trace $k$, the
next iterate is obtained from the stored step by the acceptance test with $\eta_1$, and the next
initial radius is obtained from the stored radius by the update (6.1.5) with the stored ratio
(Step 5).

For a successful but not very successful iteration, the next initial radius is strictly smaller
than the stored radius. -/
structure InternalDoublingRun (f : E → ℝ) (P : InternalDoublingParams)
    (sufficient : ℕ → (E → ℝ) → E → ℝ → E → Prop)
    (budget : Option ℕ := none) where
  /-- The iterates $x_k$. -/
  x : ℕ → E
  /-- The trust-region seminorms $p_k$. -/
  p : ℕ → Seminorm ℝ E
  /-- Each seminorm $p_k$ vanishes only at $0$. -/
  norm_separates : ∀ k v, p k v = 0 → v = 0
  /-- The models $m_k$. -/
  model : ℕ → E → ℝ
  /-- The ratios $\rho_{\mathrm{prev},k}$ of the preceding iterations, used to decide whether the
  inner loop runs. -/
  previousRatio : ℕ → ℝ
  /-- The terminating inner trace at iteration $k$, at the center $x_k$ with the model $m_k$. -/
  trace : ∀ k, InternalDoublingTrace P f (model k) (x k) (p k) (previousRatio k)
    (sufficient k (model k) (x k)) budget
  /-- The first iteration acts as if it followed a very successful one:
  $\rho_{\mathrm{prev},0} = 1$. -/
  initial_previous_ratio : previousRatio 0 = 1
  /-- The preceding ratio of iteration $k + 1$ is the stored ratio of iteration $k$. -/
  previous_ratio_update : ∀ k, previousRatio (k + 1) = (trace k).storedRatio
  /-- The next iterate is $x_k + s_{\mathrm{stored}}$ if the stored step has ratio at least
  $\eta_1$, and $x_k$ otherwise. -/
  iterate_update : ∀ k, x (k + 1) =
    Optimization.acceptStep P.η₁ f (x k) (trace k).storedStep
      (model k (x k) - model k (x k + (trace k).storedStep))
  /-- The next initial radius is obtained from the stored radius by the update (6.1.5) with the
  stored ratio. -/
  radius_update : ∀ k, BTRRadiusUpdate P.toBTRParams (trace k).storedRatio
    (trace k).storedRadius ((trace (k + 1)).radius 0)
  /-- For a successful but not very successful iteration, the next initial radius is strictly
  smaller than the stored radius. -/
  successful_radius_strict : ∀ k,
    P.η₁ ≤ (trace k).storedRatio → (trace k).storedRatio < P.η₂ →
      (trace (k + 1)).radius 0 < (trace k).storedRadius

/-- **Section 10.5.1** of [conn2000trust], reduction to Algorithm BTR. The outer iterates, the
stored steps and the stored radii of a run of internal doubling form a run of the basic
trust-region algorithm, whose sufficient-decrease condition at iteration $k$ is the condition of
the run at the stored radius.

The enlargement at iteration $k + 1$ is absorbed into the radius update at iteration $k$. This
is possible because the enlargement occurs only when that update follows a very successful
trial. -/
noncomputable def InternalDoublingRun.toBTRRun {f : E → ℝ} {P : InternalDoublingParams}
    {sufficient : ℕ → (E → ℝ) → E → ℝ → E → Prop} {budget : Option ℕ}
    (run : InternalDoublingRun f P sufficient budget) :
    BTRRun f P.toBTRParams (fun k m x s ↦ sufficient k m x (run.trace k).storedRadius s) where
  x := run.x
  p := run.p
  norm_separates := run.norm_separates
  model := run.model
  s := fun k ↦ (run.trace k).storedStep
  Δ := fun k ↦ (run.trace k).storedRadius
  delta_initial_pos :=
    (run.trace 0).initial_radius_pos.trans_le (run.trace 0).storedRadius_ge_initial
  feasible := fun k ↦ (run.trace k).feasible _ (run.trace k).storedIndex_le_last
  sufficient_decrease := fun k ↦
    (run.trace k).sufficient_decrease _ (run.trace k).storedIndex_le_last
  predicted_pos := fun k ↦ (run.trace k).predicted_pos _ (run.trace k).storedIndex_le_last
  iterate_update := run.iterate_update
  radius_update := by
    intro k
    change BTRRadiusUpdate P.toBTRParams (run.trace k).storedRatio
      (run.trace k).storedRadius (run.trace (k + 1)).storedRadius
    have hupdate := run.radius_update k
    by_cases h : P.η₂ ≤ (run.trace k).storedRatio
    · refine ⟨fun _ ↦ (hupdate.very_successful h).trans
        (run.trace (k + 1)).storedRadius_ge_initial, ?_, ?_⟩
      · exact fun _ hlt ↦ (hlt.not_ge h).elim
      · exact fun hlt ↦ (hlt.not_ge (P.eta₁_le_eta₂.trans h)).elim
    · have hprevious : run.previousRatio (k + 1) < P.η₂ := by
        rw [run.previous_ratio_update]
        exact lt_of_not_ge h
      rw [(run.trace (k + 1)).storedRadius_eq_initial_of_previous_not_very_successful hprevious]
      exact hupdate

/-- **Algorithm 10.5.1** of [conn2000trust], with a finite budget. Let $N \in \mathbb{N}$, and let
$\Delta_j$ and $s_j$ be radii and steps with $\Delta_0 > 0$ such that, for all $j \le N + 1$,
the step $s_j$ lies in the trust region of radius $\Delta_j$, satisfies the sufficient-decrease
condition at $\Delta_j$ and decreases the model, and $\gamma_3 \Delta_j \le \Delta_{j+1}$ for
$j < N + 1$. Then there is a terminating trace with budget $N$ whose radii are $\Delta_j$ and
whose steps are $s_j$.

So the inner loop terminates whenever the prescribed probes can be computed. The retained trial
satisfies the same acceptance rule, so a run with this budget also has the representation
`ConnGouldToint.Chapter10.InternalDoublingRun.toBTRRun`. -/
theorem exists_cappedInternalDoublingTrace {P : InternalDoublingParams} {f m : E → ℝ}
    {x : E} {p : Seminorm ℝ E} {previousRatio : ℝ} {sufficient : ℝ → E → Prop}
    (N : ℕ) (radius : ℕ → ℝ) (step : ℕ → E) (hpos : 0 < radius 0)
    (hfeas : ∀ j ≤ N + 1, x + step j ∈ trustRegion p x (radius j))
    (hsuff : ∀ j ≤ N + 1, sufficient (radius j) (step j))
    (hpred : ∀ j ≤ N + 1, 0 < m x - m (x + step j))
    (hgrowth : ∀ j < N + 1, P.γ₃ * radius j ≤ radius (j + 1)) :
    ∃ trace : InternalDoublingTrace P f m x p previousRatio sufficient (some N),
      trace.radius = radius ∧ trace.step = step := by
  classical
  by_cases henter : P.η₂ ≤ previousRatio ∧ P.η₂ ≤ btrRatio f m x (step 0)
  · let good (j : ℕ) := P.η₂ ≤ btrRatio f m x (step j) ∧ ‖step (j - 1)‖ < ‖step j‖
    have hex : ∃ j, 0 < j ∧ (j = N + 1 ∨ ¬ good j) := ⟨N + 1, by omega, Or.inl rfl⟩
    let j := Nat.find hex
    have hj : 0 < j ∧ (j = N + 1 ∨ ¬ good j) := Nat.find_spec hex
    have hjN : j ≤ N + 1 := Nat.find_min' hex ⟨by omega, Or.inl rfl⟩
    refine ⟨{
      last := j
      radius := radius
      step := step
      initial_radius_pos := hpos
      enter := ⟨fun _ ↦ henter, fun _ ↦ hj.1⟩
      feasible i hi := hfeas i (hi.trans hjN)
      sufficient_decrease i hi := hsuff i (hi.trans hjN)
      predicted_pos i hi := hpred i (hi.trans hjN)
      enlarge i hi := hgrowth i (hi.trans_le hjN)
      continue_loop i hi hij := ?_
      within_budget := ?_
      stop := fun _ ↦ hj.2.imp_left (fun h ↦ ⟨N, rfl, h⟩)
    }, rfl, rfl⟩
    · by_contra hn
      exact (Nat.find_min hex hij) ⟨hi, Or.inr hn⟩
    · intro M h
      cases Option.some.inj h
      exact hjN
  · refine ⟨{
      last := 0
      radius := radius
      step := step
      initial_radius_pos := hpos
      enter := by simp [henter]
      feasible i hi := hfeas i (by omega)
      sufficient_decrease i hi := hsuff i (by omega)
      predicted_pos i hi := hpred i (by omega)
      enlarge _ h := (Nat.not_lt_zero _ h).elim
      continue_loop _ _ h := (Nat.not_lt_zero _ h).elim
      within_budget := fun _ _ ↦ Nat.zero_le _
      stop := fun h ↦ (Nat.not_lt_zero _ h).elim
    }, rfl, rfl⟩

end Doubling

/-! ### Radius updates from the step length -/

section StepLength

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Equation (10.5.2)** of [conn2000trust]. After a rejected trial step $s$, the new radius
$\Delta'$ satisfies the **step-length rejection** rule
$$\bar\gamma_1 \|s\| \le \Delta' \le \bar\gamma_2 \|s\|,$$
where $\|s\| = p(s)$ is the length of the step in the current trust-region seminorm $p$. -/
def StepLengthRejection (γ₁bar γ₂bar : ℝ) (p : Seminorm ℝ E) (s : E) (Δ' : ℝ) : Prop :=
  γ₁bar * p s ≤ Δ' ∧ Δ' ≤ γ₂bar * p s

/-- **Equations (10.5.2)–(10.5.3)** of [conn2000trust]. Let $\Delta'$ satisfy the step-length
rejection rule for $s$ in the seminorm $p$, with $\bar\gamma_2 < 1$ and $p(s) > 0$. If the next
seminorm $p'$ satisfies $p(s) \le p'(s)$, then $x + s$ is not in the trust region
$\{y : p'(y - x) \le \Delta'\}$. -/
theorem rejected_trial_not_feasible_after_step_contraction
    {p p' : Seminorm ℝ E} {x s : E} {γ₁bar γ₂bar Δ' : ℝ}
    (hΔ : StepLengthRejection γ₁bar γ₂bar p s Δ') (hγ : γ₂bar < 1)
    (hs : 0 < p s) (hnorm : p s ≤ p' s) :
    x + s ∉ trustRegion p' x Δ' := by
  rw [mem_trustRegion, add_sub_cancel_left]
  exact not_le.mpr (hΔ.2.trans_lt ((mul_lt_of_lt_one_left hs hγ).trans_le hnorm))

/-- **Equation (10.5.4)** of [conn2000trust]. Let $\kappa \ge 0$, $\Delta \ge 0$ and
$0 \le \gamma_2 \le 1$, let the step $s$ satisfy the sufficient decrease condition AA.1 at
radius $\Delta$ for the model $m$ and the vector $g$, and let $s$ be rejected,
$\rho(s) < \eta_1$. If $p(s) \le \gamma_2^j \Delta$, then $x + s$ lies in the trust region of
radius $\gamma_2^j \Delta$, the step satisfies AA.1 at this radius, and the acceptance test with
$\eta_1$ rejects it again.

So a rejected trial can be reused at a smaller radius as long as it satisfies the feasibility
test (10.5.4). -/
theorem rejected_trial_reusable {f m : E → ℝ} {x s g : E} {p : Seminorm ℝ E}
    {β κ Δ γ₂ η₁ : ℝ} {j : ℕ}
    (hκ : 0 ≤ κ) (hΔ : 0 ≤ Δ) (hγ₀ : 0 ≤ γ₂) (hγ₁ : γ₂ ≤ 1)
    (hdec : HasSufficientModelDecrease m x s g β Δ κ)
    (hfit : p s ≤ γ₂ ^ j * Δ) (hreject : btrRatio f m x s < η₁) :
    x + s ∈ trustRegion p x (γ₂ ^ j * Δ) ∧
      HasSufficientModelDecrease m x s g β (γ₂ ^ j * Δ) κ ∧
      Optimization.acceptStep η₁ f x s (m x - m (x + s)) = x := by
  refine ⟨?_, ⟨hdec.1, ?_⟩, Optimization.acceptStep_of_lt hreject⟩
  · rwa [mem_trustRegion, add_sub_cancel_left]
  · have hrad : γ₂ ^ j * Δ ≤ Δ :=
      mul_le_of_le_one_left hΔ (pow_le_one₀ hγ₀ hγ₁)
    exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl hrad)
      (mul_nonneg hκ (norm_nonneg _))).trans hdec.2

/-- **Equation (10.5.4)** of [conn2000trust]. Let $0 \le \gamma < 1$ and $0 < a \le \Delta$. Then
there is $j \in \mathbb{N}$ such that $a \le \gamma^i \Delta$ for all $i \le j$ and
$\gamma^{j+1} \Delta < a$.

With $a$ the length of the rejected step, $\gamma^j \Delta$ is the last feasible radius of the
geometric sequence (10.5.4). -/
theorem exists_last_feasible_rejection {γ Δ a : ℝ}
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) (ha : 0 < a) (hinit : a ≤ Δ) :
    ∃ j : ℕ, a ≤ γ ^ j * Δ ∧ γ ^ (j + 1) * Δ < a ∧
      ∀ i ≤ j, a ≤ γ ^ i * Δ := by
  classical
  have hlim : Filter.Tendsto (fun k : ℕ ↦ γ ^ k * Δ) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ₀ hγ₁).mul_const Δ
  have hfail : ∃ j : ℕ, γ ^ j * Δ < a := (hlim.eventually (gt_mem_nhds ha)).exists
  let n := Nat.find hfail
  have hn : γ ^ n * Δ < a := Nat.find_spec hfail
  have hn₀ : n ≠ 0 := by
    intro hz
    simp only [hz, pow_zero, one_mul] at hn
    exact hn.not_ge hinit
  let j := n - 1
  have hj : j + 1 = n := by omega
  have hprior (i : ℕ) (hi : i ≤ j) : a ≤ γ ^ i * Δ :=
    le_of_not_gt (Nat.find_min hfail (by omega : i < n))
  exact ⟨j, hprior j le_rfl, by simpa only [hj] using hn, hprior⟩

/-- **Equations (10.5.1), (10.5.2) and (10.5.5)** of [conn2000trust]. Let the factors satisfy
$\gamma_1/\gamma_2 \le \bar\gamma_1$ and $\bar\gamma_2 \le \gamma_2$, let $p(s) \le R$ and
$\gamma_2 R < p(s)$, and let $\Delta'$ satisfy the step-length rejection rule for $s$. Then
$$\gamma_1 R \le \Delta' \le \gamma_2 R,$$
so the new radius lies in the rejection interval (10.5.1) of the basic algorithm at the radius
$R$.

Here $R$ is the last feasible geometric radius. The two comparisons of the factors in (10.5.5)
suffice for this containment. -/
theorem step_length_rejection_simulated {P : BTRParams} {p : Seminorm ℝ E}
    {s : E} {R Δ' γ₁bar γ₂bar : ℝ}
    (hlower : P.γ₁ / P.γ₂ ≤ γ₁bar) (hupper : γ₂bar ≤ P.γ₂)
    (hfit : p s ≤ R) (hfail : P.γ₂ * R < p s)
    (hΔ : StepLengthRejection γ₁bar γ₂bar p s Δ') :
    P.γ₁ * R ≤ Δ' ∧ Δ' ≤ P.γ₂ * R := by
  have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have hs : 0 ≤ p s := apply_nonneg _ _
  constructor
  · have hdiv : R ≤ p s / P.γ₂ := (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using hfail.le)
    calc
      _ ≤ P.γ₁ * (p s / P.γ₂) := mul_le_mul_of_nonneg_left hdiv P.gamma₁_pos.le
      _ = (P.γ₁ / P.γ₂) * p s := by ring
      _ ≤ γ₁bar * p s := mul_le_mul_of_nonneg_right hlower hs
      _ ≤ _ := hΔ.1
  · exact hΔ.2.trans ((mul_le_mul_of_nonneg_right hupper hs).trans
      (mul_le_mul_of_nonneg_left hfit hγ.le))

/-- **Equation (10.5.5)** of [conn2000trust]. If $\gamma_1/\gamma_2 \le \bar\gamma_1 < \bar\gamma_2
\le \gamma_2$, then $\gamma_1 \le \gamma_2^2$. So the two step-length factors can lie in the
prescribed interval only if the contraction factors of the basic algorithm satisfy
$\gamma_1 \le \gamma_2^2$. -/
theorem step_length_rejection_compatible {P : BTRParams} {γ₁bar γ₂bar : ℝ}
    (hlower : P.γ₁ / P.γ₂ ≤ γ₁bar) (hbars : γ₁bar < γ₂bar)
    (hupper : γ₂bar ≤ P.γ₂) : P.γ₁ ≤ P.γ₂ ^ 2 := by
  have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have h := (div_le_iff₀ hγ).mp (hlower.trans (hbars.le.trans hupper))
  simpa only [pow_two] using h

/-- **Equation (10.5.6)** of [conn2000trust]. The **step-length radius update** is the three-case
update (6.1.5) applied with the step length $p(s)$ in place of the radius: for the ratio $\rho$,
the new radius $\Delta'$ satisfies $p(s) \le \Delta'$ if $\rho \ge \eta_2$,
$\gamma_2 p(s) \le \Delta' \le p(s)$ if $\eta_1 \le \rho < \eta_2$, and
$\gamma_1 p(s) \le \Delta' \le \gamma_2 p(s)$ if $\rho < \eta_1$. -/
abbrev StepLengthRadiusUpdate (P : BTRParams) (ρ : ℝ)
    (p : Seminorm ℝ E) (s : E) (Δ' : ℝ) : Prop :=
  BTRRadiusUpdate P ρ (p s) Δ'

/-- **Equation (10.5.7)** of [conn2000trust]. The **Cauchy step-length safeguard** requires the step
$s$ to be at least as long as the Cauchy step $s_C$: $p(s_C) \le p(s)$. -/
def CauchyStepLengthSafeguard (p : Seminorm ℝ E) (s sC : E) : Prop :=
  p sC ≤ p s

/-- **Equation (10.5.8)** of [conn2000trust]. The **boundary safeguard** requires that the step $s$
reach the boundary when the Cauchy step $s_C$ does: $p(s_C) = \Delta$ implies $p(s) = \Delta$. -/
def CauchyBoundarySafeguard (p : Seminorm ℝ E) (s sC : E) (Δ : ℝ) : Prop :=
  p sC = Δ → p s = Δ

/-- **Equations (10.5.7)–(10.5.8)** of [conn2000trust]. If the step $s$ is feasible,
$p(s) \le \Delta$, and satisfies the length safeguard (10.5.7), then it satisfies the boundary
safeguard (10.5.8). -/
theorem CauchyStepLengthSafeguard.boundary {p : Seminorm ℝ E} {s sC : E} {Δ : ℝ}
    (h : CauchyStepLengthSafeguard p s sC) (hfit : p s ≤ Δ) :
    CauchyBoundarySafeguard p s sC Δ := by
  intro hC
  exact le_antisymm hfit (hC ▸ h)

/-- **Equations (10.5.6)–(10.5.8)** of [conn2000trust]. Let $\Delta'$ be obtained by the step-length
update (10.5.6) with ratio $\rho \ge \eta_2$, and let $s$ satisfy the boundary safeguard
(10.5.8). If the Cauchy step is on the boundary, $p(s_C) = \Delta$, then $\Delta \le \Delta'$.

So the safeguard restores the property of the basic update that a very successful iteration does
not contract the radius. -/
theorem StepLengthRadiusUpdate.noncontract_of_cauchy_boundary
    {P : BTRParams} {p : Seminorm ℝ E} {s sC : E} {ρ Δ Δ' : ℝ}
    (hu : StepLengthRadiusUpdate P ρ p s Δ')
    (h : CauchyBoundarySafeguard p s sC Δ) (hC : p sC = Δ) (hρ : P.η₂ ≤ ρ) :
    Δ ≤ Δ' :=
  h hC ▸ hu.very_successful hρ

end StepLength

/-! ### Counterexamples -/

/-- **Algorithm 10.5.1** of [conn2000trust], nontermination of the inner loop. Let $f(x) = e^{-x}$
on $\mathbb{R}$ with the absolute value as trust-region norm, the center $0$, the exact model
$m = f$, and the probes $s_j = \Delta_j = 2^j$. Then $f$ is twice continuously differentiable
and bounded below, and for every $j$ the probe $s_j$ lies in the trust region of radius
$\Delta_j$, $\Delta_{j+1} = 2 \Delta_j$, $f(0) - f(s_j) > 0$, the ratio is $\rho(s_j) = 1$, and
$|s_j| < |s_{j+1}|$. Every probe satisfies AA.1 at its radius with some constant $\kappa$ and
any $\beta \ge 1$. Nevertheless, for any parameters and any sufficient-decrease condition, no
terminating trace without a budget, with preceding ratio $1$, has the steps $s_j$ for all
$j \le J$.

So without a limit on the inner loop, the printed stopping rule can continue forever, even for a
smooth objective bounded below and exact models. -/
theorem internalDoubling_unbounded_inner_counterexample :
    let f : ℝ → ℝ := fun x ↦ Real.exp (-x)
    let r : ℕ → ℝ := fun j ↦ 2 ^ j
    let p : Seminorm ℝ ℝ := normSeminorm ℝ ℝ
    ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
      (∀ j, r j ∈ trustRegion p 0 (r j) ∧
        2 * r j = r (j + 1) ∧
        0 < f 0 - f (0 + r j) ∧
        btrRatio f f 0 (r j) = 1 ∧ ‖r j‖ < ‖r (j + 1)‖) ∧
      (∀ (P : InternalDoublingParams) (sufficient : ℝ → ℝ → Prop)
          (trace : InternalDoublingTrace P f f 0 p 1 sufficient),
        (∀ j ≤ trace.last, trace.step j = r j) → False) ∧
      ∃ κ : ℝ, ∀ j β, 1 ≤ β →
        HasSufficientModelDecrease f 0 (r j) (gradient f 0) β (r j) κ := by
  dsimp only
  let f : ℝ → ℝ := fun x ↦ Real.exp (-x)
  let r : ℕ → ℝ := fun j ↦ 2 ^ j
  have hr (j : ℕ) : 1 ≤ r j := one_le_pow₀ (by norm_num)
  have hpos (j : ℕ) : 0 < r j := zero_lt_one.trans_le (hr j)
  have hexp : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hdrop (j : ℕ) : 1 - Real.exp (-1) ≤ f 0 - f (0 + r j) := by
    simp only [f, neg_zero, Real.exp_zero, zero_add]
    exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (hr j))) _
  have hprobes (j : ℕ) : r j ∈ trustRegion (normSeminorm ℝ ℝ) 0 (r j) ∧
      2 * r j = r (j + 1) ∧ 0 < f 0 - f (0 + r j) ∧
      btrRatio f f 0 (r j) = 1 ∧ ‖r j‖ < ‖r (j + 1)‖ := by
    have hpow : 2 * r j = r (j + 1) := by simp [r, pow_succ, mul_comm]
    have hpred : 0 < f 0 - f (0 + r j) := (sub_pos.mpr hexp).trans_le (hdrop j)
    refine ⟨?_, hpow, hpred, ?_, ?_⟩
    · rw [mem_trustRegion, sub_zero, coe_normSeminorm, Real.norm_eq_abs, abs_of_pos (hpos j)]
    · change (f 0 - f (0 + r j)) / (f 0 - f (0 + r j)) = 1
      exact div_self hpred.ne'
    · rw [Real.norm_of_nonneg (hpos j).le, Real.norm_of_nonneg (hpos (j + 1)).le, ← hpow]
      linarith [hpos j]
  refine ⟨Real.contDiff_exp.comp contDiff_id.neg, ⟨0, ?_⟩, hprobes, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (Real.exp_pos (-x)).le
  · intro P sufficient trace hmatch
    exact trace.no_termination_of_always_continue P.eta₂_lt_one.le r hmatch
      (fun j ↦ (hprobes j).2.2.2.1 ▸ P.eta₂_lt_one.le) (fun j ↦ (hprobes j).2.2.2.2)
  · let κ := (1 - Real.exp (-1)) / 2
    have hκ : 0 < κ := half_pos (sub_pos.mpr hexp)
    have hg : gradient f 0 = -1 := by
      rw [gradient_eq_deriv']
      have h := (Real.hasDerivAt_exp (- (0 : ℝ))).comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
      change deriv (Real.exp ∘ Neg.neg) 0 = -1
      simpa only [id_eq, neg_zero, Real.exp_zero, one_mul] using h.deriv
    refine ⟨κ, fun j β hβ ↦ ⟨⟨hκ, ?_⟩, ?_⟩⟩
    · dsimp [κ]
      linarith [Real.exp_pos (-1)]
    · rw [hg, norm_neg, norm_one, mul_one]
      have hmin : min (1 / β) (r j) ≤ 1 :=
        (min_le_left _ _).trans (div_le_one (zero_lt_one.trans_le hβ) |>.mpr hβ)
      calc
        _ ≤ κ * 1 := mul_le_mul_of_nonneg_left hmin hκ.le
        _ ≤ 1 - Real.exp (-1) := by dsimp [κ]; linarith
        _ ≤ _ := hdrop j

/-- **Example after (10.5.6)** of [conn2000trust]. Let $f(x) = x^2$ on $\mathbb{R}$, and let
$\Delta_k = 2^{-k}$, $x_k = 1 + \Delta_k$ and $s_k = -\Delta_k/2$. For any parameters of the
basic algorithm and every $k$, the step $s_k$ lies in the trust region of radius $\Delta_k$
about $x_k$, decreases $f$, satisfies AA.1 with $\beta = 3$ and $\kappa = 1/4$ for the exact
model, has ratio $1$, and $\Delta_{k+1}$ is a step-length update (10.5.6) with ratio $1$;
moreover $x_{k+1} = x_k + s_k$. But $x_k \to 1$ and $f'(1) \neq 0$.

So the step-length update can force geometric contraction at every iteration, despite exact
models and very successful ratios, and the iterates converge to a noncritical point. -/
theorem stepLengthRadiusUpdate_counterexample (P : BTRParams) :
    let f : ℝ → ℝ := fun x ↦ x ^ 2
    let Δ : ℕ → ℝ := fun k ↦ (1 / 2) ^ k
    let x : ℕ → ℝ := fun k ↦ 1 + Δ k
    let s : ℕ → ℝ := fun k ↦ -(Δ k / 2)
    (∀ k, x k + s k ∈ trustRegion (normSeminorm ℝ ℝ) (x k) (Δ k) ∧
      0 < f (x k) - f (x k + s k) ∧
      HasSufficientModelDecrease f (x k) (s k) (gradient f (x k)) 3 (Δ k) (1 / 4) ∧
      btrRatio f f (x k) (s k) = 1 ∧
      StepLengthRadiusUpdate P 1 (normSeminorm ℝ ℝ) (s k) (Δ (k + 1)) ∧
      x (k + 1) = x k + s k) ∧
      Filter.Tendsto x Filter.atTop (nhds 1) ∧ gradient f 1 ≠ 0 := by
  dsimp only
  let f : ℝ → ℝ := fun x ↦ x ^ 2
  let Δ : ℕ → ℝ := fun k ↦ (1 / 2) ^ k
  let x : ℕ → ℝ := fun k ↦ 1 + Δ k
  let s : ℕ → ℝ := fun k ↦ -(Δ k / 2)
  have hgrad (z : ℝ) : gradient f z = 2 * z := by
    rw [gradient_eq_deriv']
    change deriv (fun x : ℝ ↦ x ^ 2) z = _
    rw [deriv_pow_field]
    norm_num
  have hpos (k : ℕ) : 0 < Δ k := pow_pos (by norm_num) _
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hsucc : Δ (k + 1) = Δ k / 2 := by dsimp [Δ]; rw [pow_succ]; ring
    have hlen : ‖s k‖ = Δ k / 2 := by
      change |-(Δ k / 2)| = Δ k / 2
      rw [abs_neg, abs_of_nonneg (by positivity [hpos k])]
    have hx : Δ k ≤ x k := by dsimp [x]; linarith
    have hx₀ : 0 < x k := (hpos k).trans_le hx
    have hsq : (Δ k) ^ 2 ≤ x k * Δ k := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hx (hpos k).le
    have hpred : x k * Δ k / 2 ≤ f (x k) - f (x k + s k) := by
      change x k * Δ k / 2 ≤ (x k) ^ 2 - (x k + -(Δ k / 2)) ^ 2
      nlinarith only [hsq, mul_nonneg hx₀.le (hpos k).le]
    have hpred₀ : 0 < f (x k) - f (x k + s k) :=
      (half_pos (mul_pos hx₀ (hpos k))).trans_le hpred
    refine ⟨?_, hpred₀, ?_, ?_, ?_, ?_⟩
    · rw [mem_trustRegion, add_sub_cancel_left, coe_normSeminorm, hlen]
      linarith [hpos k]
    · refine ⟨by norm_num, ?_⟩
      rw [hgrad, Real.norm_of_nonneg (by positivity [hx₀])]
      calc
        _ ≤ (1 / 4 : ℝ) * (2 * x k) * Δ k :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity [hx₀])
        _ = x k * Δ k / 2 := by ring
        _ ≤ _ := hpred
    · change (f (x k) - f (x k + s k)) / (f (x k) - f (x k + s k)) = 1
      exact div_self hpred₀.ne'
    · refine ⟨?_, ?_, ?_⟩
      · intro _
        change normSeminorm ℝ ℝ (s k) ≤ Δ (k + 1)
        rw [coe_normSeminorm, hlen, hsucc]
      · intro _ hlt
        exact (hlt.not_ge P.eta₂_lt_one.le).elim
      · intro hlt
        exact (hlt.not_ge (P.eta₁_le_eta₂.trans P.eta₂_lt_one.le)).elim
    · change 1 + Δ (k + 1) = 1 + Δ k + -(Δ k / 2)
      rw [hsucc]
      ring
  · have ht : Filter.Tendsto Δ Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [x, add_zero] using ht.const_add 1
  · rw [hgrad]
    norm_num

end ConnGouldToint.Chapter10
