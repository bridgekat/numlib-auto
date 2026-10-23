import Numlib.Optimization.Regularization.Cubic.SpectralCounterexample
import Numlib.Optimization.Regularization.Cubic.PhaseCountCounterexample
import Numlib.Optimization.Regularization.Cubic.LocalCountCounterexample
import Numlib.Optimization.SecondOrder.HessianRegion

/-!
# Local positive curvature and phase complexity

The positive-curvature neighborhood uses actual Hessian eigenpairs and the
explicit radius from Lemma 5.4.1. Its local-minimum assumption is retained,
although positive least curvature and the Lipschitz bound suffice for this
perturbation statement. Further local convergence and count results remain
specified in the plans.
-/

namespace CartisGouldToint

/-- **Lemma 5.4.1 (region of local strong convexity).** The printed positive
radius defines a neighborhood of the local minimizer, and every actual least
Hessian eigenvalue throughout its closed ball is at least half the value at
the minimizer. Genuine unit Hessian eigenpairs specify the least eigenvalues.
The proof even permits dropping the local-minimum assumption. -/
theorem lemma_5_4_1 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xstar ustar : EuclideanSpace ℝ (Fin n)} {ℓstar L : ℝ}
    (_hf : ContDiff ℝ 2 f) (_hmin : IsLocalMin f xstar)
    (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓstar ustar)
    (hℓ : 0 < ℓstar) (hL : 0 < L)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖) :
    let qstar := ℓstar / (4 * L)
    0 < qstar ∧ Metric.closedBall xstar qstar ∈ nhds xstar ∧
      (∀ (x v : EuclideanSpace ℝ (Fin n)), ‖x - xstar‖ ≤ qstar → ‖v‖ = 1 →
        ℓstar / 2 ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)) ∧
      ∀ (x u : EuclideanSpace ℝ (Fin n)) (μ : ℝ), ‖x - xstar‖ ≤ qstar →
        SecondOrderTrustRegion.IsLeastEigenpair f x μ u → ℓstar / 2 ≤ μ := by
  dsimp only
  have hq : 0 < ℓstar / (4 * L) := by positivity
  exact ⟨hq, Metric.closedBall_mem_nhds xstar hq,
    fun _ _ hx hv => hstar.curvature_ge_half_on_ball hℓ hL hlip hx _ hv,
    fun _ _ _ hx he => hstar.ge_half_on_ball hℓ hL hlip hx he⟩

end CartisGouldToint

namespace CartisGouldToint

/-- **Counterexample to Lemma 5.4.3.** All five printed local-threshold terms
are finite, and their exact minimum is `1/16`. The initial gradient equals
`ζ=513/32768≤ζ*/2`, and the point is in the prescribed radius-`1/4` ball.
The actual tightened AR2 run needs its first successful trial when `ε=ζ/2`,
while the displayed double logarithm is zero. A ceiling alone does not repair
this count: its argument needs an additional positive correction. -/
theorem lemma_5_4_3_counterexample :
    let f := HighOrderRegularization.ObstructionCounterexample.objective
    let x := CubicRegularization.LocalCountCounterexample.point
    let ζstar := CubicRegularization.LocalCountCounterexample.printedZeta
      1 1 (1 / 2) (1 / 4) 12 (3 / 4)
    ContDiff ℝ 2 f ∧ IsLocalMin f 0 ∧ (∀ z, 0 ≤ f z) ∧
      (∀ u v, ‖iteratedFDeriv ℝ 2 f u - iteratedFDeriv ℝ 2 f v‖ ≤ 1 * ‖u - v‖) ∧
      SecondOrderTrustRegion.IsLeastEigenpair f 0 1 1 ∧
      max (1 / 4 : ℝ) (3 * 1 / (1 - 3 / 4)) = 12 ∧ ζstar = 1 / 16 ∧
      (‖x 0‖ ≤ (1 : ℝ) / 4 ∧ ‖fderiv ℝ f (x 0)‖ = (513 / 32768 : ℝ) ∧
        (513 / 32768 : ℝ) ≤ ζstar / 2) ∧
      CubicRegularization.FirstOrderRun f x (fun _ => -(1 : ℝ) / 64)
        (fun _ => 1 / 4) (fun _ => 1) (1 / 4) (3 / 4) (1 / 2) 2 3 (1 / 4)
          (1 / 2) ((513 / 32768 : ℝ) / 2) ⊤ 1 ∧
      ‖fderiv ℝ (CubicRegularization.model f (x 0) (1 / 4)) (-(1 : ℝ) / 64)‖ ≤
        (1 / 2 : ℝ) * min ‖fderiv ℝ f (x 0)‖
          ((1 / 2 : ℝ) * ‖(-(1 : ℝ) / 64)‖ ^ 2) ∧
      ‖fderiv ℝ f (x 1)‖ ≤ ((513 / 32768 : ℝ) / 2) ∧
      Real.logb 2 (Real.logb 2 ((513 / 32768 : ℝ) / ((513 / 32768 : ℝ) / 2))) = 0 ∧
      ¬∃ k : ℕ, (k : ℝ) ≤
        Real.logb 2 (Real.logb 2 ((513 / 32768 : ℝ) / ((513 / 32768 : ℝ) / 2))) ∧
          ‖fderiv ℝ f (x k)‖ ≤ ((513 / 32768 : ℝ) / 2) := by
  dsimp only
  open CubicRegularization.LocalCountCounterexample in
    exact ⟨regularity.1, regularity.2.1, regularity.2.2.1, regularity.2.2.2,
      least_eigenpair 0, printed_constants.1, printed_constants.2, initial_region,
      run, stricter_test, terminal_certificate, count_fails.1, count_fails.2⟩

end CartisGouldToint


open CubicRegularization.PhaseCountCounterexample in
/-- **Counterexample to Theorem 5.4.4's literal total count.** The actual
quadratic has a genuine accepted model-stationary AR2 trial, and all produced
points lie in the positive-curvature neighborhood. At epsilon=zeta/sqrt(2),
the printed double logarithm is minus one. It cancels the additive one, leaving
a total bound below one although one successful trial is necessary. All five
local-threshold terms are finite, and the global coefficient is exactly the
source coefficient from Lemma 3.3.4. -/
theorem CartisGouldToint.theorem_5_4_4_counterexample :
    let f := HighOrderRegularization.ObstructionCounterexample.objective
    let x := CubicRegularization.QuadraticTrial.point u
    let ζstar := CubicRegularization.LocalCountCounterexample.printedZeta
      1 1 (1 / 2) (1 / 4) 12 (3 / 4)
    ContDiff ℝ 2 f ∧ IsLocalMin f 0 ∧ (∀ z, 0 ≤ f z) ∧
      (∀ a b, ‖iteratedFDeriv ℝ 2 f a - iteratedFDeriv ℝ 2 f b‖ ≤ ‖a - b‖) ∧
      SecondOrderTrustRegion.IsLeastEigenpair f 0 1 1 ∧
      max (1 / 4 : ℝ) (3 * 1 / (1 - 3 / 4)) = 12 ∧ ζstar = 1 / 16 ∧
      0 < zeta ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
      (‖x 0‖ ≤ (1 : ℝ) / 4 ∧ ‖fderiv ℝ f (x 0)‖ = zeta ∧ zeta ≤ ζstar / 2) ∧
      CubicRegularization.FirstOrderRun f x (fun _ => -u)
        (fun _ => 1/4) (fun _ => 1) (1/4) (3/4) (1/2) 2 3 (1/4) (1/2) epsilon ⊤ 1 ∧
      ‖fderiv ℝ (CubicRegularization.model f (x 0) (1/4)) (-u)‖ ≤
        (1/2 : ℝ) * min ‖fderiv ℝ f (x 0)‖ ((1/2 : ℝ) * ‖-u‖ ^ 2) ∧
      (∀ k, ¬((1 : ℝ)/4 < ‖x k‖ ∧ epsilon < ‖fderiv ℝ f (x k)‖ ∧
        ‖fderiv ℝ f (x k)‖ ≤ zeta)) ∧
      epsilon < ‖fderiv ℝ f (x 0)‖ ∧ ‖fderiv ℝ f (x 1)‖ < epsilon ∧
      kappa = 6 * ((1 : ℝ) + 1/2 + 12) ^ (3/2 : ℝ) /
        ((2 : ℝ) ^ (3/2 : ℝ) * (1/4) * (1/4)) ∧
      Real.logb 2 (Real.logb 2 (zeta / epsilon)) = -1 ∧
      ¬∃ k : ℕ, (k : ℝ) ≤ kappa * (f zeta - 0) / zeta ^ (3/2 : ℝ) +
        Real.logb 2 (Real.logb 2 (zeta / epsilon)) + 1 ∧
        ‖fderiv ℝ f (x k)‖ < epsilon := by
  dsimp only
  have hr := CubicRegularization.LocalCountCounterexample.regularity
  have hp := CubicRegularization.LocalCountCounterexample.printed_constants
  exact ⟨hr.1, hr.2.1, hr.2.2.1, by simpa only [one_mul] using hr.2.2.2,
    CubicRegularization.LocalCountCounterexample.least_eigenpair 0, hp.1, hp.2,
    zeta_bounds.1, epsilon_bounds.1, epsilon_bounds.2.2, initial_region, actual_run,
    stricter_test, never_excluded, initial_fails, terminal_passes, rfl,
    printed_double_log, count_fails⟩

namespace CartisGouldToint

/-- **Counterexample to Lemma 5.4.2.** A positive scalar quadratic has a true
accepted AR2 trial satisfying the tightened actual model-gradient test. The
Hessian Lipschitz constant is positive, `sigmaMin < theta`, and all five
printed threshold terms are finite and positive. Their exact minimum is
`45/100501`. The initial point belongs even to the printed small-gradient
local region, but its accepted endpoint violates (5.4.4). Thus the claimed
coefficient fails independently of any zero-denominator convention. -/
theorem lemma_5_4_2_counterexample :
    let f := CubicRegularization.SpectralCounterexample.objective
    let x := CubicRegularization.SpectralCounterexample.point
    let u := CubicRegularization.SpectralCounterexample.u
    let ζstar := CubicRegularization.LocalCountCounterexample.printedZeta
      (1 / 10) (1 / 1000) (1 / 2) (1 / 4) 100 (3 / 4)
    ContDiff ℝ 2 f ∧ IsLocalMin f 0 ∧ (∀ z, 0 ≤ f z) ∧
      (∀ a b, ‖iteratedFDeriv ℝ 2 f a - iteratedFDeriv ℝ 2 f b‖ ≤
        (1 / 1000 : ℝ) * ‖a - b‖) ∧
      SecondOrderTrustRegion.IsLeastEigenpair f 0 (1 / 10) 1 ∧
      (0 : ℝ) < 1 / 1000 ∧ (0 : ℝ) < 1 / 2 - 1 / 4 ∧
      max (100 : ℝ) (3 * (1 / 1000) / (1 - 3 / 4)) = 100 ∧
      ζstar = 45 / 100501 ∧
      CubicRegularization.FirstOrderRun f x (fun _ => -u) (fun _ => 100)
        (fun _ => 1) (1 / 4) (3 / 4) (1 / 2) 2 3 (1 / 4) (1 / 2)
          (1 / 100000000000) ⊤ 1 ∧
      ‖fderiv ℝ (CubicRegularization.model f (x 0) 100) (-u)‖ ≤
        (1 / 2 : ℝ) * min ‖fderiv ℝ f (x 0)‖ ((1 / 2 : ℝ) * ‖-u‖ ^ 2) ∧
      (‖x 0‖ ≤ (1 / 10 : ℝ) / (4 * (1 / 1000)) ∧
        ‖x 1‖ ≤ (1 / 10 : ℝ) / (4 * (1 / 1000)) ∧
        ‖fderiv ℝ f (x 0)‖ ≤ ζstar) ∧
      ‖fderiv ℝ f (x 0)‖ ^ 2 / ζstar < ‖fderiv ℝ f (x 1)‖ := by
  dsimp only
  open CubicRegularization.SpectralCounterexample in
    exact ⟨regularity.1, regularity.2.1, regularity.2.2.1, regularity.2.2.2,
      least_eigenpair 0, by norm_num, by norm_num, parameter_cap,
      printed_constants.2.2.2.2.2, actual_run, stricter_test, local_region,
      printed_bound_fails⟩

end CartisGouldToint
