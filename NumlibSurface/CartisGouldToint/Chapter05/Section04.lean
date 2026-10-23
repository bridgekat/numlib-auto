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
