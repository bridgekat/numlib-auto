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
