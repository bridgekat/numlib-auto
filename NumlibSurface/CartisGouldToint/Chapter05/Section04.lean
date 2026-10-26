import Numlib.Optimization.Regularization.Cubic.LocalGlobalCounts
import Numlib.Optimization.Regularization.Cubic.LocalComplexity
import Numlib.Optimization.Regularization.Cubic.LocalConvergence
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

namespace CartisGouldToint

/-- **Corrected Lemma 5.4.2.** The true local step multiplier is
`2*(1+theta)/lambda`; the cubic penalty has no constant Hessian shift.
The explicit positive five-term replacement threshold gives the displayed
quadratic derivative bound on every accepted local trial, and entry into its
small-gradient region makes every subsequent available trial very successful
and keeps all subsequent iterates in that region. The tightened trace contains
only actual model tests, objective ratios and parameter/point updates. -/
theorem lemma_5_4_2_corrected {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ ℓ L : ℝ} {N : ℕ}
    {xstar ustar : EuclideanSpace ℝ (Fin n)}
    (h : CubicRegularization.TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f xstar)
    (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖) :
    let ζ := CubicRegularization.localThreshold ℓ L θ
      (max (σ 0) (γ₃ * L / (1 - η₂))) η₂
    0 < ζ ∧
      (∀ i < N, ‖x i - xstar‖ ≤ ℓ / (4 * L) → η₁ ≤ ρ i →
        ‖fderiv ℝ f (x (i + 1))‖ ≤ 1 / ζ * ‖fderiv ℝ f (x i)‖ ^ 2) ∧
      ∀ k₀ ≤ N, ‖x k₀ - xstar‖ ≤ ℓ / (4 * L) →
        ‖fderiv ℝ f (x k₀)‖ ≤ ζ →
        (∀ i, k₀ ≤ i → i ≤ N →
          ‖x i - xstar‖ ≤ ℓ / (4 * L) ∧ ‖fderiv ℝ f (x i)‖ ≤ ζ) ∧
        ∀ i, k₀ ≤ i → i < N → η₂ ≤ ρ i ∧
          ‖fderiv ℝ f (x (i + 1))‖ ≤ 1 / ζ * ‖fderiv ℝ f (x i)‖ ^ 2 := by
  dsimp only
  have hcap : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hz := CubicRegularization.localThreshold_pos hℓ hL h.theta_pos hcap
    h.updates.eta2_lt_one
  have hc := CubicRegularization.localQuadraticConstant_le_inv_threshold hℓ hL
    h.theta_pos hcap h.updates.eta2_lt_one
  refine ⟨hz, ?_, ?_⟩
  · intro i hi hx hs
    exact (h.local_quadratic_step hf hstar hℓ hL hlip hi hx hs).trans
      (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
  · intro k₀ hk₀ hx₀ hg₀
    obtain ⟨hi, ht⟩ := h.local_persistence hf hstar hℓ hL hmin.fderiv_eq_zero hlip
      hk₀ hx₀ hg₀
    refine ⟨hi, ?_⟩
    intro i hki hiN
    have hh := ht i hki hiN
    exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))⟩

end CartisGouldToint

namespace CartisGouldToint

/-- **Corrected Lemma 5.4.3.** Entry into the repaired positive-curvature
region with gradient at most `zeta <= localThreshold/2` gives an actual first
`epsilon`-stationary iterate within the natural budget
`ceil(logb 2 (1 + max 0 (logb 2 (zeta / epsilon))))`.
Every intervening trial is very successful, so the same bound counts successful
iterations. Consistent primitive prefixes describe the execution until its
actual gradient test passes; no termination index or convergence is assumed.
The positive correction inside the logarithm replaces the false printed count
and covers every positive accuracy, including the initial stopping test. -/
theorem lemma_5_4_3_corrected {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ ℓ L ζ ε : ℝ} {k₀ : ℕ}
    {xstar ustar : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f xstar)
    (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hζ : 0 < ζ) (hε : 0 < ε)
    (hζbound : ζ ≤ CubicRegularization.localThreshold ℓ L θ
      (max (σ 0) (γ₃ * L / (1 - η₂))) η₂ / 2)
    (hx₀ : ‖x k₀ - xstar‖ ≤ ℓ / (4 * L))
    (hg₀ : ‖fderiv ℝ f (x k₀)‖ ≤ ζ)
    (hprefix : ∀ N, (∀ i, k₀ ≤ i → i < N → ε < ‖fderiv ℝ f (x i)‖) →
      CubicRegularization.TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N) :
    ∃ K ≤ EvaluationComplexity.quadraticIterationBudget ζ ε,
      ‖fderiv ℝ f (x (k₀ + K))‖ ≤ ε ∧
      (∀ k < K, ε < ‖fderiv ℝ f (x (k₀ + k))‖) ∧
      CubicRegularization.TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ (k₀ + K) ∧
      ∀ k < K, η₂ ≤ ρ (k₀ + k) :=
  CubicRegularization.exists_local_target_count hf hstar hℓ hL hmin.fderiv_eq_zero
    hlip hζ hε hζbound hx₀ hg₀ hprefix

end CartisGouldToint

namespace CartisGouldToint

/-- **Corrected Theorem 5.4.4.** The original large-current-gradient count
holds with its single initialization allowance and actual cubic coefficient.
The total bound uses the repaired local threshold and the safe natural local
budget. To ensure the printed strict final inequality at every positive
`epsilon`, run the actual gradient stopping test at `epsilon/2`; the exclusion
of small gradients outside the local ball uses that same internal tolerance.
The backbone also proves the nonstrict `epsilon` version with the original
exclusion. All coefficients are fixed independently of the requested accuracy;
no termination, parameter cap, decrease floor or iteration count is assumed.
Function evaluations include initialization, and both gradient and Hessian
schedules include initialization and each actual successful update. -/
theorem theorem_5_4_4_corrected {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ L ℓ ζ ε flow : ℝ}
    {xstar ustar : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f xstar)
    (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) (hζ : 0 < ζ) (hε : 0 < ε)
    (hζbound : ζ ≤ CubicRegularization.localThreshold ℓ L θ
      (max (σ 0) (γ₃ * L / (1 - η₂))) η₂ / 2)
    (hexclude : ∀ i, ε / 2 < ‖fderiv ℝ f (x i)‖ →
      ‖fderiv ℝ f (x i)‖ ≤ ζ → ‖x i - xstar‖ ≤ ℓ / (4 * L))
    (hprefix : ∀ N, (∀ i < N, ε / 2 < ‖fderiv ℝ f (x i)‖) →
      CubicRegularization.TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N) :
    let G := (f (x 0) - flow) /
      (CubicRegularization.decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ζ ^ (3 / 2 : ℝ))
    let B := EvaluationComplexity.quadraticIterationBudget ζ (ε / 2)
    let A := 1 + |Real.log γ₁| / Real.log γ₂
    let C := Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
    ∃ K, ‖fderiv ℝ f (x K)‖ < ε ∧ ‖fderiv ℝ f (x K)‖ ≤ ε / 2 ∧
      (∀ i < K, ε / 2 < ‖fderiv ℝ f (x i)‖) ∧
      CubicRegularization.TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ K ∧
      ((EvaluationComplexity.successfulIterations
        {i | η₁ ≤ ρ i ∧ ζ < ‖fderiv ℝ f (x i)‖} K).card : ℝ) ≤ G + 1 ∧
      ((EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} K).card : ℝ) ≤
        G + 1 + B ∧
      (K : ℝ) ≤ (G + 1 + B) * A + C ∧
      (K : ℝ) + 1 ≤ (G + 1 + B) * A + C + 1 ∧
      ((EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} K).card : ℝ) + 1 ≤
        G + B + 2 := by
  dsimp only
  obtain ⟨K, hK, hfirst, hrun, hlarge, hsuccess, htrials, hfunctions, hderivatives⟩ :=
    CubicRegularization.exists_local_global_complexity hf hstar hℓ hL
      hmin.fderiv_eq_zero hlip hlow hζ (half_pos hε) hζbound hexclude hprefix
  refine ⟨K, ?_, hK, hfirst, hrun, hlarge, hsuccess, htrials, hfunctions, hderivatives⟩
  linarith only [hK, hε]

end CartisGouldToint
