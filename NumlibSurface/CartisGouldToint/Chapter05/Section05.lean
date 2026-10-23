import Numlib.Optimization.Regularization.Universal.Threshold

/-!
# Universal regularization with real powers

The source finite factorial and actual model tests are retained. Optional
second-order accuracy disables its derivative test explicitly. Trial-point
stopping is checked before acceptance, and the parameter has no added floor.
The final row of the printed update table is read using the surrounding prose:
failure of either the ratio or a length test increases the parameter.
-/
namespace CartisGouldToint
/-- Algorithm5.5.1: a genuine prefix before trial-point termination. -/
abbrev universalArpRun {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : UniversalRegularization.Settings p) (ε1 : ℝ) (ε2 : Option ℝ)
    (D : UniversalRegularization.Data (EuclideanSpace ℝ (Fin n))) (N : ℕ) : Prop :=
  UniversalRegularization.Run f P ε1 ε2 D N

/-- **Lemma5.5.1.** Every actual computed model step gives the stated Taylor
prediction decrease, with the finite factorial of its real power. This holds
also for the terminal trial, which is checked before acceptance. -/
theorem lemma_5_5_1 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : UniversalRegularization.Settings p} {ε2 : Option ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} {σ : ℝ}
    (h : UniversalRegularization.Step f P ε2 x s σ) :
    σ / Real.finiteFactorial P.r * ‖s‖ ^ P.r ≤
      f x - TaylorModel.eval f p x s := h.taylor_decrease.le
/-- **Lemma5.5.2.** Every actual computed step satisfies the displayed gradient
bound. With second-order accuracy enabled, every actual unit Hessian value has
the displayed negative-curvature bound, equivalently the least-eigenvalue bound
in finite-dimensional Euclidean space. Both coefficients use the source finite
real factorial, including Hölder exponents zero and one. -/
theorem lemma_5_5_2 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : UniversalRegularization.Settings p} {ε2 : Option ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} {σ H β : ℝ}
    (hf : ContDiff ℝ p f) (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (hσ : 0 ≤ σ) (hp : ∀ e ∈ ε2, 2 ≤ p)
    (h : UniversalRegularization.Step f P ε2 x s σ) :
    ‖fderiv ℝ f (x + s)‖ ≤
      H / Real.finiteFactorial ((p : ℝ) + β - 1) * ‖s‖ ^ ((p : ℝ) + β - 1) +
      σ / Real.finiteFactorial (P.r - 1) * ‖s‖ ^ (P.r - 1) +
      P.theta1 * ‖s‖ ^ (P.r - 1) ∧
    ∀ e ∈ ε2, ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
      -iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) ≤
        H / Real.finiteFactorial ((p : ℝ) + β - 2) * ‖s‖ ^ ((p : ℝ) + β - 2) +
        σ / Real.finiteFactorial (P.r - 2) * ‖s‖ ^ (P.r - 2) +
        P.theta2 * ‖s‖ ^ (P.r - 2) :=
  ⟨h.gradient_bound hf hH hβ hβ1 hholder hσ,
    fun e he v hv => h.curvature_bound (hp e he) hf hH hβ hβ1 hholder hσ he v hv⟩
/-- **Lemma5.5.3.** The source threshold gives the very successful ratio and
all enabled length checks. With second-order accuracy disabled the second
threshold is vacuous; with it enabled the two thresholds together are exactly
the maximum of the three source terms in(5.5.20). -/
theorem lemma_5_5_3 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : UniversalRegularization.Settings p} {ε2 : Option ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} {σ H β : ℝ}
    (hf : ContDiff ℝ p f) (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    (hσ : 0 < σ) (h : UniversalRegularization.Step f P ε2 x s σ)
    (hp : ∀ e ∈ ε2, 2 ≤ p) (ha2 : ∀ e ∈ ε2, 2 ≤ (p : ℝ) + β)
    (hparameter : max (P.theta1 * Real.finiteFactorial (P.r - 1))
      (UniversalRegularization.betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r)) ≤ σ)
    (hsecond : ∀ e ∈ ε2, P.theta2 * Real.finiteFactorial (P.r - 2) ≤ σ) :
    P.eta2 ≤ (f x - f (x + s)) / (f x - TaylorModel.eval f p x s) ∧
      P.alpha1 * ‖fderiv ℝ f (x + s)‖ ≤ σ * ‖s‖ ^ (P.r - 1) ∧
      ∀ e ∈ ε2, ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
        -P.alpha2 * iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) ≤ σ * ‖s‖ ^ (P.r - 2) :=
  h.very_successful hf hH hβ hβ1 hholder ha har hσ hp ha2
    ((le_max_left _ _).trans hparameter) hsecond ((le_max_right _ _).trans hparameter)
/-- **Lemma5.5.4.** The source accuracy thresholds imply the step-dependent
threshold and hence a very successful trial whenever its literal stopping test
fails. The optional second-order threshold is disabled explicitly for first
order; the two maxima combine to the four-term maximum in(5.5.29). -/
theorem lemma_5_5_4 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : UniversalRegularization.Settings p} {ε1 : ℝ} {ε2 : Option ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} {σ H β : ℝ}
    (hf : ContDiff ℝ p f) (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    (hσ : 0 < σ) (hε1 : 0 < ε1) (hε2 : ∀ e ∈ ε2, 0 < e)
    (h : UniversalRegularization.Step f P ε2 x s σ)
    (hfail : ¬UniversalRegularization.Stops f ε1 ε2 (x + s))
    (hp : ∀ e ∈ ε2, 2 ≤ p) (ha2 : ∀ e ∈ ε2, 2 < (p : ℝ) + β)
    (hfirst : max (P.theta1 * Real.finiteFactorial (P.r - 1))
      (UniversalRegularization.thresholdCoefficient P H β 1 *
        ε1 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1))) ≤ σ)
    (hsecond : ∀ e ∈ ε2, max (P.theta2 * Real.finiteFactorial (P.r - 2))
      (UniversalRegularization.thresholdCoefficient P H β 2 *
        e ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2))) ≤ σ) :
    max (P.theta1 * Real.finiteFactorial (P.r - 1))
      (UniversalRegularization.betaCoefficient P H β * ‖s‖ ^ ((p : ℝ) + β - P.r)) ≤ σ ∧
      (∀ e ∈ ε2, P.theta2 * Real.finiteFactorial (P.r - 2) ≤ σ) ∧
      P.eta2 ≤ (f x - f (x + s)) / (f x - TaylorModel.eval f p x s) ∧
      P.alpha1 * ‖fderiv ℝ f (x + s)‖ ≤ σ * ‖s‖ ^ (P.r - 1) ∧
      ∀ e ∈ ε2, ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
        -P.alpha2 * iteratedFDeriv ℝ 2 f (x + s) (fun _ => v) ≤ σ * ‖s‖ ^ (P.r - 2) := by
  have hκ := h.threshold_of_trial_failure hf hH hβ hβ1 hholder ha har hσ hε1 hε2
    hfail hp ha2 hfirst hsecond
  have hθ1 := (le_max_left _ _).trans hfirst
  have hθ2 : ∀ e ∈ ε2, P.theta2 * Real.finiteFactorial (P.r - 2) ≤ σ :=
    fun e he => (le_max_left _ _).trans (hsecond e he)
  exact ⟨max_le hθ1 hκ, hθ2, h.very_successful hf hH hβ hβ1 hholder ha har hσ hp
    (fun e he => (ha2 e he).le) hθ1 hθ2 hκ⟩
end CartisGouldToint
