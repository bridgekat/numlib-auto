import Numlib.Optimization.Quadratic.HardCase.ProjectionCounterexample
import Numlib.Optimization.Quadratic.Regularization.Stopping
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Generalized hard-case iteration and weighted regularization termination

The stopping tests use the actual model in the inner product induced by the
positive-definite metric. The dual derivative norm is therefore the metric
inverse norm of its gradient. The Hessian bound is stated on every metric-unit
direction, equivalently as the least eigenvalue bound for the scaled Hessian.

Equation (9.3.14c) prints an unscaled Euclidean least eigenvalue, whereas the
preceding prose requests the appropriate metric scalings. The literal printed
conclusion is false: take M=4I, H=−8I, τ=2, σ=1, r=3, g=0, s=(1/2,0),
θ₁=2 and θ₂=1. All three scalar tests hold, but the Euclidean Hessian in the
orthogonal unit direction equals −4, below the claimed −1. The declaration
`theorem_9_3_2_scaled` proves the intended metric-scaled correction; for M=I
this is the printed Euclidean bound.

Theorem 9.3.1 has a separate projection error: generalized inverse iteration
requires a nonzero metric projection onto the least eigenspace. Its printed
Euclidean projection permits a starting vector trapped in a higher eigenspace.
The concrete two-dimensional counterexample below has legal fixed controls
n=2, gamma=2, omega=1 and arbitrarily close initial shifts, but no convergence.
-/

namespace CartisGouldToint

/-- The three actual stopping tests (9.3.14) for the weighted regularized model.
The first and second Fréchet derivatives are taken in its metric inner product;
the universal unit-direction Hessian bound is the scaled least eigenvalue test. -/
def regularizationStepTermination {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n))
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hM : M.toLinearMap.IsSymmetricCoercive) (σ r θ₁ θ₂ : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  let m := regularizationSubproblemModel g H M hM σ r ∘
    QuadraticRegularization.Metric.toOriginal M hM
  let z := WithEnergy.equiv M.toLinearMap hM s
  m z ≤ m 0 ∧ ‖fderiv ℝ m z‖ ≤ θ₁ / 2 * weightedNorm M hM s ^ 2 ∧
    ∀ v : WithEnergy M.toLinearMap hM, ‖v‖ = 1 →
      -θ₂ * weightedNorm M hM s ≤ fderiv ℝ (fderiv ℝ m) z v v

/-- The metric-scaled correction of Theorem 9.3.2: the three scalar secular tests
guarantee actual model decrease,
small metric-dual gradient and the scaled Hessian lower bound. Membership in the
feasible pencil region means a nonnegative shift and a positive-semidefinite
shifted pencil; the linear system itself is assumed exactly as in (8.2.2).
This includes singular feasible endpoints whenever the system has a solution.
The printed unscaled Hessian bound is false for general metrics; this theorem
uses the scaled Hessian required by the preceding source prose. -/
theorem theorem_9_3_2_scaled {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : H.toLinearMap.IsSymmetric) (hM : M.toLinearMap.IsSymmetricCoercive)
    {σ r τ θ₁ θ₂ : ℝ} (hσ : 0 < σ) (hr : 2 < r) (hτ : 0 ≤ τ)
    (_hθ₁ : 0 < θ₁) (_hθ₂ : 0 < θ₂) {s : EuclideanSpace ℝ (Fin n)}
    (hsolve : (H + τ • M) s = -g)
    (hpsd : ∀ v, 0 ≤ inner ℝ ((H + τ • M) v) v)
    (hu : weightedNorm M hM s ^ 2 ≤
      (r / 2) ^ (2 / (r - 2)) * (τ / σ) ^ (2 / (r - 2)))
    (hc : |(weightedNorm M hM s ^ 2) ^ ((r - 2) / 2) - τ / σ| ≤
      θ₁ / (2 * σ) * (weightedNorm M hM s ^ 2) ^ (1 / 2 : ℝ))
    (hl : -θ₂ / σ * (weightedNorm M hM s ^ 2) ^ (1 / 2 : ℝ) ≤
      (weightedNorm M hM s ^ 2) ^ ((r - 2) / 2) - τ / σ) :
    regularizationStepTermination g H M hM σ r θ₁ θ₂ s :=
  QuadraticRegularization.Metric.stopping_tests M hM g H hH hr hσ hτ
    hsolve hpsd hu hc hl

end CartisGouldToint

namespace CartisGouldToint

/-- The actual primitive trace of Algorithm 9.3.1: normalized inverse solves,
Rayleigh evaluations and the legal scalar control updates. The spectral-start
projection guard is a separate hypothesis; its printed Euclidean form is false
for general metrics, as witnessed by `theorem_9_3_1_counterexample`. -/
abbrev hardCaseInverseIterationRun {n : ℕ}
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (least : ℝ) (shift : ℕ → ℝ) (vector : ℕ → EuclideanSpace ℝ (Fin n))
    (innerVector : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (count : ℕ → ℕ)
    (exponent weight : ℕ → ℝ) (ωL ωU γL γU : ℝ) (nU : WithTop ℕ) : Prop :=
  QuadraticSecular.HardCase.Run H M least shift vector innerVector count exponent weight
    ωL ωU γL γU nU

/-- Counterexample to the literal generalized-metric Theorem 9.3.1. The actual
symmetric Hessian has least generalized eigenvalue -1 in a genuinely positive
metric. Its starting vector is metric-unit and satisfies the printed nonzero
Euclidean projection, but has zero metric projection onto the least eigenspace.
For every positive neighborhood of the target 1, an actual legal n=2, gamma=2,
omega=1 run starts in that neighborhood and fails to converge to the target.
The corrected theorem must require nonzero metric projection instead. -/
theorem theorem_9_3_1_counterexample :
    let H := QuadraticSecular.HardCaseCounterexample.hessian
    let M := QuadraticSecular.HardCaseCounterexample.metric
    let v := QuadraticSecular.HardCaseCounterexample.leastVector
    let z := QuadraticSecular.HardCaseCounterexample.trappedVector
    M.toLinearMap.IsSymmetricCoercive ∧ H.toLinearMap.IsSymmetric ∧
      energyNorm M.toLinearMap v = 1 ∧ H v = -(1 : ℝ) • M v ∧
      (∀ x, energyNorm M.toLinearMap x = 1 → -1 ≤ inner ℝ (H x) x) ∧
      energyNorm M.toLinearMap z = 1 ∧ inner ℝ z v ≠ 0 ∧ inner ℝ (M z) v = 0 ∧
      ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 1 < a ∧ a < 1 + δ ∧
        hardCaseInverseIterationRun H M (-1)
          (QuadraticSecular.HardCaseCounterexample.shifts a) (fun _ => z) (fun _ _ => z)
          (fun _ => 2) (fun _ => 2) (fun _ => 1) 1 1 (3 / 2) (1 / 2) (2 : WithTop ℕ) ∧
        (∀ k, secularFunction H M 0 (QuadraticSecular.HardCaseCounterexample.shifts a k) <
          QuadraticSecular.HardCaseCounterexample.shifts a k ^ 2) ∧
        ¬Filter.Tendsto (QuadraticSecular.HardCaseCounterexample.shifts a)
          Filter.atTop (nhds 1) := by
  dsimp only
  refine ⟨QuadraticSecular.HardCaseCounterexample.metric_coercive,
    QuadraticSecular.HardCaseCounterexample.hessian_symmetric,
    QuadraticSecular.HardCaseCounterexample.least_metric_norm,
    QuadraticSecular.HardCaseCounterexample.least_eigenvector,
    fun _ hx => QuadraticSecular.HardCaseCounterexample.least_rayleigh hx,
    QuadraticSecular.HardCaseCounterexample.trapped_metric_norm,
    ?_, QuadraticSecular.HardCaseCounterexample.metric_projection_zero, ?_⟩
  · rw [QuadraticSecular.HardCaseCounterexample.printed_projection]
    norm_num
  · intro δ hδ
    obtain ⟨a, ha, hclose, hrun, hnot⟩ :=
      QuadraticSecular.HardCaseCounterexample.arbitrarily_close_counterexample hδ
    exact ⟨a, ha, hclose, hrun,
      QuadraticSecular.HardCaseCounterexample.upper_secular_region ha, hnot⟩

end CartisGouldToint
