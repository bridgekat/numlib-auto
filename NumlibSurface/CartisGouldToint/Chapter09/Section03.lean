import Numlib.Optimization.Quadratic.Regularization.Stopping
import NumlibSurface.CartisGouldToint.Chapter08.Section01

/-!
# Constructive termination for a weighted regularized quadratic

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
