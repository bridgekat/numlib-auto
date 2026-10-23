import Numlib.Optimization.Quadratic.HardCase.Classification
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Easy- and hard-case global minimizers

The generalized inverse is the actual metric spectral inverse, with zero
reciprocal on singular components. It satisfies `A G A = A`; its particular
vector is metric-orthogonal to the full shifted kernel. An ordinary Euclidean
Moore–Penrose inverse need not produce this metric-orthogonal particular vector.

For repeated least eigenvalues the correction lies in the entire eigenspace.
The source single-eigenvector description is existential for each minimizer.
Singular interior trust-region minimizers at shift zero need only be feasible;
the source boundary-radius equation is imposed only for positive multipliers.
-/

namespace CartisGouldToint

/-- The actual metric generalized inverse in (8.3.2), including singular shifts. -/
noncomputable abbrev quadraticPencilGeneralizedInverse {n : ℕ}
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M) (τ : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := B.metricInverse τ

/-- Corollary 8.3.1: every global minimizer has its compatible metric
particular solution plus a full-kernel correction, the exact norm and value,
and uniqueness in the easy case. The singular correction belongs to the
entire least eigenspace, covering arbitrary multiplicity. -/
theorem corollary_8_3_1 {n : ℕ} [NeZero n]
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    (hH : H.toLinearMap.IsSymmetric) (hM : M.toLinearMap.IsSymmetricCoercive)
    (g s : EuclideanSpace ℝ (Fin n)) {r σ : ℝ} (hr : 2 < r) (hσ : 0 < σ)
    (hmin : ∀ t, regularizationSubproblemModel g H M hM σ r s ≤
      regularizationSubproblemModel g H M hM σ r t) :
    let τ := σ * weightedNorm M hM s ^ (r - 2)
    let ss := -(quadraticPencilGeneralizedInverse B τ g)
    0 ≤ τ ∧ -B.leftmost ≤ τ ∧ (H + τ • M) ss = -g ∧
      (∃ v, (H + τ • M) v = 0 ∧ s = ss + v ∧
        (τ = -B.leftmost → H v = B.leftmost • M v)) ∧
      weightedNorm M hM s = (τ / σ) ^ (1 / (r - 2)) ∧
      regularizationSubproblemModel g H M hM σ r s =
        (inner ℝ g ss - (r - 2) / r * τ * (τ / σ) ^ (2 / (r - 2))) / 2 ∧
      (-B.leftmost < τ → s = ss ∧
        ∀ t, regularizationSubproblemModel g H M hM σ r t ≤
          regularizationSubproblemModel g H M hM σ r s → t = s) := by
  have hm : ∀ t, QuadraticOptimality.model H g s +
      σ / r * energyNorm M.toLinearMap s ^ r ≤ QuadraticOptimality.model H g t +
        σ / r * energyNorm M.toLinearMap t ^ r := by
    simpa only [QuadraticOptimality.model_eq, regularizationSubproblemModel,
      quadraticModel, weightedNorm] using hmin
  have hc := B.regularization_classification hH hM g s hr hσ hm
  simpa only [QuadraticSecular.PencilBasis.particular_eq_neg_metricInverse,
    quadraticPencilGeneralizedInverse, QuadraticOptimality.model_eq,
    regularizationSubproblemModel, quadraticModel, weightedNorm] using hc

/-- Corollary 8.3.2: every feasible global trust-region minimizer has a
compatible metric particular solution and a full-kernel correction, with the
exact minimum value and complementarity. Positive multipliers enforce the
boundary radius; zero multipliers retain all feasible interior corrections.
The easy case gives equality to the particular vector and uniqueness. -/
theorem corollary_8_3_2 {n : ℕ} [NeZero n]
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    (hH : H.toLinearMap.IsSymmetric) (hM : M.toLinearMap.IsSymmetricCoercive)
    (g s : EuclideanSpace ℝ (Fin n)) {Δ : ℝ} (hΔ : 0 < Δ)
    (hs : weightedNorm M hM s ≤ Δ)
    (hmin : ∀ t, weightedNorm M hM t ≤ Δ → quadraticModel g H s ≤ quadraticModel g H t) :
    ∃ τ : ℝ, let ss := -(quadraticPencilGeneralizedInverse B τ g)
      0 ≤ τ ∧ -B.leftmost ≤ τ ∧ (H + τ • M) ss = -g ∧
      (∃ v, (H + τ • M) v = 0 ∧ s = ss + v ∧
        (τ = -B.leftmost → H v = B.leftmost • M v)) ∧
      τ * (weightedNorm M hM s ^ 2 - Δ ^ 2) = 0 ∧
      (0 < τ → weightedNorm M hM s = Δ) ∧
      quadraticModel g H s = (inner ℝ g ss - τ * Δ ^ 2) / 2 ∧
      (-B.leftmost < τ → s = ss ∧
        ∀ t, weightedNorm M hM t ≤ Δ → quadraticModel g H t ≤ quadraticModel g H s → t = s) := by
  have hm : ∀ t, energyNorm M.toLinearMap t ≤ Δ →
      QuadraticOptimality.model H g s ≤ QuadraticOptimality.model H g t := by
    simpa only [QuadraticOptimality.model_eq, quadraticModel, weightedNorm] using hmin
  have hc := B.trust_region_classification hH hM g s hΔ hs hm
  simpa only [QuadraticSecular.PencilBasis.particular_eq_neg_metricInverse,
    quadraticPencilGeneralizedInverse, QuadraticOptimality.model_eq,
    quadraticModel, weightedNorm] using hc

end CartisGouldToint
