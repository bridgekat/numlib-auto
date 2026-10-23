import Numlib.Optimization.Quadratic.Optimality.Regularization
import Numlib.Optimization.Quadratic.Optimality.Metric

/-!
# Weighted regularized quadratic global optimality

The exact energy-space transport preserves both the original quadratic and
the full real-power metric penalty, its multiplier, and shifted curvature.
-/

namespace QuadraticOptimality.Metric
open QuadraticRegularization.Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (M : E →L[ℝ] E) (hM : M.toLinearMap.IsSymmetricCoercive)

/-- The metric-coordinate regularized model equals the original model with its actual energy
norm. -/
theorem regularized_eq (H : E →L[ℝ] E) (g : E) (σ r : ℝ) (s : E) :
    regularized (hessian M hM H) (gradient M hM g) σ r
      (WithEnergy.equiv M.toLinearMap hM s) = 
      inner ℝ g s + inner ℝ (H s) s / 2 + σ / r * energyNorm M.toLinearMap s ^ r := by
  rw [regularized, model_eq]
  rfl

include hM in
/-- The full regularized quadratic global-minimum characterization holds for an arbitrary
positive-definite metric, including every zero or nonzero minimizer. -/
theorem regularized_iff {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {r σ : ℝ} (hr : 2 < r) (hσ : 0 ≤ σ) :
    (∀ t : E, inner ℝ g s + inner ℝ (H s) s / 2 + σ / r * energyNorm M.toLinearMap s ^ r ≤
      inner ℝ g t + inner ℝ (H t) t / 2 + σ / r * energyNorm M.toLinearMap t ^ r) ↔
    (H + (σ * energyNorm M.toLinearMap s ^ (r - 2)) • M) s = -g ∧
      ∀ v, 0 ≤ inner ℝ ((H + (σ * energyNorm M.toLinearMap s ^ (r - 2)) • M) v) v := by
  have hh := QuadraticOptimality.regularized_iff (hessian_symmetric M hM hH)
    (gradient M hM g) (WithEnergy.equiv M.toLinearMap hM s) hr hσ
  constructor
  · intro hm
    have hm' : ∀ t : WithEnergy M.toLinearMap hM,
        regularized (hessian M hM H) (gradient M hM g) σ r
          (WithEnergy.equiv M.toLinearMap hM s) ≤
        regularized (hessian M hM H) (gradient M hM g) σ r t := by
      intro t
      obtain ⟨v, rfl⟩ := (WithEnergy.equiv M.toLinearMap hM).surjective t
      simpa only [regularized_eq] using hm v
    obtain ⟨hsolve, hPSD⟩ := hh.mp hm'
    refine ⟨(solve_iff M hM H g s _).mp hsolve, ?_⟩
    intro v
    simpa only [shifted_inner, WithEnergy.norm_equiv] using
      hPSD (WithEnergy.equiv M.toLinearMap hM v)
  · rintro ⟨hsolve, hPSD⟩
    have hm := hh.mpr ⟨(solve_iff M hM H g s _).mpr hsolve, ?_⟩
    · intro t
      simpa only [regularized_eq] using hm (WithEnergy.equiv M.toLinearMap hM t)
    · intro v
      obtain ⟨w, rfl⟩ := (WithEnergy.equiv M.toLinearMap hM).surjective v
      simpa only [shifted_inner, WithEnergy.norm_equiv] using hPSD w

include hM in
/-- Positive definiteness of the original shifted pencil implies uniqueness of the actual
weighted regularized minimizer. -/
theorem unique_regularized {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {r σ : ℝ} (hr : 2 < r) (hσ : 0 ≤ σ)
    (hsolve : (H + (σ * energyNorm M.toLinearMap s ^ (r - 2)) • M) s = -g)
    (hPD : ∀ v, v ≠ 0 →
      0 < inner ℝ ((H + (σ * energyNorm M.toLinearMap s ^ (r - 2)) • M) v) v) :
    ∀ t : E, inner ℝ g t + inner ℝ (H t) t / 2 + σ / r * energyNorm M.toLinearMap t ^ r ≤
      inner ℝ g s + inner ℝ (H s) s / 2 + σ / r * energyNorm M.toLinearMap s ^ r → t = s := by
  intro t ht
  have he := QuadraticOptimality.unique_regularized (hessian_symmetric M hM hH)
    (gradient M hM g) (WithEnergy.equiv M.toLinearMap hM s) hr hσ
    ((solve_iff M hM H g s _).mpr hsolve) ?_
    (WithEnergy.equiv M.toLinearMap hM t) (by simpa only [regularized_eq] using ht)
  · exact (WithEnergy.equiv M.toLinearMap hM).injective he
  · intro v hv
    obtain ⟨w, rfl⟩ := (WithEnergy.equiv M.toLinearMap hM).surjective v
    have hw : w ≠ 0 := by intro hh; subst w; exact hv rfl
    simpa only [shifted_inner, WithEnergy.norm_equiv] using hPD w hw

end QuadraticOptimality.Metric
