import Numlib.Analysis.Calculus.EuclideanOne
import Numlib.Analysis.Calculus.LinearPullbackLipschitzJets

/-!
# Higher derivative bounds on Euclidean one-space

The scalar-coordinate lift preserves global Lipschitz constants of all higher derivatives.
-/

noncomputable section
open scoped NNReal
namespace EuclideanOne

/-- Scalar higher derivative Lipschitz estimates transport isometrically to Euclidean one-space. -/
theorem iteratedFDeriv_lipschitz {f : ℝ → ℝ} {p : ℕ} (hf : ContDiff ℝ p f)
    {L : ℝ≥0} (hL : LipschitzWith L (iteratedDeriv p f)) :
    LipschitzWith L (iteratedFDeriv ℝ p (lift f)) := by
  have h := ContinuousLinearMap.lipschitzWith_iteratedFDeriv_scalar_comp
    coord.toContinuousLinearEquiv.toContinuousLinearMap hf hL
  have hn : ‖coord.toContinuousLinearEquiv.toContinuousLinearMap‖ = 1 :=
    coord.toLinearIsometry.norm_toContinuousLinearMap
  have hn' : ‖coord.toContinuousLinearEquiv.toContinuousLinearMap‖₊ = 1 := by
    apply Subtype.ext
    exact hn
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [dist_eq_norm, lift, hn'] using h.dist_le_mul x y

end EuclideanOne
