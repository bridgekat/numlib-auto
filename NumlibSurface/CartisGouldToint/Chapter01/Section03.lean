import Numlib.Optimization.RegularizedTaylorModel
import Numlib.Optimization.HessianCurvature
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Common notation

The Taylor polynomial uses the actual iterated Fréchet derivatives, with factorial normalization.
-/
noncomputable section
namespace CartisGouldToint.Chapter01.Section03

/-- The degree-`p` Taylor polynomial `T_{f,p}(x,s)` from Section 1.3. -/
def taylorModel {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Optimization.RegularizedTaylorModel.taylorModel f p x s

/-- The least eigenvalue of the actual Hessian, represented by its Rayleigh infimum. -/
def leastHessianEigenvalue {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Optimization.leastCurvature (fderiv ℝ (fderiv ℝ f) x)

/-- In positive dimension the Hessian's least curvature is an actual eigenvalue. -/
theorem leastHessianEigenvalue_hasEigenvalue {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f x) :
    Module.End.HasEigenvalue
      (InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ f) x)).toLinearMap
      (leastHessianEigenvalue f x) :=
  Optimization.hasEigenvalue_leastCurvature (Optimization.hessian_symmetric hf)

/-- The least-Hessian-eigenvalue lower bound is exactly a quadratic-form lower bound. -/
theorem le_leastHessianEigenvalue_iff {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    a ≤ leastHessianEigenvalue f x ↔
      ∀ u, a * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x u u :=
  Optimization.le_leastCurvature_iff _ _

end CartisGouldToint.Chapter01.Section03
