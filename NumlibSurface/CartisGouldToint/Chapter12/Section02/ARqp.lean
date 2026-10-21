import NumlibSurface.CartisGouldToint.Chapter12.Section02
import Numlib.Optimization.HigherOrderApproximateRegularization

/-!
# ARqp and its detailed inner procedure

The outer trace distinguishes the two stopping locations, actual objective evaluation,
acceptance and rejection, the three parameter update intervals, inherited radii, and cached
derivatives. The inner trace records fraction-of-global-decrease minimization, increasing
accuracy, ordered Taylor-gap tests and radius halving at orders at least three.

These are legal execution specifications. Finite termination and the quantitative bounds
remain separate mathematical obligations. The source's inner long-step test uses `≥ 1`,
whereas its outer interface uses `> 1`; no theorem identifies these boundary cases here.
-/

noncomputable section
namespace CartisGouldToint.Chapter12.Section02
open Optimization
variable {n : ℕ}
namespace ARqp

/-- The parameters and strict accuracy intervals of Algorithm 12.2.2. -/
abbrev Parameters := HigherOrderApproximateRegularization.Parameters

/-- The canonical model is exactly the source's factorial-normalized model (12.2.23). -/
theorem model_eq (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) :
    HigherOrderApproximateRegularization.model f p x sigma =
      regularizedTaylorModel f p x sigma :=
  (regularizedTaylorModel_eq_model f p x sigma).symm

end ARqp

/-- Algorithm 12.2.2: legal finite ARqp executions, including both stopping locations.
All witnesses concern actual Taylor gaps, and counts include individual derivative orders.
The endpoint may continue, so the definition makes no finite-termination assumption. -/
abbrev algorithm_12_2_2 (P : ARqp.Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (delta : ℕ → ℝ) (N : ℕ) :=
  HigherOrderApproximateRegularization.OuterExecution P f x sigma delta N

/-- Algorithm 12.2.3: the detailed inner program, on the actual model (12.2.23).
The global minimum is attained, not an assumed existence oracle. Legal prefixes do not
assume the finite-return theorem. Fraction one forces an actual global minimizing step. -/
abbrev algorithm_12_2_3 (P : ARqp.Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (minimizer : EuclideanSpace ℝ (Fin n)) (N : ℕ) :=
  HigherOrderApproximateRegularization.InnerExecution P
    (HigherOrderApproximateRegularization.model f P.p x sigma) minimizer N

/-- A boundary-corrected variant of the detailed inner transition: a unit step is tested,
and a longer step returns the inherited outer radii required by (12.2.28).
This is stated separately from the source's Algorithm 12.2.3. -/
abbrev arqpInnerTransitionStrictBoundary (P : ARqp.Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (sigma : ℝ) (minimizer : EuclideanSpace ℝ (Fin n)) (inherited : ℕ → ℝ) :=
  HigherOrderApproximateRegularization.CorrectedInnerTransition P
    (HigherOrderApproximateRegularization.model f P.p x sigma) minimizer inherited

/-- The Cᵖ clause of Lemma 12.2.7, valid for every degree and without objective smoothness.
The sharp derivative bounds and Lipschitz constant remain separate obligations. -/
theorem regularizedTaylorModel_contDiff (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) :
    ContDiff ℝ p (regularizedTaylorModel f p x sigma) := by
  rw [← ARqp.model_eq]
  exact HigherOrderApproximateRegularization.contDiff_model f p x sigma

end CartisGouldToint.Chapter12.Section02
