import Numlib.Optimization.AnchoredTaylorModelBounds
import NumlibSurface.CartisGouldToint.Chapter12.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section02

/-!
# Chapter 14, Section 2: anchored bounds for feasible regularized models

The level-set assumptions supply every derivative remainder used in the regularization
analysis. Objective and model gap comparisons use exactly the same endpoint-feasible
displacements. These analytic statements impose no convexity on the feasible region.
-/

noncomputable section
open scoped Nat
open Optimization
namespace CartisGouldToint.Chapter14.Section02

variable {n r p j : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {X U : Set (EuclideanSpace ℝ (Fin n))} {x₀ x s : EuclideanSpace ℝ (Fin n)}
  {includeValue : Bool} {L B : ℕ → ℝ}

/-- The anchored source assumptions give sharp remainders for every derivative of the
actual Chapter 12 Taylor model, including trials outside the initial sublevel set. -/
theorem SmoothBoundedJetsOnLevelSet.derivative_remainder
    (hf : SmoothBoundedJetsOnLevelSet f X x₀ r includeValue U L B)
    (hp : 1 ≤ p) (hpr : p ≤ r) (hj : j ≤ p)
    (hx : x ∈ feasibleSublevelSet f X x₀) (hxs : x + s ∈ U) :
    ‖iteratedFDeriv ℝ j f (x + s) -
      iteratedFDeriv ℝ j (Chapter01.Section03.taylorModel f p x) s‖ ≤
      L p / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) :=
  hf.toHasAnchoredBoundedJets.derivative_remainder hp hpr hj hx hxs

/-- Every source regularized-model derivative differs from the objective derivative by
its sharp factorial bound under the actual anchored level-set assumptions. -/
theorem SmoothBoundedJetsOnLevelSet.regularized_derivative_difference
    (hf : SmoothBoundedJetsOnLevelSet f X x₀ r includeValue U L B)
    (hp : 1 ≤ p) (hpr : p ≤ r) (hj : j ≤ p)
    (hx : x ∈ feasibleSublevelSet f X x₀) (hxs : x + s ∈ X) (hs : s ≠ 0)
    {σ S : ℝ} (hσ : 0 ≤ σ) (hS : σ ≤ S) :
    ‖iteratedFDeriv ℝ j f (x + s) -
      iteratedFDeriv ℝ j (Chapter12.Section02.regularizedTaylorModel f p x σ) s‖ ≤
      (L p + S) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  simpa only [Chapter12.Section02.regularizedTaylorModel_eq_model] using
    hf.toHasAnchoredBoundedJets.regularized_derivative_difference hp hpr hj hx
      (hf.feasible_subset hxs) hs hσ hS

/-- The constrained gap and its actual source regularized-model gap differ by the full
factorial-weighted Taylor error. The model feasible set is translated from the original `X`. -/
theorem SmoothBoundedJetsOnLevelSet.regularized_gap_difference
    (hf : SmoothBoundedJetsOnLevelSet f X x₀ r includeValue U L B)
    (hp : 1 ≤ p) (hpr : p ≤ r) (hj : j ≤ p) (hX : IsClosed X)
    (hx : x ∈ feasibleSublevelSet f X x₀) (hxs : x + s ∈ X) (hs : s ≠ 0)
    {σ S δ : ℝ} (hσ : 0 ≤ σ) (hS : σ ≤ S) (hδ : 0 ≤ δ) :
    |constrainedTaylorGap f X j (x + s) δ -
      constrainedTaylorGap (Chapter12.Section02.regularizedTaylorModel f p x σ)
        (feasibleDisplacements X x) j s δ| ≤
      (L p + S) * ∑ i ∈ Finset.Icc 1 j,
        δ ^ i * ‖s‖ ^ (p - i + 1) / ((i ! : ℝ) * ((p - i + 1)! : ℝ)) := by
  simpa only [Chapter12.Section02.regularizedTaylorModel_eq_model] using
    hf.toHasAnchoredBoundedJets.regularized_gap_difference hp hpr hj hX hx hxs
      hf.feasible_subset hs hσ hS hδ

/-- A true failed constrained test and a passing actual model test supply the sharp
transfer inequality under f.D1pLaB.X or f.D0pLaB.X. No unit-radius convention is imposed. -/
theorem SmoothBoundedJetsOnLevelSet.transfer_of_gap_failure
    (hf : SmoothBoundedJetsOnLevelSet f X x₀ r includeValue U L B)
    (hp : 1 ≤ p) (hpr : p ≤ r) (hj : j ≤ p) (hX : IsClosed X)
    (hx : x ∈ feasibleSublevelSet f X x₀) (hxs : x + s ∈ X) (hs : s ≠ 0)
    {σ S δ ε θ : ℝ} (hσ : 0 ≤ σ) (hS : σ ≤ S) (hδ : 0 ≤ δ)
    (hfail : ε * δ ^ j / (j ! : ℝ) < constrainedTaylorGap f X j (x + s) δ)
    (hmodel : constrainedTaylorGap (Chapter12.Section02.regularizedTaylorModel f p x σ)
      (feasibleDisplacements X x) j s δ ≤ θ * ε * δ ^ j / (j ! : ℝ)) :
    (1 - θ) * ε * δ ^ j / (j ! : ℝ) <
      (L p + S) * ∑ i ∈ Finset.Icc 1 j,
        δ ^ i * ‖s‖ ^ (p - i + 1) / ((i ! : ℝ) * ((p - i + 1)! : ℝ)) := by
  apply hf.toHasAnchoredBoundedJets.transfer_of_gap_failure hp hpr hj hX hx hxs
    hf.feasible_subset hs hσ hS hδ hfail
  simpa only [Chapter12.Section02.regularizedTaylorModel_eq_model] using hmodel

end CartisGouldToint.Chapter14.Section02
