import NumlibSurface.CartisGouldToint.Chapter13.Section03
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDARadii
import Numlib.Optimization.ExplicitRegularizationBounds

/-!
# Chapter 13, Section 3: actual ARqpEDA executions

Algorithm 13.3.2 retains the actual inspections and inner executions of Section 13.1.
The literal short-step check covers orders through `q`. Stopping additionally checks
(13.3.17), and the trial ratio uses actual approximate endpoint values with known errors.
Step 0 makes no value query. The first trial obtains both endpoint values; later trials
may reuse a sufficiently accurate cached current value. All actual calls are recorded.
The certification and accepted-value-payment clauses below do not assert the remaining
printed global parameter, request-threshold reachability or complexity theorems.
-/

noncomputable section
namespace CartisGouldToint.Chapter13.Section03
open Optimization ExplicitRegularization
variable {n : ℕ}

/-- The source ARqpIDA constants with the additional restriction (13.3.13). -/
abbrev ARqpEDAParameters := ExplicitRegularization.Parameters

/-- Algorithm 13.3.2: actual finite prefixes with known tensor and value errors,
observable Step 1.5 certification, literal `q`-checked Step 2, source parameter updates,
and one or two actual value requests per trial. Initialization makes no value query;
rejected steps reuse the same derivative key and retain the current endpoint value cache. -/
abbrev algorithm_13_3_2 (P : ARqpEDAParameters)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (O : ExplicitAccuracyOracle f P.p) (N : ℕ) :=
  ExplicitRegularization.Execution P O N

namespace ARqpEDA

/-- A full ARqpEDA run obeys every operational transition until its first observable
certificate, using the actual selected inspection at each state. -/
abbrev algorithm (P : ARqpEDAParameters) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (O : ExplicitAccuracyOracle f P.p) (state : ℕ → ExplicitRegularization.State
      (EuclideanSpace ℝ (Fin n)))
    (inspection : ∀ k, ExplicitRegularization.Inspection P O.derivative (state k))
    (trial accepted : ℕ → Bool)
    (queries : ℕ → List (EuclideanSpace ℝ (Fin n) × ℝ)) : Prop :=
  ExplicitRegularization.IsExecution P O state inspection trial accepted queries

/-- The actual known-error certificate implies true source approximate optimality.
This is part (i) of Lemma 13.3.6; its global request-threshold clause remains separate. -/
theorem certified_quality {P : ARqpEDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ExplicitAccuracyOracle f P.p} {N : ℕ}
    (r : algorithm_13_3_2 P O N)
    (hc : ExplicitRegularization.Certified P (r.state N) (r.inspection N)) :
    HigherOrderApproximateRegularization.SatisfiesCriteria P.toImplicitParameters.toParameters
      f (r.state N).point (r.inspection N).radii :=
  r.certified_quality hc

/-- Every actual accepted trial retains the source half-acceptance true-objective payment,
including when its old endpoint reuses a more accurate cached value. -/
theorem accepted_value_decrease {P : ARqpEDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ExplicitAccuracyOracle f P.p}
    {a : ExplicitRegularization.State (EuclideanSpace ℝ (Fin n))}
    {s : EuclideanSpace ℝ (Fin n)} (v : ExplicitRegularization.ValueTrial P O a s)
    (ha : P.eta1 ≤ v.ratio) :
    P.eta1 * InexactTaylorModels.decrement (O.derivative a.point a.request) P.p s / 2 ≤
      f a.point - f (a.point + s) := v.accepted_decrease ha

end ARqpEDA
end CartisGouldToint.Chapter13.Section03
