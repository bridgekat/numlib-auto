import NumlibSurface.CartisGouldToint.AppendixB.Chapter02.FiniteValley
import Numlib.Optimization.SteepestDescentValleyLocalRays

/-!
# Smoothness and first local ray minima for the finite SDEX completion

These results complete the analytic bounds and first-local-minimum clauses for the
actual finite family introduced in `FiniteValley`. The integer count is rounded and the
right tail is completed by a unit transition to a constant. Equation (B.2.24) extends the
objective affinely at the left endpoint and freezes width and midpoint; a reflection in
x would reverse the nonzero first derivative and would not be C1. The reflection used
in the transverse profile is instead reflection in the centered vertical coordinate.

The first local minimum in Lemma B.2.6 is not a global ray minimum. The actual global
counterexample `finite_valley_not_global_exact` and the independent Chapter 2 quadratic
global exact-search lower bound retain their distinct meanings. The parent `Chapter02`
module identifies the concrete source cells and records the finite range, integer count,
explicit exterior completion and first-local interpretation in Lemmas B.2.2–B.2.6.
-/

noncomputable section
open Optimization.SteepestDescentValley Set
open scoped NNReal

namespace CartisGouldToint.AppendixB.Chapter02

/-- The actual moving-strip term and its first and second Fréchet derivatives are
uniformly bounded on the whole plane; in particular this includes all mixed derivatives. -/
theorem finite_valley_uniform_mixed_derivatives :
    ∃ K > 0, ∀ (P : Parameters) (j : ℕ), j ≤ 2 →
      ∀ p : EuclideanSpace ℝ (Fin 2),
        ‖iteratedFDeriv ℝ j (euclideanMovingProfile P) p‖ ≤ K :=
  exists_euclideanMovingProfile_jet_bound

/-- The full actual finite objective has uniformly bounded genuine Hessian operator
norm, with a constant fixed before the tolerance and cell count. -/
theorem finite_valley_uniform_hessian_bound :
    ∃ K > 0, ∀ (P : Parameters) (p : EuclideanSpace ℝ (Fin 2)),
      ‖iteratedFDeriv ℝ 2 (euclideanObjective P) p‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := exists_euclideanObjective_derivative_bound
  exact ⟨K, hK, fun P p => hb P 2 (by omega) (by omega) p⟩

/-- All actual completed finite valley objectives have globally Lipschitz gradients
with one constant independent of both tolerance and cell count. -/
theorem finite_valley_uniform_gradient_lipschitz :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ P : Parameters,
      LipschitzWith K (gradient (euclideanObjective P)) :=
  exists_euclideanObjective_gradient_lipschitz

/-- The actual prescribed successor is the first local minimum of the complete
negative-gradient ray, with every earlier nonnegative parameter excluded. -/
theorem finite_valley_first_local_ray_minimum (P : Parameters) {k : ℕ} (hk : k < P.count) :
    IsLocalMin (fun a => euclideanObjective P
      (nodePoint P k - a • gradient (euclideanObjective P) (nodePoint P k))) (Real.sqrt 2) ∧
      ∀ a ∈ Ico (0 : ℝ) (Real.sqrt 2), ¬ IsLocalMin (fun a => euclideanObjective P
        (nodePoint P k - a • gradient (euclideanObjective P) (nodePoint P k))) a :=
  firstLocalMin_negativeGradientRay P hk

end CartisGouldToint.AppendixB.Chapter02
