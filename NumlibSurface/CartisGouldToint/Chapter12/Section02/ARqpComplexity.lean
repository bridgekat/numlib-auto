import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpBounds
import Numlib.Optimization.HigherOrderApproximateRegularizationComplexity

/-!
# First true ARqp attainment on legal outer prefixes

The conditional companion makes operational prefix availability explicit. An unconditional
corrected inner-generated theorem still requires coupling actual returned traces to outer
transitions, including equality stops that may produce a new radius vector.
-/

noncomputable section
namespace CartisGouldToint.Chapter12.Section02
open Optimization HigherOrderApproximateRegularization
variable {n : ℕ} {P : Parameters} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The true actual compact-gap criteria agree with the source approximate minimizer
at every valid vector of radii. -/
theorem satisfiesCriteria_iff_isApproxOrderMinimizer
    {x : EuclideanSpace ℝ (Fin n)} {δ : ℕ → ℝ} (hδ : ValidRadii P δ) :
    SatisfiesCriteria P f x δ ↔ Section01.IsApproxOrderMinimizer f x P.q P.epsilon δ := by
  rw [satisfiesCriteria_iff_isApproxMinimizer hδ]
  constructor
  · intro h
    exact {
      h with
      order_pos := P.order_pos
      epsilon_le_one := fun j hj hjq => (P.epsilon_lt_one j hj hjq).le
      radius_le_one := fun j hj hjq => (hδ j hj hjq).2 }
  · exact fun h => h.toIsApproxMinimizer

/-- The canonical and source complexity exponents agree in both radius regimes. -/
@[simp] theorem complexityExponent_eq_arqpComplexityExponent (p q j : ℕ) :
    complexityExponent p q j = arqpComplexityExponent p q j := rfl

/-- The point sought by Theorem 12.2.14 allows a returned radius vector; the first regime
requires unit radii at every active order. -/
def ARqpTruePoint (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ δ, Section01.IsApproxOrderMinimizer f x P.q P.epsilon δ ∧
    (P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → δ j = 1)

/-- A true point is exactly a source approximate minimizer with the appropriate radii. -/
theorem arqpTruePoint_iff (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ARqpTruePoint P f x ↔
    ∃ δ, Section01.IsApproxOrderMinimizer f x P.q P.epsilon δ ∧
      (P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → δ j = 1) := Iff.rfl

/-- Conditional companion to Theorem 12.2.14. Actual legal prefix availability is exposed
as a premise. All-order Taylor comparison, parameter budgets, cache costs and both exact
tolerance exponent regimes are proved, rather than assumed as execution fields. The
corrected inner-generated theorem remains open until actual provenance discharges availability. -/
theorem theorem_12_2_14_of_legal_prefixes
    {x : EuclideanSpace ℝ (Fin n)} {σ κ low : ℝ} {δ : ℕ → ℝ} {L : ℕ → ℝ}
    (state : ℕ → OuterState (EuclideanSpace ℝ (Fin n)))
    (hf : LipschitzDerivativeFamily f P.p L) (hκ : 0 < κ) (hlow : ∀ y, low ≤ f y)
    (hvalid : ∀ k, ValidRadii P (state k).radii)
    (hstateUnit : ∀ k, P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → (state k).radii j = 1)
    (hprefix : ∀ N, (∀ k < N, ¬ARqpTruePoint P f (state k).point) →
      ∃ run : OuterExecution P f x σ δ N, run.state = state)
    (hunit : ∀ N (run : OuterExecution P f x σ δ N), run.state = state →
      ∀ k (hk : k < N), P.q ≤ 2 →
        ∀ j, 1 ≤ j → j ≤ P.q → (run.executedTrial k hk).trial.radii j = 1)
    (hlower : ∀ N (run : OuterExecution P f x σ δ N), run.state = state →
      ∀ k (hk : k < N), 2 < P.q →
        ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ (run.executedTrial k hk).trial.radii j) :
    let A := modelDecreaseConstant P.p P.q P.order_pos P.theta
      (L P.p + parameterUpper P σ (L P.p)) κ P.sigmaMin
    let T := toleranceMeasure P.p P.q P.order_pos P.epsilon
    ∃ K : ℕ, ARqpTruePoint P f (state K).point ∧
      (∀ k < K, ¬ARqpTruePoint P f (state k).point) ∧
      ∃ run : OuterExecution P f x σ δ K, run.state = state ∧
        (run.functionCount : ℝ) ≤ trialMultiplier P * ((f x - low) / (P.eta1 * (A * T))) +
          trialMultiplier P + parameterBudget P σ (L P.p) + 2 ∧
        (run.derivativeBatchCount : ℝ) ≤ (f x - low) / (P.eta1 * (A * T)) + 2 := by
  apply exists_first_true_attainment_of_legal_prefixes state (ARqpTruePoint P f)
    (hf.at_order (P.order_pos.trans P.order_le) le_rfl)
    (hf.one_le P.p (P.order_pos.trans P.order_le) le_rfl) hκ hlow
    _ hprefix hunit hlower
  intro k hc
  exact ⟨(state k).radii,
    (satisfiesCriteria_iff_isApproxOrderMinimizer (hvalid k)).mp hc, hstateUnit k⟩

end CartisGouldToint.Chapter12.Section02
