import Numlib.Optimization.SafeguardedSecularSearch

/-!
# A complete nonterminating search at a root endpoint

A non-strict initial bracket and a nonempty desired region permit a legal midpoint run
that approaches its lower endpoint forever. Finite-entry guarantees must account for this
endpoint case, as opposed to relying only on geometric width convergence.
-/

noncomputable section
namespace Optimization.SafeguardedSecularSearch

/-- Fixed midpoint safeguards used by the explicit endpoint example. -/
def halfParameters : Parameters :=
  ⟨1 / 2, 1 / 2, by norm_num, le_rfl, by norm_num⟩

/-- The midpoint choice does not request an auxiliary spectral estimate. -/
def halfChoice : Choice := ⟨1 / 2, 1 / 2, false, false, none⟩

/-- A legal bracket with initial lower endpoint exactly equal to the root. -/
def endpointState (k : ℕ) : State :=
  ⟨1, 1 + (1 / 2 : ℝ) ^ k, 1 + (1 / 2 : ℝ) ^ (k + 1)⟩

/-- The actual lower endpoint of every example state. -/
@[simp] theorem endpointState_lower (k : ℕ) : (endpointState k).lower = 1 := rfl

/-- The actual upper endpoint of every example state. -/
@[simp] theorem endpointState_upper (k : ℕ) :
    (endpointState k).upper = 1 + (1 / 2 : ℝ) ^ k := rfl

/-- The actual trial in every example state. -/
@[simp] theorem endpointState_candidate (k : ℕ) :
    (endpointState k).candidate = 1 + (1 / 2 : ℝ) ^ (k + 1) := rfl

/-- Every trial in the endpoint example remains strictly above the root. -/
theorem endpointState_greater (k : ℕ) :
    cutoffClassifier 0 1 (endpointState k).candidate = .greater := by
  have hp : 0 < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  have hpos : ¬1 + (1 / 2 : ℝ) ^ (k + 1) ≤ 0 := by linarith
  have hroot : ¬1 + (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by linarith
  change (if 1 + (1 / 2 : ℝ) ^ (k + 1) ≤ 0 then Region.negative
    else if 1 + (1 / 2 : ℝ) ^ (k + 1) ≤ 1 then Region.lower else Region.greater) = Region.greater
  rw [ite_eq_right hpos, ite_eq_right hroot]

/-- The shrinking endpoint brackets obey every midpoint-search transition indefinitely. -/
theorem endpointState_isRun (pole : ℝ) :
    IsRun halfParameters (cutoffClassifier 0 1) pole 1 endpointState (fun _ => halfChoice) := by
  have hpow (k : ℕ) : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ k := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]
  constructor
  · norm_num [Brackets, endpointState]
  · intro k _
    simp [Choice.Legal, halfChoice, halfParameters]
  · intro k _ a ha
    cases ha
  · intro k _
    rw [endpointState_greater k]
    simp [endpointState, halfChoice]
  · intro k _
    rw [endpointState_greater k]
    simp only [endpointState, updateBounds_upper, halfChoice, reduceIte]
    rw [min_eq_right (by linarith [hpow k] :
      1 + (1 / 2 : ℝ) ^ (k + 1) ≤ 1 + (1 / 2 : ℝ) ^ k)]
  · intro k _
    rw [endpointState_greater k]
    simp only [halfChoice, updateBounds_lower, updateBounds_upper, reduceIte, improveLower_none,
      trial_false]
    have hm : min (1 + (1 / 2 : ℝ) ^ k) (1 + (1 / 2 : ℝ) ^ (k + 1)) =
        1 + (1 / 2 : ℝ) ^ (k + 1) := min_eq_right (by linarith [hpow k])
    change (endpointState (k + 1)).candidate ∈ Set.Icc
      (max 0 (1 + 1 / 2 * (min (1 + (1 / 2 : ℝ) ^ k)
        (1 + (1 / 2 : ℝ) ^ (k + 1)) - 1)))
      (max 0 (1 + 1 / 2 * (min (1 + (1 / 2 : ℝ) ^ k)
        (1 + (1 / 2 : ℝ) ^ (k + 1)) - 1)))
    have hnonneg : 0 ≤ 1 + 1 / 2 * (1 + (1 / 2 : ℝ) ^ (k + 1) - 1) := by
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (k + 1)]
    rw [hm, max_eq_right hnonneg]
    have he : (endpointState (k + 1)).candidate =
        1 + 1 / 2 * (1 + (1 / 2 : ℝ) ^ (k + 1) - 1) := by
      dsimp [endpointState]
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
      ring
    exact ⟨he.ge, he.le⟩

/-- A nonempty lower region and a valid non-strict initial bracket do not alone imply entry.
The failure is a complete infinite legal midpoint run, not an isolated trial. -/
theorem endpoint_nontermination :
    (∃ a, cutoffClassifier 0 1 a = .lower) ∧
      IsRun halfParameters (cutoffClassifier 0 1) 0 1 endpointState (fun _ => halfChoice) ∧
      ∀ k, cutoffClassifier 0 1 (endpointState k).candidate ≠ .lower := by
  refine ⟨⟨1, by norm_num [cutoffClassifier]⟩, endpointState_isRun 0, ?_⟩
  intro k
  rw [endpointState_greater]
  decide

end Optimization.SafeguardedSecularSearch
