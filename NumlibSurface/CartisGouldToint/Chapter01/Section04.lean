import Numlib.Analysis.Calculus.RegularityRequirement
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chapter 1, Section 4: assumption names

The source gives a naming convention, not a conjunction imposed on every problem. Each
mnemonic denotes a concrete regularity or boundedness predicate. An omitted location means
the whole Euclidean domain; a set suffix is interpreted on an explicitly open neighborhood.
-/

namespace CartisGouldToint.Chapter01.Section04

/-- Interpret an objective-assumption mnemonic on the whole Euclidean domain.
Use `.smooth p` for continuous differentiability, `.derivativeLipschitz q p` for the stated
inclusive derivative range, and `.boundedBelow` for the genuine value lower bound. -/
def objectiveAssumptions {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (name : FunctionRegularity.Requirement) : Prop := FunctionRegularity.Globally name f

/-- A location suffix means the named requirement holds on an open neighborhood of that set. -/
def objectiveAssumptionsNear {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (name : FunctionRegularity.Requirement) (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  FunctionRegularity.Near name f S

/-- The mnemonic f.Cp is standard global continuous differentiability. -/
@[simp] theorem objectiveAssumptions_smooth_iff {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) :
    objectiveAssumptions f (.smooth p) ↔ ContDiff ℝ p f :=
  FunctionRegularity.globally_smooth_iff f p

/-- The mnemonic f.Bb is a genuine uniform lower bound on objective values. -/
@[simp] theorem objectiveAssumptions_boundedBelow_iff {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    objectiveAssumptions f .boundedBelow ↔ ∃ b : ℝ, ∀ x, b ≤ f x := by
  simp [objectiveAssumptions, FunctionRegularity.Globally]

/-- The mnemonic f.DqpL states Lipschitz continuity of every actual derivative in the range. -/
@[simp] theorem objectiveAssumptions_derivativeLipschitz_iff {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (q p : ℕ) :
    objectiveAssumptions f (.derivativeLipschitz q p) ↔ ContDiff ℝ p f ∧
      ∀ j, q ≤ j → j ≤ p → ∃ L : NNReal, LipschitzWith L (iteratedFDeriv ℝ j f) := by
  simp [objectiveAssumptions, FunctionRegularity.Globally, lipschitzOnWith_univ, contDiffOn_univ]

/-- The whole-domain location suffix agrees with omitting the location. -/
@[simp] theorem objectiveAssumptionsNear_univ_iff {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (name : FunctionRegularity.Requirement) :
    objectiveAssumptionsNear f name Set.univ ↔ objectiveAssumptions f name :=
  FunctionRegularity.near_univ_iff name f

end CartisGouldToint.Chapter01.Section04
