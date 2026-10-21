import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# First-order accuracy and the objective assumptions

The assumptions f.Bb and f.gL and the approximate first-order minimizer of §2.1.
The underlying space is the book's Euclidean `ℝⁿ`. A small gradient is an approximate necessary
optimality condition; it is not asserted to imply local minimality.
-/

noncomputable section

namespace CartisGouldToint.Chapter02.Section01

variable {n : ℕ}

/-- Assumption f.Bb: the objective is bounded below on the whole space. -/
def assumption_f_Bb (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  BddBelow (Set.range f)

/-- A lower bound witnesses f.Bb precisely when it bounds every objective value. -/
theorem assumption_f_Bb_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    assumption_f_Bb f ↔ ∃ low : ℝ, ∀ x, low ≤ f x := by
  simp [assumption_f_Bb, BddBelow, Set.Nonempty, lowerBounds]

/-- Assumption f.gL: a continuously differentiable objective with a globally Lipschitz gradient,
using the book's normalization `1 ≤ L`. -/
def assumption_f_gL (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ 1 ≤ L ∧ ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- f.gL provides the genuine continuous linear derivative represented by the gradient. -/
theorem assumption_f_gL.hasFDerivAt {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (h : assumption_f_gL f L) (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt f (innerSL ℝ (gradient f x)) x :=
  (h.1.differentiable_one x).hasGradientAt.hasFDerivAt

/-- f.gL provides a positive Lipschitz upper bound. -/
theorem assumption_f_gL.constant_pos {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (h : assumption_f_gL f L) : 0 < L := lt_of_lt_of_le zero_lt_one h.2.1

/-- The normalized Lipschitz estimate in f.gL. -/
theorem assumption_f_gL.lipschitz {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (h : assumption_f_gL f L) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := h.2.2 x y

/-- Equation (2.1.2): the first-order stopping test at tolerance `ε`. -/
def approximateFirstOrderMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop := ‖gradient f x‖ ≤ ε

/-- The first-order accuracy predicate is exactly the book's gradient-norm test. -/
@[simp] theorem approximateFirstOrderMinimizer_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {ε : ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    approximateFirstOrderMinimizer f ε x ↔ ‖gradient f x‖ ≤ ε := Iff.rfl

end CartisGouldToint.Chapter02.Section01
