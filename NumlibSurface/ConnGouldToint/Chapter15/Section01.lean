/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas

/-! # The nonlinear programs underlying SQP -/

namespace ConnGouldToint.Chapter15

variable {E ι κ : Type*}

/-- The feasible set for the mixed equality and inequality program (15.1.1).
The two constraint families are indexed separately. -/
def nonlinearFeasibleSet (cEq : ι → E → ℝ) (cIneq : κ → E → ℝ) : Set E :=
  {x | (∀ i, cEq i x = 0) ∧ ∀ j, 0 ≤ cIneq j x}

/-- The solution condition for the mixed program (15.1.1). -/
def IsMixedNonlinearSolution (f : E → ℝ) (cEq : ι → E → ℝ)
    (cIneq : κ → E → ℝ) (x : E) : Prop :=
  x ∈ nonlinearFeasibleSet cEq cIneq ∧ IsMinOn f (nonlinearFeasibleSet cEq cIneq) x

/-- The solution condition for the equality-only program (15.1.2). -/
def IsEqualityNonlinearSolution (f : E → ℝ) (cEq : ι → E → ℝ) (x : E) : Prop :=
  (∀ i, cEq i x = 0) ∧ IsMinOn f {y | ∀ i, cEq i y = 0} x

/-- The equality-only program is the mixed program with an empty inequality family. -/
theorem isMixedNonlinearSolution_iff_isEqualityNonlinearSolution [IsEmpty κ]
    (f : E → ℝ) (cEq : ι → E → ℝ) (cIneq : κ → E → ℝ) (x : E) :
    IsMixedNonlinearSolution f cEq cIneq x ↔ IsEqualityNonlinearSolution f cEq x := by
  have h : nonlinearFeasibleSet cEq cIneq = {y | ∀ i, cEq i y = 0} := by
    ext y
    simp [nonlinearFeasibleSet]
  simp [IsMixedNonlinearSolution, IsEqualityNonlinearSolution, h]

/-- Continuous constraints make the feasible set of (15.1.1) closed. -/
theorem isClosed_nonlinearFeasibleSet [TopologicalSpace E]
    {cEq : ι → E → ℝ} {cIneq : κ → E → ℝ}
    (hEq : ∀ i, Continuous (cEq i)) (hIneq : ∀ j, Continuous (cIneq j)) :
    IsClosed (nonlinearFeasibleSet cEq cIneq) := by
  have h : nonlinearFeasibleSet cEq cIneq =
      (⋂ i, {x | cEq i x = 0}) ∩ (⋂ j, {x | 0 ≤ cIneq j x}) := by
    ext x
    simp [nonlinearFeasibleSet]
  rw [h]
  exact (isClosed_iInter fun i ↦ isClosed_eq (hEq i) continuous_const).inter
    (isClosed_iInter fun j ↦ isClosed_le continuous_const (hIneq j))

end ConnGouldToint.Chapter15
