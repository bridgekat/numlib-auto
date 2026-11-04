/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Motivation and basic notation for penalty methods -/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter14

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- AW.1. The objective and constraint map are twice continuously differentiable. -/
def AW1 (f : E → ℝ) (c : E → F) : Prop :=
  ContDiff ℝ 2 f ∧ ContDiff ℝ 2 c

/-- The equality-constrained Lagrangian in (14.1.4). -/
def lagrangian (f : E → ℝ) (c : E → F) (y : F) (x : E) : ℝ :=
  f x - ⟪y, c x⟫

end ConnGouldToint.Chapter14
