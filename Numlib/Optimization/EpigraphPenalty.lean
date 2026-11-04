/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar epigraph penalty

Minimizing the exact penalty over the epigraph variable recovers the original objective value
and uniquely determines the epigraph variable when the penalty parameter exceeds one.
-/

namespace Numlib.Optimization

/-- The max-based penalty in the scalar epigraph variable `t` for objective value `v`. -/
def epigraphPenalty (v σ t : ℝ) : ℝ :=
  (1 - σ) * t + σ * max t v

/-- The penalty is bounded below by the original objective value. -/
theorem le_epigraphPenalty {v σ t : ℝ} (hσ : 1 ≤ σ) :
    v ≤ epigraphPenalty v σ t := by
  unfold epigraphPenalty
  rcases le_total v t with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (sub_nonneg.mpr h)]

/-- For a parameter strictly above one, only the tight epigraph variable attains the bound. -/
theorem epigraphPenalty_eq_iff {v σ t : ℝ} (hσ : 1 < σ) :
    epigraphPenalty v σ t = v ↔ t = v := by
  constructor
  · intro heq
    unfold epigraphPenalty at heq
    rcases lt_trichotomy t v with h | h | h
    · rw [max_eq_right h.le] at heq
      nlinarith [mul_pos (sub_pos.mpr hσ) (sub_pos.mpr h)]
    · exact h
    · rw [max_eq_left h.le] at heq
      linarith
  · rintro rfl
    unfold epigraphPenalty
    rw [max_self]
    ring

end Numlib.Optimization
