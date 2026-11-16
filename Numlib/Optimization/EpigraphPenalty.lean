/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar epigraph penalty

The problem of minimizing a value $v \in \mathbb{R}$ can be written in epigraph form: minimize $t$
subject to $t \ge v$. The exact penalty of the constraint with parameter $\sigma$ is
$$P_\sigma(t) = t + \sigma \max\{v - t, 0\} = (1 - \sigma)\,t + \sigma \max\{t, v\}.$$
This file shows that $P_\sigma(t) \ge v$ for every $t$ when $\sigma \ge 1$, and that for
$\sigma > 1$ the bound $v$ is attained only at the tight epigraph variable $t = v$.

## Main definitions

* `Numlib.Optimization.epigraphPenalty`: the penalty $(1 - \sigma)\,t + \sigma \max\{t, v\}$.

## Main results

* `Numlib.Optimization.le_epigraphPenalty`: if $\sigma \ge 1$, then $v \le P_\sigma(t)$.
* `Numlib.Optimization.epigraphPenalty_eq_iff`: if $\sigma > 1$, then $P_\sigma(t) = v$ if and only
  if $t = v$.
-/

namespace Numlib.Optimization

/-- The **epigraph penalty** for the objective value $v$, with penalty parameter $\sigma$, at the
epigraph variable $t$:
$$P_\sigma(t) = (1 - \sigma)\,t + \sigma \max\{t, v\}.$$
This equals $t + \sigma \max\{v - t, 0\}$, the exact penalty of the constraint $t \ge v$. -/
def epigraphPenalty (v σ t : ℝ) : ℝ :=
  (1 - σ) * t + σ * max t v

/-- Let $v, \sigma, t \in \mathbb{R}$ with $\sigma \ge 1$. Then the epigraph penalty is bounded
below by the objective value:
$$v \le (1 - \sigma)\,t + \sigma \max\{t, v\}.$$
-/
theorem le_epigraphPenalty {v σ t : ℝ} (hσ : 1 ≤ σ) :
    v ≤ epigraphPenalty v σ t := by
  unfold epigraphPenalty
  rcases le_total v t with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (sub_nonneg.mpr h)]

/-- Let $v, \sigma, t \in \mathbb{R}$ with $\sigma > 1$. Then the epigraph penalty attains the
objective value only at the tight epigraph variable:
$$(1 - \sigma)\,t + \sigma \max\{t, v\} = v \iff t = v.$$
-/
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
