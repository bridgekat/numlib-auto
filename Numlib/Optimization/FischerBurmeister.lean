/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# The Fischer–Burmeister complementarity residual

The Fischer–Burmeister function $\varphi(a, b) = \sqrt{a^2 + b^2} - a - b$ turns the scalar
complementarity condition $a \ge 0$, $b \ge 0$, $ab = 0$ into the single equation
$\varphi(a, b) = 0$.

## Main definitions

* `Numlib.Optimization.fischerBurmeister`: the residual $\sqrt{a^2 + b^2} - a - b$.

## Main results

* `Numlib.Optimization.fischerBurmeister_eq_zero_iff`: $\varphi(a, b) = 0$ if and only if $a \ge 0$,
  $b \ge 0$ and $ab = 0$.
-/

namespace Numlib.Optimization

/-- The **Fischer–Burmeister residual** of $a, b \in \mathbb{R}$:
$$\varphi(a, b) = \sqrt{a^2 + b^2} - a - b.$$
-/
noncomputable def fischerBurmeister (a b : ℝ) : ℝ :=
  √(a ^ 2 + b ^ 2) - a - b

/-- For $a, b \in \mathbb{R}$, the Fischer–Burmeister residual vanishes exactly at the solutions of
the scalar complementarity problem:
$$\sqrt{a^2 + b^2} - a - b = 0 \iff a \ge 0,\ b \ge 0 \text{ and } ab = 0.$$
-/
theorem fischerBurmeister_eq_zero_iff {a b : ℝ} :
    fischerBurmeister a b = 0 ↔ 0 ≤ a ∧ 0 ≤ b ∧ a * b = 0 := by
  unfold fischerBurmeister
  constructor
  · intro h
    have hs : √(a ^ 2 + b ^ 2) = a + b := by linarith
    have hsum : 0 ≤ a + b := by
      rw [← hs]
      exact Real.sqrt_nonneg _
    have hsq := Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
    rw [hs] at hsq
    have hab : a * b = 0 := by nlinarith
    rcases mul_eq_zero.mp hab with ha | hb
    · exact ⟨by simp [ha], by simpa [ha] using hsum, hab⟩
    · exact ⟨by simpa [hb] using hsum, by simp [hb], hab⟩
  · rintro ⟨ha, hb, hab⟩
    rcases mul_eq_zero.mp hab with h | h
    · simp [h, Real.sqrt_sq hb]
    · simp [h, Real.sqrt_sq ha]

end Numlib.Optimization
