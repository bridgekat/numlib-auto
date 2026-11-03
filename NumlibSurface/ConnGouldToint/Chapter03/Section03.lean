import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Sequences and basic iterations

Section 3.3.1 of [conn2000trust] measures convergence rates by comparing errors to the limit.
The displayed Q-rate criteria on pp. 50–51 have an indexing error: the left-hand side must
be the error at the successor index, `‖u (k + 1) - x‖`. The reciprocal sequence below satisfies
the printed quadratic inequality despite failing the corrected one.
-/

open Filter Topology Asymptotics

namespace ConnGouldToint.Chapter03

variable {E : Type*} [NormedAddCommGroup E]

/-- Q-linear convergence, with the successor error bounded by a fixed strict contraction
factor times the current error. -/
def ConvergesQLinearly (u : ℕ → E) (x : E) : Prop :=
  Tendsto u atTop (𝓝 x) ∧ ∃ q ∈ Set.Ico (0 : ℝ) 1,
    ∀ᶠ k in atTop, ‖u (k + 1) - x‖ ≤ q * ‖u k - x‖

/-- Q-superlinear convergence, with the successor error little-o of the current error. -/
def ConvergesQSuperlinearly (u : ℕ → E) (x : E) : Prop :=
  Tendsto u atTop (𝓝 x) ∧ (fun k => u (k + 1) - x) =o[atTop] fun k => u k - x

/-- Q-quadratic convergence, with the successor error bounded by a fixed multiple of
the squared current error. -/
def ConvergesQQuadratically (u : ℕ → E) (x : E) : Prop :=
  Tendsto u atTop (𝓝 x) ∧ ∃ C : ℝ, ∀ᶠ k in atTop, ‖u (k + 1) - x‖ ≤ C * ‖u k - x‖ ^ 2

/-- R-quadratic convergence, with the error dominated by a Q-quadratically convergent
sequence of nonnegative real numbers. -/
def ConvergesRQuadratically (u : ℕ → E) (x : E) : Prop :=
  ∃ w : ℕ → ℝ, ConvergesQQuadratically w 0 ∧ ∀ k, ‖u k - x‖ ≤ w k

/-- The sequence `1 / (k + 1)` converges to zero and satisfies the printed Q-quadratic
inequality with constant one, although its convergence fails the corrected Q-quadratic test. -/
theorem reciprocal_succ_counterexample :
    let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    Tendsto u atTop (𝓝 0) ∧ (∀ k, ‖u (k + 1) - u k‖ ≤ ‖u k‖ ^ 2) ∧
      ¬ ConvergesQQuadratically u 0 := by
  dsimp only
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_, ?_⟩
  · intro k
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hmono : 1 / ((k : ℝ) + 1 + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 hmono),
      Real.norm_of_nonneg (by positivity)]
    have hcalc : -(1 / ((k : ℝ) + 1 + 1) - 1 / ((k : ℝ) + 1)) =
        1 / (((k : ℝ) + 1 + 1) * ((k : ℝ) + 1)) := by
      field_simp; ring
    rw [hcalc, div_pow, one_pow]
    gcongr; linarith
  · rintro ⟨-, C, hC⟩
    rw [eventually_atTop] at hC
    obtain ⟨N, hN⟩ := hC
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * C)
    let k := max N m
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h := hN k (le_max_left _ _)
    have hm' : (m : ℝ) ≤ k := by exact_mod_cast le_max_right N m
    simp only [sub_zero, Nat.cast_add, Nat.cast_one] at h
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), div_pow,
      one_pow, mul_one_div] at h
    have h' := (div_le_div_iff₀ (by positivity : (0 : ℝ) < k + 1 + 1)
      (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)).mp h
    have hC₀ : 0 ≤ C := by
      by_contra! hneg
      nlinarith [mul_neg_of_neg_of_pos hneg (by positivity : (0 : ℝ) < k + 1 + 1)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ k + 1 by positivity)
      (show (0 : ℝ) ≤ k + 1 - 2 * C by linarith), mul_nonneg hC₀ hk]

end ConnGouldToint.Chapter03
