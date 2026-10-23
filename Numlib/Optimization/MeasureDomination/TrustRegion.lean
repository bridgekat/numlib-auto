import Numlib.Optimization.MeasureDomination.Regularization
import Numlib.Optimization.TrustRegion.FirstOrder

/-!
# Trust-region decrease from a historical optimality measure

The actual historical minimum controls accepted decrease. Successful labels may
continue after termination only at the unchanged terminal point. The primitive
rules imply an explicit current-gap recurrence, but do not identify the current
measure with its historical minimum.
-/

namespace MeasureDomination
open Set Filter Topology
variable {E : Type*}

/-- The actual minimum of the optimality measure on the inclusive iterate prefix. -/
noncomputable def pastMeasure (ψ : E → ℝ) (x : ℕ → E) (k : ℕ) : ℝ :=
  FirstOrderTrustRegion.prefixMinimum (fun i => ψ (x i)) k

/-- The historical minimum is no greater than any actual earlier measure. -/
theorem pastMeasure_le (ψ : E → ℝ) (x : ℕ → E) {k i : ℕ} (hi : i ≤ k) :
    pastMeasure ψ x k ≤ ψ (x i) := FirstOrderTrustRegion.prefixMinimum_le _ hi

/-- A common lower bound for actual earlier measures bounds their historical minimum. -/
theorem le_pastMeasure {ψ : E → ℝ} {x : ℕ → E} {k : ℕ} {m : ℝ}
    (hm : ∀ i ≤ k, m ≤ ψ (x i)) : m ≤ pastMeasure ψ x k :=
  FirstOrderTrustRegion.le_prefixMinimum hm

/-- The finite historical minimum is attained at an actual iterate. -/
theorem pastMeasure_attains (ψ : E → ℝ) (x : ℕ → E) (k : ℕ) :
    ∃ i ≤ k, pastMeasure ψ x k = ψ (x i) := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf'
    (show (Finset.range (k + 1)).Nonempty from ⟨0, by simp⟩) (fun i => ψ (x i))
  exact ⟨i, by have := Finset.mem_range.mp hi; omega, he⟩

/-- The abstract TR class has actual historical-measure decrease, unchanged
rejected points, successful-prefix density and a constant continuation after a
zero-measure stop. No convergence or evaluation bound is an algorithm field. -/
structure TRRun (f ψ : E → ℝ) (x : ℕ → E) (S : Set ℕ) (ν κ κR κA : ℝ) : Prop where
  exponent_ge_one : 1 ≤ ν
  coefficient_pos : 0 < κ
  infinite_success : S.Infinite
  rejected : ∀ k, k ∉ S → x (k + 1) = x k
  decrease : ∀ k ∈ S, κ * pastMeasure ψ x k ^ ν ≤ f (x k) - f (x (k + 1))
  density_factor : 1 ≤ κR
  density_additive : 0 ≤ κA
  density : ∀ N : ℕ, (N : ℝ) ≤ κR *
    (EvaluationComplexity.successfulIterations S N).card + κA
  stopped_point : ∀ k, ψ (x k) = 0 → x (k + 1) = x k

variable {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ} {x : ℕ → E} {S : Set ℕ}

/-- The actual objective gap is nonincreasing under both accepted and rejected
historical-measure steps. -/
theorem TRRun.gap_antitone (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) : Antitone (fun k => gap f fstar (x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hk : k ∈ S
  · have hmin : 0 ≤ pastMeasure ψ x k := le_pastMeasure (fun _ _ => hd.measure_nonneg _)
    have hp := mul_nonneg hr.coefficient_pos.le (Real.rpow_nonneg hmin ν)
    have hh := hr.decrease k hk
    dsimp [gap]
    linarith
  · rw [hr.rejected k hk]

/-- Domination at the actual historical minimizer and monotonicity give the
explicit current-gap power decrease at every accepted iteration. -/
theorem TRRun.explicit_decrease (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {k : ℕ} (hk : k ∈ S) :
    gap f fstar (x (k + 1)) + κν / κψ ^ (ν / μ) *
      gap f fstar (x k) ^ (ν / μ) ≤ gap f fstar (x k) := by
  obtain ⟨i, hi, hmin⟩ := pastMeasure_attains ψ x k
  have ht : 0 ≤ ν / μ :=
    (div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
      (zero_lt_one.trans_le hd.level_ge_one)).le
  have hc : 0 ≤ κν / κψ ^ (ν / μ) := by
    exact div_nonneg hr.coefficient_pos.le (Real.rpow_nonneg hd.coefficient_pos.le _)
  have hp := Real.rpow_le_rpow (hd.gap_nonneg _) ((hr.gap_antitone hd) hi) ht
  have hb := (mul_le_mul_of_nonneg_left hp hc).trans
    (hd.power_gap_le (zero_lt_one.trans_le hr.exponent_ge_one) hr.coefficient_pos (x i))
  rw [←hmin] at hb
  have hh := hr.decrease k hk
  dsimp [gap] at *
  linarith

end MeasureDomination
