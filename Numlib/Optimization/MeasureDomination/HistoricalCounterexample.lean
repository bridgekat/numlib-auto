import Numlib.Optimization.MeasureDomination.TrustRegion

/-!
# A continuous current-measure obstruction for historical trust-region decrease

A smooth quadratic objective has a continuous nonnegative measure vanishing
exactly on its global minima. Every trial is accepted, and the actual historical
measure gives the required fourth-power decrease. Nevertheless the current
measure equals one on every even iteration.
-/

namespace MeasureDomination.HistoricalCounterexample
open Set Filter Topology

/-- A genuine smooth quadratic objective on the real plane. -/
noncomputable def objective (z : ℝ × ℝ) : ℝ := z.2 ^ 2

/-- The continuous optimality measure dominates the absolute second coordinate
and vanishes precisely at global minimizers of the quadratic. -/
noncomputable def measure (z : ℝ × ℝ) : ℝ := max |z.2| |z.1 * z.2|

/-- Actual iterates alternate a growing first coordinate with zero while the
objective coordinate decreases geometrically at every accepted iteration. -/
noncomputable def iterate (n : ℕ) : ℝ × ℝ :=
  (if Even n then (2 : ℝ) ^ n else 0, (1 / 2 : ℝ) ^ n)

/-- The objective is smooth to every order. -/
theorem objective_contDiff : ContDiff ℝ ⊤ objective := contDiff_snd.pow 2

/-- The measure is continuous on the whole plane. -/
theorem measure_continuous : Continuous measure :=
  continuous_snd.abs.max (continuous_fst.mul continuous_snd).abs

/-- The actual measure is zero exactly on the set of global minimizers. -/
theorem measure_zero_iff (z : ℝ × ℝ) : measure z = 0 ↔ objective z = 0 := by
  have hn : 0 ≤ measure z := (abs_nonneg z.2).trans (le_max_left _ _)
  constructor
  · intro hz
    have hh : |z.2| ≤ measure z := le_max_left _ _
    rw [hz] at hh
    have he := abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    simp only [objective, he, zero_pow (by decide : 2 ≠ 0)]
  · intro hz
    have he : z.2 = 0 := eq_zero_of_pow_eq_zero (by simpa only [objective] using hz)
    simp only [measure, he, abs_zero, mul_zero, max_self]

/-- Global measure domination has level two and coefficient one. -/
theorem dominated : Dominated objective measure 0 2 1 := by
  refine ⟨⟨⟨(0, 0), by simp [objective]⟩, ?_⟩, ?_, by norm_num, zero_lt_one, ?_⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact sq_nonneg _
  · intro z
    exact (abs_nonneg z.2).trans (le_max_left _ _)
  · intro z
    have hm : |z.2| ≤ measure z := le_max_left _ _
    have hp := pow_le_pow_left₀ (abs_nonneg z.2) hm 2
    simpa only [objective, sub_zero, one_mul, Real.rpow_ofNat, sq_abs] using hp

/-- Even iterates have measure one and odd iterates have the geometric measure. -/
theorem measure_iterate (n : ℕ) :
    measure (iterate n) = if Even n then 1 else (1 / 2 : ℝ) ^ n := by
  have hq : 0 ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) _
  have hq1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [←mul_pow]; norm_num
  unfold measure iterate
  split_ifs with hn
  · simp only [hp, abs_of_nonneg hq, abs_one, max_eq_right hq1]
  · simp only [zero_mul, abs_zero, abs_of_nonneg hq, max_eq_left hq]

/-- Every actual measure remains positive, so none of the primitive stopping
rules is invoked in this continued execution. -/
theorem measure_iterate_pos (n : ℕ) : 0 < measure (iterate n) := by
  rw [measure_iterate]
  split_ifs <;> positivity

/-- The true historical minimum is small even at the intervening large-measure iterates. -/
theorem pastMeasure_le_twice (n : ℕ) :
    pastMeasure measure iterate n ≤ 2 * (1 / 2 : ℝ) ^ n := by
  by_cases he : Even n
  · by_cases hz : n = 0
    · subst n
      have hh := pastMeasure_le measure iterate (k := 0) (i := 0) le_rfl
      rw [measure_iterate] at hh
      norm_num at hh ⊢
      exact hh.trans (by norm_num)
    · have ho : ¬Even (n - 1) := by simp only [Nat.even_iff] at he ⊢; omega
      have hh := pastMeasure_le measure iterate (k := n) (i := n - 1) (by omega)
      rw [measure_iterate, ite_eq_right ho] at hh
      have heq : (1 / 2 : ℝ) ^ (n - 1) = 2 * (1 / 2 : ℝ) ^ n := by
        conv_rhs => rw [show n = n - 1 + 1 by omega, pow_succ]
        ring
      exact hh.trans heq.le
  · have hh := pastMeasure_le measure iterate (k := n) (i := n) le_rfl
    rw [measure_iterate, ite_eq_right he] at hh
    have hp : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    exact hh.trans (by linarith)

/-- Every actual trial satisfies the precise historical fourth-power decrease. -/
theorem historical_decrease (n : ℕ) :
    (1 / 64 : ℝ) * pastMeasure measure iterate n ^ (4 : ℝ) ≤
      objective (iterate n) - objective (iterate (n + 1)) := by
  let q := (1 / 2 : ℝ) ^ n
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hmin : 0 ≤ pastMeasure measure iterate n :=
    le_pastMeasure (fun _ _ => (measure_iterate_pos _).le)
  have hp := pow_le_pow_left₀ hmin (pastMeasure_le_twice n) 4
  have hsq : q ^ 2 ≤ 1 := pow_le_one₀ hq hq1
  have hfour := mul_le_mul_of_nonneg_left hsq (sq_nonneg q)
  have hdrop : objective (iterate n) - objective (iterate (n + 1)) = 3 / 4 * q ^ 2 := by
    simp only [objective, iterate, pow_succ]
    dsimp only [q]
    ring
  rw [Real.rpow_ofNat, hdrop]
  change pastMeasure measure iterate n ^ 4 ≤ (2 * q) ^ 4 at hp
  nlinarith

/-- All trials are genuine successes, with density one and the source's legal
parameters. The zero-measure termination rule is retained. -/
theorem run : TRRun objective measure iterate Set.univ 4 (1 / 64) 1 0 := by
  refine ⟨by norm_num, by norm_num, Set.infinite_univ, fun _ hn => (hn trivial).elim,
    fun n _ => historical_decrease n, le_rfl, le_rfl, ?_, ?_⟩
  · intro N
    simp only [EvaluationComplexity.successfulIterations, Set.mem_univ,
      Finset.filter_true, Finset.card_range, one_mul, add_zero]
    exact le_rfl
  · intro n hn
    exact ((measure_iterate_pos n).ne' hn).elim

/-- The actual current optimality measures do not converge to zero along the
all-success execution, despite continuous measure and smooth objective. -/
theorem not_tendsto_measure :
    ¬Tendsto (fun n => measure (iterate n)) atTop (nhds 0) := by
  intro hh
  have hm : StrictMono (fun n : ℕ => 2 * n) := by
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_left hab (by norm_num)
  have hs := hh.comp hm.tendsto_atTop
  have he (n : ℕ) : measure (iterate (2 * n)) = 1 := by
    rw [measure_iterate, ite_eq_left (even_two_mul n)]
  change Tendsto (fun n => measure (iterate (2 * n))) atTop (nhds 0) at hs
  simp only [he] at hs
  have hz : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hs
  norm_num at hz

/-- Every successful label is an actual iteration in this all-success example. -/
theorem not_tendsto_successful_measure :
    ¬Tendsto (fun n => measure (iterate (successIndex Set.univ n))) atTop (nhds 0) := by
  simpa only [successIndex, Set.mem_univ, Nat.nth_true] using not_tendsto_measure

/-- The actual objective gaps converge to zero along the same execution. -/
theorem gap_tendsto_zero : Tendsto (fun n => gap objective 0 (iterate n)) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [gap, objective, iterate, sub_zero, zero_pow (by decide : 2 ≠ 0)] using ht.pow 2

/-- The actual historical measures converge to zero although current measures do not. -/
theorem pastMeasure_tendsto_zero :
    Tendsto (pastMeasure measure iterate) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply squeeze_zero (fun n => le_pastMeasure (fun _ _ => (measure_iterate_pos _).le))
    pastMeasure_le_twice
  simpa only [mul_zero] using tendsto_const_nhds.mul ht

end MeasureDomination.HistoricalCounterexample
