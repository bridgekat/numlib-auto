import Numlib.Optimization.MeasureDomination.HistoricalCounterexample
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The historical-measure obstruction in the Euclidean plane

Coordinate projection transports the actual quadratic, continuous measure and
all-success iterates to the textbook's Euclidean space, preserving every actual
objective value, historical minimum and stopping test.
-/

namespace MeasureDomination.HistoricalCounterexample
open Set Filter Topology

/-- The two actual Euclidean coordinates as a continuous linear map to a pair. -/
noncomputable def coordinatePair : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).prod
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2))

/-- The Euclidean vector with the specified first and second coordinates. -/
noncomputable def fromPair (z : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![z.1, z.2]

/-- Projection recovers both coordinates of the specified Euclidean vector. -/
@[simp] theorem coordinatePair_fromPair (z : ℝ × ℝ) : coordinatePair (fromPair z) = z := by
  ext <;> rfl

/-- The complete obstruction with the textbook's Euclidean ambient norm. The
actual objective is the square of coordinate one; the measure is the maximum
of its absolute value and the absolute product of coordinates zero and one. -/
theorem euclidean_counterexample :
    ∃ (f ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
      (x : ℕ → EuclideanSpace ℝ (Fin 2)),
      ContDiff ℝ ⊤ f ∧ Continuous ψ ∧ (∀ z, ψ z = 0 ↔ f z = 0) ∧
      Dominated f ψ 0 2 1 ∧ TRRun f ψ x Set.univ 4 (1 / 64) 1 0 ∧
      gap f 0 (x 0) = 1 ∧ (∀ n, 0 < ψ (x n)) ∧
      Tendsto (fun n => gap f 0 (x n)) atTop (nhds 0) ∧
      Tendsto (pastMeasure ψ x) atTop (nhds 0) ∧
      ¬Tendsto (fun n => ψ (x (successIndex Set.univ n))) atTop (nhds 0) := by
  let f : EuclideanSpace ℝ (Fin 2) → ℝ := objective ∘ coordinatePair
  let ψ : EuclideanSpace ℝ (Fin 2) → ℝ := measure ∘ coordinatePair
  let x : ℕ → EuclideanSpace ℝ (Fin 2) := fromPair ∘ iterate
  have hf (n : ℕ) : f (x n) = objective (iterate n) := by simp only [f, x,
    Function.comp_apply, coordinatePair_fromPair]
  have hψ (n : ℕ) : ψ (x n) = measure (iterate n) := by simp only [ψ, x,
    Function.comp_apply, coordinatePair_fromPair]
  have hp (n : ℕ) : pastMeasure ψ x n = pastMeasure measure iterate n := by
    simp only [pastMeasure, hψ]
  have hdom : Dominated f ψ 0 2 1 := by
    refine ⟨⟨⟨fromPair (0, 0), ?_⟩, ?_⟩,
      fun z => dominated.measure_nonneg (coordinatePair z), dominated.level_ge_one,
      dominated.coefficient_pos, fun z => dominated.domination (coordinatePair z)⟩
    · simp only [f, Function.comp_apply, coordinatePair_fromPair, objective]
      norm_num
    · intro y hy
      obtain ⟨z, rfl⟩ := hy
      exact dominated.minimum.2 (Set.mem_range_self (coordinatePair z))
  have hr : TRRun f ψ x Set.univ 4 (1 / 64) 1 0 := by
    refine ⟨run.exponent_ge_one, run.coefficient_pos, run.infinite_success,
      fun _ hn => (hn trivial).elim, ?_, run.density_factor, run.density_additive,
      run.density, ?_⟩
    · intro n _
      simpa only [hp, hf] using historical_decrease n
    · intro n hn
      rw [hψ] at hn
      exact ((measure_iterate_pos n).ne' hn).elim
  refine ⟨f, ψ, x, objective_contDiff.comp coordinatePair.contDiff,
    measure_continuous.comp coordinatePair.continuous, fun z => measure_zero_iff _, hdom,
    hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gap, hf]
    norm_num [objective, iterate]
  · intro n
    simpa only [hψ] using measure_iterate_pos n
  · simpa only [gap, hf] using gap_tendsto_zero
  · rw [show pastMeasure ψ x = pastMeasure measure iterate from funext hp]
    exact pastMeasure_tendsto_zero
  · simpa only [hψ] using not_tendsto_successful_measure

end MeasureDomination.HistoricalCounterexample
