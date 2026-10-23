import Numlib.Optimization.MeasureDomination.TrustRegionRates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A false unit threshold in historical trust-region convergence

A smooth scalar quadratic reaches its exact minimizer after one accepted step.
Its final positive gap is strictly above the genuine threshold, yet below one.
-/

namespace MeasureDomination.ThresholdCounterexample

/-- A smooth quadratic on the one-dimensional Euclidean space. -/
noncomputable def objective (z : EuclideanSpace ℝ (Fin 1)) : ℝ := z 0 ^ 2

/-- Absolute coordinate is an exact quadratic domination measure. -/
noncomputable def measure (z : EuclideanSpace ℝ (Fin 1)) : ℝ := |z 0|

/-- A genuine accepted step from three quarters to the exact minimum. -/
noncomputable def iterate (k : ℕ) : EuclideanSpace ℝ (Fin 1) :=
  if k = 0 then WithLp.toLp 2 (fun _ => 3 / 4) else 0

/-- The objective has derivatives of every order. -/
theorem objective_contDiff : ContDiff ℝ ⊤ objective := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff.pow 2

/-- Exact domination has level two and coefficient one. -/
theorem dominated : Dominated objective measure 0 2 1 := by
  refine ⟨⟨⟨0, by simp [objective]⟩, ?_⟩, fun z => abs_nonneg _, by norm_num,
    zero_lt_one, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact sq_nonneg _
  · intro z
    simp only [objective, measure, sub_zero, one_mul, Real.rpow_ofNat, sq_abs, le_refl]

/-- The historical measure yields the required actual accepted decrease. -/
theorem run : TRRun objective measure iterate Set.univ 1 (1 / 2) 1 0 := by
  refine ⟨le_rfl, by norm_num, Set.infinite_univ, fun _ hn => (hn trivial).elim,
    ?_, le_rfl, le_rfl, ?_, ?_⟩
  · intro k _
    have hh := pastMeasure_le measure iterate (k := k) (i := k) le_rfl
    rw [Real.rpow_one]
    by_cases hk : k = 0
    · subst k
      norm_num [measure, iterate] at hh
      norm_num [objective, iterate]
      linarith
    · have hh0 : pastMeasure measure iterate k ≤ 0 := by
        simpa [measure, iterate, hk] using hh
      simpa [objective, iterate, hk, Nat.succ_ne_zero] using
        mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1 / 2) hh0
  · intro N
    simp only [EvaluationComplexity.successfulIterations, Set.mem_univ,
      Finset.filter_true, Finset.card_range, one_mul, add_zero, le_refl]
  · intro k hh
    by_cases hk : k = 0
    · subst k
      norm_num [measure, iterate] at hh
    · simp [iterate, hk]

/-- The correct source threshold is one quarter. -/
theorem threshold : trGapThreshold 1 (1 / 2) 2 1 = 1 / 4 := by
  norm_num [trGapThreshold, Real.rpow_neg, Real.rpow_natCast]

/-- The initial gap is strictly above the correct threshold, but every actual
positive gap is below one, contradicting the printed unnormalized bound. -/
theorem obstruction :
    trGapThreshold 1 (1 / 2) 2 1 < gap objective 0 (iterate 0) ∧
      (∀ k, gap objective 0 (iterate k) < 1) ∧
      gap objective 0 (iterate 1) = 0 := by
  rw [threshold]
  refine ⟨by norm_num [gap, objective, iterate], ?_, by norm_num [gap, objective, iterate]⟩
  intro k
  by_cases hk : k = 0 <;> norm_num [gap, objective, iterate, hk]

end MeasureDomination.ThresholdCounterexample
