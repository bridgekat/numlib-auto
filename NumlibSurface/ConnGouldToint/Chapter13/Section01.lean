import Numlib.Optimization.LogBarrier
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases

/-! # The logarithmic barrier -/

open Filter Metric
open scoped BigOperators Topology

namespace ConnGouldToint.Chapter13

/-- The log-barrier term (13.1.2), evaluated on strictly positive vectors. -/
noncomputable abbrev logBarrier {ι : Type*} [Fintype ι] (x : ι → ℝ) (μ : ℝ) : ℝ :=
  Optimization.logBarrier μ x

/-- The barrier objective (13.1.1). -/
noncomputable def logBarrierObjective {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (μ : ℝ) : ℝ :=
  f x + logBarrier x μ

/-- The bounded-path version of AC.8 for the logarithmic barrier. -/
theorem logBarrier_boundary_divergence {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {x : ℕ → ι → ℝ}
    (hx : ∀ n i, 0 < x n i) (hbounded : ∀ n i, x n i ≤ M)
    (ht : Tendsto (fun n ↦ infDist (x n) (frontier (Optimization.nonnegativeOrthant ι)))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ logBarrier (x n) μ) atTop atTop :=
  Optimization.tendsto_logBarrier_of_bounded_of_infDist_frontier hμ hx hbounded ht

/-- The logarithmic barrier does not satisfy the unrestricted AC.8.
A coordinate tending to infinity can cancel the logarithm of a coordinate
tending to zero, even as the distance to the boundary tends to zero. -/
theorem logBarrier_unbounded_boundary_counterexample :
    ∃ x : ℕ → Fin 2 → ℝ, (∀ n i, 0 < x n i) ∧
      Tendsto (fun n ↦ infDist (x n) (frontier (Optimization.nonnegativeOrthant (Fin 2))))
        atTop (𝓝 0) ∧
      (∀ n, logBarrier (x n) 1 = 0) ∧
      ¬ Tendsto (fun n ↦ logBarrier (x n) 1) atTop atTop := by
  let x (n : ℕ) (i : Fin 2) := if i = 0 then 1 / ((n : ℝ) + 1) else (n : ℝ) + 1
  let y (n : ℕ) (i : Fin 2) := if i = 0 then (0 : ℝ) else (n : ℝ) + 1
  have hy (n : ℕ) : y n ∈ frontier (Optimization.nonnegativeOrthant (Fin 2)) := by
    apply Optimization.mem_frontier_nonnegativeOrthant.mpr
    refine ⟨fun i ↦ ?_, 0, by simp [y]⟩
    by_cases hi : i = 0
    · simpa only [y, ite_eq_left hi] using (le_rfl : (0 : ℝ) ≤ 0)
    · simpa only [y, ite_eq_right hi] using (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hdist (n : ℕ) : infDist (x n) (frontier (Optimization.nonnegativeOrthant (Fin 2))) ≤
      1 / ((n : ℝ) + 1) := by
    refine (infDist_le_dist_of_mem (hy n)).trans ((dist_pi_le_iff (by positivity)).mpr ?_)
    intro i
    fin_cases i
    · change dist (1 / ((n : ℝ) + 1)) 0 ≤ _
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    · change dist ((n : ℝ) + 1) ((n : ℝ) + 1) ≤ _
      rw [dist_self]
      positivity
  have hb (n : ℕ) : logBarrier (x n) 1 = 0 := by
    simp [Optimization.logBarrier, Fin.sum_univ_two, x]
  refine ⟨x, fun n i ↦ ?_, ?_, hb, ?_⟩
  · by_cases hi : i = 0
    · simpa only [x, ite_eq_left hi] using (show 0 < 1 / ((n : ℝ) + 1) by positivity)
    · simpa only [x, ite_eq_right hi] using (show 0 < (n : ℝ) + 1 by positivity)
  · exact squeeze_zero' (Eventually.of_forall fun _ ↦ infDist_nonneg)
      (Eventually.of_forall hdist) tendsto_one_div_add_atTop_nhds_zero_nat
  · intro h
    obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp h (1 : ℝ)).exists
    rw [hb] at hn
    norm_num at hn

end ConnGouldToint.Chapter13
