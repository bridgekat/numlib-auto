import Numlib.Optimization.HighOrder.ModelSolve.Computation
import Numlib.Optimization.HighOrder.CriticalityLocalMin

/-!
# Unit-radius low-order computations at actual global minima

A global minimum passes the first- and second-order actual Taylor checks
with zero reductions. No model-test conclusion is assumed in the computation.
-/

namespace ModelSolve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- At a genuine global model minimum, the actual first- and second-order
Taylor tests pass with unit radius and zero reductions. The constructed record
contains actual Taylor decrements, not assumed criticality conclusions. -/
theorem stepComputation_unit_of_isMin {m : E → ℝ} {p : ℕ}
    (hf : ContDiff ℝ p m) {ι : Type*} (order : ι → ℕ)
    (horder : ∀ a, 0 < order a ∧ order a ≤ min 2 p)
    {θ ζ : ℝ} (hθ : 0 < θ) (hζ : 0 < ζ) (ε : ι → ℝ) (hε : ∀ a, 0 < ε a)
    (s : E) (hmin : ∀ t, m s ≤ m t) :
    StepComputation m order θ ζ ε s (fun _ => 1) := by
  classical
  have hlocal : IsLocalMin m s := Filter.Eventually.of_forall hmin
  have hzero : ∀ a, TaylorModel.criticality m (order a) s 1 = 0 := by
    intro a
    have ha := horder a
    have ha2 : order a ≤ 2 := ha.2.trans (min_le_left _ _)
    have hap : order a ≤ p := ha.2.trans (min_le_right _ _)
    interval_cases hj : order a
    · omega
    · exact TaylorModel.criticality_one_eq_zero_of_isLocalMin hlocal zero_le_one
    · exact TaylorModel.criticality_two_eq_zero_of_isLocalMin
        (hf.of_le (by exact_mod_cast hap)) hlocal zero_le_one
  have hfrac : ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧
      ModelDecrease.ApproximateGlobalStep m μ s := by
    refine ⟨1, zero_lt_one, le_rfl, ?_⟩
    intro t
    simpa only [one_mul] using sub_le_sub_left (hmin t) (m 0)
  refine ⟨hfrac, ?_⟩
  by_cases hs : 1 < ‖s‖
  · exact Or.inl ⟨hs, fun _ => rfl⟩
  · right
    refine ⟨not_lt.mp hs, (fun _ _ => s), (fun _ _ => 0), (fun _ => 0),
      (fun _ => 0), ?_⟩
    intro a
    refine ⟨fun _ ht => (Nat.not_lt_zero _ ht).elim, ?_, fun _ => rfl, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun _ ht => (Nat.not_lt_zero _ ht).elim,
        fun _ ht => (Nat.not_lt_zero _ ht).elim,
        fun _ ht => (Nat.not_lt_zero _ ht).elim⟩
    · simp
    · simp
    · rw [hzero a]
      simp
    · rw [TaylorModel.decrement_zero]
      have := hε a
      positivity

end ModelSolve
