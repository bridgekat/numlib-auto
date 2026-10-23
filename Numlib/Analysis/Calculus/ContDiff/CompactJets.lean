import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Common finite derivative bounds on compact sets

Continuity of the genuine derivative tensors and finiteness of the order range
give one positive bound before every point of a compact set and every order.
-/

open Set
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A finite-smooth map has a common positive bound on all its actual derivative
norms through that order on any compact set. -/
theorem IsCompact.exists_bound_iteratedFDeriv {K : Set E} (hK : IsCompact K)
    {n : ℕ} {f : E → F} (hf : ContDiff 𝕜 n f) :
    ∃ B > 0, ∀ j ≤ n, ∀ x ∈ K, ‖iteratedFDeriv 𝕜 j f x‖ ≤ B := by
  let G : E → Fin (n + 1) → ℝ := fun x j => ‖iteratedFDeriv 𝕜 j.val f x‖
  have hG : Continuous G := by
    apply continuous_pi
    intro j
    exact (hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_of_lt_succ j.isLt)).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro j hj x hx
  have hh : ‖iteratedFDeriv 𝕜 j f x‖ ≤ ‖G x‖ := by
    simpa only [G, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      norm_le_pi_norm (G x) (⟨j, by omega⟩ : Fin (n + 1))
  exact hh.trans ((hC x hx).trans (by linarith [le_max_left C (0 : ℝ)]))
