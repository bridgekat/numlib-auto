/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.ContinuousMap.Compact`, beside `ContinuousMap.norm_le`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The sup norm of a continuous function on a compact space is attained

`ContinuousMap.exists_norm_apply_eq_norm`: on a nonempty compact space, some point `x` has
`‖f x‖ = ‖f‖`.
-/

namespace ContinuousMap

/-- **The sup norm of a continuous function on a nonempty compact space is attained.** -/
theorem exists_norm_apply_eq_norm {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [SeminormedAddCommGroup E] (f : C(X, E)) : ∃ x, ‖f x‖ = ‖f‖ := by
  obtain ⟨t, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_norm.comp f.continuous).continuousOn
  refine ⟨t, le_antisymm (f.norm_coe_le_norm t) ?_⟩
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  exact fun u => by simpa using hmax (Set.mem_univ u)

end ContinuousMap
