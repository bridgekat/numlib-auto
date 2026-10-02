/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.FiniteDimension`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic

/-!
# Coordinates in a finite linearly independent family

`LinearIndependent.exists_forall_sum_norm_le`: the coordinates of a vector in the span of a finite
linearly independent family `x` of a normed space are bounded in ℓ¹ by a fixed multiple `κ` of its
norm, `∑ ‖c j‖ ≤ κ ‖∑ c j x j‖`. The constant measures how far from orthonormal the family is; it
is what turns per-vector estimates into subspace estimates
(`Submodule.gap_le_of_forall_norm_sub_le`).
-/

/-- **The ℓ¹ conditioning constant of a finite linearly independent family**: the coordinates of a
vector in the span are bounded by a fixed multiple of its norm.

The constant depends on the family and not only on its cardinality, and it is what measures how far
from orthonormal the family is. It comes from `LinearMap.exists_antilipschitzWith`, the injective
linear map here being `c ↦ ∑ c j • x j` on the finite-dimensional space `ι → 𝕜`; no finite
dimensionality of the ambient space is needed. -/
theorem LinearIndependent.exists_forall_sum_norm_le {𝕜 F ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι] {x : ι → F}
    (hx : LinearIndependent 𝕜 x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ c : ι → 𝕜, ∑ j, ‖c j‖ ≤ κ * ‖∑ j, c j • x j‖ := by
  have hker : LinearMap.ker (Fintype.linearCombination 𝕜 x) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext j
    exact Fintype.linearIndependent_iff.1 hx c
      (by simpa [Fintype.linearCombination_apply] using hc) j
  obtain ⟨K, hK, hanti⟩ := (Fintype.linearCombination 𝕜 x).exists_antilipschitzWith hker
  refine ⟨Fintype.card ι * K + 1, by positivity, fun c => ?_⟩
  have hc : ‖c‖ ≤ K * ‖∑ j, c j • x j‖ := by
    simpa [Fintype.linearCombination_apply] using ZeroHomClass.bound_of_antilipschitz _ hanti c
  calc ∑ j, ‖c j‖ ≤ ∑ _j : ι, ‖c‖ := Finset.sum_le_sum fun j _ => norm_le_pi_norm c j
    _ = Fintype.card ι * ‖c‖ := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * (K * ‖∑ j, c j • x j‖) := by gcongr
    _ ≤ (Fintype.card ι * K + 1) * ‖∑ j, c j • x j‖ := by
        rw [← mul_assoc]
        nlinarith [norm_nonneg (∑ j, c j • x j)]
