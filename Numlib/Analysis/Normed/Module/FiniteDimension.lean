/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $x_1, \dots, x_m$ be a finite linearly independent family in a normed space $F$ over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. This file shows that the coordinates of a vector in the
span of the family are bounded in $\ell^1$ by a fixed multiple $\kappa$ of its norm: $$\sum_j |c_j|
\le \kappa \, \Bigl\| \sum_j c_j x_j \Bigr\|.$$ The constant $\kappa$ measures how far the family is
from orthonormal. It turns estimates for single vectors into estimates for subspaces, as in
`Submodule.gap_le_of_forall_norm_sub_le`.

## Main results

* `LinearIndependent.exists_forall_sum_norm_le`: there is a constant $\kappa > 0$ with
  $\sum_j |c_j| \le \kappa \|\sum_j c_j x_j\|$ for all coefficients $c$.
-/

/-- Let $F$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$(x_j)_{j \in \iota}$ be a linearly independent family in $F$ indexed by a finite type $\iota$.
Then there is a constant $\kappa > 0$ such that $$\sum_{j \in \iota} |c_j| \le \kappa \, \Bigl\|
\sum_{j \in \iota} c_j x_j \Bigr\| \quad \text{for all } c \in \mathbb{K}^\iota.$$

The constant depends on the family and not only on its cardinality; it measures how far the
family is from orthonormal. The space $F$ need not be finite-dimensional. The constant comes
from `LinearMap.exists_antilipschitzWith`, applied to the injective linear map
$c \mapsto \sum_j c_j x_j$ on the finite-dimensional space $\mathbb{K}^\iota$. -/
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
