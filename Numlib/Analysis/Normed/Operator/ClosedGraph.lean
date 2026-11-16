/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Banach`, beside
`LinearMap.continuous_of_seq_closed_graph`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# A bounded lift along an injective bounded map

Let $X$ and $Y$ be real Banach spaces, let $Z$ be a real normed space, and let $J : Y \to Z$ be an
injective bounded linear map. A bounded linear map $S : X \to Z$ whose values all lie in the range
of $J$ factors as $S = J \circ T$ with $T : X \to Y$ bounded linear. The lift $T$ is linear because
$J$ is injective, and it is continuous by the closed graph theorem because $J$ and $S$ are
continuous. This is how a solution operator with values in a smaller space, such as
$D(A) \to H^1_0(\Omega)$ or $D(A^\ell) \to H^{2\ell}(\Omega)$, is made bounded for the norm of the
smaller space.

## Main results

* `exists_continuousLinearMap_comp_eq_of_injective`: a bounded linear map into the range of an
  injective bounded linear map $J$ lifts to a bounded linear map $T$ with $J \circ T = S$.
-/

open Filter Topology

/-- **A bounded lift along an injective bounded map.** Let $X$ and $Y$ be real Banach spaces, let
$Z$ be a real normed space, let $J : Y \to Z$ be an injective bounded linear map, and let
$S : X \to Z$ be a bounded linear map such that for every $x \in X$ there is $y \in Y$ with
$Jy = Sx$. Then there is a bounded linear map $T : X \to Y$ with $$J(Tx) = Sx \qquad \text{for
all } x \in X.$$

The space $Z$ need not be complete. The lift is linear because $J$ is injective, and its graph
is closed because $J$ and $S$ are continuous, so the closed graph theorem makes it bounded. -/
theorem exists_continuousLinearMap_comp_eq_of_injective {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {J : Y →L[ℝ] Z} (hJ : Function.Injective J)
    {S : X →L[ℝ] Z} (hS : ∀ x, ∃ y, J y = S x) : ∃ T : X →L[ℝ] Y, ∀ x, J (T x) = S x := by
  choose T hT using hS
  obtain ⟨Tₗ, hTₗ⟩ : ∃ Tₗ : X →ₗ[ℝ] Y, ∀ x, Tₗ x = T x := by
    refine ⟨{ toFun := T, map_add' := fun x y ↦ ?_, map_smul' := fun c x ↦ ?_ }, fun _ ↦ rfl⟩
    · refine hJ ?_
      rw [map_add, hT, hT, hT, map_add]
    · refine hJ ?_
      rw [RingHom.id_apply, map_smul, hT, hT, map_smul]
  have hcont : Continuous Tₗ := by
    refine Tₗ.continuous_of_seq_closed_graph fun u x y hux hTy ↦ ?_
    have h1 : Tendsto (fun n ↦ J (Tₗ (u n))) atTop (𝓝 (J y)) := (J.continuous.tendsto y).comp hTy
    have h2 : Tendsto (fun n ↦ S (u n)) atTop (𝓝 (S x)) := (S.continuous.tendsto x).comp hux
    have h12 : (fun n ↦ J (Tₗ (u n))) = fun n ↦ S (u n) := by
      funext n
      rw [hTₗ, hT]
    rw [h12] at h1
    refine hJ ?_
    rw [hTₗ, hT, tendsto_nhds_unique h1 h2]
  exact ⟨⟨Tₗ, hcont⟩, fun x ↦ by rw [← hT x, ← hTₗ x]; rfl⟩
