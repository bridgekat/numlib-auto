import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Best approximation

`IsBestApprox K u v`: `v ∈ K` minimizes `‖u - v‖` over `K`. Existence from finite-dimensional
subspaces (Atkinson–Han Thm 3.3.16, Kress Thm 3.50), uniqueness in strictly convex spaces
(AH Thm 3.3.21), the Hilbert-space characterizations (AH Lemma 3.4.1, Thm 3.4.6; Kress Thm 3.51)
as glue to Mathlib's orthogonal projection, and the Lebesgue lemma for projections
(AH (3.7.11), (3.7.14), (3.7.21)).
-/

section Normed

variable {V : Type*} [SeminormedAddCommGroup V]

/-- `v ∈ K` is a best approximation of `u` from `K`. -/
def IsBestApprox (K : Set V) (u v : V) : Prop := v ∈ K ∧ ∀ w ∈ K, ‖u - v‖ ≤ ‖u - w‖

theorem IsBestApprox.norm_sub_eq_infDist {K : Set V} {u v : V} (h : IsBestApprox K u v) :
    ‖u - v‖ = Metric.infDist u K := by
  sorry

theorem isBestApprox_iff_norm_sub_eq_infDist {K : Set V} {u v : V} (hv : v ∈ K) :
    IsBestApprox K u v ↔ ‖u - v‖ = Metric.infDist u K := by
  sorry

end Normed

section Real

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- The set of best approximations from a convex set is convex (AH Thm 3.3.12). -/
theorem convex_setOf_isBestApprox {K : Set V} (hK : Convex ℝ K) (u : V) :
    Convex ℝ {v | IsBestApprox K u v} := by
  sorry

end Real

section Existence

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- AH Thm 3.3.16 / Kress Thm 3.50: best approximations from finite-dimensional subspaces exist. -/
theorem exists_isBestApprox_of_finiteDimensional [CompleteSpace 𝕜] (K : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 K] (u : V) : ∃ v, IsBestApprox (K : Set V) u v := by
  sorry

/-- AH Thm 3.3.15: best approximations from closed convex finite-dimensional sets exist (a closed
subset of a finite-dimensional subspace). -/
theorem exists_isBestApprox_of_isClosed_of_finiteDimensional [CompleteSpace 𝕜] {K : Set V}
    (hK : IsClosed K) (hne : K.Nonempty) (S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S]
    (hKS : K ⊆ S) (u : V) : ∃ v, IsBestApprox K u v := by
  sorry

end Existence

section Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]

/-- AH Thm 3.3.21: in a strictly convex space, best approximations from a convex set are unique. -/
theorem IsBestApprox.unique {K : Set V} (hK : Convex ℝ K) {u v₁ v₂ : V} (h₁ : IsBestApprox K u v₁)
    (h₂ : IsBestApprox K u v₂) : v₁ = v₂ := by
  sorry

end Uniqueness

section RealHilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- AH Lemma 3.4.1 (variational characterization on convex sets, real inner product spaces):
`v` is a best approximation of `u` from convex `K` iff `⟪u - v, w - v⟫ ≤ 0` for all `w ∈ K`
(Mathlib: `norm_eq_iInf_iff_real_inner_le_zero`). -/
theorem isBestApprox_iff_inner_le_zero {K : Set V} (hK : Convex ℝ K) {u v : V} (hv : v ∈ K) :
    IsBestApprox K u v ↔ ∀ w ∈ K, inner ℝ (u - v) (w - v) ≤ 0 := by
  sorry

/-- AH Prop 3.4.4: the metric projection onto a convex set is monotone and non-expansive,
in pairs form. -/
theorem IsBestApprox.dist_le_dist {K : Set V} (hK : Convex ℝ K) {u₁ u₂ v₁ v₂ : V}
    (h₁ : IsBestApprox K u₁ v₁) (h₂ : IsBestApprox K u₂ v₂) :
    0 ≤ inner ℝ (v₁ - v₂) (u₁ - u₂) ∧ ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ := by
  sorry

end RealHilbert

section Hilbert

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- AH Thm 3.4.6 / Kress Thm 3.51 (subspaces): best approximation iff the error is orthogonal. -/
theorem isBestApprox_iff_mem_orthogonal (K : Submodule 𝕜 V) {u v : V} (hv : v ∈ K) :
    IsBestApprox (K : Set V) u v ↔ u - v ∈ Kᗮ := by
  sorry

/-- The best approximation from a subspace with an orthogonal projection is `P_K u`
(AH Thm 3.4.6/3.4.7, Kress Thm 3.52). -/
theorem isBestApprox_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] (u : V) :
    IsBestApprox (K : Set V) u (K.starProjection u) := by
  sorry

theorem IsBestApprox.eq_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] {u v : V}
    (h : IsBestApprox (K : Set V) u v) : v = K.starProjection u := by
  sorry

/-- Kress Cor 3.53 (normal equations): with a basis `u i` of `K`, `∑ a i • u i` is the best
approximation of `w` iff `∑_i a i ⟪u j, u i⟫ = ⟪u j, w⟫` for all `j`. -/
theorem isBestApprox_sum_iff {ι : Type*} [Fintype ι] (u : ι → V) (a : ι → 𝕜) (w : V) :
    IsBestApprox (Submodule.span 𝕜 (Set.range u) : Set V) w (∑ i, a i • u i) ↔
      ∀ j, ∑ i, a i * inner 𝕜 (u j) (u i) = inner 𝕜 (u j) w := by
  sorry

end Hilbert

section Lebesgue

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Lebesgue lemma (AH (3.7.11)/(3.7.14)/(3.7.21) abstracted): for a bounded projection `P`
(`P ∘ P = P`) onto `S = range P`, `‖u - P u‖ ≤ (1 + ‖P‖) dist(u, S)`. -/
theorem norm_sub_apply_le_of_isIdempotentElem (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ (1 + ‖P‖) * Metric.infDist u (LinearMap.range (P : V →ₗ[𝕜] V) : Set V) := by
  sorry

/-- Pointwise form: `‖u - P u‖ ≤ (1 + ‖P‖) ‖u - q‖` for every `q` in the range of `P`. -/
theorem norm_sub_apply_le_of_isIdempotentElem_of_mem (P : V →L[𝕜] V) (hP : IsIdempotentElem P)
    (u : V) {q : V} (hq : q ∈ LinearMap.range (P : V →ₗ[𝕜] V)) :
    ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - q‖ := by
  sorry

/-- Sharper form `‖u - P u‖ ≤ ‖1 - P‖ dist(u, S)`. -/
theorem norm_sub_apply_le_of_isIdempotentElem' (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ ‖(1 : V →L[𝕜] V) - P‖ *
      Metric.infDist u (LinearMap.range (P : V →ₗ[𝕜] V) : Set V) := by
  sorry

/-- AH Ex 3.6.7: a nonzero bounded projection has norm `≥ 1`. -/
theorem one_le_norm_of_isIdempotentElem {P : V →L[𝕜] V} (hP : IsIdempotentElem P) (h0 : P ≠ 0) :
    1 ≤ ‖P‖ := by
  sorry

end Lebesgue
