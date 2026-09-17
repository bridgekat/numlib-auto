/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Numlib.Analysis.Normed.Module.BestApprox

/-!
# The projection onto a closed convex set of a Hilbert space

The metric projection `P_K` onto a nonempty closed convex subset `K` of a real Hilbert space, as
the function `bestApprox K` of `Numlib.Analysis.Normed.Module.BestApprox`: the projection theorem,
its variational characterization, the nonexpansiveness of the projection, and its agreement
with `Submodule.starProjection` on closed subspaces. This is [brezis2011functional] §5.1
(Theorem 5.2, Proposition 5.3, Corollary 5.4) and [han2009theoretical] §3.4 (Theorem 3.4.3,
Proposition 3.4.4, Theorem 3.4.6).

Mathlib proves the projection theorem as an existence statement
(`exists_norm_eq_iInf_of_complete_convex`) and characterizes the minimizer
(`norm_eq_iInf_iff_real_inner_le_zero`), but bundles the projection as a map only for subspaces
(`Submodule.starProjection`); the map onto a convex set is `bestApprox K`, defined in any
seminormed space by choice, with the hypotheses of the projection theorem on the theorems.

## Main statements

* `exists_isBestApprox_of_isClosed`, `existsUnique_isBestApprox` — **the projection theorem**
  ([brezis2011functional] Theorem 5.2): for `K` nonempty, closed and convex, every `u` has a
  unique best approximation from `K`. Hence `isBestApprox_bestApprox_of_isClosed`,
  `bestApprox_mem`.
* `inner_sub_bestApprox_le_zero`, `bestApprox_eq_iff` — the variational characterization
  `⟪u - P_K u, v - P_K u⟫ ≤ 0` for all `v ∈ K`, which determines `P_K u`.
* `inner_bestApprox_sub_nonneg`, `norm_bestApprox_sub_bestApprox_le`, `lipschitzWith_bestApprox`
  — the projection is monotone and does not increase distances
  ([brezis2011functional] Proposition 5.3).
* `bestApprox_eq_starProjection` — on a closed subspace the metric projection is the orthogonal
  projection ([brezis2011functional] Corollary 5.4), over `RCLike 𝕜`.

The scalars are real for the convex-set theory, as in Mathlib's
`norm_eq_iInf_iff_real_inner_le_zero`; over `RCLike 𝕜` the map is still the metric projection
(it is defined from the norm alone) and the subspace clause is stated there.
-/

open scoped InnerProductSpace

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **The projection theorem, existence** ([brezis2011functional] Theorem 5.2): in a real
Hilbert space every point has a best approximation from a nonempty closed convex set. This is
Mathlib's `exists_norm_eq_iInf_of_complete_convex` read through the metric description of
`IsBestApprox`; the backbone's `exists_isBestApprox_of_convex`
(`Numlib.Variational.WeakMinimization`) is the same statement by the direct method of the
calculus of variations. -/
theorem exists_isBestApprox_of_isClosed {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u : V) : ∃ v, IsBestApprox K u v := by
  obtain ⟨v, hv, hnorm⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hK u
  refine ⟨v, (isBestApprox_iff_norm_sub_eq_infDist hv).2 ?_⟩
  rw [hnorm, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]

/-- **The projection theorem** ([brezis2011functional] Theorem 5.2) as a `∃!`: existence from
`exists_isBestApprox_of_isClosed`, uniqueness from strict convexity (`IsBestApprox.unique`). -/
theorem existsUnique_isBestApprox {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u : V) : ∃! v, IsBestApprox K u v := by
  obtain ⟨v, hv⟩ := exists_isBestApprox_of_isClosed hne hcl hK u
  exact ⟨v, hv, fun w hw => hw.unique hK hv⟩

variable {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K)
include hne hcl hK

/-- For `K` nonempty closed convex, `bestApprox K u` is a best approximation of `u` from `K`:
the projection `P_K u` of [brezis2011functional] §5.1, unconditionally. -/
theorem isBestApprox_bestApprox_of_isClosed (u : V) : IsBestApprox K u (bestApprox K u) :=
  isBestApprox_bestApprox (exists_isBestApprox_of_isClosed hne hcl hK u)

/-- The projection onto a nonempty closed convex set lands in it. -/
theorem bestApprox_mem (u : V) : bestApprox K u ∈ K :=
  (isBestApprox_bestApprox_of_isClosed hne hcl hK u).1

/-- **The variational inequality of the projection** ([brezis2011functional] Theorem 5.2,
formula (3)): `⟪u - P_K u, v - P_K u⟫ ≤ 0` for every `v ∈ K`. -/
theorem inner_sub_bestApprox_le_zero (u : V) :
    ∀ v ∈ K, ⟪u - bestApprox K u, v - bestApprox K u⟫_ℝ ≤ 0 :=
  (isBestApprox_iff_inner_le_zero hK (bestApprox_mem hne hcl hK u)).1
    (isBestApprox_bestApprox_of_isClosed hne hcl hK u)

/-- **The variational characterization of the projection** ([brezis2011functional] Theorem 5.2):
`P_K u = w` iff `w ∈ K` and `⟪u - w, v - w⟫ ≤ 0` for every `v ∈ K`. -/
theorem bestApprox_eq_iff {u w : V} :
    bestApprox K u = w ↔ w ∈ K ∧ ∀ v ∈ K, ⟪u - w, v - w⟫_ℝ ≤ 0 := by
  constructor
  · rintro rfl
    exact ⟨bestApprox_mem hne hcl hK u, inner_sub_bestApprox_le_zero hne hcl hK u⟩
  · rintro ⟨hw, h⟩
    exact IsBestApprox.bestApprox_eq hK ((isBestApprox_iff_inner_le_zero hK hw).2 h)

/-- **The projection is monotone**: `0 ≤ ⟪P_K u₁ - P_K u₂, u₁ - u₂⟫` (the first clause of
`IsBestApprox.dist_le_dist`, [han2009theoretical] Proposition 3.4.4). -/
theorem inner_bestApprox_sub_nonneg (u₁ u₂ : V) :
    0 ≤ ⟪bestApprox K u₁ - bestApprox K u₂, u₁ - u₂⟫_ℝ :=
  ((isBestApprox_bestApprox_of_isClosed hne hcl hK u₁).dist_le_dist hK
    (isBestApprox_bestApprox_of_isClosed hne hcl hK u₂)).1

/-- **The projection does not increase distances** ([brezis2011functional] Proposition 5.3):
`‖P_K u₁ - P_K u₂‖ ≤ ‖u₁ - u₂‖`. -/
theorem norm_bestApprox_sub_bestApprox_le (u₁ u₂ : V) :
    ‖bestApprox K u₁ - bestApprox K u₂‖ ≤ ‖u₁ - u₂‖ :=
  ((isBestApprox_bestApprox_of_isClosed hne hcl hK u₁).dist_le_dist hK
    (isBestApprox_bestApprox_of_isClosed hne hcl hK u₂)).2

/-- The projection onto a nonempty closed convex set is `1`-Lipschitz
([brezis2011functional] Proposition 5.3). -/
theorem lipschitzWith_bestApprox : LipschitzWith 1 (bestApprox K) :=
  LipschitzWith.of_dist_le_mul fun u₁ u₂ => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_bestApprox_sub_bestApprox_le hne hcl hK u₁ u₂

end Hilbert

section Subspace

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **On a subspace the metric projection is the orthogonal projection**
([brezis2011functional] Corollary 5.4): for `K : Submodule 𝕜 V` with an orthogonal projection,
`bestApprox K u = K.starProjection u`. With `Submodule.starProjection` a bounded linear map,
this is the corollary's "`P_M` is a linear operator"; its characterization "`u ∈ M` and
`⟪f - u, v⟫ = 0` for all `v ∈ M`" is `isBestApprox_iff_mem_orthogonal`. -/
theorem bestApprox_eq_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] (u : V) :
    bestApprox (K : Set V) u = K.starProjection u :=
  (isBestApprox_bestApprox ⟨_, isBestApprox_starProjection K u⟩).eq_starProjection K

end Subspace
