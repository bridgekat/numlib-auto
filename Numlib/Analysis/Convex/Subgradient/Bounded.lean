import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Subgradient.Monotone

/-!
# Local boundedness of the subdifferential

A proper convex function is Lipschitz on every compact subset `S` of the interior of its effective
domain, and *the same constant* bounds its subgradients and its directional derivatives there:
there is a `K ≥ 0` with `f` Lipschitz on `S` with constant `K`, with
`⟨z, y⟩ ≤ K ‖z‖` for every `x ∈ S`, every `y ∈ ∂f x` and every direction `z`, and with
`f'(x; z) ≤ K ‖z‖` for every `x ∈ S`. When `f` is in addition closed, the image
`∂f(S) = ⋃ {∂f x | x ∈ S}` is nonempty and compact.

## Main results

* `exists_lipschitz_forall_pairing_le_of_isCompact` — the three bounds with one constant, over an
  arbitrary pairing (Theorem 24.7 in [^1]); `exists_forall_norm_le_of_isCompact` gives `‖y‖ ≤ K`.
* `isCompact_subgradient`, `isCompact_image_subgradientRel` — `∂f x` and `∂f(S)` are compact, hence
  closed and bounded, and `∂f(S)` is non-empty.

## Implementation notes

The bound on subgradients is stated as `⟨z, y⟩ ≤ K ‖z‖` for all `z`, which asks for no norm on the
dual side; when `F = E` is an inner-product space, reading it at `z = y` gives `‖y‖ ≤ K`. The
compactness statements are for a real inner-product space paired with itself, and closedness of `f`
is used only for them.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24.
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

namespace ConvexAnalysis

/-! ### The quantitative half -/

section Bound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- Moving a point of `S` a distance `δ` in any direction keeps it inside the collar
`cthickening δ S`. -/
theorem mem_cthickening_add_smul {S : Set E} {x : E} (hx : x ∈ S) {δ : ℝ} (hδ : 0 < δ) {z : E}
    (hz : z ≠ 0) : x + (δ / ‖z‖) • z ∈ Metric.cthickening δ S := by
  have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
  refine Metric.mem_cthickening_of_dist_le _ _ _ _ hx (le_of_eq ?_)
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hδ hznorm)]
  field_simp

/-- **The quantitative half**. On a compact `S ⊆ int (dom f)` a single constant `K` is
simultaneously a Lipschitz constant for `f`, a bound `⟨z, y⟩ ≤ K ‖z‖` for every subgradient at
every point of `S`, and a bound `f'(x; z) ≤ K ‖z‖` for the directional derivatives. `K` is taken to
be a Lipschitz constant on a compact collar `cthickening δ S ⊆ int (dom f)`, and the other two
bounds are read off it at the point `x + (δ / ‖z‖) • z`, which stays in the collar. -/
theorem exists_lipschitz_forall_pairing_le_of_isCompact (hf : ConvexFn f) (hp : Proper f)
    {S : Set E} (hS : IsCompact S) (hSD : S ⊆ interior (dom f)) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x => (f x).toReal) S ∧
      (∀ x ∈ S, ∀ y ∈ subgradient B f x, ∀ z : E, B z y ≤ (K : ℝ) * ‖z‖) ∧
      ∀ x ∈ S, ∀ z : E, dirDeriv f x z ≤ (((K : ℝ) * ‖z‖ : ℝ) : EReal) := by
  obtain ⟨δ, hδ, hδsub⟩ := hS.exists_cthickening_subset_open isOpen_interior hSD
  have hTc : IsCompact (Metric.cthickening δ S) := hS.cthickening
  have hTdom : Metric.cthickening δ S ⊆ dom f := hδsub.trans interior_subset
  have hTri : Metric.cthickening δ S ⊆ ri (dom f) := fun w hw =>
    Convex.interior_subset_relint hf.convex_dom ⟨w, hδsub hw⟩ (hδsub hw)
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith_of_isCompact hp hTc hTri
  -- The single estimate both halves consume.
  have hkey : ∀ x ∈ S, ∀ z : E, z ≠ 0 → ∀ a b : ℝ, f x = (a : EReal) →
      f (x + (δ / ‖z‖) • z) = (b : EReal) → b - a ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := by
    intro x hx z hz a b ha hb
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hxT : x ∈ Metric.cthickening δ S := Metric.self_subset_cthickening S hx
    have hwT := mem_cthickening_add_smul hx hδ hz
    have hnorm : dist (x + (δ / ‖z‖) • z) x = (δ / ‖z‖) * ‖z‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hδ hznorm)]
    have hlip := hK.dist_le_mul _ hwT _ hxT
    simp only [ha, hb, EReal.toReal_coe, Real.dist_eq, hnorm] at hlip
    exact (le_abs_self _).trans hlip
  refine ⟨K, hK.mono (Metric.self_subset_cthickening S), ?_, ?_⟩
  · intro x hx y hy z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have ht : (0 : ℝ) < δ / ‖z‖ := div_pos hδ hznorm
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x)
      (hTdom (Metric.self_subset_cthickening S hx))
    obtain ⟨b, hb⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot _)
      (hTdom (mem_cthickening_add_smul hx hδ hz))
    have hsg := hy (x + (δ / ‖z‖) • z)
    rw [add_sub_cancel_left, map_smul, LinearMap.smul_apply, smul_eq_mul, ha, hb,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at hsg
    refine le_of_mul_le_mul_left ?_ ht
    calc (δ / ‖z‖) * B z y
        ≤ b - a := by linarith
      _ ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := hkey x hx z hz a b ha hb
      _ = (δ / ‖z‖) * ((K : ℝ) * ‖z‖) := by ring
  · intro x hx z
    have hxT : x ∈ Metric.cthickening δ S := Metric.self_subset_cthickening S hx
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) (hTdom hxT)
    rcases eq_or_ne z 0 with rfl | hz
    · rw [dirDeriv_zero (by rw [ha]; exact EReal.coe_ne_top a) (hp.ne_bot x)]
      simp
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have ht : (0 : ℝ) < δ / ‖z‖ := div_pos hδ hznorm
    obtain ⟨b, hb⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot _)
      (hTdom (mem_cthickening_add_smul hx hδ hz))
    refine le_trans (dirDeriv_le f x z ht) ?_
    rw [ha, hb, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff,
      div_le_iff₀ ht]
    calc b - a ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := hkey x hx z hz a b ha hb
      _ = (K : ℝ) * ‖z‖ * (δ / ‖z‖) := by ring

end Bound

/-! ### The topological half -/

section Image

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- The norm form of the subgradient bound: on a compact `S ⊆ int (dom f)` a single constant bounds
`‖y‖` for every subgradient `y` at every point of `S`. -/
theorem exists_forall_norm_le_of_isCompact (hf : ConvexFn f) (hp : Proper f) {S : Set E}
    (hS : IsCompact S) (hSD : S ⊆ interior (dom f)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ S, ∀ y ∈ subgradient (innerₗ E) f x, ‖y‖ ≤ K := by
  obtain ⟨K, -, hpair, -⟩ :=
    exists_lipschitz_forall_pairing_le_of_isCompact (B := innerₗ E) hf hp hS hSD
  refine ⟨K, K.coe_nonneg, fun x hx y hy => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have h := hpair x hx y hy y
  rw [innerₗ_apply_apply, real_inner_self_eq_norm_mul_norm] at h
  exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hy0)

/-- `∂f x` is compact at every interior point of `dom f`: closed because it is an intersection of
closed half-spaces, and bounded by the constant above. -/
theorem isCompact_subgradient (hf : ConvexFn f) (hp : Proper f) {x : E}
    (hx : x ∈ interior (dom f)) : IsCompact (subgradient (innerₗ E) f x) := by
  have : IsContinuousPairing ((innerₗ E).flip) := by rw [flip_innerₗ]; infer_instance
  obtain ⟨K, -, hK⟩ := exists_forall_norm_le_of_isCompact hf hp isCompact_singleton
    (by simpa using hx)
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E) K)
    (isClosed_subgradient _ _) fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hK x rfl y hy

/-- **Nonemptiness**: `∂f(S) ≠ ∅` for a nonempty `S ⊆ int (dom f)`. -/
theorem image_subgradientRel_nonempty (hf : ConvexFn f) (hp : Proper f) {S : Set E}
    (hne : S.Nonempty) (hSD : S ⊆ interior (dom f)) :
    ((subgradientRel (innerₗ E) f).image S).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := subgradient_nonempty_of_mem_relint_dom (B := innerₗ E) hf hp
    (Convex.interior_subset_relint hf.convex_dom ⟨x, hSD hx⟩ (hSD hx))
  exact ⟨y, x, hx, hy⟩

/-- **The topological half**: `∂f(S)` is compact for a closed proper convex `f` and a compact
`S ⊆ int (dom f)`. The graph of `∂f` is closed, so it meets the compact box
`S ×ˢ closedBall 0 K` in a compact set of which `∂f(S)` is the projection. -/
theorem isCompact_image_subgradientRel (hf : ClosedProperConvexFn f) {S : Set E}
    (hS : IsCompact S) (hSD : S ⊆ interior (dom f)) :
    IsCompact ((subgradientRel (innerₗ E) f).image S) := by
  obtain ⟨K, -, hnorm⟩ := exists_forall_norm_le_of_isCompact hf.convex hf.proper hS hSD
  have hbox : IsCompact (S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) :=
    IsCompact.prod hS (isCompact_closedBall 0 (K : ℝ))
  have hclosed : IsClosed (subgradientRel (innerₗ E) f) := by
    refine isClosed_subgradientRel ?_ hf.proper hf.lowerSemicontinuous
    exact continuous_inner
  have hcap : IsCompact (subgradientRel (innerₗ E) f ∩ S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) :=
    hbox.inter_left hclosed
  have himg : (subgradientRel (innerₗ E) f).image S
      = Prod.snd '' (subgradientRel (innerₗ E) f ∩ S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx, by simpa using hnorm x hx y hxy⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hpS, -⟩, rfl⟩
      exact ⟨p.1, hpS, hp⟩
  rw [himg]
  exact hcap.image continuous_snd

end Image

end ConvexAnalysis
