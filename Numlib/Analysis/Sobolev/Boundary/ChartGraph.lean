/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: beside `Numlib/Analysis/Sobolev/Chart.lean` (`Mathlib.Analysis.Distribution.Sobolev`);
the graph form of the implicit function theorem belongs in
`Mathlib.Analysis.Calculus.ImplicitContDiff`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Numlib.Analysis.Sobolev.Chart

/-!
# From local charts to local graphs: the chart ⇒ graph bridge

Two definitions of a `C^n` domain coexist in this library: Atkinson–Han's `IsContDiffDomain n Ω`
(`Numlib/Analysis/Sobolev/Domain.lean`: near every boundary point and after a rigid motion of the
coordinates, `Ω` is the region above the graph of a `C^n` function) and Brezis's
`IsContDiffChartDomain n Ω` (`Numlib/Analysis/Sobolev/Chart.lean`: every boundary point lies in the
range of a chart `H : Q → U` of class `C^n` with `H(Q₊) = U ∩ Ω`). The direction graph ⇒ chart is
elementary and is `IsContDiffDomain.isContDiffChartDomain` of `Chart.lean`; this file proves the
converse, `IsContDiffChartDomain.isContDiffDomain`, by the implicit function theorem, so that the
two definitions are equivalent (`isContDiffChartDomain_iff_isContDiffDomain`) for `1 ≤ n`,
`n ≠ ω`, and every chart domain inherits the boundary data (surface measure, outward normal,
divergence theorem, trace) built on the graph definition.

The proof: at a boundary point `x₀` with chart `(U, H, H⁻¹)`, the last coordinate
`Φ := (H⁻¹ ·)_N` is `C^n` on the open set `U`, `Ω ∩ U = {Φ > 0}` and `Φ x₀ = 0`; its derivative
at `x₀` is nonzero because `DH⁻¹(x₀)` is invertible with inverse `DH(H⁻¹ x₀)`
(`ContDiffChart.isInvertible_fderiv_invFun`, the chain rule on the two open sets). A rigid motion
`L` sends a unit vector `v` with `DΦ(x₀) v > 0` to `e_N`; in the rotated coordinates
`Ψ := Φ ∘ L⁻¹` has `∂_N Ψ > 0` near `L x₀`, and Mathlib's implicit function theorem
`ContDiffAt.implicitFunction` on `ℝ^d × ℝ` gives the graph function `g₀` of the zero set.
Since `Ψ` is strictly increasing along vertical lines where `∂_N Ψ > 0`
(`EuclideanSpace.lt_of_fderiv_single_last_pos`), `{Ψ > 0}` is the region *above* the graph in a
small ball; the implicit function theorem applied again at every point of the graph shows `g₀`
is `C^n` on a ball (this is what makes the case `n = ∞` work, where `ContDiffAt` at one point
gives no neighbourhood of regularity), and a smooth bump function extends `g₀` from that ball to
a globally `C^n` function `g`. This last step is why `n = ω` is excluded: an analytic graph
function on a ball need not extend analytically to all of `ℝ^d` (the unit disc is a chart domain
of class `C^ω` but not a `C^ω` graph domain).

## Main statements

* `ContDiffChart.isInvertible_fderiv_invFun`: the derivative of the inverse chart is invertible at
  every point of `U`;
* `EuclideanSpace.exists_linearIsometryEquiv_apply_eq_single_last`: a rigid motion sending a given
  unit vector to `e_N` (a reflection);
* `EuclideanSpace.exists_contDiff_forall_pos_iff_of_fderiv_single_last_pos`: the implicit function
  theorem in graph form — near a point where `Ψ = 0` and `∂_N Ψ > 0`, `{Ψ > 0}` is the region above
  the graph of a globally `C^n` function;
* `IsBoundaryGraphAt.of_contDiffAt_of_fderiv_ne_zero`: a regular level set is locally a graph after
  a rigid motion, in the shape of `IsBoundaryGraphAt`;
* `IsContDiffChartDomain.isContDiffDomain`, `isContDiffChartDomain_iff_isContDiffDomain`: the
  bridge and the equivalence of the two definitions.

## References

[brezis2011functional] §9.2 (the chart definition); Atkinson–Han, Definition 7.2.1 (the graph
definition).
-/

open Filter Set Topology

open scoped ContDiff

noncomputable section

variable {d : ℕ}

/-! ### Two general lemmas

Candidates for relocation: a scalar continuous linear map with `A 1 ≠ 0` is invertible, and a
nonzero functional is positive at some unit vector. -/

/-- A continuous linear map `ℝ →L[ℝ] ℝ` with `A 1 ≠ 0` is invertible: its inverse is
`(A 1)⁻¹ • id`. -/
theorem ContinuousLinearMap.isInvertible_of_apply_one_ne_zero (A : ℝ →L[ℝ] ℝ) (h : A 1 ≠ 0) :
    A.IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := (A 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    ?_ ?_
  · refine ContinuousLinearMap.ext_ring ?_
    simp [inv_mul_cancel₀ h]
  · refine ContinuousLinearMap.ext_ring ?_
    simp [inv_mul_cancel₀ h]

/-- A nonzero continuous linear functional is positive at some unit vector. -/
theorem ContinuousLinearMap.exists_norm_eq_one_and_pos_of_ne_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {L : F →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∃ v : F, ‖v‖ = 1 ∧ 0 < L v := by
  obtain ⟨x, hx⟩ : ∃ x, L x ≠ 0 := by
    by_contra h
    exact hL (ContinuousLinearMap.ext fun x ↦ by simpa using not_exists.1 h x)
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · refine ⟨‖x‖⁻¹ • (-x), ?_, ?_⟩
    · rw [norm_smul, norm_neg, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.2 hx0).ne']
    rw [map_smul, map_neg, smul_eq_mul]
    exact mul_pos (inv_pos.2 (norm_pos_iff.2 hx0)) (neg_pos.2 hneg)
  · refine ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx0, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact mul_pos (inv_pos.2 (norm_pos_iff.2 hx0)) hpos

/-! ### A rigid motion sending a unit vector to `e_N` -/

namespace EuclideanSpace

/-- **A rigid motion taking a unit vector to the last basis vector `e_N`**: the reflection across
the hyperplane orthogonal to `v - e_N` (the identity when `v = e_N`). -/
theorem exists_linearIsometryEquiv_apply_eq_single_last {v : EuclideanSpace ℝ (Fin (d + 1))}
    (hv : ‖v‖ = 1) :
    ∃ L : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)),
      L v = single (Fin.last d) 1 := by
  refine ⟨Submodule.reflection (ℝ ∙ (v - single (Fin.last d) 1))ᗮ, Submodule.reflection_sub ?_⟩
  simp [hv]

/-- **A rigid motion taking a unit vector to `e_N`**, as an affine isometry equivalence (linear,
`T 0 = 0`): the affine form of `exists_linearIsometryEquiv_apply_eq_single_last`, in the shape
`IsBoundaryGraphAt` carries. -/
theorem exists_affineIsometryEquiv_map_eq_single_last {v : EuclideanSpace ℝ (Fin (d + 1))}
    (hv : ‖v‖ = 1) :
    ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)),
      T 0 = 0 ∧ T.linearIsometryEquiv v = single (Fin.last d) 1 := by
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv_apply_eq_single_last hv
  exact ⟨L.toAffineIsometryEquiv, by simp, by simpa using hL⟩

/-! ### Monotonicity along the vertical lines of `ℝ^{d+1}`

The splitting `ℝ^{d+1} ≃ ℝ^d × ℝ` in the order the implicit function theorem wants
(`EuclideanSpace.initLastL`) and the vertical lines `t ↦ (x', t)` are in
`Numlib/Analysis/Sobolev/Chart.lean`. -/

/-- **Monotonicity along vertical lines**: on a convex set where `Ψ` is differentiable with
`∂_N Ψ > 0`, `Ψ` is strictly increasing along every vertical line `t ↦ (x', t)`. This is what
puts `{Ψ > 0}` *above* the zero set of `Ψ`. -/
theorem lt_of_fderiv_single_last_pos {Ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hs : Convex ℝ s)
    (hΨ : ∀ y ∈ s, DifferentiableAt ℝ Ψ y ∧ 0 < fderiv ℝ Ψ y (single (Fin.last d) 1))
    {x' : EuclideanSpace ℝ (Fin d)} {a b : ℝ} (ha : snocLast x' a ∈ s) (hb : snocLast x' b ∈ s)
    (hab : a < b) : Ψ (snocLast x' a) < Ψ (snocLast x' b) := by
  set D : Set ℝ := (fun t ↦ snocLast x' t) ⁻¹' s with hD
  have hDc : Convex ℝ D := by
    have : (fun t ↦ snocLast x' t) = AffineMap.lineMap (snocLast x' 0) (snocLast x' 1) :=
      funext (snocLast_eq_lineMap x')
    rw [hD, this]
    exact hs.affine_preimage _
  have hderiv : ∀ t ∈ D, HasDerivAt (fun t ↦ Ψ (snocLast x' t))
      (fderiv ℝ Ψ (snocLast x' t) (single (Fin.last d) 1)) t :=
    fun t ht ↦ (hΨ _ ht).1.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_snocLast x' t)
  have hmono : StrictMonoOn (fun t ↦ Ψ (snocLast x' t)) D := by
    refine strictMonoOn_of_deriv_pos hDc
      (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt) fun t ht ↦ ?_
    have ht' : t ∈ D := interior_subset ht
    rw [(hderiv t ht').deriv]
    exact (hΨ _ ht').2
  exact hmono ha hb hab

/-! ### The implicit function theorem in graph form -/

/-- **The implicit function theorem in graph form**: if `Ψ : ℝ^{d+1} → ℝ` is `C^n` on a
neighbourhood of `y₀` (`1 ≤ n`, `n ≠ ω`), vanishes at `y₀` and has `∂_N Ψ (y₀) > 0`, then there
are `ρ > 0` and a globally `C^n` function `g : ℝ^d → ℝ` such that, in the ball `B(y₀, ρ)`,
`{Ψ > 0}` is the region strictly above the graph of `g`: `0 < Ψ y ↔ g y' < y_N`.

Mathlib's `ContDiffAt.implicitFunction` on `ℝ^d × ℝ` gives the local graph function `g₀` of the
zero set; `lt_of_fderiv_single_last_pos` identifies `{Ψ > 0}` with the region above it in a ball
where `∂_N Ψ > 0`; the implicit function theorem at every point of the graph makes `g₀` `C^n` on
a ball around `y₀'` (needed for `n = ∞`, where `ContDiffAt` at a point gives no neighbourhood
of regularity); a smooth bump function then extends `g₀` from a smaller ball to all of `ℝ^d` —
the step that excludes `n = ω`. -/
theorem exists_contDiff_forall_pos_iff_of_fderiv_single_last_pos {n : WithTop ℕ∞} (h1n : 1 ≤ n)
    (hnω : n ≠ ω) {Ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {y₀ : EuclideanSpace ℝ (Fin (d + 1))}
    (hΨ : ∀ᶠ y in 𝓝 y₀, ContDiffAt ℝ n Ψ y) (hΨ₀ : Ψ y₀ = 0)
    (hΨ' : 0 < fderiv ℝ Ψ y₀ (single (Fin.last d) 1)) :
    ∃ ρ > 0, ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ n g ∧
      ∀ y ∈ Metric.ball y₀ ρ, (0 < Ψ y ↔ g (init y) < y (Fin.last d)) := by
  have hn : n ≠ 0 := by rintro rfl; simp at h1n
  -- the ball where `Ψ` is `C^n` with `∂_N Ψ > 0`
  have hev : ∀ᶠ y in 𝓝 y₀, ContDiffAt ℝ n Ψ y ∧ 0 < fderiv ℝ Ψ y (single (Fin.last d) 1) := by
    refine hΨ.and ?_
    have hc : ContinuousAt (fun y ↦ fderiv ℝ Ψ y (single (Fin.last d) 1)) y₀ :=
      (hΨ.self_of_nhds.continuousAt_fderiv hn).clm_apply continuousAt_const
    exact hc.eventually (lt_mem_nhds hΨ')
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set S := Metric.ball y₀ ρ₁ with hSdef
  have hSo : IsOpen S := Metric.isOpen_ball
  have hy₀S : y₀ ∈ S := Metric.mem_ball_self hρ₁
  have hS : ∀ y ∈ S, DifferentiableAt ℝ Ψ y ∧ 0 < fderiv ℝ Ψ y (single (Fin.last d) 1) :=
    fun y hy ↦ ⟨(hball₁ y hy).1.differentiableAt hn, (hball₁ y hy).2⟩
  -- the implicit equation on `ℝ^d × ℝ`
  set f : EuclideanSpace ℝ (Fin d) × ℝ → ℝ := Ψ ∘ (initLastL d).symm with hfdef
  have hfapp : ∀ u, f u = Ψ (snocLast u.1 u.2) := fun u ↦ rfl
  have hcdf : ∀ u : EuclideanSpace ℝ (Fin d) × ℝ, (initLastL d).symm u ∈ S →
      ContDiffAt ℝ n f u :=
    fun u hu ↦ (hball₁ _ hu).1.comp u (initLastL d).symm.contDiff.contDiffAt
  have hif : ∀ u : EuclideanSpace ℝ (Fin d) × ℝ, (initLastL d).symm u ∈ S →
      (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin d)) ℝ).IsInvertible := by
    intro u hu
    refine ContinuousLinearMap.isInvertible_of_apply_one_ne_zero _ ?_
    rw [hfdef, (initLastL d).symm.comp_right_fderiv]
    simpa [snocLast_zero_one] using (hS _ hu).2.ne'
  -- the implicit function at `y₀`
  set u₀ : EuclideanSpace ℝ (Fin d) × ℝ := (init y₀, y₀ (Fin.last d)) with hu₀def
  have hu₀S : (initLastL d).symm u₀ ∈ S := by simpa [hu₀def] using hy₀S
  set g₀ := (hcdf u₀ hu₀S).implicitFunction hn (hif u₀ hu₀S) with hg₀def
  have hg₀c : ContinuousAt g₀ (init y₀) :=
    ((hcdf u₀ hu₀S).contDiffAt_implicitFunction hn (hif u₀ hu₀S)).continuousAt
  have hg₀₀ : g₀ (init y₀) = y₀ (Fin.last d) :=
    (hcdf u₀ hu₀S).implicitFunction_apply_self hn (hif u₀ hu₀S)
  have hg₀z : ∀ᶠ x' in 𝓝 (init y₀), Ψ (snocLast x' (g₀ x')) = 0 := by
    have := (hcdf u₀ hu₀S).eventually_apply_implicitFunction hn (hif u₀ hu₀S)
    refine this.mono fun x' hx' ↦ ?_
    rw [hfapp, hfapp] at hx'
    simpa [hu₀def, hΨ₀] using hx'
  have hg₀S : ∀ᶠ x' in 𝓝 (init y₀), snocLast x' (g₀ x') ∈ S := by
    have ht : Tendsto (fun x' ↦ snocLast x' (g₀ x')) (𝓝 (init y₀))
        (𝓝 (snocLast (init y₀) (g₀ (init y₀)))) :=
      continuous_snocLast.continuousAt.tendsto.comp (continuousAt_id.prodMk hg₀c)
    rw [hg₀₀, snocLast_init_last] at ht
    exact ht.eventually_mem (hSo.mem_nhds hy₀S)
  obtain ⟨ρ', hρ', hball'⟩ := Metric.eventually_nhds_iff_ball.1 (hg₀z.and hg₀S)
  -- the characterization of `{Ψ > 0}` and `{Ψ = 0}` on the box
  have hbox : ∀ y ∈ S, init y ∈ Metric.ball (init y₀) ρ' →
      (0 < Ψ y ↔ g₀ (init y) < y (Fin.last d)) ∧ (Ψ y = 0 ↔ g₀ (init y) = y (Fin.last d)) := by
    intro y hyS hy'
    obtain ⟨hz, hzS⟩ := hball' _ hy'
    have hy : snocLast (init y) (y (Fin.last d)) = y := snocLast_init_last y
    have hyS' : snocLast (init y) (y (Fin.last d)) ∈ S := by rw [hy]; exact hyS
    rcases lt_trichotomy (g₀ (init y)) (y (Fin.last d)) with hlt | heq | hgt
    · have := lt_of_fderiv_single_last_pos (convex_ball y₀ ρ₁) hS hzS hyS' hlt
      rw [hz, hy] at this
      exact ⟨⟨fun _ ↦ hlt, fun _ ↦ this⟩, ⟨fun h ↦ absurd h this.ne', fun h ↦ absurd h hlt.ne⟩⟩
    · have : Ψ y = 0 := by rw [← hy, ← heq, hz]
      exact ⟨⟨fun h ↦ absurd this h.ne', fun h ↦ absurd heq h.ne⟩, ⟨fun _ ↦ heq, fun _ ↦ this⟩⟩
    · have := lt_of_fderiv_single_last_pos (convex_ball y₀ ρ₁) hS hyS' hzS hgt
      rw [hz, hy] at this
      exact ⟨⟨fun h ↦ absurd h (not_lt.2 this.le), fun h ↦ absurd h (not_lt.2 hgt.le)⟩,
        ⟨fun h ↦ absurd h this.ne, fun h ↦ absurd h hgt.ne'⟩⟩
  -- `g₀` is `C^n` on the ball: the implicit function theorem at every point of the graph
  have hg₀d : ∀ x' ∈ Metric.ball (init y₀) ρ', ContDiffAt ℝ n g₀ x' := by
    intro x' hx'
    obtain ⟨hz, hzS⟩ := hball' _ hx'
    set u₁ : EuclideanSpace ℝ (Fin d) × ℝ := (x', g₀ x') with hu₁def
    have hu₁S : (initLastL d).symm u₁ ∈ S := hzS
    set g₁ := (hcdf u₁ hu₁S).implicitFunction hn (hif u₁ hu₁S) with hg₁def
    have hg₁d : ContDiffAt ℝ n g₁ x' :=
      (hcdf u₁ hu₁S).contDiffAt_implicitFunction hn (hif u₁ hu₁S)
    have hg₁₀ : g₁ x' = g₀ x' := (hcdf u₁ hu₁S).implicitFunction_apply_self hn (hif u₁ hu₁S)
    have hg₁z : ∀ᶠ z in 𝓝 x', Ψ (snocLast z (g₁ z)) = 0 := by
      have := (hcdf u₁ hu₁S).eventually_apply_implicitFunction hn (hif u₁ hu₁S)
      refine this.mono fun z hz' ↦ ?_
      rw [hfapp, hfapp] at hz'
      simpa [hu₁def, hz] using hz'
    have hg₁S : ∀ᶠ z in 𝓝 x', snocLast z (g₁ z) ∈ S := by
      have ht : Tendsto (fun z ↦ snocLast z (g₁ z)) (𝓝 x') (𝓝 (snocLast x' (g₁ x'))) :=
        continuous_snocLast.continuousAt.tendsto.comp (continuousAt_id.prodMk hg₁d.continuousAt)
      rw [hg₁₀] at ht
      exact ht.eventually_mem (hSo.mem_nhds hzS)
    have hzb : ∀ᶠ z in 𝓝 x', z ∈ Metric.ball (init y₀) ρ' := Metric.isOpen_ball.eventually_mem hx'
    refine hg₁d.congr_of_eventuallyEq ?_
    filter_upwards [hg₁z, hg₁S, hzb] with z hz1 hz2 hz3
    have := ((hbox _ hz2 (by simpa using hz3)).2).1 (by simpa using hz1)
    simpa using this
  -- globalize by a bump function
  obtain ⟨m, rfl⟩ : ∃ m : ℕ∞, n = m := by
    rcases n with _ | m
    · exact absurd rfl hnω
    · exact ⟨m, rfl⟩
  let χ : ContDiffBump (init y₀) := ⟨ρ' / 3, ρ' / 2, by positivity, by linarith⟩
  set g : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x' ↦ y₀ (Fin.last d) + χ x' * (g₀ x' - y₀ (Fin.last d)) with hgdef
  have hg : ContDiff ℝ m g := by
    refine contDiff_iff_contDiffAt.2 fun x' ↦ ?_
    by_cases hx' : x' ∈ Metric.ball (init y₀) ρ'
    · exact contDiffAt_const.add (χ.contDiffAt.mul ((hg₀d x' hx').sub contDiffAt_const))
    · have hχ : χ =ᶠ[𝓝 x'] 0 := by
        rw [← notMem_tsupport_iff_eventuallyEq, χ.tsupport_eq]
        intro h
        exact hx' (Metric.closedBall_subset_ball (show ρ' / 2 < ρ' by linarith) h)
      refine (contDiffAt_const (c := y₀ (Fin.last d))).congr_of_eventuallyEq ?_
      filter_upwards [hχ] with z hz
      simp [hgdef, hz]
  have hgeq : ∀ x' ∈ Metric.ball (init y₀) (ρ' / 3), g x' = g₀ x' := fun x' hx' ↦ by
    simp [hgdef, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx')]
  refine ⟨min ρ₁ (ρ' / 3), lt_min hρ₁ (by positivity), g, hg, fun y hy ↦ ?_⟩
  have hyS : y ∈ S := Metric.ball_subset_ball (min_le_left _ _) hy
  have hy' : init y ∈ Metric.ball (init y₀) (ρ' / 3) :=
    lt_of_le_of_lt (dist_init_le y y₀) (lt_of_lt_of_le hy (min_le_right _ _))
  rw [hgeq _ hy']
  exact (hbox y hyS (Metric.ball_subset_ball (by linarith) hy')).1

end EuclideanSpace

/-! ### A regular level set is locally a graph -/

section LevelSet

open EuclideanSpace

variable {n : WithTop ℕ∞} {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **A regular level set is locally a graph**, in the shape of `IsBoundaryGraphAt`: for
`1 ≤ n`, `n ≠ ω`, a neighbourhood `V` of `x₀` and `Φ : ℝ^{d+1} → ℝ` which is `C^n` on a
neighbourhood of `x₀`, with `Φ x₀ = 0`, `DΦ(x₀) ≠ 0` and `Ω ∩ V = {x ∈ V | 0 < Φ x}`, there is
`r > 0` with `IsBoundaryGraphAt {g | ContDiff ℝ n g} Ω x₀ r`: after the rigid motion sending a
unit vector `v` with `DΦ(x₀) v > 0` to `e_N`
(`EuclideanSpace.exists_linearIsometryEquiv_apply_eq_single_last`), the implicit function theorem
in graph form (`EuclideanSpace.exists_contDiff_forall_pos_iff_of_fderiv_single_last_pos`) applies
to `Ψ := Φ ∘ L⁻¹` at `L x₀`.

The regularity hypothesis is on a neighbourhood because `ContDiffAt ℝ ∞ Φ x₀` alone gives no
neighbourhood on which `Φ` is `C^∞` (for `n ≠ ∞` the two are equivalent, `ContDiffAt.eventually`);
`n ≠ ω` because the graph function is globalized by a bump function. -/
theorem IsBoundaryGraphAt.of_contDiffAt_of_fderiv_ne_zero (h1n : 1 ≤ n) (hnω : n ≠ ω)
    {V : Set (EuclideanSpace ℝ (Fin (d + 1)))} {x₀ : EuclideanSpace ℝ (Fin (d + 1))}
    {Φ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hV : V ∈ 𝓝 x₀)
    (hΦ : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ n Φ x) (hΦ₀ : Φ x₀ = 0) (hΦ' : fderiv ℝ Φ x₀ ≠ 0)
    (hΩ : Ω ∩ V = {x ∈ V | 0 < Φ x}) :
    ∃ r > 0, IsBoundaryGraphAt {g | ContDiff ℝ n g} Ω x₀ r := by
  have hΩ' : ∀ x ∈ V, (x ∈ Ω ↔ 0 < Φ x) := fun x hx ↦ by
    have := Set.ext_iff.1 hΩ x
    simpa [hx] using this
  obtain ⟨v, hv1, hv⟩ := ContinuousLinearMap.exists_norm_eq_one_and_pos_of_ne_zero hΦ'
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv_apply_eq_single_last hv1
  set Ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ := Φ ∘ L.symm with hΨdef
  have hΨ : ∀ᶠ y in 𝓝 (L x₀), ContDiffAt ℝ n Ψ y := by
    have h : ∀ᶠ y in 𝓝 (L x₀), ContDiffAt ℝ n Φ (L.symm y) := by
      have h := L.symm.continuous.tendsto (L x₀)
      rw [L.symm_apply_apply] at h
      exact h.eventually hΦ
    exact h.mono fun y hy ↦ hy.comp y L.symm.contDiff.contDiffAt
  have hΨ₀ : Ψ (L x₀) = 0 := by simp [hΨdef, hΦ₀]
  have hΨ' : 0 < fderiv ℝ Ψ (L x₀) (single (Fin.last d) 1) := by
    have : fderiv ℝ Ψ (L x₀) = fderiv ℝ Φ x₀ ∘L
        (L.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] _) := by
      rw [hΨdef, ← L.symm.coe_toContinuousLinearEquiv,
        L.symm.toContinuousLinearEquiv.comp_right_fderiv]
      simp
    rw [this]
    simpa [← hL] using hv
  obtain ⟨ρ, hρ, g, hg, hgraph⟩ :=
    exists_contDiff_forall_pos_iff_of_fderiv_single_last_pos h1n hnω hΨ hΨ₀ hΨ'
  obtain ⟨r₀, hr₀, hr₀V⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨min r₀ ρ, lt_min hr₀ hρ, L.toAffineIsometryEquiv, g, hg, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  constructor
  · rintro ⟨hxΩ, hxb⟩
    refine ⟨hxb, ?_⟩
    have hxV : x ∈ V := hr₀V (Metric.ball_subset_ball (min_le_left _ _) hxb)
    have hLx : L x ∈ Metric.ball (L x₀) ρ := by
      rw [Metric.mem_ball, L.dist_map]
      exact lt_of_lt_of_le hxb (min_le_right _ _)
    exact (hgraph _ hLx).1 (by simpa [hΨdef] using (hΩ' x hxV).1 hxΩ)
  · rintro ⟨hxb, hlt⟩
    refine ⟨?_, hxb⟩
    have hxV : x ∈ V := hr₀V (Metric.ball_subset_ball (min_le_left _ _) hxb)
    have hLx : L x ∈ Metric.ball (L x₀) ρ := by
      rw [Metric.mem_ball, L.dist_map]
      exact lt_of_lt_of_le hxb (min_le_right _ _)
    exact (hΩ' x hxV).2 (by simpa [hΨdef] using (hgraph _ hLx).2 hlt)

end LevelSet

/-! ### The derivative of the inverse chart -/

namespace ContDiffChart

variable {n : WithTop ℕ∞} {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} (c : ContDiffChart n Ω)

/-- The inverse chart `H⁻¹ ∈ C^n(Ū)` is `C^n` at every point of the open set `U`. -/
theorem contDiffAt_invFun {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ c.U) :
    ContDiffAt ℝ n c.invFun x :=
  (c.contDiffOn_invFun.mono subset_closure).contDiffAt (c.isOpen_U.mem_nhds hx)

/-- The chart `H ∈ C^n(Q̄)` is `C^n` at every point of the open cylinder `Q`. -/
theorem contDiffAt_toFun {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y ∈ unitChartCube d) :
    ContDiffAt ℝ n c.toFun y :=
  (c.contDiffOn.mono subset_closure).contDiffAt (isOpen_unitChartCube.mem_nhds hy)

/-- The chain rule for `H ∘ H⁻¹ = id` on the open set `U`: `DH(H⁻¹ x) ∘ DH⁻¹(x) = id`. -/
theorem fderiv_toFun_comp_fderiv_invFun (h1n : 1 ≤ n) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x ∈ c.U) :
    fderiv ℝ c.toFun (c.invFun x) ∘L fderiv ℝ c.invFun x = ContinuousLinearMap.id ℝ _ := by
  have hn : n ≠ 0 := by rintro rfl; simp at h1n
  have h1 : DifferentiableAt ℝ c.invFun x := (c.contDiffAt_invFun hx).differentiableAt hn
  have h2 : DifferentiableAt ℝ c.toFun (c.invFun x) :=
    (c.contDiffAt_toFun (c.mapsTo_invFun hx)).differentiableAt hn
  have hcomp : c.toFun ∘ c.invFun =ᶠ[𝓝 x] id :=
    (c.isOpen_U.eventually_mem hx).mono fun y hy ↦ c.toFun_invFun hy
  rw [← fderiv_comp x h2 h1, hcomp.fderiv_eq, fderiv_id]

/-- The chain rule for `H⁻¹ ∘ H = id` on the open cylinder `Q`, read at `H⁻¹ x` for `x ∈ U`:
`DH⁻¹(x) ∘ DH(H⁻¹ x) = id`. -/
theorem fderiv_invFun_comp_fderiv_toFun (h1n : 1 ≤ n) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x ∈ c.U) :
    fderiv ℝ c.invFun x ∘L fderiv ℝ c.toFun (c.invFun x) = ContinuousLinearMap.id ℝ _ := by
  have hn : n ≠ 0 := by rintro rfl; simp at h1n
  have hy : c.invFun x ∈ unitChartCube d := c.mapsTo_invFun hx
  have h1 : DifferentiableAt ℝ c.toFun (c.invFun x) :=
    (c.contDiffAt_toFun hy).differentiableAt hn
  have h2 : DifferentiableAt ℝ c.invFun (c.toFun (c.invFun x)) := by
    rw [c.toFun_invFun hx]
    exact (c.contDiffAt_invFun hx).differentiableAt hn
  have hcomp : c.invFun ∘ c.toFun =ᶠ[𝓝 (c.invFun x)] id :=
    (isOpen_unitChartCube.eventually_mem hy).mono fun y hy ↦ c.invFun_toFun hy
  have := fderiv_comp (c.invFun x) h2 h1
  rw [hcomp.fderiv_eq, fderiv_id, c.toFun_invFun hx] at this
  exact this.symm

/-- **The derivative of the inverse chart is invertible** at every point of `U`, for `1 ≤ n`:
its inverse is `DH(H⁻¹ x)`, by the chain rule on `H ∘ H⁻¹ = id` (on `U`) and `H⁻¹ ∘ H = id`
(on `Q`). -/
theorem isInvertible_fderiv_invFun (h1n : 1 ≤ n) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x ∈ c.U) : (fderiv ℝ c.invFun x).IsInvertible :=
  .of_inverse (c.fderiv_invFun_comp_fderiv_toFun h1n hx)
    (c.fderiv_toFun_comp_fderiv_invFun h1n hx)

/-- **The last coordinate of the inverse chart has nonzero derivative** at every point of `U`,
for `1 ≤ n`: `DH⁻¹(x)` is surjective, so some direction is sent to `e_N`. -/
theorem fderiv_invFun_last_ne_zero (h1n : 1 ≤ n) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x ∈ c.U) :
    fderiv ℝ (fun y ↦ c.invFun y (Fin.last d)) x ≠ 0 := by
  have hn : n ≠ 0 := by rintro rfl; simp at h1n
  have hd : DifferentiableAt ℝ c.invFun x := (c.contDiffAt_invFun hx).differentiableAt hn
  have hf : fderiv ℝ (fun y ↦ c.invFun y (Fin.last d)) x =
      EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d) ∘L fderiv ℝ c.invFun x := by
    change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d) ∘ c.invFun) x = _
    rw [fderiv_comp x (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).differentiableAt hd,
      ContinuousLinearMap.fderiv]
  intro h0
  obtain ⟨v, hv⟩ :=
    (c.isInvertible_fderiv_invFun h1n hx).surjective (EuclideanSpace.single (Fin.last d) 1)
  have := congrArg (fun A : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] ℝ ↦ A v) h0
  simp [hf, hv] at this

end ContDiffChart

/-! ### Chart ⇒ graph -/

section Bridge

variable {n : WithTop ℕ∞} {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Chart ⇒ graph**: an open set of class `C^n` by local charts in the sense of
[brezis2011functional] §9.2 (`IsContDiffChartDomain`) is a `C^n` domain in the graph sense of
Atkinson–Han, Definition 7.2.1 (`IsContDiffDomain`), for `1 ≤ n`, `n ≠ ω`. At a boundary point
`x₀` with chart `(U, H, H⁻¹)`, the last coordinate `Φ := (H⁻¹ ·)_N` is `C^n` on `U`, vanishes
at `x₀` (`x₀ ∈ ∂Ω`, `ContDiffChart.invFun_mem_zero_iff`), has nonzero derivative
(`ContDiffChart.fderiv_invFun_last_ne_zero`) and `Ω ∩ U = {Φ > 0}`
(`ContDiffChart.invFun_mem_pos_iff`), so `IsBoundaryGraphAt.of_contDiffAt_of_fderiv_ne_zero`
gives the graph chart. Together with `IsContDiffDomain.isContDiffChartDomain` of `Chart.lean`,
the two definitions are equivalent (`isContDiffChartDomain_iff_isContDiffDomain`).

The exclusion of `n = ω` is genuine: the unit disc of `ℝ²` is a chart domain of class `C^ω`
(polar coordinates), but no rigid motion makes its boundary the graph of a function analytic on
the whole line. -/
theorem IsContDiffChartDomain.isContDiffDomain (h : IsContDiffChartDomain n Ω) (h1n : 1 ≤ n)
    (hnω : n ≠ ω) : IsContDiffDomain n Ω := by
  refine ⟨h.isOpen, fun x₀ hx₀ ↦ ?_⟩
  obtain ⟨c, hx₀U⟩ := h.exists_chart hx₀
  set Φ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ := fun x ↦ c.invFun x (Fin.last d) with hΦdef
  have hΦ : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ n Φ x :=
    (c.isOpen_U.eventually_mem hx₀U).mono fun x hx ↦
      (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).contDiff.contDiffAt.comp x
        (c.contDiffAt_invFun hx)
  have hΦ₀ : Φ x₀ = 0 := ((c.invFun_mem_zero_iff hx₀U).2 hx₀).2
  have hΦ' : fderiv ℝ Φ x₀ ≠ 0 := c.fderiv_invFun_last_ne_zero h1n hx₀U
  have hΩ : Ω ∩ c.U = {x ∈ c.U | 0 < Φ x} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hxΩ, hxU⟩
      exact ⟨hxU, ((c.invFun_mem_pos_iff hxU).2 hxΩ).2⟩
    · rintro ⟨hxU, hpos⟩
      exact ⟨(c.invFun_mem_pos_iff hxU).1 ⟨c.mapsTo_invFun hxU, hpos⟩, hxU⟩
  exact IsBoundaryGraphAt.of_contDiffAt_of_fderiv_ne_zero h1n hnω (c.isOpen_U.mem_nhds hx₀U) hΦ
    hΦ₀ hΦ' hΩ

/-- **The two definitions of a `C^n` domain agree** for `1 ≤ n`, `n ≠ ω`: Brezis's by local
charts (`IsContDiffChartDomain`) and Atkinson–Han's by local graphs (`IsContDiffDomain`). -/
theorem isContDiffChartDomain_iff_isContDiffDomain (h1n : 1 ≤ n) (hnω : n ≠ ω) :
    IsContDiffChartDomain n Ω ↔ IsContDiffDomain n Ω :=
  ⟨fun h ↦ h.isContDiffDomain h1n hnω, fun h ↦ h.isContDiffChartDomain⟩

end Bridge

end
