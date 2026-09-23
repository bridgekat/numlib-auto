import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Convex.Recession.Function

/-!
# Continuity of a convex function on the relative interior of its domain

A proper convex function on a finite-dimensional space is continuous, relative to the affine hull
of its effective domain, at every relative interior point of that domain. Mathlib proves this for
a real-valued `ConvexOn ℝ C f` as `ConvexOn.continuousOn_intrinsicInterior` (and its local
Lipschitz form `ConvexOn.locallyLipschitzOn_intrinsicInterior`); this file transports it to the
`EReal`-valued `ConvexFn` through the real trace `(f x).toReal`, and supplies the quantitative
refinements: Lipschitz continuity on compact subsets of `ri (dom f)` with an explicit constant, and
uniform continuity on the whole space. The Lipschitz constants are carried from the interior case
to the relative one by an explicit linear *chart* of the affine hull, which is also what
`Convergence.lean` uses to pass its equi-Lipschitz and convergence theorems from open convex sets
to relative interiors.

## Main results

* `relint_eq_vadd_image_interior` — the *chart*: `ri C = x₀ + ι (int D)`, where `D` is the trace of
  `C` on a subspace `V` spanned by `C - x₀`. This is the reduction "relative interior = interior in
  the affine hull", carried out in a linear chart rather than in the affine hull itself, so that
  `Convex` and `ConvexOn` — which need a module, not a torsor — still apply.
* `exists_chart_retraction` — the chart packaged with a *continuous linear* retraction, which is
  what carries Lipschitz constants back from the chart to `E`.
* `ConvexFn.continuousOn_toReal_relint_convexDom`, `ConvexFn.continuousOn_relint_convexDom` —
  continuity on `ri (dom f)`, in the real-valued and the `EReal`-valued form, from Mathlib's
  `ConvexOn.continuousOn_intrinsicInterior`; `ConvexFn.continuous_of_convexDom_eq_univ` is the
  everywhere-finite case.
* `ConvexOn.lipschitzOnWith_of_abs_le_of_cthickening_subset`,
  `ConvexOn.exists_lipschitzOnWith_of_isCompact`, `ConvexFn.exists_lipschitzOnWith_of_isCompact` —
  Lipschitz continuity on compact subsets: the quantitative form with the constant `2M/ε`
  exhibited (which is what equi-Lipschitz statements need, and which needs no
  finite-dimensionality), then the `interior` and the `ri` form.
* `ConvexFn.uniformContinuous_toReal_iff` — uniform continuity on the whole space, with
  `ConvexFn.exists_lipschitzWith_of_recessionFn_ne_top` as its quantitative half and
  `ConvexFn.exists_lipschitzWith_of_frequently_le`, `ConvexFn.exists_lipschitzWith_of_le_lipschitz`
  as two easily checked sufficient conditions.
* `intrinsicInterior_vadd` — translation invariance of `ri`, which the chart needs and which
  Mathlib does not state.
* `ConvexOn.continuous_of_lowerSemicontinuous` — outside the finite-dimensional theory: a
  real-valued convex lower semicontinuous function on a Banach space is continuous, by Baire's
  theorem. It lives at the end of this file, outside the `ConvexAnalysis` namespace.

## Implementation notes

The chart is a linear subspace, not the affine hull. `intrinsicInterior ℝ C` is defined as the
interior taken inside `↥(affineSpan ℝ C)`, but that subtype is an `AddTorsor`, while `Convex`,
`ConvexOn` and every Mathlib continuity theorem need a *module*; fixing `x₀ ∈ C` and moving to a
subspace `V` spanned by `C - x₀` costs one translation and buys the whole module API. The subspace
is a parameter rather than a definition — every lemma takes `V` with `hV : V = span ℝ (C - x₀)` —
so that instance synthesis for `↥V` never has to unfold a `Submodule.span`; callers obtain an
opaque `V` from `⟨_, rfl⟩`. Transporting continuity back to `E` uses a continuous left inverse
rather than the embedding, which finite-dimensionality supplies through
`LinearMap.linearProjOfIsCompl`.

## A real-valued convex lower semicontinuous function on a Banach space is continuous

`ConvexOn.continuous_of_lowerSemicontinuous`: a function `f : E → ℝ` on a complete real normed
space that is convex and lower semicontinuous *and finite everywhere* is continuous, hence locally
Lipschitz.

The point is that finiteness does the work of a local upper bound.  The sublevel sets `{f ≤ n}` are
closed, by lower semicontinuity, and cover `E`, because `f` is real-valued; Baire's theorem gives
one of them a nonempty interior, so `f` is bounded above near some point, and a convex function
bounded above near one point is continuous everywhere — that last implication is Mathlib's
`ConvexOn.continuousOn_tfae`.

Completeness is what makes the space a Baire space and is the only role it plays; the statement
holds verbatim over any barrelled space.  Without finiteness the conclusion fails at once: an
extended-real convex lower semicontinuous function jumps to `+∞` off its domain.

This is why the hypothesis "`j : V → ℝ` is convex and lower semicontinuous", standard in the theory
of elliptic variational inequalities, silently provides the continuity of `j` that convergence
proofs for their numerical approximation need; see [han2009theoretical], Chapter 11.

## References

* [rockafellar1970convex] §10.
-/

open Pointwise Set
open scoped NNReal

namespace ConvexAnalysis

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x₀ : E} {V : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
/-- The relative interior is translation invariant. -/
theorem intrinsicInterior_vadd (v : E) (s : Set E) : ri (v +ᵥ s) = v +ᵥ ri s := by
  have h : ∀ t : Set E, v +ᵥ t = (AffineIsometryEquiv.constVAdd ℝ E v).toAffineIsometry '' t :=
    fun t => by rw [← Set.image_vadd]; rfl
  rw [h, h, AffineIsometry.intrinsicInterior_image]

/-- The **chart** of `C` at `x₀` in a subspace `V`: the directions `z ∈ V` with `x₀ + z ∈ C`. -/
def chart (C : Set E) (x₀ : E) (V : Submodule ℝ E) : Set V := {z | x₀ + (z : E) ∈ C}

omit [FiniteDimensional ℝ E] in
@[simp] theorem mem_chart {z : V} : z ∈ chart C x₀ V ↔ x₀ + (z : E) ∈ C := Iff.rfl

omit [FiniteDimensional ℝ E] in
/-- The chart maps onto the translate `C - x₀`. -/
theorem image_chart (hV : V = Submodule.span ℝ ((fun x => x - x₀) '' C)) :
    V.subtype '' chart C x₀ V = (fun x => x - x₀) '' C := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨x₀ + (z : E), hz, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x - x₀, hV ▸ Submodule.subset_span ⟨x, hx, rfl⟩⟩, ?_, rfl⟩
    change x₀ + (x - x₀) ∈ C
    rwa [add_sub_cancel]

omit [FiniteDimensional ℝ E] in
theorem zero_mem_chart (hx₀ : x₀ ∈ C) : (0 : V) ∈ chart C x₀ V := by
  change x₀ + ((0 : V) : E) ∈ C
  simpa using hx₀

omit [FiniteDimensional ℝ E] in
theorem convex_chart (hC : Convex ℝ C) : Convex ℝ (chart C x₀ V) := by
  intro z hz w hw a b ha hb hab
  change x₀ + ((a • z + b • w : V) : E) ∈ C
  have hsplit : x₀ + ((a • z + b • w : V) : E)
      = a • (x₀ + (z : E)) + b • (x₀ + (w : E)) := by
    push_cast
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  rw [hsplit]
  exact hC hz hw ha hb hab

omit [FiniteDimensional ℝ E] in
/-- The chart affinely spans the chart space: that is what makes `ri` collapse to `interior`
there. -/
theorem affineSpan_chart (hx₀ : x₀ ∈ C)
    (hV : V = Submodule.span ℝ ((fun x => x - x₀) '' C)) :
    affineSpan ℝ (chart C x₀ V) = ⊤ := by
  have h0 : (0 : V) ∈ chart C x₀ V := zero_mem_chart hx₀
  have hspan : Submodule.span ℝ (chart C x₀ V) = ⊤ := by
    refine Submodule.map_injective_of_injective V.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, image_chart hV, ← hV]
  have hvs : vectorSpan ℝ (chart C x₀ V) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun z hz => ?_
    have hmem := vsub_mem_vectorSpan ℝ hz h0
    simpa using hmem
  exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ V V ⟨0, h0⟩).2 hvs

/-- **The relative interior, computed in the chart.** `ri C` is the translate by `x₀` of the image
of the ordinary interior of `chart C x₀ V`. -/
theorem relint_eq_vadd_image_interior (hC : Convex ℝ C) (hx₀ : x₀ ∈ C)
    (hV : V = Submodule.span ℝ ((fun x => x - x₀) '' C)) :
    ri C = x₀ +ᵥ (V.subtype '' interior (chart C x₀ V)) := by
  have htrans : (fun x => x - x₀) '' C = (-x₀) +ᵥ C := by
    rw [← Set.image_vadd]
    exact Set.image_congr' fun x => sub_eq_neg_add x x₀
  have hstep : ri ((-x₀) +ᵥ C) = V.subtype '' interior (chart C x₀ V) := by
    have h2 : ri (chart C x₀ V) = interior (chart C x₀ V) :=
      intrinsicInterior_eq_interior (affineSpan_chart hx₀ hV)
    have h1 : ri (V.subtype '' chart C x₀ V) = V.subtype '' ri (chart C x₀ V) :=
      Convex.relint_image (convex_chart hC) V.subtype
    rw [image_chart hV, htrans, h2] at h1
    exact h1
  rw [← hstep, intrinsicInterior_vadd, vadd_vadd, add_neg_cancel, zero_vadd]

/-- **The chart, packaged for reuse.** For a convex `C` and a point `x₀ ∈ C` there is a subspace `V`
and a *continuous linear retraction* `r : E →L[ℝ] V` such that `x ↦ r (x - x₀)` carries `ri C` into
`interior (chart C x₀ V)` and `x₀ + r (x - x₀) = x` there, together with the chart identity
`relint_eq_vadd_image_interior` for that `V`. Continuity transports along `r` because `r` is
continuous, and Lipschitz constants because `r` is *bounded*. -/
theorem exists_chart_retraction (hC : Convex ℝ C) (hx₀ : x₀ ∈ C) :
    ∃ (V : Submodule ℝ E) (r : E →L[ℝ] V),
      ri C = x₀ +ᵥ (V.subtype '' interior (chart C x₀ V)) ∧
      Set.MapsTo (fun x : E => r (x - x₀)) (ri C) (interior (chart C x₀ V)) ∧
      ∀ x ∈ ri C, x₀ + ((r (x - x₀) : V) : E) = x := by
  obtain ⟨V, hV⟩ : ∃ V : Submodule ℝ E, V = Submodule.span ℝ ((fun x => x - x₀) '' C) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  have hW' : IsCompl (LinearMap.range V.subtype) W := by rwa [Submodule.range_subtype]
  have hrz : ∀ z : V,
      (LinearMap.linearProjOfIsCompl W V.subtype V.injective_subtype hW') (z : E) = z := fun z =>
    LinearMap.linearProjOfIsCompl_apply_left W V.subtype V.injective_subtype hW' z
  have himg := relint_eq_vadd_image_interior hC hx₀ hV
  refine ⟨V, LinearMap.toContinuousLinearMap
    (LinearMap.linearProjOfIsCompl W V.subtype V.injective_subtype hW'), himg, ?_, ?_⟩
  · intro x hx
    rw [himg] at hx
    obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hx
    simpa [hrz z] using hz
  · intro x hx
    rw [himg] at hx
    obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hx
    simp [hrz z]

end Chart

section Relint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- The real-valued restriction of `f` is convex on `dom f`, in Mathlib's sense. -/
theorem ConvexFn.convexOn_toReal_convexDom (hf : ConvexFn f) (hp : ProperConvex f) :
    ConvexOn ℝ (convexDom f) fun x => (f x).toReal := by
  rw [convexOn_iff_convexFn]
  have hrestrict : convexRestrict (convexDom f) (fun x => (((f x).toReal : ℝ) : EReal)) = f := by
    funext x
    by_cases hx : x ∈ convexDom f
    · rw [convexRestrict_of_mem hx]
      exact EReal.coe_toReal (mem_convexDom.1 hx).ne (hp.ne_bot x)
    · rw [convexRestrict_of_notMem hx]
      exact (top_le_iff.1 (not_lt.1 hx)).symm
  rwa [hrestrict]

/-- **A proper convex function is continuous, relative to the affine hull of its domain, at every
relative interior point** — real-valued form: Mathlib's `ConvexOn.continuousOn_intrinsicInterior`
applied to the real trace of `f` on `dom f`. -/
theorem ConvexFn.continuousOn_toReal_relint_convexDom (hf : ConvexFn f) (hp : ProperConvex f) :
    ContinuousOn (fun x => (f x).toReal) (ri (convexDom f)) :=
  (hf.convexOn_toReal_convexDom hp).continuousOn_intrinsicInterior

/-- **A proper convex function on a finite-dimensional space is continuous on `ri (dom f)`**,
relative to the affine hull of its effective domain. -/
theorem ConvexFn.continuousOn_relint_convexDom (hf : ConvexFn f) (hp : ProperConvex f) :
    ContinuousOn f (ri (convexDom f)) := by
  have hcoe : Set.EqOn f (fun x => (((f x).toReal : ℝ) : EReal)) (ri (convexDom f)) := by
    intro x hx
    have hx' : x ∈ convexDom f := intrinsicInterior_subset hx
    exact (EReal.coe_toReal (mem_convexDom.1 hx').ne (hp.ne_bot x)).symm
  exact ContinuousOn.congr
    (continuous_coe_real_ereal.comp_continuousOn (hf.continuousOn_toReal_relint_convexDom hp)) hcoe

end Relint

/-! ### Functions finite everywhere -/

section FiniteEverywhere

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **A convex function that is finite everywhere is continuous.** `dom f = univ` is "finite on
all of `Rⁿ`", properness supplying the other half. -/
theorem ConvexFn.continuous_of_convexDom_eq_univ (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) : Continuous f := by
  have hri : ri (convexDom f) = Set.univ := by rw [hdom, intrinsicInterior_univ]
  rw [← continuousOn_univ, ← hri]
  exact hf.continuousOn_relint_convexDom hp

/-- A convex function finite everywhere is continuous, real-valued form. -/
theorem ConvexFn.continuous_toReal_of_convexDom_eq_univ (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) : Continuous fun x => (f x).toReal := by
  have hri : ri (convexDom f) = Set.univ := by rw [hdom, intrinsicInterior_univ]
  rw [← continuousOn_univ, ← hri]
  exact hf.continuousOn_toReal_relint_convexDom hp

end FiniteEverywhere

/-! ### Lipschitz continuity on compact subsets of the relative interior -/

section Lipschitz

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {D : Set W} {ψ : W → ℝ}

omit [FiniteDimensional ℝ W] in
/-- **The quantitative core.** If `ψ` is convex on `D` and bounded by `M` in absolute value on the
closed `ε`-collar of `S`, and that collar lies inside `D`, then `ψ` is Lipschitz on `S` with
constant `2M/ε`. For `x ≠ y` in `S` the point
`z = y + (ε / ‖y - x‖) • (y - x)` sits in the collar and expresses `y` as a convex combination of
`x` and `z`, so convexity bounds the increment by the oscillation of `ψ` over the collar.

The constant is *exhibited* rather than existentially quantified: a family of convex functions
sharing one collar and one bound is therefore equi-Lipschitzian with a single constant. Mathlib's
`ConvexOn.lipschitzOnWith_of_abs_le` is the two-sided ball version, and
the collar argument does not follow from it. -/
theorem _root_.ConvexOn.lipschitzOnWith_of_abs_le_of_cthickening_subset (hψ : ConvexOn ℝ D ψ)
    {S : Set W} {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hsub : Metric.cthickening ε S ⊆ D)
    (hMabs : ∀ w ∈ Metric.cthickening ε S, |ψ w| ≤ M) :
    LipschitzOnWith (Real.toNNReal (2 * M / ε)) ψ S := by
  have key : ∀ x ∈ S, ∀ y ∈ S, ψ y - ψ x ≤ 2 * M / ε * ‖y - x‖ := by
    intro x hx y hy
    rcases eq_or_ne y x with rfl | hne
    · simp
    have ht : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have hεt : (0 : ℝ) < ε + ‖y - x‖ := by positivity
    have hzy : y + (ε / ‖y - x‖) • (y - x) - y = (ε / ‖y - x‖) • (y - x) := by
      rw [add_sub_cancel_left]
    have hdist : dist (y + (ε / ‖y - x‖) • (y - x)) y = ε := by
      rw [dist_eq_norm, hzy, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < ε / ‖y - x‖)]
      field_simp
    have hzT : y + (ε / ‖y - x‖) • (y - x) ∈ Metric.cthickening ε S :=
      Metric.mem_cthickening_of_dist_le _ _ _ _ hy hdist.le
    have hzD : y + (ε / ‖y - x‖) • (y - x) ∈ D := hsub hzT
    have hxD : x ∈ D := hsub (Metric.self_subset_cthickening S hx)
    have hxT : x ∈ Metric.cthickening ε S := Metric.self_subset_cthickening S hx
    have hcombo : (1 - ‖y - x‖ / (ε + ‖y - x‖)) • x
        + (‖y - x‖ / (ε + ‖y - x‖)) • (y + (ε / ‖y - x‖) • (y - x)) = y := by
      match_scalars <;> field_simp <;> ring
    have hlam0 : (0 : ℝ) ≤ ‖y - x‖ / (ε + ‖y - x‖) := by positivity
    have hlam1 : ‖y - x‖ / (ε + ‖y - x‖) ≤ 1 := by
      rw [div_le_one hεt]; linarith
    have hconv := hψ.2 hxD hzD (by linarith : (0 : ℝ) ≤ 1 - ‖y - x‖ / (ε + ‖y - x‖)) hlam0
      (by ring)
    rw [hcombo] at hconv
    simp only [smul_eq_mul] at hconv
    have hosc : ψ (y + (ε / ‖y - x‖) • (y - x)) - ψ x ≤ 2 * M := by
      have h1 := abs_le.1 (hMabs _ hzT)
      have h2 := abs_le.1 (hMabs x hxT)
      linarith [h1.2, h2.1]
    have hstep : ψ y - ψ x
        ≤ (‖y - x‖ / (ε + ‖y - x‖)) * (ψ (y + (ε / ‖y - x‖) • (y - x)) - ψ x) := by
      linarith [hconv]
    have hlamt : ‖y - x‖ / (ε + ‖y - x‖) ≤ ‖y - x‖ / ε :=
      (div_le_div_iff_of_pos_left ht hεt hε).2 (by linarith)
    rcases le_or_gt (ψ (y + (ε / ‖y - x‖) • (y - x)) - ψ x) 0 with hneg | hpos
    · have hle0 : ψ y - ψ x ≤ 0 :=
        hstep.trans (mul_nonpos_of_nonneg_of_nonpos hlam0 hneg)
      exact hle0.trans (mul_nonneg (div_nonneg (by linarith) hε.le) (norm_nonneg _))
    · calc ψ y - ψ x
          ≤ (‖y - x‖ / (ε + ‖y - x‖)) * (ψ (y + (ε / ‖y - x‖) • (y - x)) - ψ x) := hstep
        _ ≤ (‖y - x‖ / ε) * (2 * M) := mul_le_mul hlamt hosc hpos.le (by positivity)
        _ = 2 * M / ε * ‖y - x‖ := by ring
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (div_nonneg (by linarith) hε.le)]
  rcases abs_cases (ψ x - ψ y) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    exact key y hy x hx
  · rw [h, norm_sub_rev]
    linarith [key x hx y hy]

/-- **The interior form**: a function convex on `D` is Lipschitz on every compact subset of
`interior D`. Compactness supplies an `ε`-collar of `S` still inside
`interior D`, on which continuity bounds `ψ`. -/
theorem _root_.ConvexOn.exists_lipschitzOnWith_of_isCompact (hψ : ConvexOn ℝ D ψ) {S : Set W}
    (hS : IsCompact S) (hSD : S ⊆ interior D) : ∃ K : ℝ≥0, LipschitzOnWith K ψ S := by
  obtain ⟨ε, hε, hsub⟩ := hS.exists_cthickening_subset_open isOpen_interior hSD
  obtain ⟨M, hM⟩ := (hS.cthickening (r := ε)).exists_bound_of_continuousOn
    ((ConvexOn.continuousOn_interior hψ).mono hsub)
  refine ⟨_, ConvexOn.lipschitzOnWith_of_abs_le_of_cthickening_subset hψ hε (abs_nonneg M)
    (hsub.trans interior_subset) fun w hw => ?_⟩
  have hw' := hM w hw
  rw [Real.norm_eq_abs] at hw'
  exact hw'.trans (le_abs_self M)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **A proper convex function is Lipschitz on every compact subset of `ri (dom f)`.** The usual
statement is for closed bounded subsets, which in finite dimensions is the same thing. The
retraction of the chart is a continuous linear map, hence Lipschitz,
so it carries Lipschitz constants back as well as continuity. -/
theorem ConvexFn.exists_lipschitzOnWith_of_isCompact (hf : ConvexFn f) (hp : ProperConvex f)
    {S : Set E}
    (hS : IsCompact S) (hSD : S ⊆ ri (convexDom f)) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x => (f x).toReal) S := by
  obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
  obtain ⟨V, r, -, hmaps, hid⟩ := exists_chart_retraction hf.convex_convexDom hx₀
  have hconv : ConvexOn ℝ (convexDom f) (fun x => (f x).toReal) := hf.convexOn_toReal_convexDom hp
  have hshift : (AffineMap.const ℝ V x₀ + V.subtype.toAffineMap) ⁻¹' convexDom f
      = chart (convexDom f) x₀ V := rfl
  have hψ : ConvexOn ℝ (chart (convexDom f) x₀ V) fun z : V => (f (x₀ + (z : E))).toReal :=
    hshift ▸ hconv.comp_affineMap (AffineMap.const ℝ V x₀ + V.subtype.toAffineMap)
  have hρ : Continuous fun x : E => r (x - x₀) :=
    r.continuous.comp (continuous_id.sub continuous_const)
  have hS'c : IsCompact ((fun x : E => r (x - x₀)) '' S) := hS.image hρ
  have hS'sub : (fun x : E => r (x - x₀)) '' S ⊆ interior (chart (convexDom f) x₀ V) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps (hSD hx)
  obtain ⟨K, hK⟩ := ConvexOn.exists_lipschitzOnWith_of_isCompact hψ hS'c hS'sub
  have hrlip : LipschitzWith ‖r‖₊ (fun x : E => r (x - x₀)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hsub : (r (x - x₀) : V) - r (y - x₀) = r (x - y) := by
      rw [← map_sub]; congr 1; abel
    rw [dist_eq_norm, hsub, dist_eq_norm, coe_nnnorm]
    exact r.le_opNorm _
  have hcomp : LipschitzOnWith (K * ‖r‖₊)
      ((fun z : V => (f (x₀ + (z : E))).toReal) ∘ fun x : E => r (x - x₀)) S :=
    hK.comp hrlip.lipschitzOnWith fun x hx => Set.mem_image_of_mem _ hx
  refine ⟨K * ‖r‖₊, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hval : ∀ z ∈ S, (f (x₀ + ((r (z - x₀) : V) : E))).toReal = (f z).toReal := fun z hz => by
    rw [hid z (hSD hz)]
  have := hcomp.dist_le_mul x hx y hy
  rwa [Function.comp_apply, Function.comp_apply, hval x hx, hval y hy] at this

end Lipschitz

/-! ### Uniform continuity and Lipschitz continuity on the whole space -/

section UniformContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A proper function whose effective domain is everything is the coercion of its real form. -/
theorem coe_toReal_of_convexDom_eq_univ (hp : ProperConvex f) (hdom : convexDom f = Set.univ)
    (x : E) :
    (((f x).toReal : ℝ) : EReal) = f x := by
  refine EReal.coe_toReal ?_ (hp.ne_bot x)
  have hx : x ∈ convexDom f := by rw [hdom]; exact Set.mem_univ x
  exact (mem_convexDom.1 hx).ne

/-- A finite convex function on the whole space is closed: it is continuous, hence lower
semicontinuous, hence has a closed epigraph. -/
theorem ConvexFn.isClosed_epi_of_convexDom_eq_univ (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) : IsClosed (epi f) :=
  lowerSemicontinuous_iff_isClosed_epi.1
    (hf.continuous_of_convexDom_eq_univ hp hdom).lowerSemicontinuous

/-- **When `f0⁺` is finite everywhere it is bounded by a linear function of the norm.** The
constant is `α = sup {(f0⁺) z | ‖z‖ = 1}`, finite because `f0⁺` is a finite convex function, hence
continuous, and the unit ball is compact; positive homogeneity spreads the bound over the whole
space. -/
theorem exists_recessionFn_le_of_forall_ne_top (hp : ProperConvex f)
    (hrec : ∀ y, recessionFn f y ≠ ⊤) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, recessionFn f y ≤ ((M * ‖y‖ : ℝ) : EReal) := by
  have hrdom : convexDom (recessionFn f) = Set.univ :=
    Set.eq_univ_of_forall fun y => mem_convexDom.2 (lt_top_iff_ne_top.2 (hrec y))
  have hrcont : Continuous fun y => (recessionFn f y).toReal :=
    (convexFn_recessionFn f).continuous_toReal_of_convexDom_eq_univ
        (properConvex_recessionFn hp) hrdom
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    hrcont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Metric.mem_closedBall_self zero_le_one))
  refine ⟨M, hM0, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · rw [recessionFn_apply_zero hp]
    simp
  · have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hu : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hyn), inv_mul_cancel₀ hyn.ne']
    have hsmul : ‖y‖ • (‖y‖⁻¹ • y) = y := smul_inv_smul₀ hyn.ne' y
    have hfin := coe_toReal_of_convexDom_eq_univ (properConvex_recessionFn hp) hrdom (‖y‖⁻¹ • y)
    have hle : (recessionFn f (‖y‖⁻¹ • y)).toReal ≤ M :=
      le_trans (le_abs_self _)
        (hM _ (by simpa [Metric.mem_closedBall, dist_zero_right] using hu.le))
    calc recessionFn f y = recessionFn f (‖y‖ • (‖y‖⁻¹ • y)) := by rw [hsmul]
      _ = ((‖y‖ : ℝ) : EReal) * recessionFn f (‖y‖⁻¹ • y) :=
          posHomogeneous_recessionFn f ‖y‖ hyn _
      _ = ((‖y‖ * (recessionFn f (‖y‖⁻¹ • y)).toReal : ℝ) : EReal) := by
          rw [EReal.coe_mul, hfin]
      _ ≤ ((M * ‖y‖ : ℝ) : EReal) := by
          refine EReal.coe_le_coe_iff.2 ?_
          nlinarith [hyn.le]

/-- **Sufficiency**: if the recession function of a finite convex function on the whole space is
finite everywhere, the function is Lipschitz, with `α` as constant. -/
theorem ConvexFn.exists_lipschitzWith_of_recessionFn_ne_top (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) (hrec : ∀ y, recessionFn f y ≠ ⊤) :
    ∃ K : ℝ≥0, LipschitzWith K fun x => (f x).toReal := by
  obtain ⟨M, hM0, hMle⟩ := exists_recessionFn_le_of_forall_ne_top hp hrec
  obtain ⟨K, hKcoe⟩ : ∃ K : ℝ≥0, (K : ℝ) = M := ⟨⟨M, hM0⟩, rfl⟩
  have key : ∀ u v : E, (f v).toReal - (f u).toReal ≤ M * ‖v - u‖ := by
    intro u v
    have huv : u + (v - u) = v := by abel
    have h1 := le_add_recessionFn hf hp u (v - u)
    rw [huv] at h1
    have h2 : f v ≤ f u + ((M * ‖v - u‖ : ℝ) : EReal) :=
      h1.trans (add_le_add le_rfl (hMle (v - u)))
    rw [← coe_toReal_of_convexDom_eq_univ hp hdom v, ← coe_toReal_of_convexDom_eq_univ hp hdom u,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    linarith
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x z => ?_⟩
  rw [Real.dist_eq, dist_eq_norm, hKcoe]
  rcases abs_cases ((f x).toReal - (f z).toReal) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    exact key z x
  · rw [h, norm_sub_rev]
    linarith [key x z]

omit [FiniteDimensional ℝ E] in
/-- **Necessity**: a uniformly continuous finite convex function has a finite recession function.
Uniform continuity at `ε = 1` bounds `f (x + z) - f x` by `1` uniformly in `x` for short `z`, which
says `(f0⁺) z ≤ 1`. -/
theorem ConvexFn.recessionFn_ne_top_of_uniformContinuous (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) (hu : UniformContinuous fun x => (f x).toReal) (y : E) :
    recessionFn f y ≠ ⊤ := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1 hu 1 one_pos
  have key : ∀ z : E, ‖z‖ < δ → recessionFn f z ≤ ((1 : ℝ) : EReal) := by
    intro z hz
    rw [recessionFn_apply_eq_iSup_sub hf hp.ne_bot]
    refine iSup₂_le fun x _ => ?_
    have hd : dist (x + z) x < δ := by rw [dist_eq_norm, add_sub_cancel_left]; exact hz
    have hlt := hδ' hd
    rw [Real.dist_eq] at hlt
    have h1 : (f (x + z)).toReal - (f x).toReal ≤ 1 := (le_abs_self _).trans hlt.le
    rw [← coe_toReal_of_convexDom_eq_univ hp hdom (x + z),
        ← coe_toReal_of_convexDom_eq_univ hp hdom x,
      ← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.2 h1
  rcases eq_or_ne y 0 with rfl | hy
  · rw [recessionFn_apply_zero hp]
    simp
  · have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hcpos : 0 < δ / (2 * ‖y‖) := by positivity
    have hnorm : ‖(δ / (2 * ‖y‖)) • y‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos,
        show δ / (2 * ‖y‖) * ‖y‖ = δ / 2 by field_simp]
      linarith
    have hcy := key _ hnorm
    rw [posHomogeneous_recessionFn f _ hcpos y] at hcy
    intro htop
    rw [htop, EReal.coe_mul_top_of_pos hcpos, top_le_iff] at hcy
    exact EReal.coe_ne_top 1 hcy

/-- **A finite convex function on the whole space is uniformly continuous exactly when its
recession function is finite everywhere**, and then it is in fact Lipschitz
(`ConvexFn.exists_lipschitzWith_of_recessionFn_ne_top`). -/
theorem ConvexFn.uniformContinuous_toReal_iff (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) :
    (UniformContinuous fun x => (f x).toReal) ↔ ∀ y, recessionFn f y ≠ ⊤ := by
  refine ⟨fun hu y => hf.recessionFn_ne_top_of_uniformContinuous hp hdom hu y, fun hrec => ?_⟩
  obtain ⟨K, hK⟩ := hf.exists_lipschitzWith_of_recessionFn_ne_top hp hdom hrec
  exact hK.uniformContinuous

/-- For Lipschitz continuity it is enough that `f (a • y) / a` stay bounded above along *some*
sequence `a → ∞`, in every direction `y`. The quotient is nondecreasing in `a`, so a bound reached
infinitely often is a bound everywhere. -/
theorem ConvexFn.exists_lipschitzWith_of_frequently_le (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ)
    (h : ∀ y : E, ∃ c : ℝ, ∃ᶠ a : ℝ in Filter.atTop, f (a • y) ≤ ((c * a : ℝ) : EReal)) :
    ∃ K : ℝ≥0, LipschitzWith K fun x => (f x).toReal := by
  refine hf.exists_lipschitzWith_of_recessionFn_ne_top hp hdom fun y => ?_
  obtain ⟨c, hfreq⟩ := h y
  have h0 : (0 : E) ∈ convexDom f := by rw [hdom]; exact Set.mem_univ 0
  have hclosed := hf.isClosed_epi_of_convexDom_eq_univ hp hdom
  obtain ⟨F0, hF0⟩ : ∃ r : ℝ, f 0 = (r : EReal) :=
    ⟨(f 0).toReal, (coe_toReal_of_convexDom_eq_univ hp hdom 0).symm⟩
  have hbound : recessionFn f y ≤ ((c + |F0| : ℝ) : EReal) := by
    rw [recessionFn_le_coe_iff_of_isClosed hf hclosed hp.ne_bot h0]
    intro a ha
    obtain ⟨a', ha'le, ha'ge⟩ :=
      (hfreq.and_eventually (Filter.eventually_ge_atTop (max a 1))).exists
    have ha'1 : (1 : ℝ) ≤ a' := le_trans (le_max_right a 1) ha'ge
    have ha'0 : (0 : ℝ) < a' := lt_of_lt_of_le zero_lt_one ha'1
    have hq' : ((a'⁻¹ : ℝ) : EReal) * (f (0 + a' • y) - f 0)
        ≤ ((c + |F0| : ℝ) : EReal) := by
      rw [coe_inv_mul_sub_le_coe_iff hp.ne_bot h0 ha'0, zero_add, hF0, ← EReal.coe_add]
      refine ha'le.trans (EReal.coe_le_coe_iff.2 ?_)
      nlinarith [abs_nonneg F0, neg_abs_le F0]
    refine (coe_inv_mul_sub_le_coe_iff hp.ne_bot h0 ha).1 ?_
    exact (monotone_coe_inv_mul_sub hf hp.ne_bot h0 y ha
      (le_trans (le_max_left a 1) ha'ge)).trans hq'
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hbound

/-- **A finite convex function dominated by a Lipschitz function is itself Lipschitz.** The usual
statement assumes the dominating `g` convex; the proof does not use it, so `g` here is an arbitrary
Lipschitz function. -/
theorem ConvexFn.exists_lipschitzWith_of_le_lipschitz (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) {g : E → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hle : ∀ x, f x ≤ ((g x : ℝ) : EReal)) :
    ∃ K' : ℝ≥0, LipschitzWith K' fun x => (f x).toReal := by
  refine hf.exists_lipschitzWith_of_frequently_le hp hdom fun y =>
    ⟨|g 0| + (K : ℝ) * ‖y‖, Filter.Eventually.frequently ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with a ha
  refine (hle _).trans (EReal.coe_le_coe_iff.2 ?_)
  have hd : dist (g (a • y)) (g 0) ≤ (K : ℝ) * dist (a • y) (0 : E) := hg.dist_le_mul _ _
  rw [Real.dist_eq, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ a)] at hd
  have h1 : g (a • y) - g 0 ≤ (K : ℝ) * (a * ‖y‖) := (le_abs_self _).trans hd
  nlinarith [le_abs_self (g 0), abs_nonneg (g 0), norm_nonneg y, K.coe_nonneg]

end UniformContinuity

end ConvexAnalysis

section BanachSpace

open Filter Topology

/-- **A convex, lower semicontinuous, real-valued function on a Banach space is continuous.**
Lower semicontinuity makes the sublevel sets `{f ≤ n}` closed and finiteness makes them cover the
space, so Baire's theorem bounds `f` above on a ball; a convex function bounded above on some ball
is continuous. -/
theorem ConvexOn.continuous_of_lowerSemicontinuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : E → ℝ} (hcv : ConvexOn ℝ univ f)
    (hlsc : LowerSemicontinuous f) : Continuous f := by
  have hclosed : ∀ n : ℕ, IsClosed (f ⁻¹' Iic (n : ℝ)) := fun n => hlsc.isClosed_preimage _
  have hcover : ⋃ n : ℕ, f ⁻¹' Iic (n : ℝ) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (f x)
    exact ⟨n, hn⟩
  obtain ⟨n, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have hbdd : (𝓝 x₀).IsBoundedUnder (· ≤ ·) f :=
    ⟨(n : ℝ), eventually_map.2 (mem_interior_iff_mem_nhds.1 hx₀)⟩
  have htfae : (∃ y ∈ (univ : Set E), (𝓝 y).IsBoundedUnder (· ≤ ·) f) ↔ ContinuousOn f univ :=
    (ConvexOn.continuousOn_tfae isOpen_univ ⟨x₀, mem_univ _⟩ hcv).out 4 2
  rw [← continuousOn_univ]
  exact htfae.1 ⟨x₀, mem_univ _, hbdd⟩

end BanachSpace
