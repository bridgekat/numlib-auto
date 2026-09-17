/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.DerivativeTest`, beside the sufficient second-derivative
test `isLocalMin_of_deriv_deriv_pos`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# The necessary second-derivative test at a maximum

Mathlib's `isLocalMin_of_deriv_deriv_pos` is the *sufficient* second-derivative test: a critical
point with positive second derivative is a local minimum. This file has the *necessary* test, in
the two forms the classical maximum principles of Brezis, *Functional Analysis, Sobolev Spaces
and Partial Differential Equations* (Remarks 26–27 of chapter 8 and Theorem 10.6) use:

* `IsLocalMax.deriv_deriv_nonpos`: at an interior local maximum of a function continuous there,
  `f'' ≤ 0` — with Mathlib's junk-value convention for `deriv`, so no differentiability is
  assumed; the continuity cannot be dropped (`f x = x²/2` for `x ≠ 0`, `f 0 = 1`, has a local
  maximum at `0` with `deriv f = id` and `deriv (deriv f) 0 = 1`);
* `IsLocalMaxOn.deriv_deriv_nonpos_of_deriv_eq_zero`: the one-sided form at an endpoint, for a
  function that is `C²` on `[x₀, x₀ + δ)`, has vanishing one-sided derivative at `x₀` and a local
  maximum there among the points to the right — `u'' (x₀⁺) ≤ 0`. Its engine is
  `IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Ici`, stated with explicit derivative data.

## References

[brezis2011functional], chapter 8, Remarks 26 and 27.
-/

open Filter Set Topology

/-- **The second-derivative test at an interior maximum**: if `f : ℝ → ℝ` has a local maximum at
`x₀` and is continuous there, then `deriv (deriv f) x₀ ≤ 0`. No differentiability is assumed
(`deriv` is `0` where it does not exist), but the continuity is needed. The proof is the
contrapositive of Mathlib's `isLocalMin_of_deriv_deriv_pos`: a point that is both a local maximum
and a local minimum is a point near which `f` is constant, where both derivatives vanish. -/
theorem IsLocalMax.deriv_deriv_nonpos {f : ℝ → ℝ} {x₀ : ℝ} (hf : IsLocalMax f x₀)
    (hc : ContinuousAt f x₀) : deriv (deriv f) x₀ ≤ 0 := by
  by_contra hpos
  replace hpos : 0 < deriv (deriv f) x₀ := not_le.1 hpos
  have hmin : IsLocalMin f x₀ := isLocalMin_of_deriv_deriv_pos hpos hf.deriv_eq_zero hc
  -- `f` is constant near `x₀`
  have hconst : ∀ᶠ y in 𝓝 x₀, f y = f x₀ := by
    filter_upwards [hf, hmin] with y hy hy'
    exact le_antisymm hy hy'
  -- hence `deriv f` vanishes near `x₀`, and so does `deriv (deriv f)` at `x₀`
  have hderiv : ∀ᶠ y in 𝓝 x₀, deriv f y = 0 := by
    filter_upwards [eventually_eventually_nhds.2 hconst] with y hy
    rw [Filter.EventuallyEq.deriv_eq (hy : f =ᶠ[𝓝 y] fun _ ↦ f x₀), deriv_const]
  have : deriv (deriv f) x₀ = 0 := by
    rw [Filter.EventuallyEq.deriv_eq (hderiv : deriv f =ᶠ[𝓝 x₀] fun _ ↦ 0), deriv_const]
  exact absurd this hpos.ne'

/-- **The one-sided second-derivative test at an endpoint, with explicit derivative data**: if
`u` has a local maximum at `x₀` among the points of `[x₀, ∞)`, has the one-sided derivative `u' y`
at every `y` near `x₀` in `[x₀, ∞)`, and `u'` has one-sided derivative `c` at `x₀` with
`u' x₀ = 0`, then `c ≤ 0`. Were `c > 0`, `u'` would be positive just to the right of `x₀` and,
by the mean value theorem, `u` would increase there. -/
theorem IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Ici {u u' : ℝ → ℝ} {x₀ c : ℝ}
    (hmax : IsLocalMaxOn u (Ici x₀) x₀)
    (hu : ∀ᶠ y in 𝓝[≥] x₀, HasDerivWithinAt u (u' y) (Ici x₀) y)
    (hu' : HasDerivWithinAt u' c (Ici x₀) x₀) (h0 : u' x₀ = 0) : c ≤ 0 := by
  by_contra hc
  replace hc : 0 < c := not_le.1 hc
  -- `u' > 0` just to the right of `x₀`
  have hpos : ∀ᶠ y in 𝓝[>] x₀, 0 < u' y := by
    have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x₀)).1
      (hu'.mono Ioi_subset_Ici_self)
    filter_upwards [hslope.eventually (eventually_gt_nhds hc), self_mem_nhdsWithin] with y hy hy'
    rw [slope_def_field, h0, sub_zero] at hy
    exact (div_pos_iff_of_pos_right (sub_pos.2 hy')).1 hy
  -- a right neighbourhood on which `u ≤ u x₀`, `u` is differentiable and `u' > 0`
  have hall : ∀ᶠ y in 𝓝[>] x₀,
      u y ≤ u x₀ ∧ HasDerivWithinAt u (u' y) (Ici x₀) y ∧ 0 < u' y := by
    have h1 : ∀ᶠ y in 𝓝[>] x₀, u y ≤ u x₀ :=
      (hmax : ∀ᶠ y in 𝓝[Ici x₀] x₀, u y ≤ u x₀).filter_mono
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact h1.and ((hu.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)).and hpos)
  obtain ⟨b, hb, hP⟩ := (nhdsGT_basis x₀).eventually_iff.1 hall
  set t := (x₀ + b) / 2 with ht
  have htx : x₀ < t := by rw [ht]; linarith
  have htb : t < b := by rw [ht]; linarith
  -- the mean value theorem on `[x₀, t]`
  have hx₀ : HasDerivWithinAt u (u' x₀) (Ici x₀) x₀ := hu.self_of_nhdsWithin (mem_Ici.2 le_rfl)
  have hcont : ContinuousOn u (Icc x₀ t) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with rfl | hlt
    · exact hx₀.continuousWithinAt.mono Icc_subset_Ici_self
    · exact ((hP ⟨hlt, hy.2.trans_lt htb⟩).2.1.hasDerivAt (Ici_mem_nhds hlt)).continuousAt
        |>.continuousWithinAt
  have hdiff : ∀ y ∈ Ioo x₀ t, HasDerivAt u (u' y) y := fun y hy ↦
    (hP ⟨hy.1, hy.2.trans htb⟩).2.1.hasDerivAt (Ici_mem_nhds hy.1)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope u u' htx hcont hdiff
  have hξpos : 0 < u' ξ := (hP ⟨hξ.1, hξ.2.trans htb⟩).2.2
  have hut : u t ≤ u x₀ := (hP ⟨htx, htb⟩).1
  have : u' ξ * (t - x₀) = u t - u x₀ := by
    rw [hξeq, div_mul_cancel₀ _ (sub_pos.2 htx).ne']
  nlinarith [mul_pos hξpos (sub_pos.2 htx)]

/-- **The one-sided second-derivative test at an endpoint** ([brezis2011functional], chapter 8,
Remark 27): if `u` is `C²` on `[x₀, x₀ + δ)`, its one-sided derivative `u'(x₀⁺) = 0`, and `x₀` is a
local maximum of `u` among the points of `[x₀, ∞)`, then the one-sided second derivative
`u''(x₀⁺) ≤ 0`. The one-sided derivatives are `derivWithin … (Ici x₀)`; when `u` is `C²` on a
two-sided neighbourhood they are the ordinary derivatives (`derivWithin_of_mem_nhds`). -/
theorem IsLocalMaxOn.deriv_deriv_nonpos_of_deriv_eq_zero {u : ℝ → ℝ} {x₀ δ : ℝ} (hδ : 0 < δ)
    (hu : ContDiffOn ℝ 2 u (Ico x₀ (x₀ + δ))) (h0 : derivWithin u (Ici x₀) x₀ = 0)
    (hmax : IsLocalMaxOn u (Ici x₀) x₀) :
    derivWithin (derivWithin u (Ici x₀)) (Ici x₀) x₀ ≤ 0 := by
  set S := Ico x₀ (x₀ + δ) with hS
  have hSu : UniqueDiffOn ℝ S := uniqueDiffOn_Ico x₀ (x₀ + δ)
  have hSmem : ∀ y ∈ S, S ∈ 𝓝[Ici x₀] y := fun y hy ↦ by
    rw [hS, ← Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds hy.2)
  have hx₀S : x₀ ∈ S := ⟨le_rfl, by linarith⟩
  -- on `S`, the derivative within `S` is the one-sided derivative
  have hderiv : ∀ y ∈ S, derivWithin u S y = derivWithin u (Ici x₀) y := fun y hy ↦ by
    rw [hS, ← Ici_inter_Iio, derivWithin_inter (Iio_mem_nhds hy.2)]
  -- `u` is differentiable within `S`, with the one-sided derivative
  have hu1 : ∀ y ∈ S, HasDerivWithinAt u (derivWithin u (Ici x₀) y) (Ici x₀) y := fun y hy ↦ by
    rw [← hderiv y hy]
    exact ((hu.differentiableOn (by norm_num)) y hy).hasDerivWithinAt.mono_of_mem_nhdsWithin
      (hSmem y hy)
  -- the derivative within `S` is `C¹` on `S`, hence differentiable within `S` at `x₀`
  have hu2 : ContDiffOn ℝ 1 (derivWithin u S) S := by
    have h2 : ContDiffOn ℝ ((1 : ℕ) + 1) u S := hu
    exact ((contDiffOn_succ_iff_derivWithin hSu).1 h2).2.2
  have hc : HasDerivWithinAt (derivWithin u (Ici x₀)) (derivWithin (derivWithin u S) S x₀)
      (Ici x₀) x₀ := by
    refine (((hu2.differentiableOn one_ne_zero) x₀ hx₀S).hasDerivWithinAt.congr
      (fun y hy ↦ (hderiv y hy).symm) (hderiv x₀ hx₀S).symm).mono_of_mem_nhdsWithin
      (hSmem x₀ hx₀S)
  rw [hc.derivWithin (uniqueDiffWithinAt_Ici x₀)]
  exact hmax.nonpos_of_hasDerivWithinAt_Ici
    (eventually_of_mem (hSmem x₀ hx₀S) hu1) hc h0
