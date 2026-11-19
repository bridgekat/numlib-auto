/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Analysis.Analytic.IsolatedZeros
import Numlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.Subpath
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Numlib.Analysis.Calculus.SegmentAverage
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Cauchy

/-!
# Resolvent integrals along complex paths

The integral of the resolvent around a piecewise continuously differentiable loop is
a sum of the spectral idempotents weighted by winding numbers. For a holomorphic scalar weight,
the coefficients of the higher-order poles contribute Taylor coefficients. This yields a
path-integral representation of the primary functional calculus.

## Main definitions

* `Path.IsPiecewiseC1` describes concatenations of continuously differentiable paths.
* `Path.IsLipschitz` states that the path parametrization is Lipschitz on the unit interval.
* `complexLineIntegral` is the complex integral along a path of a Banach-space-valued function.
* `complexPathIndex` is the integral of the simple pole divided by $2\pi i$.

## Main results

* `complexLineIntegral_resolvent` evaluates the normalized resolvent integral for a piecewise
  $C^1$ loop.
* `Path.exists_lipschitz_reparametrization` gives an orientation-preserving Lipschitz
  parametrization of a rectifiable path.
* `normalized_complexLineIntegral_div_sub_pow` is Cauchy's formula for derivatives along
  Lipschitz loops in open convex sets.
* `pfc_eq_sum_complexLineIntegral` recovers the primary functional calculus from finitely many
  such loops with total winding number one at every spectral value.
* `normalized_complexLineIntegral_cauchy_family` gives the homological
  Cauchy formula on arbitrary open sets. Its derivative formula yields
  `pfc_eq_sum_complexLineIntegral_homological` for the primary calculus.
-/

open Complex Polynomial Set MeasureTheory
open scoped Real Interval NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

private noncomputable def complexForm (f : ℂ → V) (z : ℂ) : ℂ →L[ℂ] V :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (f z)

/-- A piecewise continuously differentiable path is a finite concatenation of paths with
a continuous derivative on their closed parameter intervals. -/
inductive Path.IsPiecewiseC1 : {a b : ℂ} → Path a b → Prop
  | single {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend unitInterval) :
      Path.IsPiecewiseC1 γ
  | trans {a b c : ℂ} {γ₁ : Path a b} {γ₂ : Path b c}
      (h₁ : Path.IsPiecewiseC1 γ₁) (h₂ : Path.IsPiecewiseC1 γ₂) :
      Path.IsPiecewiseC1 (γ₁.trans γ₂)

/-- The complex line integral of $f$ along $\gamma$, integrating $f(\gamma(t))\,d\gamma(t)$. -/
noncomputable def complexLineIntegral {a b : ℂ} (γ : Path a b) (f : ℂ → V) : V :=
  curveIntegral (complexForm f) γ

/-- The winding integral of $\gamma$ about $w$, divided by $2\pi i$. -/
noncomputable def complexPathIndex {a : ℂ} (γ : Path a a) (w : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * complexLineIntegral γ (fun z => (z - w)⁻¹)

private theorem curveIntegralFun_complexForm {a b : ℂ} (γ : Path a b) (f : ℂ → V) :
    curveIntegralFun (complexForm f) γ =
      fun t => derivWithin γ.extend unitInterval t • f (γ.extend t) := by
  funext t
  simp only [curveIntegralFun_def, complexForm, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]

private theorem complexLineIntegral_eq_interval {a b : ℂ} (γ : Path a b) (f : ℂ → V) :
    complexLineIntegral γ f =
      ∫ t in 0..1, derivWithin γ.extend unitInterval t • f (γ.extend t) := by
  rw [complexLineIntegral, curveIntegral_def, curveIntegralFun_complexForm]

/-- The given path parametrization is Lipschitz on the unit interval. -/
def Path.IsLipschitz {X : Type*} [MetricSpace X] {a b : X} (γ : Path a b) : Prop :=
  ∃ K : ℝ≥0, LipschitzWith K γ

theorem Path.lipschitzWith_extend {X : Type*} [MetricSpace X] {a b : X} {γ : Path a b}
    {K : ℝ≥0} (hγ : LipschitzWith K γ) : LipschitzWith K γ.extend := by
  change LipschitzWith K (γ ∘ projIcc 0 1 zero_le_one)
  simpa only [mul_one] using hγ.comp (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1))

theorem Path.IsLipschitz.exists_lipschitzWith_extend {X : Type*} [MetricSpace X] {a b : X}
    {γ : Path a b} (hγ : γ.IsLipschitz) : ∃ K : ℝ≥0, LipschitzWith K γ.extend := by
  obtain ⟨K, hK⟩ := hγ
  exact ⟨K, Path.lipschitzWith_extend hK⟩

/-- Concatenating Lipschitz paths preserves Lipschitz regularity. -/
theorem Path.IsLipschitz.trans {X : Type*} [MetricSpace X] {a b c : X}
    {γ₁ : Path a b} {γ₂ : Path b c} (h₁ : γ₁.IsLipschitz) (h₂ : γ₂.IsLipschitz) :
    (γ₁.trans γ₂).IsLipschitz := by
  obtain ⟨K₁, hK₁⟩ := h₁.exists_lipschitzWith_extend
  obtain ⟨K₂, hK₂⟩ := h₂.exists_lipschitzWith_extend
  let C : ℝ≥0 := 2 * (K₁ + K₂)
  let γ := γ₁.trans γ₂
  have hLeft (x y : ℝ) (hx : x ≤ 1 / 2) (hy : y ≤ 1 / 2) :
      dist (γ.extend x) (γ.extend y) ≤ (C : ℝ) * dist x y := by
    rw [Path.extend_trans_of_le_half _ _ hx, Path.extend_trans_of_le_half _ _ hy]
    calc
      _ ≤ (K₁ : ℝ) * dist (2 * x) (2 * y) := hK₁.dist_le_mul _ _
      _ = (2 * (K₁ : ℝ)) * dist x y := by
        simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ _ := by
        dsimp [C]
        gcongr
        exact le_add_of_nonneg_right K₂.2
  have hRight (x y : ℝ) (hx : 1 / 2 ≤ x) (hy : 1 / 2 ≤ y) :
      dist (γ.extend x) (γ.extend y) ≤ (C : ℝ) * dist x y := by
    rw [Path.extend_trans_of_half_le _ _ hx, Path.extend_trans_of_half_le _ _ hy]
    calc
      _ ≤ (K₂ : ℝ) * dist (2 * x - 1) (2 * y - 1) := hK₂.dist_le_mul _ _
      _ = (2 * (K₂ : ℝ)) * dist x y := by
        simp only [Real.dist_eq, sub_sub_sub_cancel_right, ← mul_sub, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ _ := by
        dsimp [C]
        gcongr
        exact le_add_of_nonneg_left K₁.2
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hAll (x y : ℝ) (hxy : x ≤ y) :
      dist (γ.extend x) (γ.extend y) ≤ (C : ℝ) * dist x y := by
    by_cases hy : y ≤ 1 / 2
    · exact hLeft x y (hxy.trans hy) hy
    by_cases hx : 1 / 2 ≤ x
    · exact hRight x y hx (hx.trans hxy)
    have hx' : x ≤ 1 / 2 := le_of_not_ge hx
    have hy' : 1 / 2 ≤ y := le_of_not_ge hy
    calc
      _ ≤ dist (γ.extend x) (γ.extend (1 / 2)) + dist (γ.extend (1 / 2)) (γ.extend y) :=
        dist_triangle _ _ _
      _ ≤ (C : ℝ) * dist x (1 / 2) + (C : ℝ) * dist (1 / 2) y :=
        add_le_add (hLeft _ _ hx' le_rfl) (hRight _ _ le_rfl hy')
      _ = _ := by
        rw [← mul_add]
        congr 1
        simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx'),
          abs_of_nonpos (sub_nonpos.mpr hy'), abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring
  change dist (γ x) (γ y) ≤ (C : ℝ) * dist (x : ℝ) (y : ℝ)
  have hx : γ.extend (x : ℝ) = γ x := Path.extend_apply γ x.2
  have hy : γ.extend (y : ℝ) = γ y := Path.extend_apply γ y.2
  rw [← hx, ← hy]
  rcases le_total (x : ℝ) (y : ℝ) with hxy | hyx
  · exact hAll x y hxy
  · rw [dist_comm (γ.extend (x : ℝ)), dist_comm (x : ℝ)]
    exact hAll y x hyx

/-- A piecewise continuously differentiable path is Lipschitz. -/
theorem Path.IsPiecewiseC1.isLipschitz {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseC1) :
    γ.IsLipschitz := by
  induction hγ with
  | single γ hγ =>
    obtain ⟨K, hK⟩ := hγ.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
    refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    change dist (γ x) (γ y) ≤ (K : ℝ) * dist (x : ℝ) (y : ℝ)
    have hx : γ.extend (x : ℝ) = γ x := Path.extend_apply γ x.2
    have hy : γ.extend (y : ℝ) = γ y := Path.extend_apply γ y.2
    rw [← hx, ← hy]
    exact hK.dist_le_mul x x.2 y y.2
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

namespace Path

open scoped unitInterval

variable {X : Type*} [MetricSpace X] {a b : X}

/-- A rectifiable path has a Lipschitz parametrization obtained by an increasing
homeomorphism of the unit interval. The change of parameter is the normalized sum
of the original parameter and the cumulative variation. -/
theorem exists_lipschitz_reparametrization (γ : Path a b)
    (hγ : BoundedVariationOn γ.extend unitInterval) :
    ∃ (ρ : I ≃o I) (η : Path a b) (K : NNReal),
      LipschitzWith K η ∧ ∀ t, η (ρ t) = γ t := by
  let len := variationOnFromTo γ.extend unitInterval 0
  have hlen_mon : MonotoneOn len unitInterval :=
    variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn unitInterval.zero_mem
  have hlen_cont : ContinuousOn len unitInterval := fun t ht =>
    (hγ.continuousWithinAt_variationOnFromTo_iff unitInterval.zero_mem ht).mpr
      γ.continuous_extend.continuousWithinAt
  have hlen₀ : len 0 = 0 := variationOnFromTo.self _ _ _
  have hL : 0 < len 1 + 1 := by
    have h := hlen_mon unitInterval.zero_mem unitInterval.one_mem zero_le_one
    linarith
  let v (t : ℝ) := (len t + t) / (len 1 + 1)
  have hv₀ : v 0 = 0 := by simp [v, hlen₀]
  have hv₁ : v 1 = 1 := div_self hL.ne'
  have hv_strict : StrictMonoOn v unitInterval := by
    intro x hx y hy hxy
    apply (div_lt_div_iff_of_pos_right hL).mpr
    exact add_lt_add_of_le_of_lt (hlen_mon hx hy hxy.le) hxy
  have hv_cont : ContinuousOn v unitInterval := (hlen_cont.add continuousOn_id).div_const _
  have hv_range : v '' unitInterval = unitInterval := by
    rw [unitInterval, hv_cont.image_Icc_of_monotoneOn zero_le_one hv_strict.monotoneOn, hv₀, hv₁]
  have hv_maps : MapsTo v unitInterval unitInterval := mapsTo_iff_image_subset.mpr hv_range.le
  let ρfun (t : I) : I := ⟨v t, hv_maps t.2⟩
  have hρstrict : StrictMono ρfun := fun x y hxy => hv_strict x.2 y.2 hxy
  have hρsurj : Function.Surjective ρfun := by
    intro t
    have ht : (t : ℝ) ∈ v '' unitInterval := hv_range.symm ▸ t.2
    obtain ⟨s, hs, hst⟩ := ht
    exact ⟨⟨s, hs⟩, Subtype.ext hst⟩
  let ρ : I ≃o I := StrictMono.orderIsoOfSurjective ρfun hρstrict hρsurj
  have hρ₀ : ρ 0 = 0 := Subtype.ext hv₀
  have hρ₁ : ρ 1 = 1 := Subtype.ext hv₁
  have hdist (x y : I) : dist (γ x) (γ y) ≤ (len 1 + 1) * dist (ρ x) (ρ y) := by
    suffices hs : ∀ x y : I, x ≤ y →
        dist (γ x) (γ y) ≤ (len 1 + 1) * dist (ρ x) (ρ y) by
      rcases le_total x y with hxy | hyx
      · exact hs x y hxy
      · rw [dist_comm (γ x), dist_comm (ρ x)]
        exact hs y x hyx
    intro x y hxy
    have hsub := variationOnFromTo.sub_right hγ.locallyBoundedVariationOn
      unitInterval.zero_mem y.2 x.2
    have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
    rw [variationOnFromTo.eq_of_le _ _ hxy'] at hsub
    have hvar := hγ.mono (inter_subset_left :
      unitInterval ∩ Icc (x : ℝ) (y : ℝ) ⊆ unitInterval)
    have hdist' := ENNReal.toReal_mono hvar
      (eVariationOn.edist_le γ.extend ⟨x.2, le_rfl, hxy'⟩ ⟨y.2, hxy', le_rfl⟩)
    rw [← dist_edist, Path.extend_apply γ x.2, Path.extend_apply γ y.2] at hdist'
    change dist (γ x) (γ y) ≤ _ at hdist'
    rw [← hsub] at hdist'
    have hvxy : v x ≤ v y := hv_strict.monotoneOn x.2 y.2 hxy
    change dist (γ x) (γ y) ≤ (len 1 + 1) * |v x - v y|
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hvxy)]
    dsimp [v]
    rw [← sub_div, mul_div_cancel₀ _ hL.ne']
    linarith
  let K : NNReal := ⟨len 1 + 1, hL.le⟩
  have hLip : LipschitzWith K (fun t => γ (ρ.symm t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (γ (ρ.symm x)) (γ (ρ.symm y)) ≤ (len 1 + 1) * dist x y
    simpa only [OrderIso.apply_symm_apply] using hdist (ρ.symm x) (ρ.symm y)
  let η : Path a b :=
    ⟨⟨fun t => γ (ρ.symm t), hLip.continuous⟩,
      by
        change γ (ρ.symm 0) = a
        rw [← hρ₀, ρ.symm_apply_apply, γ.source],
      by
        change γ (ρ.symm 1) = b
        rw [← hρ₁, ρ.symm_apply_apply, γ.target]⟩
  exact ⟨ρ, η, K, hLip, fun t => congrArg γ (ρ.symm_apply_apply t)⟩

end Path

private theorem derivWithin_path_ae_eq_deriv {a b : ℂ} (γ : Path a b) :
    derivWithin γ.extend unitInterval =ᵐ[volume.restrict (Ioc 0 1)] deriv γ.extend := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo] with t ht
  exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

private theorem path_extend_mapsTo_range {a b : ℂ} (γ : Path a b) :
    MapsTo γ.extend unitInterval (Set.range γ) := by
  intro t ht
  exact ⟨⟨t, ht⟩, (Path.extend_apply γ ht).symm⟩

private theorem complexLineIntegral_eq_interval_deriv {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] {a b : ℂ} (γ : Path a b) (f : ℂ → V) :
    complexLineIntegral γ f =
      ∫ t in 0..1, deriv γ.extend t • f (γ.extend t) := by
  rw [complexLineIntegral, curveIntegral_def]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le zero_le_one]
  filter_upwards [derivWithin_path_ae_eq_deriv γ] with t ht
  simp only [curveIntegralFun_def]
  change derivWithin γ.extend unitInterval t • f (γ.extend t) = _
  rw [ht]

/-- For a Lipschitz path and a continuous integrand, the parameter integrand is interval
integrable. -/
theorem complexLineIntegral_intervalIntegrable_lipschitz {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsLipschitz) {f : ℂ → V} (hf : ContinuousOn f (Set.range γ)) :
    IntervalIntegrable (fun t => derivWithin γ.extend unitInterval t • f (γ.extend t)) volume 0 1 := by
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzWith_extend
  have hfγ : ContinuousOn (f ∘ γ.extend) unitInterval :=
    hf.comp γ.continuous_extend.continuousOn (path_extend_mapsTo_range γ)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ
  have hJ : IntervalIntegrable (fun t => deriv γ.extend t • f (γ.extend t)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hc : AEStronglyMeasurable (f ∘ γ.extend) (volume.restrict (Ioc 0 1)) :=
      hfγ.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
    have hd : AEStronglyMeasurable (deriv γ.extend) (volume.restrict (Ioc 0 1)) :=
      (measurable_deriv _).aestronglyMeasurable
    refine Integrable.of_bound (hd.smul hc) ((K : ℝ) * M) ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc]
      with t ht
    rw [norm_smul]
    exact mul_le_mul (norm_deriv_le_of_lipschitz hK) (hM t (Ioc_subset_Icc_self ht))
      (norm_nonneg _) K.2
  apply hJ.congr_ae
  rw [uIoc_of_le zero_le_one]
  filter_upwards [derivWithin_path_ae_eq_deriv γ] with t ht
  rw [ht]

/-- A holomorphic primitive integrates to its endpoint difference along a Lipschitz
parametrization. -/
theorem complexLineIntegral_derivative_lipschitz {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsLipschitz) {S : Set ℂ} (hOpen : IsOpen S) (hRange : Set.range γ ⊆ S)
    {F f : ℂ → ℂ} (hF : ∀ z ∈ S, HasDerivAt F (f z) z)
    (hf : ContinuousOn f (Set.range γ)) : complexLineIntegral γ f = F b - F a := by
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzWith_extend
  have hDiff : DifferentiableOn ℂ F S :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hLocal : LocallyLipschitzOn (Set.range γ) F := by
    intro z hz
    have hAn := hDiff.analyticAt (hOpen.mem_nhds (hRange hz))
    obtain ⟨L, t, ht, hL⟩ := hAn.contDiffAt.exists_lipschitzOnWith (𝕂 := ℂ)
    exact ⟨L, t, nhdsWithin_le_nhds ht, hL⟩
  obtain ⟨L, hL⟩ := hLocal.exists_lipschitzOnWith_of_compact (isCompact_range γ.continuous)
  let φ := F ∘ γ.extend
  have hφ : AbsolutelyContinuousOnInterval φ 0 1 := by
    apply hL.comp_absolutelyContinuousOnInterval
    · simpa only [uIcc_of_le zero_le_one] using path_extend_mapsTo_range γ
    · exact hK.lipschitzOnWith.absolutelyContinuousOnInterval
  let g (t : ℝ) := deriv γ.extend t • f (γ.extend t)
  have hg : ∀ᵐ t ∂volume.restrict (Ioo 0 1), HasDerivAt φ (g t) t := by
    have hA := (hK.ae_differentiableAt (μ := volume)).filter_mono
      (ae_mono (Measure.restrict_le_self (s := Ioo (0 : ℝ) 1)))
    filter_upwards [hA, ae_restrict_mem (μ := volume) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo]
      with t ht ht'
    have hmem := hRange (path_extend_mapsTo_range γ (Ioo_subset_Icc_self ht'))
    exact (hF (γ.extend t) hmem).scomp t ht.hasDerivAt
  have hI : IntervalIntegrable g volume 0 1 := by
    apply (complexLineIntegral_intervalIntegrable_lipschitz hγ hf).congr_ae
    rw [uIoc_of_le zero_le_one]
    filter_upwards [derivWithin_path_ae_eq_deriv γ] with t ht
    simp only [g, ht]
  have hcoord (L : ℂ →L[ℝ] ℝ) :
      L (∫ t in 0..1, g t) = L (F b - F a) := by
    have hLφ : AbsolutelyContinuousOnInterval (L ∘ φ) 0 1 :=
      L.lipschitzWith.comp_absolutelyContinuousOnInterval hφ
    rw [← L.intervalIntegral_comp_comm hI, map_sub]
    calc
      (∫ t in 0..1, L (g t)) = ∫ t in 0..1, deriv (L ∘ φ) t := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        filter_upwards [hg] with t ht
        exact (L.hasFDerivAt.comp_hasDerivAt t ht).deriv.symm
      _ = L (F b) - L (F a) := by
        rw [hLφ.integral_deriv_eq_sub]
        simp only [Function.comp_apply, φ, Path.extend_one, Path.extend_zero]
  rw [complexLineIntegral_eq_interval_deriv]
  exact Complex.ext (hcoord reCLM) (hcoord imCLM)

/-- The parameter integrand of a continuous function along a piecewise $C^1$ path is integrable. -/
theorem complexLineIntegral_intervalIntegrable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseC1)
    {f : ℂ → X} (hf : ContinuousOn f (Set.range γ)) :
    IntervalIntegrable (fun t => derivWithin γ.extend unitInterval t • f (γ.extend t))
      volume 0 1 := by
  let ω (z : ℂ) := (ContinuousLinearMap.id ℂ ℂ).smulRight (f z)
  have hEq {a b : ℂ} (γ' : Path a b) : curveIntegralFun ω γ' =
      fun t => derivWithin γ'.extend unitInterval t • f (γ'.extend t) := by
    funext t
    rw [curveIntegralFun_def]
    rfl
  have hCI : CurveIntegrable ω γ := by
    revert hf
    induction hγ with
    | single γ hγ =>
      intro hf
      rw [CurveIntegrable, hEq]
      refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
      apply (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).smul
      exact hf.comp hγ.continuousOn (fun t ht => ⟨⟨t, ht⟩, (Path.extend_apply γ ht).symm⟩)
    | @trans a b c γ₁ γ₂ _ _ ih₁ ih₂ =>
      intro hf
      rw [Path.trans_range] at hf
      exact (ih₁ (hf.mono Set.subset_union_left)).trans (ih₂ (hf.mono Set.subset_union_right))
  rw [CurveIntegrable, hEq] at hCI
  exact hCI

/-- The complex line integral of a finite sum is the sum of the integrals. -/
theorem complexLineIntegral_finset_sum {X ι : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {a b : ℂ} {γ : Path a b} (hγ : γ.IsLipschitz)
    (S : Finset ι) (f : ι → ℂ → X) (hf : ∀ i ∈ S, ContinuousOn (f i) (Set.range γ)) :
    complexLineIntegral γ (fun z => ∑ i ∈ S, f i z) = ∑ i ∈ S, complexLineIntegral γ (f i) := by
  simp only [complexLineIntegral_eq_interval, Finset.smul_sum]
  exact intervalIntegral.integral_finsetSum
    (fun i hi => complexLineIntegral_intervalIntegrable_lipschitz hγ (hf i hi))

/-- A constant vector can be taken outside a scalar-valued complex line integral. -/
theorem complexLineIntegral_smul_const {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {a b : ℂ} (γ : Path a b) (f : ℂ → ℂ) (v : X) :
    complexLineIntegral γ (fun z => f z • v) = complexLineIntegral γ f • v := by
  simp only [complexLineIntegral_eq_interval, smul_smul,
    intervalIntegral.integral_smul_const, smul_eq_mul]

/-- The complex line integral depends only on the integrand along the path. -/
theorem complexLineIntegral_congr_on_path {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {a b : ℂ} (γ : Path a b) {f g : ℂ → X}
    (h : Set.EqOn f g (Set.range γ)) : complexLineIntegral γ f = complexLineIntegral γ g := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  exact congrArg (derivWithin γ.extend unitInterval t • ·)
    (h ⟨⟨t, ht⟩, (Path.extend_apply γ ht).symm⟩)

/-- A constant scalar can be taken outside a complex line integral. -/
theorem complexLineIntegral_scalar_mul {a b : ℂ} (γ : Path a b) (c : ℂ)
    (f : ℂ → ℂ) :
    complexLineIntegral γ (fun z => c * f z) = c * complexLineIntegral γ f := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval]
  simp only [smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  rw [intervalIntegral.integral_const_mul]

/-- The line integral of a difference equals the difference of the integrals. -/
theorem complexLineIntegral_sub_of_continuousOn {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsLipschitz) {f g : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ))
    (hg : ContinuousOn g (Set.range γ)) :
    complexLineIntegral γ (fun z => f z - g z) =
      complexLineIntegral γ f - complexLineIntegral γ g := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval,
    complexLineIntegral_eq_interval]
  simp_rw [smul_sub]
  exact intervalIntegral.integral_sub (complexLineIntegral_intervalIntegrable_lipschitz hγ hf)
    (complexLineIntegral_intervalIntegrable_lipschitz hγ hg)

/-- The complex line integral of a derivative is the difference of endpoint values. -/
theorem complexLineIntegral_derivative {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsPiecewiseC1) {f F : ℂ → ℂ}
    (hF : ∀ z ∈ Set.range γ, HasDerivAt F (f z) z)
    (hf : ContinuousOn f (Set.range γ)) :
    complexLineIntegral γ f = F b - F a := by
  induction hγ with
  | single γ hγ =>
    rw [complexLineIntegral_eq_interval]
    have hm (t : ℝ) (ht : t ∈ unitInterval) : γ.extend t ∈ Set.range γ :=
      ⟨⟨t, ht⟩, (Path.extend_apply γ ht).symm⟩
    have hFc : ContinuousOn F (Set.range γ) :=
      fun z hz => (hF z hz).continuousAt.continuousWithinAt
    have hc : ContinuousOn (F ∘ γ.extend) unitInterval := hFc.comp hγ.continuousOn hm
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc
      (fun t ht => by
        have hn : unitInterval ∈ nhds t := Icc_mem_nhds ht.1 ht.2
        have ht' : t ∈ unitInterval := Ioo_subset_Icc_self ht
        have hcurve := ((hγ.differentiableOn (by norm_num) t ht').differentiableAt hn).hasDerivAt
        have h := (hF (γ.extend t) (hm t ht')).scomp t hcurve
        simpa only [derivWithin_of_mem_nhds hn] using h)
      (complexLineIntegral_intervalIntegrable (Path.IsPiecewiseC1.single γ hγ) hf)
    simpa only [Function.comp_apply, Path.extend_one, Path.extend_zero] using hh
  | @trans a b c γ₁ γ₂ hγ₁ hγ₂ ih₁ ih₂ =>
    rw [Path.trans_range] at hF hf
    let ω (z : ℂ) := (ContinuousLinearMap.id ℂ ℂ).smulRight (f z)
    have hint {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseC1)
        (hf : ContinuousOn f (Set.range γ)) : CurveIntegrable ω γ := by
      have he : curveIntegralFun ω γ =
          fun t => derivWithin γ.extend unitInterval t • f (γ.extend t) := by
        funext t
        rw [curveIntegralFun_def]
        rfl
      rw [CurveIntegrable, he]
      exact complexLineIntegral_intervalIntegrable hγ hf
    have hf₁ := hf.mono Set.subset_union_left
    have hf₂ := hf.mono Set.subset_union_right
    have he : complexLineIntegral (γ₁.trans γ₂) f =
        complexLineIntegral γ₁ f + complexLineIntegral γ₂ f :=
      curveIntegral_trans (hint hγ₁ hf₁) (hint hγ₂ hf₂)
    rw [he, ih₁ (fun z hz => hF z (Or.inl hz)) hf₁,
      ih₂ (fun z hz => hF z (Or.inr hz)) hf₂]
    abel

/-- The line integral of a sum equals the sum of the integrals. -/
theorem complexLineIntegral_add_of_continuousOn {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsLipschitz) {f g : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ))
    (hg : ContinuousOn g (Set.range γ)) :
    complexLineIntegral γ (fun z => f z + g z) =
      complexLineIntegral γ f + complexLineIntegral γ g := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval,
    complexLineIntegral_eq_interval]
  simp_rw [smul_add]
  exact intervalIntegral.integral_add (complexLineIntegral_intervalIntegrable_lipschitz hγ hf)
    (complexLineIntegral_intervalIntegrable_lipschitz hγ hg)

/-- A holomorphic function on an open convex set integrates to zero
along any Lipschitz loop in that set. -/
theorem complexLineIntegral_zero_of_differentiableOn_convex {a : ℂ} {γ : Path a a}
    (hγ : γ.IsLipschitz) {S : Set ℂ} (hOpen : IsOpen S) (hConvex : Convex ℝ S)
    (hRange : Set.range γ ⊆ S) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    complexLineIntegral γ f = 0 := by
  obtain ⟨F, hF⟩ := hConvex.exists_forall_hasDerivWithinAt hf
  rw [complexLineIntegral_derivative_lipschitz hγ hOpen hRange
    (fun z hz => (hF z hz).hasDerivAt (hOpen.mem_nhds hz))
    (hf.continuousOn.mono hRange), sub_self]

/-- A continuous linear map commutes with complex line integration. -/
theorem complexLineIntegral_map {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℂ X] [NormedSpace ℂ Y]
    [CompleteSpace X] [CompleteSpace Y]
    {a b : ℂ} {γ : Path a b} (hγ : γ.IsLipschitz) {f : ℂ → X}
    (hf : ContinuousOn f (Set.range γ)) (L : X →L[ℂ] Y) :
    complexLineIntegral γ (fun z => L (f z)) = L (complexLineIntegral γ f) := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval]
  simp_rw [← map_smul]
  exact L.intervalIntegral_comp_comm (complexLineIntegral_intervalIntegrable_lipschitz hγ hf)

private noncomputable def inversePolePrimitive (w : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  ((-(j : ℤ)) : ℂ)⁻¹ * (z - w) ^ (-(j : ℤ))

private theorem hasDerivAt_inversePolePrimitive {w z : ℂ} (hz : z ≠ w) {j : ℕ}
    (hj : 0 < j) :
    HasDerivAt (inversePolePrimitive w j) (((z - w) ^ (j + 1))⁻¹) z := by
  let m : ℤ := -(j : ℤ)
  let F : ℂ → ℂ := fun z => (m : ℂ)⁻¹ * (z - w) ^ m
  have hm : (m : ℂ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have h := ((hasDerivAt_zpow m (z - w) (Or.inl (sub_ne_zero.mpr hz))).comp z
        ((hasDerivAt_id z).sub_const w)).const_mul ((m : ℂ)⁻¹)
  change HasDerivAt F ((m : ℂ)⁻¹ * (((m : ℂ) * (z - w) ^ (m - 1)) * 1)) z at h
  have he : m - 1 = -((j + 1 : ℕ) : ℤ) := by omega
  rw [mul_one, ← mul_assoc, inv_mul_cancel₀ hm, one_mul, he, zpow_neg, zpow_natCast] at h
  have hFun : F = inversePolePrimitive w j := by
    funext x
    simp only [F, m, inversePolePrimitive, Int.cast_neg]
  exact hFun ▸ h

/-- A pole of order at least two has zero integral along a closed path avoiding its pole. -/
theorem complexLineIntegral_inversePole_succ_eq_zero {a w : ℂ} (γ : Path a a)
    (hγ : γ.IsLipschitz) (hw : w ∉ Set.range γ) {j : ℕ} (hj : 0 < j) :
    complexLineIntegral γ (fun z => ((z - w) ^ (j + 1))⁻¹) = 0 := by
  have hRange : Set.range γ ⊆ {w}ᶜ := fun z hz he => hw (mem_singleton_iff.mp he ▸ hz)
  have hc : ContinuousOn (fun z : ℂ => ((z - w) ^ (j + 1))⁻¹) (Set.range γ) :=
    ((continuousOn_id.sub continuousOn_const).pow _).inv₀ fun z hz =>
      pow_ne_zero _ (sub_ne_zero.mpr (fun (he : z = w) => hw (he ▸ hz)))
  rw [complexLineIntegral_derivative_lipschitz hγ isOpen_compl_singleton hRange
    (fun _ hz => hasDerivAt_inversePolePrimitive hz hj) hc, sub_self]

private theorem iterate_dslope_eq_taylorJet {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (j : ℕ) :
    (Function.swap dslope w)^[j] f w = Hermite.taylorJet f w j := by
  obtain ⟨p, hp⟩ := hf
  have hds := hp.has_fpower_series_iterate_dslope_fslope j
  obtain ⟨r, hr⟩ := hp
  obtain ⟨q, hq, hcoeff⟩ := hr.exists_hasFPowerSeriesOnBall_iteratedDeriv j
  have hq₀ : q.coeff 0 = iteratedDeriv j f w := hq.coeff_zero 1
  rw [hcoeff, Nat.zero_add, Nat.descFactorial_self] at hq₀
  rw [← hds.coeff_zero 1, ← FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.coeff_iterate_fslope, Nat.zero_add, Hermite.taylorJet, ← hq₀]
  rw [mul_comm, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr j.factorial_ne_zero)]

private theorem continuousOn_inversePole {a b w : ℂ} {γ : Path a b}
    (hAvoid : w ∉ Set.range γ) (j : ℕ) :
    ContinuousOn (fun z => ((z - w) ^ j)⁻¹) (Set.range γ) :=
  ((continuousOn_id.sub continuousOn_const).pow j).inv₀ fun z hz =>
    pow_ne_zero j (sub_ne_zero.mpr (fun (he : z = w) => hAvoid (he ▸ hz)))

private theorem complexLineIntegral_dslope {a w : ℂ} (γ : Path a a)
    (hγ : γ.IsLipschitz) (hAvoid : w ∉ Set.range γ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range γ)) (j : ℕ) :
    complexLineIntegral γ (fun z => f z / (z - w) ^ (j + 2)) =
      complexLineIntegral γ (fun z => dslope f w z / (z - w) ^ (j + 1)) := by
  have hDecompose : Set.EqOn (fun z => f z / (z - w) ^ (j + 2))
      (fun z => dslope f w z / (z - w) ^ (j + 1) + f w * ((z - w) ^ (j + 2))⁻¹)
      (Set.range γ) := by
    intro z hz
    have hne : z ≠ w := fun he => hAvoid (he ▸ hz)
    have hsub : z - w ≠ 0 := sub_ne_zero.mpr hne
    simp only [dslope_of_ne _ hne, slope_def_field, pow_succ _ (j + 1)]
    field_simp
    ring
  have hInv := continuousOn_inversePole hAvoid (j + 2)
  have hD : ContinuousOn (dslope f w) (Set.range γ) := by
    intro z hz
    exact (continuousWithinAt_dslope_of_ne (fun (he : z = w) => hAvoid (he ▸ hz))).mpr (hf z hz)
  have hLeft : ContinuousOn (fun z => dslope f w z / (z - w) ^ (j + 1)) (Set.range γ) := by
    simp only [div_eq_mul_inv]
    exact hD.mul (continuousOn_inversePole hAvoid (j + 1))
  have hRight : ContinuousOn (fun z => f w * ((z - w) ^ (j + 2))⁻¹) (Set.range γ) :=
    continuousOn_const.mul hInv
  rw [complexLineIntegral_congr_on_path γ hDecompose,
    complexLineIntegral_add_of_continuousOn hγ hLeft hRight,
    complexLineIntegral_scalar_mul,
    complexLineIntegral_inversePole_succ_eq_zero γ hγ hAvoid (Nat.succ_pos j), mul_zero, add_zero]

private theorem complexLineIntegral_eq_iterate_dslope {a w : ℂ} (γ : Path a a)
    (hγ : γ.IsLipschitz) (hAvoid : w ∉ Set.range γ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range γ)) (j : ℕ) :
    complexLineIntegral γ (fun z => f z / (z - w) ^ (j + 1)) =
      complexLineIntegral γ (fun z => ((Function.swap dslope w)^[j] f) z / (z - w)) := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    rw [complexLineIntegral_dslope γ hγ hAvoid hf, ih, Function.iterate_succ_apply]
    intro z hz
    exact (continuousWithinAt_dslope_of_ne (fun (he : z = w) => hAvoid (he ▸ hz))).mpr (hf z hz)

private theorem complexLineIntegral_simplePole_of_differentiableOn_convex
    {a w : ℂ} {S : Set ℂ} (γ : Path a a) (hγ : γ.IsLipschitz)
    (hOpen : IsOpen S) (hConvex : Convex ℝ S) (hRange : Set.range γ ⊆ S) (hAvoid : w ∉ Set.range γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    complexLineIntegral γ (fun z => f z / (z - w)) =
      f w * complexLineIntegral γ (fun z => (z - w)⁻¹) := by
  have hDiff : DifferentiableOn ℂ (dslope f w) S := by
    intro z hz
    exact ((hf.analyticAt (hOpen.mem_nhds hz)).dslope w
      ).differentiableAt.differentiableWithinAt
  have hEq : Set.EqOn (fun z => f z / (z - w))
      (fun z => dslope f w z + f w * (z - w)⁻¹) (Set.range γ) := by
    intro z hz
    have hne : z ≠ w := fun he => hAvoid (he ▸ hz)
    simp only [dslope_of_ne f hne, slope_def_field]
    ring
  have hPole : ContinuousOn (fun z => f w * (z - w)⁻¹) (Set.range γ) := by
    have hInv : ContinuousOn (fun z => (z - w)⁻¹) (Set.range γ) := by
      simpa only [pow_one] using continuousOn_inversePole hAvoid 1
    exact continuousOn_const.mul hInv
  rw [complexLineIntegral_congr_on_path γ hEq,
    complexLineIntegral_add_of_continuousOn hγ (hDiff.continuousOn.mono hRange) hPole,
    complexLineIntegral_zero_of_differentiableOn_convex hγ hOpen hConvex hRange hDiff, zero_add,
    complexLineIntegral_scalar_mul]

private theorem differentiableOn_iterate_dslope {S : Set ℂ} (hOpen : IsOpen S) (w : ℂ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) (j : ℕ) :
    DifferentiableOn ℂ ((Function.swap dslope w)^[j] f) S := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    intro z hz
    exact ((ih.analyticAt (hOpen.mem_nhds hz)).dslope w
      ).differentiableAt.differentiableWithinAt

/-- Cauchy's formula for derivatives along any Lipschitz loop contained in
an open convex set of holomorphy. At a point off the loop, the normalized
integral is its winding number times the
corresponding Taylor coefficient. Points outside the set contribute zero. -/
theorem normalized_complexLineIntegral_div_sub_pow {a w : ℂ} {S : Set ℂ} (γ : Path a a)
    (hγ : γ.IsLipschitz)
    (hOpen : IsOpen S) (hConvex : Convex ℝ S) (hRange : Set.range γ ⊆ S)
    (hAvoid : w ∉ Set.range γ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S)
    (j : ℕ) :
    (2 * π * I)⁻¹ * complexLineIntegral γ (fun z => f z / (z - w) ^ (j + 1)) =
      complexPathIndex γ w * Hermite.taylorJet f w j := by
  by_cases hw : w ∈ S
  · rw [complexLineIntegral_eq_iterate_dslope γ hγ hAvoid (hf.continuousOn.mono hRange),
      complexLineIntegral_simplePole_of_differentiableOn_convex γ hγ hOpen hConvex hRange hAvoid
        (differentiableOn_iterate_dslope hOpen w hf j),
      iterate_dslope_eq_taylorJet (hf.analyticAt (hOpen.mem_nhds hw)) j,
      complexPathIndex]
    ring
  · have hne (z : ℂ) (hz : z ∈ S) : z - w ≠ 0 :=
      sub_ne_zero.mpr (fun he => hw (he ▸ hz))
    have hsub : DifferentiableOn ℂ (fun z => z - w) S :=
      differentiableOn_id.sub_const w
    have hfDiv : DifferentiableOn ℂ (fun z => f z / (z - w) ^ (j + 1)) S :=
      hf.div (hsub.pow (j + 1)) (fun z hz => pow_ne_zero _ (hne z hz))
    have hInv : DifferentiableOn ℂ (fun z => (z - w)⁻¹) S := hsub.inv hne
    rw [complexLineIntegral_zero_of_differentiableOn_convex hγ hOpen hConvex hRange hfDiv,
      complexPathIndex,
      complexLineIntegral_zero_of_differentiableOn_convex hγ hOpen hConvex hRange hInv]
    simp

/-- Cauchy's formula for the simple pole on a Lipschitz loop in a disk of holomorphy. -/
theorem normalized_complexLineIntegral_cauchy_disk {a w c : ℂ} (γ : Path a a)
    (hγ : γ.IsLipschitz) {R : ℝ} (hDisk : Set.range γ ⊆ Metric.ball c R)
    (hAvoid : w ∉ Set.range γ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball c R)) :
    (2 * π * I)⁻¹ * complexLineIntegral γ (fun z => (z - w)⁻¹ * f z) =
      complexPathIndex γ w * f w := by
  simpa only [zero_add, pow_one, Hermite.taylorJet_zero, div_eq_inv_mul] using
    normalized_complexLineIntegral_div_sub_pow γ hγ Metric.isOpen_ball
      (convex_ball _ _) hDisk hAvoid hf 0

section ComplexContourParameters

open Filter Metric Topology Bornology

private theorem complexLineIntegral_hasDerivAt_parameter {a b z₀ : ℂ} {γ : Path a b}
    (hγ : γ.IsLipschitz) {U : Set ℂ} (hU : IsOpen U) (hz₀ : z₀ ∈ U) {F D : ℂ → ℂ → ℂ}
    (hF : ∀ z ∈ U, ContinuousOn (F z) (Set.range γ))
    (hD : ContinuousOn (fun p : ℂ × ℂ => D p.1 p.2) (U ×ˢ Set.range γ))
    (hd : ∀ z ∈ U, ∀ w ∈ Set.range γ, HasDerivAt (fun x => F x w) (D z w) z) :
    HasDerivAt (fun z => complexLineIntegral γ (F z)) (complexLineIntegral γ (D z₀)) z₀ := by
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzWith_extend
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  have hC : Metric.closedBall z₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrU
  have hγC : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hBall : IsCompact (Metric.closedBall z₀ (r / 2)) := isCompact_closedBall z₀ (r / 2)
  obtain ⟨C, hCbound⟩ := (hBall.prod hγC).exists_bound_of_continuousOn
    (hD.mono (Set.prod_mono hC Subset.rfl))
  have hMeas {g : ℂ → ℂ} (hg : ContinuousOn g (Set.range γ)) :
      AEStronglyMeasurable (fun t : ℝ => deriv γ.extend t * g (γ.extend t))
        (volume.restrict (uIoc (0 : ℝ) 1)) := by
    rw [uIoc_of_le zero_le_one]
    have hc : ContinuousOn (g ∘ γ.extend) unitInterval :=
      hg.comp γ.continuous_extend.continuousOn (path_extend_mapsTo_range γ)
    exact (measurable_deriv _).aestronglyMeasurable.mul
      (hc.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self)
  have hInt : IntervalIntegrable (fun t : ℝ => deriv γ.extend t * F z₀ (γ.extend t)) volume 0 1 := by
    apply (complexLineIntegral_intervalIntegrable_lipschitz hγ (hF z₀ hz₀)).congr_ae
    rw [uIoc_of_le zero_le_one]
    filter_upwards [derivWithin_path_ae_eq_deriv γ] with t ht
    simp only [ht, smul_eq_mul]
  have hD₀ : ContinuousOn (D z₀) (Set.range γ) :=
    hD.comp (f := fun w : ℂ => (z₀, w)) (by fun_prop) (fun _ hw => ⟨hz₀, hw⟩)
  simp only [complexLineIntegral_eq_interval_deriv, smul_eq_mul]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun z t => deriv γ.extend t * D z (γ.extend t))
    (bound := fun _ => (K : ℝ) * C)
    (ball_mem_nhds z₀ (half_pos hr))
    (eventually_of_mem (hU.mem_nhds hz₀) fun z hz => hMeas (hF z hz))
    hInt (hMeas hD₀) ?_ intervalIntegrable_const ?_).2
  · apply ae_of_all
    intro t ht z hz
    rw [uIoc_of_le zero_le_one] at ht
    have hγt := path_extend_mapsTo_range γ (Ioc_subset_Icc_self ht)
    rw [norm_mul]
    exact mul_le_mul (norm_deriv_le_of_lipschitz hK)
      (hCbound (z, γ.extend t) ⟨ball_subset_closedBall hz, hγt⟩)
      (norm_nonneg _) K.2
  · apply ae_of_all
    intro t ht z hz
    rw [uIoc_of_le zero_le_one] at ht
    exact (hd z (hC (ball_subset_closedBall hz)) _
      (path_extend_mapsTo_range γ (Ioc_subset_Icc_self ht))).const_mul _

/-- Differentiating the Cauchy kernel under the integral along a Lipschitz path. -/
theorem complexLineIntegral_hasDerivAt_cauchyTransform {a b z : ℂ} {γ : Path a b}
    (hγ : γ.IsLipschitz) {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) (hz : z ∉ Set.range γ) :
    HasDerivAt (fun x => complexLineIntegral γ (fun w => f w / (w - x)))
      (complexLineIntegral γ (fun w => f w / (w - z) ^ 2)) z := by
  have hOpen : IsOpen ((Set.range γ)ᶜ) := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hne (z : ℂ) (hz : z ∉ Set.range γ) (w : ℂ) (hw : w ∈ Set.range γ) : w - z ≠ 0 :=
    sub_ne_zero.mpr fun h => hz (h ▸ hw)
  refine complexLineIntegral_hasDerivAt_parameter hγ hOpen hz
    (F := fun z w => f w / (w - z)) (D := fun z w => f w / (w - z) ^ 2) ?_ ?_ ?_
  · intro z hz
    exact hf.div (continuousOn_id.sub continuousOn_const) fun w hw => hne z hz w hw
  · have hproj : MapsTo (@Prod.snd ℂ ℂ) ((Set.range γ)ᶜ ×ˢ Set.range γ) (Set.range γ) :=
      fun _ hp => hp.2
    exact (hf.comp continuous_snd.continuousOn hproj).div
      ((continuous_snd.sub continuous_fst).pow 2).continuousOn
      (fun p hp => pow_ne_zero _ (hne p.1 hp.1 p.2 hp.2))
  · intro z hz w hw
    have h := ((hasDerivAt_const z w).sub (hasDerivAt_id z)).inv (hne z hz w hw)
    have h' := h.const_mul (f w)
    convert h' using 1
    · funext x
      simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]

/-- Off the path, the winding index has derivative zero. -/
theorem complexPathIndex_hasDerivAt_zero {a z : ℂ} {γ : Path a a}
    (hγ : γ.IsLipschitz) (hz : z ∉ Set.range γ) :
    HasDerivAt (complexPathIndex γ) 0 z := by
  have h := complexLineIntegral_hasDerivAt_cauchyTransform hγ
    (f := fun _ => 1) continuousOn_const hz
  have hzero := complexLineIntegral_inversePole_succ_eq_zero γ hγ hz (j := 1) one_pos
  rw [show (fun w : ℂ => (1 : ℂ) / (w - z) ^ 2) = (fun w => ((w - z) ^ (1 + 1))⁻¹) by simp [one_div], hzero] at h
  have h' := h.const_mul ((2 * π * I)⁻¹)
  rw [mul_zero] at h'
  convert h' using 1
  funext x
  simp only [complexPathIndex, one_div]

/-- The winding index is locally constant off a closed Lipschitz path. -/
theorem complexPathIndex_eventuallyEq {a z : ℂ} {γ : Path a a}
    (hγ : γ.IsLipschitz) (hz : z ∉ Set.range γ) :
    complexPathIndex γ =ᶠ[𝓝 z] (fun _ => complexPathIndex γ z) := by
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    ((isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds hz)
  have hDer (w : ℂ) (hw : w ∈ Metric.ball z r) : HasDerivAt (complexPathIndex γ) 0 w :=
    complexPathIndex_hasDerivAt_zero hγ (hrsub hw)
  have hConst (w : ℂ) (hw : w ∈ Metric.ball z r) : complexPathIndex γ w = complexPathIndex γ z :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected
    (f := complexPathIndex γ)
    (fun w hw => (hDer w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hDer w hw).deriv) hw (Metric.mem_ball_self hr)
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  exact hConst w hw

private theorem complexPathIndex_zero_of_contained_ball {a z : ℂ} {γ : Path a a}
    (hγ : γ.IsLipschitz) {R : ℝ} (hK : Set.range γ ⊆ Metric.ball (0 : ℂ) R) (hz : R ≤ ‖z‖) :
    complexPathIndex γ z = 0 := by
  have hne (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) R) : w - z ≠ 0 := by
    refine sub_ne_zero.mpr (fun h => ?_)
    exact (not_lt_of_ge hz) (by simpa [h] using hw)
  have hDiff : DifferentiableOn ℂ (fun w : ℂ => (w - z)⁻¹) (Metric.ball (0 : ℂ) R) :=
    (differentiableOn_id.sub_const z).inv hne
  rw [complexPathIndex, complexLineIntegral_zero_of_differentiableOn_convex hγ
    Metric.isOpen_ball (convex_ball _ _) hK hDiff, mul_zero]

end ComplexContourParameters


section ComplexContourSlopes

open Filter Metric Topology Bornology

private noncomputable def weightedComplexSegmentAverage (f : ℂ → ℂ) (k : ℕ) (a z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, t ^ k • f (a + t • (z - a))

private theorem continuousOn_weightedComplexSegmentAverage {K : Set ℂ}
    (hK : IsCompact K) (hConv : Convex ℝ K) {f : ℂ → ℂ} (hf : ContinuousOn f K) (k : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => weightedComplexSegmentAverage f k p.2 p.1) (K ×ˢ K) := by
  let : CompactSpace ↥(K ×ˢ K) := isCompact_iff_compactSpace.mp (hK.prod hK)
  let P (q : ↥(K ×ˢ K) × ℝ) : ℂ :=
    q.1.1.2 + ((projIcc 0 1 zero_le_one q.2 : Icc (0 : ℝ) 1) : ℝ) • (q.1.1.1 - q.1.1.2)
  have hPk (q : ↥(K ×ˢ K) × ℝ) : P q ∈ K :=
    hConv.add_smul_sub_mem q.1.2.2 q.1.2.1 (projIcc 0 1 zero_le_one q.2).2
  have hPc : Continuous P := by
    have hp : Continuous fun q : ↥(K ×ˢ K) × ℝ =>
        ((projIcc 0 1 zero_le_one q.2 : Icc (0 : ℝ) 1) : ℝ) :=
      continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)
    unfold P
    fun_prop
  let F (q : ↥(K ×ˢ K)) (t : ℝ) := ((projIcc 0 1 zero_le_one t : Icc (0 : ℝ) 1) : ℝ)^k • f (P (q,t))
  have hF : Continuous F.uncurry := by
    have hφ : Continuous (fun q : ↥(K ×ˢ K) × ℝ => f (P q)) :=
      (continuousOn_iff_continuous_domRestrict.mp hf).comp (hPc.subtype_mk hPk)
    have hp : Continuous fun q : ↥(K ×ˢ K) × ℝ =>
        ((projIcc 0 1 zero_le_one q.2 : Icc (0 : ℝ) 1) : ℝ) :=
      continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)
    exact (hp.pow k).smul hφ
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  apply continuousOn_iff_continuous_domRestrict.mpr
  refine hi.congr fun q => ?_
  change (∫ t in Icc (0 : ℝ) 1, F q t) = weightedComplexSegmentAverage f k q.1.2 q.1.1
  rw [weightedComplexSegmentAverage, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp [F, P, projIcc_of_mem _ ht]

private theorem dslope_eq_weightedComplexSegmentAverage {U : Set ℂ} (hConv : Convex ℝ U)
    {f : ℂ → ℂ} (hD : ∀ w ∈ U, HasDerivAt f (deriv f w) w)
    (hc : ContinuousOn (deriv f) U) {a z : ℂ} (ha : a ∈ U) (hz : z ∈ U) :
    dslope f a z = weightedComplexSegmentAverage (deriv f) 0 a z := by
  by_cases he : z = a
  · subst z
    simp [dslope_same, weightedComplexSegmentAverage]
  · rw [dslope_of_ne _ he, slope_def_field]
    have h := eq_add_smul_integral_comp_segment hConv hD hc ha hz
    change f z = f a + (z - a) * ∫ t in (0 : ℝ)..1, deriv f (a + t • (z - a)) at h
    rw [h, add_sub_cancel_left, weightedComplexSegmentAverage]
    simp only [pow_zero, one_smul]
    field_simp

private theorem hasDerivAt_dslope_segment {U : Set ℂ} (hOpen : IsOpen U) (hConv : Convex ℝ U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) {a z : ℂ} (ha : a ∈ U) (hz : z ∈ U) :
    HasDerivAt (dslope f a) (weightedComplexSegmentAverage (deriv (deriv f)) 1 a z) z := by
  have hD (w : ℂ) (hw : w ∈ U) : HasDerivAt f (deriv f w) w := (hf w hw).differentiableAt.hasDerivAt
  have hDC := hf.deriv.continuousOn
  have hi := hasDerivAt_integral_pow_smul_comp_segment hOpen hConv
    (fun w hw => (hf.deriv w hw).differentiableAt.hasDerivAt) hf.deriv.deriv.continuousOn ha hz 0
  apply hi.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hz] with w hw
  exact dslope_eq_weightedComplexSegmentAverage hConv hD hDC ha hw

private theorem hasDerivAt_dslope_formula {f : ℂ → ℂ} {z w : ℂ} (hf : DifferentiableAt ℂ f z) (h : z ≠ w) :
    HasDerivAt (dslope f w) ((deriv f z * (z - w) - (f z - f w)) / (z - w)^2) z := by
  have hquot := (hf.hasDerivAt.sub_const (f w)).div ((hasDerivAt_id z).sub_const w) (sub_ne_zero.mpr h)
  have hQ : HasDerivAt (fun x => (f x - f w) / (x - w))
      ((deriv f z * (z - w) - (f z - f w)) / (z - w)^2) z := by
    simpa only [id_eq, mul_one, Pi.div_def] using hquot
  apply hQ.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds h] with x hx
  rw [dslope_of_ne _ hx, slope_def_field]

private theorem complexDslope_joint_continuous {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.2 p.1) (U ×ˢ U) ∧
      ContinuousOn (fun p : ℂ × ℂ => deriv (dslope f p.2) p.1) (U ×ˢ U) := by
  have hD (w : ℂ) (hw : w ∈ U) : HasDerivAt f (deriv f w) w := (hf w hw).differentiableAt.hasDerivAt
  have hpair : ∀ p : ℂ × ℂ, p ∈ U ×ˢ U →
      ContinuousAt (fun p : ℂ × ℂ => dslope f p.2 p.1) p ∧
      ContinuousAt (fun p : ℂ × ℂ => deriv (dslope f p.2) p.1) p := by
    intro p hp
    by_cases he : p.1 = p.2
    · obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU p.1 hp.1
      let B := Metric.ball p.1 r
      let K := Metric.closedBall p.1 (r/2)
      have hKB : K ⊆ B := closedBall_subset_ball (half_lt_self hr)
      have hB : B ⊆ U := hrU
      have hKU : K ⊆ U := hKB.trans hB
      have hK : K ×ˢ K ∈ 𝓝 p := by
        rw [nhds_prod_eq]
        exact prod_mem_prod (closedBall_mem_nhds _ (half_pos hr)) (he ▸ closedBall_mem_nhds _ (half_pos hr))
      have hBOpen : IsOpen B := isOpen_ball
      have hBC : Convex ℝ B := convex_ball _ _
      have hJ₁ := continuousOn_weightedComplexSegmentAverage
        (K := K) (isCompact_closedBall _ _) (convex_closedBall _ _) (hf.deriv.continuousOn.mono hKU) 0
      have hJ₂ := continuousOn_weightedComplexSegmentAverage
        (K := K) (isCompact_closedBall _ _) (convex_closedBall _ _) (hf.deriv.deriv.continuousOn.mono hKU) 1
      constructor
      · apply (hJ₁.continuousAt hK).congr
        filter_upwards [hK] with q hq
        exact (dslope_eq_weightedComplexSegmentAverage hBC
          (fun w hw => hD w (hB hw)) (hf.deriv.continuousOn.mono hB) (hKB hq.2) (hKB hq.1)).symm
      · apply (hJ₂.continuousAt hK).congr
        filter_upwards [hK] with q hq
        exact (hasDerivAt_dslope_segment hBOpen hBC (hf.mono hB) (hKB hq.2) (hKB hq.1)).deriv.symm
    · have hp₁ : ContinuousAt (fun q : ℂ × ℂ => f q.1) p :=
        (hf p.1 hp.1).continuousAt.comp continuous_fst.continuousAt
      have hp₂ : ContinuousAt (fun q : ℂ × ℂ => f q.2) p :=
        (hf p.2 hp.2).continuousAt.comp continuous_snd.continuousAt
      have hpD : ContinuousAt (fun q : ℂ × ℂ => deriv f q.1) p :=
        (hf.deriv p.1 hp.1).continuousAt.comp continuous_fst.continuousAt
      have hsub : ContinuousAt (fun q : ℂ × ℂ => q.1 - q.2) p :=
        continuous_fst.continuousAt.sub continuous_snd.continuousAt
      have hne : ∀ᶠ q : ℂ × ℂ in 𝓝 p, q.1 ≠ q.2 := (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds he
      constructor
      · apply ((hp₁.sub hp₂).div hsub (sub_ne_zero.mpr he)).congr
        filter_upwards [hne] with q hq
        rw [dslope_of_ne _ hq, slope_def_field]
        rfl
      · apply (((hpD.mul hsub).sub (hp₁.sub hp₂)).div (hsub.pow 2) (pow_ne_zero _ (sub_ne_zero.mpr he))).congr
        filter_upwards [hne, (hU.prod hU).mem_nhds hp] with q hq hqU
        exact (hasDerivAt_dslope_formula (hf q.1 hqU.1).differentiableAt hq).deriv.symm
  exact ⟨fun p hp => (hpair p hp).1.continuousWithinAt, fun p hp => (hpair p hp).2.continuousWithinAt⟩

private theorem differentiableOn_complexLineIntegral_dslope {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsLipschitz) {U : Set ℂ} (hU : IsOpen U) (hRange : Set.range γ ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun z => complexLineIntegral γ (fun w => dslope f w z)) U := by
  have hA := hf.analyticOnNhd hU
  have h := complexDslope_joint_continuous hU hA
  intro z hz
  apply (complexLineIntegral_hasDerivAt_parameter hγ hU hz
    (F := fun x w => dslope f w x) (D := fun x w => deriv (dslope f w) x) ?_ ?_ ?_).differentiableAt.differentiableWithinAt
  · intro x hx
    exact h.1.comp (f := fun w : ℂ => (x, w)) (by fun_prop) fun _ hw => ⟨hx, hRange hw⟩
  · exact h.2.mono (Set.prod_mono Subset.rfl hRange)
  · intro x hx w _
    exact ((hA x hx).dslope w).differentiableAt.hasDerivAt

end ComplexContourSlopes


section HomologicalCauchy

open Filter Metric Topology Bornology

private theorem tendsto_complexLineIntegral_cauchyTransform {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsLipschitz) {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) :
    Tendsto (fun z => complexLineIntegral γ (fun w => f w / (w - z))) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzWith_extend
  have hRange : IsCompact (Set.range γ) := isCompact_range γ.continuous
  obtain ⟨R, hR⟩ := hRange.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (id : ℂ → ℂ) _)
  obtain ⟨M, hM⟩ := hRange.exists_bound_of_continuousOn hf
  have hM₀ : 0 ≤ M := (norm_nonneg (f (γ 0))).trans (hM _ (mem_range_self 0))
  refine squeeze_zero_norm' (a := fun z => (K : ℝ) * M / (‖z‖ - R)) ?_ ?_
  · filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
    rw [complexLineIntegral_eq_interval_deriv]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := (K : ℝ) * M / (‖z‖ - R))
      (f := fun t => deriv γ.extend t • (f (γ.extend t) / (γ.extend t - z)))
    rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at h
    apply h
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have hw := path_extend_mapsTo_range γ (Ioc_subset_Icc_self ht)
    have hR' : ‖γ.extend t‖ ≤ R := hR _ hw
    have hdist : ‖z‖ - R ≤ ‖γ.extend t - z‖ := by
      have he := norm_le_norm_sub_add (z : ℂ) (γ.extend t)
      rw [norm_sub_rev] at he
      linarith
    rw [norm_smul, norm_div]
    have hdiv : ‖f (γ.extend t)‖ / ‖γ.extend t - z‖ ≤ M / (‖z‖ - R) :=
      div_le_div₀ hM₀ (hM _ hw) (sub_pos.mpr hz) hdist
    rw [mul_div_assoc]
    exact mul_le_mul (norm_deriv_le_of_lipschitz hK) hdiv (by positivity) K.2
  · refine tendsto_const_nhds.div_atTop ?_
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right _ (-R) (tendsto_norm_cocompact_atTop (E := ℂ))

/-- The total winding number of a finite family of closed paths. -/
noncomputable def complexTotalPathIndex {ι : Type*} [Fintype ι] {a : ι → ℂ}
    (γ : (i : ι) → Path (a i) (a i)) (z : ℂ) : ℂ := ∑ i, complexPathIndex (γ i) z

private theorem complexTotalPathIndex_eventuallyEq {ι : Type*} [Fintype ι]
    {a : ι → ℂ} {γ : (i : ι) → Path (a i) (a i)} (hγ : ∀ i, (γ i).IsLipschitz)
    {z : ℂ} (hz : ∀ i, z ∉ Set.range (γ i)) :
    complexTotalPathIndex γ =ᶠ[𝓝 z] (fun _ => complexTotalPathIndex γ z) := by
  have h : ∀ᶠ w in 𝓝 z, ∀ i, complexPathIndex (γ i) w = complexPathIndex (γ i) z :=
    eventually_all.mpr fun i => complexPathIndex_eventuallyEq (hγ i) (hz i)
  exact h.mono fun _ hw => Finset.sum_congr rfl (fun i _ => hw i)

private theorem complexTotalPathIndex_eventually_zero {ι : Type*} [Fintype ι]
    {a : ι → ℂ} {γ : (i : ι) → Path (a i) (a i)} (hγ : ∀ i, (γ i).IsLipschitz) :
    ∀ᶠ z in cocompact ℂ, complexTotalPathIndex γ z = 0 ∧ ∀ i, z ∉ Set.range (γ i) := by
  have hcompact : IsCompact (⋃ i, Set.range (γ i)) := isCompact_iUnion fun i => isCompact_range (γ i).continuous
  obtain ⟨R, hR⟩ := hcompact.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (id : ℂ → ℂ) _)
  have hAll (i : ι) : Set.range (γ i) ⊆ Metric.ball (0 : ℂ) (R + 1) := by
    intro w hw
    rw [mem_ball_zero_iff]
    exact (hR w (mem_iUnion.mpr ⟨i, hw⟩)).trans_lt (lt_add_one R)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 1)] with z hz
  constructor
  · exact Finset.sum_eq_zero fun i _ => complexPathIndex_zero_of_contained_ball (hγ i) (hAll i) hz
  · intro i hi
    exact (not_lt_of_ge hz) (mem_ball_zero_iff.mp (hAll i hi))

/-- The homological Cauchy formula for the Cauchy transform of a finite family
of closed Lipschitz paths. The total winding number vanishes outside the open
set of holomorphy. The set may be nonconvex and the paths may intersect. -/
theorem normalized_complexLineIntegral_cauchy_family {ι : Type*} [Fintype ι] {a : ι → ℂ}
    (γ : (i : ι) → Path (a i) (a i)) (hγ : ∀ i, (γ i).IsLipschitz)
    {U : Set ℂ} (hU : IsOpen U) (hRange : ∀ i, Set.range (γ i) ⊆ U)
    (hNull : ∀ z ∉ U, complexTotalPathIndex γ z = 0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : ∀ i, z ∉ Set.range (γ i)) :
    (2 * π * I)⁻¹ * ∑ i, complexLineIntegral (γ i) (fun w => f w / (w - z)) =
      complexTotalPathIndex γ z * f z := by
  classical
  let K : Set ℂ := ⋃ i, Set.range (γ i)
  let J := complexTotalPathIndex γ
  let O : Set ℂ := Kᶜ ∩ {z | J z = 0}
  let C (z : ℂ) := ∑ i, complexLineIntegral (γ i) (fun w => f w / (w - z))
  let D (z : ℂ) := ∑ i, complexLineIntegral (γ i) (fun w => dslope f w z)
  let G (z : ℂ) := if z ∈ U then D z else C z
  have hK : IsCompact K := isCompact_iUnion fun i => isCompact_range (γ i).continuous
  have hKU : K ⊆ U := iUnion_subset hRange
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    have ho := hK.isClosed.isOpen_compl.mem_nhds hw.1
    have hi := complexTotalPathIndex_eventuallyEq hγ (z := w) (fun i hi => hw.1 (mem_iUnion.mpr ⟨i,hi⟩))
    filter_upwards [ho,hi] with v hv he
    exact ⟨hv, he.trans hw.2⟩
  have hDiffer (w : ℂ) (hwU : w ∈ U) (hwK : w ∉ K) :
      D w = C w - f w * (2 * π * I) * J w := by
    have hd (i : ι) : complexLineIntegral (γ i) (fun z => dslope f z w) =
        complexLineIntegral (γ i) (fun z => f z / (z - w)) -
          f w * complexLineIntegral (γ i) (fun z => (z - w)⁻¹) := by
      have hne (z : ℂ) (hz : z ∈ Set.range (γ i)) : z - w ≠ 0 :=
        sub_ne_zero.mpr fun h => hwK (mem_iUnion.mpr ⟨i, h ▸ hz⟩)
      have hInv : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (Set.range (γ i)) :=
        (continuousOn_id.sub continuousOn_const).inv₀ hne
      have hfDiv : ContinuousOn (fun z : ℂ => f z / (z - w)) (Set.range (γ i)) :=
        (hf.continuousOn.mono (hRange i)).div (continuousOn_id.sub continuousOn_const) hne
      have hfInv : ContinuousOn (fun z : ℂ => f w * (z - w)⁻¹) (Set.range (γ i)) :=
        continuousOn_const.mul hInv
      have hs := complexLineIntegral_sub_of_continuousOn (hγ i) hfDiv hfInv
      rw [← complexLineIntegral_scalar_mul, ← hs]
      apply complexLineIntegral_congr_on_path
      intro z hz
      have hn : w ≠ z := fun h => (hne z hz) (sub_eq_zero.mpr h.symm)
      change dslope f z w = f z / (z - w) - f w * (z - w)⁻¹
      rw [dslope_of_ne _ hn, slope_def_field]
      field_simp [hne z hz, sub_ne_zero.mpr hn]
      ring
    simp only [D, C, hd, Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    have hk : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    simp only [J, complexTotalPathIndex, complexPathIndex, ← Finset.mul_sum]
    field_simp
  have hAgreement : Set.EqOn G C O := by
    intro w hw
    by_cases h : w ∈ U
    · rw [show G w = D w from ite_eq_left h, hDiffer w h hw.1, show J w = 0 from hw.2, mul_zero, sub_zero]
    · exact ite_eq_right h
  have hC : DifferentiableOn ℂ C Kᶜ := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    exact DifferentiableAt.fun_sum fun i _ =>
      (complexLineIntegral_hasDerivAt_cauchyTransform (hγ i) (hf.continuousOn.mono (hRange i))
        (fun hi => hw (mem_iUnion.mpr ⟨i,hi⟩))).differentiableAt
  have hD : DifferentiableOn ℂ D U := fun w hw =>
    DifferentiableWithinAt.fun_sum fun i _ => differentiableOn_complexLineIntegral_dslope (hγ i) hU (hRange i) hf w hw
  have hG : Differentiable ℂ G := by
    intro w
    by_cases hw : w ∈ U
    · exact (hD.differentiableAt (hU.mem_nhds hw)).congr_of_eventuallyEq
        (eventually_of_mem (hU.mem_nhds hw) fun _ h => ite_eq_left h)
    · have hwO : w ∈ O := ⟨fun h => hw (hKU h), hNull w hw⟩
      exact (hC.differentiableAt (hK.isClosed.isOpen_compl.mem_nhds hwO.1)).congr_of_eventuallyEq
        (eventually_of_mem (hO.mem_nhds hwO) hAgreement)
  have hInfinity : Tendsto G (cocompact ℂ) (𝓝 0) := by
    have h : Tendsto C (cocompact ℂ) (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using
        tendsto_finsetSum Finset.univ (fun i _ => tendsto_complexLineIntegral_cauchyTransform (hγ i) (hf.continuousOn.mono (hRange i)))
    apply h.congr'
    filter_upwards [complexTotalPathIndex_eventually_zero hγ] with w hw
    exact (hAgreement ⟨fun hK => by obtain ⟨i, hi⟩ := mem_iUnion.mp hK; exact hw.2 i hi, hw.1⟩).symm
  have hGzero : G z = 0 := hG.apply_eq_of_tendsto_cocompact z hInfinity
  have hx : z ∉ K := fun hk => by obtain ⟨i, hi⟩ := mem_iUnion.mp hk; exact hz i hi
  change (2 * π * I)⁻¹ * C z = J z * f z
  by_cases h : z ∈ U
  · rw [show G z = D z from ite_eq_left h, hDiffer z h hx, sub_eq_zero] at hGzero
    rw [hGzero]
    have hk : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    field_simp
  · rw [show G z = C z from ite_eq_right h] at hGzero
    rw [hGzero, show J z = 0 from hNull z h, mul_zero, zero_mul]

end HomologicalCauchy


section HomologicalCauchyJets

/-- Cauchy's formula for derivatives on a finite family of closed Lipschitz
paths whose total winding vanishes outside the holomorphy domain. -/
theorem normalized_complexLineIntegral_div_sub_pow_family {ι : Type*} [Fintype ι] {a : ι → ℂ}
    (γ : (i : ι) → Path (a i) (a i)) (hγ : ∀ i, (γ i).IsLipschitz)
    {U : Set ℂ} (hU : IsOpen U) (hRange : ∀ i, Set.range (γ i) ⊆ U)
    (hNull : ∀ z ∉ U, complexTotalPathIndex γ z = 0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : ∀ i, z ∉ Set.range (γ i)) (j : ℕ) :
    (2 * π * I)⁻¹ * ∑ i, complexLineIntegral (γ i) (fun w => f w / (w - z) ^ (j + 1)) =
      complexTotalPathIndex γ z * Hermite.taylorJet f z j := by
  simp_rw [complexLineIntegral_eq_iterate_dslope (γ _) (hγ _) (hz _) (hf.continuousOn.mono (hRange _)) j]
  rw [normalized_complexLineIntegral_cauchy_family γ hγ hU hRange hNull
    (differentiableOn_iterate_dslope hU z hf j) hz]
  by_cases h : z ∈ U
  · rw [iterate_dslope_eq_taylorJet (hf.analyticAt (hU.mem_nhds h)) j]
  · rw [hNull z h, zero_mul, zero_mul]

/-- Cauchy's theorem for cycles in arbitrary open sets, expressed by the vanishing
of total winding off the domain. -/
theorem complexLineIntegral_sum_eq_zero_of_total_winding {ι : Type*} [Fintype ι] {a : ι → ℂ}
    (γ : (i : ι) → Path (a i) (a i)) (hγ : ∀ i, (γ i).IsLipschitz)
    {U : Set ℂ} (hU : IsOpen U) (hRange : ∀ i, Set.range (γ i) ⊆ U)
    (hNull : ∀ z ∉ U, complexTotalPathIndex γ z = 0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) : ∑ i, complexLineIntegral (γ i) f = 0 := by
  have hE := complexTotalPathIndex_eventually_zero hγ
  obtain ⟨z, hz₀, hz⟩ := hE.exists
  have hg : DifferentiableOn ℂ (fun w => (w - z) * f w) U := (differentiableOn_id.sub_const z).mul hf
  have h := normalized_complexLineIntegral_cauchy_family γ hγ hU hRange hNull hg hz
  have hInt (i : ι) : complexLineIntegral (γ i) (fun w => (w - z) * f w / (w - z)) =
      complexLineIntegral (γ i) f := by
    apply complexLineIntegral_congr_on_path
    intro w hw
    change (w - z) * f w / (w - z) = f w
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr (fun e => hz i (e ▸ hw))
    field_simp
  simp only [hInt, hz₀, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero))

end HomologicalCauchyJets


/-- The scalar pole expansion of the weighted resolvent integral. The path
avoids the roots of the minimal polynomial. -/
theorem complexLineIntegral_smul_resolvent_scalar_expansion {B : Type*}
    [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] {a : B} (ha : IsIntegral ℂ a)
    {p : ℂ} (γ : Path p p) (hγ : γ.IsLipschitz)
    (hAvoid : ∀ w ∈ (minpoly ℂ a).roots.toFinset, w ∉ Set.range γ)
    {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) :
    (2 * π * I)⁻¹ • complexLineIntegral γ (fun z => f z • Ring.inverse (algebraMap ℂ B z - a)) =
      ∑ w ∈ (minpoly ℂ a).roots.toFinset, ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w),
        ((2 * π * I)⁻¹ * complexLineIntegral γ (fun z => f z / (z - w) ^ (j + 1))) •
          ((a - algebraMap ℂ B w) ^ j * spectralIdempotent a w) := by
  let X (w : ℂ) (j : ℕ) := (a - algebraMap ℂ B w) ^ j * spectralIdempotent a w
  let F (w : ℂ) (j : ℕ) (z : ℂ) := f z / (z - w) ^ (j + 1)
  let terms (w : ℂ) (z : ℂ) := ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w), F w j z • X w j
  have hc (w : ℂ) (hw : w ∈ (minpoly ℂ a).roots.toFinset) (j : ℕ) :
      ContinuousOn (F w j) (Set.range γ) := by
    simp only [F, div_eq_mul_inv]
    exact hf.mul (continuousOn_inversePole (hAvoid w hw) (j + 1))
  have hEq : Set.EqOn (fun z => f z • Ring.inverse (algebraMap ℂ B z - a))
      (fun z => ∑ w ∈ (minpoly ℂ a).roots.toFinset, terms w z) (Set.range γ) := by
    intro z hz
    have hroot : z ∉ (minpoly ℂ a).roots := fun h => hAvoid z (Multiset.mem_toFinset.mpr h) hz
    simp only [inverse_sub_eq_sum_spectralIdempotent ha (IsAlgClosed.splits _) hroot,
      Finset.smul_sum, smul_smul, F, X, terms, div_eq_mul_inv]
  have hTerms (w : ℂ) (hw : w ∈ (minpoly ℂ a).roots.toFinset) :
      ContinuousOn (terms w) (Set.range γ) :=
    continuousOn_finsetSum _ fun j _ => (hc w hw j).smul continuousOn_const
  rw [complexLineIntegral_congr_on_path γ hEq,
    complexLineIntegral_finset_sum hγ _ terms hTerms, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  unfold terms
  rw [complexLineIntegral_finset_sum hγ _ (fun j z => F w j z • X w j)
    (fun j _ => (hc w hw j).smul continuousOn_const), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [complexLineIntegral_smul_const, smul_smul]

/-- The primary functional calculus is the weighted resolvent integral over
any finite Lipschitz cycle with the prescribed winding numbers. The open set
of holomorphy can be nonconvex or multiply connected. -/
theorem pfc_eq_sum_complexLineIntegral_homological {B : Type*}
    [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] {a : B} (ha : IsIntegral ℂ a)
    {ι : Type*} [Fintype ι] {p : ι → ℂ} (γ : (i : ι) → Path (p i) (p i))
    (hγ : ∀ i, (γ i).IsLipschitz) {U : Set ℂ} (hOpen : IsOpen U) (hRange : ∀ i, Set.range (γ i) ⊆ U)
    (hNull : ∀ z ∉ U, complexTotalPathIndex γ z = 0)
    (hAvoid : ∀ i w, w ∈ (minpoly ℂ a).roots.toFinset → w ∉ Set.range (γ i))
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hIndex : ∀ w ∈ (minpoly ℂ a).roots.toFinset, complexTotalPathIndex γ w = 1) :
    pfc f a = ∑ i, (2 * π * I)⁻¹ • complexLineIntegral (γ i) (fun z =>
      f z • Ring.inverse (algebraMap ℂ B z - a)) := by
  rw [pfc_eq_sum_spectralIdempotent ha (IsAlgClosed.splits _) f]
  simp_rw [complexLineIntegral_smul_resolvent_scalar_expansion ha (γ _) (hγ _) (hAvoid _) (hf.continuousOn.mono (hRange _))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← Finset.mul_sum,
    normalized_complexLineIntegral_div_sub_pow_family γ hγ hOpen hRange hNull hf (fun i => hAvoid i w hw) j,
    hIndex w hw, one_mul]


section Resolvent

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- The normalized weighted resolvent integral on a Lipschitz loop in an open convex set of
holomorphy has a primary expansion. The coefficient at each spectral value is its Taylor
coefficient multiplied by its winding number. -/
theorem complexLineIntegral_smul_resolvent {a : B} (ha : IsIntegral ℂ a) {p : ℂ} {S : Set ℂ}
    (γ : Path p p) (hγ : γ.IsLipschitz)
    (hOpen : IsOpen S) (hConvex : Convex ℝ S) (hRange : Set.range γ ⊆ S)
    (hAvoid : ∀ w ∈ (minpoly ℂ a).roots.toFinset, w ∉ Set.range γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    (2 * π * I)⁻¹ • complexLineIntegral γ (fun z =>
      f z • Ring.inverse (algebraMap ℂ B z - a)) =
      ∑ w ∈ (minpoly ℂ a).roots.toFinset, ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w),
        (complexPathIndex γ w * Hermite.taylorJet f w j) •
          ((a - algebraMap ℂ B w) ^ j * spectralIdempotent a w) := by
  rw [complexLineIntegral_smul_resolvent_scalar_expansion ha γ hγ hAvoid (hf.continuousOn.mono hRange)]
  refine Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (· • ((a - algebraMap ℂ B w) ^ j * spectralIdempotent a w))
    (normalized_complexLineIntegral_div_sub_pow γ hγ hOpen hConvex hRange (hAvoid w hw) hf j)

/-- A finite family of Lipschitz loops recovers the primary functional calculus when each
loop lies in an open convex set of holomorphy. The total winding number is one
at every spectral value. -/
theorem pfc_eq_sum_complexLineIntegral {a : B} (ha : IsIntegral ℂ a) {ι : Type*} [Fintype ι]
    {p : ι → ℂ} (γ : (i : ι) → Path (p i) (p i)) (hγ : ∀ i, (γ i).IsLipschitz)
    (S : ι → Set ℂ) (hOpen : ∀ i, IsOpen (S i)) (hConvex : ∀ i, Convex ℝ (S i))
    (hRange : ∀ i, Set.range (γ i) ⊆ S i)
    (hAvoid : ∀ i w, w ∈ (minpoly ℂ a).roots.toFinset → w ∉ Set.range (γ i))
    {f : ℂ → ℂ} (hf : ∀ i, DifferentiableOn ℂ f (S i))
    (hIndex : ∀ w ∈ (minpoly ℂ a).roots.toFinset, ∑ i, complexPathIndex (γ i) w = 1) :
    pfc f a = ∑ i, (2 * π * I)⁻¹ • complexLineIntegral (γ i) (fun z =>
      f z • Ring.inverse (algebraMap ℂ B z - a)) := by
  rw [pfc_eq_sum_spectralIdempotent ha (IsAlgClosed.splits _) f]
  simp_rw [complexLineIntegral_smul_resolvent ha (γ _) (hγ _)
    (hOpen _) (hConvex _) (hRange _) (hAvoid _) (hf _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← Finset.sum_mul, hIndex w hw, one_mul]

/-- The normalized integral of the resolvent around a Lipschitz loop avoiding the spectrum
is the sum of its spectral idempotents weighted by the respective winding numbers. -/
theorem complexLineIntegral_resolvent_of_lipschitz {a : B} (ha : IsIntegral ℂ a) {z₀ : ℂ}
    (γ : Path z₀ z₀) (hγ : γ.IsLipschitz)
    (hAvoid : ∀ w ∈ (minpoly ℂ a).roots.toFinset, w ∉ Set.range γ) :
    (2 * π * I)⁻¹ • complexLineIntegral γ (fun z => Ring.inverse (algebraMap ℂ B z - a)) =
      ∑ w ∈ (minpoly ℂ a).roots.toFinset, complexPathIndex γ w • spectralIdempotent a w := by
  have h := complexLineIntegral_smul_resolvent ha γ hγ isOpen_univ (convex_univ) (subset_univ _)
    hAvoid (f := fun _ => 1) (differentiableOn_const 1)
  simp only [one_smul] at h
  rw [h]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_eq_single 0]
  · simp [Hermite.taylorJet_zero]
  · intro j _ hj
    have hJet : Hermite.taylorJet (fun _ : ℂ => (1 : ℂ)) w j = 0 := by
      simp [Hermite.taylorJet, iteratedDeriv_const, hj]
    rw [hJet, mul_zero, zero_smul]
  · intro h0
    have hm := Multiset.mem_toFinset.mp hw
    exact (h0 (Finset.mem_range.mpr
      ((rootMultiplicity_pos (ne_zero_of_mem_roots hm)).mpr (isRoot_of_mem_roots hm)))).elim

/-- The normalized integral of the resolvent around a piecewise $C^1$ loop avoiding the spectrum
is the sum of its spectral idempotents weighted by the respective winding numbers. The inverse
is the ring inverse, and the operator is assumed integral over $\mathbb C$. -/
theorem complexLineIntegral_resolvent {a : B} (ha : IsIntegral ℂ a) {z₀ : ℂ}
    (γ : Path z₀ z₀) (hγ : γ.IsPiecewiseC1)
    (havoid : ∀ t ∈ unitInterval, γ.extend t ∉ (minpoly ℂ a).roots) :
    (2 * π * I)⁻¹ • complexLineIntegral γ (fun z => Ring.inverse (algebraMap ℂ B z - a)) =
      ∑ w ∈ (minpoly ℂ a).roots.toFinset, complexPathIndex γ w • spectralIdempotent a w := by
  apply complexLineIntegral_resolvent_of_lipschitz ha γ hγ.isLipschitz
  intro w hw
  rintro ⟨t, rfl⟩
  apply havoid t t.2
  rw [Path.extend_apply γ t.2]
  exact Multiset.mem_toFinset.mp hw

end Resolvent

section IndexEnclosures

open Filter Metric Topology Bornology

/-- The winding index is constant on each connected component of a loop's complement. -/
theorem complexPathIndex_eq_of_mem_connectedComponentIn {a z w : ℂ} {γ : Path a a}
    (hγ : γ.IsLipschitz) (hz : z ∉ Set.range γ)
    (hw : w ∈ connectedComponentIn ((Set.range γ)ᶜ) z) : complexPathIndex γ w = complexPathIndex γ z := by
  have hOpen : IsOpen ((Set.range γ)ᶜ) := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hDer (u : ℂ) (hu : u ∈ connectedComponentIn ((Set.range γ)ᶜ) z) :=
    complexPathIndex_hasDerivAt_zero hγ (connectedComponentIn_subset _ _ hu)
  exact hOpen.connectedComponentIn.is_const_of_deriv_eq_zero isPreconnected_connectedComponentIn
    (fun u hu => (hDer u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hDer u hu).deriv) hw (mem_connectedComponentIn hz)

/-- The winding index is zero in every unbounded connected component of the
complement of a closed Lipschitz path. -/
theorem complexPathIndex_eq_zero_of_unbounded_connectedComponentIn {a z : ℂ} {γ : Path a a}
    (hγ : γ.IsLipschitz) (hz : z ∉ Set.range γ)
    (h : ¬ IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z)) : complexPathIndex γ z = 0 := by
  obtain ⟨R, hR⟩ := (isCompact_range γ.continuous).exists_bound_of_continuousOn
    (continuousOn_id : ContinuousOn (id : ℂ → ℂ) _)
  have hB : Set.range γ ⊆ Metric.ball (0 : ℂ) (R + 1) := fun w hw =>
    mem_ball_zero_iff.mpr ((hR w hw).trans_lt (lt_add_one R))
  have hx : ∃ w ∈ connectedComponentIn ((Set.range γ)ᶜ) z, R + 1 < ‖w‖ := by
    by_contra! he
    exact h (isBounded_iff_forall_norm_le.mpr ⟨R + 1, he⟩)
  obtain ⟨w, hw, hwR⟩ := hx
  rw [← complexPathIndex_eq_of_mem_connectedComponentIn hγ hz hw]
  exact complexPathIndex_zero_of_contained_ball hγ hB hwR.le

/-- The open part of the plane on which the cycle winds once. -/
noncomputable def complexCycleEnclosure {ι : Type*} [Fintype ι] {a : ι → ℂ}
    (γ : (i : ι) → Path (a i) (a i)) : Set ℂ :=
  {w | (∀ i, w ∉ Set.range (γ i)) ∧ complexTotalPathIndex γ w = 1}

/-- A cycle has positive index orientation when its total winding off its
traces is zero or one. The enclosed region then has winding one. -/
def HasPositiveCycleIndex {ι : Type*} [Fintype ι] {a : ι → ℂ}
    (γ : (i : ι) → Path (a i) (a i)) : Prop :=
  ∀ w, (∀ i, w ∉ Set.range (γ i)) → complexTotalPathIndex γ w = 0 ∨ complexTotalPathIndex γ w = 1

/-- The winding-one enclosure is open. -/
theorem isOpen_complexCycleEnclosure {ι : Type*} [Fintype ι] {a : ι → ℂ}
    {γ : (i : ι) → Path (a i) (a i)} (hγ : ∀ i, (γ i).IsLipschitz) :
    IsOpen (complexCycleEnclosure γ) := by
  have hK : IsCompact (⋃ i, Set.range (γ i)) := isCompact_iUnion fun i => isCompact_range (γ i).continuous
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  have hNot : w ∉ ⋃ i, Set.range (γ i) := fun he => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp he
    exact hw.1 i hi
  have hCond := hK.isClosed.isOpen_compl.mem_nhds (show w ∈ (⋃ i, Set.range (γ i))ᶜ from hNot)
  filter_upwards [hCond, complexTotalPathIndex_eventuallyEq hγ hw.1] with z hz hEq
  exact ⟨fun i hi => hz (mem_iUnion.mpr ⟨i, hi⟩), hEq.trans hw.2⟩

/-- The winding-one enclosure of a finite Lipschitz cycle is bounded. -/
theorem isBounded_complexCycleEnclosure {ι : Type*} [Fintype ι] {a : ι → ℂ}
    {γ : (i : ι) → Path (a i) (a i)} (hγ : ∀ i, (γ i).IsLipschitz) :
    IsBounded (complexCycleEnclosure γ) := by
  have h : ∀ᶠ z in cocompact ℂ, z ∈ (complexCycleEnclosure γ)ᶜ :=
    (complexTotalPathIndex_eventually_zero hγ).mono fun z hz hE => zero_ne_one (hz.1.symm.trans hE.2)
  rw [isBounded_def, Metric.cobounded_eq_cocompact]
  exact h

/-- Outside a holomorphy domain containing the traces and enclosure of a
positively index-oriented cycle, the total winding vanishes. -/
theorem HasPositiveCycleIndex.vanishes_outside {ι : Type*} [Fintype ι] {a : ι → ℂ}
    {γ : (i : ι) → Path (a i) (a i)} (h : HasPositiveCycleIndex γ)
    {U : Set ℂ} (hTrace : ∀ i, Set.range (γ i) ⊆ U) (hEnclose : complexCycleEnclosure γ ⊆ U)
    {w : ℂ} (hw : w ∉ U) : complexTotalPathIndex γ w = 0 := by
  have hAvoid : ∀ i, w ∉ Set.range (γ i) := fun i hi => hw (hTrace i hi)
  rcases h w hAvoid with he | he
  · exact he
  · exact False.elim (hw (hEnclose ⟨hAvoid, he⟩))

namespace Path

open scoped unitInterval

/-- An increasing Lipschitz parametrization of the same rectifiable path. -/
structure LipschitzReparametrization {a b : ℂ} (γ : Path a b) where
  path : Path a b
  orderIso : I ≃o I
  isLipschitz : path.IsLipschitz
  apply_orderIso : ∀ t, path (orderIso t) = γ t

/-- Rectifiability gives a Lipschitz representative with its increasing time change. -/
noncomputable def LipschitzReparametrization.of_rectifiable {a b : ℂ} (γ : Path a b)
    (hγ : BoundedVariationOn γ.extend unitInterval) : γ.LipschitzReparametrization := by
  classical
  let E := γ.exists_lipschitz_reparametrization hγ
  let ρ := Classical.choose E
  let η := Classical.choose (Classical.choose_spec E)
  let K := Classical.choose (Classical.choose_spec (Classical.choose_spec E))
  have h := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec E))
  exact ⟨η, ρ, ⟨K, h.1⟩, h.2⟩

/-- The increasing reparametrization preserves the whole geometric trace. -/
theorem LipschitzReparametrization.range_eq {a b : ℂ} {γ : Path a b} (η : γ.LipschitzReparametrization) :
    Set.range η.path = Set.range γ := by
  apply Set.Subset.antisymm
  · rintro z ⟨t,rfl⟩
    obtain ⟨u, hu⟩ := η.orderIso.surjective t
    exact ⟨u, (η.apply_orderIso u).symm.trans (congrArg η.path hu)⟩
  · rintro z ⟨t,rfl⟩
    exact ⟨η.orderIso t, η.apply_orderIso t⟩

end Path

end IndexEnclosures

section ComplexSubpaths

open Filter Metric Topology
open scoped unitInterval

private theorem complexSubpath_extend_affine {a b : ℂ} (γ : Path a b) (s t : I) {u : ℝ}
    (hu : u ∈ unitInterval) : (γ.subpath s t).extend u =
      γ.extend ((s : ℝ) + ((t : ℝ) - (s : ℝ)) * u) := by
  rw [Path.extend_apply _ hu]
  change γ (Icc.convexComb s t ⟨u, hu⟩) = _
  let v := Icc.convexComb s t ⟨u, hu⟩
  have hv : (v : ℝ) = (s : ℝ) + ((t : ℝ) - (s : ℝ)) * u := by
    dsimp [v, Icc.convexComb]
    ring
  rw [← hv, Path.extend_apply _ v.2]

/-- Lipschitz regularity is preserved on subpaths with their affine parameters. -/
theorem Path.IsLipschitz.subpath {a b : ℂ} {γ : Path a b} (hγ : γ.IsLipschitz) (s t : I) :
    (γ.subpath s t).IsLipschitz := by
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzWith_extend
  let L : ℝ≥0 := K * Real.nnabs ((t : ℝ) - (s : ℝ))
  refine ⟨L, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  have hEq (u : I) : (γ.subpath s t) u = γ.extend ((s : ℝ) + ((t : ℝ) - (s : ℝ)) * u) := by
    rw [← Path.extend_apply (γ.subpath s t) u.2]
    exact complexSubpath_extend_affine γ s t u.2
  rw [hEq u, hEq v]
  refine (hK.dist_le_mul _ _).trans_eq ?_
  change (K : ℝ) * dist _ _ = (K : ℝ) * |(t : ℝ) - s| * dist (u : ℝ) (v : ℝ)
  simp only [Real.dist_eq, show (s : ℝ) + ((t : ℝ) - s) * u - ((s : ℝ) + ((t : ℝ) - s) * v) =
    ((t : ℝ) - s) * (u - v) by ring, abs_mul, mul_assoc]

/-- A subpath integral is the restriction of the original parameter integral to the subinterval. -/
theorem complexLineIntegral_subpath {a b : ℂ} {γ : Path a b} (hγ : γ.IsLipschitz)
    (s t : I) (f : ℂ → ℂ) :
    complexLineIntegral (γ.subpath s t) f =
      ∫ u in (s : ℝ)..(t : ℝ), deriv γ.extend u • f (γ.extend u) := by
  by_cases h : s = t
  · subst t
    rw [Path.subpath_self, intervalIntegral.integral_same, complexLineIntegral, curveIntegral_refl]
  let c : ℝ := (t : ℝ) - (s : ℝ)
  let α (u : ℝ) := (s : ℝ) + c * u
  have hc : c ≠ 0 := sub_ne_zero.mpr (fun e => h (Subtype.ext e.symm))
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzWith_extend
  have hQA : QuasiMeasurePreserving α volume volume := by
    have h1 := (measurePreserving_add_left (volume : Measure ℝ) (s : ℝ)).quasiMeasurePreserving
    have h2 := MeasureTheory.Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hc
    exact h1.comp h2
  have hDiff : ∀ᵐ u ∂volume, DifferentiableAt ℝ γ.extend (α u) := hQA.ae (hK.ae_differentiableAt (μ := volume))
  have hEq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
      (γ.subpath s t).extend =ᶠ[𝓝 u] (γ.extend ∘ α) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    exact complexSubpath_extend_affine γ s t (Ioo_subset_Icc_self hv)
  rw [complexLineIntegral_eq_interval_deriv]
  let F (u : ℝ) := deriv γ.extend u • f (γ.extend u)
  have hI : (∫ u in (0 : ℝ)..1, deriv (γ.subpath s t).extend u • f ((γ.subpath s t).extend u)) =
      ∫ u in (0 : ℝ)..1, c • F (α u) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [hDiff.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (μ := volume) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo] with u hdu hu
    have hA : HasDerivAt α c u := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id u).const_mul c).const_add (s : ℝ))
    have hd : deriv (γ.subpath s t).extend u = c • deriv γ.extend (α u) :=
      ((hdu.hasDerivAt.scomp u hA).congr_of_eventuallyEq (hEq hu)).deriv
    rw [hd, complexSubpath_extend_affine γ s t (Ioo_subset_Icc_self hu)]
    exact smul_assoc c _ _
  rw [hI, intervalIntegral.integral_smul]
  change (c • ∫ u in (0 : ℝ)..1, F ((s : ℝ) + c * u)) = _
  rw [intervalIntegral.smul_integral_comp_add_mul, mul_zero, add_zero, mul_one]
  rw [show (s : ℝ) + c = t by dsimp [c]; ring]

end ComplexSubpaths

section OrientedContourReparametrizations

open Filter Metric Topology
open scoped unitInterval

private noncomputable def complexLineIntegralUpTo {a b : ℂ} (γ : Path a b) (f : ℂ → ℂ) (t : I) : ℂ :=
  ∫ u in (0 : ℝ)..(t : ℝ), deriv γ.extend u • f (γ.extend u)

private theorem complexLineIntegralUpTo_sub {a b : ℂ} {γ : Path a b} (hγ : γ.IsLipschitz)
    {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) (s t : I) :
    complexLineIntegralUpTo γ f t - complexLineIntegralUpTo γ f s = complexLineIntegral (γ.subpath s t) f := by
  let w (u : ℝ) := deriv γ.extend u • f (γ.extend u)
  have hI : IntervalIntegrable w volume 0 1 := by
    apply (complexLineIntegral_intervalIntegrable_lipschitz hγ hf).congr_ae
    rw [uIoc_of_le zero_le_one]
    filter_upwards [derivWithin_path_ae_eq_deriv γ] with u hu
    simp only [w, hu]
  have hI' (u : I) : IntervalIntegrable w volume 0 (u : ℝ) := hI.mono_set (by
    rw [uIcc_of_le u.2.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc_right u.2.2)
  rw [complexLineIntegral_subpath hγ]
  exact intervalIntegral.integral_interval_sub_left (hI' t) (hI' s)

/-- An increasing homeomorphism of the parameter preserves a holomorphic
contour integral when both representatives are Lipschitz. The time change
itself need only be an order isomorphism. -/
theorem complexLineIntegral_eq_of_orderIso_reparametrization {a b : ℂ} {γ η : Path a b}
    (hγ : γ.IsLipschitz) (hη : η.IsLipschitz) (ρ : I ≃o I) (hρ : ∀ t, η (ρ t) = γ t)
    {U : Set ℂ} (hU : IsOpen U) (hRange : Set.range γ ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) : complexLineIntegral γ f = complexLineIntegral η f := by
  have hηEq : Set.range η = Set.range γ := le_antisymm (by
    rintro _ ⟨t,rfl⟩
    obtain ⟨v,hv⟩ := ρ.surjective t
    exact ⟨v,(hρ v).symm.trans (congrArg η hv)⟩) (by
    rintro _ ⟨t,rfl⟩
    exact ⟨ρ t, hρ t⟩)
  have hηRange : Set.range η ⊆ U := hηEq ▸ hRange
  let D (t : I) := complexLineIntegralUpTo γ f t - complexLineIntegralUpTo η f (ρ t)
  have hLoc : IsLocallyConstant D := by
    apply (IsLocallyConstant.iff_eventually_eq D).mpr
    intro t
    obtain ⟨R, hR, hRU⟩ := isOpen_iff.mp hU (γ t) (hRange (mem_range_self _))
    let B := Metric.ball (γ t) R
    obtain ⟨P, hP⟩ := (convex_ball (γ t) R).exists_forall_hasDerivWithinAt (hf.mono hRU)
    have hDeriv (w : ℂ) (hw : w ∈ B) : HasDerivAt P (f w) w :=
      (hP w hw).hasDerivAt (Metric.isOpen_ball.mem_nhds hw)
    have hM : γ ⁻¹' B ∈ 𝓝 t := γ.continuous.continuousAt (Metric.ball_mem_nhds (γ t) hR)
    obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp hM
    filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
    have hB (v : I) (hv : v ∈ uIcc t s) : γ v ∈ B := by
      have hv' : (v : ℝ) ∈ uIcc (t : ℝ) (s : ℝ) :=
        (show Monotone (Subtype.val : I → ℝ) from fun _ _ h => h).image_uIcc_subset (mem_image_of_mem _ hv)
      have hd : dist v t ≤ dist s t := by
        change dist (v : ℝ) (t : ℝ) ≤ dist (s : ℝ) (t : ℝ)
        simpa only [dist_comm _ (t : ℝ)] using Real.dist_left_le_of_mem_uIcc hv'
      exact hδB (lt_of_le_of_lt hd hs)
    have hγ_sub : Set.range (γ.subpath t s) ⊆ B := by
      rw [Path.range_subpath]
      rintro _ ⟨v,hv,rfl⟩
      exact hB v hv
    have hη_sub : Set.range (η.subpath (ρ t) (ρ s)) ⊆ B := by
      rw [Path.range_subpath]
      rintro _ ⟨v,hv,rfl⟩
      have hv' : ρ.symm v ∈ uIcc t s := by
        simpa only [ρ.symm_apply_apply] using ρ.symm.monotone.image_uIcc_subset (mem_image_of_mem ρ.symm hv)
      rw [← ρ.apply_symm_apply v, hρ]
      exact hB _ hv'
    have h1 := complexLineIntegral_derivative_lipschitz (hγ.subpath t s) Metric.isOpen_ball hγ_sub hDeriv
      (hf.continuousOn.mono (hγ_sub.trans hRU))
    have h2 := complexLineIntegral_derivative_lipschitz (hη.subpath (ρ t) (ρ s)) Metric.isOpen_ball hη_sub hDeriv
      (hf.continuousOn.mono (hη_sub.trans hRU))
    rw [← complexLineIntegralUpTo_sub hγ (hf.continuousOn.mono hRange)] at h1
    rw [← complexLineIntegralUpTo_sub hη (hf.continuousOn.mono hηRange), hρ s, hρ t] at h2
    dsimp only [D]
    linear_combination h1 - h2
  have hOne : ρ 1 = 1 := ρ.map_top
  have hZero : ρ 0 = 0 := ρ.map_bot
  have he := hLoc.apply_eq_of_preconnectedSpace 1 0
  change complexLineIntegralUpTo γ f 1 - complexLineIntegralUpTo η f (ρ 1) =
    complexLineIntegralUpTo γ f 0 - complexLineIntegralUpTo η f (ρ 0) at he
  simp only [hOne, hZero, complexLineIntegralUpTo, show ((1 : I) : ℝ) = 1 from rfl, show ((0 : I) : ℝ) = 0 from rfl,
    intervalIntegral.integral_same, sub_self, ← complexLineIntegral_eq_interval_deriv] at he
  exact sub_eq_zero.mp he

/-- Increasing Lipschitz representatives of the same rectifiable path define
one holomorphic contour integral. -/
theorem Path.LipschitzReparametrization.complexLineIntegral_eq {a b : ℂ} {γ : Path a b}
    (η ξ : γ.LipschitzReparametrization) {U : Set ℂ} (hU : IsOpen U) (hRange : Set.range γ ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) : complexLineIntegral η.path f = complexLineIntegral ξ.path f := by
  let ρ := η.orderIso.symm.trans ξ.orderIso
  have hρ (t : I) : ξ.path (ρ t) = η.path t := by
    change ξ.path (ξ.orderIso (η.orderIso.symm t)) = η.path t
    rw [ξ.apply_orderIso, ← η.apply_orderIso, η.orderIso.apply_symm_apply]
  exact complexLineIntegral_eq_of_orderIso_reparametrization η.isLipschitz ξ.isLipschitz ρ hρ
    hU (η.range_eq ▸ hRange) hf

/-- Any two increasing Lipschitz representatives of the same rectifiable
loop give the same winding index about a point off the original trace. -/
theorem Path.LipschitzReparametrization.complexPathIndex_eq {a w : ℂ} {γ : Path a a}
    (η ξ : γ.LipschitzReparametrization) (hw : w ∉ Set.range γ) :
    complexPathIndex η.path w = complexPathIndex ξ.path w := by
  have hDiff : DifferentiableOn ℂ (fun z : ℂ => (z - w)⁻¹) {w}ᶜ :=
    (differentiableOn_id.sub_const w).inv fun z hz => sub_ne_zero.mpr hz
  have hRange : Set.range γ ⊆ ({w} : Set ℂ)ᶜ := fun _ hz h => hw ((mem_singleton_iff.mp h) ▸ hz)
  rw [complexPathIndex, complexPathIndex, η.complexLineIntegral_eq ξ isOpen_compl_singleton hRange hDiff]

/-- The holomorphic line integral along a rectifiable path, using an increasing
Lipschitz parametrization. -/
noncomputable def rectifiableComplexLineIntegral {a b : ℂ} (γ : Path a b)
    (hγ : BoundedVariationOn γ.extend unitInterval) (f : ℂ → ℂ) : ℂ :=
  complexLineIntegral (Path.LipschitzReparametrization.of_rectifiable γ hγ).path f

/-- Any increasing Lipschitz parametrization computes the rectifiable integral
when the integrand is holomorphic on a neighborhood of the trace. -/
theorem rectifiableComplexLineIntegral_eq {a b : ℂ} {γ : Path a b}
    (hγ : BoundedVariationOn γ.extend unitInterval) (η : γ.LipschitzReparametrization)
    {U : Set ℂ} (hU : IsOpen U) (hRange : Set.range γ ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    rectifiableComplexLineIntegral γ hγ f = complexLineIntegral η.path f :=
  (Path.LipschitzReparametrization.of_rectifiable γ hγ).complexLineIntegral_eq η hU hRange hf

end OrientedContourReparametrizations

section IntegralWindingNumbers

open Filter Metric Topology
open scoped unitInterval

private theorem eventually_subpath_range_subset {a b : ℂ} (γ : Path a b) (t : I)
    {S : Set ℂ} (h : S ∈ 𝓝 (γ t)) : ∀ᶠ s in 𝓝 t, Set.range (γ.subpath t s) ⊆ S := by
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.mp (γ.continuous.continuousAt h)
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
  rw [Path.range_subpath]
  rintro _ ⟨v,hv,rfl⟩
  have hv' : (v : ℝ) ∈ uIcc (t : ℝ) (s : ℝ) :=
    (show Monotone (Subtype.val : I → ℝ) from fun _ _ h => h).image_uIcc_subset (mem_image_of_mem _ hv)
  have hd : dist v t ≤ dist s t := by
    change dist (v : ℝ) (t : ℝ) ≤ dist (s : ℝ) (t : ℝ)
    simpa only [dist_comm _ (t : ℝ)] using Real.dist_left_le_of_mem_uIcc hv'
  exact hδS (lt_of_le_of_lt hd hs)

/-- The contour integral of the reciprocal kernel around a closed Lipschitz
path is an integer multiple of `2 π i`. -/
theorem complexPathIndex_exists_int {a w : ℂ} {γ : Path a a}
    (hγ : γ.IsLipschitz) (hw : w ∉ Set.range γ) :
    ∃ n : ℤ, complexPathIndex γ w = (n : ℂ) := by
  let f (z : ℂ) := (z - w)⁻¹
  let J := complexLineIntegralUpTo γ f
  let Q (t : I) := Complex.exp (J t) / (γ t - w)
  have hne (t : I) : γ t - w ≠ 0 :=
    sub_ne_zero.mpr fun he => hw (he ▸ mem_range_self t)
  have hc : ContinuousOn f (Set.range γ) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun _ ⟨t,ht⟩ => ht ▸ hne t
  have hLoc : IsLocallyConstant Q := by
    apply (IsLocallyConstant.iff_eventually_eq Q).mpr
    intro t
    let r (z : ℂ) := (z - w) / (γ t - w)
    let U := r ⁻¹' Complex.slitPlane
    have hOpen : IsOpen U := Complex.isOpen_slitPlane.preimage (by unfold r; fun_prop)
    have htU : γ t ∈ U := by
      change (γ t - w) / (γ t - w) ∈ Complex.slitPlane
      rw [div_self (hne t)]
      exact Complex.one_mem_slitPlane
    let P (z : ℂ) := Complex.log (r z)
    have hP (z : ℂ) (hz : z ∈ U) : HasDerivAt P (f z) z := by
      have h₁ : HasDerivAt r (1 / (γ t - w)) z := by
        simpa only [id_eq] using ((hasDerivAt_id z).sub_const w).div_const (γ t - w)
      apply ((Complex.hasDerivAt_log hz).comp z h₁).congr_deriv
      dsimp [f,r]
      rw [inv_div, one_div]
      have hz' : z - w ≠ 0 := fun h => Complex.slitPlane_ne_zero hz (by simp [r, h])
      field_simp [hne t, hz']
    filter_upwards [eventually_subpath_range_subset γ t (hOpen.mem_nhds htU)] with s hs
    have h := complexLineIntegral_derivative_lipschitz (hγ.subpath t s) hOpen hs hP
      (hc.mono (by rw [Path.range_subpath]; exact image_subset_range _ _))
    rw [← complexLineIntegralUpTo_sub hγ hc] at h
    change J s - J t = P (γ s) - P (γ t) at h
    have htP : P (γ t) = 0 := by simp [P, r]
    rw [htP, sub_zero] at h
    have he := congrArg Complex.exp h
    rw [Complex.exp_sub, show Complex.exp (P (γ s)) = r (γ s) from
      Complex.exp_log (div_ne_zero (hne s) (hne t))] at he
    change Complex.exp (J s) / Complex.exp (J t) = (γ s - w) / (γ t - w) at he
    apply (div_eq_div_iff (hne s) (hne t)).mpr
    exact (div_eq_div_iff (Complex.exp_ne_zero _) (hne t)).mp he |>.trans (mul_comm _ _)
  have he : Q 1 = Q 0 := hLoc.apply_eq_of_preconnectedSpace 1 0
  have hInt : Complex.exp (complexLineIntegral γ f) = 1 := by
    have hz : a - w ≠ 0 := fun h => hw ((sub_eq_zero.mp h) ▸ ⟨0, γ.source⟩)
    apply (div_left_inj' hz).mp
    simpa only [Q, J, complexLineIntegralUpTo, show ((1 : I) : ℝ) = 1 from rfl,
      show ((0 : I) : ℝ) = 0 from rfl, intervalIntegral.integral_same, Complex.exp_zero,
      Path.target, Path.source, ← complexLineIntegral_eq_interval_deriv] using he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hInt
  refine ⟨n, ?_⟩
  have hC : (2 * π * Complex.I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  change (2 * π * Complex.I)⁻¹ * complexLineIntegral γ f = (n : ℂ)
  rw [hn]
  field_simp

end IntegralWindingNumbers
