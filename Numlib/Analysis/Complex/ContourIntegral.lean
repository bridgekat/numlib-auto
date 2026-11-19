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
  let X (w : ℂ) (j : ℕ) := (a - algebraMap ℂ B w) ^ j * spectralIdempotent a w
  let F (w : ℂ) (j : ℕ) (z : ℂ) := f z / (z - w) ^ (j + 1)
  let terms (w : ℂ) (z : ℂ) :=
    ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w), F w j z • X w j
  have hc (w : ℂ) (hw : w ∈ (minpoly ℂ a).roots.toFinset) (j : ℕ) :
      ContinuousOn (F w j) (Set.range γ) := by
    simp only [F, div_eq_mul_inv]
    exact (hf.continuousOn.mono hRange).mul (continuousOn_inversePole (hAvoid w hw) (j + 1))
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
  exact congrArg (· • X w j)
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
