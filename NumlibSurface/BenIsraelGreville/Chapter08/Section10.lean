/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter08.Section09
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Image densities from graph and spherical coordinates

Section 8.10 of [benIsrael2003generalized] computes the density of a real
function of a random vector by integrating the vector's density over level
sets. Densities are specified by an equality of measures, so representatives
may differ on Lebesgue-null sets. The spherical formula is given on the
positive ray and the chosen density representative vanishes elsewhere.
-/

noncomputable section

namespace BenIsraelGreville.Chapter08

open EuclideanSpace MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace

/-- A measurable Lebesgue density of a probability law. -/
def IsLebesgueProbabilityDensity {E : Type*} [MeasureSpace E]
    (μ : Measure E) (f : E → ℝ≥0∞) : Prop :=
  Measurable f ∧ μ = volume.withDensity f ∧ IsProbabilityMeasure μ

namespace IsLebesgueProbabilityDensity

variable {E : Type*} [MeasureSpace E] {μ : Measure E} {f : E → ℝ≥0∞}

/-- The density is measurable. -/
theorem measurable (hf : IsLebesgueProbabilityDensity μ f) : Measurable f := hf.1

/-- The law is Lebesgue measure weighted by its density. -/
theorem eq_withDensity (hf : IsLebesgueProbabilityDensity μ f) : μ = volume.withDensity f := hf.2.1

/-- The law has total mass one. -/
theorem isProbabilityMeasure (hf : IsLebesgueProbabilityDensity μ f) : IsProbabilityMeasure μ :=
  hf.2.2

/-- A probability density is finite almost everywhere. -/
theorem ae_ne_top (hf : IsLebesgueProbabilityDensity μ f) : ∀ᵐ x ∂volume, f x ≠ ⊤ := by
  let := hf.isProbabilityMeasure
  have htotal : (∫⁻ x, f x) = 1 := by
    rw [← Measure.restrict_univ (μ := (volume : Measure E)),
      ← withDensity_apply _ MeasurableSet.univ,
      ← hf.eq_withDensity, measure_univ]
  exact (ae_lt_top hf.measurable (htotal.trans_ne ENNReal.one_ne_top)).mono fun _ hx => hx.ne

/-- Transport a probability density through a volume-preserving coordinates change. -/
theorem map_measurePreserving {F : Type*} [MeasureSpace F] (hf : IsLebesgueProbabilityDensity μ f)
    (e : E ≃ᵐ F) (he : MeasurePreserving e volume volume) :
    IsLebesgueProbabilityDensity (μ.map e) (f ∘ e.symm) := by
  have hm := hf.measurable.comp e.symm.measurable
  refine ⟨hm, ?_,
    (Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).mpr hf.isProbabilityMeasure⟩
  ext S hS
  rw [Measure.map_apply e.measurable hS, hf.eq_withDensity, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS]
  simpa only [Function.comp_apply, e.symm_apply_apply] using he.setLIntegral_comp_preimage hS hm

/-- A probability density may be represented by a real-valued function
using its almost-everywhere finiteness. -/
theorem ofReal_toReal (hf : IsLebesgueProbabilityDensity μ f) :
    IsLebesgueProbabilityDensity μ (fun x => ENNReal.ofReal (f x).toReal) := by
  refine ⟨hf.measurable.ennreal_toReal.ennreal_ofReal, hf.eq_withDensity.trans ?_,
    hf.isProbabilityMeasure⟩
  apply withDensity_congr_ae
  exact hf.ae_ne_top.mono fun _ hx => (ENNReal.ofReal_toReal hx).symm

end IsLebesgueProbabilityDensity

section GraphDensity

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-- **Equations (178)–(180)** of [benIsrael2003generalized], Chapter 8.
The graph coordinates keep the first `d` coordinates and solve the level
constraint for the last coordinate. The chart covers every real level in
each fiber. `heightDeriv` is the derivative with respect to the level. -/
structure ImageGraphChart (h : 𝔼 → ℝ) where
  /-- Inverse height as a function of the first coordinates and level. -/
  height : 𝔼' × ℝ → ℝ
  /-- Derivative of the inverse height with respect to the level. -/
  heightDeriv : 𝔼' × ℝ → ℝ
  /-- The inverse height is jointly measurable. -/
  measurable_height : Measurable height
  /-- Its level derivative is jointly measurable. -/
  measurable_heightDeriv : Measurable heightDeriv
  /-- Substituting the inverse height gives the specified level. -/
  level_height : ∀ u y, h (snocLast u (height (u, y))) = y
  /-- Solving for the height of a point recovers its last coordinate. -/
  height_level : ∀ u t, height (u, h (snocLast u t)) = t
  /-- The level derivative gives the one-dimensional Jacobian. -/
  hasDerivAt_height : ∀ u y, HasDerivAt (fun z => height (u, z)) (heightDeriv (u, y)) y
  /-- At a fixed level the height gives a smooth graph. -/
  contDiff_height : ∀ y, ContDiff ℝ 1 (fun u => height (u, y))

private theorem measurePreserving_snocLast (k : ℕ) :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin k) × ℝ => snocLast z.1 z.2)
      ((volume : Measure (EuclideanSpace ℝ (Fin k))).prod (volume : Measure ℝ))
      (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) :=
  ((measurePreserving_lastInit k).symm (lastInitEquiv k)).comp Measure.measurePreserving_swap

private theorem measurable_snocLast (k : ℕ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin k) × ℝ => snocLast z.1 z.2) :=
  (measurePreserving_snocLast k).measurable

namespace ImageGraphChart

variable {h : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (chart : ImageGraphChart (d := d) h)

/-- **Equation (182)** of [benIsrael2003generalized], Chapter 8.
At a fixed level the inverse height parametrizes precisely that level set. -/
theorem range_height (y : ℝ) :
    range (fun u => snocLast u (chart.height (u, y))) = {x | h x = y} := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact chart.level_height u y
  · intro hy
    refine ⟨init x, ?_⟩
    change h x = y at hy
    have he := chart.height_level (init x) (x (Fin.last _))
    rw [snocLast_init_last] at he
    change snocLast (init x) (chart.height (init x, y)) = x
    rw [← hy, he, snocLast_init_last]

private theorem image_height (u : 𝔼') (S : Set ℝ) :
    (fun y => chart.height (u, y)) '' S = (fun t => h (snocLast u t)) ⁻¹' S := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    change h (snocLast u (chart.height (u, y))) ∈ S
    rwa [chart.level_height]
  · intro ht
    exact ⟨h (snocLast u t), ht, chart.height_level u t⟩

private theorem injective_height (u : 𝔼') : Function.Injective (fun y => chart.height (u, y)) := by
  have hinv : Function.LeftInverse (fun t => h (snocLast u t)) (fun y => chart.height (u, y)) :=
    chart.level_height u
  exact hinv.injective

end ImageGraphChart

/-- The expression for the image density in Equation (181). -/
def graphImageDensity {h : 𝔼 → ℝ} (chart : ImageGraphChart h) (f : 𝔼 → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal |chart.heightDeriv (u, y)| * f (snocLast u (chart.height (u, y)))

/-- **Equations (181a)–(181b)** of [benIsrael2003generalized], Chapter 8.
The inverse-height derivative supplies the density of the image law. -/
theorem imageDensity_graph {h : 𝔼 → ℝ} (hh : Measurable h) (chart : ImageGraphChart h)
    {μ : Measure 𝔼} {f : 𝔼 → ℝ≥0∞} (hf : IsLebesgueProbabilityDensity μ f) :
    IsLebesgueProbabilityDensity (μ.map h) (graphImageDensity chart f) := by
  let q : 𝔼' × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal |chart.heightDeriv z| * f (snocLast z.1 (chart.height z))
  have hq : Measurable q :=
    (continuous_abs.measurable.comp chart.measurable_heightDeriv).ennreal_ofReal.mul
      (hf.measurable.comp
        ((measurable_snocLast d).comp (measurable_fst.prodMk chart.measurable_height)))
  refine ⟨hq.lintegral_prod_left', ?_,
    (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).mpr hf.isProbabilityMeasure⟩
  ext S hS
  rw [Measure.map_apply hh hS, hf.eq_withDensity,
    withDensity_apply _ (hh hS), withDensity_apply _ hS]
  let T := h ⁻¹' S
  let I : 𝔼' × ℝ → ℝ≥0∞ := fun z => T.indicator f (snocLast z.1 z.2)
  have hI : Measurable I := (hf.measurable.indicator (hh hS)).comp (measurable_snocLast d)
  have hJS : MeasurableSet (Prod.snd ⁻¹' S : Set (𝔼' × ℝ)) := measurable_snd hS
  let J : 𝔼' × ℝ → ℝ≥0∞ := (Prod.snd ⁻¹' S).indicator q
  have hJ : Measurable J := hq.indicator hJS
  calc
    (∫⁻ x in T, f x) = ∫⁻ z, I z ∂((volume : Measure 𝔼').prod (volume : Measure ℝ)) := by
      rw [← lintegral_indicator (hh hS)]
      exact ((measurePreserving_snocLast d).lintegral_comp (hf.measurable.indicator (hh hS))).symm
    _ = ∫⁻ u, ∫⁻ y, J (u, y) := by
      rw [lintegral_prod I hI.aemeasurable]
      refine lintegral_congr fun u => ?_
      have hpre : (fun t => h (snocLast u t)) ⁻¹' S = (fun y => chart.height (u, y)) '' S :=
        (chart.image_height u S).symm
      have ht : MeasurableSet ((fun t => h (snocLast u t)) ⁻¹' S) := by
        apply hh.comp ((measurable_snocLast d).comp (measurable_const.prodMk measurable_id)) hS
      have hIu : (fun t => I (u, t)) =
          ((fun t => h (snocLast u t)) ⁻¹' S).indicator (fun t => f (snocLast u t)) := by
        funext t
        rfl
      have hJu : (fun y => J (u, y)) = S.indicator (fun y => q (u, y)) := by
        funext y
        rfl
      rw [hIu, hJu, lintegral_indicator ht, lintegral_indicator hS, hpre]
      exact lintegral_image_eq_lintegral_abs_deriv_mul hS
        (fun y _ => (chart.hasDerivAt_height u y).hasDerivWithinAt)
        (chart.injective_height u).injOn (fun t => f (snocLast u t))
    _ = ∫⁻ y, ∫⁻ u, J (u, y) := lintegral_lintegral_swap hJ.aemeasurable
    _ = ∫⁻ y in S, graphImageDensity chart f y := by
      rw [← lintegral_indicator hS]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ S
      · simp only [J, mem_preimage, hy, indicator_of_mem]
        rfl
      · simp only [J, mem_preimage, hy, not_false_eq_true,
          indicator_of_notMem, lintegral_zero]

/-- **Theorem 14**, Equations (184)–(185) of [benIsrael2003generalized], Chapter 8.
If the ratio of the level derivative to the graph area factor depends only
on the level, the density is the surface integral times the absolute ratio. -/
theorem theorem_14 {h : 𝔼 → ℝ} (hh : Measurable h) (chart : ImageGraphChart h)
    {μ : Measure 𝔼} {f : 𝔼 → ℝ≥0∞} (hf : IsLebesgueProbabilityDensity μ f)
    (c : ℝ → ℝ) (hc : ∀ u y,
      chart.heightDeriv (u, y) / graphDensity (fun v => chart.height (v, y)) u = c y) :
    IsLebesgueProbabilityDensity (μ.map h) (fun y => ENNReal.ofReal |c y| *
      ∫⁻ x, f x ∂graphMeasure (AffineIsometryEquiv.refl ℝ 𝔼)
        (fun u => chart.height (u, y)) univ) := by
  convert imageDensity_graph hh chart hf using 1
  funext y
  rw [lintegral_graphMeasure (chart.contDiff_height y), Measure.restrict_univ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, graphImageDensity]
  refine lintegral_congr fun u => ?_
  have hg : 0 < graphDensity (fun v => chart.height (v, y)) u := by
    unfold graphDensity
    positivity
  have hd := (div_eq_iff hg.ne').mp (hc u y)
  rw [hd, abs_mul, abs_of_pos hg, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]
  rfl

end GraphDensity

section LinearImage

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

private theorem measurable_inner_normal (ξ : 𝔼) : Measurable (fun x : 𝔼 => ⟪ξ, x⟫_ℝ) :=
  (innerSL ℝ ξ).continuous.measurable

/-- **Equations (186)–(188)** of [benIsrael2003generalized], Chapter 8.
The inverse height of a nonvertical hyperplane and its constant derivative. -/
def linearImageGraphChart (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) :
    ImageGraphChart (fun x => ⟪ξ, x⟫_ℝ) where
  height z := radonHeight ξ z.2 z.1
  heightDeriv _ := (ξ (Fin.last d))⁻¹
  measurable_height := by
    change Measurable (fun z : 𝔼' × ℝ =>
      (z.2 - innerSL ℝ (init ξ) z.1) / ξ (Fin.last d))
    fun_prop
  measurable_heightDeriv := measurable_const
  level_height u y := inner_radonChart ξ hξ y u
  height_level u t := by
    change radonHeight ξ ⟪ξ, snocLast u t⟫_ℝ u = t
    conv_lhs => rw [← snocLast_init_last ξ, inner_snocLast]
    simp only [radonHeight, init_snocLast, snocLast_apply_last, add_sub_cancel_left]
    rw [mul_comm, mul_div_cancel_right₀ _ hξ]
  hasDerivAt_height u y := by
    simpa [radonHeight, one_div] using
      (((hasDerivAt_id y).sub_const ⟪init ξ, u⟫_ℝ).div_const (ξ (Fin.last d)))
  contDiff_height y := (contDiff_const.sub (innerSL ℝ (init ξ)).contDiff).div_const _

/-- The Radon transform of a nonnegative measurable function as an extended
Lebesgue integral. The orthogonal chart includes vertical hyperplanes. -/
def radonLIntegral (f : 𝔼 → ℝ≥0∞) (ξ : 𝔼) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, f (radonNormalChart ξ y u)

/-- The nonnegative Radon transform is integration against the measure of the
hyperplane from the corresponding orthogonal chart. -/
theorem radonLIntegral_eq_graphMeasure (f : 𝔼 → ℝ≥0∞) (ξ : 𝔼) (y : ℝ) :
    radonLIntegral f ξ y = ∫⁻ x, f x ∂graphMeasure (radonFrame ξ).toAffineIsometryEquiv
      (fun _ => y / ‖ξ‖) univ := by
  rw [lintegral_graphMeasure contDiff_const, Measure.restrict_univ]
  simp only [graphDensity, gradient_fun_const, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul]
  rfl

/-- **Equation (188b)** of [benIsrael2003generalized], Chapter 8.
In a nonvertical chart the hyperplane area factor is the norm of the normal
vector divided by the absolute value of its last coordinate. -/
theorem radonLIntegral_nonvertical (f : 𝔼 → ℝ≥0∞) (ξ : 𝔼)
    (hξ : ξ (Fin.last d) ≠ 0) (y : ℝ) :
    radonLIntegral f ξ y = ENNReal.ofReal (‖ξ‖ / |ξ (Fin.last d)|) *
      ∫⁻ u, f (radonChart ξ y u) := by
  let chart := linearImageGraphChart ξ hξ
  have hξ₀ : ξ ≠ 0 := fun h => hξ (by simp [h])
  have he : graphMeasure (radonFrame ξ).toAffineIsometryEquiv (fun _ => y / ‖ξ‖) univ =
      graphMeasure (AffineIsometryEquiv.refl ℝ 𝔼) (radonHeight ξ y) univ := by
    apply graphMeasure_eq_of_range_eq contDiff_const (chart.contDiff_height y)
    change range (radonNormalChart ξ y) = range (radonChart ξ y)
    rw [range_radonNormalChart ξ hξ₀, range_radonChart ξ hξ]
  have hc : ContDiff ℝ 1 (radonHeight ξ y) := chart.contDiff_height y
  rw [radonLIntegral_eq_graphMeasure, he, lintegral_graphMeasure hc, Measure.restrict_univ]
  simp only [graphDensity_radonHeight ξ hξ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-- **Corollary 4** in the last-coordinate chart. A nonvertical linear
image has the Radon density divided by the norm of the normal. -/
theorem corollary_4_nonvertical (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0)
    {μ : Measure 𝔼} {f : 𝔼 → ℝ≥0∞} (hf : IsLebesgueProbabilityDensity μ f) :
    IsLebesgueProbabilityDensity (μ.map fun x => ⟪ξ, x⟫_ℝ)
      (fun y => ENNReal.ofReal (‖ξ‖⁻¹) * radonLIntegral f ξ y) := by
  let chart := linearImageGraphChart ξ hξ
  convert imageDensity_graph (measurable_inner_normal ξ) chart hf using 1
  funext y
  rw [radonLIntegral_nonvertical f ξ hξ, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg ξ))]
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr (fun h => hξ (by simp [h]))
  rw [show ‖ξ‖⁻¹ * (‖ξ‖ / |ξ (Fin.last d)|) = |ξ (Fin.last d)|⁻¹ by field_simp]
  change _ = ∫⁻ u, ENNReal.ofReal |(ξ (Fin.last d))⁻¹| * f (radonChart ξ y u)
  rw [abs_inv, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **Corollary 4**, Equations (189)–(190) of [benIsrael2003generalized],
Chapter 8. Every nonzero linear image has the Radon density divided by the
norm of the normal, including when its last coordinate vanishes. -/
theorem corollary_4 (ξ : 𝔼) (hξ : ξ ≠ 0) {μ : Measure 𝔼} {f : 𝔼 → ℝ≥0∞}
    (hf : IsLebesgueProbabilityDensity μ f) :
    IsLebesgueProbabilityDensity (μ.map fun x => ⟪ξ, x⟫_ℝ)
      (fun y => ENNReal.ofReal (‖ξ‖⁻¹) * radonLIntegral f ξ y) := by
  let R := radonFrame ξ
  have hRf := hf.map_measurePreserving R.toMeasurableEquiv R.measurePreserving
  have hRξ : (R ξ) (Fin.last d) ≠ 0 := by
    rw [radonFrame_normal ξ hξ, snocLast_apply_last]
    exact norm_ne_zero_iff.mpr hξ
  have h := corollary_4_nonvertical (R ξ) hRξ hRf
  rw [Measure.map_map (measurable_inner_normal (R ξ)) R.toMeasurableEquiv.measurable] at h
  have hh : (fun x => ⟪R ξ, x⟫_ℝ) ∘ R.toMeasurableEquiv = (fun x => ⟪ξ, x⟫_ℝ) := by
    funext x
    exact R.inner_map_map ξ x
  rw [hh, LinearIsometryEquiv.norm_map] at h
  convert h using 1
  funext y
  congr 1
  change radonLIntegral f ξ y = radonLIntegral (f ∘ R.symm) (R ξ) y
  rw [radonLIntegral_nonvertical (f ∘ R.symm) (R ξ) hRξ]
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hRξ' : R ξ = snocLast 0 ‖ξ‖ := radonFrame_normal ξ hξ
  have hnorm : ‖snocLast (0 : 𝔼') ‖ξ‖‖ = ‖ξ‖ := by
    simpa only [hRξ'] using R.norm_map ξ
  simp only [hRξ', hnorm, snocLast_apply_last, abs_of_nonneg (norm_nonneg ξ),
    div_self hn, ENNReal.ofReal_one, one_mul, radonLIntegral]
  apply lintegral_congr
  intro u
  simp [radonChart, radonHeight, radonNormalChart, R]

/-- **Equation (190)** of [benIsrael2003generalized], Chapter 8,
using the real-valued Radon transform of Section 8.9. -/
theorem corollary_4_radonTransformAll (ξ : 𝔼) (hξ : ξ ≠ 0) {μ : Measure 𝔼} {f : 𝔼 → ℝ}
    (hf : IsLebesgueProbabilityDensity μ (fun x => ENNReal.ofReal (f x)))
    (hm : Measurable f) (h₀ : ∀ x, 0 ≤ f x) :
    IsLebesgueProbabilityDensity (μ.map fun x => ⟪ξ, x⟫_ℝ)
      (fun y => ENNReal.ofReal (radonTransformAll f ξ y / ‖ξ‖)) := by
  have h := (corollary_4 ξ hξ hf).ofReal_toReal
  convert h using 1
  funext y
  congr 1
  have hm' : Measurable (fun u => f (radonNormalChart ξ y u)) :=
    hm.comp ((radonFrame ξ).symm.continuous.measurable.comp
      ((measurable_snocLast d).comp (measurable_id.prodMk measurable_const)))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg ξ)),
    radonLIntegral, radonTransformAll,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => h₀ _)
      hm'.aestronglyMeasurable]
  ring

end LinearImage

section SphericalImage

open Metric

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- For positive radius `r`, dilate the angular measure on the unit sphere
and multiply by the `d`-dimensional area factor. The spherical density
uses this measure only at positive radii. -/
def sphereSurfaceMeasure (d : ℕ) (r : ℝ) : Measure 𝔼 :=
  ENNReal.ofReal (r ^ d) • (volume : Measure 𝔼).toSphere.map
    (fun ω : sphere (0 : 𝔼) 1 => r • (ω : 𝔼))

/-- The integral over a sphere at a fixed positive radius. -/
def sphereLIntegral (f : 𝔼 → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, f x ∂sphereSurfaceMeasure d r

/-- Integration over a sphere can be pulled back to the unit sphere. -/
theorem sphereLIntegral_eq (f : 𝔼 → ℝ≥0∞) (hf : Measurable f) (r : ℝ) :
    sphereLIntegral f r = ENNReal.ofReal (r ^ d) *
      ∫⁻ ω : sphere (0 : 𝔼) 1, f (r • (ω : 𝔼)) ∂(volume : Measure 𝔼).toSphere := by
  rw [sphereLIntegral, sphereSurfaceMeasure, lintegral_smul_measure,
    lintegral_map hf (by fun_prop), smul_eq_mul]

private theorem measurable_sphereLIntegral {f : 𝔼 → ℝ≥0∞} (hf : Measurable f) :
    Measurable (sphereLIntegral f) := by
  have h : Measurable (fun z : ℝ × sphere (0 : 𝔼) 1 => f (z.1 • (z.2 : 𝔼))) := hf.comp (by fun_prop)
  have hm := (measurable_id.pow_const d).ennreal_ofReal.mul
    (h.lintegral_prod_right' (ν := (volume : Measure 𝔼).toSphere))
  convert hm using 1
  funext r
  exact sphereLIntegral_eq f hf r

/-- Polar change of variables with the surface integral on each sphere. -/
theorem lintegral_eq_lintegral_sphereLIntegral (f : 𝔼 → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ r in Ioi (0 : ℝ), sphereLIntegral f r := by
  let μ : Measure 𝔼 := volume
  let g : sphere (0 : 𝔼) 1 × Ioi (0 : ℝ) → ℝ≥0∞ := fun z => f ((z.2 : ℝ) • (z.1 : 𝔼))
  have hg : Measurable g := hf.comp (by fun_prop)
  have hσ := μ.measurePreserving_homeomorphUnitSphereProd
  have hdim : Module.finrank ℝ 𝔼 - 1 = d := by simp
  rw [hdim] at hσ
  calc
    (∫⁻ x, f x) = ∫⁻ x : ({(0 : 𝔼)}ᶜ : Set 𝔼), f x.1 ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ z, g z ∂μ.toSphere.prod (Measure.volumeIoiPow d) := by
      have h := hσ.lintegral_comp hg
      refine Eq.trans ?_ h
      apply lintegral_congr
      intro x
      simp only [g, ← homeomorphUnitSphereProd_symm_apply_coe, Homeomorph.symm_apply_apply]
    _ = ∫⁻ r : Ioi (0 : ℝ), (∫⁻ ω, g (ω, r) ∂μ.toSphere) ∂Measure.volumeIoiPow d :=
      lintegral_prod_symm' _ hg
    _ = ∫⁻ r in Ioi (0 : ℝ), sphereLIntegral f r := by
      rw [Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg.lintegral_prod_left']
      have he : ((fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ d)) *
          (fun r => ∫⁻ ω, g (ω, r) ∂μ.toSphere)) = fun r => sphereLIntegral f r.1 := by
        funext r
        exact (sphereLIntegral_eq f hf r.1).symm
      rw [he, lintegral_subtype_comap measurableSet_Ioi]

/-- **Equation (195)** of [benIsrael2003generalized], Chapter 8.
The density is zero off the positive ray, and otherwise divides the
sphere integral by the derivative of the squared radius. -/
def normSqImageDensity (f : 𝔼 → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  if 0 < y then ENNReal.ofReal ((2 * Real.sqrt y)⁻¹) * sphereLIntegral f (Real.sqrt y) else 0

private theorem image_sqrt_inter_Ioi (S : Set ℝ) :
    Real.sqrt '' (S ∩ Ioi 0) = Ioi 0 ∩ (fun r : ℝ => r ^ 2) ⁻¹' S := by
  ext r
  constructor
  · rintro ⟨y, ⟨hy, hy₀⟩, rfl⟩
    refine ⟨mem_Ioi.mpr (Real.sqrt_pos.2 hy₀), ?_⟩
    change Real.sqrt y ^ 2 ∈ S
    rwa [Real.sq_sqrt (mem_Ioi.mp hy₀).le]
  · rintro ⟨hr, hS⟩
    exact ⟨r ^ 2, ⟨hS, mem_Ioi.mpr (sq_pos_of_pos hr)⟩, Real.sqrt_sq (mem_Ioi.mp hr).le⟩

private theorem sphereLIntegral_indicator_normSq (S : Set ℝ) {f : 𝔼 → ℝ≥0∞} (hf : Measurable f)
    (hS : MeasurableSet S) (r : ℝ) (hr : 0 < r) :
    sphereLIntegral (((fun x : 𝔼 => ‖x‖ ^ 2) ⁻¹' S).indicator f) r =
      ((fun t : ℝ => t ^ 2) ⁻¹' S).indicator (sphereLIntegral f) r := by
  have hm : Measurable (fun x : 𝔼 => ‖x‖ ^ 2) := by fun_prop
  rw [sphereLIntegral_eq _ (hf.indicator (hm hS))]
  have hn (ω : sphere (0 : 𝔼) 1) : ‖r • (ω : 𝔼)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp ω.2, mul_one]
  by_cases h : r ^ 2 ∈ S
  · simp only [indicator, mem_preimage, hn, h, ite_true]
    exact (sphereLIntegral_eq f hf r).symm
  · simp only [indicator, mem_preimage, hn, h, ite_false, lintegral_zero, mul_zero]

/-- **Corollary 5**, Equations (191)–(195) of [benIsrael2003generalized],
Chapter 8. The squared norm has the surface-integral density in (195). -/
theorem corollary_5 {μ : Measure 𝔼} {f : 𝔼 → ℝ≥0∞} (hf : IsLebesgueProbabilityDensity μ f) :
    IsLebesgueProbabilityDensity (μ.map fun x => ‖x‖ ^ 2) (normSqImageDensity f) := by
  have hm : Measurable (fun x : 𝔼 => ‖x‖ ^ 2) := by fun_prop
  have hs := measurable_sphereLIntegral hf.measurable
  have hd : Measurable (fun y : ℝ =>
    ENNReal.ofReal ((2 * Real.sqrt y)⁻¹) * sphereLIntegral f (Real.sqrt y)) := by
    fun_prop
  refine ⟨hd.indicator measurableSet_Ioi, ?_,
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr hf.isProbabilityMeasure⟩
  ext S hS
  rw [Measure.map_apply hm hS, hf.eq_withDensity,
    withDensity_apply _ (hm hS), withDensity_apply _ hS]
  let A := (fun x : 𝔼 => ‖x‖ ^ 2) ⁻¹' S
  let B := (fun r : ℝ => r ^ 2) ⁻¹' S
  have hB : MeasurableSet B := (measurable_id.pow_const 2) hS
  calc
    (∫⁻ x in A, f x) = ∫⁻ r in Ioi (0 : ℝ), sphereLIntegral (A.indicator f) r := by
      rw [← lintegral_indicator (hm hS)]
      exact lintegral_eq_lintegral_sphereLIntegral _ (hf.measurable.indicator (hm hS))
    _ = ∫⁻ r in Real.sqrt '' (S ∩ Ioi 0), sphereLIntegral f r := by
      rw [image_sqrt_inter_Ioi, inter_comm, ← Measure.restrict_restrict hB,
        ← lintegral_indicator hB]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact sphereLIntegral_indicator_normSq S hf.measurable hS r hr
    _ = ∫⁻ y in S ∩ Ioi 0,
      ENNReal.ofReal ((2 * Real.sqrt y)⁻¹) * sphereLIntegral f (Real.sqrt y) := by
      have hinj : InjOn Real.sqrt (S ∩ Ioi 0) := by
        intro x hx y hy he
        have hh := congrArg (fun t : ℝ => t ^ 2) he
        change (Real.sqrt x)^2 = (Real.sqrt y)^2 at hh
        rwa [Real.sq_sqrt (mem_Ioi.mp hx.2).le, Real.sq_sqrt (mem_Ioi.mp hy.2).le] at hh
      have hp : (S ∩ Ioi (0 : ℝ)).indicator
          (fun y => ENNReal.ofReal |1 / (2 * Real.sqrt y)| * sphereLIntegral f (Real.sqrt y)) =
          (S ∩ Ioi (0 : ℝ)).indicator
          (fun y => ENNReal.ofReal ((2 * Real.sqrt y)⁻¹) * sphereLIntegral f (Real.sqrt y)) := by
        funext y
        by_cases hy : y ∈ S ∩ Ioi (0 : ℝ)
        · simp only [indicator_of_mem hy, one_div,
          abs_of_nonneg (by positivity : 0 ≤ (2 * Real.sqrt y)⁻¹)]
        · simp only [indicator_of_notMem hy]
      rw [lintegral_image_eq_lintegral_abs_deriv_mul (hS.inter measurableSet_Ioi)
        (fun y hy => (Real.hasDerivAt_sqrt hy.2.ne').hasDerivWithinAt) hinj,
        ← lintegral_indicator (hS.inter measurableSet_Ioi), hp,
          lintegral_indicator (hS.inter measurableSet_Ioi)]
    _ = ∫⁻ y in S, normSqImageDensity f y := by
      rw [inter_comm, ← Measure.restrict_restrict measurableSet_Ioi,
        ← lintegral_indicator measurableSet_Ioi]
      rfl

/-- **Equations (191) and (194)** of [benIsrael2003generalized], Chapter 8.
The level variable is the sum of the squares of all coordinates. -/
theorem normSqImage_eq_sum_sq (x : 𝔼) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq x

/-- **Equation (192)** of [benIsrael2003generalized], Chapter 8.
With sign `ε = ±1`, these give the two hemisphere heights. -/
def hemisphereHeight (ε y : ℝ) (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ε * Real.sqrt (y - ‖u‖ ^ 2)

/-- Each hemisphere height solves the squared-radius level equation. -/
theorem normSq_snocLast_hemisphereHeight {ε y : ℝ} (hε : ε ^ 2 = 1)
    {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ ^ 2 < y) :
    ‖snocLast u (hemisphereHeight ε y u)‖ ^ 2 = y := by
  rw [norm_sq_eq_init_add_last, init_snocLast, snocLast_apply_last, hemisphereHeight,
    mul_pow, hε, one_mul, Real.sq_sqrt (sub_pos.mpr hu).le]
  ring

/-- **Equation (193a)** of [benIsrael2003generalized], Chapter 8.
The derivative of a hemisphere height with respect to the squared radius. -/
theorem hasDerivAt_hemisphereHeight {ε y : ℝ} {u : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ ^ 2 < y) :
    HasDerivAt (fun t => hemisphereHeight ε t u) (ε / (2 * Real.sqrt (y - ‖u‖ ^ 2))) y := by
  have h := (Real.hasDerivAt_sqrt (sub_pos.mpr hu).ne').comp y
    ((hasDerivAt_id y).sub_const (‖u‖ ^ 2))
  simpa [hemisphereHeight, div_eq_mul_inv] using h.const_mul ε

private theorem hasGradientAt_hemisphereHeight {ε y : ℝ} {u : EuclideanSpace ℝ (Fin d)}
    (hu : ‖u‖ ^ 2 < y) :
    HasGradientAt (hemisphereHeight ε y) ((-ε / Real.sqrt (y - ‖u‖ ^ 2)) • u) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (Real.hasDerivAt_sqrt (sub_pos.mpr hu).ne').comp_hasFDerivAt u
    ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_sub y)
  have he : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)))
      ((-ε / Real.sqrt (y - ‖u‖ ^ 2)) • u) =
      ε • ((1 / (2 * Real.sqrt (y - ‖u‖ ^ 2))) • -(2 • innerSL ℝ u)) := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply, smul_eq_mul]
    ring
  rw [he]
  exact h.const_smul ε

/-- **Equation (193b)** of [benIsrael2003generalized], Chapter 8.
The hemisphere chart has surface Jacobian `√y / √(y−‖u‖²)` at interior points. -/
theorem graphDensity_hemisphereHeight {ε y : ℝ} (hε : ε ^ 2 = 1)
    {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ ^ 2 < y) :
    graphDensity (hemisphereHeight ε y) u = Real.sqrt y / Real.sqrt (y - ‖u‖ ^ 2) := by
  have hp := sub_pos.mpr hu
  have hpos := Real.sqrt_pos.mpr hp
  have hy : 0 < y := (sq_nonneg _).trans_lt hu
  rw [graphDensity, (hasGradientAt_hemisphereHeight (ε := ε) hu).gradient, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, div_pow, neg_sq, hε, Real.sq_sqrt hp.le,
    ← Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg y) hpos.le), div_pow, Real.sq_sqrt hy.le,
    Real.sq_sqrt hp.le]
  congr 1
  field_simp
  ring

/-- **Example 6**, Equations (196)–(197) of [benIsrael2003generalized], Chapter 8.
When the joint density depends only on the squared norm, the squared-radius
density is the radial profile times the explicit Euclidean sphere factor. -/
theorem density_normSq_of_spherical {μ : Measure 𝔼} (p : ℝ → ℝ≥0∞)
    (hf : IsLebesgueProbabilityDensity μ (fun x => p (‖x‖ ^ 2))) :
    IsLebesgueProbabilityDensity (μ.map fun x => ‖x‖ ^ 2) (fun y =>
      if 0 < y then ENNReal.ofReal
        (Real.pi ^ ((↑(d + 1) : ℝ) / 2) / Real.Gamma ((↑(d + 1) : ℝ) / 2) *
          y ^ ((↑(d + 1) : ℝ) / 2 - 1)) * p y else 0) := by
  convert corollary_5 hf using 1
  funext y
  rw [normSqImageDensity]
  by_cases hy : 0 < y
  · rw [ite_eq_left hy, ite_eq_left hy, sphereLIntegral_eq _ hf.measurable]
    have hrad (ω : sphere (0 : 𝔼) 1) : ‖Real.sqrt y • (ω : 𝔼)‖ ^ 2 = y := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        mem_sphere_zero_iff_norm.mp ω.2, mul_one, Real.sq_sqrt hy.le]
    simp_rw [hrad, lintegral_const]
    let q : ℝ := (↑(d + 1) : ℝ) / 2
    have hA : (volume : Measure 𝔼).toSphere univ =
        ENNReal.ofReal (2 * Real.pi ^ q / Real.Gamma q) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact congrArg ENNReal.ofReal (exercise_41_unitSphereArea (Nat.succ_ne_zero d))
    rw [hA]
    have hpow : Real.sqrt y ^ d / Real.sqrt y = y ^ (q - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_sub hy]
      congr 1
      simp only [q, Nat.cast_add, Nat.cast_one]
      ring
    have hh : ((2 * Real.sqrt y)⁻¹ * Real.sqrt y ^ d) * (2 * Real.pi ^ q / Real.Gamma q) =
        Real.pi ^ q / Real.Gamma q * y ^ (q - 1) := by
      rw [← hpow]
      field_simp [(Real.sqrt_pos.mpr hy).ne']
    symm
    calc
      _ = (ENNReal.ofReal ((2 * Real.sqrt y)⁻¹) * ENNReal.ofReal (Real.sqrt y ^ d) *
          ENNReal.ofReal (2 * Real.pi ^ q / Real.Gamma q)) * p y := by ac_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.sqrt y)⁻¹),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.sqrt y)⁻¹ * Real.sqrt y ^ d), hh]
  · rw [ite_eq_right hy, ite_eq_right hy]

section HemisphereIntegrals

local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-- The surface integral over an open hemisphere expressed in its
last-coordinate chart. -/
def hemisphereLIntegral (ε : ℝ) (f : 𝔼 → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in {u : 𝔼' | ‖u‖ ^ 2 < y},
    ENNReal.ofReal (graphDensity (hemisphereHeight ε y) u) * f (snocLast u (hemisphereHeight ε y u))

/-- The squared-radius density using the upper and lower hemisphere charts. -/
def normSqHemisphereDensity (f : 𝔼 → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  if 0 < y then ENNReal.ofReal ((2 * Real.sqrt y)⁻¹) *
    (hemisphereLIntegral 1 f y + hemisphereLIntegral (-1) f y) else 0

private def hemisphereKernel (ε : ℝ) (f : 𝔼 → ℝ≥0∞) (z : 𝔼' × ℝ) : ℝ≥0∞ :=
  if ‖z.1‖ ^ 2 < z.2 then ENNReal.ofReal ((2 * Real.sqrt (z.2 - ‖z.1‖ ^ 2))⁻¹) *
    f (snocLast z.1 (hemisphereHeight ε z.2 z.1)) else 0

private theorem measurable_hemisphereKernel (ε : ℝ) {f : 𝔼 → ℝ≥0∞} (hf : Measurable f) :
    Measurable (hemisphereKernel ε f) := by
  have ha : Measurable (fun z : 𝔼' × ℝ =>
    ENNReal.ofReal ((2 * Real.sqrt (z.2 - ‖z.1‖ ^ 2))⁻¹)) := by
    fun_prop
  have hb : Measurable (fun z : 𝔼' × ℝ => hemisphereHeight ε z.2 z.1) := by
    unfold hemisphereHeight
    fun_prop
  exact (ha.mul (hf.comp ((measurable_snocLast d).comp (measurable_fst.prodMk hb)))).ite
    (measurableSet_lt (measurable_fst.norm.pow_const 2) measurable_snd) measurable_const

private theorem image_signed_sqrt {ε a : ℝ} (hε : ε ^ 2 = 1) :
    (fun y => ε * Real.sqrt (y - a)) '' Ioi a = {t | 0 < ε * t} := by
  have hsq : ε * ε = 1 := by simpa only [pow_two] using hε
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 < ε * (ε * Real.sqrt (y - a))
    rw [← mul_assoc, hsq, one_mul]
    exact Real.sqrt_pos.mpr (sub_pos.mpr hy)
  · intro ht
    change 0 < ε * t at ht
    have ht₀ : t ≠ 0 := by
      intro he
      simp [he] at ht
    refine ⟨a + t ^ 2, mem_Ioi.mpr (lt_add_of_pos_right _ (sq_pos_of_ne_zero ht₀)), ?_⟩
    have hsq' : (ε * t) ^ 2 = t ^ 2 := by rw [mul_pow, hε, one_mul]
    change ε * Real.sqrt (a + t ^ 2 - a) = t
    rw [add_sub_cancel_left, ← hsq', Real.sqrt_sq ht.le, ← mul_assoc, hsq, one_mul]

private theorem lintegral_hemisphereKernel {ε : ℝ} (hε : ε ^ 2 = 1) (f : 𝔼 → ℝ≥0∞) (u : 𝔼') :
    ∫⁻ t in {t : ℝ | 0 < ε * t}, f (snocLast u t) = ∫⁻ y, hemisphereKernel ε f (u, y) := by
  let a := ‖u‖ ^ 2
  have hinj : InjOn (fun y => ε * Real.sqrt (y - a)) (Ioi a) := by
    intro x hx y hy he
    have he' := congrArg (fun t : ℝ => t ^ 2) he
    change (ε * Real.sqrt (x - a)) ^ 2 = (ε * Real.sqrt (y - a)) ^ 2 at he'
    simp only [mul_pow, hε, one_mul, Real.sq_sqrt (sub_pos.mpr hx).le,
      Real.sq_sqrt (sub_pos.mpr hy).le] at he'
    exact sub_left_injective he'
  have hd (y : ℝ) (hy : y ∈ Ioi a) :
      HasDerivAt (fun y => ε * Real.sqrt (y - a)) (ε / (2 * Real.sqrt (y - a))) y :=
    hasDerivAt_hemisphereHeight hy
  have ha : |ε| = 1 := (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp (by rw [sq_abs, hε, one_pow])
  rw [← image_signed_sqrt (a := a) hε, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun y hy => (hd y hy).hasDerivWithinAt) hinj, ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun y => ?_
  change (Ioi a).indicator _ y = _
  by_cases hy : y ∈ Ioi a
  · have hy' : ‖u‖ ^ 2 < y := hy
    rw [indicator_of_mem hy]
    simp [hemisphereKernel, hy', hemisphereHeight, abs_div, ha,
      abs_of_nonneg (show 0 ≤ 2 * Real.sqrt (y - a) by positivity), one_div, a]
  · rw [indicator_of_notMem hy]
    have hy' : ¬ ‖u‖ ^ 2 < y := hy
    simp [hemisphereKernel, hy']

private theorem lintegral_eq_lintegral_hemisphereKernel (f : 𝔼 → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ y, ∫⁻ u, (hemisphereKernel 1 f (u, y) + hemisphereKernel (-1) f (u, y)) := by
  let F : 𝔼' × ℝ → ℝ≥0∞ := fun z => f (snocLast z.1 z.2)
  let K : 𝔼' × ℝ → ℝ≥0∞ := fun z => hemisphereKernel 1 f z + hemisphereKernel (-1) f z
  have hF : Measurable F := hf.comp (measurable_snocLast d)
  have hK : Measurable K := (measurable_hemisphereKernel 1 hf).add
    (measurable_hemisphereKernel (-1) hf)
  have splitR : ({(0 : ℝ)}ᶜ : Set ℝ) = Ioi 0 ∪ Iio 0 := by
    ext x
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_Ioi, mem_Iio]
    exact ne_iff_gt_or_lt
  calc
    (∫⁻ x, f x) = ∫⁻ z, F z ∂((volume : Measure 𝔼').prod (volume : Measure ℝ)) :=
      ((measurePreserving_snocLast d).lintegral_comp hf).symm
    _ = ∫⁻ u, ∫⁻ t, F (u, t) := lintegral_prod F hF.aemeasurable
    _ = ∫⁻ u, ∫⁻ y, K (u, y) := by
      refine lintegral_congr fun u => ?_
      have hs : ∫⁻ t, F (u, t) =
        (∫⁻ t in Ioi (0 : ℝ), F (u, t)) + ∫⁻ t in Iio (0 : ℝ), F (u, t) := by
        calc
          _ = ∫⁻ t in ({(0 : ℝ)}ᶜ : Set ℝ), F (u, t) := by rw [restrict_compl_singleton]
          _ = _ := by
            have hd : Disjoint (Ioi (0 : ℝ)) (Iio 0) :=
              disjoint_left.mpr fun _ h₁ h₂ => lt_asymm (mem_Ioi.mp h₁) (mem_Iio.mp h₂)
            rw [splitR, lintegral_union measurableSet_Iio hd]
      have h₁ : {t : ℝ | 0 < 1 * t} = Ioi 0 := by ext t; simp
      have h₂ : {t : ℝ | 0 < (-1) * t} = Iio 0 := by ext t; simp
      rw [hs, ← h₁, ← h₂]
      change (∫⁻ t in {t : ℝ | 0 < 1 * t}, f (snocLast u t)) +
        (∫⁻ t in {t : ℝ | 0 < (-1) * t}, f (snocLast u t)) = _
      rw [lintegral_hemisphereKernel (by norm_num : (1 : ℝ) ^ 2 = 1) f u,
        lintegral_hemisphereKernel (by norm_num : (-1 : ℝ) ^ 2 = 1) f u]
      exact (lintegral_add_left ((measurable_hemisphereKernel 1 hf).comp
        (measurable_const.prodMk measurable_id)) _).symm
    _ = ∫⁻ y, ∫⁻ u, K (u, y) := lintegral_lintegral_swap hK.aemeasurable

private theorem hemisphereKernel_eq_graphDensity {ε : ℝ} (hε : ε ^ 2 = 1) (f : 𝔼 → ℝ≥0∞)
    {y : ℝ} (hy : 0 < y) :
    ∫⁻ u, hemisphereKernel ε f (u, y) =
      ENNReal.ofReal ((2 * Real.sqrt y)⁻¹) * hemisphereLIntegral ε f y := by
  have hmeas : MeasurableSet {u : 𝔼' | ‖u‖ ^ 2 < y} :=
    measurableSet_lt (show Measurable (fun u : 𝔼' => ‖u‖ ^ 2) by fun_prop) measurable_const
  rw [hemisphereLIntegral, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator hmeas]
  refine lintegral_congr fun u => ?_
  by_cases hu : ‖u‖ ^ 2 < y
  · have hu' : u ∈ {u : 𝔼' | ‖u‖ ^ 2 < y} := hu
    rw [indicator_of_mem hu']
    simp only [hemisphereKernel, ite_eq_left hu, graphDensity_hemisphereHeight hε hu,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.sqrt y)⁻¹)]
    congr 2
    field_simp [(Real.sqrt_pos.mpr hy).ne', (Real.sqrt_pos.mpr (sub_pos.mpr hu)).ne']
  · have hu' : u ∉ {u : 𝔼' | ‖u‖ ^ 2 < y} := hu
    simp only [hemisphereKernel, ite_eq_right hu, indicator_of_notMem hu']

private theorem normSqHemisphereDensity_eq_kernel (f : 𝔼 → ℝ≥0∞) (hf : Measurable f) (y : ℝ) :
    normSqHemisphereDensity f y =
      ∫⁻ u, (hemisphereKernel 1 f (u, y) + hemisphereKernel (-1) f (u, y)) := by
  unfold normSqHemisphereDensity
  by_cases hy : 0 < y
  · have hm : Measurable (fun u : 𝔼' => hemisphereKernel 1 f (u, y)) :=
      (measurable_hemisphereKernel 1 hf).comp (measurable_id.prodMk measurable_const)
    rw [ite_eq_left hy, lintegral_add_left hm,
      hemisphereKernel_eq_graphDensity (by norm_num : (1 : ℝ) ^ 2 = 1) f hy,
      hemisphereKernel_eq_graphDensity (by norm_num : (-1 : ℝ) ^ 2 = 1) f hy, mul_add]
  · have h (u : 𝔼') : ¬ ‖u‖ ^ 2 < y := not_lt_of_ge ((not_lt.mp hy).trans (sq_nonneg _))
    simp only [ite_eq_right hy, hemisphereKernel, h, ite_false, add_zero, lintegral_zero]

/-- **Corollary 5**, Equation (195), evaluated by the two hemisphere
charts over the open ball of radius `√y`. -/
theorem corollary_5_hemispheres {μ : Measure 𝔼} {f : 𝔼 → ℝ≥0∞}
    (hf : IsLebesgueProbabilityDensity μ f) :
    IsLebesgueProbabilityDensity (μ.map fun x => ‖x‖ ^ 2) (normSqHemisphereDensity f) := by
  have hm : Measurable (fun x : 𝔼 => ‖x‖ ^ 2) := by fun_prop
  have hk : Measurable (normSqHemisphereDensity f) := by
    have h := (measurable_hemisphereKernel 1 hf.measurable).add
      (measurable_hemisphereKernel (-1) hf.measurable)
    convert h.lintegral_prod_left' (μ := (volume : Measure 𝔼')) using 1
    funext y
    exact normSqHemisphereDensity_eq_kernel f hf.measurable y
  refine ⟨hk, ?_,
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr hf.isProbabilityMeasure⟩
  ext S hS
  rw [Measure.map_apply hm hS, hf.eq_withDensity,
    withDensity_apply _ (hm hS), withDensity_apply _ hS,
    ← lintegral_indicator (hm hS),
      lintegral_eq_lintegral_hemisphereKernel _ (hf.measurable.indicator (hm hS)),
    ← lintegral_indicator hS]
  refine lintegral_congr fun y => ?_
  let A := (fun x : 𝔼 => ‖x‖ ^ 2) ⁻¹' S
  have hq (ε : ℝ) (hε : ε ^ 2 = 1) (u : 𝔼') :
      hemisphereKernel ε (A.indicator f) (u, y) =
        S.indicator (fun v => hemisphereKernel ε f (u, v)) y := by
    by_cases hu : ‖u‖ ^ 2 < y
    · have hmem : snocLast u (hemisphereHeight ε y u) ∈ A ↔ y ∈ S := by
        change ‖snocLast u (hemisphereHeight ε y u)‖ ^ 2 ∈ S ↔ y ∈ S
        rw [normSq_snocLast_hemisphereHeight hε hu]
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy]
        simp only [hemisphereKernel, ite_eq_left hu, indicator_of_mem (hmem.mpr hy)]
      · rw [indicator_of_notMem hy]
        simp only [hemisphereKernel, ite_eq_left hu, indicator_of_notMem (hmem.not.mpr hy),
          mul_zero]
    · simp only [hemisphereKernel, ite_eq_right hu, indicator]
      split_ifs <;> rfl
  change (∫⁻ u, hemisphereKernel 1 (A.indicator f) (u, y) +
    hemisphereKernel (-1) (A.indicator f) (u, y)) = _
  simp_rw [hq 1 (by norm_num), hq (-1) (by norm_num)]
  by_cases hy : y ∈ S
  · simp only [indicator_of_mem hy]
    exact (normSqHemisphereDensity_eq_kernel f hf.measurable y).symm
  · simp only [indicator_of_notMem hy, add_zero, lintegral_zero]

/-- The angular and hemisphere formulas give the same density almost everywhere. -/
theorem normSqImageDensity_ae_eq_hemisphereDensity {μ : Measure 𝔼} {f : 𝔼 → ℝ≥0∞}
    (hf : IsLebesgueProbabilityDensity μ f) :
    normSqImageDensity f =ᵐ[volume] normSqHemisphereDensity f := by
  have h₁ := corollary_5 hf
  have h₂ := corollary_5_hemispheres hf
  exact (withDensity_eq_iff_of_sigmaFinite h₁.measurable.aemeasurable h₂.measurable.aemeasurable).mp
    (h₁.eq_withDensity.symm.trans h₂.eq_withDensity)

end HemisphereIntegrals

end SphericalImage

section ChiSquared

open ProbabilityTheory

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The joint law of independent standard normal coordinates. -/
def independentStandardNormalLaw (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (MeasurableEquiv.toLp 2 (Fin n → ℝ))

private theorem independentStandardNormal_pi_density (n : ℕ) :
    IsLebesgueProbabilityDensity (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  have hm : Measurable (fun x : Fin n → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) :=
    Finset.measurable_prod _
      (fun i _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  refine ⟨hm.ennreal_ofReal, Measure.pi_eq ?_, inferInstance⟩
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  have hm' : Integrable (fun x : Fin n → ℝ => ∏ i, gaussianPDFReal 0 1 (x i))
      (volume.restrict (univ.pi S)) := by
    change Integrable _ ((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (univ.pi S))
    rw [Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun i => (integrable_gaussianPDFReal 0 1).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hm'
    (Filter.Eventually.of_forall fun _ =>
      Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg 0 1 _)]
  change ENNReal.ofReal (∫ x, (∏ i, gaussianPDFReal 0 1 (x i))
    ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (univ.pi S)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  simp_rw [gaussianReal_apply_eq_integral (0 : ℝ) one_ne_zero]

/-- **Exercise 48** of [benIsrael2003generalized], Chapter 8. The joint
density of independent standard normal coordinates is a function of the
squared norm, as in Equation (196). -/
theorem independentStandardNormalLaw_density (n : ℕ) :
    IsLebesgueProbabilityDensity (independentStandardNormalLaw n)
      (fun x => ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / 2))) := by
  have h := (independentStandardNormal_pi_density n).map_measurePreserving
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) (PiLp.volume_preserving_toLp (Fin n))
  change IsLebesgueProbabilityDensity (independentStandardNormalLaw n)
    (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) at h
  convert h using 1
  funext x
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, ← Finset.sum_div]
  congr 1
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  · rw [Finset.sum_neg_distrib, EuclideanSpace.real_norm_sq_eq]

/-- **Exercise 48**, Equation (202) of [benIsrael2003generalized], Chapter 8.
The sum of squares of `d+1` independent standard normal variables has the
chi-squared density with `d+1` degrees of freedom. -/
theorem exercise_8_48 (d : ℕ) :
    IsLebesgueProbabilityDensity
      ((independentStandardNormalLaw (d + 1)).map fun x => ‖x‖ ^ 2)
      (fun y => if 0 < y then ENNReal.ofReal
        (1 / ((2 : ℝ) ^ ((↑(d + 1) : ℝ) / 2) * Real.Gamma ((↑(d + 1) : ℝ) / 2)) *
          y ^ ((↑(d + 1) : ℝ) / 2 - 1) * Real.exp (-y / 2)) else 0) := by
  let q : ℝ := (↑(d + 1) : ℝ) / 2
  have h := density_normSq_of_spherical
    (fun y => ENNReal.ofReal ((2 * Real.pi) ^ (-q) * Real.exp (-y / 2)))
    (by simpa only [q, neg_div] using independentStandardNormalLaw_density (d + 1))
  convert h using 1
  funext y
  by_cases hy : 0 < y
  · rw [ite_eq_left hy, ite_eq_left hy,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi ^ q / Real.Gamma q * y ^ (q - 1))]
    congr 1
    change 1 / ((2 : ℝ) ^ q * Real.Gamma q) * y ^ (q - 1) * Real.exp (-y / 2) =
      (Real.pi ^ q / Real.Gamma q * y ^ (q - 1)) * ((2 * Real.pi) ^ (-q) * Real.exp (-y / 2))
    rw [Real.rpow_neg (by positivity : 0 ≤ 2 * Real.pi), Real.mul_rpow (by norm_num) Real.pi_pos.le]
    field_simp [(Real.rpow_pos_of_pos Real.pi_pos q).ne']
  · rw [ite_eq_right hy, ite_eq_right hy]

end ChiSquared

section RestrictedGraphDensity

open EuclideanSpace

variable {d : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "Y" => EuclideanSpace ℝ (Fin (d + 1))

/-- A last-coordinate inverse defined on the attainable levels. For each
horizontal parameter its domain consists of the attained levels and its
height gives the unique corresponding final coordinate. -/
structure RestrictedImageGraphChart (h : Y → ℝ) where
  /-- The pairs of a horizontal parameter and an attainable level. -/
  domain : Set (X × ℝ)
  /-- Height as a function of parameter and level. -/
  height : X × ℝ → ℝ
  /-- Derivative of the inverse height in the level coordinate. -/
  heightDeriv : X × ℝ → ℝ
  /-- The domain of attainable levels is measurable. -/
  measurable_domain : MeasurableSet domain
  /-- The globally extended height function is measurable. -/
  measurable_height : Measurable height
  /-- The globally extended derivative is measurable. -/
  measurable_heightDeriv : Measurable heightDeriv
  /-- Every point in the original space has an attainable level. -/
  level_mem (u : X) (t : ℝ) : (u, h (snocLast u t)) ∈ domain
  /-- The inverse height attains the specified level. -/
  level_height (u : X) (y : ℝ) : (u, y) ∈ domain → h (snocLast u (height (u, y))) = y
  /-- The inverse recovers the original coordinate at its own level. -/
  height_level (u : X) (t : ℝ) : height (u, h (snocLast u t)) = t
  /-- The derivative only needs to exist within the attainable levels. -/
  hasDerivWithinAt_height (u : X) (y : ℝ) (hy : (u, y) ∈ domain) :
    HasDerivWithinAt (fun z => height (u, z)) (heightDeriv (u, y))
      {z | (u, z) ∈ domain} y

namespace RestrictedImageGraphChart

variable {h : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (chart : RestrictedImageGraphChart (d := d) h)

/-- The horizontal parameters at which the level is attained. -/
def parameters (y : ℝ) : Set (EuclideanSpace ℝ (Fin d)) := {u | (u, y) ∈ chart.domain}

/-- The horizontal slice of an attainable-level chart is measurable. -/
theorem measurableSet_parameters (y : ℝ) : MeasurableSet (chart.parameters y) :=
  chart.measurable_domain.preimage (measurable_id.prodMk measurable_const)

/-- The restricted height graph is exactly the level set. -/
theorem image_height_parameters (y : ℝ) :
    (fun u => snocLast u (chart.height (u, y))) '' chart.parameters y = {x | h x = y} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact chart.level_height u y hu
  · intro hx
    change h x = y at hx
    refine ⟨init x, ?_, ?_⟩
    · have hd := chart.level_mem (init x) (x (Fin.last d))
      rwa [snocLast_init_last, hx] at hd
    · have hi := chart.height_level (init x) (x (Fin.last d))
      rw [snocLast_init_last, hx] at hi
      dsimp only
      rw [hi, snocLast_init_last]

private theorem image_height_levels (u : EuclideanSpace ℝ (Fin d)) (S : Set ℝ) :
    (fun y => chart.height (u, y)) '' (S ∩ {y | (u, y) ∈ chart.domain}) =
      (fun t => h (snocLast u t)) ⁻¹' S := by
  ext t
  constructor
  · rintro ⟨y, ⟨hyS, hyD⟩, rfl⟩
    change h (snocLast u (chart.height (u, y))) ∈ S
    rwa [chart.level_height u y hyD]
  · intro ht
    exact ⟨h (snocLast u t), ⟨ht, chart.level_mem u t⟩, chart.height_level u t⟩

private theorem injOn_height (u : EuclideanSpace ℝ (Fin d)) (S : Set ℝ) :
    InjOn (fun y => chart.height (u, y)) (S ∩ {y | (u, y) ∈ chart.domain}) := by
  intro y hy z hz he
  dsimp only at he
  rw [← chart.level_height u y hy.2, ← chart.level_height u z hz.2, he]

end RestrictedImageGraphChart

/-- The restricted image density integrates only over horizontal
parameters at which the target level is attainable. -/
def restrictedGraphImageDensity {h : Y → ℝ} (chart : RestrictedImageGraphChart (d := d) h)
    (f : Y → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in chart.parameters y, ENNReal.ofReal |chart.heightDeriv (u, y)| *
    f (snocLast u (chart.height (u, y)))

/-- **Equations (178)–(183)** of [benIsrael2003generalized], Chapter 8.
The coordinate change only requires an inverse on the attainable levels.
The pushforward law has the fiber integral density over the corresponding
horizontal parameters. -/
theorem imageDensity_graph_restricted {h : Y → ℝ} (hh : Measurable h)
    (chart : RestrictedImageGraphChart (d := d) h) {μ : Measure Y} {f : Y → ℝ≥0∞}
    (hf : IsLebesgueProbabilityDensity μ f) :
    IsLebesgueProbabilityDensity (μ.map h) (restrictedGraphImageDensity chart f) := by
  let raw : X × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal |chart.heightDeriv z| * f (snocLast z.1 (chart.height z))
  let q := chart.domain.indicator raw
  have hraw : Measurable raw :=
    (continuous_abs.measurable.comp chart.measurable_heightDeriv).ennreal_ofReal.mul
      (hf.measurable.comp ((measurable_snocLast d).comp (measurable_fst.prodMk chart.measurable_height)))
  have hq : Measurable q := hraw.indicator chart.measurable_domain
  have hqint (y : ℝ) : (∫⁻ u, q (u, y)) = restrictedGraphImageDensity chart f y := by
    unfold restrictedGraphImageDensity
    rw [← lintegral_indicator (chart.measurableSet_parameters y)]
    rfl
  have hm : Measurable (restrictedGraphImageDensity chart f) := by
    rw [← funext hqint]
    exact hq.lintegral_prod_left'
  refine ⟨hm, ?_, (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).mpr hf.isProbabilityMeasure⟩
  ext S hS
  rw [Measure.map_apply hh hS, hf.eq_withDensity, withDensity_apply _ (hh hS), withDensity_apply _ hS]
  let T := h ⁻¹' S
  let I : X × ℝ → ℝ≥0∞ := fun z => T.indicator f (snocLast z.1 z.2)
  have hI : Measurable I := (hf.measurable.indicator (hh hS)).comp (measurable_snocLast d)
  let J := (Prod.snd ⁻¹' S : Set (X × ℝ)).indicator q
  have hJ : Measurable J := hq.indicator (measurable_snd hS)
  calc
    (∫⁻ x in T, f x) = ∫⁻ z, I z ∂((volume : Measure X).prod (volume : Measure ℝ)) := by
      rw [← lintegral_indicator (hh hS)]
      exact ((measurePreserving_snocLast d).lintegral_comp
        (hf.measurable.indicator (hh hS))).symm
    _ = ∫⁻ u, ∫⁻ y, J (u, y) := by
      rw [lintegral_prod I hI.aemeasurable]
      refine lintegral_congr fun u => ?_
      let Su := S ∩ {y | (u, y) ∈ chart.domain}
      have hSu : MeasurableSet Su :=
        hS.inter (chart.measurable_domain.preimage (measurable_const.prodMk measurable_id))
      have hpre : (fun t => h (snocLast u t)) ⁻¹' S =
          (fun y => chart.height (u, y)) '' Su := (chart.image_height_levels u S).symm
      have ht : MeasurableSet ((fun t => h (snocLast u t)) ⁻¹' S) :=
        hh.comp ((measurable_snocLast d).comp (measurable_const.prodMk measurable_id)) hS
      have hIu : (fun t => I (u, t)) =
          ((fun t => h (snocLast u t)) ⁻¹' S).indicator (fun t => f (snocLast u t)) := rfl
      have hJu : (fun y => J (u, y)) = Su.indicator (fun y => raw (u, y)) := by
        funext y
        by_cases hy : y ∈ S <;> by_cases hUy : (u, y) ∈ chart.domain <;>
          simp [J, q, Su, hy, hUy]
      rw [hIu, hJu, lintegral_indicator ht, lintegral_indicator hSu, hpre]
      exact lintegral_image_eq_lintegral_abs_deriv_mul hSu
        (fun y hy => (chart.hasDerivWithinAt_height u y hy.2).mono Set.inter_subset_right)
        (chart.injOn_height u S) (fun t => f (snocLast u t))
    _ = ∫⁻ y, ∫⁻ u, J (u, y) := lintegral_lintegral_swap hJ.aemeasurable
    _ = ∫⁻ y in S, restrictedGraphImageDensity chart f y := by
      rw [← lintegral_indicator hS]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ S
      · simpa only [J, mem_preimage, hy, indicator_of_mem] using hqint y
      · simp only [J, mem_preimage, hy, not_false_eq_true, indicator_of_notMem, lintegral_zero]

/-- **Theorem 14**, Equations (184)–(185), of [benIsrael2003generalized],
Chapter 8. On the open attainable-parameter domains, the level density
is the actual normalized Hausdorff integral times the absolute ratio of
the level derivative to the graph's area density. -/
theorem theorem_14_restricted {h : Y → ℝ} (hh : Measurable h)
    (chart : RestrictedImageGraphChart (d := d) h)
    {μ : Measure Y} {f : Y → ℝ≥0∞} (hf : IsLebesgueProbabilityDensity μ f)
    (hopen : ∀ y, IsOpen (chart.parameters y))
    (hsmooth : ∀ y, ContDiffOn ℝ 1 (fun u => chart.height (u, y)) (chart.parameters y))
    (c : ℝ → ℝ) (hc : ∀ y u, u ∈ chart.parameters y →
      chart.heightDeriv (u, y) / graphDensity (fun v => chart.height (v, y)) u = c y) :
    IsLebesgueProbabilityDensity (μ.map h) (fun y => ENNReal.ofReal |c y| *
      ∫⁻ x in {x | h x = y}, f x ∂(euclideanHausdorffMeasure d (d + 1))) := by
  convert imageDensity_graph_restricted hh chart hf using 1
  funext y
  let D := chart.parameters y
  let g := fun u => chart.height (u, y)
  let φ : X → Y := fun u => snocLast u (g u)
  have hφ : ContDiffOn ℝ 1 φ D := by
    change ContDiffOn ℝ 1 ((lastInitL d).symm ∘ fun u : X => (g u, u)) D
    exact (lastInitL d).symm.toContinuousLinearMap.contDiff.comp_contDiffOn
      ((hsmooth y).prodMk contDiffOn_id)
  have hD (u : X) (hu : u ∈ D) :
      HasFDerivAt φ (snocLastL (fderiv ℝ g u)) u := by
    have hd := ((hsmooth y).differentiableOn one_ne_zero u hu).differentiableAt ((hopen y).mem_nhds hu)
    exact (lastInitL d).symm.hasFDerivAt.comp u (hd.hasFDerivAt.prodMk (hasFDerivAt_id u))
  have hRank (u : X) (hu : u ∈ D) : Function.Injective (fderiv ℝ φ u) := by
    rw [(hD u hu).fderiv]
    intro a b h
    simpa only [snocLastL_apply, init_snocLast] using congrArg init h
  have hinj : InjOn φ D := by
    intro a _ b _ h
    simpa only [φ, init_snocLast] using congrArg init h
  rw [← chart.image_height_parameters y]
  change ENNReal.ofReal |c y| *
      (∫⁻ x in φ '' D, f x ∂(euclideanHausdorffMeasure d (d + 1))) = _
  rw [lintegral_areaFormula (hopen y) (chart.measurableSet_parameters y) Subset.rfl
    (fun u hu => (hD u hu).differentiableAt.hasFDerivAt)
    (hφ.continuousOn_fderiv_of_isOpen (hopen y) le_rfl) hRank hinj hf.measurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold restrictedGraphImageDensity
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (chart.measurableSet_parameters y)] with u hu
  have hg : EuclideanSpace.gram (fderiv ℝ φ u) = graphDensity g u := by
    rw [(hD u hu).fderiv, gram_snocLastL, graphDensity, norm_gradient_eq]
  have hratio : chart.heightDeriv (u, y) = c y * graphDensity g u :=
    (div_eq_iff (graphDensity_ne_zero (g := g) u)).mp (hc y u hu)
  rw [hg, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), hratio, abs_mul,
    abs_of_nonneg (graphDensity_pos (g := g) u).le]

end RestrictedGraphDensity

section PointwiseHemisphereIntegrals

open EuclideanSpace Metric
open scoped Pointwise

variable {d : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "Y" => EuclideanSpace ℝ (Fin (d + 1))
local notation "H" => euclideanHausdorffMeasure d (d + 1)

private theorem normalizedHausdorff_image_radius (r : ℝ) (hr : 0 < r) (S : Set Y) :
    H ((fun x : Y => r • x) '' S) = ENNReal.ofReal (r ^ d) * H S := by
  change H (r • S) = _
  simp only [euclideanHausdorffMeasure, Measure.smul_apply]
  rw [Measure.hausdorffMeasure_smul₀ (by positivity) hr.ne']
  have hcoe : (↑‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
    change ‖r‖ₑ = _
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos hr]
  simp only [ENNReal.smul_def, NNReal.rpow_natCast, ENNReal.coe_pow, hcoe,
    smul_eq_mul, ENNReal.ofReal_pow hr.le]
  ac_rfl

/-- The positive-radius spherical measure is normalized Hausdorff
measure on the corresponding sphere. -/
theorem sphereSurfaceMeasure_eq_hausdorff {r : ℝ} (hr : 0 < r) :
    sphereSurfaceMeasure d r = (H).restrict (sphere (0 : Y) r) := by
  let φ : Y → Y := fun x => r • x
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hi : Function.Injective φ := smul_right_injective Y hr.ne'
  have hs : Function.Surjective φ := by
    intro y
    exact ⟨r⁻¹ • y, by simp [φ, smul_smul, hr.ne']⟩
  have hrange : φ '' sphere (0 : Y) 1 = sphere (0 : Y) r := by
    change r • sphere (0 : Y) 1 = _
    rw [smul_sphere' hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  unfold sphereSurfaceMeasure
  change ENNReal.ofReal (r ^ d) • ((volume : Measure Y).toSphere.map
    (φ ∘ (Subtype.val : sphere (0 : Y) 1 → Y))) = _
  rw [← Measure.map_map hφ measurable_subtype_coe, exercise_40_polar_area_eq_hausdorff]
  apply Measure.ext
  intro S hS
  rw [Measure.smul_apply, Measure.map_apply hφ hS,
    Measure.restrict_apply (hφ hS), Measure.restrict_apply hS]
  have himg : φ '' (φ ⁻¹' S ∩ sphere (0 : Y) 1) = S ∩ sphere (0 : Y) r := by
    rw [Set.image_inter hi, hrange, Set.image_preimage_eq_inter_range, hs.range_eq, inter_univ]
  rw [← himg]
  exact (normalizedHausdorff_image_radius r hr _).symm

private theorem image_signed_hemisphere_chart {ε y : ℝ} (hε : ε ^ 2 = 1) (hy : 0 < y) :
    (fun u : X => snocLast u (hemisphereHeight ε y u)) '' {u | ‖u‖ ^ 2 < y} =
      sphere (0 : Y) (Real.sqrt y) ∩ {x : Y | 0 < ε * x (Fin.last d)} := by
  have hε' : ε * ε = 1 := by simpa only [pow_two] using hε
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [mem_sphere, dist_zero_right]
      apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [normSq_snocLast_hemisphereHeight hε hu, Real.sq_sqrt hy.le]
    · change 0 < ε * snocLast u (hemisphereHeight ε y u) (Fin.last d)
      rw [snocLast_apply_last, hemisphereHeight, ← mul_assoc, hε', one_mul]
      exact Real.sqrt_pos_of_pos (sub_pos.mpr hu)
  · rintro ⟨hs, hp⟩
    let u := init x
    let t := x (Fin.last d)
    have hnorm : ‖x‖ = Real.sqrt y := by simpa using hs
    have hsq : ‖u‖ ^ 2 + t ^ 2 = y := by
      rw [← norm_sq_eq_init_add_last, hnorm, Real.sq_sqrt hy.le]
    have hsign : 0 < ε * t := hp
    have ht : t ≠ 0 := by intro h; simp [h] at hsign
    have hu : ‖u‖ ^ 2 < y := by linarith [sq_pos_of_ne_zero ht]
    have hheight : hemisphereHeight ε y u = t := by
      rw [hemisphereHeight, show y - ‖u‖ ^ 2 = t ^ 2 by linarith only [hsq],
        show t ^ 2 = (ε * t) ^ 2 by rw [mul_pow, hε, one_mul],
        Real.sqrt_sq hsign.le, ← mul_assoc, hε', one_mul]
    refine ⟨u, hu, ?_⟩
    dsimp only
    rw [hheight]
    exact snocLast_init_last x

private theorem hemisphereLIntegral_eq_Hausdorff {ε y : ℝ} (hε : ε ^ 2 = 1)
    (hy : 0 < y) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    hemisphereLIntegral ε f y =
      ∫⁻ x in sphere (0 : Y) (Real.sqrt y) ∩ {x : Y | 0 < ε * x (Fin.last d)}, f x ∂H := by
  let D : Set X := {u | ‖u‖ ^ 2 < y}
  let g : X → ℝ := hemisphereHeight ε y
  let φ : X → Y := fun u => snocLast u (g u)
  have hD : IsOpen D := isOpen_lt (continuous_norm.pow 2) continuous_const
  have hg : ContDiffOn ℝ 1 g D := by
    unfold g hemisphereHeight
    exact contDiffOn_const.mul (((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn).sqrt
      (fun u hu => (sub_pos.mpr hu).ne'))
  have hc : ContDiffOn ℝ 1 φ D := by
    change ContDiffOn ℝ 1 ((lastInitL d).symm ∘ fun u : X => (g u, u)) D
    exact (lastInitL d).symm.toContinuousLinearMap.contDiff.comp_contDiffOn (hg.prodMk contDiffOn_id)
  have hDf (u : X) (hu : u ∈ D) :
      HasFDerivAt φ (snocLastL (fderiv ℝ g u)) u := by
    have h := (hg.differentiableOn one_ne_zero u hu).differentiableAt (hD.mem_nhds hu)
    exact (lastInitL d).symm.hasFDerivAt.comp u (h.hasFDerivAt.prodMk (hasFDerivAt_id u))
  have hRank (u : X) (hu : u ∈ D) : Function.Injective (fderiv ℝ φ u) := by
    rw [(hDf u hu).fderiv]
    intro a b h
    simpa only [snocLastL_apply, init_snocLast] using congrArg init h
  have hinj : InjOn φ D := by
    intro a _ b _ h
    simpa only [φ, init_snocLast] using congrArg init h
  rw [← image_signed_hemisphere_chart hε hy,
    lintegral_areaFormula hD hD.measurableSet Subset.rfl
      (fun u hu => (hDf u hu).differentiableAt.hasFDerivAt)
      (hc.continuousOn_fderiv_of_isOpen hD le_rfl) hRank hinj hf]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hD.measurableSet] with u hu
  change ENNReal.ofReal (graphDensity g u) * f (φ u) =
    ENNReal.ofReal (EuclideanSpace.gram (fderiv ℝ φ u)) * f (φ u)
  rw [(hDf u hu).fderiv, gram_snocLastL, graphDensity, norm_gradient_eq]

private theorem sphere_equator_Hausdorff_zero {r : ℝ} (hr : 0 < r) :
    H (sphere (0 : Y) r ∩ {x : Y | x (Fin.last d) = 0}) = 0 := by
  have h : (fun x : Y => r • x) '' (sphere (0 : Y) 1 ∩ {x : Y | x (Fin.last d) = 0}) =
      sphere (0 : Y) r ∩ {x : Y | x (Fin.last d) = 0} := by
    rw [Set.image_inter (smul_right_injective Y hr.ne')]
    have h₁ : (fun x : Y => r • x) '' sphere (0 : Y) 1 = sphere 0 r := by
      change r • sphere (0 : Y) 1 = _
      rw [smul_sphere' hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
    have h₂ : (fun x : Y => r • x) '' {x : Y | x (Fin.last d) = 0} =
        {x : Y | x (Fin.last d) = 0} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        change r * x (Fin.last d) = 0
        rw [show x (Fin.last d) = 0 from hx, mul_zero]
      · intro hz
        refine ⟨r⁻¹ • z, ?_, ?_⟩
        · change r⁻¹ * z (Fin.last d) = 0
          rw [show z (Fin.last d) = 0 from hz, mul_zero]
        · simp [smul_smul, hr.ne']
    rw [h₁, h₂]
  rw [← h, normalizedHausdorff_image_radius r hr]
  have hu : H (sphere (0 : Y) 1 ∩ {x : Y | x (Fin.last d) = 0}) = 0 := by
    by_cases hd : d = 0
    · subst d
      have he : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩
          {x : EuclideanSpace ℝ (Fin 1) | x (Fin.last 0) = 0} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hs, hx⟩
        have hz : x = 0 := by
          ext i
          rw [show i = Fin.last 0 from Subsingleton.elim _ _]
          exact hx
        simp [hz] at hs
      rw [he, measure_empty]
    · exact exercise_41_equator_measure_zero hd
  rw [hu, mul_zero]

/-- **Corollary 5**, Equation (195), of [benIsrael2003generalized], Chapter 8.
For every positive squared radius, the angular integral is the sum of
the two open hemisphere chart integrals. -/
theorem sphereLIntegral_eq_hemispheres {f : Y → ℝ≥0∞} (hf : Measurable f)
    {y : ℝ} (hy : 0 < y) :
    sphereLIntegral f (Real.sqrt y) = hemisphereLIntegral 1 f y + hemisphereLIntegral (-1) f y := by
  let r := Real.sqrt y
  let U : Set Y := sphere (0 : Y) r ∩ {x | 0 < x (Fin.last d)}
  let L : Set Y := sphere (0 : Y) r ∩ {x | x (Fin.last d) < 0}
  let E : Set Y := sphere (0 : Y) r ∩ {x | x (Fin.last d) = 0}
  have hcover : sphere (0 : Y) r = (U ∪ L) ∪ E := by
    ext x
    constructor
    · intro hx
      rcases lt_trichotomy (x (Fin.last d)) 0 with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hx, hlt⟩)
      · exact Or.inr ⟨hx, heq⟩
      · exact Or.inl (Or.inl ⟨hx, hgt⟩)
    · rintro ((h | h) | h) <;> exact h.1
  let p : Y →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last d)
  have hL : MeasurableSet L := isClosed_sphere.measurableSet.inter
    (measurableSet_lt p.measurable measurable_const)
  have hE : MeasurableSet E := isClosed_sphere.measurableSet.inter
    (measurableSet_eq_fun p.measurable measurable_const)
  have hul : Disjoint U L := Set.disjoint_left.mpr fun x hx hy =>
    lt_asymm (show 0 < x (Fin.last d) from hx.2) (show x (Fin.last d) < 0 from hy.2)
  have he : Disjoint (U ∪ L) E := Set.disjoint_left.mpr fun x hx hz => by
    rcases hx with hx | hx
    · exact (show 0 < x (Fin.last d) from hx.2).ne hz.2.symm
    · exact (show x (Fin.last d) < 0 from hx.2).ne hz.2
  have hEzero : H E = 0 := sphere_equator_Hausdorff_zero (Real.sqrt_pos_of_pos hy)
  unfold sphereLIntegral
  rw [sphereSurfaceMeasure_eq_hausdorff (Real.sqrt_pos_of_pos hy), hcover,
    lintegral_union hE he, setLIntegral_measure_zero E f hEzero, add_zero, lintegral_union hL hul,
    hemisphereLIntegral_eq_Hausdorff (by norm_num : (1 : ℝ) ^ 2 = 1) hy hf,
    hemisphereLIntegral_eq_Hausdorff (by norm_num : (-1 : ℝ) ^ 2 = 1) hy hf]
  simp only [U, L, r, one_mul, neg_one_mul, neg_pos]

end PointwiseHemisphereIntegrals

section UniformProjection

open EuclideanSpace Matrix

local notation "X₁" => EuclideanSpace ℝ (Fin 1)
local notation "X₂" => EuclideanSpace ℝ (Fin 2)

private def euclideanOneCoordEquiv : X₁ ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

private theorem euclideanOneCoordEquiv_apply (u : X₁) : euclideanOneCoordEquiv u = u 0 := rfl

private theorem measurePreserving_euclideanOneCoordEquiv :
    MeasurePreserving euclideanOneCoordEquiv volume volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))

private def uniformSquare : Set X₂ := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

private theorem measurableSet_uniformSquare : MeasurableSet uniformSquare := by
  have h : uniformSquare = ⋂ i : Fin 2, (EuclideanSpace.proj (𝕜 := ℝ) i) ⁻¹' Icc 0 1 := by
    ext x
    simp only [uniformSquare, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage,
      EuclideanSpace.coe_proj, Set.mem_Icc]
  rw [h]
  exact MeasurableSet.iInter fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).measurable measurableSet_Icc

private theorem volume_uniformSquare : (volume : Measure X₂) uniformSquare = 1 := by
  have he : uniformSquare = WithLp.ofLp ⁻¹' Set.Icc (0 : Fin 2 → ℝ) 1 := by
    ext x
    simp only [uniformSquare, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def,
      Pi.zero_apply, Pi.one_apply]
    exact forall_and
  rw [he, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage measurableSet_Icc.nullMeasurableSet]
  simp [Real.volume_Icc_pi]

/-- The joint Lebesgue law with independent coordinates uniform on the unit interval. -/
def uniformSquareLaw : Measure X₂ := volume.restrict uniformSquare

private theorem uniformSquareLaw_density :
    IsLebesgueProbabilityDensity uniformSquareLaw (uniformSquare.indicator fun _ => 1) := by
  refine ⟨measurable_const.indicator measurableSet_uniformSquare, ?_, ?_⟩
  · exact (withDensity_indicator_one (μ := volume) measurableSet_uniformSquare).symm
  · constructor
    rw [uniformSquareLaw, Measure.restrict_apply_univ, volume_uniformSquare]

private theorem interval_overlap_abs_formula (l u c v : ℝ) (hlu : l ≤ u) (hcv : c ≤ v) :
    max 0 (min u v - max l c) =
      (|u - c| - |u - v| - |l - c| + |l - v|) / 2 := by
  by_cases h₁ : u ≤ c
  · have hu : u ≤ v := h₁.trans hcv
    have hl : l ≤ c := hlu.trans h₁
    rw [min_eq_left hu, max_eq_right hl, max_eq_left (sub_nonpos.mpr h₁),
      abs_of_nonpos (sub_nonpos.mpr h₁), abs_of_nonpos (sub_nonpos.mpr hu),
      abs_of_nonpos (sub_nonpos.mpr hl), abs_of_nonpos (sub_nonpos.mpr (hl.trans hcv))]
    ring
  by_cases h₂ : v ≤ l
  · have hu : v ≤ u := h₂.trans hlu
    have hl : c ≤ l := hcv.trans h₂
    rw [min_eq_right hu, max_eq_left hl, max_eq_left (sub_nonpos.mpr h₂),
      abs_of_nonneg (sub_nonneg.mpr (hl.trans hlu)), abs_of_nonneg (sub_nonneg.mpr hu),
      abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonneg (sub_nonneg.mpr h₂)]
    ring
  have hpos : 0 ≤ min u v - max l c :=
    sub_nonneg.mpr (le_min (max_le hlu (le_of_not_ge h₁)) (max_le (le_of_not_ge h₂) hcv))
  rw [max_eq_right hpos, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h₁)),
    abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h₂))]
  rcases le_total u v with huv | hvu <;> rcases le_total l c with hlc | hcl
  · rw [min_eq_left huv, max_eq_right hlc, abs_of_nonpos (sub_nonpos.mpr huv),
      abs_of_nonpos (sub_nonpos.mpr hlc)]
    ring
  · rw [min_eq_left huv, max_eq_left hcl, abs_of_nonpos (sub_nonpos.mpr huv),
      abs_of_nonneg (sub_nonneg.mpr hcl)]
    ring
  · rw [min_eq_right hvu, max_eq_right hlc, abs_of_nonneg (sub_nonneg.mpr hvu),
      abs_of_nonpos (sub_nonpos.mpr hlc)]
    ring
  · rw [min_eq_right hvu, max_eq_left hcl, abs_of_nonneg (sub_nonneg.mpr hvu),
      abs_of_nonneg (sub_nonneg.mpr hcl)]
    ring

private theorem scaled_unit_interval_iff {a t : ℝ} (ha : a ≠ 0) :
    t ∈ Icc (0 : ℝ) 1 ↔ a * t ∈ Icc (min 0 a) (max 0 a) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [min_eq_right ha.le, max_eq_left ha.le]
    constructor
    · intro ht
      exact ⟨by simpa using mul_le_mul_of_nonpos_left ht.2 ha.le,
        by simpa using mul_le_mul_of_nonpos_left ht.1 ha.le⟩
    · intro ht
      constructor
      · by_contra! ht₀
        exact (show 0 < a * t from mul_pos_of_neg_of_neg ha ht₀).not_ge ht.2
      · by_contra! ht₁
        have h : a * t < a := by simpa using mul_lt_mul_of_neg_left ht₁ ha
        exact h.not_ge ht.1
  · rw [min_eq_left ha.le, max_eq_right ha.le]
    constructor
    · intro ht
      exact ⟨mul_nonneg ha.le ht.1, by simpa using mul_le_mul_of_nonneg_left ht.2 ha.le⟩
    · intro ht
      exact ⟨nonneg_of_mul_nonneg_right ht.1 ha,
        (mul_le_mul_iff_right₀ ha).1 (by simpa [mul_comm] using ht.2)⟩

private theorem shifted_interval_iff {b y w : ℝ} (hb : b ≠ 0) :
    (y - w) / b ∈ Icc (0 : ℝ) 1 ↔ w ∈ Icc (y - max 0 b) (y - min 0 b) := by
  rw [scaled_unit_interval_iff hb, mul_div_cancel₀ _ hb]
  simp only [Set.mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

private theorem uniform_abs_formula (a b y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    let l := min 0 a
    let u := max 0 a
    let c := y - max 0 b
    let v := y - min 0 b
    max 0 (min u v - max l c) / (|a| * |b|) =
       (|y - a - b| - |y - a| - |y - b| + |y|) / (2 * a * b) := by
  dsimp only
  rw [interval_overlap_abs_formula _ _ _ _ (min_le_max : min 0 a ≤ max 0 a)
    (sub_le_sub_left min_le_max _)]
  have habs (p q : ℝ) : |p - (y - q)| = |y - p - q| := by
    rw [abs_sub_comm]
    congr 1
    ring
  simp only [habs]
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb <;>
    simp only [min_eq_right, min_eq_left, max_eq_right, max_eq_left, ha.le, hb.le, abs_of_neg,
      abs_of_pos, ha, hb, sub_zero] <;>
    field_simp [ne_of_lt, ne_of_gt, ha.ne, hb.ne] <;> ring

private theorem volume_uniform_fiber (a b y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (volume : Measure ℝ) {t | t ∈ Icc (0 : ℝ) 1 ∧ (y - a * t) / b ∈ Icc 0 1} =
      ENNReal.ofReal ((max 0 (min (max 0 a) (y - min 0 b) -
        max (min 0 a) (y - max 0 b))) / |a|) := by
  let S : Set ℝ := Icc (min 0 a) (max 0 a) ∩ Icc (y - max 0 b) (y - min 0 b)
  have hpre : {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ (y - a * t) / b ∈ Icc 0 1} =
      (fun t => a * t) ⁻¹' S := by
    ext t
    exact and_congr (scaled_unit_interval_iff ha) (shifted_interval_iff hb)
  rw [hpre, Real.volume_preimage_mul_left ha]
  have hS : S = Icc (max (min 0 a) (y - max 0 b)) (min (max 0 a) (y - min 0 b)) := by
    ext t
    simp [S, Set.mem_Icc, and_assoc, and_left_comm, and_comm]
  rw [hS, Real.volume_Icc, abs_inv, ← ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))]
  let w := min (max 0 a) (y - min 0 b) - max (min 0 a) (y - max 0 b)
  change ENNReal.ofReal (|a|⁻¹ * w) = ENNReal.ofReal (max 0 w / |a|)
  by_cases hz : 0 ≤ w
  · rw [max_eq_right hz, div_eq_mul_inv, mul_comm]
  · rw [max_eq_left (le_of_not_ge hz), zero_div, ENNReal.ofReal_zero,
      ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (abs_nonneg _))
        (le_of_not_ge hz))]

/-- **Exercise 47**, Equation (201), of [benIsrael2003generalized], Chapter 8.
The projection of the independent uniform square has the four-absolute-value
density for any two nonzero coefficients. -/
theorem exercise_8_47 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsLebesgueProbabilityDensity
      (uniformSquareLaw.map fun x => a * x 0 + b * x 1)
      (fun y => ENNReal.ofReal ((|y - a - b| - |y - a| - |y - b| + |y|) / (2 * a * b))) := by
  let F : X₂ → ℝ≥0∞ := uniformSquare.indicator (fun _ => 1)
  let ξ : X₂ := WithLp.toLp 2 ![a, b]
  have hξ : ξ (Fin.last 1) ≠ 0 := hb
  let chart := linearImageGraphChart ξ hξ
  have hinner (x : X₂) : ⟪ξ, x⟫_ℝ = a * x 0 + b * x 1 := by
    simp [inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, ξ, mul_comm]
  have hd := imageDensity_graph (measurable_inner_normal ξ) chart uniformSquareLaw_density
  have hh (u : X₁) (y : ℝ) : chart.height (u, y) = (y - a * u 0) / b := by
    change radonHeight ξ y u = _
    have h : ⟪init ξ, u⟫_ℝ = a * u 0 := by
      simp [inner_eq_star_dotProduct, dotProduct, ξ, init, mul_comm]
    rw [radonHeight, h]
    rfl
  have hder (u : X₁) (y : ℝ) : |chart.heightDeriv (u, y)| = |b|⁻¹ := by
    change |b⁻¹| = _
    rw [abs_inv]
  have hD (y : ℝ) : graphImageDensity chart F y =
      ENNReal.ofReal ((|y - a - b| - |y - a| - |y - b| + |y|) / (2 * a * b)) := by
    let S : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ (y - a * t) / b ∈ Icc 0 1}
    have hS : MeasurableSet S := measurableSet_Icc.inter
      (measurableSet_Icc.preimage (by fun_prop))
    have hE (u : X₁) :
        F (snocLast u (chart.height (u, y))) = S.indicator (fun _ => 1) (euclideanOneCoordEquiv u) := by
      have he : snocLast u (chart.height (u, y)) ∈ uniformSquare ↔ euclideanOneCoordEquiv u ∈ S := by
        rw [hh, euclideanOneCoordEquiv_apply]
        change (∀ i : Fin 2, 0 ≤ snocLast u ((y - a * u 0) / b) i ∧
          snocLast u ((y - a * u 0) / b) i ≤ 1) ↔
          u 0 ∈ Icc (0 : ℝ) 1 ∧ (y - a * u 0) / b ∈ Icc 0 1
        rw [Fin.forall_fin_two]
        rfl
      by_cases h : euclideanOneCoordEquiv u ∈ S
      · rw [Set.indicator_of_mem h]
        exact Set.indicator_of_mem (he.mpr h) _
      · rw [Set.indicator_of_notMem h]
        exact Set.indicator_of_notMem (fun hh => h (he.mp hh)) _
    unfold graphImageDensity
    simp_rw [hder]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp_rw [hE]
    have htrans : (∫⁻ u : X₁, S.indicator (fun _ => (1 : ℝ≥0∞)) (euclideanOneCoordEquiv u)) =
        ∫⁻ t : ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) t :=
      measurePreserving_euclideanOneCoordEquiv.lintegral_comp (measurable_const.indicator hS)
    rw [htrans]
    change ENNReal.ofReal |b|⁻¹ * (∫⁻ t : ℝ, S.indicator 1 t) = _
    rw [lintegral_indicator_one hS, volume_uniform_fiber a b y ha hb,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg b))]
    congr 1
    rw [show |b|⁻¹ * (max 0 (min (max 0 a) (y - min 0 b) - max (min 0 a) (y - max 0 b)) / |a|) =
      max 0 (min (max 0 a) (y - min 0 b) - max (min 0 a) (y - max 0 b)) / (|a| * |b|) by ring,
      uniform_abs_formula a b y ha hb]
  rw [show (fun x : X₂ => a * x 0 + b * x 1) = (fun x => ⟪ξ, x⟫_ℝ) from funext fun x => (hinner x).symm]
  change IsLebesgueProbabilityDensity _ _
  rw [← funext hD]
  exact hd

/-- The sum of the two coordinates in **Exercise 47** has the symmetric triangular
density with support [0,2]. -/
theorem exercise_8_47_triangular :
    IsLebesgueProbabilityDensity (uniformSquareLaw.map (fun x => x 0 + x 1))
      (fun y => ENNReal.ofReal
        (if 0 ≤ y ∧ y < 1 then y else if 1 ≤ y ∧ y ≤ 2 then 2 - y else 0)) := by
  have h := exercise_8_47 1 1 one_ne_zero one_ne_zero
  simp only [one_mul] at h
  convert h using 1
  funext y
  congr 1
  by_cases h0 : 0 ≤ y
  · by_cases h1 : y < 1
    · simp only [ite_eq_left (show 0 ≤ y ∧ y < 1 from ⟨h0, h1⟩), abs_of_nonneg h0, abs_of_nonpos (by linarith : y - 1 ≤ 0),
        abs_of_nonpos (by linarith : y - 1 - 1 ≤ 0)]
      ring
    · by_cases h2 : y ≤ 2
      · simp only [ite_eq_right (fun hp : 0 ≤ y ∧ y < 1 => h1 hp.2), ite_eq_left (show 1 ≤ y ∧ y ≤ 2 from ⟨le_of_not_gt h1, h2⟩),
          abs_of_nonneg h0, abs_of_nonneg (by linarith : 0 ≤ y - 1), abs_of_nonpos (by linarith : y - 1 - 1 ≤ 0)]
        ring
      · simp only [ite_eq_right (fun hp : 0 ≤ y ∧ y < 1 => h1 hp.2), ite_eq_right (fun hp : 1 ≤ y ∧ y ≤ 2 => h2 hp.2),
          abs_of_nonneg h0, abs_of_nonneg (by linarith : 0 ≤ y - 1), abs_of_nonneg (by linarith : 0 ≤ y - 1 - 1)]
        ring
  · simp only [ite_eq_right (fun hp : 0 ≤ y ∧ y < 1 => h0 hp.1),
      ite_eq_right (fun hp : 1 ≤ y ∧ y ≤ 2 => h0 (zero_le_one.trans hp.1)),
      abs_of_nonpos (le_of_not_ge h0), abs_of_nonpos (by linarith : y - 1 ≤ 0),
      abs_of_nonpos (by linarith : y - 1 - 1 ≤ 0)]
    ring

end UniformProjection

section ExponentialMean

open EuclideanSpace ProbabilityTheory Matrix
open scoped Pointwise BigOperators InnerProductSpace

variable {d : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "Y" => EuclideanSpace ℝ (Fin (d + 1))

/-- The joint law of independent exponential coordinates with common rate. -/
def independentExponentialLaw (n : ℕ) (rate : ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (Measure.pi (fun _ : Fin n => expMeasure rate)).map (MeasurableEquiv.toLp 2 (Fin n → ℝ))

private theorem integrable_exponentialPDFReal' {rate : ℝ} (hRate : 0 < rate) :
    Integrable (exponentialPDFReal rate) := by
  refine ⟨(measurable_exponentialPDFReal rate).aestronglyMeasurable, ?_⟩
  change (∫⁻ x, ‖exponentialPDFReal rate x‖ₑ) < ⊤
  simp_rw [Real.enorm_eq_ofReal (exponentialPDFReal_nonneg hRate _)]
  exact (lintegral_exponentialPDF_eq_one hRate).trans_lt ENNReal.one_lt_top

private theorem independentExponential_pi_density (n : ℕ) {rate : ℝ} (hRate : 0 < rate) :
    IsLebesgueProbabilityDensity (Measure.pi (fun _ : Fin n => expMeasure rate))
      (fun x => ENNReal.ofReal (∏ i, exponentialPDFReal rate (x i))) := by
  have hm : Measurable (fun x : Fin n → ℝ => ∏ i, exponentialPDFReal rate (x i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_exponentialPDFReal rate).comp (measurable_pi_apply i))
  let : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hRate
  refine ⟨hm.ennreal_ofReal, Measure.pi_eq ?_, inferInstance⟩
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  have hm' : Integrable (fun x : Fin n → ℝ => ∏ i, exponentialPDFReal rate (x i))
      (volume.restrict (univ.pi S)) := by
    change Integrable _ ((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (univ.pi S))
    rw [Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun i => (integrable_exponentialPDFReal' hRate).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hm'
    (Filter.Eventually.of_forall fun _ => Finset.prod_nonneg fun _ _ => exponentialPDFReal_nonneg hRate _)]
  change ENNReal.ofReal (∫ x, (∏ i, exponentialPDFReal rate (x i))
    ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (univ.pi S)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => integral_nonneg (exponentialPDFReal_nonneg hRate)]
  apply Finset.prod_congr rfl
  intro i _
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_exponentialPDFReal' hRate).restrict
    (Filter.Eventually.of_forall (exponentialPDFReal_nonneg hRate))]
  unfold expMeasure gammaMeasure
  rw [withDensity_apply _ (hS i)]
  rfl

/-- The explicit joint density of the independent exponential law. -/
def independentExponentialDensity (n : ℕ) (rate : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  if ∀ i, 0 ≤ x i then ENNReal.ofReal (rate ^ n * Real.exp (-rate * ∑ i, x i)) else 0

/-- The joint density is the product of the exponential coordinate densities. -/
theorem independentExponentialLaw_density (n : ℕ) {rate : ℝ} (hRate : 0 < rate) :
    IsLebesgueProbabilityDensity (independentExponentialLaw n rate)
      (independentExponentialDensity n rate) := by
  have H := (independentExponential_pi_density n hRate).map_measurePreserving
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) (PiLp.volume_preserving_toLp (Fin n))
  change IsLebesgueProbabilityDensity (independentExponentialLaw n rate)
    (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (∏ i, exponentialPDFReal rate (x i))) at H
  convert H using 1
  funext x
  unfold independentExponentialDensity
  by_cases hx : ∀ i, 0 ≤ x i
  · rw [ite_eq_left hx]
    have he (i : Fin n) : exponentialPDFReal rate (x i) = rate * Real.exp (-(rate * x i)) := by
      simp [exponentialPDFReal, gammaPDFReal, hx i, Real.Gamma_one]
    simp only [he, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    rw [ite_eq_right (fun h => hi.not_ge (h i)),
      Finset.prod_eq_zero (Finset.mem_univ i) (show exponentialPDFReal rate (x i) = 0 from by
        simp [exponentialPDFReal, gammaPDFReal, hi.not_ge]), ENNReal.ofReal_zero]

private def simplexMeanParameters (t : ℝ) : Set X :=
  {u | (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ t}

private theorem simplexMeanParameters_measurable (t : ℝ) :
    MeasurableSet (simplexMeanParameters (d := d) t) := by
  have h : simplexMeanParameters (d := d) t =
      (⋂ i : Fin d, {u : X | 0 ≤ u i}) ∩ {u | ∑ i, u i ≤ t} := by
    ext u
    simp [simplexMeanParameters]
  rw [h]
  exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const (by fun_prop)).inter
    (measurableSet_le (by fun_prop) measurable_const)

private theorem simplexMeanParameters_volume (t : ℝ) (ht : 0 ≤ t) :
    (volume : Measure X) (simplexMeanParameters t) =
      ENNReal.ofReal (t ^ d * ((d.factorial : ℝ)⁻¹)) := by
  have h : simplexMeanParameters (d := d) t = t • unitInterceptSimplex d := by
    ext u
    change (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ t ↔ ∃ v ∈ unitInterceptSimplex d, t • v = u
    constructor
    · intro hu
      rcases eq_or_lt_of_le ht with hzero | hp
      · subst t
        have hcoord (i : Fin d) : u i = 0 := le_antisymm
          ((Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)).trans hu.2) (hu.1 i)
        exact ⟨0, by simp [unitInterceptSimplex], by ext i; simp [hcoord i]⟩
      · refine ⟨t⁻¹ • u, ⟨fun i => mul_nonneg (inv_nonneg.mpr ht) (hu.1 i), ?_⟩, ?_⟩
        · change ∑ i, t⁻¹ * u i ≤ 1
          rw [← Finset.mul_sum, ← div_eq_inv_mul, div_le_iff₀ hp, one_mul]
          exact hu.2
        · rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨fun i => mul_nonneg ht (hv.1 i), ?_⟩
      change ∑ i, t * v i ≤ t
      rw [← Finset.mul_sum]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.2 ht
  rw [h, Measure.addHaar_smul_of_nonneg volume ht, volume_unitInterceptSimplex,
    finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_mul (pow_nonneg ht _)]

/-- **Exercise 45**, Equation (198), of [benIsrael2003generalized], Chapter 8.
The mean of d+1 independent rate exponential variables has the stated
Gamma density, using a representative supported on the nonnegative ray. -/
theorem exercise_8_45 (d : ℕ) {rate : ℝ} (hRate : 0 < rate) :
    let n : ℝ := d + 1
    IsLebesgueProbabilityDensity ((independentExponentialLaw (d + 1) rate).map
      fun x => (∑ i : Fin (d + 1), x i) / n)
      (fun y => if 0 ≤ y then
        ENNReal.ofReal ((rate * n) ^ (d + 1) * y ^ d * Real.exp (-(rate * n * y)) / d.factorial)
        else 0) := by
  dsimp only
  let n : ℝ := d + 1
  let ξ : EuclideanSpace ℝ (Fin (d + 1)) := WithLp.toLp 2 (fun _ => n⁻¹)
  have hn : 0 < n := by dsimp [n]; positivity
  have hξ : ξ (Fin.last d) ≠ 0 := inv_ne_zero hn.ne'
  have hmean (x : EuclideanSpace ℝ (Fin (d + 1))) : ⟪ξ, x⟫_ℝ = (∑ i, x i) / n := by
    simp only [inner_eq_star_dotProduct, star_trivial, dotProduct, ξ, ← Finset.sum_mul,
      div_eq_mul_inv]
  let chart := linearImageGraphChart ξ hξ
  have hdensity := imageDensity_graph (measurable_inner_normal ξ) chart
    (independentExponentialLaw_density (d + 1) hRate)
  have hh (u : EuclideanSpace ℝ (Fin d)) (y : ℝ) : chart.height (u, y) = n * y - ∑ i, u i := by
    change radonHeight ξ y u = _
    have hinner : ⟪init ξ, u⟫_ℝ = (∑ i, u i) * n⁻¹ := by
      simp only [inner_eq_star_dotProduct, star_trivial, dotProduct]
      change (∑ i : Fin d, u i * n⁻¹) = (∑ i, u i) * n⁻¹
      rw [Finset.sum_mul]
    rw [radonHeight, hinner]
    change (y - (∑ i, u i) * n⁻¹) / n⁻¹ = _
    field_simp [hn.ne']
  have hderiv (u : EuclideanSpace ℝ (Fin d)) (y : ℝ) : |chart.heightDeriv (u, y)| = n := by
    change |(n⁻¹)⁻¹| = n
    rw [inv_inv, abs_of_pos hn]
  have hD (y : ℝ) : graphImageDensity chart (independentExponentialDensity (d + 1) rate) y =
      if 0 ≤ y then ENNReal.ofReal ((rate * n) ^ (d + 1) * y ^ d *
        Real.exp (-(rate * n * y)) / d.factorial) else 0 := by
    let M := ENNReal.ofReal (n * (rate ^ (d + 1) * Real.exp (-(rate * n * y))))
    let S := simplexMeanParameters (d := d) (n * y)
    have he (u : EuclideanSpace ℝ (Fin d)) :
        ENNReal.ofReal |chart.heightDeriv (u, y)| *
          independentExponentialDensity (d + 1) rate (snocLast u (chart.height (u, y))) =
          S.indicator (fun _ => M) u := by
      rw [hderiv, hh, independentExponentialDensity]
      have hS : (∀ i, 0 ≤ snocLast u (n * y - ∑ i, u i) i) ↔ u ∈ S := by
        simp only [Fin.forall_fin_succ', snocLast_apply_castSucc, snocLast_apply_last, sub_nonneg]
        rfl
      have hsum : (∑ i, snocLast u (n * y - ∑ i, u i) i) = n * y := by
        rw [Fin.sum_univ_castSucc]
        simp only [snocLast_apply_castSucc, snocLast_apply_last]
        ring
      rw [hsum]
      by_cases hu : u ∈ S
      · rw [ite_eq_left (hS.mpr hu), Set.indicator_of_mem hu, ← ENNReal.ofReal_mul hn.le]
        congr 2
        ring
      · simp only [ite_eq_right (fun h => hu (hS.mp h)), Set.indicator_of_notMem hu, mul_zero]
    unfold graphImageDensity
    simp_rw [he]
    rw [lintegral_indicator (simplexMeanParameters_measurable _), setLIntegral_const]
    by_cases hy : 0 ≤ y
    · rw [ite_eq_left hy, simplexMeanParameters_volume _ (mul_nonneg hn.le hy)]
      change ENNReal.ofReal (n * (rate ^ (d + 1) * Real.exp (-(rate * n * y)))) *
        ENNReal.ofReal ((n * y) ^ d * ((d.factorial : ℝ)⁻¹)) = _
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_pow, mul_pow, pow_succ n]
      ring
    · rw [ite_eq_right hy]
      have hz : S = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro u ⟨hu, hSum⟩
        exact (mul_neg_of_pos_of_neg hn (lt_of_not_ge hy)).not_ge
          ((Finset.sum_nonneg fun i _ => hu i).trans hSum)
      change M * (volume : Measure (EuclideanSpace ℝ (Fin d))) S = 0
      rw [hz, measure_empty, mul_zero]
  rw [show (fun x : EuclideanSpace ℝ (Fin (d + 1)) => (∑ i, x i) / (↑d + 1)) = (fun x => ⟪ξ, x⟫_ℝ) from
    funext fun x => (hmean x).symm]
  rw [← funext hD]
  exact hdensity

end ExponentialMean

section ExponentialSimplexFace

open EuclideanSpace

/-- **Exercise 45**, Equation (198), of [benIsrael2003generalized], Chapter 8.
The nonnegative sum-level set is a scaled simplex facet, with the
normalized Hausdorff area used in the density computation. -/
theorem exercise_8_45_simplex_face_area (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (euclideanHausdorffMeasure d (d + 1)).real
      {x : EuclideanSpace ℝ (Fin (d + 1)) | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = t} =
      Real.sqrt ((d : ℝ) + 1) * t ^ d / d.factorial := by
  let Y := EuclideanSpace ℝ (Fin (d + 1))
  let a : Y := WithLp.toLp 2 fun _ => 1
  have h (s : ℝ) : interceptSimplexUpperFacet a s = {x : Y | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = s} := by
    ext x
    change ((∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i = s) ↔ ((∀ i, 0 ≤ x i) ∧ ∑ i, x i = s)
    simp [a]
  have hS : interceptSimplexUpperFacet a t =
      (fun x : Y => t • x) '' interceptSimplexUpperFacet a 1 := by
    rw [h, h]
    ext x
    constructor
    · rintro ⟨hx, hsum⟩
      refine ⟨t⁻¹ • x, ⟨fun i => mul_nonneg (inv_nonneg.mpr ht.le) (hx i), ?_⟩, ?_⟩
      · change (∑ i, t⁻¹ * x i) = 1
        rw [← Finset.mul_sum, hsum, inv_mul_cancel₀ ht.ne']
      · change t • (t⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    · rintro ⟨x, ⟨hx, hsum⟩, rfl⟩
      refine ⟨fun i => mul_nonneg ht.le (hx i), ?_⟩
      change (∑ i, t * x i) = t
      rw [← Finset.mul_sum, hsum, mul_one]
  rw [← h, hS]
  change (euclideanHausdorffMeasure d (d + 1)
    ((fun x : Y => t • x) '' interceptSimplexUpperFacet a 1)).toReal = _
  rw [normalizedHausdorff_image_radius t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
  rw [show ((euclideanHausdorffMeasure d (d + 1)) (interceptSimplexUpperFacet a 1)).toReal =
    Real.sqrt ((d : ℝ) + 1) / (d.factorial : ℝ) from (exercise_38_simplex_facet_areas d).2]
  ring

end ExponentialSimplexFace

section BivariateNormal

open EuclideanSpace ProbabilityTheory Matrix
open scoped InnerProductSpace BigOperators NNReal ProbabilityTheory

/-- The density in Equation (199) for centered unit-variance coordinates. -/
def bivariateNormalDensity (ρ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi * Real.sqrt (1 - ρ ^ 2))⁻¹ *
    Real.exp (-(x 0 ^ 2 - 2 * ρ * x 0 * x 1 + x 1 ^ 2) / (2 * (1 - ρ ^ 2))))

private theorem independentStandardNormalLaw_map_inner {d : ℕ}
    (ξ : EuclideanSpace ℝ (Fin (d + 1))) (hξ : ξ ≠ 0) :
    (independentStandardNormalLaw (d + 1)).map (fun x => ⟪ξ, x⟫_ℝ) =
      gaussianReal 0 (⟨‖ξ‖ ^ 2, sq_nonneg _⟩ : ℝ≥0) := by
  let R := radonFrame ξ
  let μ := independentStandardNormalLaw (d + 1)
  have hf := independentStandardNormalLaw_density (d + 1)
  change IsLebesgueProbabilityDensity μ _ at hf
  have hR := hf.map_measurePreserving R.toMeasurableEquiv R.measurePreserving
  have hμ : μ.map R = μ := by
    change μ.map R.toMeasurableEquiv = μ
    rw [hR.eq_withDensity, hf.eq_withDensity]
    congr 1
    funext x
    change ENNReal.ofReal ((2 * Real.pi) ^ (-((↑(d + 1) : ℝ)) / 2) *
      Real.exp (-(‖R.symm x‖ ^ 2) / 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-((↑(d + 1) : ℝ)) / 2) *
      Real.exp (-(‖x‖ ^ 2) / 2))
    rw [R.symm.norm_map]
  have hinner (x : EuclideanSpace ℝ (Fin (d + 1))) :
      ⟪R ξ, x⟫_ℝ = ‖ξ‖ * x (Fin.last d) := by
    rw [show R ξ = snocLast 0 ‖ξ‖ from radonFrame_normal ξ hξ]
    simp [inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hcoord : μ.map (fun x => x (Fin.last d)) = gaussianReal 0 1 := by
    change ((Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)).map
      (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ))).map
      (fun x : EuclideanSpace ℝ (Fin (d + 1)) => x (Fin.last d)) = _
    rw [Measure.map_map (by fun_prop) (MeasurableEquiv.toLp 2 _).measurable]
    exact (measurePreserving_eval (fun _ : Fin (d + 1) => gaussianReal 0 1) (Fin.last d)).map_eq
  calc
    μ.map (fun x => ⟪ξ, x⟫_ℝ) = (μ.map R).map (fun x => ⟪R ξ, x⟫_ℝ) := by
      change _ = (μ.map R.toMeasurableEquiv).map (fun x => ⟪R ξ, x⟫_ℝ)
      rw [Measure.map_map (measurable_inner_normal _) R.toMeasurableEquiv.measurable]
      congr 1
      exact funext fun x => (R.inner_map_map ξ x).symm
    _ = (μ.map (fun x => x (Fin.last d))).map (‖ξ‖ * ·) := by
      rw [hμ, show (fun x => ⟪R ξ, x⟫_ℝ) = _ from funext hinner, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [hcoord, gaussianReal_map_const_mul, mul_zero, mul_one]
      rfl

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

private def normalShearLinear (ρ s : ℝ) : E₂ →L[ℝ] E₂ :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (ρ • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) + s • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

private theorem normalShearLinear_apply (ρ s : ℝ) (x : E₂) :
    normalShearLinear ρ s x = WithLp.toLp 2 ![x 0, ρ * x 0 + s * x 1] := by
  ext i
  fin_cases i <;> simp [normalShearLinear, PiLp.smul_apply]

private def normalShear (ρ s : ℝ) (hs : s ≠ 0) : E₂ ≃L[ℝ] E₂ :=
  (LinearEquiv.ofLinearMap (normalShearLinear ρ s).toLinearMap
    (normalShearLinear (-ρ/s) s⁻¹).toLinearMap
    (by
      ext x i
      fin_cases i
      · simp [normalShearLinear_apply]
      · simp [normalShearLinear_apply]
        field_simp [hs]
        ring)
    (by
      ext x i
      fin_cases i
      · simp [normalShearLinear_apply]
      · simp [normalShearLinear_apply]
        field_simp [hs]
        ring)).toContinuousLinearEquiv

private theorem normalShear_apply (ρ s : ℝ) (hs : s ≠ 0) (x : E₂) :
    normalShear ρ s hs x = WithLp.toLp 2 ![x 0, ρ * x 0 + s * x 1] :=
  normalShearLinear_apply _ _ _

private theorem normalShear_symm_apply (ρ s : ℝ) (hs : s ≠ 0) (x : E₂) :
    (normalShear ρ s hs).symm x = WithLp.toLp 2 ![x 0, (-ρ / s) * x 0 + s⁻¹ * x 1] :=
  normalShearLinear_apply _ _ _

private theorem normalShear_symm_det (ρ s : ℝ) (hs : s ≠ 0) :
    (normalShear ρ s hs).symm.toContinuousLinearMap.det = s⁻¹ := by
  have hm : stdMatrix ((normalShear ρ s hs).symm.toContinuousLinearMap) =
      !![1, 0; -ρ / s, s⁻¹] := by
    ext i j
    rw [stdMatrix_apply]
    change (normalShear ρ s hs).symm (EuclideanSpace.single j 1) i = _
    rw [normalShear_symm_apply]
    fin_cases i <;> fin_cases j <;> simp
  change LinearMap.det (normalShear ρ s hs).symm.toContinuousLinearMap.toLinearMap = _
  rw [← det_stdMatrix, hm, Matrix.det_fin_two]
  simp

private theorem bivariateNormal_complement_pos {ρ : ℝ} (hρ : |ρ| < 1) : 0 < 1 - ρ ^ 2 := by
  have h : ρ ^ 2 < (1 : ℝ) ^ 2 := sq_lt_sq.mpr (by simpa only [abs_one] using hρ)
  nlinarith

private theorem normalShear_map_density {ρ : ℝ} (hρ : |ρ| < 1) :
    let s := Real.sqrt (1 - ρ ^ 2)
    let hs : s ≠ 0 := (Real.sqrt_pos.mpr (bivariateNormal_complement_pos hρ)).ne'
    IsLebesgueProbabilityDensity ((independentStandardNormalLaw 2).map (normalShear ρ s hs))
      (bivariateNormalDensity ρ) := by
  dsimp only
  let s := Real.sqrt (1 - ρ ^ 2)
  have hρ' : 0 < 1 - ρ ^ 2 := bivariateNormal_complement_pos hρ
  have hs : 0 < s := Real.sqrt_pos.mpr hρ'
  have hss : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hρ'.le
  let T := normalShear ρ s hs.ne'
  change IsLebesgueProbabilityDensity ((independentStandardNormalLaw 2).map T) _
  let f : E₂ → ℝ≥0∞ := fun z => ENNReal.ofReal ((2 * Real.pi) ^ (-(2 : ℝ) / 2) *
    Real.exp (-(‖z‖ ^ 2) / 2))
  have hf := independentStandardNormalLaw_density 2
  change IsLebesgueProbabilityDensity (independentStandardNormalLaw 2) f at hf
  refine ⟨by unfold bivariateNormalDensity; fun_prop, ?_,
    (Measure.isProbabilityMeasure_map_iff T.continuous.measurable.aemeasurable).mpr hf.isProbabilityMeasure⟩
  ext U hU
  rw [Measure.map_apply T.continuous.measurable hU, hf.eq_withDensity]
  have hpre : T ⁻¹' U = T.symm '' U := by
    ext z
    constructor
    · intro hz
      exact ⟨T z, hz, T.symm_apply_apply z⟩
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, T.apply_symm_apply] using hx
  rw [withDensity_apply _ (T.continuous.measurable hU), withDensity_apply _ hU, hpre,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU
      (fun _ _ => T.symm.hasFDerivAt.hasFDerivWithinAt) T.symm.injective.injOn]
  apply lintegral_congr
  intro x
  rw [show T.symm.toContinuousLinearMap.det = s⁻¹ from normalShear_symm_det ρ s hs.ne',
    abs_of_pos (inv_pos.mpr hs), ← ENNReal.ofReal_mul (inv_nonneg.mpr hs.le)]
  unfold bivariateNormalDensity
  change _ = ENNReal.ofReal ((2 * Real.pi * s)⁻¹ * _)
  congr 1
  have hpow : (2 * Real.pi : ℝ) ^ (-(2 : ℝ) / 2) = (2 * Real.pi)⁻¹ := by
    rw [show (-(2 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  have hnorm : -(‖T.symm x‖ ^ 2) / 2 =
      -(x 0 ^ 2 - 2 * ρ * x 0 * x 1 + x 1 ^ 2) / (2 * (1 - ρ ^ 2)) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, show T.symm x = _ from
      normalShear_symm_apply ρ s hs.ne' x]
    change -(x 0 ^ 2 + ((-ρ / s) * x 0 + s⁻¹ * x 1) ^ 2) / 2 = _
    rw [← hss]
    field_simp [hs.ne']
    linear_combination -(x 0 ^ 2) * hss
  rw [hpow, hnorm, mul_inv, ← mul_assoc]
  congr 1
  ring

/-- The centered, unit-variance bivariate normal law of Equation (199). -/
def bivariateNormalLaw (ρ : ℝ) : Measure E₂ := volume.withDensity (bivariateNormalDensity ρ)

/-- Equation (199) is a probability density whenever the correlation lies
strictly between minus one and one. -/
theorem bivariateNormalLaw_density {ρ : ℝ} (hρ : |ρ| < 1) :
    IsLebesgueProbabilityDensity (bivariateNormalLaw ρ) (bivariateNormalDensity ρ) := by
  have h := normalShear_map_density hρ
  refine ⟨h.measurable, rfl, ?_⟩
  unfold bivariateNormalLaw
  rw [← h.eq_withDensity]
  exact h.isProbabilityMeasure

/-- The variance of the linear projection of two centered unit-variance
coordinates with correlation ρ. -/
def bivariateNormalProjectionVariance (ρ a b : ℝ) : ℝ := a ^ 2 + 2 * a * b * ρ + b ^ 2

/-- **Exercise 46**, Equations (199)–(200), of [benIsrael2003generalized],
Chapter 8. A nonzero real linear projection of the bivariate normal has the
stated centered Gaussian law, mean, variance, and explicit density. -/
theorem exercise_8_46 {ρ a b : ℝ} (hρ : |ρ| < 1) (hab : a ≠ 0 ∨ b ≠ 0)
    {μ : Measure E₂} (hμ : IsLebesgueProbabilityDensity μ (bivariateNormalDensity ρ)) :
    ∃ v : ℝ≥0, (v : ℝ) = bivariateNormalProjectionVariance ρ a b ∧ 0 < v ∧
      let ν := μ.map (fun x => a * x 0 + b * x 1)
      ν = gaussianReal 0 v ∧
        (∫ y, y ∂ν) = 0 ∧ Var[fun y ↦ y; ν] = v ∧
        IsLebesgueProbabilityDensity ν
          (fun y => ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ *
            Real.exp (-y ^ 2 / (2 * v)))) := by
  let s := Real.sqrt (1 - ρ ^ 2)
  have hρ' : 0 < 1 - ρ ^ 2 := bivariateNormal_complement_pos hρ
  have hs : 0 < s := Real.sqrt_pos.mpr hρ'
  have hss : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hρ'.le
  let T := normalShear ρ s hs.ne'
  have hT := normalShear_map_density hρ
  change IsLebesgueProbabilityDensity ((independentStandardNormalLaw 2).map T) _ at hT
  have hμeq : μ = (independentStandardNormalLaw 2).map T :=
    hμ.eq_withDensity.trans hT.eq_withDensity.symm
  let ξ : E₂ := WithLp.toLp 2 ![a + ρ * b, b * s]
  have hξ : ξ ≠ 0 := by
    intro h
    have h1 := congrArg (fun x : E₂ => x 1) h
    change b * s = 0 at h1
    have hb := (mul_eq_zero.mp h1).resolve_right hs.ne'
    have h0 := congrArg (fun x : E₂ => x 0) h
    change a + ρ * b = 0 at h0
    rw [hb, mul_zero, add_zero] at h0
    exact hab.elim (fun h => h h0) (fun h => h hb)
  let v : ℝ≥0 := ⟨‖ξ‖ ^ 2, sq_nonneg _⟩
  have hv : 0 < v := by
    change 0 < ‖ξ‖ ^ 2
    exact pow_pos (norm_pos_iff.mpr hξ) _
  refine ⟨v, ?_, hv, ?_⟩
  · change ‖ξ‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (a + ρ * b) ^ 2 + (b * s) ^ 2 = a ^ 2 + 2 * a * b * ρ + b ^ 2
    linear_combination b ^ 2 * hss
  have hproj (z : E₂) : a * T z 0 + b * T z 1 = ⟪ξ, z⟫_ℝ := by
    rw [show T z = _ from normalShear_apply ρ s hs.ne' z]
    simp [inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, ξ]
    ring
  have hGaussian : μ.map (fun x => a * x 0 + b * x 1) = gaussianReal 0 v := by
    rw [hμeq, Measure.map_map (by fun_prop) T.continuous.measurable]
    change (independentStandardNormalLaw 2).map (fun z => a * T z 0 + b * T z 1) = _
    rw [funext hproj]
    exact independentStandardNormalLaw_map_inner ξ hξ
  dsimp only
  rw [hGaussian]
  refine ⟨rfl, integral_id_gaussianReal, variance_fun_id_gaussianReal, ?_⟩
  have he : gaussianPDF 0 v = fun y => ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.exp (-y ^ 2 / (2 * v))) := by
    rw [gaussianPDF_def, gaussianPDFReal_def]
    simp only [sub_zero]
  rw [← he]
  exact ⟨measurable_gaussianPDF _ _, gaussianReal_of_var_ne_zero _ hv.ne', inferInstance⟩


/-- The sum and difference in **Exercise 46** are centered Gaussians with
variances (2(1+ρ)) and (2(1−ρ)), respectively. -/
theorem exercise_8_46_sum_sub {ρ : ℝ} (hρ : |ρ| < 1)
    {μ : Measure E₂} (hμ : IsLebesgueProbabilityDensity μ (bivariateNormalDensity ρ)) :
    let vp : ℝ≥0 := ⟨2 * (1 + ρ), by linarith [(abs_lt.mp hρ).1]⟩
    let vm : ℝ≥0 := ⟨2 * (1 - ρ), by linarith [(abs_lt.mp hρ).2]⟩
    μ.map (fun x => x 0 + x 1) = gaussianReal 0 vp ∧
      μ.map (fun x => x 0 - x 1) = gaussianReal 0 vm := by
  dsimp only
  obtain ⟨vp, hvp, _, hp, _, _, _⟩ := exercise_8_46 (a := 1) (b := 1) hρ (Or.inl one_ne_zero) hμ
  obtain ⟨vm, hvm, _, hm, _, _, _⟩ := exercise_8_46 (a := 1) (b := -1) hρ (Or.inl one_ne_zero) hμ
  have hp' : vp = ⟨2 * (1 + ρ), by linarith [(abs_lt.mp hρ).1]⟩ := by
    apply NNReal.eq
    change (vp : ℝ) = 2 * (1 + ρ)
    rw [hvp]
    dsimp [bivariateNormalProjectionVariance]
    ring
  have hm' : vm = ⟨2 * (1 - ρ), by linarith [(abs_lt.mp hρ).2]⟩ := by
    apply NNReal.eq
    change (vm : ℝ) = 2 * (1 - ρ)
    rw [hvm]
    dsimp [bivariateNormalProjectionVariance]
    ring
  exact ⟨by simpa only [one_mul, hp'] using hp, by simpa only [one_mul, neg_one_mul, sub_eq_add_neg, hm'] using hm⟩

end BivariateNormal

section UniformProjectionMarginals

open EuclideanSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

private def unitIntervalUniformLaw : Measure ℝ := volume.restrict (Icc 0 1)

private theorem unitIntervalUniformLaw_probability : IsProbabilityMeasure unitIntervalUniformLaw := by
  constructor
  simp [unitIntervalUniformLaw, Real.volume_Icc]

/-- The joint law in **Exercise 47** is the product of two independent
unit-interval uniform laws, expressed in Euclidean coordinates. -/
theorem uniformSquareLaw_eq_product :
    uniformSquareLaw =
      (Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Icc 0 1))).map
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) := by
  let e := MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
  have he : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp (Fin 2)
  change uniformSquareLaw = (Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Icc 0 1))).map e
  rw [← Measure.restrict_pi_pi, Set.pi_univ_Icc]
  ext S hS
  rw [uniformSquareLaw, Measure.restrict_apply hS, Measure.map_apply e.measurable hS,
    Measure.restrict_apply (e.measurable hS)]
  have hs : e ⁻¹' uniformSquare = Icc (0 : Fin 2 → ℝ) 1 := by
    ext x
    change (∀ i, 0 ≤ x i ∧ x i ≤ 1) ↔ _
    simp only [Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    exact forall_and
  change volume (S ∩ uniformSquare) = volume (e ⁻¹' S ∩ Icc (0 : Fin 2 → ℝ) 1)
  rw [← hs, ← Set.preimage_inter]
  exact (he.measure_preimage (hS.inter measurableSet_uniformSquare).nullMeasurableSet).symm

private theorem uniformSquareLaw_map_coord (i : Fin 2) :
    uniformSquareLaw.map (fun x => x i) = unitIntervalUniformLaw := by
  let := unitIntervalUniformLaw_probability
  rw [uniformSquareLaw_eq_product, Measure.map_map (by fun_prop) (MeasurableEquiv.toLp 2 _).measurable]
  exact (measurePreserving_eval (fun _ : Fin 2 => unitIntervalUniformLaw) i).map_eq

/-- With exactly one nonzero coefficient, **Exercise 47** reduces to the
uniform density on the interval between zero and that coefficient. -/
theorem exercise_8_47_single (i : Fin 2) {c : ℝ} (hc : c ≠ 0) :
    IsLebesgueProbabilityDensity ((uniformSquareLaw : Measure E₂).map fun x => c * x i)
      ((Icc (min 0 c) (max 0 c)).indicator fun _ => ENNReal.ofReal |c|⁻¹) := by
  rw [show (fun x : E₂ => c * x i) = (c * ·) ∘ (fun x : E₂ => x i) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), uniformSquareLaw_map_coord]
  let := unitIntervalUniformLaw_probability
  refine ⟨measurable_const.indicator measurableSet_Icc, ?_,
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance⟩
  ext S hS
  rw [unitIntervalUniformLaw, Measure.map_apply (by fun_prop) hS,
    Measure.restrict_apply (hS.preimage (by fun_prop)), withDensity_apply _ hS,
    lintegral_indicator measurableSet_Icc, setLIntegral_const, Measure.restrict_apply measurableSet_Icc]
  have h : (fun x : ℝ => c * x) ⁻¹' Icc (min 0 c) (max 0 c) = Icc (0 : ℝ) 1 := by
    ext x
    exact (scaled_unit_interval_iff hc).symm
  rw [← h, ← Set.preimage_inter, Real.volume_preimage_mul_left hc, abs_inv, Set.inter_comm]


/-- If both coefficients vanish, the projected law is the point mass at zero. -/
theorem exercise_8_47_zero :
    (uniformSquareLaw : Measure E₂).map (fun _ => (0 : ℝ)) = Measure.dirac 0 := by
  rw [Measure.map_const, uniformSquareLaw, Measure.restrict_apply_univ, volume_uniformSquare, one_smul]

end UniformProjectionMarginals

end BenIsraelGreville.Chapter08
