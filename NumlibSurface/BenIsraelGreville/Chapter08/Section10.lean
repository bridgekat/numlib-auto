/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter08.Section09
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Pi
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

end BenIsraelGreville.Chapter08
