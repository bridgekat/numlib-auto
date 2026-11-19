/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import NumlibSurface.BenIsraelGreville.Chapter08.Section05
import NumlibSurface.BenIsraelGreville.Chapter00.Section05
import Numlib.Analysis.Sobolev.Boundary.GraphMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Matrix volume and change of variables

Section 8.9 of [benIsrael2003generalized] uses matrix volume to generalize the
Jacobian factor for changes of variables. The graph formulas use the local
surface measure constructed by weighting parameter Lebesgue measure.

## Deviations from the source

* The full-column-rank hypothesis in (124) requires the parameter dimension
  to be at most the ambient dimension.
* The geometric area formula for general embeddings and the Hausdorff
  identification for curved graph pieces are open. For affine hyperplanes
  the normalized Hausdorff measure identification is proved by isometry.
* The cylindrical and spherical exercise calculations establish the
  Jacobian factors. The geometric surface integrals require the area formula.
  In (159b), the radius that would multiply the pulled-back integrand is
  already present in the Jacobian factor. The comparison with the matrix volume
from Chapter 0 uses positive parameter dimension because that definition
assigns zero volume to the rank-zero matrix.
-/

noncomputable section

namespace BenIsraelGreville.Chapter08

open Filter Matrix MeasureTheory Set
open scoped ENNReal NNReal Matrix InnerProductSpace

variable {m n d : ℕ}

/-- **Equation (123)** of [benIsrael2003generalized], Chapter 8.
The Jacobian matrix is the coordinate matrix of the Fréchet derivative. -/
abbrev jacobian (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin m) (Fin n) ℝ :=
  jacobianMatrix f x

/-- **Equation (122)** of [benIsrael2003generalized], Chapter 8.
An injective differentiable change of variables multiplies the integrand
by the absolute determinant of its Jacobian. -/
theorem integral_changeVariables
    {φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    (hφ : ∀ u ∈ U, DifferentiableAt ℝ φ u) (hinj : InjOn φ U)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ v in φ '' U, f v = ∫ u in U, f (φ u) * |(jacobian φ u).det| := by
  convert integral_image_eq_integral_abs_det_fderiv_smul volume hU
    (fun u hu => (hφ u hu).hasFDerivAt.hasFDerivWithinAt) hinj f using 2
  funext u
  rw [smul_eq_mul, mul_comm]
  congr 2
  exact EuclideanSpace.det_stdMatrix _

/-- **Equation (125)** of [benIsrael2003generalized], Chapter 8.
The volume of a positive full-column-rank matrix is the square root of
the determinant of its column Gram matrix. -/
theorem matrixVolume_eq_sqrt_gramDet (A : Matrix (Fin m) (Fin n) ℝ)
    (hr : A.rank = n) (hn : n ≠ 0) :
    Chapter00.matrixVolume A = Real.sqrt ((Aᵀ * A).det) := by
  have h := Chapter00.matrixVolume_sq_eq_det_transpose_mul A hr hn
  have hA : 0 ≤ Chapter00.matrixVolume A := by
    unfold Chapter00.matrixVolume
    split <;> positivity
  rw [← h, Real.sqrt_sq hA]

/-- In the positive-dimensional square full-rank case, the volume is the
absolute determinant. -/
theorem matrixVolume_eq_abs_det (A : Matrix (Fin n) (Fin n) ℝ)
    (hr : A.rank = n) (hn : n ≠ 0) :
    Chapter00.matrixVolume A = |A.det| := by
  rw [matrixVolume_eq_sqrt_gramDet A hr hn, det_mul, det_transpose, ← pow_two,
    Real.sqrt_sq_eq_abs]

/-- The Gram factor of a derivative equals the volume of its rectangular
Jacobian when the latter has positive full column rank. -/
theorem gram_fderiv_eq_matrixVolume_jacobian
    (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin n)) (hr : (jacobian φ u).rank = n) (hn : n ≠ 0) :
    EuclideanSpace.gram (fderiv ℝ φ u) = Chapter00.matrixVolume (jacobian φ u) :=
  (matrixVolume_eq_sqrt_gramDet (jacobian φ u) hr hn).symm

/-- Hausdorff measure normalized to agree with Lebesgue measure on the
parameter space of the same dimension. -/
def euclideanHausdorffMeasure (d m : ℕ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (Measure.hausdorffMeasure
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ)) • Measure.hausdorffMeasure (d : ℝ)

/-- In its full dimension the normalized Hausdorff measure is Lebesgue measure. -/
theorem euclideanHausdorffMeasure_self (d : ℕ) :
    euclideanHausdorffMeasure d d = volume := by
  let μ : Measure (EuclideanSpace ℝ (Fin d)) :=
    Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ)
  have heq : (Measure.hausdorffMeasure (d : ℝ) : Measure (EuclideanSpace ℝ (Fin d))) = μ := by
    simp [μ]
  change Measure.addHaarScalarFactor volume μ • (Measure.hausdorffMeasure (d : ℝ)) = volume
  rw [heq]
  exact (Measure.isAddLeftInvariant_eq_smul volume μ).symm

section Graph

open EuclideanSpace

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-- **Equation (132)** of [benIsrael2003generalized], Chapter 8.
A differentiable scalar graph has the Gram Jacobian
`√(1 + ‖∇g‖²)`, in any rigid frame. -/
theorem gram_jacobian_graph (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {g : 𝔼' → ℝ}
    {u : 𝔼'} (hg : DifferentiableAt ℝ g u) :
    Real.sqrt (((jacobian (graphParam T g) u)ᵀ * jacobian (graphParam T g) u).det) =
      Real.sqrt (1 + ‖gradient g u‖ ^ 2) :=
  (graphDensity_eq_gram T hg).symm

/-- **Equations (130) and (133)** of [benIsrael2003generalized], Chapter 8.
Integration against the local graph measure reduces to weighted Lebesgue
integration over the parameter domain. -/
theorem integral_graph (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {g : 𝔼' → ℝ}
    (hg : ContDiff ℝ 1 g) (U : Set 𝔼') {f : 𝔼 → ℝ}
    (hf : AEStronglyMeasurable f (graphMeasure T g U)) :
    ∫ v, f v ∂(graphMeasure T g U) =
      ∫ u in U, f (graphParam T g u) * Real.sqrt (1 + ‖gradient g u‖ ^ 2) := by
  simpa only [graphDensity, smul_eq_mul, mul_comm] using integral_graphMeasure hg U hf

/-- **Equation (134)** of [benIsrael2003generalized], Chapter 8.
The graph measure of the whole parametrized piece is the integral of its
Gram density, including the case of infinite area. -/
theorem graph_area (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {g : 𝔼' → ℝ}
    (hg : ContDiff ℝ 1 g) (U : Set 𝔼') :
    graphMeasure T g U univ = ∫⁻ u in U, ENNReal.ofReal (Real.sqrt (1 + ‖gradient g u‖ ^ 2)) := by
  simpa only [lintegral_const, one_mul, mul_one, graphDensity] using
    lintegral_graphMeasure (T := T) hg U (fun _ => 1)

/-- Smooth graph charts with the same image define the same surface
measure, including charts with opposite choices of upward normal. -/
theorem graphMeasure_eq_of_range_eq
    {T₁ T₂ : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g₁ g₂ : 𝔼' → ℝ}
    (h₁ : ContDiff ℝ 1 g₁) (h₂ : ContDiff ℝ 1 g₂)
    (hV : range (graphParam T₁ g₁) = range (graphParam T₂ g₂)) :
    graphMeasure T₁ g₁ univ = graphMeasure T₂ g₂ univ := by
  let ψ := graphTransition T₁ g₁ T₂
  have hψ : ∀ u, graphParam T₂ g₂ (ψ u) = graphParam T₁ g₁ u := by
    intro u
    have hu : graphParam T₁ g₁ u ∈ range (graphParam T₂ g₂) := hV ▸ mem_range_self u
    obtain ⟨v, hv⟩ := hu
    have heq : ψ u = v := by
      rw [show ψ u = init (T₂ (graphParam T₁ g₁ u)) from rfl, ← hv, init_apply_graphParam]
    rw [heq, hv]
  have hbij : Function.Bijective ψ := by
    constructor
    · intro u v huv
      have he := congrArg (graphParam T₂ g₂) huv
      exact graphParam_injective ((hψ u).symm.trans (he.trans (hψ v)))
    · intro v
      have hv : graphParam T₂ g₂ v ∈ range (graphParam T₁ g₁) := hV.symm ▸ mem_range_self v
      obtain ⟨u, hu⟩ := hv
      exact ⟨u, graphParam_injective ((hψ u).trans hu)⟩
  have hd := (contDiff_graphTransition (T₁ := T₁) (T₂ := T₂) h₁).differentiable one_ne_zero
  have hden (u : 𝔼') :
      graphDensity g₁ u = graphDensity g₂ (ψ u) *
        |(fderiv ℝ ψ u).det| := by
    rw [graphDensity_eq_gram T₁ (h₁.differentiable one_ne_zero _),
      graphDensity_eq_gram T₂ (h₂.differentiable one_ne_zero _)]
    have heq : graphParam T₁ g₁ = graphParam T₂ g₂ ∘ ψ := funext fun v => (hψ v).symm
    have hc : fderiv ℝ (graphParam T₁ g₁) u =
        fderiv ℝ (graphParam T₂ g₂) (ψ u) ∘L fderiv ℝ ψ u := by
      rw [heq]
      exact fderiv_comp u ((contDiff_graphParam h₂).differentiable one_ne_zero _) (hd u)
    rw [hc, gram_comp]
  ext S hS
  simp only [graphMeasure_apply h₁.continuous _ hS, graphMeasure_apply h₂.continuous _ hS,
    univ_inter]
  have hpre : graphParam T₂ g₂ ⁻¹' S = ψ '' (graphParam T₁ g₁ ⁻¹' S) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, rfl⟩ := hbij.2 v
      refine ⟨u, ?_, rfl⟩
      change graphParam T₁ g₁ u ∈ S
      rwa [← hψ u]
    · rintro ⟨u, hu, rfl⟩
      change graphParam T₂ g₂ (ψ u) ∈ S
      rwa [hψ u]
  have hpreM := (continuous_graphParam (T := T₁) h₁.continuous).measurable hS
  rw [hpre, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpreM
    (fun u _ => (hd u).hasFDerivAt.hasFDerivWithinAt) hbij.1.injOn]
  exact setLIntegral_congr_fun hpreM fun u _ => by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm, ← hden]

end Graph

section Radon

open EuclideanSpace

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-- **Equation (136)** of [benIsrael2003generalized], Chapter 8.
The height of the hyperplane over the first coordinates. -/
def radonHeight (ξ : 𝔼) (p : ℝ) (u : 𝔼') : ℝ :=
  (p - ⟪init ξ, u⟫_ℝ) / ξ (Fin.last d)

/-- The nonvertical hyperplane is parametrized by inserting its height as
the last coordinate. -/
def radonChart (ξ : 𝔼) (p : ℝ) (u : 𝔼') : 𝔼 :=
  snocLast u (radonHeight ξ p u)

/-- The nonvertical chart takes its values in the specified hyperplane. -/
theorem inner_radonChart (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) (p : ℝ) (u : 𝔼') :
    ⟪ξ, radonChart ξ p u⟫_ℝ = p := by
  conv_lhs => rw [← snocLast_init_last ξ]
  rw [radonChart, inner_snocLast, radonHeight]
  simp only [init_snocLast, snocLast_apply_last]
  field_simp
  ring

/-- **Equation (135)** of [benIsrael2003generalized], Chapter 8.
The chart parametrizes exactly the hyperplane at level `p`. -/
theorem range_radonChart (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) (p : ℝ) :
    range (radonChart ξ p) = {x | ⟪ξ, x⟫_ℝ = p} := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact inner_radonChart ξ hξ p u
  · intro hx
    change ⟪ξ, x⟫_ℝ = p at hx
    rw [← snocLast_init_last ξ, ← snocLast_init_last x, inner_snocLast] at hx
    refine ⟨init x, ?_⟩
    rw [radonChart, radonHeight]
    have h : (p - ⟪init ξ, init x⟫_ℝ) / ξ (Fin.last d) = x (Fin.last d) := by
      rw [div_eq_iff hξ]
      linarith
    rw [h, snocLast_init_last]

private theorem contDiff_radonHeight (ξ : 𝔼) (p : ℝ) :
    ContDiff ℝ 1 (radonHeight ξ p) :=
  (contDiff_const.sub (innerSL ℝ (init ξ)).contDiff).div_const _

private theorem hasGradientAt_radonHeight (ξ : 𝔼) (p : ℝ) (u : 𝔼') :
    HasGradientAt (radonHeight ξ p) (-(ξ (Fin.last d))⁻¹ • init ξ) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((innerSL ℝ (init ξ)).hasFDerivAt (x := u)).const_sub p
  convert h.const_smul (ξ (Fin.last d))⁻¹ using 1
  · funext v
    exact div_eq_inv_mul _ _
  · ext v
    simp [InnerProductSpace.toDual_apply_apply]

/-- **Equation (137)** of [benIsrael2003generalized], Chapter 8.
The graph density on a nonvertical slice is constant. -/
theorem graphDensity_radonHeight (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) (p : ℝ) (u : 𝔼') :
    graphDensity (radonHeight ξ p) u = ‖ξ‖ / |ξ (Fin.last d)| := by
  have hsquare : ‖ξ‖ ^ 2 = ‖init ξ‖ ^ 2 + (ξ (Fin.last d)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    conv_lhs => rw [← snocLast_init_last ξ, inner_snocLast]
    ring
  rw [graphDensity, (hasGradientAt_radonHeight ξ p u).gradient, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_inv, ← Real.sqrt_sq (div_nonneg (norm_nonneg _) (abs_nonneg _))]
  congr 1
  rw [div_pow, hsquare, sq_abs]
  field_simp
  rw [sq_abs]
  ring

/-- **Equation (139)** of [benIsrael2003generalized], Chapter 8.
The nonvertical Radon transform in graph coordinates. -/
def radonTransform {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : 𝔼 → G) (ξ : 𝔼) (p : ℝ) : G :=
  (‖ξ‖ / |ξ (Fin.last d)|) • ∫ u, f (radonChart ξ p u)

/-- **Equation (138)** of [benIsrael2003generalized], Chapter 8.
The graph formula computes the integral with respect to the local surface
measure on the nonvertical hyperplane. -/
theorem radonTransform_eq_graphIntegral
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : 𝔼 → G) (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) (p : ℝ)
    (hf : AEStronglyMeasurable f
      (graphMeasure (AffineIsometryEquiv.refl ℝ 𝔼) (radonHeight ξ p) univ)) :
    radonTransform f ξ p =
      ∫ x, f x ∂(graphMeasure (AffineIsometryEquiv.refl ℝ 𝔼) (radonHeight ξ p) univ) := by
  rw [integral_graphMeasure (contDiff_radonHeight ξ p) univ hf]
  change radonTransform f ξ p =
    ∫ u in univ, graphDensity (radonHeight ξ p) u • f (radonChart ξ p u)
  simp [graphDensity_radonHeight ξ hξ, radonTransform, integral_smul]

private theorem measurePreserving_radonChart (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) :
    MeasurePreserving (fun z : 𝔼' × ℝ => radonChart ξ z.2 z.1)
      ((volume : Measure 𝔼').prod (volume : Measure ℝ))
      (ENNReal.ofReal |ξ (Fin.last d)| • (volume : Measure 𝔼)) := by
  let c := ENNReal.ofReal |ξ (Fin.last d)|
  have hskew : MeasurePreserving (fun z : 𝔼' × ℝ => (z.1, radonHeight ξ z.2 z.1))
      ((volume : Measure 𝔼').prod (volume : Measure ℝ))
      ((volume : Measure 𝔼').prod (c • (volume : Measure ℝ))) := by
    refine (MeasurePreserving.id (volume : Measure 𝔼')).skew_product
      (g := fun u p => radonHeight ξ p u) ?_ (Filter.Eventually.of_forall fun u => ?_)
    · change Measurable fun z : 𝔼' × ℝ =>
        (z.2 - innerSL ℝ (init ξ) z.1) / ξ (Fin.last d)
      fun_prop
    · let k := ⟪init ξ, u⟫_ℝ
      change Measure.map (fun p : ℝ => (p - k) / ξ (Fin.last d)) volume = _
      rw [show (fun p : ℝ => (p - k) / ξ (Fin.last d)) =
        (fun t : ℝ => (ξ (Fin.last d))⁻¹ • t) ∘ (fun p : ℝ => p - k)
        by ext p; simp [div_eq_mul_inv, mul_comm]]
      rw [← Measure.map_map (by fun_prop) (by fun_prop)]
      simp only [sub_eq_add_neg, map_add_right_eq_self]
      rw [Measure.map_addHaar_smul _ (inv_ne_zero hξ)]
      simp [c]
  have hs := (measurePreserving_lastInit d).symm (lastInitEquiv d)
  have h : MeasurePreserving (fun z : 𝔼' × ℝ => snocLast z.1 z.2)
      ((volume : Measure 𝔼').prod (volume : Measure ℝ)) volume :=
    hs.comp Measure.measurePreserving_swap
  have hscale : MeasurePreserving (fun z : 𝔼' × ℝ => snocLast z.1 z.2)
      (c • (volume : Measure 𝔼').prod (volume : Measure ℝ)) (c • volume) := by
    refine ⟨h.measurable, ?_⟩
    rw [Measure.map_smul _ h.measurable.aemeasurable, h.map_eq]
  rw [Measure.prod_smul_right] at hskew
  exact hscale.comp hskew

/-- **Equation (143)** of [benIsrael2003generalized], Chapter 8.
Splitting a Lebesgue integral by the level of a nonvertical linear
functional contributes the inverse absolute last coefficient. -/
theorem integral_eq_integral_radonChart {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (f : 𝔼 → G) (hf : Integrable f)
    (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) :
    ∫ x, f x = |ξ (Fin.last d)|⁻¹ • ∫ p, ∫ u, f (radonChart ξ p u) := by
  have h := measurePreserving_radonChart ξ hξ
  have hf' := hf.smul_measure (c := ENNReal.ofReal |ξ (Fin.last d)|) ENNReal.ofReal_ne_top
  have hI : (∫ z : 𝔼' × ℝ, f (radonChart ξ z.2 z.1)
        ∂((volume : Measure 𝔼').prod (volume : Measure ℝ))) =
      ∫ x, f x ∂(ENNReal.ofReal |ξ (Fin.last d)| • volume) := by
    rw [← h.map_eq, integral_map h.measurable.aemeasurable]
    rw [h.map_eq]
    exact hf'.aestronglyMeasurable
  have hF := integral_prod_symm (f ∘ fun z : 𝔼' × ℝ => radonChart ξ z.2 z.1)
    (h.integrable_comp_of_integrable hf')
  change (∫ z, (f ∘ fun z : 𝔼' × ℝ => radonChart ξ z.2 z.1) z
    ∂((volume : Measure 𝔼').prod (volume : Measure ℝ))) = _ at hI
  rw [hF, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at hI
  simp only [Function.comp_apply] at hI
  rw [hI, smul_smul, inv_mul_cancel₀ (abs_ne_zero.mpr hξ), one_smul]

/-- **Equation (142)** of [benIsrael2003generalized], Chapter 8.
A Lebesgue integral is the integral of the Radon slices weighted by the
inverse norm of the normal. -/
theorem integral_eq_integral_radonTransform {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (f : 𝔼 → G) (hf : Integrable f)
    (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) :
    ∫ x, f x = ‖ξ‖⁻¹ • ∫ p, radonTransform f ξ p := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr (fun h => hξ (by simp [h]))
  rw [integral_eq_integral_radonChart f hf ξ hξ]
  simp only [radonTransform, integral_smul, smul_smul]
  congr 1
  field_simp

open scoped InnerProductSpace

/-- An orthogonal frame that takes the normal direction to the last axis.
The reflection gives an explicit frame for every nonzero normal. -/
def radonFrame (ξ : 𝔼) : 𝔼 ≃ₗᵢ[ℝ] 𝔼 :=
  (ℝ ∙ (‖ξ‖⁻¹ • ξ - single (Fin.last d) 1))ᗮ.reflection

/-- In the orthogonal frame the nonzero normal points along the last coordinate. -/
theorem radonFrame_normal (ξ : 𝔼) (hξ : ξ ≠ 0) :
    radonFrame ξ ξ = snocLast 0 ‖ξ‖ := by
  have hn := norm_ne_zero_iff.mpr hξ
  have hunit : ‖‖ξ‖⁻¹ • ξ‖ = ‖(single (Fin.last d) 1 : 𝔼)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg ξ), inv_mul_cancel₀ hn]
    simp
  have hframe : radonFrame ξ (‖ξ‖⁻¹ • ξ) = single (Fin.last d) 1 :=
    Submodule.reflection_sub hunit
  rw [map_smul] at hframe
  calc
    radonFrame ξ ξ = ‖ξ‖ • (‖ξ‖⁻¹ • radonFrame ξ ξ) := by
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    _ = snocLast 0 ‖ξ‖ := by
      rw [hframe, ← snocLast_zero_one]
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [PiLp.smul_apply]

/-- Each level of a nonzero linear functional is an affine Euclidean
space of codimension one, parametrized with an isometric frame. -/
def radonNormalChart (ξ : 𝔼) (p : ℝ) (u : 𝔼') : 𝔼 :=
  (radonFrame ξ).symm (snocLast u (p / ‖ξ‖))

private theorem inner_radonFrame_symm (ξ : 𝔼) (hξ : ξ ≠ 0) (u : 𝔼') (t : ℝ) :
    ⟪ξ, (radonFrame ξ).symm (snocLast u t)⟫_ℝ = ‖ξ‖ * t := by
  rw [← (radonFrame ξ).inner_map_map, LinearIsometryEquiv.apply_symm_apply, radonFrame_normal ξ hξ,
    inner_snocLast, inner_zero_left, zero_add]

/-- In any nonzero normal direction the chart has the specified level. -/
theorem inner_radonNormalChart (ξ : 𝔼) (hξ : ξ ≠ 0) (p : ℝ) (u : 𝔼') :
    ⟪ξ, radonNormalChart ξ p u⟫_ℝ = p := by
  rw [radonNormalChart, inner_radonFrame_symm ξ hξ]
  field_simp [norm_ne_zero_iff.mpr hξ]

/-- The orthogonal chart covers the full affine hyperplane. -/
theorem range_radonNormalChart (ξ : 𝔼) (hξ : ξ ≠ 0) (p : ℝ) :
    range (radonNormalChart ξ p) = {x | ⟪ξ, x⟫_ℝ = p} := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact inner_radonNormalChart ξ hξ p u
  · intro hx
    change ⟪ξ, x⟫_ℝ = p at hx
    let y := radonFrame ξ x
    have hy : ⟪ξ, (radonFrame ξ).symm (snocLast (init y) (y (Fin.last d)))⟫_ℝ = p := by
      simpa only [snocLast_init_last, y, LinearIsometryEquiv.symm_apply_apply] using hx
    rw [inner_radonFrame_symm ξ hξ] at hy
    refine ⟨init y, ?_⟩
    rw [radonNormalChart, div_eq_iff (norm_ne_zero_iff.mpr hξ) |>.mpr (by linarith : p = _),
      snocLast_init_last]
    exact (radonFrame ξ).symm_apply_apply x

private theorem norm_snocLast_sq (u : 𝔼') (t : ℝ) :
    ‖snocLast u t‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_snocLast, pow_two]

/-- The orthogonal coordinates preserve distances along a hyperplane. -/
theorem isometry_radonNormalChart (ξ : 𝔼) (p : ℝ) :
    Isometry (radonNormalChart ξ p) := by
  refine (radonFrame ξ).symm.isometry.comp (Isometry.of_dist_eq fun u v => ?_)
  let t := p / ‖ξ‖
  change dist (snocLast u t) (snocLast v t) = dist u v
  have hsub : snocLast u t - snocLast v t = snocLast (u - v) 0 := by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [PiLp.sub_apply]
  simp only [dist_eq_norm, hsub]
  have h := norm_snocLast_sq (u - v) 0
  norm_num at h
  exact h

/-- The Radon transform over arbitrary hyperplanes with nonzero normal. -/
def radonTransformAll {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : 𝔼 → G) (ξ : 𝔼) (p : ℝ) : G :=
  ∫ u, f (radonNormalChart ξ p u)

/-- The orthogonal chart computes integration against the induced graph
measure on the slice. -/
theorem radonTransformAll_eq_graphIntegral
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : 𝔼 → G) (ξ : 𝔼) (p : ℝ) :
    radonTransformAll f ξ p =
      ∫ x, f x ∂(graphMeasure (radonFrame ξ).toAffineIsometryEquiv
        (fun _ => p / ‖ξ‖) univ) := by
  rw [graphMeasure, Measure.restrict_univ]
  have hden : (fun u : 𝔼' => ENNReal.ofReal (graphDensity (fun _ => p / ‖ξ‖) u)) = 1 := by
    funext u
    simp [graphDensity, gradient_fun_const]
  rw [hden, withDensity_one, (measurableEmbedding_graphParam continuous_const).integral_map]
  rfl

/-- **Equation (138)** of [benIsrael2003generalized], Chapter 8.
The Radon transform is integration against normalized Hausdorff measure
restricted to the hyperplane. -/
theorem radonTransformAll_eq_integral_hausdorff
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : 𝔼 → G) (ξ : 𝔼) (hξ : ξ ≠ 0) (p : ℝ) :
    radonTransformAll f ξ p = ∫ x in {x | ⟪ξ, x⟫_ℝ = p}, f x
      ∂(euclideanHausdorffMeasure d (d + 1)) := by
  have hi := isometry_radonNormalChart ξ p
  have hmap : Measure.map (radonNormalChart ξ p) volume =
      (euclideanHausdorffMeasure d (d + 1)).restrict {x | ⟪ξ, x⟫_ℝ = p} := by
    rw [← euclideanHausdorffMeasure_self d]
    unfold euclideanHausdorffMeasure
    rw [Measure.map_smul _ hi.continuous.measurable.aemeasurable,
      hi.map_hausdorffMeasure (Or.inl (by positivity)), range_radonNormalChart ξ hξ,
      Measure.restrict_smul]
  have hme : MeasurableEmbedding (radonNormalChart ξ p) :=
    measurableEmbedding_graphParam (T := (radonFrame ξ).toAffineIsometryEquiv)
      (g := fun _ => p / ‖ξ‖) continuous_const
  rw [← hmap, hme.integral_map]
  rfl

/-- Both coordinate formulas give the same slice integral when the last
coordinate of the normal is nonzero. -/
theorem radonTransformAll_eq_radonTransform
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : 𝔼 → G) (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) (p : ℝ)
    (hf : AEStronglyMeasurable f
      (graphMeasure (AffineIsometryEquiv.refl ℝ 𝔼) (radonHeight ξ p) univ)) :
    radonTransformAll f ξ p = radonTransform f ξ p := by
  have hξ' : ξ ≠ 0 := fun h => hξ (by simp [h])
  rw [radonTransformAll_eq_graphIntegral, radonTransform_eq_graphIntegral f ξ hξ p hf]
  have h : graphMeasure (radonFrame ξ).toAffineIsometryEquiv (fun _ => p / ‖ξ‖) univ =
      graphMeasure (AffineIsometryEquiv.refl ℝ 𝔼) (radonHeight ξ p) univ := by
    apply graphMeasure_eq_of_range_eq contDiff_const (contDiff_radonHeight ξ p)
    change range (radonNormalChart ξ p) = range (radonChart ξ p)
    rw [range_radonNormalChart ξ hξ', range_radonChart ξ hξ]
  rw [h]

/-- **Equations (141)–(142)** of [benIsrael2003generalized], Chapter 8.
The decomposition of a Lebesgue integral into parallel slices works for
every nonzero normal. -/
theorem integral_eq_integral_radonTransformAll
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f : 𝔼 → G) (hf : Integrable f) (ξ : 𝔼) (hξ : ξ ≠ 0) :
    ∫ x, f x = ‖ξ‖⁻¹ • ∫ p, radonTransformAll f ξ p := by
  let g := f ∘ (radonFrame ξ).symm
  have hg : Integrable g := (MeasureTheory.integrable_comp (radonFrame ξ).symm f).mpr hf
  have hn := norm_ne_zero_iff.mpr hξ
  have h := integral_eq_integral_radonChart g hg (snocLast 0 ‖ξ‖)
    (by simpa only [snocLast_apply_last] using hn)
  rw [← MeasureTheory.integral_comp (radonFrame ξ).symm f]
  change (∫ x, g x) = _
  simpa [radonChart, radonHeight, g, radonNormalChart, radonTransformAll,
    abs_of_nonneg (norm_nonneg ξ)] using h

end Radon

section Fourier

/-- **Equation (144)** of [benIsrael2003generalized], Chapter 8.
The symmetric Fourier transform uses angular frequency. -/
def symmetricFourier (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ •
    ∫ x, Complex.exp (-((⟪ξ, x⟫_ℝ : ℝ) : ℂ) * Complex.I) * f x

/-- **Equation (146)** of [benIsrael2003generalized], Chapter 8.
The inverse transform uses the same scale and the opposite sign. -/
def symmetricFourierInv (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ •
    ∫ ξ, Complex.exp (((⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I) * g ξ

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

private theorem integral_exp_mul_eq_radonTransform (f : 𝔼 → ℂ) (hf : Integrable f)
    (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) (s : ℝ) :
    ∫ x, Complex.exp (↑(s * ⟪ξ, x⟫_ℝ) * Complex.I) * f x =
      ‖ξ‖⁻¹ • ∫ p : ℝ, Complex.exp (↑(s * p) * Complex.I) * radonTransform f ξ p := by
  have hcont : Continuous fun x : 𝔼 => Complex.exp (↑(s * ⟪ξ, x⟫_ℝ) * Complex.I) := by
    change Continuous fun x : 𝔼 => Complex.exp (↑(s * innerSL ℝ ξ x) * Complex.I)
    fun_prop
  have hg : Integrable (fun x => Complex.exp (↑(s * ⟪ξ, x⟫_ℝ) * Complex.I) * f x) := by
    apply hf.mono (hcont.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simp [Complex.norm_exp, Complex.mul_re]
  rw [integral_eq_integral_radonTransform _ hg ξ hξ]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun p => ?_
  simp only [radonTransform, inner_radonChart ξ hξ]
  let c := Complex.exp (↑(s * p) * Complex.I)
  change (‖ξ‖ / |ξ (Fin.last d)|) • (∫ u, c • f (radonChart ξ p u)) =
    c • ((‖ξ‖ / |ξ (Fin.last d)|) • ∫ u, f (radonChart ξ p u))
  rw [integral_smul, smul_comm]

/-- **Equation (145)** of [benIsrael2003generalized], Chapter 8.
The Fourier integral is a one-dimensional Fourier integral of the
nonvertical Radon slices. -/
theorem fourierTransform_eq_radonTransform (f : 𝔼 → ℂ) (hf : Integrable f)
    (ξ : 𝔼) (hξ : ξ (Fin.last d) ≠ 0) :
    symmetricFourier f ξ =
      (((2 * Real.pi) ^ (((d + 1 : ℕ) : ℝ) / 2))⁻¹ / ‖ξ‖) •
        ∫ p : ℝ, Complex.exp (-(p : ℂ) * Complex.I) * radonTransform f ξ p := by
  unfold symmetricFourier
  simpa only [neg_one_mul, Complex.ofReal_neg, smul_smul, div_eq_mul_inv] using
    congrArg (((2 * Real.pi) ^ (((d + 1 : ℕ) : ℝ) / 2))⁻¹ • ·)
      (integral_exp_mul_eq_radonTransform f hf ξ hξ (-1))

/-- **Equation (146)** of [benIsrael2003generalized], Chapter 8.
The inverse Fourier integral has the corresponding Radon slice formula. -/
theorem fourierInv_eq_radonTransform (g : 𝔼 → ℂ) (hg : Integrable g)
    (x : 𝔼) (hx : x (Fin.last d) ≠ 0) :
    symmetricFourierInv g x =
      (((2 * Real.pi) ^ (((d + 1 : ℕ) : ℝ) / 2))⁻¹ / ‖x‖) •
        ∫ p : ℝ, Complex.exp ((p : ℂ) * Complex.I) * radonTransform g x p := by
  unfold symmetricFourierInv
  simpa only [one_mul, smul_smul, div_eq_mul_inv] using
    congrArg (((2 * Real.pi) ^ (((d + 1 : ℕ) : ℝ) / 2))⁻¹ • ·)
      (integral_exp_mul_eq_radonTransform g hg x hx 1)

open scoped FourierTransform

private theorem symmetricFourier_eq_fourier (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    symmetricFourier f ((2 * Real.pi) • ξ) =
      ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ • (𝓕 f) ξ := by
  rw [symmetricFourier, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change Complex.exp (-↑⟪(2 * Real.pi) • ξ, x⟫_ℝ * Complex.I) * f x =
      Complex.exp (↑(-2 * Real.pi * ⟪x, ξ⟫_ℝ) * Complex.I) * f x
    rw [real_inner_smul_left, real_inner_comm ξ x]
    apply congrArg (· * f x)
    apply congrArg Complex.exp
    push_cast
    ring

/-- **Equation (146)** of [benIsrael2003generalized], Chapter 8.
The symmetric inverse recovers an integrable function at its continuity
points when its symmetric Fourier transform is integrable. -/
theorem symmetricFourierInv_fourier
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) (hg : Integrable (symmetricFourier f))
    {x : EuclideanSpace ℝ (Fin n)} (hx : ContinuousAt f x) :
    symmetricFourierInv (symmetricFourier f) x = f x := by
  let c : ℝ := 2 * Real.pi
  let k : ℝ := (c ^ ((n : ℝ) / 2))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hk : k ≠ 0 := inv_ne_zero (Real.rpow_pos_of_pos hc _).ne'
  have hscaled (w : EuclideanSpace ℝ (Fin n)) : symmetricFourier f (c • w) = k • (𝓕 f) w :=
    symmetricFourier_eq_fourier f w
  have hF : Integrable (𝓕 f) := by
    have h := Integrable.smul k⁻¹ (hg.comp_smul hc.ne')
    convert h using 1
    funext w
    change (𝓕 f) w = k⁻¹ • symmetricFourier f (c • w)
    rw [hscaled, inv_smul_smul₀ hk]
  let K (w : EuclideanSpace ℝ (Fin n)) := Complex.exp (((⟪x, w⟫_ℝ : ℝ) : ℂ) * Complex.I)
  have hs :
      (∫ w, K w * symmetricFourier f w) =
        c ^ n • ∫ w, K (c • w) * symmetricFourier f (c • w) := by
    have h := Measure.integral_comp_inv_smul (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (fun w => K (c • w) * symmetricFourier f (c • w)) c
    simpa only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul, finrank_euclideanSpace,
      Fintype.card_fin, abs_of_nonneg (pow_nonneg hc.le n)] using h
  have hKernel (w : EuclideanSpace ℝ (Fin n)) :
      K (c • w) * symmetricFourier f (c • w) =
        k • (Complex.exp (↑(2 * Real.pi * ⟪w, x⟫_ℝ) * Complex.I) * (𝓕 f) w) := by
    rw [hscaled, ← mul_smul_comm]
    unfold K
    rw [real_inner_smul_right, real_inner_comm x w]
  have hK :
      (∫ w, K (c • w) * symmetricFourier f (c • w)) = k • (𝓕⁻ (𝓕 f)) x := by
    rw [Real.fourierInv_eq', ← integral_smul]
    exact integral_congr_ae (Filter.Eventually.of_forall hKernel)
  change k • (∫ w, K w * symmetricFourier f w) = f x
  rw [hs, hK, smul_smul, smul_smul, hf.fourierInv_fourier_eq hF hx]
  have hnorm : k * c ^ n * k = 1 := by
    dsimp [k]
    have hpow : c ^ n = c ^ ((n : ℝ) / 2) * c ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hc, add_halves]
    rw [hpow]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hc _)]
  rw [hnorm, one_smul]

end Fourier

section ParametrizedSurfaces

/-- **Exercise 32**, Equation (147), of [benIsrael2003generalized], Chapter 8.
For a two-column Jacobian, its volume is `√(E G - F²)`, where `E` and `G`
are the squared norms of the columns and `F` is their inner product. -/
theorem exercise_32 (A : Matrix (Fin m) (Fin 2) ℝ) (hA : A.rank = 2) :
    let E := ∑ i, (A i 0) ^ 2
    let F := ∑ i, A i 0 * A i 1
    let G := ∑ i, (A i 1) ^ 2
    Chapter00.matrixVolume A = Real.sqrt (E * G - F ^ 2) := by
  dsimp
  rw [matrixVolume_eq_sqrt_gramDet A hA (by decide), det_fin_two]
  congr 1
  change (∑ i, A i 0 * A i 0) * (∑ i, A i 1 * A i 1) -
      (∑ i, A i 0 * A i 1) * (∑ i, A i 1 * A i 0) =
    (∑ i, (A i 0) ^ 2) * (∑ i, (A i 1) ^ 2) - (∑ i, A i 0 * A i 1) ^ 2
  simp only [← pow_two]
  have h : (∑ i, A i 1 * A i 0) = ∑ i, A i 0 * A i 1 :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [h, ← pow_two]

/-- The volume of the one-column Jacobian of a curve is its speed. -/
theorem exercise_33_jacobian_volume (v : Fin m → ℝ) :
    Chapter00.matrixVolume (Matrix.of (fun i (_ : Fin 1) => v i)) =
      Real.sqrt (∑ i, (v i) ^ 2) := by
  let A : Matrix (Fin m) (Fin 1) ℝ := Matrix.of fun i _ => v i
  change Chapter00.matrixVolume A = _
  by_cases hA : A = 0
  · have hv (i : Fin m) : v i = 0 := congrFun₂ hA i 0
    simp [hA, hv, Chapter00.matrixVolume]
  · have hr : A.rank = 1 := by
      have hpos : 0 < A.rank := Nat.pos_of_ne_zero (fun h => hA (rank_eq_zero_iff.mp h))
      have hle : A.rank ≤ 1 := by simpa using A.rank_le_card_width
      omega
    rw [matrixVolume_eq_sqrt_gramDet A hr (by decide), det_fin_one]
    simp [A, Matrix.mul_apply, pow_two]

/-- **Exercise 34**, Equations (153)–(154), of [benIsrael2003generalized],
Chapter 8. The cylindrical graph Jacobian with radial and angular height
derivatives `a` and `b` has volume `√(r² + r² a² + b²)`. -/
theorem exercise_34_jacobian_volume (r θ a b : ℝ)
    (h : (!![Real.cos θ, -r * Real.sin θ; Real.sin θ, r * Real.cos θ; a, b] :
      Matrix (Fin 3) (Fin 2) ℝ).rank = 2) :
    Chapter00.matrixVolume !![Real.cos θ, -r * Real.sin θ; Real.sin θ, r * Real.cos θ; a, b] =
      Real.sqrt (r ^ 2 + r ^ 2 * a ^ 2 + b ^ 2) := by
  rw [exercise_32 _ h]
  congr 1
  simp only [Fin.sum_univ_three]
  change (Real.cos θ ^ 2 + Real.sin θ ^ 2 + a ^ 2) *
      ((-r * Real.sin θ) ^ 2 + (r * Real.cos θ) ^ 2 + b ^ 2) -
      (Real.cos θ * (-r * Real.sin θ) + Real.sin θ * (r * Real.cos θ) + a * b) ^ 2 =
    r ^ 2 + r ^ 2 * a ^ 2 + b ^ 2
  linear_combination (r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2 + 1 + a ^ 2) + b ^ 2) *
    Real.sin_sq_add_cos_sq θ

/-- **Exercise 35**, Equation (156), of [benIsrael2003generalized], Chapter 8.
For an axially symmetric cylindrical graph the angular height derivative
vanishes, leaving `r √(1+a²)` for nonnegative radius `r`. -/
theorem exercise_35_jacobian_volume (r θ a : ℝ) (hr : 0 ≤ r)
    (h : (!![Real.cos θ, -r * Real.sin θ; Real.sin θ, r * Real.cos θ; a, 0] :
      Matrix (Fin 3) (Fin 2) ℝ).rank = 2) :
    Chapter00.matrixVolume !![Real.cos θ, -r * Real.sin θ; Real.sin θ, r * Real.cos θ; a, 0] =
      r * Real.sqrt (1 + a ^ 2) := by
  rw [exercise_34_jacobian_volume _ _ _ _ h]
  have harg : r ^ 2 + r ^ 2 * a ^ 2 + (0 : ℝ) ^ 2 = r ^ 2 * (1 + a ^ 2) := by ring
  rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr]

/-- The two columns obtained by differentiating the axially symmetric
spherical chart with `ρ = r` and `ρ' = a`. -/
def sphericalJacobian (r a φ θ : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![(a * Real.sin φ + r * Real.cos φ) * Real.cos θ, -(r * Real.sin φ) * Real.sin θ;
    (a * Real.sin φ + r * Real.cos φ) * Real.sin θ, r * Real.sin φ * Real.cos θ;
    a * Real.cos φ - r * Real.sin φ, 0]

/-- **Exercise 36**, Equation (159a), of [benIsrael2003generalized], Chapter 8.
An axially symmetric spherical chart has volume
`ρ √(ρ² + (ρ')²) sin φ` on the physical range of the spherical coordinates. -/
theorem exercise_36_jacobian_volume (r a φ θ : ℝ) (hr : 0 ≤ r) (hφ : 0 ≤ Real.sin φ)
    (h : (sphericalJacobian r a φ θ).rank = 2) :
    Chapter00.matrixVolume (sphericalJacobian r a φ θ) =
      r * Real.sqrt (r ^ 2 + a ^ 2) * Real.sin φ := by
  rw [exercise_32 _ h]
  have harg : (∑ i : Fin 3, (sphericalJacobian r a φ θ i 0) ^ 2) *
        (∑ i : Fin 3, (sphericalJacobian r a φ θ i 1) ^ 2) -
        (∑ i : Fin 3, sphericalJacobian r a φ θ i 0 * sphericalJacobian r a φ θ i 1) ^ 2 =
      (r * Real.sin φ) ^ 2 * (r ^ 2 + a ^ 2) := by
    simp only [sphericalJacobian, Fin.sum_univ_three]
    let q := a * Real.sin φ + r * Real.cos φ
    let z := a * Real.cos φ - r * Real.sin φ
    let t := r * Real.sin φ
    change ((q * Real.cos θ) ^ 2 + (q * Real.sin θ) ^ 2 + z ^ 2) *
        ((-t * Real.sin θ) ^ 2 + (t * Real.cos θ) ^ 2 + (0 : ℝ) ^ 2) -
        (q * Real.cos θ * (-t * Real.sin θ) + q * Real.sin θ * (t * Real.cos θ) + z * 0) ^ 2 =
      t ^ 2 * (r ^ 2 + a ^ 2)
    have hE : (q * Real.cos θ) ^ 2 + (q * Real.sin θ) ^ 2 + z ^ 2 = r ^ 2 + a ^ 2 := by
      dsimp [q, z]
      linear_combination (a * Real.sin φ + r * Real.cos φ) ^ 2 * Real.sin_sq_add_cos_sq θ +
        (a ^ 2 + r ^ 2) * Real.sin_sq_add_cos_sq φ
    rw [hE]
    linear_combination (r ^ 2 + a ^ 2) * t ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hr hφ)]
  ring

private def omittedRowEquiv (d : ℕ) : Fin (d + 1) ≃ Chapter00.IndexSequence d (d + 1) :=
  Equiv.ofBijective Fin.succAboveOrderEmb (by
    constructor
    · intro j k hjk
      have hr := congrArg (fun e : Chapter00.IndexSequence d (d + 1) => range e) hjk
      rw [Fin.range_succAboveOrderEmb, Fin.range_succAboveOrderEmb] at hr
      simpa using hr
    · intro e
      have hnot : ¬ Function.Surjective e := by
        intro he
        have hle := Fintype.card_le_of_surjective e he
        simp at hle
      have hnot' : ∃ j, ∀ i, e i ≠ j := by
        simpa only [Function.Surjective, not_forall, not_exists] using hnot
      obtain ⟨j, hj⟩ := hnot'
      have hc : (Finset.univ.erase j).card = d := by simp
      have he : ∀ i, e i ∈ Finset.univ.erase j := fun i => by simp [hj i]
      have hs : ∀ i, Fin.succAboveOrderEmb j i ∈ Finset.univ.erase j := fun i => by simp
      exact ⟨j, (Finset.orderEmbOfFin_unique' hc hs).trans
        (Finset.orderEmbOfFin_unique' hc he).symm⟩)

/-- **Exercise 37**, Equation (162), of [benIsrael2003generalized], Chapter 8.
The squared volume of a codimension-one matrix equals the sum of the
squared volumes of its coordinate projections. Each projection omits
one row. The same identity applies to these volumes divided by a common
simplex factorial. -/
theorem exercise_37_projected_volumes (A : Matrix (Fin (d + 1)) (Fin d) ℝ)
    (hA : A.rank = d) (hd : d ≠ 0) :
    (Chapter00.matrixVolume A / d.factorial) ^ 2 =
      ∑ j : Fin (d + 1), (|(A.submatrix (Fin.succAbove j) id).det| / d.factorial) ^ 2 := by
  simp_rw [div_pow, sq_abs]
  rw [← Finset.sum_div, Chapter00.matrixVolume_sq_eq_det_transpose_mul A hA hd,
    Chapter00.det_mul_eq_sum_minors]
  congr 1
  simp_rw [← transpose_submatrix, det_transpose, ← pow_two]
  exact (Equiv.sum_comp (omittedRowEquiv d)
    (fun r => (A.submatrix r id).det ^ 2)).symm

end ParametrizedSurfaces

section BallAndSphere

open Metric

/-- Lebesgue volume of the Euclidean ball of radius `r`. -/
def euclideanBallVolume (n : ℕ) (r : ℝ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).real (closedBall 0 r)

/-- The surface area of the Euclidean unit sphere, using the angular
measure in the polar decomposition of Lebesgue measure. -/
def euclideanUnitSphereArea (n : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.real univ

/-- **Exercise 42**, Equation (172), of [benIsrael2003generalized], Chapter 8.
The Euclidean unit ball has volume `π^(n/2) / Γ(n/2+1)`. -/
theorem exercise_42_unitBallVolume (hn : n ≠ 0) :
    euclideanBallVolume n 1 = Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
  let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [euclideanBallVolume, Measure.real, EuclideanSpace.volume_closedBall,
    Fintype.card_fin]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul Real.pi_pos.le]
  ring_nf

/-- **Exercise 40**, Equation (168), of [benIsrael2003generalized], Chapter 8.
Lebesgue volume scales by the radius to the dimension power. -/
theorem exercise_40_ballVolume (hn : n ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    euclideanBallVolume n r = euclideanBallVolume n 1 * r ^ n := by
  let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  simp only [euclideanBallVolume, Measure.real, EuclideanSpace.volume_closedBall,
    Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, mul_comm]

/-- **Exercise 40**, Equation (169), of [benIsrael2003generalized], Chapter 8.
The unit-sphere area is the ambient dimension times the unit-ball volume. -/
theorem exercise_40_unitSphereArea (hn : n ≠ 0) :
    euclideanUnitSphereArea n = n * euclideanBallVolume n 1 := by
  let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [euclideanUnitSphereArea, Measure.toSphere_real_apply_univ, euclideanBallVolume,
    Measure.real, Measure.real, Measure.addHaar_closedBall_eq_addHaar_ball,
    finrank_euclideanSpace, Fintype.card_fin]

/-- **Exercise 40**, Equation (168), of [benIsrael2003generalized], Chapter 8.
The radial derivative of ball volume at positive radius is the unit-sphere
area times the radius to the ambient dimension minus one. -/
theorem exercise_40_hasDerivAt_ballVolume (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (euclideanBallVolume n) (euclideanUnitSphereArea n * r ^ (n - 1)) r := by
  rw [exercise_40_unitSphereArea hn]
  have h := (hasDerivAt_pow n r).const_mul (euclideanBallVolume n 1)
  have heq : (fun t : ℝ => euclideanBallVolume n 1 * t ^ n) =ᶠ[nhds r] euclideanBallVolume n :=
    by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      exact (exercise_40_ballVolume hn (le_of_lt ht)).symm
  convert h.congr_of_eventuallyEq heq.symm using 1
  ring

/-- **Exercise 41**, the closed form in Equation (171) of
[benIsrael2003generalized], Chapter 8. -/
theorem exercise_41_unitSphereArea (hn : n ≠ 0) :
    euclideanUnitSphereArea n =
      2 * Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2) := by
  rw [exercise_40_unitSphereArea hn, exercise_42_unitBallVolume hn,
    Real.Gamma_add_one (by positivity)]
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

open scoped Pointwise in
/-- **Exercise 40**, the sphere scaling in Equation (168) of
[benIsrael2003generalized], Chapter 8. Hausdorff surface measure scales
by the radius to the dimension of the sphere. -/
theorem exercise_40_sphere_scaling {r : ℝ} (hr : 0 < r) :
    (Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ))
        (sphere (0 : EuclideanSpace ℝ (Fin n)) r) =
      ENNReal.ofReal r ^ (n - 1) *
        (Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ))
          (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hs : r • sphere (0 : EuclideanSpace ℝ (Fin n)) 1 = sphere 0 r := by
    rw [smul_sphere' hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  rw [← hs, Measure.hausdorffMeasure_smul₀ (by positivity) hr.ne']
  have hr' : (↑‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
    have h : ‖r‖₊ = r.toNNReal := by
      ext
      change ‖r‖ = (r.toNNReal : ℝ)
      rw [Real.coe_toNNReal _ hr.le, Real.norm_eq_abs, abs_of_pos hr]
    exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h
  simp only [ENNReal.smul_def, NNReal.rpow_natCast, ENNReal.coe_pow, hr', smul_eq_mul]

/-- **Exercise 41**, Equation (170), of [benIsrael2003generalized], Chapter 8.
The upper hemisphere graph has Gram density `1 / √(1-‖u‖²)` strictly
inside the unit disk. -/
theorem exercise_41_hemisphere_density
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ < 1) :
    EuclideanSpace.graphDensity (fun x => Real.sqrt (1 - ‖x‖ ^ 2)) u =
      (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹ := by
  have hpos : 0 < 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  let r := Real.sqrt (1 - ‖u‖ ^ 2)
  have hr : r ≠ 0 := (Real.sqrt_pos_of_pos hpos).ne'
  have hGrad : HasGradientAt (fun x => Real.sqrt (1 - ‖x‖ ^ 2)) (-r⁻¹ • u) u := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have h := ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_sub 1).sqrt hpos.ne'
    convert h using 1
    ext w
    simp only [InnerProductSpace.toDual_apply_apply, smul_apply, neg_apply, real_inner_smul_left,
      smul_eq_mul, two_smul]
    change -r⁻¹ * ⟪u, w⟫_ℝ = (1 / (2 * r)) * -(⟪u, w⟫_ℝ + ⟪u, w⟫_ℝ)
    field_simp
    ring
  change Real.sqrt (1 + ‖gradient (fun x => Real.sqrt (1 - ‖x‖ ^ 2)) u‖ ^ 2) = r⁻¹
  have hrsq : r ^ 2 = 1 - ‖u‖ ^ 2 := Real.sq_sqrt hpos.le
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
  rw [hGrad.gradient, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_of_nonneg hrnonneg]
  calc
    Real.sqrt (1 + (r⁻¹ * ‖u‖) ^ 2) = Real.sqrt (r⁻¹ ^ 2) := by
      congr 1
      field_simp
      nlinarith
    _ = r⁻¹ := Real.sqrt_sq (inv_nonneg.mpr hrnonneg)

end BallAndSphere

section BetaAndGamma

/-- **Exercise 39**, Equation (164), of [benIsrael2003generalized], Chapter 8.
The Gamma function is given by Euler's integral at positive arguments. -/
theorem exercise_39_gamma_integral {p : ℝ} (hp : 0 < p) :
    Real.Gamma p = ∫ x in Ioi 0, x ^ (p - 1) * Real.exp (-x) := by
  simpa only [mul_comm] using Real.Gamma_eq_integral hp

/-- **Exercise 39**, Equations (165a)–(165c), of
[benIsrael2003generalized], Chapter 8. -/
theorem exercise_39_gamma_values (p : ℝ) (hp : 0 < p) :
    Real.Gamma 1 = 1 ∧ Real.Gamma (p + 1) = p * Real.Gamma p ∧
      Real.Gamma (1 / 2) = Real.sqrt Real.pi :=
  ⟨Real.Gamma_one, Real.Gamma_add_one hp.ne', Real.Gamma_one_half_eq⟩

/-- **Exercise 39**, Equation (166), of [benIsrael2003generalized], Chapter 8.
The Beta integral in the order used in the source. -/
def realBeta (p q : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - x) ^ (p - 1) * x ^ (q - 1)

/-- **Exercise 39**, Equation (167a), of [benIsrael2003generalized], Chapter 8.
Euler's Beta integral in terms of the Gamma function. -/
theorem exercise_39_beta_eq_gamma {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    realBeta p q = Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hreal : Complex.betaIntegral (q : ℂ) (p : ℂ) = (realBeta p q : ℂ) := by
    rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    push_cast
    rw [Complex.ofReal_cpow (by linarith [hx.2]), Complex.ofReal_cpow hx.1]
    push_cast
    ring
  have h := Complex.betaIntegral_eq_Gamma_mul_div (q : ℂ) (p : ℂ)
    (by exact_mod_cast hq) (by exact_mod_cast hp)
  rw [hreal, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_div] at h
  exact_mod_cast (by simpa only [add_comm q p, mul_comm (Real.Gamma q) (Real.Gamma p)] using h :
    (realBeta p q : ℂ) = ↑(Real.Gamma p * Real.Gamma q / Real.Gamma (p + q)))

/-- **Exercise 39**, Equation (167b), of [benIsrael2003generalized], Chapter 8. -/
theorem exercise_39_beta_succ_right {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    realBeta p (q + 1) / realBeta p q = q / (p + q) := by
  rw [exercise_39_beta_eq_gamma hp (by positivity), exercise_39_beta_eq_gamma hp hq,
    ← add_assoc, Real.Gamma_add_one hq.ne', Real.Gamma_add_one (add_pos hp hq).ne']
  have hp' := (Real.Gamma_pos_of_pos hp).ne'
  have hq' := (Real.Gamma_pos_of_pos hq).ne'
  have hpq' := (Real.Gamma_pos_of_pos (add_pos hp hq)).ne'
  field_simp

/-- **Exercise 39**, Equation (167c), of [benIsrael2003generalized], Chapter 8. -/
theorem exercise_39_beta_succ_left {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    realBeta (p + 1) q / realBeta p q = p / (p + q) := by
  rw [exercise_39_beta_eq_gamma (by positivity) hq, exercise_39_beta_eq_gamma hp hq,
    add_right_comm, Real.Gamma_add_one hp.ne', Real.Gamma_add_one (add_pos hp hq).ne']
  have hp' := (Real.Gamma_pos_of_pos hp).ne'
  have hq' := (Real.Gamma_pos_of_pos hq).ne'
  have hpq' := (Real.Gamma_pos_of_pos (add_pos hp hq)).ne'
  field_simp

end BetaAndGamma

section RadonExercises

open EuclideanSpace

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-- **Exercise 43** of [benIsrael2003generalized], Chapter 8.
Normalizing the hyperplane's normal divides its level by the same norm
and preserves its Radon integral. -/
theorem exercise_43_radon_normalize {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : 𝔼 → G) (ξ : 𝔼) (hξ : ξ ≠ 0) (p : ℝ) :
    let ξ₀ := ‖ξ‖⁻¹ • ξ
    ‖ξ₀‖ = 1 ∧ radonTransformAll f ξ₀ (p / ‖ξ‖) = radonTransformAll f ξ p := by
  dsimp
  have hn := norm_ne_zero_iff.mpr hξ
  have hξ₀ : ‖‖ξ‖⁻¹ • ξ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg ξ), inv_mul_cancel₀ hn]
  refine ⟨hξ₀, ?_⟩
  have hξ₀' : ‖ξ‖⁻¹ • ξ ≠ 0 := by
    rw [← norm_ne_zero_iff, hξ₀]
    norm_num
  rw [radonTransformAll_eq_graphIntegral, radonTransformAll_eq_graphIntegral]
  have h : graphMeasure (radonFrame (‖ξ‖⁻¹ • ξ)).toAffineIsometryEquiv
        (fun _ => (p / ‖ξ‖) / ‖‖ξ‖⁻¹ • ξ‖) univ =
      graphMeasure (radonFrame ξ).toAffineIsometryEquiv (fun _ => p / ‖ξ‖) univ := by
    apply graphMeasure_eq_of_range_eq contDiff_const contDiff_const
    change range (radonNormalChart (‖ξ‖⁻¹ • ξ) (p / ‖ξ‖)) =
      range (radonNormalChart ξ p)
    rw [range_radonNormalChart _ hξ₀', range_radonNormalChart ξ hξ]
    ext x
    simp only [Set.mem_ofPred_eq, real_inner_smul_left, div_eq_inv_mul,
      mul_right_inj' (inv_ne_zero hn)]
  rw [h]

/-- A bounded measurable weight that depends only on the hyperplane level
can be taken outside each Radon slice. -/
theorem integral_mul_radonTransformAll {f : 𝔼 → ℝ} (hf : Integrable f)
    (ξ : 𝔼) (hξ : ξ ≠ 0) (k : ℝ → ℝ) (hk : Measurable k)
    (C : ℝ) (hC : ∀ t, ‖k t‖ ≤ C) :
    ∫ x, k ⟪ξ, x⟫_ℝ * f x = ‖ξ‖⁻¹ * ∫ p, k p * radonTransformAll f ξ p := by
  have hm : Measurable fun x : 𝔼 => k ⟪ξ, x⟫_ℝ :=
    hk.comp (innerSL ℝ ξ).continuous.measurable
  have hg : Integrable (fun x => k ⟪ξ, x⟫_ℝ * f x) := by
    convert hf.bdd_smul C hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hC ⟪ξ, x⟫_ℝ) using 1
  rw [integral_eq_integral_radonTransformAll _ hg ξ hξ, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    simp only [radonTransformAll, inner_radonNormalChart ξ hξ, integral_const_mul]

/-- **Exercise 43**, Equation (174), of [benIsrael2003generalized], Chapter 8.
For a unit normal the Radon transform satisfies the weak Dirac-delta
formula, tested against any bounded measurable scalar function. -/
theorem exercise_43_dirac {f : 𝔼 → ℝ} (hf : Integrable f)
    (ξ : 𝔼) (hξ : ‖ξ‖ = 1) (k : ℝ → ℝ) (hk : Measurable k)
    (C : ℝ) (hC : ∀ t, ‖k t‖ ≤ C) :
    ∫ p, k p * radonTransformAll f ξ p =
      ∫ x, (∫ p, k p ∂Measure.dirac ⟪ξ, x⟫_ℝ) * f x := by
  have hξ' : ξ ≠ 0 := norm_ne_zero_iff.mp (hξ ▸ one_ne_zero)
  simp_rw [integral_dirac k]
  simpa only [hξ, inv_one, one_mul] using (integral_mul_radonTransformAll hf ξ hξ' k hk C hC).symm

/-- **Exercise 44** of [benIsrael2003generalized], Chapter 8.
The Radon transform of a planar Gaussian is a Gaussian in the offset,
for all nonzero normals including the vertical case. -/
theorem exercise_44_gaussian (ξ : EuclideanSpace ℝ (Fin 2)) (_hξ : ξ ≠ 0) (p : ℝ) :
    radonTransformAll (fun x => Real.exp (-‖x‖ ^ 2)) ξ p =
      Real.sqrt Real.pi * Real.exp (-(p ^ 2) / ‖ξ‖ ^ 2) := by
  simp only [radonTransformAll, radonNormalChart, LinearIsometryEquiv.norm_map, norm_snocLast_sq,
    neg_add, Real.exp_add, integral_mul_const, div_pow, neg_div]
  congr 1
  let e : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  calc
    ∫ u : EuclideanSpace ℝ (Fin 1), Real.exp (-‖u‖ ^ 2)
      = ∫ x : ℝ, Real.exp (-‖e x‖ ^ 2) :=
        (MeasureTheory.integral_comp e (fun u => Real.exp (-‖u‖ ^ 2))).symm
    _ = ∫ x : ℝ, Real.exp (-x ^ 2) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have he : ‖e x‖ = ‖x‖ := e.norm_map x
      change Real.exp (-‖e x‖ ^ 2) = Real.exp (-x ^ 2)
      rw [he, Real.norm_eq_abs, sq_abs]
    _ = Real.sqrt Real.pi := by
      simpa only [neg_one_mul, div_one] using integral_gaussian (1 : ℝ)

end RadonExercises

section Cylinders

open EuclideanSpace Metric

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

private theorem fubini_unitBall_slice (u : 𝔼') (hu : ‖u‖ ≤ 1) :
    (fun t : ℝ => snocLast u t) ⁻¹' closedBall (0 : 𝔼) 1 =
      Icc (-Real.sqrt (1 - ‖u‖ ^ 2)) (Real.sqrt (1 - ‖u‖ ^ 2)) := by
  have hq : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  ext t
  change dist (snocLast u t) 0 ≤ 1 ↔
    -Real.sqrt (1 - ‖u‖ ^ 2) ≤ t ∧ t ≤ Real.sqrt (1 - ‖u‖ ^ 2)
  rw [dist_zero_right]
  have habs : |t| ≤ Real.sqrt (1 - ‖u‖ ^ 2) ↔ t ^ 2 ≤ 1 - ‖u‖ ^ 2 := by
    rw [Real.le_sqrt (abs_nonneg t) hq, sq_abs]
  rw [← abs_le, habs]
  have hnorm := norm_snocLast_sq u t
  constructor
  · intro ht
    nlinarith [norm_nonneg (snocLast u t)]
  · intro ht
    nlinarith [norm_nonneg (snocLast u t)]

/-- **Exercise 42**, Equation (173), of [benIsrael2003generalized], Chapter 8.
The volume of the unit ball is the integral of the lengths of its
vertical chords. -/
theorem exercise_42_cylinder_integral :
    euclideanBallVolume (d + 1) 1 =
      2 * ∫ u in closedBall (0 : 𝔼') 1, Real.sqrt (1 - ‖u‖ ^ 2) := by
  let B := closedBall (0 : 𝔼) 1
  let A := closedBall (0 : 𝔼') 1
  let f := B.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f :=
    (integrableOn_const (measure_closedBall_lt_top (μ := volume) (x := (0 : 𝔼))
      (r := 1)).ne).integrable_indicator measurableSet_closedBall
  have hleft : (∫ x, f x) = euclideanBallVolume (d + 1) 1 := by
    rw [show f = B.indicator (fun _ => 1) by rfl, integral_indicator measurableSet_closedBall]
    simp [euclideanBallVolume]
  rw [← hleft, integral_lastInit _ hf]
  have hr : (fun u : 𝔼' => ∫ t, f (snocLast u t)) =
      A.indicator (fun u => 2 * Real.sqrt (1 - ‖u‖ ^ 2)) := by
    funext u
    by_cases hu : u ∈ A
    · have hu' : ‖u‖ ≤ 1 := by simpa [A, dist_zero_right] using hu
      have hpre := fubini_unitBall_slice u hu'
      change (∫ t, B.indicator (fun _ => 1) (snocLast u t)) = _
      have hcomp : (fun t => B.indicator (fun _ : 𝔼 => (1 : ℝ)) (snocLast u t)) =
          ((fun t => snocLast u t) ⁻¹' B).indicator (fun _ => 1) := by
        funext t
        exact (indicator_comp_right (fun t => snocLast u t) (g := fun _ => 1)).symm
      rw [hcomp, show (fun t => snocLast u t) ⁻¹' B = _ from hpre]
      rw [integral_indicator measurableSet_Icc, integral_const, Measure.real,
        Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal]
      · simp only [smul_eq_mul, mul_one, indicator_of_mem hu]
        ring
      · linarith [Real.sqrt_nonneg (1 - ‖u‖ ^ 2)]
    · rw [indicator_of_notMem hu]
      have hn : 1 < ‖u‖ := by simpa [A, dist_zero_right] using hu
      have hzero : ∀ t : ℝ, f (snocLast u t) = 0 := by
        intro t
        apply indicator_of_notMem
        intro ht
        have hle : ‖snocLast u t‖ ≤ 1 := by simpa [B, dist_zero_right] using ht
        nlinarith [norm_snocLast_sq u t, norm_nonneg (snocLast u t), sq_nonneg t]
      simp [hzero]
  rw [hr, integral_indicator measurableSet_closedBall, integral_const_mul]

end Cylinders

section LinearArea

open EuclideanSpace

local notation "𝔼ₙ" => EuclideanSpace ℝ (Fin n)
local notation "𝔼ₘ" => EuclideanSpace ℝ (Fin m)

private theorem euclideanHausdorffMeasure_image_isometry {i : 𝔼ₙ → 𝔼ₘ}
    (hi : Isometry i) (U : Set 𝔼ₙ) :
    euclideanHausdorffMeasure n m (i '' U) = volume U := by
  rw [← euclideanHausdorffMeasure_self n]
  simp only [euclideanHausdorffMeasure, Measure.smul_apply]
  rw [hi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg n))]

/-- **Equation (124)** of [benIsrael2003generalized], Chapter 8, for an
injective linear chart. Normalized Hausdorff measure on the image of a set
is its Lebesgue measure times the Gram volume of the chart. -/
theorem hausdorffMeasure_image_linear (L : 𝔼ₙ →L[ℝ] 𝔼ₘ) (hL : Function.Injective L)
    (U : Set 𝔼ₙ) :
    euclideanHausdorffMeasure n m (L '' U) = ENNReal.ofReal (gram L) * volume U := by
  let W := LinearMap.range L.toLinearMap
  have hdim : Module.finrank ℝ W = n := by
    rw [LinearMap.finrank_range_of_inj hL]
    simp
  let e : W ≃ₗᵢ[ℝ] 𝔼ₙ := (stdOrthonormalBasis ℝ W).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim))
  let i : 𝔼ₙ →ₗᵢ[ℝ] 𝔼ₘ := W.subtypeₗᵢ.comp e.symm.toLinearIsometry
  let A : 𝔼ₙ →L[ℝ] 𝔼ₙ := (e.toContinuousLinearEquiv : W →L[ℝ] 𝔼ₙ).comp
    (L.codRestrict W (fun x => LinearMap.mem_range_self L.toLinearMap x))
  have hLA : L = i.toContinuousLinearMap.comp A := by
    apply ContinuousLinearMap.ext
    intro x
    change L x = (e.symm (e ⟨L x, _⟩)).1
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hgram : EuclideanSpace.gram i.toContinuousLinearMap = 1 := by
    unfold EuclideanSpace.gram
    rw [gramDet_eq_det_of_inner]
    change Real.sqrt (Matrix.of fun j k : Fin n => ⟪i (single j 1), i (single k 1)⟫_ℝ).det = 1
    suffices (Matrix.of fun j k : Fin n =>
        ⟪i (single j 1), i (single k 1)⟫_ℝ) = (1 : Matrix (Fin n) (Fin n) ℝ) by
      rw [this, Matrix.det_one, Real.sqrt_one]
    ext j k
    rw [Matrix.of_apply, i.inner_map_map, Matrix.one_apply]
    exact orthonormal_iff_ite.mp (orthonormal_single (𝕜 := ℝ)) j k
  have hdet : gram L = |A.det| := by
    rw [hLA, gram_comp, hgram, one_mul]
  rw [hdet, hLA]
  change euclideanHausdorffMeasure n m ((i ∘ A) '' U) = _
  have heimage : (i ∘ A) '' U = i '' (A '' U) := (Set.image_image i A U).symm
  rw [heimage, euclideanHausdorffMeasure_image_isometry i.isometry]
  exact Measure.addHaar_image_continuousLinearMap volume A U

end LinearArea

section SmoothArea

open MeasureTheory Filter Set EuclideanSpace TopologicalSpace InnerProductSpace
open scoped ENNReal NNReal Topology

variable {n m : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m)
local notation "H" => euclideanHausdorffMeasure n m

private theorem continuous_gram : Continuous (EuclideanSpace.gram : (X →L[ℝ] Y) → ℝ) := by
  have h (L : X →L[ℝ] Y) : EuclideanSpace.gram L = Real.sqrt (Matrix.gram ℝ (fun i : Fin n => L (single i 1))).det := by
    rw [EuclideanSpace.gram, gramDet_eq_det_of_inner]
    rfl
  change Continuous (fun L : X →L[ℝ] Y => EuclideanSpace.gram L)
  simp_rw [h]
  apply Real.continuous_sqrt.comp
  apply Continuous.matrix_det
  change Continuous (fun L : X →L[ℝ] Y =>
    (Matrix.of fun i j : Fin n => inner ℝ (L (single i 1)) (L (single j 1))))
  apply continuous_matrix
  intro i j
  change Continuous (fun L : X →L[ℝ] Y => inner ℝ (L (single i 1)) (L (single j 1)))
  fun_prop

private theorem gram_pos_of_injective (L : X →L[ℝ] Y) (hL : Function.Injective L) :
    0 < EuclideanSpace.gram L := by
  unfold EuclideanSpace.gram
  rw [gramDet_eq_det_of_inner]
  apply Real.sqrt_pos_of_pos
  apply Matrix.PosDef.det_pos
  exact Matrix.posDef_gram_of_linearIndependent
    ((orthonormal_single (𝕜 := ℝ) (ι := Fin n)).linearIndependent.map' L.toLinearMap
      (LinearMap.ker_eq_bot.mpr hL))

private theorem hausdorff_image_compare {f g : X → Y} {s : Set X} {r : ℝ≥0}
    (hg : InjOn g s)
    (hle : ∀ a ∈ s, ∀ b ∈ s, dist (f a) (f b) ≤ (r : ℝ) * dist (g a) (g b)) :
    H (f '' s) ≤ (r : ℝ≥0∞) ^ n * H (g '' s) := by
  let inv : Y → X := Function.invFunOn g s
  have hInv : LeftInvOn inv g s := hg.leftInvOn_invFunOn
  have hL : LipschitzOnWith r (f ∘ inv) (g '' s) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [Function.comp_apply, hInv ha, hInv hb]
    exact hle a ha b hb
  have he : (f ∘ inv) '' (g '' s) = f '' s := by
    rw [image_image]
    exact image_congr fun x hx => congrArg f (hInv hx)
  have hHaus := hL.hausdorffMeasure_image_le (d := (n : ℝ)) (by positivity)
  rw [he, ENNReal.rpow_natCast] at hHaus
  let c := Measure.addHaarScalarFactor (volume : Measure X)
    (Measure.hausdorffMeasure (Module.finrank ℝ X : ℝ))
  change c * _ ≤ (r : ℝ≥0∞) ^ n * (c * _)
  rw [mul_left_comm]
  gcongr
  exact hHaus

/-- On a small convex neighborhood of a full-rank derivative, the chart and the
linearization distort their respective pairwise distances by at most the given factor. -/
private theorem local_hausdorff_chart_control {Ω : Set X} (hΩ : IsOpen Ω)
    {f : X → Y} {f' : X → X →L[ℝ] Y} (hf : ∀ x ∈ Ω, HasFDerivAt f (f' x) x)
    (hfc : ContinuousOn f' Ω) (hRank : ∀ x ∈ Ω, Function.Injective (f' x))
    {r : ℝ≥0} (hr : 1 < r) (x : X) (hx : x ∈ Ω) :
    ∃ (δ : ℝ), 0 < δ ∧ Metric.ball x δ ⊆ Ω ∧
      (∀ y ∈ Metric.ball x δ, EuclideanSpace.gram (f' y) ≤ r * EuclideanSpace.gram (f' x) ∧ EuclideanSpace.gram (f' x) ≤ r * EuclideanSpace.gram (f' y)) ∧
      (∀ a ∈ Metric.ball x δ, ∀ b ∈ Metric.ball x δ,
        dist (f a) (f b) ≤ r * dist (f' x a) (f' x b) ∧
        dist (f' x a) (f' x b) ≤ r * dist (f a) (f b)) := by
  let L := f' x
  have hr' : (1 : ℝ) < r := hr
  obtain ⟨C, hC, hInv⟩ := L.injective_iff_antilipschitz.mp (hRank x hx)
  have hC' : 0 < (C : ℝ) := hC
  let e : ℝ := min ((r : ℝ) - 1) (1 - (r : ℝ)⁻¹)
  have he : 0 < e := lt_min (sub_pos.mpr hr') (sub_pos.mpr (inv_lt_one_of_one_lt₀ hr'))
  have hdiv : 0 < e / C := div_pos he hC'
  have hg : 0 < EuclideanSpace.gram L := gram_pos_of_injective L (hRank x hx)
  let d : ℝ := min (((r : ℝ) - 1) * EuclideanSpace.gram L) ((1 - (r : ℝ)⁻¹) * EuclideanSpace.gram L)
  have hd : 0 < d := lt_min (mul_pos (sub_pos.mpr hr') hg)
    (mul_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ hr')) hg)
  have hOpen : Ω ∈ 𝓝 x := hΩ.mem_nhds hx
  have hcont : ContinuousAt f' x := (hfc x hx).continuousAt hOpen
  have hgcont : ContinuousAt (EuclideanSpace.gram ∘ f') x := continuous_gram.continuousAt.comp hcont
  have hMem : Ω ∩ ((f' ⁻¹' Metric.ball L (e / C)) ∩
      ((EuclideanSpace.gram ∘ f') ⁻¹' Metric.ball (EuclideanSpace.gram L) d)) ∈ 𝓝 x :=
    inter_mem hOpen (inter_mem (hcont (Metric.ball_mem_nhds L hdiv))
      (hgcont (Metric.ball_mem_nhds (EuclideanSpace.gram L) hd)))
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.mem_nhds_iff.mp hMem
  refine ⟨δ₀, hδ₀, fun y hy => (hδ hy).1, ?_, ?_⟩
  · intro y hy
    have hb : |EuclideanSpace.gram (f' y) - EuclideanSpace.gram L| < d := by
      simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, Function.comp_apply] using (hδ hy).2.2
    obtain ⟨hb₁, hb₂⟩ := abs_lt.mp hb
    have h₁ : d ≤ ((r : ℝ) - 1) * EuclideanSpace.gram L := min_le_left ..
    have h₂ : d ≤ (1 - (r : ℝ)⁻¹) * EuclideanSpace.gram L := min_le_right ..
    constructor
    · linarith
    · have : (r : ℝ)⁻¹ * EuclideanSpace.gram L ≤ EuclideanSpace.gram (f' y) := by linarith
      rwa [inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < r), mul_comm] at this
  · intro a ha b hb
    have ht : ‖f b - f a - L (b - a)‖ ≤ (e / C) * ‖b - a‖ := by
      apply (convex_ball x δ₀).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun y hy => (hf y (hδ hy).1).hasFDerivWithinAt) ?_ ha hb
      intro y hy
      have hz := (hδ hy).2.1
      exact (by simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hz :
        ‖f' y - L‖ < e / C).le
    have ht' : ‖f b - f a - L (b - a)‖ ≤ e * ‖L (b - a)‖ := by
      refine ht.trans ?_
      have hc : ‖b - a‖ ≤ (C : ℝ) * ‖L (b - a)‖ := by
        rw [map_sub]
        change AntilipschitzWith C L at hInv
        simpa only [dist_eq_norm] using hInv.le_mul_dist b a
      calc
        (e / C) * ‖b - a‖ ≤ (e / C) * (C * ‖L (b - a)‖) :=
          mul_le_mul_of_nonneg_left hc hdiv.le
        _ = e * ‖L (b - a)‖ := by rw [← mul_assoc, div_mul_cancel₀ _ hC'.ne']
    have h₁ := (norm_sub_norm_le (f b - f a) (L (b - a))).trans ht'
    have h₂ : ‖L (b - a)‖ - ‖f b - f a‖ ≤ e * ‖L (b - a)‖ := by
      refine (norm_sub_norm_le (L (b - a)) (f b - f a)).trans ?_
      rw [norm_sub_rev (L (b - a))]
      exact ht'
    have h₃ : e * ‖L (b - a)‖ ≤ ((r : ℝ) - 1) * ‖L (b - a)‖ :=
      mul_le_mul_of_nonneg_right (min_le_left ..) (norm_nonneg _)
    have h₄ : e * ‖L (b - a)‖ ≤ (1 - (r : ℝ)⁻¹) * ‖L (b - a)‖ :=
      mul_le_mul_of_nonneg_right (min_le_right ..) (norm_nonneg _)
    rw [dist_comm (f a) (f b), dist_comm (f' x a) (f' x b), dist_eq_norm, dist_eq_norm,
      ← map_sub (f' x)]
    constructor
    · linarith
    · have : (r : ℝ)⁻¹ * ‖L (b - a)‖ ≤ ‖f b - f a‖ := by linarith
      rwa [inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < r), mul_comm] at this

private theorem gram_lintegral_compare {f g : X → Y} {D : Set X}
    (hD : MeasurableSet D) {J : X → ℝ} {j : ℝ} {r : ℝ≥0}
    (hg : ∀ x ∈ D, J x ≤ r * j ∧ j ≤ r * J x)
    (hF : H (g '' D) = ENNReal.ofReal j * volume D)
    (hfg : H (f '' D) ≤ (r : ℝ≥0∞) ^ n * H (g '' D))
    (hgf : H (g '' D) ≤ (r : ℝ≥0∞) ^ n * H (f '' D)) :
    H (f '' D) ≤ (r : ℝ≥0∞) ^ (n + 1) * (∫⁻ x in D, ENNReal.ofReal (J x)) ∧
      (∫⁻ x in D, ENNReal.ofReal (J x)) ≤ (r : ℝ≥0∞) ^ (n + 1) * H (f '' D) := by
  have h₁ : (∫⁻ x in D, ENNReal.ofReal (J x)) ≤ (r : ℝ≥0∞) * H (g '' D) := by
    rw [hF, ← mul_assoc, ← Measure.restrict_apply_univ (μ := volume) D, ← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hD] with x hx
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul r.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal (hg x hx).1
  have h₂ : H (g '' D) ≤ (r : ℝ≥0∞) * (∫⁻ x in D, ENNReal.ofReal (J x)) := by
    rw [hF, ← Measure.restrict_apply_univ (μ := volume) D, ← lintegral_const,
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hD] with x hx
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul r.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal (hg x hx).2
  constructor
  · calc
      H (f '' D) ≤ (r : ℝ≥0∞) ^ n * H (g '' D) := hfg
      _ ≤ (r : ℝ≥0∞) ^ n * ((r : ℝ≥0∞) * (∫⁻ x in D, ENNReal.ofReal (J x))) := by gcongr
      _ = _ := by rw [pow_succ, mul_assoc]
  · calc
      _ ≤ (r : ℝ≥0∞) * H (g '' D) := h₁
      _ ≤ (r : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n * H (f '' D)) := by gcongr
      _ = _ := by rw [pow_succ, mul_left_comm, mul_assoc]

private theorem global_hausdorff_chart_comparison {Ω S : Set X} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hsub : S ⊆ Ω) {f : X → Y} {f' : X → X →L[ℝ] Y}
    (hf : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) (hfc : ContinuousOn f' Ω)
    (hRank : ∀ x ∈ Ω, Function.Injective (f' x)) (hinj : InjOn f S)
    {r : ℝ≥0} (hr : 1 < r) :
    H (f '' S) ≤ (r : ℝ≥0∞) ^ (n + 1) * (∫⁻ x in S, ENNReal.ofReal (EuclideanSpace.gram (f' x))) ∧
      (∫⁻ x in S, ENNReal.ofReal (EuclideanSpace.gram (f' x))) ≤ (r : ℝ≥0∞) ^ (n + 1) * H (f '' S) := by
  by_cases hSEmpty : S = ∅
  · simp [hSEmpty]
  have hSn : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSEmpty
  let : Nonempty Ω := by
    obtain ⟨x, hx⟩ := hSn
    exact ⟨⟨x, hsub hx⟩⟩
  have hB (x : Ω) := local_hausdorff_chart_control hΩ hf hfc hRank hr x.val x.property
  choose δ hδ hBΩ hGram hComp using hB
  have hCover : S ⊆ ⋃ x : Ω, Metric.ball x.val (δ x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hsub hx⟩, Metric.mem_ball_self (hδ ⟨x, hsub hx⟩)⟩
  obtain ⟨a, ha⟩ :=
    (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover _ (fun _ => Metric.isOpen_ball) hCover
  let B (k : ℕ) := Metric.ball (a k).val (δ (a k))
  let T (k : ℕ) := S ∩ disjointed B k
  have hBT (k : ℕ) : T k ⊆ B k := inter_subset_right.trans (disjointed_subset B k)
  have hTS (k : ℕ) : T k ⊆ S := inter_subset_left
  have hT (k : ℕ) : MeasurableSet (T k) :=
    hS.inter (MeasurableSet.disjointed (fun _ => measurableSet_ball) k)
  have hDisj : Pairwise (Function.onFun Disjoint T) :=
    pairwise_disjoint_mono (disjoint_disjointed B) (fun _ => inter_subset_right)
  have hUnion : (⋃ k, T k) = S := by
    change ⋃ k, S ∩ disjointed B k = S
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_self_of_subset_left ha]
  have hCont : ContinuousOn f S := fun x hx => (hf x (hsub hx)).continuousAt.continuousWithinAt
  have hImMeas (k : ℕ) : MeasurableSet (f '' T k) :=
    (hT k).image_of_continuousOn_injOn (hCont.mono (hTS k)) (hinj.mono (hTS k))
  have hImDisj : Pairwise (Function.onFun Disjoint (fun k => f '' T k)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hey⟩
    have hh := hinj (hTS j hy) (hTS i hx) hey
    exact Set.disjoint_left.mp (hDisj hij) hx (hh ▸ hy)
  have hIm : H (f '' S) = ∑' k, H (f '' T k) := by
    rw [← hUnion, image_iUnion, measure_iUnion hImDisj hImMeas]
  have hJI : (∫⁻ x in S, ENNReal.ofReal (EuclideanSpace.gram (f' x))) =
      ∑' k, ∫⁻ x in T k, ENNReal.ofReal (EuclideanSpace.gram (f' x)) := by
    rw [← hUnion, lintegral_iUnion hT hDisj]
  have hLoc (k : ℕ) :=
    gram_lintegral_compare (n := n) (m := m) (f := f) (g := f' (a k))
      (hT k) (fun x hx => hGram (a k) x (hBT k hx))
      (hausdorffMeasure_image_linear _ (hRank (a k) (a k).property) (T k))
      (hausdorff_image_compare (hRank (a k) (a k).property).injOn
        (fun x hx y hy => (hComp (a k) x (hBT k hx) y (hBT k hy)).1))
      (hausdorff_image_compare (hinj.mono (hTS k))
        (fun x hx y hy => (hComp (a k) x (hBT k hx) y (hBT k hy)).2))
  rw [hIm, hJI, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨tsum_le_tsum (fun k => (hLoc k).1), tsum_le_tsum (fun k => (hLoc k).2)⟩

private theorem ennreal_le_of_all_factors {a b : ℝ≥0∞} (n : ℕ)
    (h : ∀ r : ℝ≥0, 1 < r → a ≤ (r : ℝ≥0∞) ^ n * b) : a ≤ b := by
  have hpow : Tendsto (fun r : ℝ≥0 => (r : ℝ≥0∞) ^ n) (𝓝[>] 1) (𝓝 1) := by
    have hc : Continuous (fun r : ℝ≥0 => (r : ℝ≥0∞) ^ n) := by fun_prop
    have ht := hc.continuousAt (x := (1 : ℝ≥0))
    simpa only [ContinuousWithinAt, ENNReal.coe_one, one_pow] using
      ht.continuousWithinAt (s := Ioi (1 : ℝ≥0))
  have hlim := ENNReal.Tendsto.mul_const hpow (b := b) (Or.inl one_ne_zero)
  rw [one_mul] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact h r hr

/-- **Equation (124)** of [benIsrael2003generalized], Chapter 8.
For an injective chart with continuous, injective derivative on a
neighborhood, normalized Hausdorff measure equals the weighted
Lebesgue measure of the parameters. -/
theorem hausdorffMeasure_image_eq_lintegral_gram {Ω S : Set X} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hsub : S ⊆ Ω) {f : X → Y} {f' : X → X →L[ℝ] Y}
    (hf : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) (hfc : ContinuousOn f' Ω)
    (hRank : ∀ x ∈ Ω, Function.Injective (f' x)) (hinj : InjOn f S) :
    H (f '' S) = ∫⁻ x in S, ENNReal.ofReal (EuclideanSpace.gram (f' x)) := by
  apply le_antisymm <;> apply ennreal_le_of_all_factors (n + 1) <;> intro r hr
  · exact (global_hausdorff_chart_comparison hΩ hS hsub hf hfc hRank hinj hr).1
  · exact (global_hausdorff_chart_comparison hΩ hS hsub hf hfc hRank hinj hr).2

private theorem map_gram_density_eq_hausdorff {Ω S : Set X} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hsub : S ⊆ Ω) {f : X → Y} {f' : X → X →L[ℝ] Y}
    (hf : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) (hfc : ContinuousOn f' Ω)
    (hRank : ∀ x ∈ Ω, Function.Injective (f' x)) (hinj : InjOn f S) :
    Measure.map (S.domRestrict f)
        (Measure.comap Subtype.val (volume.withDensity (fun x => ENNReal.ofReal (EuclideanSpace.gram (f' x))))) =
      (H).restrict (f '' S) := by
  have hCont : ContinuousOn f S := fun x hx => (hf x (hsub hx)).continuousAt.continuousWithinAt
  have hEmb := hCont.measurableEmbedding hS hinj
  let J (x : X) := ENNReal.ofReal (EuclideanSpace.gram (f' x))
  apply Measure.ext
  intro T hT
  let U := Subtype.val '' (S.domRestrict f ⁻¹' T)
  have hUm : MeasurableSet U :=
    (MeasurableEmbedding.subtype_coe hS).measurableSet_image.mpr (hEmb.measurable hT)
  have hUS : U ⊆ S := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hUT : f '' U = T ∩ f '' S := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨hx, mem_image_of_mem f x.property⟩
    · rintro ⟨hy, ⟨x, hx, rfl⟩⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  change (Measure.map (S.domRestrict f) (Measure.comap Subtype.val (volume.withDensity J))) T =
    (H).restrict (f '' S) T
  rw [Measure.map_apply hEmb.measurable hT, (MeasurableEmbedding.subtype_coe hS).comap_apply,
    withDensity_apply J hUm, Measure.restrict_apply hT, ← hUT]
  symm
  exact hausdorffMeasure_image_eq_lintegral_gram hΩ hUm (hUS.trans hsub) hf hfc hRank (hinj.mono hUS)

/-- **Equation (124)** of [benIsrael2003generalized], Chapter 8.
Integration over the image of a smooth injective immersion uses
normalized Hausdorff measure and the Gram factor in the parameters. -/
theorem integral_areaFormula {Ω S : Set X} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hsub : S ⊆ Ω) {f : X → Y} {f' : X → X →L[ℝ] Y}
    (hf : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) (hfc : ContinuousOn f' Ω)
    (hRank : ∀ x ∈ Ω, Function.Injective (f' x)) (hinj : InjOn f S)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Y → E) :
    ∫ y in f '' S, g y ∂H = ∫ x in S, EuclideanSpace.gram (f' x) • g (f x) := by
  have hCont : ContinuousOn f S := fun x hx => (hf x (hsub hx)).continuousAt.continuousWithinAt
  have hJ : AEMeasurable (fun x => (EuclideanSpace.gram (f' x)).toNNReal) (volume.restrict S) :=
    ((continuous_real_toNNReal.comp continuous_gram).comp_continuousOn (hfc.mono hsub)).aemeasurable hS
  rw [← map_gram_density_eq_hausdorff hΩ hS hsub hf hfc hRank hinj,
    (hCont.measurableEmbedding hS hinj).integral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hS).integral_map, map_comap_subtype_coe hS,
    setIntegral_withDensity_eq_setIntegral_smul₀ hJ _ hS]
  congr with x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (gram_nonneg _)]

/-- **Equations (130), (133)–(134)** of [benIsrael2003generalized], Chapter 8.
The weighted chart measure is exactly normalized Hausdorff measure on
the graph piece. -/
theorem graphMeasure_eq_hausdorff {d : ℕ}
    (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 1 g)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : MeasurableSet U) :
    graphMeasure T g U = (euclideanHausdorffMeasure d (d + 1)).restrict (graphParam T g '' U) := by
  let f := graphParam T g
  have hC : ContDiff ℝ 1 f := contDiff_graphParam hg
  have hdf (u : _) := (hC.differentiable one_ne_zero u).hasFDerivAt
  have hRank (u : _) : Function.Injective (fderiv ℝ f u) :=
    injective_fderiv_graphParam (T := T) (hg.differentiable one_ne_zero u)
  apply Measure.ext
  intro S hS
  have hUS : MeasurableSet (U ∩ f ⁻¹' S) := hU.inter (hC.continuous.measurable hS)
  have hI : f '' (U ∩ f ⁻¹' S) = S ∩ f '' U := by rw [image_inter_preimage, inter_comm]
  have hArea := hausdorffMeasure_image_eq_lintegral_gram isOpen_univ hUS (subset_univ _)
    (fun u _ => hdf u) (hC.continuous_fderiv one_ne_zero).continuousOn (fun u _ => hRank u)
    graphParam_injective.injOn
  rw [graphMeasure_apply hg.continuous U hS, Measure.restrict_apply hS]
  change (∫⁻ u in U ∩ f ⁻¹' S, ENNReal.ofReal (graphDensity g u)) =
    euclideanHausdorffMeasure d (d + 1) (S ∩ f '' U)
  rw [← hI, hArea]
  simp_rw [graphDensity_eq_gram T (hg.differentiable one_ne_zero _)]
  rfl

end SmoothArea

section Parallelogram
open EuclideanSpace InnerProductGeometry

variable {m : ℕ}

private theorem volume_euclideanUnitSquare :
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1} = 1 := by
  let S : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 1)
  have hS : MeasurableSet S := MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  have hs : {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} =
      WithLp.ofLp ⁻¹' S := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  rw [hs, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage hS.nullMeasurableSet]
  simp only [S, volume_pi_pi, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

private theorem gram_two_columns_as_angle (L : EuclideanSpace ℝ (Fin 2) →L[ℝ]
    EuclideanSpace ℝ (Fin m)) :
    let u := L (single 0 1)
    let v := L (single 1 1)
    EuclideanSpace.gram L = ‖u‖ * ‖v‖ * |Real.sin (angle u v)| := by
  dsimp only
  rw [EuclideanSpace.gram, gramDet_eq_det_of_inner, Matrix.det_fin_two]
  simp only [Matrix.of_apply, abs_of_nonneg (sin_angle_nonneg _ _)]
  rw [real_inner_comm (L (single 0 1)) (L (single 1 1))]
  exact (sin_angle_mul_norm_mul_norm _ _).symm.trans (mul_comm _ _)

/-- **Exercise 32**, Equation (147), of [benIsrael2003generalized], Chapter 8.
The geometric area of the parallelogram spanned by the two columns equals
the product of their lengths and the absolute sine of their angle. A zero
off-diagonal Gram entry is exactly preservation of the coordinate right angle. -/
theorem exercise_32_angle_area
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) :
    let u := L (single 0 1)
    let v := L (single 1 1)
    (euclideanHausdorffMeasure 2 m).real (L '' {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}) =
        ‖u‖ * ‖v‖ * |Real.sin (angle u v)| ∧
      (⟪u, v⟫_ℝ = 0 ↔ angle u v = Real.pi / 2) := by
  dsimp only
  refine ⟨?_, inner_eq_zero_iff_angle_eq_pi_div_two _ _⟩
  unfold Measure.real
  rw [hausdorffMeasure_image_linear L hL, volume_euclideanUnitSquare, mul_one,
    gram_two_columns_as_angle]
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)

private theorem expand_two_coordinates (x : EuclideanSpace ℝ (Fin 2)) :
    x = x 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      x 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

/-- **Exercise 32**, after Equation (147), of [benIsrael2003generalized],
Chapter 8. Orthogonal columns with equal lengths give a common positive
length scale in every direction and preserve all angles. -/
theorem exercise_32_isotropic_scaling
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L)
    (horth : ⟪L (single 0 1), L (single 1 1)⟫_ℝ = 0)
    (heq : ‖L (single 0 1)‖ = ‖L (single 1 1)‖) :
    ∃ c : ℝ, 0 < c ∧ (∀ x, ‖L x‖ = c * ‖x‖) ∧
      ∀ x y, angle (L x) (L y) = angle x y := by
  let u := L (single 0 1)
  let v := L (single 1 1)
  let c := ‖u‖
  have hne : u ≠ 0 := by
    intro h
    have hzero := hL (show L (single 0 1) = L 0 by simpa only [map_zero] using h)
    have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hzero
    simp at h1
  have hc : 0 < c := norm_pos_iff.mpr hne
  have huv : ⟪u, v⟫_ℝ = 0 := horth
  have hsym : ⟪v, u⟫_ℝ = 0 := (real_inner_comm u v).trans huv
  have hinner (x y : EuclideanSpace ℝ (Fin 2)) : ⟪L x, L y⟫_ℝ = c ^ 2 * ⟪x, y⟫_ℝ := by
    have hxy : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
      simp [inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]
    have hLx : L x = x 0 • u + x 1 • v := by
      conv_lhs => rw [expand_two_coordinates x, map_add, map_smul, map_smul]
    have hLy : L y = y 0 • u + y 1 • v := by
      conv_lhs => rw [expand_two_coordinates y, map_add, map_smul, map_smul]
    rw [hLx, hLy, hxy]
    have hu : ⟪u, u⟫_ℝ = c ^ 2 := real_inner_self_eq_norm_sq _
    have hv : ⟪v, v⟫_ℝ = c ^ 2 := (real_inner_self_eq_norm_sq _).trans (congrArg (fun r : ℝ => r ^ 2) heq.symm)
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      huv, hsym, hu, hv, mul_zero, zero_add, add_zero]
    ring
  have hdil (x : EuclideanSpace ℝ (Fin 2)) : ‖L x‖ = c * ‖x‖ := by
    have h := hinner x x
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hc.le (norm_nonneg _))).mp (by rw [mul_pow]; exact h)
  refine ⟨c, hc, hdil, fun x y => ?_⟩
  change Real.arccos (⟪L x, L y⟫_ℝ / (‖L x‖ * ‖L y‖)) =
    Real.arccos (⟪x, y⟫_ℝ / (‖x‖ * ‖y‖))
  rw [hinner, hdil, hdil, show c * ‖x‖ * (c * ‖y‖) = c ^ 2 * (‖x‖ * ‖y‖) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc.ne')]

end Parallelogram

section UnitInterceptSimplex
open scoped ENNReal Pointwise BigOperators
open EuclideanSpace

/-- The coordinate simplex of dimension d has nonnegative coordinates with
sum bounded by one. -/
def unitInterceptSimplex (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1}

private theorem measurableSet_unitInterceptSimplex (d : ℕ) :
    MeasurableSet (unitInterceptSimplex d) := by
  have hs : unitInterceptSimplex d =
      (⋂ i : Fin d, {x : EuclideanSpace ℝ (Fin d) | 0 ≤ x i}) ∩ {x | (∑ i, x i) ≤ 1} := by
    ext x
    simp [unitInterceptSimplex]
  rw [hs]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (by fun_prop))
  · exact measurableSet_le (by fun_prop) measurable_const

private theorem simplexSection_eq_smul (d : ℕ) {c : ℝ} (hc : 0 < c) :
    {u : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c} =
      c • unitInterceptSimplex d := by
  ext u
  change (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c ↔ ∃ v ∈ unitInterceptSimplex d, c • v = u
  constructor
  · intro hu
    refine ⟨c⁻¹ • u, ?_, ?_⟩
    · refine ⟨fun i => mul_nonneg (inv_nonneg.mpr hc.le) (hu.1 i), ?_⟩
      change ∑ i, c⁻¹ * u i ≤ 1
      rw [← Finset.mul_sum, ← div_eq_inv_mul, div_le_iff₀ hc, one_mul]
      exact hu.2
    · rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun i => mul_nonneg hc.le (hv.1 i), ?_⟩
    change ∑ i, c * v i ≤ c
    rw [← Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.2 hc.le

/-- The Lebesgue volume of the unit-intercept coordinate simplex is 1/d!.
This includes the zero-dimensional simplex of volume one. -/
theorem volume_unitInterceptSimplex (d : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (unitInterceptSimplex d) =
      ENNReal.ofReal ((d.factorial : ℝ)⁻¹) := by
  induction d with
  | zero =>
    rw [volume_euclideanSpace_eq_dirac, Measure.dirac_apply' _ (measurableSet_unitInterceptSimplex 0)]
    simp [unitInterceptSimplex]
  | succ d ih =>
    let S : Set (ℝ × EuclideanSpace ℝ (Fin d)) :=
      (lastInitEquiv d).symm ⁻¹' unitInterceptSimplex (d + 1)
    have hS : MeasurableSet S :=
      (measurableSet_unitInterceptSimplex (d + 1)).preimage (lastInitEquiv d).symm.measurable
    have hpre : (lastInitEquiv d) ⁻¹' S = unitInterceptSimplex (d + 1) := by
      ext x
      simp [S]
    rw [← hpre, (measurePreserving_lastInit d).measure_preimage hS.nullMeasurableSet]
    change ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))) S = _
    rw [Measure.prod_apply hS]
    have hsect (t : ℝ) : Prod.mk t ⁻¹' S =
        {u : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ u i) ∧ 0 ≤ t ∧ ∑ i, u i ≤ 1 - t} := by
      ext u
      simp only [S, Set.mem_preimage, lastInitEquiv_symm_apply, unitInterceptSimplex,
        Set.mem_ofPred_eq, Fin.forall_fin_succ', Fin.sum_univ_castSucc,
        snocLast_apply_last, snocLast_apply_castSucc]
      rw [le_sub_iff_add_le]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
    let g (t : ℝ) := (1 - t) ^ d * ((d.factorial : ℝ)⁻¹)
    have ha :
        (fun t => volume (Prod.mk t ⁻¹' S)) =ᵐ[volume]
          (Set.Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (g t)) := by
      have hne (z : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ z := by simp [ae_iff]
      filter_upwards [hne 0, hne 1]
        with t h0 h1
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · have hc : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 h1)
        rw [Set.indicator_of_mem ht, hsect]
        have he : {u : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ u i) ∧ 0 ≤ t ∧ ∑ i, u i ≤ 1 - t} =
            (1 - t) • unitInterceptSimplex d := by
          rw [← simplexSection_eq_smul d hc]
          simp [ht.1.le]
        rw [he, Measure.addHaar_smul_of_nonneg volume hc.le, ih, finrank_euclideanSpace,
          Fintype.card_fin, ← ENNReal.ofReal_mul (pow_nonneg hc.le _)]
      · rw [Set.indicator_of_notMem ht, hsect]
        have he : {u : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ u i) ∧ 0 ≤ t ∧ ∑ i, u i ≤ 1 - t} =
            ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro u ⟨hu, ht₀, hsum⟩
          have hnonneg : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu i
          exact ht ⟨lt_of_le_of_ne ht₀ h0.symm, by linarith⟩
        rw [he, measure_empty]
    rw [lintegral_congr_ae ha, lintegral_indicator measurableSet_Ioc]
    have hg : IntervalIntegrable g volume 0 1 := by
      apply Continuous.intervalIntegrable
      dsimp [g]
      fun_prop
    have hg' : Integrable g ((volume : Measure ℝ).restrict (Ioc 0 1)) :=
      hg.1
    have hgn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc 0 1)] g := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (by positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hg' hgn,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
    change (∫ t in (0 : ℝ)..1, (1 - t) ^ d * ((d.factorial : ℝ)⁻¹)) =
      ((d + 1).factorial : ℝ)⁻¹
    rw [intervalIntegral.integral_mul_const,
      show (∫ t in (0 : ℝ)..1, (1 - t) ^ d) = ∫ t in (0 : ℝ)..1, t ^ d by
        simpa only [sub_self, sub_zero] using
          intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ d) (a := 0) (b := 1) 1,
      integral_pow]
    simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
    ring


end UnitInterceptSimplex

section SimplexFacets

open EuclideanSpace
open scoped InnerProductSpace BigOperators

variable {d : ℕ}

/-- The positive-intercept simplex in Equation (160). -/
def interceptSimplex (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ) :
    Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i ≤ a₀}

/-- The upper facet, where the linear bound of the simplex is attained. -/
def interceptSimplexUpperFacet (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ) :
    Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i = a₀}

/-- The coordinate facet with coordinate j equal to zero. -/
def interceptSimplexCoordinateFacet (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ)
    (j : Fin (d + 1)) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  interceptSimplex a a₀ ∩ {x | x j = 0}

/-- Orthogonal projection onto the coordinate plane with coordinate j zero. -/
def simplexFacetProjection (j : Fin (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  x - x j • EuclideanSpace.single j 1

/-- The coordinate projection sets the selected coordinate to zero. -/
@[simp]
theorem simplexFacetProjection_apply (j : Fin (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1)))
    (i : Fin (d + 1)) :
    simplexFacetProjection j x i = if i = j then 0 else x i := by
  by_cases h : i = j
  · subst i
    simp [simplexFacetProjection]
  · simp [simplexFacetProjection, h]

/-- Deleting the jth coordinate maps the upper facet onto the jth coordinate
facet, as in the proof of Exercise 37. -/
theorem simplexFacetProjection_image_upperFacet
    (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ)
    (ha : ∀ i, 0 < a i) (j : Fin (d + 1)) :
    simplexFacetProjection j '' interceptSimplexUpperFacet a a₀ =
      interceptSimplexCoordinateFacet a a₀ j := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hpy (i : Fin (d + 1)) : 0 ≤ simplexFacetProjection j y i := by
      rw [simplexFacetProjection_apply]
      split_ifs with hi
      · exact le_rfl
      · exact hy.1 i
    refine ⟨⟨hpy, ?_⟩, by simp⟩
    rw [← hy.2]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (ha i).le
    rw [simplexFacetProjection_apply]
    split_ifs
    · exact hy.1 i
    · rfl
  · intro hx
    let t := (a₀ - ∑ i, a i * x i) / a j
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1.2) (ha j).le
    let y := x + t • EuclideanSpace.single j 1
    have hy (i : Fin (d + 1)) : y i = x i + if i = j then t else 0 := by
      by_cases hi : i = j
      · subst i
        simp [y]
      · simp [y, hi]
    refine ⟨y, ⟨fun i => ?_, ?_⟩, ?_⟩
    · rw [hy]
      exact add_nonneg (hx.1.1 i) (by split_ifs <;> positivity)
    · have he (i : Fin (d + 1)) :
          a i * y i = a i * x i + if i = j then a j * t else 0 := by
        rw [hy, mul_add]
        split_ifs with hi
        · rw [hi]
        · rw [mul_zero]
      simp only [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      dsimp [t]
      field_simp [(ha j).ne']
      ring
    · ext i
      by_cases hi : i = j
      · subst i
        simpa only [simplexFacetProjection_apply, ite_true] using hx.2.symm
      · rw [simplexFacetProjection_apply, ite_eq_right hi, hy, ite_eq_right hi, add_zero]

private def lastFacetParameter (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i : Fin d, a i.castSucc * u i ≤ a₀}

private theorem weightedSum_snocLast (a : EuclideanSpace ℝ (Fin (d + 1)))
    (u : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ∑ i, a i * snocLast u t i = (∑ i : Fin d, a i.castSucc * u i) + a (Fin.last d) * t := by
  rw [Fin.sum_univ_castSucc]
  simp only [snocLast_apply_castSucc, snocLast_apply_last]

private theorem lastFacetCoordinate_eq_image (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ) :
    interceptSimplexCoordinateFacet a a₀ (Fin.last d) =
      snocLastL (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) '' lastFacetParameter a a₀ := by
  ext x
  constructor
  · intro hx
    have hz : x (Fin.last d) = 0 := hx.2
    have hsnoc : snocLast (init x) 0 = x := by
      rw [← hz, snocLast_init_last]
    refine ⟨init x, ⟨fun i => hx.1.1 i.castSucc, ?_⟩, ?_⟩
    · have hs := hx.1.2
      change (∑ i, a i * x i) ≤ a₀ at hs
      rw [← hsnoc, weightedSum_snocLast, mul_zero, add_zero] at hs
      exact hs
    · simpa only [snocLastL_apply, zero_apply] using hsnoc
  · rintro ⟨u, hu, rfl⟩
    change ((∀ i, 0 ≤ snocLast u 0 i) ∧ ∑ i, a i * snocLast u 0 i ≤ a₀) ∧
      snocLast u 0 (Fin.last d) = 0
    refine ⟨⟨?_, ?_⟩, snocLast_apply_last _ _⟩
    · simp only [Fin.forall_fin_succ', snocLast_apply_castSucc, snocLast_apply_last]
      exact ⟨hu.1, le_rfl⟩
    · rw [weightedSum_snocLast, mul_zero, add_zero]
      exact hu.2

private def slopeLastFacet (a : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ _ (-(a (Fin.last d))⁻¹ • init a)

private theorem slopeLastFacet_apply (a : EuclideanSpace ℝ (Fin (d + 1)))
    (u : EuclideanSpace ℝ (Fin d)) :
    slopeLastFacet a u = -(∑ i : Fin d, a i.castSucc * u i) / a (Fin.last d) := by
  change ⟪-(a (Fin.last d))⁻¹ • init a, u⟫_ℝ = _
  rw [real_inner_smul_left]
  have h : ⟪init a, u⟫_ℝ = ∑ i : Fin d, a i.castSucc * u i := by
    simp only [inner_eq_star_dotProduct, star_trivial, dotProduct]
    exact Finset.sum_congr rfl (fun i _ => mul_comm (u i) (a i.castSucc))
  rw [h]
  ring

private theorem lastFacetUpper_eq_image (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ)
    (ha : 0 < a (Fin.last d)) :
    interceptSimplexUpperFacet a a₀ =
      (fun x : EuclideanSpace ℝ (Fin (d + 1)) => x + snocLast 0 (a₀ / a (Fin.last d))) ''
        (snocLastL (slopeLastFacet a) '' lastFacetParameter a a₀) := by
  let p := snocLast (0 : EuclideanSpace ℝ (Fin d)) (a₀ / a (Fin.last d))
  have hp (u : EuclideanSpace ℝ (Fin d)) :
      snocLastL (slopeLastFacet a) u + p =
        snocLast u ((a₀ - ∑ i : Fin d, a i.castSucc * u i) / a (Fin.last d)) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [PiLp.add_apply, snocLastL_apply, snocLast_apply_last, p, slopeLastFacet_apply]
      ring
    · simp [p, snocLastL_apply]
  ext x
  constructor
  · intro hx
    let u := init x
    have hsum := hx.2
    change ∑ i, a i * x i = a₀ at hsum
    rw [← snocLast_init_last x, weightedSum_snocLast] at hsum
    have hlast : (a₀ - ∑ i : Fin d, a i.castSucc * u i) / a (Fin.last d) = x (Fin.last d) := by
      apply (div_eq_iff ha.ne').2
      dsimp only [u]
      linarith only [hsum]
    refine ⟨snocLastL (slopeLastFacet a) u, ⟨u, ⟨fun i => hx.1 i.castSucc, ?_⟩, rfl⟩, ?_⟩
    · dsimp only [u]
      linarith only [hsum, mul_nonneg ha.le (hx.1 (Fin.last d))]
    · change snocLastL (slopeLastFacet a) u + p = x
      rw [hp, hlast]
      exact snocLast_init_last x
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    change snocLastL (slopeLastFacet a) u + p ∈ _
    rw [hp]
    change (∀ i, 0 ≤ snocLast u _ i) ∧ ∑ i, a i * snocLast u _ i = a₀
    refine ⟨?_, ?_⟩
    · simp only [Fin.forall_fin_succ', snocLast_apply_castSucc, snocLast_apply_last]
      exact ⟨hu.1, div_nonneg (sub_nonneg.mpr hu.2) ha.le⟩
    · rw [weightedSum_snocLast]
      field_simp [ha.ne']
      ring

private theorem euclideanHausdorffMeasure_image_self {m k : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)} (hf : Isometry f)
    (S : Set (EuclideanSpace ℝ (Fin m))) :
    euclideanHausdorffMeasure k m (f '' S) = euclideanHausdorffMeasure k m S := by
  simp only [euclideanHausdorffMeasure, Measure.smul_apply]
  rw [hf.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg k))]

private theorem snocLastL_injective (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    Function.Injective (snocLastL ℓ) := by
  intro x y h
  simpa only [snocLastL_apply, init_snocLast] using congrArg init h

private theorem measure_lastCoordinateFacet (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ) :
    euclideanHausdorffMeasure d (d + 1) (interceptSimplexCoordinateFacet a a₀ (Fin.last d)) =
      volume (lastFacetParameter a a₀) := by
  rw [lastFacetCoordinate_eq_image, hausdorffMeasure_image_linear _ (snocLastL_injective _),
    gram_snocLastL, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_one,
    ENNReal.ofReal_one, one_mul]

private theorem area_lastFacet_ratio (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ)
    (ha : 0 < a (Fin.last d)) :
    (euclideanHausdorffMeasure d (d + 1)).real (interceptSimplexUpperFacet a a₀) =
      (‖a‖ / a (Fin.last d)) *
        (euclideanHausdorffMeasure d (d + 1)).real
          (interceptSimplexCoordinateFacet a a₀ (Fin.last d)) := by
  have h𝓁 : ‖slopeLastFacet a‖ = ‖init a‖ / a (Fin.last d) := by
    rw [slopeLastFacet, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_inv, abs_of_pos ha, div_eq_mul_inv, mul_comm]
  have hnorm : ‖a‖ ^ 2 = ‖init a‖ ^ 2 + (a (Fin.last d)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    rfl
  have hgram : EuclideanSpace.gram (snocLastL (slopeLastFacet a)) = ‖a‖ / a (Fin.last d) := by
    rw [gram_snocLastL, h𝓁, ← Real.sqrt_sq (div_nonneg (norm_nonneg a) ha.le)]
    congr 1
    field_simp [ha.ne']
    linarith only [hnorm]
  have hiso : Isometry (fun x : EuclideanSpace ℝ (Fin (d + 1)) =>
      x + snocLast 0 (a₀ / a (Fin.last d))) :=
    (IsometryEquiv.vaddConst (V := EuclideanSpace ℝ (Fin (d + 1)))
      (snocLast 0 (a₀ / a (Fin.last d)))).isometry
  unfold Measure.real
  rw [lastFacetUpper_eq_image a a₀ ha, euclideanHausdorffMeasure_image_self hiso,
    hausdorffMeasure_image_linear _ (snocLastL_injective _), measure_lastCoordinateFacet,
    hgram, ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (norm_nonneg a) ha.le)]

private def facetSwap (j : Fin (d + 1)) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap j (Fin.last d))

private theorem facetSwap_apply (j : Fin (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1)))
    (i : Fin (d + 1)) : facetSwap j x i = x ((Equiv.swap j (Fin.last d)).symm i) := rfl

private theorem facetSwap_images
    (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ) (j : Fin (d + 1)) :
    (facetSwap j '' interceptSimplexUpperFacet a a₀ =
      interceptSimplexUpperFacet (facetSwap j a) a₀) ∧
    (facetSwap j '' interceptSimplexCoordinateFacet a a₀ j =
      interceptSimplexCoordinateFacet (facetSwap j a) a₀ (Fin.last d)) := by
  let e := Equiv.swap j (Fin.last d)
  let E := facetSwap j
  have he (x : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin (d + 1)) : E x i = x (e.symm i) :=
    facetSwap_apply j x i
  have hn (x : EuclideanSpace ℝ (Fin (d + 1))) :
      (∀ i, 0 ≤ E x i) ↔ (∀ i, 0 ≤ x i) := by
    constructor
    · intro h i
      simpa only [he, Equiv.symm_apply_apply] using h (e i)
    · intro h i
      rw [he]
      exact h _
  have hs (x : EuclideanSpace ℝ (Fin (d + 1))) :
      ∑ i, E a i * E x i = ∑ i, a i * x i := by
    simp_rw [he]
    exact Equiv.sum_comp e.symm (fun i => a i * x i)
  have hl (x : EuclideanSpace ℝ (Fin (d + 1))) : E x (Fin.last d) = x j := by
    rw [he, show e.symm (Fin.last d) = j by simp [e]]
  have himage (S T : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (h : ∀ x, E x ∈ T ↔ x ∈ S) : E '' S = T := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    exact ⟨fun ⟨z, hz, hz'⟩ => (h x).2 (E.injective hz' ▸ hz), fun hy => ⟨x, (h x).1 hy, rfl⟩⟩
  constructor
  · apply himage
    intro x
    change ((∀ i, 0 ≤ E x i) ∧ ∑ i, E a i * E x i = a₀) ↔ _
    rw [hn, hs]
    rfl
  · apply himage
    intro x
    change (((∀ i, 0 ≤ E x i) ∧ ∑ i, E a i * E x i ≤ a₀) ∧ E x (Fin.last d) = 0) ↔ _
    rw [hn, hs, hl]
    rfl

/-- **Exercise 37**, Equations (162)–(163), of [benIsrael2003generalized],
Chapter 8. The upper facet's area is the coordinate facet's area times the
ratio of the normal's length to the selected coordinate. The squared upper
area is the sum of the squared coordinate facet areas. -/
theorem exercise_37_simplex_facet_areas
    (a : EuclideanSpace ℝ (Fin (d + 1))) (a₀ : ℝ) (ha : ∀ i, 0 < a i) (_ha₀ : 0 < a₀) :
    let H := (euclideanHausdorffMeasure d (d + 1)).real
    let A₀ := H (interceptSimplexUpperFacet a a₀)
    let A := fun j => H (interceptSimplexCoordinateFacet a a₀ j)
    (∀ j, A₀ = (‖a‖ / a j) * A j) ∧ A₀ ^ 2 = ∑ j, (A j) ^ 2 := by
  dsimp only
  let H := (euclideanHausdorffMeasure d (d + 1)).real
  let A₀ := H (interceptSimplexUpperFacet a a₀)
  let A := fun j => H (interceptSimplexCoordinateFacet a a₀ j)
  change (∀ j, A₀ = (‖a‖ / a j) * A j) ∧ A₀ ^ 2 = ∑ j, (A j) ^ 2
  have hratio (j : Fin (d + 1)) : A₀ = (‖a‖ / a j) * A j := by
    let E := facetSwap j
    have hE : (E a) (Fin.last d) = a j := by rw [facetSwap_apply, Equiv.symm_swap, Equiv.swap_apply_right]
    obtain ⟨hup, hcoord⟩ := facetSwap_images a a₀ j
    have h := area_lastFacet_ratio (E a) a₀ (hE ▸ ha j)
    rw [hE, E.norm_map, ← hup, ← hcoord] at h
    unfold Measure.real at h
    rw [euclideanHausdorffMeasure_image_self E.isometry,
      euclideanHausdorffMeasure_image_self E.isometry] at h
    exact h
  refine ⟨hratio, ?_⟩
  have hnorm : ‖a‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact fun h => (ha (Fin.last d)).ne' (congrArg (fun x : EuclideanSpace ℝ (Fin (d + 1)) =>
      x (Fin.last d)) h)
  have hA (j : Fin (d + 1)) : A j = A₀ * a j / ‖a‖ := by
    rw [hratio j]
    field_simp [(ha j).ne', hnorm]
  simp_rw [hA, div_pow, mul_pow]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq,
    mul_div_cancel_right₀ _ (pow_ne_zero 2 hnorm)]

/-- **Exercise 38** of [benIsrael2003generalized], Chapter 8. The coordinate
facets of the unit-intercept simplex have area 1/d!, and the upper facet has
area √(d+1)/d!. -/
theorem exercise_38_simplex_facet_areas (d : ℕ) :
    let a : EuclideanSpace ℝ (Fin (d + 1)) := WithLp.toLp 2 fun _ => 1
    let H := (euclideanHausdorffMeasure d (d + 1)).real
    (∀ j, H (interceptSimplexCoordinateFacet a 1 j) = ((d.factorial : ℝ)⁻¹)) ∧
      H (interceptSimplexUpperFacet a 1) = Real.sqrt (d + 1) / (d.factorial : ℝ) := by
  dsimp only
  let a : EuclideanSpace ℝ (Fin (d + 1)) := WithLp.toLp 2 fun _ => 1
  let H := (euclideanHausdorffMeasure d (d + 1)).real
  have hcoord (j : Fin (d + 1)) : H (interceptSimplexCoordinateFacet a 1 j) = ((d.factorial : ℝ)⁻¹) := by
    let E := facetSwap j
    have he : E a = a := by
      ext i
      rfl
    have hm := (facetSwap_images a 1 j).2
    rw [he] at hm
    unfold H Measure.real
    rw [← euclideanHausdorffMeasure_image_self (facetSwap j).isometry, hm, measure_lastCoordinateFacet]
    have hP : lastFacetParameter a 1 = unitInterceptSimplex d := by
      ext u
      simp [lastFacetParameter, unitInterceptSimplex, a]
    rw [hP, volume_unitInterceptSimplex, ENNReal.toReal_ofReal (by positivity)]
  refine ⟨hcoord, ?_⟩
  have h := (exercise_37_simplex_facet_areas a 1 (fun _ => zero_lt_one) zero_lt_one).1 (Fin.last d)
  change H (interceptSimplexUpperFacet a 1) =
    ‖a‖ / a (Fin.last d) * H (interceptSimplexCoordinateFacet a 1 (Fin.last d)) at h
  change H (interceptSimplexUpperFacet a 1) = _
  rw [h, hcoord (Fin.last d)]
  have hnorm : ‖a‖ = Real.sqrt (d + 1) := by
    rw [EuclideanSpace.norm_eq]
    simp [a, Nat.cast_add]
  rw [hnorm]
  change Real.sqrt (d + 1) / 1 * ((d.factorial : ℝ)⁻¹) = _
  rw [div_one, div_eq_mul_inv]

end SimplexFacets

section ArcIntegrals

open EuclideanSpace
open scoped BigOperators InnerProductSpace

variable {m : ℕ}

local notation "X₁" => EuclideanSpace ℝ (Fin 1)
local notation "Y" => EuclideanSpace ℝ (Fin m)
local notation "p₀₁" => EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)

private theorem gram_curveDerivative (v : Y) :
    EuclideanSpace.gram ((p₀₁).smulRight v) = ‖v‖ := by
  rw [EuclideanSpace.gram, gramDet_eq_det_of_inner, Matrix.det_fin_one, Matrix.of_apply]
  have he : p₀₁ (EuclideanSpace.single 0 1) = 1 := by simp
  simp only [ContinuousLinearMap.smulRight_apply, he, one_smul, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg v)]

/-- **Exercise 33**, Equation (149), of [benIsrael2003generalized], Chapter 8.
The scalar line integral over a regular injective arc has the speed factor.
The same formula applies to any nonreversed compact parameter interval. -/
theorem exercise_33_line_integral {φ : ℝ → Y} (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b)
    (hregular : ∀ t ∈ Icc a b, deriv φ t ≠ 0)
    (hinj : InjOn φ (Icc a b)) (f : Y → ℝ) :
    (∫ x in φ '' Icc a b, f x ∂(euclideanHausdorffMeasure 1 m)) =
      ∫ t in a..b, f (φ t) * Real.sqrt (∑ i, (deriv φ t i)^2) := by
  let e : X₁ ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have he (x : X₁) : e x = x 0 := rfl
  have hevol : MeasurePreserving e volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))
  let ψ : X₁ → Y := fun x => φ (x 0)
  let S : Set X₁ := e ⁻¹' Icc a b
  let Ω : Set X₁ := {x | deriv φ (x 0) ≠ 0}
  have hc : ContDiff ℝ 1 ψ := hφ.comp (p₀₁).contDiff
  have hDiff := hc.differentiable one_ne_zero
  have hΩ : IsOpen Ω := isOpen_ne.preimage (hφ.continuous_deriv_one.comp (p₀₁).continuous)
  have hS : MeasurableSet S := e.measurable measurableSet_Icc
  have hsub : S ⊆ Ω := fun x hx => hregular (e x) hx
  have hinj' : InjOn ψ S := by
    intro x hx y hy hxy
    exact e.injective (hinj hx hy hxy)
  have himg : ψ '' S = φ '' Icc a b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, hx, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, by simpa only [S, Set.mem_preimage, e.apply_symm_apply] using ht,
        congrArg φ (e.apply_symm_apply t)⟩
  have hderiv (x : X₁) : fderiv ℝ ψ x = (p₀₁).smulRight (deriv φ (x 0)) := by
    have hp : HasFDerivAt (fun v : X₁ => v 0) p₀₁ x := (p₀₁).hasFDerivAt
    have h := (hφ.differentiable one_ne_zero (x 0)).hasDerivAt.hasFDerivAt.comp x hp
    change fderiv ℝ (φ ∘ fun v : X₁ => v 0) x = _
    rw [h.fderiv]
    ext v
    rfl
  have hRank (x : X₁) (hx : x ∈ Ω) : Function.Injective (fderiv ℝ ψ x) := by
    rw [hderiv]
    intro y z hyz
    have heq : y 0 = z 0 := by
      change y 0 • deriv φ (x 0) = z 0 • deriv φ (x 0) at hyz
      exact (smul_left_injective ℝ (show deriv φ (x 0) ≠ 0 from hx)) hyz
    apply e.injective
    exact heq
  rw [← himg, integral_areaFormula hΩ hS hsub (fun x _ => (hDiff x).hasFDerivAt)
    (hc.continuous_fderiv one_ne_zero).continuousOn hRank hinj' f]
  simp_rw [hderiv, gram_curveDerivative, smul_eq_mul]
  have hnorm (t : ℝ) : ‖deriv φ t‖ = Real.sqrt (∑ i, (deriv φ t i)^2) := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm]
  rw [intervalIntegral.integral_of_le hab, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have ht := hevol.setIntegral_preimage_emb e.measurableEmbedding
    (fun t : ℝ => f (φ t) * Real.sqrt (∑ i, (deriv φ t i)^2)) (Icc a b)
  simpa only [he, ψ, S, mul_comm] using ht

/-- **Exercise 33**, Equation (150), of [benIsrael2003generalized], Chapter 8.
A regular injective arc's geometric length equals the speed integral. -/
theorem exercise_33_arc_length {φ : ℝ → Y} (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b)
    (hregular : ∀ t ∈ Icc a b, deriv φ t ≠ 0) (hinj : InjOn φ (Icc a b)) :
    (euclideanHausdorffMeasure 1 m).real (φ '' Icc a b) =
      ∫ t in a..b, Real.sqrt (∑ i, (deriv φ t i)^2) := by
  simpa only [setIntegral_const, smul_eq_mul, mul_one, one_mul] using
    exercise_33_line_integral hφ hab hregular hinj (fun _ => 1)

/-- **Exercise 33**, after Equation (150), of [benIsrael2003generalized],
Chapter 8. Taking one coordinate as the parameter yields the graph formula.
The parameter is placed in the final coordinate. -/
theorem exercise_33_graph_arc_length {d : ℕ}
    (g : ℝ → EuclideanSpace ℝ (Fin d)) (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a ≤ b) :
    (euclideanHausdorffMeasure 1 (d + 1)).real ((fun t => snocLast (g t) t) '' Icc a b) =
      ∫ t in a..b, Real.sqrt (1 + ∑ i, (deriv g t i)^2) := by
  let φ : ℝ → EuclideanSpace ℝ (Fin (d + 1)) := fun t => snocLast (g t) t
  have hcomp : φ = ((lastInitL d).symm : ℝ × EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1))) ∘ (fun t => (t, g t)) := rfl
  have hc : ContDiff ℝ 1 φ := by
    rw [hcomp]
    exact ((lastInitL d).symm : ℝ × EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1))).contDiff.comp (contDiff_id.prodMk hg)
  have hderiv (t : ℝ) : deriv φ t = snocLast (deriv g t) 1 := by
    have h := (((lastInitL d).symm : ℝ × EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1))).hasFDerivAt (x := (t, g t))).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hg.differentiable one_ne_zero t).hasDerivAt)
    rw [hcomp]
    exact h.deriv
  have hreg (t : ℝ) (_ht : t ∈ Icc a b) : deriv φ t ≠ 0 := by
    rw [hderiv]
    intro h
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin (d + 1)) => x (Fin.last d)) h
    simp at he
  have hinj : InjOn φ (Icc a b) := by
    intro x _ y _ h
    have he := congrArg (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) h
    simpa [φ] using he
  rw [exercise_33_arc_length hc hab hreg hinj]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [hderiv, Fin.sum_univ_castSucc]
  simp only [snocLast_apply_castSucc, snocLast_apply_last, one_pow, add_comm]

end ArcIntegrals

section ChartDerivatives

open EuclideanSpace

local notation "X₂" => EuclideanSpace ℝ (Fin 2)
local notation "X₃" => EuclideanSpace ℝ (Fin 3)
local notation "e₀" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e₁" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
local notation "p₀" => EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
local notation "p₁" => EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)

private def chartVector (x y z : ℝ) : X₃ :=
  x • EuclideanSpace.single 0 1 + y • EuclideanSpace.single 1 1 + z • EuclideanSpace.single 2 1

private def chartDerivative (L₀ L₁ L₂ : X₂ →L[ℝ] ℝ) : X₂ →L[ℝ] X₃ :=
  L₀.smulRight (EuclideanSpace.single 0 1) + L₁.smulRight (EuclideanSpace.single 1 1) +
    L₂.smulRight (EuclideanSpace.single 2 1)

private theorem hasFDerivAt_chartVector {x y z : X₂ → ℝ} {L₀ L₁ L₂ : X₂ →L[ℝ] ℝ}
    {u : X₂} (hx : HasFDerivAt x L₀ u) (hy : HasFDerivAt y L₁ u)
    (hz : HasFDerivAt z L₂ u) :
    HasFDerivAt (fun v => chartVector (x v) (y v) (z v)) (chartDerivative L₀ L₁ L₂) u :=
  ((hx.smul_const _).add (hy.smul_const _)).add (hz.smul_const _)

private theorem chartDerivative_matrix (L₀ L₁ L₂ : X₂ →L[ℝ] ℝ) :
    stdMatrix (chartDerivative L₀ L₁ L₂) =
      !![L₀ e₀, L₀ e₁; L₁ e₀, L₁ e₁; L₂ e₀, L₂ e₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stdMatrix_apply, chartDerivative, ContinuousLinearMap.smulRight_apply]

private theorem gram_formula_two_columns (L : X₂ →L[ℝ] X₃) :
    let A := stdMatrix L
    EuclideanSpace.gram L = Real.sqrt
      ((∑ i, (A i 0)^2) * (∑ i, (A i 1)^2) - (∑ i, A i 0 * A i 1)^2) := by
  dsimp only
  rw [EuclideanSpace.gram, gramDet, Matrix.det_fin_two]
  congr 1
  let A := stdMatrix L
  change (∑ i, A i 0 * A i 0) * (∑ i, A i 1 * A i 1) -
      (∑ i, A i 0 * A i 1) * (∑ i, A i 1 * A i 0) = _
  have h : (∑ i, A i 1 * A i 0) = ∑ i, A i 0 * A i 1 :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [h, ← pow_two]
  simp only [pow_two]
  rfl

private theorem injective_of_gram_pos {n m : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (h : 0 < EuclideanSpace.gram L) : Function.Injective L := by
  let A := stdMatrix L
  have hp : 0 < (Aᵀ * A).det := Real.sqrt_pos.mp h
  have hmul : Function.Injective ((Aᵀ * A).mulVec) :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hp.ne'))
  have hL : A.toEuclideanLin = L.toLinearMap := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.toLin_toMatrix _ _ _
  intro x y hxy
  have hxy' : A *ᵥ WithLp.ofLp x = A *ᵥ WithLp.ofLp y := by
    have he : Matrix.toEuclideanLin A x = Matrix.toEuclideanLin A y := by rwa [hL]
    exact congrArg WithLp.ofLp he
  have hxy'' := congrArg ((Aᵀ).mulVec) hxy'
  simp only [Matrix.mulVec_mulVec] at hxy''
  exact (WithLp.ofLp_injective 2) (hmul hxy'')

/-- **Equations (151)–(152)** of [benIsrael2003generalized], Chapter 8.
The graph of a height given as a function of radius and azimuth. -/
def cylindricalSurfaceChart (z : X₂ → ℝ) (u : X₂) : X₃ :=
  chartVector (u 0 * Real.cos (u 1)) (u 0 * Real.sin (u 1)) (z u)

private def cylindricalSurfaceDerivative (z : X₂ → ℝ) (u : X₂) : X₂ →L[ℝ] X₃ :=
  chartDerivative
    (Real.cos (u 1) • p₀ - (u 0 * Real.sin (u 1)) • p₁)
    (Real.sin (u 1) • p₀ + (u 0 * Real.cos (u 1)) • p₁)
    (fderiv ℝ z u)

/-- **Exercise 34**, Equation (153), of [benIsrael2003generalized], Chapter 8.
The cylindrical chart has the stated three coordinate derivatives. -/
theorem exercise_34_surface_jacobian {z : X₂ → ℝ} {u : X₂} (hz : DifferentiableAt ℝ z u) :
    jacobian (cylindricalSurfaceChart z) u =
      !![Real.cos (u 1), -u 0 * Real.sin (u 1);
        Real.sin (u 1), u 0 * Real.cos (u 1);
        fderiv ℝ z u e₀, fderiv ℝ z u e₁] := by
  have h₀ := (proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := u)
  have h₁ := (proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := u)
  have hx : HasFDerivAt (fun v : X₂ => v 0 * Real.cos (v 1))
      (Real.cos (u 1) • p₀ - (u 0 * Real.sin (u 1)) • p₁) u := by
    convert h₀.mul h₁.cos using 1 <;> try rfl
    change Real.cos (u 1) • p₀ - (u 0 * Real.sin (u 1)) • p₁ =
      u 0 • ((-Real.sin (u 1)) • p₁) + Real.cos (u 1) • p₀
    module
  have hy : HasFDerivAt (fun v : X₂ => v 0 * Real.sin (v 1))
      (Real.sin (u 1) • p₀ + (u 0 * Real.cos (u 1)) • p₁) u := by
    convert h₀.mul h₁.sin using 1 <;> try rfl
    change Real.sin (u 1) • p₀ + (u 0 * Real.cos (u 1)) • p₁ =
      u 0 • (Real.cos (u 1) • p₁) + Real.sin (u 1) • p₀
    module
  have hD : HasFDerivAt (cylindricalSurfaceChart z) (cylindricalSurfaceDerivative z u) u :=
    hasFDerivAt_chartVector hx hy hz.hasFDerivAt
  change stdMatrix (fderiv ℝ (cylindricalSurfaceChart z) u) = _
  rw [hD.fderiv, cylindricalSurfaceDerivative, chartDerivative_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neg_mul]

/-- **Exercise 34**, Equation (154), of [benIsrael2003generalized], Chapter 8.
The cylindrical graph surface element, expressed without division by radius. -/
theorem exercise_34_surface_density {z : X₂ → ℝ} {u : X₂}
    (hz : DifferentiableAt ℝ z u) :
    EuclideanSpace.gram (fderiv ℝ (cylindricalSurfaceChart z) u) =
      Real.sqrt ((u 0)^2 + (u 0)^2 * (fderiv ℝ z u e₀)^2 + (fderiv ℝ z u e₁)^2) := by
  rw [gram_formula_two_columns]
  have hM := exercise_34_surface_jacobian hz
  change stdMatrix (fderiv ℝ (cylindricalSurfaceChart z) u) = _ at hM
  rw [hM]
  congr 1
  simp only [Fin.sum_univ_three]
  let r := u 0
  let θ := u 1
  let a := fderiv ℝ z u e₀
  let b := fderiv ℝ z u e₁
  change (Real.cos θ ^ 2 + Real.sin θ ^ 2 + a ^ 2) *
      ((-r * Real.sin θ) ^ 2 + (r * Real.cos θ) ^ 2 + b ^ 2) -
      (Real.cos θ * (-r * Real.sin θ) + Real.sin θ * (r * Real.cos θ) + a * b) ^ 2 =
    r ^ 2 + r ^ 2 * a ^ 2 + b ^ 2
  linear_combination (r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2 + 1 + a ^ 2) + b ^ 2) *
    Real.sin_sq_add_cos_sq θ

private theorem hasFDerivAt_comp_radius {z : ℝ → ℝ} {u : X₂}
    (hz : DifferentiableAt ℝ z (u 0)) :
    HasFDerivAt (fun v : X₂ => z (v 0)) (deriv z (u 0) • p₀) u := by
  have hp : HasFDerivAt (fun v : X₂ => v 0) p₀ u := (p₀).hasFDerivAt
  have h := hz.hasDerivAt.comp_hasFDerivAt u hp
  exact h

/-- **Exercise 35**, Equation (156), of [benIsrael2003generalized], Chapter 8.
The azimuth derivative of a radial height vanishes in the chart's surface element. -/
theorem exercise_35_surface_density {z : ℝ → ℝ} {u : X₂}
    (hz : DifferentiableAt ℝ z (u 0)) (hr : 0 ≤ u 0) :
    EuclideanSpace.gram (fderiv ℝ (cylindricalSurfaceChart (fun v => z (v 0))) u) =
      u 0 * Real.sqrt (1 + (deriv z (u 0))^2) := by
  have h := hasFDerivAt_comp_radius hz
  rw [exercise_34_surface_density h.differentiableAt, h.fderiv]
  have he₀ : (deriv z (u 0) • p₀) e₀ = deriv z (u 0) := by simp
  have he₁ : (deriv z (u 0) • p₀) e₁ = 0 := by simp
  rw [he₀, he₁]
  have harg : (u 0)^2 + (u 0)^2 * (deriv z (u 0))^2 + (0 : ℝ)^2 =
      (u 0)^2 * (1 + (deriv z (u 0))^2) := by ring
  rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr]

/-- **Equations (157)–(158)** of [benIsrael2003generalized], Chapter 8.
The spherical surface chart for a radius depending on the polar angle. -/
def sphericalSurfaceChart (ρ : ℝ → ℝ) (u : X₂) : X₃ :=
  chartVector (ρ (u 0) * Real.sin (u 0) * Real.cos (u 1))
    (ρ (u 0) * Real.sin (u 0) * Real.sin (u 1)) (ρ (u 0) * Real.cos (u 0))

private def sphericalSurfaceDerivative (ρ : ℝ → ℝ) (u : X₂) : X₂ →L[ℝ] X₃ :=
  let a := deriv ρ (u 0) * Real.sin (u 0) + ρ (u 0) * Real.cos (u 0)
  let r := ρ (u 0) * Real.sin (u 0)
  chartDerivative
    ((a * Real.cos (u 1)) • p₀ - (r * Real.sin (u 1)) • p₁)
    ((a * Real.sin (u 1)) • p₀ + (r * Real.cos (u 1)) • p₁)
    ((deriv ρ (u 0) * Real.cos (u 0) - ρ (u 0) * Real.sin (u 0)) • p₀)

/-- **Exercise 36**, Equations (157)–(159), of [benIsrael2003generalized],
Chapter 8. The two columns of the displayed spherical Jacobian are the
derivatives of the actual chart. -/
theorem exercise_36_surface_jacobian {ρ : ℝ → ℝ} {u : X₂}
    (hρ : DifferentiableAt ℝ ρ (u 0)) :
    jacobian (sphericalSurfaceChart ρ) u =
      sphericalJacobian (ρ (u 0)) (deriv ρ (u 0)) (u 0) (u 1) := by
  let a := deriv ρ (u 0) * Real.sin (u 0) + ρ (u 0) * Real.cos (u 0)
  let r := ρ (u 0) * Real.sin (u 0)
  have h₀ := (p₀).hasFDerivAt (x := u)
  have h₁ := (p₁).hasFDerivAt (x := u)
  have hρ' := hasFDerivAt_comp_radius hρ
  have hq : HasFDerivAt (fun v : X₂ => ρ (v 0) * Real.sin (v 0)) (a • p₀) u := by
    convert hρ'.mul h₀.sin using 1 <;> try rfl
    change a • p₀ = ρ (u 0) • (Real.cos (u 0) • p₀) +
      Real.sin (u 0) • (deriv ρ (u 0) • p₀)
    dsimp only [a]
    module
  have hx : HasFDerivAt (fun v : X₂ => ρ (v 0) * Real.sin (v 0) * Real.cos (v 1))
      ((a * Real.cos (u 1)) • p₀ - (r * Real.sin (u 1)) • p₁) u := by
    convert hq.mul h₁.cos using 1 <;> try rfl
    change (a * Real.cos (u 1)) • p₀ - (r * Real.sin (u 1)) • p₁ =
      r • ((-Real.sin (u 1)) • p₁) + Real.cos (u 1) • (a • p₀)
    module
  have hy : HasFDerivAt (fun v : X₂ => ρ (v 0) * Real.sin (v 0) * Real.sin (v 1))
      ((a * Real.sin (u 1)) • p₀ + (r * Real.cos (u 1)) • p₁) u := by
    convert hq.mul h₁.sin using 1 <;> try rfl
    change (a * Real.sin (u 1)) • p₀ + (r * Real.cos (u 1)) • p₁ =
      r • (Real.cos (u 1) • p₁) + Real.sin (u 1) • (a • p₀)
    module
  have hz : HasFDerivAt (fun v : X₂ => ρ (v 0) * Real.cos (v 0))
      ((deriv ρ (u 0) * Real.cos (u 0) - ρ (u 0) * Real.sin (u 0)) • p₀) u := by
    convert hρ'.mul h₀.cos using 1 <;> try rfl
    change (deriv ρ (u 0) * Real.cos (u 0) - ρ (u 0) * Real.sin (u 0)) • p₀ =
      ρ (u 0) • ((-Real.sin (u 0)) • p₀) + Real.cos (u 0) • (deriv ρ (u 0) • p₀)
    module
  have hD : HasFDerivAt (sphericalSurfaceChart ρ) (sphericalSurfaceDerivative ρ u) u :=
    hasFDerivAt_chartVector hx hy hz
  change stdMatrix (fderiv ℝ (sphericalSurfaceChart ρ) u) = _
  rw [hD.fderiv, sphericalSurfaceDerivative, chartDerivative_matrix, sphericalJacobian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neg_mul]

/-- **Exercise 36**, Equation (159a), of [benIsrael2003generalized], Chapter 8.
The surface element of the stated spherical chart on the physical range. -/
theorem exercise_36_surface_density {ρ : ℝ → ℝ} {u : X₂}
    (hρ : DifferentiableAt ℝ ρ (u 0)) (hr : 0 ≤ ρ (u 0)) (hφ : 0 ≤ Real.sin (u 0)) :
    EuclideanSpace.gram (fderiv ℝ (sphericalSurfaceChart ρ) u) =
      ρ (u 0) * Real.sqrt ((ρ (u 0))^2 + (deriv ρ (u 0))^2) * Real.sin (u 0) := by
  rw [gram_formula_two_columns]
  have hM := exercise_36_surface_jacobian hρ
  change stdMatrix (fderiv ℝ (sphericalSurfaceChart ρ) u) = _ at hM
  rw [hM]
  let r := ρ (u 0)
  let a := deriv ρ (u 0)
  let φ := u 0
  let θ := u 1
  let q := a * Real.sin φ + r * Real.cos φ
  let z := a * Real.cos φ - r * Real.sin φ
  let t := r * Real.sin φ
  have harg : ((q * Real.cos θ) ^ 2 + (q * Real.sin θ) ^ 2 + z ^ 2) *
        ((-t * Real.sin θ) ^ 2 + (t * Real.cos θ) ^ 2 + (0 : ℝ) ^ 2) -
        (q * Real.cos θ * (-t * Real.sin θ) + q * Real.sin θ * (t * Real.cos θ) + z * 0) ^ 2 =
      t ^ 2 * (r ^ 2 + a ^ 2) := by
    have hE : (q * Real.cos θ) ^ 2 + (q * Real.sin θ) ^ 2 + z ^ 2 = r ^ 2 + a ^ 2 := by
      dsimp [q, z]
      linear_combination (a * Real.sin φ + r * Real.cos φ) ^ 2 * Real.sin_sq_add_cos_sq θ +
        (a ^ 2 + r ^ 2) * Real.sin_sq_add_cos_sq φ
    rw [hE]
    linear_combination (r ^ 2 + a ^ 2) * t ^ 2 * Real.sin_sq_add_cos_sq θ
  simp only [Fin.sum_univ_three]
  change Real.sqrt (((q * Real.cos θ) ^ 2 + (q * Real.sin θ) ^ 2 + z ^ 2) *
        ((-t * Real.sin θ) ^ 2 + (t * Real.cos θ) ^ 2 + (0 : ℝ) ^ 2) -
        (q * Real.cos θ * (-t * Real.sin θ) + q * Real.sin θ * (t * Real.cos θ) + z * 0) ^ 2) = _
  rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hr hφ)]
  change r * Real.sin φ * Real.sqrt (r ^ 2 + a ^ 2) = r * Real.sqrt (r ^ 2 + a ^ 2) * Real.sin φ
  ring

private theorem cylindricalSurfaceChart_contDiff {z : X₂ → ℝ} (hz : ContDiff ℝ 1 z) :
    ContDiff ℝ 1 (cylindricalSurfaceChart z) := by
  have hp₀ : ContDiff ℝ 1 (fun u : X₂ => u 0) := (p₀).contDiff
  have hp₁ : ContDiff ℝ 1 (fun u : X₂ => u 1) := (p₁).contDiff
  unfold cylindricalSurfaceChart chartVector
  fun_prop

/-- **Exercise 34**, Equation (155), of [benIsrael2003generalized], Chapter 8.
An injective cylindrical angle chart at positive radii gives the weighted
surface integral for normalized two-dimensional Hausdorff measure. -/
theorem exercise_34_surface_integral {z : X₂ → ℝ} (hz : ContDiff ℝ 1 z)
    {S : Set X₂} (hS : MeasurableSet S) (hr : ∀ u ∈ S, 0 < u 0)
    (hinj : InjOn (cylindricalSurfaceChart z) S) (f : X₃ → ℝ) :
    (∫ v in cylindricalSurfaceChart z '' S, f v ∂(euclideanHausdorffMeasure 2 3)) =
      ∫ u in S, f (cylindricalSurfaceChart z u) *
        Real.sqrt ((u 0)^2 + (u 0)^2 * (fderiv ℝ z u e₀)^2 + (fderiv ℝ z u e₁)^2) := by
  let Ω : Set X₂ := {u | 0 < u 0}
  have hΩ : IsOpen Ω := isOpen_lt continuous_const (p₀).continuous
  have hc := cylindricalSurfaceChart_contDiff hz
  have hDiff := hc.differentiable one_ne_zero
  have hz' := hz.differentiable one_ne_zero
  have hRank (u : X₂) (hu : u ∈ Ω) :
      Function.Injective (fderiv ℝ (cylindricalSurfaceChart z) u) := by
    apply injective_of_gram_pos
    rw [exercise_34_surface_density (hz' u)]
    exact Real.sqrt_pos_of_pos (by
      have : 0 < u 0 := hu
      positivity)
  rw [integral_areaFormula hΩ hS hr (fun u _ => (hDiff u).hasFDerivAt)
    (hc.continuous_fderiv one_ne_zero).continuousOn hRank hinj f]
  apply setIntegral_congr_fun hS
  intro u _
  dsimp only
  rw [smul_eq_mul, exercise_34_surface_density (hz' u), mul_comm]

/-- **Exercise 35** of [benIsrael2003generalized], Chapter 8.
The Hausdorff surface integral on a cylindrical graph with radial height
has the factor r times the square root of 1 plus the squared radial derivative. -/
theorem exercise_35_surface_integral {z : ℝ → ℝ} (hz : ContDiff ℝ 1 z)
    {S : Set X₂} (hS : MeasurableSet S) (hr : ∀ u ∈ S, 0 < u 0)
    (hinj : InjOn (cylindricalSurfaceChart (fun v => z (v 0))) S) (f : X₃ → ℝ) :
    (∫ v in cylindricalSurfaceChart (fun u => z (u 0)) '' S, f v ∂(euclideanHausdorffMeasure 2 3)) =
      ∫ u in S, f (cylindricalSurfaceChart (fun v => z (v 0)) u) *
        (u 0 * Real.sqrt (1 + (deriv z (u 0))^2)) := by
  have hc : ContDiff ℝ 1 (fun u : X₂ => z (u 0)) := hz.comp (p₀).contDiff
  rw [exercise_34_surface_integral hc hS hr hinj f]
  apply setIntegral_congr_fun hS
  intro u hu
  dsimp only
  rw [← exercise_34_surface_density (hc.differentiable one_ne_zero u),
    exercise_35_surface_density (hz.differentiable one_ne_zero _) (hr u hu).le]

private theorem sphericalSurfaceChart_contDiff {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) :
    ContDiff ℝ 1 (sphericalSurfaceChart ρ) := by
  have hp₀ : ContDiff ℝ 1 (fun u : X₂ => u 0) := (p₀).contDiff
  have hp₁ : ContDiff ℝ 1 (fun u : X₂ => u 1) := (p₁).contDiff
  unfold sphericalSurfaceChart chartVector
  fun_prop

/-- **Exercise 36**, Equation (159a), of [benIsrael2003generalized], Chapter 8.
For an injective spherical chart away from the poles, the explicit factor
is the radius times root squared radius plus squared radial derivative,
times the sine of the polar angle. -/
theorem exercise_36_surface_integral {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ)
    {S : Set X₂} (hS : MeasurableSet S) (hr : ∀ u ∈ S, 0 < ρ (u 0))
    (hφ : ∀ u ∈ S, 0 < Real.sin (u 0))
    (hinj : InjOn (sphericalSurfaceChart ρ) S) (f : X₃ → ℝ) :
    (∫ v in sphericalSurfaceChart ρ '' S, f v ∂(euclideanHausdorffMeasure 2 3)) =
      ∫ u in S, f (sphericalSurfaceChart ρ u) *
        (ρ (u 0) * Real.sqrt ((ρ (u 0))^2 + (deriv ρ (u 0))^2) * Real.sin (u 0)) := by
  let Ω : Set X₂ := {u | 0 < ρ (u 0)} ∩ {u | 0 < Real.sin (u 0)}
  have hΩ : IsOpen Ω := (isOpen_lt continuous_const (hρ.continuous.comp (p₀).continuous)).inter
    (isOpen_lt continuous_const (Real.continuous_sin.comp (p₀).continuous))
  have hsub : S ⊆ Ω := fun u hu => ⟨hr u hu, hφ u hu⟩
  have hc := sphericalSurfaceChart_contDiff hρ
  have hDiff := hc.differentiable one_ne_zero
  have hρ' := hρ.differentiable one_ne_zero
  have hRank (u : X₂) (hu : u ∈ Ω) :
      Function.Injective (fderiv ℝ (sphericalSurfaceChart ρ) u) := by
    apply injective_of_gram_pos
    have hr' : 0 < ρ (u 0) := hu.1
    have hφ' : 0 < Real.sin (u 0) := hu.2
    rw [exercise_36_surface_density (hρ' _) hr'.le hφ'.le]
    positivity
  rw [integral_areaFormula hΩ hS hsub (fun u _ => (hDiff u).hasFDerivAt)
    (hc.continuous_fderiv one_ne_zero).continuousOn hRank hinj f]
  apply setIntegral_congr_fun hS
  intro u hu
  dsimp only
  rw [smul_eq_mul, exercise_36_surface_density (hρ' _) (hr u hu).le (hφ u hu).le, mul_comm]

end ChartDerivatives

section HemisphereBeta

/-- **Exercise 41**, Equation (171), of [benIsrael2003generalized], Chapter 8.
The substitution x = r² evaluates the hemisphere's radial integral by
the Beta function. -/
theorem exercise_41_radial_beta {d : ℕ} (hd : d ≠ 0) :
    (∫ r in Ioo (0 : ℝ) 1, r ^ (d - 1) * (Real.sqrt (1 - r ^ 2))⁻¹) =
      realBeta ((d : ℝ) / 2) (1 / 2) / 2 := by
  let W := Ioo (0 : ℝ) 1
  let B (x : ℝ) := (1 - x) ^ ((1 / 2 : ℝ) - 1) * x ^ ((d : ℝ) / 2 - 1)
  have hsym : realBeta ((d : ℝ) / 2) (1 / 2) = realBeta (1 / 2) ((d : ℝ) / 2) := by
    rw [exercise_39_beta_eq_gamma (by positivity) (by norm_num),
      exercise_39_beta_eq_gamma (by norm_num) (by positivity)]
    ring_nf
  have hImg : (fun r : ℝ => r ^ 2) '' W = W := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨sq_pos_of_pos hr.1, (sq_lt_one_iff_abs_lt_one _).2 (by rw [abs_of_pos hr.1]; exact hr.2)⟩
    · intro hx
      refine ⟨Real.sqrt x, ⟨Real.sqrt_pos_of_pos hx.1, (Real.sqrt_lt' zero_lt_one).2 (by simpa using hx.2)⟩, Real.sq_sqrt hx.1.le⟩
  have hinj : InjOn (fun r : ℝ => r ^ 2) W := by
    intro x hx y hy hxy
    exact (sq_eq_sq₀ hx.1.le hy.1.le).mp hxy
  have hD (r : ℝ) (_hr : r ∈ W) : HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * r) W r := by
    exact (by simpa using hasDerivAt_pow 2 r : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hD hinj B
  rw [hImg] at h
  have hBeta : (∫ r in W, B r) = realBeta (1 / 2) ((d : ℝ) / 2) := by
    rw [realBeta, intervalIntegral.integral_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  have hfactor (r : ℝ) (hr : r ∈ W) :
      |2 * r| • B (r ^ 2) = 2 * (r ^ (d - 1) * (Real.sqrt (1 - r ^ 2))⁻¹) := by
    have hr₂ : 0 ≤ 1 - r ^ 2 := by nlinarith [mul_pos hr.1 (sub_pos.mpr hr.2)]
    have hpow : (r ^ 2) ^ ((d : ℝ) / 2 - 1) = r ^ ((d : ℝ) - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.1.le]
      norm_num
      ring_nf
    have hcombine : r * r ^ ((d : ℝ) - 2) = r ^ (d - 1 : ℕ) := by
      rw [mul_comm, ← Real.rpow_add_one hr.1.ne', ← Real.rpow_natCast]
      congr 1
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hd), Nat.cast_one]
      ring
    simp only [B, smul_eq_mul, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hr.1)]
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg hr₂, ← Real.sqrt_eq_rpow, hpow]
    calc
      _ = 2 * ((r * r ^ ((d : ℝ) - 2)) * (Real.sqrt (1 - r ^ 2))⁻¹) := by ring
      _ = _ := by rw [hcombine]
  rw [hBeta, setIntegral_congr_fun measurableSet_Ioo hfactor, integral_const_mul] at h
  rw [hsym, h]
  ring

/-- **Exercise 41**, Equation (171), of [benIsrael2003generalized], Chapter 8.
The hemisphere graph density integrated over its parameter disk is the
lower-dimensional angular area times half the Beta factor. -/
theorem exercise_41_hemisphere_radial_integral {d : ℕ} (hd : d ≠ 0) :
    (∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹) =
      euclideanUnitSphereArea d * (realBeta ((d : ℝ) / 2) (1 / 2) / 2) := by
  let h (r : ℝ) := (Real.sqrt (1 - r ^ 2))⁻¹
  let f := (Iio (1 : ℝ)).indicator h
  have hf : (fun u : EuclideanSpace ℝ (Fin d) =>
      (Metric.ball 0 1).indicator (fun v => h ‖v‖) u) = fun u => f ‖u‖ := by
    ext u
    by_cases hu : ‖u‖ < 1 <;> simp [Metric.mem_ball, f, hu]
  let : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume
  have he : (d : ℝ) * μ.real (Metric.ball 0 1) = euclideanUnitSphereArea d := by
    rw [euclideanUnitSphereArea, Measure.toSphere_real_apply_univ, finrank_euclideanSpace, Fintype.card_fin]
  change (∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, h ‖u‖) = _
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, hf,
    integral_fun_norm_addHaar μ f]
  simp only [nsmul_eq_mul, smul_eq_mul, finrank_euclideanSpace, Fintype.card_fin]
  rw [← mul_assoc, he]
  congr 1
  have heq (r : ℝ) : r ^ (d - 1) * f r =
      (Iio 1).indicator (fun t : ℝ => t ^ (d - 1) * h t) r := by
    by_cases hr : r < 1 <;> simp [f, hr]
  rw [show (fun r => r ^ (d - 1) * f r) = _ from funext heq,
    setIntegral_indicator measurableSet_Iio, show Ioi (0 : ℝ) ∩ Iio 1 = Ioo 0 1 by rfl]
  exact exercise_41_radial_beta hd

/-- The Beta recurrence for consecutive angular sphere areas. -/
theorem exercise_41_sphere_area_beta {d : ℕ} (hd : d ≠ 0) :
    euclideanUnitSphereArea (d + 1) =
      euclideanUnitSphereArea d * realBeta ((d : ℝ) / 2) (1 / 2) := by
  have hd' : 0 < (d : ℝ) / 2 := by positivity
  rw [exercise_41_unitSphereArea (Nat.succ_ne_zero d), exercise_41_unitSphereArea hd,
    exercise_39_beta_eq_gamma hd' (by norm_num), Real.Gamma_one_half_eq]
  have hp : (d + 1 : ℕ) / (2 : ℝ) = (d : ℝ) / 2 + 1 / 2 := by push_cast; ring
  rw [hp, Real.rpow_add Real.pi_pos, ← Real.sqrt_eq_rpow]
  field_simp [(Real.Gamma_pos_of_pos hd').ne']

/-- The angular unit-sphere area is twice the explicit hemisphere graph
integral over the open unit parameter disk. -/
theorem exercise_41_hemisphere_integral_angular {d : ℕ} (hd : d ≠ 0) :
    euclideanUnitSphereArea (d + 1) =
      2 * (∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹) := by
  rw [exercise_41_sphere_area_beta hd, exercise_41_hemisphere_radial_integral hd]
  ring

end HemisphereBeta

section HemisphereGeometry

open EuclideanSpace
open scoped BigOperators InnerProductSpace

variable {d : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "Y" => EuclideanSpace ℝ (Fin (d + 1))
local notation "B" => Metric.ball (0 : X) 1
local notation "Σₛ" => Metric.sphere (0 : Y) 1
local notation "H" => euclideanHausdorffMeasure d (d + 1)

/-- The positive-height chart of the Euclidean unit sphere. Its regular
parameter domain is the open unit ball. -/
def sphereUpperChart (u : X) : Y :=
  snocLast u (Real.sqrt (1 - ‖u‖ ^ 2))

private theorem hemisphereHeight_pos_arg {u : X} (hu : u ∈ B) : 0 < 1 - ‖u‖ ^ 2 := by
  have h : ‖u‖ < 1 := by simpa using hu
  nlinarith [mul_pos (sub_pos.mpr h) (add_pos_of_nonneg_of_pos (norm_nonneg u) zero_lt_one)]

/-- The chart image is the open upper hemisphere of the unit sphere. -/
theorem sphereUpperChart_image_ball :
    sphereUpperChart '' B = Σₛ ∩ {x : Y | 0 < x (Fin.last d)} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hp := hemisphereHeight_pos_arg hu
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right]
      apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
      rw [sphereUpperChart, norm_snocLast_sq, Real.sq_sqrt hp.le]
      ring
    · simpa only [Set.mem_ofPred_eq, sphereUpperChart, snocLast_apply_last] using Real.sqrt_pos_of_pos hp
  · rintro ⟨hs, ht⟩
    let u := init x
    let t := x (Fin.last d)
    have hnorm : ‖x‖ = 1 := by simpa using hs
    have ht' : 0 < t := ht
    have hsq : ‖u‖ ^ 2 + t ^ 2 = 1 := by
      rw [← norm_snocLast_sq, show snocLast u t = x from snocLast_init_last x, hnorm, one_pow]
    have hB : u ∈ B := by
      rw [Metric.mem_ball, dist_zero_right]
      nlinarith [sq_pos_of_pos ht']
    have hlast : Real.sqrt (1 - ‖u‖ ^ 2) = t := by
      rw [show 1 - ‖u‖ ^ 2 = t ^ 2 by linarith only [hsq], Real.sqrt_sq ht'.le]
    exact ⟨u, hB, by rw [sphereUpperChart, hlast]; exact snocLast_init_last x⟩

private theorem sphereUpperChart_injective : Function.Injective (sphereUpperChart (d := d)) := by
  intro x y h
  simpa only [sphereUpperChart, init_snocLast] using congrArg init h

private theorem sphereUpperChart_contDiffOn : ContDiffOn ℝ 1 (sphereUpperChart (d := d)) B := by
  have hg : ContDiffOn ℝ 1 (fun u : X => Real.sqrt (1 - ‖u‖ ^ 2)) B :=
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn).sqrt
      (fun u hu => (hemisphereHeight_pos_arg hu).ne')
  change ContDiffOn ℝ 1 ((lastInitL d).symm ∘ fun u : X =>
    (Real.sqrt (1 - ‖u‖ ^ 2), u)) B
  exact (lastInitL d).symm.toContinuousLinearMap.contDiff.comp_contDiffOn (hg.prodMk contDiffOn_id)

private theorem sphereUpperChart_hasFDerivAt {u : X} (hu : u ∈ B) :
    HasFDerivAt sphereUpperChart
      (snocLastL (fderiv ℝ (fun v : X => Real.sqrt (1 - ‖v‖ ^ 2)) u)) u := by
  let g := fun v : X => Real.sqrt (1 - ‖v‖ ^ 2)
  have hg : DifferentiableAt ℝ g u :=
    (((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_sub 1).sqrt
      (hemisphereHeight_pos_arg hu).ne').differentiableAt
  change HasFDerivAt (fun u : X => (lastInitL d).symm (g u, u)) _ u
  exact (lastInitL d).symm.hasFDerivAt.comp u (hg.hasFDerivAt.prodMk (hasFDerivAt_id u))

private theorem sphereUpperChart_gram {u : X} (hu : u ∈ B) :
    EuclideanSpace.gram (fderiv ℝ sphereUpperChart u) = (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹ := by
  rw [(sphereUpperChart_hasFDerivAt hu).fderiv, gram_snocLastL]
  have hd := exercise_41_hemisphere_density u (by simpa using hu)
  simpa only [graphDensity, norm_gradient_eq] using hd

/-- Scalar integration on the open upper hemisphere with its geometric
Hausdorff surface measure. -/
theorem exercise_41_upper_hemisphere_integral {S : Set X} (hS : MeasurableSet S)
    (hsub : S ⊆ B) (f : Y → ℝ) :
    (∫ x in sphereUpperChart '' S, f x ∂H) =
      ∫ u in S, f (sphereUpperChart u) * (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹ := by
  have hDiff (u : X) (hu : u ∈ B) : HasFDerivAt sphereUpperChart (fderiv ℝ sphereUpperChart u) u :=
    (sphereUpperChart_hasFDerivAt hu).differentiableAt.hasFDerivAt
  have hRank (u : X) (hu : u ∈ B) : Function.Injective (fderiv ℝ sphereUpperChart u) := by
    rw [(sphereUpperChart_hasFDerivAt hu).fderiv]
    intro x y h
    simpa only [snocLastL_apply, init_snocLast] using congrArg init h
  rw [integral_areaFormula Metric.isOpen_ball hS hsub hDiff
    (sphereUpperChart_contDiffOn.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
    hRank sphereUpperChart_injective.injOn f]
  apply setIntegral_congr_fun hS
  intro u hu
  dsimp only
  rw [sphereUpperChart_gram (hsub hu), smul_eq_mul, mul_comm]

private theorem sphereEquator_eq_image :
    Σₛ ∩ {x : Y | x (Fin.last d) = 0} =
      snocLastL (0 : X →L[ℝ] ℝ) '' Metric.sphere (0 : X) 1 := by
  ext x
  constructor
  · rintro ⟨hs, hx⟩
    have hzero : x (Fin.last d) = 0 := hx
    have hsnoc : snocLast (init x) 0 = x := by rw [← hzero, snocLast_init_last]
    have hnorm : ‖x‖ = 1 := by simpa using hs
    have hsquared := norm_snocLast_sq (init x) (0 : ℝ)
    rw [hsnoc, hnorm, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hsquared
    refine ⟨init x, ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right]
      apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
      simpa only [one_pow] using hsquared.symm
    · simpa only [snocLastL_apply, zero_apply] using hsnoc
  · rintro ⟨u, hu, rfl⟩
    have hnorm : ‖u‖ = 1 := by simpa using hu
    refine ⟨?_, by simp [snocLastL_apply]⟩
    rw [Metric.mem_sphere, dist_zero_right, snocLastL_apply, zero_apply]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [norm_snocLast_sq, hnorm]
    norm_num

/-- The equator has zero normalized surface measure in dimensions at least two. -/
theorem exercise_41_equator_measure_zero (hd : d ≠ 0) :
    H (Σₛ ∩ {x : Y | x (Fin.last d) = 0}) = 0 := by
  let : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  have hInjective : Function.Injective (snocLastL (0 : X →L[ℝ] ℝ)) := by
    intro x y h
    simpa only [snocLastL_apply, init_snocLast] using congrArg init h
  rw [sphereEquator_eq_image, hausdorffMeasure_image_linear _ hInjective,
    Measure.addHaar_sphere_of_ne_zero volume 0 one_ne_zero, mul_zero]

/-- **Exercise 41**, Equations (170)–(171), of [benIsrael2003generalized],
Chapter 8. The geometric sphere area is twice its upper hemisphere chart
integral, and the equator has zero surface measure. -/
theorem exercise_41_hemisphere_integral (hd : d ≠ 0) :
    (H).real Σₛ = 2 * (∫ u in B, (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹) := by
  let U : Set Y := Σₛ ∩ {x : Y | 0 < x (Fin.last d)}
  let L : Set Y := Σₛ ∩ {x : Y | x (Fin.last d) < 0}
  let E : Set Y := Σₛ ∩ {x : Y | x (Fin.last d) = 0}
  have hL : MeasurableSet L := Metric.isClosed_sphere.measurableSet.inter
    (measurableSet_lt (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).measurable measurable_const)
  have hE : MeasurableSet E := Metric.isClosed_sphere.measurableSet.inter
    (measurableSet_eq_fun (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).measurable measurable_const)
  have hcover : Σₛ = (U ∪ L) ∪ E := by
    ext x
    constructor
    · intro hx
      rcases lt_trichotomy (x (Fin.last d)) 0 with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hx, hlt⟩)
      · exact Or.inr ⟨hx, heq⟩
      · exact Or.inl (Or.inl ⟨hx, hgt⟩)
    · rintro ((h | h) | h) <;> exact h.1
  have hUL : Disjoint U L := Set.disjoint_left.mpr fun x h₁ h₂ => by
    exact (lt_asymm (show 0 < x (Fin.last d) from h₁.2)
      (show x (Fin.last d) < 0 from h₂.2))
  have hD : Disjoint (U ∪ L) E := Set.disjoint_left.mpr fun _ h₁ h₂ => by
    rcases h₁ with h₁ | h₁
    · exact h₁.2.ne h₂.2.symm
    · exact h₁.2.ne h₂.2
  have hzero : H E = 0 := exercise_41_equator_measure_zero hd
  have hneg : (fun x : Y => -x) '' U = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hny : ‖y‖ = 1 := by simpa using hy.1
      exact ⟨by simpa [Metric.mem_sphere, dist_zero_right, norm_neg] using hny,
        by simpa only [Set.mem_ofPred_eq, PiLp.neg_apply, neg_lt_zero] using hy.2⟩
    · intro hx
      have hnx : ‖x‖ = 1 := by simpa using hx.1
      exact ⟨-x, ⟨by simpa [Metric.mem_sphere, dist_zero_right, norm_neg] using hnx,
        by simpa only [Set.mem_ofPred_eq, PiLp.neg_apply, neg_pos] using hx.2⟩, neg_neg x⟩
  have hsame : H L = H U := by
    have hi : Isometry (fun x : Y => -x) := (LinearIsometryEquiv.neg ℝ : Y ≃ₗᵢ[ℝ] Y).isometry
    rw [← hneg]
    simp only [euclideanHausdorffMeasure, Measure.smul_apply]
    rw [hi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg d))]
  have hu : (H).real U = ∫ u in B, (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹ := by
    rw [show U = sphereUpperChart '' B from sphereUpperChart_image_ball.symm]
    simpa only [setIntegral_const, smul_eq_mul, mul_one, one_mul] using
      exercise_41_upper_hemisphere_integral Metric.isOpen_ball.measurableSet Subset.rfl (fun _ => 1)
  unfold Measure.real at hu ⊢
  rw [hcover, measure_union hD hE, measure_union hUL hL, hzero, add_zero, hsame,
    ← two_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat, hu]

end HemisphereGeometry

section SpherePolarDeterminant

open EuclideanSpace
open scoped BigOperators InnerProductSpace

variable {d : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "Y" => EuclideanSpace ℝ (Fin (d + 1))
local notation "B" => Metric.ball (0 : X) 1
local notation "g" => fun u : X => Real.sqrt (1 - ‖u‖ ^ 2)

private theorem eq_sum_coordinate_smul (u : X) :
    (∑ i, u i • EuclideanSpace.single i (1 : ℝ)) = u := by
  ext j
  simp [Pi.single_apply]

private theorem sum_coordinate_apply (ℓ : X →L[ℝ] ℝ) (u : X) :
    (∑ j, u j * ℓ (EuclideanSpace.single j 1)) = ℓ u := by
  conv_rhs => rw [← eq_sum_coordinate_smul u]
  simp only [map_sum, map_smul, smul_eq_mul]

private theorem radial_sphere_matrix_det
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (u : X) {r : ℝ} (hr : r ≠ 0) (c : ℝ) (ℓ : X →L[ℝ] ℝ)
    (hfirst : ∀ i j : Fin d, A i.castSucc j.castSucc = r * (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (hlastrow : ∀ j : Fin d, A (Fin.last d) j.castSucc = r * ℓ (EuclideanSpace.single j 1))
    (hlastcol : ∀ i : Fin d, A i.castSucc (Fin.last d) = u i)
    (hcorner : A (Fin.last d) (Fin.last d) = c) :
    A.det = r ^ d * (c - ℓ u) := by
  let coef : Fin (d + 1) → ℝ := Fin.lastCases 1 (fun j => -u j / r)
  let T := A.updateCol (Fin.last d) (fun i => ∑ j, coef j * A i j)
  have he : T.det = A.det := by
    simpa only [T, coef, Fin.lastCases_last, smul_eq_mul, one_mul] using
      Matrix.det_updateCol_sum A (Fin.last d) coef
  have hv (i : Fin d) : T i.castSucc (Fin.last d) = 0 := by
    rw [show T i.castSucc (Fin.last d) = ∑ j, coef j * A i.castSucc j by simp [T]]
    rw [Fin.sum_univ_castSucc]
    simp only [coef, Fin.lastCases_castSucc, Fin.lastCases_last, hfirst, hlastcol, one_mul]
    have hSum : (∑ j : Fin d, -u j / r * (r * (1 : Matrix (Fin d) (Fin d) ℝ) i j)) = -u i := by
      rw [Finset.sum_eq_single i]
      · rw [Matrix.one_apply_eq, mul_one, div_mul_cancel₀ _ hr]
      · intro j _ hj
        rw [Matrix.one_apply_ne hj.symm, mul_zero, mul_zero]
      · simp
    rw [hSum, neg_add_cancel]
  have hcorner' : T (Fin.last d) (Fin.last d) = c - ℓ u := by
    rw [show T (Fin.last d) (Fin.last d) = ∑ j, coef j * A (Fin.last d) j by simp [T]]
    rw [Fin.sum_univ_castSucc]
    simp only [coef, Fin.lastCases_castSucc, Fin.lastCases_last, hlastrow, hcorner, one_mul]
    have hh (j : Fin d) :
        -u j / r * (r * ℓ (EuclideanSpace.single j 1)) = -(u j * ℓ (EuclideanSpace.single j 1)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hr, neg_mul]
    simp only [hh, Finset.sum_neg_distrib, sum_coordinate_apply]
    ring
  have hminor : T.submatrix (Fin.last d).succAbove (Fin.last d).succAbove =
      r • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    have hj : j.castSucc ≠ Fin.last d := Fin.castSucc_ne_last j
    simp [Matrix.submatrix_apply, Fin.succAbove_last, T, Matrix.updateCol, hj,
      hfirst]
  rw [← he, Matrix.det_succ_column T (Fin.last d), Finset.sum_eq_single (Fin.last d)]
  · rw [hcorner', hminor, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
      ← two_mul, pow_mul]
    ring
  · intro i _ hi
    have h := Fin.lastCases (motive := fun j => j ≠ Fin.last d → T j (Fin.last d) = 0)
      (fun h => (h rfl).elim) (fun j _ => hv j) i hi
    rw [h, mul_zero, zero_mul]
  · simp

/-- The full-dimensional radial chart over the positive hemisphere. The
last parameter is the radius and the initial coordinates parametrize the sphere. -/
def sphereUpperRadialMap (x : Y) : Y := x (Fin.last d) • sphereUpperChart (init x)

private def sphereChartInitL : Y →L[ℝ] X :=
  (ContinuousLinearMap.snd ℝ ℝ X).comp (lastInitL d).toContinuousLinearMap

private theorem sphereChartInitL_apply (x : Y) : sphereChartInitL x = init x := rfl

private theorem hemisphere_deriv_apply_self {u : X} (hu : u ∈ B) :
    (fderiv ℝ g u) u = -‖u‖ ^ 2 / Real.sqrt (1 - ‖u‖ ^ 2) := by
  have h := ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_sub 1).sqrt
    (hemisphereHeight_pos_arg hu).ne'
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
    innerSL_apply_apply, real_inner_self_eq_norm_sq]
  ring

private theorem sphereUpperRadialMap_hasFDerivAt {x : Y} (hu : init x ∈ B) :
    HasFDerivAt sphereUpperRadialMap
      ((x (Fin.last d)) • ((snocLastL (fderiv ℝ g (init x))).comp sphereChartInitL) +
        (EuclideanSpace.proj (Fin.last d)).smulRight (sphereUpperChart (init x))) x := by
  have hinit : HasFDerivAt (fun x : Y => init x) sphereChartInitL x := sphereChartInitL.hasFDerivAt
  have h := (sphereUpperChart_hasFDerivAt hu).comp x hinit
  exact (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).hasFDerivAt.smul h

private theorem init_single_castSucc (j : Fin d) :
    init (EuclideanSpace.single j.castSucc (1 : ℝ)) = EuclideanSpace.single j 1 := by
  ext i
  simp [init]

private theorem init_single_last :
    init (EuclideanSpace.single (Fin.last d) (1 : ℝ)) = (0 : X) := by
  ext i
  simp [init]

/-- The radial map has the expected radius power times the upper-hemisphere
density in its full-dimensional Jacobian. -/
theorem sphereUpperRadialMap_det_fderiv {x : Y} (hu : init x ∈ B) (hr : 0 < x (Fin.last d)) :
    (fderiv ℝ sphereUpperRadialMap x).det =
      (x (Fin.last d)) ^ d * (Real.sqrt (1 - ‖init x‖ ^ 2))⁻¹ := by
  let u := init x
  let r := x (Fin.last d)
  let ℓ := fderiv ℝ g u
  let c := Real.sqrt (1 - ‖u‖ ^ 2)
  let A := stdMatrix (fderiv ℝ sphereUpperRadialMap x)
  have hD := (sphereUpperRadialMap_hasFDerivAt hu).fderiv
  have hcol (j : Fin d) :
      (fderiv ℝ sphereUpperRadialMap x) (EuclideanSpace.single j.castSucc 1) =
        r • snocLast (EuclideanSpace.single j 1) (ℓ (EuclideanSpace.single j 1)) := by
    simp [hD, r, ℓ, u, sphereChartInitL_apply, init_single_castSucc, snocLastL_apply,
      Fin.castSucc_ne_last]
  have hLast :
      (fderiv ℝ sphereUpperRadialMap x) (EuclideanSpace.single (Fin.last d) 1) =
        sphereUpperChart u := by
    have hzero : snocLast (0 : X) 0 = (0 : Y) := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    simp [hD, sphereChartInitL_apply, snocLastL_apply, u, hzero]
  change LinearMap.det (fderiv ℝ sphereUpperRadialMap x).toLinearMap = _
  rw [← det_stdMatrix]
  change A.det = r ^ d * c⁻¹
  rw [radial_sphere_matrix_det A u hr.ne' c ℓ]
  · congr 1
    have hc : c ^ 2 = 1 - ‖u‖ ^ 2 := Real.sq_sqrt (hemisphereHeight_pos_arg hu).le
    have hcnz : c ≠ 0 := (Real.sqrt_pos_of_pos (hemisphereHeight_pos_arg hu)).ne'
    have hℓ : ℓ u = -‖u‖ ^ 2 / c := hemisphere_deriv_apply_self hu
    rw [hℓ]
    field_simp [hcnz]
    linarith only [hc]
  · intro i j
    rw [show A i.castSucc j.castSucc =
      (fderiv ℝ sphereUpperRadialMap x) (EuclideanSpace.single j.castSucc 1) i.castSucc from stdMatrix_apply _ _ _,
      hcol, PiLp.smul_apply, snocLast_apply_castSucc]
    by_cases h : i = j <;> simp [Matrix.one_apply, PiLp.single_apply, h, r]
  · intro j
    rw [show A (Fin.last d) j.castSucc =
      (fderiv ℝ sphereUpperRadialMap x) (EuclideanSpace.single j.castSucc 1) (Fin.last d) from stdMatrix_apply _ _ _,
      hcol, PiLp.smul_apply, snocLast_apply_last]
    rfl
  · intro i
    rw [show A i.castSucc (Fin.last d) =
      (fderiv ℝ sphereUpperRadialMap x) (EuclideanSpace.single (Fin.last d) 1) i.castSucc from stdMatrix_apply _ _ _,
      hLast, sphereUpperChart, snocLast_apply_castSucc]
  · rw [show A (Fin.last d) (Fin.last d) =
      (fderiv ℝ sphereUpperRadialMap x) (EuclideanSpace.single (Fin.last d) 1) (Fin.last d) from stdMatrix_apply _ _ _,
      hLast, sphereUpperChart, snocLast_apply_last]

end SpherePolarDeterminant

section SpherePolarCone

open EuclideanSpace
open scoped BigOperators InnerProductSpace Pointwise

variable {d : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "Y" => EuclideanSpace ℝ (Fin (d + 1))
local notation "B" => Metric.ball (0 : X) 1
local notation "Σₛ" => Metric.sphere (0 : Y) 1
local notation "H" => euclideanHausdorffMeasure d (d + 1)
local notation "I" => Set.Ioo (0 : ℝ) 1
local notation "g" => fun u : X => Real.sqrt (1 - ‖u‖ ^ 2)

private def spherePolarCylinder (S : Set X) : Set Y :=
  {x | init x ∈ S ∧ x (Fin.last d) ∈ I}

private theorem spherePolarCylinder_measurable {S : Set X} (hS : MeasurableSet S) :
    MeasurableSet (spherePolarCylinder S) :=
  (sphereChartInitL.measurable hS).inter
    ((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).measurable measurableSet_Ioo)

private theorem sphereUpperChart_norm {u : X} (hu : u ∈ B) :
    ‖sphereUpperChart u‖ = 1 := by
  have h := (show sphereUpperChart u ∈ sphereUpperChart '' B from ⟨u, hu, rfl⟩)
  rw [sphereUpperChart_image_ball] at h
  simpa using h.1

private theorem sphereUpperRadialMap_norm {x : Y} (hu : init x ∈ B) (hr : 0 ≤ x (Fin.last d)) :
    ‖sphereUpperRadialMap x‖ = x (Fin.last d) := by
  rw [sphereUpperRadialMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, sphereUpperChart_norm hu, mul_one]

private theorem sphereUpperRadialMap_injOn {S : Set X} (hsub : S ⊆ B) :
    InjOn sphereUpperRadialMap (spherePolarCylinder S) := by
  intro x hx y hy he
  have hxr : 0 < x (Fin.last d) := hx.2.1
  have hyr : 0 < y (Fin.last d) := hy.2.1
  have hr : x (Fin.last d) = y (Fin.last d) := by
    have hn := congrArg norm he
    exact (sphereUpperRadialMap_norm (hsub hx.1) hxr.le).symm.trans
      (hn.trans (sphereUpperRadialMap_norm (hsub hy.1) hyr.le))
  change x (Fin.last d) • sphereUpperChart (init x) =
    y (Fin.last d) • sphereUpperChart (init y) at he
  rw [← hr] at he
  have hinit : init x = init y :=
    sphereUpperChart_injective ((smul_right_injective _ hxr.ne') he)
  rw [← snocLast_init_last x, ← snocLast_init_last y, hinit, hr]

private theorem sphereUpperRadialMap_continuous :
    Continuous (sphereUpperRadialMap (d := d)) := by
  have hu : Continuous (fun x : Y => init x) := sphereChartInitL.continuous
  have hg : Continuous (g : X → ℝ) := by fun_prop
  have hc : Continuous (sphereUpperChart (d := d)) :=
    continuous_snocLast.comp (continuous_id.prodMk hg)
  exact (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).continuous.smul (hc.comp hu)

private theorem sphereUpperRadialMap_image (S : Set X) :
    sphereUpperRadialMap '' spherePolarCylinder S = I • (sphereUpperChart '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x (Fin.last d), hx.2, sphereUpperChart (init x), ⟨init x, hx.1, rfl⟩, rfl⟩
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨snocLast u r, ?_, ?_⟩
    · simpa only [spherePolarCylinder, Set.mem_ofPred_eq, init_snocLast, snocLast_apply_last] using ⟨hu, hr⟩
    · simp only [sphereUpperRadialMap, init_snocLast, snocLast_apply_last]

private theorem sphere_radial_power_lintegral (d : ℕ) :
    (∫⁻ r in I, ENNReal.ofReal (r ^ d)) = ENNReal.ofReal ((d + 1 : ℝ)⁻¹) := by
  let f : ℝ → ℝ := fun r => r ^ d
  have hf : IntervalIntegrable f volume 0 1 := (continuous_id.pow d).intervalIntegrable _ _
  rw [restrict_Ioo_eq_restrict_Ioc]
  have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc 0 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pow_nonneg hr.1.le d
  rw [← ofReal_integral_eq_lintegral_ofReal hf.1 hnn,
    ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  simp [div_eq_mul_inv]

private theorem spherePolarCylinder_lintegral (S : Set X) (hS : MeasurableSet S) :
    (∫⁻ x in spherePolarCylinder S,
      ENNReal.ofReal ((x (Fin.last d)) ^ d) * ENNReal.ofReal ((g (init x))⁻¹)) =
      ENNReal.ofReal ((d + 1 : ℝ)⁻¹) * ∫⁻ u in S, ENNReal.ofReal ((g u)⁻¹) := by
  let q (t : ℝ) := ENNReal.ofReal (t ^ d)
  let w (u : X) := ENNReal.ofReal ((g u)⁻¹)
  let f (x : Y) := q (x (Fin.last d)) * w (init x)
  have hq : Measurable q := by
    apply ENNReal.measurable_ofReal.comp
    exact (continuous_id.pow d).measurable
  have hw : Measurable w := by
    apply ENNReal.measurable_ofReal.comp
    exact Measurable.inv (show Measurable (g : X → ℝ) by fun_prop)
  have hf : Measurable f := (hq.comp (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).measurable).mul
    (hw.comp sphereChartInitL.measurable)
  have hC := spherePolarCylinder_measurable hS
  change (∫⁻ x in spherePolarCylinder S, f x) = _
  rw [← lintegral_indicator hC, lintegral_lastInit _ (hf.indicator hC).aemeasurable,
    ← lintegral_const_mul _ hw, ← lintegral_indicator hS]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu]
    have he (t : ℝ) : (spherePolarCylinder S).indicator f (snocLast u t) =
        (I).indicator (fun r => q r * w u) t := by
      have hm : snocLast u t ∈ spherePolarCylinder S ↔ t ∈ I := by
        change (init (snocLast u t) ∈ S ∧ snocLast u t (Fin.last d) ∈ I) ↔ _
        rw [init_snocLast, snocLast_apply_last]
        exact and_iff_right hu
      by_cases ht : t ∈ I
      · rw [Set.indicator_of_mem (hm.mpr ht), Set.indicator_of_mem ht]
        simp only [f, init_snocLast, snocLast_apply_last]
      · rw [Set.indicator_of_notMem (fun h => ht (hm.mp h)), Set.indicator_of_notMem ht]
    simp_rw [he]
    rw [lintegral_indicator measurableSet_Ioo, lintegral_mul_const _ hq, sphere_radial_power_lintegral]
  · rw [Set.indicator_of_notMem hu]
    have he (t : ℝ) : (spherePolarCylinder S).indicator f (snocLast u t) = 0 := by
      simp [spherePolarCylinder, hu, init_snocLast]
    simp only [he, lintegral_zero]

private theorem sphereUpperCone_volume {S : Set X} (hS : MeasurableSet S) (hsub : S ⊆ B) :
    MeasurableSet (I • (sphereUpperChart '' S)) ∧
      (volume : Measure Y) (I • (sphereUpperChart '' S)) =
        ENNReal.ofReal ((d + 1 : ℝ)⁻¹) * (∫⁻ u in S, ENNReal.ofReal ((g u)⁻¹)) := by
  let C := spherePolarCylinder S
  have hC : MeasurableSet C := spherePolarCylinder_measurable hS
  have hi : InjOn sphereUpperRadialMap C := sphereUpperRadialMap_injOn hsub
  have hD (x : Y) (hx : x ∈ C) :
      HasFDerivWithinAt sphereUpperRadialMap (fderiv ℝ sphereUpperRadialMap x) C x :=
    (sphereUpperRadialMap_hasFDerivAt (hsub hx.1)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  rw [← sphereUpperRadialMap_image]
  refine ⟨hC.image_of_continuousOn_injOn sphereUpperRadialMap_continuous.continuousOn hi, ?_⟩
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hC hD hi (fun _ => 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at hh
  rw [hh, ← spherePolarCylinder_lintegral S hS]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hC] with x hx
  have hr : 0 < x (Fin.last d) := hx.2.1
  have hg : 0 ≤ (g (init x))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [sphereUpperRadialMap_det_fderiv (hsub hx.1) hr, abs_of_nonneg (mul_nonneg (pow_nonneg hr.le _) hg),
    ENNReal.ofReal_mul (pow_nonneg hr.le _)]

end SpherePolarCone

section PolarMeasureEquality

open EuclideanSpace
open scoped BigOperators InnerProductSpace Pointwise

variable {d : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin d)
local notation "Y" => EuclideanSpace ℝ (Fin (d + 1))
local notation "B" => Metric.ball (0 : X) 1
local notation "Σₛ" => Metric.sphere (0 : Y) 1
local notation "H" => euclideanHausdorffMeasure d (d + 1)
local notation "I" => Set.Ioo (0 : ℝ) 1
local notation "V" => (volume : Measure Y)

private theorem sphereUpperChart_continuous :
    Continuous (sphereUpperChart (d := d)) :=
  continuous_snocLast.comp (continuous_id.prodMk (by fun_prop))

private theorem normalized_upper_sphere_cone {S : Set Y} (hS : MeasurableSet S)
    (hsub : S ⊆ Σₛ ∩ {x : Y | 0 < x (Fin.last d)}) :
    MeasurableSet (I • S) ∧ (d + 1 : ℝ≥0∞) * V (I • S) = H S := by
  let U := B ∩ sphereUpperChart ⁻¹' S
  have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet.inter
    (sphereUpperChart_continuous.measurable hS)
  have hUsub : U ⊆ B := inter_subset_left
  have himg : sphereUpperChart '' U = S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have h := hsub hy
      rw [← sphereUpperChart_image_ball] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨u, ⟨hu, hy⟩, rfl⟩
  rw [← himg]
  obtain ⟨hm, hcone⟩ := sphereUpperCone_volume hU hUsub
  refine ⟨hm, ?_⟩
  have hDiff (u : X) (hu : u ∈ B) : HasFDerivAt sphereUpperChart (fderiv ℝ sphereUpperChart u) u :=
    (sphereUpperChart_hasFDerivAt hu).differentiableAt.hasFDerivAt
  have hRank (u : X) (hu : u ∈ B) : Function.Injective (fderiv ℝ sphereUpperChart u) := by
    rw [(sphereUpperChart_hasFDerivAt hu).fderiv]
    intro x y he
    simpa only [snocLastL_apply, init_snocLast] using congrArg init he
  rw [hcone, hausdorffMeasure_image_eq_lintegral_gram Metric.isOpen_ball hU hUsub hDiff
    (sphereUpperChart_contDiffOn.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
    hRank sphereUpperChart_injective.injOn, ← mul_assoc]
  have hcancel : (d + 1 : ℝ≥0∞) * ENNReal.ofReal ((d + 1 : ℝ)⁻¹) = 1 := by
    have he : (d + 1 : ℝ≥0∞) = ENNReal.ofReal (d + 1 : ℝ) := by
      simp [ENNReal.ofReal_add, Nat.cast_nonneg]
    rw [he, ← ENNReal.ofReal_mul (by positivity)]
    simp [(show (d + 1 : ℝ) ≠ 0 by positivity)]
  rw [hcancel, one_mul]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hU] with u hu
  rw [sphereUpperChart_gram (hUsub hu)]

private theorem polarCone_neg_image (S : Set Y) :
    (fun x : Y => -x) '' (I • S) = I • ((fun x : Y => -x) '' S) := by
  ext z
  constructor
  · rintro ⟨_, ⟨r, hr, y, hy, rfl⟩, rfl⟩
    exact ⟨r, hr, -y, ⟨y, hy, rfl⟩, smul_neg r y⟩
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨r • y, ⟨r, hr, y, hy, rfl⟩, (smul_neg r y).symm⟩

private theorem measure_neg_image_polar (S : Set Y) :
    V ((fun x : Y => -x) '' S) = V S := by
  conv_lhs => rw [← Measure.map_neg_eq_self V]
  rw [measurableEmbedding_neg.map_apply, Set.preimage_image_eq _ neg_injective]

private theorem hausdorff_neg_image_polar (S : Set Y) :
    H ((fun x : Y => -x) '' S) = H S := by
  have hi : Isometry (fun x : Y => -x) := (LinearIsometryEquiv.neg ℝ : Y ≃ₗᵢ[ℝ] Y).isometry
  simp only [euclideanHausdorffMeasure, Measure.smul_apply]
  rw [hi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg d))]

private theorem normalized_lower_sphere_cone {S : Set Y} (hS : MeasurableSet S)
    (hsub : S ⊆ Σₛ ∩ {x : Y | x (Fin.last d) < 0}) :
    MeasurableSet (I • S) ∧ (d + 1 : ℝ≥0∞) * V (I • S) = H S := by
  let T := (fun x : Y => -x) '' S
  have hT : MeasurableSet T := measurableEmbedding_neg.measurableSet_image.mpr hS
  have hTsub : T ⊆ Σₛ ∩ {x : Y | 0 < x (Fin.last d)} := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hn, hl⟩ := hsub hx
    exact ⟨by simpa [Metric.mem_sphere, dist_zero_right, norm_neg] using hn,
      by simpa only [Set.mem_ofPred_eq, PiLp.neg_apply, neg_pos] using hl⟩
  obtain ⟨hC, hvol⟩ := normalized_upper_sphere_cone hT hTsub
  dsimp only [T] at hC hvol
  rw [← polarCone_neg_image] at hC hvol
  rw [measure_neg_image_polar, hausdorff_neg_image_polar] at hvol
  exact ⟨measurableEmbedding_neg.measurableSet_image.mp hC, hvol⟩

private theorem volume_sphereEquatorialHyperplane :
    V {x : Y | x (Fin.last d) = 0} = 0 := by
  have hEq : {x : Y | x (Fin.last d) = 0} =
      lastInitEquiv d ⁻¹' ({(0 : ℝ)} ×ˢ (Set.univ : Set X)) := by
    ext x
    simp [lastInitEquiv_apply]
  rw [hEq, (measurePreserving_lastInit d).measure_preimage
    ((measurableSet_singleton _).prod MeasurableSet.univ).nullMeasurableSet]
  change ((volume : Measure ℝ).prod (volume : Measure X))
    ({(0 : ℝ)} ×ˢ (Set.univ : Set X)) = 0
  rw [Measure.prod_prod, measure_singleton, zero_mul]

private theorem volume_sphereEquatorialCone {S : Set Y}
    (hS : S ⊆ {y : Y | y (Fin.last d) = 0}) : V (I • S) = 0 := by
  apply measure_mono_null _ (volume_sphereEquatorialHyperplane (d := d))
  rintro _ ⟨r, _, y, hy, rfl⟩
  change r * y (Fin.last d) = 0
  rw [show y (Fin.last d) = 0 from hS hy, mul_zero]

private theorem polarCone_disjoint_of_hemispheres {U L : Set Y}
    (hU : U ⊆ {x : Y | 0 < x (Fin.last d)}) (hL : L ⊆ {x : Y | x (Fin.last d) < 0}) :
    Disjoint (I • U) (I • L) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨r, hr, x, hx, h₁⟩ ⟨s, hs, y, hy, h₂⟩
  have h₁' : 0 < z (Fin.last d) := by
    rw [← h₁, PiLp.smul_apply, smul_eq_mul]
    exact mul_pos hr.1 (hU hx)
  have h₂' : z (Fin.last d) < 0 := by
    rw [← h₂, PiLp.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hs.1 (hL hy)
  exact lt_asymm h₁' h₂'

private theorem measure_union_of_null_right {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {S T : Set Z} (h : μ T = 0) : μ (S ∪ T) = μ S := by
  apply le_antisymm
  · calc
      _ ≤ μ S + μ T := measure_union_le S T
      _ = _ := by rw [h, add_zero]
  · exact measure_mono subset_union_left

private theorem sphere_one_equator_empty :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩
      {x : EuclideanSpace ℝ (Fin 1) | x (Fin.last 0) = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hs, hx⟩
  have hz : x = 0 := by
    ext i
    have hi : i = Fin.last 0 := Subsingleton.elim _ _
    rw [hi]
    exact hx
  simp [hz] at hs

private theorem normalized_full_sphere_cone {S : Set Y}
    (hS : MeasurableSet S) (hsub : S ⊆ Σₛ) :
    (d + 1 : ℝ≥0∞) * V (I • S) = H S := by
  let U := S ∩ {x : Y | 0 < x (Fin.last d)}
  let L := S ∩ {x : Y | x (Fin.last d) < 0}
  let E := S ∩ {x : Y | x (Fin.last d) = 0}
  have hcover : S = (U ∪ L) ∪ E := by
    ext x
    constructor
    · intro hx
      rcases lt_trichotomy (x (Fin.last d)) 0 with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hx, hlt⟩)
      · exact Or.inr ⟨hx, heq⟩
      · exact Or.inl (Or.inl ⟨hx, hgt⟩)
    · rintro ((hx | hx) | hx) <;> exact hx.1
  let p : Y →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last d)
  have hU : MeasurableSet U := hS.inter (measurableSet_lt measurable_const p.measurable)
  have hL : MeasurableSet L := hS.inter (measurableSet_lt p.measurable measurable_const)
  have hUsub : U ⊆ Σₛ ∩ {x : Y | 0 < x (Fin.last d)} := fun _ hx => ⟨hsub hx.1, hx.2⟩
  have hLsub : L ⊆ Σₛ ∩ {x : Y | x (Fin.last d) < 0} := fun _ hx => ⟨hsub hx.1, hx.2⟩
  have hEsub : E ⊆ Σₛ ∩ {x : Y | x (Fin.last d) = 0} := fun _ hx => ⟨hsub hx.1, hx.2⟩
  have hHU : Disjoint U L := Set.disjoint_left.mpr fun x hx hy =>
    lt_asymm (show 0 < x (Fin.last d) from hx.2) (show x (Fin.last d) < 0 from hy.2)
  have hHE : H E = 0 := by
    apply measure_mono_null hEsub
    by_cases hd : d = 0
    · subst d
      rw [sphere_one_equator_empty, measure_empty]
    · exact exercise_41_equator_measure_zero hd
  have hVE : V (I • E) = 0 := volume_sphereEquatorialCone inter_subset_right
  obtain ⟨_, hu⟩ := normalized_upper_sphere_cone hU hUsub
  obtain ⟨hLC, hl⟩ := normalized_lower_sphere_cone hL hLsub
  rw [hcover, Set.smul_union, Set.smul_union,
    measure_union_of_null_right V hVE, measure_union_of_null_right H hHE,
    measure_union (polarCone_disjoint_of_hemispheres inter_subset_right inter_subset_right) hLC,
    measure_union hHU hL, mul_add, hu, hl]

/-- **Exercise 40**, Equations (168)–(169), of [benIsrael2003generalized],
Chapter 8. The angular measure in the polar decomposition is precisely
the restriction of normalized Hausdorff measure to the unit sphere,
including the two-point sphere in ambient dimension one. -/
theorem exercise_40_polar_area_eq_hausdorff :
    Measure.map (Subtype.val : Σₛ → Y) (V).toSphere = (H).restrict Σₛ := by
  apply Measure.ext
  intro S hS
  have hmeas : Measurable (Subtype.val : Σₛ → Y) := measurable_subtype_coe
  rw [Measure.map_apply hmeas hS, Measure.restrict_apply hS, Measure.toSphere_apply' V (hmeas hS)]
  have hImage : (Subtype.val : Σₛ → Y) '' ((Subtype.val : Σₛ → Y) ⁻¹' S) = S ∩ Σₛ := by
    ext x
    exact ⟨fun ⟨y, hy, e⟩ => e ▸ ⟨hy, y.property⟩, fun hx => ⟨⟨x, hx.2⟩, hx.1, rfl⟩⟩
  rw [hImage, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  exact normalized_full_sphere_cone (hS.inter Metric.isClosed_sphere.measurableSet) inter_subset_right

end PolarMeasureEquality

section NonnegativeAreaFormula

open EuclideanSpace

/-- **Equation (124)** of [benIsrael2003generalized], Chapter 8, for the
nonnegative Lebesgue integral. An injective smooth chart multiplies the
parameter integrand by the Gram volume of its derivative. -/
theorem lintegral_areaFormula {n m : ℕ}
    {Ω S : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hsub : S ⊆ Ω)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hf : ∀ x ∈ Ω, HasFDerivAt f (f' x) x) (hfc : ContinuousOn f' Ω)
    (hRank : ∀ x ∈ Ω, Function.Injective (f' x)) (hinj : InjOn f S)
    {g : EuclideanSpace ℝ (Fin m) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ y in f '' S, g y ∂(euclideanHausdorffMeasure n m)) =
      ∫⁻ x in S, ENNReal.ofReal (EuclideanSpace.gram (f' x)) * g (f x) := by
  have hCont : ContinuousOn f S := fun x hx => (hf x (hsub hx)).continuousAt.continuousWithinAt
  have hJ : AEMeasurable (fun x => ENNReal.ofReal (EuclideanSpace.gram (f' x))) (volume.restrict S) :=
    ((ENNReal.continuous_ofReal.comp continuous_gram).comp_continuousOn (hfc.mono hsub)).aemeasurable hS
  have hgS : AEMeasurable (fun x => g (f x)) (volume.restrict S) :=
    hg.comp_aemeasurable (hCont.aemeasurable hS)
  rw [← map_gram_density_eq_hausdorff hΩ hS hsub hf hfc hRank hinj,
    (hCont.measurableEmbedding hS hinj).lintegral_map]
  simp only [Set.domRestrict_apply, ← Function.comp_apply (f := g)]
  rw [lintegral_subtype_comap hS, restrict_withDensity hS]
  simpa only [Pi.mul_apply, Function.comp_apply] using
    lintegral_withDensity_eq_lintegral_mul₀ hJ hgS

end NonnegativeAreaFormula

/-- **Exercise 41**, Equation (171), of [benIsrael2003generalized],
Chapter 8. The normalized Hausdorff area of the Euclidean unit sphere
equals the stated Gamma-function formula. -/
theorem exercise_41_geometric_sphere_area {d : ℕ} (hd : d ≠ 0) :
    (euclideanHausdorffMeasure d (d + 1)).real
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) =
        2 * Real.pi ^ (((d + 1 : ℕ) : ℝ) / 2) / Real.Gamma (((d + 1 : ℕ) : ℝ) / 2) := by
  rw [exercise_41_hemisphere_integral hd, ← exercise_41_hemisphere_integral_angular hd,
    exercise_41_unitSphereArea (Nat.succ_ne_zero d)]

end BenIsraelGreville.Chapter08
