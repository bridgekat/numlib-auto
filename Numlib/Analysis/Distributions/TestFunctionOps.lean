import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Numlib.Analysis.Sobolev.Space
import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Operations on test functions: the `L²` class and the negative Laplacian

Three constructions on the test functions `𝓓(Ω, ℝ)` of an open set `Ω ⊆ ℝ^N`: a test function
on `Ω'` read as a test function on a larger `Ω` (`TestFunction.ofLE`), the class of a test
function in `L²(Ω)` (`TestFunction.toL2`) and its negative Laplacian `−∑ᵢ ∂ᵢ∂ᵢφ`, again a test
function (`TestFunction.negLaplacian`), from the smoothness and support properties of the
second derivatives of a smooth compactly supported function (`Elliptic.laplacianRep_props`).
These are the tools by which the test functions are shown to lie in every `D(A^ℓ)` of the
Dirichlet Laplacian (`Numlib/Analysis/PDE/DirichletLaplacian`).

The last section is the fundamental lemma of the calculus of variations for a function `g`
continuous on `Ω`: `∫_Ω g φ ≥ 0` for every nonnegative test function forces `g ≥ 0` on `Ω`
(`nonneg_on_of_forall_integral_mul_testFunction_nonneg`), and `∫_Ω g φ = 0` for every test
function supported in an open `U ⊆ Ω` forces `g = 0` on `U`
(`eqOn_zero_of_forall_integral_mul_testFunction_eq_zero`).
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

namespace Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second derivative `∂_y ∂_y θ` of a smooth function, as a function. -/
theorem contDiff_fderiv_fderiv_apply {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) (y : E) :
    ContDiff ℝ ∞ fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z y) x y :=
  (((hθ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).fderiv_right (m := ∞)
    le_rfl).clm_apply contDiff_const

variable {N : ℕ}

/-- The Laplacian `Δθ = ∑ᵢ ∂ᵢ∂ᵢθ` of a smooth compactly supported `θ` is smooth, compactly
supported, with support inside the support of `θ`. -/
theorem laplacianRep_props {θ : EuclideanSpace ℝ (Fin N) → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) :
    ContDiff ℝ ∞ (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ∧
    HasCompactSupport (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ∧
    tsupport (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ⊆ tsupport θ := by
  have hsub : tsupport (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ⊆ tsupport θ := by
    refine closure_minimal ((Finset.support_sum _ _).trans ?_) (isClosed_tsupport θ)
    refine Set.iUnion₂_subset fun i _ ↦ subset_closure.trans ?_
    exact (tsupport_fderiv_apply_subset ℝ _).trans (tsupport_fderiv_apply_subset ℝ _)
  refine ⟨ContDiff.sum fun i _ ↦ contDiff_fderiv_fderiv_apply hθ _,
    hθc.of_isClosed_subset (isClosed_tsupport _) hsub, hsub⟩

end Elliptic

open Elliptic

/-- A test function on `Ω'` is a test function on any larger open set. -/
def TestFunction.ofLE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω' : Opens E}
    (ψ : 𝓓(Ω', ℝ)) (h : Ω' ≤ Ω) : 𝓓(Ω, ℝ) where
  toFun := ψ
  contDiff' := ψ.contDiff
  hasCompactSupport' := ψ.hasCompactSupport
  tsupport_subset' := ψ.tsupport_subset.trans h

/-- The function of the test function read on the larger set is the function. -/
@[simp]
theorem TestFunction.ofLE_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω Ω' : Opens E} (ψ : 𝓓(Ω', ℝ)) (h : Ω' ≤ Ω) : (ψ.ofLE h : E → ℝ) = ψ :=
  rfl

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The `L²(Ω)` class of a test function. -/
def TestFunction.toL2 (φ : 𝓓(Ω, ℝ)) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (φ.memLp 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toLp φ

/-- The `L²(Ω)` class of a test function is the function. -/
theorem TestFunction.coeFn_toL2 (φ : 𝓓(Ω, ℝ)) :
    ⇑φ.toL2 =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ :=
  MemLp.coeFn_toLp _

/-- **The negative Laplacian of a test function**, `−∑ᵢ ∂ᵢ∂ᵢ φ`, is a test function. -/
def TestFunction.negLaplacian (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) where
  toFun x := -∑ i, fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single i 1)
  contDiff' := (laplacianRep_props φ.contDiff φ.hasCompactSupport).1.neg
  hasCompactSupport' := (laplacianRep_props φ.contDiff φ.hasCompactSupport).2.1.neg
  tsupport_subset' := by
    refine subset_trans ?_ ((laplacianRep_props φ.contDiff φ.hasCompactSupport).2.2.trans
      φ.tsupport_subset)
    exact (tsupport_neg _).subset

/-- The negative Laplacian of a test function, as a function. -/
theorem TestFunction.negLaplacian_coe (φ : 𝓓(Ω, ℝ)) :
    (φ.negLaplacian : EuclideanSpace ℝ (Fin N) → ℝ)
      = fun x ↦ -∑ i, fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) :=
  rfl

/-! ### The fundamental lemma of the calculus of variations for continuous functions -/

section FundamentalLemma

/-- **The fundamental lemma of the calculus of variations, inequality form**: a function `g`
continuous on an open `Ω ⊆ ℝ^N` with `∫_Ω g φ ≥ 0` for every nonnegative test function `φ` is
nonnegative on `Ω`.  Where `g(x₀) < 0`, a bump at `x₀` supported in `{g < g(x₀)/2}` gives a
negative integral. -/
theorem nonneg_on_of_forall_integral_mul_testFunction_nonneg {g : EuclideanSpace ℝ (Fin N) → ℝ}
    (hg : ContinuousOn g Ω)
    (h : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x * φ x) :
    ∀ x ∈ Ω, 0 ≤ g x := by
  intro x₀ hx₀
  by_contra hneg
  push Not at hneg
  -- a ball around `x₀` inside `Ω` on which `g < g x₀ / 2`
  have hat : ContinuousAt g x₀ := hg.continuousAt (Ω.isOpen.mem_nhds hx₀)
  have hev : ∀ᶠ x in 𝓝 x₀, g x < g x₀ / 2 := hat.eventually (gt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hev.and (Ω.isOpen.mem_nhds hx₀))
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hclosed : closedBall x₀ r ⊆ ball x₀ ε := closedBall_subset_ball (by linarith)
  -- the bump
  let β : ContDiffBump x₀ := ⟨r / 2, r, by positivity, by linarith⟩
  let φ : 𝓓(Ω, ℝ) := ⟨β, β.contDiff, β.hasCompactSupport, by
    rw [β.tsupport_eq]
    exact fun x hx ↦ (hball (hclosed hx)).2⟩
  have hφ : ∀ x, φ x = β x := fun _ ↦ rfl
  have hφ0 : ∀ x, 0 ≤ φ x := fun x ↦ β.nonneg
  have hint := integrable_mul_testFunction (μ := volume) hg φ
  -- the integrand is nonpositive everywhere and negative on the inner ball
  have hnonneg : 0 ≤ fun x ↦ -(g x * φ x) := by
    intro x
    simp only [Pi.zero_apply]
    by_cases hx : x ∈ ball x₀ ε
    · have := (hball hx).1
      rw [neg_nonneg]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hφ0 x)
    · have hφx : φ x = 0 := by
        rw [hφ]
        exact β.zero_of_le_dist (by
          rw [mem_ball] at hx
          push Not at hx
          linarith)
      rw [hφx, mul_zero, neg_zero]
  have hsupp : ball x₀ (r / 2) ⊆ Function.support fun x ↦ -(g x * φ x) := by
    intro x hx
    have h1 : φ x = 1 := by
      rw [hφ]
      exact β.one_of_mem_closedBall (ball_subset_closedBall hx)
    have h2 : g x < g x₀ / 2 := (hball (ball_subset_ball (by linarith) hx)).1
    simp only [Function.mem_support, h1, mul_one, neg_ne_zero]
    exact (by linarith : g x < 0).ne
  have hpos : 0 < (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      (Function.support fun x ↦ -(g x * φ x)) := by
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    have hsub : ball x₀ (r / 2) ∩ (Ω : Set (EuclideanSpace ℝ (Fin N))) = ball x₀ (r / 2) :=
      inter_eq_left.2 fun x hx ↦ (hball (ball_subset_ball (by linarith) hx)).2
    rw [Measure.restrict_apply' Ω.isOpen.measurableSet, hsub]
    exact measure_ball_pos _ _ (by positivity)
  have hlt := (integral_pos_iff_support_of_nonneg hnonneg hint.neg).2 hpos
  rw [integral_neg] at hlt
  linarith [h φ hφ0]

/-- **The fundamental lemma on an open subset**: a function `g` continuous on `Ω` with
`∫_Ω g φ = 0` for every test function supported in an open `U ⊆ Ω` vanishes on `U`
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` and continuity). -/
theorem eqOn_zero_of_forall_integral_mul_testFunction_eq_zero {g : EuclideanSpace ℝ (Fin N) → ℝ}
    (hg : ContinuousOn g Ω) {U : Set (EuclideanSpace ℝ (Fin N))} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω)
    (h : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U →
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x * φ x = 0) :
    ∀ x ∈ U, g x = 0 := by
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    ((hg.mono hUΩ).locallyIntegrableOn hU.measurableSet) fun ψ hψ hψc hψs ↦ by
    let φ : 𝓓(Ω, ℝ) := ⟨ψ, hψ, hψc, hψs.trans hUΩ⟩
    have := h φ hψs
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hUΩ (hψs h)), zero_smul]]
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [smul_eq_mul]
      rw [mul_comm]
      rfl)
  have hae : g =ᵐ[volume.restrict U] 0 := (ae_restrict_iff' hU.measurableSet).2 key
  exact Measure.eqOn_open_of_ae_eq hae hU (hg.mono hUΩ) continuousOn_const

end FundamentalLemma
