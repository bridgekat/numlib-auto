import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Numlib.Analysis.Sobolev.Space

/-!
# Operations on test functions: the `L²` class and the negative Laplacian

Three constructions on the test functions `𝓓(Ω, ℝ)` of an open set `Ω ⊆ ℝ^N`: a test function
on `Ω'` read as a test function on a larger `Ω` (`TestFunction.ofLE`), the class of a test
function in `L²(Ω)` (`TestFunction.toL2`) and its negative Laplacian `−∑ᵢ ∂ᵢ∂ᵢφ`, again a test
function (`TestFunction.negLaplacian`), from the smoothness and support properties of the
second derivatives of a smooth compactly supported function (`Elliptic.laplacianRep_props`).
These are the tools by which the test functions are shown to lie in every `D(A^ℓ)` of the
Dirichlet Laplacian (`Numlib/Analysis/PDE/DirichletLaplacian`).
-/

open Filter MeasureTheory Set TopologicalSpace
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
