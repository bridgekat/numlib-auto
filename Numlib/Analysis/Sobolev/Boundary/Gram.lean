/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.PiL2` (the Gram determinant of a linear map
between Euclidean spaces) or, once a surface measure exists there,
`Mathlib.MeasureTheory.Measure.Hausdorff`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.Analysis.Sobolev.Chart

/-!
# The Gram determinant of a linear map `ℝ^d → ℝ^N`

The Gram determinant of a linear map `L : ℝ^d → ℝ^N`, `gramDet L = det (Lᵀ L)`, and its square
root `gram L`, the `d`-dimensional volume scaling of `L`. It is the density with which a `C¹`
parametrization `Φ : ℝ^d ⊇ D → ℝ^N` transports Lebesgue measure to a surface measure,
`∫ f dσ = ∫_D f (Φ x') gram (DΦ x') dx'`, and the three identities proved here are what make that
transport independent of the parametrization: `gram (L ∘ A) = gram L · |det A|` for a square `A`
(so two parametrizations related by a `C¹` transition give the same measure, through Mathlib's
change of variables `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`),
`gram (U ∘ L) = gram L` for an isometry `U` (rigid motions do not change it), and
`gram (v ↦ (v, ℓ v)) = √(1 + ‖ℓ‖²)` for the graph map of a linear form `ℓ`, the classical
`√(1 + |∇g|²)`. Kept apart from `Numlib/Analysis/Sobolev/Boundary/GraphMeasure.lean` so that a
later chart-based (Brezis-style) surface measure can reuse it (decision B2 of
`notes/boundary/planning-brief.md`).

Matrices are taken with respect to the standard orthonormal bases
`(EuclideanSpace.basisFun (Fin d) ℝ).toBasis` and `(EuclideanSpace.basisFun (Fin N) ℝ).toBasis`
through `LinearMap.toMatrix` (`EuclideanSpace.stdMatrix`), so that `Lᵀ L` is the matrix of inner
products `⟪L eᵢ, L eⱼ⟫` (`gramDet_eq_det_of_inner`), which is the form every identity is proved
through.

## Main definitions

* `EuclideanSpace.stdMatrix L`, the matrix of `L : ℝ^d →L[ℝ] ℝ^N` in the standard bases;
* `EuclideanSpace.gramDet L = det (Mᵀ M)` and `EuclideanSpace.gram L = √(gramDet L)`;
* `EuclideanSpace.snocLastL ℓ`, the graph map `v ↦ (v, ℓ v)` of a linear form as a continuous
  linear map `ℝ^d →L[ℝ] ℝ^{d+1}`.

## Main statements

* `EuclideanSpace.gramDet_nonneg`: `Mᵀ M` is positive semidefinite;
* `EuclideanSpace.gram_comp`: `gram (L ∘L A) = gram L * |det A|`;
* `EuclideanSpace.gram_isometry_comp`: `gram (U ∘L L) = gram L` for a linear isometry `U`;
* `EuclideanSpace.gram_snocLastL`: `gram (snocLastL ℓ) = √(1 + ‖ℓ‖²)`.
-/

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace EuclideanSpace

variable {d N : ℕ}

/-! ### The matrix of a linear map in the standard bases -/

/-- The matrix of `L : ℝ^d →L[ℝ] ℝ^N` with respect to the standard orthonormal bases: the
`Matrix (Fin N) (Fin d) ℝ` whose `j`-th column is `L e_j`. -/
def stdMatrix (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    Matrix (Fin N) (Fin d) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis L

/-- The entries of the standard matrix are the coordinates of the images of the basis vectors. -/
theorem stdMatrix_apply (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (i : Fin N) (j : Fin d) : stdMatrix L i j = L (single j 1) i := by
  rw [stdMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    basisFun_repr, OrthonormalBasis.coe_toBasis, basisFun_apply]
  rfl

/-- The standard matrix of a composite is the product of the standard matrices. -/
theorem stdMatrix_comp (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    stdMatrix (L ∘L A) = stdMatrix L * stdMatrix A := by
  rw [stdMatrix, stdMatrix, stdMatrix, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix_comp _ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]

/-- The determinant of the standard matrix of an endomorphism is its determinant. -/
theorem det_stdMatrix (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    (stdMatrix A).det
      = LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
  LinearMap.det_toMatrix _ _

/-! ### The Gram determinant -/

/-- **The Gram determinant** of `L : ℝ^d →L[ℝ] ℝ^N`: the determinant of the Gram matrix `Mᵀ * M`
of the standard matrix `M := stdMatrix L`, that is of the matrix `(⟪L eᵢ, L eⱼ⟫)ᵢⱼ` of inner
products of the images of the basis vectors (`gramDet_eq_det_of_inner`). Its square root
`EuclideanSpace.gram L` is the `d`-dimensional volume scaling factor of `L`. -/
def gramDet (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) : ℝ :=
  ((stdMatrix L)ᵀ * stdMatrix L).det

/-- The Gram determinant is the determinant of the matrix of inner products
`⟪L eᵢ, L eⱼ⟫` of the images of the standard basis vectors. -/
theorem gramDet_eq_det_of_inner (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    gramDet L = (Matrix.of fun i j ↦ ⟪L (single i 1), L (single j 1)⟫_ℝ).det := by
  unfold gramDet
  congr 1
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, stdMatrix_apply, Matrix.of_apply,
    inner_eq_star_dotProduct, dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/-- The Gram determinant is nonnegative: `Mᵀ * M` is positive semidefinite. -/
theorem gramDet_nonneg (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    0 ≤ gramDet L := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (stdMatrix L)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_nonneg

/-- **The Gram determinant of a composite with a square map**:
`gramDet (L ∘L A) = gramDet L * (det A)²` for `A : ℝ^d →L[ℝ] ℝ^d`, since the Gram matrix of
`L ∘L A` is `Aᵀ (Mᵀ M) A`. -/
theorem gramDet_comp (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    gramDet (L ∘L A) = gramDet L * LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin d)) ^ 2 := by
  unfold gramDet
  rw [stdMatrix_comp, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (stdMatrix L)ᵀ,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_stdMatrix]
  ring

/-- **A linear isometry of the target does not change the Gram determinant**: the inner products
`⟪U (L eᵢ), U (L eⱼ)⟫` are the `⟪L eᵢ, L eⱼ⟫`. -/
theorem gramDet_isometry_comp (U : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    gramDet ((U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) ∘L L) = gramDet L := by
  rw [gramDet_eq_det_of_inner, gramDet_eq_det_of_inner]
  congr 1
  ext i j
  simp [LinearIsometryEquiv.inner_map_map]

/-! ### The graph map of a linear form -/

/-- **The graph map of a linear form** `ℓ : ℝ^d →L[ℝ] ℝ` as a continuous linear map
`ℝ^d →L[ℝ] ℝ^{d+1}`: `v ↦ snocLast v (ℓ v) = (v, ℓ v)`. It is the derivative of the graph
parametrization `x' ↦ (x', g x')` at a point where `g` has derivative `ℓ`
(`EuclideanSpace.hasFDerivAt_graphParam` in `Boundary/GraphMeasure.lean`). -/
def snocLastL (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  ((lastInitL d).symm : ℝ × EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) ∘L
    ℓ.prod (ContinuousLinearMap.id ℝ _)

@[simp]
theorem snocLastL_apply (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    snocLastL ℓ v = snocLast v (ℓ v) :=
  rfl

/-- **The Gram determinant of a graph map**: `gramDet (snocLastL ℓ) = 1 + ∑ i, (ℓ eᵢ)²`. The
Gram matrix is `1 + u uᵀ` with `u i = ℓ eᵢ`, and the matrix determinant lemma
`Matrix.det_one_add_replicateCol_mul_replicateRow` gives `1 + u ⬝ᵥ u`. -/
theorem gramDet_snocLastL (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    gramDet (snocLastL ℓ) = 1 + ∑ i, (ℓ (single i 1)) ^ 2 := by
  rw [gramDet_eq_det_of_inner]
  have h : (Matrix.of fun i j ↦ ⟪snocLastL ℓ (single i 1), snocLastL ℓ (single j 1)⟫_ℝ)
      = 1 + replicateCol Unit (fun i ↦ ℓ (single i 1)) *
        replicateRow Unit (fun i ↦ ℓ (single i 1)) := by
    rw [← vecMulVec_eq]
    ext i j
    simp only [Matrix.of_apply, snocLastL_apply, inner_snocLast, Matrix.add_apply, Matrix.one_apply,
      vecMulVec_apply, EuclideanSpace.inner_single_left, conj_trivial, one_mul, PiLp.single_apply]
  rw [h, det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, sq]

/-- **The Gram determinant of a graph map is `1 + ‖ℓ‖²`**: the sum `∑ i, (ℓ eᵢ)²` is the squared
norm of the Riesz representative of `ℓ`, which is `‖ℓ‖`. For `ℓ = fderiv ℝ g x` this is
`1 + ‖gradient g x‖ ^ 2`, since `gradient g x = (toDual ℝ _).symm (fderiv ℝ g x)`. -/
theorem gramDet_snocLastL_eq_one_add_norm_sq (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    gramDet (snocLastL ℓ) = 1 + ‖ℓ‖ ^ 2 := by
  rw [gramDet_snocLastL]
  congr 1
  have h1 : ‖ℓ‖ = ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ℓ‖ := by
    rw [LinearIsometryEquiv.norm_map]
  have h2 : ∀ i, ℓ (single i 1)
      = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ℓ i := fun i ↦ by
    rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right]
    simp
  simp only [h1, h2, EuclideanSpace.real_norm_sq_eq]

/-! ### The volume scaling factor `gram L = √(gramDet L)` -/

/-- **The `d`-dimensional volume scaling factor** `gram L = √(gramDet L)` of `L : ℝ^d →L[ℝ] ℝ^N`:
the density with which a parametrization with derivative `L` transports `d`-dimensional Lebesgue
measure. -/
def gram (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) : ℝ :=
  Real.sqrt (gramDet L)

theorem gram_nonneg (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) : 0 ≤ gram L :=
  Real.sqrt_nonneg _

theorem gram_sq (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    gram L ^ 2 = gramDet L :=
  Real.sq_sqrt (gramDet_nonneg L)

/-- **The change-of-parameters identity** at a single point: `gram (L ∘L A) = gram L * |det A|`
for `A : ℝ^d →L[ℝ] ℝ^d` — the identity `gram (Φ ∘ ψ) = (gram Φ ∘ ψ) · |det Dψ|` of decision B2 of
`notes/boundary/planning-brief.md`, applied in `EuclideanSpace.graphDensity_graphTransition`. -/
theorem gram_comp (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    gram (L ∘L A) = gram L * |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin d))| := by
  rw [gram, gram, gramDet_comp, Real.sqrt_mul (gramDet_nonneg L), Real.sqrt_sq_eq_abs]

/-- A linear isometry of the target does not change the volume scaling factor. -/
theorem gram_isometry_comp (U : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    gram ((U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) ∘L L) = gram L := by
  rw [gram, gram, gramDet_isometry_comp]

/-- **The surface element of a graph**: `gram (snocLastL ℓ) = √(1 + ‖ℓ‖²)`, the classical
`√(1 + |∇g|²)` for `ℓ = fderiv ℝ g x`. -/
theorem gram_snocLastL (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    gram (snocLastL ℓ) = Real.sqrt (1 + ‖ℓ‖ ^ 2) := by
  rw [gram, gramDet_snocLastL_eq_one_add_norm_sq]

end EuclideanSpace

end
