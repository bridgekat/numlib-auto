/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# The Gram determinant of a linear map $\mathbb{R}^d \to \mathbb{R}^N$

Let $L : \mathbb{R}^d \to \mathbb{R}^N$ be linear, with matrix $M \in \mathbb{R}^{N \times d}$ in
the standard bases. Its **Gram determinant** is $\det(M^T M)$, and its square root
$\sqrt{\det(M^T M)}$ is the factor by which $L$ scales $d$-dimensional volume. It is the density
with which a $C^1$ parametrization $\Phi : D \to \mathbb{R}^N$, $D \subseteq \mathbb{R}^d$, carries
Lebesgue measure to a surface measure,
$$\int f \, d\sigma = \int_D f(\Phi(x')) \sqrt{\det\bigl(D\Phi(x')^T D\Phi(x')\bigr)} \, dx'.$$
This file proves the three identities that make this measure independent of the parametrization. For
a square matrix $A$, the factor of $L A$ is the factor of $L$ times $|\det A|$; with Mathlib's
change of variables `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`, two
parametrizations related by a $C^1$ transition then give the same measure. A linear isometry $U$ of
$\mathbb{R}^N$ does not change the factor, so rigid motions do not change the measure. For the graph
map $v \mapsto (v, \ell v)$ of a linear form $\ell$ the factor is $\sqrt{1 + \|\ell\|^2}$, the
classical surface element $\sqrt{1 + |\nabla g|^2}$. This file is separate from
`Numlib.Analysis.Sobolev.Boundary.GraphMeasure` so that a surface measure built from charts can also
use it.

## Main definitions

* `EuclideanSpace.stdMatrix`: the matrix of a linear map $\mathbb{R}^d \to \mathbb{R}^N$ in the
  standard bases.
* `EuclideanSpace.gramDet`: the Gram determinant $\det(M^T M)$.
* `EuclideanSpace.gram`: the volume scaling factor $\sqrt{\det(M^T M)}$.
* `EuclideanSpace.snocLastL`: the graph map $v \mapsto (v, \ell v)$ of a linear form $\ell$, as a
  continuous linear map $\mathbb{R}^d \to \mathbb{R}^{d+1}$.

## Main results

* `EuclideanSpace.gramDet_nonneg`: the Gram determinant is nonnegative.
* `EuclideanSpace.gram_comp`: $\operatorname{gram}(L \circ A) = \operatorname{gram}(L) \, |\det A|$
  for $A : \mathbb{R}^d \to \mathbb{R}^d$.
* `EuclideanSpace.gram_isometry_comp`: $\operatorname{gram}(U \circ L) = \operatorname{gram}(L)$ for
  a linear isometry $U$ of $\mathbb{R}^N$.
* `EuclideanSpace.gram_snocLastL`: the graph map of $\ell$ has
  $\operatorname{gram} = \sqrt{1 + \|\ell\|^2}$.

## Implementation notes

* Matrices are taken with respect to the standard orthonormal bases
  `(EuclideanSpace.basisFun (Fin d) ℝ).toBasis` and `(EuclideanSpace.basisFun (Fin N) ℝ).toBasis`
  through `LinearMap.toMatrix`. Then $M^T M$ is the matrix of inner products
  $\langle L e_i, L e_j \rangle$ (`EuclideanSpace.gramDet_eq_det_of_inner`), and every identity is
  proved in this form.
-/

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace EuclideanSpace

variable {d N : ℕ}

/-! ### The matrix of a linear map in the standard bases -/

/-- **The standard matrix** of a continuous linear map $L : \mathbb{R}^d \to \mathbb{R}^N$: the
matrix $M \in \mathbb{R}^{N \times d}$ of $L$ with respect to the standard orthonormal bases,
whose $j$-th column is $L e_j$. -/
def stdMatrix (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    Matrix (Fin N) (Fin d) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis L

/-- The entries of the standard matrix are the coordinates of the images of the basis vectors:
$M_{ij} = (L e_j)_i$. -/
theorem stdMatrix_apply (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (i : Fin N) (j : Fin d) : stdMatrix L i j = L (single j 1) i := by
  rw [stdMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    basisFun_repr, OrthonormalBasis.coe_toBasis, basisFun_apply]
  rfl

/-- The standard matrix of a composition is the product of the standard matrices: for
$L : \mathbb{R}^d \to \mathbb{R}^N$ and $A : \mathbb{R}^d \to \mathbb{R}^d$, the matrix of
$L \circ A$ is the matrix of $L$ times the matrix of $A$. -/
theorem stdMatrix_comp (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    stdMatrix (L ∘L A) = stdMatrix L * stdMatrix A := by
  rw [stdMatrix, stdMatrix, stdMatrix, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix_comp _ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]

/-- For a linear map $A : \mathbb{R}^d \to \mathbb{R}^d$, the determinant of the standard matrix of
$A$ is the determinant of $A$. -/
theorem det_stdMatrix (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    (stdMatrix A).det
      = LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
  LinearMap.det_toMatrix _ _

/-! ### The Gram determinant -/

/-- **The Gram determinant** of a continuous linear map $L : \mathbb{R}^d \to \mathbb{R}^N$: the
number $\det(M^T M)$, where $M$ is the standard matrix of $L$.

The matrix $M^T M$ is the matrix $(\langle L e_i, L e_j \rangle)_{ij}$ of inner products of the
images of the basis vectors (`EuclideanSpace.gramDet_eq_det_of_inner`). Its square root
`EuclideanSpace.gram L` is the $d$-dimensional volume scaling factor of $L$. -/
def gramDet (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) : ℝ :=
  ((stdMatrix L)ᵀ * stdMatrix L).det

/-- The Gram determinant of $L : \mathbb{R}^d \to \mathbb{R}^N$ is the determinant of the matrix of
inner products of the images of the standard basis vectors:
$$\operatorname{gramDet} L = \det\bigl(\langle L e_i, L e_j \rangle\bigr)_{i,j=1}^d.$$
-/
theorem gramDet_eq_det_of_inner (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    gramDet L = (Matrix.of fun i j ↦ ⟪L (single i 1), L (single j 1)⟫_ℝ).det := by
  unfold gramDet
  congr 1
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, stdMatrix_apply, Matrix.of_apply,
    inner_eq_star_dotProduct, dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/-- The Gram determinant is nonnegative: $\det(M^T M) \ge 0$, because $M^T M$ is positive
semidefinite. -/
theorem gramDet_nonneg (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    0 ≤ gramDet L := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (stdMatrix L)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_nonneg

/-- **The Gram determinant of a composition with a square map.** For
$L : \mathbb{R}^d \to \mathbb{R}^N$ and $A : \mathbb{R}^d \to \mathbb{R}^d$,
$$\operatorname{gramDet}(L \circ A) = \operatorname{gramDet}(L) \, (\det A)^2.$$

The Gram matrix of $L \circ A$ is $A^T (M^T M) A$. -/
theorem gramDet_comp (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    gramDet (L ∘L A) = gramDet L * LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin d)) ^ 2 := by
  unfold gramDet
  rw [stdMatrix_comp, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (stdMatrix L)ᵀ,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_stdMatrix]
  ring

/-- **A linear isometry of the target does not change the Gram determinant.** For a linear isometric
equivalence $U$ of $\mathbb{R}^N$ and $L : \mathbb{R}^d \to \mathbb{R}^N$,
$\operatorname{gramDet}(U \circ L) = \operatorname{gramDet}(L)$, because $\langle U L e_i, U L
e_j \rangle = \langle L e_i, L e_j \rangle$. -/
theorem gramDet_isometry_comp (U : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    gramDet ((U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) ∘L L) = gramDet L := by
  rw [gramDet_eq_det_of_inner, gramDet_eq_det_of_inner]
  congr 1
  ext i j
  simp [LinearIsometryEquiv.inner_map_map]

/-! ### The graph map of a linear form -/

/-- **The graph map of a linear form** $\ell : \mathbb{R}^d \to \mathbb{R}$: the continuous linear
map $\mathbb{R}^d \to \mathbb{R}^{d+1}$, $v \mapsto (v, \ell v)$, with $\ell v$ as the last
coordinate.

It is the derivative of the graph parametrization $x' \mapsto (x', g(x'))$ at a point where $g$
has derivative $\ell$ (`EuclideanSpace.hasFDerivAt_graphParam` in
`Numlib.Analysis.Sobolev.Boundary.GraphMeasure`). -/
def snocLastL (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  ((lastInitL d).symm : ℝ × EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) ∘L
    ℓ.prod (ContinuousLinearMap.id ℝ _)

/-- The graph map of $\ell$ sends $v$ to $(v, \ell v)$, that is `EuclideanSpace.snocLast v (ℓ v)`.
-/
@[simp]
theorem snocLastL_apply (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    snocLastL ℓ v = snocLast v (ℓ v) :=
  rfl

/-- **The Gram determinant of a graph map.** For a linear form $\ell : \mathbb{R}^d \to \mathbb{R}$,
the graph map $v \mapsto (v, \ell v)$ has
$$\operatorname{gramDet} = 1 + \sum_{i=1}^d (\ell e_i)^2.$$

The Gram matrix is $I + u u^T$ with $u_i = \ell e_i$, and the matrix determinant lemma
`Matrix.det_one_add_replicateCol_mul_replicateRow` gives $1 + u^T u$. -/
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

/-- **The Gram determinant of a graph map is $1 + \|\ell\|^2$.** For a continuous linear form
$\ell : \mathbb{R}^d \to \mathbb{R}$ with operator norm $\|\ell\|$, the graph map
$v \mapsto (v, \ell v)$ has $\operatorname{gramDet} = 1 + \|\ell\|^2$.

The sum $\sum_i (\ell e_i)^2$ is the squared norm of the Riesz representative of $\ell$, and the
norm of that representative is $\|\ell\|$. For $\ell = Dg(x)$ this is $1 + \|\nabla g(x)\|^2$,
since `gradient g x` is `(InnerProductSpace.toDual ℝ _).symm (fderiv ℝ g x)`. -/
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

/-! ### The volume scaling factor $\sqrt{\det(M^T M)}$ -/

/-- **The $d$-dimensional volume scaling factor** of a continuous linear map
$L : \mathbb{R}^d \to \mathbb{R}^N$: the square root $\operatorname{gram} L =
\sqrt{\operatorname{gramDet} L}$ of its Gram determinant. It is the density with which a
parametrization with derivative $L$ carries $d$-dimensional Lebesgue measure to a surface. -/
def gram (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) : ℝ :=
  Real.sqrt (gramDet L)

/-- The volume scaling factor is nonnegative: $\operatorname{gram} L \ge 0$. -/
theorem gram_nonneg (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) : 0 ≤ gram L :=
  Real.sqrt_nonneg _

/-- The square of the volume scaling factor is the Gram determinant: $(\operatorname{gram} L)^2 =
\operatorname{gramDet} L$. -/
theorem gram_sq (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    gram L ^ 2 = gramDet L :=
  Real.sq_sqrt (gramDet_nonneg L)

/-- **The change-of-parameters identity at one point.** For $L : \mathbb{R}^d \to \mathbb{R}^N$ and
$A : \mathbb{R}^d \to \mathbb{R}^d$,
$$\operatorname{gram}(L \circ A) = \operatorname{gram}(L) \, |\det A|.$$

Applied to the derivatives of parametrizations, it gives $\operatorname{gram} D(\Phi \circ
\psi) = (\operatorname{gram} D\Phi \circ \psi) \, |\det D\psi|$ for a change of parameters
$\psi$; it is used in this form in `EuclideanSpace.graphDensity_graphTransition`. -/
theorem gram_comp (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    gram (L ∘L A) = gram L * |LinearMap.det (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin d))| := by
  rw [gram, gram, gramDet_comp, Real.sqrt_mul (gramDet_nonneg L), Real.sqrt_sq_eq_abs]

/-- A linear isometry of the target does not change the volume scaling factor: for a linear
isometric equivalence $U$ of $\mathbb{R}^N$ and $L : \mathbb{R}^d \to \mathbb{R}^N$,
$\operatorname{gram}(U \circ L) = \operatorname{gram}(L)$. -/
theorem gram_isometry_comp (U : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    gram ((U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) ∘L L) = gram L := by
  rw [gram, gram, gramDet_isometry_comp]

/-- **The surface element of a graph.** For a continuous linear form
$\ell : \mathbb{R}^d \to \mathbb{R}$, the graph map $v \mapsto (v, \ell v)$ has
$$\operatorname{gram} = \sqrt{1 + \|\ell\|^2}.$$
For $\ell = Dg(x)$ this is the classical surface element $\sqrt{1 + |\nabla g(x)|^2}$. -/
theorem gram_snocLastL (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    gram (snocLastL ℓ) = Real.sqrt (1 + ‖ℓ‖ ^ 2) := by
  rw [gram, gramDet_snocLastL_eq_one_add_norm_sq]

end EuclideanSpace

end
