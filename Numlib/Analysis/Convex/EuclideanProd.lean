/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.InnerProductSpace.EuclideanProd

/-!
# Convexity along the concatenation of coordinates

Let $J : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}^{m+n}$ be the concatenation of coordinates,
$J(x, y) = (x_1, \dots, x_m, y_1, \dots, y_n)$. A text on convex analysis in $\mathbb{R}^n$, such as
[rockafellar1970convex], identifies $\mathbb{R}^m \times \mathbb{R}^n$ with $\mathbb{R}^{m+n}$
without comment, but in Lean the two spaces are different types. This module shows that the
conjugate, the subdifferential and the relative interior commute with $J$. The map $J$ itself, its
coordinates and its inner product are in `Numlib.Analysis.InnerProductSpace.EuclideanProd`.

All results come from one identity, `inner_euclideanProdEquiv`: $\langle J(u, x), J(v, y) \rangle =
\langle u, v \rangle + \langle x, y \rangle$. Thus the inner product of $\mathbb{R}^{m+n}$, read
through $J$, is the product pairing of $\mathbb{R}^m \times \mathbb{R}^n$ with itself. Each
transport result applies a general rule for a change of variables by a linear equivalence that is
adjoint for the two pairings: `ConvexAnalysis.convexConj_comp_linearEquiv` for the conjugate,
`ConvexAnalysis.subdifferential_comp_linearEquiv` for the subdifferential, and `Convex.relint_image`
for the relative interior. The corresponding rules for polar cones and cone hulls,
`ConvexAnalysis.polarCone_image_of_pairing_eq` and `ConvexAnalysis.coe_hull_image`, are in
`Numlib.Analysis.Convex.Duality.Polar`.

## Main results

* `ConvexAnalysis.prodPairing_euclideanProdEquiv_symm`: the product pairing of $J^{-1} z$ and $q$ is
  $\langle z, J q \rangle$.
* `ConvexAnalysis.isAdjointPair_euclideanProdEquiv`: $J^{-1}$ and $J$ are adjoint for the inner
  product of $\mathbb{R}^{m+n}$ and the product pairing.
* `ConvexAnalysis.convexConj_comp_euclideanProdEquiv`: the conjugate of $f \circ J^{-1}$ is
  $f^* \circ J^{-1}$.
* `ConvexAnalysis.subdifferential_comp_euclideanProdEquiv`: $\partial (f \circ J^{-1})(z) =
  J(\partial f(J^{-1} z))$.
* `ConvexAnalysis.relint_image_euclideanProdEquiv`,
  `ConvexAnalysis.relint_image_euclideanProdEquiv_symm`: $J$ and $J^{-1}$ map the relative interior
  of a convex set onto the relative interior of its image.

## Implementation notes

* The map $J$ is `euclideanProdEquiv m n`, a continuous linear equivalence from the plain product
  `EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)` to `EuclideanSpace ℝ (Fin (m + n))`.
* The product pairing is `ConvexAnalysis.prodPairing` of the two inner products `innerₗ`, which
  sends $((u, x), (v, y))$ to $\langle u, v \rangle + \langle x, y \rangle$.
-/

open Set

namespace ConvexAnalysis

/-! ### The adjointness of the concatenation -/

section Pairing

variable {m n : ℕ}

/-- For $z \in \mathbb{R}^{m+n}$ and $q \in \mathbb{R}^m \times \mathbb{R}^n$, the product pairing
of $J^{-1} z$ and $q$ equals $\langle z, J q \rangle$, where $J$ is the concatenation of
coordinates. -/
theorem prodPairing_euclideanProdEquiv_symm (z : EuclideanSpace ℝ (Fin (m + n)))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    prodPairing (innerₗ (EuclideanSpace ℝ (Fin m))) (innerₗ (EuclideanSpace ℝ (Fin n)))
        ((euclideanProdEquiv m n).symm z) q
      = innerₗ (EuclideanSpace ℝ (Fin (m + n))) z (euclideanProdEquiv m n q) := by
  have h := inner_euclideanProdEquiv ((euclideanProdEquiv m n).symm z) q
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Let $J : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}^{m+n}$ be the concatenation of
coordinates. The maps $J^{-1}$ and $J$ are an **adjoint pair** for the inner product of
$\mathbb{R}^{m+n}$ and the product pairing of $\mathbb{R}^m \times \mathbb{R}^n$: for all
$z \in \mathbb{R}^{m+n}$ and $q \in \mathbb{R}^m \times \mathbb{R}^n$,
$$\langle J^{-1} z, q \rangle_{\mathbb{R}^m \times \mathbb{R}^n} = \langle z, J q
  \rangle_{\mathbb{R}^{m+n}}.$$

This is the hypothesis `ConvexAnalysis.IsAdjointPair` that
`ConvexAnalysis.convexConj_comp_linearEquiv` and
`ConvexAnalysis.subdifferential_comp_linearEquiv` take. It is the only mathematical input of the
transport results of this module. -/
theorem isAdjointPair_euclideanProdEquiv :
    IsAdjointPair (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
      (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m))) (innerₗ (EuclideanSpace ℝ (Fin n))))
      ((euclideanProdEquiv m n).symm.toLinearEquiv : EuclideanSpace ℝ (Fin (m + n)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
      ((euclideanProdEquiv m n).toLinearEquiv :
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (m + n))) :=
  fun z q => prodPairing_euclideanProdEquiv_symm z q

end Pairing

/-! ### The transport -/

section Transport

variable {m n : ℕ}

/-- Let $f : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ and let $J$ be the
concatenation of coordinates. Then for every $z \in \mathbb{R}^{m+n}$,
$$(f \circ J^{-1})^*(z) = f^*(J^{-1} z),$$
where the conjugate on the left is taken for the inner product of $\mathbb{R}^{m+n}$, and the
conjugate on the right for the product pairing of $\mathbb{R}^m \times \mathbb{R}^n$.

The proof specializes `ConvexAnalysis.convexConj_comp_linearEquiv` to
`ConvexAnalysis.isAdjointPair_euclideanProdEquiv`. -/
theorem convexConj_comp_euclideanProdEquiv (f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
    → EReal) (z : EuclideanSpace ℝ (Fin (m + n))) :
    convexConj (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
        (fun w => f ((euclideanProdEquiv m n).symm w)) z
      = convexConj (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m)))
          (innerₗ (EuclideanSpace ℝ (Fin n)))) f ((euclideanProdEquiv m n).symm z) :=
  convexConj_comp_linearEquiv (euclideanProdEquiv m n).symm.toLinearEquiv
    (euclideanProdEquiv m n).toLinearEquiv isAdjointPair_euclideanProdEquiv f z

/-- Let $f : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ and let $J$ be the
concatenation of coordinates. Then for every $z \in \mathbb{R}^{m+n}$,
$$\partial (f \circ J^{-1})(z) = J\bigl(\partial f(J^{-1} z)\bigr),$$
where the subdifferential on the left is taken for the inner product of $\mathbb{R}^{m+n}$, and
the subdifferential on the right for the product pairing of $\mathbb{R}^m \times \mathbb{R}^n$.

The proof specializes `ConvexAnalysis.subdifferential_comp_linearEquiv` to
`ConvexAnalysis.isAdjointPair_euclideanProdEquiv`. -/
theorem subdifferential_comp_euclideanProdEquiv (f : EuclideanSpace ℝ (Fin m) ×
    EuclideanSpace ℝ (Fin n) → EReal) (z : EuclideanSpace ℝ (Fin (m + n))) :
    subdifferential (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
        (fun w => f ((euclideanProdEquiv m n).symm w)) z
      = euclideanProdEquiv m n '' subdifferential (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m)))
          (innerₗ (EuclideanSpace ℝ (Fin n)))) f ((euclideanProdEquiv m n).symm z) :=
  subdifferential_comp_linearEquiv (euclideanProdEquiv m n).symm.toLinearEquiv
    (euclideanProdEquiv m n).toLinearEquiv isAdjointPair_euclideanProdEquiv f z

/-- Let $C \subseteq \mathbb{R}^m \times \mathbb{R}^n$ be convex and let $J$ be the concatenation of
coordinates. Then
$$\operatorname{ri} J(C) = J(\operatorname{ri} C).$$

The relative interior $\operatorname{ri}$ is `intrinsicInterior ℝ`. The proof specializes
`Convex.relint_image`. -/
theorem relint_image_euclideanProdEquiv
    {C : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C) :
    ri (euclideanProdEquiv m n '' C) = euclideanProdEquiv m n '' ri C :=
  Convex.relint_image hC (euclideanProdEquiv m n).toLinearEquiv.toLinearMap

/-- Let $D \subseteq \mathbb{R}^{m+n}$ be convex and let $J$ be the concatenation of coordinates.
Then $\operatorname{ri} J^{-1}(D) = J^{-1}(\operatorname{ri} D)$. -/
theorem relint_image_euclideanProdEquiv_symm {D : Set (EuclideanSpace ℝ (Fin (m + n)))}
    (hD : Convex ℝ D) :
    ri ((euclideanProdEquiv m n).symm '' D) = (euclideanProdEquiv m n).symm '' ri D :=
  Convex.relint_image hD (euclideanProdEquiv m n).symm.toLinearEquiv.toLinearMap

end Transport

end ConvexAnalysis
