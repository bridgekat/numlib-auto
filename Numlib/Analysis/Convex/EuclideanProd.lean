import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.InnerProductSpace.EuclideanProd

/-!
# Convexity along the concatenation of coordinates

`EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin (m + n))` are
different types, and a text written in `ℝⁿ` moves between them without comment. The move itself —
the concatenation `euclideanProdEquiv`, its coordinates and its inner product — is
`Numlib/Analysis/InnerProductSpace/EuclideanProd`, which knows nothing of convexity. This module is
what a convexity statement needs on top of it: the transport along the concatenation of
`convexConj`, `subdifferential` and `ri`.

Everything turns on `inner_euclideanProdEquiv`: concatenation adds the two inner products, so the
form `prodPairing` that a product is paired with *is* the inner product of `ℝᵐ⁺ⁿ` read through the
concatenation. `isAdjointPair_euclideanProdEquiv` packages that as an adjointness datum, and each
transport lemma is one application of a general substitution rule to it —
`convexConj_comp_linearEquiv` of `Duality/Conjugate`, `subdifferential_comp_linearEquiv` of
`Subdifferential/Calculus`, `Convex.relint_image` of `RelativeInterior`. The two rules a statement
about *cones* needs, `polarCone_image_of_pairing_eq` and `coe_hull_image`, are in `Duality/Polar`
with the rest of the polarity calculus.

## Main results

* `prodPairing_euclideanProdEquiv_symm`, `isAdjointPair_euclideanProdEquiv` — the pairing pulled
  back along the concatenation, and the adjointness datum every transport below consumes.
* `convexConj_comp_euclideanProdEquiv`, `subdifferential_comp_euclideanProdEquiv`,
  `relint_image_euclideanProdEquiv`, `relint_image_euclideanProdEquiv_symm` — conjugate,
  subdifferential and relative interior transport.

## References

* [rockafellar1970convex].
-/

open Set

namespace ConvexAnalysis

/-! ### The adjointness datum -/

section Pairing

variable {m n : ℕ}

/-- The inner product of `ℝᵐ⁺ⁿ` pulled back along the concatenation is `prodPairing`. -/
theorem prodPairing_euclideanProdEquiv_symm (z : EuclideanSpace ℝ (Fin (m + n)))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    prodPairing (innerₗ (EuclideanSpace ℝ (Fin m))) (innerₗ (EuclideanSpace ℝ (Fin n)))
        ((euclideanProdEquiv m n).symm z) q
      = innerₗ (EuclideanSpace ℝ (Fin (m + n))) z (euclideanProdEquiv m n q) := by
  have h := inner_euclideanProdEquiv ((euclideanProdEquiv m n).symm z) q
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **Concatenation is an adjoint pair for the two pairings.** This is the hypothesis
`convexConj_comp_linearEquiv` and `subdifferential_comp_linearEquiv` take, and the only mathematical
input the transport has. -/
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

/-- **The conjugate transports along the concatenation.** A function `f` on `ℝᵐ × ℝⁿ` read as a
function on `ℝᵐ⁺ⁿ` has, as its conjugate for the inner product of `ℝᵐ⁺ⁿ`, the conjugate of `f` for
`prodPairing` read the same way. -/
theorem convexConj_comp_euclideanProdEquiv (f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
    → EReal) (z : EuclideanSpace ℝ (Fin (m + n))) :
    convexConj (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
        (fun w => f ((euclideanProdEquiv m n).symm w)) z
      = convexConj (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m)))
          (innerₗ (EuclideanSpace ℝ (Fin n)))) f ((euclideanProdEquiv m n).symm z) :=
  convexConj_comp_linearEquiv (euclideanProdEquiv m n).symm.toLinearEquiv
    (euclideanProdEquiv m n).toLinearEquiv isAdjointPair_euclideanProdEquiv f z

/-- **The subdifferential transports along the concatenation.** -/
theorem subdifferential_comp_euclideanProdEquiv (f : EuclideanSpace ℝ (Fin m) ×
    EuclideanSpace ℝ (Fin n) → EReal) (z : EuclideanSpace ℝ (Fin (m + n))) :
    subdifferential (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
        (fun w => f ((euclideanProdEquiv m n).symm w)) z
      = euclideanProdEquiv m n '' subdifferential (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m)))
          (innerₗ (EuclideanSpace ℝ (Fin n)))) f ((euclideanProdEquiv m n).symm z) :=
  subdifferential_comp_linearEquiv (euclideanProdEquiv m n).symm.toLinearEquiv
    (euclideanProdEquiv m n).toLinearEquiv isAdjointPair_euclideanProdEquiv f z

/-- **The relative interior transports along the concatenation.** -/
theorem relint_image_euclideanProdEquiv
    {C : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C) :
    ri (euclideanProdEquiv m n '' C) = euclideanProdEquiv m n '' ri C :=
  Convex.relint_image hC (euclideanProdEquiv m n).toLinearEquiv.toLinearMap

/-- **The relative interior transports along the concatenation**, read the other way. -/
theorem relint_image_euclideanProdEquiv_symm {D : Set (EuclideanSpace ℝ (Fin (m + n)))}
    (hD : Convex ℝ D) :
    ri ((euclideanProdEquiv m n).symm '' D) = (euclideanProdEquiv m n).symm '' ri D :=
  Convex.relint_image hD (euclideanProdEquiv m n).symm.toLinearEquiv.toLinearMap

end Transport

end ConvexAnalysis
