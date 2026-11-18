import Mathlib.LinearAlgebra.Matrix.ToLin
import Numlib.Multigrid.ResidualCycle

/-!
# Coupled local residual corrections

Local residual responses $M_i$ are linear maps on a global space. A response may restrict to a
coordinate patch, solve a coupled local problem, and extend the correction by zero. An additive
sweep adds the damped responses to the same residual; a multiplicative sweep recomputes the
residual at each patch. These constructions apply also to indefinite operators.

## Main definitions

* `DomainDecomposition.coordinateRestriction`: selection of the coordinates of an embedded patch.
* `DomainDecomposition.exactLocalResponse`: solution of the Galerkin problem on a patch.
* `DomainDecomposition.additiveResponse`: the sum of the damped patch responses.
* `DomainDecomposition.multiplicativeSweep`: ordered damped local updates.

## Main results

* `DomainDecomposition.coordinateRestriction_mul_mul_transpose`: restriction and zero extension
  compress the matrix to a principal submatrix.
* `DomainDecomposition.multiplicativeSweep_error`: a sweep propagates the error by the ordered
  product of the patch error operators.
-/

namespace DomainDecomposition

open Matrix Multigrid

section Coordinates

variable {𝕜 global localIdx : Type*} [CommRing 𝕜] [DecidableEq global]

/-- For a coordinate embedding $\iota$ into the global index type, the **coordinate
restriction** has entry $1$ at $(i,\iota(i))$ and $0$ at other entries. Its transpose is
extension by zero. -/
def coordinateRestriction (embed : localIdx ↪ global) : Matrix localIdx global 𝕜 :=
  Matrix.of fun patch column => if column = embed patch then 1 else 0

/-- Restriction along $\iota$ takes entry $\iota(i)$ of a global vector at local index $i$. -/
@[simp]
theorem coordinateRestriction_mulVec [Fintype global] (embed : localIdx ↪ global)
    (vector : global → 𝕜) :
    coordinateRestriction embed *ᵥ vector = vector ∘ embed := by
  funext patch
  simp [coordinateRestriction, mulVec, dotProduct, ite_mul]

/-- If $R$ selects coordinates along $\iota$, then $RAR^T$ is the submatrix
$(A_{\iota(i),\iota(j)})_{ij}$ for every square global matrix $A$. -/
theorem coordinateRestriction_mul_mul_transpose [Fintype global] (embed : localIdx ↪ global)
    (A : Matrix global global 𝕜) :
    coordinateRestriction embed * A * (coordinateRestriction embed)ᵀ =
      A.submatrix embed embed := by
  have hleft (patch : localIdx) (column : global) :
      ((coordinateRestriction embed : Matrix localIdx global 𝕜) * A) patch column =
        A (embed patch) column := by
    simp [Matrix.mul_apply, coordinateRestriction, ite_mul]
  ext patch column
  rw [Matrix.mul_apply]
  simp only [hleft, transpose_apply]
  simp [coordinateRestriction, mul_ite]

end Coordinates

variable {𝕜 E F ι : Type*} [CommRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- For patch transfers $R$ and $P$, the **exact local residual response** is
$P(RAP)^{-1}R$. The inverse here is the ring inverse, defined to be zero if the compression
is not a unit. An invertible compression guarantees exactness for every local right-hand side. -/
noncomputable def exactLocalResponse (A : Module.End 𝕜 E) (patch : TransferPair 𝕜 E F) :
    Module.End 𝕜 E :=
  patch.coarseResponse (Ring.inverse (patch.petrovGalerkinCoarse A)) 1

/-- An undamped exact local correction on an invertible patch leaves zero restricted residual. -/
theorem restricted_residual_exactLocalResponse (A : Module.End 𝕜 E)
    (patch : TransferPair 𝕜 E F) (hpatch : IsUnit (patch.petrovGalerkinCoarse A))
    (rhs iterate : E) :
    patch.restrict (rhs - A (residualCorrection A (exactLocalResponse A patch) rhs iterate)) =
      0 := by
  simp only [residualCorrection, exactLocalResponse, TransferPair.coarseResponse_apply, one_smul]
  apply patch.restricted_residual_eq_zero
  rw [← Module.End.mul_apply, Ring.mul_inverse_cancel _ hpatch, Module.End.one_apply]

/-- The **additive response** of a finite patch family with weights $\omega_i$ is
$\sum_i \omega_i M_i$, where every local response $M_i$ acts on the same global residual. -/
def additiveResponse [Fintype ι] (localResponse : ι → Module.End 𝕜 E) (weight : ι → 𝕜) :
    Module.End 𝕜 E :=
  ∑ patch, weight patch • localResponse patch

/-- The additive update adds the sum of all weighted local corrections to the input iterate. -/
theorem residualCorrection_additiveResponse [Fintype ι] (A : Module.End 𝕜 E)
    (localResponse : ι → Module.End 𝕜 E) (weight : ι → 𝕜) (rhs iterate : E) :
    residualCorrection A (additiveResponse localResponse weight) rhs iterate =
      iterate + ∑ patch, weight patch • localResponse patch (rhs - A iterate) := by
  simp [residualCorrection, additiveResponse, LinearMap.sum_apply]

/-- The **multiplicative sweep** visits the specified patches in list order. At patch $i$ it
updates the current iterate by $\omega_i M_i$ applied to its current residual. Patches may be
repeated, and an empty visit list leaves the iterate unchanged. -/
def multiplicativeSweep (A : Module.End 𝕜 E) (localResponse : ι → Module.End 𝕜 E)
    (weight : ι → 𝕜) (rhs : E) : List ι → E → E
  | [], iterate => iterate
  | patch :: rest, iterate =>
    multiplicativeSweep A localResponse weight rhs rest
      (residualCorrection A (weight patch • localResponse patch) rhs iterate)

/-- The sweep's **error operator** takes the product of $I-\omega_i M_i A$ in the order of
application: the map for the first patch is the rightmost factor. The empty product is $I$. -/
def multiplicativeSweepError (A : Module.End 𝕜 E) (localResponse : ι → Module.End 𝕜 E)
    (weight : ι → 𝕜) : List ι → Module.End 𝕜 E
  | [] => 1
  | patch :: rest => multiplicativeSweepError A localResponse weight rest *
    residualError A (weight patch • localResponse patch)

/-- If $Ax_* = b$, a multiplicative sweep propagates $x_* - x$ by the product of the local
error operators in visit order. -/
theorem multiplicativeSweep_error (A : Module.End 𝕜 E) (localResponse : ι → Module.End 𝕜 E)
    (weight : ι → 𝕜) {rhs solution : E} (hsol : A solution = rhs)
    (order : List ι) (iterate : E) :
    solution - multiplicativeSweep A localResponse weight rhs order iterate =
      multiplicativeSweepError A localResponse weight order (solution - iterate) := by
  induction order generalizing iterate with
  | nil => rfl
  | cons patch rest ih =>
    rw [multiplicativeSweep, ih, residualCorrection_error A _ hsol, multiplicativeSweepError,
      Module.End.mul_apply]

end DomainDecomposition
