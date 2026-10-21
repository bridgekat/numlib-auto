import Numlib.Analysis.InnerProductSpace.SymmetricMultilinear
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Appendix A.6: tensors

A symmetric cubical order-`p` tensor is represented by its symmetric continuous multilinear
form on Euclidean space. Its diagonal is (A.6); the first maximum in (A.7) is represented by
an actual unit-sphere supremum and is attained for positive dimension. For positive order it
equals the full multilinear operator norm by Banach’s symmetric multilinear norm theorem.
The `p`-kernel (A.8) is the diagonal zero set, which is not generally a subspace.

The sphere supremum is extended by zero in dimension zero. In order zero it is the absolute
constant value in positive dimension; in zero dimension the sphere is empty instead.
-/

noncomputable section

namespace CartisGouldToint.AppendixA.Section06

/-- A symmetric cubical tensor, represented by its associated real multilinear form. -/
abbrev Tensor (n p : ℕ) :=
  ContinuousMultilinearMap.symmetricSubmodule
    (E := EuclideanSpace ℝ (Fin n)) (F := ℝ) (p := p)

/-- Equation (A.6): apply a tensor to `p` copies of a Euclidean vector. -/
def tensorDiagonal {n p : ℕ} (T : Tensor n p) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  T.val.diagonal v

/-- The first expression in (A.7): the supremum of absolute diagonal values on the unit
sphere, extended by zero when the sphere is empty. -/
def tensorInducedNorm {n p : ℕ} (T : Tensor n p) : ℝ := T.val.diagonalNorm

/-- Equation (A.8): the set of vectors where the tensor's diagonal vanishes. -/
def tensorPowerKernel {n p : ℕ} (T : Tensor n p) : Set (EuclideanSpace ℝ (Fin n)) :=
  T.val.diagonalZeroSet

/-- The tensor power kernel consists exactly of diagonal zeros. -/
@[simp] theorem mem_tensorPowerKernel {n p : ℕ} (T : Tensor n p)
    (v : EuclideanSpace ℝ (Fin n)) : v ∈ tensorPowerKernel T ↔ tensorDiagonal T v = 0 :=
  Iff.rfl

/-- Tensor diagonal evaluation is homogeneous of degree `p`. -/
@[simp] theorem tensorDiagonal_smul {n p : ℕ} (T : Tensor n p) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    tensorDiagonal T (c • v) = c ^ p * tensorDiagonal T v := T.val.diagonal_smul c v

/-- The induced diagonal norm is bounded by the full multilinear operator norm. -/
theorem tensorInducedNorm_le_operator_norm {n p : ℕ} (T : Tensor n p) :
    tensorInducedNorm T ≤ ‖T.val‖ := T.val.diagonalNorm_le_norm

/-- The supremum in the tensor norm is an actual maximum in positive dimension. -/
theorem exists_abs_tensorDiagonal_eq_tensorInducedNorm {n p : ℕ} (hn : 0 < n)
    (T : Tensor n p) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧ |tensorDiagonal T v| = tensorInducedNorm T := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa [tensorDiagonal, tensorInducedNorm, Real.norm_eq_abs] using
    T.val.exists_norm_diagonal_eq_diagonalNorm

/-- The tensor norm is zero on the zero-dimensional space because its unit sphere is empty. -/
@[simp] theorem tensorInducedNorm_dimension_zero {p : ℕ} (T : Tensor 0 p) :
    tensorInducedNorm T = 0 := T.val.diagonalNorm_of_subsingleton

/-- The tensor norm controls every positive-order diagonal evaluation. -/
theorem abs_tensorDiagonal_le {n p : ℕ} (T : Tensor n p) (hp : 0 < p)
    (v : EuclideanSpace ℝ (Fin n)) :
    |tensorDiagonal T v| ≤ tensorInducedNorm T * ‖v‖ ^ p :=
  T.val.norm_diagonal_le_diagonalNorm_mul hp v

/-- A nonnegative constant bounds the tensor norm exactly when it bounds all diagonal
values homogeneously. -/
theorem tensorInducedNorm_le_iff {n p : ℕ} (T : Tensor n p) (hp : 0 < p)
    {C : ℝ} (hC : 0 ≤ C) :
    tensorInducedNorm T ≤ C ↔
      ∀ v : EuclideanSpace ℝ (Fin n), |tensorDiagonal T v| ≤ C * ‖v‖ ^ p :=
  T.val.diagonalNorm_le_iff hp hC

/-- For vectors (order-one tensors), the diagonal norm equals the operator norm. -/
theorem tensor_diagonal_norm_eq_operator_norm_order_one {n : ℕ} (T : Tensor n 1) :
    tensorInducedNorm T = ‖T.val‖ := T.val.diagonalNorm_order_one

/-- Order-zero tensors have constant diagonal values. -/
theorem tensorDiagonal_order_zero {n : ℕ} (T : Tensor n 0)
    (v : EuclideanSpace ℝ (Fin n)) : tensorDiagonal T v = tensorDiagonal T 0 :=
  T.val.diagonal_order_zero v

/-- The induced norm varies continuously with the tensor coefficients. -/
theorem continuous_tensorInducedNorm {n p : ℕ} :
    Continuous (tensorInducedNorm : Tensor n p → ℝ) :=
  ContinuousMultilinearMap.continuous_diagonalNorm.comp continuous_subtype_val

/-- For order-one tensors the power kernel is a linear subspace. -/
theorem tensorPowerKernel_order_one {n : ℕ} (T : Tensor n 1) :
    tensorPowerKernel T = (T.val.diagonalLinearMap.ker : Set (EuclideanSpace ℝ (Fin n))) :=
  T.val.diagonalZeroSet_order_one

/-- Tensor power kernels are closed. -/
theorem isClosed_tensorPowerKernel {n p : ℕ} (T : Tensor n p) :
    IsClosed (tensorPowerKernel T) := T.val.isClosed_diagonalZeroSet

/-- Tensor power kernels are stable under scalar multiplication. -/
theorem smul_mem_tensorPowerKernel {n p : ℕ} (T : Tensor n p)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ tensorPowerKernel T) (c : ℝ) :
    c • v ∈ tensorPowerKernel T := T.val.smul_mem_diagonalZeroSet hv c

/-- Equation (A.7): the diagonal unit-sphere supremum of a positive-order symmetric tensor
is its full multilinear operator norm, including in dimension zero. -/
theorem tensor_diagonal_norm_eq_operator_norm {n p : ℕ} (T : Tensor n p) (hp : 0 < p) :
    tensorInducedNorm T = ‖T.val‖ :=
  T.val.diagonalNorm_eq_norm_of_isSymmetric hp T.property

end CartisGouldToint.AppendixA.Section06
