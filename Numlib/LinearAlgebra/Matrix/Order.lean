/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Order`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Matrix.Basic

/-!
# The entrywise order and the entrywise absolute value of matrices

`Matrix.EntrywiseLE A B`, written `A ≤ₑ B`, holds when `A i j ≤ B i j` for every entry;
`Matrix.EntrywiseNonneg A` is `0 ≤ₑ A`, the *nonnegative matrices* of the theory of regular
splittings; and `Matrix.abs A`, written `A.abs`, is the matrix of the absolute values of the
entries. Together they carry the componentwise calculus behind the convergence theory of regular
splittings and behind rounding-error analysis: monotonicity of a product in either factor when the
other one is nonnegative (`Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left` and
`Matrix.EntrywiseLE.mul_of_entrywiseNonneg_right`, which is Saad[^saad-iterative] §1.10, Prop 1.26,
and whose clause-by-clause companions are his Prop 1.24), the stability of nonnegativity under
sums, products, powers and matrix-vector multiplication, and the triangle inequality for a product,
`(A * B).abs ≤ₑ A.abs * B.abs` (`Matrix.abs_mul_entrywiseLE`), which is the matrix form of the
componentwise bounds of Higham[^higham] §3.5.

## Notation

`A ≤ₑ B` is `Matrix.EntrywiseLE A B`, scoped in `Matrix` beside `*ᵥ`. The entrywise absolute value
has no notation of its own, because `|·|` is already the lattice absolute value and `A.abs` reads
well enough.

## Implementation notes

The entrywise order is a *predicate*, not an `LE` instance. Mathlib already orders square matrices
over an `RCLike` field by the Loewner order — there `A ≤ B` means that `B - A` is positive
semidefinite — as instances scoped in `MatrixOrder`, and a second `LE` on the same type would make
every statement about either of them ambiguous.

Vectors are plain `Pi` types, and there the entrywise order and absolute value *are* the canonical
`≤` and `|·|`. So the statements that mix the two — `Matrix.abs_mulVec_le`,
`Matrix.EntrywiseNonneg.mulVec_nonneg` — use `≤` and `|·|` on the vector side and `≤ₑ` and `.abs`
on the matrix side.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^higham]: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd edition,
  SIAM, 2002.
-/

namespace Matrix

variable {l m n ι : Type*} {α : Type*}

/-! ### The entrywise order -/

section LE

variable [LE α]

/-- `A ≤ₑ B` holds when `A i j ≤ B i j` for every entry: the *entrywise* order on matrices.

It is a predicate rather than an `LE` instance because Mathlib's order on square matrices over an
`RCLike` field, scoped in `MatrixOrder`, is the Loewner order `A ≤ B ↔ (B - A).PosSemidef`, and the
two must not compete for the same notation. -/
def EntrywiseLE (A B : Matrix m n α) : Prop := ∀ i j, A i j ≤ B i j

@[inherit_doc] scoped infix:50 " ≤ₑ " => Matrix.EntrywiseLE

/-- The entrywise order, unfolded. -/
theorem entrywiseLE_iff {A B : Matrix m n α} : A ≤ₑ B ↔ ∀ i j, A i j ≤ B i j := Iff.rfl

/-- A matrix is *entrywise nonnegative* when `0 ≤ₑ A`; this is the relation written `A ≥ 0` in
Saad, *Iterative Methods for Sparse Linear Systems*, §1.10. -/
def EntrywiseNonneg [Zero α] (A : Matrix m n α) : Prop := (0 : Matrix m n α) ≤ₑ A

/-- Entrywise nonnegativity, unfolded. -/
theorem entrywiseNonneg_iff [Zero α] {A : Matrix m n α} :
    A.EntrywiseNonneg ↔ ∀ i j, 0 ≤ A i j := Iff.rfl

/-- The defining property of an entrywise nonnegative matrix, with the zero matrix already
evaluated at `i`, `j`. -/
theorem EntrywiseNonneg.apply [Zero α] {A : Matrix m n α} (hA : A.EntrywiseNonneg) (i : m) (j : n) :
    0 ≤ A i j := hA i j

end LE

section Preorder

variable [Preorder α] {A B C : Matrix m n α}

/-- The entrywise order is reflexive. -/
@[refl] theorem EntrywiseLE.refl (A : Matrix m n α) : A ≤ₑ A := fun _ _ => le_rfl

/-- The entrywise order is reflexive. -/
theorem EntrywiseLE.rfl : A ≤ₑ A := EntrywiseLE.refl A

/-- The entrywise order is transitive. -/
@[trans] theorem EntrywiseLE.trans (hAB : A ≤ₑ B) (hBC : B ≤ₑ C) : A ≤ₑ C :=
  fun i j => (hAB i j).trans (hBC i j)

/-- Equal matrices are entrywise comparable. -/
theorem EntrywiseLE.of_eq (h : A = B) : A ≤ₑ B := h ▸ EntrywiseLE.rfl

/-- The zero matrix is entrywise nonnegative. -/
theorem entrywiseNonneg_zero [Zero α] : (0 : Matrix m n α).EntrywiseNonneg := EntrywiseLE.rfl

end Preorder

/-- The entrywise order is antisymmetric. -/
theorem EntrywiseLE.antisymm [PartialOrder α] {A B : Matrix m n α} (hAB : A ≤ₑ B) (hBA : B ≤ₑ A) :
    A = B :=
  Matrix.ext fun i j => le_antisymm (hAB i j) (hBA i j)

/-! ### Sums -/

section AddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable {A B C D : Matrix m n α}

/-- The entrywise order is compatible with addition. -/
theorem EntrywiseLE.add (hAB : A ≤ₑ B) (hCD : C ≤ₑ D) : A + C ≤ₑ B + D :=
  fun i j => add_le_add (hAB i j) (hCD i j)

/-- The sum of two entrywise nonnegative matrices is entrywise nonnegative. -/
theorem EntrywiseNonneg.add (hA : A.EntrywiseNonneg) (hB : B.EntrywiseNonneg) :
    (A + B).EntrywiseNonneg :=
  fun i j => add_nonneg (hA.apply i j) (hB.apply i j)

/-- A finite sum of entrywise nonnegative matrices is entrywise nonnegative; this is what makes
the partial sums of a Neumann series `∑ Bᵏ` of a nonnegative `B` nonnegative. -/
theorem EntrywiseNonneg.sum {s : Finset ι} {f : ι → Matrix m n α}
    (hf : ∀ i ∈ s, (f i).EntrywiseNonneg) : (∑ i ∈ s, f i).EntrywiseNonneg := by
  intro i j
  simpa only [Matrix.zero_apply, Matrix.sum_apply] using
    Finset.sum_nonneg fun k hk => (hf k hk).apply i j

end AddCommMonoid

/-- `A ≤ₑ B` is nonnegativity of the difference. -/
theorem entrywiseLE_iff_entrywiseNonneg_sub [AddCommGroup α] [PartialOrder α]
    [IsOrderedAddMonoid α] {A B : Matrix m n α} : A ≤ₑ B ↔ (B - A).EntrywiseNonneg := by
  simp only [entrywiseLE_iff, entrywiseNonneg_iff, Matrix.sub_apply, sub_nonneg]

/-! ### The entrywise absolute value -/

section Abs

variable [Lattice α] [AddGroup α]

/-- The entrywise absolute value of a matrix, `A.abs i j = |A i j|`.

Beware that inside `namespace Matrix` the bare name `abs` refers to this function rather than to
the lattice absolute value `_root_.abs`; the notation `|·|` is unaffected, and continues to mean
the lattice absolute value of a scalar or of a vector. -/
def abs (A : Matrix m n α) : Matrix m n α := A.map (|·|)

/-- The entries of `A.abs` are the absolute values of the entries of `A`. -/
@[simp] theorem abs_apply (A : Matrix m n α) (i : m) (j : n) : A.abs i j = |A i j| := rfl

end Abs

section LatticeOrderedGroup

variable [Lattice α] [AddCommGroup α] [IsOrderedAddMonoid α]

/-- An entrywise absolute value is entrywise nonnegative. -/
theorem entrywiseNonneg_abs (A : Matrix m n α) : A.abs.EntrywiseNonneg :=
  fun i j => abs_nonneg (A i j)

/-- The triangle inequality, entrywise. -/
theorem abs_add_entrywiseLE (A B : Matrix m n α) : (A + B).abs ≤ₑ A.abs + B.abs :=
  fun i j => by simpa using abs_add_le (A i j) (B i j)

end LatticeOrderedGroup

/-! ### Products -/

section Semiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α]

/-- The identity matrix is entrywise nonnegative. -/
theorem entrywiseNonneg_one [DecidableEq n] : (1 : Matrix n n α).EntrywiseNonneg := by
  intro i j
  rw [Matrix.zero_apply, Matrix.one_apply]
  split
  · exact zero_le_one
  · exact le_rfl

/-- Multiplying on the left by an entrywise nonnegative matrix is monotone for the entrywise
order (Saad, *Iterative Methods for Sparse Linear Systems*, Prop 1.26). -/
theorem EntrywiseLE.mul_of_entrywiseNonneg_left [Fintype l] {C : Matrix m l α}
    {A B : Matrix l n α} (hC : C.EntrywiseNonneg) (hAB : A ≤ₑ B) : C * A ≤ₑ C * B := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hAB k j) (hC.apply i k)

/-- Multiplying on the right by an entrywise nonnegative matrix is monotone for the entrywise
order (Saad, *Iterative Methods for Sparse Linear Systems*, Prop 1.26). -/
theorem EntrywiseLE.mul_of_entrywiseNonneg_right [Fintype l] {C : Matrix l n α}
    {A B : Matrix m l α} (hC : C.EntrywiseNonneg) (hAB : A ≤ₑ B) : A * C ≤ₑ B * C := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hAB i k) (hC.apply k j)

/-- The product of two entrywise nonnegative matrices is entrywise nonnegative. -/
theorem EntrywiseNonneg.mul [Fintype l] {A : Matrix m l α} {B : Matrix l n α}
    (hA : A.EntrywiseNonneg) (hB : B.EntrywiseNonneg) : (A * B).EntrywiseNonneg := by
  intro i j
  simpa only [Matrix.zero_apply, Matrix.mul_apply] using
    Finset.sum_nonneg fun k _ => mul_nonneg (hA.apply i k) (hB.apply k j)

/-- Every power of an entrywise nonnegative matrix is entrywise nonnegative. -/
theorem EntrywiseNonneg.pow [Fintype n] [DecidableEq n] {A : Matrix n n α}
    (hA : A.EntrywiseNonneg) (k : ℕ) : (A ^ k).EntrywiseNonneg :=
  fun i j => Matrix.pow_apply_nonneg hA.apply k i j

/-- Scaling by a nonnegative scalar is monotone for the entrywise order. -/
theorem EntrywiseLE.smul_of_nonneg {c : α} {A B : Matrix m n α} (hc : 0 ≤ c) (hAB : A ≤ₑ B) :
    c • A ≤ₑ c • B :=
  fun i j => by
    simpa only [Matrix.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left (hAB i j) hc

/-- An entrywise nonnegative matrix maps entrywise nonnegative vectors to entrywise nonnegative
vectors. -/
theorem EntrywiseNonneg.mulVec_nonneg [Fintype n] {A : Matrix m n α} {x : n → α}
    (hA : A.EntrywiseNonneg) (hx : 0 ≤ x) : 0 ≤ A *ᵥ x := by
  refine Pi.le_def.mpr fun i => ?_
  simpa only [Pi.zero_apply, Matrix.mulVec_apply_eq_sum] using
    Finset.sum_nonneg fun k _ => mul_nonneg (hA.apply i k) (Pi.le_def.mp hx k)

/-- An entrywise nonnegative matrix acts monotonically on vectors. -/
theorem EntrywiseNonneg.mulVec_mono [Fintype n] {A : Matrix m n α} {x y : n → α}
    (hA : A.EntrywiseNonneg) (hxy : x ≤ y) : A *ᵥ x ≤ A *ᵥ y := by
  refine Pi.le_def.mpr fun i => ?_
  simp only [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (Pi.le_def.mp hxy k) (hA.apply i k)

end Semiring

/-! ### The absolute value of a product -/

section Ring

variable [Ring α] [LinearOrder α] [IsOrderedRing α]

/-- The entrywise triangle inequality for a matrix product, `|A * B| ≤ |A| |B|` in the notation of
the books: the matrix form of the componentwise bounds of Higham, *Accuracy and Stability of
Numerical Algorithms*, §3.5. -/
theorem abs_mul_entrywiseLE [Fintype l] (A : Matrix m l α) (B : Matrix l n α) :
    (A * B).abs ≤ₑ A.abs * B.abs := by
  intro i j
  simp only [Matrix.abs_apply, Matrix.mul_apply]
  calc |∑ k, A i k * B k j|
      ≤ ∑ k, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |A i k| * |B k j| := by simp [abs_mul]

/-- The vector form of `Matrix.abs_mul_entrywiseLE`: `|A *ᵥ x| ≤ A.abs *ᵥ |x|`, with the entrywise
order and absolute value of the `Pi` type on the vector side. -/
theorem abs_mulVec_le [Fintype n] (A : Matrix m n α) (x : n → α) :
    |A *ᵥ x| ≤ A.abs *ᵥ |x| := by
  refine Pi.le_def.mpr fun i => ?_
  simp only [Pi.abs_apply, Matrix.mulVec_apply_eq_sum, Matrix.abs_apply]
  calc |∑ k, A i k * x k|
      ≤ ∑ k, |A i k * x k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |A i k| * |x k| := by simp [abs_mul]

end Ring

end Matrix
