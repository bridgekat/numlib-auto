/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.UnitaryGroup`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Two-sided unitary equivalence

`Matrix.IsUnitaryEquiv A U T V` says that `U` and `V` are unitary and `Uᴴ A V = T`, that is
`A = U T Vᴴ`. It is the common core of the two-sided unitary factorizations of a rectangular
matrix — the singular value decomposition, the URV and ULV decompositions, the complete
orthogonal decompositions and the bidiagonalizations of [golub2013matrix] §2.4, §5.4 — each of
which adds a shape condition on the middle factor `T` (as a structure extending this one, or as
a projection to it). The core carries the unitary algebra they share.

## Main definitions

* `Matrix.IsUnitaryEquiv A U T V`: `U`, `V` unitary and `Uᴴ A V = T`. The field names
  `mem_unitaryGroup_left`, `mem_unitaryGroup_right`, `star_mul_mul` are the ones of every
  two-sided factorization in `Numlib`: *left* and *right* always name the side of `A`.

## Main results

* `Matrix.conjTranspose_mul_self_of_mem_unitaryGroup`,
  `Matrix.mul_conjTranspose_self_of_mem_unitaryGroup`: `Uᴴ U = 1` and `U Uᴴ = 1` for a unitary `U`,
  in the `ᴴ` notation of the factorizations (Mathlib states them with `star`);
  `Matrix.submatrix_equiv_mem_unitaryGroup`: permuting rows and columns keeps a matrix unitary.
* `Matrix.IsUnitaryEquiv.eq_mul_mul`: `A = U T Vᴴ`; `Matrix.IsUnitaryEquiv.mul_eq`: `A V = U T`;
  `Matrix.IsUnitaryEquiv.mulVec_col`: `A vⱼ = U tⱼ` column by column.
* `Matrix.IsUnitaryEquiv.conjTranspose_mul_self`: `Vᴴ (Aᴴ A) V = Tᴴ T`, and its row twin
  `Matrix.IsUnitaryEquiv.mul_conjTranspose_self`: `Uᴴ (A Aᴴ) U = T Tᴴ`.
* `Matrix.IsUnitaryEquiv.rank_eq`: `rank A = rank T`.
* `Matrix.IsUnitaryEquiv.conjTranspose` (the adjoint equivalence `Vᴴ Aᴴ U = Tᴴ`) and
  `Matrix.IsUnitaryEquiv.trans` (composition).

## References

* [golub2013matrix] §2.4, §5.4.
-/

namespace Matrix

variable {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommRing α] [StarRing α]

/-! ### The two one-sided identities of a unitary matrix -/

section Unitary

variable {U : Matrix n n α}

/-- A unitary matrix has orthonormal columns: `Uᴴ U = 1`. -/
theorem conjTranspose_mul_self_of_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) : Uᴴ * U = 1 :=
  mem_unitaryGroup_iff'.1 hU

/-- A unitary matrix has orthonormal rows: `U Uᴴ = 1`. -/
theorem mul_conjTranspose_self_of_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) : U * Uᴴ = 1 :=
  mem_unitaryGroup_iff.1 hU

/-- The adjoint of a unitary matrix is unitary. -/
theorem conjTranspose_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) : Uᴴ ∈ unitaryGroup n α :=
  Unitary.star_mem hU

/-- The determinant of a unitary matrix is a unit. -/
theorem isUnit_det_of_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) : IsUnit U.det :=
  isUnit_det_of_left_inverse (conjTranspose_mul_self_of_mem_unitaryGroup hU)

/-- Permuting the rows and the columns of a unitary matrix keeps it unitary. -/
theorem submatrix_equiv_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) (e₁ e₂ : n ≃ n) :
    U.submatrix e₁ e₂ ∈ unitaryGroup n α := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv U Uᴴ e₁ e₂ e₁, mul_conjTranspose_self_of_mem_unitaryGroup hU,
    submatrix_one_equiv]

/-- Permuting the rows of a unitary matrix keeps it unitary. -/
theorem submatrix_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) (e : n ≃ n) :
    U.submatrix e id ∈ unitaryGroup n α :=
  submatrix_equiv_mem_unitaryGroup hU e (Equiv.refl n)

end Unitary

/-! ### Two-sided unitary equivalence -/

/-- **Two-sided unitary equivalence** `Uᴴ A V = T`, i.e. `A = U T Vᴴ` with `U`, `V` unitary: the
common core of the singular value, URV, ULV, complete orthogonal and bidiagonal factorizations
([golub2013matrix] §2.4, §5.4), which add a shape condition on `T`. -/
structure IsUnitaryEquiv (A : Matrix m n α) (U : Matrix m m α) (T : Matrix m n α)
    (V : Matrix n n α) : Prop where
  /-- The left factor is unitary. -/
  mem_unitaryGroup_left : U ∈ unitaryGroup m α
  /-- The right factor is unitary. -/
  mem_unitaryGroup_right : V ∈ unitaryGroup n α
  /-- The factorization `Uᴴ A V = T`. -/
  star_mul_mul : star U * A * V = T

/-- Any two unitary matrices carry `A` to `Uᴴ A V`. -/
theorem isUnitaryEquiv_star_mul_mul {A : Matrix m n α} {U : Matrix m m α} {V : Matrix n n α}
    (hU : U ∈ unitaryGroup m α) (hV : V ∈ unitaryGroup n α) :
    IsUnitaryEquiv A U (star U * A * V) V :=
  ⟨hU, hV, rfl⟩

namespace IsUnitaryEquiv

variable {A : Matrix m n α} {U : Matrix m m α} {T : Matrix m n α} {V : Matrix n n α}

/-- The factorization in `ᴴ` notation, `Uᴴ A V = T`. -/
theorem conjTranspose_mul_mul (h : IsUnitaryEquiv A U T V) : Uᴴ * A * V = T :=
  h.star_mul_mul

/-- `A V = U T`. -/
theorem mul_eq (h : IsUnitaryEquiv A U T V) : A * V = U * T := by
  rw [← h.conjTranspose_mul_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U,
    mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_left, Matrix.one_mul]

/-- `Uᴴ A = T Vᴴ`. -/
theorem conjTranspose_mul_eq (h : IsUnitaryEquiv A U T V) : Uᴴ * A = T * Vᴴ := by
  rw [← h.conjTranspose_mul_mul, Matrix.mul_assoc _ V,
    mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_right, Matrix.mul_one]

/-- `A = U T Vᴴ`. -/
theorem eq_mul_mul (h : IsUnitaryEquiv A U T V) : A = U * T * Vᴴ := by
  rw [← h.mul_eq, Matrix.mul_assoc,
    mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_right, Matrix.mul_one]

/-- Column by column, `A V = U T`: `A vⱼ = U tⱼ`. -/
theorem mulVec_col (h : IsUnitaryEquiv A U T V) (j : n) : A *ᵥ V.col j = U *ᵥ T.col j := by
  rw [← col_mul_eq_mulVec_col, ← col_mul_eq_mulVec_col, h.mul_eq]

/-- `Vᴴ (Aᴴ A) V = Tᴴ T`: the right factor diagonalizes the Gram matrix as far as `T` does. -/
theorem conjTranspose_mul_self (h : IsUnitaryEquiv A U T V) : Vᴴ * (Aᴴ * A) * V = Tᴴ * T := by
  rw [← h.conjTranspose_mul_mul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U, mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_left,
    Matrix.one_mul]

/-- `Uᴴ (A Aᴴ) U = T Tᴴ`, the row twin of `Matrix.IsUnitaryEquiv.conjTranspose_mul_self`. -/
theorem mul_conjTranspose_self (h : IsUnitaryEquiv A U T V) : Uᴴ * (A * Aᴴ) * U = T * Tᴴ := by
  rw [← h.conjTranspose_mul_mul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V, mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_right,
    Matrix.one_mul]

/-- The unitary factors do not change the rank: `rank A = rank T`. -/
theorem rank_eq (h : IsUnitaryEquiv A U T V) : A.rank = T.rank := by
  rw [← h.conjTranspose_mul_mul,
    rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_mem_unitaryGroup h.mem_unitaryGroup_right),
    rank_mul_eq_right_of_isUnit_det _ _
      (isUnit_det_of_mem_unitaryGroup (conjTranspose_mem_unitaryGroup h.mem_unitaryGroup_left))]

/-- The adjoint equivalence: `Vᴴ Aᴴ U = Tᴴ`. -/
theorem conjTranspose (h : IsUnitaryEquiv A U T V) : IsUnitaryEquiv Aᴴ V Tᴴ U where
  mem_unitaryGroup_left := h.mem_unitaryGroup_right
  mem_unitaryGroup_right := h.mem_unitaryGroup_left
  star_mul_mul := by
    rw [← h.conjTranspose_mul_mul, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, star_eq_conjTranspose, Matrix.mul_assoc]

/-- Two-sided unitary equivalences compose: from `Uᴴ A V = T` and `U'ᴴ T V' = T'`,
`(U U')ᴴ A (V V') = T'`. -/
theorem trans {U' : Matrix m m α} {T' : Matrix m n α} {V' : Matrix n n α}
    (h : IsUnitaryEquiv A U T V) (h' : IsUnitaryEquiv T U' T' V') :
    IsUnitaryEquiv A (U * U') T' (V * V') where
  mem_unitaryGroup_left := mul_mem h.mem_unitaryGroup_left h'.mem_unitaryGroup_left
  mem_unitaryGroup_right := mul_mem h.mem_unitaryGroup_right h'.mem_unitaryGroup_right
  star_mul_mul := by
    rw [← h'.star_mul_mul, ← h.star_mul_mul, star_mul]
    simp only [Matrix.mul_assoc]

end IsUnitaryEquiv

end Matrix
