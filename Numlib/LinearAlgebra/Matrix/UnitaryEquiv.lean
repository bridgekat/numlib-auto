/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $\alpha$ be a commutative ring with an involution $x \mapsto x^*$, and write $X^H$ for the
conjugate transpose of a matrix $X$. A matrix $A \in \alpha^{m \times n}$ is **unitarily
equivalent** to $T \in \alpha^{m \times n}$ through unitary matrices $U \in \alpha^{m \times m}$ and
$V \in \alpha^{n \times n}$ if $U^H A V = T$, that is, $A = U T V^H$. This relation is the common
core of the two-sided unitary factorizations of a rectangular matrix in [golub2013matrix], §2.4 and
§5.4: the singular value decomposition, the URV and ULV decompositions, the complete orthogonal
decompositions and the bidiagonalizations. Each of these adds a condition on the shape of the middle
factor $T$. This module proves the algebra that they share: $A V = U T$, $V^H (A^H A) V = T^H T$,
$\operatorname{rank} A = \operatorname{rank} T$, the adjoint relation and composition.

## Main definitions

* `Matrix.IsUnitaryEquiv`: $U$ and $V$ are unitary and $U^H A V = T$.

## Main results

* `Matrix.conjTranspose_mul_self_of_mem_unitaryGroup`,
  `Matrix.mul_conjTranspose_self_of_mem_unitaryGroup`: a unitary matrix $U$ satisfies $U^H U = I$
  and $U U^H = I$.
* `Matrix.submatrix_equiv_mem_unitaryGroup`: a permutation of the rows and the columns keeps a
  matrix unitary.
* `Matrix.IsUnitaryEquiv.eq_mul_mul`, `Matrix.IsUnitaryEquiv.mul_eq`,
  `Matrix.IsUnitaryEquiv.mulVec_col`: $A = U T V^H$, $A V = U T$, and $A v_j = U t_j$ for the
  columns $v_j$ of $V$ and $t_j$ of $T$.
* `Matrix.IsUnitaryEquiv.conjTranspose_mul_self`, `Matrix.IsUnitaryEquiv.mul_conjTranspose_self`:
  $V^H (A^H A) V = T^H T$ and $U^H (A A^H) U = T T^H$.
* `Matrix.IsUnitaryEquiv.rank_eq`: $\operatorname{rank} A = \operatorname{rank} T$.
* `Matrix.IsUnitaryEquiv.conjTranspose`, `Matrix.IsUnitaryEquiv.trans`: $V^H A^H U = T^H$, and two
  unitary equivalences compose.

## Implementation notes

* A two-sided factorization in `Numlib` is a structure that extends `Matrix.IsUnitaryEquiv` or has a
  projection to it. The field names `mem_unitaryGroup_left`, `mem_unitaryGroup_right` and
  `star_mul_mul` are the same in every such factorization: *left* and *right* always name the side
  of $A$ on which the factor acts.
* The defining field is stated with `star U`, the form of Mathlib's `Matrix.unitaryGroup`. The
  lemmas `Matrix.conjTranspose_mul_self_of_mem_unitaryGroup` and
  `Matrix.mul_conjTranspose_self_of_mem_unitaryGroup` restate Mathlib's identities with `ᴴ`, the
  notation of the factorizations.
-/

namespace Matrix

variable {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommRing α] [StarRing α]

/-! ### The two one-sided identities of a unitary matrix -/

section Unitary

variable {U : Matrix n n α}

/-- A unitary matrix $U$ has orthonormal columns: $U^H U = I$. -/
theorem conjTranspose_mul_self_of_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) : Uᴴ * U = 1 :=
  mem_unitaryGroup_iff'.1 hU

/-- A unitary matrix $U$ has orthonormal rows: $U U^H = I$. -/
theorem mul_conjTranspose_self_of_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) : U * Uᴴ = 1 :=
  mem_unitaryGroup_iff.1 hU

/-- If $U$ is unitary, then $U^H$ is unitary. -/
theorem conjTranspose_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) : Uᴴ ∈ unitaryGroup n α :=
  Unitary.star_mem hU

/-- The determinant of a unitary matrix is a unit of the ring $\alpha$. -/
theorem isUnit_det_of_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) : IsUnit U.det :=
  isUnit_det_of_left_inverse (conjTranspose_mul_self_of_mem_unitaryGroup hU)

/-- Let $U$ be a unitary $n \times n$ matrix and let $e_1, e_2$ be permutations of the index set.
Then the matrix with entries $U_{e_1(i), e_2(j)}$ is unitary. -/
theorem submatrix_equiv_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) (e₁ e₂ : n ≃ n) :
    U.submatrix e₁ e₂ ∈ unitaryGroup n α := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv U Uᴴ e₁ e₂ e₁, mul_conjTranspose_self_of_mem_unitaryGroup hU,
    submatrix_one_equiv]

/-- Let $U$ be a unitary $n \times n$ matrix and let $e$ be a permutation of the index set. Then the
matrix with entries $U_{e(i), j}$, obtained by a permutation of the rows, is unitary. -/
theorem submatrix_mem_unitaryGroup (hU : U ∈ unitaryGroup n α) (e : n ≃ n) :
    U.submatrix e id ∈ unitaryGroup n α :=
  submatrix_equiv_mem_unitaryGroup hU e (Equiv.refl n)

end Unitary

/-! ### Two-sided unitary equivalence -/

/-- Let $A, T \in \alpha^{m \times n}$, $U \in \alpha^{m \times m}$ and $V \in \alpha^{n \times n}$.
The matrix $A$ is **unitarily equivalent** to $T$ through $U$ and $V$ if $U$ and $V$ are unitary
and
$$U^H A V = T,$$
that is, $A = U T V^H$.

This is the common core of the singular value, URV, ULV, complete orthogonal and bidiagonal
factorizations of [golub2013matrix], §2.4 and §5.4, which add a condition on the shape of $T$.
The field `star_mul_mul` states the identity with `star U`, which is $U^H$. -/
structure IsUnitaryEquiv (A : Matrix m n α) (U : Matrix m m α) (T : Matrix m n α)
    (V : Matrix n n α) : Prop where
  /-- The left factor $U$ is unitary. -/
  mem_unitaryGroup_left : U ∈ unitaryGroup m α
  /-- The right factor $V$ is unitary. -/
  mem_unitaryGroup_right : V ∈ unitaryGroup n α
  /-- The factorization $U^H A V = T$. -/
  star_mul_mul : star U * A * V = T

/-- Let $A \in \alpha^{m \times n}$ and let $U \in \alpha^{m \times m}$ and
$V \in \alpha^{n \times n}$ be unitary. Then $A$ is unitarily equivalent to $U^H A V$ through
$U$ and $V$. -/
theorem isUnitaryEquiv_star_mul_mul {A : Matrix m n α} {U : Matrix m m α} {V : Matrix n n α}
    (hU : U ∈ unitaryGroup m α) (hV : V ∈ unitaryGroup n α) :
    IsUnitaryEquiv A U (star U * A * V) V :=
  ⟨hU, hV, rfl⟩

namespace IsUnitaryEquiv

variable {A : Matrix m n α} {U : Matrix m m α} {T : Matrix m n α} {V : Matrix n n α}

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then $U^H A V = T$, with the
conjugate transpose written as `ᴴ`. -/
theorem conjTranspose_mul_mul (h : IsUnitaryEquiv A U T V) : Uᴴ * A * V = T :=
  h.star_mul_mul

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then $A V = U T$. -/
theorem mul_eq (h : IsUnitaryEquiv A U T V) : A * V = U * T := by
  rw [← h.conjTranspose_mul_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U,
    mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_left, Matrix.one_mul]

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then $U^H A = T V^H$. -/
theorem conjTranspose_mul_eq (h : IsUnitaryEquiv A U T V) : Uᴴ * A = T * Vᴴ := by
  rw [← h.conjTranspose_mul_mul, Matrix.mul_assoc _ V,
    mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_right, Matrix.mul_one]

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then $A = U T V^H$. -/
theorem eq_mul_mul (h : IsUnitaryEquiv A U T V) : A = U * T * Vᴴ := by
  rw [← h.mul_eq, Matrix.mul_assoc,
    mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_right, Matrix.mul_one]

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then for each column index $j$ the
columns $v_j$ of $V$ and $t_j$ of $T$ satisfy $A v_j = U t_j$. This is the identity $A V = U T$,
column by column. -/
theorem mulVec_col (h : IsUnitaryEquiv A U T V) (j : n) : A *ᵥ V.col j = U *ᵥ T.col j := by
  rw [← col_mul_eq_mulVec_col, ← col_mul_eq_mulVec_col, h.mul_eq]

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then
$$V^H (A^H A) V = T^H T.$$
Thus the right factor $V$ reduces the Gram matrix $A^H A$ as far as $T$ is reduced: for example,
to a diagonal matrix when $T$ is diagonal. -/
theorem conjTranspose_mul_self (h : IsUnitaryEquiv A U T V) : Vᴴ * (Aᴴ * A) * V = Tᴴ * T := by
  rw [← h.conjTranspose_mul_mul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U, mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_left,
    Matrix.one_mul]

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then
$$U^H (A A^H) U = T T^H.$$
This is the identity for the rows that corresponds to
`Matrix.IsUnitaryEquiv.conjTranspose_mul_self`. -/
theorem mul_conjTranspose_self (h : IsUnitaryEquiv A U T V) : Uᴴ * (A * Aᴴ) * U = T * Tᴴ := by
  rw [← h.conjTranspose_mul_mul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V, mul_conjTranspose_self_of_mem_unitaryGroup h.mem_unitaryGroup_right,
    Matrix.one_mul]

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then
$\operatorname{rank} A = \operatorname{rank} T$: the unitary factors do not change the rank. -/
theorem rank_eq (h : IsUnitaryEquiv A U T V) : A.rank = T.rank := by
  rw [← h.conjTranspose_mul_mul,
    rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_mem_unitaryGroup h.mem_unitaryGroup_right),
    rank_mul_eq_right_of_isUnit_det _ _
      (isUnit_det_of_mem_unitaryGroup (conjTranspose_mem_unitaryGroup h.mem_unitaryGroup_left))]

/-- If $A$ is unitarily equivalent to $T$ through $U$ and $V$, then $A^H$ is unitarily equivalent to
$T^H$ through $V$ and $U$, that is, $V^H A^H U = T^H$. -/
theorem conjTranspose (h : IsUnitaryEquiv A U T V) : IsUnitaryEquiv Aᴴ V Tᴴ U where
  mem_unitaryGroup_left := h.mem_unitaryGroup_right
  mem_unitaryGroup_right := h.mem_unitaryGroup_left
  star_mul_mul := by
    rw [← h.conjTranspose_mul_mul, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, star_eq_conjTranspose, Matrix.mul_assoc]

/-- Two-sided unitary equivalences compose. If $A$ is unitarily equivalent to $T$ through $U$ and
$V$, and $T$ is unitarily equivalent to $T'$ through $U'$ and $V'$, then $A$ is unitarily
equivalent to $T'$ through $U U'$ and $V V'$:
$$(U U')^H A (V V') = T'.$$
-/
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
