/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Cauchy` beside `Mathlib.LinearAlgebra.Vandermonde`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Numlib.LinearAlgebra.Matrix.Cholesky

/-!
# The Cauchy matrix and its determinant

Let $K$ be a field and let $x, y \in K^n$ with $x_i + y_j \ne 0$ for all $i, j$. The **Cauchy
matrix** of $x$ and $y$ is the matrix $C$ with entries $C_{ij} = (x_i + y_j)^{-1}$. Its determinant
has the closed form
$$\det C = \frac{\prod_{i < j} (x_j - x_i)(y_j - y_i)}{\prod_{i, j} (x_i + y_j)}.$$
In particular, a Cauchy matrix with distinct $x_i$ and distinct $y_j$ is nonsingular. So the
functions $t \mapsto t^{x_i}$ on $L^2(0, 1)$, whose Gram matrix $((x_i + x_j + 1)^{-1})_{ij}$ is a
Cauchy matrix, are linearly independent when the $x_i$ are distinct.

The **Hilbert matrix** $H_n$ with entries $h_{ij} = 1 / (i + j + 1)$, for indices from $0$, is the
Cauchy matrix of $x_i = i + 1$ and $y_j = j$. It is nonsingular in characteristic $0$, its
determinant is positive over an ordered field, and over $\mathbb{R}$ it is positive definite.

## Main definitions

* `Matrix.cauchy`: the Cauchy matrix $((x_i + y_j)^{-1})_{ij}$.
* `Matrix.hilbert`: the Hilbert matrix $(1 / (i + j + 1))_{ij}$ of order $n$.

## Main results

* `Matrix.det_cauchy`: the closed form of the Cauchy determinant.
* `Matrix.det_cauchy_ne_zero`: the Cauchy determinant is nonzero when the $x_i$ are distinct and the
  $y_j$ are distinct.
* `Matrix.hilbert_eq_cauchy`: the Hilbert matrix is the Cauchy matrix of $x_i = i + 1$ and
  $y_j = j$.
* `Matrix.isUnit_hilbert`: in characteristic $0$, the Hilbert matrix is nonsingular.
* `Matrix.det_hilbert_pos`: over an ordered field, $\det H_n > 0$.
* `Matrix.posDef_hilbert`: the real Hilbert matrix is positive definite.

## Proof outline

The Cauchy determinant follows from the classical row reduction. Subtracting row $0$ from every
other row makes the entry $(i, j)$ a multiple of $(x_i + y_j)^{-1} (x_0 + y_j)^{-1}$. This factors
as a scaling of the rows and of the columns of a matrix whose first row is constant. Subtracting
column $0$ from every other column then clears the first row, and a Laplace expansion along it
leaves a Cauchy matrix of one size less, again up to scalings. The positive definiteness of the
Hilbert matrix follows from Sylvester's criterion of `Numlib.LinearAlgebra.Matrix.Cholesky`, because
its leading principal submatrices are Hilbert matrices with positive determinants.

## Implementation notes

* The matrices are indexed by `Fin n`, so the indices start from $0$. The induction of the row
  reduction is on `Fin (n + 1)`.
* The entries are field inverses, which are $0$ at $0$. In positive characteristic, an entry
  $(i + j + 1)^{-1}$ of the Hilbert matrix can be $0$ for this reason.
-/

namespace Matrix

variable {K : Type*} [Field K]

/-- The **Cauchy matrix** of $x, y \in K^n$ is the $n \times n$ matrix $C$ with entries
$$C_{ij} = (x_i + y_j)^{-1}.$$
The inverse is the field inverse, which is $0$ at $0$. -/
def cauchy {n : ℕ} (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  .of fun i j => (x i + y j)⁻¹

/-- The entries of the Cauchy matrix are $C_{ij} = (x_i + y_j)^{-1}$. -/
@[simp]
theorem cauchy_apply {n : ℕ} (x y : Fin n → K) (i j : Fin n) :
    cauchy x y i j = (x i + y j)⁻¹ :=
  rfl

/-- **The Cauchy determinant.** Let $K$ be a field and let $x, y \in K^n$ with $x_i + y_j \ne 0$ for
all $i, j$. Then the Cauchy matrix $C$ of $x$ and $y$ has the determinant
$$\det C = \frac{\prod_{i < j} (x_j - x_i)(y_j - y_i)}{\prod_{i, j} (x_i + y_j)}.$$

The proof is by induction on $n$: a row reduction and a column reduction with the index $0$,
followed by a Laplace expansion along the first row, leave a Cauchy matrix of size $n - 1$ up to
scalings of the rows and the columns. -/
theorem det_cauchy : ∀ {n : ℕ} (x y : Fin n → K), (∀ i j, x i + y j ≠ 0) →
    (cauchy x y).det = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j - x i) * (y j - y i)))
      / ∏ i : Fin n, ∏ j : Fin n, (x i + y j) := by
  intro n
  induction n with
  | zero => intro x y _; simp
  | succ n ih =>
    intro x y h
    -- the nonvanishing of the products that appear
    have hden0 : (∏ j : Fin (n + 1), (x 0 + y j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => h 0 j
    have hden1 : (∏ i : Fin n, (x i.succ + y 0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => h i.succ 0
    have hdenn : (∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => h i.succ j.succ
    -- subtracting row `0` from every other row
    have hB : (Matrix.of fun i j : Fin (n + 1) =>
        if i = 0 then (x 0 + y j)⁻¹
        else (x 0 - x i) * ((x i + y j)⁻¹ * (x 0 + y j)⁻¹)).det = (cauchy x y).det := by
      refine Matrix.det_eq_of_forall_row_eq_smul_add_const
        (c := fun i => if i = 0 then 0 else -1) 0 (by simp) fun i j => ?_
      by_cases hi : i = 0
      · simp [hi]
      · have h1 := h i j
        have h2 := h 0 j
        simp only [of_apply, hi, ite_false, cauchy_apply, neg_mul, one_mul]
        field_simp
        ring
    -- factoring the rows and the columns
    have hBfac : (Matrix.of fun i j : Fin (n + 1) =>
        if i = 0 then (x 0 + y j)⁻¹
        else (x 0 - x i) * ((x i + y j)⁻¹ * (x 0 + y j)⁻¹))
        = Matrix.of fun i j : Fin (n + 1) => (if i = 0 then 1 else x 0 - x i) *
            ((x 0 + y j)⁻¹ * (if i = 0 then 1 else (x i + y j)⁻¹)) := by
      ext i j
      by_cases hi : i = 0
      · simp [hi]
      · simp only [of_apply, hi, ite_false]
        ring
    have hM1 : (Matrix.of fun i j : Fin (n + 1) => (if i = 0 then 1 else x 0 - x i) *
          ((x 0 + y j)⁻¹ * (if i = 0 then 1 else (x i + y j)⁻¹))).det
        = (∏ i : Fin (n + 1), (if i = 0 then 1 else x 0 - x i)) *
          (Matrix.of fun i j : Fin (n + 1) =>
            (x 0 + y j)⁻¹ * (if i = 0 then 1 else (x i + y j)⁻¹)).det :=
      Matrix.det_mul_column _ _
    have hM2 : (Matrix.of fun i j : Fin (n + 1) =>
          (x 0 + y j)⁻¹ * (if i = 0 then 1 else (x i + y j)⁻¹)).det
        = (∏ j : Fin (n + 1), (x 0 + y j)⁻¹) *
          (Matrix.of fun i j : Fin (n + 1) => if i = 0 then 1 else (x i + y j)⁻¹).det :=
      Matrix.det_mul_row _ _
    have hM : (cauchy x y).det
        = (∏ i : Fin (n + 1), (if i = 0 then 1 else x 0 - x i)) *
          ((∏ j : Fin (n + 1), (x 0 + y j)⁻¹) *
            (Matrix.of fun i j : Fin (n + 1) => if i = 0 then 1 else (x i + y j)⁻¹).det) := by
      rw [← hB, hBfac, hM1, hM2]
    -- subtracting column `0` from every other column
    have hN : (Matrix.of fun i j : Fin (n + 1) =>
        if j = 0 then (if i = 0 then 1 else (x i + y 0)⁻¹)
        else (if i = 0 then 1 else (x i + y j)⁻¹) - (if i = 0 then 1 else (x i + y 0)⁻¹)).det
        = (Matrix.of fun i j : Fin (n + 1) => if i = 0 then 1 else (x i + y j)⁻¹).det := by
      rw [← Matrix.det_transpose, ← Matrix.det_transpose
        (Matrix.of fun i j : Fin (n + 1) => if i = 0 then 1 else (x i + y j)⁻¹)]
      refine Matrix.det_eq_of_forall_row_eq_smul_add_const
        (c := fun j => if j = 0 then 0 else -1) 0 (by simp) fun j i => ?_
      by_cases hj : j = 0
      · simp [hj]
      · simp only [Matrix.transpose_apply, of_apply, hj, ite_false, neg_mul, one_mul]
        ring
    -- the first row is now `(1, 0, …, 0)`, and a Laplace expansion along it drops a size
    have hexp : (Matrix.of fun i j : Fin (n + 1) =>
        if j = 0 then (if i = 0 then 1 else (x i + y 0)⁻¹)
        else (if i = 0 then 1 else (x i + y j)⁻¹) - (if i = 0 then 1 else (x i + y 0)⁻¹)).det
        = ((Matrix.of fun i j : Fin (n + 1) =>
            if j = 0 then (if i = 0 then 1 else (x i + y 0)⁻¹)
            else (if i = 0 then 1 else (x i + y j)⁻¹) -
              (if i = 0 then 1 else (x i + y 0)⁻¹)).submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
      · simp
      · intro j _ hj0
        simp [hj0]
      · simp
    have hsub : (Matrix.of fun i j : Fin (n + 1) =>
        if j = 0 then (if i = 0 then 1 else (x i + y 0)⁻¹)
        else (if i = 0 then 1 else (x i + y j)⁻¹) -
          (if i = 0 then 1 else (x i + y 0)⁻¹)).submatrix Fin.succ Fin.succ
        = Matrix.of fun i j : Fin n => (x i.succ + y 0)⁻¹ *
            ((y 0 - y j.succ) * cauchy (x ∘ Fin.succ) (y ∘ Fin.succ) i j) := by
      ext i j
      have h1 := h i.succ j.succ
      have h2 := h i.succ 0
      simp only [Matrix.submatrix_apply, of_apply, Fin.succ_ne_zero, ite_false, cauchy_apply,
        Function.comp_apply]
      field_simp
      ring
    have hsubdet : ((Matrix.of fun i j : Fin (n + 1) =>
        if j = 0 then (if i = 0 then 1 else (x i + y 0)⁻¹)
        else (if i = 0 then 1 else (x i + y j)⁻¹) -
          (if i = 0 then 1 else (x i + y 0)⁻¹)).submatrix Fin.succ Fin.succ).det
        = (∏ i : Fin n, (x i.succ + y 0)⁻¹) * ((∏ j : Fin n, (y 0 - y j.succ)) *
            (cauchy (x ∘ Fin.succ) (y ∘ Fin.succ)).det) := by
      have e1 : (Matrix.of fun i j : Fin n => (x i.succ + y 0)⁻¹ *
            ((y 0 - y j.succ) * cauchy (x ∘ Fin.succ) (y ∘ Fin.succ) i j)).det
          = (∏ i : Fin n, (x i.succ + y 0)⁻¹) *
            (Matrix.of fun i j : Fin n =>
              (y 0 - y j.succ) * cauchy (x ∘ Fin.succ) (y ∘ Fin.succ) i j).det :=
        Matrix.det_mul_column _ _
      have e2 : (Matrix.of fun i j : Fin n =>
            (y 0 - y j.succ) * cauchy (x ∘ Fin.succ) (y ∘ Fin.succ) i j).det
          = (∏ j : Fin n, (y 0 - y j.succ)) * (cauchy (x ∘ Fin.succ) (y ∘ Fin.succ)).det :=
        Matrix.det_mul_row _ _
      rw [hsub, e1, e2]
    -- the induction hypothesis, and the two products split off the index `0`
    have hih := ih (x ∘ Fin.succ) (y ∘ Fin.succ) fun i j => h i.succ j.succ
    simp only [Function.comp_apply] at hih
    have hnum : (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, ((x j - x i) * (y j - y i)))
        = (∏ i : Fin n, ((x 0 - x i.succ) * (y 0 - y i.succ))) *
          ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j.succ - x i.succ) * (y j.succ - y i.succ)) := by
      rw [Fin.prod_univ_succ]
      congr 1
      · rw [Fin.prod_Ioi_zero]
        exact Finset.prod_congr rfl fun i _ => by ring
      · exact Finset.prod_congr rfl fun i _ => Fin.prod_Ioi_succ _ i
    have hden : (∏ i : Fin (n + 1), ∏ j : Fin (n + 1), (x i + y j))
        = (∏ j : Fin (n + 1), (x 0 + y j)) * ((∏ i : Fin n, (x i.succ + y 0)) *
          ∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)) := by
      rw [Fin.prod_univ_succ, ← Finset.prod_mul_distrib]
      congr 1
      exact Finset.prod_congr rfl fun i _ => Fin.prod_univ_succ _
    have hrow : (∏ i : Fin (n + 1), (if i = 0 then 1 else x 0 - x i))
        = ∏ i : Fin n, (x 0 - x i.succ) := by
      rw [Fin.prod_univ_succ]
      simp [Fin.succ_ne_zero]
    have hsplit : (∏ i : Fin n, ((x 0 - x i.succ) * (y 0 - y i.succ)))
        = (∏ i : Fin n, (x 0 - x i.succ)) * ∏ i : Fin n, (y 0 - y i.succ) :=
      Finset.prod_mul_distrib
    -- assembling: everything is now a rational expression in six products
    rw [hM, ← hN, hexp, hsubdet, hih, hnum, hden, Finset.prod_inv_distrib,
      Finset.prod_inv_distrib, hrow, hsplit]
    set PA := ∏ j : Fin (n + 1), (x 0 + y j)
    set PB := ∏ i : Fin n, (x i.succ + y 0)
    set PD := ∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)
    set PX := ∏ i : Fin n, (x 0 - x i.succ)
    set PY := ∏ i : Fin n, (y 0 - y i.succ)
    set PN := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j.succ - x i.succ) * (y j.succ - y i.succ))
    field_simp

/-- Let $K$ be a field and let $x, y \in K^n$ with $x_i + y_j \ne 0$ for all $i, j$. If the entries
of $x$ are distinct and the entries of $y$ are distinct, then the Cauchy matrix of $x$ and $y$
has a nonzero determinant. -/
theorem det_cauchy_ne_zero {n : ℕ} {x y : Fin n → K} (h : ∀ i j, x i + y j ≠ 0)
    (hx : Function.Injective x) (hy : Function.Injective y) : (cauchy x y).det ≠ 0 := by
  rw [det_cauchy x y h, div_ne_zero_iff]
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_,
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => h i j⟩
  have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
  exact mul_ne_zero (sub_ne_zero.2 fun heq => hij (hx heq).symm)
    (sub_ne_zero.2 fun heq => hij (hy heq).symm)

/-!
### The Hilbert matrix

The Hilbert matrix $h_{ij} = 1 / (i + j + 1)$ is the Cauchy matrix of $x_i = i + 1$ and $y_j = j$.
It is nonsingular, its determinant is positive over an ordered field, and it is positive definite by
Sylvester's criterion, since its leading principal submatrices are Hilbert matrices
(`Matrix.hilbert_submatrix_castLE`, `Matrix.det_leadingPrincipalSubmatrix_fin`).
-/

section Hilbert

open scoped ComplexOrder

/-- The **Hilbert matrix** of order $n$ over a field $K$ is the matrix $H_n$ with entries
$$h_{ij} = \frac{1}{i + j + 1}, \qquad 0 \le i, j < n.$$
With indices from $1$, this is the matrix $h_{ij} = 1 / (i + j - 1)$ of
[quarteroni2000numerical], (3.32).

It is the Cauchy matrix of $x_i = i + 1$ and $y_j = j$ (`Matrix.hilbert_eq_cauchy`), the Gram
matrix of the monomials $1, t, \dots, t^{n-1}$ in $L^2(0, 1)$, and the standard example of an
ill-conditioned symmetric positive definite matrix. The entry is the field inverse of
$i + j + 1$, which is $0$ if $i + j + 1 = 0$ in $K$. -/
def hilbert (K : Type*) [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  .of fun i j => ((i : K) + j + 1)⁻¹

variable (K)

/-- The entries of the Hilbert matrix are $h_{ij} = 1 / (i + j + 1)$. -/
theorem hilbert_apply (n : ℕ) (i j : Fin n) : hilbert K n i j = 1 / ((i : K) + j + 1) := by
  simp [hilbert]

/-- The Hilbert matrix is the Cauchy matrix of $x_i = i + 1$ and $y_j = j$. -/
theorem hilbert_eq_cauchy (n : ℕ) :
    hilbert K n = cauchy (fun i : Fin n => (i : K) + 1) fun j => (j : K) := by
  ext i j
  simp only [hilbert, of_apply, cauchy_apply]
  ring_nf

/-- Let $K$ be a field of characteristic $0$. Then the Hilbert matrix of every order $n$ is
nonsingular.

It is a Cauchy matrix with distinct $x_i$ and distinct $y_j$, so `Matrix.det_cauchy_ne_zero`
applies. -/
theorem isUnit_hilbert [CharZero K] (n : ℕ) : IsUnit (hilbert K n) := by
  rw [isUnit_iff_isUnit_det, hilbert_eq_cauchy, isUnit_iff_ne_zero]
  refine det_cauchy_ne_zero (fun i j => ?_) (fun i j h => ?_) fun i j h => ?_
  · have : ((i : K) + 1 + j) = ((i + 1 + j : ℕ) : K) := by push_cast; ring
    rw [this]
    exact Nat.cast_ne_zero.2 (by omega)
  · exact Fin.ext (Nat.cast_injective (add_right_cancel h))
  · exact Fin.ext (Nat.cast_injective h)

/-- Let $K$ be an ordered field. Then the Hilbert matrix of every order $n$ has a positive
determinant.

In the Cauchy determinant every factor is $(x_j - x_i)(y_j - y_i) = (j - i)^2$ with $i < j$, and
every $x_i + y_j = i + j + 1$ is positive. -/
theorem det_hilbert_pos [LinearOrder K] [IsStrictOrderedRing K] (n : ℕ) :
    0 < (hilbert K n).det := by
  rw [hilbert_eq_cauchy, det_cauchy _ _ fun i j => by positivity]
  refine div_pos (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_)
    (Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity)
  have hij : (i : K) < j := by exact_mod_cast Finset.mem_Ioi.1 hj
  have h1 : (0 : K) < (j : K) + 1 - ((i : K) + 1) := by linarith
  have h2 : (0 : K) < (j : K) - i := by linarith
  exact mul_pos h1 h2

/-- For $m \le n$, the leading principal submatrix of order $m$ of the Hilbert matrix $H_n$ is
$H_m$. -/
theorem hilbert_submatrix_castLE (n m : ℕ) (h : m ≤ n) :
    (hilbert K n).submatrix (Fin.castLE h) (Fin.castLE h) = hilbert K m := by
  ext i j
  simp [hilbert]

/-- Over a field with the trivial involution, the Hilbert matrix is symmetric. -/
theorem isHermitian_hilbert [StarRing K] [TrivialStar K] (n : ℕ) : (hilbert K n).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, hilbert, of_apply, star_trivial]
  ring_nf

/-- **The Hilbert matrix is positive definite.** For every $n$, the real Hilbert matrix $H_n$ is
symmetric positive definite.

The proof is Sylvester's criterion: the leading principal minors are determinants of smaller
Hilbert matrices, which are positive. Section 3.4.2 of [quarteroni2000numerical] factors $H_3$
as $LDL^T$ with positive $D$, and Example 3.2 there runs Gaussian elimination on it without
pivoting. -/
theorem posDef_hilbert (n : ℕ) : (hilbert ℝ n).PosDef := by
  refine (posDef_iff_forall_det_leadingPrincipalSubmatrix_pos (isHermitian_hilbert ℝ n)).2
    fun k => ?_
  rw [det_leadingPrincipalSubmatrix_fin, hilbert_submatrix_castLE]
  exact det_hilbert_pos ℝ _

end Hilbert

end Matrix
