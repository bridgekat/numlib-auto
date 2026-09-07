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

/-!
# The Cauchy matrix and its determinant

The **Cauchy matrix** of two families `x, y : Fin n → K` is the matrix `C` with entries `C i j = (x
i + y j)⁻¹`. Its determinant has the closed form

`det C = ∏_{i < j} (x j - x i) (y j - y i) / ∏_{i, j} (x i + y j)`,

which is `Matrix.det_cauchy`. In particular a Cauchy matrix with distinct `x i` and distinct `y j`
is nonsingular (`Matrix.det_cauchy_ne_zero`), so the family of functions whose Gram matrix it is —
`t ↦ t ^ (x i)` on `L²(0, 1)`, whose Gram matrix is `(x i + x j + 1)⁻¹` — is linearly independent.

The proof is the classical row reduction, in the shape that suits `Fin (n + 1)`: subtracting row `0`
from every other row makes the entry at `(i, j)` a multiple of `(x i + y j)⁻¹ (x 0 + y j)⁻¹`, which
factors as a scaling of the rows and of the columns of a matrix whose first row is constant;
subtracting column `0` from every other column then clears the first row, and a Laplace expansion
along it leaves a Cauchy matrix of one size less, again up to scalings.

## Main results

* `Matrix.det_cauchy`: the closed form of the determinant.
* `Matrix.det_cauchy_ne_zero`: it is nonzero when the `x i` are distinct and the `y j` are distinct.
-/

namespace Matrix

variable {K : Type*} [Field K]

/-- The **Cauchy matrix** of `x` and `y`: the matrix with entries `(x i + y j)⁻¹`. -/
def cauchy {n : ℕ} (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  .of fun i j => (x i + y j)⁻¹

@[simp]
theorem cauchy_apply {n : ℕ} (x y : Fin n → K) (i j : Fin n) :
    cauchy x y i j = (x i + y j)⁻¹ :=
  rfl

/-- **The Cauchy determinant.** -/
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

/-- A Cauchy matrix whose `x` and whose `y` are injective is nonsingular. -/
theorem det_cauchy_ne_zero {n : ℕ} {x y : Fin n → K} (h : ∀ i j, x i + y j ≠ 0)
    (hx : Function.Injective x) (hy : Function.Injective y) : (cauchy x y).det ≠ 0 := by
  rw [det_cauchy x y h, div_ne_zero_iff]
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_,
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => h i j⟩
  have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
  exact mul_ne_zero (sub_ne_zero.2 fun heq => hij (hx heq).symm)
    (sub_ne_zero.2 fun heq => hij (hy heq).symm)

end Matrix
