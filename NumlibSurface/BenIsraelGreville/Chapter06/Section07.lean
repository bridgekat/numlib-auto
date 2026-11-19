/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter06.Section04
import Mathlib.Analysis.Complex.CauchyIntegral
import Numlib.Analysis.Matrix.Function.CFC
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Lagrange

/-!
# Rectangular spectral calculus

Section 6.7 of [benIsrael2003generalized] chooses phases for the nonzero
singular values and uses their rank-one partial isometries to define
functions and resolvents of rectangular matrices.

## Deviations from the source

* **Corollary 3** (correction). The pseudoinverse uses the adjoints of
  the rectangular spectral components.
* **Lemma 6** (correction). The product on the right side of the first
  resolvent identity contains the aggregate partial isometry between
  the two resolvents, as in the intermediate step of the printed proof.
* **Exercises 84, 85 and 91** (negative powers). Negative powers act by
  powers of the Moore–Penrose inverse on the corresponding support.
* **Exercise 89** (scope). The coefficients used in the imaginary
  exponential are real so that each exponential coefficient has unit modulus.
-/

namespace BenIsraelGreville.Chapter06

open Matrix

section Calculus

variable {m n k p : Type*} [Fintype k] [DecidableEq k]

/-- The spectral expansion for a fixed pair of left and right
singular-vector matrices and a diagonal of coefficients. -/
def rectangularSpectralExpansion (U : Matrix m k ℂ) (V : Matrix n k ℂ) (d : k → ℂ) :
    Matrix m n ℂ := U * diagonal d * Vᴴ

/-- **Theorem 18** of [benIsrael2003generalized], Chapter 6, in thin
singular-vector coordinates. Each coefficient in the chosen support is
nonzero and the left and right families have orthonormal columns. -/
structure IsRectangularSpectralDecomposition [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    (U : Matrix m k ℂ) (V : Matrix n k ℂ) (d : k → ℂ) : Prop where
  left_orthonormal : Uᴴ * U = 1
  right_orthonormal : Vᴴ * V = 1
  eq_expansion : A = rectangularSpectralExpansion U V d
  coeff_ne_zero : ∀ i, d i ≠ 0

/-- **Definition 6** of [benIsrael2003generalized], Chapter 6, Equations
(156)–(157). Apply the scalar function to the coefficients of the fixed
rectangular spectral expansion. -/
def rectangularMatrixFunction (U : Matrix m k ℂ) (V : Matrix n k ℂ) (d : k → ℂ)
    (f : ℂ → ℂ) : Matrix m n ℂ :=
  rectangularSpectralExpansion U V (fun i => f (d i))

/-- **Equation (152)** of [benIsrael2003generalized], Chapter 6.
The component of one coordinate in the chosen spectral expansion. -/
def rectangularSpectralComponent (U : Matrix m k ℂ) (V : Matrix n k ℂ) (i : k) :
    Matrix m n ℂ :=
  rectangularSpectralExpansion U V (fun j => if j = i then 1 else 0)

/-- **Equations (151), (156)** of [benIsrael2003generalized], Chapter 6.
The product in thin coordinates equals the sum of its scaled
rank-one components. -/
theorem rectangularSpectralExpansion_eq_sum (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (d : k → ℂ) :
    rectangularSpectralExpansion U V d = ∑ i, d i • rectangularSpectralComponent U V i := by
  classical
  have hD : diagonal d = ∑ i, d i • diagonal (fun j => if j = i then (1 : ℂ) else 0) := by
    ext a b
    by_cases hb : a = b
    · subst b
      simp [Matrix.sum_apply, Matrix.smul_apply, mul_ite]
    · simp [Matrix.sum_apply, Matrix.smul_apply, hb]
  calc
    rectangularSpectralExpansion U V d =
        U * (∑ i, d i • diagonal (fun j => if j = i then (1 : ℂ) else 0)) * Vᴴ :=
      congrArg (fun D : Matrix k k ℂ => U * D * Vᴴ) hD
    _ = _ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [rectangularSpectralComponent, rectangularSpectralExpansion,
        Matrix.mul_smul, Matrix.smul_mul]

/-- **Equation (152)** of [benIsrael2003generalized], Chapter 6,
in outer-product form. -/
theorem rectangularSpectralComponent_eq_vecMulVec (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (i : k) :
    rectangularSpectralComponent U V i = vecMulVec (U.col i) (star (V.col i)) := by
  ext a b
  unfold rectangularSpectralComponent rectangularSpectralExpansion
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp only [mul_diagonal, eq_self, ite_true, mul_one, conjTranspose_apply,
      vecMulVec_apply, Matrix.col_apply, Pi.star_apply]
  · intro j _ hj
    simp only [mul_diagonal, ite_eq_right hj, mul_zero, zero_mul]
  · simp

private theorem rectangularSpectralExpansion_adjoint (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (d : k → ℂ) :
    (rectangularSpectralExpansion U V d)ᴴ =
      rectangularSpectralExpansion V U (fun i => star (d i)) := by
  simp only [rectangularSpectralExpansion, conjTranspose_mul, conjTranspose_conjTranspose,
    diagonal_conjTranspose, Matrix.mul_assoc]
  rfl

private theorem rectangularSpectralExpansion_mul [Fintype n]
    (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (W : Matrix p k ℂ) (hV : Vᴴ * V = 1) (a b : k → ℂ) :
    rectangularSpectralExpansion U V a * rectangularSpectralExpansion V W b =
      rectangularSpectralExpansion U W (fun i => a i * b i) := by
  unfold rectangularSpectralExpansion
  calc
    _ = U * (diagonal a * (Vᴴ * V) * diagonal b) * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one, diagonal_mul_diagonal]

private theorem rectangularSpectralExpansion_sub (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (a b : k → ℂ) :
    rectangularSpectralExpansion U V a - rectangularSpectralExpansion U V b =
      rectangularSpectralExpansion U V (fun i => a i - b i) := by
  simp only [rectangularSpectralExpansion, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]

private theorem rectangularSpectralExpansion_smul (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (c : ℂ) (a : k → ℂ) :
    c • rectangularSpectralExpansion U V a =
      rectangularSpectralExpansion U V (fun i => c * a i) := by
  rw [rectangularSpectralExpansion, rectangularSpectralExpansion, ← Matrix.smul_mul,
    ← Matrix.mul_smul, ← diagonal_smul]
  rfl

private theorem rectangularSpectralExpansion_one (U : Matrix m k ℂ) (V : Matrix n k ℂ) :
    rectangularSpectralExpansion U V (fun _ => 1) = U * Vᴴ := by
  rw [rectangularSpectralExpansion, diagonal_one, Matrix.mul_one]

/-- **Theorem 19(a)** of [benIsrael2003generalized], Chapter 6.
The rectangular calculus is additive in its scalar function. -/
theorem rectangularMatrixFunction_add (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (d : k → ℂ) (f g : ℂ → ℂ) :
    rectangularMatrixFunction U V d (fun z => f z + g z) =
      rectangularMatrixFunction U V d f + rectangularMatrixFunction U V d g := by
  simp only [rectangularMatrixFunction, rectangularSpectralExpansion, ← diagonal_add,
    Matrix.mul_add, Matrix.add_mul]

variable [Fintype m] [Fintype n]

/-- **Theorem 19(b)** of [benIsrael2003generalized], Chapter 6.
Pointwise multiplication corresponds to matrix multiplication with the
adjoint of the aggregate partial isometry inserted. -/
theorem rectangularMatrixFunction_mul (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (d : k → ℂ) (f g : ℂ → ℂ) :
    rectangularMatrixFunction U V d (fun z => f z * g z) =
      rectangularMatrixFunction U V d f * (U * Vᴴ)ᴴ * rectangularMatrixFunction U V d g := by
  simp only [rectangularMatrixFunction, ← rectangularSpectralExpansion_one U V,
    rectangularSpectralExpansion_adjoint, star_one]
  rw [rectangularSpectralExpansion_mul _ _ _ hV, rectangularSpectralExpansion_mul _ _ _ hU]
  simp only [mul_one]

/-- **Theorem 19(c)** of [benIsrael2003generalized], Chapter 6.
Composition evaluates the second function in the same coordinates; if
the transformed coefficients stay nonzero they give another spectral
decomposition on the same support. -/
theorem rectangularMatrixFunction_comp {A : Matrix m n ℂ} {U : Matrix m k ℂ}
    {V : Matrix n k ℂ} {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d)
    (f g : ℂ → ℂ) (hg : ∀ i, g (d i) ≠ 0) :
    IsRectangularSpectralDecomposition (rectangularMatrixFunction U V d g)
      U V (fun i => g (d i)) ∧
      rectangularMatrixFunction U V d (f ∘ g) =
        rectangularMatrixFunction U V (fun i => g (d i)) f :=
  ⟨⟨h.left_orthonormal, h.right_orthonormal, rfl, hg⟩, rfl⟩

variable [DecidableEq n]

private theorem rectangularSpectralExpansion_pinv (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (d : k → ℂ) :
    (rectangularSpectralExpansion U V d).pinv =
      rectangularSpectralExpansion V U (fun i => (d i)⁻¹) := by
  let A := rectangularSpectralExpansion U V d
  let X := rectangularSpectralExpansion V U (fun i => (d i)⁻¹)
  have hAX : A * X = rectangularSpectralExpansion U U (fun i => d i * (d i)⁻¹) :=
    rectangularSpectralExpansion_mul U V U hV _ _
  have hXA : X * A = rectangularSpectralExpansion V V (fun i => (d i)⁻¹ * d i) :=
    rectangularSpectralExpansion_mul V U V hU _ _
  change A.pinv = X
  symm
  refine A.pinv_unique ?_ ?_ ?_ ?_
  · rw [hAX]
    change _ * rectangularSpectralExpansion U V d = _
    rw [rectangularSpectralExpansion_mul _ _ _ hU]
    apply congrArg (rectangularSpectralExpansion U V)
    funext i
    by_cases hi : d i = 0 <;> simp [hi, mul_inv_cancel₀]
  · rw [hXA]
    change _ * rectangularSpectralExpansion V U (fun i => (d i)⁻¹) = _
    rw [rectangularSpectralExpansion_mul _ _ _ hV]
    apply congrArg (rectangularSpectralExpansion V U)
    funext i
    by_cases hi : d i = 0 <;> simp [hi, inv_mul_cancel₀]
  · rw [hAX]
    change (rectangularSpectralExpansion U U _)ᴴ = _
    rw [rectangularSpectralExpansion_adjoint]
    apply congrArg (rectangularSpectralExpansion U U)
    funext i
    by_cases hi : d i = 0 <;> simp [hi, mul_inv_cancel₀]
  · rw [hXA]
    change (rectangularSpectralExpansion V V _)ᴴ = _
    rw [rectangularSpectralExpansion_adjoint]
    apply congrArg (rectangularSpectralExpansion V V)
    funext i
    by_cases hi : d i = 0 <;> simp [hi, inv_mul_cancel₀]

/-- **Corollary 3** of [benIsrael2003generalized], Chapter 6, Equation
(153), in thin coordinates. Reciprocate the coefficients and exchange
the left and right singular-vector matrices. -/
theorem corollary_6_3 {A : Matrix m n ℂ} {U : Matrix m k ℂ} {V : Matrix n k ℂ}
    {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d) :
    A.pinv = rectangularSpectralExpansion V U (fun i => (d i)⁻¹) := by
  rw [h.eq_expansion, rectangularSpectralExpansion_pinv U V h.left_orthonormal h.right_orthonormal]

/-- **Corollary 3**, sum form, of [benIsrael2003generalized], Chapter 6.
The reciprocal weights multiply the adjoints of the components. -/
theorem corollary_6_3_sum {A : Matrix m n ℂ} {U : Matrix m k ℂ} {V : Matrix n k ℂ}
    {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d) :
    A.pinv = ∑ i, (d i)⁻¹ • (rectangularSpectralComponent U V i)ᴴ := by
  rw [corollary_6_3 h, rectangularSpectralExpansion_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold rectangularSpectralComponent
  rw [rectangularSpectralExpansion_adjoint]
  apply congrArg (rectangularSpectralExpansion V U)
  funext j
  by_cases hj : j = i <;> simp [hj]

omit [DecidableEq n] in
/-- **Theorem 18** of [benIsrael2003generalized], Chapter 6, Equations
(149a)–(150). Distinct components annihilate one another under adjoint
multiplication, and their sum is the aggregate partial isometry. -/
theorem rectangularSpectralComponents_orthogonal (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (∀ i j, i ≠ j →
      rectangularSpectralComponent U V i * (rectangularSpectralComponent U V j)ᴴ = 0 ∧
      (rectangularSpectralComponent U V i)ᴴ * rectangularSpectralComponent U V j = 0) ∧
      ∑ i, rectangularSpectralComponent U V i = U * Vᴴ := by
  constructor
  · intro i j hij
    constructor
    · simp only [rectangularSpectralComponent, rectangularSpectralExpansion_adjoint,
        rectangularSpectralExpansion_mul _ _ _ hV]
      have he : (fun a => (if a = i then (1 : ℂ) else 0) * star (if a = j then 1 else 0)) =
          fun _ => 0 := by
        funext a
        by_cases ha : a = i <;> simp [ha, hij]
      rw [he]
      simp [rectangularSpectralExpansion]
    · simp only [rectangularSpectralComponent, rectangularSpectralExpansion_adjoint,
        rectangularSpectralExpansion_mul _ _ _ hU]
      have he : (fun a => star (if a = i then (1 : ℂ) else 0) * (if a = j then 1 else 0)) =
          fun _ => 0 := by
        funext a
        by_cases ha : a = i <;> simp [ha, hij]
      rw [he]
      simp [rectangularSpectralExpansion]
  · have he := rectangularSpectralExpansion_eq_sum U V (fun _ => (1 : ℂ))
    simpa only [rectangularSpectralExpansion_one, one_smul] using he.symm

omit [DecidableEq n] in
private theorem rectangularSpectralExpansion_rank (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (d : k → ℂ) :
    (rectangularSpectralExpansion U V d).rank = (diagonal d).rank := by
  let X := rectangularSpectralExpansion U V d
  have hRec : Uᴴ * X * V = diagonal d := by
    change Uᴴ * (U * diagonal d * Vᴴ) * V = _
    calc
      _ = (Uᴴ * U) * diagonal d * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
  refine le_antisymm ?_ ?_
  · unfold rectangularSpectralExpansion
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · rw [← hRec]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

omit [DecidableEq n] in
/-- The number of nonzero rectangular spectral coefficients is the rank. -/
theorem IsRectangularSpectralDecomposition.rank_eq_card {A : Matrix m n ℂ}
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) : A.rank = Fintype.card k := by
  classical
  rw [h.eq_expansion, rectangularSpectralExpansion_rank U V h.left_orthonormal h.right_orthonormal,
    rank_diagonal, Fintype.card_subtype]
  simp [h.coeff_ne_zero]

private theorem rectangularSpectralExpansion_partialIsometry {U : Matrix m k ℂ}
    {V : Matrix n k ℂ} (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) {d : k → ℂ}
    (hd : ∀ i, d i = 0 ∨ d i = 1) :
    IsPartialIsometry (rectangularSpectralExpansion U V d) := by
  apply (isPartialIsometry_iff_adjoint_eq_pinv _).mpr
  rw [rectangularSpectralExpansion_adjoint, rectangularSpectralExpansion_pinv U V hU hV]
  apply congrArg (rectangularSpectralExpansion V U)
  funext i
  rcases hd i with h | h <;> simp [h]

/-- **Theorem 18** of [benIsrael2003generalized], Chapter 6.
Each rectangular spectral component is a rank-one partial isometry. -/
theorem rectangularSpectralComponent_rank_one (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (i : k) :
    (rectangularSpectralComponent U V i).rank = 1 ∧
      IsPartialIsometry (rectangularSpectralComponent U V i) := by
  classical
  constructor
  · unfold rectangularSpectralComponent
    rw [rectangularSpectralExpansion_rank U V hU hV, rank_diagonal, Fintype.card_subtype]
    have hs : Finset.univ.filter (fun j : k => (if j = i then (1 : ℂ) else 0) ≠ 0) = {i} := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [hs, Finset.card_singleton]
  · exact rectangularSpectralExpansion_partialIsometry hU hV
      (fun j => by by_cases hj : j = i <;> simp [hj])

/-- **Theorem 18** of [benIsrael2003generalized], Chapter 6, Equations
(149b)–(150). The aggregate is a partial isometry and inserts the
correct adjoint in the component commutation relation. -/
theorem rectangularSpectralComponent_commutes {A : Matrix m n ℂ}
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) (i : k) :
    IsPartialIsometry (U * Vᴴ) ∧
      rectangularSpectralComponent U V i * (U * Vᴴ)ᴴ * A =
        A * (U * Vᴴ)ᴴ * rectangularSpectralComponent U V i := by
  constructor
  · rw [← rectangularSpectralExpansion_one U V]
    exact rectangularSpectralExpansion_partialIsometry h.left_orthonormal h.right_orthonormal
      (fun _ => Or.inr rfl)
  · rw [h.eq_expansion]
    simp only [rectangularSpectralComponent, ← rectangularSpectralExpansion_one U V,
      rectangularSpectralExpansion_adjoint, star_one]
    rw [rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal,
      rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal,
      rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal,
      rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal]
    simp only [mul_one, one_mul, mul_comm]

open Classical in
/-- **Equation (158)** of [benIsrael2003generalized], Chapter 6.
The grouped component retains exactly the coordinates at a prescribed
spectral coefficient. -/
noncomputable def rectangularGroupedComponent (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (d : k → ℂ) (w : ℂ) : Matrix m n ℂ :=
  rectangularSpectralExpansion U V (fun i => if d i = w then 1 else 0)

omit [Fintype m] [Fintype n] [DecidableEq n] in
open Classical in
/-- The grouped component is the sum of all components at its coefficient. -/
theorem rectangularGroupedComponent_eq_sum (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (d : k → ℂ) (w : ℂ) :
    rectangularGroupedComponent U V d w =
      ∑ i ∈ Finset.univ.filter (fun i => d i = w), rectangularSpectralComponent U V i := by
  classical
  rw [rectangularGroupedComponent, rectangularSpectralExpansion_eq_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : d i = w <;> simp [hi]

/-- **Lemma 5(a)** of [benIsrael2003generalized], Chapter 6.
Grouping components with a common coefficient gives a partial isometry. -/
theorem rectangularGroupedComponent_partialIsometry (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (d : k → ℂ) (w : ℂ) :
    IsPartialIsometry (rectangularGroupedComponent U V d w) := by
  classical
  unfold rectangularGroupedComponent
  exact rectangularSpectralExpansion_partialIsometry hU hV
    (fun i => by by_cases hi : d i = w <;> simp [hi])

/-- **Exercise 83** of [benIsrael2003generalized], Chapter 6, Equations
(171a)–(171b). Generalized integer powers raise each spectral
coefficient to the indicated power in the fixed singular coordinates. -/
noncomputable def rectangularPower (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (d : k → ℂ) (j : ℤ) : Matrix m n ℂ :=
  rectangularMatrixFunction U V d (fun z => z ^ j)

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- The zeroth generalized power is the aggregate partial isometry. -/
theorem rectangularPower_zero (U : Matrix m k ℂ) (V : Matrix n k ℂ) (d : k → ℂ) :
    rectangularPower U V d 0 = U * Vᴴ := by
  simp only [rectangularPower, rectangularMatrixFunction, zpow_zero,
    rectangularSpectralExpansion_one]

omit [DecidableEq n] in
/-- The first generalized power is the original matrix. -/
theorem rectangularPower_one {A : Matrix m n ℂ} {U : Matrix m k ℂ}
    {V : Matrix n k ℂ} {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d) :
    rectangularPower U V d 1 = A := by
  simpa only [rectangularPower, rectangularMatrixFunction, zpow_one] using h.eq_expansion.symm

omit [DecidableEq n] in
/-- **Exercise 83**, Equation (172), of [benIsrael2003generalized],
Chapter 6. Generalized powers add exponents under the twisted product.
Taking an exponent of one or minus one gives the two recurrences. -/
theorem rectangularPower_add {A : Matrix m n ℂ} {U : Matrix m k ℂ}
    {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) (a b : ℤ) :
    rectangularPower U V d (a + b) =
      rectangularPower U V d a * (U * Vᴴ)ᴴ * rectangularPower U V d b := by
  have he : (fun i => d i ^ (a + b)) = fun i => d i ^ a * d i ^ b :=
    funext fun i => zpow_add₀ (h.coeff_ne_zero i) a b
  have hm := rectangularMatrixFunction_mul U V h.left_orthonormal h.right_orthonormal d
    (fun z => z ^ a) (fun z => z ^ b)
  simpa only [rectangularPower, rectangularMatrixFunction, he] using hm

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- **Exercise 84(a)** of [benIsrael2003generalized], Chapter 6.
Adjointing generalized powers exchanges the two bases and conjugates
their coefficients. -/
theorem rectangularPower_adjoint (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (d : k → ℂ) (j : ℤ) :
    (rectangularPower U V d j)ᴴ = rectangularPower V U (fun i => star (d i)) j := by
  simp only [rectangularPower, rectangularMatrixFunction, rectangularSpectralExpansion_adjoint]
  apply congrArg (rectangularSpectralExpansion V U)
  funext i
  exact map_zpow₀ (starRingEnd ℂ) (d i) j

/-- **Exercise 84**, Equation (173c), of [benIsrael2003generalized],
Chapter 6. For real coefficients the negative first power is the
adjoint of the Moore–Penrose inverse. -/
theorem rectangularPower_neg_one {A : Matrix m n ℂ} {U : Matrix m k ℂ}
    {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) (hd : ∀ i, star (d i) = d i) :
    rectangularPower U V d (-1) = A.pinvᴴ := by
  rw [corollary_6_3 h, rectangularSpectralExpansion_adjoint]
  simp only [rectangularPower, rectangularMatrixFunction, _root_.zpow_neg_one,
    ← starRingEnd_apply]
  apply congrArg (rectangularSpectralExpansion U V)
  funext i
  rw [map_inv₀, starRingEnd_apply, hd]

/-- **Exercise 84(b)** of [benIsrael2003generalized], Chapter 6,
for nonnegative Gram powers. Odd generalized powers agree with
ordinary powers of either Gram matrix times the original matrix. -/
theorem rectangularPower_odd_nat [DecidableEq m] {A : Matrix m n ℂ} {U : Matrix m k ℂ}
    {V : Matrix n k ℂ} {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d)
    (hd : ∀ i, star (d i) = d i) (j : ℕ) :
    rectangularPower U V d (2 * (j : ℤ) + 1) = A * (Aᴴ * A) ^ j ∧
    rectangularPower U V d (2 * (j : ℤ) + 1) = (A * Aᴴ) ^ j * A := by
  have hRight : Aᴴ * A = rectangularSpectralExpansion V V (fun i => d i ^ (2 : ℤ)) := by
    rw [h.eq_expansion, rectangularSpectralExpansion_adjoint,
      rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal]
    simp only [hd, zpow_ofNat, pow_two]
  have hLeft : A * Aᴴ = rectangularSpectralExpansion U U (fun i => d i ^ (2 : ℤ)) := by
    rw [h.eq_expansion, rectangularSpectralExpansion_adjoint,
      rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal]
    simp only [hd, zpow_ofNat, pow_two]
  have hStepR (a : ℤ) : rectangularPower U V d (a + 2) =
      rectangularPower U V d a * (Aᴴ * A) := by
    rw [hRight]
    unfold rectangularPower rectangularMatrixFunction
    rw [rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal]
    exact congrArg (rectangularSpectralExpansion U V)
      (funext fun i => zpow_add₀ (h.coeff_ne_zero i) a 2)
  have hStepL (a : ℤ) : rectangularPower U V d (a + 2) =
      (A * Aᴴ) * rectangularPower U V d a := by
    rw [hLeft]
    unfold rectangularPower rectangularMatrixFunction
    rw [rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal]
    exact congrArg (rectangularSpectralExpansion U V)
      (funext fun i => (zpow_add₀ (h.coeff_ne_zero i) a 2).trans (mul_comm _ _))
  induction j with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_add, pow_zero, Matrix.mul_one, Matrix.one_mul,
      rectangularPower_one h, and_self]
  | succ j ih =>
    have he : 2 * ((j + 1 : ℕ) : ℤ) + 1 = (2 * (j : ℤ) + 1) + 2 := by omega
    constructor
    · rw [he, hStepR, ih.1, Matrix.mul_assoc, pow_succ]
    · rw [he, hStepL, ih.2, ← Matrix.mul_assoc, pow_succ']

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- **Exercise 86** of [benIsrael2003generalized], Chapter 6.
Evaluation of a polynomial in ternary powers uses the odd generalized
powers in the chosen singular coordinates. -/
noncomputable def ternaryPolynomial (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (d : k → ℂ) (p : Polynomial ℂ) : Matrix m n ℂ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • rectangularPower U V d (2 * (i : ℤ) + 1)

/-- **Exercise 86** of [benIsrael2003generalized], Chapter 6.
A ternary polynomial is an ordinary polynomial of either Gram matrix
multiplied by the original matrix. -/
theorem ternaryPolynomial_eq_gram [DecidableEq m] {A : Matrix m n ℂ}
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d)
    (hd : ∀ i, star (d i) = d i) (p : Polynomial ℂ) :
    ternaryPolynomial U V d p = A * Polynomial.aeval (Aᴴ * A) p ∧
      ternaryPolynomial U V d p = Polynomial.aeval (A * Aᴴ) p * A := by
  constructor
  · simp only [ternaryPolynomial, Polynomial.aeval_eq_sum_range, Matrix.mul_sum, Matrix.mul_smul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (p.coeff i • ·)
      (rectangularPower_odd_nat h hd i).1)
  · simp only [ternaryPolynomial, Polynomial.aeval_eq_sum_range, Matrix.sum_mul, Matrix.smul_mul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (p.coeff i • ·)
      (rectangularPower_odd_nat h hd i).2)

omit [DecidableEq n] in
/-- **Exercise 91** of [benIsrael2003generalized], Chapter 6, Equation
(179). Applying a scalar function to either normal polar factor and
inserting the common partial isometry gives the rectangular function. -/
theorem rectangularMatrixFunction_polar_factors (U : Matrix m k ℂ) (V : Matrix n k ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (d : k → ℂ) (f : ℂ → ℂ) :
    rectangularMatrixFunction U V d f = rectangularMatrixFunction U U d f * (U * Vᴴ) ∧
    rectangularMatrixFunction U V d f = (U * Vᴴ) * rectangularMatrixFunction V V d f := by
  simp only [rectangularMatrixFunction, ← rectangularSpectralExpansion_one U V,
    rectangularSpectralExpansion_mul _ _ _ hU, rectangularSpectralExpansion_mul _ _ _ hV,
    mul_one, one_mul, and_self]

/-- **Equation (164)** of [benIsrael2003generalized], Chapter 6.
The rectangular resolvent is the pseudoinverse of the shifted matrix
with the aggregate partial isometry as the shift direction. -/
noncomputable def generalizedResolvent (A E : Matrix m n ℂ) (z : ℂ) : Matrix n m ℂ :=
  (z • E - A).pinv

/-- In the chosen rectangular spectral coordinates the resolvent
reciprocates the shifted coefficients and exchanges the two bases. -/
theorem generalizedResolvent_eq_spectralExpansion {A : Matrix m n ℂ}
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) (z : ℂ) :
    generalizedResolvent A (U * Vᴴ) z =
      rectangularSpectralExpansion V U (fun i => (z - d i)⁻¹) := by
  rw [generalizedResolvent, h.eq_expansion, ← rectangularSpectralExpansion_one U V,
    rectangularSpectralExpansion_smul, rectangularSpectralExpansion_sub,
    rectangularSpectralExpansion_pinv U V h.left_orthonormal h.right_orthonormal]
  simp only [mul_one]

/-- **Lemma 6**, corrected Equation (165), of [benIsrael2003generalized],
Chapter 6. The first resolvent identity inserts the aggregate partial
isometry between the two inverse factors. -/
theorem lemma_6_6 {A : Matrix m n ℂ} {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) {z w : ℂ}
    (hz : ∀ i, z ≠ d i) (hw : ∀ i, w ≠ d i) :
    generalizedResolvent A (U * Vᴴ) z - generalizedResolvent A (U * Vᴴ) w =
      (w - z) • (generalizedResolvent A (U * Vᴴ) z * (U * Vᴴ) *
        generalizedResolvent A (U * Vᴴ) w) := by
  simp only [generalizedResolvent_eq_spectralExpansion h]
  rw [rectangularSpectralExpansion_sub, ← rectangularSpectralExpansion_one U V,
    rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal,
    rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal,
    rectangularSpectralExpansion_smul]
  apply congrArg (rectangularSpectralExpansion V U)
  funext i
  rw [mul_one]
  field_simp [sub_ne_zero.mpr (hz i), sub_ne_zero.mpr (hw i)]
  ring

end Calculus

section PhaseChoice

/-- **Theorem 18** of [benIsrael2003generalized], Chapter 6, Equation
(151). Prescribed complex coefficients with the moduli of the positive
singular values give a rectangular spectral decomposition. -/
theorem theorem_6_18 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (d : Fin A.rank → ℂ) (hd : ∀ i, ‖d i‖ = A.sortedSingularValues i) :
    ∃ U V, IsRectangularSpectralDecomposition A U V d := by
  obtain ⟨U, V, h⟩ := theorem_6_2 A
  let Ur := U.submatrix id (Fin.castLE A.rank_le_height)
  let Vr := V.submatrix id (Fin.castLE A.rank_le_width)
  let D := diagonal (fun i : Fin A.rank => (A.sortedSingularValues i : ℂ))
  let p (i : Fin A.rank) := d i / (A.sortedSingularValues i : ℂ)
  let T := diagonal p
  have hσ (i : Fin A.rank) : 0 < A.sortedSingularValues i :=
    lt_of_le_of_ne (A.sortedSingularValues_nonneg i)
      (Ne.symm fun hz => not_le.mpr i.isLt ((A.sortedSingularValues_eq_zero_iff_rank_le _).mp hz))
  have hN (i : Fin A.rank) : ‖p i‖ = 1 := by
    change ‖d i / (A.sortedSingularValues i : ℂ)‖ = 1
    rw [norm_div, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hσ i),
      div_self (hσ i).ne']
  have hP (i : Fin A.rank) : p i * star (p i) = 1 := by
    change p i * starRingEnd ℂ (p i) = 1
    rw [Complex.mul_conj', hN]
    norm_num
  have hTT₁ : T * Tᴴ = 1 := by
    change diagonal p * (diagonal p)ᴴ = 1
    rw [diagonal_conjTranspose, diagonal_mul_diagonal,
      show (fun i => p i * (star p) i) = fun _ => (1 : ℂ) from funext hP, diagonal_one]
  have hTT₂ : Tᴴ * T = 1 := by
    change (diagonal p)ᴴ * diagonal p = 1
    rw [diagonal_conjTranspose, diagonal_mul_diagonal,
      show (fun i => (star p) i * p i) = fun _ => (1 : ℂ) from
        funext (fun i => (mul_comm _ _).trans (hP i)), diagonal_one]
  have hD : D * T = diagonal d := by
    change diagonal (fun i : Fin A.rank => (A.sortedSingularValues i : ℂ)) * diagonal p = _
    rw [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext i
    change (A.sortedSingularValues i : ℂ) * (d i / (A.sortedSingularValues i : ℂ)) = d i
    field_simp [Complex.ofReal_ne_zero.mpr (hσ i).ne']
  have hU : Urᴴ * Ur = 1 := conjTranspose_submatrix_castLE_mul_self _ h.1.mem_unitaryGroup_left
  have hV : Vrᴴ * Vr = 1 := conjTranspose_submatrix_castLE_mul_self _ h.1.mem_unitaryGroup_right
  have hA : A = Ur * D * Vrᴴ :=
    (svd_truncation_rank h).symm.trans (svd_truncation_expansion h le_rfl).1
  refine ⟨Ur, Vr * T, hU, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul]
    calc
      _ = Tᴴ * (Vrᴴ * Vr) * T := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one, hTT₂]
  · change A = Ur * diagonal d * (Vr * T)ᴴ
    rw [← hD, conjTranspose_mul]
    calc
      A = Ur * D * Vrᴴ := hA
      _ = Ur * D * (T * Tᴴ) * Vrᴴ := by rw [hTT₁, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro i h0
    have he := hd i
    rw [h0, norm_zero] at he
    exact (hσ i).ne' he.symm

end PhaseChoice

section Circles

open Metric
open scoped Matrix.Norms.Frobenius

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq n] [DecidableEq k]

/-- The normalized Cauchy integral of a scalar function times the
rectangular resolvent along a circle. Its output has transposed shape. -/
noncomputable def rectangularCircleCalculus (A E : Matrix m n ℂ) (f : ℂ → ℂ)
    (c : ℂ) (R : ℝ) : Matrix n m ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    circleIntegral (fun z => f z • generalizedResolvent A E z) c R

open Classical in
private theorem normalized_circleIntegral_inv_mul (f : ℂ → ℂ) {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∉ sphere c R) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (fun z => (z - w)⁻¹ * f z) c R =
      if w ∈ ball c R then f w else 0 := by
  classical
  by_cases hi : w ∈ ball c R
  · have he := hf.circleIntegral_sub_inv_smul hi
    simp only [smul_eq_mul] at he
    have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    rw [ite_eq_left hi, he, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  · have hOutside : w ∉ closedBall c R := by
      intro hc
      exact hw (mem_sphere.mpr (le_antisymm (mem_closedBall.mp hc) (le_of_not_gt hi)))
    have hg : DifferentiableOn ℂ (fun z => (z - w)⁻¹ * f z) (closedBall c R) :=
      ((differentiableOn_id.sub_const w).inv fun z hz =>
        sub_ne_zero.mpr (fun e => hOutside (e ▸ hz))).mul hf
    have he := (hg.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hR.le
    rw [ite_eq_right hi, he, mul_zero]

open Classical in
/-- **Lemma 5** of [benIsrael2003generalized], Chapter 6, circular
contour form. The normalized integral retains exactly the coefficients
inside the circle, including all occurrences of any repeated value. -/
theorem lemma_6_5_circular {A : Matrix m n ℂ} {U : Matrix m k ℂ} {V : Matrix n k ℂ}
    {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hd : ∀ i, d i ∉ sphere c R) :
    rectangularCircleCalculus A (U * Vᴴ) f c R =
      rectangularSpectralExpansion V U (fun i => if d i ∈ ball c R then f (d i) else 0) := by
  classical
  let g (i : k) (z : ℂ) := (z - d i)⁻¹ * f z
  have hF : (fun z => f z • generalizedResolvent A (U * Vᴴ) z) =
      fun z => ∑ i, g i z • rectangularSpectralComponent V U i := by
    funext z
    rw [generalizedResolvent_eq_spectralExpansion h, rectangularSpectralExpansion_eq_sum,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    exact mul_comm _ _
  have hInt (i : k) : CircleIntegrable (fun z => g i z • rectangularSpectralComponent V U i)
      c R := by
    have hi : ContinuousOn (g i) (sphere c R) := by
      refine ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => ?_).mul
        (hf.continuousOn.mono sphere_subset_closedBall)
      apply sub_ne_zero.mpr
      intro he
      change z = d i at he
      exact hd i (he ▸ hz)
    exact (hi.smul continuousOn_const).circleIntegrable hR.le
  rw [rectangularCircleCalculus, hF, circleIntegral.integral_fun_sum (fun i _ => hInt i),
    Finset.smul_sum, rectangularSpectralExpansion_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [circleIntegral.integral_smul_const, smul_smul,
    normalized_circleIntegral_inv_mul f hR hf (hd i)]

/-- **Lemma 5(a)** of [benIsrael2003generalized], Chapter 6, Equation
(159), for a circle isolating one distinct spectral coefficient. -/
theorem lemma_6_5_circular_grouped {A : Matrix m n ℂ}
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hd : ∀ i, d i ∉ sphere c R) (hInside : ∀ i, d i ∈ ball c R ↔ d i = w) :
    rectangularCircleCalculus A (U * Vᴴ) (fun _ => 1) c R =
      (rectangularGroupedComponent U V d w)ᴴ := by
  classical
  rw [lemma_6_5_circular h hR _ (differentiableOn_const 1) hd,
    rectangularGroupedComponent, rectangularSpectralExpansion_adjoint]
  apply congrArg (rectangularSpectralExpansion V U)
  funext i
  by_cases hi : d i = w
  · simp only [ite_eq_left ((hInside i).mpr hi), ite_eq_left hi, star_one]
  · simp only [ite_eq_right (mt (hInside i).mp hi), ite_eq_right hi, star_zero]

/-- **Lemma 5(b)** of [benIsrael2003generalized], Chapter 6, Equation
(160), for a finite family of circular contours. Each coefficient
lies inside exactly one circle and none lie on a boundary. -/
theorem lemma_6_5_circle_family {j : Type*} [Fintype j] {A : Matrix m n ℂ}
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) (c : j → ℂ) (R : j → ℝ)
    (hR : ∀ a, 0 < R a) (f : ℂ → ℂ) (hf : ∀ a, DifferentiableOn ℂ f (closedBall (c a) (R a)))
    (hd : ∀ a i, d i ∉ sphere (c a) (R a))
    (hCover : ∀ i, ∃! a, d i ∈ ball (c a) (R a)) :
    (∑ a, rectangularCircleCalculus A (U * Vᴴ) f (c a) (R a)) =
      rectangularMatrixFunction V U d f := by
  classical
  simp_rw [lemma_6_5_circular h (hR _) f (hf _) (hd _), rectangularMatrixFunction,
    rectangularSpectralExpansion_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_smul]
  congr 1
  obtain ⟨a, ha, hu⟩ := hCover i
  rw [Finset.sum_eq_single a]
  · simp [ha]
  · intro b _ hne
    exact ite_eq_right (fun hb => hne (hu b hb))
  · simp

/-- When the circle encloses all coefficients, the integral gives the
functional calculus with the left and right singular bases exchanged. -/
theorem rectangularCircleCalculus_eq_reversed {A : Matrix m n ℂ}
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedBall c R))
    (hd : ∀ i, d i ∈ ball c R) :
    rectangularCircleCalculus A (U * Vᴴ) f c R = rectangularMatrixFunction V U d f := by
  rw [lemma_6_5_circular h hR f hf (fun i hi => (ne_of_lt (mem_ball.mp (hd i))) (mem_sphere.mp hi))]
  unfold rectangularMatrixFunction
  simp only [ite_eq_left (hd _)]

/-- **Corollary 4** of [benIsrael2003generalized], Chapter 6, Equation
(163), for a circular contour. Multiplication on both sides by the
aggregate partial isometry restores the original rectangular shape. -/
theorem corollary_6_4_circular {A : Matrix m n ℂ} {U : Matrix m k ℂ} {V : Matrix n k ℂ}
    {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedBall c R))
    (hd : ∀ i, d i ∈ ball c R) :
    rectangularMatrixFunction U V d f =
      (U * Vᴴ) * rectangularCircleCalculus A (U * Vᴴ) f c R * (U * Vᴴ) := by
  rw [rectangularCircleCalculus_eq_reversed h hR f hf hd]
  simp only [rectangularMatrixFunction, ← rectangularSpectralExpansion_one U V]
  rw [rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal,
    rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal]
  simp only [one_mul, mul_one]

/-- **Lemma 7** of [benIsrael2003generalized], Chapter 6, Equation (166),
for a circular contour. The normalized resolvent integrals multiply
with the aggregate partial isometry between them. -/
theorem lemma_6_7_circular {A : Matrix m n ℂ} {U : Matrix m k ℂ} {V : Matrix n k ℂ}
    {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hg : DifferentiableOn ℂ g (closedBall c R))
    (hd : ∀ i, d i ∈ ball c R) :
    rectangularCircleCalculus A (U * Vᴴ) f c R * (U * Vᴴ) *
        rectangularCircleCalculus A (U * Vᴴ) g c R =
      rectangularCircleCalculus A (U * Vᴴ) (fun z => f z * g z) c R := by
  rw [rectangularCircleCalculus_eq_reversed h hR f hf hd,
    rectangularCircleCalculus_eq_reversed h hR g hg hd,
    rectangularCircleCalculus_eq_reversed h hR (fun z => f z * g z) (hf.mul hg) hd]
  simp only [rectangularMatrixFunction, ← rectangularSpectralExpansion_one U V]
  rw [rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal,
    rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal]
  simp only [mul_one]

/-- **Equation (161)** of [benIsrael2003generalized], Chapter 6, for a
circular contour. Integrating with the reciprocal scalar function
gives the Moore–Penrose inverse when the disk excludes zero. -/
theorem rectangularCircleCalculus_inv {A : Matrix m n ℂ}
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hd : ∀ i, d i ∈ ball c R) (h0 : (0 : ℂ) ∉ closedBall c R) :
    rectangularCircleCalculus A (U * Vᴴ) (fun z => z⁻¹) c R = A.pinv := by
  have hi : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) (closedBall c R) :=
    differentiableOn_id.inv fun z hz he => h0 (he ▸ hz)
  rw [rectangularCircleCalculus_eq_reversed h hR _ hi hd, corollary_6_3 h]
  rfl

/-- **Theorem 20** of [benIsrael2003generalized], Chapter 6, Equation
(169), for circular contours. The product of the two normalized
resolvent integrals with the right-hand side solves a consistent
rectangular matrix equation. -/
theorem theorem_6_20_circular {p q l : Type*} [Fintype p] [Fintype q] [Fintype l]
    [DecidableEq q] [DecidableEq l] {A : Matrix m n ℂ} {B : Matrix p q ℂ} (D : Matrix m q ℂ)
    {U : Matrix m k ℂ} {V : Matrix n k ℂ} {S : Matrix p l ℂ} {T : Matrix q l ℂ}
    {a : k → ℂ} {b : l → ℂ}
    (hA : IsRectangularSpectralDecomposition A U V a)
    (hB : IsRectangularSpectralDecomposition B S T b)
    {cA cB : ℂ} {RA RB : ℝ} (hRA : 0 < RA) (hRB : 0 < RB)
    (ha : ∀ i, a i ∈ ball cA RA) (hb : ∀ j, b j ∈ ball cB RB)
    (ha0 : (0 : ℂ) ∉ closedBall cA RA) (hb0 : (0 : ℂ) ∉ closedBall cB RB)
    (hConsistent : ∃ X : Matrix n p ℂ, A * X * B = D) :
    let X := rectangularCircleCalculus A (U * Vᴴ) (fun z => z⁻¹) cA RA * D *
      rectangularCircleCalculus B (S * Tᴴ) (fun z => z⁻¹) cB RB
    A * X * B = D := by
  obtain ⟨X₀, rfl⟩ := hConsistent
  dsimp only
  rw [rectangularCircleCalculus_inv hA hRA ha ha0, rectangularCircleCalculus_inv hB hRB hb hb0]
  calc
    _ = (A * A.pinv * A) * X₀ * (B * B.pinv * B) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [A.mul_pinv_mul_self, B.mul_pinv_mul_self]

end Circles

section NormalCoordinates

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem rectangularSpectralExpansion_restrict
    (U : Matrix n n ℂ) (d : n → ℂ) (S : Finset n) (hS : ∀ i ∉ S, d i = 0) :
    let W := U.submatrix id (fun i : S => i.val)
    rectangularSpectralExpansion U U d = rectangularSpectralExpansion W W (fun i => d i.val) := by
  let W := U.submatrix id (fun i : S => i.val)
  change rectangularSpectralExpansion U U d = rectangularSpectralExpansion W W (fun i => d i.val)
  rw [rectangularSpectralExpansion_eq_sum, rectangularSpectralExpansion_eq_sum]
  have he (i : S) :
      rectangularSpectralComponent U U i.val = rectangularSpectralComponent W W i := by
    rw [rectangularSpectralComponent_eq_vecMulVec, rectangularSpectralComponent_eq_vecMulVec]
    rfl
  calc
    _ = ∑ i ∈ S, d i • rectangularSpectralComponent U U i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [hS i hi, zero_smul]
    _ = ∑ i : S, d i.val • rectangularSpectralComponent U U i.val :=
      (Finset.sum_coe_sort S (fun i => d i • rectangularSpectralComponent U U i)).symm
    _ = _ := Finset.sum_congr rfl fun i _ => congrArg (d i.val • ·) (he i)

private theorem normal_rectangular_decomposition_of_support
    {A U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) {d : n → ℂ}
    (hA : A = U * diagonal d * Uᴴ) (S : Finset n) (hS : ∀ i, i ∈ S ↔ d i ≠ 0) :
    let W := U.submatrix id (fun i : S => i.val)
    IsRectangularSpectralDecomposition A W W (fun i => d i.val) := by
  let W := U.submatrix id (fun i : S => i.val)
  have hW : Wᴴ * W = 1 := by
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
      conjTranspose_mul_self_of_mem_unitaryGroup hU]
    exact submatrix_one _ Subtype.val_injective
  refine ⟨hW, hW, ?_, fun i => (hS i.val).mp i.property⟩
  exact hA.trans (rectangularSpectralExpansion_restrict U d S
    (fun i hi => not_not.mp fun hd => hi ((hS i).mpr hd)))

/-- **Equations (154)–(155)** of [benIsrael2003generalized], Chapter 6.
A normal matrix has a thin rectangular spectral decomposition with
equal left and right eigenvectors. Its rank-one components are
orthogonal projections. -/
theorem normal_rectangular_decomposition (A : Matrix n n ℂ) (hA : IsStarNormal A) :
    ∃ (U : Matrix n n ℂ) (d : n → ℂ) (S : Finset n),
      U ∈ unitaryGroup n ℂ ∧ A = U * diagonal d * Uᴴ ∧
      (∀ i, i ∈ S ↔ d i ≠ 0) ∧
      let W := U.submatrix id (fun i : S => i.val)
      IsRectangularSpectralDecomposition A W W (fun i => d i.val) ∧
      ∀ i : S, (rectangularSpectralComponent W W i).IsHermitian ∧
        IsIdempotentElem (rectangularSpectralComponent W W i) := by
  classical
  obtain ⟨U, hU, d, hD⟩ := Matrix.IsStarNormal.spectral_theorem.mp hA
  let S := Finset.univ.filter (fun i => d i ≠ 0)
  have hFull : A = U * diagonal d * Uᴴ := calc
    _ = (U * Uᴴ) * A * (U * Uᴴ) := by
      rw [mul_conjTranspose_self_of_mem_unitaryGroup hU, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * A * U) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hD]
  have hS (i : n) : i ∈ S ↔ d i ≠ 0 := by simp [S]
  have h := normal_rectangular_decomposition_of_support hU hFull S hS
  refine ⟨U, d, S, hU, hFull, hS, h, ?_⟩
  let W := U.submatrix id (fun i : S => i.val)
  intro i
  let e (j : S) : ℂ := if j = i then 1 else 0
  have he (j : S) : star (e j) = e j := by by_cases hj : j = i <;> simp [e, hj]
  have hs (j : S) : e j * e j = e j := by by_cases hj : j = i <;> simp [e, hj]
  constructor
  · change (rectangularSpectralExpansion W W e)ᴴ = rectangularSpectralExpansion W W e
    rw [rectangularSpectralExpansion_adjoint, show (fun j => star (e j)) = e from funext he]
  · change rectangularSpectralExpansion W W e * rectangularSpectralExpansion W W e =
      rectangularSpectralExpansion W W e
    rw [rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal,
      show (fun j => e j * e j) = e from funext hs]

private theorem square_rectangular_support_projectors {k : Type*} [Fintype k] [DecidableEq k]
    {A : Matrix n n ℂ} {W : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A W W d) :
    W * Wᴴ = Chapter02.orthogonalProjector (toEuclideanLin A).range ∧
      1 - W * Wᴴ = Chapter02.orthogonalProjector (toEuclideanLin A).ker := by
  have hC (i : k) : d i * (d i)⁻¹ = 1 := mul_inv_cancel₀ (h.coeff_ne_zero i)
  have hC' (i : k) : (d i)⁻¹ * d i = 1 := inv_mul_cancel₀ (h.coeff_ne_zero i)
  have hL : A * A.pinv = W * Wᴴ := by
    rw [corollary_6_3 h, h.eq_expansion, rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal,
      show (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℂ) from funext hC,
      rectangularSpectralExpansion_one]
  have hR : A.pinv * A = W * Wᴴ := by
    rw [corollary_6_3 h, h.eq_expansion, rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal,
      show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) from funext hC',
      rectangularSpectralExpansion_one]
  have hRange : W * Wᴴ = Chapter02.orthogonalProjector (toEuclideanLin A).range := by
    apply toEuclideanLin.injective
    rw [← hL, A.mul_pinv_eq_starProjection, Chapter02.toEuclideanLin_orthogonalProjector]
  have hKer : W * Wᴴ = Chapter02.orthogonalProjector (toEuclideanLin A).kerᗮ := by
    apply toEuclideanLin.injective
    rw [← hR, A.pinv_mul_eq_starProjection, Chapter02.toEuclideanLin_orthogonalProjector,
      LinearMap.orthogonal_ker, toEuclideanLin_conjTranspose_eq_adjoint]
  refine ⟨hRange, ?_⟩
  rw [hKer, ← Chapter02.exercise_56, Submodule.orthogonal_orthogonal]

/-- **Exercise 82** of [benIsrael2003generalized], Chapter 6, Equation
(170). In a diagonal unitary representation, the supported rectangular
calculus agrees with the primary matrix function after adding the value
at zero times the orthogonal projection onto the kernel. -/
theorem exercise_6_82 {A U : Matrix n n ℂ} {d : n → ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hA : A = U * diagonal d * Uᴴ)
    (S : Finset n) (hS : ∀ i, i ∈ S ↔ d i ≠ 0) (f : ℂ → ℂ) :
    let W := U.submatrix id (fun i : S => i.val)
    pfc f A =
      rectangularMatrixFunction W W (fun i => d i.val) f +
        f 0 • Chapter02.orthogonalProjector (toEuclideanLin A).ker := by
  classical
  let W := U.submatrix id (fun i : S => i.val)
  let b (i : n) : ℂ := if i ∈ S then f (d i) else 0
  let c (i : n) : ℂ := if i ∈ S then 1 else 0
  let u : unitary (Matrix n n ℂ) := ⟨U, hU⟩
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u
  have hp : pfc f A = rectangularSpectralExpansion U U (f ∘ d) := by
    have hφ : A = φ (diagonal d) := hA
    rw [hφ, ← φ.coe_toAlgEquiv, ← AlgEquiv.map_pfc, Matrix.pfc_diagonal]
    rfl
  have hD : diagonal (f ∘ d) = diagonal b + f 0 • (1 - diagonal c) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ S
      · simp [b, c, hi]
      · have hz : d i = 0 := not_not.mp fun hdi => hi ((hS i).mpr hdi)
        simp [b, c, hi, hz]
    · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, Matrix.smul_apply]
  have hb : rectangularSpectralExpansion U U b =
      rectangularMatrixFunction W W (fun i => d i.val) f := by
    rw [rectangularSpectralExpansion_restrict U b S (fun i hi => by simp [b, hi])]
    apply congrArg (rectangularSpectralExpansion W W)
    funext i
    simp [b, i.property]
  have hc : rectangularSpectralExpansion U U c = W * Wᴴ := by
    rw [rectangularSpectralExpansion_restrict U c S (fun i hi => by simp [c, hi])]
    have he : (fun i : S => c i.val) = fun _ => (1 : ℂ) := funext (fun i => by simp [c, i.property])
    rw [he, rectangularSpectralExpansion_one]
  have h := normal_rectangular_decomposition_of_support hU hA S hS
  change pfc f A = rectangularMatrixFunction W W (fun i => d i.val) f +
    f 0 • Chapter02.orthogonalProjector (toEuclideanLin A).ker
  rw [hp, ← (square_rectangular_support_projectors h).2, ← hb, ← hc]
  unfold rectangularSpectralExpansion
  rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_conjTranspose_self_of_mem_unitaryGroup hU]

end NormalCoordinates

section SupportedPowers

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

private theorem rectangularSpectralExpansion_pow_succ (W : Matrix n k ℂ)
    (hW : Wᴴ * W = 1) (d : k → ℂ) (j : ℕ) :
    rectangularSpectralExpansion W W d ^ (j + 1) =
      rectangularSpectralExpansion W W (fun i => d i ^ (j + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, rectangularSpectralExpansion_mul _ _ _ hW]
    apply congrArg (rectangularSpectralExpansion W W)
    funext i
    rw [← pow_succ]

omit [DecidableEq m] in
/-- **Exercise 85** of [benIsrael2003generalized], Chapter 6, Equation
(174). In eigenvalue coordinates the positive powers are ordinary, the
zeroth power projects onto the range, and the negative powers are
positive powers of the Moore–Penrose inverse. -/
theorem exercise_6_85 {A : Matrix n n ℂ} {W : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A W W d) :
    (∀ j : ℕ, rectangularPower W W d ((j + 1 : ℕ) : ℤ) = A ^ (j + 1)) ∧
    rectangularPower W W d 0 = Chapter02.orthogonalProjector (toEuclideanLin A).range ∧
    (∀ j : ℕ, rectangularPower W W d (-((j + 1 : ℕ) : ℤ)) = A.pinv ^ (j + 1)) := by
  refine ⟨?_, (rectangularPower_zero W W d).trans (square_rectangular_support_projectors h).1, ?_⟩
  · intro j
    rw [h.eq_expansion, rectangularSpectralExpansion_pow_succ W h.left_orthonormal]
    simp only [rectangularPower, rectangularMatrixFunction, zpow_natCast]
  · intro j
    rw [corollary_6_3 h, rectangularSpectralExpansion_pow_succ W h.left_orthonormal]
    simp only [rectangularPower, rectangularMatrixFunction, _root_.zpow_neg, zpow_natCast, inv_pow]

/-- **Exercise 84(b)** of [benIsrael2003generalized], Chapter 6.
Negative exponents on the Gram support are powers of the Gram
pseudoinverses. The odd-power identities remain valid for singular matrices. -/
theorem rectangularPower_odd_negative {A : Matrix m n ℂ} {U : Matrix m k ℂ}
    {V : Matrix n k ℂ} {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d)
    (hd : ∀ i, star (d i) = d i) (j : ℕ) :
    rectangularPower U V d (1 - 2 * (j : ℤ)) = A * (Aᴴ * A).pinv ^ j ∧
    rectangularPower U V d (1 - 2 * (j : ℤ)) = (A * Aᴴ).pinv ^ j * A := by
  let c (i : k) := d i ^ (2 : ℤ)
  have hRight : Aᴴ * A = rectangularSpectralExpansion V V c := by
    rw [h.eq_expansion, rectangularSpectralExpansion_adjoint,
      rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal]
    simp only [c, hd, zpow_ofNat, pow_two]
  have hLeft : A * Aᴴ = rectangularSpectralExpansion U U c := by
    rw [h.eq_expansion, rectangularSpectralExpansion_adjoint,
      rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal]
    simp only [c, hd, zpow_ofNat, pow_two]
  have hcn (i : k) : c i ≠ 0 := zpow_ne_zero _ (h.coeff_ne_zero i)
  have hGR : IsRectangularSpectralDecomposition (Aᴴ * A) V V c :=
    ⟨h.right_orthonormal, h.right_orthonormal, hRight, hcn⟩
  have hGL : IsRectangularSpectralDecomposition (A * Aᴴ) U U c :=
    ⟨h.left_orthonormal, h.left_orthonormal, hLeft, hcn⟩
  have hGInv (i : k) : (c i)⁻¹ = d i ^ (-2 : ℤ) := by
    change (d i ^ (2 : ℤ))⁻¹ = d i ^ (-2 : ℤ)
    rw [_root_.zpow_neg]
  have hStepR (a : ℤ) : rectangularPower U V d (a + (-2)) =
      rectangularPower U V d a * (Aᴴ * A).pinv := by
    rw [corollary_6_3 hGR]
    unfold rectangularPower rectangularMatrixFunction
    rw [rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal]
    apply congrArg (rectangularSpectralExpansion U V)
    funext i
    rw [hGInv, ← zpow_add₀ (h.coeff_ne_zero i)]
  have hStepL (a : ℤ) : rectangularPower U V d (a + (-2)) =
      (A * Aᴴ).pinv * rectangularPower U V d a := by
    rw [corollary_6_3 hGL]
    unfold rectangularPower rectangularMatrixFunction
    rw [rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal]
    apply congrArg (rectangularSpectralExpansion U V)
    funext i
    rw [hGInv, mul_comm, ← zpow_add₀ (h.coeff_ne_zero i)]
  induction j with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, sub_zero, pow_zero, Matrix.mul_one, Matrix.one_mul,
      rectangularPower_one h, and_self]
  | succ j ih =>
    have he : 1 - 2 * ((j + 1 : ℕ) : ℤ) = (1 - 2 * (j : ℤ)) + (-2) := by omega
    exact ⟨by rw [he, hStepR, ih.1, Matrix.mul_assoc, pow_succ],
      by rw [he, hStepL, ih.2, ← Matrix.mul_assoc, pow_succ']⟩

/-- **Exercise 91** of [benIsrael2003generalized], Chapter 6, Equation
(180). The generalized powers are the ordinary positive or supported
negative powers of the normal polar factors, with the shared partial
isometry inserted. The zeroth power is the shared partial isometry. -/
theorem rectangularPower_polar_factors {A : Matrix m n ℂ} {U : Matrix m k ℂ}
    {V : Matrix n k ℂ} {d : k → ℂ} (h : IsRectangularSpectralDecomposition A U V d) :
    let G := rectangularSpectralExpansion U U d
    let H := rectangularSpectralExpansion V V d
    let E := U * Vᴴ
    (∀ j : ℕ, rectangularPower U V d ((j + 1 : ℕ) : ℤ) = G ^ (j + 1) * E ∧
      rectangularPower U V d ((j + 1 : ℕ) : ℤ) = E * H ^ (j + 1)) ∧
    rectangularPower U V d 0 = E ∧
    (∀ j : ℕ, rectangularPower U V d (-((j + 1 : ℕ) : ℤ)) = G.pinv ^ (j + 1) * E ∧
      rectangularPower U V d (-((j + 1 : ℕ) : ℤ)) = E * H.pinv ^ (j + 1)) := by
  let G := rectangularSpectralExpansion U U d
  let H := rectangularSpectralExpansion V V d
  let E := U * Vᴴ
  have hg : IsRectangularSpectralDecomposition G U U d :=
    ⟨h.left_orthonormal, h.left_orthonormal, rfl, h.coeff_ne_zero⟩
  have hh : IsRectangularSpectralDecomposition H V V d :=
    ⟨h.right_orthonormal, h.right_orthonormal, rfl, h.coeff_ne_zero⟩
  have he (t : ℤ) : rectangularPower U V d t = rectangularPower U U d t * E ∧
      rectangularPower U V d t = E * rectangularPower V V d t :=
    rectangularMatrixFunction_polar_factors U V h.left_orthonormal h.right_orthonormal d
      (fun z => z ^ t)
  refine ⟨?_, rectangularPower_zero U V d, ?_⟩
  · intro j
    simpa only [(exercise_6_85 hg).1 j, (exercise_6_85 hh).1 j] using he ((j + 1 : ℕ) : ℤ)
  · intro j
    simpa only [(exercise_6_85 hg).2.2 j, (exercise_6_85 hh).2.2 j] using he (-((j + 1 : ℕ) : ℤ))

end SupportedPowers

section PolynomialInverse

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open Polynomial in
/-- **Exercise 87** of [benIsrael2003generalized], Chapter 6, Equations
(175)–(176). A polynomial annihilator of the specified form determines
the Moore–Penrose inverse of a Hermitian matrix. The identity also
holds for nonmonic q. -/
theorem exercise_6_87 (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (q : Polynomial ℂ) {l : ℕ} {c : ℂ} (hc : c ≠ 0)
    (hAnn : aeval A (C c * X ^ l * (1 - X * q)) = 0) :
    let Q := aeval A q
    A.pinv = Q + q.eval 0 • (A * Q - 1) ∧
      A * Q = A * A.pinv ∧ (IsUnit A → A⁻¹ = Q) := by
  let Q := aeval A q
  let P := A.pinv * A
  have hComm : Commute A.pinv A := by
    change A.pinv * A = A * A.pinv
    apply toEuclideanLin.injective
    rw [A.pinv_mul_eq_starProjection, A.mul_pinv_eq_starProjection, hA.eq]
  have hP : P = A * A.pinv := hComm.eq
  have hp : P * P = P := by
    change (A.pinv * A) * (A.pinv * A) = A.pinv * A
    rw [← Matrix.mul_assoc (A.pinv * A) A.pinv A, A.pinv_mul_self_mul_pinv]
  have hAP : A * P = A := by
    change A * (A.pinv * A) = A
    rw [← Matrix.mul_assoc, A.mul_pinv_mul_self]
  have hPA : P * A = A := by rw [hP, A.mul_pinv_mul_self]
  have hIP : A.pinv * P = A.pinv := by
    rw [hP, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]
  have hPPow (j : ℕ) : P ^ (j + 1) = P := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ih, hp]
  have hIPow (j : ℕ) : A.pinv * P ^ j = A.pinv := by
    cases j with
    | zero => rw [pow_zero, Matrix.mul_one]
    | succ j => rw [hPPow, hIP]
  have hz : c • (A ^ l * (1 - A * Q)) = 0 := by
    simpa only [Q, map_mul, map_pow, map_sub, map_one, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc] using hAnn
  have hAn := (smul_eq_zero.mp hz).resolve_left hc
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, ← Matrix.mul_assoc, ← pow_succ] at hAn
  have hCancel : A.pinv ^ (l + 1) * A ^ l = A.pinv := by
    rw [pow_succ', Matrix.mul_assoc, ← hComm.mul_pow, hIPow]
  have hpq : A.pinv = P * Q := by
    have he := congrArg (A.pinv ^ (l + 1) * ·) hAn
    rw [hCancel, ← Matrix.mul_assoc, ← hComm.mul_pow, hPPow] at he
    exact he
  have hAQ : A * Q = P := by
    rw [hP]
    calc
      A * Q = A * P * Q := by rw [hAP]
      _ = A * A.pinv := by rw [Matrix.mul_assoc, ← hpq]
  have hql : X ∣ q - C (q.eval 0) := by
    rw [X_dvd_iff]
    simp [coeff_zero_eq_eval_zero]
  obtain ⟨p, hq⟩ := hql
  have hEval : Q - q.eval 0 • (1 : Matrix n n ℂ) = A * aeval A p := by
    have he := congrArg (aeval A) hq
    simpa only [Q, map_sub, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one] using he
  have hProj : P * (Q - q.eval 0 • (1 : Matrix n n ℂ)) = Q - q.eval 0 • 1 := by
    rw [hEval, ← Matrix.mul_assoc, hPA]
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at hProj
  refine ⟨?_, hAQ.trans hP, ?_⟩
  · calc
      A.pinv = P * Q := hpq
      _ = (P * Q - q.eval 0 • P) + q.eval 0 • P := by abel
      _ = Q + q.eval 0 • (A * Q - 1) := by rw [hProj, hAQ, smul_sub]; abel
  · intro hu
    have hP₁ : P = 1 := by
      change A.pinv * A = 1
      rw [Matrix.pinv_eq_inv hu, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hu)]
    rw [← Matrix.pinv_eq_inv hu, hpq, hP₁, Matrix.one_mul]

open Polynomial in
/-- **Exercise 88** of [benIsrael2003generalized], Chapter 6, Equation
(177). A factorized annihilator of the column Gram matrix expresses
the rectangular Moore–Penrose inverse as a Gram polynomial times
the adjoint. -/
theorem exercise_6_88 (A : Matrix m n ℂ) (q : Polynomial ℂ)
    {l : ℕ} {c : ℂ} (hc : c ≠ 0)
    (hAnn : aeval (Aᴴ * A) (C c * X ^ l * (1 - X * q)) = 0) :
    A.pinv = aeval (Aᴴ * A) q * Aᴴ := by
  let G := Aᴴ * A
  let Q := aeval G q
  obtain ⟨hG, hGQ, -⟩ := exercise_6_87 G (isHermitian_conjTranspose_mul_self A) q hc hAnn
  change G.pinv = Q + q.eval 0 • (G * Q - 1) at hG
  change G * Q = G * G.pinv at hGQ
  have hA : A.pinv = G.pinv * Aᴴ := (Chapter01.pinv_gram A).1
  have hP : G * G.pinv * Aᴴ = Aᴴ := by
    rw [Matrix.mul_assoc, ← hA]
    change (Aᴴ * A) * A.pinv = Aᴴ
    rw [Matrix.mul_assoc, A.conjTranspose_mul_mul_pinv]
  change A.pinv = Q * Aᴴ
  rw [hA, hG, Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul,
    hGQ, hP, sub_self, smul_zero, add_zero]

end PolynomialInverse

section SpectralExponential

private theorem rectangularSpectralExpansion_partialIsometry_of_norm_one
    {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] {U : Matrix m k ℂ} {V : Matrix n k ℂ}
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) {d : k → ℂ} (hd : ∀ i, ‖d i‖ = 1) :
    IsPartialIsometry (rectangularSpectralExpansion U V d) := by
  apply (isPartialIsometry_iff_adjoint_eq_pinv _).mpr
  rw [rectangularSpectralExpansion_adjoint, rectangularSpectralExpansion_pinv U V hU hV]
  apply congrArg (rectangularSpectralExpansion V U)
  funext i
  have hn : d i ≠ 0 := norm_ne_zero_iff.mp (by rw [hd]; norm_num)
  apply (mul_eq_one_iff_eq_inv₀ hn).mp
  rw [mul_comm]
  change d i * (starRingEnd ℂ) (d i) = 1
  rw [Complex.mul_conj', hd]
  norm_num

/-- **Exercise 89** of [benIsrael2003generalized], Chapter 6.
A rectangular matrix is a partial isometry precisely when it is the
supported imaginary exponential of a rectangular decomposition with
real coefficients. -/
theorem exercise_6_89 {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℂ) :
    IsPartialIsometry W ↔
      ∃ (A : Matrix (Fin m) (Fin n) ℂ)
        (U : Matrix (Fin m) (Fin W.rank) ℂ) (V : Matrix (Fin n) (Fin W.rank) ℂ)
        (θ : Fin W.rank → ℝ),
      IsRectangularSpectralDecomposition A U V (fun i => (θ i : ℂ)) ∧
        W = rectangularMatrixFunction U V (fun i => (θ i : ℂ))
          (fun z => Complex.exp (Complex.I * z)) := by
  constructor
  · intro hW
    obtain ⟨U, V, h⟩ := theorem_6_18 W (fun _ => 1) (fun i => by
      rw [(exercise_6_41 W).mp hW i i.isLt, norm_one])
    let t : ℝ := 2 * Real.pi
    let θ : Fin W.rank → ℝ := fun _ => t
    have ht : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by dsimp [t]; positivity)
    refine ⟨(t : ℂ) • W, U, V, θ,
      ⟨h.left_orthonormal, h.right_orthonormal, ?_, fun _ => ht⟩, ?_⟩
    · have he := congrArg (fun M : Matrix (Fin m) (Fin n) ℂ => (t : ℂ) • M) h.eq_expansion
      exact he.trans (by rw [rectangularSpectralExpansion_smul]; simp only [θ, mul_one])
    · refine h.eq_expansion.trans ?_
      unfold rectangularMatrixFunction
      apply congrArg (rectangularSpectralExpansion U V)
      funext i
      change 1 = Complex.exp (Complex.I * (t : ℂ))
      rw [mul_comm, show (t : ℂ) = 2 * (Real.pi : ℂ) from by simp [t],
        Complex.exp_two_pi_mul_I]
  · rintro ⟨A, U, V, θ, h, he⟩
    have hp := rectangularSpectralExpansion_partialIsometry_of_norm_one
      h.left_orthonormal h.right_orthonormal (fun i => Complex.norm_exp_I_mul_ofReal (θ i))
    exact (congrArg IsPartialIsometry he).mpr hp

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectral_diagonalization_eq {A U : Matrix n n ℂ} {d : n → ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (h : Uᴴ * A * U = diagonal d) :
    A = U * diagonal d * Uᴴ := by
  have hu := mul_conjTranspose_self_of_mem_unitaryGroup hU
  calc
    _ = (U * Uᴴ) * A * (U * Uᴴ) := by rw [hu, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * A * U) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

private theorem diagonal_mem_unitaryGroup_iff_norm_one (d : n → ℂ) :
    diagonal d ∈ unitaryGroup n ℂ ↔ ∀ i, ‖d i‖ = 1 := by
  rw [mem_unitaryGroup_iff]
  change diagonal d * (diagonal d)ᴴ = 1 ↔ _
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one, diagonal_injective.eq_iff]
  rw [funext_iff]
  apply forall_congr'
  intro i
  change d i * (starRingEnd ℂ) (d i) = 1 ↔ _
  rw [Complex.mul_conj']
  constructor
  · intro h
    have h' : ‖d i‖ ^ 2 = 1 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (h'.trans (one_pow 2).symm)
  · intro h
    simp [h]

private theorem exp_I_smul_eq_rectangularSpectralExpansion {A U : Matrix n n ℂ}
    {d : n → ℂ} (hU : U ∈ unitaryGroup n ℂ) (hA : A = U * diagonal d * Uᴴ) :
    NormedSpace.exp (Complex.I • A) =
      rectangularSpectralExpansion U U (fun i => Complex.exp (Complex.I * d i)) := by
  have hUnit : IsUnit U :=
    (isUnit_iff_isUnit_det U).mpr (isUnit_det_of_mem_unitaryGroup hU)
  have hInv : U⁻¹ = Uᴴ := inv_eq_right_inv (mul_conjTranspose_self_of_mem_unitaryGroup hU)
  rw [hA, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hInv, Matrix.exp_conj _ _ hUnit,
    ← diagonal_smul, Matrix.exp_diagonal]
  simp only [rectangularSpectralExpansion, hInv]
  apply congrArg (fun z : n → ℂ => U * diagonal z * Uᴴ)
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rfl

/-- **Exercise 90** of [benIsrael2003generalized], Chapter 6, Equation
(178′). A complex square matrix is unitary precisely when it is the
classical imaginary exponential of a Hermitian matrix. -/
theorem exercise_6_90 (A : Matrix n n ℂ) :
    A ∈ unitaryGroup n ℂ ↔
      ∃ H : Matrix n n ℂ, H.IsHermitian ∧ A = NormedSpace.exp (Complex.I • H) := by
  constructor
  · intro hA
    have hN : IsStarNormal A :=
      ⟨(conjTranspose_mul_self_of_mem_unitaryGroup hA).trans
        (mul_conjTranspose_self_of_mem_unitaryGroup hA).symm⟩
    obtain ⟨U, hU, d, hD⟩ := Matrix.IsStarNormal.spectral_theorem.mp hN
    have he := spectral_diagonalization_eq hU hD
    have hdu : diagonal d ∈ unitaryGroup n ℂ := by
      rw [← hD]
      exact mul_mem (mul_mem (conjTranspose_mem_unitaryGroup hU) hA) hU
    have hphase (i : n) : Complex.exp (Complex.I * (Complex.arg (d i) : ℂ)) = d i := by
      have h := Complex.norm_mul_exp_arg_mul_I (d i)
      rw [(diagonal_mem_unitaryGroup_iff_norm_one d).mp hdu i, Complex.ofReal_one, one_mul] at h
      exact (congrArg Complex.exp (mul_comm _ _)).trans h
    let θ : n → ℂ := fun i => (Complex.arg (d i) : ℂ)
    let H := U * diagonal θ * Uᴴ
    have hHerm : (diagonal θ).IsHermitian := by
      apply isHermitian_diagonal_iff.mpr
      intro i
      change (starRingEnd ℂ) (Complex.arg (d i) : ℂ) = (Complex.arg (d i) : ℂ)
      simp
    refine ⟨H, isHermitian_mul_mul_conjTranspose U hHerm, ?_⟩
    rw [exp_I_smul_eq_rectangularSpectralExpansion hU (show H = U * diagonal θ * Uᴴ from rfl),
      show (fun i => Complex.exp (Complex.I * θ i)) = d from funext hphase]
    exact he
  · rintro ⟨H, hH, rfl⟩
    let U : Matrix n n ℂ := ↑hH.eigenvectorUnitary
    let θ : n → ℂ := fun i => (hH.eigenvalues i : ℂ)
    have hU : U ∈ unitaryGroup n ℂ := hH.eigenvectorUnitary.property
    have he : H = U * diagonal θ * Uᴴ := by
      exact hH.spectral_theorem
    rw [exp_I_smul_eq_rectangularSpectralExpansion hU he]
    exact mul_mem (mul_mem hU ((diagonal_mem_unitaryGroup_iff_norm_one _).mpr
      (fun i => Complex.norm_exp_I_mul_ofReal _))) (conjTranspose_mem_unitaryGroup hU)

/-- **Exercise 90** of [benIsrael2003generalized], Chapter 6, Equation
(178). The supported imaginary exponential becomes the classical
one after adding the orthogonal projector onto the kernel. -/
theorem exercise_6_90_supported {H U : Matrix n n ℂ} {d : n → ℂ}
    (hU : U ∈ unitaryGroup n ℂ) (hH : H = U * diagonal d * Uᴴ)
    (S : Finset n) (hS : ∀ i, i ∈ S ↔ d i ≠ 0) :
    let W := U.submatrix id (fun i : S => i.val)
    NormedSpace.exp (Complex.I • H) =
      rectangularMatrixFunction W W (fun i => d i.val) (fun z => Complex.exp (Complex.I * z)) +
        Chapter02.orthogonalProjector (toEuclideanLin H).ker := by
  let f (z : ℂ) := Complex.exp (Complex.I * z)
  let u : unitary (Matrix n n ℂ) := ⟨U, hU⟩
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u
  have hp : pfc f H = rectangularSpectralExpansion U U (f ∘ d) := by
    have hφ : H = φ (diagonal d) := hH
    rw [hφ, ← φ.coe_toAlgEquiv, ← AlgEquiv.map_pfc, Matrix.pfc_diagonal]
    rfl
  have he := exercise_6_82 hU hH S hS f
  rw [hp] at he
  rw [exp_I_smul_eq_rectangularSpectralExpansion hU hH]
  simpa only [f, Function.comp_def, mul_zero, Complex.exp_zero, one_smul] using he

end SpectralExponential

section SimpleComponents

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
  [DecidableEq n] [DecidableEq k] [DecidableEq l]

private theorem rectangular_gram_coeff (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]
  change z * (starRingEnd ℂ) z = _
  rw [Complex.mul_conj', Complex.ofReal_pow]

private theorem mul_aeval_gram_eq_rectangularSpectralExpansion
    {A : Matrix m n ℂ} {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d) (p : Polynomial ℂ) :
    A * Polynomial.aeval (Aᴴ * A) p =
      rectangularSpectralExpansion U V (fun i => d i * p.eval ((‖d i‖ ^ 2 : ℝ) : ℂ)) := by
  let c (i : k) : ℂ := ((‖d i‖ ^ 2 : ℝ) : ℂ)
  have hg : Aᴴ * A = rectangularSpectralExpansion V V c := by
    rw [h.eq_expansion, rectangularSpectralExpansion_adjoint,
      rectangularSpectralExpansion_mul _ _ _ h.left_orthonormal]
    exact congrArg (rectangularSpectralExpansion V V) (funext fun i => rectangular_gram_coeff (d i))
  have hPow (j : ℕ) :
      A * (Aᴴ * A) ^ j = rectangularSpectralExpansion U V (fun i => d i * c i ^ j) := by
    induction j with
    | zero => simpa only [pow_zero, Matrix.mul_one, mul_one] using h.eq_expansion
    | succ j ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, hg,
        rectangularSpectralExpansion_mul _ _ _ h.right_orthonormal]
      apply congrArg (rectangularSpectralExpansion U V)
      funext i
      rw [pow_succ, mul_assoc]
  let L : (k → ℂ) →ₗ[ℂ] Matrix m n ℂ :=
    { toFun := rectangularSpectralExpansion U V
      map_add' := fun a b => by
        change rectangularSpectralExpansion U V (a + b) =
          rectangularSpectralExpansion U V a + rectangularSpectralExpansion U V b
        simp only [rectangularSpectralExpansion, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
        rfl
      map_smul' := fun a b => (rectangularSpectralExpansion_smul U V a b).symm }
  rw [Polynomial.aeval_eq_sum_range, Matrix.mul_sum]
  simp only [Matrix.mul_smul, hPow]
  change (∑ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j • L (fun i => d i * c i ^ j)) = L (fun i => d i * p.eval (c i))
  simp_rw [← map_smul]
  rw [← map_sum]
  apply congrArg L
  funext i
  rw [Finset.sum_apply, Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change p.coeff j * (d i * c i ^ j) = d i * (p.coeff j * c i ^ j)
  ring

/-- **Theorem 18** of [benIsrael2003generalized], Chapter 6, uniqueness
at a simple singular value. The rank-one term normalized by the
coefficient's phase is independent of the chosen singular vectors. -/
theorem rectangular_simple_singular_component_unique
    {A : Matrix m n ℂ} {U : Matrix m k ℂ} {V : Matrix n k ℂ} {d : k → ℂ}
    {U' : Matrix m l ℂ} {V' : Matrix n l ℂ} {d' : l → ℂ}
    (h : IsRectangularSpectralDecomposition A U V d)
    (h' : IsRectangularSpectralDecomposition A U' V' d')
    (i : k) (j : l) (hSame : ‖d i‖ = ‖d' j‖)
    (hi : ∀ a, ‖d a‖ = ‖d i‖ → a = i)
    (hj : ∀ b, ‖d' b‖ = ‖d' j‖ → b = j) :
    (d i / (‖d i‖ : ℂ)) • rectangularSpectralComponent U V i =
      (d' j / (‖d' j‖ : ℂ)) • rectangularSpectralComponent U' V' j := by
  classical
  let c (a : k) : ℂ := ((‖d a‖ ^ 2 : ℝ) : ℂ)
  let c' (b : l) : ℂ := ((‖d' b‖ ^ 2 : ℝ) : ℂ)
  let S := (Finset.univ.image c) ∪ (Finset.univ.image c')
  let s := ‖d i‖
  let δ : ℂ := c i
  let r (z : ℂ) : ℂ := if z = δ then (s : ℂ)⁻¹ else 0
  let q := Lagrange.interpolate S id r
  have hq (z : ℂ) (hz : z ∈ S) : q.eval z = r z :=
    Lagrange.eval_interpolate_at_node (v := id) (r := r) (fun _ _ _ _ hh => hh) hz
  have hc (a : k) : c a = δ ↔ a = i := by
    constructor
    · intro he
      apply hi
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (Complex.ofReal_injective he)
    · rintro rfl; rfl
  have hc' (b : l) : c' b = δ ↔ b = j := by
    have heq : c' j = δ := by dsimp [c', δ, c]; rw [hSame]
    rw [← heq]
    constructor
    · intro he
      apply hj
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (Complex.ofReal_injective he)
    · rintro rfl; rfl
  have he₁ : A * Polynomial.aeval (Aᴴ * A) q =
      (d i / (s : ℂ)) • rectangularSpectralComponent U V i := by
    rw [mul_aeval_gram_eq_rectangularSpectralExpansion h, rectangularSpectralComponent,
      rectangularSpectralExpansion_smul]
    apply congrArg (rectangularSpectralExpansion U V)
    funext a
    change d a * q.eval (c a) = (d i / (s : ℂ)) * (if a = i then 1 else 0)
    rw [hq _ (Finset.mem_union_left _ (Finset.mem_image_of_mem c (Finset.mem_univ a)))]
    by_cases ha : a = i
    · subst a
      simp [r, δ, div_eq_mul_inv]
    · simp [r, ha, mt (hc a).mp ha]
  have he₂ : A * Polynomial.aeval (Aᴴ * A) q =
      (d' j / (s : ℂ)) • rectangularSpectralComponent U' V' j := by
    rw [mul_aeval_gram_eq_rectangularSpectralExpansion h', rectangularSpectralComponent,
      rectangularSpectralExpansion_smul]
    apply congrArg (rectangularSpectralExpansion U' V')
    funext b
    change d' b * q.eval (c' b) = (d' j / (s : ℂ)) * (if b = j then 1 else 0)
    rw [hq _ (Finset.mem_union_right _ (Finset.mem_image_of_mem c' (Finset.mem_univ b)))]
    by_cases hb : b = j
    · subst b
      simp [r, (hc' j).mpr rfl, div_eq_mul_inv]
    · simp [r, hb, mt (hc' b).mp hb]
  have hh := he₁.symm.trans he₂
  change (d i / (‖d i‖ : ℂ)) • _ = (d' j / (‖d i‖ : ℂ)) • _ at hh
  simpa only [hSame] using hh

end SimpleComponents

end BenIsraelGreville.Chapter06
