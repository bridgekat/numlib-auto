/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter06.Section04
import Mathlib.Analysis.Complex.CauchyIntegral

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

end BenIsraelGreville.Chapter06
