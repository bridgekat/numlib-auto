/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter03.Section02
import NumlibSurface.BenIsraelGreville.Chapter01.Section05
import NumlibSurface.BenIsraelGreville.Chapter02.Section06
import NumlibSurface.BenIsraelGreville.Chapter02.Section07
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Mathlib.Analysis.Matrix.Order

/-!
# Weighted generalized inverses

Section 3.4 of [benIsrael2003generalized] uses positive definite weights
on residual and solution spaces. Invertible Gram factors reduce the
weighted variational problems and the weighted Penrose equations to
their Euclidean counterparts.

In Exercise 35 the quadratic expression gives the squared minimum
norm.
In Exercise 42 the prescribed kernel is the inverse image under the
weight of the perpendicular complement of the range, as in the
source's derivation of Equation (72).
-/

namespace BenIsraelGreville.Chapter03

open Matrix
open scoped ComplexOrder InnerProductSpace MatrixOrder
open BenIsraelGreville.Chapter01 (definition_1 mem_one_three_iff mem_one_four_iff)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Equations (49)–(50) of [benIsrael2003generalized]. For a positive
definite weight this is the norm induced by its Hermitian form. -/
noncomputable def weightedNorm (W : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℝ :=
  Real.sqrt (RCLike.re (inner ℂ x (toEuclideanLin W x)))

/-- A Gram factor converts the weighted norm to the Euclidean norm. -/
theorem weightedNorm_gram (R : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    weightedNorm (Rᴴ * R) x = ‖toEuclideanLin R x‖ := by
  rw [weightedNorm, toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_right,
    ← norm_sq_eq_re_inner, Real.sqrt_sq_eq_abs, abs_norm]

/-- The weighted least-squares property minimizes the residual in the
codomain weight. -/
def IsWeightedLeastSquaresSolution (W : Matrix m m ℂ) (A : Matrix m n ℂ)
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) : Prop :=
  ∀ y, weightedNorm W (toEuclideanLin A x - b) ≤ weightedNorm W (toEuclideanLin A y - b)

/-- The weighted minimum-norm solution minimizes the domain weight
among exact solutions. -/
def IsWeightedMinNormSolution (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) : Prop :=
  toEuclideanLin A x = b ∧ ∀ y, toEuclideanLin A y = b → weightedNorm Q x ≤ weightedNorm Q y

/-- The weighted minimum-norm least-squares solution minimizes the
domain weight among the least-squares solutions in the codomain weight. -/
def IsWeightedMinNormLeastSquaresSolution (W : Matrix m m ℂ) (Q : Matrix n n ℂ)
    (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) : Prop :=
  IsWeightedLeastSquaresSolution W A b x ∧
    ∀ y, IsWeightedLeastSquaresSolution W A b y → weightedNorm Q x ≤ weightedNorm Q y

private theorem isUnit_sqrt (W : Matrix n n ℂ) (hW : W.PosDef) :
    IsUnit (CFC.sqrt W) := by
  have h : (CFC.sqrt W) * (CFC.sqrt W) = W := by
    rw [← sq, CFC.sq_sqrt W hW.posSemidef.nonneg]
  apply (Matrix.isUnit_iff_isUnit_det _).2
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 hW.isUnit
  rw [← h, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

set_option linter.unusedDecidableInType false in
-- The matrix functional calculus in this statement uses the same matrix instances as its callers.
private theorem sqrt_gram (W : Matrix n n ℂ) (hW : W.PosDef) :
    (CFC.sqrt W)ᴴ * CFC.sqrt W = W := by
  rw [(CFC.sqrt_nonneg W).posSemidef.isHermitian.eq, ← sq, CFC.sq_sqrt W hW.posSemidef.nonneg]

omit [Fintype n] [DecidableEq n] in
private theorem factor_left_eq_iff (R : Matrix m m ℂ) (hR : IsUnit R)
    (B C : Matrix m n ℂ) : R * B = R * C ↔ B = C := by
  constructor
  · intro h
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 hR
    simpa only [nonsing_inv_mul_cancel_left R _ hd] using congrArg (fun D => R⁻¹ * D) h
  · exact fun h => congrArg (R * ·) h

omit [Fintype m] [DecidableEq m] in
private theorem factor_right_eq_iff (S : Matrix n n ℂ) (hS : IsUnit S)
    (B C : Matrix m n ℂ) : B * S = C * S ↔ B = C := by
  constructor
  · intro h
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 hS
    simpa only [mul_nonsing_inv_cancel_right S _ hd] using congrArg (fun D => D * S⁻¹) h
  · exact fun h => congrArg (· * S) h

private theorem isHermitian_congruence_iff (R : Matrix n n ℂ) (hR : IsUnit R)
    (B : Matrix n n ℂ) : IsHermitian (Rᴴ * B * R) ↔ IsHermitian B := by
  change (Rᴴ * B * R)ᴴ = Rᴴ * B * R ↔ Bᴴ = B
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    ← Matrix.mul_assoc, factor_right_eq_iff R hR,
    factor_left_eq_iff Rᴴ (by simpa only [← star_eq_conjTranspose] using hR.star)]

private theorem isHermitian_weighted_iff (R : Matrix n n ℂ) (hR : IsUnit R)
    (B : Matrix n n ℂ) :
    IsHermitian ((Rᴴ * R) * B) ↔ IsHermitian (R * B * R⁻¹) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hR
  have h : Rᴴ * (R * B * R⁻¹) * R = (Rᴴ * R) * B := by
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.mul_one]
  conv_rhs => rw [← isHermitian_congruence_iff R hR, h]

private theorem coordinate_inner_eq_iff (A : Matrix m n ℂ) (X : Matrix n m ℂ)
    (R : Matrix m m ℂ) (S : Matrix n n ℂ) (hR : IsUnit R) (hS : IsUnit S) :
    let B := R * A * S⁻¹
    let Y := S * X * R⁻¹
    B * Y * B = B ↔ A * X * A = A := by
  intro B Y
  have hr := (Matrix.isUnit_iff_isUnit_det _).1 hR
  have hs := (Matrix.isUnit_iff_isUnit_det _).1 hS
  have h : B * Y * B = R * (A * X * A) * S⁻¹ := by
    dsimp only [B, Y]
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hr,
      nonsing_inv_mul_cancel_left _ _ hs]
  rw [h]
  exact (factor_right_eq_iff S⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hS) _ _).trans
    (factor_left_eq_iff R hR _ _)

private theorem coordinate_products (A : Matrix m n ℂ) (X : Matrix n m ℂ)
    (R : Matrix m m ℂ) (S : Matrix n n ℂ) (hR : IsUnit R) (hS : IsUnit S) :
    let B := R * A * S⁻¹
    let Y := S * X * R⁻¹
    B * Y = R * (A * X) * R⁻¹ ∧ Y * B = S * (X * A) * S⁻¹ := by
  intro B Y
  have hr := (Matrix.isUnit_iff_isUnit_det _).1 hR
  have hs := (Matrix.isUnit_iff_isUnit_det _).1 hS
  constructor <;> dsimp only [B, Y] <;>
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hr,
      nonsing_inv_mul_cancel_left _ _ hs]

/-- Equations (52)–(53). The weighted residual and solution norm become
Euclidean norms under invertible Gram factors. -/
theorem weighted_coordinates (A : Matrix m n ℂ) (R : Matrix m m ℂ) (S : Matrix n n ℂ)
    (hS : IsUnit S) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    weightedNorm (Rᴴ * R) (toEuclideanLin A x - b) =
      ‖toEuclideanLin (R * A * S⁻¹) (toEuclideanLin S x) - toEuclideanLin R b‖ ∧
    weightedNorm (Sᴴ * S) x = ‖toEuclideanLin S x‖ := by
  refine ⟨?_, weightedNorm_gram S x⟩
  rw [weightedNorm_gram, map_sub, toEuclideanLin_mul_apply,
    toEuclideanLin_nonsing_inv_mul_apply hS, toEuclideanLin_mul_apply]

private theorem coordinates_apply (A : Matrix m n ℂ) (R : Matrix m m ℂ) (S : Matrix n n ℂ)
    (hS : IsUnit S) (x : EuclideanSpace ℂ n) :
    toEuclideanLin (R * A * S⁻¹) (toEuclideanLin S x) =
      toEuclideanLin R (toEuclideanLin A x) := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_nonsing_inv_mul_apply hS, toEuclideanLin_mul_apply]

private theorem weighted_lsq_coordinates_iff (W : Matrix m m ℂ) (A : Matrix m n ℂ)
    (R : Matrix m m ℂ) (S : Matrix n n ℂ) (hR : Rᴴ * R = W) (hS : IsUnit S)
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    IsWeightedLeastSquaresSolution W A b x ↔
      IsLeastSquaresSolution (R * A * S⁻¹) (toEuclideanLin R b) (toEuclideanLin S x) := by
  subst W
  have hs : Function.Surjective (toEuclideanLin S) :=
    Function.RightInverse.surjective (toEuclideanLin_mul_nonsing_inv_apply hS)
  constructor
  · intro h y
    obtain ⟨z, rfl⟩ := hs y
    simpa only [← (weighted_coordinates A R S hS b _).1] using h z
  · intro h y
    simpa only [← (weighted_coordinates A R S hS b _).1] using h (toEuclideanLin S y)

private theorem weighted_minNorm_coordinates_iff (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (R : Matrix m m ℂ) (S : Matrix n n ℂ) (hR : IsUnit R) (hS : IsUnit S)
    (hQ : Sᴴ * S = Q) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    IsWeightedMinNormSolution Q A b x ↔
      IsMinNormSolution (R * A * S⁻¹) (toEuclideanLin R b) (toEuclideanLin S x) := by
  subst Q
  have hr : Function.Injective (toEuclideanLin R) :=
    Function.LeftInverse.injective (toEuclideanLin_nonsing_inv_mul_apply hR)
  have hs : Function.Surjective (toEuclideanLin S) :=
    Function.RightInverse.surjective (toEuclideanLin_mul_nonsing_inv_apply hS)
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨by rw [coordinates_apply A R S hS, hx], ?_⟩
    intro y hy
    obtain ⟨z, rfl⟩ := hs y
    rw [coordinates_apply A R S hS] at hy
    simpa only [weightedNorm_gram] using h z (hr hy)
  · rintro ⟨hx, h⟩
    rw [coordinates_apply A R S hS] at hx
    refine ⟨hr hx, fun y hy => ?_⟩
    simpa only [weightedNorm_gram] using
      h (toEuclideanLin S y) (by rw [coordinates_apply A R S hS, hy])

/-- The weighted minimum-norm least-squares property is equivalent to
the Euclidean property in the Gram-factor coordinates. -/
theorem weighted_minNormLeastSquares_coordinates_iff
    (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (R : Matrix m m ℂ) (S : Matrix n n ℂ) (hW : Rᴴ * R = W)
    (hQ : Sᴴ * S = Q) (hS : IsUnit S) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    IsWeightedMinNormLeastSquaresSolution W Q A b x ↔
      IsMinNormLeastSquaresSolution (R * A * S⁻¹) (toEuclideanLin R b) (toEuclideanLin S x) := by
  subst Q
  have hs : Function.Surjective (toEuclideanLin S) :=
    Function.RightInverse.surjective (toEuclideanLin_mul_nonsing_inv_apply hS)
  have hL z := weighted_lsq_coordinates_iff W A R S hW hS b z
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨(hL x).mp hx, ?_⟩
    intro y hy
    obtain ⟨z, rfl⟩ := hs y
    simpa only [weightedNorm_gram] using h z ((hL z).mpr hy)
  · rintro ⟨hx, h⟩
    exact ⟨(hL x).mpr hx, fun y hy => by
      simpa only [weightedNorm_gram] using h (toEuclideanLin S y) ((hL y).mp hy)⟩

private theorem inverse_coordinates_apply (X : Matrix n m ℂ) (R : Matrix m m ℂ)
    (S : Matrix n n ℂ) (hR : IsUnit R) (b : EuclideanSpace ℂ m) :
    toEuclideanLin (S * X * R⁻¹) (toEuclideanLin R b) =
      toEuclideanLin S (toEuclideanLin X b) :=
  coordinates_apply X S R hR b

/-- **Theorem 4** of [benIsrael2003generalized]. A matrix consistently
produces weighted least-squares solutions exactly when it satisfies the
inner equation and the weighted first Hermitian equation. -/
theorem theorem_4 (A : Matrix m n ℂ) (X : Matrix n m ℂ) (W : Matrix m m ℂ)
    (hW : W.PosDef) :
    A * X * A = A ∧ IsHermitian (W * (A * X)) ↔
      ∀ b, IsWeightedLeastSquaresSolution W A b (toEuclideanLin X b) := by
  let R := CFC.sqrt W
  let S : Matrix n n ℂ := 1
  let B := R * A * S⁻¹
  let Y := S * X * R⁻¹
  have hR : IsUnit R := isUnit_sqrt W hW
  have hS : IsUnit S := isUnit_one
  have hG : Rᴴ * R = W := sqrt_gram W hW
  have hI := coordinate_inner_eq_iff A X R S hR hS
  have hP := (coordinate_products A X R S hR hS).1
  change B * Y = R * (A * X) * R⁻¹ at hP
  have hH : IsHermitian (W * (A * X)) ↔ IsHermitian (B * Y) := by
    rw [hP, ← hG]
    exact isHermitian_weighted_iff R hR _
  calc
    _ ↔ Y ∈ definition_1 B {.inner, .hermitianMul} := by
        rw [mem_one_three_iff]
        exact and_congr hI.symm hH
    _ ↔ ∀ b, leastSquaresSolution B b (toEuclideanLin Y b) := theorem_1 B Y
    _ ↔ _ := by
      have hs : Function.Surjective (toEuclideanLin R) :=
        Function.RightInverse.surjective (toEuclideanLin_mul_nonsing_inv_apply hR)
      constructor
      · intro h b
        apply (weighted_lsq_coordinates_iff W A R S hG hS b _).mpr
        rw [← inverse_coordinates_apply X R S hR b]
        exact h (toEuclideanLin R b)
      · intro h b
        obtain ⟨a, rfl⟩ := hs b
        change leastSquaresSolution B (toEuclideanLin R a)
          (toEuclideanLin (S * X * R⁻¹) (toEuclideanLin R a))
        rw [inverse_coordinates_apply X R S hR a]
        exact (weighted_lsq_coordinates_iff W A R S hG hS a _).mp (h a)

/-- **Theorem 5** of [benIsrael2003generalized]. On consistent right-hand
sides the inner equation and the weighted second Hermitian equation
characterize the matrix producing the weighted minimum-norm solution. -/
theorem theorem_5 (A : Matrix m n ℂ) (X : Matrix n m ℂ) (Q : Matrix n n ℂ)
    (hQ : Q.PosDef) :
    A * X * A = A ∧ IsHermitian (Q * (X * A)) ↔
      ∀ b ∈ LinearMap.range (toEuclideanLin A),
        IsWeightedMinNormSolution Q A b (toEuclideanLin X b) := by
  let R : Matrix m m ℂ := 1
  let S := CFC.sqrt Q
  let B := R * A * S⁻¹
  let Y := S * X * R⁻¹
  have hR : IsUnit R := isUnit_one
  have hS : IsUnit S := isUnit_sqrt Q hQ
  have hG : Sᴴ * S = Q := sqrt_gram Q hQ
  have hI := coordinate_inner_eq_iff A X R S hR hS
  have hP := (coordinate_products A X R S hR hS).2
  change Y * B = S * (X * A) * S⁻¹ at hP
  have hH : IsHermitian (Q * (X * A)) ↔ IsHermitian (Y * B) := by
    rw [hP, ← hG]
    exact isHermitian_weighted_iff S hS _
  calc
    _ ↔ Y ∈ definition_1 B {.inner, .hermitianMulRev} := by
        rw [mem_one_four_iff]
        exact and_congr hI.symm hH
    _ ↔ ∀ b ∈ LinearMap.range (toEuclideanLin B), IsMinNormSolution B b (toEuclideanLin Y b) :=
      theorem_2 B Y
    _ ↔ _ := by
      constructor
      · intro h b hb
        apply (weighted_minNorm_coordinates_iff Q A R S hR hS hG b _).mpr
        rw [← inverse_coordinates_apply X R S hR b]
        obtain ⟨a, ha⟩ := hb
        exact h _ ⟨toEuclideanLin S a, (coordinates_apply A R S hS a).trans
          (congrArg (toEuclideanLin R) ha)⟩
      · intro h b hb
        obtain ⟨y, rfl⟩ := hb
        have hs := Function.RightInverse.surjective (toEuclideanLin_mul_nonsing_inv_apply hS)
        obtain ⟨x, rfl⟩ := hs y
        let b := toEuclideanLin A x
        change IsMinNormSolution B (toEuclideanLin B (toEuclideanLin S x))
          (toEuclideanLin Y (toEuclideanLin B (toEuclideanLin S x)))
        rw [coordinates_apply A R S hS, inverse_coordinates_apply X R S hR]
        exact (weighted_minNorm_coordinates_iff Q A R S hR hS hG b _).mp (h b ⟨x, rfl⟩)

/-- The four weighted Penrose equations in **Corollary 4**. -/
def IsWeightedReflexiveInverse (W : Matrix m m ℂ) (Q : Matrix n n ℂ)
    (A : Matrix m n ℂ) (X : Matrix n m ℂ) : Prop :=
  A * X * A = A ∧ X * A * X = X ∧
    IsHermitian (W * (A * X)) ∧ IsHermitian (Q * (X * A))

/-- The Gram-factor formula of **Exercise 37**, Equation (68b). -/
noncomputable def weightedInverseFromFactors (A : Matrix m n ℂ)
    (R : Matrix m m ℂ) (S : Matrix n n ℂ) : Matrix n m ℂ :=
  S⁻¹ * (R * A * S⁻¹).pinv * R

/-- The weighted reflexive inverse of **Corollary 4**, in its
square-root form **(68a)**. -/
noncomputable def weightedInverse (W : Matrix m m ℂ) (Q : Matrix n n ℂ)
    (A : Matrix m n ℂ) : Matrix n m ℂ :=
  weightedInverseFromFactors A (CFC.sqrt W) (CFC.sqrt Q)

private theorem weightedInverseFromFactors_forward (A : Matrix m n ℂ)
    (R : Matrix m m ℂ) (S : Matrix n n ℂ) (hR : IsUnit R) (hS : IsUnit S) :
    S * weightedInverseFromFactors A R S * R⁻¹ = (R * A * S⁻¹).pinv := by
  have hr := (Matrix.isUnit_iff_isUnit_det _).1 hR
  have hs := (Matrix.isUnit_iff_isUnit_det _).1 hS
  simp only [weightedInverseFromFactors, Matrix.mul_assoc, mul_nonsing_inv _ hr, Matrix.mul_one,
    mul_nonsing_inv_cancel_left _ _ hs]

/-- Under invertible Gram factors the weighted equations become the
ordinary Penrose equations. This includes both directions of Equations
(56)–(58). -/
theorem weightedInverse_coordinates_iff (A : Matrix m n ℂ) (X : Matrix n m ℂ)
    (R : Matrix m m ℂ) (S : Matrix n n ℂ) (hR : IsUnit R) (hS : IsUnit S) :
    let B := R * A * S⁻¹
    let Y := S * X * R⁻¹
    IsWeightedReflexiveInverse (Rᴴ * R) (Sᴴ * S) A X ↔
      B * Y * B = B ∧ Y * B * Y = Y ∧ IsHermitian (B * Y) ∧ IsHermitian (Y * B) := by
  intro B Y
  obtain ⟨hBY, hYB⟩ := coordinate_products A X R S hR hS
  change B * Y = _ at hBY
  change Y * B = _ at hYB
  unfold IsWeightedReflexiveInverse
  have h₃ : IsHermitian (Rᴴ * R * (A * X)) ↔ IsHermitian (B * Y) := by
    rw [hBY]
    exact isHermitian_weighted_iff R hR _
  have h₄ : IsHermitian (Sᴴ * S * (X * A)) ↔ IsHermitian (Y * B) := by
    rw [hYB]
    exact isHermitian_weighted_iff S hS _
  exact and_congr (coordinate_inner_eq_iff A X R S hR hS).symm
    (and_congr (coordinate_inner_eq_iff X A S R hS hR).symm (and_congr h₃ h₄))

/-- For any invertible Gram factors the weighted equations have the
same unique solution, given by Equation (68b). -/
theorem isWeightedReflexiveInverse_iff_eq_fromFactors
    (A : Matrix m n ℂ) (X : Matrix n m ℂ) (R : Matrix m m ℂ) (S : Matrix n n ℂ)
    (hR : IsUnit R) (hS : IsUnit S) :
    IsWeightedReflexiveInverse (Rᴴ * R) (Sᴴ * S) A X ↔ X = weightedInverseFromFactors A R S := by
  let B := R * A * S⁻¹
  let Y := S * X * R⁻¹
  have ht := weightedInverse_coordinates_iff A X R S hR hS
  change IsWeightedReflexiveInverse (Rᴴ * R) (Sᴴ * S) A X ↔
    B * Y * B = B ∧ Y * B * Y = Y ∧ IsHermitian (B * Y) ∧ IsHermitian (Y * B) at ht
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ht.mp h
    have he : Y = B.pinv := pinv_unique (A := B) (B := Y) h₁ h₂ h₃ h₄
    have hforward := weightedInverseFromFactors_forward A R S hR hS
    apply (factor_left_eq_iff S hS _ _).mp
    apply (factor_right_eq_iff R⁻¹ (isUnit_nonsing_inv_iff.mpr hR) _ _).mp
    exact he.trans hforward.symm
  · rintro rfl
    apply (weightedInverse_coordinates_iff A (weightedInverseFromFactors A R S) R S hR hS).mpr
    rw [weightedInverseFromFactors_forward A R S hR hS]
    exact ⟨B.mul_pinv_mul_self, B.pinv_mul_self_mul_pinv,
      B.isHermitian_mul_pinv, B.isHermitian_pinv_mul⟩

/-- The weighted equations uniquely characterize the square-root formula. -/
theorem isWeightedReflexiveInverse_iff_eq
    (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ) (X : Matrix n m ℂ)
    (hW : W.PosDef) (hQ : Q.PosDef) :
    IsWeightedReflexiveInverse W Q A X ↔ X = weightedInverse W Q A := by
  simpa only [sqrt_gram W hW, sqrt_gram Q hQ, weightedInverse] using
    isWeightedReflexiveInverse_iff_eq_fromFactors A X (CFC.sqrt W) (CFC.sqrt Q)
      (isUnit_sqrt W hW) (isUnit_sqrt Q hQ)

/-- A vector minimizes the weighted solution norm among weighted
least-squares solutions exactly when it is the image of the datum
under the weighted reflexive inverse. -/
theorem isWeightedMinNormLeastSquaresSolution_iff
    (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hW : W.PosDef) (hQ : Q.PosDef) (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    IsWeightedMinNormLeastSquaresSolution W Q A b x ↔
      x = toEuclideanLin (weightedInverse W Q A) b := by
  let R := CFC.sqrt W
  let S := CFC.sqrt Q
  let B := R * A * S⁻¹
  let Y := weightedInverse W Q A
  have hR : IsUnit R := isUnit_sqrt W hW
  have hS : IsUnit S := isUnit_sqrt Q hQ
  have ht := weighted_minNormLeastSquares_coordinates_iff W Q A R S
    (sqrt_gram W hW) (sqrt_gram Q hQ) hS b x
  have hcoord :
      toEuclideanLin S (toEuclideanLin Y b) = toEuclideanLin B.pinv (toEuclideanLin R b) := by
    rw [← inverse_coordinates_apply Y R S hR b]
    change toEuclideanLin (S * weightedInverseFromFactors A R S * R⁻¹) (toEuclideanLin R b) = _
    rw [weightedInverseFromFactors_forward A R S hR hS]
  constructor
  · intro h
    apply Function.LeftInverse.injective (toEuclideanLin_nonsing_inv_mul_apply hS)
    rw [show weightedInverse W Q A = Y from rfl, hcoord]
    exact (ht.mp h).eq_pinv
  · intro h
    apply ht.mpr
    rw [h, show weightedInverse W Q A = Y from rfl, hcoord]
    exact isMinNormLeastSquaresSolution_pinv B (toEuclideanLin R b)

/-- **Corollary 4** of [benIsrael2003generalized]. The weighted
equations and the weighted minimum-norm least-squares property both
characterize the same unique matrix. -/
theorem corollary_4 (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hW : W.PosDef) (hQ : Q.PosDef) (X : Matrix n m ℂ) :
    (IsWeightedReflexiveInverse W Q A X ↔ X = weightedInverse W Q A) ∧
      ((∀ b, IsWeightedMinNormLeastSquaresSolution W Q A b (toEuclideanLin X b)) ↔
        X = weightedInverse W Q A) := by
  refine ⟨isWeightedReflexiveInverse_iff_eq W Q A X hW hQ, ?_⟩
  simp only [isWeightedMinNormLeastSquaresSolution_iff W Q A hW hQ]
  exact ⟨fun h => toEuclideanLin.injective (LinearMap.ext h), fun h b => by rw [h]⟩

/-- **Exercises 32 and 37** of [benIsrael2003generalized]. The
square-root result agrees with the formula using arbitrary invertible
Gram factors, including the Cholesky factors. -/
theorem exercise_3_37 (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hW : W.PosDef) (hQ : Q.PosDef) (R : Matrix m m ℂ) (S : Matrix n n ℂ)
    (hR : IsUnit R) (hS : IsUnit S) (hRW : Rᴴ * R = W) (hSQ : Sᴴ * S = Q) :
    weightedInverse W Q A = weightedInverseFromFactors A R S := by
  apply (isWeightedReflexiveInverse_iff_eq_fromFactors A _ R S hR hS).mp
  rw [hRW, hSQ]
  exact (isWeightedReflexiveInverse_iff_eq W Q A _ hW hQ).mpr rfl

/-- The positive definite square root is the unique positive definite
matrix whose square is the original matrix. -/
theorem existsUnique_posDef_sq_eq (W : Matrix n n ℂ) (hW : W.PosDef) :
    ∃! R : Matrix n n ℂ, R.PosDef ∧ R ^ 2 = W := by
  refine ⟨CFC.sqrt W, ⟨(CFC.sqrt_nonneg W).posSemidef.posDef_iff_isUnit.mpr (isUnit_sqrt W hW),
    CFC.sq_sqrt W hW.posSemidef.nonneg⟩, ?_⟩
  intro R hR
  symm
  exact (CFC.sqrt_eq_iff W R hW.posSemidef.nonneg hR.1.posSemidef.nonneg).mpr
    (by simpa only [pow_two] using hR.2)

/-- **Exercise 31** of [benIsrael2003generalized]. The positive square
root applies the scalar square root to the Hermitian eigenvalues. -/
theorem exercise_3_31 (W : Matrix n n ℂ) (hW : W.PosDef) :
    let U := (hW.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
    CFC.sqrt W =
      U * diagonal (fun i => (Real.sqrt (hW.isHermitian.eigenvalues i) : ℂ)) * Uᴴ := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ W, hW.isHermitian.cfc_eq]
  simp only [IsHermitian.cfc, Real.coe_sqrt, Real.coe_toNNReal',
    Unitary.conjStarAlgAut_apply, ← star_eq_conjTranspose]
  congr 1
  apply congrArg (fun D : Matrix n n ℂ => _ * D)
  apply congrArg diagonal
  funext i
  simp only [Function.comp_apply, max_eq_left (hW.eigenvalues_pos i).le]
  rfl

private theorem isUnit_of_posDef_gram (R W : Matrix n n ℂ) (hW : W.PosDef)
    (hR : Rᴴ * R = W) : IsUnit R := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 hW.isUnit
  rw [← hR, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- **Exercise 32** of [benIsrael2003generalized]. The upper
triangular Cholesky factors give the weighted inverse formula. -/
theorem exercise_3_32 [LinearOrder m] [LinearOrder n] (W : Matrix m m ℂ)
    (Q : Matrix n n ℂ) (A : Matrix m n ℂ) (hW : W.PosDef) (hQ : Q.PosDef) :
    ∃ (R : Matrix m m ℂ) (S : Matrix n n ℂ), IsCholesky W R ∧ IsCholesky Q S ∧
      weightedInverse W Q A = weightedInverseFromFactors A R S := by
  obtain ⟨R, hR⟩ := exists_isCholesky hW
  obtain ⟨S, hS⟩ := exists_isCholesky hQ
  have hRW : Rᴴ * R = W := hR.conjTranspose_mul_self
  have hSQ : Sᴴ * S = Q := hS.conjTranspose_mul_self
  exact ⟨R, S, hR, hS, exercise_3_37 W Q A hW hQ R S
    (isUnit_of_posDef_gram R W hW hRW) (isUnit_of_posDef_gram S Q hQ hSQ) hRW hSQ⟩

/-- **Exercise 33** of [benIsrael2003generalized]. Weighted least
squares is equivalent to the weighted normal equations. -/
theorem exercise_3_33 (W : Matrix m m ℂ) (A : Matrix m n ℂ) (hW : W.PosDef)
    (b : EuclideanSpace ℂ m) (x : EuclideanSpace ℂ n) :
    IsWeightedLeastSquaresSolution W A b x ↔
      toEuclideanLin (Aᴴ * W * A) x = toEuclideanLin (Aᴴ * W) b := by
  let R := CFC.sqrt W
  have hG : Rᴴ * R = W := sqrt_gram W hW
  have h := weighted_lsq_coordinates_iff W A R (1 : Matrix n n ℂ) hG isUnit_one b x
  simp only [inv_one, Matrix.mul_one, toEuclideanLin_one_apply] at h
  rw [h, isLeastSquaresSolution_iff_normalEquations]
  have h₁ : (R * A)ᴴ * (R * A) = Aᴴ * W * A := by
    rw [conjTranspose_mul, ← hG]
    simp only [Matrix.mul_assoc]
  have h₂ : (R * A)ᴴ * R = Aᴴ * W := by
    rw [conjTranspose_mul, ← hG, Matrix.mul_assoc]
  rw [h₁, ← toEuclideanLin_mul_apply, h₂]

/-- **Exercise 34** of [benIsrael2003generalized]. A feasible weighted
least-squares minimizer is exactly the solution component of the
displayed saddle system. -/
theorem exercise_3_34 {k : Type*} [Fintype k] [DecidableEq k]
    (W : Matrix m m ℂ) (A : Matrix m n ℂ) (B : Matrix k n ℂ) (hW : W.PosDef)
    (b : EuclideanSpace ℂ m) (d : EuclideanSpace ℂ k) (x : EuclideanSpace ℂ n) :
    (toEuclideanLin B x = d ∧ ∀ y, toEuclideanLin B y = d →
        weightedNorm W (toEuclideanLin A x - b) ≤ weightedNorm W (toEuclideanLin A y - b)) ↔
      toEuclideanLin B x = d ∧ ∃ z : EuclideanSpace ℂ k,
        toEuclideanLin (Aᴴ * W * A) x + toEuclideanLin Bᴴ z = toEuclideanLin (Aᴴ * W) b := by
  apply and_congr_right
  intro hx
  let K := (toEuclideanLin B).ker
  let P := Chapter02.orthogonalProjector K
  let b' := b - toEuclideanLin A x
  have hp : toEuclideanLin P = K.starProjection.toLinearMap :=
    Chapter02.toEuclideanLin_orthogonalProjector K
  have hshift (u : EuclideanSpace ℂ n) :
      toEuclideanLin (A * P) u - b' = toEuclideanLin A (x + toEuclideanLin P u) - b := by
    rw [toEuclideanLin_mul_apply, map_add]
    dsimp only [b']
    abel
  have heq : (∀ y, toEuclideanLin B y = d →
      weightedNorm W (toEuclideanLin A x - b) ≤ weightedNorm W (toEuclideanLin A y - b)) ↔
      IsWeightedLeastSquaresSolution W (A * P) b' 0 := by
    have hstart : toEuclideanLin (A * P) 0 - b' = toEuclideanLin A x - b := by
      rw [hshift, map_zero, add_zero]
    constructor
    · intro h u
      rw [hstart, hshift]
      apply h
      have hnull : toEuclideanLin B (toEuclideanLin P u) = 0 := by
        rw [hp]
        exact K.starProjection_apply_mem u
      rw [map_add, hx, hnull, add_zero]
    · intro h y hy
      have hmem : y - x ∈ K := by
        change toEuclideanLin B (y - x) = 0
        rw [map_sub, hy, hx, sub_self]
      have hf : toEuclideanLin P (y - x) = y - x := by
        rw [hp]
        exact K.starProjection_eq_self_iff.mpr hmem
      have hh := h (y - x)
      rw [hstart, hshift, hf] at hh
      rw [show x + (y - x) = y by abel] at hh
      exact hh
  rw [heq, exercise_3_33 W (A * P) hW, map_zero, eq_comm (a := (0 : EuclideanSpace ℂ n))]
  have hM : (A * P)ᴴ * W = P * (Aᴴ * W) := by
    rw [conjTranspose_mul, (Chapter02.isHermitian_orthogonalProjector K).eq, Matrix.mul_assoc]
  rw [hM, toEuclideanLin_mul_apply, hp]
  change K.starProjection (toEuclideanLin (Aᴴ * W) b') = 0 ↔ _
  rw [K.starProjection_apply_eq_zero_iff]
  have hK : Kᗮ = LinearMap.range (toEuclideanLin Bᴴ) := by
    rw [toEuclideanLin_conjTranspose_eq_adjoint]
    exact (toEuclideanLin B).orthogonal_ker
  rw [hK]
  change (∃ z, toEuclideanLin Bᴴ z = toEuclideanLin (Aᴴ * W) b') ↔ _
  simp only [b', map_sub, ← toEuclideanLin_mul_apply, eq_sub_iff_add_eq, add_comm]

/-- **Exercise 35** of [benIsrael2003generalized]. Any inner inverse
of the weighted row Gram matrix produces the same minimum-norm
solution and gives its squared norm. -/
theorem exercise_3_35 (Q : Matrix n n ℂ) (A : Matrix m n ℂ) (hQ : Q.PosDef)
    {b : EuclideanSpace ℂ m} (hb : b ∈ LinearMap.range (toEuclideanLin A))
    (U : Matrix m m ℂ) (hU : (A * Q⁻¹ * Aᴴ).IsInnerInverse U) :
    let x := toEuclideanLin (Q⁻¹ * Aᴴ * U) b
    (∀ y, IsWeightedMinNormSolution Q A b y ↔ y = x) ∧
      weightedNorm Q x ^ 2 = RCLike.re (inner ℂ b (toEuclideanLin U b)) := by
  intro x
  let S := CFC.sqrt Q
  let B := A * S⁻¹
  have hs : IsUnit S := isUnit_sqrt Q hQ
  have hg : Sᴴ * S = Q := sqrt_gram Q hQ
  have hS : Sᴴ = S := (CFC.sqrt_nonneg Q).posSemidef.isHermitian.eq
  have hi : Q⁻¹ = S⁻¹ * S⁻¹ := by rw [← hg, hS, Matrix.mul_inv_rev]
  have hB : B * Bᴴ = A * Q⁻¹ * Aᴴ := by
    dsimp only [B]
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, hS, hi]
    simp only [Matrix.mul_assoc]
  have hU' : U ∈ definition_1 (B * Bᴴ) {.inner} := by
    rw [BenIsraelGreville.Chapter01.mem_one_iff, hB]
    exact hU
  have hM : Bᴴ * U ∈ definition_1 B {.inner, .hermitianMulRev} := by
    have h := Chapter01.theorem_3_b B hU'
    rw [mem_penroseInverses_iff] at h ⊢
    exact fun c hc => h c (by
      rcases hc with rfl | rfl <;> simp)
  have hB' : S⁻¹ * (Bᴴ * U) = Q⁻¹ * Aᴴ * U := by
    dsimp only [B]
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, hS, hi]
    simp only [Matrix.mul_assoc]
  have hx : toEuclideanLin S x = toEuclideanLin (Bᴴ * U) b := by
    change toEuclideanLin S (toEuclideanLin (Q⁻¹ * Aᴴ * U) b) = _
    rw [← hB', toEuclideanLin_mul_apply, toEuclideanLin_mul_nonsing_inv_apply hs]
  have hX (y : EuclideanSpace ℂ n) :
      IsWeightedMinNormSolution Q A b y ↔ IsMinNormSolution B b (toEuclideanLin S y) := by
    simpa only [Matrix.one_mul, toEuclideanLin_one_apply, B] using
      weighted_minNorm_coordinates_iff Q A 1 S isUnit_one hs hg b y
  have hb' : b ∈ LinearMap.range (toEuclideanLin B) := by
    obtain ⟨v, hv⟩ := hb
    refine ⟨toEuclideanLin S v, ?_⟩
    rwa [toEuclideanLin_mul_apply, toEuclideanLin_nonsing_inv_mul_apply hs]
  have hmin : IsWeightedMinNormSolution Q A b x := by
    apply (hX x).mpr
    rw [hx]
    exact (theorem_2 B (Bᴴ * U)).mp hM b hb'
  refine ⟨fun y => ?_, ?_⟩
  · constructor
    · intro hy
      obtain ⟨z, _, _, _, huniq⟩ := corollary_2 hb'
      exact Function.LeftInverse.injective (toEuclideanLin_nonsing_inv_mul_apply hs)
        ((huniq _ ((hX y).mp hy)).trans (huniq _ ((hX x).mp hmin)).symm)
    · rintro rfl
      exact hmin
  have hQx : toEuclideanLin Q x = toEuclideanLin Aᴴ (toEuclideanLin U b) := by
    change toEuclideanLin Q (toEuclideanLin (Q⁻¹ * Aᴴ * U) b) = _
    rw [← toEuclideanLin_mul_apply, Matrix.mul_assoc Q⁻¹, mul_nonsing_inv_cancel_left _ _
      ((Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit), toEuclideanLin_mul_apply]
  calc
    weightedNorm Q x ^ 2 = ‖toEuclideanLin S x‖ ^ 2 := by rw [← hg, weightedNorm_gram]
    _ = RCLike.re (inner ℂ x (toEuclideanLin Q x)) := by
      rw [← hg, toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_right,
        ← norm_sq_eq_re_inner]
    _ = _ := by
      rw [hQx, toEuclideanLin_conjTranspose_inner_right, hmin.1]

/-- **Exercise 36** of [benIsrael2003generalized]. The alternative
second Hermitian condition uses the inverse of the domain weight. -/
theorem exercise_3_36 (Q : Matrix n n ℂ) (B : Matrix n n ℂ) (hQ : Q.PosDef) :
    IsHermitian (Q * B) ↔ IsHermitian (B * Q⁻¹) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit
  have h : Qᴴ * (B * Q⁻¹) * Q = Q * B := by
    simp only [hQ.isHermitian.eq, Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.mul_one]
  simpa only [h] using isHermitian_congruence_iff Q hQ.isUnit (B * Q⁻¹)

/-- **Exercise 38** of [benIsrael2003generalized]. A single inner
inverse of the Gram matrix of the normal equations gives the weighted
reflexive inverse. -/
theorem exercise_3_38 (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hW : W.PosDef) (hQ : Q.PosDef) (U : Matrix n n ℂ)
    (hU : (Aᴴ * W * A * Q⁻¹ * (Aᴴ * W * A)).IsInnerInverse U) :
    weightedInverse W Q A = Q⁻¹ * (Aᴴ * W * A) * U * (Aᴴ * W) := by
  let N := Aᴴ * W * A
  have hN : N.IsHermitian := isHermitian_conjTranspose_mul_mul A hW.isHermitian
  have hU' : (N * Q⁻¹ * Nᴴ).IsInnerInverse U := by
    rw [hN.eq]
    exact hU
  apply toEuclideanLin.injective
  ext b : 1
  let x := toEuclideanLin (weightedInverse W Q A) b
  have hx := (isWeightedMinNormLeastSquaresSolution_iff W Q A hW hQ b x).mpr rfl
  have hnorm := (exercise_3_33 W A hW b x).mp hx.1
  have hmin : IsWeightedMinNormSolution Q N (toEuclideanLin (Aᴴ * W) b) x :=
    ⟨hnorm, fun y hy => hx.2 y ((exercise_3_33 W A hW b y).mpr hy)⟩
  have he := (exercise_3_35 Q N hQ ⟨x, hnorm⟩ U hU').1 x
  rw [hN.eq] at he
  rw [toEuclideanLin_mul_apply]
  exact he.mp hmin

/-- **Exercise 39** of [benIsrael2003generalized]. Two positive
definite Hermitian forms give a positive definite weight for which
the idempotent is self-adjoint. -/
theorem exercise_3_39 (E H K : Matrix n n ℂ) (hE : E * E = E)
    (hH : H.PosDef) (hK : K.PosDef) :
    let V := Eᴴ * H * E + (1 - E)ᴴ * K * (1 - E)
    V.PosDef ∧ IsHermitian (V * E) := by
  intro V
  have h₁ := isHermitian_conjTranspose_mul_mul E hH.isHermitian
  have h₂ := isHermitian_conjTranspose_mul_mul (1 - E) hK.isHermitian
  constructor
  · refine PosDef.of_dotProduct_mulVec_pos (h₁.add h₂) fun x hx => ?_
    change 0 < star x ⬝ᵥ (V *ᵥ x)
    have hform (P L : Matrix n n ℂ) :
        star x ⬝ᵥ ((Pᴴ * L * P) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (L *ᵥ (P *ᵥ x)) := by
      simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
    change 0 < star x ⬝ᵥ
      ((Eᴴ * H * E + (1 - E)ᴴ * K * (1 - E)) *ᵥ x)
    rw [add_mulVec, dotProduct_add, hform, hform]
    by_cases he : E *ᵥ x = 0
    · have hx' : (1 - E) *ᵥ x ≠ 0 := by
        rwa [sub_mulVec, one_mulVec, he, sub_zero]
      exact add_pos_of_nonneg_of_pos (hH.posSemidef.dotProduct_mulVec_nonneg _)
        (hK.dotProduct_mulVec_pos hx')
    · exact add_pos_of_pos_of_nonneg (hH.dotProduct_mulVec_pos he)
        (hK.posSemidef.dotProduct_mulVec_nonneg _)
  · have hVE : V * E = Eᴴ * H * E := by
      dsimp only [V]
      rw [Matrix.add_mul, Matrix.mul_assoc _ E E, hE, Matrix.mul_assoc _ (1 - E) E,
        Matrix.sub_mul, Matrix.one_mul, hE, sub_self, Matrix.mul_zero, add_zero]
    rw [hVE]
    exact h₁

/-- **Exercise 40** of [benIsrael2003generalized]. The displayed
two-dimensional family arises from the two scalar weights. -/
theorem exercise_3_40 (a b : ℝ) (ha : 0 < a) (hb : a < b) :
    let E : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 0]
    let V : Matrix (Fin 2) (Fin 2) ℂ := !![a, a; a, b]
    V.PosDef ∧ (V * E).IsHermitian ∧
      V = (a : ℂ) • (Eᴴ * E) + (((b - a) / 2 : ℝ) : ℂ) • ((1 - E)ᴴ * (1 - E)) := by
  intro E V
  let H : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun _ => (a : ℂ)
  let K : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun _ => (((b - a) / 2 : ℝ) : ℂ)
  have hE : E * E = E := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E, Matrix.mul_apply, Fin.sum_univ_two]
  have hH : H.PosDef := posDef_diagonal_iff.mpr (fun _ => by exact_mod_cast ha)
  have hK : K.PosDef := posDef_diagonal_iff.mpr
    (fun _ => by exact_mod_cast half_pos (sub_pos.mpr hb))
  have hV : V = Eᴴ * H * E + (1 - E)ᴴ * K * (1 - E) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E, V, H, K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        Matrix.conjTranspose_apply]
  obtain ⟨h₁, h₂⟩ := exercise_3_39 E H K hE hH hK
  refine ⟨hV.symm ▸ h₁, hV.symm ▸ h₂, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, V, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.conjTranspose_apply]
  ring

/-- **Exercise 41** of [benIsrael2003generalized]. Every reflexive
inverse is the weighted inverse for some positive definite weights. -/
theorem exercise_3_41 (A : Matrix m n ℂ) (X : Matrix n m ℂ)
    (h₁ : A * X * A = A) (h₂ : X * A * X = X) :
    ∃ (W : Matrix m m ℂ) (Q : Matrix n n ℂ), W.PosDef ∧ Q.PosDef ∧
      X = weightedInverse W Q A := by
  have hAX : (A * X) * (A * X) = A * X := by rw [← Matrix.mul_assoc, h₁]
  have hXA : (X * A) * (X * A) = X * A := by rw [← Matrix.mul_assoc, h₂]
  obtain ⟨hW, hW'⟩ := exercise_3_39 (A * X) 1 1 hAX PosDef.one PosDef.one
  obtain ⟨hQ, hQ'⟩ := exercise_3_39 (X * A) 1 1 hXA PosDef.one PosDef.one
  refine ⟨_, _, hW, hQ, ?_⟩
  exact (isWeightedReflexiveInverse_iff_eq _ _ A X hW hQ).mp ⟨h₁, h₂, hW', hQ'⟩

/-- **Exercise 42**, Equations (71)–(72) of [benIsrael2003generalized].
Pulling the two Euclidean perpendicular complements back along the
weight maps gives the weighted inverse's range and kernel. -/
theorem exercise_3_42 (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hW : W.PosDef) (hQ : Q.PosDef) :
    let X := weightedInverse W Q A
    (toEuclideanLin X).range = (toEuclideanLin A).kerᗮ.comap (toEuclideanLin Q) ∧
      (toEuclideanLin X).ker = (toEuclideanLin A).rangeᗮ.comap (toEuclideanLin W) := by
  intro X
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (isWeightedReflexiveInverse_iff_eq W Q A X hW hQ).mpr rfl
  have hQX : (toEuclideanLin (Q * X)).range = (toEuclideanLin A).kerᗮ := by
    have hprod : Q * X * A = (X * A)ᴴ * Q := by
      have hh := h₄.symm
      rw [conjTranspose_mul, hQ.isHermitian.eq, ← Matrix.mul_assoc] at hh
      exact hh
    have hrange : (toEuclideanLin (Q * X)).range = (toEuclideanLin (Q * X * A)).range := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨toEuclideanLin X y, ?_⟩
        rw [← toEuclideanLin_mul_apply,
          show Q * X * A * X = Q * (X * A * X) by simp only [Matrix.mul_assoc], h₂]
      · rintro ⟨y, rfl⟩
        exact ⟨toEuclideanLin A y, toEuclideanLin_mul_apply (Q * X) A y |>.symm⟩
    have hker : (toEuclideanLin (X * A)).ker = (toEuclideanLin A).ker := by
      ext x
      simp only [LinearMap.mem_ker, toEuclideanLin_mul_apply]
      constructor
      · intro hx
        have h := congrArg (toEuclideanLin A) hx
        rw [map_zero, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, h₁] at h
        exact h
      · intro hx
        rw [hx, map_zero]
    have hs := Function.RightInverse.surjective
      (toEuclideanLin_mul_nonsing_inv_apply hQ.isUnit)
    rw [hrange, hprod, ← hker, LinearMap.orthogonal_ker,
      ← toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin_mul,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)]
  constructor
  · ext x
    change x ∈ (toEuclideanLin X).range ↔ toEuclideanLin Q x ∈ (toEuclideanLin A).kerᗮ
    rw [← hQX]
    have hi := Function.LeftInverse.injective (toEuclideanLin_nonsing_inv_mul_apply hQ.isUnit)
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, toEuclideanLin_mul_apply Q X y⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hi (by rwa [toEuclideanLin_mul_apply] at hy)⟩
  · have hAX : (toEuclideanLin (A * X)).range = (toEuclideanLin A).range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨toEuclideanLin X x, toEuclideanLin_mul_apply A X x |>.symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨toEuclideanLin A x, by rw [← toEuclideanLin_mul_apply, h₁]⟩
    have hp : (A * X)ᴴ * W = W * (A * X) := by
      simpa only [conjTranspose_mul, hW.isHermitian.eq] using h₃.eq
    have hi := Function.LeftInverse.injective (toEuclideanLin_nonsing_inv_mul_apply hW.isUnit)
    ext y
    change toEuclideanLin X y = 0 ↔ toEuclideanLin W y ∈ (toEuclideanLin A).rangeᗮ
    rw [← hAX, LinearMap.orthogonal_range, ← toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.mem_ker, ← toEuclideanLin_mul_apply, hp, toEuclideanLin_mul_apply,
      ← (toEuclideanLin W).map_zero, hi.eq_iff, toEuclideanLin_mul_apply]
    constructor
    · intro hy
      rw [hy, map_zero]
    · intro hy
      have h := congrArg (toEuclideanLin X) hy
      rw [map_zero, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, h₂] at h
      exact h

/-- Equations (73)–(74) describe all positive definite weights making
an idempotent self-adjoint. -/
theorem exercise_3_42_weight_family (E V : Matrix n n ℂ) (hE : E * E = E) :
    V.PosDef ∧ (V * E).IsHermitian ↔
      ∃ H K : Matrix n n ℂ, H.PosDef ∧ K.PosDef ∧
        V = Eᴴ * H * E + (1 - E)ᴴ * K * (1 - E) := by
  constructor
  · rintro ⟨hV, hVE⟩
    refine ⟨V, V, hV, hV, ?_⟩
    have h₁ : Eᴴ * V = V * E := by
      simpa only [conjTranspose_mul, hV.isHermitian.eq] using hVE.eq
    have h₂ : (1 - E)ᴴ * V = V * (1 - E) := by
      rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.one_mul, h₁,
        Matrix.mul_sub, Matrix.mul_one]
    have h₃ : (1 - E) * (1 - E) = 1 - E := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hE, sub_self, sub_zero]
    rw [h₁, h₂, Matrix.mul_assoc V E E, Matrix.mul_assoc V (1 - E), hE, h₃,
      ← Matrix.mul_add, add_comm E, sub_add_cancel, Matrix.mul_one]
  · rintro ⟨H, K, hH, hK, rfl⟩
    exact exercise_3_39 E H K hE hH hK

/-- The weighted inverse in **Exercise 42** is the prescribed
reflexive inverse from Theorem 2.12(c). The two oblique projectors
give the decompositions of both weights in (73)–(74). -/
theorem exercise_3_42_prescribed (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hW : W.PosDef) (hQ : Q.PosDef) :
    let X := weightedInverse W Q A
    let T := X.mulVecLin.range
    let S := X.mulVecLin.ker
    ∃ (hT : IsCompl T A.mulVecLin.ker) (hS : IsCompl A.mulVecLin.range S),
      let P := Chapter02.projectorMatrix hT
      let R := Chapter02.projectorMatrix hS
      X = P * A.pinv * R ∧
      (∃ Q₁ Q₂ : Matrix n n ℂ, Q₁.PosDef ∧ Q₂.PosDef ∧
        Q = (1 - P)ᴴ * Q₁ * (1 - P) + Pᴴ * Q₂ * P) ∧
      (∃ W₁ W₂ : Matrix m m ℂ, W₁.PosDef ∧ W₂.PosDef ∧
        W = Rᴴ * W₁ * R + (1 - R)ᴴ * W₂ * (1 - R)) := by
  intro X T S
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (isWeightedReflexiveInverse_iff_eq W Q A X hW hQ).mpr rfl
  have hAX : (A * X) * (A * X) = A * X := by rw [← Matrix.mul_assoc, h₁]
  have hXA : (X * A) * (X * A) = X * A := by rw [← Matrix.mul_assoc, h₂]
  have hI : A.IsInnerInverse X := isInnerInverse_iff.mpr h₁
  have hO : X.IsInnerInverse A := isInnerInverse_iff.mpr h₂
  have hP : IsIdempotentElem (X * A).mulVecLin := by
    change (X * A).mulVecLin.comp (X * A).mulVecLin = (X * A).mulVecLin
    rw [← mulVecLin_mul, hXA]
  have hR : IsIdempotentElem (A * X).mulVecLin := by
    change (A * X).mulVecLin.comp (A * X).mulVecLin = (A * X).mulVecLin
    rw [← mulVecLin_mul, hAX]
  have hT : IsCompl T A.mulVecLin.ker := by
    have h := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hP).isCompl
    rwa [hO.range_mul, hI.ker_mul_rev] at h
  have hS : IsCompl A.mulVecLin.range S := by
    have h := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hR).isCompl
    rwa [hI.range_mul, hO.ker_mul_rev] at h
  refine ⟨hT, hS, ?_⟩
  have h := Chapter02.theorem_12 A hS hT A.pinv A.mul_pinv_mul_self
  obtain ⟨hR', hP'⟩ := (h.1 X).mp ⟨hI, hO.ker_mul_rev, hO.range_mul⟩
  have hX := h.2.2.2 X (Chapter01.mem_one_two_iff.mpr ⟨hI, h₂⟩) rfl rfl
  refine ⟨hX, ?_, ?_⟩
  · obtain ⟨H, K, hH, hK, he⟩ := (exercise_3_42_weight_family (X * A) Q hXA).mp ⟨hQ, h₄⟩
    exact ⟨K, H, hK, hH, by rw [← hP', add_comm]; exact he⟩
  · obtain ⟨H, K, hH, hK, he⟩ := (exercise_3_42_weight_family (A * X) W hAX).mp ⟨hW, h₃⟩
    exact ⟨H, K, hH, hK, by rwa [← hR']⟩

/-- **Exercise 43** of [benIsrael2003generalized]. The weighted
reflexive inverse has an ordinary inverse formula on rank factors. -/
theorem exercise_3_43 {k : Type*} [Fintype k] [DecidableEq k]
    (W : Matrix m m ℂ) (Q : Matrix n n ℂ) (A : Matrix m n ℂ)
    (F : Matrix m k ℂ) (G : Matrix k n ℂ) (hW : W.PosDef) (hQ : Q.PosDef)
    (hA : A = F * G) (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) :
    IsUnit (Fᴴ * W * A * Q⁻¹ * Gᴴ) ∧
      weightedInverse W Q A = Q⁻¹ * Gᴴ * (Fᴴ * W * A * Q⁻¹ * Gᴴ)⁻¹ * Fᴴ * W := by
  let R := Fᴴ * W * F
  let S := G * Q⁻¹ * Gᴴ
  let U := Q⁻¹ * Gᴴ
  let V := Fᴴ * W
  let X := U * (R * S)⁻¹ * V
  have hR : R.PosDef := hW.conjTranspose_mul_mul_same
    (mulVec_injective_iff_rank_eq_card.mpr hF)
  have hS : S.PosDef := by
    have h := hQ.inv.conjTranspose_mul_mul_same (B := Gᴴ)
      (mulVec_injective_iff_rank_eq_card.mpr (G.rank_conjTranspose.trans hG))
    simpa only [S, conjTranspose_conjTranspose] using h
  have hMid : Fᴴ * W * A * Q⁻¹ * Gᴴ = R * S := by
    rw [hA]
    simp only [R, S, Matrix.mul_assoc]
  have hMid' : V * A * U = R * S := by
    simpa only [Matrix.mul_assoc, V, U] using hMid
  have hr := (isUnit_iff_isUnit_det _).mp hR.isUnit
  have hs := (isUnit_iff_isUnit_det _).mp hS.isUnit
  have hq := (isUnit_iff_isUnit_det _).mp hQ.isUnit
  have hAX : A * X = F * R⁻¹ * V := calc
    A * X = F * (S * S⁻¹) * R⁻¹ * V := by
      dsimp only [X]
      rw [hA, Matrix.mul_inv_rev]
      simp only [U, S, Matrix.mul_assoc]
    _ = _ := by rw [mul_nonsing_inv _ hs, Matrix.mul_one]
  have hXA : X * A = U * S⁻¹ * G := calc
    X * A = U * S⁻¹ * (R⁻¹ * R) * G := by
      dsimp only [X]
      rw [hA, Matrix.mul_inv_rev]
      simp only [V, R, Matrix.mul_assoc]
    _ = _ := by rw [nonsing_inv_mul _ hr, Matrix.mul_one]
  have h₁ : A * X * A = A := calc
    A * X * A = F * (R⁻¹ * R) * G := by
      rw [hAX, hA]
      simp only [R, V, Matrix.mul_assoc]
    _ = A := by rw [nonsing_inv_mul _ hr, Matrix.mul_one, ← hA]
  have h₂ : X * A * X = X := calc
    X * A * X = U * ((R * S)⁻¹ * (V * A * U)) * (R * S)⁻¹ * V := by
      simp only [X, Matrix.mul_assoc]
    _ = X := by
      rw [hMid', nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (hR.isUnit.mul hS.isUnit)),
        Matrix.mul_one]
  have h₃ : IsHermitian (W * (A * X)) := by
    have hV : Vᴴ = W * F := by rw [conjTranspose_mul, hW.isHermitian.eq,
      conjTranspose_conjTranspose]
    rw [hAX, show W * (F * R⁻¹ * V) = Vᴴ * R⁻¹ * V by
      rw [hV]; simp only [Matrix.mul_assoc]]
    exact isHermitian_conjTranspose_mul_mul V hR.inv.isHermitian
  have h₄ : IsHermitian (Q * (X * A)) := by
    rw [hXA]
    have h : Q * (U * S⁻¹ * G) = Gᴴ * S⁻¹ * G := by
      simp only [U, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hq]
    rw [h]
    exact isHermitian_conjTranspose_mul_mul G hS.inv.isHermitian
  refine ⟨hMid ▸ hR.isUnit.mul hS.isUnit, ?_⟩
  have he := (isWeightedReflexiveInverse_iff_eq W Q A X hW hQ).mp ⟨h₁, h₂, h₃, h₄⟩
  rw [← he, hMid]
  simp only [X, U, V, Matrix.mul_assoc]

end BenIsraelGreville.Chapter03
