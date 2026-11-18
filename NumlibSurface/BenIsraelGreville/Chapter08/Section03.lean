/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.Moments.Variance

/-!
# The linear statistical model

Section 8.3 of [benIsrael2003generalized] studies unbiased estimation by
matrix multiplication and covariance comparisons in Loewner order. The
coefficient optimization is deterministic. Its statistical interpretation
uses finite collections of square-integrable random variables.

## Deviations from the source

* **Corollary 1** uses the scalar estimate $b^T X^\dagger y$. Its coefficient
  condition concerns the column space of $X$.
* **Equation (18)** interprets minimum norm for the estimator coefficient.
* **Theorem 2(b)** uses the projected parameter as the estimand. The covariance
  factor in **Equation (31)** is $V^2$, consistently with (12) and the squared norm.
* **Exercise 6** labels the identity block by the nonzero spectral support and
  the zero block by its complement. Ordering the labels places those blocks
  in the printed order.
-/

namespace BenIsraelGreville.Chapter08

open Matrix MeasureTheory ProbabilityTheory

section Moments

variable {Ω n m p : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- **Section 8.3** of [benIsrael2003generalized]. The expectation of a
random vector is the vector of its coordinate expectations. -/
noncomputable def expectationVector (Y : Ω → n → ℝ) : n → ℝ :=
  fun i => ∫ ω, Y ω i ∂μ

/-- **Section 8.3** of [benIsrael2003generalized]. The covariance of a
random vector is the matrix of the pairwise covariances of its coordinates. -/
noncomputable def covarianceMatrix (Y : Ω → n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => ProbabilityTheory.covariance (fun ω => Y ω i) (fun ω => Y ω j) μ

/-- The coordinate definition of covariance in **Section 8.3** of
[benIsrael2003generalized]. -/
theorem covarianceMatrix_apply (Y : Ω → n → ℝ) (i j : n) :
    covarianceMatrix μ Y i j =
      ∫ ω, (Y ω i - expectationVector μ Y i) * (Y ω j - expectationVector μ Y j) ∂μ :=
  rfl

/-- **Equations (10)–(13)** of [benIsrael2003generalized], Chapter 8.
For every parameter the coordinates are square integrable, the expectation
is the design matrix applied to the parameter, and the covariance is fixed.
The covariance parameter is the full covariance matrix. -/
structure IsLinearStatisticalModel [Fintype p] (X : Matrix n p ℝ) (S : Matrix n n ℝ)
    (Y : (p → ℝ) → Ω → n → ℝ) : Prop where
  /-- Each coordinate of the observation is square integrable. -/
  memLp : ∀ β i, MemLp (fun ω => Y β ω i) 2 μ
  /-- The model at each fixed parameter has mean `X *ᵥ β`. -/
  mean : ∀ β, expectationVector μ (Y β) = X *ᵥ β
  /-- The covariance is the same at each parameter. -/
  covariance : ∀ β, covarianceMatrix μ (Y β) = S

variable {μ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private theorem memLp_mulVec_coordinate [Fintype n] (A : Matrix m n ℝ) (Y : Ω → n → ℝ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ) (i : m) :
    MemLp (fun ω => (A *ᵥ Y ω) i) 2 μ := by
  change MemLp (fun ω => ∑ j, A i j * Y ω j) 2 μ
  exact memLp_finsetSum _ fun j _ => (hY j).const_mul _

/-- Taking expectations commutes with application of an estimator matrix. -/
theorem expectationVector_mulVec [Fintype n] (A : Matrix m n ℝ) (Y : Ω → n → ℝ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ) :
    expectationVector μ (fun ω => A *ᵥ Y ω) = A *ᵥ expectationVector μ Y := by
  funext i
  change (∫ ω, ∑ j, A i j * Y ω j ∂μ) = ∑ j, A i j * expectationVector μ Y j
  rw [integral_finsetSum _ (fun j _ => ((hY j).const_mul (A i j)).integrable (by norm_num))]
  simp only [expectationVector, integral_const_mul]

/-- Covariance transforms by $A \operatorname{Cov}(Y) A^T$ under application
of an estimator matrix. -/
theorem covarianceMatrix_mulVec [Fintype n] (A : Matrix m n ℝ) (Y : Ω → n → ℝ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ) :
    covarianceMatrix μ (fun ω => A *ᵥ Y ω) = A * covarianceMatrix μ Y * Aᵀ := by
  ext i j
  change ProbabilityTheory.covariance (fun ω => ∑ k, A i k * Y ω k)
    (fun ω => ∑ l, A j l * Y ω l) μ = _
  rw [covariance_fun_sum_fun_sum (fun k => (hY k).const_mul (A i k))
    (fun l => (hY l).const_mul (A j l))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, Matrix.mul_apply,
    transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change A j k * (A i l * covarianceMatrix μ Y l k) =
    A i l * covarianceMatrix μ Y l k * A j k
  ring

/-- Adding a constant vector translates the expectation and preserves the
covariance. -/
theorem moments_add_const (Y : Ω → n → ℝ) (a : n → ℝ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ) :
    expectationVector μ (fun ω => Y ω + a) = expectationVector μ Y + a ∧
      covarianceMatrix μ (fun ω => Y ω + a) = covarianceMatrix μ Y := by
  constructor
  · funext i
    change (∫ ω, Y ω i + a i ∂μ) = (∫ ω, Y ω i ∂μ) + a i
    rw [integral_add ((hY i).integrable (by norm_num)) (integrable_const _)]
    simp
  · ext i j
    change ProbabilityTheory.covariance (fun ω => Y ω i + a i) (fun ω => Y ω j + a j) μ =
      ProbabilityTheory.covariance (fun ω => Y ω i) (fun ω => Y ω j) μ
    rw [covariance_add_const_left ((hY i).integrable (by norm_num)),
      covariance_add_const_right ((hY j).integrable (by norm_num))]

/-- **Exercise 1** of [benIsrael2003generalized], Chapter 8. Affine maps of
the observation have the corresponding affine mean and transformed covariance. -/
theorem exercise_8_1 [Fintype n] [Fintype p]
    {X : Matrix n p ℝ} {S : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X S Y) (A : Matrix m n ℝ) (a : m → ℝ) (β : p → ℝ) :
    expectationVector μ (fun ω => A *ᵥ Y β ω + a) = (A * X) *ᵥ β + a ∧
      covarianceMatrix μ (fun ω => A *ᵥ Y β ω + a) = A * S * Aᵀ := by
  obtain ⟨hm, hc⟩ := moments_add_const (μ := μ) (fun ω => A *ᵥ Y β ω) a
    (memLp_mulVec_coordinate A (Y β) (hY.memLp β))
  rw [hm, expectationVector_mulVec A (Y β) (hY.memLp β), hY.mean, mulVec_mulVec]
  rw [hc, covarianceMatrix_mulVec A (Y β) (hY.memLp β), hY.covariance]
  exact ⟨rfl, rfl⟩

/-- **Equations (10)–(13)** of [benIsrael2003generalized], Chapter 8.
The observation model is equivalent to its centered error model. -/
theorem isLinearStatisticalModel_iff_centered_error [Fintype p]
    {X : Matrix n p ℝ} {S : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ} :
    IsLinearStatisticalModel μ X S Y ↔ ∀ β,
      (∀ i, MemLp (fun ω => (Y β ω - X *ᵥ β) i) 2 μ) ∧
      expectationVector μ (fun ω => Y β ω - X *ᵥ β) = 0 ∧
      covarianceMatrix μ (fun ω => Y β ω - X *ᵥ β) = S := by
  constructor
  · intro h β
    have hLp (i : n) : MemLp (fun ω => (Y β ω - X *ᵥ β) i) 2 μ :=
      (h.memLp β i).sub (memLp_const ((X *ᵥ β) i))
    obtain ⟨hm, hc⟩ := moments_add_const (μ := μ) (Y β) (-(X *ᵥ β)) (h.memLp β)
    refine ⟨hLp, ?_, ?_⟩
    · simpa only [← sub_eq_add_neg, h.mean, sub_self] using hm
    · simpa only [← sub_eq_add_neg, h.covariance] using hc
  · intro h
    have hY (β : p → ℝ) : (fun ω => Y β ω - X *ᵥ β + X *ᵥ β) = Y β := by
      funext ω
      exact sub_add_cancel _ _
    refine ⟨?_, ?_, ?_⟩
    · intro β i
      have h' := ((h β).1 i).add (memLp_const ((X *ᵥ β) i) (μ := μ) (p := 2))
      convert h' using 1
      funext ω
      exact (sub_add_cancel _ _).symm
    · intro β
      have hm := (moments_add_const (fun ω => Y β ω - X *ᵥ β) (X *ᵥ β) (h β).1).1
      rw [hY, (h β).2.1, zero_add] at hm
      exact hm
    · intro β
      have hc := (moments_add_const (fun ω => Y β ω - X *ᵥ β) (X *ᵥ β) (h β).1).2
      rw [hY, (h β).2.2] at hc
      exact hc

/-- **Equations (10)–(13)** of [benIsrael2003generalized], Chapter 8.
A single centered error vector with fixed covariance gives a linear statistical
model by adding the design mean at each parameter. -/
theorem isLinearStatisticalModel_add_shared_error [Fintype p]
    (X : Matrix n p ℝ) (ε : Ω → n → ℝ)
    (hLp : ∀ i, MemLp (fun ω => ε ω i) 2 μ) (hmean : expectationVector μ ε = 0) :
    IsLinearStatisticalModel μ X (covarianceMatrix μ ε) (fun β ω => X *ᵥ β + ε ω) := by
  apply isLinearStatisticalModel_iff_centered_error.mpr
  intro β
  simpa only [add_comm (X *ᵥ β), add_sub_cancel_right] using
    (show (∀ i, MemLp (fun ω => ε ω i) 2 μ) ∧ expectationVector μ ε = 0 ∧
      covarianceMatrix μ ε = covarianceMatrix μ ε from ⟨hLp, hmean, rfl⟩)

/-- A square-integrable random vector with zero covariance equals its
expectation almost surely. -/
theorem ae_eq_expectationVector_of_covarianceMatrix_eq_zero [Countable n]
    {Y : Ω → n → ℝ} (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ)
    (h : covarianceMatrix μ Y = 0) :
    Y =ᵐ[μ] fun _ => expectationVector μ Y := by
  have hi (i : n) : ∀ᵐ ω ∂μ, Y ω i = expectationVector μ Y i := by
    have hz : covarianceMatrix μ Y i i = 0 := congrArg (fun M : Matrix n n ℝ => M i i) h
    change ProbabilityTheory.covariance (fun ω => Y ω i) (fun ω => Y ω i) μ = 0 at hz
    rw [covariance_self (hY i).aemeasurable] at hz
    exact ae_eq_integral_of_variance_eq_zero (hY i) hz
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  exact funext hω

end Moments


open Matrix
open scoped MatrixOrder

section Estimators

variable {n m p : Type*} [Fintype n] [Fintype p]

/-- **Equations (14)–(17)** of [benIsrael2003generalized], Chapter 8.
The coefficient `A` is unbiased for the target `B` if `A * X = B`. -/
def IsLinearUnbiasedEstimator (X : Matrix n p ℝ) (B : Matrix m p ℝ)
    (A : Matrix m n ℝ) : Prop :=
  A * X = B

/-- **Equations (16)–(17)** of [benIsrael2003generalized], Chapter 8.
The target is estimable if some linear coefficient is unbiased for it. -/
def IsEstimable (X : Matrix n p ℝ) (B : Matrix m p ℝ) : Prop :=
  ∃ A, IsLinearUnbiasedEstimator X B A

/-- **Equation (19)** of [benIsrael2003generalized], Chapter 8.
The covariance of a BLUE is least in Loewner order among unbiased coefficients. -/
def IsBestLinearUnbiasedEstimator [Finite m] (X : Matrix n p ℝ) (S : Matrix n n ℝ)
    (B : Matrix m p ℝ) (A : Matrix m n ℝ) : Prop :=
  IsLinearUnbiasedEstimator X B A ∧
    ∀ A' : Matrix m n ℝ, IsLinearUnbiasedEstimator X B A' → A * S * Aᵀ ≤ A' * S * A'ᵀ

/-- **Equation (20)** of [benIsrael2003generalized], Chapter 8.
The class `E(X)` consists of coefficients whose rows belong to the column space of `X`. -/
def estimatorClass (X : Matrix n p ℝ) : Set (Matrix m n ℝ) :=
  {A | ∃ K : Matrix m p ℝ, A = K * Xᵀ}

omit [Fintype p] in
/-- **Equation (17)** of [benIsrael2003generalized], Chapter 8.
An estimand is estimable exactly when each target row belongs to the row space
of the design matrix. -/
theorem isEstimable_iff_row_space (X : Matrix n p ℝ) (B : Matrix m p ℝ) :
    IsEstimable X B ↔ ∀ i, B.row i ∈ Submodule.span ℝ (Set.range X.row) := by
  classical
  have hR : Xᵀ.mulVecLin.range = Submodule.span ℝ (Set.range X.row) := by
    rw [range_mulVecLin, col_transpose]
  rw [← hR]
  constructor
  · rintro ⟨A, hA⟩ i
    exact ⟨A.row i, funext fun j => by
      change Xᵀ.mulVec (A.row i) j = B i j
      rw [← show A * X = B from hA, Matrix.mul_apply, mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _⟩
  · intro h
    choose a ha using h
    refine ⟨Matrix.of a, ?_⟩
    change Matrix.of a * X = B
    ext i j
    have hij := congrFun (ha i) j
    change Xᵀ.mulVec (a i) j = B i j at hij
    rw [← hij, Matrix.mul_apply, mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Equation (17)** of [benIsrael2003generalized], Chapter 8.
An estimable target is unchanged by the projector `X† * X`. -/
theorem isEstimable_iff_pinv_mul [DecidableEq p] (X : Matrix n p ℝ) (B : Matrix m p ℝ) :
    IsEstimable X B ↔ B * X.pinv * X = B := by
  constructor
  · rintro ⟨A, hA⟩
    change A * X = B at hA
    rw [← hA]
    calc
      A * X * X.pinv * X = A * (X * X.pinv * X) := by simp only [Matrix.mul_assoc]
      _ = A * X := by rw [X.mul_pinv_mul_self]
  · exact fun h => ⟨B * X.pinv, h⟩

variable [DecidableEq n] [DecidableEq p]

/-- **Equation (23)** of [benIsrael2003generalized], Chapter 8.
The projector onto the null space of the transposed design matrix. -/
noncomputable def observationResidualProjector (X : Matrix n p ℝ) : Matrix n n ℝ :=
  1 - X * X.pinv

omit [DecidableEq n] in
private theorem mul_pinv_transpose (X : Matrix n p ℝ) : (X * X.pinv)ᵀ = X * X.pinv := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using X.isHermitian_mul_pinv.eq

omit [DecidableEq n] in
private theorem pinv_mul_transpose (X : Matrix n p ℝ) : (X.pinv * X)ᵀ = X.pinv * X := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using X.isHermitian_pinv_mul.eq

omit [DecidableEq n] in
private theorem projection_mul_self (X : Matrix n p ℝ) :
    X * X.pinv * (X * X.pinv) = X * X.pinv := by
  rw [← Matrix.mul_assoc, X.mul_pinv_mul_self]

private theorem residual_transpose (X : Matrix n p ℝ) :
    (observationResidualProjector X)ᵀ = observationResidualProjector X := by
  simp only [observationResidualProjector, transpose_sub, transpose_one, mul_pinv_transpose]

private theorem residual_mul_design (X : Matrix n p ℝ) :
    observationResidualProjector X * X = 0 := by
  rw [observationResidualProjector, Matrix.sub_mul, Matrix.one_mul, X.mul_pinv_mul_self, sub_self]

private theorem design_transpose_mul_residual (X : Matrix n p ℝ) :
    Xᵀ * observationResidualProjector X = 0 := by
  rw [← residual_transpose, ← transpose_mul, residual_mul_design, transpose_zero]

private theorem residual_mul_self (X : Matrix n p ℝ) :
    observationResidualProjector X * observationResidualProjector X =
      observationResidualProjector X := by
  have h : X * X.pinv * observationResidualProjector X = 0 := by
    rw [observationResidualProjector, Matrix.mul_sub, Matrix.mul_one, projection_mul_self, sub_self]
  change (1 - X * X.pinv) * observationResidualProjector X = _
  rw [Matrix.sub_mul, Matrix.one_mul, h, sub_zero]

private theorem eq_mul_residual_of_mul_design_eq_zero (X : Matrix n p ℝ)
    {D : Matrix m n ℝ} (hD : D * X = 0) : D * observationResidualProjector X = D := by
  rw [observationResidualProjector, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hD,
    Matrix.zero_mul, sub_zero]

private theorem transpose_pinv (A : Matrix n p ℝ) : Aᵀ.pinv = A.pinvᵀ := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using A.pinv_conjTranspose

omit [DecidableEq n] in
private theorem pinv_eq_gramPinv_mul_transpose (A : Matrix n p ℝ) :
    A.pinv = A.gramPinv * Aᵀ := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using A.pinv_def

omit [DecidableEq n] in
/-- **Equation (18)** of [benIsrael2003generalized], Chapter 8.
For full column rank, the pseudoinverse is the usual least-squares coefficient. -/
theorem pinv_eq_normalEquations_coefficient (X : Matrix n p ℝ) (hX : X.rank = Fintype.card p) :
    X.pinv = (Xᵀ * X)⁻¹ * Xᵀ := by
  have h : IsUnit (Xᴴ * X) := mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_iff_rank_eq_card.mpr (X.rank_conjTranspose_mul_self.trans hX))
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    X.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit h

omit [DecidableEq n] in
private theorem pinv_mul_design_of_full_rank (X : Matrix n p ℝ) (hX : X.rank = Fintype.card p) :
    X.pinv * X = 1 := by
  have hg : (Xᵀ * X).rank = Fintype.card p := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using X.rank_conjTranspose_mul_self.trans hX
  have hu : IsUnit (Xᵀ * X) :=
    mulVec_surjective_iff_isUnit.mp (mulVec_surjective_iff_rank_eq_card.mpr hg)
  rw [pinv_eq_normalEquations_coefficient X hX, Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hu)]

/-- **Equations (25)–(26)** of [benIsrael2003generalized], Chapter 8,
in row form. Every unbiased coefficient is a least-squares coefficient plus
a matrix supported on the observation null space. -/
theorem isLinearUnbiasedEstimator_iff_residualProjector {X : Matrix n p ℝ} {B : Matrix m p ℝ}
    (hB : IsEstimable X B) (A : Matrix m n ℝ) :
    IsLinearUnbiasedEstimator X B A ↔
      ∃ W : Matrix m n ℝ, A = B * X.pinv + W * observationResidualProjector X := by
  have hb := (isEstimable_iff_pinv_mul X B).mp hB
  constructor
  · intro hA
    change A * X = B at hA
    refine ⟨A, ?_⟩
    rw [observationResidualProjector, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hA]
    abel
  · rintro ⟨W, rfl⟩
    change (B * X.pinv + W * observationResidualProjector X) * X = B
    rw [Matrix.add_mul, hb, Matrix.mul_assoc W, residual_mul_design, Matrix.mul_zero, add_zero]

omit [DecidableEq n] in
/-- **Equations (20)–(21)** of [benIsrael2003generalized], Chapter 8.
The least-squares coefficient is the unique unbiased coefficient in the
estimator class `E(X)` of an estimable target. -/
theorem estimatorClass_unbiased_eq {X : Matrix n p ℝ} {B : Matrix m p ℝ}
    (hB : IsEstimable X B) :
    IsLinearUnbiasedEstimator X B (B * X.pinv) ∧ B * X.pinv ∈ estimatorClass X ∧
      ∀ A : Matrix m n ℝ,
        IsLinearUnbiasedEstimator X B A → A ∈ estimatorClass X → A = B * X.pinv := by
  classical
  refine ⟨(isEstimable_iff_pinv_mul X B).mp hB, ⟨B * X.gramPinv, ?_⟩, ?_⟩
  · rw [pinv_eq_gramPinv_mul_transpose, Matrix.mul_assoc]
  · rintro A hA ⟨K, hK⟩
    change A * X = B at hA
    have hQ : A * observationResidualProjector X = 0 := by
      rw [hK, Matrix.mul_assoc, design_transpose_mul_residual, Matrix.mul_zero]
    rw [observationResidualProjector, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, hA, sub_eq_zero] at hQ
    exact hQ

private theorem cov_white_sub (X : Matrix n p ℝ) (A : Matrix m n ℝ)
    (B : Matrix m p ℝ) (σ : ℝ) (hA : A * X = B) :
    A * (σ ^ 2 • (1 : Matrix n n ℝ)) * Aᵀ -
      (B * X.pinv) * (σ ^ 2 • (1 : Matrix n n ℝ)) * (B * X.pinv)ᵀ =
      σ ^ 2 • (A * observationResidualProjector X * Aᵀ) := by
  have hC : (B * X.pinv) = A * (X * X.pinv) := by rw [← hA, Matrix.mul_assoc]
  have hGram : (B * X.pinv) * (B * X.pinv)ᵀ = A * (X * X.pinv) * Aᵀ := by
    rw [hC, transpose_mul, mul_pinv_transpose]
    calc
      _ = A * (X * X.pinv * (X * X.pinv)) * Aᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [projection_mul_self]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hGram, ← smul_sub,
    observationResidualProjector, Matrix.mul_sub, Matrix.sub_mul]

/-- **Equation (22)** of [benIsrael2003generalized], Chapter 8.
This is the covariance difference between any unbiased coefficient and
the least-squares coefficient in the homoscedastic model. -/
theorem gaussMarkov_covariance_difference (X : Matrix n p ℝ) (A : Matrix m n ℝ)
    (B : Matrix m p ℝ) (σ : ℝ) (hA : IsLinearUnbiasedEstimator X B A) :
    A * (σ ^ 2 • (1 : Matrix n n ℝ)) * Aᵀ -
      (B * X.pinv) * (σ ^ 2 • (1 : Matrix n n ℝ)) * (B * X.pinv)ᵀ =
      σ ^ 2 • (A * observationResidualProjector X * Aᵀ) :=
  cov_white_sub X A B σ hA

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 8, in coefficient form.
When the covariance is a scalar multiple of the identity, least squares
gives a BLUE for each estimable target. -/
theorem gaussMarkov_coefficients [Finite m] {X : Matrix n p ℝ} {B : Matrix m p ℝ}
    (hB : IsEstimable X B) (σ : ℝ) :
    IsBestLinearUnbiasedEstimator X (σ ^ 2 • (1 : Matrix n n ℝ)) B (B * X.pinv) := by
  refine ⟨(isEstimable_iff_pinv_mul X B).mp hB, fun A hA => ?_⟩
  rw [Matrix.le_iff, gaussMarkov_covariance_difference X A B σ hA]
  let Q := observationResidualProjector X
  have hQ : (A * Q) * (A * Q)ᵀ = A * Q * Aᵀ := by
    rw [transpose_mul, show Qᵀ = Q from residual_transpose X]
    calc
      A * Q * (Q * Aᵀ) = A * (Q * Q) * Aᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [show Q * Q = Q from residual_mul_self X]
  rw [← hQ]
  apply Matrix.PosSemidef.smul _ (sq_nonneg σ)
  simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose (A * Q)

omit [DecidableEq n] [DecidableEq p] in
/-- Every linear target is estimable when the design matrix has full column rank. -/
theorem isEstimable_of_full_column_rank (X : Matrix n p ℝ)
    (hX : X.rank = Fintype.card p) (B : Matrix m p ℝ) : IsEstimable X B := by
  classical
  apply (isEstimable_iff_pinv_mul X B).mpr
  rw [Matrix.mul_assoc, pinv_mul_design_of_full_rank X hX, Matrix.mul_one]


/-- **Equation (20)** of [benIsrael2003generalized], Chapter 8.
The estimator class consists exactly of coefficients that annihilate the
observation residual projector. -/
theorem mem_estimatorClass_iff_mul_residual_eq_zero (X : Matrix n p ℝ) (A : Matrix m n ℝ) :
    A ∈ estimatorClass X ↔ A * observationResidualProjector X = 0 := by
  constructor
  · rintro ⟨K, rfl⟩
    rw [Matrix.mul_assoc, design_transpose_mul_residual, Matrix.mul_zero]
  · intro h
    rw [observationResidualProjector, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, sub_eq_zero] at h
    refine ⟨A * X * X.gramPinv, ?_⟩
    calc
      A = A * X * X.pinv := h
      _ = A * X * X.gramPinv * Xᵀ := by
        rw [pinv_eq_gramPinv_mul_transpose, Matrix.mul_assoc (A * X)]

/-- In the model of **Theorem 1** of [benIsrael2003generalized], Chapter 8,
nonzero noise gives a nonzero covariance excess for an unbiased
coefficient outside `E(X)`. -/
theorem gaussMarkov_covariance_difference_ne_zero (X : Matrix n p ℝ) (A : Matrix m n ℝ)
    (B : Matrix m p ℝ) (σ : ℝ) (hσ : σ ≠ 0)
    (hA : IsLinearUnbiasedEstimator X B A) (hE : A ∉ estimatorClass X) :
    A * (σ ^ 2 • (1 : Matrix n n ℝ)) * Aᵀ -
      (B * X.pinv) * (σ ^ 2 • (1 : Matrix n n ℝ)) * (B * X.pinv)ᵀ ≠ 0 := by
  rw [gaussMarkov_covariance_difference X A B σ hA, ne_eq, smul_eq_zero]
  refine not_or.mpr ⟨pow_ne_zero 2 hσ, fun h => hE ?_⟩
  let Q := observationResidualProjector X
  have hQQ : Q * Q = Q := residual_mul_self X
  have hQT : Qᵀ = Q := residual_transpose X
  have hGram : (A * Q) * (A * Q)ᵀ = A * Q * Aᵀ := by
    rw [transpose_mul, hQT, ← Matrix.mul_assoc, Matrix.mul_assoc A Q Q, hQQ]
  change A * Q * Aᵀ = 0 at h
  rw [← hGram, ← conjTranspose_eq_transpose_of_trivial, self_mul_conjTranspose_eq_zero] at h
  exact (mem_estimatorClass_iff_mul_residual_eq_zero X A).mpr h

omit [DecidableEq n] in
/-- **Equation (18)** of [benIsrael2003generalized], Chapter 8,
with minimum norm understood for the coefficient matrix. The least-squares
coefficient has smallest squared Frobenius norm among unbiased coefficients. -/
theorem leastSquares_coefficient_min_frobenius_sq [Fintype m]
    {X : Matrix n p ℝ} {A : Matrix m n ℝ} {B : Matrix m p ℝ}
    (hA : IsLinearUnbiasedEstimator X B A) :
    ∑ i, ∑ j, ((B * X.pinv) i j) ^ 2 ≤ ∑ i, ∑ j, (A i j) ^ 2 := by
  classical
  have h := (gaussMarkov_coefficients (show IsEstimable X B from ⟨A, hA⟩) 1).2 A hA
  have hPSD : (A * Aᵀ - (B * X.pinv) * (B * X.pinv)ᵀ).PosSemidef := by
    simpa only [one_pow, one_smul, Matrix.mul_one] using Matrix.le_iff.mp h
  apply Finset.sum_le_sum
  intro i _
  have hi := hPSD.diag_nonneg (i := i)
  simpa only [Matrix.sub_apply, Matrix.mul_apply, transpose_apply, ← sq, sub_nonneg] using hi

/-- **Equation (23)** of [benIsrael2003generalized], Chapter 8.
The generalized BLUE coefficient for the projected parameter. -/
noncomputable def generalizedBLUE (X : Matrix n p ℝ) (V : Matrix n n ℝ) : Matrix p n ℝ :=
  X.pinv * (1 - V * (observationResidualProjector X * V).pinv)

private theorem residual_mul_pinv_mul_X (X : Matrix n p ℝ) (V : Matrix n n ℝ)
    (hV : Vᵀ = V) : (observationResidualProjector X * V).pinv * X = 0 := by
  let Q := observationResidualProjector X
  change (Q * V).pinv * X = 0
  rw [pinv_eq_gramPinv_mul_transpose, transpose_mul, residual_transpose, hV]
  simp only [Matrix.mul_assoc, residual_mul_design, Matrix.mul_zero]

private theorem residual_mul_pinv_mul_residual (X : Matrix n p ℝ) (V : Matrix n n ℝ)
    (hV : Vᵀ = V) :
    (observationResidualProjector X * V).pinv * observationResidualProjector X =
      (observationResidualProjector X * V).pinv := by
  let Q := observationResidualProjector X
  change (Q * V).pinv * Q = _
  rw [pinv_eq_gramPinv_mul_transpose, transpose_mul, residual_transpose, hV]
  change (Q * V).gramPinv * (V * Q) * Q = (Q * V).gramPinv * (V * Q)
  simp only [Matrix.mul_assoc]
  rw [show Q * Q = Q from residual_mul_self X]

/-- **Equations (23), (32)** of [benIsrael2003generalized], Chapter 8.
The two transposed forms for the generalized BLUE coefficient agree. -/
theorem generalizedBLUE_eq_transpose (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    generalizedBLUE X V = X.pinv * (1 - (V * observationResidualProjector X).pinv * V)ᵀ := by
  have hT : (V * observationResidualProjector X)ᵀ = observationResidualProjector X * V := by
    rw [transpose_mul, residual_transpose, hV]
  rw [generalizedBLUE, transpose_sub, transpose_one, transpose_mul, hV, ← transpose_pinv, hT]

/-- **Theorem 2(b)** of [benIsrael2003generalized], Chapter 8. The generalized
BLUE estimates the parameter projected to the row space of the design. -/
theorem generalizedBLUE_mul_design (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    generalizedBLUE X V * X = X.pinv * X := by
  rw [generalizedBLUE, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc V,
    residual_mul_pinv_mul_X X V hV, Matrix.mul_zero, sub_zero]

private theorem generalizedBLUE_mul_V (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    generalizedBLUE X V * V =
      X.pinv * V * (1 - (observationResidualProjector X * V).pinv *
        (observationResidualProjector X * V)) := by
  let Q := observationResidualProjector X
  let T := Q * V
  have hp : T.pinv * V = T.pinv * T := by
    change (Q * V).pinv * V = (Q * V).pinv * (Q * V)
    rw [← Matrix.mul_assoc, residual_mul_pinv_mul_residual X V hV]
  change (X.pinv * (1 - V * T.pinv)) * V = X.pinv * V * (1 - T.pinv * T)
  rw [Matrix.mul_assoc X.pinv, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc V, hp]
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]

private theorem generalizedBLUE_weighted_orthogonal {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hV : Vᵀ = V) {D : Matrix m n ℝ} (hD : D * X = 0) (B : Matrix m p ℝ) :
    B * generalizedBLUE X V * V * (D * V)ᵀ = 0 := by
  let Q := observationResidualProjector X
  let T := Q * V
  have hD' : D * V = D * T := by
    change D * V = D * (Q * V)
    rw [← Matrix.mul_assoc, eq_mul_residual_of_mul_design_eq_zero X hD]
  have hp : (1 - T.pinv * T) * Tᵀ = 0 := by
    have h : T.pinv * T * Tᵀ = Tᵀ := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using T.pinv_mul_self_mul_conjTranspose
    rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  rw [Matrix.mul_assoc B, generalizedBLUE_mul_V X V hV, hD', transpose_mul]
  change B * (X.pinv * V * (1 - T.pinv * T)) * (Tᵀ * Dᵀ) = 0
  calc
    _ = B * (X.pinv * V) * ((1 - T.pinv * T) * Tᵀ) * Dᵀ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hp, Matrix.mul_zero, Matrix.zero_mul]

omit [DecidableEq n] [DecidableEq p] in
private theorem covariance_square_factor (A : Matrix m n ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    A * (V * V) * Aᵀ = (A * V) * (A * V)ᵀ := by
  rw [transpose_mul, hV]
  simp only [Matrix.mul_assoc]

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 8.
For any unbiased coefficient, its covariance excess over the generalized
BLUE is the Gram matrix of its covariance-weighted difference. -/
theorem generalizedBLUE_covariance_difference {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hV : Vᵀ = V) {B : Matrix m p ℝ} {A : Matrix m n ℝ}
    (hA : IsLinearUnbiasedEstimator X B A) :
    let C := B * generalizedBLUE X V
    A * (V * V) * Aᵀ - C * (V * V) * Cᵀ = ((A - C) * V) * ((A - C) * V)ᵀ := by
  intro C
  let D := A - C
  change A * X = B at hA
  have hCX : C * X = B := by
    change (B * generalizedBLUE X V) * X = B
    rw [Matrix.mul_assoc, generalizedBLUE_mul_design X V hV,
      ← Matrix.mul_assoc, (isEstimable_iff_pinv_mul X B).mp ⟨A, hA⟩]
  have hD : D * X = 0 := by rw [show D = A - C from rfl, Matrix.sub_mul, hA, hCX, sub_self]
  have h₁ : (C * V) * (D * V)ᵀ = 0 := generalizedBLUE_weighted_orthogonal hV hD B
  have h₂ : (D * V) * (C * V)ᵀ = 0 := by
    have h := congrArg Matrix.transpose h₁
    rwa [transpose_mul, transpose_transpose, transpose_zero] at h
  have hAD : A = C + D := by dsimp only [D]; abel
  change A * (V * V) * Aᵀ - C * (V * V) * Cᵀ = (D * V) * (D * V)ᵀ
  rw [covariance_square_factor A V hV, covariance_square_factor C V hV, hAD,
    Matrix.add_mul, transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    h₁, h₂, add_zero, zero_add, add_sub_cancel_left]

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 8, in coefficient form.
For an estimable target, the generalized estimator is unbiased and has
least covariance among unbiased estimators, including for singular covariance. -/
theorem generalizedGaussMarkov_coefficients [Finite m] {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hV : Vᵀ = V) {B : Matrix m p ℝ} (hB : IsEstimable X B) :
    IsBestLinearUnbiasedEstimator X (V * V) B (B * generalizedBLUE X V) := by
  refine ⟨?_, fun A hA => ?_⟩
  · change (B * generalizedBLUE X V) * X = B
    rw [Matrix.mul_assoc, generalizedBLUE_mul_design X V hV, ← Matrix.mul_assoc,
      (isEstimable_iff_pinv_mul X B).mp hB]
  · rw [Matrix.le_iff, generalizedBLUE_covariance_difference hV hA]
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_self_mul_conjTranspose ((A - B * generalizedBLUE X V) * V)

/-- **Equations (27), (29)–(31)** of [benIsrael2003generalized], Chapter 8.
An unbiased coefficient is best exactly when its covariance-weighted
difference from the canonical BLUE vanishes. -/
theorem isBestLinearUnbiasedEstimator_iff_difference [Finite m]
    {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hV : Vᵀ = V) {B : Matrix m p ℝ} (A : Matrix m n ℝ) :
    IsBestLinearUnbiasedEstimator X (V * V) B A ↔
      IsLinearUnbiasedEstimator X B A ∧ (A - B * generalizedBLUE X V) * V = 0 := by
  let C := B * generalizedBLUE X V
  change IsBestLinearUnbiasedEstimator X (V * V) B A ↔
    IsLinearUnbiasedEstimator X B A ∧ (A - C) * V = 0
  constructor
  · rintro ⟨hA, hbest⟩
    have hc : IsBestLinearUnbiasedEstimator X (V * V) B C :=
      generalizedGaussMarkov_coefficients hV ⟨A, hA⟩
    have hEq := le_antisymm (hbest C hc.1) (hc.2 A hA)
    have h := generalizedBLUE_covariance_difference hV hA
    change A * (V * V) * Aᵀ - C * (V * V) * Cᵀ = ((A - C) * V) * ((A - C) * V)ᵀ at h
    rw [hEq, sub_self] at h
    refine ⟨hA, self_mul_conjTranspose_eq_zero.mp ?_⟩
    simpa only [conjTranspose_eq_transpose_of_trivial] using h.symm
  · rintro ⟨hA, hdiff⟩
    have hc : IsBestLinearUnbiasedEstimator X (V * V) B C :=
      generalizedGaussMarkov_coefficients hV ⟨A, hA⟩
    have h := generalizedBLUE_covariance_difference hV hA
    change A * (V * V) * Aᵀ - C * (V * V) * Cᵀ = ((A - C) * V) * ((A - C) * V)ᵀ at h
    rw [hdiff, Matrix.zero_mul, sub_eq_zero] at h
    exact ⟨hA, fun A' hA' => h.symm ▸ hc.2 A' hA'⟩

/-- **Theorem 2(b)** of [benIsrael2003generalized], Chapter 8.
The estimate of the projected parameter lies in the row space of the design. -/
theorem generalizedBLUE_mulVec_mem_transpose_range (X : Matrix n p ℝ) (V : Matrix n n ℝ)
    (y : n → ℝ) : generalizedBLUE X V *ᵥ y ∈ Xᵀ.mulVecLin.range := by
  have hp : X.pinv * X * X.pinv = X.pinv := X.pinv_mul_self_mul_pinv
  have h1 : X.pinv * X = Xᵀ * X.pinvᵀ := by
    rw [← transpose_mul, pinv_mul_transpose]
  let z := generalizedBLUE X V *ᵥ y
  refine ⟨X.pinvᵀ *ᵥ z, ?_⟩
  change Xᵀ *ᵥ (X.pinvᵀ *ᵥ z) = z
  rw [mulVec_mulVec, ← h1]
  dsimp only [z, generalizedBLUE]
  rw [mulVec_mulVec, ← Matrix.mul_assoc, hp]

end Estimators


section StatisticalEstimation

variable {Ω n m p : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype n] [Fintype p]

/-- **Equations (16)–(17)** of [benIsrael2003generalized], Chapter 8.
The coefficient condition is equivalent to the expectation identity at every parameter. -/
theorem isLinearUnbiasedEstimator_iff_expectation
    {X : Matrix n p ℝ} {S : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X S Y) (A : Matrix m n ℝ) (B : Matrix m p ℝ) :
    IsLinearUnbiasedEstimator X B A ↔
      ∀ β, expectationVector μ (fun ω => A *ᵥ Y β ω) = B *ᵥ β := by
  change A * X = B ↔ _
  simp only [expectationVector_mulVec A (Y _) (hY.memLp _), hY.mean, mulVec_mulVec]
  exact ext_iff_mulVec

/-- **Equation (19)** of [benIsrael2003generalized], Chapter 8.
The coefficient inequality compares the covariances of the actual estimators. -/
theorem covarianceMatrix_le_of_bestLinearUnbiasedEstimator [Finite m]
    {X : Matrix n p ℝ} {S : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X S Y) {A C : Matrix m n ℝ} {B : Matrix m p ℝ}
    (hC : IsBestLinearUnbiasedEstimator X S B C) (hA : IsLinearUnbiasedEstimator X B A)
    (β : p → ℝ) :
    covarianceMatrix μ (fun ω => C *ᵥ Y β ω) ≤ covarianceMatrix μ (fun ω => A *ᵥ Y β ω) := by
  rw [covarianceMatrix_mulVec C (Y β) (hY.memLp β),
    covarianceMatrix_mulVec A (Y β) (hY.memLp β), hY.covariance]
  exact hC.2 A hA

/-- **Equations (30)–(31)** of [benIsrael2003generalized], Chapter 8.
Any linear combination that annihilates the design and covariance square root
vanishes almost surely. -/
theorem ae_zero_mulVec_of_annihilates_design_covariance
    {X : Matrix n p ℝ} {V : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X (V * V) Y)
    {D : Matrix m n ℝ} (hDX : D * X = 0) (hDV : D * V = 0)
    [Countable m] (β : p → ℝ) :
    (fun ω => D *ᵥ Y β ω) =ᵐ[μ] fun _ => 0 := by
  have hmean : expectationVector μ (fun ω => D *ᵥ Y β ω) = 0 := by
    rw [expectationVector_mulVec D (Y β) (hY.memLp β), hY.mean, mulVec_mulVec, hDX, zero_mulVec]
  have hCov : covarianceMatrix μ (fun ω => D *ᵥ Y β ω) = 0 := by
    rw [covarianceMatrix_mulVec D (Y β) (hY.memLp β), hY.covariance, ← Matrix.mul_assoc D V V,
      hDV, Matrix.zero_mul, Matrix.zero_mul]
  simpa only [hmean] using
    ae_eq_expectationVector_of_covarianceMatrix_eq_zero
      (memLp_mulVec_coordinate D (Y β) (hY.memLp β)) hCov

variable [DecidableEq n] [DecidableEq p]

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 8. In the
homoscedastic model with full-column-rank design, the least-squares estimator
is BLUE. Every unbiased coefficient in the estimator class agrees with it. -/
theorem theorem_1 [Finite m] {X : Matrix n p ℝ} (σ : ℝ) {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix n n ℝ)) Y)
    (hX : X.rank = Fintype.card p) (B : Matrix m p ℝ) :
    IsEstimable X B ∧
      IsBestLinearUnbiasedEstimator X (σ ^ 2 • (1 : Matrix n n ℝ)) B (B * X.pinv) ∧
      B * X.pinv ∈ estimatorClass X ∧
      (∀ A : Matrix m n ℝ, IsLinearUnbiasedEstimator X B A → ∀ β,
        covarianceMatrix μ (fun ω => (B * X.pinv) *ᵥ Y β ω) ≤
          covarianceMatrix μ (fun ω => A *ᵥ Y β ω)) ∧
      ∀ A : Matrix m n ℝ, IsLinearUnbiasedEstimator X B A → A ∈ estimatorClass X →
        ∀ β, (fun ω => A *ᵥ Y β ω) =ᵐ[μ] fun ω => (B * X.pinv) *ᵥ Y β ω := by
  have hb := isEstimable_of_full_column_rank X hX B
  have hbest := gaussMarkov_coefficients hb σ
  have hClass := estimatorClass_unbiased_eq hb
  refine ⟨hb, hbest, hClass.2.1,
    fun _ hA β => covarianceMatrix_le_of_bestLinearUnbiasedEstimator hY hbest hA β, ?_⟩
  intro A hA hm β
  rw [hClass.2.2 A hA hm]

/-- **Equations (29)–(31)** and **Theorem 2(a)** of [benIsrael2003generalized],
Chapter 8. Any BLUE equals the generalized BLUE applied to the observation,
almost surely at every parameter. -/
theorem ae_eq_generalizedBLUE_of_bestLinearUnbiasedEstimator [Finite m]
    {X : Matrix n p ℝ} {V : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X (V * V) Y) (hV : Vᵀ = V)
    {B : Matrix m p ℝ} {A : Matrix m n ℝ} (hA : IsBestLinearUnbiasedEstimator X (V * V) B A)
    (β : p → ℝ) :
    (fun ω => A *ᵥ Y β ω) =ᵐ[μ] fun ω => (B * generalizedBLUE X V) *ᵥ Y β ω := by
  have h := (isBestLinearUnbiasedEstimator_iff_difference hV A).mp hA
  have hC := generalizedGaussMarkov_coefficients hV (show IsEstimable X B from ⟨A, h.1⟩)
  have hDX : (A - B * generalizedBLUE X V) * X = 0 := by
    rw [Matrix.sub_mul, show A * X = B from h.1,
      show (B * generalizedBLUE X V) * X = B from hC.1, sub_self]
  have h0 := ae_zero_mulVec_of_annihilates_design_covariance hY hDX h.2 β
  filter_upwards [h0] with ω hω
  exact sub_eq_zero.mp (by simpa only [sub_mulVec] using hω)

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 8.
Every estimable linear target has an almost surely unique BLUE. The parameter
vector estimate lies in the row space of the design and is BLUE for the
projected parameter. -/
theorem theorem_2 [Finite m]
    {X : Matrix n p ℝ} {V : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X (V * V) Y) (hV : Vᵀ = V)
    {B : Matrix m p ℝ} (hB : IsEstimable X B) :
    IsBestLinearUnbiasedEstimator X (V * V) B (B * generalizedBLUE X V) ∧
      (∀ A : Matrix m n ℝ, IsBestLinearUnbiasedEstimator X (V * V) B A → ∀ β,
        (fun ω => A *ᵥ Y β ω) =ᵐ[μ] fun ω => (B * generalizedBLUE X V) *ᵥ Y β ω) ∧
      (∀ β ω, generalizedBLUE X V *ᵥ Y β ω ∈ Xᵀ.mulVecLin.range) ∧
      IsBestLinearUnbiasedEstimator X (V * V) (X.pinv * X) (generalizedBLUE X V) := by
  refine ⟨generalizedGaussMarkov_coefficients hV hB,
    fun _ hA β => ae_eq_generalizedBLUE_of_bestLinearUnbiasedEstimator hY hV hA β,
    fun β ω => generalizedBLUE_mulVec_mem_transpose_range X V (Y β ω), ?_⟩
  have h := generalizedGaussMarkov_coefficients hV
    (show IsEstimable X (X.pinv * X) from ⟨X.pinv, rfl⟩)
  have hc : (X.pinv * X) * generalizedBLUE X V = generalizedBLUE X V := by
    unfold generalizedBLUE
    rw [← Matrix.mul_assoc, X.pinv_mul_self_mul_pinv]
  rwa [hc] at h

end StatisticalEstimation

section AlternateCoefficients

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

omit [DecidableEq n] in
private theorem pinv_eq_pinv_gram_mul_transpose (A : Matrix n p ℝ) :
    A.pinv = (Aᵀ * A).pinv * Aᵀ := by
  let G := Aᵀ * A
  have hG : Gᴴ = G := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (isHermitian_conjTranspose_mul_self A).eq
  have hP := A.isHermitian_gramPinv.eq
  have hc : A.gramPinv * G = G * A.gramPinv := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using A.gramPinv_mul_gram_comm
  have hGP : A.gramPinv = G.pinv := by
    refine G.pinv_unique ?_ ?_ ?_ ?_
    · simpa only [G, conjTranspose_eq_transpose_of_trivial] using A.gram_mul_gramPinv_mul_gram
    · simpa only [G, conjTranspose_eq_transpose_of_trivial] using A.gramPinv_mul_gram_mul_gramPinv
    · change (G * A.gramPinv)ᴴ = G * A.gramPinv
      rw [conjTranspose_mul, hG, hP, hc]
    · change (A.gramPinv * G)ᴴ = A.gramPinv * G
      rw [conjTranspose_mul, hG, hP, hc]
  rw [pinv_eq_gramPinv_mul_transpose, hGP]

/-- **Equation (33)** of [benIsrael2003generalized], Chapter 8.
The estimator can be computed from the covariance in the residual space. -/
theorem generalizedBLUE_eq_covariance (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    let Q := observationResidualProjector X
    generalizedBLUE X V = X.pinv * (1 - (Q * (V * V) * Q).pinv * (Q * (V * V)))ᵀ := by
  intro Q
  have hT : (V * Q)ᵀ = Q * V := by rw [transpose_mul, show Qᵀ = Q from residual_transpose X, hV]
  have hG : (V * Q)ᵀ * (V * Q) = Q * (V * V) * Q := by
    rw [hT]
    simp only [Matrix.mul_assoc]
  rw [generalizedBLUE_eq_transpose X V hV]
  change X.pinv * (1 - (V * Q).pinv * V)ᵀ = _
  rw [pinv_eq_pinv_gram_mul_transpose (V * Q), hG, hT]
  simp only [Matrix.mul_assoc]

/-- **Exercise 9**, Equation (42) of [benIsrael2003generalized], Chapter 8.
The pseudoinverse of the whitened design is obtained by removing the
whitened observation null space. -/
theorem exercise_8_9 (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V)
    (hu : IsUnit V) :
    (V⁻¹ * X).pinv = X.pinv * V *
      (1 - (V * observationResidualProjector X) * (V * observationResidualProjector X).pinv) := by
  let Q := observationResidualProjector X
  let W := V * Q
  let R := 1 - W * W.pinv
  let J := V⁻¹ * X
  let C := X.pinv * V * R
  have hdet := (isUnit_iff_isUnit_det V).mp hu
  have hl := V.nonsing_inv_mul hdet
  have hr := V.mul_nonsing_inv hdet
  have hW : Wᵀ = Q * V := by
    change (V * Q)ᵀ = Q * V
    rw [transpose_mul, show Qᵀ = Q from residual_transpose X, hV]
  have hwj : Wᵀ * J = 0 := by
    change Wᵀ * (V⁻¹ * X) = 0
    rw [hW, Matrix.mul_assoc Q V, ← Matrix.mul_assoc V V⁻¹, hr,
      Matrix.one_mul, show Q * X = 0 from residual_mul_design X]
  have hwr : Wᵀ * R = 0 := by
    have h := W.conjTranspose_mul_mul_pinv
    rw [conjTranspose_eq_transpose_of_trivial] at h
    change Wᵀ * (1 - W * W.pinv) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have hRJ : R * J = J := by
    have h : W.pinv * J = 0 := by
      rw [pinv_eq_gramPinv_mul_transpose, Matrix.mul_assoc, hwj, Matrix.mul_zero]
    change (1 - W * W.pinv) * J = J
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc W W.pinv, h, Matrix.mul_zero, sub_zero]
  have hP : X * X.pinv * (V * R) = V * R := by
    rw [hW, Matrix.mul_assoc] at hwr
    change (1 - X * X.pinv) * (V * R) = 0 at hwr
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, eq_comm] at hwr
  have hJC : J * C = R := by
    calc
      (V⁻¹ * X) * (X.pinv * V * R) = V⁻¹ * (X * X.pinv * (V * R)) := by
        simp only [Matrix.mul_assoc]
      _ = R := by rw [hP, ← Matrix.mul_assoc, hl, Matrix.one_mul]
  have hCJ : C * J = X.pinv * X := by
    calc
      C * J = X.pinv * (V * (R * J)) := by dsimp only [C]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRJ, show J = V⁻¹ * X from rfl, ← Matrix.mul_assoc V V⁻¹, hr, Matrix.one_mul]
  have hC : (X.pinv * X) * C = C := by
    dsimp only [C]
    rw [← Matrix.mul_assoc (X.pinv * X), ← Matrix.mul_assoc (X.pinv * X),
      X.pinv_mul_self_mul_pinv]
  change J.pinv = C
  symm
  exact J.pinv_unique (by rw [hJC, hRJ]) (by rw [hCJ, hC])
    (hJC ▸ isHermitian_one.sub W.isHermitian_mul_pinv)
    (hCJ ▸ X.isHermitian_pinv_mul)

/-- For nonsingular covariance factors, the generalized BLUE is the
ordinary least-squares coefficient of the whitened observation. -/
theorem generalizedBLUE_eq_whitened (X : Matrix n p ℝ) (V : Matrix n n ℝ)
    (hV : Vᵀ = V) (hu : IsUnit V) :
    generalizedBLUE X V = (V⁻¹ * X).pinv * V⁻¹ := by
  let Q := observationResidualProjector X
  let T := Q * V
  let W := V * Q
  have hT : Tᵀ = W := by
    change (Q * V)ᵀ = V * Q
    rw [transpose_mul, hV, show Qᵀ = Q from residual_transpose X]
  have he : T.pinv * T = W * W.pinv := by
    calc
      _ = (T.pinv * T)ᵀ := (pinv_mul_transpose T).symm
      _ = _ := by rw [transpose_mul, ← transpose_pinv, hT]
  have ht : T.pinv * V = T.pinv * T := by
    change (Q * V).pinv * V = (Q * V).pinv * (Q * V)
    rw [← Matrix.mul_assoc, residual_mul_pinv_mul_residual X V hV]
  have hr := V.mul_nonsing_inv ((isUnit_iff_isUnit_det V).mp hu)
  have hw : W * W.pinv * V⁻¹ = T.pinv := by
    rw [← he, ← ht, Matrix.mul_assoc, hr, Matrix.mul_one]
  rw [exercise_8_9 X V hV hu]
  change X.pinv * (1 - V * T.pinv) = X.pinv * V * (1 - W * W.pinv) * V⁻¹
  calc
    _ = X.pinv * (V * (1 - W * W.pinv) * V⁻¹) := by
      rw [Matrix.mul_sub V, Matrix.mul_one, Matrix.sub_mul, hr, Matrix.mul_assoc V, hw]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **Equation (34)** of [benIsrael2003generalized], Chapter 8.
For a nonsingular covariance factor the estimator solves the weighted
normal equations via the pseudoinverse. -/
theorem generalizedBLUE_eq_weighted_normalEquations (X : Matrix n p ℝ) (V : Matrix n n ℝ)
    (hV : Vᵀ = V) (hu : IsUnit V) :
    generalizedBLUE X V = (Xᵀ * (V * V)⁻¹ * X).pinv * Xᵀ * (V * V)⁻¹ := by
  let J := V⁻¹ * X
  have hr := V.mul_nonsing_inv ((isUnit_iff_isUnit_det V).mp hu)
  have h₂ : (V * V)⁻¹ = V⁻¹ * V⁻¹ := by
    apply inv_eq_right_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V V⁻¹, hr, Matrix.one_mul, hr]
  have hT : Jᵀ = Xᵀ * V⁻¹ := by
    change (V⁻¹ * X)ᵀ = Xᵀ * V⁻¹
    rw [transpose_mul, transpose_nonsing_inv, hV]
  have hG : Jᵀ * J = Xᵀ * (V * V)⁻¹ * X := by
    rw [hT, h₂]
    change Xᵀ * V⁻¹ * (V⁻¹ * X) = _
    simp only [Matrix.mul_assoc]
  rw [generalizedBLUE_eq_whitened X V hV hu]
  change J.pinv * V⁻¹ = _
  rw [pinv_eq_pinv_gram_mul_transpose, hG, hT, h₂]
  simp only [Matrix.mul_assoc]

/-- **Equation (35)** of [benIsrael2003generalized], Chapter 8.
The generalized estimator reduces to ordinary least squares for scalar covariance. -/
theorem generalizedBLUE_scalar_covariance (X : Matrix n p ℝ) (σ : ℝ) :
    generalizedBLUE X (σ • (1 : Matrix n n ℝ)) = X.pinv := by
  by_cases hσ : σ = 0
  · simp [hσ, generalizedBLUE]
  · let V := σ • (1 : Matrix n n ℝ)
    let B := X.pinv * X
    have hV : Vᵀ = V := by simp [V]
    have hVV : V * V = σ ^ 2 • (1 : Matrix n n ℝ) := by
      simp [V, smul_smul, pow_two]
    have hB : IsEstimable X B := ⟨X.pinv, rfl⟩
    have hbest := gaussMarkov_coefficients hB σ
    have hBX : B * X.pinv = X.pinv := X.pinv_mul_self_mul_pinv
    rw [hBX, ← hVV] at hbest
    have h := (isBestLinearUnbiasedEstimator_iff_difference hV X.pinv).mp hbest
    have hC : B * generalizedBLUE X V = generalizedBLUE X V := by
      dsimp only [B, generalizedBLUE]
      rw [← Matrix.mul_assoc, X.pinv_mul_self_mul_pinv]
    rw [hC] at h
    have hz := h.2
    change (X.pinv - generalizedBLUE X V) * (σ • (1 : Matrix n n ℝ)) = 0 at hz
    rw [Matrix.mul_smul, Matrix.mul_one, smul_eq_zero] at hz
    exact (sub_eq_zero.mp (hz.resolve_left hσ)).symm

/-- **Corollary 2** of [benIsrael2003generalized], Chapter 8.
The equivalent covariance and weighted normal-equation forms of the
generalized estimator. -/
theorem corollary_2 (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    let Q := observationResidualProjector X
    generalizedBLUE X V = X.pinv * (1 - (V * Q).pinv * V)ᵀ ∧
      generalizedBLUE X V = X.pinv * (1 - (Q * (V * V) * Q).pinv * (Q * (V * V)))ᵀ ∧
      (IsUnit (V * V) →
        generalizedBLUE X V = (Xᵀ * (V * V)⁻¹ * X).pinv * Xᵀ * (V * V)⁻¹) ∧
      ∀ σ : ℝ, generalizedBLUE X (σ • (1 : Matrix n n ℝ)) = X.pinv := by
  intro Q
  exact ⟨generalizedBLUE_eq_transpose X V hV, generalizedBLUE_eq_covariance X V hV,
    fun hu => generalizedBLUE_eq_weighted_normalEquations X V hV (isUnit_of_mul_isUnit_left hu),
    generalizedBLUE_scalar_covariance X⟩

end AlternateCoefficients

section ScalarEstimators

variable {Ω n p : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

omit [Fintype n] [DecidableEq n] [DecidableEq p] in
private theorem rowEstimator_mem_class (X : Matrix n p ℝ) {a : n → ℝ}
    (ha : a ∈ X.mulVecLin.range) : replicateRow Unit a ∈ estimatorClass X := by
  obtain ⟨k, hk⟩ := ha
  refine ⟨replicateRow Unit k, ?_⟩
  ext i j
  have h := congrFun hk j
  change (X *ᵥ k) j = a j at h
  change a j = ∑ t, k t * X j t
  rw [← h]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **Corollary 1** of [benIsrael2003generalized], Chapter 8.
The least-squares estimator of a linear functional has minimum variance.
An unbiased coefficient in the column space of the design gives the same
scalar estimator almost surely. -/
theorem corollary_1 {X : Matrix n p ℝ} (σ : ℝ) {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix n n ℝ)) Y)
    (hX : X.rank = Fintype.card p) (b : p → ℝ) :
    IsEstimable X (replicateRow Unit b) ∧
      (∀ a : n → ℝ, IsLinearUnbiasedEstimator X (replicateRow Unit b) (replicateRow Unit a) →
        ∀ β, variance (fun ω => b ⬝ᵥ (X.pinv *ᵥ Y β ω)) μ ≤
          variance (fun ω => a ⬝ᵥ Y β ω) μ) ∧
      ∀ a : n → ℝ, IsLinearUnbiasedEstimator X (replicateRow Unit b) (replicateRow Unit a) →
        a ∈ X.mulVecLin.range → ∀ β,
        (fun ω => a ⬝ᵥ Y β ω) =ᵐ[μ] fun ω => b ⬝ᵥ (X.pinv *ᵥ Y β ω) := by
  let B := replicateRow Unit b
  obtain ⟨hB, hbest, _, hcov, hAE⟩ := theorem_1 σ hY hX B
  refine ⟨hB, ?_, ?_⟩
  · intro a ha β
    let A := replicateRow Unit a
    let C := B * X.pinv
    have hpos := Matrix.le_iff.mp (hcov A ha β)
    have h := hpos.diag_nonneg (i := ())
    change 0 ≤ ProbabilityTheory.covariance (fun ω => (A *ᵥ Y β ω) ())
      (fun ω => (A *ᵥ Y β ω) ()) μ -
      ProbabilityTheory.covariance (fun ω => (C *ᵥ Y β ω) ())
      (fun ω => (C *ᵥ Y β ω) ()) μ at h
    rw [covariance_self (memLp_mulVec_coordinate A (Y β) (hY.memLp β) ()).aemeasurable,
      covariance_self (memLp_mulVec_coordinate C (Y β) (hY.memLp β) ()).aemeasurable] at h
    have hC : (fun ω => (C *ᵥ Y β ω) ()) = fun ω => b ⬝ᵥ (X.pinv *ᵥ Y β ω) := by
      funext ω
      change ((B * X.pinv) *ᵥ Y β ω) () = _
      rw [← mulVec_mulVec]
      rfl
    rw [hC] at h
    exact sub_nonneg.mp h
  · intro a ha hass β
    filter_upwards [hAE (replicateRow Unit a) ha (rowEstimator_mem_class X hass) β] with ω hω
    have h := congrFun hω ()
    rw [← mulVec_mulVec] at h
    exact h

omit [DecidableEq n] in
/-- **Exercise 2(a)** of [benIsrael2003generalized], Chapter 8.
A rank-deficient design has no unbiased estimator for the whole parameter. -/
theorem exercise_8_2a (X : Matrix n p ℝ) (hX : X.rank < Fintype.card p) :
    ¬IsEstimable X (1 : Matrix p p ℝ) := by
  rintro ⟨A, hA⟩
  change A * X = 1 at hA
  have h := rank_mul_le_right A X
  rw [hA, rank_one] at h
  exact not_le_of_gt hX h

omit [DecidableEq n] [DecidableEq p] in
/-- **Exercise 2(b)** of [benIsrael2003generalized], Chapter 8.
A nonzero row functional from the design null space is unestimable. -/
theorem exercise_8_2b (X : Matrix n p ℝ) {b : p → ℝ} (hb : X *ᵥ b = 0) (hne : b ≠ 0) :
    ¬IsEstimable X (replicateRow Unit b) := by
  rintro ⟨A, hA⟩
  have h : (replicateRow Unit b) *ᵥ b = 0 := by
    rw [← show A * X = replicateRow Unit b from hA, ← mulVec_mulVec, hb, mulVec_zero]
  have hz : b ⬝ᵥ b = 0 := congrFun h ()
  exact hne (dotProduct_self_eq_zero.mp hz)

omit [DecidableEq n] [DecidableEq p] in
/-- **Exercise 7** of [benIsrael2003generalized], Chapter 8.
The components with zero covariance are almost surely equal to their
deterministic design values. This applies to the null-space rows in (40b). -/
theorem exercise_8_7 {m : Type*} [Countable m]
    {X : Matrix n p ℝ} {S : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X S Y)
    {A : Matrix m n ℝ} (hAS : A * S = 0) (β : p → ℝ) :
    (fun ω => A *ᵥ Y β ω) =ᵐ[μ] fun _ => (A * X) *ᵥ β := by
  have h0 : covarianceMatrix μ (fun ω => A *ᵥ Y β ω) = 0 := by
    rw [covarianceMatrix_mulVec A (Y β) (hY.memLp β), hY.covariance, hAS, Matrix.zero_mul]
  have hM : expectationVector μ (fun ω => A *ᵥ Y β ω) = (A * X) *ᵥ β := by
    rw [expectationVector_mulVec A (Y β) (hY.memLp β), hY.mean, mulVec_mulVec]
  simpa only [hM] using
    ae_eq_expectationVector_of_covarianceMatrix_eq_zero
      (memLp_mulVec_coordinate A (Y β) (hY.memLp β)) h0

end ScalarEstimators

section BLUEFamilies

variable {n p m : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- **Equations (27)–(28)** of [benIsrael2003generalized], Chapter 8.
All BLUE coefficients are the canonical one plus a variation through
the null space of the covariance-weighted design residual. -/
theorem isBestLinearUnbiasedEstimator_iff_affine_family [Finite m]
    {X : Matrix n p ℝ} {V : Matrix n n ℝ} (hV : Vᵀ = V)
    {B : Matrix m p ℝ} (hB : IsEstimable X B) (A : Matrix m n ℝ) :
    let Q := observationResidualProjector X
    let T := Q * V
    IsBestLinearUnbiasedEstimator X (V * V) B A ↔
      ∃ W : Matrix m n ℝ, A = B * generalizedBLUE X V + W * (1 - T * T.pinv) * Q := by
  intro Q T
  let C := B * generalizedBLUE X V
  let L := 1 - T * T.pinv
  have hCX : C * X = B := (generalizedGaussMarkov_coefficients hV hB).1
  have hQX : Q * X = 0 := residual_mul_design X
  have hLT : L * T = 0 := by
    change (1 - T * T.pinv) * T = 0
    rw [Matrix.sub_mul, Matrix.one_mul, T.mul_pinv_mul_self, sub_self]
  rw [isBestLinearUnbiasedEstimator_iff_difference hV A]
  change IsLinearUnbiasedEstimator X B A ∧ (A - C) * V = 0 ↔
    ∃ W : Matrix m n ℝ, A = C + W * L * Q
  constructor
  · rintro ⟨hA, hDV⟩
    let D := A - C
    have hDX : D * X = 0 := by
      rw [show D = A - C from rfl, Matrix.sub_mul, show A * X = B from hA, hCX, sub_self]
    have hDQ : D * Q = D := eq_mul_residual_of_mul_design_eq_zero X hDX
    have hDT : D * T = 0 := by
      change D * (Q * V) = 0
      rw [← Matrix.mul_assoc, hDQ]
      exact hDV
    have hDL : D * L = D := by
      change D * (1 - T * T.pinv) = D
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc D T T.pinv, hDT,
        Matrix.zero_mul, sub_zero]
    refine ⟨D, ?_⟩
    rw [hDL, hDQ]
    dsimp only [D]
    abel
  · rintro ⟨W, rfl⟩
    constructor
    · change (C + W * L * Q) * X = B
      rw [Matrix.add_mul, hCX, Matrix.mul_assoc (W * L), hQX, Matrix.mul_zero, add_zero]
    · rw [add_sub_cancel_left, Matrix.mul_assoc (W * L)]
      change W * L * T = 0
      rw [Matrix.mul_assoc, hLT, Matrix.mul_zero]

omit [DecidableEq n] in
private theorem pinv_mul_eq_zero_iff_transpose_mul_eq_zero
    {t : Type*} {M : Matrix n p ℝ} {N : Matrix n t ℝ} :
    M.pinv * N = 0 ↔ Mᵀ * N = 0 := by
  constructor
  · intro h
    have he : Mᵀ * (M * M.pinv) = Mᵀ := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using M.conjTranspose_mul_mul_pinv
    rw [← he, Matrix.mul_assoc Mᵀ, Matrix.mul_assoc M, h, Matrix.mul_zero, Matrix.mul_zero]
  · intro h
    rw [pinv_eq_gramPinv_mul_transpose, Matrix.mul_assoc, h, Matrix.mul_zero]

omit [DecidableEq n] in
private theorem mul_pinvTranspose_eq_zero_iff_mul_self_eq_zero {X : Matrix n p ℝ}
    (N : Matrix m n ℝ) : N * X.pinvᵀ = 0 ↔ N * X = 0 := by
  constructor
  · intro h
    have he : X.pinvᵀ * (Xᵀ * X) = X := by
      have h := X.conjTranspose_mul_mul_pinv
      rw [conjTranspose_eq_transpose_of_trivial] at h
      simpa only [transpose_mul, transpose_transpose, Matrix.mul_assoc] using
        congrArg Matrix.transpose h
    rw [← he, ← Matrix.mul_assoc N, h, Matrix.zero_mul]
  · intro h
    rw [pinv_eq_gramPinv_mul_transpose, transpose_mul, transpose_transpose, ← Matrix.mul_assoc N,
      h, Matrix.zero_mul]

private theorem generalizedBLUE_eq_naive_iff_transposed_correction_zero
    (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    generalizedBLUE X V = X.pinv ↔
      ((V * observationResidualProjector X).pinv * V) * X.pinvᵀ = 0 := by
  rw [generalizedBLUE_eq_transpose X V hV,
    transpose_sub, transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_self]
  constructor
  · intro h
    simpa only [transpose_mul, transpose_transpose, transpose_zero] using
      congrArg Matrix.transpose h
  · intro h
    simpa only [transpose_mul, transpose_transpose, transpose_zero] using
      congrArg Matrix.transpose h

/-- **Equation (41)** of [benIsrael2003generalized], Chapter 8. The two
coefficients agree precisely when the correction vanishes on the column
space projector of the design. -/
theorem generalizedBLUE_eq_naive_iff_equation_41
    (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    generalizedBLUE X V = X.pinv ↔
      ((V * observationResidualProjector X).pinv * V) * (X * X.pinv) = 0 := by
  let P := X * X.pinv
  let C := (V * observationResidualProjector X).pinv * V
  have hP : X.pinvᵀ * Xᵀ = P := by
    change X.pinvᵀ * Xᵀ = X * X.pinv
    rw [← transpose_mul, mul_pinv_transpose]
  have hPX : P * X.pinvᵀ = X.pinvᵀ := by
    have h : X.pinv * P = X.pinv := by
      change X.pinv * (X * X.pinv) = X.pinv
      rw [← Matrix.mul_assoc, X.pinv_mul_self_mul_pinv]
    have ht := congrArg Matrix.transpose h
    rwa [transpose_mul, show Pᵀ = P from mul_pinv_transpose X] at ht
  rw [generalizedBLUE_eq_naive_iff_transposed_correction_zero X V hV]
  change C * X.pinvᵀ = 0 ↔ C * P = 0
  exact ⟨fun h => by rw [← hP, ← Matrix.mul_assoc, h, Matrix.zero_mul],
    fun h => by rw [← hPX, ← Matrix.mul_assoc, h, Matrix.zero_mul]⟩

/-- **Exercise 8**, Equation (41) of [benIsrael2003generalized], Chapter 8.
The generalized coefficient equals the least-squares coefficient exactly
when the covariance preserves the column space of the design. -/
theorem exercise_8_8 (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V) :
    generalizedBLUE X V = X.pinv ↔ ((V * V) * X).mulVecLin.range ≤ X.mulVecLin.range := by
  let Q := observationResidualProjector X
  let W := V * Q
  have hW : Wᵀ = Q * V := by
    change (V * Q)ᵀ = Q * V
    rw [transpose_mul, show Qᵀ = Q from residual_transpose X, hV]
  have h0 : generalizedBLUE X V = X.pinv ↔ (W.pinv * V) * X.pinvᵀ = 0 :=
    generalizedBLUE_eq_naive_iff_transposed_correction_zero X V hV
  have h1 : (W.pinv * V) * X.pinvᵀ = 0 ↔ Q * ((V * V) * X) = 0 := by
    rw [Matrix.mul_assoc W.pinv, pinv_mul_eq_zero_iff_transpose_mul_eq_zero, hW,
      ← Matrix.mul_assoc (Q * V), ← Matrix.mul_assoc Q,
      mul_pinvTranspose_eq_zero_iff_mul_self_eq_zero]
    simp only [Matrix.mul_assoc]
  rw [h0, h1]
  constructor
  · intro h y hy
    obtain ⟨b, rfl⟩ := hy
    have h' : (1 - X * X.pinv) * ((V * V) * X) = 0 := h
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h'
    exact ⟨X.pinv *ᵥ (((V * V) * X) *ᵥ b), by
      change X *ᵥ (X.pinv *ᵥ (((V * V) * X) *ᵥ b)) = ((V * V) * X) *ᵥ b
      rw [mulVec_mulVec, mulVec_mulVec, ← h']⟩
  · intro h
    apply ext_iff_mulVec.mpr
    intro b
    obtain ⟨z, hz⟩ := h (LinearMap.mem_range_self (((V * V) * X).mulVecLin) b)
    change X *ᵥ z = ((V * V) * X) *ᵥ b at hz
    rw [← mulVec_mulVec, ← hz, mulVec_mulVec, show Q * X = 0 from residual_mul_design X,
      zero_mulVec, zero_mulVec]

end BLUEFamilies

section ConstrainedModels

variable {Ω n p m k : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype n] [Fintype p] [Fintype k]

omit [IsProbabilityMeasure μ] in
private theorem affine_coefficients_on_fiber_iff
    (C : Matrix k p ℝ) (c : k → ℝ) (D : Matrix m p ℝ) (a : m → ℝ)
    (hc : ∃ β, C *ᵥ β = c) :
    (∀ β, C *ᵥ β = c → D *ᵥ β = -a) ↔
      ∃ L : Matrix m k ℝ, D = L * C ∧ a = -(L *ᵥ c) := by
  classical
  obtain ⟨β₀, hβ₀⟩ := hc
  constructor
  · intro h
    have hker (u : p → ℝ) (hu : C *ᵥ u = 0) : D *ᵥ u = 0 := by
      have hu' : C *ᵥ (β₀ + u) = c := by rw [mulVec_add, hβ₀, hu, add_zero]
      have he := h (β₀ + u) hu'
      rw [mulVec_add, h β₀ hβ₀, add_eq_left] at he
      exact he
    let L := D * C.pinv
    have hF : D = L * C := by
      apply ext_iff_mulVec.mpr
      intro β
      have hu : C *ᵥ (β - C.pinv *ᵥ (C *ᵥ β)) = 0 := by
        rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, C.mul_pinv_mul_self, sub_self]
      have hz := hker (β - C.pinv *ᵥ (C *ᵥ β)) hu
      rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, sub_eq_zero] at hz
      exact hz
    refine ⟨L, hF, ?_⟩
    have h0 := h β₀ hβ₀
    rw [hF, ← mulVec_mulVec, hβ₀] at h0
    calc
      a = -(-a) := (neg_neg a).symm
      _ = -(L *ᵥ c) := congrArg Neg.neg h0.symm
  · rintro ⟨L, hD, ha⟩ β hb
    rw [hD, ← mulVec_mulVec, hb, ha, neg_neg]

/-- **Exercise 4**, Equations (37)–(38) of [benIsrael2003generalized], Chapter 8.
An affine estimator is unbiased on the nonempty parameter fiber exactly
when its coefficient discrepancy factors through the constraint matrix and
its constant term cancels the resulting value on the fiber. -/
theorem exercise_8_4
    {X : Matrix n p ℝ} {S : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X S Y)
    (C : Matrix k p ℝ) (c : k → ℝ) (hc : ∃ β, C *ᵥ β = c)
    (A : Matrix m n ℝ) (B : Matrix m p ℝ) (a : m → ℝ) :
    (∀ β, C *ᵥ β = c → expectationVector μ (fun ω => A *ᵥ Y β ω + a) = B *ᵥ β) ↔
      ∃ L : Matrix m k ℝ, A * X - B = L * C ∧ a = -(L *ᵥ c) := by
  rw [← affine_coefficients_on_fiber_iff C c (A * X - B) a hc]
  refine forall_congr' fun β => imp_congr_right fun _ => ?_
  rw [(exercise_8_1 hY A a β).1, sub_mulVec]
  exact ⟨fun h => by rw [← h]; abel,
    fun h => by rw [← sub_eq_zero, add_sub_right_comm, h, neg_add_cancel]⟩

omit [IsProbabilityMeasure μ] [Fintype k] in
private theorem pinv_mul_design_mulVec_eq_self_of_null_constraints [DecidableEq p]
    (X : Matrix n p ℝ) (C : Matrix k p ℝ)
    (hC : Submodule.span ℝ (Set.range C.row) = X.mulVecLin.ker) {β : p → ℝ}
    (hβ : C *ᵥ β = 0) : (X.pinv * X) *ᵥ β = β := by
  let K := 1 - X.pinv * X
  have hXK : X * K = 0 := by
    dsimp only [K]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, X.mul_pinv_mul_self, sub_self]
  have hKs : Kᵀ = K := by
    simp only [K, transpose_sub, transpose_one, pinv_mul_transpose]
  have hKK : K * K = K := by
    have h1 : (X.pinv * X) * K = 0 := by
      rw [Matrix.mul_assoc, hXK, Matrix.mul_zero]
    change (1 - X.pinv * X) * K = K
    rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_zero]
  have hK : K *ᵥ β ∈ Submodule.span ℝ (Set.range C.row) := by
    rw [hC, LinearMap.mem_ker]
    change X *ᵥ (K *ᵥ β) = 0
    rw [mulVec_mulVec, hXK, zero_mulVec]
  have hdot : ∀ v ∈ Submodule.span ℝ (Set.range C.row), v ⬝ᵥ β = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact congrFun hβ i
    | zero => rw [zero_dotProduct]
    | add x y hx hy hx0 hy0 => rw [add_dotProduct, hx0, hy0, add_zero]
    | smul t x hx hx0 => rw [smul_dotProduct, hx0, smul_zero]
  have hK0 : K *ᵥ β = 0 := by
    apply dotProduct_self_eq_zero.mp
    rw [dotProduct_mulVec, ← vecMul_transpose K β, hKs, vecMul_vecMul, hKK, ← hKs, vecMul_transpose]
    exact hdot _ hK
  change (1 - X.pinv * X) *ᵥ β = 0 at hK0
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hK0
  exact hK0.symm

omit [Fintype k] in
/-- **Exercise 3**, Equation (36) of [benIsrael2003generalized], Chapter 8.
If the constraint rows span the design null space, every linear target
is estimable on the constrained parameter space. -/
theorem exercise_8_3 [DecidableEq p]
    {X : Matrix n p ℝ} {S : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X S Y)
    (C : Matrix k p ℝ) (hC : Submodule.span ℝ (Set.range C.row) = X.mulVecLin.ker)
    (B : Matrix m p ℝ) :
    ∀ β, C *ᵥ β = 0 → expectationVector μ (fun ω => (B * X.pinv) *ᵥ Y β ω) = B *ᵥ β := by
  intro β hβ
  rw [expectationVector_mulVec, hY.mean, mulVec_mulVec, Matrix.mul_assoc,
    ← mulVec_mulVec, pinv_mul_design_mulVec_eq_self_of_null_constraints X C hC hβ]
  exact hY.memLp β

end ConstrainedModels

section Whitening

variable {Ω n p : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The covariance matrix of a square-integrable random vector is positive
semidefinite. Its quadratic forms are variances of linear functionals. -/
theorem covarianceMatrix_posSemidef [Finite n] (Y : Ω → n → ℝ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ) : (covarianceMatrix μ Y).PosSemidef := by
  let := Fintype.ofFinite n
  apply posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · change (covarianceMatrix μ Y)ᴴ = covarianceMatrix μ Y
    rw [conjTranspose_eq_transpose_of_trivial]
    ext i j
    change ProbabilityTheory.covariance (fun ω => Y ω j) (fun ω => Y ω i) μ =
      ProbabilityTheory.covariance (fun ω => Y ω i) (fun ω => Y ω j) μ
    exact covariance_comm _ _
  · intro x
    let A := replicateRow Unit x
    have h : 0 ≤ covarianceMatrix μ (fun ω => A *ᵥ Y ω) () () := by
      change 0 ≤ ProbabilityTheory.covariance (fun ω => (A *ᵥ Y ω) ())
        (fun ω => (A *ᵥ Y ω) ()) μ
      rw [covariance_self (memLp_mulVec_coordinate A Y hY ()).aemeasurable]
      exact variance_nonneg _ _
    rw [covarianceMatrix_mulVec A Y hY, Matrix.mul_assoc] at h
    have hEntry : (A * (covarianceMatrix μ Y * Aᵀ)) () () =
        x ⬝ᵥ (covarianceMatrix μ Y *ᵥ x) := rfl
    rw [star_trivial, ← hEntry]
    exact h

variable [Fintype n]

/-- **Exercise 6** of [benIsrael2003generalized], Chapter 8.
An orthogonal eigenbasis and a nonsingular rescaling whiten the nonzero
covariance components. The spectral support labels the identity block
and its complement labels the zero block. -/
theorem covariance_whitening_factor [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S.PosSemidef) :
    ∃ (U : Matrix n n ℝ) (d : n → ℝ) (T : Matrix n n ℝ),
      Uᵀ * U = 1 ∧ Uᵀ * S * U = diagonal d ∧ (∀ i, 0 ≤ d i) ∧
      S.rank = Fintype.card {i // d i ≠ 0} ∧
      T = diagonal (fun i => if d i = 0 then 1 else (Real.sqrt (d i))⁻¹) * Uᵀ ∧
      IsUnit T ∧ T * S * Tᵀ = diagonal (fun i => if d i = 0 then 0 else 1) := by
  let u := hS.isHermitian.eigenvectorUnitary
  let U : Matrix n n ℝ := u
  let d := hS.isHermitian.eigenvalues
  let g (i : n) := if d i = 0 then 1 else (Real.sqrt (d i))⁻¹
  let D := diagonal g
  let T := D * Uᵀ
  have hU : Uᵀ * U = 1 := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self u
  have hD : Uᵀ * S * U = diagonal d := by
    simpa only [Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp] using
      hS.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hd : ∀ i, 0 ≤ d i := hS.eigenvalues_nonneg
  have hUu : IsUnit U.det := isUnit_det_of_left_inverse hU
  have hUTu : IsUnit Uᵀ.det := isUnit_det_of_right_inverse hU
  have hr := congrArg Matrix.rank hD
  rw [rank_mul_eq_left_of_isUnit_det U _ hUu, rank_mul_eq_right_of_isUnit_det Uᵀ _ hUTu,
    rank_diagonal] at hr
  have hdg (i : n) : g i ≠ 0 := by
    by_cases hi : d i = 0
    · simp [g, hi]
    · exact by
        simp [g, hi, (Real.sqrt_pos.2 (lt_of_le_of_ne (hd i) (Ne.symm hi))).ne']
  have hDu : IsUnit D := Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i =>
    isUnit_iff_ne_zero.mpr (hdg i))
  refine ⟨U, d, T, hU, hD, hd, hr, rfl, hDu.mul ((isUnit_iff_isUnit_det Uᵀ).mpr hUTu), ?_⟩
  change D * Uᵀ * S * (D * Uᵀ)ᵀ = _
  have hDt : Dᵀ = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp [D, hij, Ne.symm hij]
  rw [transpose_mul, transpose_transpose, hDt]
  calc
    D * Uᵀ * S * (U * D) = D * (Uᵀ * S * U) * D := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hD, show D = diagonal g from rfl, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : d i = 0
      · simp [g, hi]
      · have hsq : Real.sqrt (d i) * Real.sqrt (d i) = d i := by
          rw [← sq, Real.sq_sqrt (hd i)]
        change g i * d i * g i = _
        simp only [g, ite_eq_right hi]
        have hz := (Real.sqrt_pos.2 (lt_of_le_of_ne (hd i) (Ne.symm hi))).ne'
        calc
          _ = (Real.sqrt (d i))⁻¹ * (Real.sqrt (d i) * Real.sqrt (d i)) *
              (Real.sqrt (d i))⁻¹ := by rw [hsq]
          _ = 1 := by rw [← mul_assoc (Real.sqrt (d i))⁻¹, inv_mul_cancel₀ hz, one_mul,
            mul_inv_cancel₀ hz]

/-- **Exercise 6**, Equation (40) of [benIsrael2003generalized], Chapter 8.
An invertible observation transformation produces a model with diagonal
covariance equal to the identity on the nonzero spectral support. -/
theorem exercise_8_6 [Fintype p] [DecidableEq n]
    {X : Matrix n p ℝ} {S : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X S Y) :
    ∃ (U : Matrix n n ℝ) (d : n → ℝ) (T : Matrix n n ℝ),
      Uᵀ * U = 1 ∧ Uᵀ * S * U = diagonal d ∧ (∀ i, 0 ≤ d i) ∧
      S.rank = Fintype.card {i // d i ≠ 0} ∧
      T = diagonal (fun i => if d i = 0 then 1 else (Real.sqrt (d i))⁻¹) * Uᵀ ∧
      IsUnit T ∧
      IsLinearStatisticalModel μ (T * X) (diagonal (fun i => if d i = 0 then 0 else 1))
        (fun β ω => T *ᵥ Y β ω) := by
  have hS := covarianceMatrix_posSemidef (Y 0) (hY.memLp 0)
  rw [hY.covariance] at hS
  obtain ⟨U, d, T, hu, hd, hnonneg, hr, htd, ht, hCov⟩ := covariance_whitening_factor hS
  refine ⟨U, d, T, hu, hd, hnonneg, hr, htd, ht, ?_⟩
  refine ⟨fun β i => memLp_mulVec_coordinate T (Y β) (hY.memLp β) i, ?_, ?_⟩
  · intro β
    rw [expectationVector_mulVec T (Y β) (hY.memLp β), hY.mean, mulVec_mulVec]
  · intro β
    rw [covarianceMatrix_mulVec T (Y β) (hY.memLp β), hY.covariance, hCov]


/-- **Exercise 7**, Equation (40b) of [benIsrael2003generalized], Chapter 8.
The rows of the orthogonal transform indexed by zero eigenvalues give
the deterministic part of the observation. -/
theorem exercise_8_7_spectral [Fintype p] [DecidableEq n]
    {X : Matrix n p ℝ} {S U : Matrix n n ℝ} {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X S Y) (d : n → ℝ)
    (hU : Uᵀ * U = 1) (hD : Uᵀ * S * U = diagonal d) (β : p → ℝ) :
    let A := Uᵀ.submatrix (fun i : {i // d i = 0} => i.1) id
    (fun ω => A *ᵥ Y β ω) =ᵐ[μ] fun _ => (A * X) *ᵥ β := by
  intro A
  have hu : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hUS : Uᵀ * S = diagonal d * Uᵀ := calc
    _ = (Uᵀ * S) * (U * Uᵀ) := by rw [hu, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hD]
  apply exercise_8_7 hY ?_ β
  ext i j
  change (Uᵀ * S) i.1 j = 0
  rw [hUS, diagonal_mul, i.2, zero_mul]

/-- **Exercise 7** of [benIsrael2003generalized], Chapter 8.
The zero-eigenvalue columns of the orthogonal transform form a basis of
the covariance kernel. -/
theorem exercise_8_7_spectral_kernel_basis [DecidableEq n]
    {S U : Matrix n n ℝ} (d : n → ℝ) (hU : Uᵀ * U = 1)
    (hD : Uᵀ * S * U = diagonal d) :
    let cols := fun i : {i // d i = 0} => U.col i.1
    LinearIndependent ℝ cols ∧ Submodule.span ℝ (Set.range cols) = S.mulVecLin.ker := by
  intro cols
  have hu : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hSU : S * U = U * diagonal d := by
    rw [← hD, ← Matrix.mul_assoc U, ← Matrix.mul_assoc U, hu, Matrix.one_mul]
  have hUS : Uᵀ * S = diagonal d * Uᵀ := by
    rw [← hD, Matrix.mul_assoc (Uᵀ * S), hu, Matrix.mul_one]
  have hUcols : LinearIndependent ℝ U.col := Matrix.mulVec_injective_iff.mp (by
    intro x y hxy
    have h := congrArg Uᵀ.mulVec hxy
    simpa only [mulVec_mulVec, hU, one_mulVec] using h)
  refine ⟨hUcols.comp Subtype.val Subtype.val_injective, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change S *ᵥ U.col i.1 = 0
    rw [← mulVec_single_one, mulVec_mulVec, hSU, ← mulVec_mulVec]
    have hd : diagonal d *ᵥ Pi.single i.1 1 = 0 := by
      ext j
      rw [mulVec_diagonal]
      by_cases hj : j = i.1
      · simp [hj, i.2]
      · simp [Pi.single_eq_of_ne hj]
    rw [hd, mulVec_zero]
  · intro x hx
    change S *ᵥ x = 0 at hx
    let z := Uᵀ *ᵥ x
    have hdz : diagonal d *ᵥ z = 0 := by
      rw [show z = Uᵀ *ᵥ x from rfl, mulVec_mulVec, ← hUS, ← mulVec_mulVec, hx, mulVec_zero]
    have hxz : U *ᵥ z = x := by
      rw [show z = Uᵀ *ᵥ x from rfl, mulVec_mulVec, hu, one_mulVec]
    have hsum : U *ᵥ z = ∑ i, z i • U.col i := by
      funext j
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col_apply]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [← hxz, hsum]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : d i = 0
    · have hm : U.col i ∈ Set.range cols := ⟨⟨i, hi⟩, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
    · have hz : z i = 0 := by
        have h := congrFun hdz i
        rw [mulVec_diagonal] at h
        exact (mul_eq_zero.mp h).resolve_left hi
      rw [hz, zero_smul]
      exact Submodule.zero_mem _

/-- **Exercise 7**, Equations (40a)–(40b) of [benIsrael2003generalized],
Chapter 8. The whitened observation splits into a scaled part on the
positive spectral support and an unscaled part on the zero eigenspace. -/
theorem exercise_8_7_spectral_error_blocks [Fintype p]
    (X : Matrix n p ℝ) (U : Matrix n n ℝ) (d : n → ℝ)
    (y ε : n → ℝ) (β : p → ℝ) (hy : y = X *ᵥ β + ε) :
    let A := Matrix.of fun (i : {i // d i ≠ 0}) (j : n) =>
      (Real.sqrt (d i.1))⁻¹ * Uᵀ i.1 j
    let B := Uᵀ.submatrix (fun i : {i // d i = 0} => i.1) id
    A *ᵥ y = (A * X) *ᵥ β + A *ᵥ ε ∧ B *ᵥ y = (B * X) *ᵥ β + B *ᵥ ε := by
  intro A B
  simp only [hy, mulVec_add, mulVec_mulVec, and_self]

end Whitening

section Aitken

variable {n p k : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

omit [DecidableEq p] in
/-- **Equation (39)** of [benIsrael2003generalized], Chapter 8.
The weighted residual sum of squares with covariance matrix `S`. -/
noncomputable def weightedSquaredResidual (S : Matrix n n ℝ) (X : Matrix n p ℝ)
    (y : n → ℝ) (β : p → ℝ) : ℝ :=
  let r := X *ᵥ β - y
  r ⬝ᵥ (S⁻¹ *ᵥ r)

/-- **Exercise 5**, Equation (39) of [benIsrael2003generalized], Chapter 8.
With full column rank and nonsingular covariance, the BLUE coefficient
applied to the data is the unique minimizer of the weighted residual. -/
theorem exercise_8_5 (X : Matrix n p ℝ) (V : Matrix n n ℝ) (hV : Vᵀ = V)
    (hu : IsUnit V) (hX : X.rank = Fintype.card p) (y : n → ℝ) (β : p → ℝ) :
    (∀ γ, weightedSquaredResidual (V * V) X y β ≤ weightedSquaredResidual (V * V) X y γ) ↔
      β = generalizedBLUE X V *ᵥ y := by
  let J := V⁻¹ * X
  let z : EuclideanSpace ℝ n := WithLp.toLp 2 (V⁻¹ *ᵥ y)
  have hvd := (isUnit_iff_isUnit_det V).mp hu
  have hi := V.mul_nonsing_inv hvd
  have hS : (V * V)⁻¹ = V⁻¹ * V⁻¹ := by
    apply inv_eq_right_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V V⁻¹, hi, Matrix.one_mul, hi]
  have hiT : (V⁻¹)ᵀ = V⁻¹ := by rw [transpose_nonsing_inv, hV]
  have hW (γ : p → ℝ) : weightedSquaredResidual (V * V) X y γ =
      ‖J.toEuclideanLin (WithLp.toLp 2 γ) - z‖ ^ 2 := by
    let r := X *ᵥ γ - y
    have hLp : J.toEuclideanLin (WithLp.toLp 2 γ) - z =
        (WithLp.toLp 2 (V⁻¹ *ᵥ r) : EuclideanSpace ℝ n) := by
      rw [toEuclideanLin_toLp]
      change WithLp.toLp 2 ((V⁻¹ * X) *ᵥ γ) - WithLp.toLp 2 (V⁻¹ *ᵥ y) = _
      rw [show V⁻¹ *ᵥ r = V⁻¹ *ᵥ (X *ᵥ γ - y) from rfl, mulVec_sub, mulVec_mulVec]
      rfl
    rw [hLp, EuclideanSpace.real_norm_sq_eq]
    change r ⬝ᵥ ((V * V)⁻¹ *ᵥ r) = ∑ i, ((V⁻¹ *ᵥ r) i) ^ 2
    rw [hS, ← mulVec_mulVec, ← hiT, dotProduct_transpose_mulVec]
    simp only [hiT, dotProduct, pow_two]
  have hJ : J.rank = Fintype.card p := by
    change (V⁻¹ * X).rank = _
    rw [rank_mul_eq_right_of_isUnit_det V⁻¹ X (isUnit_nonsing_inv_det V hvd), hX]
  have hJL := pinv_mul_design_of_full_rank J hJ
  have hInd : LinearIndependent ℝ Jᵀ := by
    change LinearIndependent ℝ J.col
    apply mulVec_injective_iff.mp
    intro x x' hx
    have he := congrArg (J.pinv *ᵥ ·) hx
    simpa only [mulVec_mulVec, hJL, one_mulVec] using he
  have hobj :
      (∀ γ, weightedSquaredResidual (V * V) X y β ≤ weightedSquaredResidual (V * V) X y γ) ↔
        IsLeastSquaresSolution J z (WithLp.toLp 2 β) := by
    rw [isLeastSquaresSolution_iff]
    constructor
    · intro h γ
      have he := h γ.ofLp
      rw [hW, hW, WithLp.toLp_ofLp] at he
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
    · intro h γ
      rw [hW, hW]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h (WithLp.toLp 2 γ))
  rw [hobj, isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent hInd]
  have hC : J.pinv.toEuclideanLin z =
      (WithLp.toLp 2 (generalizedBLUE X V *ᵥ y) : EuclideanSpace ℝ p) := by
    change J.pinv.toEuclideanLin (WithLp.toLp 2 (V⁻¹ *ᵥ y)) = _
    rw [toEuclideanLin_toLp, mulVec_mulVec, ← generalizedBLUE_eq_whitened X V hV hu]
  rw [hC]
  exact ⟨fun h => congrArg WithLp.ofLp h, fun h => congrArg (WithLp.toLp 2) h⟩

omit [DecidableEq p] in
/-- **Exercise 5** of [benIsrael2003generalized], Chapter 8, factorized form.
For each parameter the smallest squared norm of a feasible error vector
equals the weighted residual objective. -/
theorem exercise_8_5_factored [Fintype k]
    {S : Matrix n n ℝ} (hS : IsUnit S) (C : Matrix n k ℝ) (hC : S = C * Cᵀ)
    (X : Matrix n p ℝ) (y : n → ℝ) (β : p → ℝ) :
    let u₀ := Cᵀ *ᵥ (S⁻¹ *ᵥ (y - X *ᵥ β))
    X *ᵥ β + C *ᵥ u₀ = y ∧ weightedSquaredResidual S X y β = u₀ ⬝ᵥ u₀ ∧
      ∀ u, X *ᵥ β + C *ᵥ u = y → u₀ ⬝ᵥ u₀ ≤ u ⬝ᵥ u := by
  intro u₀
  let r := y - X *ᵥ β
  let v := S⁻¹ *ᵥ r
  have hCv : C *ᵥ u₀ = r := by
    change C *ᵥ (Cᵀ *ᵥ (S⁻¹ *ᵥ r)) = r
    rw [mulVec_mulVec, ← hC, mulVec_mulVec,
      S.mul_nonsing_inv ((isUnit_iff_isUnit_det S).mp hS), one_mulVec]
  have hFeas : X *ᵥ β + C *ᵥ u₀ = y := by rw [hCv]; dsimp only [r]; abel
  refine ⟨hFeas, ?_, ?_⟩
  · have hN : u₀ ⬝ᵥ u₀ = v ⬝ᵥ r := by
      change u₀ ⬝ᵥ (Cᵀ *ᵥ v) = _
      rw [dotProduct_transpose_mulVec, hCv]
    rw [hN]
    change (X *ᵥ β - y) ⬝ᵥ (S⁻¹ *ᵥ (X *ᵥ β - y)) = (S⁻¹ *ᵥ r) ⬝ᵥ r
    rw [show X *ᵥ β - y = -r from by dsimp only [r]; abel, mulVec_neg, neg_dotProduct,
      dotProduct_neg, neg_neg, dotProduct_comm]
  · intro u hu
    let d := u - u₀
    have hCd : C *ᵥ d = 0 := by
      rw [show d = u - u₀ from rfl, mulVec_sub, add_left_cancel (hu.trans hFeas.symm), sub_self]
    have hdu : d ⬝ᵥ u₀ = 0 := by
      change d ⬝ᵥ (Cᵀ *ᵥ v) = 0
      rw [dotProduct_transpose_mulVec, hCd, dotProduct_zero]
    have hud : u₀ ⬝ᵥ d = 0 := by rw [dotProduct_comm, hdu]
    have he : u₀ + d = u := by dsimp only [d]; abel
    calc
      u₀ ⬝ᵥ u₀ ≤ u₀ ⬝ᵥ u₀ + d ⬝ᵥ d := le_add_of_nonneg_right
        (Finset.sum_nonneg fun i _ => mul_self_nonneg (d i))
      _ = (u₀ + d) ⬝ᵥ (u₀ + d) := by
        rw [add_dotProduct, dotProduct_add, dotProduct_add, hdu, hud, add_zero, zero_add]
      _ = _ := by rw [he]

end Aitken

end BenIsraelGreville.Chapter08
