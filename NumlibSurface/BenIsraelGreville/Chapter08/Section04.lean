/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import NumlibSurface.BenIsraelGreville.Chapter08.Section03
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Ridge regression

Section 8.4 of [benIsrael2003generalized] uses the singular coordinates of
a real design matrix to compute the mean squared error of ridge regression
and compare it with that of the least-squares estimator.

## Deviations from the source

* **Equations (44)–(46)** use the orthogonality of the left singular factor
  for the distribution of the rotated error.
* **Theorem 3** assumes positive noise variance and a nonempty parameter space.
  Both conditions are necessary for strict improvement.
* **Exercise 11** distinguishes a diagonal penalty in the original coordinates
  from a diagonal penalty in the right singular basis. The coordinatewise
  minimizer with a positive finite penalty assumes nonzero signal in that
  coordinate and positive variance.
* **Exercise 12** uses strict decrease of the positive shrinkage coefficients.
  Weak monotonicity allows the unchanged least-squares coefficients.
-/

namespace BenIsraelGreville.Chapter08

open Matrix
open scoped BigOperators

section Ridge

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq p]

/-- **Equation (48)** of [benIsrael2003generalized], Chapter 8.
The ridge estimator applies the Tikhonov coefficient to the observations.
The parameter is positive for ridge regression and zero at the full-rank
least-squares endpoint. -/
noncomputable def ridgeEstimator (X : Matrix n p ℝ) (k : ℝ) (y : n → ℝ) : p → ℝ :=
  X.tikhonov k *ᵥ y

/-- **Equation (48)** of [benIsrael2003generalized], Chapter 8.
The matrix formula for the ridge estimator in the original coordinates. -/
theorem ridgeEstimator_eq (X : Matrix n p ℝ) (k : ℝ) (y : n → ℝ) :
    ridgeEstimator X k y = ((Xᵀ * X + k • (1 : Matrix p p ℝ))⁻¹ * Xᵀ) *ᵥ y := by
  rw [ridgeEstimator, tikhonov_def, conjTranspose_eq_transpose_of_trivial, add_comm]
  rfl

private theorem ridgeCoefficient_zero (X : Matrix n p ℝ) (hX : X.rank = Fintype.card p) :
    X.tikhonov 0 = X.pinv := by
  rw [tikhonov_def, RCLike.ofReal_zero, zero_smul, zero_add,
    conjTranspose_eq_transpose_of_trivial, pinv_eq_normalEquations_coefficient X hX]

/-- **Equations (18) and (48)** of [benIsrael2003generalized], Chapter 8.
At zero regularization a full-column-rank design gives the ordinary
least-squares estimator. -/
theorem ridgeEstimator_zero (X : Matrix n p ℝ) (hX : X.rank = Fintype.card p) (y : n → ℝ) :
    ridgeEstimator X 0 y = X.pinv *ᵥ y := by
  rw [ridgeEstimator, ridgeCoefficient_zero X hX]

/-- **Equation (50)** of [benIsrael2003generalized], Chapter 8.
The ridge coefficient that multiplies an observation in a singular direction. -/
noncomputable def ridgeShrinkageFactor (s k : ℝ) : ℝ := s / (s ^ 2 + k)

/-- At the least-squares endpoint the coefficient is the reciprocal singular value. -/
theorem ridgeShrinkageFactor_zero (s : ℝ) : ridgeShrinkageFactor s 0 = s⁻¹ := by
  by_cases h : s = 0
  · simp [ridgeShrinkageFactor, h]
  · unfold ridgeShrinkageFactor
    rw [add_zero, pow_two]
    field_simp

end Ridge

section SingularCoordinates

variable {n p : ℕ}
variable {X : Matrix (Fin n) (Fin p) ℝ} {U : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin p) (Fin p) ℝ} {s : ℕ → ℝ}

private theorem parameterCount_le (hX : X.rank = p) : p ≤ n := by
  simpa only [hX, Fintype.card_fin] using X.rank_le_card_height

/-- **Equation (43)** of [benIsrael2003generalized], Chapter 8.
Full column rank makes the singular value in each parameter direction positive. -/
theorem positive_singularValues_of_full_column_rank (hS : IsSVD X U s V)
    (hX : X.rank = p) (i : Fin p) : 0 < s i := by
  have hs := hS.singularValues_eq (i.isLt.trans_le (parameterCount_le hX)) i.isLt
  rw [hs]
  refine lt_of_le_of_ne (X.sortedSingularValues_nonneg _) ?_
  intro hz
  have hle := (X.sortedSingularValues_eq_zero_iff_rank_le i).mp hz.symm
  rw [hX] at hle
  exact (not_le.mpr i.isLt) hle

/-- **Equations (48)–(50)** of [benIsrael2003generalized], Chapter 8.
The ridge coefficient is diagonal between the left and right singular bases,
including at zero regularization for a full-column-rank design. -/
theorem ridgeCoefficient_svd (hS : IsSVD X U s V) (hX : X.rank = p) {k : ℝ} (hk : 0 ≤ k) :
    X.tikhonov k = V *
      (rectDiagonal (fun i => ridgeShrinkageFactor (s i) k) : Matrix (Fin p) (Fin n) ℝ) * Uᵀ := by
  rcases eq_or_lt_of_le hk with hEq | hPos
  · subst k
    rw [ridgeCoefficient_zero X (by simpa only [Fintype.card_fin] using hX)]
    simpa only [ridgeShrinkageFactor_zero, RCLike.ofReal_real_eq_id, id_eq,
      star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hS.pinv_eq
  · simpa only [ridgeShrinkageFactor, RCLike.ofReal_real_eq_id, id_eq, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using hS.tikhonov_eq hPos

/-- **Equations (44), (49.i), and (50)** of [benIsrael2003generalized], Chapter 8.
The coordinate of the ridge estimate is its corresponding singular-coordinate
observation multiplied by the ridge shrinkage coefficient. -/
theorem ridgeEstimator_svd (hS : IsSVD X U s V) (hX : X.rank = p) {k : ℝ} (hk : 0 ≤ k)
    (y : Fin n → ℝ) (i : Fin p) :
    (Vᵀ *ᵥ ridgeEstimator X k y) i =
      ridgeShrinkageFactor (s i) k * (Uᵀ *ᵥ y) (Fin.castLE (parameterCount_le hX) i) := by
  have hV : Vᵀ * V = 1 := mem_unitaryGroup_iff'.mp hS.mem_unitaryGroup_right
  rw [ridgeEstimator, mulVec_mulVec, ridgeCoefficient_svd hS hX hk,
    ← Matrix.mul_assoc Vᵀ, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, ← mulVec_mulVec]
  exact rectDiagonal_mulVec _ _ i (i.isLt.trans_le (parameterCount_le hX))

/-- **Equation (47a)** of [benIsrael2003generalized], Chapter 8.
In the singular basis the least-squares estimate divides each observation
by its corresponding positive singular value. -/
theorem ridgeBLUE_coordinate (hS : IsSVD X U s V) (hX : X.rank = p)
    (y : Fin n → ℝ) (i : Fin p) :
    (Vᵀ *ᵥ (X.pinv *ᵥ y)) i =
      (Uᵀ *ᵥ y) (Fin.castLE (parameterCount_le hX) i) / s i := by
  rw [← ridgeEstimator_zero X (by simpa only [Fintype.card_fin] using hX),
    ridgeEstimator_svd hS hX le_rfl,
    ridgeShrinkageFactor_zero, div_eq_mul_inv, mul_comm]

end SingularCoordinates

section Risk

/-- The scalar summand of **Equation (53)** of [benIsrael2003generalized], Chapter 8. -/
noncomputable def ridgeCoordinateRisk (s σ γ k : ℝ) : ℝ :=
  (s ^ 2 * σ ^ 2 + k ^ 2 * γ ^ 2) / (s ^ 2 + k) ^ 2

/-- **Equation (53)** of [benIsrael2003generalized], Chapter 8.
The risk is the sum of the risks in the parameter singular basis. -/
noncomputable def ridgeRisk {p : Type*} [Fintype p] (s : p → ℝ)
    (σ : ℝ) (γ : p → ℝ) (k : ℝ) : ℝ :=
  ∑ i, ridgeCoordinateRisk (s i) σ (γ i) k

/-- **Equation (54)** of [benIsrael2003generalized], Chapter 8,
for one singular coordinate. -/
theorem hasDerivAt_ridgeCoordinateRisk (s σ γ k : ℝ) (hk : s ^ 2 + k ≠ 0) :
    HasDerivAt (ridgeCoordinateRisk s σ γ)
      (2 * s ^ 2 * (k * γ ^ 2 - σ ^ 2) / (s ^ 2 + k) ^ 3) k := by
  have hn := (((hasDerivAt_id k).pow 2).mul_const (γ ^ 2)).const_add (s ^ 2 * σ ^ 2)
  have hd := (((hasDerivAt_id k).const_add (s ^ 2)).pow 2)
  convert hn.fun_div hd (pow_ne_zero 2 hk) using 1
  · funext j
    rfl
  · simp only [Pi.pow_apply, id_eq]
    norm_num
    field_simp
    ring

/-- **Equation (54)** of [benIsrael2003generalized], Chapter 8.
Differentiate the sum of coordinate risks. -/
theorem hasDerivAt_ridgeRisk {p : Type*} [Fintype p] (s : p → ℝ) (σ : ℝ)
    (γ : p → ℝ) (k : ℝ) (hk : ∀ i, s i ^ 2 + k ≠ 0) :
    HasDerivAt (ridgeRisk s σ γ)
      (∑ i, 2 * s i ^ 2 * (k * γ i ^ 2 - σ ^ 2) / (s i ^ 2 + k) ^ 3) k := by
  classical
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    hasDerivAt_ridgeCoordinateRisk (s i) σ (γ i) k (hk i)

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 8.
Every coordinate contributes a negative derivative at the least-squares endpoint
when the variance is positive and the singular values are positive. -/
theorem deriv_ridgeRisk_zero_neg {p : Type*} [Fintype p] [Nonempty p] {s : p → ℝ}
    (hs : ∀ i, 0 < s i) (σ : ℝ) (hσ : 0 < σ ^ 2) (γ : p → ℝ) :
    deriv (ridgeRisk s σ γ) 0 < 0 := by
  classical
  rw [(hasDerivAt_ridgeRisk s σ γ 0 (fun i => by have := hs i; positivity)).deriv]
  calc
    _ < ∑ _ : p, (0 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro i _
      simp only [zero_mul, zero_sub, add_zero]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (by have := hs i; positivity) (neg_lt_zero.mpr hσ))
        (by have := hs i; positivity)
    _ = _ := by simp

private theorem ridgeCoordinateRisk_zero {s σ γ : ℝ} (hs : s ≠ 0) :
    ridgeCoordinateRisk s σ γ 0 = σ ^ 2 / s ^ 2 := by
  unfold ridgeCoordinateRisk
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero]
  field_simp

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 8, coordinate estimate.
A positive penalty gives an improvement whenever its product with the squared
signal does not exceed the noise variance. -/
theorem ridgeCoordinateRisk_lt_zeroPenalty {s σ γ k : ℝ}
    (hs : 0 < s) (hσ : 0 < σ ^ 2) (hk : 0 < k) (hsmall : k * γ ^ 2 ≤ σ ^ 2) :
    ridgeCoordinateRisk s σ γ k < ridgeCoordinateRisk s σ γ 0 := by
  have ha : 0 < s ^ 2 := by positivity
  have hb : 0 < s ^ 2 + k := add_pos ha hk
  rw [ridgeCoordinateRisk_zero hs.ne']
  calc
    ridgeCoordinateRisk s σ γ k ≤ ((s ^ 2 + k) * σ ^ 2) / (s ^ 2 + k) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hsmall hk.le
      nlinarith
    _ = σ ^ 2 / (s ^ 2 + k) := by field_simp
    _ < σ ^ 2 / s ^ 2 := div_lt_div_of_pos_left hσ ha (by linarith)

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 8, singular-coordinate form.
A single positive penalty can improve every coordinate simultaneously. -/
theorem exists_positive_ridgeRisk_lt_zeroPenalty {p : Type*} [Fintype p] [Nonempty p]
    {s : p → ℝ} (hs : ∀ i, 0 < s i) (σ : ℝ) (hσ : 0 < σ ^ 2) (γ : p → ℝ) :
    ∃ k > 0, (∀ i, ridgeCoordinateRisk (s i) σ (γ i) k < ridgeCoordinateRisk (s i) σ (γ i) 0) ∧
      ridgeRisk s σ γ k < ridgeRisk s σ γ 0 := by
  classical
  let C := ∑ i, γ i ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hD : 0 < 1 + C := by linarith
  refine ⟨σ ^ 2 / (1 + C), div_pos hσ hD, ?_⟩
  have h i : ridgeCoordinateRisk (s i) σ (γ i) (σ ^ 2 / (1 + C)) <
      ridgeCoordinateRisk (s i) σ (γ i) 0 := by
    apply ridgeCoordinateRisk_lt_zeroPenalty (hs i) hσ (div_pos hσ hD)
    have hsum : γ i ^ 2 ≤ C := Finset.single_le_sum
      (f := fun j => γ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    exact mul_le_mul_of_nonneg_left (by linarith) hσ.le
  exact ⟨h, Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h i)⟩

end Risk

section MeanSquaredError

open MeasureTheory ProbabilityTheory

variable {Ω p : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- **Section 8.4** of [benIsrael2003generalized].
The bias of the estimator is its expected value minus the parameter. -/
noncomputable def estimatorBias (Z : Ω → p → ℝ) (β : p → ℝ) : p → ℝ :=
  expectationVector μ Z - β

/-- **Section 8.4** of [benIsrael2003generalized].
The mean squared error is the expected squared Euclidean distance to the parameter. -/
noncomputable def estimatorMeanSquaredError [Fintype p] (Z : Ω → p → ℝ) (β : p → ℝ) : ℝ :=
  ∫ ω, ∑ i, (Z ω i - β i) ^ 2 ∂μ

/-- The coordinate definition of the mean squared error is the expected squared norm. -/
theorem estimatorMeanSquaredError_eq_integral_norm_sq [Fintype p]
    (Z : Ω → p → ℝ) (β : p → ℝ) :
    estimatorMeanSquaredError μ Z β =
      ∫ ω, ‖(WithLp.toLp 2 (Z ω - β) : EuclideanSpace ℝ p)‖ ^ 2 ∂μ := by
  simp only [estimatorMeanSquaredError, EuclideanSpace.real_norm_sq_eq, Pi.sub_apply]

/-- A mean squared error is nonnegative. -/
theorem estimatorMeanSquaredError_nonneg [Fintype p] (Z : Ω → p → ℝ) (β : p → ℝ) :
    0 ≤ estimatorMeanSquaredError μ Z β :=
  integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Applying an orthogonal matrix to both arguments leaves the mean squared error unchanged. -/
theorem estimatorMeanSquaredError_orthogonal [Fintype p] [DecidableEq p]
    {Q : Matrix p p ℝ} (hQ : Q ∈ orthogonalGroup p ℝ)
    (Z : Ω → p → ℝ) (β : p → ℝ) :
    estimatorMeanSquaredError μ (fun ω => Q *ᵥ Z ω) (Q *ᵥ β) =
      estimatorMeanSquaredError μ Z β := by
  rw [estimatorMeanSquaredError_eq_integral_norm_sq, estimatorMeanSquaredError_eq_integral_norm_sq]
  congr with ω
  rw [← mulVec_sub, ← toEuclideanLin_toLp, norm_toEuclideanLin_apply_of_mem_unitaryGroup hQ]

variable {μ} [IsProbabilityMeasure μ]

private theorem expected_sq_error {W : Ω → ℝ} (hW : MemLp W 2 μ) (t : ℝ) :
    (∫ ω, (W ω - t) ^ 2 ∂μ) = variance W μ + ((∫ ω, W ω ∂μ) - t) ^ 2 := by
  have hv := variance_eq_sub (hW.sub (memLp_const t))
  change variance (fun ω => W ω - t) μ =
    (∫ ω, (W ω - t) ^ 2 ∂μ) - (∫ ω, W ω - t ∂μ) ^ 2 at hv
  rw [variance_sub_const hW.aestronglyMeasurable, integral_sub
    (hW.integrable (by norm_num)) (integrable_const t), integral_const] at hv
  simp only [probReal_univ, one_smul] at hv
  exact (eq_sub_iff_add_eq.mp hv).symm

private theorem integrable_sq_error {W : Ω → ℝ} (hW : MemLp W 2 μ) (t : ℝ) :
    Integrable (fun ω => (W ω - t) ^ 2) μ :=
  (hW.sub (memLp_const t)).integrable_sq

/-- **Exercise 10** of [benIsrael2003generalized], Chapter 8.
The mean squared error is the trace of the covariance plus the squared norm of the bias. -/
theorem exercise_8_10 [Fintype p] (Z : Ω → p → ℝ) (β : p → ℝ)
    (hZ : ∀ i, MemLp (fun ω => Z ω i) 2 μ) :
    estimatorMeanSquaredError μ Z β =
      (covarianceMatrix μ Z).trace +
        ‖(WithLp.toLp 2 (estimatorBias μ Z β) : EuclideanSpace ℝ p)‖ ^ 2 := by
  classical
  rw [estimatorMeanSquaredError, integral_finsetSum _
    (fun i _ => integrable_sq_error (hZ i) (β i)), Matrix.trace, EuclideanSpace.real_norm_sq_eq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [expected_sq_error (hZ i) (β i)]
  change variance (fun ω => Z ω i) μ + ((∫ ω, Z ω i ∂μ) - β i) ^ 2 =
    covariance (fun ω => Z ω i) (fun ω => Z ω i) μ +
      ((∫ ω, Z ω i ∂μ) - β i) ^ 2
  rw [covariance_self (hZ i).aemeasurable]

omit [IsProbabilityMeasure μ] in
private theorem memLp_estimator_coordinate {m : Type*} [Fintype p]
    (A : Matrix m p ℝ) {Z : Ω → p → ℝ} (hZ : ∀ i, MemLp (fun ω => Z ω i) 2 μ)
    (j : m) : MemLp (fun ω => (A *ᵥ Z ω) j) 2 μ := by
  change MemLp (fun ω => ∑ i, A j i * Z ω i) 2 μ
  exact memLp_finsetSum _ (fun i _ => (hZ i).const_mul _)

private theorem scalarShrinkage_moments {W : Ω → ℝ} (hW : MemLp W 2 μ) {s σ γ : ℝ}
    (hmean : (∫ ω, W ω ∂μ) = s * γ) (hvar : variance W μ = σ ^ 2) (c : ℝ) :
    (∫ ω, c * W ω ∂μ) - γ = (c * s - 1) * γ ∧
      variance (fun ω => c * W ω) μ = c ^ 2 * σ ^ 2 ∧
      (∫ ω, (c * W ω - γ) ^ 2 ∂μ) = c ^ 2 * σ ^ 2 + ((c * s - 1) * γ) ^ 2 := by
  have hm : (∫ ω, c * W ω ∂μ) - γ = (c * s - 1) * γ := by
    rw [integral_const_mul, hmean]
    ring
  have hv : variance (fun ω => c * W ω) μ = c ^ 2 * σ ^ 2 := by
    rw [variance_const_mul, hvar]
  exact ⟨hm, hv, by rw [expected_sq_error (hW.const_mul c) γ, hv, hm]⟩

private theorem scalarRidge_moments {W : Ω → ℝ} (hW : MemLp W 2 μ) {s σ γ k : ℝ}
    (hmean : (∫ ω, W ω ∂μ) = s * γ) (hvar : variance W μ = σ ^ 2)
    (hk : s ^ 2 + k ≠ 0) :
    (∫ ω, ridgeShrinkageFactor s k * W ω ∂μ) - γ = -k * γ / (s ^ 2 + k) ∧
      variance (fun ω => ridgeShrinkageFactor s k * W ω) μ =
        s ^ 2 * σ ^ 2 / (s ^ 2 + k) ^ 2 ∧
      (∫ ω, (ridgeShrinkageFactor s k * W ω - γ) ^ 2 ∂μ) =
        ridgeCoordinateRisk s σ γ k := by
  obtain ⟨hm, hv, hE⟩ := scalarShrinkage_moments hW hmean hvar (ridgeShrinkageFactor s k)
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, ridgeShrinkageFactor]
    field_simp
    ring
  · rw [hv, ridgeShrinkageFactor, div_pow]
    ring
  · rw [hE, ridgeShrinkageFactor, ridgeCoordinateRisk]
    field_simp
    ring

end MeanSquaredError

section StatisticalRidge

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n p : ℕ} {s : ℕ → ℝ}
  {X : Matrix (Fin n) (Fin p) ℝ} {U : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin p) (Fin p) ℝ} {Y : (Fin p → ℝ) → Ω → Fin n → ℝ}

private theorem svd_design_mulVec (hS : IsSVD X U s V) (β : Fin p → ℝ) :
    Uᵀ *ᵥ (X *ᵥ β) = rectDiagonal s *ᵥ (Vᵀ *ᵥ β) := by
  have hV : V * Vᵀ = 1 := mem_unitaryGroup_iff.mp hS.mem_unitaryGroup_right
  have hXV : Uᵀ * X * V = rectDiagonal s := hS.star_mul_mul
  rw [mulVec_mulVec, mulVec_mulVec, ← hXV, Matrix.mul_assoc (Uᵀ * X) V Vᵀ,
    hV, Matrix.mul_one]

/-- **Equations (44)–(45)** of [benIsrael2003generalized], Chapter 8.
The transformed observations satisfy the design equation in singular coordinates. -/
theorem ridge_svd_model_equation (hS : IsSVD X U s V)
    (β : Fin p → ℝ) (ε : Fin n → ℝ) :
    Uᵀ *ᵥ (X *ᵥ β + ε) =
      rectDiagonal s *ᵥ (Vᵀ *ᵥ β) + Uᵀ *ᵥ ε := by
  rw [mulVec_add, svd_design_mulVec hS]

/-- **Equations (44)–(46)** of [benIsrael2003generalized], Chapter 8.
In the singular coordinates the mean is the diagonal design applied to the
transformed parameter, with the same isotropic covariance. -/
theorem ridge_svd_model_moments (hS : IsSVD X U s V) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) :
    let Z := fun ω => Uᵀ *ᵥ Y β ω
    let γ := Vᵀ *ᵥ β
    expectationVector μ Z = rectDiagonal s *ᵥ γ ∧
      covarianceMatrix μ Z = σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  dsimp only
  have hU : Uᵀ * U = 1 := mem_unitaryGroup_iff'.mp hS.mem_unitaryGroup_left
  constructor
  · rw [expectationVector_mulVec _ _ (hY.memLp β), hY.mean β, svd_design_mulVec hS]
  · rw [covarianceMatrix_mulVec _ _ (hY.memLp β), hY.covariance β, transpose_transpose,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]

private theorem ridge_svd_coordinate_observation_moments (hS : IsSVD X U s V) (hX : X.rank = p)
    (σ : ℝ) (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) (i : Fin p) :
    let W := fun ω => (Uᵀ *ᵥ Y β ω) (Fin.castLE (parameterCount_le hX) i)
    let γ := Vᵀ *ᵥ β
    MemLp W 2 μ ∧ (∫ ω, W ω ∂μ) = s i * γ i ∧ variance W μ = σ ^ 2 := by
  let j := Fin.castLE (parameterCount_le hX) i
  let Z := fun ω => Uᵀ *ᵥ Y β ω
  let W := fun ω => Z ω j
  change MemLp W 2 μ ∧ (∫ ω, W ω ∂μ) = s i * (Vᵀ *ᵥ β) i ∧ variance W μ = σ ^ 2
  have hW : MemLp W 2 μ := memLp_estimator_coordinate Uᵀ (hY.memLp β) j
  obtain ⟨hm, hv⟩ := ridge_svd_model_moments hS σ hY β
  refine ⟨hW, ?_, ?_⟩
  · change expectationVector μ Z j = _
    rw [show expectationVector μ Z = _ from hm,
      rectDiagonal_mulVec _ _ j (by exact i.isLt)]
    rfl
  · have h := congrFun (congrFun hv j) j
    change covariance W W μ = σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) j j at h
    rw [covariance_self hW.aemeasurable] at h
    simpa only [Matrix.one_apply_eq, smul_eq_mul, mul_one] using h

/-- **Equations (51)–(53)** of [benIsrael2003generalized], Chapter 8.
The singular-coordinate estimator has the stated coordinate biases and
variances, and its total mean squared error is the sum of the coordinate risks. -/
theorem ridgeEstimator_moments (hS : IsSVD X U s V) (hX : X.rank = p) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) {k : ℝ} (hk : 0 ≤ k) :
    let γ := Vᵀ *ᵥ β
    let Z := fun ω => Vᵀ *ᵥ ridgeEstimator X k (Y β ω)
    (∀ i : Fin p, estimatorBias μ Z γ i = -k * γ i / (s i ^ 2 + k) ∧
      variance (fun ω => Z ω i) μ = s i ^ 2 * σ ^ 2 / (s i ^ 2 + k) ^ 2) ∧
      estimatorMeanSquaredError μ Z γ = ridgeRisk (fun i : Fin p => s i) σ γ k := by
  let γ := Vᵀ *ᵥ β
  let Z := fun ω => Vᵀ *ᵥ ridgeEstimator X k (Y β ω)
  let W := fun (i : Fin p) ω => (Uᵀ *ᵥ Y β ω) (Fin.castLE (parameterCount_le hX) i)
  have hcoord (i : Fin p) : (fun ω => Z ω i) = fun ω => ridgeShrinkageFactor (s i) k * W i ω :=
    funext (fun ω => ridgeEstimator_svd hS hX hk (Y β ω) i)
  have hW (i : Fin p) : MemLp (W i) 2 μ ∧ (∫ ω, W i ω ∂μ) = s i * γ i ∧
      variance (W i) μ = σ ^ 2 := ridge_svd_coordinate_observation_moments hS hX σ hY β i
  have hZ (i : Fin p) : MemLp (fun ω => Z ω i) 2 μ := by
    rw [hcoord i]
    exact (hW i).1.const_mul _
  have hMoments (i : Fin p) := scalarRidge_moments (hW i).1 (hW i).2.1 (hW i).2.2
    (k := k) (by have := positive_singularValues_of_full_column_rank hS hX i; positivity)
  constructor
  · intro i
    change (∫ ω, Z ω i ∂μ) - γ i = _ ∧ variance (fun ω => Z ω i) μ = _
    rw [hcoord i]
    exact ⟨(hMoments i).1, (hMoments i).2.1⟩
  · change estimatorMeanSquaredError μ Z γ = _
    rw [estimatorMeanSquaredError, integral_finsetSum _
      (fun i _ => integrable_sq_error (hZ i) (γ i)), ridgeRisk]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ∫ ω, (ridgeShrinkageFactor (s i) k * W i ω - γ i) ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω =>
          congrArg (fun t : ℝ => (t - γ i) ^ 2) (congrFun (hcoord i) ω))
      _ = _ := (hMoments i).2.2

/-- **Equation (53)** of [benIsrael2003generalized], Chapter 8, in the original
coordinates. Orthogonality gives the same mean squared error as in the
right singular basis. -/
theorem ridgeEstimator_meanSquaredError_eq (hS : IsSVD X U s V) (hX : X.rank = p) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) {k : ℝ} (hk : 0 ≤ k) :
    estimatorMeanSquaredError μ (fun ω => ridgeEstimator X k (Y β ω)) β =
      ridgeRisk (fun i : Fin p => s i) σ (Vᵀ *ᵥ β) k := by
  have hV : Vᵀ ∈ orthogonalGroup (Fin p) ℝ := Unitary.star_mem hS.mem_unitaryGroup_right
  exact (estimatorMeanSquaredError_orthogonal μ hV _ _).symm.trans
    (ridgeEstimator_moments hS hX σ hY β hk).2

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 8.
For positive noise variance and at least one parameter, a positive ridge
penalty has strictly smaller mean squared error than the full-rank BLUE. -/
theorem theorem_3 (hX : X.rank = p) (hp : 0 < p) (σ : ℝ) (hσ : 0 < σ ^ 2)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) :
    ∃ k > 0, estimatorMeanSquaredError μ (fun ω => ridgeEstimator X k (Y β ω)) β <
      estimatorMeanSquaredError μ (fun ω => ridgeEstimator X 0 (Y β ω)) β := by
  obtain ⟨U, s, V, hS⟩ := exists_isSVD X
  let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨k, hk, _, hbound⟩ := exists_positive_ridgeRisk_lt_zeroPenalty
    (positive_singularValues_of_full_column_rank hS hX) σ hσ (Vᵀ *ᵥ β)
  refine ⟨k, hk, ?_⟩
  rw [ridgeEstimator_meanSquaredError_eq hS hX σ hY β hk.le,
    ridgeEstimator_meanSquaredError_eq hS hX σ hY β le_rfl]
  exact hbound

end StatisticalRidge

section CanonicalEstimator

variable {n p : ℕ} {X : Matrix (Fin n) (Fin p) ℝ}
  {U : Matrix (Fin n) (Fin n) ℝ} {V : Matrix (Fin p) (Fin p) ℝ} {s : ℕ → ℝ}

private theorem rank_rectDiagonal_of_svd (hS : IsSVD X U s V) :
    (rectDiagonal s : Matrix (Fin n) (Fin p) ℝ).rank = X.rank := by
  rw [← show Uᵀ * X * V = rectDiagonal s from hS.star_mul_mul,
    rank_mul_eq_left_of_isUnit_det V _
      (isUnit_det_of_mem_unitaryGroup hS.mem_unitaryGroup_right),
    rank_mul_eq_right_of_isUnit_det Uᵀ X
      (isUnit_det_of_mem_unitaryGroup (Unitary.star_mem hS.mem_unitaryGroup_left))]

/-- **Equation (49)** of [benIsrael2003generalized], Chapter 8.
The same estimator applied to the diagonal design and rotated observations
gives the right singular coordinates of the original ridge estimate. -/
theorem ridgeEstimator_canonical (hS : IsSVD X U s V) (hX : X.rank = p) {k : ℝ}
    (hk : 0 ≤ k) (y : Fin n → ℝ) :
    Vᵀ *ᵥ ridgeEstimator X k y =
      ridgeEstimator (rectDiagonal s : Matrix (Fin n) (Fin p) ℝ) k (Uᵀ *ᵥ y) := by
  let D : Matrix (Fin n) (Fin p) ℝ := rectDiagonal s
  have hD : IsSVD D (1 : Matrix (Fin n) (Fin n) ℝ) s (1 : Matrix (Fin p) (Fin p) ℝ) := by
    refine ⟨⟨one_mem _, one_mem _, ?_⟩, hS.antitone, hS.nonneg⟩
    simp [D]
  have hr : D.rank = p := (rank_rectDiagonal_of_svd hS).trans hX
  funext i
  rw [ridgeEstimator_svd hS hX hk]
  simpa only [transpose_one, one_mulVec] using
    (ridgeEstimator_svd hD hr hk (Uᵀ *ᵥ y) i).symm

private theorem rectDiagonal_gram {s : ℕ → ℝ} (hpn : p ≤ n) :
    let D : Matrix (Fin n) (Fin p) ℝ := rectDiagonal s
    Dᵀ * D = diagonal (fun i : Fin p => s i ^ 2) := by
  dsimp only
  rw [← conjTranspose_eq_transpose_of_trivial, conjTranspose_rectDiagonal_mul_self]
  congr 1
  funext i
  simp [lt_of_lt_of_le i.isLt hpn, pow_two]

private theorem inverse_diagonal_of_nonzero {p : Type*} [Fintype p] [DecidableEq p]
    (b : p → ℝ) (hb : ∀ i, b i ≠ 0) :
    (diagonal b)⁻¹ = diagonal (fun i => (b i)⁻¹) := by
  apply inv_eq_left_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hb i)

private theorem add_diagonal_to_rectDiagonal_gram {s : ℕ → ℝ} (hpn : p ≤ n)
    (k : Fin p → ℝ) :
    let D : Matrix (Fin n) (Fin p) ℝ := rectDiagonal s
    Dᵀ * D + diagonal k = diagonal (fun i : Fin p => s i ^ 2 + k i) := by
  dsimp only
  rw [rectDiagonal_gram hpn, ← diagonal_add]

end CanonicalEstimator

section Endpoint

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n p : ℕ} {s : ℕ → ℝ}
  {X : Matrix (Fin n) (Fin p) ℝ} {U : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin p) (Fin p) ℝ} {Y : (Fin p → ℝ) → Ω → Fin n → ℝ}

/-- **Equation (47b)** of [benIsrael2003generalized], Chapter 8.
The least-squares estimate in each singular direction is unbiased with
variance equal to the noise variance over the squared singular value. -/
theorem ridgeBLUE_coordinate_moments (hS : IsSVD X U s V) (hX : X.rank = p) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) (i : Fin p) :
    let Z := fun ω => Vᵀ *ᵥ (X.pinv *ᵥ Y β ω)
    let γ := Vᵀ *ᵥ β
    expectationVector μ Z i = γ i ∧
      variance (fun ω => Z ω i) μ = σ ^ 2 / s i ^ 2 ∧
      (∫ ω, (Z ω i - γ i) ^ 2 ∂μ) = σ ^ 2 / s i ^ 2 := by
  let Z := fun ω => Vᵀ *ᵥ (X.pinv *ᵥ Y β ω)
  let γ := Vᵀ *ᵥ β
  have hr (ω : Ω) : ridgeEstimator X 0 (Y β ω) = X.pinv *ᵥ Y β ω :=
    ridgeEstimator_zero X (by simpa only [Fintype.card_fin] using hX) (Y β ω)
  have hm := (ridgeEstimator_moments hS hX σ hY β le_rfl).1 i
  dsimp only at hm
  simp_rw [hr] at hm
  change expectationVector μ Z i = γ i ∧ variance (fun ω => Z ω i) μ = _ ∧ _
  have hmean : expectationVector μ Z i = γ i := by
    apply sub_eq_zero.mp
    simpa [estimatorBias, Z, γ] using hm.1
  have hvar : variance (fun ω => Z ω i) μ = σ ^ 2 / s i ^ 2 := by
    have hv := hm.2
    change variance (fun ω => Z ω i) μ = _ at hv
    have hi := (positive_singularValues_of_full_column_rank hS hX i).ne'
    rw [hv, add_zero]
    field_simp
  have hZ : MemLp (fun ω => Z ω i) 2 μ := by
    apply memLp_estimator_coordinate Vᵀ
    exact fun j => memLp_estimator_coordinate X.pinv (hY.memLp β) j
  refine ⟨hmean, hvar, ?_⟩
  rw [expected_sq_error hZ (γ i), hvar, show (∫ ω, Z ω i ∂μ) = γ i from hmean]
  simp

/-- **Equation (51)** of [benIsrael2003generalized], Chapter 8.
The bias in the canonical coordinates is the inverse regularized Gram
matrix applied to the parameter, scaled by the negative penalty. -/
theorem ridgeEstimator_bias_vector (hS : IsSVD X U s V) (hX : X.rank = p) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) {k : ℝ} (hk : 0 ≤ k) :
    let D : Matrix (Fin n) (Fin p) ℝ := rectDiagonal s
    let γ := Vᵀ *ᵥ β
    let Z := fun ω => Vᵀ *ᵥ ridgeEstimator X k (Y β ω)
    estimatorBias μ Z γ = (-k) • ((Dᵀ * D + k • (1 : Matrix (Fin p) (Fin p) ℝ))⁻¹ *ᵥ γ) := by
  dsimp only
  rw [smul_one_eq_diagonal, add_diagonal_to_rectDiagonal_gram (parameterCount_le hX),
    inverse_diagonal_of_nonzero _ (fun i => by
      have := positive_singularValues_of_full_column_rank hS hX i
      positivity)]
  funext i
  rw [(ridgeEstimator_moments hS hX σ hY β hk).1 i |>.1, Pi.smul_apply, smul_eq_mul,
    mulVec_diagonal, div_eq_mul_inv]
  ring

/-- **Theorem 3**, Equation (54) of [benIsrael2003generalized], Chapter 8.
The right derivative of the actual mean squared error at zero is negative. -/
theorem ridgeEstimator_meanSquaredError_right_deriv_neg
    (hS : IsSVD X U s V) (hX : X.rank = p) (hp : 0 < p) (σ : ℝ) (hσ : 0 < σ ^ 2)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) :
    derivWithin (fun k => estimatorMeanSquaredError μ (fun ω => ridgeEstimator X k (Y β ω)) β)
      (Set.Ici 0) 0 < 0 := by
  let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  let γ := Vᵀ *ᵥ β
  have hs := positive_singularValues_of_full_column_rank hS hX
  have hd := hasDerivAt_ridgeRisk (fun i : Fin p => s i) σ γ 0 (fun i => by
    have := hs i
    positivity)
  have hw := hd.hasDerivWithinAt (s := Set.Ici 0)
  have h := hw.congr_of_mem
    (fun k hk => ridgeEstimator_meanSquaredError_eq hS hX σ hY β hk) (by simp)
  rw [h.derivWithin (uniqueDiffWithinAt_Ici 0), ← hd.deriv]
  exact deriv_ridgeRisk_zero_neg hs σ hσ γ

/-- If the noise variance is zero, the full-rank least-squares endpoint has
zero mean squared error and no ridge penalty can strictly improve it. -/
theorem ridgeEstimator_no_improvement_of_zero_variance
    (hX : X.rank = p)
    (hY : IsLinearStatisticalModel μ X (0 : Matrix (Fin n) (Fin n) ℝ) Y)
    (β : Fin p → ℝ) (k : ℝ) :
    estimatorMeanSquaredError μ (fun ω => ridgeEstimator X 0 (Y β ω)) β = 0 ∧
      0 ≤ estimatorMeanSquaredError μ (fun ω => ridgeEstimator X k (Y β ω)) β := by
  obtain ⟨U, s, V, hS⟩ := exists_isSVD X
  have hY' : IsLinearStatisticalModel μ X ((0 : ℝ) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y := by
    simpa using hY
  refine ⟨?_, estimatorMeanSquaredError_nonneg μ _ _⟩
  rw [ridgeEstimator_meanSquaredError_eq hS hX 0 hY' β le_rfl]
  simp [ridgeRisk, ridgeCoordinateRisk]

omit [IsProbabilityMeasure μ] in
/-- If the parameter space is empty, its mean squared error is zero for every penalty. -/
theorem ridgeEstimator_meanSquaredError_empty
    (X : Matrix (Fin n) (Fin 0) ℝ) (Y : Ω → Fin n → ℝ) (k : ℝ) (β : Fin 0 → ℝ) :
    estimatorMeanSquaredError μ (fun ω => ridgeEstimator X k (Y ω)) β = 0 := by
  simp [estimatorMeanSquaredError]

end Endpoint

section GaussianCoordinates

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n p : ℕ} {s : ℕ → ℝ}
  {X : Matrix (Fin n) (Fin p) ℝ} {U : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin p) (Fin p) ℝ} {Y : (Fin p → ℝ) → Ω → Fin n → ℝ}

omit [IsProbabilityMeasure μ] in
private theorem gaussian_add_constant {G : Ω → EuclideanSpace ℝ (Fin n)}
    (hG : HasGaussianLaw G μ) (a : EuclideanSpace ℝ (Fin n)) :
    HasGaussianLaw (fun ω => G ω + a) μ := by
  have hg := hG.aemeasurable
  refine ⟨hg.add aemeasurable_const, ?_⟩
  have := hG.isGaussian_map
  change IsGaussian (μ.map ((· + a) ∘ G))
  rw [← AEMeasurable.map_map_of_aemeasurable]
  · infer_instance
  all_goals fun_prop

/-- **Equations (44)–(46)** of [benIsrael2003generalized], Chapter 8.
An orthogonal observation rotation preserves Gaussianity and the isotropic
covariance of the centered error. -/
theorem ridgeGaussian_rotated_error (hS : IsSVD X U s V) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ)
    (hG : HasGaussianLaw
      (fun ω => (WithLp.toLp 2 (Y β ω - X *ᵥ β) : EuclideanSpace ℝ (Fin n))) μ) :
    let W := fun ω => Uᵀ *ᵥ (Y β ω - X *ᵥ β)
    HasGaussianLaw (fun ω => (WithLp.toLp 2 (W ω) : EuclideanSpace ℝ (Fin n))) μ ∧
      expectationVector μ W = 0 ∧
      covarianceMatrix μ W = σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let W := fun ω => Y β ω - X *ᵥ β
  have hW (i : Fin n) : MemLp (fun ω => W ω i) 2 μ := (hY.memLp β i).sub (memLp_const _)
  have hMean : expectationVector μ W = 0 := by
    simpa only [W, sub_eq_add_neg, hY.mean β, add_neg_cancel] using
      (moments_add_const (Y β) (-(X *ᵥ β)) (hY.memLp β)).1
  have hCov : covarianceMatrix μ W = σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simpa only [W, sub_eq_add_neg, hY.covariance β] using
      (moments_add_const (Y β) (-(X *ᵥ β)) (hY.memLp β)).2
  have hU : Uᵀ * U = 1 := mem_unitaryGroup_iff'.mp hS.mem_unitaryGroup_left
  refine ⟨?_, ?_, ?_⟩
  · simpa only [toEuclideanCLM_toLp] using hG.map_fun (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Uᵀ)
  · rw [expectationVector_mulVec Uᵀ W hW, hMean, mulVec_zero]
  · rw [covarianceMatrix_mulVec Uᵀ W hW, hCov, transpose_transpose,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]

/-- **Equations (46a)–(46b)** of [benIsrael2003generalized], Chapter 8.
A rotated observation has a real Gaussian marginal with its corresponding
design mean and the unchanged noise variance. The design mean is zero
in the observation directions beyond the parameter space. -/
theorem ridgeGaussian_coordinate_law (hS : IsSVD X U s V) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ)
    (hG : HasGaussianLaw
      (fun ω => (WithLp.toLp 2 (Y β ω - X *ᵥ β) : EuclideanSpace ℝ (Fin n))) μ)
    (i : Fin n) :
    μ.map (fun ω => (Uᵀ *ᵥ Y β ω) i) =
      gaussianReal ((rectDiagonal s *ᵥ (Vᵀ *ᵥ β)) i) (σ ^ 2).toNNReal := by
  let W := fun ω => Uᵀ *ᵥ Y β ω
  have hObs : HasGaussianLaw (fun ω => (WithLp.toLp 2 (Y β ω) : EuclideanSpace ℝ (Fin n))) μ := by
    simpa only [← WithLp.toLp_add, sub_add_cancel] using
      gaussian_add_constant hG (WithLp.toLp 2 (X *ᵥ β))
  have hZ : HasGaussianLaw (fun ω => (WithLp.toLp 2 (W ω) : EuclideanSpace ℝ (Fin n))) μ := by
    simpa only [W, toEuclideanCLM_toLp] using hObs.map_fun (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Uᵀ)
  have hI : HasGaussianLaw (fun ω => W ω i) μ := hZ.map_fun (EuclideanSpace.proj i)
  obtain ⟨hm, hv⟩ := ridge_svd_model_moments hS σ hY β
  have hmean : (∫ ω, W ω i ∂μ) = (rectDiagonal s *ᵥ (Vᵀ *ᵥ β)) i := congrFun hm i
  have hvar := congrFun (congrFun hv i) i
  change covariance (fun ω => W ω i) (fun ω => W ω i) μ = _ at hvar
  rw [covariance_self hI.aemeasurable] at hvar
  change variance (fun ω => W ω i) μ = σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) i i at hvar
  have hvar' : variance (fun ω => W ω i) μ = σ ^ 2 := by
    simpa only [Matrix.one_apply_eq, smul_eq_mul, mul_one] using hvar
  change μ.map (fun ω => W ω i) = _
  rw [hI.map_eq_gaussianReal, hmean, hvar']

end GaussianCoordinates

section Shrinkage

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- **Equation (56)** of [benIsrael2003generalized], Chapter 8.
A diagonal shrinkage estimator multiplies the observation coordinates
by their chosen coefficients. -/
def shrinkageEstimator {p : Type*} (c : p → ℝ) (z : p → ℝ) : p → ℝ :=
  fun i => c i * z i

/-- The mean squared error of the scalar shrinkage estimator in **Exercise 12**
of [benIsrael2003generalized], Chapter 8. -/
noncomputable def shrinkageCoordinateRisk (s σ γ c : ℝ) : ℝ :=
  c ^ 2 * σ ^ 2 + ((c * s - 1) * γ) ^ 2

/-- **Exercise 12** of [benIsrael2003generalized], Chapter 8.
The admissible families are continuous at zero and strictly decrease
from their positive least-squares coefficients. -/
structure IsShrinkageFamily {p : Type*} (s : p → ℝ) (c : p → ℝ → ℝ) : Prop where
  /-- The initial coefficient is the usual unbiased least-squares coefficient. -/
  at_zero : ∀ i, c i 0 = (s i)⁻¹
  /-- The coefficients are continuous on the nonnegative penalties. -/
  continuousOn : ∀ i, ContinuousOn (c i) (Set.Ici 0)
  /-- Positive coefficients strictly decrease with the penalty. -/
  strictAntiOn : ∀ i, StrictAntiOn (c i) (Set.Ici 0)
  /-- For positive singular values the shrinkage coefficient has positive sign. -/
  positive : ∀ i k, 0 ≤ k → 0 < c i k

/-- **Equation (50)** and **Exercise 12** of [benIsrael2003generalized], Chapter 8.
The ridge shrinkage factors have the required decrease, continuity, and sign. -/
theorem isShrinkageFamily_ridge {p : Type*} {s : p → ℝ} (hs : ∀ i, 0 < s i) :
    IsShrinkageFamily s (fun i => ridgeShrinkageFactor (s i)) := by
  refine ⟨fun i => ridgeShrinkageFactor_zero (s i), ?_, ?_, ?_⟩
  · intro i a ha
    change 0 ≤ a at ha
    apply ContinuousAt.continuousWithinAt
    unfold ridgeShrinkageFactor
    apply continuousAt_const.div (continuousAt_const.add continuousAt_id)
    change s i ^ 2 + a ≠ 0
    have := hs i
    positivity
  · intro i a ha b hb hab
    have hi := hs i
    change 0 ≤ a at ha
    exact div_lt_div_of_pos_left hi (by positivity) (by linarith)
  · intro i k hk
    have hi := hs i
    exact div_pos hi (by positivity)

/-- **Exercise 12** of [benIsrael2003generalized], Chapter 8, in singular coordinates.
For sufficiently small positive penalties, every coordinate simultaneously
has smaller mean squared error than the least-squares coordinate. -/
theorem exists_positive_shrinkageCoordinateRisk_lt {p : Type*} [Finite p]
    {s : p → ℝ} {c : p → ℝ → ℝ} (hs : ∀ i, 0 < s i)
    (hc : IsShrinkageFamily s c) (σ : ℝ) (hσ : 0 < σ ^ 2) (γ : p → ℝ) :
    ∃ k > 0, ∀ i, shrinkageCoordinateRisk (s i) σ (γ i) (c i k) <
      shrinkageCoordinateRisk (s i) σ (γ i) (c i 0) := by
  let := Fintype.ofFinite p
  let B (i : p) (k : ℝ) :=
    (c i k + (s i)⁻¹) * σ ^ 2 + (c i k - (s i)⁻¹) * (s i ^ 2 * γ i ^ 2)
  have hB (i : p) : ∀ᶠ k : ℝ in 𝓝[Set.Ioi 0] 0, 0 < B i k := by
    have hC := hc.continuousOn i 0 (by simp)
    have hcont : ContinuousWithinAt (B i) (Set.Ici 0) 0 := by
      dsimp only [B]
      exact ((hC.add continuousWithinAt_const).mul continuousWithinAt_const).add
        ((hC.sub continuousWithinAt_const).mul continuousWithinAt_const)
    have hpos : 0 < B i 0 := by
      have hi := hs i
      simp only [B, hc.at_zero, sub_self, zero_mul, add_zero]
      exact mul_pos (add_pos (inv_pos.mpr hi) (inv_pos.mpr hi)) hσ
    exact (hcont.eventually (eventually_gt_nhds hpos)).filter_mono
      (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hK : ∀ᶠ k : ℝ in 𝓝[Set.Ioi 0] 0, 0 < k := self_mem_nhdsWithin
  obtain ⟨k, hk, hsmall⟩ := (hK.and (eventually_all.2 hB)).exists
  refine ⟨k, hk, fun i => sub_lt_zero.mp ?_⟩
  have hq : c i k < (s i)⁻¹ := by
    rw [← hc.at_zero i]
    exact hc.strictAntiOn i (by simp) hk.le hk
  have hid :
      shrinkageCoordinateRisk (s i) σ (γ i) (c i k) -
        shrinkageCoordinateRisk (s i) σ (γ i) (c i 0) = (c i k - (s i)⁻¹) * B i k := by
    rw [hc.at_zero]
    have hi := (hs i).ne'
    unfold shrinkageCoordinateRisk
    dsimp only [B]
    field_simp
    ring
  rw [hid]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hq) (hsmall i)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n p : ℕ} {s : ℕ → ℝ}
  {X : Matrix (Fin n) (Fin p) ℝ} {U : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin p) (Fin p) ℝ} {Y : (Fin p → ℝ) → Ω → Fin n → ℝ}

/-- **Exercise 12** of [benIsrael2003generalized], Chapter 8.
A common small positive penalty improves every singular-coordinate
shrinkage estimate compared with its BLUE at penalty zero. -/
theorem exercise_8_12 (hS : IsSVD X U s V) (hX : X.rank = p) (σ : ℝ) (hσ : 0 < σ ^ 2)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) {c : Fin p → ℝ → ℝ}
    (hc : IsShrinkageFamily (fun i : Fin p => s i) c) :
    let γ := Vᵀ *ᵥ β
    let Z := fun ω i => (Uᵀ *ᵥ Y β ω) (Fin.castLE (parameterCount_le hX) i)
    ∃ k > 0, ∀ i : Fin p, (∫ ω, (shrinkageEstimator (fun j => c j k) (Z ω) i - γ i) ^ 2 ∂μ) <
      (∫ ω, ((Vᵀ *ᵥ (X.pinv *ᵥ Y β ω)) i - γ i) ^ 2 ∂μ) := by
  let γ := Vᵀ *ᵥ β
  let Z := fun (ω : Ω) (i : Fin p) => (Uᵀ *ᵥ Y β ω) (Fin.castLE (parameterCount_le hX) i)
  obtain ⟨k, hk, hsmall⟩ := exists_positive_shrinkageCoordinateRisk_lt
    (positive_singularValues_of_full_column_rank hS hX) hc σ hσ γ
  refine ⟨k, hk, fun i => ?_⟩
  have hW := ridge_svd_coordinate_observation_moments hS hX σ hY β i
  have h0 (ω : Ω) : (Vᵀ *ᵥ (X.pinv *ᵥ Y β ω)) i = c i 0 * Z ω i := by
    rw [ridgeBLUE_coordinate hS hX, hc.at_zero, div_eq_mul_inv, mul_comm]
  change (∫ ω, (c i k * Z ω i - γ i) ^ 2 ∂μ) <
    (∫ ω, ((Vᵀ *ᵥ (X.pinv *ᵥ Y β ω)) i - γ i) ^ 2 ∂μ)
  simp_rw [h0]
  rw [(scalarShrinkage_moments hW.1 hW.2.1 hW.2.2 (c i k)).2.2,
    (scalarShrinkage_moments hW.1 hW.2.1 hW.2.2 (c i 0)).2.2]
  exact hsmall i

end Shrinkage

section DiagonalPenalty

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq p]

/-- **Equation (55)** of [benIsrael2003generalized], Chapter 8.
The generalized ridge estimator with a diagonal penalty in the specified basis. -/
noncomputable def diagonalRidgeEstimator (X : Matrix n p ℝ) (k : p → ℝ) (y : n → ℝ) : p → ℝ :=
  ((Xᵀ * X + diagonal k)⁻¹ * Xᵀ) *ᵥ y

/-- The sum of the coordinate mean squared errors with separate penalties,
as in **Exercise 11** of [benIsrael2003generalized], Chapter 8. -/
noncomputable def diagonalRidgeRisk (s : p → ℝ) (σ : ℝ) (γ k : p → ℝ) : ℝ :=
  ∑ i, ridgeCoordinateRisk (s i) σ (γ i) (k i)

end DiagonalPenalty

section DiagonalPenaltyCoordinates

variable {n p : ℕ} {X : Matrix (Fin n) (Fin p) ℝ}
  {U : Matrix (Fin n) (Fin n) ℝ} {V : Matrix (Fin p) (Fin p) ℝ} {s : ℕ → ℝ}

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 8.
In the right singular coordinates each observation is shrunk using its own penalty. -/
theorem diagonalRidgeEstimator_rectDiagonal (hpn : p ≤ n) (k : Fin p → ℝ)
    (hk : ∀ i : Fin p, s i ^ 2 + k i ≠ 0) (z : Fin n → ℝ) (i : Fin p) :
    diagonalRidgeEstimator (rectDiagonal s : Matrix (Fin n) (Fin p) ℝ) k z i =
      ridgeShrinkageFactor (s i) (k i) * z (Fin.castLE hpn i) := by
  have hT : (rectDiagonal s : Matrix (Fin n) (Fin p) ℝ)ᵀ =
      (rectDiagonal s : Matrix (Fin p) (Fin n) ℝ) := by
    rw [← conjTranspose_eq_transpose_of_trivial, rectDiagonal_conjTranspose]
    rfl
  rw [diagonalRidgeEstimator, add_diagonal_to_rectDiagonal_gram hpn,
    inverse_diagonal_of_nonzero _ hk, ← mulVec_mulVec, mulVec_diagonal, hT,
    rectDiagonal_mulVec _ _ i (i.isLt.trans_le hpn), ridgeShrinkageFactor]
  change (s i ^ 2 + k i)⁻¹ * (s i * z (Fin.castLE hpn i)) =
    s i / (s i ^ 2 + k i) * z (Fin.castLE hpn i)
  ring

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 8.
To apply separate penalties in the right singular directions, the penalty
matrix in the original coordinates is `V diag(k) Vᵀ`. -/
theorem diagonalRidgeEstimator_rotated_penalty (hS : IsSVD X U s V) (hX : X.rank = p)
    (k : Fin p → ℝ) (hk : ∀ i, 0 ≤ k i) (y : Fin n → ℝ) :
    Vᵀ *ᵥ (((Xᵀ * X + V * diagonal k * Vᵀ)⁻¹ * Xᵀ) *ᵥ y) =
      diagonalRidgeEstimator (rectDiagonal s : Matrix (Fin n) (Fin p) ℝ) k (Uᵀ *ᵥ y) := by
  let D : Matrix (Fin n) (Fin p) ℝ := rectDiagonal s
  let B := Dᵀ * D + diagonal k
  let f := Unitary.conjStarAlgAut ℝ _ ⟨V, hS.mem_unitaryGroup_right⟩
  have hEq : X = U * D * Vᵀ := hS.eq_mul_mul_star
  have hXt : Xᵀ = V * Dᵀ * Uᵀ := by
    rw [hEq, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  have hU : Uᵀ * U = 1 := mem_unitaryGroup_iff'.mp hS.mem_unitaryGroup_left
  have hV : Vᵀ * V = 1 := mem_unitaryGroup_iff'.mp hS.mem_unitaryGroup_right
  have hGram : Xᵀ * X = V * (Dᵀ * D) * Vᵀ := by
    rw [hXt, hEq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  have hdet : IsUnit B.det := by
    apply (isUnit_iff_isUnit_det B).mp
    change IsUnit (Dᵀ * D + diagonal k)
    rw [add_diagonal_to_rectDiagonal_gram (parameterCount_le hX), isUnit_diagonal, Pi.isUnit_iff]
    intro i
    have hi := positive_singularValues_of_full_column_rank hS hX i
    have hki := hk i
    exact isUnit_iff_ne_zero.mpr (by positivity)
  have hf (C : Matrix (Fin p) (Fin p) ℝ) : f C = V * C * Vᵀ := rfl
  have hP : Xᵀ * X + V * diagonal k * Vᵀ = f B := by
    rw [hGram, hf]
    change _ = V * (Dᵀ * D + diagonal k) * Vᵀ
    rw [Matrix.mul_add, Matrix.add_mul]
  have hinv : (f B)⁻¹ = f B⁻¹ := by
    apply inv_eq_left_inv
    rw [← map_mul, nonsing_inv_mul B hdet, map_one]
  rw [hP, hinv, hf, hXt, diagonalRidgeEstimator, mulVec_mulVec, ← mulVec_mulVec]
  change Vᵀ *ᵥ ((V * B⁻¹ * Vᵀ * (V * Dᵀ * Uᵀ)) *ᵥ y) =
    (B⁻¹ * Dᵀ) *ᵥ (Uᵀ *ᵥ y)
  rw [mulVec_mulVec, mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul, ← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]

end DiagonalPenaltyCoordinates

section DiagonalPenaltyRisk

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n p : ℕ} {s : ℕ → ℝ}
  {X : Matrix (Fin n) (Fin p) ℝ} {U : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin p) (Fin p) ℝ} {Y : (Fin p → ℝ) → Ω → Fin n → ℝ}

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 8.
The mean squared error for independent penalties in singular coordinates
is the sum of the scalar ridge risks at the corresponding penalties. -/
theorem exercise_8_11_risk (hS : IsSVD X U s V) (hX : X.rank = p) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ) (k : Fin p → ℝ) (hk : ∀ i, 0 ≤ k i) :
    let D : Matrix (Fin n) (Fin p) ℝ := rectDiagonal s
    let γ := Vᵀ *ᵥ β
    let Z := fun ω => diagonalRidgeEstimator D k (Uᵀ *ᵥ Y β ω)
    estimatorMeanSquaredError μ Z γ = diagonalRidgeRisk (fun i : Fin p => s i) σ γ k := by
  let D : Matrix (Fin n) (Fin p) ℝ := rectDiagonal s
  let γ := Vᵀ *ᵥ β
  let Z := fun ω => diagonalRidgeEstimator D k (Uᵀ *ᵥ Y β ω)
  let W := fun (i : Fin p) ω => (Uᵀ *ᵥ Y β ω) (Fin.castLE (parameterCount_le hX) i)
  have hden (i : Fin p) : s i ^ 2 + k i ≠ 0 := by
    have hi := positive_singularValues_of_full_column_rank hS hX i
    have hki := hk i
    positivity
  have hZ (i : Fin p) (ω : Ω) : Z ω i = ridgeShrinkageFactor (s i) (k i) * W i ω :=
    diagonalRidgeEstimator_rectDiagonal (parameterCount_le hX) k hden _ i
  change estimatorMeanSquaredError μ Z γ = _
  simp_rw [estimatorMeanSquaredError, hZ]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have hobs := ridge_svd_coordinate_observation_moments hS hX σ hY β i
    exact (scalarRidge_moments hobs.1 hobs.2.1 hobs.2.2 (hden i)).2.2
  · intro i _
    have hobs := ridge_svd_coordinate_observation_moments hS hX σ hY β i
    exact integrable_sq_error (hobs.1.const_mul _) (γ i)

end DiagonalPenaltyRisk

section DiagonalPenaltyOptimality

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 8.
The gradient of the diagonal-penalty risk consists of the displayed
one-coordinate derivatives. -/
theorem hasFDerivAt_diagonalRidgeRisk {p : Type*} [Fintype p]
    (s : p → ℝ) (σ : ℝ) (γ k : p → ℝ) (hk : ∀ i, s i ^ 2 + k i ≠ 0) :
    HasFDerivAt (diagonalRidgeRisk s σ γ)
      (∑ i, (2 * s i ^ 2 * (k i * γ i ^ 2 - σ ^ 2) / (s i ^ 2 + k i) ^ 3) •
        (ContinuousLinearMap.proj i : (p → ℝ) →L[ℝ] ℝ)) k := by
  classical
  change HasFDerivAt (fun t => ∑ i, ridgeCoordinateRisk (s i) σ (γ i) (t i)) _ k
  refine HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ?_)
  let e : (p → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have he : HasFDerivAt (fun t : p → ℝ => t i) e k := e.hasFDerivAt
  have hi := ((hasDerivAt_ridgeCoordinateRisk (s i) σ (γ i) (k i) (hk i)).hasFDerivAt).comp k he
  let r := 2 * s i ^ 2 * (k i * γ i ^ 2 - σ ^ 2) / (s i ^ 2 + k i) ^ 3
  have hLin : ContinuousLinearMap.toSpanSingleton ℝ r ∘SL e = r • e := by
    ext t
    change t i * r = r * t i
    exact mul_comm _ _
  change HasFDerivAt (ridgeCoordinateRisk (s i) σ (γ i) ∘ (fun t => t i))
    (r • e) k
  rw [← hLin]
  exact hi

private theorem ridgeCoordinateRisk_sub_minimum {s σ γ k : ℝ} (hs : 0 < s)
    (hσ : 0 < σ ^ 2) (hk : 0 ≤ k) :
    ridgeCoordinateRisk s σ γ k - σ ^ 2 * γ ^ 2 / (σ ^ 2 + s ^ 2 * γ ^ 2) =
      s ^ 2 * (k * γ ^ 2 - σ ^ 2) ^ 2 / ((s ^ 2 + k) ^ 2 * (σ ^ 2 + s ^ 2 * γ ^ 2)) := by
  have hd : 0 < σ ^ 2 + s ^ 2 * γ ^ 2 := by positivity
  have he : 0 < s ^ 2 + k := by positivity
  unfold ridgeCoordinateRisk
  field_simp
  ring

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 8.
With positive variance and nonzero signal the optimal coordinate penalty is
`σ² / γ²`. It uniquely minimizes the risk among nonnegative penalties. -/
theorem ridgeCoordinateRisk_optimal {s σ γ : ℝ} (hs : 0 < s)
    (hσ : 0 < σ ^ 2) (hγ : γ ≠ 0) :
    let k₀ := σ ^ 2 / γ ^ 2
    0 < k₀ ∧ ∀ k ≥ 0, ridgeCoordinateRisk s σ γ k₀ ≤ ridgeCoordinateRisk s σ γ k ∧
      (ridgeCoordinateRisk s σ γ k₀ = ridgeCoordinateRisk s σ γ k ↔ k = k₀) := by
  let k₀ := σ ^ 2 / γ ^ 2
  have hγsq : 0 < γ ^ 2 := sq_pos_of_ne_zero hγ
  have h₀ : 0 < k₀ := div_pos hσ hγsq
  have hmul : k₀ * γ ^ 2 = σ ^ 2 := div_mul_cancel₀ _ hγsq.ne'
  have hopt := ridgeCoordinateRisk_sub_minimum hs hσ h₀.le (γ := γ)
  change ridgeCoordinateRisk s σ γ k₀ - _ = _ at hopt
  simp only [hmul, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div] at hopt
  have hEq := sub_eq_zero.mp hopt
  refine ⟨h₀, fun k hk => ?_⟩
  rw [hEq]
  have hkEq := ridgeCoordinateRisk_sub_minimum hs hσ hk (γ := γ)
  refine ⟨sub_nonneg.mp (hkEq.symm ▸ (show 0 ≤ _ by positivity)), ?_⟩
  constructor
  · intro h
    rw [← h, sub_self] at hkEq
    have hd : 0 < (s ^ 2 + k) ^ 2 * (σ ^ 2 + s ^ 2 * γ ^ 2) := by positivity
    have hnum : s ^ 2 * (k * γ ^ 2 - σ ^ 2) ^ 2 = 0 :=
      (div_eq_zero_iff.mp hkEq.symm).resolve_right hd.ne'
    have hsne : s ^ 2 ≠ 0 := by positivity
    have he : k * γ ^ 2 = σ ^ 2 := sub_eq_zero.mp
      ((pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hnum).resolve_left hsne))
    exact (eq_div_iff hγsq.ne').mpr he
  · rintro rfl
    exact hEq.symm

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 8.
The full diagonal-penalty risk is minimized by the independently optimized
coordinates whenever all those finite positive optima exist. -/
theorem exercise_8_11_optimal {p : Type*} [Fintype p] {s : p → ℝ}
    (hs : ∀ i, 0 < s i) (σ : ℝ) (hσ : 0 < σ ^ 2) (γ : p → ℝ) (hγ : ∀ i, γ i ≠ 0) :
    let k₀ := fun i => σ ^ 2 / γ i ^ 2
    (∀ i, 0 < k₀ i) ∧ IsMinOn (diagonalRidgeRisk s σ γ) {k | ∀ i, 0 ≤ k i} k₀ := by
  let k₀ := fun i => σ ^ 2 / γ i ^ 2
  have hOpt (i : p) := ridgeCoordinateRisk_optimal (hs i) hσ (hγ i)
  refine ⟨fun i => (hOpt i).1, ?_⟩
  apply isMinOn_iff.mpr
  intro k hk
  exact Finset.sum_le_sum (fun i _ => ((hOpt i).2 (k i) (hk i)).1)

end DiagonalPenaltyOptimality

section GaussianLaw

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {n p : ℕ} {s : ℕ → ℝ}
  {X : Matrix (Fin n) (Fin p) ℝ} {U : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin p) (Fin p) ℝ} {Y : (Fin p → ℝ) → Ω → Fin n → ℝ}

private theorem gaussianLaw_eq_multivariate_of_moments {W : Ω → Fin n → ℝ}
    (hW : HasGaussianLaw (fun ω => (WithLp.toLp 2 (W ω) : EuclideanSpace ℝ (Fin n))) μ)
    (b : Fin n → ℝ) {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (hmean : expectationVector μ W = b) (hCov : covarianceMatrix μ W = S) :
    μ.map (fun ω => (WithLp.toLp 2 (W ω) : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian (WithLp.toLp 2 b) S := by
  let G := fun ω => (WithLp.toLp 2 (W ω) : EuclideanSpace ℝ (Fin n))
  have hG : HasGaussianLaw G μ := hW
  have := hG.isGaussian_map
  have hGM := hG.aemeasurable
  change μ.map G = _
  apply IsGaussian.ext
  · rw [integral_id_multivariateGaussian', integral_map hGM (aestronglyMeasurable_id)]
    ext i
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hG.integrable
    exact h.symm.trans (congrFun hmean i)
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
    have he (i : Fin n) : (fun u => ⟪(EuclideanSpace.basisFun (Fin n) ℝ).toBasis i, u⟫) =
        fun u => u i := by
      ext u
      simp [PiLp.inner_apply]
    simp_rw [he, covariance_eval_multivariateGaussian hS]
    rw [covariance_map_fun (by fun_prop) (by fun_prop) hGM]
    exact congrFun (congrFun hCov i) j

/-- **Equations (44)–(46)** of [benIsrael2003generalized], Chapter 8.
The rotated error has the centered multivariate normal distribution with
the original isotropic covariance. -/
theorem ridgeGaussian_rotated_error_law [IsProbabilityMeasure μ] (hS : IsSVD X U s V) (σ : ℝ)
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) Y)
    (β : Fin p → ℝ)
    (hG : HasGaussianLaw
      (fun ω => (WithLp.toLp 2 (Y β ω - X *ᵥ β) : EuclideanSpace ℝ (Fin n))) μ) :
    μ.map (fun ω => (WithLp.toLp 2 (Uᵀ *ᵥ (Y β ω - X *ᵥ β)) : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  have hP : (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    rw [smul_one_eq_diagonal, posSemidef_diagonal_iff]
    exact fun _ => sq_nonneg σ
  obtain ⟨hW, hMean, hCov⟩ := ridgeGaussian_rotated_error hS σ hY β hG
  exact gaussianLaw_eq_multivariate_of_moments hW 0 hP hMean hCov

end GaussianLaw

section OptimalPenalty

open scoped Topology

/-- **Section 8.4** of [benIsrael2003generalized].
An optimal ridge parameter is a positive penalty minimizing the scalar ridge risk. -/
def IsOptimalRidgeParameter {p : Type*} [Fintype p] (s : p → ℝ) (σ : ℝ)
    (γ : p → ℝ) (k : ℝ) : Prop :=
  0 < k ∧ IsMinOn (ridgeRisk s σ γ) (Set.Ioi 0) k

/-- **Equation (54)** of [benIsrael2003generalized], Chapter 8.
At a positive optimum the derivative equation in the ridge penalty vanishes. -/
theorem optimalRidgeParameter_stationary {p : Type*} [Fintype p] {s : p → ℝ}
    {σ : ℝ} {γ : p → ℝ} {k : ℝ} (h : IsOptimalRidgeParameter s σ γ k) :
    (∑ i, 2 * s i ^ 2 * (k * γ i ^ 2 - σ ^ 2) / (s i ^ 2 + k) ^ 3) = 0 := by
  have hk := h.1
  have hd := hasDerivAt_ridgeRisk s σ γ k (fun _ => by positivity)
  have hm := h.2.isLocalMin (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hk))
  exact hd.deriv.symm.trans hm.deriv_eq_zero

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 8, zero-signal case.
Every increase of a nonnegative penalty strictly reduces the risk in a
zero-signal direction if its singular value and noise variance are positive. -/
theorem ridgeCoordinateRisk_zero_signal_strictAntiOn {s σ : ℝ}
    (hs : 0 < s) (hσ : 0 < σ ^ 2) :
    StrictAntiOn (ridgeCoordinateRisk s σ 0) (Set.Ici 0) := by
  intro a ha b _ hab
  change 0 ≤ a at ha
  have hsa : 0 < s ^ 2 + a := by positivity
  have hlt : s ^ 2 + a < s ^ 2 + b := by linarith
  simp only [ridgeCoordinateRisk, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, add_zero]
  exact div_lt_div_of_pos_left (mul_pos (by positivity) hσ) (by positivity)
    (pow_lt_pow_left₀ hlt hsa.le two_ne_zero)

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 8, boundary case.
If a coordinate has zero signal and positive noise variance, the full
diagonal-penalty risk has no minimum at any finite nonnegative penalty vector. -/
theorem diagonalRidgeRisk_no_minimum_of_zero_signal {p : Type*} [Fintype p]
    (s : p → ℝ) {σ : ℝ} (hσ : 0 < σ ^ 2) {γ : p → ℝ}
    (i : p) (hs : 0 < s i) (hγ : γ i = 0) (k : p → ℝ) (hk : ∀ j, 0 ≤ k j) :
    ¬ IsMinOn (diagonalRidgeRisk s σ γ) {k | ∀ j, 0 ≤ k j} k := by
  classical
  let k' := Function.update k i (k i + 1)
  have hk' : ∀ j, 0 ≤ k' j := by
    intro j
    by_cases h : j = i
    · subst j
      simpa only [k', Function.update_self] using add_nonneg (hk i) zero_le_one
    · simpa only [k', Function.update_of_ne h] using hk j
  have hi : ridgeCoordinateRisk (s i) σ (γ i) (k' i) < ridgeCoordinateRisk (s i) σ (γ i) (k i) := by
    rw [hγ, show k' i = k i + 1 from Function.update_self i (k i + 1) k]
    exact ridgeCoordinateRisk_zero_signal_strictAntiOn hs hσ (hk i)
      (add_nonneg (hk i) zero_le_one) (lt_add_one _)
  have hlt : diagonalRidgeRisk s σ γ k' < diagonalRidgeRisk s σ γ k := by
    apply Finset.sum_lt_sum
    · intro j _
      by_cases h : j = i
      · subst j
        exact hi.le
      · simp only [k', Function.update_of_ne h, le_refl]
    · exact ⟨i, Finset.mem_univ _, hi⟩
  exact fun h => hlt.not_ge (isMinOn_iff.mp h k' hk')

end OptimalPenalty

section BLUE

open MeasureTheory ProbabilityTheory

variable {Ω n p : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- **Equations (18) and (48)** of [benIsrael2003generalized], Chapter 8.
The matrix at the zero-penalty endpoint is the best linear unbiased
coefficient for the full parameter in the isotropic model. -/
theorem ridgeEstimator_zero_isBLUE {X : Matrix n p ℝ} (hX : X.rank = Fintype.card p)
    (σ : ℝ) {Y : (p → ℝ) → Ω → n → ℝ}
    (hY : IsLinearStatisticalModel μ X (σ ^ 2 • (1 : Matrix n n ℝ)) Y) :
    IsBestLinearUnbiasedEstimator X (σ ^ 2 • (1 : Matrix n n ℝ))
      (1 : Matrix p p ℝ) (X.tikhonov 0) := by
  rw [ridgeCoefficient_zero X hX]
  simpa only [Matrix.one_mul] using (theorem_1 σ hY hX (1 : Matrix p p ℝ)).2.1

end BLUE

end BenIsraelGreville.Chapter08
