import Numlib.Optimization.Subproblem.Matrix

/-!
# Cartis–Gould–Toint §8.1: The context of the step computation

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §8.1: the two subproblems of the
step computation, for a vector `g` and a symmetric matrix `H` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`
and a symmetric positive definite scaling matrix `M`.

## Main definitions

* `mNorm M v` — the scaled norm `‖v‖_M = √⟪v, M v⟫`; the dual norm `‖v‖_{M⁻¹}` is `mNorm M⁻¹ v`.
* `model g H s` — the quadratic model (8.1.1).
* `regModel g H M σ r s` — the regularized model (8.1.4), with the book's `1/r` normalization
  (footnote 59).
* `IsTrustRegionSolution g H M Δ s` — `s` is a global minimizer of the trust-region subproblem
  (8.1.2).
* `IsRegularizationSolution g H M σ r s` — `s` is a global minimizer of the regularization
  subproblem (8.1.3).

## Main results

The bridge to the operator backbone `Numlib.Optimization.Subproblem`: in the `M`-inner product space
`Subproblem.ScaledSpace hM` the scaled norm is the norm (`mNorm_eq_norm_toScaled`), the models are
the operator models of `M⁻¹ g` and `M⁻¹ H` (`model_eq_quadModel`, `regModel_eq_regModel`), and the
two subproblems are the operator subproblems (`isTrustRegionSolution_iff_scaled`,
`isRegularizationSolution_iff_scaled`).
-/

open Matrix Set Metric
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter08

open Subproblem

variable {n : ℕ}

/-- The **scaled norm** `‖v‖_M = √⟪v, M v⟫` of [cartis2022evaluation] §8.1 (after (8.1.4)). For a
positive definite `M` it is the norm of the `M`-inner product space (`mNorm_eq_norm_toScaled`); the
dual norm `‖v‖_{M⁻¹}` is `mNorm M⁻¹ v`. -/
noncomputable def mNorm (M : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  √⟪v, toEuclideanLin M v⟫

/-- The **quadratic model** `m(s) = ⟪g, s⟫ + ½ ⟪s, H s⟫` ([cartis2022evaluation] (8.1.1)). -/
noncomputable def model (g : EuclideanSpace ℝ (Fin n)) (H : Matrix (Fin n) (Fin n) ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫

/-- The **regularized model** `m^R(s, σ, r) = m(s) + (1/r) σ ‖s‖_M^r` ([cartis2022evaluation]
(8.1.4), with `r ≥ 2` in the book; `‖s‖_M ^ r` is the real power). -/
noncomputable def regModel (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  model g H s + (1 / r) * σ * mNorm M s ^ r

/-- `s` is a **global minimizer of the trust-region subproblem** (8.1.2) of [cartis2022evaluation]:
`‖s‖_M ≤ Δ` and `m(s) ≤ m(u)` for every `u` with `‖u‖_M ≤ Δ`. -/
def IsTrustRegionSolution (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  mNorm M s ≤ Δ ∧ ∀ u, mNorm M u ≤ Δ → model g H s ≤ model g H u

/-- `s` is a **global minimizer of the regularization subproblem** (8.1.3) of
[cartis2022evaluation]: `m^R(s, σ, r) ≤ m^R(u, σ, r)` for every `u`. -/
def IsRegularizationSolution (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ u, regModel g H M σ r s ≤ regModel g H M σ r u

variable {g s : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

theorem isTrustRegionSolution_iff {Δ : ℝ} :
    IsTrustRegionSolution g H M Δ s ↔
      mNorm M s ≤ Δ ∧ ∀ u, mNorm M u ≤ Δ → model g H s ≤ model g H u :=
  Iff.rfl

theorem isRegularizationSolution_iff {σ r : ℝ} :
    IsRegularizationSolution g H M σ r s ↔ ∀ u, regModel g H M σ r s ≤ regModel g H M σ r u :=
  Iff.rfl

/-- The scaled norm is nonnegative. -/
theorem mNorm_nonneg (M : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ mNorm M v :=
  Real.sqrt_nonneg _

/-! ### The bridge to the `M`-inner product space -/

/-- The scaled norm is the norm of the `M`-inner product space. -/
theorem mNorm_eq_norm_toScaled (hM : M.PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    mNorm M v = ‖toScaled hM v‖ := by
  rw [mNorm, norm_toScaled, real_inner_comm]

/-- `‖v‖_M² = ⟪v, M v⟫`. -/
theorem mNorm_sq (hM : M.PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    mNorm M v ^ 2 = ⟪v, toEuclideanLin M v⟫ := by
  rw [mNorm_eq_norm_toScaled hM, norm_toScaled_sq, real_inner_comm]

/-- The dual norm `‖g‖_{M⁻¹}` is the norm of the scaled gradient `M⁻¹ g`. -/
theorem mNorm_inv_eq_norm_scaledGrad (hM : M.PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    mNorm M⁻¹ v = ‖scaledGrad hM v‖ := by
  rw [mNorm, ← norm_scaledGrad_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The quadratic model is the operator model of `M⁻¹ g` and `M⁻¹ H` in the `M`-inner product
space. -/
theorem model_eq_quadModel (hM : M.PosDef) (s : EuclideanSpace ℝ (Fin n)) :
    model g H s = quadModel (scaledGrad hM g) (scaledOp H hM) (toScaled hM s) :=
  quadModel_scaled g s

/-- The regularized model is the operator regularized model of `M⁻¹ g` and `M⁻¹ H` in the
`M`-inner product space. -/
theorem regModel_eq_regModel (hM : M.PosDef) (σ r : ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    regModel g H M σ r s =
      Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r (toScaled hM s) := by
  rw [Subproblem.regModel_def, ← model_eq_quadModel hM, ← mNorm_eq_norm_toScaled hM, regModel]
  ring

/-- **Bridge for the trust-region subproblem**: `s` solves (8.1.2) iff `M⁻¹`-transported it is a
global minimizer of the operator model on the closed ball of radius `Δ` of the `M`-inner product
space. -/
theorem isTrustRegionSolution_iff_scaled (hM : M.PosDef) {Δ : ℝ} :
    IsTrustRegionSolution g H M Δ s ↔
      ‖toScaled hM s‖ ≤ Δ ∧
        IsMinOn (quadModel (scaledGrad hM g) (scaledOp H hM)) (closedBall 0 Δ) (toScaled hM s) := by
  simp only [IsTrustRegionSolution, isMinOn_iff, mem_closedBall_zero_iff,
    mNorm_eq_norm_toScaled hM, model_eq_quadModel hM]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h u hu => h _ hu⟩
  obtain ⟨u, rfl⟩ := (toScaled hM).surjective x
  exact h u hx

/-- **Bridge for the regularization subproblem**: `s` solves (8.1.3) iff `M⁻¹`-transported it is a
global minimizer of the operator regularized model. -/
theorem isRegularizationSolution_iff_scaled (hM : M.PosDef) {σ r : ℝ} :
    IsRegularizationSolution g H M σ r s ↔
      IsMinOn (Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r) univ
        (toScaled hM s) := by
  simp only [IsRegularizationSolution, isMinOn_univ_iff, regModel_eq_regModel hM]
  refine ⟨fun h x => ?_, fun h u => h _⟩
  obtain ⟨u, rfl⟩ := (toScaled hM).surjective x
  exact h u

/-- The scaled norm for `M = I` is the Euclidean norm. -/
@[simp]
theorem mNorm_one (x : EuclideanSpace ℝ (Fin n)) : mNorm 1 x = ‖x‖ := by
  rw [mNorm, toEuclideanLin_one, LinearMap.id_apply, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

end CartisGouldToint.Chapter08
