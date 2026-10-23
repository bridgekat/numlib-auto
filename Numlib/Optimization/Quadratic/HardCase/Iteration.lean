import Numlib.Optimization.Quadratic.Secular

/-!
# Primitive normalized generalized inverse iteration

The trace contains only the exact inverse solves, normalization, Rayleigh
calculation and parameter updates. Spectral projection and convergence conditions
are kept separate from the primitive algorithmic operations.
-/

namespace QuadraticSecular.HardCase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One actual generalized inverse solve followed by metric normalization. -/
noncomputable def inverseStep (H M : E →L[ℝ] E) (τ : ℝ) (v : E) : E :=
  let u := (H + τ • M).inverse (M v)
  (energyNorm M.toLinearMap u)⁻¹ • u

/-- The inverse-step normalization formula, exposing its actual solve and metric norm. -/
theorem inverseStep_eq (H M : E →L[ℝ] E) (τ : ℝ) (v : E) :
    inverseStep H M τ v =
      (energyNorm M.toLinearMap ((H + τ • M).inverse (M v)))⁻¹ •
        (H + τ • M).inverse (M v) := rfl

/-- The Rayleigh value of a metric-unit vector, as computed by Algorithm 9.3.1. -/
noncomputable def rayleighValue (H : E →L[ℝ] E) (v : E) : ℝ := inner ℝ v (H v)

/-- The Rayleigh evaluation is the actual Hessian quadratic form. -/
@[simp] theorem rayleighValue_apply (H : E →L[ℝ] E) (v : E) :
    rayleighValue H v = inner ℝ v (H v) := rfl

/-- The primitive exact trace of Algorithm 9.3.1, with its legal parameter ranges.
The spectral-start projection is an additional hypothesis of convergence results,
not a surrogate convergence assumption in this trace. -/
structure Run (H M : E →L[ℝ] E) (least : ℝ) (shift : ℕ → ℝ) (vector : ℕ → E)
    (innerVector : ℕ → ℕ → E) (count : ℕ → ℕ) (exponent weight : ℕ → ℝ)
    (ωL ωU γL γU : ℝ) (nU : WithTop ℕ) : Prop where
  omega_pos : 0 < ωL
  omega_ordered : ωL ≤ ωU
  gamma_upper_pos : 0 < γU
  gamma_upper_le_one : γU ≤ 1
  gamma_lower_gt_one : 1 < γL
  gamma_ordered : γL ≤ 2 - γU
  count_upper_pos : (1 : WithTop ℕ) ≤ nU
  initial_shift : -least < shift 0
  initial_unit : energyNorm M.toLinearMap (vector 0) = 1
  count_pos : ∀ k, 1 ≤ count k
  count_le : ∀ k, (count k : WithTop ℕ) ≤ nU
  weight_range : ∀ k, ωL ≤ weight k ∧ weight k ≤ ωU
  exponent_range : ∀ k, γL ≤ exponent k ∧ exponent k ≤ 2 * count k - γU
  shifted_invertible : ∀ k, (H + shift k • M).IsInvertible
  inner_initial : ∀ k, innerVector k 0 = vector k
  inner_update : ∀ k i, i < count k →
    innerVector k (i + 1) = inverseStep H M (shift k) (innerVector k i)
  vector_update : ∀ k, vector (k + 1) = innerVector k (count k)
  shift_update : ∀ k, shift (k + 1) = -rayleighValue H (vector (k + 1)) +
    weight k * (shift k + rayleighValue H (vector (k + 1))) ^ exponent k

end QuadraticSecular.HardCase
