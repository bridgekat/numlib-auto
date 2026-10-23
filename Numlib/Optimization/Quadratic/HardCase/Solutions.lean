import Numlib.Optimization.Quadratic.Secular
import Numlib.Optimization.Quadratic.Optimality.RegularizationMetric
import Mathlib.Tactic

/-!
# Compatible shifted-pencil solutions and metric generalized inverses

The bounded spectral inverse uses zero reciprocal on singular components.
Its generalized-inverse identity and metric kernel orthogonality are proved
from the actual operators and complete generalized eigenbasis. These also
give exact quadratic values and full nullspace decompositions.
-/

open scoped BigOperators
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The spectral particular solution is the finite sum of minus the gradient coefficient divided
  by the shifted eigenvalue, using real division so singular zero coefficients contribute zero. -/
noncomputable def particular (g : E) (τ : ℝ) : E :=
  ∑ i, (-inner ℝ g (B.basis i) / (τ + B.eigenvalue i)) • B.basis i

omit [Fintype ι] in
/-- An actual shifted-pencil solution forces every gradient coefficient at a singular shifted
  eigenvalue to vanish. -/
theorem coefficient_zero_of_singular_solve [Finite ι] (g s : E) (τ : ℝ)
    (hsolve : (H + τ • M) s = -g) (i : ι) (hi : τ + B.eigenvalue i = 0) :
    inner ℝ g (B.basis i) = 0 := by
  have hh := B.shifted_apply_inner τ s i
  rw [hsolve, inner_neg_left, hi, mul_zero] at hh
  linarith

/-- The particular spectral vector solves the original shifted linear system whenever that system
  is compatible. -/
theorem particular_solves (g s : E) (τ : ℝ) (hsolve : (H + τ • M) s = -g) :
    (H + τ • M) (B.particular g τ) = -g := by
  rw [particular, B.shifted_sum]
  have he (i : ι) : (-inner ℝ g (B.basis i) / (τ + B.eigenvalue i)) * (τ + B.eigenvalue i) = 
      -inner ℝ g (B.basis i) := by
    by_cases hi : τ + B.eigenvalue i = 0
    · rw [B.coefficient_zero_of_singular_solve g s τ hsolve i hi]
      simp
    · exact div_mul_cancel₀ _ hi
  simp only [he]
  simpa only [neg_smul, Finset.sum_neg_distrib] using
    (congrArg Neg.neg (B.dual_expansion g))

/-- Every actual shifted-system solution is the particular vector plus a vector in the full
  shifted kernel. -/
theorem kernel_decomposition (g s : E) (τ : ℝ) (hsolve : (H + τ • M) s = -g) :
    ∃ v : E, (H + τ • M) v = 0 ∧ s = B.particular g τ + v := by
  refine ⟨s - B.particular g τ, ?_, by abel⟩
  rw [map_sub, hsolve, B.particular_solves g s τ hsolve, sub_self]

omit [Fintype ι] in
/-- The gradient is orthogonal to every shifted-kernel vector when the original symmetric pencil
  equation holds. -/
theorem inner_kernel_zero (hH : H.toLinearMap.IsSymmetric)
    (hM : M.toLinearMap.IsSymmetric) (g s v : E) (τ : ℝ)
    (hsolve : (H + τ • M) s = -g) (hv : (H + τ • M) v = 0) : inner ℝ g v = 0 := by
  have hsym : (H + τ • M).toLinearMap.IsSymmetric := hH.add (hM.smul (by simp))
  have hh := hsym s v
  change inner ℝ ((H + τ • M) s) v = inner ℝ s ((H + τ • M) v) at hh
  rw [hsolve, hv, inner_neg_left, inner_zero_right] at hh
  linarith

/-- Every compatible solution has the same gradient inner product as the particular spectral
  solution. -/
theorem inner_particular_eq (hH : H.toLinearMap.IsSymmetric)
    (hM : M.toLinearMap.IsSymmetric) (g s : E) (τ : ℝ)
    (hsolve : (H + τ • M) s = -g) : inner ℝ g s = inner ℝ g (B.particular g τ) := by
  obtain ⟨v, hv, hs⟩ := B.kernel_decomposition g s τ hsolve
  rw [hs, inner_add_right, inner_kernel_zero hH hM g s v τ hsolve hv, add_zero]

/-- When all shifted eigenvalues are positive, the original solution equals the particular
  spectral vector. -/
theorem particular_eq_of_positive (g s : E) (τ : ℝ)
    (hsolve : (H + τ • M) s = -g) (hpos : ∀ i, 0 < τ + B.eigenvalue i) :
    s = B.particular g τ :=
  B.shifted_injective τ (fun i => (hpos i).ne') (hsolve.trans (B.particular_solves g s τ
    hsolve).symm)

end QuadraticSecular.PencilBasis

namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

omit [Nonempty ι] [Fintype ι] in
/-- Shifted positive semidefiniteness makes every shifted generalized eigenvalue nonnegative. -/
theorem denominator_nonneg_of_psd [Finite ι] (τ : ℝ)
    (hPSD : ∀ v, 0 ≤ inner ℝ ((H + τ • M) v) v) (i : ι) : 0 ≤ τ + B.eigenvalue i := by
  have hh := B.shifted_apply_inner τ (B.basis i) i
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, one_mul] at hh
  rw [←hh]
  exact hPSD _

/-- A positive-semidefinite pencil shift is at least minus the leftmost generalized eigenvalue. -/
theorem shift_ge_neg_leftmost (τ : ℝ)
    (hPSD : ∀ v, 0 ≤ inner ℝ ((H + τ • M) v) v) : -B.leftmost ≤ τ := by
  have hh : -τ ≤ B.leftmost := by
    apply Finset.le_inf'
    intro i hi
    have := B.denominator_nonneg_of_psd τ hPSD i
    linarith
  linarith

/-- A shift strictly above minus the leftmost eigenvalue makes all spectral denominators positive.
-/
theorem denom_pos_of_gt_neg_leftmost {τ : ℝ} (hτ : -B.leftmost < τ) (i : ι) :
    0 < τ + B.eigenvalue i := by
  have hh : B.leftmost ≤ B.eigenvalue i := Finset.inf'_le _ (Finset.mem_univ i)
  linarith

/-- At the singular leftmost shift every shifted-kernel correction belongs to the full leftmost
  generalized eigenspace. -/
theorem kernel_eigenvector {τ : ℝ} {v : E} (hτ : τ = -B.leftmost)
    (hv : (H + τ • M) v = 0) : H v = B.leftmost • M v := by
  change H v + τ • M v = 0 at hv
  rw [hτ, neg_smul] at hv
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hv)

end QuadraticSecular.PencilBasis

namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The actual bounded linear generalized inverse of the shifted pencil is the spectral reciprocal
  sum with zero reciprocal on singular components. -/
noncomputable def metricInverse (τ : ℝ) : E →L[ℝ] E :=
  ∑ i, (τ + B.eigenvalue i)⁻¹ • (innerSL ℝ (B.basis i)).smulRight (B.basis i)

/-- The particular vector is minus the actual metric generalized inverse applied to the original
  gradient. -/
theorem particular_eq_neg_metricInverse (g : E) (τ : ℝ) :
    B.particular g τ = -(B.metricInverse τ g) := by
  simp only [particular, metricInverse, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm (B.basis i), smul_smul]
  module

/-- The metric-basis coordinates of the particular vector are the exact reciprocal spectral
  coefficients. -/
theorem particular_coordinate (g : E) (τ : ℝ) (i : ι) :
    B.basis.repr (B.particular g τ) i = -inner ℝ g (B.basis i) / (τ + B.eigenvalue i) := by
  simp only [particular, map_sum, map_smul, Module.Basis.repr_self]
  simp [Finset.sum_apply, Finsupp.single_apply]

/-- The actual bounded spectral inverse satisfies the generalized-inverse identity A G A equals A
  at every shift, including singular shifts. -/
theorem generalized_inverse_identity (τ : ℝ) (v : E) :
    (H + τ • M) (B.metricInverse τ ((H + τ • M) v)) = (H + τ • M) v := by
  have hp := B.particular_solves (-((H + τ • M) v)) v τ (by simp)
  rw [B.particular_eq_neg_metricInverse] at hp
  simpa only [map_neg, neg_neg] using hp

end QuadraticSecular.PencilBasis

namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The value of the actual quadratic at a shifted-pencil solution is one half of the gradient
  inner product minus the shift times squared metric radius. -/
theorem quadratic_value (hM : M.toLinearMap.IsSymmetricCoercive) (g s : E) (τ : ℝ)
    (hsolve : (H + τ • M) s = -g) :
    QuadraticOptimality.model H g s = (inner ℝ g s - τ * energyNorm M.toLinearMap s ^ 2) / 2 :=
      by
  have hh := congrArg (fun v : E => inner ℝ v s) hsolve
  simp only [add_apply, smul_apply, inner_add_left, real_inner_smul_left,
    inner_neg_left] at hh
  rw [QuadraticOptimality.model_eq, hM.energyNorm_sq]
  change inner ℝ g s + inner ℝ (H s) s / 2 = (inner ℝ g s - τ * inner ℝ (M s) s) / 2
  linarith

/-- Complementary slackness gives the exact trust-region minimum-value formula with the particular
  solution and the squared trust radius. -/
theorem trust_region_value (hH : H.toLinearMap.IsSymmetric)
    (hM : M.toLinearMap.IsSymmetricCoercive) (g s : E) {τ Δ : ℝ}
    (hsolve : (H + τ • M) s = -g)
    (hcomp : τ * (energyNorm M.toLinearMap s ^ 2 - Δ ^ 2) = 0) :
    QuadraticOptimality.model H g s = (inner ℝ g (B.particular g τ) - τ * Δ ^ 2) / 2 := by
  rw [quadratic_value hM g s τ hsolve, B.inner_particular_eq hH hM.isSymmetric g s τ hsolve]
  nlinarith

/-- For positive sigma and real exponent greater than two, the exact multiplier equation gives the
  metric radius as the inverse power of the multiplier divided by sigma, including zero. -/
theorem radius_of_multiplier (M : E →L[ℝ] E) (s : E)
    {r σ τ : ℝ} (hr : 2 < r) (hσ : 0 < σ)
    (hτ : τ = σ * energyNorm M.toLinearMap s ^ (r - 2)) :
    energyNorm M.toLinearMap s = (τ / σ) ^ (1 / (r - 2)) := by
  have hh : τ / σ = energyNorm M.toLinearMap s ^ (r - 2) := by rw [hτ]; field_simp
  rw [hh, ← Real.rpow_mul (energyNorm_nonneg _ _)]
  have he : (r - 2) * (1 / (r - 2)) = 1 := by field_simp [show r - 2 ≠ 0 by linarith]
  rw [he, Real.rpow_one]

/-- The actual weighted real-power regularized model has exactly the printed minimum-value formula
  at every compatible stationary vector with the norm-power multiplier. -/
theorem regularization_value (hH : H.toLinearMap.IsSymmetric)
    (hM : M.toLinearMap.IsSymmetricCoercive) (g s : E) {r σ τ : ℝ}
    (hr : 2 < r) (hσ : 0 < σ) (hsolve : (H + τ • M) s = -g)
    (hτ : τ = σ * energyNorm M.toLinearMap s ^ (r - 2)) :
    QuadraticOptimality.model H g s + σ / r * energyNorm M.toLinearMap s ^ r = 
      (inner ℝ g (B.particular g τ) - (r - 2) / r * τ * (τ / σ) ^ (2 / (r - 2))) / 2 := by
  let R := energyNorm M.toLinearMap s
  have hpow : R ^ r = R ^ 2 * R ^ (r - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add' (energyNorm_nonneg _ _) (by linarith)]
    congr 1
    ring
  have hsq : (τ / σ) ^ (2 / (r - 2)) = R ^ 2 := by
    have hh : τ / σ = R ^ (r - 2) := by rw [hτ]; dsimp [R]; field_simp
    rw [hh, ← Real.rpow_mul (energyNorm_nonneg _ _)]
    have he : (r - 2) * (2 / (r - 2)) = 2 := by field_simp [show r - 2 ≠ 0 by linarith]
    rw [he, Real.rpow_two]
  rw [quadratic_value hM g s τ hsolve, B.inner_particular_eq hH hM.isSymmetric g s τ hsolve,
    hsq]
  change (inner ℝ g (B.particular g τ) - τ * R ^ 2) / 2 + σ / r * R ^ r = _
  rw [hpow, hτ]
  dsimp [R]
  field_simp
  ring

end QuadraticSecular.PencilBasis

namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The actual shifted-pencil quadratic form is the sum of shifted eigenvalues times squared
  metric coordinates. -/
theorem shifted_quadratic_eq_sum (τ : ℝ) (v : E) :
    inner ℝ ((H + τ • M) v) v = ∑ i, (τ + B.eigenvalue i) * (B.basis.repr v i) ^ 2 := by
  calc _ = ∑ i, (B.basis.repr v i) * inner ℝ ((H + τ • M) v) (B.basis i) := by
        nth_rw 2 [← B.basis.sum_repr v]
        simp only [inner_sum, real_inner_smul_right]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [B.shifted_apply_inner]
      ring

omit [Fintype ι] in
/-- Positive shifted eigenvalues imply positive definiteness of the original shifted pencil on all
  nonzero vectors. -/
theorem shifted_positive [Finite ι] (τ : ℝ) (hpos : ∀ i, 0 < τ + B.eigenvalue i) :
    ∀ v : E, v ≠ 0 → 0 < inner ℝ ((H + τ • M) v) v := by
  let := Fintype.ofFinite ι
  intro v hv
  have hcoeff : ∃ i, B.basis.repr v i ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hv
    apply B.basis.repr.injective
    ext i
    simp only [hh, map_zero, Finsupp.zero_apply]
  rw [B.shifted_quadratic_eq_sum]
  apply Finset.sum_pos' (fun i _ => mul_nonneg (hpos i).le (sq_nonneg _))
  obtain ⟨i, hi⟩ := hcoeff
  exact ⟨i, Finset.mem_univ _, mul_pos (hpos i) (sq_pos_of_ne_zero hi)⟩

end QuadraticSecular.PencilBasis



namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The particular spectral vector is metric-orthogonal to the entire shifted kernel, including
  repeated eigenvalues. -/
theorem particular_metric_orthogonal (g v : E) (τ : ℝ) (hv : (H + τ • M) v = 0) :
    inner ℝ (M (B.particular g τ)) v = 0 := by
  nth_rw 1 [← B.basis.sum_repr v]
  simp only [inner_sum, real_inner_smul_right, particular, B.inner_metric_sum]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hz : τ + B.eigenvalue i = 0
  · simp only [hz, div_zero, mul_zero]
  · have hh := B.shifted_apply_inner τ v i
    rw [hv, inner_zero_left] at hh
    have hc : B.basis.repr v i = 0 := (mul_eq_zero.mp hh.symm).resolve_right hz
    rw [hc, zero_mul]

/-- The squared metric norm of a particular vector plus any scalar multiple of a kernel vector is
  the sum of the particular squared norm and the scalar square times the kernel squared norm. -/
theorem metric_norm_sq_add_kernel (hM : M.toLinearMap.IsSymmetricCoercive)
    (g v : E) (τ a : ℝ) (hv : (H + τ • M) v = 0) :
    energyNorm M.toLinearMap (B.particular g τ + a • v) ^ 2 = 
      energyNorm M.toLinearMap (B.particular g τ) ^ 2 + a ^ 2 * energyNorm M.toLinearMap v ^ 2 :=
        by
  rw [hM.energyNorm_sq, hM.energyNorm_sq, hM.energyNorm_sq]
  change inner ℝ (M (B.particular g τ + a • v)) (B.particular g τ + a • v) = 
    inner ℝ (M (B.particular g τ)) (B.particular g τ) + a ^ 2 * inner ℝ (M v) v
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [B.particular_metric_orthogonal g v τ hv]
  have hh : inner ℝ (M v) (B.particular g τ) = 0 := by
    exact ((hM.isSymmetric v (B.particular g τ)).trans
      (real_inner_comm _ _)).trans (B.particular_metric_orthogonal g v τ hv)
  rw [hh]
  ring

end QuadraticSecular.PencilBasis
