import Numlib.Optimization.Quadratic.HardCase.Iteration
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The metric projection condition for generalized inverse iteration

The printed Euclidean projection guard fails for generalized eigenvectors. The
concrete symmetric operators have M=[[1,-1],[-1,2]], H=[[-1,1],[1,-1]],
least eigenvector (1,0), and trapped eigenvector (1,1). The metric is genuinely
coercive. Every actual normalized inverse step fixes the trapped vector, so the
legal fixed controls n=2, gamma=2, omega=1 generate shift_next=shift squared.
Arbitrarily close shifts above the least spectral edge consequently fail to
converge, despite satisfying the printed guard and all primitive algorithm rules.
-/

namespace QuadraticSecular.HardCaseCounterexample
open WithLp
open scoped Matrix
/-- The concrete two-dimensional Euclidean space of the counterexample. -/
abbrev Space := EuclideanSpace ℝ (Fin 2)

/-- A positive-definite metric with nonorthogonal Euclidean generalized eigenvectors. -/
noncomputable def metric : Space →L[ℝ] Space :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) ![![1, -1], ![-1, 2]]

/-- A symmetric Hessian with generalized eigenvalues -1 and zero. -/
noncomputable def hessian : Space →L[ℝ] Space :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) ![![-1, 1], ![1, -1]]

/-- A metric-unit generalized eigenvector for eigenvalue -1. -/
noncomputable def leastVector : Space := toLp 2 ![1, 0]

/-- A metric-unit generalized eigenvector for eigenvalue zero. -/
noncomputable def trappedVector : Space := toLp 2 ![1, 1]

/-- The metric operator in explicit Euclidean coordinates. -/
theorem metric_apply (x : Space) : metric x = toLp 2 ![x 0 - x 1, -x 0 + 2 * x 1] := by
  ext i
  change (![![1, -1], ![-1, 2]] *ᵥ (ofLp x)) i = (![x 0 - x 1, -x 0 + 2 * x 1]) i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-- The Hessian operator in explicit Euclidean coordinates. -/
theorem hessian_apply (x : Space) : hessian x = toLp 2 ![-x 0 + x 1, x 0 - x 1] := by
  ext i
  change (![![-1, 1], ![1, -1]] *ᵥ (ofLp x)) i = (![-x 0 + x 1, x 0 - x 1]) i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-- The genuine metric bilinear form. -/
theorem inner_metric (x y : Space) : inner ℝ (metric x) y =
    (x 0 - x 1) * y 0 + (-x 0 + 2 * x 1) * y 1 := by
  rw [metric_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The genuine Hessian bilinear form. -/
theorem inner_hessian (x y : Space) : inner ℝ (hessian x) y =
    (-x 0 + x 1) * y 0 + (x 0 - x 1) * y 1 := by
  rw [hessian_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The concrete metric is symmetric and coercive with a uniform positive bound. -/
theorem metric_coercive : metric.toLinearMap.IsSymmetricCoercive := by
  constructor
  · intro x y
    change inner ℝ (metric x) y = inner ℝ x (metric y)
    calc _ = inner ℝ (metric y) x := by rw [inner_metric, inner_metric]; ring
      _ = _ := real_inner_comm _ _
  · refine ⟨1 / 4, by norm_num, fun x => ?_⟩
    change 1 / 4 * ‖x‖ ^ 2 ≤ inner ℝ (metric x) x
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, inner_metric]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - 2 * x 1), sq_nonneg (x 1)]

/-- The concrete Hessian is symmetric. -/
theorem hessian_symmetric : hessian.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (hessian x) y = inner ℝ x (hessian y)
  calc _ = inner ℝ (hessian y) x := by rw [inner_hessian, inner_hessian]; ring
    _ = _ := real_inner_comm _ _

/-- The starting higher-eigenspace vector is metric-unit. -/
theorem trapped_metric_norm : energyNorm metric.toLinearMap trappedVector = 1 := by
  unfold energyNorm
  change Real.sqrt (inner ℝ (metric trappedVector) trappedVector) = 1
  rw [inner_metric]
  norm_num [trappedVector]

/-- The least generalized eigenvector is metric-unit. -/
theorem least_metric_norm : energyNorm metric.toLinearMap leastVector = 1 := by
  unfold energyNorm
  change Real.sqrt (inner ℝ (metric leastVector) leastVector) = 1
  rw [inner_metric]
  norm_num [leastVector]

/-- The trapped vector satisfies the source's printed Euclidean projection condition. -/
theorem printed_projection : inner ℝ trappedVector leastVector = 1 := by
  simp [trappedVector, leastVector, PiLp.inner_apply, Fin.sum_univ_two]

/-- Its actual metric projection onto the least generalized eigenspace is zero. -/
theorem metric_projection_zero : inner ℝ (metric trappedVector) leastVector = 0 := by
  rw [inner_metric]
  norm_num [trappedVector, leastVector]

/-- The least vector is an actual generalized eigenvector of eigenvalue -1. -/
theorem least_eigenvector : hessian leastVector = -(1 : ℝ) • metric leastVector := by
  rw [hessian_apply, metric_apply]
  ext i
  fin_cases i <;> norm_num [leastVector]

/-- The trapped vector is an actual generalized eigenvector of eigenvalue zero. -/
theorem trapped_eigenvector : hessian trappedVector = 0 := by
  rw [hessian_apply]
  ext i
  fin_cases i <;> norm_num [trappedVector]

/-- Every Rayleigh value on the metric unit sphere is at least -1. -/
theorem least_rayleigh {x : Space} (hx : energyNorm metric.toLinearMap x = 1) :
    -1 ≤ inner ℝ (hessian x) x := by
  have he := metric_coercive.energyNorm_sq x
  rw [hx] at he
  change 1 ^ 2 = inner ℝ (metric x) x at he
  rw [inner_metric] at he
  rw [inner_hessian]
  nlinarith [sq_nonneg (x 1)]

/-- Every shift greater than one gives an actual positive-definite shifted pencil. -/
theorem shifted_positive {τ : ℝ} (hτ : 1 < τ) (x : Space) (hx : x ≠ 0) :
    0 < inner ℝ ((hessian + τ • metric) x) x := by
  simp only [add_apply, smul_apply, inner_add_left, real_inner_smul_left,
    inner_hessian, inner_metric]
  have hs : 0 < (x 0 - x 1) ^ 2 + (x 1) ^ 2 := by
    have hne : x 0 - x 1 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hn
      push Not at hn
      have h0 : x 0 = 0 := by linarith [hn.1, hn.2]
      apply hx
      ext i
      fin_cases i <;> simp_all
    rcases hne with h | h
    · positivity
    · positivity
  have hm := mul_pos (sub_pos.mpr hτ) hs
  nlinarith [sq_nonneg (x 1)]

/-- Positive-definite shifted pencils have genuine continuous linear inverses. -/
theorem shifted_invertible {τ : ℝ} (hτ : 1 < τ) :
    (hessian + τ • metric).IsInvertible := by
  have hinj : Function.Injective (hessian + τ • metric) := by
    intro v w he
    by_contra hne
    have hh := shifted_positive hτ (v - w) (sub_ne_zero.mpr hne)
    rw [map_sub, he, sub_self, inner_zero_left] at hh
    linarith
  let e : Space ≃ₗ[ℝ] Space := LinearEquiv.ofBijective
    (hessian + τ • metric).toLinearMap
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

/-- The actual shifted inverse applied to the metric of the trapped eigenvector. -/
theorem raw_inverse {τ : ℝ} (hτ : 1 < τ) :
    (hessian + τ • metric).inverse (metric trappedVector) = τ⁻¹ • trappedVector := by
  have hInv := shifted_invertible hτ
  apply hInv.injective
  rw [hInv.self_apply_inverse, map_smul, add_apply, trapped_eigenvector, smul_apply,
    zero_add, smul_smul, inv_mul_cancel₀ (by linarith : τ ≠ 0), one_smul]

/-- The inverse vector's metric normalization factor is the positive reciprocal shift. -/
theorem inverse_metric_norm {τ : ℝ} (hτ : 1 < τ) :
    energyNorm metric.toLinearMap (τ⁻¹ • trappedVector) = τ⁻¹ := by
  change ‖WithEnergy.equiv metric.toLinearMap metric_coercive
    (τ⁻¹ • trappedVector)‖ = τ⁻¹
  rw [map_smul, norm_smul, WithEnergy.norm_equiv, trapped_metric_norm, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by linarith : 0 < τ)), mul_one]

/-- Every actual normalized inverse step fixes the wrongly initialized vector. -/
theorem inverseStep_fixed {τ : ℝ} (hτ : 1 < τ) :
    HardCase.inverseStep hessian metric τ trappedVector = trappedVector := by
  rw [HardCase.inverseStep_eq, raw_inverse hτ, inverse_metric_norm hτ, inv_inv, smul_smul,
    mul_inv_cancel₀ (by linarith : τ ≠ 0), one_smul]

/-- The Rayleigh value of the trapped vector is zero. -/
theorem trapped_rayleigh : HardCase.rayleighValue hessian trappedVector = 0 := by
  simp [HardCase.rayleighValue_apply, trapped_eigenvector]

/-- The actual Rayleigh value at the least generalized eigenvector is -1. -/
theorem least_rayleigh_value : inner ℝ (hessian leastVector) leastVector = -1 := by
  rw [inner_hessian]
  norm_num [leastVector]

/-- The shifts generated by the counterexample's exact legal updates. -/
noncomputable def shifts (a : ℝ) : ℕ → ℝ
  | 0 => a
  | k + 1 => shifts a k ^ 2

/-- Every counterexample shift stays strictly above the least spectral edge. -/
theorem shifts_gt_one {a : ℝ} (ha : 1 < a) (k : ℕ) : 1 < shifts a k := by
  induction k with
  | zero => exact ha
  | succ k ih => rw [shifts]; nlinarith

/-- Every counterexample shift remains at least its initial distance from the target. -/
theorem initial_le_shifts {a : ℝ} (ha : 1 < a) (k : ℕ) : a ≤ shifts a k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [shifts]
    have hh := shifts_gt_one ha k
    nlinarith

/-- The exact shift sequence cannot converge to the leftmost generalized spectral edge. -/
theorem shifts_not_tendsto {a : ℝ} (ha : 1 < a) :
    ¬Filter.Tendsto (shifts a) Filter.atTop (nhds 1) := by
  intro ht
  have hh : a ≤ 1 := ge_of_tendsto ht (Filter.Eventually.of_forall (initial_le_shifts ha))
  linarith

/-- All source parameter bounds and primitive updates hold for this actual
normalized inverse-iteration run: n=2, gamma=2 and omega=1. -/
theorem run_of_gt_one {a : ℝ} (ha : 1 < a) :
    HardCase.Run hessian metric (-1) (shifts a) (fun _ => trappedVector)
      (fun _ _ => trappedVector) (fun _ => 2) (fun _ => 2) (fun _ => 1)
      1 1 (3 / 2) (1 / 2) (2 : WithTop ℕ) := by
  refine {
    omega_pos := by norm_num
    omega_ordered := le_rfl
    gamma_upper_pos := by norm_num
    gamma_upper_le_one := by norm_num
    gamma_lower_gt_one := by norm_num
    gamma_ordered := by norm_num
    count_upper_pos := by norm_num
    initial_shift := by simpa only [neg_neg, shifts] using ha
    initial_unit := trapped_metric_norm
    count_pos := fun _ => by norm_num
    count_le := fun _ => le_rfl
    weight_range := fun _ => ⟨le_rfl, le_rfl⟩
    exponent_range := fun _ => by norm_num
    shifted_invertible := fun k => shifted_invertible (shifts_gt_one ha k)
    inner_initial := fun _ => rfl
    inner_update := fun k _ _ => (inverseStep_fixed (shifts_gt_one ha k)).symm
    vector_update := fun _ => rfl
    shift_update := ?_ }
  intro k
  rw [trapped_rayleigh]
  simp only [shifts, neg_zero, add_zero, one_mul]
  rw [Real.rpow_two, zero_add]

/-- With zero objective gradient the actual shifts also belong to the source's
upper secular region for the cubic comparison function tau(lambda)=lambda squared. -/
theorem upper_secular_region {a : ℝ} (ha : 1 < a) (k : ℕ) :
    secular hessian metric 0 (shifts a k) < shifts a k ^ 2 := by
  simp only [secular, solution, map_zero, neg_zero, inner_zero_left]
  exact sq_pos_of_pos (lt_trans (by norm_num) (shifts_gt_one ha k))

/-- Arbitrarily close initial shifts give actual legal runs that do not converge
when initialized using the printed Euclidean projection condition. -/
theorem arbitrarily_close_counterexample {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℝ, 1 < a ∧ a < 1 + δ ∧
      HardCase.Run hessian metric (-1) (shifts a) (fun _ => trappedVector)
        (fun _ _ => trappedVector) (fun _ => 2) (fun _ => 2) (fun _ => 1)
        1 1 (3 / 2) (1 / 2) (2 : WithTop ℕ) ∧
      ¬Filter.Tendsto (shifts a) Filter.atTop (nhds 1) := by
  refine ⟨1 + δ / 2, by linarith, by linarith, run_of_gt_one (by linarith),
    shifts_not_tendsto (by linarith)⟩

end QuadraticSecular.HardCaseCounterexample
