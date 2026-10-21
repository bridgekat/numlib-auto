import Numlib.Analysis.Calculus.LinearPullbackLipschitzJets
import Numlib.Analysis.SpecialFunctions.CappedQuadratic
import Numlib.Analysis.SpecialFunctions.InverseSqrtTail
import Numlib.Optimization.ExactKnownErrorOracle
import Numlib.Optimization.HigherOrderRegularization
import Numlib.Optimization.TaylorCriticalityFirstOrder
import Numlib.Analysis.Calculus.IteratedFDerivSymmetry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# A positive transverse objective with a slowly decaying coordinate

The objective is the sum of a capped quadratic in the first coordinate and a positive
inverse-square-root tail in the second. All derivatives are actual ambient derivatives.
Global operator-norm Lipschitz bounds include order zero; the common constant four
follows directly from scalar pullback and triangle bounds.
-/

noncomputable section
namespace Optimization.TransverseObjective
open scoped NNReal

/-- The ordinary two-dimensional real Euclidean space. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A vector specified by its transverse and slowly decaying coordinates. -/
def point (a b : ℝ) : Plane := WithLp.toLp 2 ![a, b]

/-- The transverse coordinate of a specified point. -/
@[simp] theorem point_zero_coord (a b : ℝ) : point a b 0 = a := rfl

/-- The slowly decaying coordinate of a specified point. -/
@[simp] theorem point_one_coord (a b : ℝ) : point a b 1 = b := rfl

/-- Both zero coordinates give the zero vector. -/
@[simp] theorem point_zero : point 0 0 = 0 := by ext i; fin_cases i <;> rfl

/-- Specified coordinates commute with vector addition. -/
@[simp] theorem point_add (a b c d : ℝ) : point a b + point c d = point (a + c) (b + d) := by
  ext i; fin_cases i <;> rfl

/-- Specified coordinates commute with vector subtraction. -/
@[simp] theorem point_sub (a b c d : ℝ) : point a b - point c d = point (a - c) (b - d) := by
  ext i; fin_cases i <;> rfl

/-- Specified coordinates commute with real scalar multiplication. -/
@[simp] theorem point_smul (t a b : ℝ) : t • point a b = point (t * a) (t * b) := by
  ext i; fin_cases i <;> rfl

/-- Every vector is determined by its two coordinates. -/
@[simp] theorem point_coords (x : Plane) : point (x 0) (x 1) = x := by
  ext i; fin_cases i <;> rfl

/-- The squared Euclidean norm is the sum of the squared coordinates. -/
theorem norm_point_sq (a b : ℝ) : ‖point a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- Each coordinate is bounded by the ambient Euclidean norm. -/
theorem abs_coordinate_le_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  exact PiLp.norm_apply_le x i

/-- Each coordinate projection has operator norm at most one. -/
theorem norm_proj_le_one (i : Fin 2) : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using abs_coordinate_le_norm x i

/-- The fixed positive objective on the full Euclidean plane. -/
def objective (x : Plane) : ℝ := CappedQuadratic.value (x 0) + InverseSqrtTail.value (x 1)

/-- Evaluation at specified coordinates is the scalar separable formula. -/
@[simp] theorem objective_point (a b : ℝ) :
    objective (point a b) = CappedQuadratic.value a + InverseSqrtTail.value b := rfl

/-- The actual objective is globally twice continuously differentiable. -/
theorem contDiff_objective : ContDiff ℝ 2 objective := by
  exact (CappedQuadratic.contDiff_value.comp
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).add
    (InverseSqrtTail.contDiff_value.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)

/-- Strict positivity holds everywhere, not only along selected iterates. -/
theorem objective_pos (x : Plane) : 0 < objective x :=
  add_pos_of_nonneg_of_pos (CappedQuadratic.value_nonneg _) (InverseSqrtTail.value_pos _)

/-- Zero is a global lower bound for the actual objective. -/
theorem objective_nonneg (x : Plane) : 0 ≤ objective x := (objective_pos x).le

/-- The fixed initial point has objective value one. -/
@[simp] theorem objective_initial : objective (point 0 1) = 1 := by
  simp [InverseSqrtTail.value_one]

/-- The actual derivative applies the two scalar slopes to the corresponding directions. -/
theorem fderiv_objective (x d : Plane) : fderiv ℝ objective x d =
    CappedQuadratic.first (x 0) * d 0 + InverseSqrtTail.first (x 1) * d 1 := by
  change fderiv ℝ (fun y : Plane =>
    CappedQuadratic.value (y 0) + InverseSqrtTail.value (y 1)) x d = _
  have h₀ := (CappedQuadratic.hasDerivAt_value (x 0)).hasFDerivAt.comp x
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have h₁ := (InverseSqrtTail.hasDerivAt_value (x 1)).hasFDerivAt.comp x
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  simpa only [objective, Function.comp_def, Pi.add_def, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    EuclideanSpace.coe_proj, mul_comm] using
      congrArg (fun A : Plane →L[ℝ] ℝ => A d) (h₀.add h₁).fderiv

/-- The actual Hessian is the diagonal bilinear form given by the scalar curvatures. -/
theorem secondFDeriv_objective (x a b : Plane) :
    fderiv ℝ (fderiv ℝ objective) x a b =
      CappedQuadratic.second (x 0) * a 0 * b 0 +
        InverseSqrtTail.second (x 1) * a 1 * b 1 := by
  have heq : fderiv ℝ objective = fun y : Plane =>
      CappedQuadratic.first (y 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        InverseSqrtTail.first (y 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) := by
    funext y
    ext d
    simp only [fderiv_objective, add_apply, smul_apply,
      EuclideanSpace.coe_proj, smul_eq_mul]
  rw [heq]
  have h₀ := ((CappedQuadratic.hasDerivAt_first (x 0)).hasFDerivAt.comp x
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt).smul_const
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
  have h₁ := ((InverseSqrtTail.hasDerivAt_first (x 1)).hasFDerivAt.comp x
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt).smul_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))
  simpa only [Function.comp_def, Pi.add_def, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_apply_eq_self, smul_apply, smul_eq_mul,
    EuclideanSpace.coe_proj, mul_comm, mul_left_comm, mul_assoc] using
      congrArg (fun A : Plane →L[ℝ] (Plane →L[ℝ] ℝ) => A a b) (h₀.add h₁).fderiv

/-- The gradient has exactly the two actual scalar first derivatives as coordinates. -/
theorem gradient_objective (x : Plane) :
    gradient objective x = point (CappedQuadratic.first (x 0)) (InverseSqrtTail.first (x 1)) := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  ext d
  rw [toDual_gradient]
  change fderiv ℝ objective x d = inner ℝ _ d
  rw [fderiv_objective]
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- In the transverse quadratic region, the objective has its exact quadratic-plus-tail form. -/
theorem objective_local {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) :
    objective (point a b) = a ^ 2 / 2 + InverseSqrtTail.value b := by
  rw [objective_point, CappedQuadratic.value_eq_of_abs_le_one ha]

/-- The local first derivative retains the exact scalar tail slope. -/
theorem fderiv_objective_local {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) (d : Plane) :
    fderiv ℝ objective (point a b) d = a * d 0 + InverseSqrtTail.first b * d 1 := by
  rw [fderiv_objective]
  simp only [point_zero_coord, point_one_coord, CappedQuadratic.first_eq_of_abs_le_one ha]

/-- The local Hessian has transverse curvature one and the actual scalar tail curvature. -/
theorem secondFDeriv_objective_local {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) (u v : Plane) :
    fderiv ℝ (fderiv ℝ objective) (point a b) u v =
      u 0 * v 0 + InverseSqrtTail.second b * u 1 * v 1 := by
  rw [secondFDeriv_objective]
  simp only [point_zero_coord, point_one_coord, CappedQuadratic.second_eq_of_abs_le_one ha,
    one_mul]

/-- All actual derivative tensors through order two are globally Lipschitz in full
operator norm, with one common fixed constant. -/
theorem lipschitz_jets (j : ℕ) (hj : j ≤ 2) :
    LipschitzWith 4 (iteratedFDeriv ℝ j objective) := by
  have hψ : LipschitzWith (3 / 2 : ℝ≥0) (iteratedDeriv j CappedQuadratic.value) := by
    have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases he with rfl | rfl | rfl
    · simpa only [iteratedDeriv_zero] using CappedQuadratic.lipschitz_value
    · simpa only [iteratedDeriv_one, CappedQuadratic.deriv_value] using
        CappedQuadratic.lipschitz_first.weaken
          (by exact_mod_cast (by norm_num : (1 : ℝ) ≤ 3 / 2) : (1 : ℝ≥0) ≤ 3 / 2)
    · rw [iteratedDeriv_two_eq_of_hasDerivAt CappedQuadratic.hasDerivAt_value
        CappedQuadratic.hasDerivAt_first]
      exact CappedQuadratic.lipschitz_second.weaken
        (by exact_mod_cast (by norm_num : (1 : ℝ) ≤ 3 / 2))
  have hh : LipschitzWith (9 / 4 : ℝ≥0) (iteratedDeriv j InverseSqrtTail.value) := by
    have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases he with rfl | rfl | rfl
    · simpa only [iteratedDeriv_zero] using
        InverseSqrtTail.lipschitz_value.weaken
          (by exact_mod_cast (by norm_num : (7 / 8 : ℝ) ≤ 9 / 4) : (7 / 8 : ℝ≥0) ≤ 9 / 4)
    · simpa only [iteratedDeriv_one, InverseSqrtTail.deriv_value] using
        InverseSqrtTail.lipschitz_first.weaken
          (by exact_mod_cast (by norm_num : (3 / 4 : ℝ) ≤ 9 / 4) : (3 / 4 : ℝ≥0) ≤ 9 / 4)
    · rw [iteratedDeriv_two_eq_of_hasDerivAt InverseSqrtTail.hasDerivAt_value
        InverseSqrtTail.hasDerivAt_first]
      exact InverseSqrtTail.lipschitz_second
  have hpull (i : Fin 2) {f : ℝ → ℝ} (hf : ContDiff ℝ j f) {L : ℝ≥0}
      (hL : LipschitzWith L (iteratedDeriv j f)) :
      LipschitzWith L (iteratedFDeriv ℝ j (f ∘ EuclideanSpace.proj (𝕜 := ℝ) i)) := by
    apply ((EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith_iteratedFDeriv_scalar_comp hf hL).weaken
    have hnorm : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖₊ ≤ 1 := by
      exact_mod_cast norm_proj_le_one i
    calc
      L * ‖EuclideanSpace.proj (𝕜 := ℝ) i‖₊ ^ (j + 1) ≤ L * 1 ^ (j + 1) := by gcongr
      _ = L := by simp
  have hfψ := CappedQuadratic.contDiff_value.of_le (show (j : WithTop ℕ∞) ≤ 2 by exact_mod_cast hj)
  have hfh := InverseSqrtTail.contDiff_value.of_le (show (j : WithTop ℕ∞) ≤ 2 by exact_mod_cast hj)
  have hsum := lipschitzWith_iteratedFDeriv_add
    (hfψ.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff)
    (hfh.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)
    (hpull 0 hfψ hψ) (hpull 1 hfh hh)
  change LipschitzWith ((3 / 2 : ℝ≥0) + 9 / 4) (iteratedFDeriv ℝ j objective) at hsum
  exact hsum.weaken (by exact_mod_cast (by norm_num : (3 / 2 : ℝ) + 9 / 4 ≤ 4))

/-- The actual exact oracle is defined at every point and every positive request vector. -/
def exactOracle : ExplicitTrustRegion.Oracle objective 2 :=
  ExplicitTrustRegion.Oracle.exact objective 2

/-- The fixed oracle's requested values are the actual objective values. -/
@[simp] theorem exactOracle_value (x : Plane) (h : ℝ) :
    exactOracle.value x h = objective x := rfl

/-- The fixed oracle's tensors are the actual derivative tensors at every order. -/
@[simp] theorem exactOracle_derivative (x : Plane) (h : ℕ → ℝ) (i : ℕ) :
    exactOracle.derivative x h i = iteratedFDeriv ℝ i objective x := rfl

/-- In the transverse quadratic region the first Taylor decrement is the exact linear
functional in the two coordinates. -/
theorem taylorDecrement_one_local {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) (s : Plane) :
    TaylorCriticality.taylorDecrement objective 1 (point a b) s =
      -a * s 0 - InverseSqrtTail.first b * s 1 := by
  rw [TaylorCriticality.taylorDecrement_one, fderiv_objective_local ha]
  ring

/-- The second Taylor decrement contains the true diagonal curvatures in both coordinates. -/
theorem taylorDecrement_two_local {a : ℝ} (ha : |a| ≤ 1) (b : ℝ) (s : Plane) :
    TaylorCriticality.taylorDecrement objective 2 (point a b) s =
      -a * s 0 - InverseSqrtTail.first b * s 1 -
        ((s 0) ^ 2 + InverseSqrtTail.second b * (s 1) ^ 2) / 2 := by
  rw [TaylorCriticality.taylorDecrement_two, fderiv_objective_local ha,
    secondFDeriv_objective_local ha]
  ring

/-- The actual factorial-normalized cubic Taylor model has its explicit two-coordinate
quadratic formula for every parameter and every ambient displacement. -/
theorem cubic_model_eq {a : ℝ} (ha : |a| ≤ 1) (b σ : ℝ) (s : Plane) :
    HigherOrderRegularization.model objective 2 (point a b) σ s =
      objective (point a b) + a * s 0 + InverseSqrtTail.first b * s 1 +
        ((s 0) ^ 2 + InverseSqrtTail.second b * (s 1) ^ 2) / 2 + σ / 6 * ‖s‖ ^ 3 := by
  have ht := TaylorCriticality.taylorDecrement_eq objective 2 (point a b) s
  rw [taylorDecrement_two_local ha] at ht
  unfold HigherOrderRegularization.model
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one]
  linarith

/-- The fixed initialization has the actual nonzero gradient of length one half. -/
theorem gradient_initial : gradient objective (point 0 1) = point 0 (-(1 / 2)) := by
  rw [gradient_objective]
  simp

/-- The actual first-order unit-ball gap at initialization is one half. -/
theorem first_gap_initial :
    TaylorCriticality.gapOn (TaylorCriticality.taylorDecrement objective 1 (point 0 1))
      (Metric.closedBall 0 1) = 1 / 2 := by
  have hn : ‖point 0 (-(1 / 2))‖ = (1 / 2 : ℝ) := by
    have hs := norm_point_sq 0 (-(1 / 2))
    nlinarith [norm_nonneg (point 0 (-(1 / 2)))]
  have hd : ‖fderiv ℝ objective (point 0 1)‖ = (1 / 2 : ℝ) := by
    rw [← toDual_gradient, LinearIsometryEquiv.norm_map, gradient_initial, hn]
  rw [TaylorCriticality.gapOn_taylorDecrement_one _ _ (by norm_num), hd]
  norm_num

/-- The actual Hessian is positive semidefinite everywhere in the full plane. -/
theorem secondFDeriv_nonneg (x s : Plane) :
    0 ≤ fderiv ℝ (fderiv ℝ objective) x s s := by
  rw [secondFDeriv_objective]
  have h₀ := mul_nonneg (CappedQuadratic.second_nonneg (x 0)) (sq_nonneg (s 0))
  have h₁ := mul_nonneg (InverseSqrtTail.second_nonneg (x 1)) (sq_nonneg (s 1))
  nlinarith

end Optimization.TransverseObjective
