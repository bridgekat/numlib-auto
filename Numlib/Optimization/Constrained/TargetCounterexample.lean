import Numlib.Optimization.Constrained.TargetMerit
import Numlib.Optimization.LeastNorm.Run
import Numlib.Optimization.HighOrder.CriticalityLocalMin
import Numlib.Optimization.HighOrder.CriticalityApproximate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
/-!
# A genuine two-phase obstruction to the printed Lagrangian bounds

The bounded sine objective and linear equality constraint have globally bounded
and Lipschitz first and second derivatives. Phase one is immediately feasible.
One exact inner return triggers the actual target-reset branch and all genuine
least-squares termination tests pass at unit radii. The printed first-order
Lagrangian bound forces the multiplier to be zero, and the second-order bound
then fails on a true tangent displacement. This refutes the existential
multiplier conclusion, not merely the particular multiplier used in its proof.
-/

namespace Constrained.TargetCounterexample
/-- The actual Euclidean plane of the constrained example. -/
abbrev E := EuclideanSpace ℝ (Fin 2)
/-- The continuous linear projection onto one actual Euclidean coordinate. -/
noncomputable def P (i : Fin 2) : E →L[ℝ] ℝ := EuclideanSpace.proj i
/-- The bounded smooth sine objective on the first coordinate. -/
noncomputable def objective (x : E) : ℝ := Real.sin (x 0) / 10
/-- The linear equality constraint on the second coordinate. -/
noncomputable def constraint (x : E) : ℝ := x 1
/-- The genuine target merit after the accepted target reset. -/
noncomputable def resetMerit (x : E) : ℝ := targetMerit objective constraint (-1 / 10) x

/-- The actual first derivative of the sine objective. -/
theorem objective_hasFDerivAt (x : E) :
    HasFDerivAt objective ((Real.cos (x 0) / 10) • P 0) x := by
  have h := ((Real.hasDerivAt_sin (x 0)).div_const 10).hasFDerivAt.comp x (P 0).hasFDerivAt
  convert! h using 1
  ext v
  simp [P, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- The exact derivative of the linear equality constraint. -/
theorem constraint_hasFDerivAt (x : E) : HasFDerivAt constraint (P 1) x :=
  (P 1).hasFDerivAt

/-- The actual objective derivative as a continuous linear functional. -/
theorem objective_fderiv (x : E) :
    fderiv ℝ objective x = (Real.cos (x 0) / 10) • P 0 := (objective_hasFDerivAt x).fderiv

/-- Both actual terms in the reset merit derivative. -/
theorem resetMerit_fderiv (x : E) : fderiv ℝ resetMerit x =
    x 1 • P 1 + ((objective x + 1 / 10) * (Real.cos (x 0) / 10)) • P 0 := by
  have he := (hasFDerivAt_targetMerit (objective_hasFDerivAt x).differentiableAt
    (constraint_hasFDerivAt x).differentiableAt (-1 / 10)).fderiv
  change fderiv ℝ resetMerit x = _ at he
  rw [he, objective_fderiv, (constraint_hasFDerivAt x).fderiv]
  ext v
  simp [P, constraint, innerSL_apply_apply]
  ring

/-- The genuine reset merit Hessian tensor at the terminal point. -/
theorem resetMerit_second (w : Fin 2 → E) :
    iteratedFDeriv ℝ 2 resetMerit 0 w =
      w 0 1 * w 1 1 + (1 / 100 : ℝ) * w 0 0 * w 1 0 := by
  have he : fderiv ℝ resetMerit = fun x => x 1 • P 1 +
      ((objective x + 1 / 10) * (Real.cos (x 0) / 10)) • P 0 := by
    funext x; exact resetMerit_fderiv x
  have hc : HasFDerivAt (fun x : E => Real.cos (x 0) / 10) (0 : E →L[ℝ] ℝ) 0 := by
    convert (((Real.hasDerivAt_cos 0).div_const 10).hasFDerivAt.comp (0 : E)
      (P 0).hasFDerivAt) using 1
    · rfl
    · ext v; norm_num
  have hprod := ((objective_hasFDerivAt (0 : E)).add_const (1 / 10 : ℝ)).mul hc
  have hd := ((constraint_hasFDerivAt (0 : E)).smul_const (P 1)).add
    (hprod.smul_const (P 0))
  change HasFDerivAt (fun x : E => x 1 • P 1 +
    ((objective x + 1 / 10) * (Real.cos (x 0) / 10)) • P 0) _ 0 at hd
  rw [iteratedFDeriv_two_apply, he, hd.fderiv]
  simp [P, objective, ContinuousLinearMap.smulRight_apply]
  ring_nf
  simp


/-- The true first-order reset merit Taylor decrement. -/
theorem reset_decrement_one (d : E) :
    TaylorModel.decrement resetMerit 1 0 d = -(1 / 100 : ℝ) * d 0 := by
  rw [TaylorModel.decrement_one, inner_gradient_left, resetMerit_fderiv]
  simp [P, objective]
  ring_nf
  simp

/-- The true second-order reset merit Taylor decrement. -/
theorem reset_decrement_two (d : E) :
    TaylorModel.decrement resetMerit 2 0 d =
      -(1 / 100 : ℝ) * d 0 - (1 / 200 : ℝ) * (d 0) ^ 2 - (1 / 2 : ℝ) * (d 1) ^ 2 := by
  have he := TaylorModel.decrement_two_smul resetMerit 0 d 1
  simp only [one_smul, one_pow, one_mul, inner_gradient_left, resetMerit_second,
    resetMerit_fderiv] at he
  simp [P, objective] at he
  nlinarith [he]

/-- The actual quadratic reset criticality satisfies the termination tolerance. -/
theorem reset_criticality_two_le :
    TaylorModel.criticality resetMerit 2 0 1 ≤ (1 / 200 : ℝ) := by
  obtain ⟨d, hd, he⟩ := TaylorModel.exists_decrement_eq_criticality resetMerit 2 0
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [← he, reset_decrement_two]
  nlinarith [sq_nonneg (d 0 + 1), sq_nonneg (d 1)]


/-- The Euclidean vector with two prescribed scalar coordinates. -/
noncomputable def vec (a b : ℝ) : E := WithLp.toLp 2 ![a, b]

/-- The exact Euclidean squared norm of the specified vector. -/
theorem vec_norm_sq (a b : ℝ) : ‖vec a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [vec, Fin.sum_univ_two]

/-- The actual Lagrangian gradient for every scalar multiplier. -/
theorem lagrangian_gradient (y : ℝ) :
    gradient (vectorLagrangian objective constraint y) 0 = vec (1 / 10) (-y) := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  have hf := (objective_hasFDerivAt (0 : E)).sub
    (((innerSL ℝ y).hasFDerivAt).comp (0 : E) (constraint_hasFDerivAt (0 : E)))
  change HasFDerivAt (vectorLagrangian objective constraint y) _ 0 at hf
  rw [hf.fderiv]
  ext d
  simp [P, vec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- The printed first-order conclusion forces the multiplier to vanish. -/
theorem first_bound_forces_zero {y : ℝ}
    (hy : TaylorModel.constrainedCriticality (vectorLagrangian objective constraint y)
      1 Set.univ 0 1 ≤ (1 / 10 : ℝ) * multiplierNorm y) : y = 0 := by
  rw [TaylorModel.constrainedCriticality_univ, TaylorModel.criticality_one _ _ zero_lt_one,
    one_mul, lagrangian_gradient] at hy
  have hsq := mul_self_le_mul_self (norm_nonneg _) hy
  have hm : multiplierNorm y ^ 2 = 1 + y ^ 2 := by
    unfold multiplierNorm
    rw [Real.sq_sqrt (by positivity), Real.norm_eq_abs, sq_abs]
  have hv := vec_norm_sq (1 / 10) (-y)
  nlinarith [sq_nonneg y]


/-- The actual Lagrangian derivative at an arbitrary point. -/
theorem lagrangian_fderiv (y : ℝ) (x : E) :
    fderiv ℝ (vectorLagrangian objective constraint y) x =
      (Real.cos (x 0) / 10) • P 0 - y • P 1 := by
  have hf := (objective_hasFDerivAt x).sub
    (((innerSL ℝ y).hasFDerivAt).comp x (constraint_hasFDerivAt x))
  change HasFDerivAt (vectorLagrangian objective constraint y) _ x at hf
  rw [hf.fderiv]
  ext d
  simp [P, innerSL_apply_apply]
  ring

/-- The genuine Lagrangian Hessian is zero at the terminal point. -/
theorem lagrangian_second_zero (y : ℝ) (w : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (vectorLagrangian objective constraint y) 0 w = 0 := by
  have he : fderiv ℝ (vectorLagrangian objective constraint y) =
      fun x => (Real.cos (x 0) / 10) • P 0 - y • P 1 := by
    funext x; exact lagrangian_fderiv y x
  have hc : HasFDerivAt (fun x : E => Real.cos (x 0) / 10) (0 : E →L[ℝ] ℝ) 0 := by
    convert (((Real.hasDerivAt_cos 0).div_const 10).hasFDerivAt.comp (0 : E)
      (P 0).hasFDerivAt) using 1
    · rfl
    · ext v; norm_num
  have hd := (hc.smul_const (P 0)).sub_const (y • P 1)
  change HasFDerivAt (fun x : E => (Real.cos (x 0) / 10) • P 0 - y • P 1) _ 0 at hd
  rw [iteratedFDeriv_two_apply, he, hd.fderiv]
  simp

/-- The actual quadratic Lagrangian decrement at the terminal point. -/
theorem lagrangian_decrement_two (y : ℝ) (d : E) :
    TaylorModel.decrement (vectorLagrangian objective constraint y) 2 0 d =
      -(1 / 10 : ℝ) * d 0 + y * d 1 := by
  have he := TaylorModel.decrement_two_smul (vectorLagrangian objective constraint y) 0 d 1
  simp only [one_smul, one_pow, one_mul, inner_gradient_left, lagrangian_second_zero,
    lagrangian_fderiv] at he
  simp [P] at he
  nlinarith [he]

/-- The actual kernel of the equality constraint derivative. -/
noncomputable def tangent : Set E := {d | fderiv ℝ constraint 0 d = 0}

/-- A genuine feasible tangent displacement gives positive Lagrangian criticality. -/
theorem tangent_criticality_lower (y : ℝ) :
    (1 / 10 : ℝ) ≤ TaylorModel.restrictedCriticality
      (vectorLagrangian objective constraint y) 2 tangent 0 1 := by
  have hd : ‖vec (-1) 0‖ ≤ (1 : ℝ) := by
    rw [EuclideanSpace.norm_eq]
    norm_num [vec, Fin.sum_univ_two]
  have ht : vec (-1) 0 ∈ tangent := by
    change fderiv ℝ constraint 0 (vec (-1) 0) = 0
    rw [(constraint_hasFDerivAt (0 : E)).fderiv]
    rfl
  have hb := TaylorModel.decrement_le_restrictedCriticality
    (vectorLagrangian objective constraint y) 2 tangent 0 ht hd
  simpa [lagrangian_decrement_two, vec] using hb

/-- No multiplier satisfies the first two printed Lagrangian conclusions. -/
theorem no_multiplier_satisfies_printed_bounds : ¬∃ y : ℝ,
    TaylorModel.constrainedCriticality (vectorLagrangian objective constraint y)
      1 Set.univ 0 1 ≤ (1 / 10 : ℝ) * multiplierNorm y ∧
    TaylorModel.restrictedCriticality (vectorLagrangian objective constraint y)
      2 tangent 0 1 ≤ (1 / 2 : ℝ) * ((1 / 10 : ℝ) * multiplierNorm y +
        TaylorModel.constrainedCriticality (vectorLagrangian objective constraint y)
          1 Set.univ 0 1 * ‖gradient objective 0‖) := by
  rintro ⟨y, hy, h2⟩
  have hz := first_bound_forces_zero hy
  subst y
  have hg : gradient objective 0 = vec (1 / 10) 0 := by
    have hh := lagrangian_gradient 0
    have heq : vectorLagrangian objective constraint 0 = objective := by
      funext x
      simp [vectorLagrangian]
    rw [heq] at hh
    simpa using hh
  have hn : ‖vec (1 / 10) 0‖ = (1 / 10 : ℝ) := by
    rw [EuclideanSpace.norm_eq]
    norm_num [vec, Fin.sum_univ_two]
  rw [TaylorModel.constrainedCriticality_univ, TaylorModel.criticality_one _ _ zero_lt_one,
    one_mul, lagrangian_gradient, hg] at h2
  norm_num [multiplierNorm, hn] at h2
  have hb := tangent_criticality_lower 0
  linarith


/-- The actual reset merit gradient at the terminal point. -/
theorem reset_gradient : gradient resetMerit 0 = vec (1 / 100) 0 := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, resetMerit_fderiv]
  ext d
  simp [P, vec, objective, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The exact first-order reset merit criticality at unit radius. -/
theorem reset_criticality_one : TaylorModel.criticality resetMerit 1 0 1 = (1 / 100 : ℝ) := by
  rw [TaylorModel.criticality_one _ _ zero_lt_one, one_mul, reset_gradient,
    EuclideanSpace.norm_eq]
  norm_num [vec, Fin.sum_univ_two]

/-- The genuine augmented constraint and objective-target residual vector. -/
noncomputable def residual (t : ℝ) (x : E) : E := vec (constraint x) (objective x - t)

/-- The actual augmented least-squares merit equals the stated target merit. -/
theorem merit_residual (t : ℝ) :
    LeastNorm.merit (residual t) = targetMerit objective constraint t := by
  funext x
  unfold LeastNorm.merit residual targetMerit
  rw [vec_norm_sq]
  simp [Real.norm_eq_abs, sq_abs]
  ring

/-- The actual sine objective is smooth of every finite order. -/
theorem objective_contDiff (n : ℕ) : ContDiff ℝ n objective := by
  unfold objective
  exact (Real.contDiff_sin.comp (P 0).contDiff).div_const 10

/-- The linear equality map is smooth of every finite order. -/
theorem constraint_contDiff (n : ℕ) : ContDiff ℝ n constraint := (P 1).contDiff

/-- The actual augmented least-squares merit is twice continuously differentiable. -/
theorem merit_contDiff (t : ℝ) : ContDiff ℝ 2 (LeastNorm.merit (residual t)) := by
  rw [merit_residual]
  unfold targetMerit
  exact (((constraint_contDiff 2).norm_sq (𝕜 := ℝ)).div_const 2).add
    ((((objective_contDiff 2).sub contDiff_const).pow 2).div_const 2)

/-- The inner returned point is a true local minimum of the old target merit. -/
theorem old_merit_isMin : IsLocalMin (LeastNorm.merit (residual 0)) (0 : E) := by
  apply Filter.Eventually.of_forall
  intro x
  unfold LeastNorm.merit
  have hz : residual 0 0 = 0 := by
    ext i
    fin_cases i <;> norm_num [residual, vec, objective, constraint]
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
  positivity

/-- Every actual requested old-merit criticality is zero at the inner return. -/
theorem old_criticality_zero (a : Fin 2) :
    TaylorModel.constrainedCriticality (LeastNorm.merit (residual 0))
      (InexactTrustRegion.modelOrder a) Set.univ 0 1 = 0 := by
  rw [TaylorModel.constrainedCriticality_univ]
  fin_cases a
  · exact TaylorModel.criticality_one_eq_zero_of_isLocalMin old_merit_isMin (by norm_num)
  · exact TaylorModel.criticality_two_eq_zero_of_isLocalMin
      (merit_contDiff 0) old_merit_isMin (by norm_num)

/-- The actual inner call returns the exact global least-squares root. -/
def innerCall (_ : E) (ε : Fin 2 → ℝ) (x : E) (δ : Fin 2 → ℝ) (nf nd : ℕ) : Prop :=
  x = 0 ∧ δ = (fun _ => 1) ∧ nf = 1 ∧ nd = 1 ∧ ∀ a, 0 < ε a

/-- The explicit inner solver satisfies every actual requested criticality test. -/
theorem inner_sound : LeastNorm.InnerSound (residual 0) Set.univ innerCall := by
  intro xs ε x δ nf nd hc
  obtain ⟨hx, hδ, _, _, hε⟩ := hc
  subst x δ
  refine ⟨Set.mem_univ _, fun _ => ⟨zero_lt_one, le_rfl⟩, ?_⟩
  intro a
  rw [old_criticality_zero]
  exact div_nonneg (mul_nonneg (hε a).le (by positivity)) (Nat.cast_nonneg _)

/-- The feasible initial point of the actual two-phase execution. -/
noncomputable def initial : E := vec (Real.pi / 2) 0

/-- The actual initial and reset targets and the strict reset-branch residual test. -/
theorem actual_targets :
    objective initial - Real.sqrt ((1 / 10 : ℝ) ^ 2 - ‖constraint initial‖ ^ 2) = 0 ∧
    ‖residual 0 (0 : E)‖ < (1 / 2 : ℝ) * (1 / 10) ∧
    objective 0 - Real.sqrt ((1 / 10 : ℝ) ^ 2 - ‖constraint (0 : E)‖ ^ 2) = -1 / 10 ∧
    ‖residual (-1 / 10) (0 : E)‖ = (1 / 10 : ℝ) := by
  norm_num [initial, objective, constraint, residual, vec, EuclideanSpace.norm_eq,
    Fin.sum_univ_two]



/-- The true inner tolerance request permits the exact returned point and radii. -/
theorem actual_inner_return :
    innerCall initial (fun _ : Fin 2 => (1 / 4 : ℝ) * ‖residual 0 initial‖ * (1 / 10))
      0 (fun _ => 1) 1 1 := by
  refine ⟨rfl, rfl, rfl, rfl, fun _ => ?_⟩
  norm_num [initial, residual, objective, constraint, vec, EuclideanSpace.norm_eq,
    Fin.sum_univ_two]

/-- Every actual reset-merit stopping test passes at the returned unit radii. -/
theorem reset_stopping_checks :
    ∀ a : Fin 2, TaylorModel.constrainedCriticality
      (LeastNorm.merit (residual (-1 / 10))) (InexactTrustRegion.modelOrder a) Set.univ 0 1 ≤
        (1 / 10 : ℝ) * ‖residual (-1 / 10) (0 : E)‖ /
          (InexactTrustRegion.modelOrder a).factorial := by
  intro a
  rw [merit_residual, actual_targets.2.2.2, TaylorModel.constrainedCriticality_univ]
  change TaylorModel.criticality resetMerit _ 0 1 ≤ _
  fin_cases a
  · norm_num [InexactTrustRegion.modelOrder, reset_criticality_one]
  · convert reset_criticality_two_le using 1 <;>
      norm_num [InexactTrustRegion.modelOrder]


/-- The actual derivative of the scalar cosine coefficient in the objective gradient. -/
theorem cosine_hasFDerivAt (x : E) :
    HasFDerivAt (fun z : E => Real.cos (z 0) / 10) ((-Real.sin (x 0) / 10) • P 0) x := by
  have h := ((Real.hasDerivAt_cos (x 0)).div_const 10).hasFDerivAt.comp x (P 0).hasFDerivAt
  convert! h using 1
  ext d
  simp [P, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- The actual sine objective Hessian tensor on arbitrary vectors. -/
theorem objective_second_apply (x : E) (w : Fin 2 → E) :
    iteratedFDeriv ℝ 2 objective x w =
      (-Real.sin (x 0) / 10) * (w 0 0) * (w 1 0) := by
  have he : fderiv ℝ objective = fun x => (Real.cos (x 0) / 10) • P 0 :=
    funext objective_fderiv
  have hd := (cosine_hasFDerivAt x).smul_const (P 0)
  rw [iteratedFDeriv_two_apply, he, hd.fderiv]
  simp [P, ContinuousLinearMap.smulRight_apply]

/-- Each absolute Euclidean coordinate is bounded by the genuine norm. -/
theorem coordinate_bound (x : E) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- A unit scalar Lipschitz bound controls the composed coordinate coefficient. -/
theorem scalar_coefficient_lipschitz {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (u v : E) :
    |φ (u 0) / 10 - φ (v 0) / 10| ≤ ‖u - v‖ := by
  have hh := hφ.dist_le_mul (u 0) (v 0)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hh
  have hc := coordinate_bound (u - v) 0
  have he : (u - v) 0 = u 0 - v 0 := rfl
  rw [he] at hc
  rw [← sub_div, abs_div]
  norm_num
  calc _ ≤ |u 0 - v 0| / 10 := div_le_div_of_nonneg_right hh (by norm_num)
    _ ≤ |u 0 - v 0| := div_le_self (abs_nonneg _) (by norm_num)
    _ ≤ _ := hc

/-- The genuine first derivative tensor is globally Lipschitz with constant one. -/
theorem objective_first_lipschitz (u v : E) :
    ‖iteratedFDeriv ℝ 1 objective u - iteratedFDeriv ℝ 1 objective v‖ ≤ ‖u - v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro w
  simp only [sub_apply, iteratedFDeriv_one_apply, objective_fderiv]
  change ‖Real.cos (u 0) / 10 * w 0 0 - Real.cos (v 0) / 10 * w 0 0‖ ≤ _
  rw [← sub_mul, norm_mul, Real.norm_eq_abs]
  have hm := mul_le_mul (scalar_coefficient_lipschitz Real.lipschitzWith_cos u v)
    (coordinate_bound (w 0) 0) (abs_nonneg _) (norm_nonneg _)
  simpa only [Fin.prod_univ_one, Real.norm_eq_abs] using hm

/-- The genuine second derivative tensor is globally Lipschitz with constant one. -/
theorem objective_second_lipschitz (u v : E) :
    ‖iteratedFDeriv ℝ 2 objective u - iteratedFDeriv ℝ 2 objective v‖ ≤ ‖u - v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro w
  simp only [sub_apply, objective_second_apply]
  have he : -Real.sin (u 0) / 10 * w 0 0 * w 1 0 -
      -Real.sin (v 0) / 10 * w 0 0 * w 1 0 =
      -(Real.sin (u 0) / 10 - Real.sin (v 0) / 10) * w 0 0 * w 1 0 := by ring
  rw [he, norm_mul, norm_mul, norm_neg]
  have hm := mul_le_mul (scalar_coefficient_lipschitz Real.lipschitzWith_sin u v)
    (coordinate_bound (w 0) 0) (abs_nonneg _) (norm_nonneg _)
  have hm' := mul_le_mul hm (coordinate_bound (w 1) 0) (abs_nonneg _) (by positivity)
  simpa only [Real.norm_eq_abs, Fin.prod_univ_two, mul_assoc] using hm'


/-- The actual first derivative tensor is globally bounded by one. -/
theorem objective_first_bound (x : E) : ‖iteratedFDeriv ℝ 1 objective x‖ ≤ (1 : ℝ) := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro w
  simp only [iteratedFDeriv_one_apply, objective_fderiv]
  change ‖Real.cos (x 0) / 10 * w 0 0‖ ≤ _
  rw [norm_mul]
  have hcoef : ‖Real.cos (x 0) / 10‖ ≤ (1 : ℝ) := by
    rw [norm_div, Real.norm_eq_abs]
    norm_num
    have hh := Real.abs_cos_le_one (x 0)
    linarith
  have hm := mul_le_mul hcoef (coordinate_bound (w 0) 0) (abs_nonneg _) zero_le_one
  simpa only [Fin.prod_univ_one, one_mul, Real.norm_eq_abs] using hm

/-- The actual second derivative tensor is globally bounded by one. -/
theorem objective_second_bound (x : E) : ‖iteratedFDeriv ℝ 2 objective x‖ ≤ (1 : ℝ) := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro w
  rw [objective_second_apply, norm_mul, norm_mul]
  have hcoef : ‖-Real.sin (x 0) / 10‖ ≤ (1 : ℝ) := by
    rw [norm_div, norm_neg, Real.norm_eq_abs]
    norm_num
    have hh := Real.abs_sin_le_one (x 0)
    linarith
  have hm := mul_le_mul hcoef (coordinate_bound (w 0) 0) (abs_nonneg _) zero_le_one
  have hm' := mul_le_mul hm (coordinate_bound (w 1) 0) (abs_nonneg _) (by positivity)
  simpa only [Fin.prod_univ_two, mul_assoc, one_mul, Real.norm_eq_abs] using hm'

/-- The actual linear constraint Hessian tensor vanishes everywhere. -/
theorem constraint_second_zero (x : E) : iteratedFDeriv ℝ 2 constraint x = 0 := by
  have he : fderiv ℝ constraint = fun _ => P 1 :=
    funext (fun x => (constraint_hasFDerivAt x).fderiv)
  apply ContinuousMultilinearMap.ext
  intro w
  have hc : fderiv ℝ (fun _ : E => P 1) x = 0 := (hasFDerivAt_const (P 1) x).fderiv
  rw [iteratedFDeriv_two_apply, he, hc]
  simp

/-- The genuine linear constraint derivative tensor is constant. -/
theorem constraint_first_constant (x y : E) :
    iteratedFDeriv ℝ 1 constraint x = iteratedFDeriv ℝ 1 constraint y := by
  apply ContinuousMultilinearMap.ext
  intro w
  simp only [iteratedFDeriv_one_apply, (constraint_hasFDerivAt x).fderiv,
    (constraint_hasFDerivAt y).fderiv]

/-- The actual constraint derivative tensor has norm at most one. -/
theorem constraint_first_bound (x : E) : ‖iteratedFDeriv ℝ 1 constraint x‖ ≤ (1 : ℝ) := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro w
  simp only [iteratedFDeriv_one_apply, (constraint_hasFDerivAt x).fderiv]
  change ‖(w 0) 1‖ ≤ _
  simpa only [Fin.prod_univ_one, one_mul, Real.norm_eq_abs] using
    coordinate_bound (w 0) 1

/-- All source smoothness, boundedness and global derivative Lipschitz assumptions hold. -/
theorem source_regularity :
    ContDiff ℝ 2 objective ∧ ContDiff ℝ 2 constraint ∧
    (∀ x : E, -(1 / 10 : ℝ) ≤ objective x) ∧
    (∀ x : E, objective x ≤ (1 / 10 : ℝ)) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x y : E,
      ‖iteratedFDeriv ℝ j objective x - iteratedFDeriv ℝ j objective y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x y : E,
      ‖iteratedFDeriv ℝ j constraint x - iteratedFDeriv ℝ j constraint y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x : E, ‖iteratedFDeriv ℝ j objective x‖ ≤ 1) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x : E, ‖iteratedFDeriv ℝ j constraint x‖ ≤ 1) := by
  refine ⟨objective_contDiff 2, constraint_contDiff 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold objective
    nlinarith [Real.neg_one_le_sin (x 0)]
  · intro x
    unfold objective
    nlinarith [Real.sin_le_one (x 0)]
  · intro j hj hj2 x y
    interval_cases j
    · simpa only [one_mul] using objective_first_lipschitz x y
    · simpa only [one_mul] using objective_second_lipschitz x y
  · intro j hj hj2 x y
    interval_cases j
    · rw [constraint_first_constant x y, sub_self, norm_zero]
      positivity
    · rw [constraint_second_zero, constraint_second_zero, sub_self, norm_zero]
      positivity
  · intro j hj hj2 x
    interval_cases j
    · exact objective_first_bound x
    · exact objective_second_bound x
  · intro j hj hj2 x
    interval_cases j
    · exact constraint_first_bound x
    · rw [constraint_second_zero, norm_zero]
      norm_num


/-- Phase one immediately attains primal feasibility with no inner calls. -/
theorem phase_one_run : LeastNorm.Run (q := 2) constraint Set.univ
    (fun _ _ _ _ _ _ => False) (1 / 2 * (1 / 10)) (1 / 4) (fun _ => 1 / 10)
    (fun _ => initial) (fun _ _ => 1) (fun _ => 0) (fun _ => 0) 0 := by
  constructor
  · norm_num
  · norm_num
  · intro a; norm_num
  · norm_num
  · norm_num
  · norm_num [initial, constraint, vec]
  · trivial
  · intro k hk; omega
  · intro k hk; omega

/-- The actual phase-one return satisfies the strict primal tolerance. -/
theorem phase_one_primal : ‖constraint initial‖ < (1 / 2 : ℝ) * (1 / 10) := by
  norm_num [initial, constraint, vec]

/-- The tangent displacement set is exactly the feasible constraint derivative kernel. -/
theorem tangent_eq_feasible_kernel : tangent =
    TaylorModel.feasibleDisplacements Set.univ (0 : E) ∩
      {d : E | fderiv ℝ constraint 0 d = 0} := by
  ext d
  simp [tangent, TaylorModel.feasibleDisplacements]

/-- A genuine one-call two-phase execution satisfies every actual outer check,
source regularity assumption and target update, but no multiplier satisfies the
first two printed Lagrangian conclusions simultaneously. -/
theorem verified_counterexample :
    ContDiff ℝ 2 objective ∧ ContDiff ℝ 2 constraint ∧
    (∀ x : E, -(1 / 10 : ℝ) ≤ objective x) ∧
    (∀ x : E, objective x ≤ (1 / 10 : ℝ)) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x y : E,
      ‖iteratedFDeriv ℝ j objective x - iteratedFDeriv ℝ j objective y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x y : E,
      ‖iteratedFDeriv ℝ j constraint x - iteratedFDeriv ℝ j constraint y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x : E, ‖iteratedFDeriv ℝ j objective x‖ ≤ 1) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x : E, ‖iteratedFDeriv ℝ j constraint x‖ ≤ 1) ∧
    LeastNorm.Run (q := 2) constraint Set.univ (fun _ _ _ _ _ _ => False)
      (1 / 2 * (1 / 10)) (1 / 4) (fun _ => 1 / 10) (fun _ => initial)
        (fun _ _ => 1) (fun _ => 0) (fun _ => 0) 0 ∧
    ‖constraint initial‖ < (1 / 2 : ℝ) * (1 / 10) ∧
    LeastNorm.InnerSound (residual 0) Set.univ innerCall ∧
    innerCall initial (fun _ : Fin 2 => (1 / 4 : ℝ) * ‖residual 0 initial‖ * (1 / 10))
      0 (fun _ => 1) 1 1 ∧
    objective initial - Real.sqrt ((1 / 10 : ℝ) ^ 2 - ‖constraint initial‖ ^ 2) = 0 ∧
    ‖residual 0 (0 : E)‖ < (1 / 2 : ℝ) * (1 / 10) ∧
    objective 0 - Real.sqrt ((1 / 10 : ℝ) ^ 2 - ‖constraint (0 : E)‖ ^ 2) = -1 / 10 ∧
    ‖residual (-1 / 10) (0 : E)‖ = (1 / 10 : ℝ) ∧
    (∀ a : Fin 2, TaylorModel.constrainedCriticality (LeastNorm.merit (residual (-1 / 10)))
      (InexactTrustRegion.modelOrder a) Set.univ 0 1 ≤
        (1 / 10 : ℝ) * ‖residual (-1 / 10) (0 : E)‖ /
          (InexactTrustRegion.modelOrder a).factorial) ∧
    ¬(∃ y : ℝ, TaylorModel.constrainedCriticality (vectorLagrangian objective constraint y)
      1 Set.univ 0 1 ≤ (1 / 10 : ℝ) * multiplierNorm y ∧
      TaylorModel.restrictedCriticality (vectorLagrangian objective constraint y)
        2 tangent 0 1 ≤ (1 / 2 : ℝ) * ((1 / 10 : ℝ) * multiplierNorm y +
          TaylorModel.constrainedCriticality (vectorLagrangian objective constraint y)
            1 Set.univ 0 1 * ‖gradient objective 0‖)) := by
  obtain ⟨hf, hc, hlo, hup, hfl, hcl, hfb, hcb⟩ := source_regularity
  exact ⟨hf, hc, hlo, hup, hfl, hcl, hfb, hcb, phase_one_run, phase_one_primal,
    inner_sound, actual_inner_return, actual_targets.1, actual_targets.2.1,
    actual_targets.2.2.1, actual_targets.2.2.2, reset_stopping_checks,
    no_multiplier_satisfies_printed_bounds⟩
end Constrained.TargetCounterexample
