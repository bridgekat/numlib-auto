import Numlib.Optimization.Composite.Origin

/-!
# A noncritical zero-improvement model return

For the bounded-below quadratic `(x-2)^2/2`, its first-order regularized model
at zero with parameter one has equal values at displacements zero and four.
The latter displacement passes the outer large-step bypass. Nevertheless zero
fails the requested first-order criticality at every positive radius.
-/

noncomputable section

namespace RegularizationZeroReturn
/-- The smooth bounded-below objective in the immediate-exit example. -/
def objective (x : ℝ) : ℝ := (x - 2) ^ 2 / 2

/-- The quadratic objective is smooth to every finite order. -/
theorem smooth (n : ℕ) : ContDiff ℝ n objective := by
  unfold objective
  fun_prop

/-- The objective is globally bounded below by zero. -/
theorem nonneg (x : ℝ) : 0 ≤ objective x := by
  unfold objective
  positivity

/-- The actual first derivative of the quadratic objective. -/
theorem fderiv_objective (x d : ℝ) :
    fderiv ℝ objective x d = (x - 2) * d := by
  have hx : HasDerivAt objective (x - 2) x := by
    convert (((hasDerivAt_id x).sub_const 2).pow 2).div_const 2 using 1
    · rfl
    · simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
      ring
  rw [hx.hasFDerivAt.fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- Its genuine first derivative is globally Lipschitz with constant one. -/
theorem derivative_lipschitz (x y : ℝ) :
    ‖iteratedFDeriv ℝ 1 objective x - iteratedFDeriv ℝ 1 objective y‖ ≤ ‖x - y‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro d
  simp only [sub_apply, iteratedFDeriv_one_apply, fderiv_objective]
  rw [show (x - 2) * d 0 - (y - 2) * d 0 = (x - y) * d 0 by ring, norm_mul]
  simp

/-- The actual first-order Taylor polynomial at zero. -/
theorem taylor_formula (s : ℝ) : TaylorModel.eval objective 1 0 s = 2 - 2 * s := by
  have hd : deriv objective 0 = -2 := by
    simpa using fderiv_objective 0 1
  simp [TaylorModel.eval_eq_sum, Finset.sum_range_succ, iteratedFDeriv_one_apply,
    hd, objective]
  ring

/-- The actual first-order Taylor decrement at zero. -/
theorem decrement_formula (s : ℝ) : TaylorModel.decrement objective 1 0 s = 2 * s := by
  rw [TaylorModel.decrement_eq, taylor_formula]
  norm_num [objective]

/-- Actual first-order criticality is twice the radius, including radius zero. -/
theorem criticality_formula {δ : ℝ} (hδ : 0 ≤ δ) :
    TaylorModel.criticality objective 1 0 δ = 2 * δ := by
  obtain ⟨d, hd, he⟩ := TaylorModel.exists_decrement_eq_criticality objective 1 0 hδ
  have hlo := TaylorModel.decrement_le_criticality objective 1 0
    (δ := δ) (s := δ) (by simp [Real.norm_eq_abs, abs_of_nonneg hδ])
  have hdu : d ≤ δ := (le_abs_self d).trans (by simpa [Real.norm_eq_abs] using hd)
  rw [decrement_formula] at he hlo
  linarith

/-- The genuine first-order regularization model. -/
theorem model_formula (s : ℝ) : HighOrderRegularization.model objective 1 0 1 s =
    2 - 2 * s + s ^ 2 / 2 := by
  unfold HighOrderRegularization.model ModelDecrease.penalized
  rw [taylor_formula]
  norm_num [Real.norm_eq_abs, sq_abs]
  ring

/-- The permitted large return has exactly zero model improvement. -/
theorem zero_improvement :
    HighOrderRegularization.model objective 1 0 1 4 =
      HighOrderRegularization.model objective 1 0 1 0 := by
  rw [model_formula, model_formula]
  norm_num

/-- A different displacement strictly improves the same genuine model. -/
theorem improving_displacement :
    HighOrderRegularization.model objective 1 0 1 2 <
      HighOrderRegularization.model objective 1 0 1 0 := by
  rw [model_formula, model_formula]
  norm_num

/-- No positive global-gap fraction allows the zero-improvement large return. -/
theorem not_positive_fraction : ¬∃ μ : ℝ, 0 < μ ∧
    ModelDecrease.ApproximateGlobalStep (HighOrderRegularization.model objective 1 0 1) μ 4 := by
  rintro ⟨μ, hμ, hm⟩
  have hh := hm 2
  rw [model_formula, model_formula, model_formula] at hh
  norm_num at hh
  linarith

/-- The returned point fails the requested accuracy at every positive radius. -/
theorem not_critical {δ : ℝ} (hδ : 0 < δ) :
    ¬TaylorModel.criticality objective 1 0 δ ≤ (1 / 2 : ℝ) * δ := by
  rw [criticality_formula hδ.le]
  linarith

end RegularizationZeroReturn
