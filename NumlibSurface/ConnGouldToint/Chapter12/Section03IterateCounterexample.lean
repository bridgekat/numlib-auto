import NumlibSurface.ConnGouldToint.Chapter12.Section03ConstraintExample

/-! # Failure of iterate active-set identification -/

open Filter Optimization
open scoped Topology RealInnerProductSpace

namespace ConnGouldToint.Chapter12

open Chapter06

private abbrev ExampleSpace := EuclideanSpace ℝ (Fin 3)

private noncomputable def orthant : Set ExampleSpace :=
  {v | 0 ≤ v 0 ∧ 0 ≤ v 1}

private def coord (i : Fin 3) : ExampleSpace →L[ℝ] ℝ := PiLp.proj 2 _ i

@[simp] private theorem coord_apply (i : Fin 3) (v : ExampleSpace) : coord i v = v i := rfl

private theorem orthant_closed : IsClosed orthant :=
  (isClosed_le continuous_const (coord 0).continuous).inter
    (isClosed_le continuous_const (coord 1).continuous)

private theorem orthant_convex : Convex ℝ orthant := by
  intro x hx y hy a b ha hb _
  change 0 ≤ x 0 ∧ 0 ≤ x 1 at hx
  change 0 ≤ y 0 ∧ 0 ≤ y 1 at hy
  change 0 ≤ a * x 0 + b * y 0 ∧ 0 ≤ a * x 1 + b * y 1
  exact ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)⟩

private noncomputable def point (x y t : ℝ) : ExampleSpace := WithLp.toLp 2 ![x, y, t]

@[simp] private theorem point_zero (x y t : ℝ) : point x y t 0 = x := rfl
@[simp] private theorem point_one (x y t : ℝ) : point x y t 1 = y := rfl
@[simp] private theorem point_two (x y t : ℝ) : point x y t 2 = t := rfl

private theorem example_inner (u v : ExampleSpace) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private theorem example_norm_sq (v : ExampleSpace) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

private noncomputable def objective (v : ExampleSpace) : ℝ :=
  coord 0 v + (coord 0 v)^2 + coord 1 v + (coord 1 v)^2 + (1 / 2) * (coord 2 v)^2

private noncomputable def objectiveGradient (v : ExampleSpace) : ExampleSpace :=
  point (1 + 2 * v 0) (1 + 2 * v 1) (v 2)

private theorem objective_hasGradientAt (v : ExampleSpace) :
    HasGradientAt objective (objectiveGradient v) v := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold objective
  convert ((((coord 0).hasFDerivAt.add ((coord 0).hasFDerivAt.pow 2)).add
    (coord 1).hasFDerivAt).add ((coord 1).hasFDerivAt.pow 2)).add
      (((coord 2).hasFDerivAt.pow 2).const_mul (1 / 2 : ℝ)) using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [InnerProductSpace.toDual_apply_apply, example_inner, objectiveGradient]
  ring

private theorem objective_gradient (v : ExampleSpace) :
    gradient objective v = objectiveGradient v := (objective_hasGradientAt v).gradient

private noncomputable def amplitude (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k / 8

private theorem amplitude_bounds (k : ℕ) : 0 < amplitude k ∧ amplitude k ≤ 1 / 8 := by
  have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact ⟨by unfold amplitude; positivity, by unfold amplitude; linarith⟩

private theorem amplitude_succ (k : ℕ) : amplitude (k + 1) = amplitude k / 2 := by
  unfold amplitude
  rw [pow_succ]
  ring

private noncomputable def center (k : ℕ) : ExampleSpace :=
  point 0 (amplitude k) ((amplitude k)^2)

private noncomputable def remote : ExampleSpace := point 0 0 (-1)

private theorem center_mem (k : ℕ) : center k ∈ orthant :=
  ⟨by simp [center], by simpa [center] using (amplitude_bounds k).1.le⟩

private theorem remote_mem : remote ∈ orthant := by
  change 0 ≤ remote 0 ∧ 0 ≤ remote 1
  simp [remote]

private noncomputable def linearDrop (a : ℝ) : ℝ := (1 + 2 * a) * a + a^2 * (1 + a^2)

private noncomputable def coefficient (a : ℝ) : ℝ := (linearDrop a - a / 4) / (1 + a^2)^2

private theorem linearDrop_bounds {a : ℝ} (ha : 0 < a) (hb : a ≤ 1 / 8) :
    a ≤ linearDrop a ∧ linearDrop a ≤ 2 * a := by
  have h₂ : a^2 ≤ a / 8 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hb)]
  have h₄ : a^4 ≤ a^2 := by
    nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ 1 - a^2 by linarith)]
  unfold linearDrop
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg (a^2)]

private theorem coefficient_bounds {a : ℝ} (ha : 0 < a) (hb : a ≤ 1 / 8) :
    0 ≤ coefficient a ∧ coefficient a ≤ 1 := by
  have h := linearDrop_bounds ha hb
  have hd : 0 < (1 + a^2)^2 := by positivity
  unfold coefficient
  exact ⟨div_nonneg (by linarith [h.1]) hd.le,
    (div_le_iff₀ hd).2 (by nlinarith [h.2, sq_nonneg a, sq_nonneg (a^2)])⟩

private noncomputable def model (k : ℕ) (v : ExampleSpace) : ℝ :=
  objective (center k) + ⟪objectiveGradient (center k), v - center k⟫ +
    coefficient (amplitude k) * (v 2 - center k 2)^2

private theorem model_center (k : ℕ) : model k (center k) = objective (center k) := by
  simp [model]

private theorem remote_inner (k : ℕ) :
    ⟪objectiveGradient (center k), remote - center k⟫ = -linearDrop (amplitude k) := by
  simp [example_inner, objectiveGradient, center, remote, linearDrop]
  ring

private theorem remote_drop (k : ℕ) : model k (center k) - model k remote = amplitude k / 4 := by
  rw [model_center]
  unfold model
  rw [remote_inner]
  simp only [remote, center, point_two, coefficient]
  have h : (1 + amplitude k ^ 2)^2 ≠ 0 := by positivity
  field_simp
  ring


private theorem remote_projection (k : ℕ) :
    projectedGradientPath orthant objective (center k)
      ((1 + amplitude k ^ 2) / amplitude k ^ 2) = remote := by
  let a := amplitude k
  let τ := (1 + a^2) / a^2
  have ha := (amplitude_bounds k).1
  have hb := (amplitude_bounds k).2
  have hτ : 1 ≤ τ := (le_div_iff₀ (by dsimp [a]; positivity)).2 (by linarith)
  have hτeq : τ * a^2 = 1 + a^2 := div_mul_cancel₀ _ (by dsimp [a]; positivity)
  unfold projectedGradientPath projectedRay
  rw [objective_gradient]
  apply (bestApprox_eq_iff ⟨remote, remote_mem⟩ orthant_closed orthant_convex).2
  refine ⟨remote_mem, fun v hv ↦ ?_⟩
  change 0 ≤ v 0 ∧ 0 ≤ v 1 at hv
  change ⟪center k + τ • (-objectiveGradient (center k)) - remote, v - remote⟫ ≤ 0
  simp [example_inner, center, objectiveGradient, remote, ← show a = amplitude k from rfl]
  have h₀ : -τ ≤ 0 := by linarith
  have h₁ : a + τ * -(1 + 2 * a) ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ) (show 0 ≤ 1 + 2 * a by dsimp [a]; positivity)]
  have h₂ : a^2 + τ * -(a^2) - (-1) = 0 := by linarith [hτeq]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h₀ hv.1,
    mul_nonpos_of_nonpos_of_nonneg h₁ hv.2, congrArg (· * (v 2 + 1)) h₂]

private theorem remote_distance (k : ℕ) :
    1 ≤ ‖remote - center k‖ ∧ ‖remote - center k‖ ≤ 2 := by
  let a := amplitude k
  have ha : 0 < a := (amplitude_bounds k).1
  have hb : a ≤ 1 / 8 := (amplitude_bounds k).2
  have h₂ : a^2 ≤ 1 / 64 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 8 - a by linarith)
      (show 0 ≤ 1 / 8 + a by positivity)]
  have hs : ‖remote - center k‖ ^ 2 = a^2 + (1 + a^2)^2 := by
    rw [example_norm_sq]
    simp [center, remote, a]
    ring
  constructor
  · apply (sq_le_sq₀ zero_le_one (norm_nonneg _)).mp
    nlinarith [sq_nonneg a, sq_nonneg (a^2)]
  · apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
    nlinarith [mul_nonneg (show 0 ≤ 1 / 64 - a^2 by linarith)
      (show 0 ≤ 2 + a^2 by positivity)]

private noncomputable def exampleCauchyParams : GeneralizedCauchyParams where
  upperSlope := 1 / 8
  lowerSlope := 7 / 8
  radiusFraction := 1 / 4
  endpointFactor := 1 / 4
  upper_pos := by norm_num
  slope_order := by norm_num
  lower_lt_one := by norm_num
  fraction_pos := by norm_num
  fraction_lt_one := by norm_num
  endpoint_pos := by norm_num
  endpoint_lt_half := by norm_num

private theorem remote_cauchy (k : ℕ) :
    IsApproxGeneralizedCauchyPoint exampleCauchyParams orthant objective
      (model k) (center k) 2 remote := by
  refine ⟨(1 + amplitude k ^ 2) / amplitude k ^ 2,
    by have := (amplitude_bounds k).1; positivity, (remote_projection k).symm,
    (remote_distance k).2, ?_, Or.inl ?_⟩
  · rw [objective_gradient, remote_inner]
    have h := remote_drop k
    have hl := (linearDrop_bounds (amplitude_bounds k).1 (amplitude_bounds k).2).2
    change model k remote ≤ model k (center k) + 1 / 8 * -linearDrop (amplitude k)
    linarith
  · change (1 / 4 : ℝ) * 2 ≤ ‖remote - center k‖
    linarith [(remote_distance k).1]

private theorem center_distance (k : ℕ) : ‖center (k + 1) - center k‖ ≤ 2 := by
  let a := amplitude k
  have ha : 0 < a := (amplitude_bounds k).1
  have hb : a ≤ 1 / 8 := (amplitude_bounds k).2
  have h₂ : a^2 ≤ 1 := by nlinarith [mul_nonneg ha.le (show 0 ≤ 1 - a by linarith)]
  have h₄ : a^4 ≤ a^2 := by
    nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ 1 - a^2 by linarith)]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [example_norm_sq]
  simp [center, amplitude_succ, ← show a = amplitude k from rfl]
  nlinarith

private theorem center_prediction (k : ℕ) :
    let a := amplitude k
    model k (center k) - model k (center (k + 1)) =
      (1 + 2 * a) * (a / 2) + 3 / 4 * a^4 - coefficient a * (3 / 4 * a^2)^2 := by
  rw [model_center]
  simp [model, example_inner, objectiveGradient, center, amplitude_succ]
  ring

private theorem center_prediction_bounds (k : ℕ) :
    let a := amplitude k
    a / 2 ≤ model k (center k) - model k (center (k + 1)) ∧
    model k (center k) - model k (center (k + 1)) ≤ a / 2 + a^2 + 3 / 4 * a^4 := by
  let a := amplitude k
  have h := coefficient_bounds (amplitude_bounds k).1 (amplitude_bounds k).2
  change 0 ≤ coefficient a ∧ coefficient a ≤ 1 at h
  have hh := center_prediction k
  dsimp only at hh
  rw [hh]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (sq_nonneg (3 / 4 * a^2)),
      sq_nonneg a, sq_nonneg (a^2)]
  · nlinarith [mul_nonneg h.1 (sq_nonneg (3 / 4 * a^2))]

private theorem center_actual (k : ℕ) :
    let a := amplitude k
    objective (center k) - objective (center (k + 1)) =
      a / 2 + 3 / 4 * a^2 + 15 / 32 * a^4 := by
  simp [objective, center, amplitude_succ]
  ring

private theorem center_step_eq (k : ℕ) :
    center k + (center (k + 1) - center k) = center (k + 1) := by abel

private theorem center_ratio (k : ℕ) : defaultBTRParams.η₂ ≤
    btrRatio objective (model k) (center k) (center (k + 1) - center k) := by
  let a := amplitude k
  have ha : 0 < a := (amplitude_bounds k).1
  have hb : a ≤ 1 / 8 := (amplitude_bounds k).2
  have h₂ : a^2 ≤ a / 8 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hb)]
  have h₄ : a^4 ≤ a^2 / 64 := by
    nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ 1 / 64 - a^2 by linarith)]
  have hp := center_prediction_bounds k
  have hpos : 0 < model k (center k) - model k (center (k + 1)) :=
    (half_pos ha).trans_le hp.1
  unfold btrRatio reductionRatio
  rw [center_step_eq, le_div_iff₀ hpos, center_actual]
  rw [show defaultBTRParams.η₂ = 9 / 10 by norm_num [defaultBTRParams]]
  nlinarith [hp.2]

private noncomputable def exampleRun :
    BTRRun objective defaultBTRParams (fun _ _ _ _ ↦ True) where
  x := center
  s k := center (k + 1) - center k
  Δ _ := 2
  p _ := normSeminorm ℝ ExampleSpace
  norm_separates _ v h := norm_eq_zero.mp (show ‖v‖ = 0 from h)
  delta_initial_pos := by norm_num
  feasible k := by simpa [trustRegion, add_sub_add_left_eq_sub] using center_distance k
  model := model
  sufficient_decrease _ := trivial
  predicted_pos k := by
    rw [center_step_eq]
    exact (half_pos (amplitude_bounds k).1).trans_le (center_prediction_bounds k).1
  iterate_update k := by
    rw [acceptStep_of_le (defaultBTRParams.eta₁_le_eta₂.trans (center_ratio k)), center_step_eq]
  radius_update k := by
    have h := center_ratio k
    refine ⟨fun _ ↦ le_rfl, ?_, ?_⟩
    · intro _ hh
      exact (not_lt_of_ge h hh).elim
    · intro hh
      exact (not_lt_of_ge (defaultBTRParams.eta₁_le_eta₂.trans h) hh).elim


private theorem center_tendsto : Tendsto center atTop (𝓝 (0 : ExampleSpace)) := by
  have ha : Tendsto amplitude atTop (𝓝 0) := by
    change Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k / 8) atTop (𝓝 0)
    simpa only [zero_div] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (by norm_num)).div_const (8 : ℝ)
  have ha₂ : Tendsto (fun k ↦ amplitude k ^ 2) atTop (𝓝 0) := by
    simpa using ha.pow 2
  have hh : Tendsto (fun k ↦ (![0, amplitude k, amplitude k ^ 2] : Fin 3 → ℝ))
      atTop (𝓝 (0 : Fin 3 → ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact ha
    · exact ha₂
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).tendsto (0 : Fin 3 → ℝ)).comp hh

private theorem model_Taylor (k : ℕ) :
    model k remote - (model k (center k) +
      ⟪gradient objective (center k), remote - center k⟫) ≤
        2 * ‖remote - center k‖ ^ 2 / 2 := by
  rw [model_center, objective_gradient, example_norm_sq]
  simp only [model, add_sub_cancel_left]
  have h := (coefficient_bounds (amplitude_bounds k).1 (amplitude_bounds k).2).2
  have ht : (remote - center k) 2 = remote 2 - center k 2 := rfl
  rw [ht]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg (remote 2 - center k 2)),
    sq_nonneg ((remote - center k) 0), sq_nonneg ((remote - center k) 1)]

private theorem model_dominates_cauchy (k : ℕ) : model k (center (k + 1)) ≤ model k remote := by
  have h := (center_prediction_bounds k).1
  have ha := (amplitude_bounds k).1
  linarith [remote_drop k]

private theorem objective_contDiff : ContDiff ℝ 2 objective := by
  unfold objective
  fun_prop

private theorem model_contDiff (k : ℕ) : ContDiff ℝ 2 (model k) := by
  have he : model k = fun v ↦ objective (center k) +
      ⟪objectiveGradient (center k), v - center k⟫ +
      coefficient (amplitude k) * (coord 2 v - coord 2 (center k))^2 := rfl
  rw [he]
  simp only [← InnerProductSpace.toDual_apply_apply]
  fun_prop

private theorem model_hasFDerivAt (k : ℕ) (v : ExampleSpace) :
    HasFDerivAt (model k)
      (InnerProductSpace.toDual ℝ ExampleSpace (objectiveGradient (center k)) +
        (2 * coefficient (amplitude k) * (v 2 - center k 2)) • coord 2) v := by
  let L := InnerProductSpace.toDual ℝ ExampleSpace (objectiveGradient (center k))
  have h₁ := ((L.hasFDerivAt (x := v)).sub_const (L (center k))).const_add (objective (center k))
  have h₂ := (((coord 2).hasFDerivAt (x := v) |>.sub_const (center k 2)).pow 2).const_mul
    (coefficient (amplitude k))
  convert h₁.add h₂ using 1
  · ext u
    simp [model, L, InnerProductSpace.toDual_apply_apply, inner_sub_right]
  · apply ContinuousLinearMap.ext
    intro u
    simp [L]
    ring

private theorem model_fderiv_center (k : ℕ) :
    fderiv ℝ (model k) (center k) = fderiv ℝ objective (center k) := by
  rw [(model_hasFDerivAt k (center k)).fderiv,
    (objective_hasGradientAt (center k)).hasFDerivAt.fderiv]
  simp

private theorem model_hessian (k : ℕ) (v : ExampleSpace) :
    fderiv ℝ (fderiv ℝ (model k)) v =
      (2 * coefficient (amplitude k)) • (coord 2).smulRight (coord 2) := by
  have he : fderiv ℝ (model k) = fun u ↦
      InnerProductSpace.toDual ℝ ExampleSpace (objectiveGradient (center k)) +
        (2 * coefficient (amplitude k) * (u 2 - center k 2)) • coord 2 :=
    funext fun u ↦ (model_hasFDerivAt k u).fderiv
  rw [he]
  have h := ((((coord 2).hasFDerivAt (x := v) |>.sub_const (center k 2)).const_mul
    (2 * coefficient (amplitude k))).smul_const (coord 2)).const_add
      (InnerProductSpace.toDual ℝ ExampleSpace (objectiveGradient (center k)))
  refine h.fderiv.trans ?_
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro w
  simp [mul_assoc]

private theorem objective_hessian_constant (v : ExampleSpace) :
    fderiv ℝ (fderiv ℝ objective) v =
      (2 : ℝ) • (coord 0).smulRight (coord 0) +
      (2 : ℝ) • (coord 1).smulRight (coord 1) +
      (coord 2).smulRight (coord 2) := by
  have he : fderiv ℝ objective = fun u ↦
      ((1 + 2 * u 0) : ℝ) • coord 0 + ((1 + 2 * u 1) : ℝ) • coord 1 +
        (u 2 : ℝ) • coord 2 := by
    funext u
    rw [(objective_hasGradientAt u).hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro w
    simp [InnerProductSpace.toDual_apply_apply, example_inner, objectiveGradient]
  rw [he]
  have h (i : Fin 3) :=
    (((coord i).hasFDerivAt (x := v) |>.const_mul (2 : ℝ)).const_add (1 : ℝ)).smul_const
      (coord i)
  refine (((h 0).add (h 1)).add ((coord 2).hasFDerivAt.smul_const (coord 2))).fderiv.trans ?_
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro w
  simp [mul_assoc]


private theorem objective_bddBelow : BddBelow (Set.range objective) := by
  refine ⟨-1 / 2, ?_⟩
  rintro _ ⟨v, rfl⟩
  unfold objective
  nlinarith [sq_nonneg (coord 0 v + 1 / 2), sq_nonneg (coord 1 v + 1 / 2),
    sq_nonneg (coord 2 v)]

private theorem model_hessian_bound (k : ℕ) (v : ExampleSpace) :
    ‖fderiv ℝ (fderiv ℝ (model k)) v‖ ≤ 2 * ‖(coord 2).smulRight (coord 2)‖ := by
  have h := coefficient_bounds (amplitude_bounds k).1 (amplitude_bounds k).2
  rw [model_hessian]
  refine (ContinuousLinearMap.opNorm_smul_le (2 * coefficient (amplitude k))
    ((coord 2).smulRight (coord 2))).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) h.1)]
  exact mul_le_mul_of_nonneg_right (by linarith [h.2]) (norm_nonneg _)

private theorem center_active (k : ℕ) :
    activeConstraintSet ConstraintExample.constraints (center k) = {0} := by
  have hp := (amplitude_bounds k).1
  have hz : -(1 / 4 : ℝ) ≤ center k 2 := by
    change -(1 / 4 : ℝ) ≤ amplitude k ^ 2
    nlinarith [sq_nonneg (amplitude k)]
  have hc := ConstraintExample.constraints_of_height_ge (center k) hz
  ext i
  fin_cases i
  · change ConstraintExample.constraints 0 (center k) = 0 ↔ _
    rw [hc.1]
    simp [center]
  · change ConstraintExample.constraints 1 (center k) = 0 ↔ _
    rw [hc.2]
    simp [center, hp.ne']

private noncomputable def exampleDecreaseConstant : ℝ :=
  min (exampleCauchyParams.upperSlope * exampleCauchyParams.radiusFraction / 2)
    (2 * exampleCauchyParams.upperSlope * (1 - exampleCauchyParams.lowerSlope)) / 2

private theorem exampleDecreaseConstant_mem : exampleDecreaseConstant ∈ Set.Ioo 0 1 := by
  norm_num [exampleDecreaseConstant, exampleCauchyParams]

private theorem example_sufficient_decrease (k : ℕ) (β : ℝ) (hβ : 1 ≤ β) :
    let π := cappedCriticality orthant objective (center k)
    exampleDecreaseConstant * π * min (π / β) 2 ≤
      model k (center k) - model k (center (k + 1)) := by
  let π := cappedCriticality orthant objective (center k)
  let κ := 2 * exampleDecreaseConstant
  have hκ : 0 ≤ κ := mul_nonneg (by norm_num) exampleDecreaseConstant_mem.1.le
  have h := theorem_12_2_2_of_taylor_bound exampleCauchyParams orthant_closed orthant_convex
    (center_mem k) (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    (remote_cauchy k) (model_Taylor k)
  have hκeq : κ = min (exampleCauchyParams.upperSlope * exampleCauchyParams.radiusFraction / 2)
      (2 * exampleCauchyParams.upperSlope * (1 - exampleCauchyParams.lowerSlope)) := by
    dsimp [κ, exampleDecreaseConstant]
    ring
  have hdec := cappedCriticality_decrease (f := objective) (center_mem k) hκ
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2) (hκeq.symm ▸ h.2.1)
  have hπ₀ : 0 ≤ π := le_min zero_le_one (linearDecrease_nonneg (center_mem k) zero_le_one)
  have hπ₁ : π ≤ 1 := min_le_left _ _
  change exampleDecreaseConstant * π * min (π / β) 2 ≤ _
  calc
    _ ≤ exampleDecreaseConstant * π * π := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg exampleDecreaseConstant_mem.1.le hπ₀)
      exact (min_le_left _ _).trans ((div_le_self hπ₀ hβ))
    _ = κ * π * min (π / 2) 2 := by
      rw [min_eq_left (by linarith)]
      dsimp [κ]
      ring
    _ ≤ model k (center k) - model k remote := hdec
    _ ≤ _ := sub_le_sub_left (model_dominates_cauchy k) _

/-- Theorem 12.3.8 as printed can fail at the iterates as well as at the
Cauchy points. The same run refutes the subsequence claim of Lemma 12.3.7.
A smooth representation of the orthant has two independent
active gradients at the limit, but only one active constraint at the remote
Cauchy point. Every trial is very successful and satisfies AA.5. -/
theorem theorem_12_3_8_iterate_identification_counterexample :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 3))) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
      (c : Fin 2 → EuclideanSpace ℝ (Fin 3) → ℝ) (Q : GeneralizedCauchyParams)
      (κ Bf Bm : ℝ) (w : EuclideanSpace ℝ (Fin 3))
      (run : BTRRun f defaultBTRParams (fun _ _ _ _ ↦ True)),
      Chapter03.AC2 C ∧ Chapter03.AC7 C c ∧ (∀ i, ContDiff ℝ 2 (c i)) ∧
      ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
      (∀ v, ‖fderiv ℝ (fderiv ℝ f) v‖ ≤ Bf) ∧
      Tendsto run.x atTop (𝓝 0) ∧ IsCompact (insert 0 (Set.range run.x)) ∧
      LinearIndependent ℝ (fun i : activeConstraintSet c 0 ↦ gradient (c i) 0) ∧
      -gradient f 0 ∈ intrinsicInterior ℝ (normalDirections C 0) ∧
      κ ∈ Set.Ioo 0 1 ∧ w ∈ C ∧
      (∀ k, run.x k ∈ C ∧ run.x k + run.s k ∈ C ∧ run.Δ k = 2 ∧
        (∀ v, run.p k v = ‖v‖) ∧
        ContDiff ℝ 2 (run.model k) ∧ run.model k (run.x k) = f (run.x k) ∧
        fderiv ℝ (run.model k) (run.x k) = fderiv ℝ f (run.x k) ∧
        (∀ v, ‖fderiv ℝ (fderiv ℝ (run.model k)) v‖ ≤ Bm) ∧
        IsApproxGeneralizedCauchyPoint Q C f (run.model k) (run.x k) (run.Δ k) w ∧
        run.model k (run.x k + run.s k) ≤ run.model k w ∧
        activeConstraintSet c w ⊆ activeConstraintSet c (run.x k + run.s k) ∧
        defaultBTRParams.η₂ ≤ btrRatio f (run.model k) (run.x k) (run.s k) ∧
        (∀ β ≥ 1, κ * cappedCriticality C f (run.x k) *
          min (cappedCriticality C f (run.x k) / β) (run.Δ k) ≤
            run.model k (run.x k) - run.model k (run.x k + run.s k))) ∧
      ∀ k, activeConstraintSet c (run.x k) ≠ activeConstraintSet c 0 := by
  have hset : Chapter03.AC7 orthant ConstraintExample.constraints := by
    ext v
    exact (ConstraintExample.feasible_iff v).symm
  have hao : -gradient objective (0 : ExampleSpace) ∈
      intrinsicInterior ℝ (normalDirections orthant 0) := by
    rw [objective_gradient]
    have hg : objectiveGradient (0 : ExampleSpace) = point 1 1 0 := by
      simp [objectiveGradient, PiLp.zero_apply]
    rw [hg]
    exact ConstraintExample.ao4b_at_zero
  refine ⟨orthant, objective, ConstraintExample.constraints, exampleCauchyParams,
    exampleDecreaseConstant, ‖fderiv ℝ (fderiv ℝ objective) (0 : ExampleSpace)‖,
    2 * ‖(coord 2).smulRight (coord 2)‖, remote, exampleRun,
    ⟨⟨remote, remote_mem⟩, orthant_closed, orthant_convex⟩, hset,
    fun i ↦ (ConstraintExample.contDiff_constraints i).of_le (by simp),
    objective_contDiff, objective_bddBelow, fun v ↦ ?_, center_tendsto, center_tendsto.isCompact_insert_range,
    ConstraintExample.independent_active_at_zero, hao, exampleDecreaseConstant_mem,
    remote_mem, ?_, ?_⟩
  · rw [objective_hessian_constant v, objective_hessian_constant (0 : ExampleSpace)]
  · intro k
    simp only [exampleRun, center_step_eq]
    exact ⟨center_mem k, center_mem (k + 1), trivial, fun _ ↦ rfl,
      model_contDiff k, model_center k, model_fderiv_center k, model_hessian_bound k,
      remote_cauchy k, model_dominates_cauchy k,
      by rw [center_active, show activeConstraintSet ConstraintExample.constraints remote = {0}
               from ConstraintExample.active_at_remote],
      center_ratio k, example_sufficient_decrease k⟩
  · intro k
    change activeConstraintSet ConstraintExample.constraints (center k) ≠
      activeConstraintSet ConstraintExample.constraints (0 : ExampleSpace)
    rw [center_active, ConstraintExample.active_at_zero]
    intro h
    have h₁ : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := h.symm ▸ Set.mem_univ _
    simp at h₁

end ConnGouldToint.Chapter12
