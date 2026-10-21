import Mathlib.Analysis.InnerProductSpace.NormPow

/-!
# Hessians of powers of the norm

Radial powers with exponent greater than two are twice continuously differentiable,
including at the origin. Their Hessian is represented as a curried bilinear form.
-/

open scoped Topology ContDiff
open Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Any continuous bilinear form is bounded on a repeated direction by its operator norm. -/
theorem ContinuousLinearMap.abs_apply_self_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ) (u : V) :
    |B u u| ≤ ‖B‖ * ‖u‖ ^ (2 : ℕ) := by
  calc
    _ ≤ ‖B u‖ * ‖u‖ := (B u).le_opNorm u
    _ ≤ (‖B‖ * ‖u‖) * ‖u‖ := by gcongr; exact B.le_opNorm u
    _ = _ := by ring

/-- The rank-one formula for the Hessian of a radial power. -/
noncomputable def normRpowHessian (r : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (r * ‖x‖ ^ (r - 2)) • ((innerSL ℝ).restrictScalars ℝ : E →L[ℝ] E →L[ℝ] ℝ) +
    (r * (r - 2) * ‖x‖ ^ (r - 4)) • (innerSL ℝ x).smulRight (innerSL ℝ x)

/-- The radial Hessian formula vanishes at the origin for exponents greater than two. -/
@[simp] theorem normRpowHessian_zero (r : ℝ) (hr : 2 < r) :
    normRpowHessian r (0 : E) = 0 := by
  simp [normRpowHessian, Real.zero_rpow (by linarith : r - 2 ≠ 0)]

/-- The derivative of the radial gradient exists at zero, with zero derivative. -/
theorem hasFDerivAt_fderiv_norm_rpow_zero {r : ℝ} (hr : 2 < r) :
    HasFDerivAt (fderiv ℝ (fun x : E ↦ ‖x‖ ^ r)) (0 : E →L[ℝ] E →L[ℝ] ℝ) (0 : E) := by
  have hr1 : 1 < r := by linarith
  apply HasFDerivAt.of_isLittleO
  simp only [fderiv_norm_rpow _ hr1, norm_zero, map_zero, smul_zero, sub_zero, zero_apply]
  rw [← isLittleO_norm_left, ← isLittleO_norm_right]
  have heq : (fun x : E ↦ ‖(r * ‖x‖ ^ (r - 2)) • innerSL ℝ x‖) =
      (fun x : E ↦ ‖x‖ * (r * ‖x‖ ^ (r - 2))) := by
    funext x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), innerSL_apply_norm]
    ring
  rw [heq]
  have hcont : ContinuousAt (fun x : E ↦ r * ‖x‖ ^ (r - 2)) 0 := by
    fun_prop (discharger := positivity)
  have ht : Filter.Tendsto (fun x : E ↦ r * ‖x‖ ^ (r - 2)) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow (by linarith : r - 2 ≠ 0)] using hcont.tendsto
  simpa using (isBigO_refl (fun x : E ↦ ‖x‖) (𝓝 0)).mul_isLittleO
    ((isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr ht)

/-- Away from the origin, differentiating the radial derivative gives the rank-one formula. -/
theorem hasFDerivAt_fderiv_norm_rpow {r : ℝ} (hr : 2 < r) (x : E) :
    HasFDerivAt (fderiv ℝ (fun z : E ↦ ‖z‖ ^ r)) (normRpowHessian r x) x := by
  have hr1 : 1 < r := by linarith
  by_cases hx : x = 0
  · subst x
    simpa only [normRpowHessian_zero r hr] using hasFDerivAt_fderiv_norm_rpow_zero hr
  have hn : ‖x‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hi : HasFDerivAt (fun z : E ↦ innerSL ℝ z)
      ((innerSL ℝ).restrictScalars ℝ : E →L[ℝ] E →L[ℝ] ℝ) x :=
    (innerSL ℝ).hasFDerivAt
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (p := (r - 2) / 2) (Or.inl hn)).const_mul r).smul
      hi
  have hpow (z : E) : (‖z‖ ^ (2 : ℕ)) ^ ((r - 2) / 2) = ‖z‖ ^ (r - 2) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg z)]
    congr 1
    ring
  simp only [hpow] at h
  convert! h using 1
  · funext z
    exact fderiv_norm_rpow z hr1
  · ext u v
    simp only [normRpowHessian, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, smul_eq_mul]
    have he : (‖x‖ ^ (2 : ℕ)) ^ ((r - 2) / 2 - 1) = ‖x‖ ^ (r - 4) := by
      rw [← Real.rpow_natCast_mul (norm_nonneg x)]
      congr 1
      ring
    rw [he]
    simp only [ContinuousLinearMap.coe_restrictScalars', nsmul_eq_mul]
    ring

/-- The genuine second Fréchet derivative is the radial rank-one bilinear form. -/
theorem fderiv_fderiv_norm_rpow {r : ℝ} (hr : 2 < r) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z : E ↦ ‖z‖ ^ r)) x = normRpowHessian r x :=
  (hasFDerivAt_fderiv_norm_rpow hr x).fderiv

/-- The radial Hessian is symmetric. -/
theorem normRpowHessian_comm (r : ℝ) (x u v : E) :
    normRpowHessian r x u v = normRpowHessian r x v u := by
  simp only [normRpowHessian, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_restrictScalars',
    innerSL_apply_apply, smul_eq_mul]
  change r * ‖x‖ ^ (r - 2) * inner ℝ u v +
    r * (r - 2) * ‖x‖ ^ (r - 4) * (inner ℝ x u * inner ℝ x v) =
    r * ‖x‖ ^ (r - 2) * inner ℝ v u +
    r * (r - 2) * ‖x‖ ^ (r - 4) * (inner ℝ x v * inner ℝ x u)
  rw [real_inner_comm u v]
  ring

/-- The operator norm of the radial Hessian has the sharp upper bound, also at zero. -/
theorem norm_normRpowHessian_le {r : ℝ} (hr : 2 < r) (x : E) :
    ‖normRpowHessian r x‖ ≤ r * (r - 1) * ‖x‖ ^ (r - 2) := by
  by_cases hx : x = 0
  · subst x
    simp [normRpowHessian_zero r hr, Real.zero_rpow (by linarith : r - 2 ≠ 0)]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : ‖x‖ ^ (r - 4) * ‖x‖ ^ (2 : ℕ) = ‖x‖ ^ (r - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn]
    congr 1
    ring
  have hi : ‖((innerSL ℝ).restrictScalars ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    change ‖innerSL ℝ u‖ ≤ 1 * ‖u‖
    simp only [innerSL_apply_norm, one_mul, le_refl]
  have hs : ‖(innerSL ℝ x).smulRight (innerSL ℝ x)‖ ≤ ‖x‖ ^ (2 : ℕ) := by
    simpa only [innerSL_apply_norm, pow_two] using
      (ContinuousLinearMap.norm_smulRight_apply (innerSL ℝ x) (innerSL ℝ x)).le
  calc
    ‖normRpowHessian r x‖ ≤
        ‖(r * ‖x‖ ^ (r - 2)) • ((innerSL ℝ).restrictScalars ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖ +
          ‖(r * (r - 2) * ‖x‖ ^ (r - 4)) • (innerSL ℝ x).smulRight (innerSL ℝ x)‖ :=
      norm_add_le _ _
    _ ≤ (r * ‖x‖ ^ (r - 2)) * 1 +
        (r * (r - 2) * ‖x‖ ^ (r - 4)) * ‖x‖ ^ (2 : ℕ) := by
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ r * ‖x‖ ^ (r - 2) by positivity),
        abs_of_nonneg (show 0 ≤ r * (r - 2) * ‖x‖ ^ (r - 4) by positivity)]
      exact add_le_add (mul_le_mul_of_nonneg_left hi (by positivity))
        (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by
      rw [mul_assoc (r * (r - 2)), he]
      ring

/-- Quadratic forms are controlled in every direction, without a unit-vector hypothesis. -/
theorem abs_normRpowHessian_apply_self_le {r : ℝ} (hr : 2 < r) (x u : E) :
    |normRpowHessian r x u u| ≤ r * (r - 1) * ‖x‖ ^ (r - 2) * ‖u‖ ^ (2 : ℕ) := by
  exact (ContinuousLinearMap.abs_apply_self_le _ u).trans
    (mul_le_mul_of_nonneg_right (norm_normRpowHessian_le hr x) (sq_nonneg ‖u‖))

/-- The Hessian is continuous at the origin by its vanishing norm bound. -/
theorem continuous_normRpowHessian {r : ℝ} (hr : 2 < r) :
    Continuous (normRpowHessian r : E → E →L[ℝ] E →L[ℝ] ℝ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, normRpowHessian_zero r hr, tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun z ↦ norm_nonneg _) (fun z ↦ norm_normRpowHessian_le hr z)
    have h : ContinuousAt (fun z : E ↦ r * (r - 1) * ‖z‖ ^ (r - 2)) 0 := by
      fun_prop (discharger := positivity)
    simpa only [norm_zero, Real.zero_rpow (by linarith : r - 2 ≠ 0), mul_zero] using h.tendsto
  · have hs : Continuous (fun z : E ↦ (innerSL ℝ z).smulRight (innerSL ℝ z)) :=
      ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
        (innerSL ℝ).continuous).clm_apply (innerSL ℝ).continuous
    unfold normRpowHessian
    exact ((by fun_prop (discharger := simp [hx]) :
      ContinuousAt (fun z : E ↦ (r * ‖z‖ ^ (r - 2)) •
        ((innerSL ℝ).restrictScalars ℝ : E →L[ℝ] E →L[ℝ] ℝ)) x)).add
      ((by fun_prop (discharger := simp [hx]) :
        ContinuousAt (fun z : E ↦ r * (r - 2) * ‖z‖ ^ (r - 4)) x).smul hs.continuousAt)

/-- Every radial power with exponent greater than two is genuinely C² at every point. -/
theorem contDiff_two_norm_rpow {r : ℝ} (hr : 2 < r) :
    ContDiff ℝ 2 (fun x : E ↦ ‖x‖ ^ r) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨differentiable_norm_rpow (by linarith), by simp, ?_⟩
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (hasFDerivAt_fderiv_norm_rpow hr x).differentiableAt, ?_⟩
  simpa only [funext (fderiv_fderiv_norm_rpow hr)] using continuous_normRpowHessian (E := E) hr

/-- Evaluation of the Hessian in arbitrary directions. -/
theorem normRpowHessian_apply (r : ℝ) (x u v : E) :
    normRpowHessian r x u v = r * ‖x‖ ^ (r - 2) * inner ℝ u v +
      r * (r - 2) * ‖x‖ ^ (r - 4) * (inner ℝ x u * inner ℝ x v) := by
  rfl

/-- The radial direction attains the sharp Hessian bound away from zero. -/
theorem normRpowHessian_apply_radial {r : ℝ} {x : E} (hx : x ≠ 0) :
    normRpowHessian r x x x = r * (r - 1) * ‖x‖ ^ (r - 2) * ‖x‖ ^ (2 : ℕ) := by
  have he : ‖x‖ ^ (r - 4) * ‖x‖ ^ (2 : ℕ) = ‖x‖ ^ (r - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.mpr hx)]
    congr 1
    ring
  rw [normRpowHessian_apply, real_inner_self_eq_norm_sq]
  calc
    _ = r * ‖x‖ ^ (r - 2) * ‖x‖ ^ (2 : ℕ) +
        r * (r - 2) * (‖x‖ ^ (r - 4) * ‖x‖ ^ (2 : ℕ)) * ‖x‖ ^ (2 : ℕ) := by ring
    _ = _ := by rw [he]; ring

/-- The Hessian operator norm is exactly the radial value at nonzero points. -/
theorem norm_normRpowHessian {r : ℝ} (hr : 2 < r) {x : E} (hx : x ≠ 0) :
    ‖normRpowHessian r x‖ = r * (r - 1) * ‖x‖ ^ (r - 2) := by
  apply le_antisymm (norm_normRpowHessian_le hr x)
  have h := ContinuousLinearMap.abs_apply_self_le (normRpowHessian r x) x
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 0 ≤ r - 1 := by linarith
  rw [normRpowHessian_apply_radial hx, abs_of_nonneg (by positivity)] at h
  exact (mul_le_mul_iff_left₀ (pow_pos (norm_pos_iff.mpr hx) 2)).mp h
