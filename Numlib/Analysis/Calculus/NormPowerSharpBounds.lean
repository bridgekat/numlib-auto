import Numlib.Analysis.Calculus.RadialDerivativePolynomial
import Numlib.Analysis.Calculus.NormPowerSmoothness

/-!
# Sharp diagonal norms of fractional radial derivatives

Below the radial exponent, the norm of the diagonal of the derivative tensor is
its radial evaluation. The polynomial maximum principle gives the upper bound;
the radial direction attains it. The derivatives vanish at the origin.
-/

noncomputable section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At unit base points and unit directions, the actual norm-power derivative is
the radial derivative polynomial evaluated at the directional cosine. -/
theorem iteratedFDeriv_normRpow_unit_eq_polynomial (a : ℝ) (n : ℕ) {x u : E}
    (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) :
    iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x (fun _ => u) =
      (radialDerivativePolynomial a n).eval ⟪x, u⟫ := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx
  rw [iteratedFDeriv_apply_const_eq_iteratedDeriv isOpen_compl_singleton
    (contDiffOn_normRpow a n) hx0 u, normRpow_add_smul_unit_eq_quadratic a hx hu,
    iteratedDeriv_quadratic_rpow_zero_eq_polynomial]

/-- The sharp falling-product bound for unit diagonal evaluations at unit base points. -/
theorem abs_iteratedFDeriv_normRpow_unit_le_fallingProduct {a : ℝ} {n : ℕ}
    (hn : (n : ℝ) < a) {x u : E} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) :
    |iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x (fun _ => u)| ≤
      ∏ i : Fin n, (a - i) := by
  rw [iteratedFDeriv_normRpow_unit_eq_polynomial a n hx hu]
  apply abs_radialDerivativePolynomial_eval_le hn
  apply abs_le.mp
  simpa only [hx, hu, one_mul] using abs_real_inner_le_norm x u

variable [FiniteDimensional ℝ E]

/-- A nonzero base point supplies its radius by homogeneity; the remaining directional
factor is exactly the radial derivative polynomial. -/
theorem iteratedFDeriv_normRpow_apply_unit_eq_polynomial (a : ℝ) (n : ℕ) {x u : E}
    (hx : x ≠ 0) (hu : ‖u‖ = 1) :
    iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x (fun _ => u) =
      ‖x‖ ^ (a - n) *
        (radialDerivativePolynomial a n).eval ⟪‖x‖⁻¹ • x, u⟫ := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let v := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  have he : x = ‖x‖ • v := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  conv_lhs => rw [he]
  rw [iteratedFDeriv_normRpow_smul a n hnx hv0,
    smul_apply, smul_eq_mul,
    iteratedFDeriv_normRpow_unit_eq_polynomial a n hv hu]

/-- The sharp diagonal derivative estimate at every nonzero base point. -/
theorem abs_iteratedFDeriv_normRpow_apply_unit_le {a : ℝ} {n : ℕ}
    (hn : (n : ℝ) < a) {x u : E} (hx : x ≠ 0) (hu : ‖u‖ = 1) :
    |iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x (fun _ => u)| ≤
      (∏ i : Fin n, (a - i)) * ‖x‖ ^ (a - n) := by
  rw [iteratedFDeriv_normRpow_apply_unit_eq_polynomial a n hx hu, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hv : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hbound := abs_radialDerivativePolynomial_eval_le hn
    (abs_le.mp (by simpa only [hv, hu, one_mul] using
      abs_real_inner_le_norm (‖x‖⁻¹ • x) u))
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (norm_nonneg x) (a - n))

/-- The diagonal norm of a derivative of a norm power is exactly the positive falling
product times the expected radial power, at every order below the exponent. -/
theorem diagonalNorm_iteratedFDeriv_normRpow {a : ℝ} {n : ℕ}
    (hn : (n : ℝ) < a) (x : E) :
    (iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x).diagonalNorm =
      (∏ i : Fin n, (a - i)) * ‖x‖ ^ (a - n) := by
  have hC := (fallingProduct_pos_of_lt hn).le
  have hr := Real.rpow_nonneg (norm_nonneg x) (a - n)
  by_cases hx : x = 0
  · subst x
    rw [iteratedFDeriv_norm_rpow_zero_of_lt hn, norm_zero,
      Real.zero_rpow (sub_pos.mpr hn).ne', mul_zero]
    exact le_antisymm (by simpa using
      (0 : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ).diagonalNorm_le_norm)
      (ContinuousMultilinearMap.diagonalNorm_nonneg _)
  apply le_antisymm
  · apply ContinuousMultilinearMap.diagonalNorm_le _ (mul_nonneg hC hr)
    intro u hu
    exact abs_iteratedFDeriv_normRpow_apply_unit_le hn hx hu
  · have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have h := (iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x).norm_diagonal_le_diagonalNorm hu
    rw [ContinuousMultilinearMap.diagonal_apply,
      iteratedFDeriv_normRpow_apply_unit a n hx, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC hr)] at h
    exact h

/-- Repeating the base vector in the actual derivative gives its falling product
coefficient times the original radial power, including at the origin. -/
theorem iteratedFDeriv_normRpow_apply_self {a : ℝ} {n : ℕ}
    (hn : (n : ℝ) < a) (x : E) :
    iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x (fun _ => x) =
      (∏ i : Fin n, (a - i)) * ‖x‖ ^ a := by
  by_cases hx : x = 0
  · subst x
    rw [iteratedFDeriv_norm_rpow_zero_of_lt hn]
    simp [Real.zero_rpow (show a ≠ 0 by have := Nat.cast_nonneg (α := ℝ) n; linarith)]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : x = ‖x‖ • (‖x‖⁻¹ • x) := by
    rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  have hm : (fun _ : Fin n => x) = fun _ => ‖x‖ • (‖x‖⁻¹ • x) :=
    funext fun _ => he
  rw [hm]
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, iteratedFDeriv_normRpow_apply_unit a n hx]
  rw [mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_add hnx]
  congr 2
  ring
