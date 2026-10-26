import Numlib.Optimization.Subproblem.Multiplier

/-!
# Early termination of the regularization subproblem

Algorithms for the regularization subproblem `min m^R(s) = ⟪g, s⟫ + ½ ⟪s, H s⟫ + σ/r ‖s‖^r` need
not solve it exactly: the adaptive-regularization methods of [cartis2022evaluation] only require a
step `s` with

* (9.3.14a) `m^R(s) ≤ m^R(0) = 0`,
* (9.3.14b) `‖∇m^R(s)‖ ≤ ½ θ₁ ‖s‖²`,
* (9.3.14c) `λ_min[∇²m^R(s)] ≥ -θ₂ ‖s‖`,

(`Subproblem.RegStoppingRules`). Theorem 9.3.2 gives a test, checkable from the secular function
alone, under which the step `s(λ) = -(H + λ)⁻¹ g` of a shift `λ ∈ 𝓕 = (λₛ, ∞)` satisfies them.

The book's `‖·‖_{M⁻¹}` dual norm of the gradient and the generalized eigenvalue
`λ_min[∇²m^R, M]` become, in the inner product space `E` (which carries the `M`-inner product), the
plain norm and the least value of the quadratic form `⟪v, ∇²m^R(s) v⟫` on unit vectors.

## Main statements

* `Subproblem.regStoppingRules_of_shifted`: the stopping rules hold at any solution of a shifted
  system `(H + λ) s = -g` with `H + λ ⪰ 0`, under the conditions on `‖s‖` of the proof
  of Theorem 9.3.2.
* `Subproblem.regStoppingRules_step`: Theorem 9.3.2, the same in terms of `π(λ) = ‖s(λ)‖²`
  ((9.3.15a)–(9.3.15c)).
* `Subproblem.regStoppingRules_of_isMinOn`: global minimizers satisfy the stopping rules.
-/

open Set
open scoped RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Stopping rules for the regularization subproblem** ([cartis2022evaluation] (9.3.14)) for the
step `s`, with constants `θ₁, θ₂`:
(9.3.14a) the model decreases, `m^R(s) ≤ m^R(0)`;
(9.3.14b) `‖g + H s + σ ‖s‖^{r-2} s‖ ≤ ½ θ₁ ‖s‖²` (the gradient of `m^R`, `hasGradientAt_regModel`);
(9.3.14c) `⟪v, ∇²m^R(s) v⟫ ≥ -θ₂ ‖s‖ ‖v‖²` for all `v`, i.e. the least eigenvalue of the Hessian
`regModelHessian H σ r s` is at least `-θ₂ ‖s‖`. -/
structure RegStoppingRules (g : E) (H : E →L[ℝ] E) (σ r θ₁ θ₂ : ℝ) (s : E) : Prop where
  /-- (9.3.14a): the model does not increase. -/
  decrease : regModel g H σ r s ≤ regModel g H σ r 0
  /-- (9.3.14b): the gradient `g + H s + σ ‖s‖^{r-2} s` of the regularized model is small
  (`RegStoppingRules.iff_gradient` for the form with `gradient`). -/
  gradient : ‖g + H s + (σ * ‖s‖ ^ (r - 2)) • s‖ ≤ (1 / 2) * θ₁ * ‖s‖ ^ 2
  /-- (9.3.14c): the Hessian is almost positive semidefinite. -/
  curvature : ∀ v, -(θ₂ * ‖s‖) * ‖v‖ ^ 2 ≤ ⟪v, regModelHessian H σ r s v⟫

variable {g : E} {H : E →L[ℝ] E} {σ r θ₁ θ₂ lam : ℝ} {s : E}

/-- For symmetric `H` and `r > 1`, the stopping rules (9.3.14) with the gradient `∇m^R(s)` written
as Mathlib's `gradient` of `regModel g H σ r` (`hasGradientAt_regModel`). -/
theorem RegStoppingRules.iff_gradient [CompleteSpace E] (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (hr : 1 < r) :
    RegStoppingRules g H σ r θ₁ θ₂ s ↔
      regModel g H σ r s ≤ regModel g H σ r 0 ∧
        ‖_root_.gradient (regModel g H σ r) s‖ ≤ (1 / 2) * θ₁ * ‖s‖ ^ 2 ∧
        ∀ v, -(θ₂ * ‖s‖) * ‖v‖ ^ 2 ≤ ⟪v, regModelHessian H σ r s v⟫ := by
  rw [(hasGradientAt_regModel hH σ hr s).gradient]
  exact ⟨fun h => ⟨h.decrease, h.gradient, h.curvature⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- **The stopping rules at a shifted solution** (proof of [cartis2022evaluation] Theorem 9.3.2).
Let `σ > 0`, `r > 2`, `(H + λ) s = -g` with `H + λ` positive semidefinite. If
(a) `σ/r ‖s‖^{r-2} ≤ λ/2`, (b) `|σ‖s‖^{r-2} - λ| ≤ ½ θ₁ ‖s‖` and (c) `σ‖s‖^{r-2} - λ ≥ -θ₂ ‖s‖`,
then `s` satisfies the stopping rules (9.3.14). -/
theorem regStoppingRules_of_shifted (hσ : 0 < σ) (hr : 2 < r)
    (hs : (H + lam • (1 : E →L[ℝ] E)) s = -g)
    (hpos : ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive)
    (ha : σ / r * ‖s‖ ^ (r - 2) ≤ lam / 2) (hb : |σ * ‖s‖ ^ (r - 2) - lam| ≤ (1 / 2) * θ₁ * ‖s‖)
    (hc : -(θ₂ * ‖s‖) ≤ σ * ‖s‖ ^ (r - 2) - lam) : RegStoppingRules g H σ r θ₁ θ₂ s where
  decrease := by
    rw [regModel_eq_of_shifted_general σ r hs, regModel_zero g H σ (by linarith)]
    have h1 := ContinuousLinearMap.inner_apply_nonneg_of_isPositive hpos s
    have h2 : ‖s‖ ^ 2 * (σ / r * ‖s‖ ^ (r - 2) - lam / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
    linarith
  gradient := by
    have hgrad : g + H s + (σ * ‖s‖ ^ (r - 2)) • s = (σ * ‖s‖ ^ (r - 2) - lam) • s := by
      rw [add_apply_eq_of_shifted hs, sub_smul]; abel
    rw [hgrad, norm_smul, Real.norm_eq_abs]
    calc |σ * ‖s‖ ^ (r - 2) - lam| * ‖s‖ ≤ (1 / 2) * θ₁ * ‖s‖ * ‖s‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = (1 / 2) * θ₁ * ‖s‖ ^ 2 := by ring
  curvature v := by
    have h1 := inner_regModelHessian_ge H hσ.le hr.le s v
    have h2 := ContinuousLinearMap.inner_apply_nonneg_of_isPositive hpos v
    have h3 : ⟪v, (H + (σ * ‖s‖ ^ (r - 2)) • (1 : E →L[ℝ] E)) v⟫ =
        ⟪v, (H + lam • (1 : E →L[ℝ] E)) v⟫ + (σ * ‖s‖ ^ (r - 2) - lam) * ‖v‖ ^ 2 := by
      simp only [add_apply, smul_apply,
        one_apply_eq_self, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq]
      ring
    have h4 : -(θ₂ * ‖s‖) * ‖v‖ ^ 2 ≤ (σ * ‖s‖ ^ (r - 2) - lam) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    linarith

/-- `(‖s‖²)^{a/2} = ‖s‖^a`. -/
private theorem sq_rpow_half (x : ℝ) (hx : 0 ≤ x) (a : ℝ) : (x ^ 2) ^ (a / 2) = x ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring

/-- **Global minimizers satisfy the stopping rules** (the remark after (9.3.14)): for `σ > 0`,
`r > 2` and `θ₁, θ₂ ≥ 0`, every global minimizer of `regModel g H σ r` satisfies
`RegStoppingRules g H σ r θ₁ θ₂`. -/
theorem regStoppingRules_of_isMinOn (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hσ : 0 < σ) (hr : 2 < r)
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hmin : IsMinOn (regModel g H σ r) univ s) :
    RegStoppingRules g H σ r θ₁ θ₂ s := by
  obtain ⟨hs, hpos⟩ := (isMinOn_regModel_iff hH hσ hr).1 hmin
  refine regStoppingRules_of_shifted hσ hr hs hpos ?_ ?_ ?_
  · have : σ / r ≤ σ / 2 := div_le_div_of_nonneg_left hσ.le two_pos hr.le
    have h0 : 0 ≤ ‖s‖ ^ (r - 2) := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  · simp only [sub_self, abs_zero]; positivity
  · simp only [sub_self]; nlinarith [norm_nonneg s]

variable [FiniteDimensional ℝ E] {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-- **Theorem 9.3.2** (constructive early termination test). Let `σ > 0`, `r > 2`, `λc ∈ 𝓕`, i.e.
`λc > λₛ`, `s = s(λc) = step g H λc` and `π = π(λc) = ‖s‖²`. If
(9.3.15a) `π ≤ (r/2)^{2/(r-2)} (λc/σ)^{2/(r-2)}`,
(9.3.15b) `|π^{(r-2)/2} - λc/σ| ≤ θ₁/(2σ) π^{1/2}`, and
(9.3.15c) `π^{(r-2)/2} - λc/σ ≥ -(θ₂/σ) π^{1/2}`,
then `s` satisfies the stopping rules (9.3.14). -/
theorem regStoppingRules_step (hσ : 0 < σ) (hr : 2 < r) (hlam : shiftThreshold hH < lam)
    (ha : secular g H lam ≤ (r / 2) ^ (2 / (r - 2)) * (lam / σ) ^ (2 / (r - 2)))
    (hb : |secular g H lam ^ ((r - 2) / 2) - lam / σ| ≤
      θ₁ / (2 * σ) * secular g H lam ^ (1 / 2 : ℝ))
    (hc : -(θ₂ / σ) * secular g H lam ^ (1 / 2 : ℝ) ≤ secular g H lam ^ ((r - 2) / 2) - lam / σ) :
    RegStoppingRules g H σ r θ₁ θ₂ (step g H lam) := by
  set s := step g H lam
  have hlam0 : 0 ≤ lam := shiftThreshold_nonneg.trans hlam.le
  have hlam1 : -leftmost hH < lam := neg_leftmost_le_shiftThreshold.trans_lt hlam
  have hn := norm_nonneg s
  -- `π^{(r-2)/2} = ‖s‖^{r-2}` and `π^{1/2} = ‖s‖`
  have hπr : secular g H lam ^ ((r - 2) / 2) = ‖s‖ ^ (r - 2) := sq_rpow_half _ hn _
  have hπ1 : secular g H lam ^ (1 / 2 : ℝ) = ‖s‖ := by
    rw [secular, sq_rpow_half _ hn, Real.rpow_one]
  rw [hπr, hπ1] at hb hc
  refine regStoppingRules_of_shifted hσ hr (step_spec hlam1).1 (isPositive_add_smul_of_le hlam1.le)
    ?_ ?_ ?_
  · -- raise (9.3.15a) to the power `(r-2)/2`
    have hp : 0 < (r - 2) / 2 := by linarith
    have he : 2 / (r - 2) * ((r - 2) / 2) = 1 := by field_simp [show r - 2 ≠ 0 by linarith]
    have h := Real.rpow_le_rpow (sq_nonneg _) ha hp.le
    rw [sq_rpow_half _ hn,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (div_nonneg hlam0 hσ.le),
      he, Real.rpow_one, Real.rpow_one] at h
    have hr0 : 0 < r := by linarith
    calc σ / r * ‖s‖ ^ (r - 2) ≤ σ / r * (r / 2 * (lam / σ)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = lam / 2 := by field_simp
  · have : |σ * ‖s‖ ^ (r - 2) - lam| = σ * |‖s‖ ^ (r - 2) - lam / σ| := by
      rw [← abs_of_pos hσ, ← abs_mul, abs_of_pos hσ]; congr 1; field_simp
    rw [this]
    calc σ * |‖s‖ ^ (r - 2) - lam / σ| ≤ σ * (θ₁ / (2 * σ) * ‖s‖) :=
          mul_le_mul_of_nonneg_left hb hσ.le
      _ = (1 / 2) * θ₁ * ‖s‖ := by field_simp
  · have h := mul_le_mul_of_nonneg_left hc hσ.le
    have e1 : σ * (-(θ₂ / σ) * ‖s‖) = -(θ₂ * ‖s‖) := by field_simp
    have e2 : σ * (‖s‖ ^ (r - 2) - lam / σ) = σ * ‖s‖ ^ (r - 2) - lam := by field_simp
    rw [e1, e2] at h
    exact h

end Subproblem
