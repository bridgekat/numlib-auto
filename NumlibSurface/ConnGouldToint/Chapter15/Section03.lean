import NumlibSurface.ConnGouldToint.Chapter11.Section02
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import NumlibSurface.ConnGouldToint.Chapter15.Section02
import NumlibSurface.ConnGouldToint.Chapter06.Section01

/-! # Exact-penalty SQP and second-order corrections

The quantitative Taylor hypotheses below supply the remainder orders used
in the source. Continuity of second derivatives alone supplies little-o
second-order remainders, and locally Lipschitz second derivatives give the
cubic remainders used in the reduction ratio. The ratio estimate is stated
for positive primal error, since the reduction can vanish at the solution.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Lemma 15.3.3 in quantitative form. The KKT residual is expanded
at the solution's multiplier, which makes the defect proportional to
the primal error times the joint error. -/
theorem lemma_15_3_3
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E)
    (x xstar s : E) (y ystar dy : Y)
    (B : (E × Y) ≃L[ℝ] (E × Y))
    (hB : (B : E × Y →L[ℝ] E × Y) = sqpKKT H A AT (x, y))
    (hstep : IsSQPCorrection g c H A AT (x, y) s (y + dy))
    {M L : ℝ} (hM : 0 ≤ M)
    (hinv : ‖(B.symm : E × Y →L[ℝ] E × Y)‖ ≤ M)
    (hTaylor :
      ‖sqpResidual g c AT (x, ystar) + B (xstar - x, 0)‖ ≤
        L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖)) :
    ‖x + s - xstar‖ ≤ M * L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖) ∧
    ‖s‖ ≤ (1 + M * L * ‖(x, y) - (xstar, ystar)‖) * ‖x - xstar‖ ∧
    ‖dy‖ ≤ (1 + M * L * ‖x - xstar‖) * ‖(x, y) - (xstar, ystar)‖ := by
  let z : E × Y := (x + s - xstar, y + dy - ystar)
  have hnewton := (isSQPCorrection_iff_newton g c H A AT (x, y) s dy).mp hstep
  have hdelta : B z = -(sqpResidual g c AT (x, ystar) + B (xstar - x, 0)) := by
    have hstep' : B (s, dy) = -sqpResidual g c AT (x, y) := by
      change (B : E × Y →L[ℝ] E × Y) (s, dy) = _
      rwa [hB]
    have hshift : B (0, y - ystar) =
        sqpResidual g c AT (x, y) - sqpResidual g c AT (x, ystar) := by
      change (B : E × Y →L[ℝ] E × Y) (0, y - ystar) = _
      rw [hB]
      ext
      · simp [sqpKKT, sqpResidual]
      · simp [sqpKKT, sqpResidual]
    have hz : z = (s, dy) - (xstar - x, 0) + (0, y - ystar) := by
      apply Prod.ext <;> dsimp [z] <;> abel
    rw [hz, map_add, map_sub, hstep', hshift]
    abel
  have hnorm : ‖z‖ ≤ M * L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖) := by
    calc
      _ = ‖B.symm (B z)‖ := by rw [B.symm_apply_apply]
      _ ≤ ‖(B.symm : E × Y →L[ℝ] E × Y)‖ * ‖B z‖ :=
        (B.symm : E × Y →L[ℝ] E × Y).le_opNorm _
      _ ≤ M * ‖B z‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ ≤ _ := by rw [hdelta, norm_neg, mul_assoc]; exact mul_le_mul_of_nonneg_left hTaylor hM
  have hx : ‖x + s - xstar‖ ≤ ‖z‖ := norm_fst_le z
  have hy : ‖y + dy - ystar‖ ≤ ‖z‖ := norm_snd_le z
  refine ⟨hx.trans hnorm, ?_, ?_⟩
  · calc
      _ = ‖(x + s - xstar) - (x - xstar)‖ := by congr 1; abel
      _ ≤ ‖x + s - xstar‖ + ‖x - xstar‖ := norm_sub_le _ _
      _ ≤ _ := by linarith only [hx.trans hnorm,
        show (1 + M * L * ‖(x, y) - (xstar, ystar)‖) * ‖x - xstar‖ =
          M * L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖) + ‖x - xstar‖ by ring]
  · have hys : ‖y - ystar‖ ≤ ‖(x, y) - (xstar, ystar)‖ :=
      norm_snd_le ((x, y) - (xstar, ystar))
    calc
      _ = ‖(y + dy - ystar) - (y - ystar)‖ := by congr 1; abel
      _ ≤ ‖y + dy - ystar‖ + ‖y - ystar‖ := norm_sub_le _ _
      _ ≤ _ := by linarith only [hy.trans hnorm, hys,
        show (1 + M * L * ‖x - xstar‖) * ‖(x, y) - (xstar, ystar)‖ =
          M * L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖) +
            ‖(x, y) - (xstar, ystar)‖ by ring]

omit [InnerProductSpace ℝ E] [NormedSpace ℝ Y] in
/-- Lemma 15.3.4 in a local restoration formulation. A feasible point
with constrained quadratic growth can be reached within a linear residual
bound, and the strict excess penalty controls the restoration displacement. -/
theorem lemma_15_3_4 (f : E → ℝ) (c : E → Y) (xstar : E)
    {r κ K L σ : ℝ} (hκ : 0 < κ) (hK : 0 ≤ K)
    (hσ : L * K < σ)
    (hrest : ∀ x, ‖x - xstar‖ < r → ∃ p, c p = 0 ∧ ‖p - xstar‖ < r ∧
      ‖x - p‖ ≤ K * ‖c x‖ ∧ ‖x - p‖ ≤ 1 ∧ f p - f x ≤ L * ‖c x‖ * K)
    (hgrowth : ∀ p, c p = 0 → ‖p - xstar‖ < r → κ * ‖p - xstar‖ ^ 2 ≤ f p - f xstar) :
    ∃ a > 0, ∀ x, ‖x - xstar‖ < r → a * ‖x - xstar‖ ^ 2 ≤ f x + σ * ‖c x‖ - f xstar := by
  let a := min (κ / 2) ((σ - L * K) / (2 * (K + 1)))
  have ha : 0 < a := lt_min (half_pos hκ) (div_pos (sub_pos.mpr hσ) (by positivity))
  refine ⟨a, ha, fun x hx => ?_⟩
  obtain ⟨p, hp, hpr, hxp, hsmall, hf⟩ := hrest x hx
  have hdist : ‖x - xstar‖ ≤ ‖x - p‖ + ‖p - xstar‖ := by
    rw [← show (x - p) + (p - xstar) = x - xstar by abel]
    exact norm_add_le _ _
  have hsq : ‖x - xstar‖ ^ 2 ≤ 2 * (‖x - p‖ ^ 2 + ‖p - xstar‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) hdist 2).trans (by
      nlinarith only [sq_nonneg (‖x - p‖ - ‖p - xstar‖)])
  have hlin : ‖x - p‖ ^ 2 ≤ (K + 1) * ‖c x‖ := by
    calc
      _ ≤ ‖x - p‖ := by nlinarith only [mul_nonneg (norm_nonneg (x - p)) (sub_nonneg.mpr hsmall)]
      _ ≤ K * ‖c x‖ := hxp
      _ ≤ _ := by linarith only [norm_nonneg (c x)]
  have ha₁ : 2 * a ≤ κ := by
    have := min_le_left (κ / 2) ((σ - L * K) / (2 * (K + 1)))
    linarith only [this]
  have ha₂ : (2 * a) * (K + 1) ≤ σ - L * K := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp
      (min_le_right (κ / 2) ((σ - L * K) / (2 * (K + 1))))
    linarith only [show (2 * a) * (K + 1) = a * (2 * (K + 1)) by ring, h]
  have h₁ := mul_le_mul_of_nonneg_right ha₁ (sq_nonneg ‖p - xstar‖)
  have h₂ := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 2 * a by positivity)
  have h₃ := mul_le_mul_of_nonneg_right ha₂ (norm_nonneg (c x))
  have h₄ := mul_le_mul_of_nonneg_left hsq ha.le
  nlinarith only [h₁, h₂, h₃, h₄, hf, hgrowth p hp hpr]

section Taylor

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- KKT stationarity cancels the linear difference between the exact-penalty
model step and a nearby target. -/
theorem sqp_model_target_error (f₀ fz : ℝ) (g s t : E) (H : E →L[ℝ] E)
    (A : E →L[ℝ] Z) (c₀ cz y : Z) {σ T : ℝ}
    (hH : H.toLinearMap.IsSymmetric) (hσ : ‖y‖ ≤ σ)
    (hfeas : c₀ + A s = 0)
    (hstat : ∀ d : E, ⟪g + H s, d⟫ = ⟪y, A d⟫)
    (hTaylor : |fz - ⟪y, cz⟫ -
      (Chapter06.quadraticModel f₀ g H.toLinearMap t - ⟪y, c₀ + A t⟫)| ≤ T) :
    |fz + σ * ‖cz‖ - Chapter06.quadraticModel f₀ g H.toLinearMap s| ≤
      T + (1 / 2) * ‖H‖ * ‖t - s‖ ^ 2 + 2 * σ * ‖cz‖ := by
  let d := t - s
  let q := Chapter06.quadraticModel f₀ g H.toLinearMap
  have ht : t = s + d := by dsimp [d]; abel
  have hmodel : q t - ⟪y, c₀ + A t⟫ = q s + (1 / 2) * ⟪d, H d⟫ := by
    have hc : c₀ + A t = A d := by rw [ht, map_add, ← add_assoc, hfeas, zero_add]
    have hs : ⟪s, H d⟫ = ⟪H s, d⟫ := (hH s d).symm
    have h := hstat d
    rw [inner_add_left] at h
    rw [hc, ht]
    dsimp only [q, Chapter06.quadraticModel, ContinuousLinearMap.coe_coe]
    simp only [map_add, inner_add_right, inner_add_left, hs, real_inner_comm d (H s)]
    rw [real_inner_comm d (H s)] at h
    linarith only [h]
  change |fz - ⟪y, cz⟫ - (q t - ⟪y, c₀ + A t⟫)| ≤ T at hTaylor
  rw [hmodel] at hTaylor
  have hcurv : |(1 / 2 : ℝ) * ⟪d, H d⟫| ≤ (1 / 2) * ‖H‖ * ‖d‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    calc
      _ ≤ (1 / 2) * (‖d‖ * ‖H d‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ (1 / 2) * (‖d‖ * (‖H‖ * ‖d‖)) := by gcongr; exact H.le_opNorm d
      _ = _ := by ring
  have hpen : |⟪y, cz⟫ + σ * ‖cz‖| ≤ 2 * σ * ‖cz‖ := by
    have hσ₀ := (norm_nonneg y).trans hσ
    have hy := (abs_real_inner_le_norm y cz).trans
      (mul_le_mul_of_nonneg_right hσ (norm_nonneg cz))
    calc
      _ ≤ |⟪y, cz⟫| + |σ * ‖cz‖| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg (mul_nonneg hσ₀ (norm_nonneg cz))]; linarith only [hy]
  change |fz + σ * ‖cz‖ - q s| ≤ _
  rw [show fz + σ * ‖cz‖ - q s =
    (fz - ⟪y, cz⟫ - (q s + (1 / 2) * ⟪d, H d⟫)) +
      (1 / 2) * ⟪d, H d⟫ + (⟪y, cz⟫ + σ * ‖cz‖) by ring]
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add hTaylor hcurv)) hpen)

private theorem sqp_curvature_error {d : E} {H : E →L[ℝ] E} {D B ex e : ℝ}
    (he : e ∈ Set.Icc (0 : ℝ) 1)
    (hstep : ‖d‖ ≤ D * ex * e) (hB : ‖H‖ ≤ B) :
    (1 / 2) * ‖H‖ * ‖d‖ ^ 2 ≤ (1 / 2) * B * D ^ 2 * (ex ^ 2 * e) := by
  have hsq : ‖d‖ ^ 2 ≤ D ^ 2 * (ex ^ 2 * e) := calc
    _ ≤ (D * ex * e) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hstep 2
    _ = (D ^ 2 * ex ^ 2) * (e * e) := by ring
    _ ≤ (D ^ 2 * ex ^ 2) * e :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_right he.1 he.2) (by positivity)
    _ = _ := by ring
  have hb := mul_le_mul hB hsq (sq_nonneg _) ((norm_nonneg H).trans hB)
  linarith only [hb, show (1 / 2 : ℝ) * B * D ^ 2 * (ex ^ 2 * e) =
    (1 / 2) * (B * (D ^ 2 * (ex ^ 2 * e))) by ring]

/-- Lemma 15.3.5 with quantitative Taylor remainders. -/
theorem lemma_15_3_5 (φ φstar f₀ : ℝ) (g s t : E) (H : E →L[ℝ] E)
    (A : E →L[ℝ] Z) (c₀ y : Z) {σ T D B ex e : ℝ}
    (hH : H.toLinearMap.IsSymmetric) (hσ : ‖y‖ ≤ σ)
    (hfeas : c₀ + A s = 0)
    (hstat : ∀ d : E, ⟪g + H s, d⟫ = ⟪y, A d⟫)
    (he : e ∈ Set.Icc (0 : ℝ) 1)
    (hstep : ‖t - s‖ ≤ D * ex * e) (hB : ‖H‖ ≤ B)
    (hTaylor : |φstar -
      (Chapter06.quadraticModel f₀ g H.toLinearMap t - ⟪y, c₀ + A t⟫)| ≤ T * (ex ^ 2 * e)) :
    |(φ - φstar) - (φ - Chapter06.quadraticModel f₀ g H.toLinearMap s)| ≤
      (T + (1 / 2) * B * D ^ 2) * (ex ^ 2 * e) := by
  have h := sqp_model_target_error f₀ φstar g s t H A c₀ 0 y hH hσ hfeas hstat
    (by simpa only [inner_zero_right, sub_zero] using hTaylor)
  simp only [norm_zero, mul_zero, add_zero] at h
  rw [show (φ - φstar) - (φ - Chapter06.quadraticModel f₀ g H.toLinearMap s) =
    -(φstar - Chapter06.quadraticModel f₀ g H.toLinearMap s) by ring, abs_neg]
  exact h.trans (by
    linarith only [sqp_curvature_error he hstep hB,
      show (T + (1 / 2) * B * D ^ 2) * (ex ^ 2 * e) =
        T * (ex ^ 2 * e) + (1 / 2) * B * D ^ 2 * (ex ^ 2 * e) by ring])

/-- Lemma 15.3.6. The correction solves the linearized constraint with
a Jacobian that differs from the Jacobian at the correction point by
order of the primal error. -/
theorem lemma_15_3_6 (φ f₀ fz : ℝ) (g s u : E) (H : E →L[ℝ] E)
    (A Ap As : E →L[ℝ] Z) (c₀ cs cz y : Z) {σ T D B R J ex e : ℝ}
    (hH : H.toLinearMap.IsSymmetric) (hσ : ‖y‖ ≤ σ)
    (hfeas : c₀ + A s = 0)
    (hstat : ∀ d : E, ⟪g + H s, d⟫ = ⟪y, A d⟫)
    (hex : 0 ≤ ex) (he : e ∈ Set.Icc (0 : ℝ) 1) (hJ : 0 ≤ J)
    (hstep : ‖u‖ ≤ D * ex * e) (hB : ‖H‖ ≤ B)
    (hCS : cs + Ap u = 0)
    (hJac : ‖As - Ap‖ ≤ J * ex)
    (hTaylorC : ‖cz - (cs + As u)‖ ≤ R * (ex ^ 2 * e))
    (hTaylor : |fz - ⟪y, cz⟫ -
      (Chapter06.quadraticModel f₀ g H.toLinearMap (s + u) - ⟪y, c₀ + A (s + u)⟫)| ≤
      T * (ex ^ 2 * e)) :
    |(φ - (fz + σ * ‖cz‖)) - (φ - Chapter06.quadraticModel f₀ g H.toLinearMap s)| ≤
      (T + (1 / 2) * B * D ^ 2 + 2 * σ * (R + J * D)) * (ex ^ 2 * e) := by
  have h := sqp_model_target_error f₀ fz g s (s + u) H A c₀ cz y hH hσ hfeas hstat hTaylor
  rw [add_sub_cancel_left] at h
  rw [show (φ - (fz + σ * ‖cz‖)) - (φ - Chapter06.quadraticModel f₀ g H.toLinearMap s) =
    -(fz + σ * ‖cz‖ - Chapter06.quadraticModel f₀ g H.toLinearMap s) by ring, abs_neg]
  have hcz : ‖cz‖ ≤ (R + J * D) * (ex ^ 2 * e) := by
    have hc : cs + As u = (As - Ap) u := by
      rw [sub_apply]
      rw [show cs = -(Ap u) by exact eq_neg_of_add_eq_zero_left hCS]
      abel
    calc
      _ = ‖(cz - (cs + As u)) + (cs + As u)‖ := by rw [sub_add_cancel]
      _ ≤ ‖cz - (cs + As u)‖ + ‖cs + As u‖ := norm_add_le _ _
      _ ≤ R * (ex ^ 2 * e) + (J * ex) * (D * ex * e) := by
        apply add_le_add hTaylorC
        rw [hc]
        exact ((As - Ap).le_opNorm _).trans
          (mul_le_mul hJac hstep (norm_nonneg _) (mul_nonneg hJ hex))
      _ = _ := by ring
  exact h.trans (by
    have hp := mul_le_mul_of_nonneg_left hcz (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((norm_nonneg y).trans hσ))
    linarith only [sqp_curvature_error he hstep hB, hp,
      show (T + (1 / 2) * B * D ^ 2 + 2 * σ * (R + J * D)) * (ex ^ 2 * e) =
        T * (ex ^ 2 * e) + (1 / 2) * B * D ^ 2 * (ex ^ 2 * e) +
          2 * σ * ((R + J * D) * (ex ^ 2 * e)) by ring])

end Taylor

/-- Theorem 15.3.7. At positive primal error, the model decrease is
positive and the corrected merit ratio differs from one by order of the
joint primal-dual error. -/
theorem theorem_15_3_7 {φ φstar φcorrected predicted a K T ex e : ℝ}
    (ha : 0 < a) (hT : 0 ≤ T) (hex : 0 < ex) (he : 0 ≤ e)
    (hsmall : K * e ≤ a / 2)
    (hgrowth : a * ex ^ 2 ≤ φ - φstar)
    (hmodel : |(φ - φstar) - predicted| ≤ K * (ex ^ 2 * e))
    (hcorrected : |(φ - φcorrected) - predicted| ≤ T * (ex ^ 2 * e)) :
    0 < predicted ∧ |(φ - φcorrected) / predicted - 1| ≤ (2 * T / a) * e := by
  have hhalf : (a / 2) * ex ^ 2 ≤ predicted := by
    have h₁ := (le_abs_self ((φ - φstar) - predicted)).trans hmodel
    have h₂ := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ex)
    nlinarith only [h₁, h₂, hgrowth]
  have hpred : 0 < predicted := (mul_pos (half_pos ha) (pow_pos hex _)).trans_le hhalf
  refine ⟨hpred, ?_⟩
  rw [show (φ - φcorrected) / predicted - 1 = (φ - φcorrected - predicted) / predicted by
    field_simp, abs_div, abs_of_pos hpred]
  apply (div_le_iff₀ hpred).mpr
  refine hcorrected.trans ?_
  have h := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ (2 * T / a) * e by positivity)
  refine le_trans ?_ h
  apply le_of_eq
  field_simp

/-- A scalar C² objective with a stationary point of positive curvature,
but with no local quadratic bound for the Newton error. The constraint
space may be taken to be zero-dimensional. -/
theorem sqp_C2_newton_counterexample :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ deriv f 0 = 0 ∧ deriv (deriv f) 0 = 1 ∧
      ∀ C δ : ℝ, 0 ≤ C → 0 < δ → ∃ x : ℝ, 0 < x ∧ x < δ ∧
        0 < deriv (deriv f) x ∧ C * x ^ 2 < x - deriv f x / deriv (deriv f) x := by
  let f (x : ℝ) := (1 / 2 : ℝ) * x ^ (2 : ℕ) + x ^ (5 / 2 : ℝ)
  have hf : ContDiff ℝ 2 f :=
    (contDiff_const.mul (contDiff_id.pow 2)).add
      (Real.contDiff_rpow_const_of_le (n := 2) (by norm_num))
  have hg : deriv f = fun x => x + (5 / 2 : ℝ) * x ^ (3 / 2 : ℝ) := by
    funext x
    have h₁ : HasDerivAt (fun z : ℝ => z ^ (2 : ℕ)) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h₂ : HasDerivAt (fun z : ℝ => z ^ (5 / 2 : ℝ))
        ((5 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) x := by
      convert (Real.hasDerivAt_rpow_const (x := x) (p := 5 / 2) (Or.inr (by norm_num))) using 1
      norm_num
    have h := ((h₁.const_mul (1 / 2 : ℝ)).fun_add h₂).deriv
    simpa only [f, one_div, inv_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hH : deriv (deriv f) = fun x => 1 + (15 / 4 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [hg]
    funext x
    have h₂ : HasDerivAt (fun z : ℝ => z ^ (3 / 2 : ℝ))
        ((3 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) x := by
      convert (Real.hasDerivAt_rpow_const (x := x) (p := 3 / 2) (Or.inr (by norm_num))) using 1
      norm_num
    have h := ((hasDerivAt_id x).fun_add (h₂.const_mul (5 / 2 : ℝ))).deriv
    rw [show (15 / 4 : ℝ) * x ^ (1 / 2 : ℝ) =
      (5 / 2 : ℝ) * ((3 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) by ring]
    exact h
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · rw [hg]
    norm_num [Real.zero_rpow]
  · rw [hH]
    norm_num [Real.zero_rpow]
  intro C δ hC hδ
  let t := min (min 1 (δ / 2)) (1 / (8 * (C + 1)))
  have ht : 0 < t := lt_min (lt_min zero_lt_one (half_pos hδ)) (by positivity)
  have ht₁ : t ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have htδ : t ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have htC : t ≤ 1 / (8 * (C + 1)) := min_le_right _ _
  have hr (p : ℝ) : (t ^ (2 : ℕ)) ^ p = t ^ ((2 : ℝ) * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hr₁ : (t ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = t := by rw [hr]; norm_num
  have hr₃ : (t ^ (2 : ℕ)) ^ (3 / 2 : ℝ) = t ^ (3 : ℕ) := by
    rw [hr, ← Real.rpow_natCast]
    norm_num
  refine ⟨t ^ (2 : ℕ), sq_pos_of_pos ht, ?_, ?_, ?_⟩
  · nlinarith only [htδ, hδ, mul_nonneg ht.le (sub_nonneg.mpr ht₁)]
  · simp only [hH, hr₁]
    positivity
  · rw [hH, hg]
    simp only [hr₁, hr₃]
    have hden : 0 < 1 + (15 / 4 : ℝ) * t := by positivity
    have hformula :
        t ^ (2 : ℕ) - (t ^ (2 : ℕ) + (5 / 2 : ℝ) * t ^ (3 : ℕ)) /
          (1 + (15 / 4 : ℝ) * t) =
        ((5 / 4 : ℝ) * t ^ (3 : ℕ)) / (1 + (15 / 4 : ℝ) * t) := by
      field_simp
      ring
    rw [hformula]
    apply (lt_div_iff₀ hden).mpr
    have hCt : C * t ≤ 1 / 8 := by
      have h := (le_div_iff₀ (by positivity : 0 < 8 * (C + 1))).mp htC
      nlinarith only [h, ht.le]
    have hmul := mul_le_mul hCt (show 1 + (15 / 4 : ℝ) * t ≤ 5 by linarith)
      hden.le (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hh := mul_lt_mul_of_pos_right
      (hmul.trans_lt (by norm_num : (1 / 8 : ℝ) * 5 < 5 / 4)) (pow_pos ht 3)
    nlinarith only [hh]

section ExactPenalty

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

omit [InnerProductSpace ℝ E] in
/-- A supporting functional for the scaled distance at a feasible point
is exactly a normal functional with norm at most the penalty weight. -/
theorem sqp_penalty_support_iff {C : Set Z} {r : Z} (hr : r ∈ C)
    (ell : Z →L[ℝ] ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ z, ell (z - r) ≤ σ * Metric.infDist z C) ↔
      ‖ell‖ ≤ σ ∧ ∀ c ∈ C, ell (c - r) ≤ 0 := by
  constructor
  · intro h
    refine ⟨ell.opNorm_le_bound hσ fun z => ?_, fun c hc => ?_⟩
    · have hpos : ell z ≤ σ * ‖z‖ := calc
        _ = ell ((z + r) - r) := by rw [add_sub_cancel_right]
        _ ≤ σ * Metric.infDist (z + r) C := h _
        _ ≤ _ := by
          have hd := Metric.infDist_le_dist_of_mem (x := z + r) hr
          rw [dist_eq_norm, add_sub_cancel_right] at hd
          exact mul_le_mul_of_nonneg_left hd hσ
      have hneg : -ell z ≤ σ * ‖z‖ := calc
        _ = ell ((-z + r) - r) := by rw [add_sub_cancel_right, map_neg]
        _ ≤ σ * Metric.infDist (-z + r) C := h _
        _ ≤ _ := by
          have hd := Metric.infDist_le_dist_of_mem (x := -z + r) hr
          rw [dist_eq_norm, add_sub_cancel_right, norm_neg] at hd
          exact mul_le_mul_of_nonneg_left hd hσ
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hpos⟩
    · simpa only [Metric.infDist_zero_of_mem hc, mul_zero] using h c
  · rintro ⟨hbound, hnormal⟩ z
    have hdist (c : Z) (hc : c ∈ C) : ell (z - r) ≤ σ * dist z c := by
      rw [dist_eq_norm]
      calc
        _ = ell (z - c) + ell (c - r) := by rw [← map_add, sub_add_sub_cancel]
        _ ≤ ell (z - c) := add_le_of_nonpos_right (hnormal c hc)
        _ ≤ |ell (z - c)| := le_abs_self _
        _ ≤ ‖ell‖ * ‖z - c‖ := by simpa only [Real.norm_eq_abs] using ell.le_opNorm (z - c)
        _ ≤ _ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    rcases hσ.eq_or_lt with rfl | hpos
    · simpa only [zero_mul] using hdist r hr
    · rw [mul_comm]
      apply (div_le_iff₀ hpos).mp
      exact (Metric.le_infDist ⟨r, hr⟩).mpr fun c hc =>
        (div_le_iff₀ hpos).mpr (by simpa only [mul_comm σ] using hdist c hc)

/-- The first-order part of Theorem 15.3.2 in normal-functional form.
Here the feasible residual set encodes the equality and inequality
constraints, and the norm distance gives the violation penalty. The
radius normal is common to the two systems. -/
theorem theorem_15_3_2_first_order {C : Set Z} {r : Z} (hr : r ∈ C)
    (A : E →L[ℝ] Z) (g radiusNormal : E →L[ℝ] ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ ell : Z →L[ℝ] ℝ, ‖ell‖ ≤ σ ∧ (∀ c ∈ C, ell (c - r) ≤ 0) ∧
      g + ell.comp A + radiusNormal = 0) ↔
    (∃ ell : Z →L[ℝ] ℝ, (∀ z, ell (z - r) ≤ σ * Metric.infDist z C) ∧
      g + ell.comp A + radiusNormal = 0) := by
  constructor
  · rintro ⟨ell, hb, hn, hs⟩
    exact ⟨ell, (sqp_penalty_support_iff hr ell hσ).mpr ⟨hb, hn⟩, hs⟩
  · rintro ⟨ell, hp, hs⟩
    obtain ⟨hb, hn⟩ := (sqp_penalty_support_iff hr ell hσ).mp hp
    exact ⟨ell, hb, hn, hs⟩

/-- The second-order part of Theorem 15.3.2 in tangent-cone form. For an
inactive trust region, strict exactness makes the zero directional
derivative cone of the penalty model equal the constrained critical
cone. The same quadratic Hessian is therefore tested on both. -/
theorem theorem_15_3_2_second_order {K : Set Z} (hK : IsClosed K) (h0 : (0 : Z) ∈ K)
    (A : E →L[ℝ] Z) (g : E →L[ℝ] ℝ) (H : E →L[ℝ] E)
    (ell : Z →L[ℝ] ℝ) {σ : ℝ} (hσ : ‖ell‖ < σ)
    (hnormal : ∀ z ∈ K, ell z ≤ 0) (hstat : g + ell.comp A = 0) :
    (∀ d ≠ (0 : E), A d ∈ K → g d = 0 → 0 < ⟪d, H d⟫) ↔
    (∀ d ≠ (0 : E), g d + σ * Metric.infDist (A d) K = 0 → 0 < ⟪d, H d⟫) := by
  have hsupport := (sqp_penalty_support_iff h0 ell (norm_nonneg _)).mpr
    ⟨le_rfl, by simpa only [sub_zero] using hnormal⟩
  have hcritical (d : E) :
      g d + σ * Metric.infDist (A d) K = 0 ↔ A d ∈ K ∧ g d = 0 := by
    constructor
    · intro hd
      have hs := congrArg (fun a : E →L[ℝ] ℝ => a d) hstat
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        zero_apply] at hs
      have h := hsupport (A d)
      rw [sub_zero] at h
      have he : Metric.infDist (A d) K = 0 := by
        by_contra! hne
        have hp := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hne)
        have hlt := mul_lt_mul_of_pos_right hσ hp
        linarith only [hs, h, hd, hlt]
      exact ⟨(hK.mem_iff_infDist_zero ⟨0, h0⟩).mpr he, by simpa only [he, mul_zero, add_zero] using hd⟩
    · rintro ⟨hK', hg⟩
      rw [hg, Metric.infDist_zero_of_mem hK', mul_zero, add_zero]
  constructor
  · intro h d hd hdir
    obtain ⟨hk, hg⟩ := (hcritical d).mp hdir
    exact h d hd hk hg
  · intro h d hd hk hg
    exact h d hd ((hcritical d).mpr ⟨hk, hg⟩)

end ExactPenalty

section Global

open Filter
open scoped Topology NNReal

/-- Distance form of the exact-penalty merit function (15.3.3).
For Euclidean equality and one-sided inequality residuals, distance
to the feasible residual cone is the norm of the violation vector. -/
noncomputable def sqpDistanceMerit (f : E → ℝ) (c : E → Y) (C : Set Y) (σ : ℝ)
    (x : E) : ℝ := f x + σ * Metric.infDist (c x) C

/-- Distance form of the quadratic-linearized model (15.3.4). -/
noncomputable def sqpDistanceModel (f : E → ℝ) (g : E → E) (c : E → Y)
    (A : E → E →L[ℝ] Y) (C : Set Y) (σ : ℝ)
    (x : E) (H : E →L[ℝ] E) (s : E) : ℝ :=
  Chapter06.quadraticModel (f x) (g x) H.toLinearMap s +
    σ * Metric.infDist (c x + A x s) C

/-- Uniform quadratic Taylor errors and a bounded model Hessian give
uniform normalized model agreement for the exact-penalty model. -/
theorem sqpDistanceModel_uniform_agreement (f : E → ℝ) (g : E → E) (c : E → Y)
    (A : E → E →L[ℝ] Y) (C : Set Y) {σ : ℝ} (hσ : 0 ≤ σ) {xstar : E}
    {ε Δ F K B : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ x ∈ Metric.ball xstar ε, ∀ s, ‖s‖ ≤ Δ →
      |f (x + s) - (f x + ⟪g x, s⟫)| ≤ F * ‖s‖ ^ 2)
    (hc : ∀ x ∈ Metric.ball xstar ε, ∀ s, ‖s‖ ≤ Δ →
      ‖c (x + s) - (c x + A x s)‖ ≤ K * ‖s‖ ^ 2) :
    Chapter11.UniformNormalizedModelAgreementAt (sqpDistanceMerit f c C σ)
      (fun x (H : {H : E →L[ℝ] E // ‖H‖ ≤ B}) s => sqpDistanceModel f g c A C σ x H s) xstar := by
  let D := F + (1 / 2) * B + σ * K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  intro a ha
  let r := min Δ (a / (D + 1))
  refine ⟨ε, r, hε, lt_min hΔ (by positivity), fun x hx H s hs => ?_⟩
  have hsΔ := hs.trans (min_le_left _ _)
  have habs :
      |sqpDistanceMerit f c C σ (x + s) - sqpDistanceModel f g c A C σ x H s| ≤ D * ‖s‖ ^ 2 := by
    have hd : |Metric.infDist (c (x + s)) C - Metric.infDist (c x + A x s) C| ≤
        K * ‖s‖ ^ 2 := by
      refine (abs_le.mpr ⟨?_, ?_⟩).trans (hc x hx s hsΔ)
      · have h := Metric.infDist_le_infDist_add_dist (x := c x + A x s) (y := c (x + s)) (s := C)
        rw [dist_comm, dist_eq_norm] at h
        linarith only [h]
      · have h := Metric.infDist_le_infDist_add_dist (x := c (x + s)) (y := c x + A x s) (s := C)
        rw [dist_eq_norm] at h
        linarith only [h]
    have hcurv : |(1 / 2 : ℝ) * ⟪s, (H : E →L[ℝ] E) s⟫| ≤ (1 / 2) * B * ‖s‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      calc
        _ ≤ (1 / 2) * (‖s‖ * ‖(H : E →L[ℝ] E) s‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
        _ ≤ (1 / 2) * (‖s‖ * (B * ‖s‖)) := by
          gcongr
          exact ((H : E →L[ℝ] E).le_opNorm s).trans
            (mul_le_mul_of_nonneg_right H.property (norm_nonneg _))
        _ = _ := by ring
    unfold sqpDistanceMerit sqpDistanceModel Chapter06.quadraticModel
    simp only [ContinuousLinearMap.coe_coe]
    rw [show f (x + s) + σ * Metric.infDist (c (x + s)) C -
        (f x + ⟪g x, s⟫ + 1 / 2 * ⟪s, (H : E →L[ℝ] E) s⟫ + σ * Metric.infDist (c x + A x s) C) =
        (f (x + s) - (f x + ⟪g x, s⟫) - 1 / 2 * ⟪s, (H : E →L[ℝ] E) s⟫) +
          σ * (Metric.infDist (c (x + s)) C - Metric.infDist (c x + A x s) C) by ring]
    have hp : |σ * (Metric.infDist (c (x + s)) C - Metric.infDist (c x + A x s) C)| ≤
        σ * (K * ‖s‖ ^ 2) := by
      rw [abs_mul, abs_of_nonneg hσ]
      exact mul_le_mul_of_nonneg_left hd hσ
    refine ((abs_add_le _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (hf x hx s hsΔ) hcurv)) hp)).trans ?_
    dsimp [D]
    ring_nf
    rfl
  by_cases hz : s = 0
  · simpa [Chapter11.normalizedModelError, hz] using ha.le
  have hp := norm_pos_iff.mpr hz
  rw [Chapter11.normalizedModelError, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hh := (le_div_iff₀ (by positivity : 0 < D + 1)).mp (hs.trans (min_le_right _ _))
  have hmul : D * ‖s‖ ≤ a := by nlinarith only [hh, hp.le]
  exact habs.trans (by simpa only [pow_two, ← mul_assoc] using
    mul_le_mul_of_nonneg_right hmul hp.le)

/-- Theorem 15.3.1 for the monotone nonsmooth trust-region algorithm.
At a feasible limit, the Clarke chain-rule inclusion supplies a
normal multiplier from penalty stationarity, without assuming a
multiplier already exists. -/
theorem theorem_15_3_1 [CompleteSpace E] (f : E → ℝ) (g : E → E) (c : E → Y)
    (A : E → E →L[ℝ] Y) (C : Set Y) {σ B : ℝ} (hσ : 0 ≤ σ)
    {Q : Chapter11.NonsmoothTRParams}
    (R : Chapter11.NonsmoothTRRun Q (sqpDistanceMerit f c C σ)
      (fun x (H : {H : E →L[ℝ] E // ‖H‖ ≤ B}) s => sqpDistanceModel f g c A C σ x H s))
    {xstar : E} {U : Set E} {L : NNReal} (hU : U ∈ 𝓝 xstar)
    (hL : LipschitzOnWith L (sqpDistanceMerit f c C σ) U)
    (herr : Chapter11.UniformNormalizedModelAgreementAt (sqpDistanceMerit f c C σ)
      (fun x (H : {H : E →L[ℝ] E // ‖H‖ ≤ B}) s => sqpDistanceModel f g c A C σ x H s) xstar)
    (hAA : ∀ y, R.HasLocalSufficientDecrease y)
    {j : ℕ → ℕ} (hj : StrictMono j) (hx : Tendsto (R.x ∘ j) atTop (𝓝 xstar))
    (hfeas : c xstar ∈ C)
    (hchain : ∀ w ∈ Optimization.clarkeSubgradient (sqpDistanceMerit f c C σ) xstar,
      ∃ ell : Y →L[ℝ] ℝ,
        (∀ z, ell (z - c xstar) ≤ σ * Metric.infDist z C) ∧
        ∀ d, ⟪w, d⟫ = ⟪g xstar, d⟫ + ell (A xstar d)) :
    ∃ ell : Y →L[ℝ] ℝ, ‖ell‖ ≤ σ ∧ (∀ z ∈ C, ell (z - c xstar) ≤ 0) ∧
      ∀ d, ⟪g xstar, d⟫ + ell (A xstar d) = 0 := by
  have hmatch : Chapter11.modelValueMatches (sqpDistanceMerit f c C σ)
      (fun x (H : {H : E →L[ℝ] E // ‖H‖ ≤ B}) s => sqpDistanceModel f g c A C σ x H s) := by
    intro x H
    simp [sqpDistanceModel, sqpDistanceMerit, Chapter06.quadraticModel]
  have hstat := Chapter11.theorem_11_2_5 R hU hL hmatch herr hAA hj hx
  obtain ⟨ell, hs, he⟩ := hchain 0 hstat
  obtain ⟨hb, hn⟩ := (sqp_penalty_support_iff hfeas ell hσ).mp hs
  exact ⟨ell, hb, hn, fun d => by simpa only [inner_zero_left] using (he d).symm⟩

end Global

end ConnGouldToint.Chapter15
