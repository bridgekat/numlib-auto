import Numlib.Optimization.Composite.ModelCriticality
import Numlib.Optimization.Regularization.GlobalStep

/-!
# A literal outer-algorithm composite criticality counterexample

The smooth scalar and residual functions are explicit polynomials and the
outer function is absolute value. A genuine global model minimizer satisfies
the universal global-gap condition and all actual trial checks. The true ratio
accepts the step and the exact parameter updates satisfy the printed controls.

The allowed small first-order radius makes the next true test fail and violates
Equation 14.1.30. This uses the contract of outer Algorithm 14.1.1. The optional
detailed Algorithm 14.1.2 chooses a unit first-order radius for convex outer
functions, which excludes this particular execution. Its extra choice is not a
hypothesis of Lemma 14.1.7; it is separately required by Lemma 14.1.8.
-/

noncomputable section

namespace Composite.OuterCounterexample
/-- The scalar objective part in the one-trial composite example. -/
def f (t : ℝ) : ℝ := -(251 : ℝ) / 1000 * t
/-- The smooth residual in the one-trial composite example. -/
def c (t : ℝ) : ℝ := t / 4 - 1 / 4000 - t ^ 2 / 100
/-- The actual trial step. -/
def step : ℝ := 1 / 1000
/-- The accepted optimality radius. -/
def radius : ℝ := 1 / 24998000

/-- The scalar part's actual derivative evaluated on an arbitrary direction. -/
theorem fderiv_f (x d : ℝ) : fderiv ℝ f x d = -(251 : ℝ) / 1000 * d := by
  rw [show fderiv ℝ f x d = d * deriv f x from by simp]
  have hx : deriv f x = -(251 : ℝ) / 1000 := by
    unfold f
    simp
  rw [hx]
  ring_nf

/-- The residual's actual derivative evaluated on an arbitrary direction. -/
theorem fderiv_c (x d : ℝ) : fderiv ℝ c x d = (1 / 4 - x / 50) * d := by
  have hx := (((hasDerivAt_id x).div_const 4).sub (hasDerivAt_const x (1 / 4000))).sub
    (((hasDerivAt_id x).pow 2).div_const 100)
  have hx' : HasDerivAt c (1 / 4 - x / 50) x := by
    convert hx using 1
    · funext t
      simp only [c, Pi.sub_apply, id_eq, Pi.pow_apply]
    · simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, sub_zero]
      ring_nf
  rw [hx'.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring_nf

/-- The example uses the actual composite regularization model. -/
theorem model_formula (t : ℝ) : Composite.regularizedModel f c abs 1 0 1 t =
    -(251 : ℝ) / 1000 * t + |t / 4 - 1 / 4000| + t ^ 2 / 2 := by
  unfold Composite.regularizedModel ModelDecrease.penalized
  rw [Composite.taylorModel_one, fderiv_f, fderiv_c]
  simp [f, c, Real.norm_eq_abs, sq_abs]
  congr 1 <;> ring_nf

/-- Every generalized first-order trial uses the true scalar and residual derivatives. -/
theorem decrement_formula (x d : ℝ) : Composite.decrement f c abs 1 x d =
    (251 : ℝ) / 1000 * d + |c x| - |c x + (1 / 4 - x / 50) * d| := by
  rw [Composite.decrement_eq, Composite.taylorModel_one, fderiv_f, fderiv_c]
  ring_nf

/-- The selected step globally minimizes the actual composite model. -/
theorem model_min (t : ℝ) :
    Composite.regularizedModel f c abs 1 0 1 step ≤
      Composite.regularizedModel f c abs 1 0 1 t := by
  rw [model_formula, model_formula]
  norm_num [step]
  have h := le_abs_self (t / 4 - 1 / 4000)
  nlinarith [sq_nonneg (t - 1 / 1000)]

/-- The primitive positive global-gap fraction condition holds with fraction one. -/
theorem global_step : ModelDecrease.ApproximateGlobalStep
    (Composite.regularizedModel f c abs 1 0 1) 1 step := by
  intro t
  have hm := model_min t
  change 1 * (_ - _) ≤ _ - _
  linarith

/-- The retained absolute-value function satisfies every outer-function assumption. -/
theorem outer_properties : LipschitzWith 1 (abs : ℝ → ℝ) ∧
    ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 := by
  refine ⟨?_, ?_, abs_add_le, abs_zero⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro u v
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub u v
  · refine ⟨convex_univ, ?_⟩
    intro u hu v hv a b ha hb hab
    simp only [smul_eq_mul]
    calc |a * u + b * v| ≤ |a * u| + |b * v| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- The actual model's generalized first-order criticality is zero at every radius. -/
theorem model_criticality_zero {δ : ℝ} (hδ : 0 ≤ δ) :
    Composite.criticality (Composite.smoothModel f 1 0 1)
      (Composite.residualModel c 1 0) abs 1 step δ = 0 := by
  apply Composite.criticality_one_regularizedModel_eq_zero f c (by omega)
    (K := 1) (x := 0) (s := step) _ _ (fun t => model_min t) hδ
  · exact outer_properties.1
  · exact outer_properties.2.1

/-- The true objective's initial trial exactly attains its positive-radius criticality. -/
theorem initial_criticality : Composite.criticality f c abs 1 0 (1 / 2000) =
    (501 : ℝ) / 1000 * (1 / 2000) := by
  obtain ⟨d, hd, he⟩ := Composite.exists_decrement_eq_criticality f c
    (continuous_abs) 1 0 (δ := (1 / 2000 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2000)
  have hlow := Composite.decrement_le_criticality f c continuous_abs 1 0
    (δ := (1 / 2000 : ℝ)) (s := (1 / 2000 : ℝ)) (by norm_num)
  change Composite.decrement f c abs 1 0 (1 / 2000) ≤ _ at hlow
  change Composite.decrement f c abs 1 0 d = _ at he
  have hdu : d ≤ 1 / 2000 := le_trans (le_abs_self d) (by simpa only [Real.norm_eq_abs] using hd)
  have hinner : c 0 + (1 / 4 - (0 : ℝ) / 50) * d ≤ 0 := by dsimp [c]; linarith
  rw [decrement_formula, abs_of_nonpos hinner] at he
  norm_num [c] at he
  rw [decrement_formula] at hlow
  norm_num [c] at hlow
  linarith

/-- The accepted trial radius gives an exactly attaining actual objective decrement. -/
theorem next_criticality : Composite.criticality f c abs 1 step radius =
    (251 : ℝ) / 1000 * radius + 1 / 100000000 := by
  obtain ⟨d, hd, he⟩ := Composite.exists_decrement_eq_criticality f c
    continuous_abs 1 step (δ := radius) (by norm_num [radius])
  have hlow := Composite.decrement_le_criticality f c continuous_abs 1 step
    (δ := radius) (s := radius) (by norm_num [radius])
  change Composite.decrement f c abs 1 step radius ≤ _ at hlow
  change Composite.decrement f c abs 1 step d = _ at he
  have hdu : d ≤ radius := le_trans (le_abs_self d) (by simpa only [Real.norm_eq_abs] using hd)
  rw [decrement_formula] at he hlow
  norm_num [c, step, radius] at hlow
  have habs : 0 ≤ |-(1 / 100000000 : ℝ) + 12499 / 50000 * d| := abs_nonneg _
  norm_num [c, step] at he
  change _ = criticality f c abs 1 step radius at he
  dsimp [radius, step] at hdu he ⊢
  linarith

/-- Both smooth data maps satisfy the actual global first-order regularity. -/
theorem smoothness : ContDiff ℝ 1 f ∧ ContDiff ℝ 1 c := by
  constructor
  · unfold f
    fun_prop
  · unfold c
    fun_prop

/-- The actual scalar first derivative is globally Lipschitz with source bound one. -/
theorem f_derivative_lipschitz (u v : ℝ) :
    ‖iteratedFDeriv ℝ 1 f u - iteratedFDeriv ℝ 1 f v‖ ≤ 1 * ‖u - v‖ := by
  have he : iteratedFDeriv ℝ 1 f u - iteratedFDeriv ℝ 1 f v = 0 := by
    have hu : deriv f u = -(251 : ℝ) / 1000 := by simpa using fderiv_f u 1
    have hv : deriv f v = -(251 : ℝ) / 1000 := by simpa using fderiv_f v 1
    ext
    simp [sub_apply, iteratedFDeriv_one_apply, hu, hv]
  rw [he, norm_zero]
  positivity

/-- The actual residual first derivative has global Lipschitz constant one fiftieth. -/
theorem c_derivative_lipschitz (u v : ℝ) :
    ‖iteratedFDeriv ℝ 1 c u - iteratedFDeriv ℝ 1 c v‖ ≤ (1 / 50) * ‖u - v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro z
  simp only [sub_apply, iteratedFDeriv_one_apply, fderiv_c]
  rw [show (1 / 4 - u / 50) * z 0 - (1 / 4 - v / 50) * z 0 =
    (-(u - v) / 50) * z 0 by ring, norm_mul, norm_div, norm_neg]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  norm_num
  ring_nf
  exact le_rfl

/-- The actual composite objective is bounded below independently of any tolerance. -/
theorem bounded_below (t : ℝ) : -7 ≤ f t + |c t| := by
  have ha := neg_abs_le (c t)
  dsimp [f, c] at ha ⊢
  nlinarith [sq_nonneg (t - 501 / 20)]

/-- The initial and accepted centers of the one-trial trace. -/
def point (k : ℕ) : ℝ := if k = 0 then 0 else step
/-- The true objective-to-Taylor-decrement ratio. -/
def ratio : ℝ := 50099 / 50100

/-- Every prescribed parameter update is an actual legal very-successful update. -/
theorem parameter_updates : EvaluationComplexity.RegularizationParameterUpdates
    (fun _ => (1 : ℝ)) (fun _ => ratio) (1 / 4) (1 / 2) (1 / 2) 2 3 1 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro i hi
  norm_num [ratio]

/-- The true model, actual objective ratio, strict improvement and parameter updates
form the primitive outer-algorithm trace. -/
theorem model_trace : Composite.ModelTrace f c abs 1 point (fun _ => step)
    (fun _ => 1) (fun _ => ratio) (1 / 4) (1 / 2) (1 / 2) 2 3 1 1 := by
  refine ⟨parameter_updates, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    norm_num only [point]
    simp only [ite_true]
    rw [model_formula, model_formula]
    norm_num [step]
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    norm_num only [point]
    simp only [ite_true]
    rw [Composite.taylorModel_zero, Composite.taylorModel_one, fderiv_f, fderiv_c]
    norm_num [ratio, f, c, step]

/-- The actual scalar settings, initial failing test, accepted failing test and
model trial satisfy the literal outer algorithm's requirements. -/
theorem actual_checks :
    0 < (1 / 10 : ℝ) ∧ (1 / 10 : ℝ) < 1 ∧
    0 < (2 / 5 : ℝ) ∧ (2 / 5 : ℝ) ≤ 1 ∧
    0 < radius ∧ radius ≤ 1 ∧ 0 < step ∧ ‖step‖ ≤ 1 ∧
    point 1 = point 0 + step ∧ (1 / 2 : ℝ) ≤ ratio ∧
    (2 / 5 : ℝ) * (1 / 2000) < Composite.decrement f c abs 1 0 (1 / 2000) ∧
    (2 / 5 : ℝ) * radius < Composite.decrement f c abs 1 step radius ∧
    Composite.decrement (Composite.smoothModel f 1 0 1)
      (Composite.residualModel c 1 0) abs 1 step 0 ≤ (1 / 10 : ℝ) * (2 / 5) * radius := by
  rw [Composite.decrement_zero, decrement_formula, decrement_formula]
  norm_num [radius, step, point, ratio, f, c, Real.norm_eq_abs]

/-- The source-defined uniform parameter cap is exactly one hundred fifty-three
twenty-fifths in this execution. -/
theorem parameter_cap : max (1 : ℝ) (3 * (1 + 1 / 50) / (1 - 1 / 2)) = 153 / 25 := by
  norm_num

/-- The printed one-residual-error coefficient in Equation 14.1.30 fails for this actual
one-trial outer-algorithm execution, despite genuine failure of the next true test. -/
theorem violates_printed_bound :
    ¬((1 - (1 / 10 : ℝ)) * (2 / 5) * radius ≤
      (1 + 1 / 50 + max (1 : ℝ) (3 * (1 + 1 / 50) / (1 - 1 / 2))) *
          radius * ‖step‖ + (1 / 50 : ℝ) / 2 * ‖step‖ ^ 2) := by
  norm_num [radius, step, Real.norm_eq_abs]

/-- Both operational objective trials exactly attain their actual generalized criticalities. -/
theorem attaining_tests :
    Composite.decrement f c abs 1 0 (1 / 2000) =
      Composite.criticality f c abs 1 0 (1 / 2000) ∧
    Composite.decrement f c abs 1 step radius = Composite.criticality f c abs 1 step radius := by
  rw [initial_criticality, next_criticality, decrement_formula, decrement_formula]
  norm_num [c, step, radius]

/-- The actual model trial obeys both normalized operational inequalities at the
permitted nonunit radius, with fraction `zeta=1`, `theta=1/10` and `epsilon=2/5`. -/
theorem model_tests : ‖(0 : ℝ)‖ ≤ radius ∧
    Composite.criticality (Composite.smoothModel f 1 0 1)
      (Composite.residualModel c 1 0) abs 1 step radius ≤
        Composite.decrement (Composite.smoothModel f 1 0 1)
          (Composite.residualModel c 1 0) abs 1 step 0 ∧
    Composite.decrement (Composite.smoothModel f 1 0 1)
        (Composite.residualModel c 1 0) abs 1 step 0 ≤ (1 / 10 : ℝ) * (2 / 5) * radius := by
  rw [model_criticality_zero (by norm_num [radius]), Composite.decrement_zero]
  norm_num [radius]

/-- An actual smooth bounded-below composite problem, exact global model solve,
legal accepted trace and genuine failing next test violate the printed estimate.
The model radius is permitted by outer Algorithm 14.1.1; the optional detailed
convex solver's unit-radius choice is not imposed. -/
theorem verified_counterexample :
    ContDiff ℝ 1 f ∧ ContDiff ℝ 1 c ∧
    (∀ u v, ‖iteratedFDeriv ℝ 1 f u - iteratedFDeriv ℝ 1 f v‖ ≤ 1 * ‖u - v‖) ∧
    (∀ u v,
      ‖iteratedFDeriv ℝ 1 c u - iteratedFDeriv ℝ 1 c v‖ ≤ (1 / 50) * ‖u - v‖) ∧
    (∀ t, -7 ≤ f t + |c t|) ∧
    LipschitzWith 1 (abs : ℝ → ℝ) ∧ ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 ∧
    ModelDecrease.ApproximateGlobalStep
      (Composite.regularizedModel f c abs 1 0 1) 1 step ∧
    Composite.ModelTrace f c abs 1 point (fun _ => step) (fun _ => 1) (fun _ => ratio)
      (1 / 4) (1 / 2) (1 / 2) 2 3 1 1 ∧
    point 1 = point 0 + step ∧ (1 / 2 : ℝ) ≤ ratio ∧
    0 < radius ∧ radius ≤ 1 ∧ 0 < step ∧ ‖step‖ ≤ 1 ∧
    ‖(0 : ℝ)‖ ≤ radius ∧
    Composite.criticality (Composite.smoothModel f 1 0 1)
      (Composite.residualModel c 1 0) abs 1 step radius ≤
        Composite.decrement (Composite.smoothModel f 1 0 1)
          (Composite.residualModel c 1 0) abs 1 step 0 ∧
    Composite.decrement (Composite.smoothModel f 1 0 1)
        (Composite.residualModel c 1 0) abs 1 step 0 ≤ (1 / 10 : ℝ) * (2 / 5) * radius ∧
    (2 / 5 : ℝ) * (1 / 2000) < Composite.criticality f c abs 1 0 (1 / 2000) ∧
    (2 / 5 : ℝ) * radius < Composite.criticality f c abs 1 step radius ∧
    ¬((1 - (1 / 10 : ℝ)) * (2 / 5) * radius ≤
      (1 + 1 / 50 + max (1 : ℝ) (3 * (1 + 1 / 50) / (1 - 1 / 2))) *
          radius * ‖step‖ + (1 / 50 : ℝ) / 2 * ‖step‖ ^ 2) := by
  refine ⟨smoothness.1, smoothness.2, f_derivative_lipschitz, c_derivative_lipschitz,
    bounded_below, outer_properties.1, outer_properties.2.1, outer_properties.2.2.1,
    outer_properties.2.2.2, global_step, model_trace, ?_⟩
  have hchecks := actual_checks
  have hmodel := model_tests
  rcases hchecks with ⟨_, _, _, _, hr, hr1, hs, hs1, hx, hρ, hi, hn, hm⟩
  refine ⟨hx, hρ, hr, hr1, hs, hs1, hmodel.1, hmodel.2.1, hmodel.2.2, ?_, ?_,
    violates_printed_bound⟩
  · rwa [attaining_tests.1] at hi
  · rwa [attaining_tests.2] at hn
end Composite.OuterCounterexample
