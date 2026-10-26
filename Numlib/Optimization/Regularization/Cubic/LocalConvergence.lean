import Numlib.Optimization.Regularization.Cubic.FirstOrder
import Numlib.Optimization.SecondOrder.HessianRegion
import Numlib.Optimization.SecondOrder.ShiftedNewton

/-!
# Corrected local quadratic convergence for cubic regularization

The actual cubic penalty contributes a nonnegative multiple of the step norm.
Local coercivity therefore gives the uniform inverse-Hessian step bound without
the spurious constant penalty shift in the printed coefficient.
-/

namespace CubicRegularization
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual positive Hessian curvature and the tightened relative model test
bound the step by the current derivative. The norm-dependent penalty is dropped
only through its nonnegativity. -/
theorem step_norm_le_of_positive_hessian {f : E → ℝ} {x s : E} {m σ θ : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hm : 0 < m) (hσ : 0 ≤ σ)
    (hcurv : m * ‖s‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x s s)
    (hstat : ‖fderiv ℝ (model f x σ) s‖ ≤ θ * ‖fderiv ℝ f x‖) :
    ‖s‖ ≤ (1 + θ) / m * ‖fderiv ℝ f x‖ := by
  have hM := (fderiv ℝ (model f x σ) s).le_opNorm s
  have hg := (fderiv ℝ f x).le_opNorm s
  have hval : fderiv ℝ (model f x σ) s s =
      fderiv ℝ f x s + fderiv ℝ (fderiv ℝ f) x s s + σ / 2 * ‖s‖ ^ 3 := by
    rw [fderiv_model hf]
    simp only [add_apply, quadraticDerivative, smul_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, smul_eq_mul]
    ring
  have hMval : fderiv ℝ (model f x σ) s s ≤
      θ * ‖fderiv ℝ f x‖ * ‖s‖ := by
    exact (le_abs_self _).trans (hM.trans
      (mul_le_mul_of_nonneg_right hstat (norm_nonneg _)))
  have hgval : -‖fderiv ℝ f x‖ * ‖s‖ ≤ fderiv ℝ f x s := by
    have hh := (abs_le.mp hg).1
    linarith
  have hp : 0 ≤ σ / 2 * ‖s‖ ^ 3 := by positivity
  have hb : m * ‖s‖ ^ 2 ≤ (1 + θ) * ‖fderiv ℝ f x‖ * ‖s‖ := by
    nlinarith
  by_cases hs : s = 0
  · subst s
    have hm0 : 0 ≤ (1 + θ) * ‖fderiv ℝ f x‖ := by
      have hh := hstat
      have hnorm := norm_nonneg (fderiv ℝ f x)
      nlinarith [norm_nonneg (fderiv ℝ (model f x σ) 0)]
    simpa only [norm_zero, div_mul_eq_mul_div] using div_nonneg hm0 hm.le
  · have hspos := norm_pos_iff.mpr hs
    have hh : m * ‖s‖ ≤ (1 + θ) * ‖fderiv ℝ f x‖ := by
      exact le_of_mul_le_mul_right (by nlinarith [hb]) hspos
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).mpr
    nlinarith

/-- The corrected quadratic coefficient follows from the actual step estimate
and the sharp true Taylor gradient error. -/
theorem quadratic_trial_gradient_le {f : E → ℝ} {x s : E} {m σ σcap θ L : ℝ}
    (hf : ContDiff ℝ 2 f) (hm : 0 < m) (hσ : 0 ≤ σ) (hcap : σ ≤ σcap)
    (hθ : 0 ≤ θ) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hcurv : m * ‖s‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x s s)
    (hstat : ‖fderiv ℝ (model f x σ) s‖ ≤
      θ * min ‖fderiv ℝ f x‖ (‖s‖ ^ 2 / 2)) :
    ‖fderiv ℝ f (x + s)‖ ≤ (L + θ + σcap) / 2 * ((1 + θ) / m) ^ 2 *
      ‖fderiv ℝ f x‖ ^ 2 := by
  have hg := hstat.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hθ)
  have hs := step_norm_le_of_positive_hessian hf.contDiffAt hm hσ hcurv hg
  have hq : ‖fderiv ℝ (model f x σ) s‖ ≤ θ / 2 * ‖s‖ ^ 2 := by
    have hh := hstat.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ)
    nlinarith
  have he := trial_derivative_le hf hσ hlip x s hq
  have hbase : 0 ≤ (1 + θ) / m * ‖fderiv ℝ f x‖ := by positivity
  have hs2 := (sq_le_sq₀ (norm_nonneg _) hbase).mpr hs
  have hb := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ (L + θ + σcap) / 2 by
    have := hσ.trans hcap
    positivity)
  nlinarith [sq_nonneg ‖s‖]

/-- The corrected inverse-curvature multiplier for the actual cubic step. -/
noncomputable def localStepConstant (ℓ θ : ℝ) : ℝ := 2 * (1 + θ) / ℓ

/-- The corrected quadratic gradient coefficient, including the true cap. -/
noncomputable def localQuadraticConstant (ℓ L θ σcap : ℝ) : ℝ :=
  (L + θ + σcap) / 2 * localStepConstant ℓ θ ^ 2

/-- Positive least curvature makes the corrected step coefficient positive. -/
theorem localStepConstant_pos {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ : 0 ≤ θ) :
    0 < localStepConstant ℓ θ := by unfold localStepConstant;positivity

/-- The corrected quadratic coefficient is positive under true local data. -/
theorem localQuadraticConstant_pos {ℓ L θ σcap : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hθ : 0 ≤ θ) (hcap : 0 ≤ σcap) : 0 < localQuadraticConstant ℓ L θ σcap := by
  have hs := localStepConstant_pos hℓ hθ
  unfold localQuadraticConstant
  positivity

/-- The tightened actual cubic derivative test gives a positive quadratic
Taylor prediction on a short local trial, with its true cubic penalty. -/
theorem prediction_ge_of_positive_hessian {f : E → ℝ} {x s : E} {ℓ σ θ : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (_hℓ : 0 < ℓ) (hσ : 0 ≤ σ) (hθ : 0 < θ)
    (hcurv : ℓ / 2 * ‖s‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x s s)
    (hstat : ‖fderiv ℝ (model f x σ) s‖ ≤ θ / 2 * ‖s‖ ^ 2)
    (hsmall : ‖s‖ ≤ ℓ / (4 * θ)) :
    ℓ / 8 * ‖s‖ ^ 2 ≤ eval f 2 x 0 - eval f 2 x s := by
  have hval : fderiv ℝ (model f x σ) s s = fderiv ℝ f x s +
      fderiv ℝ (fderiv ℝ f) x s s + σ / 2 * ‖s‖ ^ 3 := by
    rw [fderiv_model hf]
    simp only [add_apply, quadraticDerivative, smul_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, smul_eq_mul]
    ring
  have hupper := ((le_abs_self (fderiv ℝ (model f x σ) s s)).trans
    ((fderiv ℝ (model f x σ) s).le_opNorm s)).trans
      (mul_le_mul_of_nonneg_right hstat (norm_nonneg s))
  have hsm := (le_div_iff₀ (show 0 < 4 * θ by positivity)).mp hsmall
  have hm := mul_le_mul_of_nonneg_right hsm (sq_nonneg ‖s‖)
  have hσterm : 0 ≤ σ / 2 * ‖s‖ ^ 3 := by positivity
  rw [eval_zero, eval_two_eq]
  nlinarith

/-- The sharp actual Taylor value error and the corrected quadratic prediction
force very successful acceptance for every sufficiently short local step. -/
theorem very_successful_of_local_step {f : E → ℝ} {x s : E} {ℓ L η₂ ρ : ℝ}
    (hf : ContDiff ℝ 2 f) (hℓ : 0 < ℓ) (hL : 0 < L) (hs : s ≠ 0)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hpred : ℓ / 8 * ‖s‖ ^ 2 ≤ eval f 2 x 0 - eval f 2 x s)
    (hsmall : ‖s‖ ≤ 3 * (1 - η₂) * ℓ / (4 * L))
    (hratio : ρ = (f x - f (x + s)) / (eval f 2 x 0 - eval f 2 x s)) : η₂ ≤ ρ := by
  have hd : 0 < eval f 2 x 0 - eval f 2 x s :=
    (by positivity : 0 < ℓ / 8 * ‖s‖ ^ 2).trans_le hpred
  have herr := abs_sub_eval_le_lipschitz (p := 1) (C := Set.univ) (D := Set.univ)
    isOpen_univ (Set.Subset.refl _) convex_univ hf.contDiffOn hL.le
    (fun y _ z _ => hlip y z) (Set.mem_univ x) (Set.mem_univ (x + s))
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at herr
  have hm := (le_div_iff₀ (show 0 < 4 * L by positivity)).mp hsmall
  have hsq := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖s‖)
  have hη : 0 ≤ 1 - η₂ := by
    have hh := norm_nonneg s
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hpred hη
  rw [hratio]
  apply (le_div_iff₀ hd).mpr
  rw [eval_zero] at hp ⊢
  nlinarith [(abs_le.mp herr).2]

/-- An explicit positive replacement for the printed five-term threshold.
The true inverse-curvature coefficient replaces the spurious penalty shift. -/
noncomputable def localThreshold (ℓ L θ σcap η₂ : ℝ) : ℝ :=
  let cs := localStepConstant ℓ θ
  let cq := localQuadraticConstant ℓ L θ σcap
  let r := ℓ / (4 * L)
  min (1 / (2 * cq)) (min (r / cs) (min (ℓ * r / 2)
    (min (ℓ / (4 * θ * cs)) (3 * (1 - η₂) * ℓ / (4 * L * cs)))))

/-- Every denominator of the corrected local threshold is strictly positive. -/
theorem localThreshold_pos {ℓ L θ σcap η₂ : ℝ}
    (hℓ : 0 < ℓ) (hL : 0 < L) (hθ : 0 < θ) (hcap : 0 ≤ σcap) (hη : η₂ < 1) :
    0 < localThreshold ℓ L θ σcap η₂ := by
  have hs := localStepConstant_pos hℓ hθ.le
  have hq := localQuadraticConstant_pos hℓ hL hθ.le hcap
  unfold localThreshold
  dsimp only
  repeat' apply lt_min
  all_goals positivity

/-- The corrected threshold satisfies all five quantitative local safeguards. -/
theorem localThreshold_bounds (ℓ L θ σcap η₂ : ℝ) :
    localThreshold ℓ L θ σcap η₂ ≤ 1 / (2 * localQuadraticConstant ℓ L θ σcap) ∧
    localThreshold ℓ L θ σcap η₂ ≤ (ℓ / (4 * L)) / localStepConstant ℓ θ ∧
    localThreshold ℓ L θ σcap η₂ ≤ ℓ * (ℓ / (4 * L)) / 2 ∧
    localThreshold ℓ L θ σcap η₂ ≤ ℓ / (4 * θ * localStepConstant ℓ θ) ∧
    localThreshold ℓ L θ σcap η₂ ≤
      3 * (1 - η₂) * ℓ / (4 * L * localStepConstant ℓ θ) := by
  unfold localThreshold
  dsimp only
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))⟩

/-- Primitive tightened AR2 rules, independent of the requested stopping
accuracy. All model comparisons, ratios and updates remain the actual ones. -/
structure TightenedRun (f : E → ℝ) (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ : ℝ) (N : ℕ) : Prop
    extends ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N where
  theta_pos : 0 < θ
  point_update : ∀ i < N, x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i
  stationary : ∀ i < N, ‖fderiv ℝ (model f (x i) (σ i)) (s i)‖ ≤
    θ * min ‖fderiv ℝ f (x i)‖ (‖s i‖ ^ 2 / 2)

/-- Restriction preserves every actual tightened model and update rule. -/
theorem TightenedRun.restrict {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ : ℝ} {N M : ℕ}
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N) (hM : M ≤ N) :
    TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ M where
  toModelTrace := {
    updates := { h.updates with update := fun i hi => h.updates.update i (hi.trans_le hM) }
    improvement := fun i hi => h.improvement i (hi.trans_le hM)
    ratio := fun i hi => h.ratio i (hi.trans_le hM) }
  theta_pos := h.theta_pos
  point_update := fun i hi => h.point_update i (hi.trans_le hM)
  stationary := fun i hi => h.stationary i (hi.trans_le hM)

/-- Before a positive first-order target, a tightened primitive prefix is an
actual first-order AR2 run and therefore inherits all global cubic budgets. -/
theorem TightenedRun.toFirstOrderRun {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε : ℝ} {N : ℕ}
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hfail : ∀ i < N, ε < ‖fderiv ℝ f (x i)‖) :
    FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ ε ⊤ N where
  second_disabled := rfl
  trace := h.toModelTrace
  theta_pos := h.theta_pos
  accuracy_pos := hε
  accuracy_le_one := hε1
  not_terminated := hfail
  stationary := by
    intro i hi
    have hh := (h.stationary i hi).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) h.theta_pos.le)
    nlinarith
  step := h.point_update

/-- The corrected threshold permits retaining the source reciprocal form
of the quadratic gradient estimate. -/
theorem localQuadraticConstant_le_inv_threshold {ℓ L θ σcap η₂ : ℝ}
    (hℓ : 0 < ℓ) (hL : 0 < L) (hθ : 0 < θ) (hcap : 0 ≤ σcap) (hη : η₂ < 1) :
    localQuadraticConstant ℓ L θ σcap ≤ 1 / localThreshold ℓ L θ σcap η₂ := by
  have hq := localQuadraticConstant_pos hℓ hL hθ.le hcap
  have hz := localThreshold_pos hℓ hL hθ hcap hη
  have hh := (localThreshold_bounds ℓ L θ σcap η₂).1
  have hb := (le_div_iff₀
    (show 0 < 2 * localQuadraticConstant ℓ L θ σcap by positivity)).mp hh
  apply (le_div_iff₀ hz).mpr
  nlinarith only [hb]

section CompleteSpace
variable [CompleteSpace E]

/-- A genuine least eigenpair bounds the actual Hessian form on arbitrary
vectors, not just on its unit eigenvector. -/
theorem least_curvature_form {f : E → ℝ} {x u : E} {ℓ : ℝ}
    (hstar : SecondOrderTrustRegion.IsLeastEigenpair f x ℓ u) (v : E) :
    ℓ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hh := ShiftedNewton.least_rayleigh_lower hstar v
  rw [SecondOrderTrustRegion.hessian_apply, TaylorModel.inner_hessianOperator,
    iteratedFDeriv_two_apply] at hh
  simpa using hh

/-- The actual tensor Lipschitz bound propagates least curvature at the
minimizer to every quadratic form in a neighboring point. -/
theorem curvature_lower_of_distance {f : E → ℝ} {xstar ustar x : E} {ℓ L : ℝ}
    (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hlip : ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f xstar‖ ≤ L * ‖x - xstar‖)
    (v : E) :
    (ℓ - L * ‖x - xstar‖) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hh := (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f xstar).le_opNorm ![v, v]
  simp only [sub_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.prod_univ_two] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_right hlip (by positivity))
  have hc := least_curvature_form hstar v
  have hlo := (abs_le.mp hb).1
  nlinarith

/-- The true Taylor gradient remainder at a stationary positive-curvature point
bounds distance by the actual derivative throughout a sufficiently small ball. -/
theorem gradient_distance_le_on_ball {f : E → ℝ} {xstar ustar y : E} {ℓ L : ℝ}
    (hf : ContDiff ℝ 2 f) (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (_hL : 0 ≤ L) (hzero : fderiv ℝ f xstar = 0)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖)
    (hy : L * ‖y - xstar‖ ≤ ℓ) : ‖y - xstar‖ ≤ 2 / ℓ * ‖fderiv ℝ f y‖ := by
  let v := y - xstar
  let A := fderiv ℝ (fderiv ℝ f) xstar v
  have he := norm_fderiv_sub_quadraticDerivative_le hf hlip xstar v
  have hpoint : xstar + v = y := by dsimp [v];abel
  rw [hpoint, quadraticDerivative, hzero, zero_add] at he
  change ‖fderiv ℝ f y - A‖ ≤ L * ‖v‖ ^ 2 / 2 at he
  have hA := norm_add_le (A - fderiv ℝ f y) (fderiv ℝ f y)
  rw [sub_add_cancel, norm_sub_rev] at hA
  have hv := A.le_opNorm v
  have hc := least_curvature_form hstar v
  change ℓ * ‖v‖ ^ 2 ≤ A v at hc
  have hv' : A v ≤ ‖A‖ * ‖v‖ := (le_abs_self _).trans hv
  have hb : ℓ * ‖v‖ ≤ ‖A‖ := by
    by_cases hz : v = 0
    · simp [hz]
    · exact le_of_mul_le_mul_right (by nlinarith [hc, hv']) (norm_pos_iff.mpr hz)
  have hm := mul_le_mul_of_nonneg_right hy (norm_nonneg v)
  change L * ‖v‖ * ‖v‖ ≤ ℓ * ‖v‖ at hm
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hℓ).mpr
  nlinarith

/-- Every actual tightened local trial is very successful and preserves the
corrected region, with the true quadratic gradient coefficient. -/
theorem trial_local_properties {f : E → ℝ} {xstar ustar x s : E}
    {ℓ L θ σ σcap η₂ ρ : ℝ}
    (hf : ContDiff ℝ 2 f) (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L) (hθ : 0 < θ) (hσ : 0 ≤ σ) (hcap : σ ≤ σcap)
    (hη : η₂ < 1) (hzero : fderiv ℝ f xstar = 0)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hx : ‖x - xstar‖ ≤ ℓ / (4 * L))
    (hg : ‖fderiv ℝ f x‖ ≤ localThreshold ℓ L θ σcap η₂)
    (hs : s ≠ 0)
    (hstat : ‖fderiv ℝ (model f x σ) s‖ ≤
      θ * min ‖fderiv ℝ f x‖ (‖s‖ ^ 2 / 2))
    (hratio : ρ = (f x - f (x + s)) / (eval f 2 x 0 - eval f 2 x s)) :
    η₂ ≤ ρ ∧ ‖s‖ ≤ localStepConstant ℓ θ * ‖fderiv ℝ f x‖ ∧
      ‖fderiv ℝ f (x + s)‖ ≤
        localQuadraticConstant ℓ L θ σcap * ‖fderiv ℝ f x‖ ^ 2 ∧
      ‖x + s - xstar‖ ≤ ℓ / (4 * L) ∧
      ‖fderiv ℝ f (x + s)‖ ≤ localThreshold ℓ L θ σcap η₂ := by
  let r := ℓ / (4 * L)
  let cs := localStepConstant ℓ θ
  let cq := localQuadraticConstant ℓ L θ σcap
  let ζ := localThreshold ℓ L θ σcap η₂
  have hcap0 := hσ.trans hcap
  have hcs : 0 < cs := localStepConstant_pos hℓ hθ.le
  have hcq : 0 < cq := localQuadraticConstant_pos hℓ hL hθ.le hcap0
  have hζ : 0 < ζ := localThreshold_pos hℓ hL hθ hcap0 hη
  obtain ⟨hzq, hzr, hzd, hzp, hzρ⟩ := localThreshold_bounds ℓ L θ σcap η₂
  have hdist := (le_div_iff₀ (show 0 < 4 * L by positivity)).mp hx
  have hcurv : ℓ / 2 * ‖s‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x s s := by
    have hh := curvature_lower_of_distance hstar (hlip x xstar) s
    nlinarith [sq_nonneg ‖s‖]
  have hrel := hstat.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hθ.le)
  have hstep := step_norm_le_of_positive_hessian hf.contDiffAt (half_pos hℓ) hσ hcurv hrel
  have hcs_eq : (1 + θ) / (ℓ / 2) = cs := by dsimp [cs, localStepConstant];ring
  rw [hcs_eq] at hstep
  have hsz : ‖s‖ ≤ cs * ζ := hstep.trans (mul_le_mul_of_nonneg_left hg hcs.le)
  have hsr : ‖s‖ ≤ r := by
    have hh := mul_le_mul_of_nonneg_left hzr hcs.le
    change cs * ζ ≤ cs * (r / cs) at hh
    rw [mul_div_cancel₀ _ hcs.ne'] at hh
    exact hsz.trans hh
  have hsp : ‖s‖ ≤ ℓ / (4 * θ) := by
    have hh := mul_le_mul_of_nonneg_left hzp hcs.le
    have he : cs * (ℓ / (4 * θ * cs)) = ℓ / (4 * θ) := by field_simp
    change cs * ζ ≤ cs * (ℓ / (4 * θ * cs)) at hh
    exact hsz.trans (hh.trans_eq he)
  have hsρ : ‖s‖ ≤ 3 * (1 - η₂) * ℓ / (4 * L) := by
    have hh := mul_le_mul_of_nonneg_left hzρ hcs.le
    have he : cs * (3 * (1 - η₂) * ℓ / (4 * L * cs)) =
        3 * (1 - η₂) * ℓ / (4 * L) := by field_simp
    change cs * ζ ≤ cs * (3 * (1 - η₂) * ℓ / (4 * L * cs)) at hh
    exact hsz.trans (hh.trans_eq he)
  have hsq : ‖fderiv ℝ (model f x σ) s‖ ≤ θ / 2 * ‖s‖ ^ 2 := by
    have hh := hstat.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ.le)
    nlinarith
  have hpred := prediction_ge_of_positive_hessian hf.contDiffAt hℓ hσ hθ hcurv hsq hsp
  have hρ := very_successful_of_local_step hf hℓ hL hs hlip hpred hsρ hratio
  have hgrad := quadratic_trial_gradient_le hf (half_pos hℓ) hσ hcap hθ.le hL.le
    hlip hcurv hstat
  rw [hcs_eq] at hgrad
  change ‖fderiv ℝ f (x + s)‖ ≤ cq * ‖fderiv ℝ f x‖ ^ 2 at hgrad
  have hζq : cq * ζ ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * cq by positivity)).mp hzq
    nlinarith
  have hgg := (sq_le_sq₀ (norm_nonneg _) hζ.le).mpr hg
  have hggq := mul_le_mul_of_nonneg_left hgg hcq.le
  have hgζ : ‖fderiv ℝ f (x + s)‖ ≤ ζ := by
    nlinarith [mul_le_mul_of_nonneg_right hζq hζ.le]
  have hyfar : ‖x + s - xstar‖ ≤ r + r := by
    calc
      _ = ‖(x - xstar) + s‖ := by congr 1;abel
      _ ≤ ‖x - xstar‖ + ‖s‖ := norm_add_le _ _
      _ ≤ r + r := add_le_add hx hsr
  have hyr : L * ‖x + s - xstar‖ ≤ ℓ := by
    have he : L * (r + r) = ℓ / 2 := by dsimp [r];field_simp;ring
    exact ((mul_le_mul_of_nonneg_left hyfar hL.le).trans_eq he).trans
      (by linarith only [hℓ])
  have hyd := gradient_distance_le_on_ball hf hstar hℓ hL.le hzero hlip hyr
  have hzdist : 2 / ℓ * ζ ≤ r := by
    have hh := hzd
    change ζ ≤ ℓ * r / 2 at hh
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hℓ).mpr
    nlinarith only [hh]
  refine ⟨hρ, hstep, hgrad, ?_, hgζ⟩
  exact hyd.trans ((mul_le_mul_of_nonneg_left hgζ (by positivity)).trans hzdist)

/-- The accepted one-step quadratic estimate needs only local curvature at
the current point; the gradient need not yet be below the local threshold. -/
theorem TightenedRun.local_quadratic_step {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ ℓ L : ℝ} {N i : ℕ} {xstar ustar : E}
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    (hf : ContDiff ℝ 2 f) (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hx : ‖x i - xstar‖ ≤ ℓ / (4 * L)) (hs : η₁ ≤ ρ i) :
    ‖fderiv ℝ f (x (i + 1))‖ ≤
      localQuadraticConstant ℓ L θ (max (σ 0) (γ₃ * L / (1 - η₂))) *
        ‖fderiv ℝ f (x i)‖ ^ 2 := by
  have hd := (le_div_iff₀ (show 0 < 4 * L by positivity)).mp hx
  have hcurv : ℓ / 2 * ‖s i‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) (x i) (s i) (s i) := by
    have hh := curvature_lower_of_distance hstar (hlip (x i) xstar) (s i)
    nlinarith [sq_nonneg ‖s i‖]
  have hb := quadratic_trial_gradient_le hf (half_pos hℓ) (h.updates.pos hi.le).le
    (h.toModelTrace.parameter_le hf hL.le hlip hi.le) h.theta_pos.le hL.le hlip
      hcurv (h.stationary i hi)
  have he : (1 + θ) / (ℓ / 2) = localStepConstant ℓ θ := by unfold localStepConstant;ring
  rw [he] at hb
  rw [h.point_update i hi, ite_eq_left hs]
  exact hb

/-- A genuine tightened execution stays in the corrected local region after
entry, and every later available trial is very successful with the corrected
quadratic gradient estimate. None of these conclusions is a trace field. -/
theorem TightenedRun.local_persistence {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ ℓ L : ℝ} {N k₀ : ℕ} {xstar ustar : E}
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    (hf : ContDiff ℝ 2 f) (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L) (hzero : fderiv ℝ f xstar = 0)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (_hk₀ : k₀ ≤ N) (hx₀ : ‖x k₀ - xstar‖ ≤ ℓ / (4 * L))
    (hg₀ : ‖fderiv ℝ f (x k₀)‖ ≤
      localThreshold ℓ L θ (max (σ 0) (γ₃ * L / (1 - η₂))) η₂) :
    let ζ := localThreshold ℓ L θ (max (σ 0) (γ₃ * L / (1 - η₂))) η₂
    let cq := localQuadraticConstant ℓ L θ (max (σ 0) (γ₃ * L / (1 - η₂)))
    (∀ i, k₀ ≤ i → i ≤ N →
      ‖x i - xstar‖ ≤ ℓ / (4 * L) ∧ ‖fderiv ℝ f (x i)‖ ≤ ζ) ∧
      ∀ i, k₀ ≤ i → i < N → η₂ ≤ ρ i ∧
        ‖fderiv ℝ f (x (i + 1))‖ ≤ cq * ‖fderiv ℝ f (x i)‖ ^ 2 := by
  dsimp only
  let cap := max (σ 0) (γ₃ * L / (1 - η₂))
  let ζ := localThreshold ℓ L θ cap η₂
  let cq := localQuadraticConstant ℓ L θ cap
  have hone : ∀ i < N, ‖x i - xstar‖ ≤ ℓ / (4 * L) → ‖fderiv ℝ f (x i)‖ ≤ ζ →
      η₂ ≤ ρ i ∧ ‖x (i + 1) - xstar‖ ≤ ℓ / (4 * L) ∧
        ‖fderiv ℝ f (x (i + 1))‖ ≤ ζ ∧
        ‖fderiv ℝ f (x (i + 1))‖ ≤ cq * ‖fderiv ℝ f (x i)‖ ^ 2 := by
    intro i hi hx hg
    have hs : s i ≠ 0 := by
      intro hz
      have hh := h.improvement i hi
      rw [hz] at hh
      exact (lt_irrefl _) hh
    have hh := trial_local_properties hf hstar hℓ hL h.theta_pos
      (h.updates.pos hi.le).le (h.toModelTrace.parameter_le hf hL.le hlip hi.le)
      h.updates.eta2_lt_one hzero hlip hx hg hs (h.stationary i hi) (h.ratio i hi)
    have hxnext : x (i + 1) = x i + s i := by
      rw [h.point_update i hi, ite_eq_left (h.updates.eta1_le_eta2.trans hh.1)]
    rw [←hxnext] at hh
    exact ⟨hh.1, hh.2.2.2.1, hh.2.2.2.2, hh.2.2.1⟩
  have hinv : ∀ i, k₀ ≤ i → i ≤ N →
      ‖x i - xstar‖ ≤ ℓ / (4 * L) ∧ ‖fderiv ℝ f (x i)‖ ≤ ζ := by
    intro i hki
    induction i, hki using Nat.le_induction with
    | base => intro _;exact ⟨hx₀, hg₀⟩
    | succ i hki ih =>
      intro hi
      obtain ⟨hx, hg⟩ := ih (by omega)
      have hh := hone i (by omega) hx hg
      exact ⟨hh.2.1, hh.2.2.1⟩
  refine ⟨hinv, ?_⟩
  intro i hki hi
  have hh := hone i hi (hinv i hki hi.le).1 (hinv i hki hi.le).2
  exact ⟨hh.1, hh.2.2.2⟩

end CompleteSpace
end CubicRegularization
