import Numlib.Optimization.Regularization.Inexact.StepOne
import Numlib.Optimization.Regularization.Inexact.StepTwo
import Numlib.Analysis.Calculus.TaylorModel.Scalar
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Scalar models for guarded dynamic accuracy executions

Affine derivative jets give actual quadratic regularized models. Their exact
criticality, global minimizers and ordered radius checks make it possible to
verify each primitive operation of a dynamic accuracy execution. The bounded
sine objective has globally Lipschitz zeroth and first derivative tensors.
-/

namespace InexactRegularization.GuardedCounterexample
open InexactTrustRegion
/-- An affine function supplying an actual constant and first derivative. -/
noncomputable def affine (c g x : ℝ) : ℝ := c + g * x
/-- The actual multilinear derivative jet of an affine function at zero. -/
noncomputable def jet (c g : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  ftaylorSeries ℝ (affine c g) 0
/-- The actual scalar derivative of the affine jet source. -/
theorem deriv_affine (c g x : ℝ) : deriv (affine c g) x = g := by
  have h : HasDerivAt (affine c g) g x := by
    convert (hasDerivAt_const x c).add ((hasDerivAt_id x).const_mul g) using 1 <;>
      (first | (funext t; rfl) | ring)
  exact h.deriv
/-- The computed first-order Taylor model has its prescribed affine value. -/
theorem value (c g s : ℝ) : TaylorModel.ofJet (jet c g) 1 s = c + g * s := by
  change TaylorModel.eval (affine c g) 1 0 s = _
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  simp [Finset.sum_range_succ, deriv_affine, affine, mul_comm]
/-- The computed decrement contains exactly the supplied first derivative. -/
theorem decrement (c g s : ℝ) : TaylorModel.jetDecrement (jet c g) 1 s = -g * s := by
  rw [TaylorModel.jetDecrement, value, value]
  ring
/-- The actual norm-regularized first-order model is a scalar quadratic. -/
theorem model_formula (c g σ s : ℝ) : model (jet c g) 1 σ s = c + g * s + σ / 2 * s ^ 2 := by
  simp [model, ModelDecrease.penalized, value, Real.norm_eq_abs, sq_abs]
/-- The actual derivative of the regularized quadratic model. -/
theorem model_deriv (c g σ s : ℝ) : deriv (model (jet c g) 1 σ) s = g + σ * s := by
  have he : model (jet c g) 1 σ = fun t => c + g * t + σ / 2 * t ^ 2 :=
    funext (model_formula c g σ)
  rw [he]
  have hh : HasDerivAt (fun t : ℝ => c + g * t + σ / 2 * t ^ 2) (g + σ * s) s := by
    convert (((hasDerivAt_const s c).add ((hasDerivAt_id s).const_mul g)).add
      (((hasDerivAt_id s).pow 2).const_mul (σ / 2))) using 1 <;>
      (first | (funext t; rfl) | (simp only [id_eq]; ring))
  exact hh.deriv
/-- The true supremum of computed affine decrements on a scalar closed ball. -/
theorem criticality (c g δ : ℝ) (hδ : 0 ≤ δ) :
    TaylorModel.jetCriticality (jet c g) 1 δ = |g| * δ := by
  apply le_antisymm
  · apply (TaylorModel.jetCriticality_le_iff _ _ hδ).mpr
    intro s hs
    rw [decrement]
    calc -g * s ≤ |-g * s| := le_abs_self _
      _ = |g| * |s| := by rw [abs_mul, abs_neg]
      _ ≤ |g| * δ := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  · by_cases hg : 0 ≤ g
    · have h := TaylorModel.jetDecrement_le_jetCriticality (jet c g) 1
        (δ := δ) (s := -δ) (by simp [Real.norm_eq_abs, abs_of_nonneg hδ])
      simpa [decrement, abs_of_nonneg hg] using h
    · have h := TaylorModel.jetDecrement_le_jetCriticality (jet c g) 1
        (δ := δ) (s := δ) (by simp [Real.norm_eq_abs, abs_of_nonneg hδ])
      simpa [decrement, abs_of_neg (lt_of_not_ge hg)] using h
/-- Completing the square proves that the exact quadratic return is a global minimum. -/
theorem global_min {σ : ℝ} (hσ : 0 < σ) (c g t : ℝ) :
    model (jet c g) 1 σ (-g / σ) ≤ model (jet c g) 1 σ t := by
  rw [model_formula, model_formula]
  have hh := sq_nonneg (t + g / σ)
  field_simp at *
  nlinarith
/-- Actual geometric checks select the first order after a specified rejected prefix.
The scalar inequalities imply both failed exit tests and the final reference decrease. -/
theorem stepOne (c g σ v a : ℝ) (n : ℕ) (hv : |v| = 1)
    (hgv : g * v = -a) (ha : (1 : ℝ) / 4 < a)
    (hchosen : σ * BacktrackingGradient.step 1 n ≤ a)
    (hprev : ∀ t < n, 2 * a ≤ σ * BacktrackingGradient.step 1 t) :
    StepOneComputation (jet c g) 1 σ (1 / 2) (fun _ : Fin 1 => 1 / 2)
      (fun _ => 1) (fun _ => BacktrackingGradient.step 1 n)
      (v * BacktrackingGradient.step 1 n)
      (fun _ t => v * BacktrackingGradient.step 1 t) (fun _ => n) (some 0) := by
  have hag : |g| = a := by
    have hh := congrArg abs hgv
    rw [abs_mul, hv, mul_one, abs_neg, abs_of_pos (by linarith : 0 < a)] at hh
    exact hh
  have hd (t : ℕ) : 0 < BacktrackingGradient.step 1 t :=
    BacktrackingGradient.step_pos zero_lt_one t
  have hdec (t : ℕ) :
      TaylorModel.jetDecrement (jet c g) 1 (v * BacktrackingGradient.step 1 t) =
        a * BacktrackingGradient.step 1 t := by
    rw [decrement]
    calc -g * (v * BacktrackingGradient.step 1 t) =
        -(g * v) * BacktrackingGradient.step 1 t := by ring
      _ = _ := by rw [hgv]; ring
  have hmod (t : ℕ) : model (jet c g) 1 σ 0 -
      model (jet c g) 1 σ (v * BacktrackingGradient.step 1 t) =
        a * BacktrackingGradient.step 1 t -
          σ / 2 * (BacktrackingGradient.step 1 t) ^ 2 := by
    have hv2 : v ^ 2 = 1 := by nlinarith [sq_abs v]
    rw [model_formula, model_formula]
    rw [show g * (v * BacktrackingGradient.step 1 t) =
      (g * v) * BacktrackingGradient.step 1 t by ring, hgv, mul_pow, hv2]
    ring
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro b t
    simp only [Real.norm_eq_abs, abs_mul, hv, one_mul, abs_of_pos (hd t)]
    exact le_rfl
  · intro b t
    have hb : modelOrder b = 1 := by have := b.isLt; unfold modelOrder; omega
    rw [hb, criticality _ _ _ (hd t).le, hdec, hag]
    nlinarith [mul_pos (by linarith : 0 < a) (hd t)]
  · intro b t ht
    have hb : modelOrder b = 1 := by have := b.isLt; unfold modelOrder; omega
    rw [HalvingAccepts, hb, hdec]
    change ¬(a * BacktrackingGradient.step 1 t ≤ _ ∨ _ ≤
      model (jet c g) 1 σ 0 - model (jet c g) 1 σ _)
    rw [hmod]
    have hmul := mul_le_mul_of_nonneg_right (hprev t ht) (hd t).le
    intro hh
    rcases hh with hh | hh <;> norm_num at hh <;> nlinarith [hd t]
  · simp only [modelOrder, Fin.val_zero, zero_add, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one]
    refine ⟨trivial, ?_, ?_, ?_, ?_⟩
    · rw [hdec]; nlinarith [hd n]
    · rw [hmod]
      have hh := mul_le_mul_of_nonneg_right hchosen (hd n).le
      nlinarith [hd n]
    · intro b hb; simp at hb
    · intro b hb; have := b.isLt; simp only [Fin.lt_def] at hb; omega
/-- The first-order scalar Taylor decrement uses the actual scalar derivative. -/
theorem scalar_decrement (f : ℝ → ℝ) (x s : ℝ) :
    TaylorModel.decrement f 1 x s = -deriv f x * s := by
  rw [TaylorModel.decrement_eq, TaylorModel.eval_eq_sum_iteratedDeriv]
  simp [Finset.sum_range_succ, mul_comm]
/-- The true first-order criticality of the quadratic model vanishes at its minimum. -/
theorem model_criticality {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ) (c g : ℝ) :
    TaylorModel.criticality (model (jet c g) 1 σ) 1 (-g / σ) δ = 0 := by
  apply (TaylorModel.criticality_eq_zero_iff _ _ _ hδ).mpr
  intro t ht
  rw [scalar_decrement, model_deriv]
  have he : g + σ * (-g / σ) = 0 := by field_simp; ring
  simp [he]
/-- The quadratic global minimum satisfies every primitive Step2 comparison and test.
Small returns use unit radii and no artificial radius reductions. -/
theorem stepTwo {σ : ℝ} (hσ : 0 < σ) (c g reference : ℝ)
    (initial : Fin 1 → ℝ) :
    StepTwoComputation (jet c g) 1 modelOrder σ (9 / 10) (1 / 2)
      (fun _ => 1 / 2) reference initial (-g / σ)
      (if 1 ≤ ‖-g / σ‖ then initial else fun _ => 1) := by
  refine ⟨global_min hσ c g reference, ?_⟩
  split_ifs with hlarge
  · exact Or.inl ⟨hlarge, rfl⟩
  · refine Or.inr ⟨lt_of_not_ge hlarge, (fun _ _ => -g / σ),
      (fun _ _ => 0), (fun _ => 0), (fun _ => 0), ?_⟩
    intro a
    have ha : modelOrder a = 1 := by have := a.isLt; unfold modelOrder; omega
    refine ⟨fun _ ht => (Nat.not_lt_zero _ ht).elim,
      ⟨fun _ ht => (Nat.not_lt_zero _ ht).elim,
        fun _ ht => (Nat.not_lt_zero _ ht).elim,
        fun _ ht => (Nat.not_lt_zero _ ht).elim⟩,
      fun _ => rfl, by simp, by simp, ?_, ?_⟩
    · rw [ha, model_criticality hσ zero_le_one]
      simp
    · rw [ha, scalar_decrement]
      norm_num
/-- Both zeroth and first actual derivative tensors of sine are globally unit Lipschitz. -/
theorem sine_lipschitz (i : ℕ) (hi : i ≤ 1) (x y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.sin x - iteratedFDeriv ℝ i Real.sin y‖ ≤ ‖x - y‖ := by
  rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
  · simpa only [iteratedDeriv_zero, Real.norm_eq_abs] using Real.abs_sin_sub_sin_le x y
  · simpa only [iteratedDeriv_one, Real.deriv_sin, Real.norm_eq_abs] using
      Real.abs_cos_sub_cos_le x y
/-- The sine objective has a global lower bound. -/
theorem sine_lower (x : ℝ) : -(1 : ℝ) ≤ Real.sin x := Real.neg_one_le_sin x
/-- The true scalar first-order criticality of sine on a closed ball. -/
theorem sine_criticality {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    TaylorModel.criticality Real.sin 1 x δ = |Real.cos x| * δ := by
  have he : ∀ t : ℝ, TaylorModel.decrement Real.sin 1 x t =
      TaylorModel.jetDecrement (jet 0 (Real.cos x)) 1 t := by
    intro t; rw [scalar_decrement, decrement, Real.deriv_sin]
  apply le_antisymm
  · obtain ⟨t, ht, heq⟩ := TaylorModel.exists_decrement_eq_criticality Real.sin 1 x hδ
    rw [←heq, he]
    exact (TaylorModel.jetDecrement_le_jetCriticality _ _ ht).trans_eq
      (criticality _ _ _ hδ)
  · obtain ⟨t, ht, heq⟩ :=
      TaylorModel.exists_jetDecrement_eq_jetCriticality (jet 0 (Real.cos x)) 1 hδ
    rw [←criticality 0 (Real.cos x) δ hδ, ←heq, ←he]
    exact TaylorModel.decrement_le_criticality _ _ _ ht
/-- The actual multilinear operator error equals the scalar derivative error. -/
theorem oracle_error (c g x : ℝ) :
    ‖jet c g 1 - iteratedFDeriv ℝ 1 Real.sin x‖ = |g - Real.cos x| := by
  change ‖iteratedFDeriv ℝ 1 (affine c g) 0 - iteratedFDeriv ℝ 1 Real.sin x‖ = _
  simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
  rw [←map_sub, LinearIsometryEquiv.norm_map]
  simp [iteratedDeriv_one, deriv_affine, Real.deriv_sin, Real.norm_eq_abs]
/-- The supplied constant tensor is the affine source value at zero. -/
theorem constant_value (c g : ℝ) : jet c g 0 (fun _ => 0) = c := by
  simp [jet, ftaylorSeries, affine]
/-- The first derivative tensor is reused when only the objective constant changes. -/
theorem first_tensor_eq (c d g : ℝ) : jet c g 1 = jet d g 1 := by
  ext
  simp [jet, ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    iteratedDeriv_one, deriv_affine]
/-- The sine objective has every finite order of continuous derivatives. -/
theorem sine_smooth (n : ℕ) : ContDiff ℝ n Real.sin := Real.contDiff_sin
end InexactRegularization.GuardedCounterexample
