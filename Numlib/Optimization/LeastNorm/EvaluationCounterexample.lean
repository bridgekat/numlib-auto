import Numlib.Optimization.LeastNorm.Budget
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!
# A smooth two-call obstruction to the printed least-norm evaluation constant

The actual affine residual and its genuine Taylor criticality satisfy every
inner and outer test. Both per-call costs obey the assumed bounds with constants
one, but their sum exceeds the printed maximum of geometric sums. The merit
also satisfies all source smoothness and initial-level derivative bounds.
-/

namespace LeastNorm.EvaluationCounterexample
open TaylorModel InexactTrustRegion
/-- The fixed positive slope of the affine residual. -/
noncomputable def slope : ℝ := 667 / 2000
/-- The actual affine residual, with a globally quadratic least-squares merit. -/
noncomputable def residual (x : ℝ) : ℝ := 1 - slope * x
/-- The two actual outer dual tolerances. -/
noncomputable def accuracy (a : Fin 2) : ℝ := if a.val = 0 then 1 / 3 else 99 / 100
/-- The two allowed per-call complexity exponents, both greater than one. -/
noncomputable def exponent (a : Fin 2) : ℝ := if a.val = 0 then 8 else 50
/-- The actual initialized point, first return and exact final root. -/
noncomputable def point (k : ℕ) : ℝ := if k = 0 then 0 else if k = 1 then 202 / 667 else 2000 / 667
/-- The actual scalar derivative of the least-squares merit. -/
noncomputable def merit_deriv (x : ℝ) : ℝ := -slope * residual x

/-- The actual derivative of the squared affine residual. -/
theorem merit_hasDerivAt (x : ℝ) : HasDerivAt (merit residual) (merit_deriv x) x := by
  have hr : HasDerivAt residual (-slope) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_id x).const_mul slope) using 1 <;>
      try simp only [mul_one, zero_sub]
    funext z
    rfl
  have he : (merit residual : ℝ → ℝ) = fun z => (residual z) ^ 2 / 2 := by
    funext z
    simp [merit, Real.norm_eq_abs, sq_abs]
  rw [he]
  convert (hr.pow 2).div_const 2 using 1
  dsimp [merit_deriv]
  ring

/-- The actual gradient agrees with the scalar merit derivative. -/
theorem merit_gradient (x : ℝ) : gradient (merit residual) x = merit_deriv x := by
  rw [gradient_eq_deriv]
  exact (merit_hasDerivAt x).deriv

/-- The genuine first-order Taylor decrement of the merit. -/
theorem decrement_one (x d : ℝ) :
    TaylorModel.decrement (merit residual) 1 x d = slope * residual x * d := by
  rw [TaylorModel.decrement_one, merit_gradient]
  simp [merit_deriv]
  ring


/-- The actual second derivative tensor on arbitrary scalar input vectors. -/
theorem merit_second_apply (x : ℝ) (w : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 (merit residual) x w = slope ^ 2 * w 0 * w 1 := by
  let I : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
  have he : fderiv ℝ (merit residual) = fun z => merit_deriv z • I := by
    ext z
    rw [fderiv_eq_deriv_mul, (merit_hasDerivAt z).deriv]
    simp [I]
  have hr : HasDerivAt residual (-slope) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_id x).const_mul slope) using 1 <;>
      try simp only [mul_one, zero_sub]
    funext z
    rfl
  have hd : HasDerivAt merit_deriv (slope ^ 2) x := by
    convert hr.const_mul (-slope) using 1 <;> try rfl
    ring
  have hfd := (hd.smul_const I).hasFDerivAt.fderiv
  rw [iteratedFDeriv_two_apply, he, hfd]
  simp [I, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- The diagonal actual second derivative is nonnegative. -/
theorem merit_second (x d : ℝ) :
    iteratedFDeriv ℝ 2 (merit residual) x (fun _ => d) = slope ^ 2 * d ^ 2 := by
  rw [merit_second_apply]
  ring

/-- The genuine second-order Taylor decrement of the merit. -/
theorem decrement_two (x d : ℝ) :
    TaylorModel.decrement (merit residual) 2 x d =
      slope * residual x * d - slope ^ 2 * d ^ 2 / 2 := by
  have hh := TaylorModel.decrement_two_smul (merit residual) x d 1
  simpa only [one_smul, one_pow, one_mul, merit_second, merit_gradient, merit_deriv,
    real_inner_self_eq_norm_sq, Real.inner_apply, mul_neg, neg_mul, neg_neg] using hh


/-- The exact actual first-order constrained criticality at unit radius. -/
theorem criticality_one_eq (x : ℝ) :
    constrainedCriticality (merit residual) 1 Set.univ x 1 = |slope * residual x| := by
  rw [constrainedCriticality_univ, TaylorModel.criticality_one _ _ zero_lt_one, merit_gradient]
  simp [merit_deriv, Real.norm_eq_abs]

/-- Positive quadratic curvature bounds actual second-order criticality. -/
theorem criticality_two_le (x : ℝ) (hr : 0 ≤ residual x) :
    constrainedCriticality (merit residual) 2 Set.univ x 1 ≤ slope * residual x := by
  rw [constrainedCriticality_univ]
  obtain ⟨d, hd, he⟩ := TaylorModel.exists_decrement_eq_criticality (merit residual) 2 x
    (by norm_num : (0 : ℝ) ≤ 1)
  have hd1 : d ≤ 1 := (le_abs_self d).trans (by simpa [Real.norm_eq_abs] using hd)
  rw [← he, decrement_two]
  have ha : 0 ≤ slope := by norm_num [slope]
  have hh := mul_le_mul_of_nonneg_left hd1 (mul_nonneg ha hr)
  nlinarith [sq_nonneg (slope * d)]

/-- The actual residual values at the three computed points. -/
theorem residual_point : residual (point 0) = 1 ∧ residual (point 1) = 899 / 1000 ∧
    residual (point 2) = 0 := by norm_num [residual, point, slope]

/-- Primitive two-call inner execution with actual returned points and counters. -/
def innerCall (xs : ℝ) (ε : Fin 2 → ℝ) (x : ℝ) (δ : Fin 2 → ℝ) (nf nd : ℕ) : Prop :=
  δ = (fun _ => 1) ∧ ((xs = point 0 ∧ x = point 1 ∧
    ε = (fun a => (9 / 10) * ‖residual (point 0)‖ * accuracy a) ∧ nf = 7620 ∧ nd = 7620) ∨
    (xs = point 1 ∧ x = point 2 ∧
    ε = (fun a => (9 / 10) * ‖residual (point 1)‖ * accuracy a) ∧ nf = 26583 ∧ nd = 26583))

/-- Both actual inner returns satisfy the true all-order criticality interface. -/
theorem inner_sound : InnerSound residual Set.univ innerCall := by
  intro xs ε x δ nf nd hc
  obtain ⟨hδ, hcases⟩ := hc
  subst δ
  refine ⟨Set.mem_univ _, fun _ => ⟨zero_lt_one, le_rfl⟩, ?_⟩
  rcases hcases with ⟨hxs, hx, hε, hnf, hnd⟩ | ⟨hxs, hx, hε, hnf, hnd⟩
  · subst x ε
    intro a
    fin_cases a
    · change constrainedCriticality (merit residual) 1 Set.univ (point 1) 1 ≤ _
      rw [criticality_one_eq]
      norm_num [slope, residual, point, accuracy, modelOrder]
    · change constrainedCriticality (merit residual) 2 Set.univ (point 1) 1 ≤ _
      have hh := criticality_two_le (point 1) (by norm_num [residual, point, slope])
      norm_num [slope, residual, point, accuracy, modelOrder] at hh ⊢
      linarith
  · subst x ε
    intro a
    fin_cases a
    · change constrainedCriticality (merit residual) 1 Set.univ (point 2) 1 ≤ _
      rw [criticality_one_eq]
      norm_num [slope, residual, point, accuracy, modelOrder]
    · change constrainedCriticality (merit residual) 2 Set.univ (point 2) 1 ≤ _
      have hh := criticality_two_le (point 2) (by norm_num [residual, point, slope])
      norm_num [slope, residual, point, accuracy, modelOrder] at hh ⊢
      linarith

/-- The actual function and derivative counts of the two inner calls. -/
noncomputable def count (k : ℕ) : ℕ := if k = 0 then 7620 else 26583

/-- The outer stopping test first passes after exactly two inner calls. -/
theorem first_target_two :
    TargetAt residual Set.univ (898 / 1000) accuracy point (fun _ _ => 1) 2 ∧
    ∀ k < 2, ¬TargetAt residual Set.univ (898 / 1000) accuracy point (fun _ _ => 1) k := by
  constructor
  · left
    norm_num [residual, point, slope]
  · intro k hk
    interval_cases k
    · norm_num [TargetAt, residual, point, slope]
    · simp only [TargetAt, one_ne_zero, ite_false, not_or]
      constructor
      · norm_num [residual, point, slope]
      · intro hh
        have hb := hh (0 : Fin 2)
        rw [show modelOrder (0 : Fin 2) = 1 by rfl, criticality_one_eq] at hb
        norm_num [slope, residual, point, accuracy, modelOrder] at hb

/-- Every primitive outer rule holds for the actual two-call execution. -/
theorem two_iterations :
    Run residual Set.univ innerCall (898 / 1000) (9 / 10) accuracy point
      (fun _ _ => 1) count count 2 := by
  constructor
  · norm_num
  · norm_num
  · intro a; fin_cases a <;> norm_num [accuracy]
  · norm_num
  · norm_num
  · norm_num [residual, point, slope]
  · trivial
  · exact first_target_two.2
  · intro k hk
    interval_cases k
    · exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩⟩


/-- Both actual calls satisfy the printed least-squares per-call bounds with constants one. -/
theorem inner_counts : InnerCounts residual innerCall (by norm_num : 0 < 2)
    exponent 1 1 := by
  intro xs ε x δ nf nd hc
  obtain ⟨_, hcases⟩ := hc
  rcases hcases with ⟨hxs, hx, hε, hnf, hnd⟩ | ⟨hxs, hx, hε, hnf, hnd⟩
  · subst xs ε nf nd
    have hm := le_maximumWeight (by norm_num : 0 < 2)
      (fun a => ((9 / 10) * ‖residual (point 0)‖ * accuracy a) ^ (-exponent a)) (0 : Fin 2)
    have hp : (7620 : ℝ) ≤ merit residual (point 0) *
        ((9 / 10) * ‖residual (point 0)‖ * accuracy (0 : Fin 2)) ^ (-exponent 0) := by
      norm_num [merit, residual, point, slope, accuracy, exponent, Real.rpow_neg,
        ← Real.rpow_natCast]
    have hb := hp.trans (mul_le_mul_of_nonneg_left hm (by unfold merit; positivity))
    exact ⟨by simpa using hb, by simpa using hb⟩
  · subst xs ε nf nd
    have hm := le_maximumWeight (by norm_num : 0 < 2)
      (fun a => ((9 / 10) * ‖residual (point 1)‖ * accuracy a) ^ (-exponent a)) (1 : Fin 2)
    have hp : (26583 : ℝ) ≤ merit residual (point 1) *
        ((9 / 10) * ‖residual (point 1)‖ * accuracy (1 : Fin 2)) ^ (-exponent 1) := by
      norm_num [merit, residual, point, slope, accuracy, exponent, Real.rpow_neg,
        ← Real.rpow_natCast]
    have hb := hp.trans (mul_le_mul_of_nonneg_left hm (by unfold merit; positivity))
    exact ⟨by simpa using hb, by simpa using hb⟩

/-- The literal order-dependent factor in the printed total evaluation bound. -/
noncomputable def printedWeight (a : Fin 2) : ℝ :=
  (9 / 10 : ℝ) ^ (1 - 2 * exponent a) /
    ((9 / 10 : ℝ) ^ (1 - exponent a) - 1) *
      (898 / 1000 : ℝ) ^ (1 - exponent a) * accuracy a ^ (-exponent a)

/-- The printed total bound is strictly smaller than the actual two-call total. -/
theorem printed_evaluation_bound_false :
    ¬(∑ k ∈ Finset.range 2, (count k : ℝ)) ≤
      1 / 2 * ‖residual (point 0)‖ * maximumWeight (by norm_num : 0 < 2) printedWeight := by
  have hb : maximumWeight (by norm_num : 0 < 2) printedWeight < (34203 : ℝ) * 2 := by
    obtain ⟨a, ha⟩ := exists_maximumWeight (by norm_num : 0 < 2) printedWeight
    rw [ha]
    fin_cases a <;>
      norm_num [printedWeight, exponent, accuracy, Real.rpow_neg, ← Real.rpow_natCast]
  norm_num [Finset.sum_range_succ, count, residual, point, slope] at hb ⊢
  linarith


/-- The genuine merit is smooth of every finite order. -/
theorem merit_contDiff (n : ℕ) : ContDiff ℝ n (merit residual) := by
  have he : (merit residual : ℝ → ℝ) = fun z => (residual z) ^ 2 / 2 := by
    funext z
    simp [merit, Real.norm_eq_abs, sq_abs]
  rw [he]
  unfold residual
  fun_prop

/-- The actual scalar merit derivative is globally Lipschitz with constant one. -/
theorem derivative_lipschitz (x y : ℝ) :
    |merit_deriv x - merit_deriv y| ≤ |x - y| := by
  have he : merit_deriv x - merit_deriv y = slope ^ 2 * (x - y) := by
    unfold merit_deriv residual
    ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (by norm_num [slope])

/-- The first actual derivative tensor is globally Lipschitz with constant one. -/
theorem first_jet_lipschitz (x y : ℝ) :
    ‖iteratedFDeriv ℝ 1 (merit residual) x - iteratedFDeriv ℝ 1 (merit residual) y‖ ≤
      ‖x - y‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro w
  simp only [sub_apply, iteratedFDeriv_one_apply,
    fderiv_eq_deriv_mul, (merit_hasDerivAt x).deriv, (merit_hasDerivAt y).deriv]
  rw [← sub_mul, norm_mul]
  simpa only [Real.norm_eq_abs, Fin.prod_univ_one] using
    mul_le_mul_of_nonneg_right (derivative_lipschitz x y) (abs_nonneg (w 0))

/-- The actual second derivative tensor is constant, so its Lipschitz constant is zero. -/
theorem second_jet_constant (x y : ℝ) :
    iteratedFDeriv ℝ 2 (merit residual) x = iteratedFDeriv ℝ 2 (merit residual) y := by
  apply ContinuousMultilinearMap.ext
  intro w
  rw [merit_second_apply, merit_second_apply]

/-- Both actual derivative tensors are bounded by one on the initial merit level set. -/
theorem level_set_jet_bound {x : ℝ} (hx : merit residual x ≤ merit residual (point 0)) :
    ‖iteratedFDeriv ℝ 1 (merit residual) x‖ ≤ 1 ∧
      ‖iteratedFDeriv ℝ 2 (merit residual) x‖ ≤ 1 := by
  have hsq : residual x ^ 2 ≤ 1 := by
    norm_num [merit, Real.norm_eq_abs, sq_abs, residual_point.1] at hx
    linarith
  have hr : |residual x| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (residual x - 1), sq_nonneg (residual x + 1)]
  constructor
  · have he : ‖iteratedFDeriv ℝ 1 (merit residual) x‖ = |slope * residual x| := by
      rw [norm_iteratedFDeriv_one, ← norm_deriv_eq_norm_fderiv,
        (merit_hasDerivAt x).deriv]
      simp [merit_deriv, Real.norm_eq_abs]
    rw [he, abs_mul]
    have ha : |slope| ≤ 1 := by norm_num [slope]
    nlinarith [abs_nonneg slope, abs_nonneg (residual x)]
  · apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
    intro w
    rw [merit_second_apply]
    simp only [norm_mul, Real.norm_eq_abs, abs_pow, Fin.prod_univ_two, one_mul]
    have ha : |slope| ^ 2 ≤ 1 := by norm_num [slope]
    nlinarith [mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 1))]


/-- All source smoothness, global tensor Lipschitz and initial-level tensor
bounds hold with constants one for the actual quadratic merit. -/
theorem merit_regularity : ContDiff ℝ 2 (merit residual) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x y : ℝ,
      ‖iteratedFDeriv ℝ j (merit residual) x - iteratedFDeriv ℝ j (merit residual) y‖ ≤
        1 * ‖x - y‖) ∧
    (∀ x : ℝ, merit residual x ≤ merit residual (point 0) →
      ∀ j, 1 ≤ j → j ≤ 2 → ‖iteratedFDeriv ℝ j (merit residual) x‖ ≤ 1) := by
  refine ⟨merit_contDiff 2, ?_, ?_⟩
  · intro j hj hj2 x y
    interval_cases j
    · simpa only [one_mul] using first_jet_lipschitz x y
    · rw [second_jet_constant x y, sub_self, norm_zero, one_mul]
      exact norm_nonneg _
  · intro x hx j hj hj2
    interval_cases j
    · exact (level_set_jet_bound hx).1
    · exact (level_set_jet_bound hx).2
end LeastNorm.EvaluationCounterexample
