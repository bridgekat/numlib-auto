import Numlib.Optimization.Regularization.Inexact.PassingCubic.Objective
import Numlib.Optimization.Regularization.Inexact.StepTwo

/-!
# Actual inaccurate cubic checks before a parameter increase

The initial negative computed gradient supplies a genuine large improving
candidate. After a large regularization increase, coercivity and actual model
comparison force a short return. Every ordered check and inner model test is
constructed from the actual polynomial derivative jet.
-/

namespace InexactRegularization.PassingCubic
open Polynomial InexactTrustRegion

/-- An actual cubic polynomial supplying the initial inaccurate negative first derivative. -/
noncomputable def ghostPolynomial (H B : ℝ) : ℝ[X] := C (-H) * X + polynomial B

/-- The genuine derivative jet of the inaccurate cubic polynomial at zero. -/
noncomputable def ghostJet (H B : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  ftaylorSeries ℝ (ghostPolynomial H B).eval 0

/-- The actual initial computed cubic jets have the prescribed negative linear
coefficient. -/
theorem ghost_jets (H B : ℝ) {j : ℕ} (hj : j ≤ 3) :
    iteratedDeriv j (ghostPolynomial H B).eval 0 =
      if j = 0 then 0 else if j = 1 then -H else if j = 2 then B else -1 := by
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;> norm_num [ghostPolynomial, polynomial, Function.iterate_succ_apply',
    derivative_add, derivative_sub, derivative_C_mul, derivative_pow, derivative_X]

/-- Every computed Taylor degree through three has the exact initial polynomial value. -/
theorem ghost_value (H B : ℝ) {j : ℕ} (hj : j ≤ 3) (u : ℝ) :
    TaylorModel.ofJet (ghostJet H B) j u =
      (if j = 0 then 0 else -H * u) +
      (if j ≤ 1 then 0 else B / 2 * u ^ 2 - if j = 2 then 0 else u ^ 3 / 6) := by
  change TaylorModel.eval (ghostPolynomial H B).eval j 0 u = _
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  have hh := fun i (hi : i ≤ 3) => ghost_jets H B hi
  interval_cases j <;>
    simp [Finset.sum_range_succ, hh, show (0 : ℕ) ≤ 3 by omega,
      show (1 : ℕ) ≤ 3 by omega, show (2 : ℕ) ≤ 3 by omega] <;> ring

/-- The first-order computed decrement is the positive linear coefficient times the
direction. -/
theorem ghost_first_decrement (H B u : ℝ) :
    TaylorModel.jetDecrement (ghostJet H B) 1 u = H * u := by
  rw [TaylorModel.jetDecrement, ghost_value H B (by omega), ghost_value H B (by omega)]
  norm_num

/-- The actual first-order computed supremum has its exact scalar closed-ball value. -/
theorem ghost_first_criticality {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 ≤ δ) (B : ℝ) :
    TaylorModel.jetCriticality (ghostJet H B) 1 δ = H * δ := by
  apply le_antisymm
  · apply (TaylorModel.jetCriticality_le_iff _ _ hδ).mpr
    intro u hu
    rw [ghost_first_decrement]
    exact mul_le_mul_of_nonneg_left ((le_abs_self u).trans hu) hH
  · have hh := TaylorModel.jetDecrement_le_jetCriticality (ghostJet H B) 1
      (s := δ) (δ := δ) (by simpa only [Real.norm_eq_abs, abs_of_nonneg hδ] using le_refl δ)
    simpa only [ghost_first_decrement] using hh

/-- The actual norm-regularized initial jet has the displayed quartic value. -/
theorem ghost_model_formula (H B σ u : ℝ) : model (ghostJet H B) 3 σ u =
    -H * u + B / 2 * u ^ 2 - u ^ 3 / 6 + σ / 24 * u ^ 4 := by
  have hpow : ‖u‖ ^ 4 = u ^ 4 := by
    simp only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs]
  unfold model ModelDecrease.penalized
  rw [ghost_value H B le_rfl]
  norm_num only [Nat.reduceLeDiff, ite_false, Nat.reduceEqDiff, zero_add,
    Nat.factorial, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat]
  rw [hpow]
  ring

/-- All actual higher computed tensor norms are bounded independently of the inaccurate
first derivative. -/
theorem ghost_tensor_norm_bound {H B : ℝ} (hB : 0 ≤ B)
    {i : ℕ} (hi : 2 ≤ i) (hi3 : i ≤ 3) :
    ‖ghostJet H B i‖ ≤ max B 1 := by
  change ‖iteratedFDeriv ℝ i (ghostPolynomial H B).eval 0‖ ≤ _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ghost_jets H B hi3]
  interval_cases i <;> norm_num [Real.norm_eq_abs, abs_of_nonneg hB]

/-- Every completed ordered check of the initial inaccurate jet selects the first order. -/
theorem selected_zero_of_ghost {H B σ : ℝ} (hH : 1 ≤ H)
    {initial reduced : Fin 3 → ℝ} {reference : ℝ} {direction : Fin 3 → ℕ → ℝ}
    {count : Fin 3 → ℕ} {selected : Option (Fin 3)}
    (hinit : ∀ a, 0 < initial a ∧ initial a ≤ 1)
    (h : StepOneComputation (ghostJet H B) 3 σ (1 / 2) (fun _ => 1 / 2)
      initial reduced reference direction count selected) : selected = some 0 := by
  have hδ := (h.radius_bounds hinit 0).1
  have ha := h.approximation 0 (count 0)
  rw [← h.radius_eq 0] at ha
  have ho : modelOrder (0 : Fin 3) = 1 := rfl
  rw [ho, ghost_first_criticality (by linarith) hδ.le] at ha
  have hfail : ¬TaylorModel.jetDecrement (ghostJet H B) 1 (direction 0 (count 0)) ≤
      (1 / 2 : ℝ) / 2 * (1 / 2) * reduced 0 ^ 1 / 1 := by
    norm_num at *
    nlinarith
  cases hs : selected with
  | none =>
    rw [hs] at h
    have hp := h.outcome 0
    rw [ho] at hp
    exact (hfail (by simpa only [Nat.factorial_one, Nat.cast_one] using hp)).elim
  | some a =>
    by_cases ha0 : a = 0
    · rw [ha0]
    · have haz : (0 : Fin 3) < a := Fin.pos_iff_ne_zero.mpr ha0
      rw [hs] at h
      have hp := h.outcome.2.2.2.1 0 haz
      rw [ho] at hp
      exact (hfail (by simpa only [Nat.factorial_one, Nat.cast_one] using hp)).elim
end InexactRegularization.PassingCubic
namespace InexactRegularization.PassingCubic
open InexactTrustRegion

/-- The initial inaccurate jet admits a genuine selected-first check with no radius
reductions and a unit-bounded reference. -/
theorem ghost_initial_check {H B : ℝ} (hH : 2 ≤ H) (hB : 0 ≤ B) (hB1 : B ≤ 1) :
    ∃ (reference : ℝ) (direction : Fin 3 → ℕ → ℝ) (count : Fin 3 → ℕ),
      StepOneComputation (ghostJet H B) 3 H (1 / 2) (fun _ => 1 / 2)
        (fun _ => 1) (fun _ => 1) reference direction count (some 0) ∧
      ‖reference‖ ≤ 1 := by
  obtain ⟨reduced, reference, direction, count, selected, hone⟩ :=
    exists_stepOneComputation (σ := H) (ζ := (1 / 2 : ℝ)) (le_refl 3) (ghostJet H B)
      (lt_of_lt_of_le zero_lt_one (le_max_right B 1)) (by linarith)
      (by norm_num) (by norm_num) (fun i hi hi3 => ghost_tensor_norm_bound hB hi hi3)
      (fun _ => 1 / 2) (fun _ => 1) (fun _ => by norm_num) (fun _ => ⟨by norm_num, le_rfl⟩)
  have hsel := selected_zero_of_ghost (by linarith : 1 ≤ H)
    (fun _ => ⟨zero_lt_one, le_rfl⟩) hone
  rw [hsel] at hone
  have hc0 : count 0 = 0 := by
    by_contra hn
    have hd := hone.feasible 0 0
    have ha := hone.approximation 0 0
    have ho : modelOrder (0 : Fin 3) = 1 := rfl
    norm_num [ho, ghost_first_criticality (show 0 ≤ H by linarith) zero_le_one] at ha
    norm_num [Real.norm_eq_abs] at hd
    have hu : (1 / 2 : ℝ) ≤ direction 0 0 := by
      rw [ghost_first_decrement] at ha
      nlinarith
    have hu1 : direction 0 0 ≤ 1 := (le_abs_self _).trans hd
    have hu0 : 0 ≤ direction 0 0 := by linarith
    have hu2 := pow_le_one₀ hu0 hu1 (n := 2)
    have hu4 := pow_le_one₀ hu0 hu1 (n := 4)
    have hprod := mul_le_mul_of_nonneg_left hu (show 0 ≤ H by linarith)
    have hBprod := mul_le_mul_of_nonneg_left hu2 hB
    have hHprod := mul_le_mul_of_nonneg_left hu4 (show 0 ≤ H by linarith)
    have hdec : (1 / 16 : ℝ) ≤ model (ghostJet H B) 3 H 0 -
        model (ghostJet H B) 3 H (direction 0 0) := by
      rw [ghost_model_formula, ghost_model_formula]
      nlinarith [pow_nonneg hu0 3]
    have hacc : HalvingAccepts (ghostJet H B) 1 3 H (1 / 2) (1 / 2) 1 (direction 0) 0 :=
      Or.inr (by
        convert hdec using 1 <;>
          norm_num [BacktrackingGradient.step, model, ModelDecrease.penalized])
    exact hone.rejected 0 0 (Nat.pos_of_ne_zero hn) hacc
  have hcount : ∀ a, count a = 0 := by
    intro a
    by_cases ha : a = 0
    · simpa only [ha] using hc0
    · exact hone.outcome.2.2.2.2 a (Fin.pos_iff_ne_zero.mpr ha)
  have hred : reduced = fun _ => 1 := by
    funext a
    rw [hone.radius_eq a, hcount a]
    simp
  rw [hred] at hone
  refine ⟨reference, direction, count, hone, ?_⟩
  rw [hone.outcome.1, hc0]
  simpa only [BacktrackingGradient.step, pow_zero, div_one] using hone.feasible 0 0
end InexactRegularization.PassingCubic
namespace InexactRegularization.PassingCubic
open InexactTrustRegion

/-- Every unit-bounded reference has a common lower bound for the initial computed
regularized model. -/
theorem ghost_reference_bound {H B : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B)
    {u : ℝ} (hu : ‖u‖ ≤ 1) :
    -H - 1 / 6 ≤ model (ghostJet H B) 3 H u := by
  rw [ghost_model_formula]
  have hule : u ≤ 1 := (le_abs_self _).trans hu
  have hu3 : u ^ 3 ≤ 1 := by
    calc _ ≤ |u| ^ 3 := (le_abs_self (u ^ 3)).trans_eq (_root_.abs_pow u 3)
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
  have hlin := mul_le_mul_of_nonneg_left hule hH
  nlinarith [mul_nonneg hB (sq_nonneg u), mul_nonneg hH (by positivity : 0 ≤ u ^ 4)]

/-- The initial large candidate satisfies the actual Step2 comparison and large-step
return rules. -/
theorem ghost_first_step_two {H B : ℝ} (hH : 4 ≤ H) (hB : 0 ≤ B) (hB1 : B ≤ 1)
    {reference : ℝ} (href : ‖reference‖ ≤ 1) (initial : Fin 3 → ℝ) :
    StepTwoComputation (ghostJet H B) 3 modelOrder H (9 / 10) (1 / 2) (fun _ => 1 / 2)
      reference initial 2 initial := by
  refine ⟨?_, Or.inl ⟨by norm_num, rfl⟩⟩
  have hr := ghost_reference_bound (show 0 ≤ H by linarith) hB href
  rw [ghost_model_formula]
  norm_num
  linarith

/-- After a sufficiently large parameter increase, every candidate of norm at least one
has nonnegative actual computed model value. -/
theorem ghost_model_nonnegative_of_large {H B σ u : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hσ : 24 * H + 4 ≤ σ) (hu : 1 ≤ ‖u‖) :
    0 ≤ model (ghostJet H B) 3 σ u := by
  rw [ghost_model_formula]
  have hσpos : 0 ≤ σ := by linarith
  by_cases hu0 : 0 ≤ u
  · have hu1 : 1 ≤ u := by simpa only [Real.norm_eq_abs, abs_of_nonneg hu0] using hu
    have hu4 : 0 ≤ u ^ 4 := by positivity
    have hpow1 : u ≤ u ^ 4 := by
      simpa only [pow_one] using pow_le_pow_right₀ hu1 (by norm_num : 1 ≤ 4)
    have hpow3 : u ^ 3 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num : 3 ≤ 4)
    have hlin := mul_le_mul_of_nonneg_left hpow1 hH
    have hscale := mul_le_mul_of_nonneg_right hσ hu4
    nlinarith [mul_nonneg hB (sq_nonneg u)]
  · have hneg : u ≤ 0 := (not_le.mp hu0).le
    have hcub : u ^ 3 ≤ 0 := by nlinarith [sq_nonneg u]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hH hneg,
      mul_nonneg hB (sq_nonneg u), mul_nonneg hσpos (by positivity : 0 ≤ u ^ 4)]

/-- After the large parameter increase, genuine computed Step1 and Step2 operations exist
and necessarily return a short candidate. The conclusion follows from the actual
reference improvement and model comparison. -/
theorem ghost_short_components {H B σ : ℝ} (hH : 2 ≤ H) (hB : 0 ≤ B)
    (hσ : 24 * H + 4 ≤ σ) :
    ∃ (reduced : Fin 3 → ℝ) (reference : ℝ) (direction : Fin 3 → ℕ → ℝ)
      (count : Fin 3 → ℕ) (s : ℝ) (solved : Fin 3 → ℝ),
      StepOneComputation (ghostJet H B) 3 σ (1 / 2) (fun _ => 1 / 2)
        (fun _ => 1) reduced reference direction count (some 0) ∧
      StepTwoComputation (ghostJet H B) 3 modelOrder σ (9 / 10) (1 / 2) (fun _ => 1 / 2)
        reference reduced s solved ∧ ‖s‖ < 1 := by
  have hσpos : 0 < σ := by linarith
  obtain ⟨reduced, reference, direction, count, selected, hone⟩ :=
    exists_stepOneComputation (σ := σ) (ζ := (1 / 2 : ℝ)) (le_refl 3) (ghostJet H B)
      (lt_of_lt_of_le zero_lt_one (le_max_right B 1)) hσpos.le
      (by norm_num) (by norm_num) (fun i hi hi3 => ghost_tensor_norm_bound hB hi hi3)
      (fun _ => 1 / 2) (fun _ => 1) (fun _ => by norm_num) (fun _ => ⟨by norm_num, le_rfl⟩)
  have hsel := selected_zero_of_ghost (by linarith : 1 ≤ H)
    (fun _ => ⟨zero_lt_one, le_rfl⟩) hone
  rw [hsel] at hone
  have hreference := hone.reference_improvement (by norm_num) (by norm_num)
    (fun _ => ⟨zero_lt_one, le_rfl⟩)
  obtain ⟨s, solved, htwo⟩ :=
    exists_stepTwoComputation (θ := (9 / 10 : ℝ)) (ζ := (1 / 2 : ℝ))
      (ghostJet H B) 3 modelOrder
    (fun a => ⟨by unfold modelOrder; omega, by have := a.isLt; exact this⟩)
    hσpos (le_trans (by norm_num) (le_max_right B 1))
    (fun i hi hi3 => ghost_tensor_norm_bound hB hi hi3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 1 / 2) (fun _ => ⟨by norm_num, by norm_num⟩) reference reduced
  refine ⟨reduced, reference, direction, count, s, solved, hone, htwo, ?_⟩
  apply lt_of_not_ge
  intro hs
  have hn := ghost_model_nonnegative_of_large (by linarith : 0 ≤ H) hB hσ hs
  have hm := htwo.comparison.trans_lt hreference
  have hz : model (ghostJet H B) 3 σ 0 = 0 := by rw [ghost_model_formula]; ring
  rw [hz] at hm
  linarith
end InexactRegularization.PassingCubic
