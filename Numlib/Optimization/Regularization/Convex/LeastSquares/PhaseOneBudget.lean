import Numlib.Optimization.Regularization.Convex.FirstOrderCoefficient
import Numlib.Optimization.Regularization.Convex.LeastSquares.Complexity

/-!
# Initialized constrained residual counts without an additive offset

The exact dyadic coefficient is at most one half. The residual at the last
preterminal point therefore pays for both the final accepted step and the
initialized derivative site. A zero-length execution evaluates derivatives
only when its initial residual fails the global test.
-/

namespace ConvexLeastSquares
open Set TaylorModel HighOrderRegularization LeastSquares ConvexRegularization EvaluationComplexity

/-- A nonnegative first-order residual exponent with residual power above one
requires at least one dyadic root. -/
theorem dyadic_order_pos {p a : ℕ} {ℓ : ℝ} (hp : 0 < p) (hℓ : 1 < ℓ)
    (hι : 0 ≤ cascadingExponent p ℓ a 1) : 0 < a := by
  by_contra hn
  have ha : a = 0 := by omega
  subst a
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [cascadingExponent, pow_zero, sub_self, zero_div, Nat.cast_one, one_mul,
    Nat.add_sub_cancel] at hι
  have := div_pos (sub_pos.mpr hℓ) hpR
  linarith

/-- The exact legal first-order dyadic decrease coefficient is at most one half. -/
theorem lowerDecreaseCoefficient_le_half {p a : ℕ} (P : Settings p) {L β ℓ : ℝ}
    (hL : 0 < L) (hβ : 0 < β) (hβ1 : β < 1) (hℓ : 1 < ℓ) (ha : 0 < a) :
    lowerDecreaseCoefficient false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
      P.gamma3 L P.theta 1 β ≤ 1 / 2 := by
  have hK := firstDecreaseCoefficient_le_one P hL
  have hK0 := (firstDecreaseCoefficient_pos P hL).le
  have hpow : β ^ ((ℓ - 1) * (((p + 1 : ℕ) : ℝ)) / p) ≤ 1 :=
    Real.rpow_le_one hβ.le hβ1.le (by positivity)
  have hnum : firstDecreaseCoefficient P L *
      β ^ ((ℓ - 1) * (((p + 1 : ℕ) : ℝ)) / p) ≤ 1 :=
    (mul_le_mul hK hpow (Real.rpow_nonneg hβ.le _) (by norm_num)).trans_eq (by norm_num)
  have htwo : (2 : ℝ) ≤ 2 ^ a := by
    exact_mod_cast (show 2 ≤ (2 : ℕ) ^ a by
      simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ha)
  have hb := (lowerDecreaseCoefficient_bounds false p ℓ a P.sigmaInitial P.sigmaMin
    P.eta1 P.eta2 P.gamma3 L P.theta 1 β).2.1
  have he : decreaseConstant p p P.eta1 P.sigmaMin L
      (max P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))) P.theta =
      firstDecreaseCoefficient P L := by rfl
  rw [he] at hb
  apply hb.trans
  unfold cascadingConstant
  simp only [Nat.add_sub_cancel]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ a)).mpr
  nlinarith

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] {p : ℕ} {r : E → F} {ℓ L β : ℝ} {C S : Set E}
  {P : Settings p} {ε₀ ε₁ : ℝ} {D : Data E} {N : ℕ}

/-- Every actual initialized derivative schedule is paid by the exact residual
budget without an additive constant. -/
theorem Run.derivative_count_le (h : Run r ℓ C P ε₀ ε₁ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (powerObjective r ℓ) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
        iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ) (hι : 0 ≤ cascadingExponent p ℓ a 1)
    (j : ℕ) :
    (derivativeEvaluations r ε₀ P D N j : ℝ) ≤
      lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
        P.gamma3 L P.theta 1 β * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
          lowerAccuracyFactor false p a ε₀ ε₁ 1 := by
  classical
  let c := lowerDecreaseCoefficient false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
    P.gamma3 L P.theta 1 β
  let A := lowerAccuracyFactor false p a ε₀ ε₁ 1
  let B := lowerDenominator false p ℓ a ‖r (D.point 0)‖
  let q := 1 / (2 : ℝ) ^ a
  let d := c * A / B
  have hσ := P.sigmaMin_pos.trans_le P.sigmaMin_le_initial
  have hθ : 0 < P.theta := by have := P.theta_lower; have := P.tau_pos; linarith
  have hc : 0 < c := lowerDecreaseCoefficient_pos (η₂ := P.eta2) (γ₃ := P.gamma3)
    false p ℓ a hσ P.sigmaMin_pos P.eta1_pos hL hθ zero_lt_one hβ hβ1
  have hinv := inverse_lowerDecreaseCoefficient (η₂ := P.eta2) (γ₃ := P.gamma3)
    false p ℓ a hσ P.sigmaMin_pos P.eta1_pos hL hθ zero_lt_one hβ hβ1
  have hA : 0 < A := lowerAccuracyFactor_pos false p a h.accuracy_global_pos
    h.accuracy_first_pos zero_lt_one
  have hB : 0 < B := lowerDenominator_pos false p ℓ a _
  have hd : 0 < d := div_pos (mul_pos hc hA) hB
  have hq : 0 < q := by dsimp [q]; positivity
  have hhalf : c ≤ 1 / 2 := lowerDecreaseCoefficient_le_half P hL hβ hβ1
    h.residual_order (dyadic_order_pos P.order_pos h.residual_order hι)
  have hB1 : 1 ≤ B := (lowerDenominator_bounds false p ℓ a _).1
  have hAcc : A ≤ ε₀ ^ q := (lowerAccuracyFactor_bounds false p a ε₀ ε₁ 1).1
  have hdA : 2 * d ≤ A := by
    dsimp only [d]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hB).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhalf hA.le,
      mul_le_mul_of_nonneg_left hB1 hA.le]
  have hcount : (derivativeEvaluations r ε₀ P D N j : ℝ) * d ≤
      ‖r (D.point 0)‖ ^ q := by
    cases N with
    | zero =>
      by_cases hr : ε₀ < ‖r (D.point 0)‖
      · have hb := derivativeEvaluations_le r ε₀ P D 0 j
        rw [ConvexRegularization.derivativeEvaluations_eq] at hb
        simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
          Finset.card_empty, zero_add] at hb
        have hcR : (derivativeEvaluations r ε₀ P D 0 j : ℝ) ≤ 1 := by exact_mod_cast hb
        have hv := Real.rpow_le_rpow h.accuracy_global_pos.le hr.le hq.le
        exact (mul_le_mul_of_nonneg_right hcR hd.le).trans (by linarith)
      · have hzero : derivativeEvaluations r ε₀ P D 0 j = 0 := by
          simp [derivativeEvaluations, derivativeEvaluationNodes,
            ConvexRegularization.derivativeEvaluationNodes, successfulIterations, not_lt.mp hr]
        rw [hzero, Nat.cast_zero, zero_mul]
        exact Real.rpow_nonneg (norm_nonneg _) _
    | succ k =>
      have hp := card_successful_mul_le_gap (S := {i | P.eta1 ≤ D.ratio i})
        (f := fun i => ‖r (D.point i)‖ ^ q) (flow := ‖r (D.point k)‖ ^ q)
        (d := d) (k := k) le_rfl
        (fun i hi hs => h.successful_root_decrease hclosed hS hCS hC hf hL hlip hβ hβ1
          a hι (by omega) hs)
        (fun i hi hu => by
          change ¬P.eta1 ≤ D.ratio i at hu
          rw [h.trace.point_update i (by omega), ite_eq_right hu])
      have hv := Real.rpow_le_rpow h.accuracy_global_pos.le
        (h.residual_gt (show k < k + 1 by omega)).le hq.le
      have hb := derivativeEvaluations_le r ε₀ P D (k + 1) j
      rw [ConvexRegularization.derivativeEvaluations_eq] at hb
      have hs := card_successful_succ_le {i | P.eta1 ≤ D.ratio i} k
      have hn : (derivativeEvaluations r ε₀ P D (k + 1) j : ℝ) ≤
          (successfulIterations {i | P.eta1 ≤ D.ratio i} k).card + 2 := by
        exact_mod_cast (hb.trans (by omega))
      have hh := mul_le_mul_of_nonneg_right hn hd.le
      nlinarith
  have hdiv := (le_div_iff₀ hd).mpr hcount
  have hR : 0 ≤ ‖r (D.point 0)‖ := norm_nonneg _
  by_cases hR0 : ‖r (D.point 0)‖ = 0
  · rw [hR0, Real.zero_rpow hq.ne', zero_div] at hdiv
    have hKS : 0 < lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin
        P.eta1 P.eta2 P.gamma3 L P.theta 1 β := by
      rw [←hinv]
      exact one_div_pos.mpr hc
    exact hdiv.trans (div_nonneg (mul_nonneg hKS.le
      (lowerBudget_nonneg hR false p ℓ a)) hA.le)
  · have heq : ‖r (D.point 0)‖ ^ q / d =
        lowerSuccessfulIterationConstant false p ℓ a P.sigmaInitial P.sigmaMin P.eta1 P.eta2
          P.gamma3 L P.theta 1 β * lowerBudget false p ℓ a ‖r (D.point 0)‖ /
            lowerAccuracyFactor false p a ε₀ ε₁ 1 := by
      rw [←hinv, ←lowerBudget_eq (lt_of_le_of_ne hR (Ne.symm hR0)) false p ℓ a]
      dsimp [d, c, A, B, q]
      field_simp
    rwa [heq] at hdiv

end ConvexLeastSquares
