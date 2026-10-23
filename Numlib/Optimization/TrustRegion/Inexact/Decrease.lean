import Numlib.Optimization.TrustRegion.Inexact.Budget

/-!
# Computed decrease and trial-length floors for inexact trust regions

The selected failed test and actual polynomial comparison imply model decrease.
Actual tensor-norm bounds then force a positive trial length, which makes a
uniformly small requested accuracy pass every Step 2 request check.
-/

namespace InexactTrustRegion
open TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalized positive powers decrease with their order on the unit interval. -/
theorem pow_div_factorial_antitone {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    {j q : ℕ} (hjq : j ≤ q) : b ^ q / q.factorial ≤ b ^ j / j.factorial := by
  have hfjq : (j.factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le hjq
  calc _ ≤ b ^ j / q.factorial := div_le_div_of_nonneg_right
        (pow_le_pow_of_le_one hb hb1 hjq) (Nat.cast_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hb _) (by positivity) hfjq

/-- The source accuracy threshold lies in the unit interval when its fixed
coefficients and requested minimum accuracy do. -/
theorem accuracyThreshold_le_one {q : ℕ} {ζ κ M μ : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hM : 1 ≤ M) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) : accuracyThreshold q ζ κ M μ ≤ 1 := by
  have hfac : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hz := pow_le_one₀ hζ hζ1 (n := q + 1)
  have hk := pow_le_one₀ hκ hκ1 (n := q)
  have he := pow_le_one₀ hμ hμ1 (n := q + 1)
  have hnum : ζ ^ (q + 1) * κ ^ q * μ ^ (q + 1) ≤ 1 :=
    calc _ ≤ 1 * 1 * 1 := mul_le_mul
          (mul_le_mul hz hk (pow_nonneg hκ _) (by norm_num)) he
          (pow_nonneg hμ _) (by norm_num)
      _ = 1 := by ring
  unfold accuracyThreshold
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 4 * (q.factorial : ℝ) * M by positivity)).2
  nlinarith [mul_le_mul hfac hM (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg q.factorial)]

namespace SelectedTrials
variable {q : ℕ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {j : ℕ → Fin q} {Δ : ℕ → ℝ} {d s : ℕ → E} {ε : Fin q → ℝ} {ζ θ κ : ℝ}

/-- The actual computed failed test and a proved optimality-radius floor give
the exact source uniform model-decrease lower bound. -/
theorem decrease_of_radius_floor (h : SelectedTrials A T j Δ d s ε ζ θ)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) {i : ℕ} (hi : i ∈ T)
    (hfloor : ζ * κ * minimumAccuracy h.order_pos ε ≤ optimalityRadius θ (Δ i)) :
    (ζ * κ) ^ (q + 1) / q.factorial * minimumAccuracy h.order_pos ε ^ (q + 1) ≤
      decrement (A i) (modelOrder (j i)) (s i) := by
  let μ := minimumAccuracy h.order_pos ε
  let b := ζ * κ * μ
  have hμ := (minimumAccuracy_pos h.order_pos h.accuracy_pos).le
  have hμ1 : μ ≤ 1 := (minimumAccuracy_le h.order_pos ε (j i)).trans (h.accuracy_le_one _)
  have hb : 0 ≤ b := mul_nonneg (mul_nonneg h.zeta_pos.le hκ) hμ
  have hκ1 : κ ≤ 1 := by linarith
  have hb1 : b ≤ 1 := by
    calc _ = ζ * (κ * μ) := by dsimp [b]; ring
      _ ≤ κ * μ := mul_le_of_le_one_left (mul_nonneg hκ hμ) h.zeta_le_one
      _ ≤ μ := mul_le_of_le_one_left hμ hκ1
      _ ≤ 1 := hμ1
  have hgap : b ≤ scaledGap A j Δ d θ i := by
    have hh := h.scaledGap_lower hi
    have hm := mul_le_mul_of_nonneg_left hκhalf (mul_nonneg h.zeta_pos.le hμ)
    dsimp [b]
    nlinarith
  have hfac : (0 : ℝ) < (modelOrder (j i)).factorial := by positivity
  have hpow : b ^ modelOrder (j i) ≤ optimalityRadius θ (Δ i) ^ modelOrder (j i) :=
    pow_le_pow_left₀ hb hfloor _
  have hfinal : b ^ (q + 1) / q.factorial ≤ decrement (A i) (modelOrder (j i)) (s i) := by
    calc _ ≤ b ^ (modelOrder (j i) + 1) / (modelOrder (j i)).factorial := by
          have hp0 := pow_le_pow_of_le_one hb hb1 (Nat.succ_le_succ (j i).isLt)
          have hf0 : ((modelOrder (j i)).factorial : ℝ) ≤ q.factorial := by
            exact_mod_cast Nat.factorial_le (j i).isLt
          exact (div_le_div_of_nonneg_right hp0 (Nat.cast_nonneg _)).trans
            (div_le_div_of_nonneg_left (pow_nonneg hb _) hfac hf0)
      _ = b * b ^ modelOrder (j i) / (modelOrder (j i)).factorial := by rw [pow_succ]; ring
      _ ≤ scaledGap A j Δ d θ i * optimalityRadius θ (Δ i) ^ modelOrder (j i) /
          (modelOrder (j i)).factorial := div_le_div_of_nonneg_right
            (mul_le_mul hgap hpow (pow_nonneg hb _) (hb.trans hgap)) hfac.le
      _ ≤ _ := h.model_decrease hi
  convert hfinal using 1
  dsimp [b]
  rw [mul_pow]
  ring

end SelectedTrials

/-- Actual bounded tensor coefficients control the computed Taylor decrement
linearly in every trial step of norm at most one. -/
theorem norm_decrement_le_two_mul (A : FormalMultilinearSeries ℝ E ℝ) (j : ℕ)
    {M : ℝ} (hM : 0 ≤ M) {s : E} (hs : ‖s‖ ≤ 1)
    (hA : ∀ a, 1 ≤ a → a ≤ j → ‖A a‖ ≤ M) :
    ‖decrement A j s‖ ≤ 2 * M * ‖s‖ :=
  (norm_jetDecrement_le A j s).trans
    (tensorErrorBudget_le_two_mul (norm_nonneg s) hs hM hA)

/-- A genuine failed computed test and actual comparison step cannot have a
vanishing trial length once the operational radius floor holds. -/
theorem norm_step_ge_of_failed_test (A : FormalMultilinearSeries ℝ E ℝ)
    {q j : ℕ} (hjq : j ≤ q) {δ ζ κ M μ : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hM : 1 ≤ M) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hfloor : ζ * κ * μ ≤ δ)
    (s : E) (hA : ∀ a, 1 ≤ a → a ≤ j → ‖A a‖ ≤ M)
    (htest : ζ / 2 * μ * δ ^ j / j.factorial ≤ decrement A j s) :
    accuracyThreshold q ζ κ M μ ≤ ‖s‖ := by
  by_cases hs : ‖s‖ ≤ 1
  · let b := ζ * κ * μ
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hb1 : b ≤ 1 := by
      calc _ = ζ * (κ * μ) := by dsimp [b]; ring
        _ ≤ κ * μ := mul_le_of_le_one_left (mul_nonneg hκ hμ) hζ1
        _ ≤ μ := mul_le_of_le_one_left hμ hκ1
        _ ≤ 1 := hμ1
    have hp := pow_div_factorial_antitone hb hb1 hjq
    have hpδ := pow_le_pow_left₀ hb hfloor j
    have hscale : ζ / 2 * μ * (b ^ q / q.factorial) ≤
        ζ / 2 * μ * δ ^ j / j.factorial := by
      calc _ ≤ ζ / 2 * μ * (b ^ j / j.factorial) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ ≤ _ := by
          simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hpδ (Nat.cast_nonneg _))
            (show 0 ≤ ζ / 2 * μ by positivity)
    have hupper := (le_abs_self (decrement A j s)).trans
      (norm_decrement_le_two_mul A j (by linarith) hs hA)
    have hid : 2 * M * accuracyThreshold q ζ κ M μ = ζ / 2 * μ * (b ^ q / q.factorial) := by
      unfold accuracyThreshold
      dsimp [b]
      rw [mul_pow, mul_pow, pow_succ ζ, pow_succ μ]
      field_simp
      ring
    have hh := hscale.trans (htest.trans hupper)
    rw [← hid] at hh
    exact (mul_le_mul_iff_right₀ (show 0 < 2 * M by positivity)).mp hh
  · exact (accuracyThreshold_le_one hζ hζ1 hκ hκ1 hM hμ hμ1).trans (not_le.mp hs).le

omit [NormedSpace ℝ E] in
/-- A uniform accuracy cap at the source threshold makes every actual Step 2
relative request pass, so the accuracy-improving branch is unavailable. -/
theorem requests_of_norm_floor {q : ℕ} {c κs H : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hκs : 0 ≤ κs) (hH : H ≤ κs * c ^ q) (accuracy : ℕ → ℝ)
    (haccuracy : ∀ a, 1 ≤ a → a ≤ q → accuracy a ≤ H)
    (s : E) (hstep : c ≤ ‖s‖) :
    ∀ a, 1 ≤ a → a ≤ q → accuracy a ≤ κs * ‖s‖ ^ (q - a + 1) := by
  intro a ha haq
  have hpow : c ^ q ≤ c ^ (q - a + 1) :=
    pow_le_pow_of_le_one hc hc1 (by omega)
  exact (haccuracy a ha haq).trans (hH.trans (mul_le_mul_of_nonneg_left
    (hpow.trans (pow_le_pow_left₀ hc hstep _)) hκs))

end InexactTrustRegion
