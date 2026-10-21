import Numlib.Optimization.HigherOrderApproximateRegularization
import Numlib.Optimization.HigherOrderRegularizationBounds
import Numlib.Optimization.HigherOrderRegularizationModelBounds
import Numlib.Optimization.InexactTaylorModels
import Numlib.Analysis.SpecialFunctions.FactorialSeries
import Numlib.Analysis.Calculus.NormPowerFactorialBounds

/-!
# All-order bounds for Taylor-gap regularization

Actual objective and regularized-model derivatives control the change in their compact
Taylor gaps. A failed true objective criterion supplies the sharp transfer constant.
Failure of the conservative computed witness test is a distinct condition.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderApproximateRegularization
open RegularizedTaylorModel TaylorCriticality

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {p j : ℕ} {L σ S : ℝ} {x s : E}

/-- Every active actual objective/model derivative difference has the sharp factorial bound. -/
theorem norm_derivative_sub_model_le
    (hf : HigherOrderRegularization.DiagonalLipschitz f p L) (hp : 1 ≤ p)
    (hj : j ≤ p) (hs : s ≠ 0) (hσ : 0 ≤ σ) (hS : σ ≤ S) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (model f p x σ) s‖ ≤
      (L + S) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) :=
  HigherOrderRegularization.norm_derivative_sub_model_le hs hσ hS
    (hf.derivative_remainder hp hj x s) (norm_iteratedFDeriv_norm_pow_le_factorial hj s)

/-- All-order factorial sums control the difference of actual objective and model decrements. -/
theorem taylorDecrement_sub_model_le
    (hf : HigherOrderRegularization.DiagonalLipschitz f p L) (hp : 1 ≤ p)
    (hj : j ≤ p) (hs : s ≠ 0) (hσ : 0 ≤ σ) (hS : σ ≤ S)
    {δ : ℝ} (d : E) (hd : ‖d‖ ≤ δ) :
    |taylorDecrement f j (x + s) d - taylorDecrement (model f p x σ) j s d| ≤
      (L + S) * ∑ ℓ ∈ Finset.Icc 1 j,
        δ ^ ℓ * ‖s‖ ^ (p - ℓ + 1) / (ℓ ! : ℝ) := by
  have hC : 0 ≤ L + S := add_nonneg hf.nonneg (hσ.trans hS)
  have hb := InexactTaylorModels.decrement_error_le
    (fun i => iteratedFDeriv ℝ i f (x + s))
    (fun i => iteratedFDeriv ℝ i (model f p x σ) s)
    (fun i => (L + S) * ‖s‖ ^ (p - i + 1)) j d (by
      intro i hi
      have hip : i ≤ p := (Finset.mem_Icc.mp hi).2.trans hj
      apply (norm_derivative_sub_model_le hf hp hip hs hσ hS).trans
      exact mul_le_mul_of_nonneg_right
        (div_le_self hC (by exact_mod_cast Nat.factorial_pos (p - i + 1)))
        (pow_nonneg (norm_nonneg s) _))
  simp only [InexactTaylorModels.decrement_iteratedFDeriv] at hb
  apply hb.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ (L + S) * ‖s‖ ^ (p - i + 1) * δ ^ i / (i ! : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg d) hd i)
        (mul_nonneg hC (pow_nonneg (norm_nonneg s) _))
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
/-- The small-step model tests imply actual compact Taylor-gap bounds at every active order. -/
theorem ModelStep.gap_le {P : Parameters} {f : E → ℝ} {x : E} {σ : ℝ}
    {δ : ℕ → ℝ} (trial : ModelStep P f x σ δ) (hs : ‖trial.step‖ ≤ 1)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    gapOn (taylorDecrement (model f P.p x σ) j trial.step)
      (Metric.closedBall 0 (trial.radii j)) ≤
        P.theta * P.epsilon j * trial.radii j ^ j / (j ! : ℝ) := by
  rcases trial.quality with hlong | hall
  · exact (not_lt_of_ge hs hlong.1).elim
  · have hb := (hall j hj hjq).1.fraction_le
    have ht := (hall j hj hjq).2
    have he : P.fraction * P.theta * P.epsilon j * trial.radii j ^ j / (j ! : ℝ) =
        P.fraction * (P.theta * P.epsilon j * trial.radii j ^ j / (j ! : ℝ)) := by ring
    rw [he] at ht
    nlinarith [P.fraction_pos]

/-- The true simultaneous objective criterion uses the actual compact Taylor gaps. -/
def SatisfiesCriteria (P : Parameters) (f : E → ℝ) (x : E) (δ : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ P.q →
    gapOn (taylorDecrement f j x) (Metric.closedBall 0 (δ j)) ≤
      P.epsilon j * δ j ^ j / (j ! : ℝ)

omit [FiniteDimensional ℝ E] in
/-- Failure of the true criterion supplies an active order with true gap above tolerance. -/
theorem not_satisfiesCriteria_iff {P : Parameters} {f : E → ℝ} {x : E} {δ : ℕ → ℝ} :
    ¬SatisfiesCriteria P f x δ ↔ ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      P.epsilon j * δ j ^ j / (j ! : ℝ) <
        gapOn (taylorDecrement f j x) (Metric.closedBall 0 (δ j)) := by
  simp only [SatisfiesCriteria, not_forall, not_le, exists_prop]

/-- With valid radii, the actual criteria are precisely the canonical approximate-minimizer
conditions on their compact displacement balls. -/
theorem satisfiesCriteria_iff_isApproxMinimizer {P : Parameters} {f : E → ℝ}
    {x : E} {δ : ℕ → ℝ} (hδ : ValidRadii P δ) :
    SatisfiesCriteria P f x δ ↔
      IsApproxMinimizer f x P.q P.epsilon δ (fun j => Metric.closedBall 0 (δ j)) := by
  constructor
  · intro h
    exact {
      epsilon_pos := P.epsilon_pos
      radius_pos := fun j hj hjq => (hδ j hj hjq).1
      compact := fun j _ _ => isCompact_closedBall 0 (δ j)
      zero_mem := fun j hj hjq => by simpa using (hδ j hj hjq).1.le
      norm_le := fun _ _ _ _ hd => by simpa using hd
      gap_le := h }
  · exact fun h => h.gap_le

/-- A true failed next-point gap and the actual model step imply the source transfer estimate.
Long steps satisfy it directly; small steps use the full actual jet comparison. -/
theorem transfer_of_true_gap_failure {P : Parameters} {f : E → ℝ} {x : E} {σ S L : ℝ}
    {δ : ℕ → ℝ} (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hL : 1 ≤ L) (trial : ModelStep P f x σ δ) (hne : trial.step ≠ 0)
    (hσ : 0 ≤ σ) (hS : σ ≤ S)
    (hfail : ¬SatisfiesCriteria P f (x + trial.step) trial.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      (1 - P.theta) * P.epsilon j * trial.radii j ^ j / (j ! : ℝ) ≤
        (L + S) * ∑ ℓ ∈ Finset.Icc 1 j,
          trial.radii j ^ ℓ * ‖trial.step‖ ^ (P.p - ℓ + 1) / (ℓ ! : ℝ) := by
  by_cases hs : ‖trial.step‖ ≤ 1
  · obtain ⟨j, hj, hjq, hbad⟩ := not_satisfiesCriteria_iff.mp hfail
    refine ⟨j, hj, hjq, ?_⟩
    have hd0 : 0 ≤ trial.radii j := (trial.radii_valid j hj hjq).1.le
    have hgap := gapOn_le_gapOn_add (Δ := taylorDecrement f j (x + trial.step))
      (η := (L + S) * ∑ ℓ ∈ Finset.Icc 1 j,
        trial.radii j ^ ℓ * ‖trial.step‖ ^ (P.p - ℓ + 1) / (ℓ ! : ℝ))
      (isCompact_closedBall (0 : E) (trial.radii j))
      ⟨0, by simpa using hd0⟩
      (continuous_taylorDecrement (model f P.p x σ) j trial.step).continuousOn (fun d hd => by
        have hb := taylorDecrement_sub_model_le (x := x) hf (P.order_pos.trans P.order_le)
          (hjq.trans P.order_le) hne hσ hS d (by simpa using hd)
        linarith only [(abs_le.mp hb).2])
    have hm := trial.gap_le hs hj hjq
    have he : (1 - P.theta) * P.epsilon j * trial.radii j ^ j / (j ! : ℝ) =
        P.epsilon j * trial.radii j ^ j / (j ! : ℝ) -
          P.theta * P.epsilon j * trial.radii j ^ j / (j ! : ℝ) := by ring
    rw [he]
    linarith only [hgap, hm, hbad]
  · refine ⟨1, le_rfl, P.order_pos, ?_⟩
    have hd : 0 < trial.radii 1 := (trial.radii_valid 1 le_rfl P.order_pos).1
    have hC : 1 ≤ L + S := by linarith [hσ.trans hS]
    have hn : 1 ≤ ‖trial.step‖ ^ P.p := one_le_pow₀ (lt_of_not_ge hs).le
    have he : (1 - P.theta) * P.epsilon 1 ≤ 1 := by
      nlinarith [P.theta_pos, P.theta_lt_one, P.epsilon_pos 1 le_rfl P.order_pos,
        P.epsilon_lt_one 1 le_rfl P.order_pos]
    norm_num only [Finset.Icc_self, Finset.sum_singleton, Nat.factorial_one,
      Nat.cast_one, pow_one, div_one, Nat.sub_self, zero_add] at *
    have hp : P.p - 1 + 1 = P.p := by have := P.order_pos.trans P.order_le; omega
    rw [hp]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hn)]

/-- When the step is below the radius, a finite mixed factorial sum is controlled by
its last-order monomial. -/
theorem factorial_sum_le_of_step_le_radius {p j : ℕ} (hjp : j ≤ p)
    {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (haδ : a ≤ δ) :
    (∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ * a ^ (p - ℓ + 1) / (ℓ ! : ℝ)) ≤
      2 * δ ^ j * a ^ (p - j + 1) := by
  have hmono : ∀ ℓ ∈ Finset.Icc 1 j,
      δ ^ ℓ * a ^ (p - ℓ + 1) ≤ δ ^ j * a ^ (p - j + 1) := by
    intro ℓ hℓ
    have hℓj := (Finset.mem_Icc.mp hℓ).2
    rw [show p - ℓ + 1 = (j - ℓ) + (p - j + 1) by omega, pow_add]
    calc
      _ ≤ δ ^ ℓ * (δ ^ (j - ℓ) * a ^ (p - j + 1)) := by
        gcongr
      _ = _ := by
        rw [← mul_assoc, ← pow_add, show ℓ + (j - ℓ) = j by omega]
  have h := InexactTaylorModels.error_sum_le (e := fun ℓ => δ ^ ℓ * a ^ (p - ℓ + 1))
    (δ := 1) (by norm_num) (by positivity) hmono
  simpa only [one_pow, mul_one, mul_assoc] using h

/-- When the radius is below the step, the same sum is controlled by its first-order
monomial, independently of its truncation order. -/
theorem factorial_sum_le_of_radius_le_step {p j : ℕ} (hjp : j ≤ p)
    {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδa : δ ≤ a) :
    (∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ * a ^ (p - ℓ + 1) / (ℓ ! : ℝ)) ≤
      2 * δ * a ^ p := by
  have hmono : ∀ ℓ ∈ Finset.Icc 1 j,
      δ ^ ℓ * a ^ (p - ℓ + 1) ≤ δ * a ^ p := by
    intro ℓ hℓ
    have hℓ1 := (Finset.mem_Icc.mp hℓ).1
    have hℓp := (Finset.mem_Icc.mp hℓ).2.trans hjp
    rw [show ℓ = (ℓ - 1) + 1 by omega, pow_succ]
    calc
      _ ≤ (a ^ (ℓ - 1) * δ) * a ^ (p - ((ℓ - 1) + 1) + 1) := by
        gcongr
      _ = _ := by
        rw [show p - ((ℓ - 1) + 1) + 1 = p - ℓ + 1 by omega]
        rw [mul_right_comm, ← pow_add, show ℓ - 1 + (p - ℓ + 1) = p by omega]
        ring
  have h := InexactTaylorModels.error_sum_le (e := fun ℓ => δ ^ ℓ * a ^ (p - ℓ + 1))
    (δ := 1) (by norm_num) (by positivity) hmono
  simpa only [one_pow, mul_one, mul_assoc] using h

/-- The transfer inequality yields the low-radius-regime step-power estimate. -/
theorem power_lower_bound_of_step_le_radius {p j : ℕ} (hjp : j ≤ p)
    {a δ C ε θ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hC : 0 < C) (haδ : a ≤ δ)
    (hb : (1 - θ) * ε * δ ^ j / (j ! : ℝ) ≤
      C * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ * a ^ (p - ℓ + 1) / (ℓ ! : ℝ)) :
    (1 - θ) / (2 * (j ! : ℝ) * C) * ε ≤ a ^ (p - j + 1) := by
  have hsum := factorial_sum_le_of_step_le_radius hjp ha hδ.le haδ
  have h := hb.trans (mul_le_mul_of_nonneg_left hsum hC.le)
  have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < j !)).mp h
  have hcan : (1 - θ) * ε ≤ 2 * (j ! : ℝ) * C * a ^ (p - j + 1) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hδ j)).mp
    convert hmul using 1 <;> ring
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * (j ! : ℝ) * C)]
  convert hcan using 1
  ring

/-- The complementary regime yields the radius-weighted top step-power estimate. -/
theorem power_lower_bound_of_radius_le_step {p j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    {a δ C ε θ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hC : 0 < C) (hδa : δ ≤ a)
    (hb : (1 - θ) * ε * δ ^ j / (j ! : ℝ) ≤
      C * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ * a ^ (p - ℓ + 1) / (ℓ ! : ℝ)) :
    (1 - θ) / (2 * (j ! : ℝ) * C) * ε * δ ^ (j - 1) ≤ a ^ p := by
  have hsum := factorial_sum_le_of_radius_le_step hjp ha hδ.le hδa
  have h := hb.trans (mul_le_mul_of_nonneg_left hsum hC.le)
  have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < j !)).mp h
  have hcan : (1 - θ) * ε * δ ^ (j - 1) ≤ 2 * (j ! : ℝ) * C * a ^ p := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    rw [show δ ^ j = δ ^ (j - 1) * δ by
      rw [← pow_succ]
      congr 1
      omega] at hmul
    convert hmul using 1 <;> ring
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_iff₀ (by positivity : 0 < 2 * (j ! : ℝ) * C)]
  convert hcan using 1
  ring

/-- Taking a positive integer root preserves the coefficient and tolerance powers. -/
theorem root_mul_tolerance_le_of_power_bound {p j : ℕ} (hp : 0 < p)
    {a B ε : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hb : B * ε ^ j ≤ a ^ p) :
    B ^ (1 / (p : ℝ)) * ε ^ ((j : ℝ) / p) ≤ a := by
  have hr : (B * ε ^ j) ^ (p : ℝ)⁻¹ ≤ a :=
    (Real.rpow_inv_le_iff_of_pos (mul_nonneg hB (pow_nonneg hε j)) ha
      (by exact_mod_cast hp)).mpr (by simpa only [Real.rpow_natCast] using hb)
  rw [Real.mul_rpow hB (pow_nonneg hε j), ← Real.rpow_natCast_mul hε] at hr
  simpa only [one_div, div_eq_mul_inv, one_mul] using hr

/-- The coefficient appearing after cancellation of the source transfer inequality. -/
def transferCoefficient (j : ℕ) (θ C : ℝ) : ℝ := (1 - θ) / (2 * (j ! : ℝ) * C)

/-- The step lower-bound exponent in the two radius regimes. -/
def stepBoundExponent (p q j : ℕ) : ℝ :=
  if q ≤ 2 then 1 / ((p - j + 1 : ℕ) : ℝ) else (j : ℝ) / p

/-- A valid tolerance-independent step coefficient in both radius regimes. The minimum
in the higher-order regime retains both coefficients arising in the split at step equals radius. -/
def stepBoundConstant (p q j : ℕ) (θ C κ : ℝ) : ℝ :=
  let A := transferCoefficient j θ C
  if q ≤ 2 then A ^ (1 / ((p - j + 1 : ℕ) : ℝ))
  else min (A ^ (1 / ((p - j + 1 : ℕ) : ℝ)))
    ((A * κ ^ (j - 1)) ^ (1 / (p : ℝ)))

/-- The step coefficient is strictly positive, independently of the tolerance. -/
theorem stepBoundConstant_pos (p q j : ℕ) {θ C κ : ℝ}
    (hθ : θ < 1) (hC : 0 < C) (hκ : 0 < κ) :
    0 < stepBoundConstant p q j θ C κ := by
  have hA : 0 < transferCoefficient j θ C := div_pos (sub_pos.mpr hθ) (by positivity)
  unfold stepBoundConstant
  split_ifs <;> dsimp only <;> positivity

/-- Scalar transfer estimates imply the two-regime lower step bound with a valid common
coefficient. In the higher-order regime, the two radius cases keep their own constants. -/
theorem step_lower_bound_of_transfer {p q j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    {a δ C ε θ κ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hC : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : θ < 1) (hκ : 0 < κ)
    (hunit : q ≤ 2 → δ = 1) (hlower : 2 < q → κ * ε ≤ δ)
    (hb : (1 - θ) * ε * δ ^ j / (j ! : ℝ) ≤
      C * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ * a ^ (p - ℓ + 1) / (ℓ ! : ℝ))
    (ha1 : a ≤ 1) :
    stepBoundConstant p q j θ C κ * ε ^ stepBoundExponent p q j ≤ a := by
  let A := transferCoefficient j θ C
  have hA : 0 ≤ A := (div_pos (sub_pos.mpr hθ) (by positivity)).le
  have hp : 0 < p := by omega
  have hr : 0 < p - j + 1 := by omega
  by_cases hq : q ≤ 2
  · have hd := hunit hq
    have hbpow := power_lower_bound_of_step_le_radius hjp ha hδ hC (hd ▸ ha1) hb
    have hroot := root_mul_tolerance_le_of_power_bound (j := 1) hr ha hA hε.le
      (by simpa only [pow_one, A, transferCoefficient] using hbpow)
    simpa only [stepBoundConstant, stepBoundExponent, ite_eq_left hq, Nat.cast_one] using hroot
  · have hq' : 2 < q := by omega
    simp only [stepBoundConstant, stepBoundExponent, ite_eq_right hq]
    change min (A ^ (1 / ((p - j + 1 : ℕ) : ℝ)))
      ((A * κ ^ (j - 1)) ^ (1 / (p : ℝ))) * ε ^ ((j : ℝ) / p) ≤ a
    by_cases haδ : a ≤ δ
    · have hbpow := power_lower_bound_of_step_le_radius hjp ha hδ hC haδ hb
      have hroot := root_mul_tolerance_le_of_power_bound (j := 1) hr ha hA hε.le
        (by simpa only [pow_one, A, transferCoefficient] using hbpow)
      simp only [Nat.cast_one] at hroot
      have hrel : 1 / ((p - j + 1 : ℕ) : ℝ) ≤ (j : ℝ) / p := by
        apply (div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < p)).mpr
        rw [Nat.cast_add, Nat.cast_sub hjp, Nat.cast_one]
        have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
        have hjpr : (j : ℝ) ≤ p := by exact_mod_cast hjp
        nlinarith [mul_nonneg (by linarith : 0 ≤ (j : ℝ) - 1)
          (by linarith : 0 ≤ (p : ℝ) - j)]
      apply le_trans _ hroot
      exact mul_le_mul (min_le_left _ _)
        (Real.rpow_le_rpow_of_exponent_ge hε hε1 hrel) (by positivity) (by positivity)
    · have hbpow := power_lower_bound_of_radius_le_step hj hjp ha hδ hC
        (lt_of_not_ge haδ).le hb
      have hpower : A * κ ^ (j - 1) * ε ^ j ≤ a ^ p := by
        have hlow := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg hκ.le hε.le) (hlower hq') (j - 1))
          (mul_nonneg hA hε.le)
        have he : A * κ ^ (j - 1) * ε ^ j = A * ε * (κ * ε) ^ (j - 1) := by
          rw [mul_pow, show ε ^ j = ε ^ (j - 1) * ε by
            rw [← pow_succ]; congr 1; omega]
          ring
        rw [he]
        exact hlow.trans hbpow
      have hroot := root_mul_tolerance_le_of_power_bound hp ha
        (mul_nonneg hA (pow_nonneg hκ.le _)) hε.le hpower
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans hroot

/-- Normalized error constants make the tolerance-independent step coefficient at most one. -/
theorem stepBoundConstant_le_one (p q j : ℕ) {θ C κ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 1 ≤ C) :
    stepBoundConstant p q j θ C κ ≤ 1 := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hA0 : 0 ≤ transferCoefficient j θ C :=
    (div_pos (sub_pos.mpr hθ1) (by positivity)).le
  have hA1 : transferCoefficient j θ C ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * (j ! : ℝ) * C)).mpr
    have hjf : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.factorial_pos j
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hjf)]
  have hr := Real.rpow_le_one hA0 hA1
    (by positivity : 0 ≤ 1 / ((p - j + 1 : ℕ) : ℝ))
  unfold stepBoundConstant
  split_ifs
  · exact hr
  · exact (min_le_left _ _).trans hr

/-- A step of norm at least one meets the normalized tolerance-power step bound.
The initialized radius coefficient may be arbitrary; the transfer coefficient is normalized. -/
theorem step_lower_bound_of_one_le (P : Parameters) {C κ a : ℝ}
    (hC : 1 ≤ C) (ha : 1 ≤ a) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      stepBoundConstant P.p P.q j P.theta C κ *
        (P.epsilon j) ^ stepBoundExponent P.p P.q j ≤ a := by
  refine ⟨1, le_rfl, P.order_pos, ?_⟩
  have hb := stepBoundConstant_le_one P.p P.q 1 (κ := κ)
    P.theta_pos.le P.theta_lt_one hC
  have he : 0 ≤ stepBoundExponent P.p P.q 1 := by
    unfold stepBoundExponent
    split_ifs <;> positivity
  have hp := Real.rpow_le_one (P.epsilon_pos 1 le_rfl P.order_pos).le
    (P.epsilon_lt_one 1 le_rfl P.order_pos).le he
  exact (mul_le_mul hb hp (Real.rpow_nonneg (P.epsilon_pos 1 le_rfl P.order_pos).le _)
    zero_le_one).trans (by simpa using ha)

/-- Unit radii at orders one and two, and linear tolerance radii at higher orders,
imply the two radius regimes used by the complexity proof. -/
theorem regime_radii_of_unit_low_and_lower_high (P : Parameters) {κ : ℝ} {δ : ℕ → ℝ}
    (hκ : κ ≤ 1)
    (hunit : ∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → δ j = 1)
    (hlower : ∀ j, 3 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ δ j) :
    (P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → δ j = 1) ∧
      (2 < P.q → ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ δ j) := by
  constructor
  · intro hq j hj hjq
    exact hunit j hj hjq (hjq.trans hq)
  · intro _ j hj hjq
    by_cases hj2 : j ≤ 2
    · rw [hunit j hj hjq hj2]
      simpa only [one_mul] using mul_le_mul hκ (P.epsilon_lt_one j hj hjq).le
        (P.epsilon_pos j hj hjq).le zero_le_one
    · exact hlower j (by omega) hjq

/-- The true next-point failure yields an active-order step lower bound with both source
tolerance exponents, under the corresponding actual radius choices. -/
theorem step_lower_bound_of_true_gap_failure {P : Parameters} {f : E → ℝ} {x : E}
    {σ S L κ : ℝ} {δ : ℕ → ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (trial : ModelStep P f x σ δ) (hne : trial.step ≠ 0) (hσ : 0 ≤ σ) (hS : σ ≤ S)
    (hκ : 0 < κ)
    (hunit : P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → trial.radii j = 1)
    (hlower : 2 < P.q → ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ trial.radii j)
    (hfail : ¬SatisfiesCriteria P f (x + trial.step) trial.radii) :
    ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      stepBoundConstant P.p P.q j P.theta (L + S) κ *
        (P.epsilon j) ^ stepBoundExponent P.p P.q j ≤ ‖trial.step‖ := by
  have hC : 1 ≤ L + S := by linarith [hσ.trans hS]
  have hCp := lt_of_lt_of_le zero_lt_one hC
  by_cases hs : ‖trial.step‖ ≤ 1
  · obtain ⟨j, hj, hjq, hb⟩ := transfer_of_true_gap_failure hf hL trial hne hσ hS hfail
    refine ⟨j, hj, hjq, ?_⟩
    exact step_lower_bound_of_transfer hj (hjq.trans P.order_le) (norm_nonneg _)
      (trial.radii_valid j hj hjq).1 hCp (P.epsilon_pos j hj hjq)
      (P.epsilon_lt_one j hj hjq).le P.theta_lt_one hκ
      (fun hq => hunit hq j hj hjq) (fun hq => hlower hq j hj hjq) hb hs
  · exact step_lower_bound_of_one_le P hC (lt_of_not_ge hs).le

/-- The source complexity exponents in the two radius regimes. -/
def complexityExponent (p q j : ℕ) : ℝ :=
  if q ≤ 2 then ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)
  else (j : ℝ) * ((p + 1 : ℕ) : ℝ) / p

/-- Raising the step bound to the regularizer degree gives the complexity exponent. -/
theorem stepBoundExponent_mul_degree (p q j : ℕ) :
    stepBoundExponent p q j * ((p + 1 : ℕ) : ℝ) = complexityExponent p q j := by
  unfold stepBoundExponent complexityExponent
  split_ifs <;> ring

/-- The simultaneous tolerance scale is the minimum over every active order. -/
def toleranceMeasure (p q : ℕ) (hq : 1 ≤ q) (ε : ℕ → ℝ) : ℝ :=
  (Finset.Icc 1 q).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hq⟩⟩
    (fun j => (ε j) ^ complexityExponent p q j)

/-- The uniform model-decrease coefficient depends only on structural algorithm constants. -/
def modelDecreaseConstant (p q : ℕ) (hq : 1 ≤ q) (θ C κ σmin : ℝ) : ℝ :=
  σmin / ((p + 1)! : ℝ) *
    (Finset.Icc 1 q).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hq⟩⟩
      (fun j => stepBoundConstant p q j θ C κ ^ (p + 1))

/-- Positive active tolerances have a positive simultaneous scale. -/
theorem toleranceMeasure_pos (P : Parameters) :
    0 < toleranceMeasure P.p P.q P.order_pos P.epsilon := by
  apply (Finset.lt_inf'_iff _).mpr
  intro j hj
  exact Real.rpow_pos_of_pos (P.epsilon_pos j (Finset.mem_Icc.mp hj).1
    (Finset.mem_Icc.mp hj).2) _

/-- The structural model-decrease coefficient is strictly positive. -/
theorem modelDecreaseConstant_pos (p q : ℕ) (hq : 1 ≤ q) {θ C κ σmin : ℝ}
    (hθ : θ < 1) (hC : 0 < C) (hκ : 0 < κ) (hσmin : 0 < σmin) :
    0 < modelDecreaseConstant p q hq θ C κ σmin := by
  apply mul_pos (div_pos hσmin (by positivity))
  apply (Finset.lt_inf'_iff _).mpr
  intro j _
  exact pow_pos (stepBoundConstant_pos p q j hθ hC hκ) _

/-- An active-order step lower bound and regularizer payment imply the simultaneous
model-decrease scale, independently of the objective or the provenance of the prediction. -/
theorem predicted_decrease_of_step_lower_bound (P : Parameters) {C κ a prediction : ℝ}
    (hC : 0 < C) (hκ : 0 < κ)
    (hstep : ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      stepBoundConstant P.p P.q j P.theta C κ *
        (P.epsilon j) ^ stepBoundExponent P.p P.q j ≤ a)
    (hpay : P.sigmaMin / ((P.p + 1)! : ℝ) * a ^ (P.p + 1) ≤ prediction) :
    modelDecreaseConstant P.p P.q P.order_pos P.theta C κ P.sigmaMin *
      toleranceMeasure P.p P.q P.order_pos P.epsilon ≤ prediction := by
  obtain ⟨j, hj, hjq, hb⟩ := hstep
  have hB := stepBoundConstant_pos P.p P.q j P.theta_lt_one hC hκ
  have hε := P.epsilon_pos j hj hjq
  have hpower := pow_le_pow_left₀ (mul_nonneg hB.le (Real.rpow_nonneg hε.le _))
    hb (P.p + 1)
  rw [mul_pow, ← Real.rpow_mul_natCast hε.le, stepBoundExponent_mul_degree] at hpower
  have hc := Finset.inf'_le (s := Finset.Icc 1 P.q)
    (fun i => stepBoundConstant P.p P.q i P.theta C κ ^ (P.p + 1))
    (Finset.mem_Icc.mpr ⟨hj, hjq⟩)
  have ht := Finset.inf'_le (s := Finset.Icc 1 P.q)
    (fun i => (P.epsilon i) ^ complexityExponent P.p P.q i)
    (Finset.mem_Icc.mpr ⟨hj, hjq⟩)
  calc
    _ ≤ (P.sigmaMin / ((P.p + 1)! : ℝ)) *
        (stepBoundConstant P.p P.q j P.theta C κ ^ (P.p + 1) *
          (P.epsilon j) ^ complexityExponent P.p P.q j) := by
      unfold modelDecreaseConstant toleranceMeasure
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (div_nonneg P.sigmaMin_pos.le (by positivity))
      exact mul_le_mul hc ht (toleranceMeasure_pos P).le (by positivity)
    _ ≤ (P.sigmaMin / ((P.p + 1)! : ℝ)) * a ^ (P.p + 1) :=
      mul_le_mul_of_nonneg_left hpower (div_nonneg P.sigmaMin_pos.le (by positivity))
    _ ≤ _ := hpay

/-- Before true next-point attainment, every actual model step pays the simultaneous
tolerance-power decrease with a tolerance-independent structural coefficient. -/
theorem predicted_decrease_of_true_gap_failure {P : Parameters} {f : E → ℝ} {x : E}
    {σ S L κ : ℝ} {δ : ℕ → ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (trial : ModelStep P f x σ δ) (hne : trial.step ≠ 0)
    (hfloor : P.sigmaMin ≤ σ) (hS : σ ≤ S) (hκ : 0 < κ)
    (hunit : P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → trial.radii j = 1)
    (hlower : 2 < P.q → ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ trial.radii j)
    (hfail : ¬SatisfiesCriteria P f (x + trial.step) trial.radii) :
    modelDecreaseConstant P.p P.q P.order_pos P.theta (L + S) κ P.sigmaMin *
      toleranceMeasure P.p P.q P.order_pos P.epsilon ≤
        taylorDecrement f P.p x trial.step := by
  have hσ : 0 ≤ σ := P.sigmaMin_pos.le.trans hfloor
  obtain ⟨j, hj, hjq, hstep⟩ := step_lower_bound_of_true_gap_failure hf hL trial hne hσ hS
    hκ hunit hlower hfail
  have hC : 0 < L + S := by linarith [hσ.trans hS]
  apply predicted_decrease_of_step_lower_bound P hC hκ ⟨j, hj, hjq, hstep⟩
  have hpay := HigherOrderRegularization.predicted_decrease_of_model_le trial.nonincrease
  change σ / ((P.p + 1)! : ℝ) * ‖trial.step‖ ^ (P.p + 1) ≤
    taylorDecrement f P.p x trial.step at hpay
  exact (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hfloor (by positivity)) (pow_nonneg (norm_nonneg _) _)).trans hpay

omit [FiniteDimensional ℝ E] in
/-- A nonzero model-decreasing step with positive regularization has positive Taylor prediction. -/
theorem ModelStep.taylorDecrement_pos {P : Parameters} {f : E → ℝ} {x : E}
    {σ : ℝ} {δ : ℕ → ℝ} (trial : ModelStep P f x σ δ)
    (hne : trial.step ≠ 0) (hσ : 0 < σ) : 0 < taylorDecrement f P.p x trial.step := by
  have hpay := HigherOrderRegularization.predicted_decrease_of_model_le trial.nonincrease
  exact (mul_pos (div_pos hσ (by positivity))
    (pow_pos (norm_pos_iff.mpr hne) _)).trans_le hpay

/-- Acceptance converts the predicted decrease into actual objective decrease. -/
theorem accepted_decrease_of_true_gap_failure {P : Parameters} {f : E → ℝ} {x : E}
    {σ S L κ : ℝ} {δ : ℕ → ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hL : 1 ≤ L)
    (trial : ModelStep P f x σ δ) (hne : trial.step ≠ 0)
    (hfloor : P.sigmaMin ≤ σ) (hS : σ ≤ S) (hκ : 0 < κ)
    (hunit : P.q ≤ 2 → ∀ j, 1 ≤ j → j ≤ P.q → trial.radii j = 1)
    (hlower : 2 < P.q → ∀ j, 1 ≤ j → j ≤ P.q → κ * P.epsilon j ≤ trial.radii j)
    (hfail : ¬SatisfiesCriteria P f (x + trial.step) trial.radii)
    (haccept : P.eta1 ≤ (f x - f (x + trial.step)) / taylorDecrement f P.p x trial.step) :
    P.eta1 * (modelDecreaseConstant P.p P.q P.order_pos P.theta (L + S) κ P.sigmaMin *
      toleranceMeasure P.p P.q P.order_pos P.epsilon) ≤ f x - f (x + trial.step) := by
  have hpred := predicted_decrease_of_true_gap_failure hf hL trial hne hfloor hS hκ
    hunit hlower hfail
  exact (mul_le_mul_of_nonneg_left hpred P.eta1_pos.le).trans
    ((le_div_iff₀ (trial.taylorDecrement_pos hne (P.sigmaMin_pos.trans_le hfloor))).mp haccept)

end Optimization.HigherOrderApproximateRegularization
