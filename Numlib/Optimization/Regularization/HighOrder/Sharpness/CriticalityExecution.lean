import Numlib.Optimization.Regularization.HighOrder.Sharpness.CriticalityJets
import Numlib.Optimization.HighOrder.ModelSolve.UnitCriticality
import Numlib.Optimization.Regularization.HighOrder.CriticalityRun

/-!
# Literal low-order ARqp executions of uniform monomial witnesses

The inner accuracy is two thirds of the requested accuracy. Thus the actual
ordered check fails strictly before the final node and passes strictly there.
Genuine global model minima give all primitive Step2 fields at unit radii.
-/

namespace HighOrderRegularization.Sharpness
open InexactTrustRegion

/-- Fixed legal ARqp settings for the monomial sharpness execution. -/
noncomputable def criticalitySettings {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) :
    HighOrderRegularization.Settings p q where
  order_pos := hq
  order_le := hqp
  zeta := 1
  zeta_pos := zero_lt_one
  zeta_le_one := le_rfl
  theta := 1 / 2
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  eta1 := 1 / 4
  eta2 := 3 / 4
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := parameter p
  sigmaInitial := parameter p
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := parameter_pos p
  sigmaMin_le_initial := le_rfl

/-- Actual unit-radius arrays for a constant-spacing monomial execution. The
last ordered check passes and therefore needs no endpoint model computation. -/
noncomputable def criticalityData (p q N : ℕ) (hq : 0 < q) (t : ℝ) :
    HighOrderRegularization.ExecutionData ℝ q where
  point := point t
  step := fun _ => t
  parameter := fun _ => parameter p
  ratio := fun _ => 1
  radius := fun _ _ => 1
  solvedRadius := fun _ _ => 1
  direction := fun _ _ => 1
  selected := fun k => if k < N then some ⟨q - 1, by omega⟩ else none

/-- The actual ordered Taylor tests of the monomial construction pass exactly
at the final node. No true-optimality conclusion is assumed in the check. -/
theorem optimalityCheck_of_matches {f : ℝ → ℝ} {p q N k : ℕ} {ε : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (hε : 0 < ε)
    (h : MatchesJets f p q N (amplitude p q) (step p q (2 / 3 * ε))) (hk : k ≤ N) :
    let t := step p q (2 / 3 * ε)
    OptimalityCheck f 1 (fun _ : Fin q => ε) (fun _ => 1) (point t k)
      (fun _ => 1) ((criticalityData p q N hq t).selected k) := by
  dsimp only
  let t := step p q (2 / 3 * ε)
  have hinner : 0 < (2 : ℝ) / 3 * ε := by positivity
  have ht := (step_pos p q hinner).le
  have hdec : ∀ a : Fin q, TaylorModel.decrement f (modelOrder a) (point t k) 1 =
      TaylorModel.criticality f (modelOrder a) (point t k) 1 :=
    fun a => decrement_one_eq_criticality hq hqp h hk a.isLt (amplitude_pos p q).le ht
  have hqcrit := criticality_order_eq_accuracy hq hqp hinner.le h hk
  have hcrit : ∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (point t k) 1 =
      if modelOrder a = q then (if k < N then 2 * (2 / 3 * ε) else 2 / 3 * ε) /
        (modelOrder a).factorial else 0 := by
    intro a
    by_cases ha : modelOrder a = q
    · simpa only [ha, ite_true] using hqcrit
    · rw [ite_eq_right ha]
      exact criticality_lower_eq_zero hq h hk ((show modelOrder a ≤ q from a.isLt).trans hqp)
        (lt_of_le_of_ne a.isLt ha) zero_le_one
  refine ⟨fun _ _ => by norm_num,
    fun a _ => by rw [hdec]; simp only [one_mul]; exact le_rfl, ?_, ?_, ?_⟩
  · intro hnone a
    have hkn : ¬k < N := by
      by_contra hb
      simp [criticalityData, hb] at hnone
    rw [hdec, hcrit, ite_eq_right hkn]
    simp only [one_mul, one_pow, mul_one]
    split_ifs
    · apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
      linarith
    · positivity
  · intro a hsome
    have hkn : k < N := by
      by_contra hn
      simp [criticalityData, hn] at hsome
    have ha : a = ⟨q - 1, by omega⟩ := by
      simpa only [criticalityData, hkn, ite_true, Option.some.injEq] using hsome.symm
    have haorder : modelOrder a = q := by rw [ha]; unfold modelOrder; dsimp; omega
    rw [hdec, hcrit, ite_eq_left haorder, ite_eq_left hkn]
    simp only [one_mul, one_pow, mul_one]
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    linarith
  · intro a hsome b hba
    have hkn : k < N := by
      by_contra hn
      simp [criticalityData, hn] at hsome
    have ha : a = ⟨q - 1, by omega⟩ := by
      simpa only [criticalityData, hkn, ite_true, Option.some.injEq] using hsome.symm
    have hb : modelOrder b < q := by
      rw [ha] at hba
      unfold modelOrder
      exact_mod_cast (show b.val + 1 < q by have := hba; simp only [Fin.lt_def] at this; omega)
    rw [hdec, hcrit, ite_eq_right (ne_of_lt hb)]
    simp only [one_mul, one_pow, mul_one]
    positivity

/-- The actual monomial witness follows every primitive ARqp rule for q=1 or2.
Its model steps are genuine global minima, with literal unit-radius checks. -/
theorem criticalityRun_of_matches {f : ℝ → ℝ} {p q N : ℕ} {ε : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (hq2 : q ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : MatchesJets f p q N (amplitude p q) (step p q (2 / 3 * ε))) :
    let P := criticalitySettings hq hqp
    let t := step p q (2 / 3 * ε)
    let D := criticalityData p q N hq t
    HighOrderRegularization.Run f P (fun _ => ε) D N := by
  let t := step p q (2 / 3 * ε)
  have ht : 0 < t := step_pos p q (by positivity)
  refine {
    accuracy_pos := fun _ => hε
    accuracy_le_one := fun _ => hε1
    initial_parameter := rfl
    initial_radii := fun _ => ⟨zero_lt_one, le_rfl⟩
    modelTrace := modelTrace_of_matches hq hqp h ht
    check := fun k hk => optimalityCheck_of_matches hq hqp hε h hk
    continues := ?_
    radius_update := fun _ _ => by
      funext a
      norm_num [criticalityData, criticalitySettings]
    step_two := ?_ }
  · intro k hk hselected
    have hkn : k < N := by
      by_contra hn
      exact hselected (by simp only [criticalityData, hn, ite_false])
    change ModelSolve.StepComputation
      (model f p (point t k) (parameter p)) modelOrder (1 / 2) 1
        (fun _ => ε) t (fun _ => 1)
    apply ModelSolve.stepComputation_unit_of_isMin
      (ModelDecrease.contDiff_penalized_ofJet (ftaylorSeries ℝ f (point t k)) p p le_rfl
        (parameter p)) modelOrder
      (fun a => ⟨by unfold modelOrder; omega,
        le_min ((show modelOrder a ≤ q from a.isLt).trans hq2)
          ((show modelOrder a ≤ q from a.isLt).trans hqp)⟩)
      (by norm_num) zero_lt_one (fun _ => ε) (fun _ => hε) t
    exact model_global_min hq hqp h hkn ht.le
  · intro k hk
    simp [criticalityData, hk]

/-- Every preterminal selected order is q, so Step1 and Step2 together evaluate
all positive derivative orders. The final passing Step1 evaluates only orders
through q. This counter includes exactly those terminal refreshes. -/
def criticalityDerivativeEvaluations (q j N : ℕ) : ℕ := N + if j ≤ q then 1 else 0

/-- Every derivative order is evaluated at least once per preterminal trial,
whether or not the final passing check refreshes that particular order. -/
theorem le_criticalityDerivativeEvaluations (q j N : ℕ) :
    N ≤ criticalityDerivativeEvaluations q j N := Nat.le_add_right _ _

/-- Actual derivative-evaluation nodes: Step1 processes orders through its
selected order (or through q when all checks pass), and preterminal Step2
computes orders above the selected order for the full model. The union counts
shared within-iteration evaluations once. -/
noncomputable def derivativeEvaluationNodes {q : ℕ} (selected : ℕ → Option (Fin q))
    (j N : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.range (N + 1)).filter fun k =>
    j ≤ q ∧ ∀ a, selected k = some a → j ≤ modelOrder a) ∪
    ((Finset.range N).filter fun k => ∃ a, selected k = some a ∧ modelOrder a < j)

/-- The literal selected-q execution has every preterminal evaluation, with
an additional endpoint evaluation exactly for orders processed by Step1. -/
theorem derivativeEvaluationNodes_data {p q N : ℕ} (hq : 0 < q) (t : ℝ) (j : ℕ) :
    derivativeEvaluationNodes (criticalityData p q N hq t).selected j N =
      if j ≤ q then Finset.range (N + 1) else Finset.range N := by
  classical
  ext k
  have hlast : modelOrder (⟨q - 1, by omega⟩ : Fin q) = q := by
    unfold modelOrder
    dsimp
    omega
  by_cases hk : k < N
  · by_cases hj : j ≤ q
    · simp [derivativeEvaluationNodes, criticalityData, hk, hj, hlast,
        show k < N + 1 by omega]
    · simp [derivativeEvaluationNodes, criticalityData, hk, hj, hlast, lt_of_not_ge hj]
  · by_cases hj : j ≤ q <;>
      simp [derivativeEvaluationNodes, criticalityData, hk, hj]

/-- The claimed count is the cardinality of the actual ordered-check/model
node union, rather than an unrelated algebraic upper schedule. -/
theorem criticalityDerivativeEvaluations_eq_card {p q N : ℕ} (hq : 0 < q)
    (t : ℝ) (j : ℕ) : criticalityDerivativeEvaluations q j N =
      (derivativeEvaluationNodes (criticalityData p q N hq t).selected j N).card := by
  rw [derivativeEvaluationNodes_data]
  split_ifs <;> simp [criticalityDerivativeEvaluations, *]

end HighOrderRegularization.Sharpness
