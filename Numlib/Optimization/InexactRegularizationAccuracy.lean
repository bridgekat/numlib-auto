import Numlib.Optimization.InexactRegularizationBounds

/-!
# Error budgets for implicit regularization

Uniform requested accuracy certifies true gaps after an all-pass inspection once its radii
have the stated floor. Step-dependent errors give very successful trials by comparing the
actual objective, exact Taylor polynomial and supplied polynomial separately. The latter
condition is kept explicit on long steps, whose literal algorithm branch skips its check.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {checked : ℕ}

/-- A uniform radius floor converts the simultaneous accuracy threshold into an independent
half-tolerance budget at every active order, including vanishing error multipliers. -/
theorem uniform_error_budget {q j : ℕ} (hjq : j ≤ q) {κ ε εj δ K H v : ℝ}
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hεj : ε ≤ εj) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hlower : κ * ε ≤ δ) (hK : 0 ≤ K) (hH : 0 ≤ H) (hv : v ≤ 1)
    (hsmall : 4 * (q ! : ℝ) * K * H ≤ v * κ ^ q * ε ^ (q + 1)) :
    2 * K * H ≤ εj * δ ^ j / (2 * (j ! : ℝ)) := by
  have hscale : κ ^ q * ε ^ (q + 1) ≤ εj * δ ^ j := by
    calc
      _ = ε * (κ * ε) ^ q := by rw [mul_pow, pow_succ]; ring
      _ ≤ ε * δ ^ q := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hκ hε) hlower q) hε
      _ ≤ ε * δ ^ j := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hδ.1 hδ.2 hjq) hε
      _ ≤ εj * δ ^ j := mul_le_mul_of_nonneg_right hεj (pow_nonneg hδ.1 _)
  have hs : 4 * (q ! : ℝ) * K * H ≤ κ ^ q * ε ^ (q + 1) :=
    by
    have hs' : 4 * (q ! : ℝ) * K * H ≤ v * (κ ^ q * ε ^ (q + 1)) := by
      simpa only [mul_assoc] using hsmall
    exact hs'.trans (mul_le_of_le_one_left (by positivity) hv)
  have hfac : (j ! : ℝ) ≤ (q ! : ℝ) := by exact_mod_cast Nat.factorial_le hjq
  have hb : (2 * K * H) * (2 * (j ! : ℝ)) ≤ εj * δ ^ j := by
    calc
      _ = 4 * (j ! : ℝ) * (K * H) := by ring
      _ ≤ 4 * (q ! : ℝ) * (K * H) := by gcongr
      _ = 4 * (q ! : ℝ) * K * H := by ring
      _ ≤ _ := hs.trans hscale
  exact (le_div_iff₀ (by positivity : 0 < 2 * (j ! : ℝ))).mpr hb

/-- The explicit simultaneous threshold transfers a computed all-pass inspection to true
objective optimality at its actual post-loop radii. The radius invariant is stated separately
from the error budget; neither is inferred from a failed computed witness. -/
theorem Inspection.true_quality_of_uniform_accuracy [ProperSpace E]
    {P : Parameters} {f : E → ℝ} {x : E} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P (f x) A σ δ) (hall : I.order = P.q + 1)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    {κ ε K H : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hlower : ∀ j, 1 ≤ j → j ≤ P.q → κ * ε ≤ I.radii j)
    (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p, ‖A i - iteratedFDeriv ℝ i f x‖ ≤ K * H)
    (hsmall : 4 * (P.q ! : ℝ) * K * H ≤ P.fraction * κ ^ P.q * ε ^ (P.q + 1)) :
    ∀ j, 1 ≤ j → j ≤ P.q →
      gapOn (taylorDecrement f j x) (Metric.closedBall 0 (I.radii j)) ≤
        P.epsilon j * I.radii j ^ j / (j ! : ℝ) := by
  apply I.true_quality hall hδ (fun _ => K * H) hcoeff
  intro j hj hjq
  have hv := I.valid_radii hδ j hj hjq
  exact (error_sum_le ⟨hv.1.le, hv.2⟩ (mul_nonneg hK hH) (fun _ _ => le_rfl)).trans
    (by
      simpa only [mul_assoc] using
        (uniform_error_budget hjq hκ hε (hεj j hj hjq) ⟨hv.1.le, hv.2⟩
          (hlower j hj hjq) hK hH P.fraction_le_one hsmall))

/-- Step-dependent coefficient accuracy and a positive regularizer-paid prediction force a
very successful exact-objective ratio. The error condition is required at every active order. -/
theorem very_successful_of_step_accuracy {P : Parameters} {f : E → ℝ} {x s : E}
    {A : Coefficients E} {L K κ σ : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖A i - iteratedFDeriv ℝ i f x‖ ≤ K * κ * ‖s‖ ^ (P.p - i + 1))
    (hpos : 0 < decrement A P.p s)
    (hpay : σ * ‖s‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ) ≤ decrement A P.p s)
    (hlarge : (2 * L + 4 * ((P.p + 1)! : ℝ) * κ * K) /
      (1 - P.eta2) ≤ σ) :
    P.eta2 ≤ (f x - f (x + s)) / decrement A P.p s := by
  have hrem := hf.value_remainder (P.order_pos.trans P.order_le) x s
  have herror := decrement_error_le_step_power A (fun i => iteratedFDeriv ℝ i f x)
    s (le_refl P.p) hK hκ hcoeff
  rw [decrement_iteratedFDeriv, ← polynomial_error_eq f x A P.p s] at herror
  have herr : |f (x + s) - polynomial (f x) A P.p s| ≤
      (L / ((P.p + 1)! : ℝ) + 2 * K * κ) * ‖s‖ ^ (P.p + 1) := by
    calc
      _ ≤ |f (x + s) - RegularizedTaylorModel.taylorModel f P.p x s| +
          |RegularizedTaylorModel.taylorModel f P.p x s - polynomial (f x) A P.p s| :=
        abs_sub_le _ _ _
      _ ≤ L / ((P.p + 1)! : ℝ) * ‖s‖ ^ (P.p + 1) +
          2 * K * κ * ‖s‖ ^ (P.p + 1) := by
        rw [abs_sub_comm (RegularizedTaylorModel.taylorModel f P.p x s)]
        exact add_le_add hrem herror
      _ = _ := by ring
  have hη : 0 < 1 - P.eta2 := sub_pos.mpr P.eta2_lt_one
  have hh := (div_le_iff₀ hη).mp hlarge
  have hbase : L / ((P.p + 1)! : ℝ) + 2 * K * κ ≤
      (1 - P.eta2) * σ / ((P.p + 1)! : ℝ) := by
    apply (le_div_iff₀ (by positivity : 0 < ((P.p + 1)! : ℝ))).mpr
    have hden : (((P.p + 1)! : ℝ)) ≠ 0 := by positivity
    field_simp
    nlinarith [hf.nonneg, mul_nonneg hK hκ]
  have herr' := herr.trans (mul_le_mul_of_nonneg_right hbase (pow_nonneg (norm_nonneg s) _))
  have hp := mul_le_mul_of_nonneg_left hpay hη.le
  have he : ((1 - P.eta2) * σ / ((P.p + 1)! : ℝ)) * ‖s‖ ^ (P.p + 1) =
      (1 - P.eta2) * (σ * ‖s‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ)) := by ring
  rw [he] at herr'
  have ht := (abs_le.mp (herr'.trans hp)).2
  have hd := decrement_eq (f x) A P.p s
  rw [polynomial_zero] at hd
  apply (le_div_iff₀ hpos).mpr
  linarith

omit [NormedSpace ℝ E] in
/-- The initial request bound controls errors on long steps; short steps use the explicit
step-accuracy check. Their maximum therefore gives a valid uniform effective coefficient. -/
theorem StepAccurate.request_le_power {P : Parameters} {h : ℕ → ℝ} {s : E}
    (ha : StepAccurate P P.p h s)
    (hinit : ∀ i ∈ Finset.Icc 1 P.p, h i ≤ P.kappaInitial)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    h i ≤ max P.kappaStep P.kappaInitial * ‖s‖ ^ (P.p - i + 1) := by
  rcases ha with hl | hs
  · exact (hinit i hi).trans
      ((le_max_right _ _).trans (le_mul_of_one_le_right
        (P.kappaStep_pos.le.trans (le_max_left _ _))
        (one_le_pow₀ hl)))
  · exact (hs i hi).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (norm_nonneg s) _))

/-- A large parameter cannot increase in an all-order-checked transition. The bound includes the
independent initial-accuracy constant needed for long steps that skip the accuracy check. -/
theorem Transition.sigma_nonincrease_of_large {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P P.p f oracle a b trial accepted) {L K : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hσ : 0 ≤ a.sigma)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters a.radii)
    (hinit : ∀ i ∈ Finset.Icc 1 P.p, a.request i ≤ P.kappaInitial)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle a.point a.request i - iteratedFDeriv ℝ i f a.point‖ ≤ K * a.request i)
    (hlarge : (2 * L + 4 * ((P.p + 1)! : ℝ) * max P.kappaStep P.kappaInitial * K) /
      (1 - P.eta2) ≤ a.sigma) : b.sigma ≤ a.sigma := by
  cases t with
  | refineInspection => exact le_rfl
  | refineStep => exact le_rfl
  | trial I hq s hacc next hu =>
    have hd := InnerResult.decrement_pos I hq s hσ hδ
    have he : ∀ i ∈ Finset.Icc 1 P.p,
        ‖oracle a.point a.request i - iteratedFDeriv ℝ i f a.point‖ ≤
          K * max P.kappaStep P.kappaInitial * ‖s.step‖ ^ (P.p - i + 1) := by
      intro i hi
      calc
        _ ≤ K * a.request i := hcoeff i hi
        _ ≤ K * (max P.kappaStep P.kappaInitial * ‖s.step‖ ^ (P.p - i + 1)) :=
          mul_le_mul_of_nonneg_left (hacc.request_le_power hinit hi) hK
        _ = _ := by ring
    have hv := very_successful_of_step_accuracy hf hK
      (P.kappaStep_pos.le.trans (le_max_left _ _)) he hd.2.1 hd.1 hlarge
    change P.eta2 ≤ ratio P f oracle a s.step at hv
    unfold HigherOrderApproximateRegularization.ParameterUpdate at hu
    simp only [ite_eq_left hv] at hu
    split_ifs <;> exact hu.2

/-- Every literal transition increases its parameter by at most the largest update factor. -/
theorem Transition.sigma_le_gamma3 {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) (hσ : 0 ≤ a.sigma) :
    b.sigma ≤ P.gamma3 * a.sigma := by
  have hg : 1 ≤ P.gamma3 := (P.one_lt_gamma2.trans P.gamma2_lt_gamma3).le
  have hs : a.sigma ≤ P.gamma3 * a.sigma := le_mul_of_one_le_left hσ hg
  cases t with
  | refineInspection => exact hs
  | refineStep => exact hs
  | trial I hq s hacc next hu =>
    have hh : next ≤ P.gamma3 * a.sigma := by
      unfold HigherOrderApproximateRegularization.ParameterUpdate at hu
      split_ifs at hu
      · exact hu.2.trans hs
      · exact hu.2.trans (mul_le_mul_of_nonneg_right P.gamma2_lt_gamma3.le hσ)
      · exact hu.2
    split_ifs <;> exact hh

/-- The all-order-checked variant has a uniform parameter bound with effective accuracy constant
`max κ_s κ_h`. This states explicitly the additional constant needed on unchecked long steps. -/
theorem Execution.sigma_upper {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P P.p f oracle N)
    {L K : ℝ} (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hcoeff : ∀ k < N, ∀ i ∈ Finset.Icc 1 P.p,
      ‖oracle (r.state k).point (r.state k).request i -
          iteratedFDeriv ℝ i f (r.state k).point‖ ≤ K * (r.state k).request i)
    {k : ℕ} (hk : k ≤ N) :
    (r.state k).sigma ≤ max (r.state 0).sigma
      (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) *
        max P.kappaStep P.kappaInitial * K) / (1 - P.eta2))) := by
  let T := (2 * L + 4 * ((P.p + 1)! : ℝ) * max P.kappaStep P.kappaInitial * K) /
    (1 - P.eta2)
  have hg : 0 ≤ P.gamma3 := (zero_lt_one.trans
    (P.one_lt_gamma2.trans P.gamma2_lt_gamma3)).le
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    have ht := r.transition k (by omega)
    have hs : 0 ≤ (r.state k).sigma := P.sigmaMin_pos.le.trans (r.sigma_floor (by omega))
    by_cases hb : T ≤ (r.state k).sigma
    · exact (ht.sigma_nonincrease_of_large hf hK hs (r.valid_radii (by omega))
        (fun i hi => (r.request_bounds (by omega) hi).2.trans (r.initial_request_le i hi))
        (hcoeff k (by omega)) hb).trans (ih (by omega))
    · exact (ht.sigma_le_gamma3 hs).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_ge hb) hg).trans (le_max_right _ _))

/-- A legal transition changes requests exactly when it performs accuracy refinement. -/
theorem Transition.request_eq {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) (i : ℕ) :
    b.request i = (if trial then 1 else P.gammaAccuracy) * a.request i := by
  cases t with
  | refineInspection => rfl
  | refineStep => rfl
  | trial => split_ifs <;> simp_all

/-- The number of actual accuracy-only iterations in a prefix of the execution. -/
def Execution.refinementCount {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    (k : ℕ) : ℕ := ∑ l ∈ Finset.range k, if r.trial l then 0 else 1

/-- Each accuracy refinement multiplies every request by the prescribed geometric factor;
accepted and rejected trials leave requests unchanged. -/
theorem Execution.request_eq {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {k : ℕ} (hk : k ≤ N) (i : ℕ) :
    (r.state k).request i = P.gammaAccuracy ^ r.refinementCount k * (r.state 0).request i := by
  induction k with
  | zero => simp [Execution.refinementCount]
  | succ k ih =>
    rw [(r.transition k (by omega)).request_eq i, ih (by omega)]
    unfold Execution.refinementCount
    rw [Finset.sum_range_succ]
    by_cases ht : r.trial k = true
    · simp [ht]
    · simp [ht, pow_succ]
      ring

end Optimization.InexactRegularization
