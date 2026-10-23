import Numlib.Optimization.Regularization.HighOrder.Sharpness.Data
import Numlib.Optimization.Regularization.HighOrder.Step

/-!
# Actual monomial regularization models and accuracy scaling

The constructed objectives determine genuine finite Taylor polynomials and actual
regularized model derivatives. A fixed small parameter gives legal unit model-test
tolerances and every scalar unit direction has small model curvature. Exact model
improvement, true acceptance ratio one and operational parameter updates follow.
The spatial scaling preserves uniform objective budgets before every accuracy.
-/

open Polynomial Set
namespace HighOrderRegularization.Sharpness

/-- Prescribed scalar jets determine the actual finite Taylor polynomial. -/
theorem eval_of_matches {f : ℝ → ℝ} {p r N k : ℕ} {A t u : ℝ}
    (h : MatchesJets f p r N A t) (hk : k ≤ N) :
    TaylorModel.eval f p (point t k) u =
      (Hermite.initialPolynomial p (jet p r N A t k)).eval u := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv, Hermite.initialPolynomial_eval]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h k hk j (by have := Finset.mem_range.mp hj; omega)]
  ring

/-- The positive-side polynomial of the actual regularized model. -/
noncomputable def modelPolynomial (p r N : ℕ) (A t : ℝ) (k : ℕ) (σ : ℝ) : ℝ[X] :=
  Hermite.initialPolynomial p (jet p r N A t k) + C (σ / (p + 1).factorial) * X ^ (p + 1)

/-- At a positive scalar trial the actual model agrees with its polynomial expression. -/
theorem model_eq_polynomial {f : ℝ → ℝ} {p r N k : ℕ} {A t u : ℝ}
    (h : MatchesJets f p r N A t) (hk : k ≤ N) (σ : ℝ) (hu : 0 < u) :
    HighOrderRegularization.model f p (point t k) σ u =
      (modelPolynomial p r N A t k σ).eval u := by
  rw [HighOrderRegularization.model_eq, eval_of_matches h hk,
    Real.norm_eq_abs, abs_of_pos hu]
  simp [modelPolynomial]

/-- Every actual iterated model derivative at a positive step is the polynomial derivative. -/
theorem iteratedDeriv_model_eq {f : ℝ → ℝ} {p r N k : ℕ} {A t : ℝ}
    (h : MatchesJets f p r N A t) (hk : k ≤ N) (σ : ℝ) (ht : 0 < t) (j : ℕ) :
    iteratedDeriv j (HighOrderRegularization.model f p (point t k) σ) t =
      (derivative^[j] (modelPolynomial p r N A t k σ)).eval t := by
  have he : HighOrderRegularization.model f p (point t k) σ =ᶠ[nhds t]
      fun u => (modelPolynomial p r N A t k σ).eval u := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi ht] with u hu
    exact model_eq_polynomial h hk σ hu
  rw [he.iteratedDeriv_eq j]
  exact congrFun (Polynomial.iteratedDeriv_eval _ j) t

/-- Positive model derivatives have their exact two monomial coefficients. -/
theorem iteratedDeriv_model_formula {f : ℝ → ℝ} {p r N k j : ℕ} {A t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N A t)
    (hk : k < N) (σ : ℝ) (ht : 0 < t) (hj : 0 < j) :
    iteratedDeriv j (HighOrderRegularization.model f p (point t k) σ) t =
      -(r.descFactorial j : ℝ) * (A * t ^ balance p r / r.factorial) * t ^ (r - j) +
        σ / (p + 1).factorial * ((p + 1).descFactorial j : ℝ) * t ^ (p + 1 - j) := by
  rw [iteratedDeriv_model_eq h hk.le σ ht]
  simp only [modelPolynomial]
  simp_rw [← Module.End.pow_apply, map_add, Module.End.pow_apply]
  simp only [iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [initialPolynomial_derivative hr hrp hk hj]
  ring

/-- A common small coefficient makes all low-order model tests admissible. -/
noncomputable def coefficient (p : ℕ) : ℝ := 1 / ((p : ℝ) ^ 2 + 1)

/-- The fixed regularization parameter, independent of the requested accuracy. -/
noncomputable def parameter (p : ℕ) : ℝ := p.factorial * coefficient p

/-- The order-dependent monomial amplitude with the same fixed parameter. -/
noncomputable def amplitude (p r : ℕ) : ℝ := (r - 1).factorial * coefficient p

/-- The common coefficient is strictly positive. -/
theorem coefficient_pos (p : ℕ) : 0 < coefficient p := by unfold coefficient; positivity

/-- The chosen regularization parameter is strictly positive. -/
theorem parameter_pos (p : ℕ) : 0 < parameter p := by
  unfold parameter
  exact mul_pos (by positivity) (coefficient_pos p)

/-- Every positive-order amplitude is strictly positive. -/
theorem amplitude_pos (p r : ℕ) : 0 < amplitude p r := by
  unfold amplitude
  exact mul_pos (by positivity) (coefficient_pos p)

/-- Factorial normalization exactly balances the monomial and penalty derivatives. -/
theorem amplitude_div_factorial {r : ℕ} (hr : 0 < r) (p : ℕ) :
    amplitude p r / r.factorial = coefficient p / r := by
  have hf : (r.factorial : ℝ) = (r : ℝ) * (r - 1).factorial := by
    have he : r = (r - 1) + 1 := by omega
    have hn : r.factorial = r * (r - 1).factorial := by
      conv_lhs => rw [he, Nat.factorial_succ]
      rw [← he]
    exact_mod_cast hn
  unfold amplitude
  rw [hf]
  field_simp

/-- The exact first derivative of every nonterminal regularized model vanishes at the step. -/
theorem iteratedDeriv_model_one {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p)
    (h : MatchesJets f p r N (amplitude p r) t) (hk : k < N) (ht : 0 < t) :
    iteratedDeriv 1 (HighOrderRegularization.model f p (point t k) (parameter p)) t = 0 := by
  rw [iteratedDeriv_model_formula hr hrp h hk (parameter p) ht (by norm_num)]
  simp only [Nat.descFactorial_one, Nat.add_sub_cancel]
  have he : balance p r + (r - 1) = p := by dsimp [balance]; omega
  have hpen : parameter p / (p + 1).factorial * (p + 1 : ℕ) = coefficient p := by
    unfold parameter
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have hterm : -(r : ℝ) * (amplitude p r * t ^ balance p r / r.factorial) *
      t ^ (r - 1) = -coefficient p * t ^ p := by
    have ham : amplitude p r * t ^ balance p r / r.factorial =
        (coefficient p / r) * t ^ balance p r := by
      rw [← amplitude_div_factorial hr p]
      ring
    rw [ham]
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    have hpw : t ^ balance p r * t ^ (r - 1) = t ^ p := by rw [← pow_add, he]
    field_simp
    rw [← hpw]
    ring
  rw [hterm, hpen]
  ring

/-- Normalization cancels the leading factor of each monomial derivative. -/
theorem amplitude_descFactorial {r : ℕ} (hr : 0 < r) (p j : ℕ) :
    amplitude p r / r.factorial * (r.descFactorial (j + 1) : ℝ) =
      coefficient p * ((r - 1).descFactorial j : ℝ) := by
  have he : r = (r - 1) + 1 := by omega
  have hd : r.descFactorial (j + 1) = r * (r - 1).descFactorial j := by
    conv_lhs => rw [he, Nat.succ_descFactorial_succ]
    rw [← he]
  rw [amplitude_div_factorial hr p, hd, Nat.cast_mul]
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  field_simp

/-- The normalized penalty has the same coefficient for every positive derivative order. -/
theorem parameter_descFactorial (p j : ℕ) :
    parameter p / (p + 1).factorial * ((p + 1).descFactorial (j + 1) : ℝ) =
      coefficient p * (p.descFactorial j : ℝ) := by
  rw [Nat.succ_descFactorial_succ, Nat.cast_mul, Nat.factorial_succ]
  unfold parameter
  push_cast
  field_simp

/-- The exact positive-order model derivative factors into a difference of
actual descending-factorial monomial coefficients. -/
theorem iteratedDeriv_model_factored {f : ℝ → ℝ} {p r N k j : ℕ} {t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (hj : 0 < j)
    (h : MatchesJets f p r N (amplitude p r) t) (hk : k < N) (ht : 0 < t) :
    iteratedDeriv j (HighOrderRegularization.model f p (point t k) (parameter p)) t =
      coefficient p * ((p.descFactorial (j - 1) : ℝ) -
        ((r - 1).descFactorial (j - 1) : ℝ)) * t ^ (p + 1 - j) := by
  rw [iteratedDeriv_model_formula hr hrp h hk (parameter p) ht hj]
  have hjj : j - 1 + 1 = j := by omega
  have hp := parameter_descFactorial p (j - 1)
  rw [hjj] at hp
  rw [hp]
  have ha := amplitude_descFactorial hr p (j - 1)
  rw [hjj] at ha
  by_cases hjr : j ≤ r
  · have he : balance p r + (r - j) = p + 1 - j := by dsimp [balance]; omega
    have heq : -(r.descFactorial j : ℝ) * (amplitude p r * t ^ balance p r / r.factorial) *
        t ^ (r - j) =
        -(amplitude p r / r.factorial * (r.descFactorial j : ℝ)) * t ^ (p + 1 - j) := by
      rw [← he, pow_add]
      ring
    rw [heq, ha]
    ring
  · have hz : r.descFactorial j = 0 := Nat.descFactorial_of_lt (by omega)
    have hz' : (r - 1).descFactorial (j - 1) = 0 := Nat.descFactorial_of_lt (by omega)
    rw [hz, hz']
    simp

/-- Unit-scale spacing corresponding to a requested order-`r` accuracy. -/
noncomputable def root (p r : ℕ) (ε : ℝ) : ℝ := ε ^ ((balance p r : ℝ)⁻¹)

/-- Fixed spatial scaling makes the chosen small penalty stationary at the trial. -/
noncomputable def scale (p r : ℕ) : ℝ :=
  (2 / amplitude p r) ^ ((balance p r : ℝ)⁻¹)

/-- Actual step length in the lower-bound construction. -/
noncomputable def step (p r : ℕ) (ε : ℝ) : ℝ := scale p r * root p r ε

/-- The unit-scale spacing is positive for positive accuracy. -/
theorem root_pos (p r : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < root p r ε :=
  Real.rpow_pos_of_pos hε _

/-- Unit-scale spacing is at most one for unit-bounded accuracy. -/
theorem root_le_one (p r : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    root p r ε ≤ 1 := Real.rpow_le_one hε hε1 (by positivity)

/-- The fixed spatial scaling is positive. -/
theorem scale_pos (p r : ℕ) : 0 < scale p r :=
  Real.rpow_pos_of_pos (div_pos (by norm_num) (amplitude_pos p r)) _

/-- The actual scalar step is positive. -/
theorem step_pos (p r : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < step p r ε :=
  mul_pos (scale_pos p r) (root_pos p r hε)

/-- Balancing the actual step gives exactly twice the requested derivative accuracy. -/
theorem amplitude_step_power {p r : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    amplitude p r * step p r ε ^ balance p r = 2 * ε := by
  have hd : balance p r ≠ 0 := by dsimp [balance]; omega
  rw [step, mul_pow]
  have hs : scale p r ^ balance p r = 2 / amplitude p r :=
    Real.rpow_inv_natCast_pow (div_nonneg (by norm_num) (amplitude_pos p r).le) hd
  have hu : root p r ε ^ balance p r = ε := Real.rpow_inv_natCast_pow hε hd
  rw [hs, hu]
  have hA := (amplitude_pos p r).ne'
  field_simp

/-- The scalar balancing identity gives the exact source inverse-accuracy power. -/
theorem inverse_root_power {p r : ℕ} {ε : ℝ} (hε : 0 < ε) :
    1 / root p r ε ^ (p + 1) =
      ε ^ (-((p + 1 : ℕ) : ℝ) / balance p r) := by
  rw [root, ← Real.rpow_natCast, ← Real.rpow_mul hε.le,
    one_div, ← Real.rpow_neg hε.le]
  congr 1
  ring

/-- The count of trials is at least the exact printed inverse-accuracy power. -/
theorem inverse_accuracy_le_horizon {p r : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ε ^ (-((p + 1 : ℕ) : ℝ) / balance p r) ≤ (horizon p (root p r ε) : ℝ) := by
  rw [← inverse_root_power hε]
  exact Nat.le_ceil _

/-- All prescribed jets, values and highest-derivative Lipschitz constants are
uniform before the requested accuracy. -/
theorem exists_uniform_objectives_accuracy {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p) :
    ∃ (L : ℝ) (hL : 0 < L), ∃ B > 0,
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧
        LipschitzWith ⟨L, hL.le⟩ (iteratedDeriv p f) ∧
        MatchesJets f p r (horizon p (root p r ε)) (amplitude p r) (step p r ε) ∧
        ∀ j ≤ p, ∀ x, |iteratedDeriv j f x| ≤ B := by
  obtain ⟨L, hL, B, hB, hex⟩ := exists_uniform_objectives hr hrp
    (amplitude_pos p r).le (le_max_left 1 (scale p r))
    (C := 2 * scale p r ^ (p + 1))
  refine ⟨L, hL, B, hB, ?_⟩
  intro ε hε hε1
  apply hex (horizon p (root p r ε)) (horizon_pos p (root_pos p r hε))
    (step p r ε) (step_pos p r hε)
  · exact (mul_le_of_le_one_right (scale_pos p r).le
      (root_le_one p r hε.le hε1)).trans (le_max_right _ _)
  · have hh := horizon_mul_power_lt_two p (root_pos p r hε)
      (root_le_one p r hε.le hε1)
    have hm := mul_le_mul_of_nonneg_left hh.le
      (pow_nonneg (scale_pos p r).le (p + 1))
    simpa only [step, mul_pow, mul_left_comm, mul_comm, mul_assoc] using hm

/-- The fixed coefficient times either first or second descending factorial is at most one. -/
theorem coefficient_descFactorial_le_one {p : ℕ} (hp : 1 ≤ p) {j : ℕ}
    (hj : j = 1 ∨ j = 2) : coefficient p * (p.descFactorial j : ℝ) ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : (0 : ℝ) < (p : ℝ) ^ 2 + 1 := by positivity
  unfold coefficient
  rw [one_div_mul_eq_div, div_le_iff₀ hd]
  rcases hj with rfl | rfl
  · simp only [Nat.descFactorial_one]
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  · simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one, Nat.cast_mul]
    have hm : (p - 1 : ℕ) ≤ p := Nat.sub_le p 1
    have hmr : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hm
    nlinarith

/-- The leading descending-factorial coefficient dominates every lower-order one. -/
theorem descFactorial_monotone_low {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    {j : ℕ} (hj : j = 1 ∨ j = 2) : (r - 1).descFactorial j ≤ p.descFactorial j := by
  rcases hj with rfl | rfl
  · simpa only [Nat.descFactorial_one] using (Nat.sub_le r 1).trans hrp
  · simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one]
    exact Nat.mul_le_mul (by omega : r - 1 - 1 ≤ p - 1) (by omega : r - 1 ≤ p)

/-- The exact second or third scalar derivative lies between zero and the model-test budget. -/
theorem iteratedDeriv_model_bounds {f : ℝ → ℝ} {p r N k j : ℕ} {t : ℝ}
    (hp : j ≤ p) (hr : 0 < r) (hrp : r ≤ p) (hj : j = 2 ∨ j = 3)
    (h : MatchesJets f p r N (amplitude p r) t) (hk : k < N) (ht : 0 < t) :
    iteratedDeriv j (HighOrderRegularization.model f p (point t k) (parameter p)) t ∈
      Icc 0 (t ^ (p - j + 1)) := by
  rw [iteratedDeriv_model_factored hr hrp (by rcases hj with rfl | rfl <;> norm_num) h hk ht]
  have hj' : j - 1 = 1 ∨ j - 1 = 2 := by rcases hj with rfl | rfl <;> norm_num
  have hmono : ((r - 1).descFactorial (j - 1) : ℝ) ≤ p.descFactorial (j - 1) := by
    exact_mod_cast descFactorial_monotone_low hr hrp hj'
  have hc : 0 ≤ coefficient p * ((p.descFactorial (j - 1) : ℝ) -
      ((r - 1).descFactorial (j - 1) : ℝ)) :=
    mul_nonneg (coefficient_pos p).le (sub_nonneg.mpr hmono)
  have hc1 : coefficient p * ((p.descFactorial (j - 1) : ℝ) -
      ((r - 1).descFactorial (j - 1) : ℝ)) ≤ 1 := by
    apply le_trans _ (coefficient_descFactorial_le_one
      (by rcases hj with rfl | rfl <;> omega : 1 ≤ p) hj')
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (coefficient_pos p).le
  have he : p + 1 - j = p - j + 1 := by rcases hj with rfl | rfl <;> omega
  rw [he]
  exact ⟨mul_nonneg hc (by positivity),
    mul_le_of_le_one_left (by positivity) hc1⟩

/-- Exact stationarity implies the first-order model test at every positive model degree. -/
theorem model_first_test {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p)
    (h : MatchesJets f p r N (amplitude p r) t) (hk : k < N) (ht : 0 < t) :
    ‖fderiv ℝ (HighOrderRegularization.model f p (point t k) (parameter p)) t‖ ≤
      (1 : ℝ) * ‖t‖ ^ p := by
  rw [← norm_deriv_eq_norm_fderiv, ← iteratedDeriv_one,
    iteratedDeriv_model_one hr hrp h hk ht, norm_zero]
  positivity

/-- Nonnegative actual model curvature gives the legal second-order model test. -/
theorem model_second_test {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hp : 2 ≤ p) (hr : 0 < r) (hrp : r ≤ p)
    (h : MatchesJets f p r N (amplitude p r) t) (hk : k < N) (ht : 0 < t)
    (v : ℝ) (hv : ‖v‖ = 1) :
    -(1 : ℝ) * ‖t‖ ^ (p - 1) ≤
      iteratedFDeriv ℝ 2 (HighOrderRegularization.model f p (point t k) (parameter p))
        t (fun _ => v) := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_const, smul_eq_mul]
  have hv2 : v ^ 2 = 1 := by
    nlinarith [sq_abs v, show |v| = 1 by exact hv]
  rw [hv2, one_mul]
  have hh := iteratedDeriv_model_bounds hp hr hrp (Or.inl rfl) h hk ht
  exact (show -(1 : ℝ) * ‖t‖ ^ (p - 1) ≤ 0 by
    nlinarith [pow_nonneg (norm_nonneg t) (p - 1)]).trans hh.1

/-- The actual third model derivative obeys its legal directional tolerance. -/
theorem model_third_test {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hp : 3 ≤ p) (hr : 0 < r) (hrp : r ≤ p)
    (h : MatchesJets f p r N (amplitude p r) t) (hk : k < N) (ht : 0 < t)
    (v : ℝ) (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ 3 (HighOrderRegularization.model f p (point t k) (parameter p))
      t (fun _ => v)| ≤ (1 : ℝ) * ‖t‖ ^ (p - 2) := by
  have hh := iteratedDeriv_model_bounds hp hr hrp (Or.inr rfl) h hk ht
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_const, smul_eq_mul,
    abs_mul, abs_pow, show |v| = 1 by exact hv, one_pow, one_mul,
    abs_of_nonneg hh.1, one_mul, Real.norm_eq_abs, abs_of_pos ht]
  simpa only [show p - 3 + 1 = p - 2 by omega] using hh.2

/-- The actual models satisfy all three source tests with legal unit tolerances. -/
theorem stepConditions_of_matches {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hp : 3 ≤ p) (hr : 0 < r) (hrp : r ≤ p)
    (h : MatchesJets f p r N (amplitude p r) t) (hk : k < N) (ht : 0 < t) :
    HighOrderRegularization.StepConditions f p (point t k) t (parameter p) 1 1 1 :=
  ⟨model_first_test hr hrp h hk ht,
    model_second_test (by omega) hr hrp h hk ht,
    fun v hv => model_third_test hp hr hrp h hk ht v hv.1⟩

/-- Every unit scalar direction belongs to the small-curvature set of the actual model. -/
theorem smallModelDirections_eq {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hp : 2 ≤ p) (hr : 0 < r) (hrp : r ≤ p)
    (h : MatchesJets f p r N (amplitude p r) t) (hk : k < N) (ht : 0 < t) :
    HighOrderRegularization.smallModelDirections f p (point t k) t (parameter p) 1 =
      {v : ℝ | ‖v‖ = 1} := by
  ext v
  constructor
  · exact fun hv => hv.1
  · intro hv
    refine ⟨hv, ?_⟩
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_const, smul_eq_mul,
      abs_mul, abs_pow, show |v| = 1 by exact hv, one_pow, one_mul, one_mul,
      Real.norm_eq_abs, abs_of_pos ht]
    have hh := iteratedDeriv_model_bounds (by omega : 2 ≤ p) hr hrp (Or.inl rfl) h hk ht
    rw [abs_of_nonneg hh.1]
    simpa only [show p - 2 + 1 = p - 1 by omega] using hh.2

/-- The actual objective value at a matched interpolation node. -/
theorem MatchesJets.value_eq {f : ℝ → ℝ} {p r N k : ℕ} {A t : ℝ}
    (h : MatchesJets f p r N A t) (hk : k ≤ N) :
    f (point t k) = jet p r N A t k 0 := by simpa using h k hk 0 (Nat.zero_le p)

/-- The true Taylor polynomial predicts exactly the next prescribed objective value. -/
theorem eval_step_of_matches {f : ℝ → ℝ} {p r N k : ℕ} {A t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N A t) (hk : k < N) :
    TaylorModel.eval f p (point t k) t = f (point t (k + 1)) := by
  rw [eval_of_matches h hk.le, h.value_eq (by omega)]
  linarith [objective_residual_zero hr hrp hk A t]

/-- Every nonterminal actual objective drop is the positive prescribed monomial drop. -/
theorem objective_drop_of_matches {f : ℝ → ℝ} {p r N k : ℕ} {A t : ℝ}
    (h : MatchesJets f p r N A t) (hk : k < N) :
    f (point t k) - f (point t (k + 1)) = drop p r A t := by
  rw [h.value_eq hk.le, h.value_eq (by omega)]
  simp only [jet, ite_true]
  have hn : ((N - k : ℕ) : ℝ) = ((N - (k + 1) : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show N - k = N - (k + 1) + 1 by omega)
  rw [hn]
  ring

/-- The fixed normalized regularization coefficient. -/
theorem parameter_div_factorial (p : ℕ) :
    parameter p / (p + 1).factorial = coefficient p / (p + 1 : ℕ) := by
  unfold parameter
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The actual regularized model strictly decreases at every constructed nonterminal step. -/
theorem model_improves_of_matches {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N (amplitude p r) t)
    (hk : k < N) (ht : 0 < t) :
    HighOrderRegularization.model f p (point t k) (parameter p) t <
      HighOrderRegularization.model f p (point t k) (parameter p) 0 := by
  have hc : parameter p / (p + 1).factorial < amplitude p r / r.factorial := by
    rw [parameter_div_factorial, amplitude_div_factorial hr]
    push_cast
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < p + 1)
      (by positivity : (0 : ℝ) < r)).2
    have hpr : (r : ℝ) < p + 1 := by exact_mod_cast (show r < p + 1 by omega)
    exact mul_lt_mul_of_pos_left hpr (coefficient_pos p)
  have hm := mul_lt_mul_of_pos_right hc (show 0 < t ^ (p + 1) by positivity)
  rw [HighOrderRegularization.model_eq, HighOrderRegularization.model_zero,
    eval_step_of_matches hr hrp h hk, Real.norm_eq_abs, abs_of_pos ht]
  have hd := objective_drop_of_matches h hk
  dsimp [drop] at hd
  linarith

/-- Every constructed trial has actual objective acceptance ratio exactly one. -/
theorem ratio_eq_one_of_matches {f : ℝ → ℝ} {p r N k : ℕ} {t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N (amplitude p r) t)
    (hk : k < N) (ht : 0 < t) :
    HighOrderRegularization.ratio f p (point t k) t = 1 := by
  have hd := HighOrderRegularization.decrement_pos (parameter_pos p).le
    (model_improves_of_matches hr hrp h hk ht)
  rw [HighOrderRegularization.ratio, TaylorModel.decrement_eq,
    eval_step_of_matches hr hrp h hk, ← point_succ]
  apply div_self
  rw [TaylorModel.decrement_eq, eval_step_of_matches hr hrp h hk] at hd
  exact hd.ne'

/-- The constructed objective gives a genuine model/ratio/update trace with fixed legal settings. -/
theorem modelTrace_of_matches {f : ℝ → ℝ} {p r N : ℕ} {t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N (amplitude p r) t)
    (ht : 0 < t) :
    HighOrderRegularization.ModelTrace f p (point t) (fun _ => t)
      (fun _ => parameter p) (fun _ => 1)
      (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) N := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · refine ⟨parameter_pos p, le_rfl, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro k hk
    norm_num only
    exact ⟨max_le le_rfl (by linarith [parameter_pos p]), le_rfl⟩
  · intro k hk
    exact model_improves_of_matches hr hrp h hk ht
  · intro k hk
    exact (ratio_eq_one_of_matches hr hrp h hk ht).symm
  · intro k hk
    norm_num only
    exact point_succ t k

end HighOrderRegularization.Sharpness
