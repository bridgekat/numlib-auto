import Numlib.Optimization.Regularization.HighOrder.Sharpness.CriticalityExecution
import Numlib.Optimization.Regularization.GlobalStep.PositiveFraction
import Numlib.Optimization.HighOrder.CriticalityNorm

/-!
# Unit-radius sharpness candidates by highest-derivative cancellation

A nonstationary candidate cancels the actual highest model derivative. Lower derivative
bounds give every literal unit-radius model test and strict improvement gives a genuine
positive global fraction.
-/

namespace HighOrderRegularization.Sharpness
/-- The monomial amplitude whose highest tested model derivative cancels at the positive trial. -/
noncomputable def cancellationAmplitude (p q : ℕ) (σ : ℝ) : ℝ := σ / (p + 1 - q).factorial
/-- The normalized penalty coefficient at the tested derivative order equals the prescribed
amplitude. -/
theorem cancellation_coefficient {p q : ℕ} (hqp : q ≤ p) (σ : ℝ) :
    σ / (p + 1).factorial * ((p + 1).descFactorial q : ℝ) = cancellationAmplitude p q σ := by
  have hh : ((p + 1 - q).factorial : ℝ) * ((p + 1).descFactorial q : ℝ) =
      (p + 1).factorial := by exact_mod_cast Nat.factorial_mul_descFactorial (by omega : q ≤ p + 1)
  unfold cancellationAmplitude
  field_simp
  calc σ * ((p + 1).descFactorial q : ℝ) * ((p + 1 - q).factorial : ℝ) =
      σ * (((p + 1 - q).factorial : ℝ) * ((p + 1).descFactorial q : ℝ)) := by ring
    _ = _ := by rw [hh]
/-- The actual highest tested derivative of the regularized model vanishes at the chosen
positive step. -/
theorem highest_model_derivative_zero {f : ℝ → ℝ} {p q N k : ℕ} {σ t : ℝ}
    (hq : 0 < q) (hqp : q ≤ p)
    (h : MatchesJets f p q N (cancellationAmplitude p q σ) t) (hk : k < N) (ht : 0 < t) :
    iteratedDeriv q (HighOrderRegularization.model f p (point t k) σ) t = 0 := by
  rw [iteratedDeriv_model_formula hq hqp h hk σ ht hq,
    Nat.descFactorial_self, cancellation_coefficient hqp]
  simp only [Nat.sub_self, pow_zero, mul_one]
  dsimp [balance]
  rw [show p + 1 - q = p - q + 1 by omega]
  have hfac : (q.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring
end HighOrderRegularization.Sharpness
namespace HighOrderRegularization.Sharpness
/-- The descending-factorial coefficient normalized by the full factorial is at most one. -/
theorem descFactorial_div_factorial_le_one {n j : ℕ} (hj : j ≤ n) :
    (n.descFactorial j : ℝ) / n.factorial ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < n.factorial)).mpr
  exact_mod_cast (show n.descFactorial j ≤ n.factorial by
    have hh := Nat.factorial_mul_descFactorial hj
    have hf := Nat.factorial_pos (n - j)
    nlinarith)
/-- Every lower positive model derivative has one extra small spatial factor after the
highest derivative cancels. -/
theorem lower_model_derivative_bound {f : ℝ → ℝ} {p q N k j : ℕ} {σ t : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (hσ : 0 ≤ σ)
    (h : MatchesJets f p q N (cancellationAmplitude p q σ) t) (hk : k < N)
    (ht : 0 < t) (ht1 : t ≤ 1) (hj : 0 < j) (hjq : j < q) :
    |iteratedDeriv j (HighOrderRegularization.model f p (point t k) σ) t| ≤
      (cancellationAmplitude p q σ + σ) * t ^ balance p q * t := by
  let A := cancellationAmplitude p q σ
  have hA : 0 ≤ A := by dsimp [A, cancellationAmplitude]; positivity
  rw [iteratedDeriv_model_formula hq hqp h hk σ ht hj]
  have hpw : balance p q + (q - j) = p + 1 - j := by dsimp [balance]; omega
  have heq : -(q.descFactorial j : ℝ) * (A * t ^ balance p q / q.factorial) *
      t ^ (q - j) = -((q.descFactorial j : ℝ) / q.factorial * A * t ^ (p + 1 - j)) := by
    rw [← hpw, pow_add]
    ring
  change |-(q.descFactorial j : ℝ) * (A * t ^ balance p q / q.factorial) *
    t ^ (q - j) + _| ≤ (A + σ) * t ^ balance p q * t
  rw [heq]
  have hpow : t ^ (p + 1 - j) ≤ t ^ (balance p q + 1) :=
    pow_le_pow_of_le_one ht.le ht1 (by dsimp [balance]; omega)
  have hqj := descFactorial_div_factorial_le_one (by omega : j ≤ q)
  have hpj := descFactorial_div_factorial_le_one (by omega : j ≤ p + 1)
  calc _ ≤ |-((q.descFactorial j : ℝ) / q.factorial * A * t ^ (p + 1 - j))| +
      |σ / (p + 1).factorial * ((p + 1).descFactorial j : ℝ) * t ^ (p + 1 - j)| :=
        abs_add_le _ _
    _ = (q.descFactorial j : ℝ) / q.factorial * A * t ^ (p + 1 - j) +
      ((p + 1).descFactorial j : ℝ) / (p + 1).factorial * σ * t ^ (p + 1 - j) := by
        rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        ring
    _ ≤ 1 * A * t ^ (balance p q + 1) + 1 * σ * t ^ (balance p q + 1) := by gcongr
    _ = _ := by rw [pow_succ]; ring
/-- An interior factorial split is strictly smaller than the full factorial. -/
theorem factorial_split_lt {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) :
    q.factorial * (p + 1 - q).factorial < (p + 1).factorial := by
  have hchoose : 1 < (p + 1).choose q := by
    have hpos := Nat.choose_pos (by omega : q ≤ p + 1)
    have hne : (p + 1).choose q ≠ 1 := by
      intro he
      have hh := Nat.choose_eq_one_iff.mp he
      omega
    omega
  have heq := Nat.choose_mul_factorial_mul_factorial (by omega : q ≤ p + 1)
  have hfac : 0 < q.factorial * (p + 1 - q).factorial := by positivity
  nlinarith
/-- The cancellation candidate strictly improves the actual regularized model. -/
theorem cancellation_model_improves {f : ℝ → ℝ} {p q N k : ℕ} {σ t : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (hσ : 0 < σ)
    (h : MatchesJets f p q N (cancellationAmplitude p q σ) t) (hk : k < N)
    (ht : 0 < t) :
    HighOrderRegularization.model f p (point t k) σ t <
      HighOrderRegularization.model f p (point t k) σ 0 := by
  have hc : σ / (p + 1).factorial < cancellationAmplitude p q σ / q.factorial := by
    unfold cancellationAmplitude
    rw [div_div]
    apply div_lt_div_of_pos_left hσ (by positivity)
    have hh := factorial_split_lt hq hqp
    rw [Nat.mul_comm] at hh
    exact_mod_cast hh
  have hm := mul_lt_mul_of_pos_right hc (show 0 < t ^ (p + 1) by positivity)
  rw [HighOrderRegularization.model_eq, HighOrderRegularization.model_zero,
    eval_step_of_matches hq hqp h hk, Real.norm_eq_abs, abs_of_pos ht]
  have hd := objective_drop_of_matches h hk
  dsimp [drop] at hd
  linarith
end HighOrderRegularization.Sharpness
namespace HighOrderRegularization.Sharpness
/-- All genuine unit-ball model Taylor criticalities have a common bound with an extra
spatial factor. -/
theorem cancellation_model_criticality_bound {f : ℝ → ℝ} {p q N k j : ℕ} {σ t : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (hσ : 0 ≤ σ)
    (h : MatchesJets f p q N (cancellationAmplitude p q σ) t) (hk : k < N)
    (ht : 0 < t) (ht1 : t ≤ 1) (hjq : j ≤ q) :
    TaylorModel.criticality (HighOrderRegularization.model f p (point t k) σ) j t 1 ≤
      q * ((cancellationAmplitude p q σ + σ) * t ^ balance p q * t) := by
  have hA : 0 ≤ cancellationAmplitude p q σ := by unfold cancellationAmplitude; positivity
  have hU : 0 ≤ (cancellationAmplitude p q σ + σ) * t ^ balance p q * t := by positivity
  apply (TaylorModel.criticality_unit_le_of_scalar_jets _ j t hU ?_).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hjq) hU)
  intro a ha haj
  by_cases haq : a = q
  · subst a
    rw [highest_model_derivative_zero hq hqp h hk ht, abs_zero]
    exact hU
  · exact lower_model_derivative_bound hq hqp hσ h hk ht ht1 ha
      (lt_of_le_of_ne (haj.trans hjq) haq)
/-- The actual cancellation candidate satisfies every primitive Step2 condition with unit
radii and no reductions. -/
theorem cancellation_stepComputation {f : ℝ → ℝ} {p q N k : ℕ} {σ t ε : ℝ}
    (hq : 0 < q) (hqp : q ≤ p) (hσ : 0 < σ)
    (h : MatchesJets f p q N (cancellationAmplitude p q σ) t) (hk : k < N)
    (ht : 0 < t) (ht1 : t ≤ 1) (hε : 0 ≤ ε)
    (hsmall : (q : ℝ) * ((cancellationAmplitude p q σ + σ) * t ^ balance p q * t) ≤
      (1 / 2) * ε / q.factorial) :
    ModelSolve.StepComputation (HighOrderRegularization.model f p (point t k) σ)
      InexactTrustRegion.modelOrder (1 / 2) 1 (fun _ : Fin q => ε) t (fun _ => 1) := by
  classical
  let m := HighOrderRegularization.model f p (point t k) σ
  have hfrac : ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ModelDecrease.ApproximateGlobalStep m μ t := by
    obtain ⟨z, hz⟩ := ModelDecrease.exists_minimizer_ofJet (ftaylorSeries ℝ f (point t k)) p hσ
    exact ModelDecrease.exists_positive_fraction_of_strict_decrease hz
      (cancellation_model_improves hq hqp hσ h hk ht)
  have hlast := fun a : Fin q => TaylorModel.exists_decrement_eq_criticality
    m (InexactTrustRegion.modelOrder a) t (by norm_num : (0 : ℝ) ≤ 1)
  choose last hlast_feasible hlast_eq using hlast
  refine ⟨hfrac, Or.inr ⟨by simpa only [Real.norm_eq_abs, abs_of_pos ht] using ht1,
    (fun _ _ => t), (fun _ _ => 0), (fun _ => 0), last, ?_⟩⟩
  intro a
  refine ⟨fun _ ht => (Nat.not_lt_zero _ ht).elim, ?_, fun _ => rfl, ?_,
    hlast_feasible a, ?_, ?_⟩
  · exact ⟨fun _ ht => (Nat.not_lt_zero _ ht).elim,
      fun _ ht => (Nat.not_lt_zero _ ht).elim,
      fun _ ht => (Nat.not_lt_zero _ ht).elim⟩
  · simp
  · rw [hlast_eq a, one_mul]
  · rw [hlast_eq a]
    simp only [one_mul, one_pow, mul_one]
    have hle := (cancellation_model_criticality_bound hq hqp hσ.le h hk ht ht1
      (show InexactTrustRegion.modelOrder a ≤ q from a.isLt)).trans hsmall
    have hf : ((InexactTrustRegion.modelOrder a).factorial : ℝ) ≤ q.factorial :=
      by exact_mod_cast Nat.factorial_le (show InexactTrustRegion.modelOrder a ≤ q from a.isLt)
    have he : 0 ≤ (1 / 2 : ℝ) * ε := by positivity
    exact hle.trans (div_le_div_of_nonneg_left he (by positivity) hf)
end HighOrderRegularization.Sharpness
