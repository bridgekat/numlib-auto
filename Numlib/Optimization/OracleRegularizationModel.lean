import Numlib.Optimization.DerivativeOracleMethods
import Numlib.Optimization.HigherOrderApproximateRegularization
import Numlib.Optimization.TaylorModelRemainder

/-!
# Regularized models from raw derivative replies

A finite collection of continuous multilinear tensors defines a polynomial even when the
collection is not the jet of any objective. Positive radial regularization gives an attained
global minimum in every finite Euclidean dimension. The deterministic selection below is
therefore defined before an objective is supplied.
-/

noncomputable section
open scoped Nat ContDiff
namespace Optimization.DerivativeOracle
open ZeroChains RegularizedTaylorModel

variable {n p : ℕ}

/-- The polynomial encoded by a raw oracle reply, including its constant coefficient. -/
def Reply.taylor (R : Reply n p) (s : Space n) : ℝ :=
  R.value + ∑ q : Fin p, ((q.val + 1)! : ℝ)⁻¹ * R.derivative q (fun _ => s)

/-- Factorial-normalized radial regularization of the raw polynomial. -/
def Reply.model (R : Reply n p) (sigma : ℝ) (s : Space n) : ℝ :=
  R.taylor s + sigma / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)

/-- The raw polynomial retains the reply's value at zero displacement. -/
@[simp] theorem Reply.taylor_zero (R : Reply n p) : R.taylor 0 = R.value := by
  classical
  simp only [Reply.taylor]
  have hz (q : Fin p) : R.derivative q (fun _ => (0 : Space n)) = 0 :=
    (R.derivative q).map_coord_zero (0 : Fin (q.val + 1)) rfl
  simp [hz]

/-- Radial regularization preserves the constant coefficient. -/
@[simp] theorem Reply.model_zero (R : Reply n p) (sigma : ℝ) :
    R.model sigma 0 = R.value := by simp [Reply.model]

/-- For an actual reply the raw polynomial is exactly the objective's Taylor model. -/
theorem oracle_taylor (f : Space n → ℝ) (x s : Space n) :
    (oracle p f x).taylor s = taylorModel f p x s := by
  rw [taylorModel, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply]
  rw [add_comm]
  unfold Reply.taylor
  simp only [oracle_value, oracle_derivative, smul_eq_mul]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun j => ((j + 1)! : ℝ)⁻¹ * iteratedFDeriv ℝ (j + 1) f x (fun _ => s)) p


/-- Actual replies give precisely the canonical regularized Taylor model. -/
theorem oracle_model (f : Space n → ℝ) (x : Space n) (sigma : ℝ) :
    (oracle p f x).model sigma = HigherOrderRegularization.model f p x sigma := by
  funext s
  simp only [Reply.model, oracle_taylor, HigherOrderRegularization.model]

/-- Every raw reply defines a smooth polynomial, without symmetry or realizability assumptions. -/
theorem Reply.contDiff_taylor (R : Reply n p) (k : ℕ∞ω) : ContDiff ℝ k R.taylor := by
  unfold Reply.taylor
  apply contDiff_const.add
  apply ContDiff.sum
  intro q _
  exact contDiff_const.mul ((R.derivative q).contDiff.comp
    (contDiff_pi.mpr fun _ : Fin (q.val + 1) => contDiff_id))

/-- A coefficient-norm bound for a raw polynomial outside the unit ball. -/
theorem Reply.abs_taylor_le (R : Reply n p) (s : Space n) (hs : 1 ≤ ‖s‖) :
    |R.taylor s| ≤ (|R.value| + ∑ q : Fin p,
      ((q.val + 1)! : ℝ)⁻¹ * ‖R.derivative q‖) * ‖s‖ ^ p := by
  classical
  rw [Reply.taylor, add_mul, Finset.sum_mul]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ hs)
  · rw [← Real.norm_eq_abs]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q _
    rw [norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity :
      (0 : ℝ) < ((q.val + 1)! : ℝ))]
    have hA := (R.derivative q).le_opNorm (fun _ => s)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hA
    calc
      _ ≤ ((q.val + 1)! : ℝ)⁻¹ * (‖R.derivative q‖ * ‖s‖ ^ (q.val + 1)) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ ≤ ((q.val + 1)! : ℝ)⁻¹ * (‖R.derivative q‖ * ‖s‖ ^ p) := by
        gcongr
        exact q.isLt
      _ = _ := by ring

/-- Positive regularization dominates every raw polynomial, including inconsistent replies. -/
theorem Reply.model_eventually_ge (R : Reply n p) {sigma : ℝ} (hsigma : 0 < sigma)
    (b : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : Space n, B ≤ ‖s‖ → b ≤ R.model sigma s := by
  exact eventually_ge_regularized_of_lower_bound p (div_pos hsigma (by positivity))
    (fun s hs => (abs_le.mp (R.abs_taylor_le s hs)).1) b

/-- The regularized raw polynomial has an attained global minimum. -/
theorem Reply.exists_model_minimizer (R : Reply n p) {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ s : Space n, ∀ t, R.model sigma s ≤ R.model sigma t := by
  have hc : Continuous (R.model sigma) := (R.contDiff_taylor 0).continuous.add
    (continuous_const.mul (continuous_norm.pow _))
  obtain ⟨B, hB, hb⟩ := R.model_eventually_ge hsigma R.value
  obtain ⟨s, _, hmin⟩ := (isCompact_closedBall (0 : Space n) B).exists_isMinOn
    ⟨0, by simpa using hB⟩ hc.continuousOn
  refine ⟨s, fun t => ?_⟩
  by_cases ht : ‖t‖ ≤ B
  · exact hmin (by simpa using ht)
  · have hzero := hmin (show (0 : Space n) ∈ Metric.closedBall 0 B by simpa using hB)
    have hsz : R.model sigma s ≤ R.value := by simpa using hzero
    exact hsz.trans (hb t (le_of_lt (lt_of_not_ge ht)))

open Classical in
/-- A deterministic global-minimum step, with zero as total continuation for nonpositive
regularization. This rule uses the raw reply alone. -/
def Reply.minimizer (R : Reply n p) (sigma : ℝ) : Space n :=
  if hsigma : 0 < sigma then (R.exists_model_minimizer hsigma).choose else 0

/-- The selected step minimizes the actual raw model at every positive parameter. -/
theorem Reply.minimizer_le (R : Reply n p) {sigma : ℝ} (hsigma : 0 < sigma)
    (t : Space n) : R.model sigma (R.minimizer sigma) ≤ R.model sigma t := by
  classical
  simp only [Reply.minimizer, dite_eq_left hsigma]
  exact (R.exists_model_minimizer hsigma).choose_spec t

/-- The selected minimizer of an actual reply has zero model derivative. -/
theorem oracle_minimizer_fderiv (f : Space n → ℝ) (x : Space n) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    fderiv ℝ (HigherOrderRegularization.model f p x sigma)
      ((oracle p f x).minimizer sigma) = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  apply IsMinOn.isLocalMin (s := Set.univ) _ (by simp)
  intro t _
  change HigherOrderRegularization.model f p x sigma ((oracle p f x).minimizer sigma) ≤
    HigherOrderRegularization.model f p x sigma t
  simpa only [← oracle_model] using (oracle p f x).minimizer_le hsigma t

/-- At positive degree, the actual regularized model has the objective derivative at zero. -/
theorem fderiv_model_zero {f : Space n → ℝ} (hp : 1 ≤ p) (hf : ContDiff ℝ p f)
    (x : Space n) (sigma : ℝ) :
    fderiv ℝ (HigherOrderRegularization.model f p x sigma) 0 = fderiv ℝ f x := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have he : HigherOrderRegularization.model f (q + 1) x sigma =
      regularizedModel f (q + 1) x sigma ((q + 2)! : ℝ) ((q + 2 : ℕ) : ℝ) := by
    funext s
    simp only [HigherOrderRegularization.model, regularizedModel, Real.rpow_natCast]
  rw [he, fderiv_regularizedModel _ _ _ _ _ _ (by exact_mod_cast (by omega : 1 < q + 2)),
    fderiv_taylorModel_eq_taylorModel_fderiv hf.contDiffAt, taylorModel_zero,
    fderiv_norm_rpow _ (by exact_mod_cast (by omega : 1 < q + 2))]
  simp

/-- A nonstationary actual objective forces strict model decrease at its selected minimum. -/
theorem oracle_minimizer_strict {f : Space n → ℝ} (hp : 1 ≤ p)
    (hf : ContDiff ℝ p f) (x : Space n) {sigma : ℝ} (hsigma : 0 < sigma)
    (hgrad : fderiv ℝ f x ≠ 0) :
    HigherOrderRegularization.model f p x sigma ((oracle p f x).minimizer sigma) <
      HigherOrderRegularization.model f p x sigma 0 := by
  have hle := (oracle p f x).minimizer_le hsigma 0
  rw [oracle_model] at hle
  apply lt_of_le_of_ne hle
  intro heq
  have hm : IsLocalMin (HigherOrderRegularization.model f p x sigma) 0 := by
    apply IsMinOn.isLocalMin (s := Set.univ) _ (by simp)
    intro t _
    change HigherOrderRegularization.model f p x sigma 0 ≤
      HigherOrderRegularization.model f p x sigma t
    rw [← heq]
    simpa only [← oracle_model] using (oracle p f x).minimizer_le hsigma t
  exact hgrad ((fderiv_model_zero hp hf x sigma).symm.trans hm.fderiv_eq_zero)

end Optimization.DerivativeOracle
