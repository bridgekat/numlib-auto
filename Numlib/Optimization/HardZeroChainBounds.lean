import Numlib.Analysis.FlatGaussianBounds
import Numlib.Optimization.HardZeroChain

/-!
# Uniform scalar derivative estimates for the explicit Gaussian chain

The constants below are explicit and independent of the derivative order and of
any chain dimension. These scalar bounds do not assert the full mixed-tensor
Lipschitz estimate for the finite chain.
-/

noncomputable section
open Real Analysis.FlatGaussian

namespace Optimization.HardZeroChain

/-- Each derivative of the switch is the rescaled actual cutoff derivative. -/
theorem iteratedDeriv_psi (n : ℕ) (x : ℝ) :
    iteratedDeriv n psi x = exp 1 * ((2 : ℝ) ^ n * iteratedDeriv n cutoff (2 * x - 1)) := by
  unfold psi
  rw [iteratedDeriv_const_mul_field]
  have hs : ContDiff ℝ (n : ℕ) (fun z : ℝ ↦ cutoff (z - 1)) :=
    contDiff_cutoff.comp (by fun_prop)
  rw [show (fun y : ℝ ↦ cutoff (2 * y - 1)) =
      (fun y ↦ (fun z ↦ cutoff (z - 1)) (2 * y)) from rfl,
    iteratedDeriv_comp_const_mul hs (2 : ℝ), iteratedDeriv_comp_sub_const]

/-- Every positive-order switch derivative has a uniform explicit growth bound. -/
theorem norm_iteratedDeriv_psi_le {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ‖iteratedDeriv n psi x‖ ≤
      exp ((5 / 2 : ℝ) * n * log n + (1 + log 2 + (5 / 2 : ℝ) * log 3) * n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [iteratedDeriv_psi, norm_mul, norm_mul, norm_of_nonneg (exp_pos _).le,
    norm_pow, Real.norm_ofNat]
  calc
    _ ≤ exp 1 * ((2 : ℝ) ^ n *
        exp ((5 / 2 : ℝ) * n * log n + ((5 / 2 : ℝ) * log 3) * n)) := by
      gcongr
      exact norm_iteratedDeriv_cutoff_le hn (2 * x - 1)
    _ = exp (1 + (n : ℝ) * log 2 +
        ((5 / 2 : ℝ) * n * log n + ((5 / 2 : ℝ) * log 3) * n)) := by
      rw [show (2 : ℝ) ^ n = exp ((n : ℝ) * log 2) by
        rw [exp_nat_mul, exp_log (by norm_num)], ← exp_add, ← exp_add]
      congr 1
      ring
    _ ≤ _ := exp_le_exp.mpr (by nlinarith)

/-- The primitive factor obeys the same uniform growth bound as the switch. -/
theorem norm_iteratedDeriv_phi_le {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ‖iteratedDeriv n phi x‖ ≤
      exp ((5 / 2 : ℝ) * n * log n + (1 + log 2 + (5 / 2 : ℝ) * log 3) * n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (norm_iteratedDeriv_primitive_le hn x).trans
  apply exp_le_exp.mpr
  have hlogn := log_nonneg hn1
  have hlog3 : 0 ≤ log (3 : ℝ) := log_nonneg (by norm_num)
  nlinarith

/-- A single positive constant bounds all positive scalar derivative orders simultaneously. -/
theorem scalar_uniform_derivative_bounds :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      ‖iteratedDeriv n psi x‖ ≤ exp ((5 / 2 : ℝ) * n * log n + c * n) ∧
      ‖iteratedDeriv n phi x‖ ≤ exp ((5 / 2 : ℝ) * n * log n + c * n) := by
  refine ⟨1 + log 2 + (5 / 2 : ℝ) * log 3, ?_, fun n hn x ↦
    ⟨norm_iteratedDeriv_psi_le hn x, norm_iteratedDeriv_phi_le hn x⟩⟩
  have hlog2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hlog3 : 0 ≤ log (3 : ℝ) := log_nonneg (by norm_num)
  positivity

/-- One constant also bounds order zero and every derivative below a chosen positive order.
The exponent keeps the actual derivative order in front of `log p`, so products of
complementary derivative orders retain the required `p log p` growth. -/
theorem scalar_derivative_bounds_up_to :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ p : ℕ, 1 ≤ p → ∀ n : ℕ, n ≤ p → ∀ x : ℝ,
      ‖iteratedDeriv n psi x‖ ≤ exp ((5 / 2 : ℝ) * n * log p + c * (n + 1)) ∧
      ‖iteratedDeriv n phi x‖ ≤ exp ((5 / 2 : ℝ) * n * log p + c * (n + 1)) := by
  obtain ⟨c, hc, hb⟩ := scalar_uniform_derivative_bounds
  refine ⟨max 12 c, (by simp), fun p _ n hn x ↦ ?_⟩
  by_cases hzero : n = 0
  · subst n
    simp only [iteratedDeriv_zero, Nat.cast_zero, mul_zero, zero_mul, zero_add, mul_one]
    constructor
    · rw [norm_of_nonneg (psi_nonneg x)]
      exact (psi_le_exp_one x).trans (exp_le_exp.mpr (by simp))
    · rw [norm_of_nonneg (primitive_pos x).le]
      have hphi : phi x ≤ 12 := by simpa using psi_mul_phi_le_twelve 1 x
      have h12 : (12 : ℝ) ≤ exp 12 := by linarith [add_one_le_exp (12 : ℝ)]
      exact hphi.trans (h12.trans (exp_le_exp.mpr (le_max_left _ _)))
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hzero
    have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1
    have hlog : log (n : ℝ) ≤ log (p : ℝ) := log_le_log hnpos (by exact_mod_cast hn)
    have hexp : exp ((5 / 2 : ℝ) * n * log n + c * n) ≤
        exp ((5 / 2 : ℝ) * n * log p + max 12 c * (n + 1)) := by
      apply exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (5 / 2 : ℝ) * n by positivity)
      have hc' := mul_le_mul_of_nonneg_right (le_max_right 12 c) hnpos.le
      have hmax : (0 : ℝ) ≤ max 12 c := by positivity
      nlinarith
    exact ⟨((hb n hn1 x).1).trans hexp, ((hb n hn1 x).2).trans hexp⟩

end Optimization.HardZeroChain
