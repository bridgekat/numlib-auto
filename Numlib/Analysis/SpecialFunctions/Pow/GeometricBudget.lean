import Numlib.Analysis.SpecialFunctions.Pow.ImplicitRecurrence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Exact geometric recurrence and logarithmic hitting budgets

Ceiling a real logarithmic bound gives an actual target-reaching index.
-/

open Set Filter Topology
namespace ImplicitGap

/-- Unit implicit exponents give the exact geometric orbit. -/
theorem orbit_one_eq {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (n : ℕ) :
    orbit c 1 a n = (1 + c)⁻¹ ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := orbit_equation hc zero_lt_one ha n
    rw [Real.rpow_one, ih] at hh
    have hp : 0 < 1 + c := by linarith
    have hs : orbit c 1 a (n + 1) = ((1 + c)⁻¹ ^ n * a) / (1 + c) :=
      (eq_div_iff hp.ne').mpr (by nlinarith)
    rw [hs, pow_succ]
    ring

/-- A geometric contraction reaches every positive target with an explicit logarithmic budget. -/
theorem exists_geometric_budget {c R ε : ℝ} (hc : 0 < c) (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ N : ℕ, (1 + c)⁻¹ ^ N * R ≤ ε ∧
      (N : ℝ) ≤ (|Real.log ε| + Real.log R) / Real.log (1 + c) + 1 := by
  have hd : 0 < Real.log (1 + c) := Real.log_pos (by linarith)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  let B := (|Real.log ε| + Real.log R) / Real.log (1 + c)
  have hB : 0 ≤ B := by positivity
  refine ⟨⌈B⌉₊, ?_, (Nat.ceil_lt_add_one hB).le⟩
  have hceil := Nat.le_ceil B
  have hmul : |Real.log ε| + Real.log R ≤ (⌈B⌉₊ : ℝ) * Real.log (1 + c) :=
    (div_le_iff₀ hd).mp hceil
  have hpR : 0 < R := zero_lt_one.trans_le hR
  have hpq : 0 < (1 + c)⁻¹ := inv_pos.mpr (by linarith)
  apply (Real.log_le_log_iff (mul_pos (pow_pos hpq _) hpR) hε).mp
  rw [Real.log_mul (pow_pos hpq _).ne' hpR.ne', Real.log_pow, Real.log_inv]
  have habs := neg_abs_le (Real.log ε)
  nlinarith

/-- The exact linear orbit therefore has a uniform logarithmic target-hitting budget. -/
theorem exists_linear_budget {c a ε : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N : ℕ, orbit c 1 a N ≤ ε ∧
      (N : ℝ) ≤ (|Real.log ε| + Real.log (max 1 a)) / Real.log (1 + c) + 1 := by
  obtain ⟨N, ht, hN⟩ := exists_geometric_budget hc (le_max_left 1 a) hε
  refine ⟨N, ?_, hN⟩
  rw [orbit_one_eq hc ha]
  exact (mul_le_mul_of_nonneg_left (le_max_right 1 a) (by positivity)).trans ht
/-- Any target-reaching comparison iterate bounds the exact first hitting time. -/
theorem hittingTime_le {c τ a ε : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a)
    (hε : 0 < ε) {N : ℕ} (hN : orbit c τ a N ≤ ε) : hittingTime c τ a ε ≤ N := by
  by_contra hn
  have hh := (hittingTime_spec hc hτ ha hε).2 N (lt_of_not_ge hn)
  linarith
end ImplicitGap
