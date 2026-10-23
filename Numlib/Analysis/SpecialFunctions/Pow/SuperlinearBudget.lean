import Numlib.Analysis.SpecialFunctions.Pow.ImplicitRecurrence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Double-logarithmic budgets for genuine superlinear implicit updates

A finite target-hitting phase puts the logarithmically normalized gap above
one. Its actual expansion by the inverse exponent yields the exact
double-logarithmic ceiling bound, including a zero initial gap.
-/

open Set Filter Topology
namespace ImplicitGap

/-- The logarithmic normalization of a positive implicit orbit expands by the inverse exponent. -/
theorem normalized_log_step {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (hτ1 : τ < 1)
    (ha : 0 < a) (n : ℕ) :
    (1 / τ) * (Real.log c / (1 - τ) - Real.log (orbit c τ a n)) ≤
      Real.log c / (1 - τ) - Real.log (orbit c τ a (n + 1)) := by
  let q := 1 / τ
  let α := Real.log c / (1 - τ)
  have hq : 0 < q := by positivity
  have hu := orbit_pos hc hτ ha (n + 1)
  have hv := orbit_pos hc hτ ha n
  have hh : c * orbit c τ a (n + 1) ^ τ ≤ orbit c τ a n := by
    linarith [orbit_equation hc hτ ha.le n]
  have hlog := Real.log_le_log (mul_pos hc (Real.rpow_pos_of_pos hu τ)) hh
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hu τ).ne', Real.log_rpow hu] at hlog
  have hqt : q * τ = 1 := by dsimp [q]; field_simp
  have hα : α + q * Real.log c = q * α := by
    dsimp [α, q]
    field_simp [(sub_pos.mpr hτ1).ne', hτ.ne']
    ring
  have hb : Real.log (orbit c τ a (n + 1)) ≤
      q * Real.log (orbit c τ a n) - q * Real.log c := by
    calc _ = q * (τ * Real.log (orbit c τ a (n + 1))) := by
            rw [← mul_assoc, hqt, one_mul]
         _ ≤ q * (Real.log (orbit c τ a n) - Real.log c) :=
            mul_le_mul_of_nonneg_left (by linarith) hq.le
         _ = _ := by ring
  change q * (α - _) ≤ α - _
  nlinarith

/-- Genuine superlinear implicit orbits have uniform double-logarithmic target budgets. -/
theorem exists_superlinear_budget {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (hτ1 : τ < 1)
    (ha : 0 ≤ a) :
    ∃ A > 0, ∃ B > 0, ∀ ε : ℝ, 0 < ε → 1 ≤ |Real.log ε| →
      ∃ N : ℕ, orbit c τ a N ≤ ε ∧
        (N : ℝ) ≤ A * Real.log |Real.log ε| + B := by
  rcases ha.eq_or_lt with hz | hp
  · refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
    intro ε hε hεlog
    refine ⟨0, ?_, ?_⟩
    · simpa only [orbit_zero, ← hz] using hε.le
    · have hh := Real.log_nonneg hεlog
      push_cast
      linarith
  · let q := 1 / τ
    let α := Real.log c / (1 - τ)
    let T := hittingTime c τ a (Real.exp (α - 1))
    have hq1 : 1 < q := (lt_div_iff₀ hτ).mpr (by linarith)
    have hq : 0 < q := by linarith
    have hd : 0 < Real.log q := Real.log_pos hq1
    have hT := (hittingTime_spec hc hτ hp.le (Real.exp_pos (α - 1))).1
    have hstart : 1 ≤ α - Real.log (orbit c τ a T) := by
      have hh := Real.log_le_log (orbit_pos hc hτ hp T) hT
      rw [Real.log_exp] at hh
      linarith
    have hrate (n : ℕ) : q ^ n ≤ α - Real.log (orbit c τ a (T + n)) := by
      induction n with
      | zero => simpa using hstart
      | succ n ih =>
        have hh := normalized_log_step hc hτ hτ1 hp (T + n)
        have hm := mul_le_mul_of_nonneg_left ih hq.le
        rw [pow_succ]
        simp only [Nat.add_assoc] at hh
        change q * (α - _) ≤ α - _ at hh
        nlinarith
    have hH : 0 < |α| + 2 := by positivity
    have hlogH : 0 ≤ Real.log (|α| + 2) := Real.log_nonneg (by linarith [abs_nonneg α])
    refine ⟨1 / Real.log q, by positivity,
      (T : ℝ) + Real.log (|α| + 2) / Real.log q + 1, by positivity, ?_⟩
    intro ε hε hεlog
    let C := |α| + |Real.log ε| + 1
    have hC : 0 < C := by positivity
    have hlogC : 0 ≤ Real.log C := by
      apply Real.log_nonneg
      dsimp [C]
      linarith [abs_nonneg α, abs_nonneg (Real.log ε)]
    let n : ℕ := ⌈Real.log C / Real.log q⌉₊
    have hceil : Real.log C ≤ (n : ℝ) * Real.log q :=
      (div_le_iff₀ hd).mp (Nat.le_ceil _)
    have hpower : C ≤ q ^ n := by
      apply (Real.log_le_log_iff hC (pow_pos hq _)).mp
      rw [Real.log_pow]
      exact hceil
    have htarget : orbit c τ a (T + n) ≤ ε := by
      apply (Real.log_le_log_iff (orbit_pos hc hτ hp _) hε).mp
      have hh := hrate n
      have hα := le_abs_self α
      have hεabs := neg_abs_le (Real.log ε)
      dsimp [C] at hpower
      linarith
    have hCbound : C ≤ (|α| + 2) * |Real.log ε| := by
      dsimp [C]
      nlinarith [abs_nonneg α]
    have hlogbound := Real.log_le_log hC hCbound
    rw [Real.log_mul hH.ne' (zero_lt_one.trans_le hεlog).ne'] at hlogbound
    have hn := (Nat.ceil_lt_add_one (div_nonneg hlogC hd.le)).le
    change (n : ℝ) ≤ Real.log C / Real.log q + 1 at hn
    refine ⟨T + n, htarget, ?_⟩
    push_cast
    have hdiv := div_le_div_of_nonneg_right hlogbound hd.le
    calc (T : ℝ) + n ≤ T + ((Real.log (|α| + 2) + Real.log |Real.log ε|) / Real.log q + 1) :=
          add_le_add le_rfl (hn.trans (add_le_add hdiv le_rfl))
         _ = _ := by ring
end ImplicitGap
