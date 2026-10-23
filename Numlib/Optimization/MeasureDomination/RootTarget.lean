import Numlib.Optimization.MeasureDomination.TrustRegionBudget
import Numlib.Optimization.MeasureDomination.Superlinear

/-!
# Residual targets from scaled-power objective targets

Positive scalar powers preserve actual first attainment. Their exact algebra
transfers initialized counts and convergence rates to the original nonnegative
residual, including points with residual zero.
-/

namespace MeasureDomination
open Set Filter Topology
variable {ℓ : ℝ} {R : ℕ → ℝ} {S : Set ℕ}

/-- A positive power threshold is equivalent to its nonnegative residual threshold. -/
theorem scaled_power_le_iff {a ε : ℝ} (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hε : 0 ≤ ε) :
    a ^ ℓ / ℓ ≤ ε ^ ℓ / ℓ ↔ a ≤ ε := by
  rw [div_le_div_iff_of_pos_right hℓ]
  exact Real.rpow_le_rpow_iff ha hε hℓ

/-- The original nonnegative residual is recovered exactly from its scaled power. -/
theorem root_scaled_power {a : ℝ} (hℓ : 0 < ℓ) (ha : 0 ≤ a) :
    (ℓ * (a ^ ℓ / ℓ)) ^ (1 / ℓ) = a := by
  rw [mul_div_cancel₀ _ hℓ.ne', ←Real.rpow_mul ha, mul_one_div_cancel hℓ.ne', Real.rpow_one]

/-- Ratios of residuals are exact positive roots of scaled-power ratios, including zeros. -/
theorem ratio_eq_root_scaled_power {a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a / b = ((a ^ ℓ / ℓ) / (b ^ ℓ / ℓ)) ^ (1 / ℓ) := by
  rw [div_div_div_cancel_right₀ hℓ.ne', ←Real.div_rpow ha hb,
    ←Real.rpow_mul (div_nonneg ha hb), mul_one_div_cancel hℓ.ne', Real.rpow_one]

/-- Objective convergence gives actual residual convergence by the exact root map. -/
theorem tendsto_zero_of_scaled_power (hℓ : 0 < ℓ) (hR : ∀ n, 0 ≤ R n)
    (hh : Tendsto (fun n => R n ^ ℓ / ℓ) atTop (nhds 0)) :
    Tendsto R atTop (nhds 0) := by
  have ht := (hh.const_mul ℓ).rpow_const (Or.inr (by positivity : 0 ≤ 1 / ℓ))
  simpa only [mul_zero, Real.zero_rpow (one_div_ne_zero hℓ.ne'),
    root_scaled_power hℓ (hR _)] using ht

/-- A superlinear objective ratio yields the actual superlinear residual ratio. -/
theorem superlinear_of_scaled_power (hℓ : 0 < ℓ) (hR : ∀ n, 0 ≤ R n)
    (hh : Tendsto (fun n => (R (n + 1) ^ ℓ / ℓ) / (R n ^ ℓ / ℓ))
      atTop (nhds 0)) : Tendsto (fun n => R (n + 1) / R n) atTop (nhds 0) := by
  have ht := hh.rpow_const (Or.inr (by positivity : 0 ≤ 1 / ℓ))
  simpa only [Real.zero_rpow (one_div_ne_zero hℓ.ne'),
    ←ratio_eq_root_scaled_power hℓ (hR _) (hR _)] using ht

/-- Exact positive power substitution preserves initialized first-target power costs. -/
theorem PowerCost.root {q : ℝ} (hℓ : 0 < ℓ) (hR : ∀ n, 0 ≤ R n)
    (hh : PowerCost q (fun n => R n ^ ℓ / ℓ) S) : PowerCost (ℓ * q) R S := by
  obtain ⟨B, hB, C, hC, D, hD, F, hF, hc⟩ := hh
  refine ⟨B * ℓ ^ q, by positivity, C, hC, D * ℓ ^ q, by positivity, F, hF, ?_⟩
  intro ε hε
  have hδ : 0 < ε ^ ℓ / ℓ := div_pos (Real.rpow_pos_of_pos hε _) hℓ
  obtain ⟨K, hK, hfirst, hfun, hder⟩ := hc _ hδ
  have he : (ε ^ ℓ / ℓ) ^ (-q) = ℓ ^ q * ε ^ (-(ℓ * q)) := by
    rw [Real.div_rpow (Real.rpow_nonneg hε.le _) hℓ.le,
      ←Real.rpow_mul hε.le, Real.rpow_neg hℓ.le, div_inv_eq_mul,
      show ℓ * (-q) = -(ℓ * q) by ring, mul_comm]
  refine ⟨K, (scaled_power_le_iff hℓ (hR K) hε.le).mp hK, ?_, ?_, ?_⟩
  · intro k hk
    exact lt_of_not_ge (fun hn => (not_le_of_gt (hfirst k hk))
      ((scaled_power_le_iff hℓ (hR k) hε.le).mpr hn))
  · rw [he] at hfun
    nlinarith
  · rw [he] at hder
    nlinarith

/-- Exact positive power substitution preserves initialized logarithmic costs. -/
theorem LogarithmicCost.root (hℓ : 0 < ℓ) (hR : ∀ n, 0 ≤ R n)
    (hh : LogarithmicCost (fun n => R n ^ ℓ / ℓ) S) : LogarithmicCost R S := by
  obtain ⟨B, hB, C, hC, D, hD, F, hF, hc⟩ := hh
  refine ⟨B * ℓ, by positivity, C + B * |Real.log ℓ|, by positivity,
    D * ℓ, by positivity, F + D * |Real.log ℓ|, by positivity, ?_⟩
  intro ε hε
  have hδ : 0 < ε ^ ℓ / ℓ := div_pos (Real.rpow_pos_of_pos hε _) hℓ
  obtain ⟨K, hK, hfirst, hfun, hder⟩ := hc _ hδ
  have he : |Real.log (ε ^ ℓ / ℓ)| ≤ ℓ * |Real.log ε| + |Real.log ℓ| := by
    rw [Real.log_div (Real.rpow_pos_of_pos hε _).ne' hℓ.ne', Real.log_rpow hε]
    simpa only [abs_mul, abs_of_pos hℓ] using abs_sub (ℓ * Real.log ε) (Real.log ℓ)
  refine ⟨K, (scaled_power_le_iff hℓ (hR K) hε.le).mp hK, ?_, ?_, ?_⟩
  · intro k hk
    exact lt_of_not_ge (fun hn => (not_le_of_gt (hfirst k hk))
      ((scaled_power_le_iff hℓ (hR k) hε.le).mpr hn))
  · nlinarith [mul_le_mul_of_nonneg_left he hB.le]
  · nlinarith [mul_le_mul_of_nonneg_left he hD.le]

/-- A positive linear contraction of scaled powers gives the exact root
contraction for the actual nonnegative residuals. -/
theorem linear_step_of_scaled_power {a c : ℝ} (hℓ : 0 < ℓ) (ha : 0 ≤ a)
    (hc : 0 ≤ c) {b : ℝ} (hb : 0 ≤ b)
    (hh : a ^ ℓ / ℓ ≤ c * (b ^ ℓ / ℓ)) : a ≤ c ^ (1 / ℓ) * b := by
  have hm := mul_le_mul_of_nonneg_left hh hℓ.le
  have hl : ℓ * (a ^ ℓ / ℓ) = a ^ ℓ := mul_div_cancel₀ _ hℓ.ne'
  have hr : ℓ * (c * (b ^ ℓ / ℓ)) = c * b ^ ℓ := by field_simp
  rw [hl, hr] at hm
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg ha _) hm
    (show 0 ≤ 1 / ℓ by positivity)
  rw [←Real.rpow_mul ha, mul_one_div_cancel hℓ.ne', Real.rpow_one,
    Real.mul_rpow hc (Real.rpow_nonneg hb _), ←Real.rpow_mul hb,
    mul_one_div_cancel hℓ.ne', Real.rpow_one] at hp
  exact hp

/-- A genuine positive sublinear upper envelope for scaled powers gives a
positive sublinear upper envelope for the original nonnegative residuals. -/
theorem sublinear_envelope_of_scaled_power (hℓ : 0 < ℓ) (hR : ∀ n, 0 ≤ R n)
    (hh : (∀ n, R n ^ ℓ / ℓ = 0) ∨ ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧
      (∀ n, R n ^ ℓ / ℓ ≤ t n) ∧ Tendsto t atTop (nhds 0) ∧
      Tendsto (fun n => t (n + 1) / t n) atTop (nhds 1)) :
    (∀ n, R n = 0) ∨ ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧
      (∀ n, R n ≤ t n) ∧ Tendsto t atTop (nhds 0) ∧
      Tendsto (fun n => t (n + 1) / t n) atTop (nhds 1) := by
  rcases hh with hz | ⟨t, ht, hle, hzero, hratio⟩
  · left
    intro n
    have hh := root_scaled_power hℓ (hR n)
    rw [hz n, mul_zero, Real.zero_rpow (one_div_ne_zero hℓ.ne')] at hh
    exact hh.symm
  · right
    let u := fun n => (ℓ * t n) ^ (1 / ℓ)
    have ha : 0 < 1 / ℓ := by positivity
    refine ⟨u, fun n => Real.rpow_pos_of_pos (mul_pos hℓ (ht n)) _, ?_, ?_, ?_⟩
    · intro n
      rw [←root_scaled_power hℓ (hR n)]
      exact Real.rpow_le_rpow
        (mul_nonneg hℓ.le (div_nonneg (Real.rpow_nonneg (hR n) _) hℓ.le))
        (mul_le_mul_of_nonneg_left (hle n) hℓ.le) ha.le
    · have hh := (hzero.const_mul ℓ).rpow_const (Or.inr ha.le)
      simpa only [mul_zero, Real.zero_rpow ha.ne'] using hh
    · have hh := hratio.rpow_const (p := 1 / ℓ) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
      have he (n : ℕ) : u (n + 1) / u n = (t (n + 1) / t n) ^ (1 / ℓ) := by
        change (ℓ * t (n + 1)) ^ (1 / ℓ) / (ℓ * t n) ^ (1 / ℓ) = _
        rw [←Real.div_rpow (mul_pos hℓ (ht _)).le (mul_pos hℓ (ht _)).le,
          mul_div_mul_left _ _ hℓ.ne']
      simpa only [he, Real.one_rpow] using hh

/-- Positive power substitution gives the exact residual double-logarithmic
expression, with a fixed small-accuracy interval and initialized counters. -/
theorem DoubleLogarithmicCost.root (hℓ : 1 ≤ ℓ) (hR : ∀ n, 0 ≤ R n)
    (hh : DoubleLogarithmicCost 0 1 (fun n => R n ^ ℓ / ℓ) S) :
    DoubleLogarithmicCost (-(Real.log ℓ / ℓ)) 1 R S := by
  obtain ⟨δmax, hδmax, hδmax1, B, hB, C, hC, D, hD, F, hF, hc⟩ := hh
  have hl : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hlogl : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  let εmax := min (Real.exp (-1)) ((ℓ * δmax) ^ (1 / ℓ))
  have hmax : 0 < εmax := lt_min (Real.exp_pos _)
    (Real.rpow_pos_of_pos (mul_pos hl hδmax) _)
  refine ⟨εmax, hmax, min_le_left _ _, B, hB, C + B * Real.log ℓ, by positivity,
    D, hD, F + D * Real.log ℓ, by positivity, ?_⟩
  intro ε hε hεmax
  have hδ : 0 < ε ^ ℓ / ℓ := div_pos (Real.rpow_pos_of_pos hε _) hl
  have hδle : ε ^ ℓ / ℓ ≤ δmax := by
    have he := Real.rpow_le_rpow hε.le (hεmax.trans (min_le_right _ _)) hl.le
    rw [←Real.rpow_mul (mul_pos hl hδmax).le,
      one_div_mul_cancel hl.ne', Real.rpow_one] at he
    exact (div_le_iff₀ hl).mpr (by nlinarith)
  obtain ⟨_, K, hK, hfirst, hfun, hder⟩ := hc _ hδ hδle
  have hloge : Real.log ε ≤ -1 := by
    have he := Real.log_le_log hε (hεmax.trans (min_le_left _ _))
    rwa [Real.log_exp] at he
  have haff : |-(Real.log ℓ / ℓ) + Real.log ε| = |Real.log ε| + Real.log ℓ / ℓ := by
    rw [abs_of_nonpos
      (by linarith [div_nonneg hlogl hl.le] : -(Real.log ℓ / ℓ) + Real.log ε ≤ 0),
      abs_of_nonpos (by linarith : Real.log ε ≤ 0)]
    ring
  have hinner : 1 ≤ |-(Real.log ℓ / ℓ) + Real.log ε| := by
    rw [haff, abs_of_nonpos (by linarith : Real.log ε ≤ 0)]
    have hh : 0 ≤ Real.log ℓ / ℓ := div_nonneg hlogl hl.le
    linarith
  have he : Real.log |Real.log (ε ^ ℓ / ℓ)| =
      Real.log ℓ + Real.log |-(Real.log ℓ / ℓ) + Real.log ε| := by
    rw [Real.log_div (Real.rpow_pos_of_pos hε _).ne' hl.ne', Real.log_rpow hε,
      abs_of_nonpos (by nlinarith : ℓ * Real.log ε - Real.log ℓ ≤ 0)]
    have harg : -(ℓ * Real.log ε - Real.log ℓ) =
        ℓ * |-(Real.log ℓ / ℓ) + Real.log ε| := by
      rw [haff, abs_of_nonpos (by linarith : Real.log ε ≤ 0)]
      field_simp
      ring
    rw [harg, Real.log_mul hl.ne' (zero_lt_one.trans_le hinner).ne']
  simp only [one_mul, zero_add] at hfun hder
  rw [he] at hfun hder
  refine ⟨by simpa only [one_mul] using hinner, K,
    (scaled_power_le_iff hl (hR K) hε.le).mp hK, ?_, ?_, ?_⟩
  · intro k hk
    exact lt_of_not_ge (fun hn => (not_le_of_gt (hfirst k hk))
      ((scaled_power_le_iff hl (hR k) hε.le).mpr hn))
  · simp only [one_mul]
    nlinarith
  · simp only [one_mul]
    nlinarith

end MeasureDomination
