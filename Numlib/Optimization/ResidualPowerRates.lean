import Numlib.Optimization.ResidualPowerDomination
import Numlib.Optimization.MeasureDominationRates

/-!
# Residual tolerance budgets

These scalar identities translate objective-gap tolerances into residual tolerances.
The constants in the bounds are fixed before the residual tolerance is chosen.
-/

namespace Optimization
open MeasureDomination

/-- The transformed polynomial gap tolerance has exactly the residual exponent `-(ell-2)`. -/
theorem residual_polynomial_tolerance_identity {ell ε : ℝ} (hell : 2 < ell) (hε : 0 < ε) :
    (ε ^ ell / ell) ^ (1 - 2 / (ell / (ell - 1))) =
      ell ^ ((ell - 2) / ell) * ε ^ (-(ell - 2)) := by
  have he : 0 < ell := by linarith
  have he1 : ell - 1 ≠ 0 := by linarith
  rw [Real.div_rpow (Real.rpow_nonneg hε.le _) he.le, ← Real.rpow_mul hε.le]
  have ht : 1 - 2 / (ell / (ell - 1)) = -((ell - 2) / ell) := by
    field_simp
    ring
  rw [ht, Real.rpow_neg he.le]
  have ht' : ell * -((ell - 2) / ell) = -(ell - 2) := by field_simp
  rw [ht', div_inv_eq_mul, mul_comm]

/-- The ceiling polynomial count has a tolerance-independent coefficient and rounding term. -/
theorem residual_polynomial_count_le {ell δ ε : ℝ} (hell : 2 < ell) (hδ : 0 < δ)
    (hε : 0 < ε) :
    (polynomialIterationCount δ (2 / (ell / (ell - 1))) (ε ^ ell / ell) : ℝ) ≤
      (ell ^ ((ell - 2) / ell) / δ) * ε ^ (-(ell - 2)) + 1 := by
  unfold polynomialIterationCount
  have hbase : 0 ≤ (ε ^ ell / ell) ^ (1 - 2 / (ell / (ell - 1))) / δ := by positivity
  have h := (Nat.ceil_lt_add_one hbase).le
  rw [residual_polynomial_tolerance_identity hell hε] at h
  rw [residual_polynomial_tolerance_identity hell hε]
  convert h using 1
  ring

/-- A geometric count for a residual gap has a logarithmic tolerance budget. -/
theorem residual_geometric_count_le {v b ell ε : ℝ} (hb : 1 < b)
    (hell : 0 < ell) (hε : 0 < ε) :
    (geometricIterationCount v b (ε ^ ell / ell) : ℝ) ≤
      (ell / Real.log b) * |Real.log ε| + |Real.log (v * ell)| / Real.log b + 1 := by
  have hlb : 0 < Real.log b := Real.log_pos hb
  have ht : 0 < ε ^ ell / ell := div_pos (Real.rpow_pos_of_pos hε _) hell
  unfold geometricIterationCount
  split_ifs with hv
  · simp only [Nat.cast_zero]
    positivity
  · have hvt : ε ^ ell / ell < v := lt_of_not_ge hv
    have hv0 : 0 < v := ht.trans hvt
    have hr : 0 < Real.log (v / (ε ^ ell / ell)) :=
      Real.log_pos ((one_lt_div ht).mpr hvt)
    have hn := (Nat.ceil_lt_add_one (div_pos hr hlb).le).le
    apply hn.trans
    have hlog : Real.log (v / (ε ^ ell / ell)) = Real.log (v * ell) - ell * Real.log ε := by
      rw [Real.log_div hv0.ne' ht.ne', Real.log_div
        (Real.rpow_pos_of_pos hε _).ne' hell.ne', Real.log_rpow hε,
        Real.log_mul hv0.ne' hell.ne']
      ring
    rw [hlog]
    have ha := le_abs_self (Real.log (v * ell))
    have hc : -(ell * Real.log ε) ≤ ell * |Real.log ε| := by
      nlinarith [neg_le_abs (Real.log ε)]
    have hh := (div_le_div_iff_of_pos_right hlb).mpr (add_le_add ha hc)
    convert add_le_add_right hh 1 using 1 <;> ring

/-- For tolerances at most `exp (-1)`, the superlinear gap count has a uniform
logarithm-of-logarithm residual budget. -/
theorem residual_superlinear_count_le {B p ell ε : ℝ} (hB : 0 < B) (hp : 1 < p)
    (hell : 0 < ell) (hε : 0 < ε) (hsmall : ε ≤ Real.exp (-1)) :
    let H := |Real.log B| + ell + |Real.log ell|
    (superlinearIterationCount B (1 / 2) p (ε ^ ell / ell) : ℝ) ≤
      (1 / Real.log p) * Real.log |Real.log ε| +
        |Real.log (H / (-Real.log (1 / 2 : ℝ)))| / Real.log p + 1 := by
  dsimp only
  have hlp : 0 < Real.log p := Real.log_pos hp
  have hc : 0 < -Real.log (1 / 2 : ℝ) := by
    apply neg_pos.mpr
    exact Real.log_neg (by norm_num) (by norm_num)
  have hlε : Real.log ε ≤ -1 := (Real.log_le_iff_le_exp hε).mpr hsmall
  have habs : 1 ≤ |Real.log ε| := by rw [abs_of_nonpos (by linarith)]; linarith
  have hlogabs : 0 ≤ Real.log |Real.log ε| := Real.log_nonneg habs
  have hH : 0 < |Real.log B| + ell + |Real.log ell| := by positivity
  have ht : 0 < ε ^ ell / ell := div_pos (Real.rpow_pos_of_pos hε _) hell
  unfold superlinearIterationCount geometricIterationCount
  split_ifs with hv
  · simp only [Nat.cast_zero]
    positivity
  · have hv' : -Real.log (1 / 2 : ℝ) < Real.log (B / (ε ^ ell / ell)) := lt_of_not_ge hv
    have hv0 : 0 < Real.log (B / (ε ^ ell / ell)) := hc.trans hv'
    have hceil := (Nat.ceil_lt_add_one
      (div_nonneg (Real.log_pos ((one_lt_div hc).mpr hv')).le hlp.le)).le
    apply hceil.trans
    have hlog : Real.log (B / (ε ^ ell / ell)) =
        Real.log B - ell * Real.log ε + Real.log ell := by
      rw [Real.log_div hB.ne' ht.ne', Real.log_div
        (Real.rpow_pos_of_pos hε _).ne' hell.ne', Real.log_rpow hε]
      ring
    have hbound : Real.log (B / (ε ^ ell / ell)) ≤
        (|Real.log B| + ell + |Real.log ell|) * |Real.log ε| := by
      rw [hlog]
      have hb := mul_le_mul_of_nonneg_left habs (abs_nonneg (Real.log B))
      have he := mul_le_mul_of_nonneg_left habs (abs_nonneg (Real.log ell))
      rw [abs_of_nonpos (by linarith : Real.log ε ≤ 0)] at *
      nlinarith [le_abs_self (Real.log B), le_abs_self (Real.log ell)]
    have hratio := (div_le_div_iff_of_pos_right hc).mpr hbound
    have hlogs := Real.log_le_log (div_pos hv0 hc) hratio
    have hsplit : Real.log (((|Real.log B| + ell + |Real.log ell|) * |Real.log ε|) /
        (-Real.log (1 / 2 : ℝ))) =
        Real.log ((|Real.log B| + ell + |Real.log ell|) / (-Real.log (1 / 2 : ℝ))) +
          Real.log |Real.log ε| := by
      rw [mul_div_right_comm, Real.log_mul (div_pos hH hc).ne' (by positivity)]
    rw [hsplit] at hlogs
    have hl := le_abs_self (Real.log ((|Real.log B| + ell + |Real.log ell|) /
      (-Real.log (1 / 2 : ℝ))))
    have hfinal := (div_le_div_iff_of_pos_right hlp).mpr (hlogs.trans (add_le_add hl (le_refl _)))
    convert add_le_add_right hfinal 1 using 1 <;> ring

/-- Positive-power implicit descent tends to zero, including sequences reaching zero
in finitely many steps. -/
theorem MeasureDomination.implicit_recurrence_tendsto_zero {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  have hm : Antitone u := by
    apply antitone_nat_of_succ_le
    intro k
    have hp := mul_nonneg ha.le (Real.rpow_nonneg (hu (k + 1)) τ)
    linarith [hstep k]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m, -, he⟩ := implicit_recurrence_entry ha hτ (half_pos hε) hu hstep
  refine ⟨m, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu k)]
  exact ((hm hk).trans he).trans_lt (half_lt_self hε)

/-- Implicit subunit-power descent of a positive power gives actual consecutive
Q-superlinear convergence. The nonnegative contraction coefficient tends to zero and
remains defined when the sequence has zero terms. -/
theorem MeasureDomination.implicit_power_recurrence_q_superlinear {v : ℕ → ℝ} {ell a τ : ℝ}
    (hv : ∀ k, 0 ≤ v k) (hell : 0 < ell) (ha : 0 < a) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hstep : ∀ k, v (k + 1) ^ ell / ell + a * (v (k + 1) ^ ell / ell) ^ τ ≤
      v k ^ ell / ell) :
    Filter.Tendsto v Filter.atTop (nhds 0) ∧
      ∃ c : ℕ → ℝ, (∀ k, 0 ≤ c k) ∧ Filter.Tendsto c Filter.atTop (nhds 0) ∧
        ∀ k, v (k + 1) ≤ c k * v k := by
  have hu : ∀ k, 0 ≤ v k ^ ell / ell := fun k =>
    div_nonneg (Real.rpow_nonneg (hv k) ell) hell.le
  have ht := implicit_recurrence_tendsto_zero ha hτ0 hu hstep
  have hp : Filter.Tendsto (fun k => v k ^ ell) Filter.atTop (nhds 0) := by
    have hh := Filter.Tendsto.const_mul ell ht
    simpa only [mul_zero, mul_div_cancel₀ _ hell.ne'] using hh
  have hz : Filter.Tendsto v Filter.atTop (nhds 0) := by
    have hh := hp.rpow_const_nhds_zero (inv_pos.mpr hell)
    simpa only [Real.rpow_rpow_inv (hv _) hell.ne'] using hh
  have hα : 1 < 1 / τ := (one_lt_div hτ0).mpr hτ1
  have hβ : 0 < 1 / τ - 1 := sub_pos.mpr hα
  let K := (ell * (1 / (ell * a)) ^ (1 / τ)) ^ ell⁻¹
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  refine ⟨hz, fun k => K * v k ^ (1 / τ - 1), fun k =>
    mul_nonneg hK (Real.rpow_nonneg (hv k) _), ?_, ?_⟩
  · have hh := Filter.Tendsto.const_mul K (hz.rpow_const_nhds_zero hβ)
    simpa only [mul_zero] using hh
  · intro k
    have hs := implicit_recurrence_rpow_step (hu (k + 1)) ha hτ0 (hstep k)
    have hb : v (k + 1) ^ ell ≤ ell * ((v k ^ ell / ell) / a) ^ (1 / τ) :=
      by simpa only [mul_comm] using (div_le_iff₀ hell).mp hs
    have hid : (v k ^ ell / ell) / a = (1 / (ell * a)) * v k ^ ell := by ring
    rw [hid, Real.mul_rpow (by positivity : 0 ≤ 1 / (ell * a))
      (Real.rpow_nonneg (hv k) ell), ← Real.rpow_mul (hv k)] at hb
    have hpow : (K * v k ^ (1 / τ)) ^ ell =
        ell * (1 / (ell * a)) ^ (1 / τ) * v k ^ (ell * (1 / τ)) := by
      rw [Real.mul_rpow hK (Real.rpow_nonneg (hv k) _)]
      dsimp only [K]
      rw [Real.rpow_inv_rpow (by positivity) hell.ne', ← Real.rpow_mul (hv k)]
      congr 2
      ring
    have hbound : v (k + 1) ≤ K * v k ^ (1 / τ) := by
      apply (Real.rpow_le_rpow_iff (hv (k + 1))
        (mul_nonneg hK (Real.rpow_nonneg (hv k) _)) hell).mp
      rw [hpow]
      simpa only [mul_assoc] using hb
    have he : v k ^ (1 / τ) = v k ^ (1 / τ - 1) * v k := by
      convert Real.rpow_add_one' (hv k) (y := 1 / τ - 1) (by linarith : 1 / τ - 1 + 1 ≠ 0)
        using 1
      congr 1
      ring
    simpa only [he, mul_assoc] using hbound

end Optimization
