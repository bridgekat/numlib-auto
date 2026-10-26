import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Positive perturbed superlinear power updates

A higher-order nonnegative perturbation does not destroy positivity or local
superlinear decay of a safeguarded power update. All bounds are derived from
the genuine update expression, and their radius precedes the changing errors.
-/

open Filter Topology
namespace Real

/-- A positive common radius ensures three genuine small-power safeguards. -/
theorem exists_pos_power_safeguards {C D w a b : ℝ}
    (hw : 0 < w) (ha : 0 < a) (hb : 0 < b) :
    ∃ R > 0, R ≤ 1 ∧ ∀ e, 0 < e → e ≤ R →
      C * e ≤ 1 ∧ C * e ^ a ≤ w / 2 ∧ D * e ^ b ≤ 1 / 2 := by
  have h1 : ContinuousAt (fun e : ℝ => C * e) 0 := by fun_prop
  have h2 : ContinuousAt (fun e : ℝ => C * e ^ a) 0 :=
    continuousAt_const.mul (continuousAt_rpow_const _ _ (Or.inr ha.le))
  have h3 : ContinuousAt (fun e : ℝ => D * e ^ b) 0 :=
    continuousAt_const.mul (continuousAt_rpow_const _ _ (Or.inr hb.le))
  have he1 : ∀ᶠ e in 𝓝 (0 : ℝ), C * e < 1 :=
    h1.eventually (gt_mem_nhds (by norm_num))
  have he2 : ∀ᶠ e in 𝓝 (0 : ℝ), C * e ^ a < w / 2 :=
    h2.eventually (gt_mem_nhds (by simpa [zero_rpow ha.ne'] using half_pos hw))
  have he3 : ∀ᶠ e in 𝓝 (0 : ℝ), D * e ^ b < 1 / 2 :=
    h3.eventually (gt_mem_nhds (by simp [zero_rpow hb.ne']))
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp (he1.and (he2.and he3))
  refine ⟨min 1 (r / 2), lt_min zero_lt_one (half_pos hr), min_le_left _ _, ?_⟩
  intro e he heR
  have her : dist e 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos he]
    have hh := heR.trans (min_le_right 1 (r / 2))
    linarith
  exact ⟨(hh her).1.le, (hh her).2.1.le, (hh her).2.2.le⟩

/-- A higher-order true perturbation gives positive two-sided power bounds and
strict geometric decay of the actual corrected power update. -/
theorem positive_power_shift_bounds {C wL wU e d w γ γL γU : ℝ} {n N : ℕ}
    (hC : 0 ≤ C) (hwL : 0 < wL) (hwU : wL ≤ wU)
    (hγL : 1 < γL) (hγU : 0 < γU) (hn : 1 ≤ n) (hnN : n ≤ N)
    (he : 0 < e) (he1 : e ≤ 1) (hd0 : 0 ≤ d) (hd : d ≤ C * e ^ (2 * n))
    (hw : wL ≤ w ∧ w ≤ wU) (hγ : γL ≤ γ ∧ γ ≤ 2 * n - γU)
    (hsafe : C * e ≤ 1 ∧ C * e ^ γU ≤ wL / 2 ∧
      (wU * 2 ^ (2 * (N : ℝ))) * e ^ (γL - 1) ≤ 1 / 2) :
    0 < w * (e + d) ^ γ - d ∧
      wL / 2 * e ^ γ ≤ w * (e + d) ^ γ - d ∧
      w * (e + d) ^ γ - d ≤ (wU * 2 ^ (2 * (N : ℝ))) * e ^ γ ∧
      w * (e + d) ^ γ - d ≤ e / 2 := by
  have hd' : d ≤ C * e ^ (((2 * n : ℕ) : ℝ)) := by
    simpa only [rpow_natCast] using hd
  have hγ0 : 0 ≤ γ := (by linarith : 0 < γL).le.trans hγ.1
  have hwU0 : 0 < wU := hwL.trans_le hwU
  have hw0 : 0 ≤ w := (hwL.trans_le hw.1).le
  have hnn : (2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 2 hn
  have hdp : d ≤ e := by
    have hp := rpow_le_rpow_of_exponent_ge he he1 hnn
    have hh := hd'.trans (mul_le_mul_of_nonneg_left hp hC)
    rw [rpow_two] at hh
    nlinarith [mul_le_mul_of_nonneg_right hsafe.1 he.le]
  have hdγ : d ≤ wL / 2 * e ^ γ := by
    have hnnγ : γ + γU ≤ ((2 * n : ℕ) : ℝ) := by push_cast; linarith [hγ.2]
    have hp := rpow_le_rpow_of_exponent_ge he he1 hnnγ
    have hh := hd'.trans (mul_le_mul_of_nonneg_left hp hC)
    rw [rpow_add he] at hh
    nlinarith [mul_le_mul_of_nonneg_right hsafe.2.1 (rpow_nonneg he.le γ)]
  have hlo : wL / 2 * e ^ γ ≤ w * (e + d) ^ γ - d := by
    have hp := rpow_le_rpow he.le (by linarith : e ≤ e + d) hγ0
    have hh := mul_le_mul hw.1 hp (rpow_nonneg he.le γ) hw0
    linarith
  have hγN : γ ≤ 2 * (N : ℝ) := by
    have hnn' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith [hγ.2]
  have hup : w * (e + d) ^ γ - d ≤ (wU * 2 ^ (2 * (N : ℝ))) * e ^ γ := by
    have hp := rpow_le_rpow (by positivity : 0 ≤ e + d)
      (by linarith : e + d ≤ 2 * e) hγ0
    rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) he.le] at hp
    have h2 := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hγN
    have hh := mul_le_mul hw.2 hp (rpow_nonneg (by positivity) γ) hwU0.le
    have hh2 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right h2 (rpow_nonneg he.le γ)) hwU0.le
    nlinarith
  have hhalf : w * (e + d) ^ γ - d ≤ e / 2 := by
    have hp := rpow_le_rpow_of_exponent_ge he he1 hγ.1
    have hD : 0 ≤ wU * 2 ^ (2 * (N : ℝ)) := by positivity
    have hh := hup.trans (mul_le_mul_of_nonneg_left hp hD)
    have hpow : e ^ γL = e ^ (γL - 1) * e := by
      calc
        e ^ γL = e ^ ((γL - 1) + 1) := by congr 1; ring
        _ = e ^ (γL - 1) * e := by rw [rpow_add he, rpow_one]
    rw [hpow] at hh
    nlinarith [mul_le_mul_of_nonneg_right hsafe.2.2 he.le]
  exact ⟨(mul_pos (half_pos hwL) (rpow_pos_of_pos he γ)).trans_le hlo,
    hlo, hup, hhalf⟩

/-- Actual positive half-step decay implies a genuine zero limit. -/
theorem tendsto_zero_of_pos_half_step {e : ℕ → ℝ}
    (hpos : ∀ k, 0 < e k) (hstep : ∀ k, e (k + 1) ≤ e k / 2) :
    Tendsto e atTop (𝓝 0) := by
  have hb (k : ℕ) : e k ≤ e 0 * (1 / 2 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        e (k + 1) ≤ e k / 2 := hstep k
        _ ≤ (e 0 * (1 / 2 : ℝ) ^ k) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  exact squeeze_zero (fun k => (hpos k).le) hb (by simpa using hp.const_mul (e 0))

/-- Eventual constancy bounds every term of a natural sequence, including its
arbitrary finite prefix. -/
theorem exists_nat_bound_of_eventually_const {a : ℕ → ℕ} {n : ℕ}
    (ha : ∀ᶠ k in atTop, a k = n) : ∃ N, ∀ k, a k ≤ N := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp ha
  refine ⟨n + ∑ i ∈ Finset.range K, a i, fun k => ?_⟩
  by_cases hk : K ≤ k
  · rw [hK k hk]
    omega
  · have hh := Finset.single_le_sum (fun i _ => Nat.zero_le (a i))
      (Finset.mem_range.mpr (lt_of_not_ge hk))
    omega

end Real
