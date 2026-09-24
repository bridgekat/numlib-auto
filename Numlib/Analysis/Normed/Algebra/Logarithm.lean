import Mathlib.Analysis.Normed.Algebra.Logarithm
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Numlib.Analysis.Normed.Algebra.Exponential

/-!
# The logarithm of a normed algebra: bounds

Upstreaming candidate: natural home `Mathlib/Analysis/Normed/Algebra/Logarithm`, whose name this
module mirrors.

Mathlib's `NormedSpace.log x = ∑ₙ (-1)^{n+1}/n (x - 1)ⁿ` is defined in any topological algebra;
this module bounds it in a normed algebra over `ℝ` or `ℂ`:

* `NormedSpace.norm_log_le`: `‖log x‖ ≤ -log (1 - ‖x - 1‖)` for `‖x - 1‖ < 1`, termwise against
  the real series `∑ uⁿ/n = -log (1 - u)`. [golub2013matrix] P9.2.2 is the weaker
  `‖log (I + A)‖ ≤ ‖A‖/(1 - ‖A‖)`.

* `NormedSpace.exp_log_of_norm_sub_one_lt`: `exp (log x) = x` for `‖x - 1‖ < 1` in a complete
  normed real (or complex) algebra, a TODO of Mathlib, by showing that `e^{-log(1 + t h)} (1 + t h)`
  is constant in `t`.
-/

open Filter Topology

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- **The logarithm series is bounded termwise by the real one**:
`‖log x‖ ≤ -log (1 - ‖x - 1‖)` whenever `‖x - 1‖ < 1`. -/
theorem norm_log_le (𝕂 : Type*) [RCLike 𝕂] [NormedAlgebra 𝕂 𝔸] {x : 𝔸} (hx : ‖x - 1‖ < 1) :
    ‖log x‖ ≤ -Real.log (1 - ‖x - 1‖) := by
  set u := ‖x - 1‖
  have hg : HasSum (fun n : ℕ => u ^ n / n) (-Real.log (1 - u)) := by
    have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := u)
      (by rwa [abs_of_nonneg (norm_nonneg _)])
    refine (hasSum_nat_add_iff' 1).mp ?_
    simpa using h
  rw [log_eq_tsum 𝕂]
  refine tsum_of_norm_bounded hg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [norm_smul, norm_div, norm_pow, norm_neg, norm_one, one_pow, RCLike.norm_natCast,
      one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (norm_pow_le' _ hn) (Nat.cast_nonneg _)

section ExpLog

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The coefficients `(-1)^{n+1}/n` of the logarithm series. -/
private noncomputable def logCoeff (n : ℕ) : ℝ := (-1) ^ (n + 1) / n

omit [CompleteSpace 𝔸] in
/-- `log (1 + t h)` as a power series in the real variable `t`. -/
private theorem log_one_add_smul_eq_tsum (h : 𝔸) (t : ℝ) :
    log (1 + t • h) = ∑' n, (logCoeff n * t ^ n) • h ^ n := by
  rw [log_eq_tsum ℝ]
  simp only [add_sub_cancel_left, smul_pow, smul_smul, logCoeff]

/-- `exp a * exp (-a) = 1` in a complete normed real algebra. -/
private theorem exp_mul_exp_neg (a : 𝔸) : exp a * exp (-a) = 1 := by
  rw [← exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (Commute.refl a).neg_right
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _), add_neg_cancel, exp_zero]

/-- **`exp (log x) = x`** in a complete normed real (or complex) algebra whenever `‖x - 1‖ < 1`
(a TODO of Mathlib's `Mathlib/Analysis/Normed/Algebra/Logarithm`). With `h = x - 1` and
`L(t) = log (1 + t h)`, all of `L(t)`, `L'(t) = h (1 + t h)⁻¹` and `h` commute, so
`φ(t) = e^{-L(t)} (1 + t h)` has derivative `e^{-L} (h - L'(1 + t h)) = 0` (the derivative of the
exponential in a commuting direction is `NormedSpace.expFrechet_apply_of_commute`), and
`φ(1) = φ(0) = 1`. -/
theorem exp_log_of_norm_sub_one_lt {x : 𝔸} (hx : ‖x - 1‖ < 1) : exp (log x) = x := by
  set h := x - 1 with hh
  have hx1 : x = 1 + h := by rw [hh]; abel
  rcases eq_or_ne h 0 with h0 | h0
  · rw [hx1, h0, add_zero, log_one, exp_zero]
  set ε := ‖h‖
  have hε : 0 < ε := norm_pos_iff.mpr h0
  set ρ := (1 + ε) / 2
  have hερ : ε < ρ := by simp only [ρ]; linarith
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  have hρ0 : 0 < ρ := hε.trans hερ
  set R := ρ / ε
  have hR : 1 < R := (one_lt_div hε).mpr hερ
  set T := Metric.ball (0 : ℝ) R
  have habs : ∀ t ∈ T, |t| < R := fun t ht => by simpa [T, Real.dist_eq] using ht
  have hT : ∀ t ∈ T, ‖t • h‖ < 1 := fun t ht => by
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ε ≤ R * ε := mul_le_mul_of_nonneg_right (habs t ht).le hε.le
      _ = ρ := div_mul_cancel₀ ρ hε.ne'
      _ < 1 := hρ1
  have hu : Summable fun n : ℕ => ε / ρ * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hbound : ∀ (n : ℕ) (t : ℝ), t ∈ T →
      ‖(logCoeff n * ((n : ℝ) * t ^ (n - 1))) • h ^ n‖ ≤ ε / ρ * ρ ^ n := by
    intro n t ht
    rcases n with _ | k
    · simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_smul, norm_zero]
      positivity
    · have hc : |logCoeff (k + 1)| * |((k + 1 : ℕ) : ℝ)| = 1 := by
        rw [← abs_mul, logCoeff, div_mul_cancel₀ _ (by positivity), abs_pow, abs_neg, abs_one,
          one_pow]
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, Nat.add_sub_cancel, abs_pow,
        ← mul_assoc, hc, one_mul]
      calc |t| ^ k * ‖h ^ (k + 1)‖ ≤ R ^ k * ε ^ (k + 1) :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg t) (habs t ht).le k)
              (norm_pow_le' h k.succ_pos) (norm_nonneg _) (by positivity)
        _ = ε / ρ * ρ ^ (k + 1) := by
            have h1 : R ^ k * ε ^ k = ρ ^ k := by rw [← mul_pow, div_mul_cancel₀ ρ hε.ne']
            rw [pow_succ ε, ← mul_assoc, h1]
            field_simp
            ring
  -- the derivative of `L(t) = log (1 + t h)`
  set S : ℝ → 𝔸 := fun t => ∑' k : ℕ, (-(t • h)) ^ k
  have hS : ∀ t ∈ T, S t * (1 + t • h) = 1 := fun t ht => by
    have := geom_series_mul_neg (-(t • h)) (by rw [norm_neg]; exact hT t ht)
    rwa [sub_neg_eq_add] at this
  have hL : ∀ t ∈ T, HasDerivAt (fun t : ℝ => log (1 + t • h)) (h * S t) t := by
    intro t ht
    simp_rw [log_one_add_smul_eq_tsum h]
    have hderiv := hasDerivAt_tsum_of_isPreconnected (t := T) (y₀ := 0)
      (g := fun n (t : ℝ) => (logCoeff n * t ^ n) • h ^ n)
      (g' := fun n (t : ℝ) => (logCoeff n * ((n : ℝ) * t ^ (n - 1))) • h ^ n)
      hu Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (fun n t _ => ((hasDerivAt_pow n t).const_mul (logCoeff n)).smul_const (h ^ n))
      hbound (Metric.mem_ball_self (by linarith)) ?_ ht
    · convert hderiv using 1
      rw [(Summable.of_norm_bounded hu fun n => hbound n t ht).tsum_eq_zero_add]
      simp only [logCoeff, Nat.cast_zero, zero_mul, mul_zero, zero_smul, zero_add]
      rw [← Summable.tsum_mul_left h (summable_geometric_of_norm_lt_one
        (by rw [norm_neg]; exact hT t ht))]
      refine tsum_congr fun k => ?_
      rw [← neg_smul, smul_pow, mul_smul_comm, ← pow_succ', Nat.add_sub_cancel]
      congr 1
      rw [neg_pow]
      push_cast
      field_simp
      ring
    · convert summable_zero with n
      rcases n with _ | n <;> simp [logCoeff]
  -- commutation
  have hcomm : ∀ t : ℝ, Commute (-log (1 + t • h)) (-(h * S t)) := fun t => by
    have h1 : Commute (log (1 + t • h)) h :=
      ((Commute.one_left h).add_left ((Commute.refl h).smul_left t)).log_left
    have h2 : Commute (log (1 + t • h)) (S t) :=
      Commute.tsum_right _ fun k => ((h1.smul_right t).neg_right).pow_right k
    exact ((h1.mul_right h2).neg_left).neg_right
  -- `φ(t) = e^{-L(t)} (1 + t h)` is constant
  set φ : ℝ → 𝔸 := fun t => exp (-log (1 + t • h)) * (1 + t • h)
  have hφ : ∀ t ∈ T, HasDerivAt φ 0 t := by
    intro t ht
    have hE : HasDerivAt (fun s : ℝ => exp (-log (1 + s • h)))
        (exp (-log (1 + t • h)) * -(h * S t)) t := by
      have h1 := (hasFDerivAt_exp_smul (-log (1 + t • h)) 1).comp_hasDerivAt t (hL t ht).neg
      simp only [one_smul, Function.comp_def] at h1
      rwa [expFrechet_apply_of_commute (hcomm t), one_smul, one_smul] at h1
    have hd : HasDerivAt (fun s : ℝ => 1 + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add 1
    convert hE.mul hd using 1
    rw [mul_assoc, neg_mul, mul_assoc, hS t ht, mul_one, mul_neg, neg_add_cancel]
  have hconst : φ 1 = φ 0 :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht => (hφ t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hφ t ht).deriv) (Metric.mem_ball_self (by linarith))
      (by simpa [T, Real.dist_eq, abs_of_pos zero_lt_one] using hR)
      |>.symm
  simp only [φ, one_smul, zero_smul, add_zero, log_one, neg_zero, exp_zero, mul_one] at hconst
  rw [← hx1] at hconst
  calc exp (log x) = exp (log x) * (exp (-log x) * x) := by rw [hconst, mul_one]
    _ = x := by rw [← mul_assoc, exp_mul_exp_neg, one_mul]

end ExpLog

end NormedSpace
