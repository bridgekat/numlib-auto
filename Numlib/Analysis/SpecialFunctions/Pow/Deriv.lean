/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`, beside the derivatives of `rpow`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The smooth regularization `(t² + ε²)^{p/2} − ε^p` of `|t|^p`

For `p ≥ 1` the function `t ↦ |t|^p` is not `C¹` at the origin when `p = 1`. Its regularization
`Real.rpowReg p ε t = (t² + ε²)^{p/2} − ε^p`, `ε > 0`, is smooth in `t`, vanishes at the origin,
satisfies `0 ≤ φ_ε t ≤ (|t| + ε)^p` and `|φ_ε' t| ≤ p (|t| + ε)^{p−1}`, and tends to `|t|^p` as
`ε → 0⁺`.

It is what makes Nečas's proof of the trace inequality work at `p = 1`
(`Numlib/Analysis/Sobolev/Boundary/Trace.lean`): the divergence theorem is applied to
`φ_ε(u) w`, and the bounds above survive the passage to the limit.
-/

open Filter Topology

namespace Real

/-- **The regularization `(t² + ε²)^{p/2} − ε^p` of `|t|^p`**, smooth in `t` for `ε > 0`, with
`φ_ε 0 = 0`, `0 ≤ φ_ε t ≤ (|t| + ε)^p`, `|φ_ε' t| ≤ p (|t| + ε)^{p−1}` and `φ_ε t → |t|^p` as
`ε → 0`. It is what makes Nečas's proof of the trace inequality work at `p = 1`, where `|t|^p` is
not `C¹`. -/
noncomputable def rpowReg (p ε t : ℝ) : ℝ := (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p

variable {p ε : ℝ}

/-- `t² + ε² > 0` for `ε > 0`. -/
theorem sq_add_sq_pos (hε : 0 < ε) (t : ℝ) : 0 < t ^ 2 + ε ^ 2 := by positivity

/-- `φ_ε 0 = 0`. -/
theorem rpowReg_zero (hε : 0 < ε) : rpowReg p ε 0 = 0 := by
  have h : (0 : ℝ) ^ 2 + ε ^ 2 = ε ^ 2 := by ring
  unfold rpowReg
  rw [sub_eq_zero, h, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
  congr 1
  push_cast
  ring

/-- `φ_ε ≥ 0`. -/
theorem rpowReg_nonneg (hε : 0 < ε) (hp : 0 ≤ p) (t : ℝ) : 0 ≤ rpowReg p ε t := by
  unfold rpowReg
  rw [sub_nonneg]
  calc ε ^ p = (ε ^ 2) ^ (p / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
        congr 1
        push_cast
        ring
    _ ≤ (t ^ 2 + ε ^ 2) ^ (p / 2) :=
        Real.rpow_le_rpow (by positivity) (le_add_of_nonneg_left (by positivity))
          (by positivity)

/-- `φ_ε t ≤ (|t| + ε)^p`. -/
theorem rpowReg_le (hε : 0 < ε) (hp : 0 ≤ p) (t : ℝ) : rpowReg p ε t ≤ (|t| + ε) ^ p := by
  unfold rpowReg
  calc (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p ≤ (t ^ 2 + ε ^ 2) ^ (p / 2) :=
        sub_le_self _ (Real.rpow_nonneg hε.le _)
    _ ≤ ((|t| + ε) ^ 2) ^ (p / 2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        nlinarith [abs_nonneg t, sq_abs t]
    _ = (|t| + ε) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring

/-- The derivative of `φ_ε`: `φ_ε' t = p t (t² + ε²)^{p/2 − 1}`. -/
theorem hasDerivAt_rpowReg (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (rpowReg p ε) (p * t * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ t ^ 2 + ε ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_pow 2 t).add_const (ε ^ 2))
  have h2 := h1.rpow_const (p := p / 2) (Or.inl (sq_add_sq_pos hε t).ne')
  have h3 : HasDerivAt (fun t : ℝ ↦ (t ^ 2 + ε ^ 2) ^ (p / 2) - ε ^ p)
      (2 * t * (p / 2) * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)) t := h2.sub_const (ε ^ p)
  exact h3.congr_deriv (by ring)

/-- `φ_ε` is `C¹` (indeed smooth). -/
theorem contDiff_rpowReg (hε : 0 < ε) {n : WithTop ℕ∞} : ContDiff ℝ n (rpowReg p ε) := by
  unfold rpowReg
  refine ContDiff.sub ?_ contDiff_const
  exact ((contDiff_id.pow 2).add contDiff_const).rpow_const_of_ne fun t ↦ (sq_add_sq_pos hε t).ne'

/-- `|φ_ε' t| ≤ p (|t| + ε)^{p−1}` for `p ≥ 1`. -/
theorem abs_deriv_rpowReg_le (hε : 0 < ε) (hp : 1 ≤ p) (t : ℝ) :
    |p * t * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)| ≤ p * (|t| + ε) ^ (p - 1) := by
  have hpos := sq_add_sq_pos hε t
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg (Real.rpow_nonneg hpos.le _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hp0
  have h1 : |t| ≤ (t ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))
  calc |t| * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1)
      ≤ (t ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) * (t ^ 2 + ε ^ 2) ^ (p / 2 - 1) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hpos.le _)
    _ = (t ^ 2 + ε ^ 2) ^ ((p - 1) / 2) := by
        rw [← Real.rpow_add hpos]
        ring_nf
    _ ≤ ((|t| + ε) ^ 2) ^ ((p - 1) / 2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
        nlinarith [abs_nonneg t, sq_abs t]
    _ = (|t| + ε) ^ (p - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring

/-- `φ_ε t → |t|^p` as `ε → 0⁺`. -/
theorem tendsto_rpowReg (hp : 0 < p) (t : ℝ) :
    Tendsto (fun ε ↦ rpowReg p ε t) (𝓝[>] 0) (𝓝 (|t| ^ p)) := by
  have h1 : Tendsto (fun ε : ℝ ↦ (t ^ 2 + ε ^ 2) ^ (p / 2)) (𝓝[>] 0) (𝓝 ((t ^ 2) ^ (p / 2))) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x ^ (p / 2)) (t ^ 2) :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))
    have h : Tendsto (fun ε : ℝ ↦ t ^ 2 + ε ^ 2) (𝓝[>] 0) (𝓝 (t ^ 2)) := by
      have hc' : Continuous (fun ε : ℝ ↦ t ^ 2 + ε ^ 2) := by fun_prop
      have := (hc'.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    exact hc.tendsto.comp h
  have h2 : Tendsto (fun ε : ℝ ↦ ε ^ p) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.zero_rpow hp.ne'] using this
  have h3 : (t ^ 2 : ℝ) ^ (p / 2) = |t| ^ p := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
    congr 1
    push_cast
    ring
  have := h1.sub h2
  rw [sub_zero, h3] at this
  exact this

end Real
