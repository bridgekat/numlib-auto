import Numlib.Optimization.SteepestDescent.Exact.CorridorGradient
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# The first local line minimum of the actual corridor objective

Closed-interval polynomial identification supplies actual derivatives even at
corridor walls. A positive polynomial factorization proves descent before the
prescribed endpoint, whose actual positive curvature proves local minimality.
-/

open Polynomial Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- Every nonterminal width dominates twice the common positive decrement. -/
theorem two_widthIncrement_le_amplitude (P : Parameters) {k : ℕ} (hk : k < P.horizon) :
    2 * widthIncrement P ≤ amplitude P k := by
  have hN := P.horizon_cast_pos
  have hk' : (k : ℝ) + 1 ≤ P.horizon := by exact_mod_cast hk
  have hN1 : (1 : ℝ) ≤ P.horizon := by exact_mod_cast P.horizon_pos
  dsimp [widthIncrement, amplitude, omega]
  apply (mul_le_mul_iff_left₀ hN).mp
  field_simp
  nlinarith [P.accuracy_pos]

private theorem smoothStep_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ smoothStep.eval t ∧ smoothStep.eval t ≤ 1 ∧ smoothStep.eval t ≤ 2 * t := by
  have ht0 := ht.1
  have h0 : 0 ≤ 1 - t := by linarith [ht.2]
  have he : smoothStep.eval t = t ^ 3 * (6 * (1 - t) ^ 2 + 3 * (1 - t) + 1) := by
    simp [smoothStep]
    ring
  have he1 : 1 - smoothStep.eval t = (1 - t) ^ 3 * (1 + 3 * t + 6 * t ^ 2) := by
    simp [smoothStep]
    ring
  have he2 : 2 * t - smoothStep.eval t = t *
      (2 * (1 - t) ^ 4 + 8 * t * (1 - t) ^ 3 + 2 * t ^ 2 * (1 - t) ^ 2 +
        3 * t ^ 3 * (1 - t) + t ^ 4) := by
    simp [smoothStep]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [he]; positivity
  · have : 0 ≤ 1 - smoothStep.eval t := by rw [he1]; positivity
    linarith
  · have : 0 ≤ 2 * t - smoothStep.eval t := by rw [he2]; positivity
    linarith

/-- The true polynomial on the normalized source diagonal segment. -/
def segmentPolynomial (P : Parameters) (k : ℕ) : ℝ[X] :=
  C ((Real.sqrt 2)⁻¹) *
    (C (scalarValue P k) - C (amplitude P k ^ 2) * X +
      C (amplitude P k * widthIncrement P) * slopeCorrection +
      (C (amplitude P k) * X - C (amplitude P k / 2) -
        C (widthIncrement P / 2) * smoothStep) ^ 2)

/-- The genuine global objective along a normalized diagonal segment. -/
def segmentObjective (P : Parameters) (k : ℕ) (t : ℝ) : ℝ :=
  objective P (horizontal P k + amplitude P k * t,
    vertical P k + (-1 : ℝ) ^ k * amplitude P k * t)

/-- Actual affine line restriction preserves global finite smoothness. -/
theorem contDiff_segmentObjective (P : Parameters) (k : ℕ) :
    ContDiff ℝ 2 (segmentObjective P k) :=
  (contDiff_objective P).comp (by fun_prop)

private theorem segment_curve (P : Parameters) {k : ℕ} (hk : k < P.horizon)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 3) :
    curve P i (horizontal P k + amplitude P k * t) =
      (curvePolynomial P i k).eval (amplitude P k * t) := by
  have he := (curve_spec P i).2.2 k hk 0 (by omega)
    (horizontal P k + amplitude P k * t) ?_
  · simpa only [iteratedDeriv_zero, add_sub_cancel_left] using he
  · rw [horizontal_succ]
    have ha := amplitude_pos P hk.le
    constructor <;> nlinarith [ht.1, ht.2]

/-- The actual closed corridor segment equals its explicit polynomial. -/
theorem segmentObjective_eq_polynomial (P : Parameters) {k : ℕ} (hk : k < P.horizon)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segmentObjective P k t = (segmentPolynomial P k).eval t := by
  have ha := amplitude_pos P hk.le
  have hh : 0 < widthIncrement P := div_pos P.accuracy_pos P.horizon_cast_pos
  have hab := two_widthIncrement_le_amplitude P hk
  have hcurve (i : Fin 3) := segment_curve P hk ht i
  have hw : curve P 0 (horizontal P k + amplitude P k * t) =
      amplitude P k - widthIncrement P * smoothStep.eval t := by
    rw [hcurve 0]
    simp [curvePolynomial, widthPolynomial, ha.ne']
  have hc : curve P 1 (horizontal P k + amplitude P k * t) =
      centerValue P k + (-1 : ℝ) ^ k * widthIncrement P / 2 * smoothStep.eval t := by
    rw [hcurve 1]
    simp [curvePolynomial, centerPolynomial, ha.ne']
  have hs : scalarObjective P (horizontal P k + amplitude P k * t) =
      scalarValue P k - amplitude P k ^ 2 * t +
        amplitude P k * widthIncrement P * slopeCorrection.eval t := by
    have hle : horizontal P k + amplitude P k * t ≤ horizontal P P.horizon := by
      have hstep : horizontal P k + amplitude P k * t ≤ horizontal P (k + 1) := by
        rw [horizontal_succ]
        nlinarith [ht.2]
      exact hstep.trans (by
        rcases lt_or_eq_of_le (show k + 1 ≤ P.horizon by omega) with h | h
        · exact (horizontal_increasing P _ _ h le_rfl).le
        · rw [h])
    have hleft := scalarObjective_left P (j := 0) (by omega) hle
    simp only [iteratedDeriv_zero] at hleft
    rw [hleft, hcurve 2]
    simp [curvePolynomial, scalarPolynomial, ha.ne']
    ring
  let a := amplitude P k
  let h := widthIncrement P
  let S := smoothStep.eval t
  let b := a * t - a / 2 - h / 2 * S
  have hb : b ∈ Icc (-(a - h * S) / 2) ((a - h * S) / 2) := by
    have hS := smoothStep_bounds ht
    have hs : h * S ≤ a * t := by
      calc
        h * S ≤ h * (2 * t) := mul_le_mul_of_nonneg_left hS.2.2 hh.le
        _ ≤ a * t := by dsimp [h, a]; nlinarith [ht.1]
    dsimp [b]
    constructor <;> nlinarith [ht.2]
  have hsign : |(-1 : ℝ) ^ k| = 1 := by simp
  have hcentr : vertical P k + (-1 : ℝ) ^ k * amplitude P k * t -
      curve P 1 (horizontal P k + amplitude P k * t) ∈
      Icc (-(curve P 0 (horizontal P k + amplitude P k * t)) / 2)
        (curve P 0 (horizontal P k + amplitude P k * t) / 2) := by
    rw [hc, hw]
    have he : vertical P k + (-1 : ℝ) ^ k * amplitude P k * t -
        (centerValue P k + (-1 : ℝ) ^ k * widthIncrement P / 2 * smoothStep.eval t) =
        (-1 : ℝ) ^ k * b := by
      dsimp [b, a, h, S]
      rw [centerValue]
      ring
    rw [he]
    change (-1 : ℝ) ^ k * b ∈ Icc (-(a - h * S) / 2) ((a - h * S) / 2)
    simp only [mem_Icc, neg_div] at hb ⊢
    rw [← abs_le] at hb ⊢
    simpa only [abs_mul, hsign, one_mul] using hb
  dsimp [segmentObjective, objective, residualCorridor, corridorFunction]
  rw [hs, profile_central hcentr, hc]
  have he : vertical P k + (-1 : ℝ) ^ k * amplitude P k * t -
      (centerValue P k + (-1 : ℝ) ^ k * widthIncrement P / 2 * smoothStep.eval t) =
      (-1 : ℝ) ^ k * b := by
    dsimp [b, a, h, S]
    rw [centerValue]
    ring
  rw [he, mul_pow]
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  rw [hsq, one_mul]
  simp only [segmentPolynomial, eval_mul, eval_C, eval_add, eval_sub,
    eval_X, eval_pow]
  dsimp [b, a, h, S]
  ring

/-- Actual derivatives through order two match on the closed segment. -/
theorem segmentObjective_iteratedDeriv (P : Parameters) {k : ℕ} (hk : k < P.horizon)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (segmentObjective P k) t =
      iteratedDeriv j (segmentPolynomial P k).eval t := by
  have hp : ContDiff ℝ j (segmentPolynomial P k).eval := by
    simpa using (segmentPolynomial P k).contDiff_aeval (𝕜 := ℝ) j
  have hu := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)
  rw [← iteratedDerivWithin_eq_iteratedDeriv hu
      (((contDiff_segmentObjective P k).of_le (by exact_mod_cast hj)).contDiffAt) ht,
    ← iteratedDerivWithin_eq_iteratedDeriv hu
      hp.contDiffAt ht]
  exact iteratedDerivWithin_congr (fun z hz => segmentObjective_eq_polynomial P hk hz) ht

/-- The genuine source objective strictly decreases before its next prescribed
line-search endpoint. -/
theorem segmentObjective_deriv_neg (P : Parameters) {k : ℕ} (hk : k < P.horizon)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : deriv (segmentObjective P k) t < 0 := by
  have he := segmentObjective_iteratedDeriv P hk ⟨ht0, ht1.le⟩ (j := 1) (by omega)
  simp only [iteratedDeriv_one, Polynomial.deriv] at he
  rw [he]
  let a := amplitude P k
  let h := widthIncrement P
  let b := a - 2 * h
  have hh : 0 < h := div_pos P.accuracy_pos P.horizon_cast_pos
  have hb : 0 ≤ b := sub_nonneg.mpr (two_widthIncrement_le_amplitude P hk)
  let B4 := 8 * (1-t)^4 + 32*t*(1-t)^3 + 45*t^2*(1-t)^2 + 65*t^3*(1-t) + 8*t^4
  let B8 := 8 * (1-t)^8 + 64*t*(1-t)^7 + 218*t^2*(1-t)^6 + 490*t^3*(1-t)^5 +
    788*t^4*(1-t)^4 + 670*t^5*(1-t)^3 + 407*t^6*(1-t)^2 + 115*t^7*(1-t) + 8*t^8
  have hneg : (segmentPolynomial P k).derivative.eval t =
      -(1-t) * (2*b^2 + b*h*B4 + h^2*B8) / Real.sqrt 2 := by
    dsimp [segmentPolynomial, a, h, b, B4, B8]
    norm_num [smoothStep, slopeCorrection, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_C, derivative_X]
    ring
  rw [hneg]
  have ht : 0 < 1 - t := by linarith
  have hpos : 0 < 2*b^2 + b*h*B4 + h^2*B8 := by
    dsimp [B4, B8]
    positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ht) hpos)
    (by positivity)

/-- The actual endpoint slope vanishes, its actual curvature is positive, and
it is a genuine local minimum of the globally defined line restriction. -/
theorem segmentObjective_endpoint (P : Parameters) {k : ℕ} (hk : k < P.horizon) :
    deriv (segmentObjective P k) 1 = 0 ∧
      deriv (deriv (segmentObjective P k)) 1 = 2 * amplitude P k ^ 2 / Real.sqrt 2 ∧
      IsLocalMin (segmentObjective P k) 1 := by
  have h1 := segmentObjective_iteratedDeriv P hk (by simp : (1 : ℝ) ∈ Icc 0 1)
    (j := 1) (by omega)
  have h2 := segmentObjective_iteratedDeriv P hk (by simp : (1 : ℝ) ∈ Icc 0 1)
    (j := 2) (by omega)
  simp only [iteratedDeriv_one, Polynomial.deriv] at h1
  have hd1 : deriv (segmentObjective P k) 1 = 0 := by
    rw [h1]
    norm_num [segmentPolynomial, smoothStep, slopeCorrection, derivative_add,
      derivative_sub, derivative_mul, derivative_pow, derivative_C, derivative_X]
    ring
  have hd2 : deriv (deriv (segmentObjective P k)) 1 =
      2 * amplitude P k ^ 2 / Real.sqrt 2 := by
    rw [← show iteratedDeriv 2 (segmentObjective P k) 1 =
      deriv (deriv (segmentObjective P k)) 1 by
        rw [iteratedDeriv_succ, iteratedDeriv_one]]
    rw [h2, Polynomial.iteratedDeriv_eval]
    norm_num [segmentPolynomial, smoothStep, slopeCorrection, derivative_add,
      derivative_sub, derivative_mul, derivative_pow, derivative_C, derivative_X,
      Function.iterate_succ_apply']
    ring
  refine ⟨hd1, hd2, isLocalMin_of_deriv_deriv_pos ?_ hd1
    (contDiff_segmentObjective P k).continuous.continuousAt⟩
  rw [hd2]
  have ha := amplitude_pos P hk.le
  positivity

/-- The actual globally defined negative-gradient ray at a source node. -/
def rayObjective (P : Parameters) (k : ℕ) (α : ℝ) : ℝ :=
  euclideanObjective P (gridPoint P k - α •
    gradient (euclideanObjective P) (gridPoint P k))

/-- The genuine negative-gradient ray is the normalized diagonal segment with
parameter alpha divided by the square root of two. -/
theorem rayObjective_eq_segmentObjective (P : Parameters) {k : ℕ}
    (hk : k ≤ P.horizon) (α : ℝ) :
    rayObjective P k α = segmentObjective P k (α / Real.sqrt 2) := by
  unfold rayObjective
  rw [euclideanObjective_gradient_node P hk]
  unfold segmentObjective euclideanObjective
  apply congrArg (objective P)
  apply Prod.ext <;> simp [euclideanCoordinates, gridPoint, gridDirection, PiLp.smul_apply,
    PiLp.sub_apply] <;> ring

/-- Every prescribed source step is the first local line minimum: the true
ray derivative is negative on the entire preceding closed-left segment,
vanishes at the endpoint, and the endpoint is locally minimal. -/
theorem first_local_line_minimum (P : Parameters) {k : ℕ} (hk : k < P.horizon) :
    0 < Real.sqrt 2 ∧
    gridPoint P (k + 1) = gridPoint P k - Real.sqrt 2 •
      gradient (euclideanObjective P) (gridPoint P k) ∧
    (∀ α ∈ Ico (0 : ℝ) (Real.sqrt 2), deriv (rayObjective P k) α < 0) ∧
    deriv (rayObjective P k) (Real.sqrt 2) = 0 ∧
    IsLocalMin (rayObjective P k) (Real.sqrt 2) := by
  have hroot : 0 < Real.sqrt 2 := by positivity
  have heq : rayObjective P k = fun α => segmentObjective P k (α / Real.sqrt 2) :=
    funext (rayObjective_eq_segmentObjective P hk.le)
  have hd (α : ℝ) : deriv (rayObjective P k) α =
      deriv (segmentObjective P k) (α / Real.sqrt 2) / Real.sqrt 2 := by
    rw [heq]
    have hh := (((contDiff_segmentObjective P k).differentiable (by norm_num))
      (α / Real.sqrt 2)).hasDerivAt.comp α ((hasDerivAt_id α).div_const (Real.sqrt 2))
    simpa only [Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using hh.deriv
  obtain ⟨h1, _, hmin⟩ := segmentObjective_endpoint P hk
  refine ⟨hroot, gridPoint_succ P hk, ?_, ?_, ?_⟩
  · intro α hα
    rw [hd]
    apply div_neg_of_neg_of_pos _ hroot
    apply segmentObjective_deriv_neg P hk (div_nonneg hα.1 hroot.le)
    exact (div_lt_one hroot).mpr hα.2
  · rw [hd, div_self hroot.ne', h1, zero_div]
  · have hcont : Filter.Tendsto (fun α : ℝ => α / Real.sqrt 2)
        (nhds (Real.sqrt 2)) (nhds 1) := by
      simpa only [id_eq, div_self hroot.ne'] using
        ((continuous_id.div_const (Real.sqrt 2)).continuousAt
          (x := Real.sqrt 2)).tendsto
    have hh := hcont.eventually hmin
    rw [heq]
    change ∀ᶠ α in nhds (Real.sqrt 2),
      segmentObjective P k (Real.sqrt 2 / Real.sqrt 2) ≤
        segmentObjective P k (α / Real.sqrt 2)
    simpa only [div_self hroot.ne'] using hh

end ExactSteepestDescent.Corridor
