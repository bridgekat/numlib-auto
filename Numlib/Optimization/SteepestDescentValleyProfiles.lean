import Numlib.Analysis.Calculus.QuinticHermite
import Numlib.Analysis.Calculus.PiecewiseDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Polynomial profiles for a smooth narrowing valley

This module constructs actual scalar smoothing and transition profiles. The quintic strip
joins a quadratic core to a constant plateau. The correction coefficients have fixed seams,
so their twice continuous differentiability also gives joint Fréchet differentiability after
translation by a varying width. These components do not assert the existence of an entire
steepest descent trajectory or any global line search property.
-/

noncomputable section

open Polynomial Set

namespace Optimization.SteepestDescentValley

/-- Quintic interpolation from zero to one with vanishing first and second endpoint jets. -/
def smoothStepPolynomial : ℝ[X] := 10 * X ^ 3 - 15 * X ^ 4 + 6 * X ^ 5

/-- The actual scalar quintic smoothing profile. -/
def smoothStep (t : ℝ) : ℝ := smoothStepPolynomial.eval t

/-- The quartic adjustment to the derivative of a quintic scalar descent cell. -/
def slopeAdjustmentPolynomial : ℝ[X] := -12 * X ^ 2 + 28 * X ^ 3 - 15 * X ^ 4

/-- The actual scalar slope adjustment. -/
def slopeAdjustment (t : ℝ) : ℝ := slopeAdjustmentPolynomial.eval t

/-- Expanded formula for the smoothing profile. -/
theorem smoothStep_eq (t : ℝ) : smoothStep t = 10 * t ^ 3 - 15 * t ^ 4 + 6 * t ^ 5 := by
  simp [smoothStep, smoothStepPolynomial]

/-- Expanded formula for the slope adjustment. -/
theorem slopeAdjustment_eq (t : ℝ) :
    slopeAdjustment t = -12 * t ^ 2 + 28 * t ^ 3 - 15 * t ^ 4 := by
  simp [slopeAdjustment, slopeAdjustmentPolynomial]

/-- The smoothing starts at zero. -/
@[simp] theorem smoothStep_zero : smoothStep 0 = 0 := by norm_num [smoothStep_eq]

/-- The smoothing ends at one. -/
@[simp] theorem smoothStep_one : smoothStep 1 = 1 := by norm_num [smoothStep_eq]

/-- The scalar slope adjustment starts at zero. -/
@[simp] theorem slopeAdjustment_zero : slopeAdjustment 0 = 0 := by
  norm_num [slopeAdjustment_eq]

/-- The scalar slope adjustment ends at one. -/
@[simp] theorem slopeAdjustment_one : slopeAdjustment 1 = 1 := by
  norm_num [slopeAdjustment_eq]

/-- All endpoint derivatives through order two of the smoothing profile. -/
theorem smoothStep_endpoint_jets {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j smoothStep 0 = 0 ∧
      iteratedDeriv j smoothStep 1 = (if j = 0 then 1 else 0) := by
  change iteratedDeriv j (fun t => smoothStepPolynomial.eval t) 0 = _ ∧
    iteratedDeriv j (fun t => smoothStepPolynomial.eval t) 1 = _
  simp only [Polynomial.iteratedDeriv_eval]
  interval_cases j <;> norm_num [smoothStepPolynomial, Function.iterate_succ_apply', derivative_pow]

/-- Reflection complements the smoothing profile. -/
theorem smoothStep_reflection (t : ℝ) : smoothStep (1 - t) = 1 - smoothStep t := by
  simp only [smoothStep_eq]
  ring

/-- The first derivative is a nonnegative factored quartic. -/
theorem deriv_smoothStep (t : ℝ) : deriv smoothStep t = 30 * t ^ 2 * (1 - t) ^ 2 := by
  change deriv (fun t => smoothStepPolynomial.eval t) t = _
  rw [Polynomial.deriv]
  norm_num [smoothStepPolynomial, derivative_pow]
  ring

/-- The second derivative is an explicit factored cubic. -/
theorem iteratedDeriv_two_smoothStep (t : ℝ) :
    iteratedDeriv 2 smoothStep t = 60 * t * (1 - 3 * t + 2 * t ^ 2) := by
  change iteratedDeriv 2 (fun t => smoothStepPolynomial.eval t) t = _
  simp only [Polynomial.iteratedDeriv_eval]
  norm_num [smoothStepPolynomial, Function.iterate_succ_apply', derivative_pow]
  ring

/-- The smoothing profile is nonnegative throughout its interpolation interval. -/
theorem smoothStep_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ smoothStep t := by
  rcases ht with ⟨ht0, ht1⟩
  have ht2 : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rw [smoothStep_eq]
  have h : 10 * t ^ 3 - 15 * t ^ 4 + 6 * t ^ 5 =
      t ^ 3 * (6 * (1 - t) ^ 2 + 3 * (1 - t) + 1) := by ring
  rw [h]
  positivity

/-- The smoothing profile takes values in the unit interval. -/
theorem smoothStep_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    smoothStep t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨smoothStep_nonneg ht, ?_⟩
  have h := smoothStep_nonneg (show 1 - t ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2])
  rw [smoothStep_reflection] at h
  linarith

/-- The sharp uniform first derivative bound, attained at one half. -/
theorem abs_deriv_smoothStep_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |deriv smoothStep t| ≤ 15 / 8 := by
  rw [deriv_smoothStep, abs_of_nonneg (by positivity)]
  have h : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hb : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) (by positivity : 0 ≤ 1 / 4 + t * (1 - t))]

/-- A factorization giving the upper bound on the scalar slope adjustment. -/
theorem slopeAdjustment_sub_one (t : ℝ) :
    slopeAdjustment t - 1 = -(1 - t) ^ 2 * (15 * t ^ 2 + 2 * t + 1) := by
  rw [slopeAdjustment_eq]
  ring

/-- The slope adjustment is at most one on the unit interval. -/
theorem slopeAdjustment_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    slopeAdjustment t ≤ 1 := by
  have ht0 := ht.1
  have h := slopeAdjustment_sub_one t
  have hn : 0 ≤ (1 - t) ^ 2 * (15 * t ^ 2 + 2 * t + 1) := by positivity
  nlinarith

/-- The strict interior slope gap has a useful exact factorization. -/
theorem slopeAdjustment_sub_smoothStep (t : ℝ) :
    slopeAdjustment t - smoothStep t = -6 * t ^ 2 * (1 - t) ^ 2 * (t + 2) := by
  rw [slopeAdjustment_eq, smoothStep_eq]
  ring

/-- The scalar slope adjustment lies strictly below the smoothing profile in the interior. -/
theorem slopeAdjustment_lt_smoothStep {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    slopeAdjustment t < smoothStep t := by
  have ht0 := ht.1
  have h := slopeAdjustment_sub_smoothStep t
  have hp : 0 < 6 * t ^ 2 * (1 - t) ^ 2 * (t + 2) := by
    have h0 : 0 < 1 - t := sub_pos.mpr ht.2
    positivity
  nlinarith

/-- The unit transition strip connecting the quadratic core to the plateau `8*d²`. -/
def stripPolynomial (d : ℝ) : ℝ[X] :=
  C (d ^ 2 / 4) + C d * X + X ^ 2 +
    C ((155 / 2 : ℝ) * d ^ 2 - 6 * d - 3) * X ^ 3 +
    C (-(465 / 4 : ℝ) * d ^ 2 + 8 * d + 3) * X ^ 4 +
    C ((93 / 2 : ℝ) * d ^ 2 - 3 * d - 1) * X ^ 5

/-- Evaluate the actual parameterized transition polynomial. -/
def strip (d q : ℝ) : ℝ := (stripPolynomial d).eval q

/-- Expanded two-variable strip formula. -/
theorem strip_eq (d q : ℝ) : strip d q =
    d ^ 2 / 4 + d * q + q ^ 2 + ((155 / 2 : ℝ) * d ^ 2 - 6 * d - 3) * q ^ 3 +
    (-(465 / 4 : ℝ) * d ^ 2 + 8 * d + 3) * q ^ 4 +
    ((93 / 2 : ℝ) * d ^ 2 - 3 * d - 1) * q ^ 5 := by
  simp [strip, stripPolynomial]

/-- A positivity decomposition of the actual strip into its smoothing and core terms. -/
theorem strip_eq_nonnegative_decomposition (d q : ℝ) :
    strip d q = d ^ 2 / 4 + (31 / 4 : ℝ) * d ^ 2 * smoothStep q +
      d * q * (1 - q) ^ 3 * (1 + 3 * q) + q ^ 2 * (1 - q) ^ 3 := by
  rw [strip_eq, smoothStep_eq]
  ring

/-- The actual transition strip is nonnegative for every nonnegative width. -/
theorem strip_nonneg {d q : ℝ} (hd : 0 ≤ d) (hq : q ∈ Icc (0 : ℝ) 1) :
    0 ≤ strip d q := by
  rw [strip_eq_nonnegative_decomposition]
  have hS := smoothStep_nonneg hq
  have hq0 := hq.1
  have hq1 : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
  positivity

/-- The strip has the exact quadratic core jet at its inner seam. -/
theorem strip_inner_jets (d : ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (strip d) 0 = if j = 0 then d ^ 2 / 4 else if j = 1 then d else 2 := by
  change iteratedDeriv j (fun q => (stripPolynomial d).eval q) 0 = _
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;> norm_num [stripPolynomial, Function.iterate_succ_apply', derivative_pow]

/-- The strip has the exact constant plateau jet at its outer seam. -/
theorem strip_outer_jets (d : ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (strip d) 1 = if j = 0 then 8 * d ^ 2 else 0 := by
  change iteratedDeriv j (fun q => (stripPolynomial d).eval q) 1 = _
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    norm_num [stripPolynomial, Function.iterate_succ_apply', derivative_pow] <;> ring

/-- The inner seam value agrees with the quadratic core. -/
@[simp] theorem strip_zero (d : ℝ) : strip d 0 = d ^ 2 / 4 := by
  simpa using strip_inner_jets d (j := 0) (by omega)

/-- The outer seam value agrees with the plateau. -/
@[simp] theorem strip_one (d : ℝ) : strip d 1 = 8 * d ^ 2 := by
  simpa using strip_outer_jets d (j := 0) (by omega)

/-- The actual outward derivative of the strip. -/
theorem deriv_strip_outward (d q : ℝ) : deriv (strip d) q =
    d + 2 * q + 3 * ((155 / 2 : ℝ) * d ^ 2 - 6 * d - 3) * q ^ 2 +
    4 * (-(465 / 4 : ℝ) * d ^ 2 + 8 * d + 3) * q ^ 3 +
    5 * ((93 / 2 : ℝ) * d ^ 2 - 3 * d - 1) * q ^ 4 := by
  change deriv (fun q => (stripPolynomial d).eval q) q = _
  rw [Polynomial.deriv]
  norm_num [stripPolynomial, derivative_pow]
  ring

/-- The actual second outward derivative of the strip. -/
theorem iteratedDeriv_two_strip_outward (d q : ℝ) : iteratedDeriv 2 (strip d) q =
    2 + 6 * ((155 / 2 : ℝ) * d ^ 2 - 6 * d - 3) * q +
    12 * (-(465 / 4 : ℝ) * d ^ 2 + 8 * d + 3) * q ^ 2 +
    20 * ((93 / 2 : ℝ) * d ^ 2 - 3 * d - 1) * q ^ 3 := by
  change iteratedDeriv 2 (fun q => (stripPolynomial d).eval q) q = _
  rw [Polynomial.iteratedDeriv_eval]
  norm_num [stripPolynomial, Function.iterate_succ_apply', derivative_pow]
  ring

/-- A polynomial in width representing the same actual strip with the other variable fixed. -/
def stripWidthPolynomial (q : ℝ) : ℝ[X] :=
  X ^ 2 * C (1 / 4) + X * C q + C (q ^ 2) +
    (C (155 / 2) * X ^ 2 - 6 * X - 3) * C (q ^ 3) +
    (-C (465 / 4) * X ^ 2 + 8 * X + 3) * C (q ^ 4) +
    (C (93 / 2) * X ^ 2 - 3 * X - 1) * C (q ^ 5)

/-- Fixing the outward coordinate gives the explicit width polynomial. -/
theorem strip_eq_eval_widthPolynomial (d q : ℝ) :
    strip d q = (stripWidthPolynomial q).eval d := by
  simp [strip_eq, stripWidthPolynomial]
  ring

/-- The actual width derivative of the strip, including the translated-core terms. -/
theorem deriv_strip_width (d q : ℝ) : deriv (fun d => strip d q) d =
    d / 2 + q + (155 * d - 6) * q ^ 3 +
    (-(465 / 2 : ℝ) * d + 8) * q ^ 4 + (93 * d - 3) * q ^ 5 := by
  simp_rw [strip_eq_eval_widthPolynomial]
  rw [Polynomial.deriv]
  norm_num [stripWidthPolynomial, derivative_pow]
  ring

/-- The actual second width derivative of the strip. -/
theorem iteratedDeriv_two_strip_width (d q : ℝ) :
    iteratedDeriv 2 (fun d => strip d q) d =
      1 / 2 + 155 * q ^ 3 - (465 / 2 : ℝ) * q ^ 4 + 93 * q ^ 5 := by
  simp_rw [strip_eq_eval_widthPolynomial]
  rw [Polynomial.iteratedDeriv_eval]
  norm_num [stripWidthPolynomial, Function.iterate_succ_apply', derivative_pow]
  ring

/-- The actual mixed derivative, first in width and then in outward coordinate. -/
theorem deriv_outward_deriv_strip_width (d q : ℝ) :
    deriv (fun q => deriv (fun d => strip d q) d) q =
      1 + 3 * (155 * d - 6) * q ^ 2 +
        4 * (-(465 / 2 : ℝ) * d + 8) * q ^ 3 + 5 * (93 * d - 3) * q ^ 4 := by
  simp_rw [deriv_strip_width]
  let p : ℝ[X] := C (d / 2) + X + C (155 * d - 6) * X ^ 3 +
    C (-(465 / 2 : ℝ) * d + 8) * X ^ 4 + C (93 * d - 3) * X ^ 5
  have hp : (fun q : ℝ => d / 2 + q + (155 * d - 6) * q ^ 3 +
      (-(465 / 2 : ℝ) * d + 8) * q ^ 4 + (93 * d - 3) * q ^ 5) =
      fun q => p.eval q := by
    funext q
    simp [p]
  rw [hp, Polynomial.deriv]
  norm_num [p, derivative_pow]
  ring

/-- The strip is jointly smooth in its width and outward coordinate. -/
theorem contDiff_strip : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => strip p.1 p.2) := by
  simp only [strip_eq]
  fun_prop

/-- A single constant bounds all actual Fréchet derivatives through order two on the
compact width/strip rectangle. The constant precedes the width and strip coordinate. -/
theorem exists_strip_derivative_bound :
    ∃ C > 0, ∀ j ≤ 2, ∀ p ∈ (Icc (0 : ℝ) 2) ×ˢ (Icc (0 : ℝ) 1),
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => strip p.1 p.2) p‖ ≤ C := by
  have hb (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ p ∈ (Icc (0 : ℝ) 2) ×ˢ (Icc (0 : ℝ) 1),
        ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => strip p.1 p.2) p‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (contDiff_strip.continuous_iteratedFDeriv (by simp)).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun p hp => (hB p hp).trans (le_max_left _ _)⟩
  choose B hB hb using hb
  refine ⟨1 + ∑ j ∈ Finset.range 3, B j, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun j _ => hB j)
  · intro j hj p hp
    exact (hb j p hp).trans (by
      have h := Finset.single_le_sum (fun i _ => hB i)
        (Finset.mem_range.mpr (show j < 3 by omega))
      linarith)

/-- Evaluate the genuine joint Fréchet derivative by its two actual coordinate derivatives.
The preceding polynomial formulas make both terms explicit. -/
theorem fderiv_strip_apply (d q : ℝ) (v : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => strip p.1 p.2) (d, q) v =
      v.1 * deriv (fun d => strip d q) d + v.2 * deriv (strip d) q := by
  let f := fun p : ℝ × ℝ => strip p.1 p.2
  have hf : Differentiable ℝ f := contDiff_strip.differentiable (by simp)
  have hw : deriv (fun d => strip d q) d = fderiv ℝ f (d, q) (1, 0) := by
    simpa [f, Function.comp_def] using
      (((hf (d, q)).hasFDerivAt.comp d (hasFDerivAt_prodMk_left d q)).hasDerivAt.deriv)
  have hq : deriv (strip d) q = fderiv ℝ f (d, q) (0, 1) := by
    simpa [f, Function.comp_def] using
      (((hf (d, q)).hasFDerivAt.comp q (hasFDerivAt_prodMk_right d q)).hasDerivAt.deriv)
  change fderiv ℝ f (d, q) v = _
  have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, ← hw, ← hq]
  rfl

/-- Reflection reverses the first jet and preserves the second jet of the lower strip. -/
theorem lower_strip_endpoint_jets (d : ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (fun q => strip d (1 - q)) 0 = (if j = 0 then 8 * d ^ 2 else 0) ∧
      iteratedDeriv j (fun q => strip d (1 - q)) 1 =
        (if j = 0 then d ^ 2 / 4 else if j = 1 then -d else 2) := by
  rw [iteratedDeriv_comp_const_sub]
  simp only [sub_zero, sub_self, smul_eq_mul]
  rw [strip_outer_jets d hj, strip_inner_jets d hj]
  interval_cases j <;> norm_num

/-- Coefficients in the width expansion of the difference between strip and core. -/
def correctionPolynomial (i : Fin 3) : ℝ[X] :=
  if i = 0 then -3 * X ^ 3 + 3 * X ^ 4 - X ^ 5
  else if i = 1 then -6 * X ^ 3 + 8 * X ^ 4 - 3 * X ^ 5
  else C (155 / 2) * X ^ 3 - C (465 / 4) * X ^ 4 +
    C (93 / 2) * X ^ 5

/-- Coefficient tails that make the sum equal a constant plateau. -/
def correctionTailPolynomial (i : Fin 3) : ℝ[X] :=
  if i = 0 then -X ^ 2 else if i = 1 then -X else C (31 / 4)

/-- Actual correction coefficient with seams at zero and one. -/
def correctionCoefficient (i : Fin 3) : ℝ → ℝ :=
  joinAt 0 (fun _ => 0)
    (joinAt 1 (fun q => (correctionPolynomial i).eval q)
      (fun q => (correctionTailPolynomial i).eval q))

/-- The coefficient polynomials match zero to second order at the inner seam. -/
theorem correctionPolynomial_inner_jets (i : Fin 3) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (fun q => (correctionPolynomial i).eval q) 0 = 0 := by
  rw [Polynomial.iteratedDeriv_eval]
  fin_cases i <;> interval_cases j <;>
    norm_num [correctionPolynomial, Function.iterate_succ_apply', derivative_pow]

/-- The polynomial and tail have exactly matching jets at the outer seam. -/
theorem correctionPolynomial_outer_jets (i : Fin 3) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (fun q => (correctionPolynomial i).eval q) 1 =
      iteratedDeriv j (fun q => (correctionTailPolynomial i).eval q) 1 := by
  simp only [Polynomial.iteratedDeriv_eval]
  fin_cases i <;> interval_cases j <;>
    norm_num [correctionPolynomial, correctionTailPolynomial,
      Function.iterate_succ_apply', derivative_pow]

/-- Fixed seams preserve genuine twice continuous differentiability of the coefficients. -/
theorem contDiff_correctionCoefficient (i : Fin 3) :
    ContDiff ℝ 2 (correctionCoefficient i) := by
  have hp : ContDiff ℝ 2 (fun q : ℝ => (correctionPolynomial i).eval q) := by
    fin_cases i <;> norm_num [correctionPolynomial] <;> fun_prop
  have ht : ContDiff ℝ 2 (fun q : ℝ => (correctionTailPolynomial i).eval q) := by
    fin_cases i <;> norm_num [correctionTailPolynomial] <;> fun_prop
  have hright := contDiff_joinAt_of_matching_jets hp ht
    (fun j hj => correctionPolynomial_outer_jets i hj)
  refine (contDiff_joinAt_of_matching_jets contDiff_const hright.1 ?_).1
  intro j hj
  rw [hright.2 j hj]
  simp only [joinAt_of_le _ _ (by norm_num : (0 : ℝ) ≤ 1)]
  rw [correctionPolynomial_inner_jets i hj]
  interval_cases j <;> simp

/-- The correction is identically zero inside the quadratic core. -/
theorem correctionCoefficient_of_nonpos (i : Fin 3) {q : ℝ} (hq : q ≤ 0) :
    correctionCoefficient i q = 0 := joinAt_of_le _ _ hq

/-- The actual correction agrees with its polynomial throughout the unit strip. -/
theorem correctionCoefficient_of_mem_Icc (i : Fin 3) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    correctionCoefficient i q = (correctionPolynomial i).eval q := by
  have hm : (0 : ℝ) = (joinAt 1 (fun q => (correctionPolynomial i).eval q)
      (fun q => (correctionTailPolynomial i).eval q)) 0 := by
    rw [joinAt_of_le _ _ (by norm_num : (0 : ℝ) ≤ 1)]
    simpa only [iteratedDeriv_zero] using
      (correctionPolynomial_inner_jets i (j := 0) (by omega)).symm
  rw [correctionCoefficient, joinAt_of_ge hm hq.1, joinAt_of_le _ _ hq.2]

/-- Beyond the outer seam the correction is given by its explicit tail. -/
theorem correctionCoefficient_of_one_le (i : Fin 3) {q : ℝ} (hq : 1 ≤ q) :
    correctionCoefficient i q = (correctionTailPolynomial i).eval q := by
  rw [correctionCoefficient, joinAt_of_gt _ _ (by linarith : 0 < q)]
  apply joinAt_of_ge _ hq
  simpa only [iteratedDeriv_zero] using correctionPolynomial_outer_jets i (j := 0) (by omega)

/-- The width-dependent correction to the quadratic profile. -/
def correction (d q : ℝ) : ℝ :=
  d ^ 2 * correctionCoefficient 2 q + d * correctionCoefficient 1 q + correctionCoefficient 0 q

/-- The correction has zero value on the nonpositive half-line. -/
theorem correction_of_nonpos (d : ℝ) {q : ℝ} (hq : q ≤ 0) : correction d q = 0 := by
  simp [correction, correctionCoefficient_of_nonpos _ hq]

/-- Within the strip the correction is precisely the difference from the quadratic core. -/
theorem correction_of_mem_Icc (d : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    correction d q = strip d q - (q + d / 2) ^ 2 := by
  simp only [correction, correctionCoefficient_of_mem_Icc _ hq]
  norm_num [correctionPolynomial, strip_eq]
  ring

/-- Beyond the strip the correction cancels the quadratic and leaves the plateau. -/
theorem correction_of_one_le (d : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    correction d q = 8 * d ^ 2 - (q + d / 2) ^ 2 := by
  simp only [correction, correctionCoefficient_of_one_le _ hq]
  norm_num [correctionTailPolynomial]
  ring

/-- The correction is jointly twice continuously Fréchet differentiable. -/
theorem contDiff_correction : ContDiff ℝ 2 (fun p : ℝ × ℝ => correction p.1 p.2) := by
  have h0 := contDiff_correctionCoefficient 0
  have h1 := contDiff_correctionCoefficient 1
  have h2 := contDiff_correctionCoefficient 2
  unfold correction
  fun_prop

/-- A symmetric valley profile, with quadratic core and two unit transition strips. -/
def profile (d z : ℝ) : ℝ :=
  z ^ 2 + correction d (z - d / 2) + correction d (-z - d / 2)

/-- Reflection about the midpoint leaves the actual profile unchanged. -/
@[simp] theorem profile_reflection (d z : ℝ) : profile d (-z) = profile d z := by
  simp only [profile, neg_neg, neg_sq]
  ring

/-- The actual valley profile is jointly twice continuously Fréchet differentiable. -/
theorem contDiff_profile : ContDiff ℝ 2 (fun p : ℝ × ℝ => profile p.1 p.2) := by
  have hc := contDiff_correction
  unfold profile
  have hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1, p.2 - p.1 / 2)) := by fun_prop
  have hl : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1, -p.2 - p.1 / 2)) := by fun_prop
  exact ((contDiff_snd.pow 2).add (hc.comp hu)).add (hc.comp hl)

/-- Between the two inner seams the actual profile is the quadratic core. -/
theorem profile_core {d z : ℝ} (hl : -d / 2 ≤ z) (hu : z ≤ d / 2) :
    profile d z = z ^ 2 := by
  rw [profile, correction_of_nonpos d (by linarith : z - d / 2 ≤ 0),
    correction_of_nonpos d (by linarith : -z - d / 2 ≤ 0)]
  ring

/-- The upper unit strip is the explicit quintic, provided the width is nonnegative. -/
theorem profile_upper_strip {d z : ℝ} (hd : 0 ≤ d)
    (hz : z - d / 2 ∈ Icc (0 : ℝ) 1) : profile d z = strip d (z - d / 2) := by
  rw [profile, correction_of_mem_Icc d hz,
    correction_of_nonpos d (by linarith [hz.1] : -z - d / 2 ≤ 0)]
  ring

/-- The lower strip is the reflected upper quintic. -/
theorem profile_lower_strip {d z : ℝ} (hd : 0 ≤ d)
    (hz : -z - d / 2 ∈ Icc (0 : ℝ) 1) : profile d z = strip d (-z - d / 2) := by
  rw [← profile_reflection d z]
  exact profile_upper_strip hd hz

/-- The upper exterior is the constant plateau. -/
theorem profile_upper_plateau {d z : ℝ} (hd : 0 ≤ d) (hz : 1 ≤ z - d / 2) :
    profile d z = 8 * d ^ 2 := by
  rw [profile, correction_of_one_le d hz,
    correction_of_nonpos d (by linarith : -z - d / 2 ≤ 0)]
  ring

/-- The lower exterior is the same plateau by reflection. -/
theorem profile_lower_plateau {d z : ℝ} (hd : 0 ≤ d) (hz : 1 ≤ -z - d / 2) :
    profile d z = 8 * d ^ 2 := by
  rw [← profile_reflection d z]
  exact profile_upper_plateau hd hz

/-- Every part of the actual valley profile is nonnegative. -/
theorem profile_nonneg {d : ℝ} (hd : 0 ≤ d) (z : ℝ) : 0 ≤ profile d z := by
  by_cases hl : z ≤ -d / 2 - 1
  · rw [profile_lower_plateau hd (by linarith)]
    positivity
  by_cases hli : z ≤ -d / 2
  · rw [profile_lower_strip hd (show -z - d / 2 ∈ Icc (0 : ℝ) 1 by
      constructor <;> linarith)]
    exact strip_nonneg hd (by constructor <;> linarith)
  by_cases hui : z ≤ d / 2
  · rw [profile_core (by linarith) hui]
    positivity
  by_cases hu : z ≤ d / 2 + 1
  · rw [profile_upper_strip hd (show z - d / 2 ∈ Icc (0 : ℝ) 1 by
      constructor <;> linarith)]
    exact strip_nonneg hd (by constructor <;> linarith)
  · rw [profile_upper_plateau hd (by linarith)]
    positivity

/-- Move the midpoint and width of the actual symmetric profile along the horizontal axis. -/
def movingProfile (width midpoint : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  profile (width p.1) (p.2 - midpoint p.1)

/-- Actual twice smooth width and midpoint functions give a jointly twice smooth valley,
including its moving seams and mixed derivatives. -/
theorem contDiff_movingProfile {width midpoint : ℝ → ℝ}
    (hw : ContDiff ℝ 2 width) (hm : ContDiff ℝ 2 midpoint) :
    ContDiff ℝ 2 (movingProfile width midpoint) := by
  exact contDiff_profile.comp ((hw.comp contDiff_fst).prodMk
    (contDiff_snd.sub (hm.comp contDiff_fst)))

end Optimization.SteepestDescentValley
