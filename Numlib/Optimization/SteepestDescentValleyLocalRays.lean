import Numlib.Optimization.SteepestDescentValleySmoothBounds
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Local descent rays of the finite valley

The prescribed cells lie in the quadratic core, and their restrictions admit explicit
polynomial formulas. Local minima are distinct from global line minimizers.
-/

noncomputable section
open Set Polynomial Hermite

namespace Optimization.SteepestDescentValley

/-- The smoothing profile grows at most at its sharp derivative bound. -/
theorem smoothStep_le_mul {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    smoothStep t ≤ (15 / 8 : ℝ) * t := by
  have hs : ContDiff ℝ ⊤ smoothStep := by
    change ContDiff ℝ ⊤ (fun t => smoothStep t)
    simp only [smoothStep_eq]
    fun_prop
  have h := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hs.continuous.continuousOn
    (hs.differentiable (by simp)).differentiableOn
    (fun x hx => (le_abs_self _).trans (abs_deriv_smoothStep_le
      (interior_subset hx))) 0 (by norm_num) t ht ht.1
  simpa [smoothStep_eq] using h

/-- On every source cell the width decrement is at most half its length. -/
theorem lengthDrop_le_half_cellLength (P : Parameters) {k : ℕ} (hk : k < P.count) :
    lengthDrop P ≤ cellLength P k / 2 := by
  have h := (cellLength_bounds P (show k + 1 ≤ P.count by omega)).1
  rw [cellLength_succ] at h
  linarith [lengthDrop_le_eps P]

/-- The affine direction from one prescribed node to its successor. -/
def cellDirection (P : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![cellLength P k, cellSign k * cellLength P k]

/-- The affine line through a prescribed cell, with its successor at parameter one. -/
def cellRayPoint (P : Parameters) (k : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  nodePoint P k + t • cellDirection P k

/-- The two coordinates of the affine cell ray. -/
@[simp] theorem cellRayPoint_coordinates (P : Parameters) (k : ℕ) (t : ℝ) :
    cellRayPoint P k t 0 = nodeX P k + cellLength P k * t ∧
      cellRayPoint P k t 1 = nodeY P k + cellSign k * cellLength P k * t := by
  constructor <;> simp [cellRayPoint, cellDirection, nodePoint, mul_comm ]

/-- The horizontal coordinate of a normalized cell lies in its closed source interval. -/
theorem cellRayPoint_horizontal_mem (P : Parameters) {k : ℕ} (hk : k < P.count)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    nodeX P k + cellLength P k * t ∈ Icc (nodeX P k) (nodeX P (k + 1)) := by
  rw [nodeX_succ]
  constructor <;> nlinarith [cellLength_pos P hk.le, ht.1, ht.2]

/-- Along a prescribed segment the centered vertical coordinate stays in the closed
quadratic core, including both endpoints. -/
theorem cellRayPoint_mem_core (P : Parameters) {k : ℕ} (hk : k < P.count)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    -scalarWidth P (cellRayPoint P k t 0) / 2 ≤
        cellRayPoint P k t 1 - scalarMidpoint P (cellRayPoint P k t 0) ∧
      cellRayPoint P k t 1 - scalarMidpoint P (cellRayPoint P k t 0) ≤
        scalarWidth P (cellRayPoint P k t 0) / 2 := by
  obtain ⟨hx, hy⟩ := cellRayPoint_coordinates P k t
  rw [hx, hy, scalarWidth_cell P hk (cellRayPoint_horizontal_mem P hk ht),
    scalarMidpoint_cell P hk (cellRayPoint_horizontal_mem P hk ht)]
  have hs : cellLength P k ≠ 0 := (cellLength_pos P hk.le).ne'
  have hcoord : (nodeX P k + cellLength P k * t - nodeX P k) / cellLength P k = t := by
    field_simp
    ring
  rw [hcoord, nodeMidpoint]
  have hS := smoothStep_mem_Icc ht
  have hSt := smoothStep_le_mul ht
  have hD := lengthDrop_le_half_cellLength P hk
  have hDt : lengthDrop P * smoothStep t ≤ cellLength P k * t := by
    have h := mul_le_mul_of_nonneg_right hD hS.1
    have h' := mul_le_mul_of_nonneg_left hSt (cellLength_pos P hk.le).le
    nlinarith [mul_nonneg (cellLength_pos P hk.le).le ht.1]
  have hu : cellLength P k * t - cellLength P k / 2 - lengthDrop P * smoothStep t / 2 ≤
      (cellLength P k - lengthDrop P * smoothStep t) / 2 := by
    nlinarith [mul_nonneg (cellLength_pos P hk.le).le (sub_nonneg.mpr ht.2)]
  have hl : -(cellLength P k - lengthDrop P * smoothStep t) / 2 ≤
      cellLength P k * t - cellLength P k / 2 - lengthDrop P * smoothStep t / 2 := by linarith
  have habs : |cellSign k| = 1 := abs_cellSign k
  have hsign : cellSign k = 1 ∨ cellSign k = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs
  rcases hsign with hsign | hsign <;> rw [hsign] <;> constructor <;> linarith

/-- The explicit unnormalized polynomial restriction of a source cell. -/
def cellRayPolynomial (P : Parameters) (k : ℕ) : ℝ[X] :=
  C (nodeValue P k) - C (cellLength P k ^ 2) * X +
    C (cellLength P k * lengthDrop P) * (-4 * X ^ 3 + 7 * X ^ 4 - 3 * X ^ 5) +
    (C (cellLength P k) * X - C (cellLength P k / 2) -
      C (lengthDrop P / 2) * smoothStepPolynomial) ^ 2

/-- The actual objective restricted to a prescribed segment equals its explicit core
polynomial; this is an identity of the constructed functions. -/
theorem euclideanObjective_cellRay (P : Parameters) {k : ℕ} (hk : k < P.count)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    euclideanObjective P (cellRayPoint P k t) =
      (cellRayPolynomial P k).eval t / Real.sqrt 2 := by
  obtain ⟨hx, hy⟩ := cellRayPoint_coordinates P k t
  obtain ⟨hl, hu⟩ := cellRayPoint_mem_core P hk ht
  rw [euclideanObjective, euclideanMovingProfile, profile_core hl hu, hx, hy,
    scalarObjective_cell P hk (cellRayPoint_horizontal_mem P hk ht),
    scalarMidpoint_cell P hk (cellRayPoint_horizontal_mem P hk ht)]
  have hs : cellLength P k ≠ 0 := (cellLength_pos P hk.le).ne'
  have hcoord : (nodeX P k + cellLength P k * t - nodeX P k) / cellLength P k = t := by
    field_simp
    ring
  rw [hcoord, nodeMidpoint]
  congr 1
  have hsign : cellSign k ^ 2 = 1 := by
    rw [← sq_abs, abs_cellSign]
    norm_num
  simp only [cellRayPolynomial, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
    eval_ofNat, eval_neg, smoothStep]
  linear_combination (cellLength P k * t - cellLength P k / 2 -
    lengthDrop P * smoothStepPolynomial.eval t / 2) ^ 2 * hsign

/-- The full affine ray restriction is genuinely twice continuously differentiable. -/
theorem contDiff_euclideanObjective_cellRay (P : Parameters) (k : ℕ) :
    ContDiff ℝ 2 (fun t => euclideanObjective P (cellRayPoint P k t)) := by
  apply (contDiff_euclideanObjective P).comp
  unfold cellRayPoint
  fun_prop

/-- The actual derivatives of the full ray restriction agree with the explicit
polynomial on the closed cell, including the successor endpoint. -/
theorem iteratedDeriv_euclideanObjective_cellRay (P : Parameters) {k j : ℕ}
    (hk : k < P.count) (hj : j ≤ 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDeriv j (fun t => euclideanObjective P (cellRayPoint P k t)) t =
      ((derivative^[j]) (cellRayPolynomial P k)).eval t / Real.sqrt 2 := by
  have hg : ContDiff ℝ 2 (fun t => (cellRayPolynomial P k).eval t / Real.sqrt 2) :=
    by
      simp only [cellRayPolynomial, smoothStepPolynomial, eval_add, eval_sub, eval_mul,
        eval_pow, eval_C, eval_X, eval_ofNat, eval_neg]
      fun_prop
  rw [iteratedDeriv_eq_of_eqOn_unitInterval (contDiff_euclideanObjective_cellRay P k) hg
    (fun t ht => euclideanObjective_cellRay P hk ht) hj ht, iteratedDeriv_div_const,
    Polynomial.iteratedDeriv_eval]

/-- The first derivative of the actual cell polynomial, organized into the scalar
slope and the vertical quadratic-core chain term. -/
theorem derivative_cellRayPolynomial (P : Parameters) (k : ℕ) (t : ℝ) :
    (cellRayPolynomial P k).derivative.eval t =
      cellLength P k * (-cellLength P k + lengthDrop P * slopeAdjustment t) +
        2 * (cellLength P k * t - cellLength P k / 2 - lengthDrop P * smoothStep t / 2) *
          (cellLength P k - lengthDrop P * deriv smoothStep t / 2) := by
  simp [cellRayPolynomial, smoothStepPolynomial, slopeAdjustment_eq,
    smoothStep_eq, deriv_smoothStep, derivative_pow]
  ring

/-- At the successor the actual ray restriction has zero first derivative and
strictly positive second derivative. -/
theorem euclideanObjective_cellRay_endpoint_jets (P : Parameters) {k : ℕ} (hk : k < P.count) :
    deriv (fun t => euclideanObjective P (cellRayPoint P k t)) 1 = 0 ∧
      deriv (deriv (fun t => euclideanObjective P (cellRayPoint P k t))) 1 =
        2 * cellLength P k ^ 2 / Real.sqrt 2 := by
  have h1 := iteratedDeriv_euclideanObjective_cellRay P hk (j := 1) (by omega)
    (t := 1) (by norm_num)
  have h2 := iteratedDeriv_euclideanObjective_cellRay P hk (j := 2) (by omega)
    (t := 1) (by norm_num)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Function.iterate_succ_apply',
    Function.iterate_zero, id_eq] at h1 h2
  constructor
  · rw [h1, derivative_cellRayPolynomial]
    norm_num [smoothStep_eq, deriv_smoothStep, slopeAdjustment_eq]
    ring
  · rw [h2]
    congr 1
    simp [cellRayPolynomial, smoothStepPolynomial, derivative_pow]
    ring

/-- Every prescribed successor is an actual local minimum on its affine descent line. -/
theorem isLocalMin_euclideanObjective_cellRay (P : Parameters) {k : ℕ} (hk : k < P.count) :
    IsLocalMin (fun t => euclideanObjective P (cellRayPoint P k t)) 1 := by
  obtain ⟨h1, h2⟩ := euclideanObjective_cellRay_endpoint_jets P hk
  apply isLocalMin_of_deriv_deriv_pos (by
    rw [h2]
    positivity [cellLength_pos P hk.le]) h1
  exact (contDiff_euclideanObjective_cellRay P k).continuous.continuousAt

/-- Before the successor the actual derivative on the prescribed affine ray is
strictly negative; hence there can be no earlier local minimum. -/
theorem deriv_euclideanObjective_cellRay_neg (P : Parameters) {k : ℕ} (hk : k < P.count)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    deriv (fun t => euclideanObjective P (cellRayPoint P k t)) t < 0 := by
  have hjet := iteratedDeriv_euclideanObjective_cellRay P hk (j := 1) (by omega)
    (t := t) ⟨ht.1, ht.2.le⟩
  simp only [iteratedDeriv_one, Function.iterate_one] at hjet
  rw [hjet, derivative_cellRayPolynomial]
  apply div_neg_of_neg_of_pos ?_ (Real.sqrt_pos.mpr (by norm_num))
  have hs := cellLength_pos P hk.le
  have hdrop := lengthDrop_pos P
  by_cases ht0 : t = 0
  · subst t
    norm_num [smoothStep_eq, deriv_smoothStep, slopeAdjustment_eq]
    nlinarith [sq_pos_of_pos hs]
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
  have hS := smoothStep_mem_Icc ⟨ht.1, ht.2.le⟩
  have hD := lengthDrop_le_half_cellLength P hk
  have hder0 : 0 ≤ deriv smoothStep t := by rw [deriv_smoothStep]; positivity
  have hder := (le_abs_self _).trans (abs_deriv_smoothStep_le ⟨ht.1, ht.2.le⟩)
  let A := cellLength P k - lengthDrop P * deriv smoothStep t / 2
  let d := cellLength P k - lengthDrop P * smoothStep t
  let u := cellLength P k * t - cellLength P k / 2 - lengthDrop P * smoothStep t / 2
  have hA0 : 0 ≤ A := by
    have h := mul_le_mul_of_nonneg_right hD hder0
    have h' := mul_le_mul_of_nonneg_left hder hs.le
    dsimp [A]
    nlinarith
  have hA : A ≤ cellLength P k := by
    dsimp [A]
    nlinarith [mul_nonneg hdrop.le hder0]
  have hd : 0 ≤ d := by
    have h := mul_le_mul_of_nonneg_left hS.2 hdrop.le
    dsimp [d]
    linarith
  have hu : 2 * u ≤ d := by
    dsimp [u, d]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr ht.2.le)]
  have hprod := (mul_le_mul_of_nonneg_right hu hA0).trans
    (mul_le_mul_of_nonneg_left hA hd)
  have hgap : cellLength P k * (-cellLength P k + lengthDrop P * slopeAdjustment t) +
      d * cellLength P k < 0 := by
    have hneg := mul_neg_of_pos_of_neg (mul_pos hs hdrop)
      (sub_neg.mpr (slopeAdjustment_lt_smoothStep ht'))
    dsimp [d]
    nlinarith
  change cellLength P k * (-cellLength P k + lengthDrop P * slopeAdjustment t) + 2 * u * A < 0
  linarith

/-- The prescribed successor is the first local minimum of the full affine ray
restriction, with all nonnegative earlier parameters excluded. -/
theorem firstLocalMin_euclideanObjective_cellRay (P : Parameters) {k : ℕ} (hk : k < P.count) :
    IsLocalMin (fun t => euclideanObjective P (cellRayPoint P k t)) 1 ∧
      ∀ t ∈ Ico (0 : ℝ) 1, ¬ IsLocalMin (fun t => euclideanObjective P (cellRayPoint P k t)) t := by
  refine ⟨isLocalMin_euclideanObjective_cellRay P hk, fun t ht hmin => ?_⟩
  have hneg := deriv_euclideanObjective_cellRay_neg P hk ht
  rw [hmin.deriv_eq_zero] at hneg
  exact (lt_irrefl (0 : ℝ)) hneg

/-- The affine cell direction is the actual negative-gradient direction with the
source step parameter square root two. -/
theorem cellDirection_eq_neg_gradient (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    cellDirection P k = -Real.sqrt 2 • gradient (euclideanObjective P) (nodePoint P k) := by
  rw [gradient_euclideanObjective_node P hk]
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  ext i
  fin_cases i <;> simp [cellDirection, nodeGradient, div_eq_mul_inv]
  all_goals field_simp

/-- The actual steepest-descent ray is exactly the normalized affine cell ray. -/
theorem negativeGradientRay_eq_cellRay (P : Parameters) {k : ℕ} (hk : k ≤ P.count) (a : ℝ) :
    nodePoint P k - a • gradient (euclideanObjective P) (nodePoint P k) =
      cellRayPoint P k (a / Real.sqrt 2) := by
  rw [cellRayPoint, cellDirection_eq_neg_gradient P hk, smul_smul]
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h : a / Real.sqrt 2 * -Real.sqrt 2 = -a := by field_simp
  rw [h, neg_smul, sub_eq_add_neg]

/-- Each prescribed actual negative-gradient step is the first local ray minimum.
The conclusion concerns local minima and makes no global ray-minimizer claim. -/
theorem firstLocalMin_negativeGradientRay (P : Parameters) {k : ℕ} (hk : k < P.count) :
    IsLocalMin (fun a => euclideanObjective P
      (nodePoint P k - a • gradient (euclideanObjective P) (nodePoint P k))) (Real.sqrt 2) ∧
      ∀ a ∈ Ico (0 : ℝ) (Real.sqrt 2), ¬ IsLocalMin (fun a => euclideanObjective P
        (nodePoint P k - a • gradient (euclideanObjective P) (nodePoint P k))) a := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨hmin, hfirst⟩ := firstLocalMin_euclideanObjective_cellRay P hk
  constructor
  · have h : IsLocalMin (fun t => euclideanObjective P (cellRayPoint P k t))
        ((fun a : ℝ => a / Real.sqrt 2) (Real.sqrt 2)) := by simpa [hsqrt.ne'] using hmin
    have hcomp := h.comp_continuous (g := fun a : ℝ => a / Real.sqrt 2)
      (b := Real.sqrt 2) (by fun_prop)
    simpa only [Function.comp_def, ← negativeGradientRay_eq_cellRay P hk.le] using hcomp
  · intro a ha hlocal
    have h : IsLocalMin (fun a => euclideanObjective P
        (nodePoint P k - a • gradient (euclideanObjective P) (nodePoint P k)))
        ((fun t : ℝ => t * Real.sqrt 2) (a / Real.sqrt 2)) := by
      simpa [hsqrt.ne'] using hlocal
    have hcomp := h.comp_continuous (g := fun t : ℝ => t * Real.sqrt 2)
      (b := a / Real.sqrt 2) (by fun_prop)
    have heq : (fun t : ℝ => euclideanObjective P
        (nodePoint P k - (t * Real.sqrt 2) • gradient (euclideanObjective P) (nodePoint P k))) =
        (fun t => euclideanObjective P (cellRayPoint P k t)) := by
      ext t
      rw [negativeGradientRay_eq_cellRay P hk.le, mul_div_cancel_right₀ _ hsqrt.ne']
    apply hfirst (a / Real.sqrt 2)
      ⟨div_nonneg ha.1 hsqrt.le, (div_lt_one hsqrt).mpr ha.2⟩
    simpa only [Function.comp_def, heq] using hcomp

end Optimization.SteepestDescentValley
