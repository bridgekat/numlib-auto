import Numlib.Approximation.Hermite.Quintic
import Numlib.Approximation.Hermite.TwoSided

/-!
# Smooth coefficient profiles for quintic corridor strips

Three fixed univariate profiles realize the source quintic transition from a
central square to an exterior plateau. Each profile is genuinely twice
continuously differentiable, with a polynomial left continuation and constant
right continuation. Combining the two reflected strips produces the full
corridor function without piecewise differentiation along curved boundaries.
-/

open Polynomial Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- Fixed quintic coefficient polynomials for the squared-width, width and
constant parts of a corridor transition strip. -/
def coefficientPolynomial (i : Fin 3) : ℝ[X] :=
  Hermite.quinticFromResiduals
    (![![(1 / 4 : ℝ), 0, 0, 31 / 4, 0, 0],
       ![0, 1, 0, -1, -1, 0], ![0, 0, 2, -1, -2, -2]] i)

/-- The actual twice continuously differentiable coefficient profile. -/
def coefficientProfile (i : Fin 3) : ℝ → ℝ :=
  Hermite.twoSidedTaylor 2 (coefficientPolynomial i) 1

/-- Every coefficient profile is genuinely twice continuously differentiable. -/
theorem contDiff_coefficientProfile (i : Fin 3) : ContDiff ℝ 2 (coefficientProfile i) :=
  Hermite.contDiff_twoSidedTaylor 2 _ (by norm_num)

/-- The positive-order right endpoint jets of all three quintics vanish. -/
theorem coefficientPolynomial_right_flat (i : Fin 3) (j : ℕ) (hj : 1 ≤ j)
    (hj2 : j ≤ 2) : iteratedDeriv j (coefficientPolynomial i).eval 1 = 0 := by
  fin_cases i <;> interval_cases j <;>
    simp only [Polynomial.iteratedDeriv_eval] <;>
    norm_num [coefficientPolynomial, Hermite.quinticFromResiduals,
      Function.iterate_succ_apply', derivative_add,
      derivative_C_mul, derivative_pow, derivative_X]

/-- On the left, the profiles are respectively one quarter, u and u squared. -/
theorem coefficientProfile_left (i : Fin 3) {u : ℝ} (hu : u ≤ 0) :
    coefficientProfile i u = ![(1 / 4 : ℝ), u, u ^ 2] i := by
  have he := Hermite.twoSidedTaylor_left 2 (coefficientPolynomial i)
    (s := (1 : ℝ)) (by norm_num) (j := 0) (by norm_num) hu
  simp only [iteratedDeriv_zero] at he
  change coefficientProfile i u = _ at he
  rw [he, Hermite.taylorTail_two]
  fin_cases i <;>
    simp only [Polynomial.iteratedDeriv_eval] <;>
    norm_num [coefficientPolynomial, Hermite.quinticFromResiduals,
      Function.iterate_succ_apply', derivative_add,
      derivative_C_mul, derivative_pow, derivative_X]

/-- Beyond the strip, the profiles are respectively eight, zero and zero. -/
theorem coefficientProfile_right (i : Fin 3) {u : ℝ} (hu : 1 ≤ u) :
    coefficientProfile i u = ![(8 : ℝ), 0, 0] i := by
  have he := Hermite.twoSidedTaylor_right_flat 2 (coefficientPolynomial i)
    (by norm_num : (0 : ℝ) < 1) (coefficientPolynomial_right_flat i)
    (j := 0) (by norm_num) hu
  simp only [iteratedDeriv_zero, ite_true] at he
  change coefficientProfile i u = _ at he
  rw [he]
  fin_cases i <;> norm_num [coefficientPolynomial, Hermite.quinticFromResiduals]

/-- On the unit strip, each actual profile equals its explicit quintic polynomial. -/
theorem coefficientProfile_interval (i : Fin 3) {u : ℝ} (hu : u ∈ Icc 0 1) :
    coefficientProfile i u = (coefficientPolynomial i).eval u := by
  exact Hermite.twoSidedTaylor_interval 2 _ (by norm_num) (j := 0) (by norm_num) hu

/-- A single constant bounds the actual profile derivatives through order two
on the positive half-line, before every profile index and evaluation point. -/
theorem coefficientProfiles_bounded : ∃ B > 0, ∀ (i : Fin 3) (j : ℕ), j ≤ 2 →
    ∀ u : ℝ, 0 ≤ u → |iteratedDeriv j (coefficientProfile i) u| ≤ B := by
  have hex (i : Fin 3) := Hermite.twoSidedTaylor_bounded_nonneg 2
    (coefficientPolynomial i) (by norm_num : (0 : ℝ) < 1)
    (coefficientPolynomial_right_flat i)
  choose B hB hb using hex
  refine ⟨max (B 0) (max (B 1) (B 2)), (hB 0).trans_le (le_max_left _ _), ?_⟩
  intro i j hj u hu
  apply (hb i j hj u hu).trans
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- One smooth lower transition, with a polynomial continuation into the corridor. -/
def lowerProfile (δ z : ℝ) : ℝ :=
  δ ^ 2 * coefficientProfile 0 (-z - δ / 2) +
    δ * coefficientProfile 1 (-z - δ / 2) + coefficientProfile 2 (-z - δ / 2)

/-- Two reflected transitions combine into the actual symmetric corridor profile. -/
def profile (δ z : ℝ) : ℝ := lowerProfile δ z + lowerProfile δ (-z) - z ^ 2

/-- The lower profile equals the central square on the entire inner half-line. -/
theorem lowerProfile_inner {δ z : ℝ} (hz : -δ / 2 ≤ z) : lowerProfile δ z = z ^ 2 := by
  have hu : -z - δ / 2 ≤ 0 := by linarith
  simp only [lowerProfile, coefficientProfile_left _ hu, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- The lower profile is the exterior plateau beyond distance one from the wall. -/
theorem lowerProfile_exterior {δ z : ℝ} (hz : z ≤ -δ / 2 - 1) :
    lowerProfile δ z = 8 * δ ^ 2 := by
  have hu : 1 ≤ -z - δ / 2 := by linarith
  simp only [lowerProfile, coefficientProfile_right _ hu, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, mul_zero, add_zero]
  ring

/-- In a nonnegative-width corridor, the combined profile is the central square. -/
theorem profile_central {δ z : ℝ} (hz : -δ / 2 ≤ z ∧ z ≤ δ / 2) :
    profile δ z = z ^ 2 := by
  rw [profile, lowerProfile_inner hz.1, lowerProfile_inner (by linarith : -δ / 2 ≤ -z)]
  ring

/-- Below the corridor the reflected inner contribution cancels exactly. -/
theorem profile_lower {δ z : ℝ} (hδ : 0 ≤ δ) (hz : z ≤ -δ / 2) :
    profile δ z = lowerProfile δ z := by
  rw [profile, lowerProfile_inner (by linarith : -δ / 2 ≤ -z)]
  ring

/-- Above the corridor the original inner contribution cancels exactly. -/
theorem profile_upper {δ z : ℝ} (hδ : 0 ≤ δ) (hz : δ / 2 ≤ z) :
    profile δ z = lowerProfile δ (-z) := by
  rw [profile, lowerProfile_inner (by linarith : -δ / 2 ≤ z)]
  ring

/-- The two symmetric exterior regions have the exact source plateau value. -/
theorem profile_exterior {δ z : ℝ} (hδ : 0 ≤ δ)
    (hz : z ≤ -δ / 2 - 1 ∨ δ / 2 + 1 ≤ z) : profile δ z = 8 * δ ^ 2 := by
  rcases hz with hz | hz
  · rw [profile_lower hδ (by linarith), lowerProfile_exterior hz]
  · rw [profile_upper hδ (by linarith), lowerProfile_exterior (by linarith)]

/-- The genuine corridor profile is jointly twice continuously differentiable. -/
theorem contDiff_profile : ContDiff ℝ 2 (fun w : ℝ × ℝ => profile w.1 w.2) := by
  have hl : ContDiff ℝ 2 (fun w : ℝ × ℝ => lowerProfile w.1 w.2) := by
    unfold lowerProfile
    have ha : ContDiff ℝ 2 (fun w : ℝ × ℝ => -w.2 - w.1 / 2) := by fun_prop
    exact (((contDiff_fst.pow 2).mul ((contDiff_coefficientProfile 0).comp ha)).add
      (contDiff_fst.mul ((contDiff_coefficientProfile 1).comp ha))).add
        ((contDiff_coefficientProfile 2).comp ha)
  unfold profile
  exact (hl.add (hl.comp (contDiff_fst.prodMk contDiff_snd.neg))).sub (contDiff_snd.pow 2)


/-- On the unit outward-distance strip, the lower transition is the exact
source quintic, decomposed into squared-width, width and constant terms. -/
theorem lowerProfile_strip_formula (δ : ℝ) {u : ℝ} (hu : u ∈ Icc 0 1) :
    lowerProfile δ (-δ / 2 - u) =
      δ ^ 2 * (1 / 4 + 155 / 2 * u ^ 3 - 465 / 4 * u ^ 4 + 93 / 2 * u ^ 5) +
      δ * (u - 6 * u ^ 3 + 8 * u ^ 4 - 3 * u ^ 5) +
        (u ^ 2 - 3 * u ^ 3 + 3 * u ^ 4 - u ^ 5) := by
  have he : -(-δ / 2 - u) - δ / 2 = u := by ring
  simp only [lowerProfile, he, coefficientProfile_interval _ hu]
  norm_num [coefficientPolynomial, Hermite.quinticFromResiduals]
  ring

/-- Reflection preserves the genuine symmetric corridor profile. -/
theorem profile_neg (δ z : ℝ) : profile δ (-z) = profile δ z := by
  simp only [profile, neg_neg, neg_sq]
  ring

/-- The actual two-dimensional corridor function for supplied width and center. -/
def corridorFunction (width center : ℝ → ℝ) (w : ℝ × ℝ) : ℝ :=
  profile (width w.1) (w.2 - center w.1)

/-- Twice continuously differentiable width and center functions give a genuine
twice continuously differentiable corridor function, including every strip join. -/
theorem contDiff_corridorFunction {width center : ℝ → ℝ}
    (hw : ContDiff ℝ 2 width) (hc : ContDiff ℝ 2 center) :
    ContDiff ℝ 2 (corridorFunction width center) := by
  exact contDiff_profile.comp ((hw.comp contDiff_fst).prodMk
    (contDiff_snd.sub (hc.comp contDiff_fst)))

end ExactSteepestDescent.Corridor
