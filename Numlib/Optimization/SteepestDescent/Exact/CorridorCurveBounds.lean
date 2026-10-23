import Numlib.Optimization.SteepestDescent.Exact.CorridorCurves
import Numlib.Order.Interval.FiniteChain

/-!
# Uniform bounds for genuine corridor curves

The normalized terminal residuals of all three source interval families obey a
common cubic scale. Actual Hermite estimates therefore bound every finite-chain
jet uniformly, while endpoint-flat width and center curves have bounded positive
order derivatives on the whole real line.
-/

open Polynomial Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- The source quintic smooth step takes values in the unit interval. -/
theorem smoothStep_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    smoothStep.eval u ∈ Icc (0 : ℝ) 1 := by
  have hu0 := hu.1
  have hu1 : 0 ≤ 1-u := sub_nonneg.mpr hu.2
  have h0 : 0 ≤ u ^ 3 * (1 + 3 * (1-u) + 6 * (1-u)^2) := by positivity
  have h1 : 0 ≤ (1-u)^3 * (1+3*u+6*u^2) := by positivity
  simp only [smoothStep, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  constructor <;> nlinarith

/-- The narrowing polynomial remains between its two positive endpoint widths. -/
theorem widthPolynomial_mem (P : Parameters) {k : ℕ} (hk : k < P.horizon)
    {t : ℝ} (ht : t ∈ Icc 0 (amplitude P k)) :
    (widthPolynomial P k).eval t ∈ Icc (amplitude P (k+1)) (amplitude P k) := by
  have ht0 := ht.1
  have ha := amplitude_pos P (Nat.le_of_lt hk)
  have hstep := smoothStep_mem (u := (amplitude P k)⁻¹*t) (by
    constructor
    · positivity
    · exact (inv_mul_le_iff₀ ha).mpr (by simpa using ht.2))
  have hh : 0 ≤ widthIncrement P := by
    unfold widthIncrement
    exact div_nonneg P.accuracy_pos.le P.horizon_cast_pos.le
  simp only [widthPolynomial, eval_sub, eval_C, eval_mul, eval_comp, eval_X]
  rw [amplitude_succ]
  constructor <;> nlinarith [hstep.1,hstep.2]

/-- The source initial Taylor polynomial of degree two has the expected formula. -/
theorem initialPolynomial_two (a : ℕ → ℝ) :
    Hermite.initialPolynomial 2 a = C (a 0) + C (a 1)*X + C (a 2/2)*X^2 := by
  simp [Hermite.initialPolynomial, Hermite.jetPoly, Finset.sum_range_succ]

/-- Actual initial source jets are bounded independently of the accuracy and horizon. -/
theorem curveJet_abs_le (P : Parameters) (i : Fin 3) {k : ℕ}
    (hk : k ≤ P.horizon) (j : ℕ) (hj : j ≤ 2) : |curveJet P i k j| ≤ 4 := by
  have ha := amplitude_mem P hk
  have ha0 := amplitude_pos P hk
  have hm := centerValue_mem P k
  have hf := scalarValue_mem P hk
  fin_cases i <;> interval_cases j <;>
    simp [curveJet, widthJet, centerJet, scalarJet, abs_of_nonneg ha0.le,
      abs_of_nonneg hm.1, abs_of_nonneg hf.1] <;>
    linarith [P.accuracy_le_one]

/-- The actual terminal residuals obey uniform third-order Hermite scaling. -/
theorem curvePolynomial_residual (P : Parameters) (i : Fin 3) {k : ℕ}
    (hk : k < P.horizon) (j : ℕ) (hj : j ≤ 2) :
    |curveJet P i (k+1) j -
      (derivative^[j] (Hermite.initialPolynomial 2 (curveJet P i k))).eval
        (amplitude P k)| ≤ 4 * amplitude P k ^ (2-j+1) := by
  have ha := amplitude_pos P hk.le
  have haε := amplitude_mem P hk.le
  have hh0 : 0 ≤ widthIncrement P :=
    div_nonneg P.accuracy_pos.le P.horizon_cast_pos.le
  have hh3 := widthIncrement_le_two_mul_amplitude_cube P hk.le
  have hh2 : widthIncrement P ≤ 2 * amplitude P k ^ 2 := by
    have hε := P.accuracy_le_one
    have hhε := widthIncrement_le_two_mul_cube P
    have hsq := pow_le_pow_left₀ P.accuracy_pos.le haε.1 2
    nlinarith [sq_nonneg P.accuracy, mul_nonneg (sq_nonneg P.accuracy)
      (sub_nonneg.mpr hε)]
  have hsign : |(-1 : ℝ)^k| = 1 := by simp
  have hsign' : -1 ≤ (-1 : ℝ)^k ∧ (-1 : ℝ)^k ≤ 1 := by
    simpa only [abs_le] using (show |(-1 : ℝ)^k| ≤ 1 by simp)
  rw [initialPolynomial_two]
  apply abs_le.mpr
  constructor <;> fin_cases i <;> interval_cases j <;>
    simp [curveJet, widthJet, centerJet, scalarJet, Function.iterate_succ_apply',
      derivative_add, derivative_mul, derivative_C, derivative_X,
      amplitude_succ, centerValue_succ, scalarValue_succ] <;>
    nlinarith [pow_nonneg ha.le 3]

/-- Actual interval polynomials have uniform bounds on all derivatives through
order two, and a uniform Lipschitz constant for their second derivatives. -/
theorem curvePolynomial_uniform_bounds : ∃ L > 0, ∃ B > 0,
    ∀ (P : Parameters) (i : Fin 3) (k : ℕ), k < P.horizon →
    (∀ u ∈ Icc 0 (amplitude P k), ∀ v ∈ Icc 0 (amplitude P k),
      |iteratedDeriv 2 (curvePolynomial P i k).eval u -
        iteratedDeriv 2 (curvePolynomial P i k).eval v| ≤ L * |u-v|) ∧
    ∀ j ≤ 2, ∀ t ∈ Icc 0 (amplitude P k),
      |iteratedDeriv j (curvePolynomial P i k).eval t| ≤ B := by
  obtain ⟨L,hL,B,hB,H⟩ := Hermite.endpointPolynomial_uniform_bounds 2 4 (by norm_num)
  refine ⟨L,hL,B,hB,?_⟩
  intro P i k hk
  have heq : curvePolynomial P i k = Hermite.endpointPolynomial 2 (amplitude P k)
      (curveJet P i k) (curveJet P i (k+1)) := by
    fin_cases i
    · exact widthPolynomial_eq_endpoint P hk
    · exact centerPolynomial_eq_endpoint P hk
    · exact scalarPolynomial_eq_endpoint P hk
  rw [heq]
  have hb := H (amplitude P k) (amplitude_pos P hk.le)
    (curveJet P i k) (curveJet P i (k+1)) (curvePolynomial_residual P i hk)
  refine ⟨hb.1, hb.2 (curveJet_abs_le P i hk.le) ?_⟩
  have ha := (amplitude_mem P hk.le).2
  linarith [P.accuracy_le_one]

/-- The width of the actual global source corridor remains positive and at most two. -/
theorem curve_width_mem (P : Parameters) (t : ℝ) : curve P 0 t ∈ Icc P.accuracy 2 := by
  by_cases ht0 : t ≤ 0
  · have he := curve_left P 0 (j := 0) (by omega) ht0
    simp only [iteratedDeriv_zero] at he
    rw [he, curveSeed, Hermite.taylorTail_of_flat
      (fun a ha _ => curveJet_flat P (by decide : (0 : Fin 3) ≠ 2) 0 a ha)]
    simp only [curveJet, Matrix.cons_val_zero, widthJet, ite_true]
    rw [amplitude_zero]
    constructor <;> linarith [P.accuracy_pos, P.accuracy_le_one]
  by_cases htN : horizontal P P.horizon ≤ t
  · have he := curve_right_flat P (by decide : (0 : Fin 3) ≠ 2)
      (j := 0) (by omega) htN
    simp only [iteratedDeriv_zero, ite_true] at he
    rw [he]
    simp only [curveJet, Matrix.cons_val_zero, widthJet, ite_true, amplitude_horizon]
    exact ⟨le_rfl, P.accuracy_le_one.trans (by norm_num)⟩
  obtain ⟨k,hk,hkt⟩ := exists_mem_Icc_adjacent (horizontal P) P.horizon_pos
    (t := t) (by rw [horizontal_zero]; exact ⟨(lt_of_not_ge ht0).le,
      (lt_of_not_ge htN).le⟩)
  have he := (curve_spec P 0).2.2 k hk 0 (by omega) t hkt
  simp only [iteratedDeriv_zero] at he
  rw [he]
  have hm := widthPolynomial_mem P hk (t := t-horizontal P k) (by
    rw [horizontal_succ] at hkt
    constructor <;> linarith [hkt.1,hkt.2])
  have ha := amplitude_mem P hk.le
  have ha' := amplitude_mem P (Nat.succ_le_of_lt hk)
  change P.accuracy ≤ (widthPolynomial P k).eval (t-horizontal P k) ∧
    (widthPolynomial P k).eval (t-horizontal P k) ≤ 2
  constructor <;> linarith [hm.1,hm.2,P.accuracy_le_one]

/-- All three actual finite chains have uniform jets over the entire source grid. -/
theorem curve_uniform_bounds : ∃ B > 0, ∀ (P : Parameters) (i : Fin 3),
    ∀ j ≤ 2, ∀ t ∈ Icc 0 (horizontal P P.horizon),
      |iteratedDeriv j (curve P i) t| ≤ B := by
  obtain ⟨L,hL,B,hB,H⟩ := curvePolynomial_uniform_bounds
  refine ⟨B,hB,?_⟩
  intro P i j hj t ht
  obtain ⟨k,hk,hkt⟩ := exists_mem_Icc_adjacent (horizontal P) P.horizon_pos
    (by simpa only [horizontal_zero] using ht)
  rw [(curve_spec P i).2.2 k hk j hj t hkt]
  apply (H P i k hk).2 j hj
  rw [horizontal_succ] at hkt
  constructor <;> linarith [hkt.1,hkt.2]

/-- Width and center have uniformly bounded first and second derivatives globally;
the endpoint Taylor seeds and terminal tails are exactly constant. -/
theorem curve_flat_derivatives_bounded : ∃ B > 0, ∀ (P : Parameters) (i : Fin 3),
    i ≠ 2 → ∀ j, 1 ≤ j → j ≤ 2 → ∀ t : ℝ,
      |iteratedDeriv j (curve P i) t| ≤ B := by
  obtain ⟨B,hB,H⟩ := curve_uniform_bounds
  refine ⟨B,hB,?_⟩
  intro P i hi j hj hj2 t
  by_cases ht0 : t ≤ 0
  · rw [curve_left P i hj2 ht0, curveSeed,
      Hermite.taylorTail_of_flat (fun a ha _ => curveJet_flat P hi 0 a ha),
      iteratedDeriv_const]
    simp only [ite_eq_right (by omega : j ≠ 0), abs_zero]
    exact hB.le
  by_cases htN : horizontal P P.horizon ≤ t
  · rw [curve_right_flat P hi hj2 htN]
    simp only [ite_eq_right (by omega : j ≠ 0), abs_zero]
    exact hB.le
  exact H P i j hj2 t ⟨(lt_of_not_ge ht0).le,(lt_of_not_ge htN).le⟩

end ExactSteepestDescent.Corridor
