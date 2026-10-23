import Numlib.Optimization.SteepestDescent.Exact.CorridorCurveBounds
import Numlib.Optimization.SteepestDescent.Exact.CorridorBounds

/-!
# The genuine globally bounded-below corridor objective

A final unit quintic interval flattens the scalar objective's terminal negative
slope. It preserves all prescribed finite source jets and is followed by a
constant tail. Together with the actual corridor profile this defines the
source two-dimensional objective with a uniform lower bound.
-/

open Polynomial Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- The terminal unit quintic keeps the final value and flattens both derivatives. -/
def scalarTerminalPolynomial (P : Parameters) : ℝ[X] :=
  Hermite.quinticFromResiduals
    ![scalarValue P P.horizon, -amplitude P P.horizon, 0,
      amplitude P P.horizon, amplitude P P.horizon, 0]

/-- The actual scalar source objective, with a bounded smooth terminal extension. -/
def scalarObjective (P : Parameters) : ℝ → ℝ :=
  Hermite.extendRight 2 (curve P 2) (scalarTerminalPolynomial P)
    (horizontal P P.horizon) (horizontal P P.horizon + 1)

/-- The terminal quintic genuinely matches the final source jets. -/
theorem scalarTerminalPolynomial_left (P : Parameters) (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (scalarTerminalPolynomial P).eval 0 = curveJet P 2 P.horizon j := by
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    norm_num [scalarTerminalPolynomial, Hermite.quinticFromResiduals, curveJet,
      scalarJet, Function.iterate_succ_apply', derivative_add, derivative_mul,
      derivative_pow, derivative_C, derivative_X]

/-- The terminal quintic has the final source value and zero positive-order jets. -/
theorem scalarTerminalPolynomial_right (P : Parameters) (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (scalarTerminalPolynomial P).eval 1 =
      if j = 0 then scalarValue P P.horizon else 0 := by
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;>
    norm_num [scalarTerminalPolynomial, Hermite.quinticFromResiduals,
      Function.iterate_succ_apply', derivative_add, derivative_mul,
      derivative_pow, derivative_C, derivative_X] <;> ring

private theorem scalarObjective_matching (P : Parameters) :
    ∀ j ≤ 2, iteratedDeriv j (curve P 2) (horizontal P P.horizon) =
      iteratedDeriv j (scalarTerminalPolynomial P).eval 0 := by
  intro j hj
  exact ((curve_spec P 2).2.1 P.horizon le_rfl j hj).trans
    (scalarTerminalPolynomial_left P j hj).symm

/-- The actual scalar source objective is globally twice continuously differentiable. -/
theorem contDiff_scalarObjective (P : Parameters) : ContDiff ℝ 2 (scalarObjective P) :=
  Hermite.extendRight_contDiff (curve_spec P 2).1 (by linarith)
    (scalarObjective_matching P)

/-- The terminal flattening preserves every derivative before the last iterate. -/
theorem scalarObjective_left (P : Parameters) {j : ℕ} (hj : j ≤ 2)
    {t : ℝ} (ht : t ≤ horizontal P P.horizon) :
    iteratedDeriv j (scalarObjective P) t = iteratedDeriv j (curve P 2) t :=
  Hermite.extendRight_left (curve_spec P 2).1 (by linarith)
    (scalarObjective_matching P) hj ht

/-- The genuine final transition is the translated terminal quintic. -/
theorem scalarObjective_interval (P : Parameters) {j : ℕ} (hj : j ≤ 2)
    {t : ℝ} (ht : t ∈ Icc (horizontal P P.horizon) (horizontal P P.horizon + 1)) :
    iteratedDeriv j (scalarObjective P) t =
      iteratedDeriv j (scalarTerminalPolynomial P).eval (t-horizontal P P.horizon) :=
  Hermite.extendRight_interval (curve_spec P 2).1 (by linarith)
    (scalarObjective_matching P) hj ht

/-- The actual final continuation is constant after the unit transition. -/
theorem scalarObjective_right (P : Parameters) {j : ℕ} (hj : j ≤ 2)
    {t : ℝ} (ht : horizontal P P.horizon + 1 ≤ t) :
    iteratedDeriv j (scalarObjective P) t =
      if j = 0 then scalarValue P P.horizon else 0 := by
  rw [scalarObjective, Hermite.extendRight_tail (curve_spec P 2).1 (by linarith)
    (scalarObjective_matching P) hj ht]
  have he : horizontal P P.horizon + 1 - horizontal P P.horizon = (1 : ℝ) := by ring
  simp only [he]
  rw [Hermite.taylorTail_of_flat (fun a ha ha2 => ?_), iteratedDeriv_const]
  · simp only [scalarTerminalPolynomial_right P 0 (by omega), ite_true]
  · rw [scalarTerminalPolynomial_right P a ha2, ite_eq_right (by omega : a ≠ 0)]

/-- A fixed bound controls every actual derivative of the terminal quintic. -/
theorem scalarTerminalPolynomial_uniform_bound : ∃ B > 0, ∀ (P : Parameters),
    ∀ j ≤ 2, ∀ t ∈ Icc (0 : ℝ) 1,
      |iteratedDeriv j (scalarTerminalPolynomial P).eval t| ≤ B := by
  obtain ⟨B,hB,H⟩ := Hermite.quinticFromResiduals_uniform_bound 4
  refine ⟨B,hB,?_⟩
  intro P j hj t ht
  apply H _ ?_ j hj t ht
  intro i
  have hf := scalarValue_mem P le_rfl
  have ha := amplitude_mem P le_rfl
  have ha0 := amplitude_pos P le_rfl
  fin_cases i <;> simp [abs_of_nonneg hf.1, abs_of_nonneg ha0.le] <;>
    linarith [P.accuracy_le_one]

/-- The actual scalar seed is the prescribed linear left extension. -/
theorem curve_scalar_left (P : Parameters) {t : ℝ} (ht : t ≤ 0) :
    curve P 2 t = 4 - amplitude P 0 * t := by
  have he := curve_left P 2 (j := 0) (by omega) ht
  simp only [iteratedDeriv_zero] at he
  rw [he, curveSeed, Hermite.taylorTail_two]
  simp [curveJet, scalarJet, scalarValue]
  ring

/-- The actual globally extended scalar objective has a common lower bound. -/
theorem scalarObjective_bounded_below : ∃ B > 0, ∀ (P : Parameters) (t : ℝ),
    -B ≤ scalarObjective P t := by
  obtain ⟨B,hB,H⟩ := curve_uniform_bounds
  obtain ⟨C,hC,HC⟩ := scalarTerminalPolynomial_uniform_bound
  refine ⟨B+C,by positivity,?_⟩
  intro P t
  have hxN : 0 ≤ horizontal P P.horizon := by
    rw [← horizontal_zero P]
    exact (horizontal_increasing P 0 P.horizon P.horizon_pos le_rfl).le
  by_cases ht0 : t ≤ 0
  · have he := scalarObjective_left P (j := 0) (by omega) (ht0.trans hxN)
    simp only [iteratedDeriv_zero] at he
    rw [he, curve_scalar_left P ht0]
    have ha := amplitude_pos P (k := 0) (by omega)
    nlinarith
  by_cases htN : t ≤ horizontal P P.horizon
  · have he := scalarObjective_left P (j := 0) (by omega) htN
    simp only [iteratedDeriv_zero] at he
    rw [he]
    have hb := (abs_le.mp (H P 2 0 (by omega) t
      ⟨(lt_of_not_ge ht0).le,htN⟩)).1
    simp only [iteratedDeriv_zero] at hb
    linarith
  by_cases ht1 : t ≤ horizontal P P.horizon + 1
  · have he := scalarObjective_interval P (j := 0) (by omega)
      ⟨(lt_of_not_ge htN).le,ht1⟩
    simp only [iteratedDeriv_zero] at he
    rw [he]
    have hc := (abs_le.mp (HC P 0 (by omega) (t-horizontal P P.horizon)
      ⟨by linarith,by linarith⟩)).1
    simp only [iteratedDeriv_zero] at hc
    linarith
  · have he := scalarObjective_right P (j := 0) (by omega) (lt_of_not_ge ht1).le
    simp only [iteratedDeriv_zero,ite_true] at he
    rw [he]
    linarith [(scalarValue_mem P le_rfl).1]

/-- The genuine source profile is uniformly bounded for every vertical coordinate. -/
theorem profile_bounded : ∃ B > 0, ∀ δ ∈ Icc (0 : ℝ) 2, ∀ z : ℝ,
    |profile δ z| ≤ B := by
  obtain ⟨B,hB,H⟩ := profile_derivatives_bounded
  refine ⟨B+32,by positivity,?_⟩
  intro δ hδ z
  by_cases hz : z ∈ Icc (-2 : ℝ) 2
  · have hb := H 0 (by omega) δ hδ z hz
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
    linarith
  · have he : z ≤ -δ/2-1 ∨ δ/2+1 ≤ z := by
      simp only [mem_Icc,not_and_or,not_le] at hz
      rcases hz with hz | hz
      · left; linarith [hδ.2]
      · right; linarith [hδ.2]
    rw [profile_exterior hδ.1 he, abs_of_nonneg (by positivity)]
    nlinarith [hδ.1,hδ.2]

/-- The genuine two-dimensional corridor term is uniformly bounded on the whole plane. -/
theorem residualCorridor_bounded : ∃ B > 0, ∀ (P : Parameters) (w : ℝ × ℝ),
    |residualCorridor P w| ≤ B := by
  obtain ⟨B,hB,H⟩ := profile_bounded
  refine ⟨B,hB,?_⟩
  intro P w
  apply H _ ?_
  exact ⟨P.accuracy_pos.le.trans (curve_width_mem P w.1).1,
    (curve_width_mem P w.1).2⟩

/-- The actual source objective uses the scalar curve and the genuine corridor profile. -/
def objective (P : Parameters) (w : ℝ × ℝ) : ℝ :=
  (scalarObjective P w.1 + residualCorridor P w) / Real.sqrt 2

/-- The actual source objective is globally twice continuously differentiable. -/
theorem contDiff_objective (P : Parameters) : ContDiff ℝ 2 (objective P) :=
  ((contDiff_scalarObjective P).comp contDiff_fst |>.add
    (contDiff_residualCorridor P)).div_const _

/-- A common lower bound precedes the accuracy and all finite construction data. -/
theorem objective_bounded_below : ∃ B > 0, ∀ (P : Parameters) (w : ℝ × ℝ),
    -B ≤ objective P w := by
  obtain ⟨B,hB,H⟩ := scalarObjective_bounded_below
  obtain ⟨C,hC,HC⟩ := residualCorridor_bounded
  refine ⟨(B+C)/Real.sqrt 2,by positivity,?_⟩
  intro P w
  dsimp [objective]
  rw [← neg_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  linarith [(abs_le.mp (HC P w)).1,H P w.1]

end ExactSteepestDescent.Corridor
