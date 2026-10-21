import Numlib.Optimization.TransverseCubicModel

/-!
# Global-minimum accepted points on an inverse-square-root tail

The actual cubic Taylor model of the fixed transverse objective selects a positive,
strictly short vertical step at each point on the tail axis. Ordinary choice and natural
recursion define its accepted-point subsequence from the fixed initial ordinate one.
This subsequence is unbounded and crosses every positive slope threshold in finite time.
These are statements about accepted points; outer inspections, request refinements and
query traces are separate obligations.
-/

noncomputable section
namespace Optimization.TransversePrelude
open TransverseObjective TransverseCubicModel

/-- The positive magnitude of the actual tail slope. -/
def slope (y : ℝ) : ℝ := -InverseSqrtTail.first y

/-- The actual tail slope is positive on the right half-line. -/
theorem slope_pos {y : ℝ} (hy : 1 ≤ y) : 0 < slope y :=
  neg_pos.mpr (InverseSqrtTail.first_neg_of_one_le hy)

/-- The actual tail slope decreases as the ordinate increases. -/
theorem antitoneOn_slope : AntitoneOn slope (Set.Ici 1) := by
  intro x hx y hy hxy
  exact neg_le_neg (InverseSqrtTail.monotoneOn_first hx hy hxy)

/-- The slope at the fixed initial ordinate is one half. -/
@[simp] theorem slope_one : slope 1 = (1 / 2 : ℝ) := by
  simp [slope]

/-- The tail slope never exceeds its initial value. -/
theorem slope_le_half {y : ℝ} (hy : 1 ≤ y) : slope y ≤ (1 / 2 : ℝ) := by
  simpa using antitoneOn_slope (show (1 : ℝ) ∈ Set.Ici 1 from by simp) hy hy

/-- In the tail, the named slope has its inverse-power formula. -/
theorem slope_eq {y : ℝ} (hy : 1 ≤ y) : slope y = (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) := by
  rw [slope, InverseSqrtTail.first_of_one_le hy]
  ring

/-- A chosen attained minimum of the actual cubic Taylor model at the tail axis. -/
def step (y : ℝ) : Plane := Classical.choose
  (HigherOrderApproximateRegularization.exists_model_minimizer objective 2
    (point 0 y) (by norm_num : (0 : ℝ) < 2))

/-- The chosen step globally minimizes the actual cubic Taylor model. -/
theorem step_minimizes (y : ℝ) : ∀ d,
    HigherOrderRegularization.model objective 2 (point 0 y) 2 (step y) ≤
      HigherOrderRegularization.model objective 2 (point 0 y) 2 d :=
  Classical.choose_spec
    (HigherOrderApproximateRegularization.exists_model_minimizer objective 2
      (point 0 y) (by norm_num : (0 : ℝ) < 2))

/-- Every selected actual global minimum has zero transverse component. -/
@[simp] theorem step_zero_coord (y : ℝ) : step y 0 = 0 := by
  have hm := actual_minimizer_model (by norm_num : |(0 : ℝ)| ≤ 1) y (step_minimizes y)
  simp only [minimizer_first hm, neg_zero, zero_div]

/-- Every selected actual global minimum moves strictly forward in the tail. -/
theorem step_one_coord_pos {y : ℝ} (hy : 1 ≤ y) : 0 < step y 1 := by
  exact minimizer_second_pos (slope_pos hy) (InverseSqrtTail.second_nonneg y)
    (actual_minimizer_model (by norm_num : |(0 : ℝ)| ≤ 1) y (step_minimizes y))

/-- On the tail axis the selected step norm is exactly its positive second coordinate. -/
theorem norm_step {y : ℝ} (hy : 1 ≤ y) : ‖step y‖ = step y 1 := by
  have hn := norm_point_sq (step y 0) (step y 1)
  rw [point_coords, step_zero_coord] at hn
  have hp := step_one_coord_pos hy
  nlinarith [norm_nonneg (step y)]

/-- The selected displacement is the vertical vector with its actual positive step length. -/
theorem step_eq_point (y : ℝ) : step y = point 0 (step y 1) := by
  simpa only [step_zero_coord] using (point_coords (step y)).symm

/-- The vertical step satisfies the actual global-minimum stationarity equation. -/
theorem step_equation {y : ℝ} (hy : 1 ≤ y) :
    (step y 1) ^ 2 + InverseSqrtTail.second y * step y 1 = slope y := by
  have hs := (minimizer_stationarity
    (actual_minimizer_model (by norm_num : |(0 : ℝ)| ≤ 1) y (step_minimizes y))).2
  rw [norm_step hy] at hs
  dsimp [slope]
  nlinarith

/-- The actual global-minimum vertical step is strictly less than one. -/
theorem step_one_coord_lt_one {y : ℝ} (hy : 1 ≤ y) : step y 1 < 1 := by
  have he := step_equation hy
  have hh := slope_le_half hy
  have hp := step_one_coord_pos hy
  have hH := InverseSqrtTail.second_nonneg y
  nlinarith [mul_nonneg hH hp.le]

/-- The selected actual global-minimum displacement is strictly short. -/
theorem norm_step_lt_one {y : ℝ} (hy : 1 ≤ y) : ‖step y‖ < 1 := by
  rw [norm_step hy]
  exact step_one_coord_lt_one hy

/-- Each selected cubic model step has actual acceptance ratio at least one. -/
theorem step_ratio_ge_one {y : ℝ} (hy : 1 ≤ y) :
    1 ≤ HigherOrderRegularization.ratio objective 2 (point 0 y) (step y) :=
  actual_minimizer_ratio_ge_one (by norm_num) (by norm_num) hy (step_minimizes y)

/-- The accepted-point ordinates, starting at the tolerance-independent ordinate one. -/
def ordinate : ℕ → ℝ := Nat.rec 1 (fun _ y => y + step y 1)

/-- The accepted-point recurrence has its fixed initial ordinate. -/
@[simp] theorem ordinate_zero : ordinate 0 = 1 := rfl

/-- The accepted-point recurrence adds the selected actual global-minimum step. -/
@[simp] theorem ordinate_succ (n : ℕ) : ordinate (n + 1) = ordinate n + step (ordinate n) 1 := rfl

/-- The full Euclidean accepted point is obtained by adding the actual chosen model step. -/
theorem point_ordinate_succ (n : ℕ) :
    point 0 (ordinate (n + 1)) = point 0 (ordinate n) + step (ordinate n) := by
  rw [step_eq_point (ordinate n), point_add, ordinate_succ, zero_add]

/-- Every accepted-point ordinate stays in the inverse-square-root tail region. -/
theorem one_le_ordinate (n : ℕ) : 1 ≤ ordinate n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ordinate_succ]; linarith [step_one_coord_pos ih]

/-- The accepted-point ordinates increase strictly. -/
theorem strictMono_ordinate : StrictMono ordinate := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [ordinate_succ]
  linarith [step_one_coord_pos (one_le_ordinate n)]

/-- Every accepted-point increment is strictly less than one. -/
theorem ordinate_succ_lt (n : ℕ) : ordinate (n + 1) < ordinate n + 1 := by
  rw [ordinate_succ]
  linarith [step_one_coord_lt_one (one_le_ordinate n)]

/-- The slope is bounded by twice the actual positive global-minimum step. -/
theorem slope_le_twice_step {y : ℝ} (hy : 1 ≤ y) : slope y ≤ 2 * step y 1 := by
  have he := step_equation hy
  have hp := step_one_coord_pos hy
  have hs := step_one_coord_lt_one hy
  have hH := InverseSqrtTail.abs_second_le y
  rw [abs_of_nonneg (InverseSqrtTail.second_nonneg y)] at hH
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - step y 1) hp.le,
    mul_nonneg (by linarith : 0 ≤ 3 / 4 - InverseSqrtTail.second y) hp.le]

/-- The accepted-point subsequence is unbounded above. -/
theorem ordinate_unbounded (M : ℝ) : ∃ n, M < ordinate n := by
  by_contra h
  push Not at h
  have hM : 1 ≤ M := by simpa using h 0
  have hg := slope_pos hM
  have hinc (n : ℕ) : slope M / 2 ≤ step (ordinate n) 1 := by
    have hm := antitoneOn_slope (one_le_ordinate n) hM (h n)
    have hs := slope_le_twice_step (one_le_ordinate n)
    linarith
  have hlinear (n : ℕ) : 1 + (n : ℝ) * (slope M / 2) ≤ ordinate n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ordinate_succ, Nat.cast_add, Nat.cast_one]
      nlinarith [hinc n]
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - 1) / (slope M / 2))
  have hh := (div_lt_iff₀ (by positivity : 0 < slope M / 2)).mp hn
  have hl := hlinear n
  linarith [h n]

/-- A simple inverse-linear bound for the actual inverse-square-root tail slope. -/
theorem slope_le_inv {y : ℝ} (hy : 1 ≤ y) : slope y ≤ (1 / 2 : ℝ) / y := by
  rw [slope_eq hy]
  have hh := Real.rpow_le_rpow_of_exponent_le hy (by norm_num : -(3 / 2 : ℝ) ≤ -1)
  rw [Real.rpow_neg_one] at hh
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- The accepted-point sequence crosses every strictly positive slope threshold. -/
theorem exists_slope_le {ε : ℝ} (hε : 0 < ε) : ∃ n, slope (ordinate n) ≤ ε := by
  obtain ⟨n, hn⟩ := ordinate_unbounded ((1 / 2 : ℝ) / ε)
  refine ⟨n, (slope_le_inv (one_le_ordinate n)).trans ?_⟩
  apply (div_le_iff₀ (by linarith [one_le_ordinate n] : 0 < ordinate n)).mpr
  have hh := (div_lt_iff₀ hε).mp hn
  nlinarith

/-- The first accepted-point index at which the prescribed switching slope is reached. -/
def crossingIndex (ε : ℝ) (hε : 0 < ε) : ℕ :=
  Nat.find (exists_slope_le (show 0 < 2 * ε / 5 by positivity))

/-- At the first switching index the slope is at most two fifths of the tolerance. -/
theorem slope_crossingIndex_le {ε : ℝ} (hε : 0 < ε) :
    slope (ordinate (crossingIndex ε hε)) ≤ 2 * ε / 5 :=
  Nat.find_spec (exists_slope_le (show 0 < 2 * ε / 5 by positivity))

/-- Every accepted point before the first crossing has slope strictly above the threshold. -/
theorem lt_slope_of_lt_crossingIndex {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : n < crossingIndex ε hε) : 2 * ε / 5 < slope (ordinate n) := by
  exact lt_of_not_ge (Nat.find_min (exists_slope_le (show 0 < 2 * ε / 5 by positivity)) hn)

/-- A simple inverse-square lower bound for the actual tail slope. -/
theorem inv_sq_le_slope {y : ℝ} (hy : 1 ≤ y) : (1 / 2 : ℝ) / y ^ 2 ≤ slope y := by
  rw [slope_eq hy]
  have hh := Real.rpow_le_rpow_of_exponent_le hy
    (by norm_num : (-2 : ℝ) ≤ -(3 / 2 : ℝ))
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (by linarith : 0 ≤ y), Real.rpow_two] at hh
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- For small tolerances, the first crossing lies beyond ordinate seventeen. -/
theorem seventeen_le_crossing {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) :
    17 ≤ ordinate (crossingIndex ε hε) := by
  by_contra hn
  have hle : ordinate (crossingIndex ε hε) ≤ 17 := (lt_of_not_ge hn).le
  have hm := antitoneOn_slope (one_le_ordinate (crossingIndex ε hε))
    (show (1 : ℝ) ≤ 17 by norm_num) hle
  have hl := inv_sq_le_slope (show (1 : ℝ) ≤ 17 by norm_num)
  have hu := slope_crossingIndex_le hε
  norm_num at hl
  linarith

/-- The small-tolerance crossing is preceded by at least one accepted point. -/
theorem crossingIndex_pos {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) :
    0 < crossingIndex ε hε := by
  by_contra hn
  have hz : crossingIndex ε hε = 0 := Nat.eq_zero_of_not_pos hn
  have hu := seventeen_le_crossing hε hsmall
  rw [hz, ordinate_zero] at hu
  norm_num at hu

/-- An increment of at most one beyond ordinate sixteen loses less than the
inverse-square factor associated with seventeen sixteenths. -/
theorem slope_short_increment_lower {y t : ℝ} (hy : 16 ≤ y) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (16 / 17 : ℝ) ^ 2 * slope y ≤ slope (y + t) := by
  have hy1 : 1 ≤ y := by linarith
  have hyt : 1 ≤ y + t := by linarith
  have hcy : 1 ≤ (17 / 16 : ℝ) * y := by linarith
  have hm := antitoneOn_slope hyt hcy (show y + t ≤ (17 / 16 : ℝ) * y by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 17 / 16 by norm_num)
    (show (-2 : ℝ) ≤ -(3 / 2 : ℝ) by norm_num)
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 17 / 16), Real.rpow_two] at hp
  norm_num only [div_pow, OfNat.ofNat_ne_zero, pow_two, inv_div] at hp
  rw [slope_eq hcy, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 17 / 16)
    (by linarith : 0 ≤ y)] at hm
  rw [slope_eq hy1]
  have hpow := Real.rpow_nonneg (by linarith : 0 ≤ y) (-(3 / 2 : ℝ))
  nlinarith [mul_le_mul_of_nonneg_right hp hpow]

/-- The first small-tolerance crossing retains a slope strictly above one third
of the tolerance, in addition to its defining two-fifths upper bound. -/
theorem crossing_window {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) :
    ε / 3 < slope (ordinate (crossingIndex ε hε)) ∧
      slope (ordinate (crossingIndex ε hε)) ≤ 2 * ε / 5 ∧
      16 ≤ ordinate (crossingIndex ε hε) := by
  have hn := crossingIndex_pos hε hsmall
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hu := seventeen_le_crossing hε hsmall
  have hprevious : 2 * ε / 5 < slope (ordinate n) := by
    apply lt_slope_of_lt_crossingIndex hε
    omega
  have hlarge : 16 ≤ ordinate n := by
    rw [he] at hu
    have hs := ordinate_succ_lt n
    linarith
  have hl := slope_short_increment_lower hlarge
    (step_one_coord_pos (one_le_ordinate n)).le
    (step_one_coord_lt_one (one_le_ordinate n)).le
  rw [← ordinate_succ] at hl
  change (16 / 17 : ℝ) ^ 2 * slope (ordinate n) ≤ slope (ordinate n.succ) at hl
  rw [← he] at hl
  refine ⟨?_, slope_crossingIndex_le hε, by linarith⟩
  nlinarith

/-- The actual curvature at the switching point is at most one hundredth. -/
theorem second_crossing_le {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) :
    InverseSqrtTail.second (ordinate (crossingIndex ε hε)) ≤ 1 / 100 := by
  have hu := (crossing_window hε hsmall).2.2
  have hm := InverseSqrtTail.antitoneOn_second (show (1 : ℝ) ≤ 16 by norm_num)
    (one_le_ordinate (crossingIndex ε hε)) hu
  rw [InverseSqrtTail.second_of_one_le (show (1 : ℝ) ≤ 16 by norm_num)] at hm
  have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 16 by norm_num)
    (show -(5 / 2 : ℝ) ≤ (-2 : ℝ) by norm_num)
  have h16 : (16 : ℝ) ^ (-2 : ℝ) = 1 / 256 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16), Real.rpow_two]
    norm_num
  rw [h16] at hp
  linarith

end Optimization.TransversePrelude
