import Numlib.Optimization.SteepestDescent.Exact.CorridorProfiles
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Primitive finite zig-zag corridor data

A positive integer horizon and accuracy satisfying `N ε²=1` determine the actual
source grid, alternating vertical coordinates, scalar objective values, and
corridor width and center jets. No interpolation or convergence conclusion is
a field of the data. Uniform primitive bounds follow from the explicit formulas.
-/

open Finset
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- Primitive accuracy and integer horizon for the source exact-count construction. -/
structure Parameters where
  accuracy : ℝ
  horizon : ℕ
  accuracy_pos : 0 < accuracy
  accuracy_le_one : accuracy ≤ 1
  horizon_pos : 0 < horizon
  compatible : (horizon : ℝ) * accuracy ^ 2 = 1

/-- The source linearly decreasing excess above the requested gradient accuracy. -/
def omega (P : Parameters) (k : ℕ) : ℝ :=
  P.accuracy * ((P.horizon : ℝ) - k) / P.horizon

/-- The positive horizontal step and corridor width at each finite grid node. -/
def amplitude (P : Parameters) (k : ℕ) : ℝ := P.accuracy + omega P k

/-- The common change between consecutive source widths. -/
def widthIncrement (P : Parameters) : ℝ := P.accuracy / P.horizon

/-- Actual horizontal grid coordinates. -/
def horizontal (P : Parameters) (k : ℕ) : ℝ := ∑ i ∈ range k, amplitude P i

/-- Actual alternating vertical grid coordinates. -/
def vertical (P : Parameters) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, (-1 : ℝ) ^ i * amplitude P i

/-- Scalar objective values specified at the finite grid nodes. -/
def scalarValue (P : Parameters) (k : ℕ) : ℝ :=
  4 - ∑ i ∈ range k, amplitude P i ^ 2

/-- Corridor center values at the grid nodes. -/
def centerValue (P : Parameters) (k : ℕ) : ℝ :=
  vertical P k + (-1 : ℝ) ^ k * amplitude P k / 2

/-- The integer-compatible grid has positive horizon as a real number. -/
theorem Parameters.horizon_cast_pos (P : Parameters) : 0 < (P.horizon : ℝ) :=
  Nat.cast_pos.mpr P.horizon_pos

/-- The source excess lies between zero and the accuracy on every finite node. -/
theorem omega_mem (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    0 ≤ omega P k ∧ omega P k ≤ P.accuracy := by
  have hN := P.horizon_cast_pos
  have hk' : (k : ℝ) ≤ P.horizon := by exact_mod_cast hk
  unfold omega
  constructor
  · exact div_nonneg (mul_nonneg P.accuracy_pos.le (sub_nonneg.mpr hk')) hN.le
  · apply (div_le_iff₀ hN).mpr
    nlinarith [P.accuracy_pos, Nat.cast_nonneg (α := ℝ) k]

/-- All finite grid amplitudes lie between the accuracy and twice the accuracy. -/
theorem amplitude_mem (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    P.accuracy ≤ amplitude P k ∧ amplitude P k ≤ 2 * P.accuracy := by
  have hh := omega_mem P hk
  unfold amplitude
  constructor <;> linarith

/-- Every finite source step is strictly positive. -/
theorem amplitude_pos (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    0 < amplitude P k := P.accuracy_pos.trans_le (amplitude_mem P hk).1

/-- Consecutive widths decrease by the common positive increment. -/
theorem amplitude_succ (P : Parameters) (k : ℕ) :
    amplitude P (k + 1) = amplitude P k - widthIncrement P := by
  dsimp [amplitude, omega, widthIncrement]
  push_cast
  ring

/-- Integer compatibility identifies the width change with the accuracy cubed. -/
theorem widthIncrement_eq_cube (P : Parameters) : widthIncrement P = P.accuracy ^ 3 := by
  apply (div_eq_iff P.horizon_cast_pos.ne').mpr
  have hh := P.compatible
  nlinarith [congrArg (fun z : ℝ => z * P.accuracy) hh]

/-- The small width change satisfies the cubic Hermite residual scaling. -/
theorem widthIncrement_le_cube (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    widthIncrement P ≤ amplitude P k ^ 3 := by
  rw [widthIncrement_eq_cube]
  exact pow_le_pow_left₀ P.accuracy_pos.le (amplitude_mem P hk).1 3

/-- The primitive grid uses precisely the source horizontal increment. -/
theorem horizontal_succ (P : Parameters) (k : ℕ) :
    horizontal P (k + 1) = horizontal P k + amplitude P k := by
  simp [horizontal, sum_range_succ]

/-- The primitive grid uses precisely the source alternating vertical increment. -/
theorem vertical_succ (P : Parameters) (k : ℕ) :
    vertical P (k + 1) = vertical P k + (-1 : ℝ) ^ k * amplitude P k := by
  simp [vertical, sum_range_succ]

/-- Scalar node values decrease by the square of the actual prescribed step. -/
theorem scalarValue_succ (P : Parameters) (k : ℕ) :
    scalarValue P (k + 1) = scalarValue P k - amplitude P k ^ 2 := by
  simp only [scalarValue, sum_range_succ]
  ring

/-- Corridor center node differences have the exact alternating half-width change. -/
theorem centerValue_succ (P : Parameters) (k : ℕ) :
    centerValue P (k + 1) = centerValue P k + (-1 : ℝ) ^ k * widthIncrement P / 2 := by
  simp only [centerValue, vertical_succ, amplitude_succ, pow_succ]
  ring

/-- The finite horizontal grid is genuinely strictly increasing. -/
theorem horizontal_increasing (P : Parameters) :
    ∀ i j, i < j → j ≤ P.horizon → horizontal P i < horizontal P j := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
    intro hij hj
    rw [horizontal_succ]
    have ha := amplitude_pos P (k := j) (by omega)
    by_cases he : i = j
    · subst i
      linarith
    · exact (ih (by omega) (by omega)).trans (by linarith)

/-- Scalar node values stay in a fixed interval independently of the horizon. -/
theorem scalarValue_mem (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    0 ≤ scalarValue P k ∧ scalarValue P k ≤ 4 := by
  have hsum : (∑ i ∈ range k, amplitude P i ^ 2) ≤
      (k : ℝ) * (2 * P.accuracy) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ range k, (2 * P.accuracy) ^ 2 := by
        apply sum_le_sum
        intro i hi
        have hm := amplitude_mem P ((mem_range.mp hi).le.trans hk)
        exact pow_le_pow_left₀ (P.accuracy_pos.trans_le hm.1).le hm.2 2
      _ = _ := by simp
  have hk' : (k : ℝ) ≤ P.horizon := by exact_mod_cast hk
  have hupper : (k : ℝ) * (2 * P.accuracy) ^ 2 ≤ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hk' (sq_nonneg (2 * P.accuracy)), P.compatible]
  have hnonneg : 0 ≤ ∑ i ∈ range k, amplitude P i ^ 2 := sum_nonneg (by
    intro i hi
    exact sq_nonneg _)
  dsimp [scalarValue]
  constructor <;> linarith


/-- The excess vanishes exactly at the integer horizon. -/
theorem omega_horizon (P : Parameters) : omega P P.horizon = 0 := by
  simp [omega]

/-- The final prescribed gradient amplitude is the requested accuracy. -/
theorem amplitude_horizon (P : Parameters) : amplitude P P.horizon = P.accuracy := by
  simp [amplitude, omega_horizon]

/-- Before the integer horizon, the prescribed gradient amplitude strictly
exceeds the requested accuracy. -/
theorem amplitude_gt_accuracy (P : Parameters) {k : ℕ} (hk : k < P.horizon) :
    P.accuracy < amplitude P k := by
  have hk' : (k : ℝ) < P.horizon := by exact_mod_cast hk
  have ho : 0 < omega P k := div_pos
    (mul_pos P.accuracy_pos (sub_pos.mpr hk')) P.horizon_cast_pos
  dsimp [amplitude]
  linarith

end ExactSteepestDescent.Corridor
