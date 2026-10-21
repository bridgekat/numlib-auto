import Numlib.Analysis.Calculus.FiniteQuinticHermite
import Numlib.Optimization.SteepestDescentValleyProfiles
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Finite scalar profiles for a steepest-descent valley

The finite chain uses an integer number of cells. Its three scalar profiles are actual
explicit quintic Hermite splines, with an affine objective branch on the left and a unit
transition to a constant objective branch on the right. Width and midpoint are constant
outside the chain. The construction retains every source-cell formula. The resulting
Euclidean objective is twice continuously differentiable, including all moving seams.

This module does not assert global line minimization of the prescribed steps.
-/

noncomputable section
open Polynomial Set Hermite

namespace Optimization.SteepestDescentValley

/-- Admissible finite-chain parameters; the last two inequalities permit rounded cell counts. -/
structure Parameters where
  eps : ℝ
  count : ℕ
  eps_pos : 0 < eps
  eps_le_one : eps ≤ 1
  count_pos : 0 < count
  scaled_count_lower : 1 ≤ (count : ℝ) * eps ^ 2
  scaled_count_upper : (count : ℝ) * eps ^ 2 ≤ 2

/-- Rounding the reciprocal squared tolerance upwards gives admissible finite parameters. -/
def roundedParameters (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) : Parameters where
  eps := eps
  count := ⌈(eps ^ 2)⁻¹⌉₊
  eps_pos := hpos
  eps_le_one := hle
  count_pos := Nat.ceil_pos.mpr (inv_pos.mpr (sq_pos_of_pos hpos))
  scaled_count_lower := by
    have h := mul_le_mul_of_nonneg_right (Nat.le_ceil ((eps ^ 2)⁻¹)) (sq_nonneg eps)
    simpa only [inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos hpos))] using h
  scaled_count_upper := by
    have h := mul_le_mul_of_nonneg_right
      (Nat.ceil_lt_add_one (inv_nonneg.mpr (sq_nonneg eps))).le (sq_nonneg eps)
    have he : (eps ^ 2)⁻¹ * eps ^ 2 = 1 := inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos hpos))
    nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hle)]

/-- The rounded construction has exactly the requested tolerance. -/
@[simp] theorem roundedParameters_eps (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    (roundedParameters eps hpos hle).eps = eps := rfl

/-- The number of source cells is the ceiling of the reciprocal squared tolerance. -/
@[simp] theorem roundedParameters_count (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    (roundedParameters eps hpos hle).count = ⌈(eps ^ 2)⁻¹⌉₊ := rfl

/-- The positive, linearly decreasing length of cell `k` up to the terminal index. -/
def cellLength (P : Parameters) (k : ℕ) : ℝ :=
  P.eps + P.eps * (1 - (k : ℝ) / P.count)

/-- The common decrement between consecutive cell lengths. -/
def lengthDrop (P : Parameters) : ℝ := P.eps / P.count

/-- Alternating vertical orientation of the finite chain. -/
def cellSign (k : ℕ) : ℝ := (-1) ^ k

/-- Horizontal nodal coordinate of the finite chain. -/
def nodeX (P : Parameters) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, cellLength P i

/-- Vertical nodal coordinate of the finite chain. -/
def nodeY (P : Parameters) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, cellSign i * cellLength P i

/-- Prescribed scalar objective values at the finite nodes. -/
def nodeValue (P : Parameters) (k : ℕ) : ℝ :=
  4 - ∑ i ∈ Finset.range k, cellLength P i ^ 2

/-- Prescribed midpoint at each node. -/
def nodeMidpoint (P : Parameters) (k : ℕ) : ℝ :=
  nodeY P k + cellSign k * cellLength P k / 2

/-- The cell lengths begin at twice the tolerance. -/
@[simp] theorem cellLength_zero (P : Parameters) : cellLength P 0 = 2 * P.eps := by
  simp [cellLength]
  ring

/-- The terminal length is exactly the tolerance. -/
@[simp] theorem cellLength_count (P : Parameters) : cellLength P P.count = P.eps := by
  simp [cellLength, ne_of_gt (Nat.cast_pos.mpr P.count_pos)]

/-- The exact decrement identity holds before any restriction to the finite chain. -/
theorem cellLength_succ (P : Parameters) (k : ℕ) :
    cellLength P (k + 1) = cellLength P k - lengthDrop P := by
  simp only [cellLength, lengthDrop, Nat.cast_add, Nat.cast_one]
  ring

/-- The common decrement is positive. -/
theorem lengthDrop_pos (P : Parameters) : 0 < lengthDrop P :=
  div_pos P.eps_pos (Nat.cast_pos.mpr P.count_pos)

/-- All finite cell lengths lie between the tolerance and twice the tolerance. -/
theorem cellLength_bounds (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    P.eps ≤ cellLength P k ∧ cellLength P k ≤ 2 * P.eps := by
  have hN : (0 : ℝ) < P.count := Nat.cast_pos.mpr P.count_pos
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkN : (k : ℝ) ≤ P.count := Nat.cast_le.mpr hk
  have hq : 0 ≤ (k : ℝ) / P.count ∧ (k : ℝ) / P.count ≤ 1 :=
    ⟨div_nonneg hk0 hN.le, (div_le_one hN).mpr hkN⟩
  dsimp [cellLength]
  constructor <;> nlinarith [P.eps_pos]

/-- Every finite cell has positive length. -/
theorem cellLength_pos (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    0 < cellLength P k := P.eps_pos.trans_le (cellLength_bounds P hk).1

/-- Alternation changes the vertical orientation at every successor. -/
@[simp] theorem cellSign_succ (k : ℕ) : cellSign (k + 1) = -cellSign k := by
  simp [cellSign, pow_succ]

/-- Alternating signs have absolute value one. -/
@[simp] theorem abs_cellSign (k : ℕ) : |cellSign k| = 1 := by
  simp [cellSign, abs_pow]

/-- The horizontal increment is the current cell length. -/
theorem nodeX_succ (P : Parameters) (k : ℕ) :
    nodeX P (k + 1) = nodeX P k + cellLength P k := by
  simp [nodeX, Finset.sum_range_succ]

/-- The vertical increment is the signed current cell length. -/
theorem nodeY_succ (P : Parameters) (k : ℕ) :
    nodeY P (k + 1) = nodeY P k + cellSign k * cellLength P k := by
  simp [nodeY, Finset.sum_range_succ]

/-- The objective loses the square of the current cell length at each node. -/
theorem nodeValue_succ (P : Parameters) (k : ℕ) :
    nodeValue P (k + 1) = nodeValue P k - cellLength P k ^ 2 := by
  simp [nodeValue, Finset.sum_range_succ]
  ring

/-- The midpoint increment is half the signed length decrement. -/
theorem nodeMidpoint_succ (P : Parameters) (k : ℕ) :
    nodeMidpoint P (k + 1) = nodeMidpoint P k + cellSign k * lengthDrop P / 2 := by
  rw [nodeMidpoint, nodeY_succ, cellSign_succ, cellLength_succ, nodeMidpoint]
  ring

/-- The finite horizontal knots are strictly ordered. -/
theorem nodeX_strict (P : Parameters) : ∀ k < P.count, nodeX P k < nodeX P (k + 1) := by
  intro k hk
  rw [nodeX_succ]
  exact lt_add_of_pos_right _ (cellLength_pos P hk.le)

/-- Value, slope and vanishing second derivative for the objective at every source node. -/
def objectiveJet (P : Parameters) (k j : ℕ) : ℝ :=
  if j = 0 then nodeValue P k else if j = 1 then -cellLength P k else 0

/-- Width data are constant to second order at each node. -/
def widthJet (P : Parameters) (k : ℕ) : ℕ → ℝ := constantJet (cellLength P k)

/-- Midpoint data are constant to second order at each node. -/
def midpointJet (P : Parameters) (k : ℕ) : ℕ → ℝ := constantJet (nodeMidpoint P k)

/-- Add one unit transition interval after the last source node. -/
def extendedNodeX (P : Parameters) (k : ℕ) : ℝ :=
  if k ≤ P.count then nodeX P k else nodeX P P.count + 1

/-- The additional objective jet is constant, half a tolerance below its last source value. -/
def extendedObjectiveJet (P : Parameters) (k : ℕ) : ℕ → ℝ :=
  if k ≤ P.count then objectiveJet P k
  else constantJet (nodeValue P P.count - P.eps / 2)

/-- The full scalar objective profile, with an affine left tail and bounded right tail. -/
def scalarObjective (P : Parameters) : ℝ → ℝ :=
  finiteQuintic (P.count + 1) (extendedNodeX P) (extendedObjectiveJet P)

/-- The full width profile, constant outside the finite chain. -/
def scalarWidth (P : Parameters) : ℝ → ℝ :=
  finiteQuintic P.count (nodeX P) (widthJet P)

/-- The full midpoint profile, constant outside the finite chain. -/
def scalarMidpoint (P : Parameters) : ℝ → ℝ :=
  finiteQuintic P.count (nodeX P) (midpointJet P)

/-- The original source nodes are retained by the one-interval extension. -/
theorem extendedNodeX_of_le (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    extendedNodeX P k = nodeX P k := ite_eq_left hk

/-- The additional endpoint is exactly one unit beyond the last source node. -/
@[simp] theorem extendedNodeX_last (P : Parameters) :
    extendedNodeX P (P.count + 1) = nodeX P P.count + 1 := by
  simp [extendedNodeX]

/-- Every knot, including the terminal unit transition, is strictly ordered. -/
theorem extendedNodeX_strict (P : Parameters) :
    ∀ k < P.count + 1, extendedNodeX P k < extendedNodeX P (k + 1) := by
  intro k hk
  rcases (show k ≤ P.count by omega).eq_or_lt with rfl | hk'
  · rw [extendedNodeX_of_le P le_rfl, extendedNodeX_last]
    linarith
  · rw [extendedNodeX_of_le P hk'.le, extendedNodeX_of_le P (by omega)]
    exact nodeX_strict P k hk'

/-- The scalar objective is genuinely C2 across every finite seam and both tails. -/
theorem contDiff_scalarObjective (P : Parameters) : ContDiff ℝ 2 (scalarObjective P) :=
  (contDiff_finiteQuintic _ (extendedNodeX_strict P)).1

/-- The actual width is globally C2, including its constant tails. -/
theorem contDiff_scalarWidth (P : Parameters) : ContDiff ℝ 2 (scalarWidth P) :=
  (contDiff_finiteQuintic _ (nodeX_strict P)).1

/-- The actual midpoint is globally C2, including its constant tails. -/
theorem contDiff_scalarMidpoint (P : Parameters) : ContDiff ℝ 2 (scalarMidpoint P) :=
  (contDiff_finiteQuintic _ (nodeX_strict P)).1

/-- All source objective jets are realized by the actual scalar profile. -/
theorem scalarObjective_node_jets (P : Parameters) {k j : ℕ} (hk : k ≤ P.count)
    (hj : j ≤ 2) : iteratedDeriv j (scalarObjective P) (nodeX P k) = objectiveJet P k j := by
  have h := finiteQuintic_node_jets (extendedObjectiveJet P) (extendedNodeX_strict P)
    (show k ≤ P.count + 1 by omega) hj
  simpa [scalarObjective, extendedNodeX_of_le P hk, extendedObjectiveJet, hk] using h

/-- All source width jets are realized by the actual scalar profile. -/
theorem scalarWidth_node_jets (P : Parameters) {k j : ℕ} (hk : k ≤ P.count)
    (hj : j ≤ 2) : iteratedDeriv j (scalarWidth P) (nodeX P k) = widthJet P k j :=
  finiteQuintic_node_jets _ (nodeX_strict P) hk hj

/-- All source midpoint jets are realized by the actual scalar profile. -/
theorem scalarMidpoint_node_jets (P : Parameters) {k j : ℕ} (hk : k ≤ P.count)
    (hj : j ≤ 2) : iteratedDeriv j (scalarMidpoint P) (nodeX P k) = midpointJet P k j :=
  finiteQuintic_node_jets _ (nodeX_strict P) hk hj

/-- Interpolation between constant jets has exactly the standard quintic smoothing formula. -/
theorem quinticCell_constantJets (x s a b t : ℝ) :
    quinticCell x s (constantJet a) (constantJet b) t =
      a + (b - a) * smoothStep ((t - x) / s) := by
  rw [quinticCell_eq, smoothStep_eq]
  norm_num [quinticPolynomial, Finset.sum_range_succ, quinticCoefficient,
    quinticResidual, scaledJet, constantJet]
  ring

/-- The source objective cell is the actual explicit Hermite polynomial. -/
theorem quinticCell_objective_formula (x s d v t : ℝ) :
    quinticCell x s (fun j => if j = 0 then v else if j = 1 then -s else 0)
      (fun j => if j = 0 then v - s ^ 2 else if j = 1 then -(s - d) else 0) t =
        v - s ^ 2 * ((t - x) / s) + s * d *
          (-4 * ((t - x) / s) ^ 3 + 7 * ((t - x) / s) ^ 4 - 3 * ((t - x) / s) ^ 5) := by
  rw [quinticCell_eq]
  norm_num [quinticPolynomial, Finset.sum_range_succ, quinticCoefficient,
    quinticResidual, scaledJet]
  ring

/-- On each source cell the actual width is the prescribed smoothing polynomial. -/
theorem scalarWidth_cell (P : Parameters) {k : ℕ} (hk : k < P.count) {t : ℝ}
    (ht : t ∈ Icc (nodeX P k) (nodeX P (k + 1))) :
    scalarWidth P t = cellLength P k - lengthDrop P *
      smoothStep ((t - nodeX P k) / cellLength P k) := by
  have h := finiteQuintic_cell_jets (widthJet P) (nodeX_strict P) hk (j := 0) (by omega) ht
  simp only [iteratedDeriv_zero] at h
  rw [scalarWidth, h, nodeX_succ, add_sub_cancel_left, widthJet, widthJet,
    quinticCell_constantJets, cellLength_succ]
  ring

/-- On each source cell the actual midpoint is the signed smoothing polynomial. -/
theorem scalarMidpoint_cell (P : Parameters) {k : ℕ} (hk : k < P.count) {t : ℝ}
    (ht : t ∈ Icc (nodeX P k) (nodeX P (k + 1))) :
    scalarMidpoint P t = nodeMidpoint P k + cellSign k * lengthDrop P / 2 *
      smoothStep ((t - nodeX P k) / cellLength P k) := by
  have h := finiteQuintic_cell_jets (midpointJet P) (nodeX_strict P) hk (j := 0) (by omega) ht
  simp only [iteratedDeriv_zero] at h
  rw [scalarMidpoint, h, nodeX_succ, add_sub_cancel_left, midpointJet, midpointJet,
    quinticCell_constantJets, nodeMidpoint_succ]
  ring

/-- Every source objective cell retains its specific polynomial formula. -/
theorem scalarObjective_cell (P : Parameters) {k : ℕ} (hk : k < P.count) {t : ℝ}
    (ht : t ∈ Icc (nodeX P k) (nodeX P (k + 1))) :
    scalarObjective P t = nodeValue P k - cellLength P k ^ 2 *
      ((t - nodeX P k) / cellLength P k) + cellLength P k * lengthDrop P *
      (-4 * ((t - nodeX P k) / cellLength P k) ^ 3 +
        7 * ((t - nodeX P k) / cellLength P k) ^ 4 -
        3 * ((t - nodeX P k) / cellLength P k) ^ 5) := by
  have h := finiteQuintic_cell_jets (extendedObjectiveJet P) (extendedNodeX_strict P)
    (show k < P.count + 1 by omega) (j := 0) (by omega)
    (show t ∈ Icc (extendedNodeX P k) (extendedNodeX P (k + 1)) by
      simpa only [extendedNodeX_of_le P hk.le,
        extendedNodeX_of_le P (by omega : k + 1 ≤ P.count)] using ht)
  simp only [iteratedDeriv_zero] at h
  rw [scalarObjective, h]
  simp only [extendedNodeX_of_le P hk.le, extendedNodeX_of_le P (by omega : k + 1 ≤ P.count),
    extendedObjectiveJet, ite_eq_left hk.le, ite_eq_left (by omega : k + 1 ≤ P.count),
    nodeX_succ, add_sub_cancel_left]
  have hb : objectiveJet P (k + 1) = fun j =>
      if j = 0 then nodeValue P k - cellLength P k ^ 2
      else if j = 1 then -(cellLength P k - lengthDrop P) else 0 := by
    funext j
    simp only [objectiveJet, nodeValue_succ, cellLength_succ]
  rw [hb]
  exact quinticCell_objective_formula _ _ _ _ _

/-- The left objective branch is affine in x, as required for matching its nonzero first jet. -/
theorem scalarObjective_left (P : Parameters) {t : ℝ} (ht : t ≤ 0) :
    scalarObjective P t = 4 - 2 * P.eps * t := by
  have h := finiteQuintic_left_jets (extendedObjectiveJet P) (extendedNodeX_strict P)
    (j := 0) (by omega) (show t ≤ extendedNodeX P 0 by simpa [extendedNodeX, nodeX] using ht)
  simp only [iteratedDeriv_zero] at h
  rw [scalarObjective, h]
  norm_num [extendedObjectiveJet, extendedNodeX, objectiveJet, endpointTaylor, jetPoly,
    Finset.sum_range_succ, nodeValue, nodeX]
  ring

/-- The right objective tail is constant after the unit transition. -/
theorem scalarObjective_right (P : Parameters) {t : ℝ} (ht : nodeX P P.count + 1 ≤ t) :
    scalarObjective P t = nodeValue P P.count - P.eps / 2 := by
  have h := finiteQuintic_right_jets (extendedObjectiveJet P) (extendedNodeX_strict P)
    (j := 0) (by omega) (show extendedNodeX P (P.count + 1) ≤ t by simpa using ht)
  simpa [scalarObjective, extendedObjectiveJet, endpointTaylor_constantJet] using h

/-- Before the chain the actual width is frozen at its initial value. -/
theorem scalarWidth_left (P : Parameters) {t : ℝ} (ht : t ≤ 0) :
    scalarWidth P t = 2 * P.eps := by
  have h := finiteQuintic_left_jets (widthJet P) (nodeX_strict P)
    (j := 0) (by omega) (show t ≤ nodeX P 0 by simpa [nodeX] using ht)
  simpa [scalarWidth, widthJet, endpointTaylor_constantJet] using h

/-- After the chain the actual width is frozen at the tolerance. -/
theorem scalarWidth_right (P : Parameters) {t : ℝ} (ht : nodeX P P.count ≤ t) :
    scalarWidth P t = P.eps := by
  have h := finiteQuintic_right_jets (widthJet P) (nodeX_strict P)
    (j := 0) (by omega) ht
  simpa [scalarWidth, widthJet, endpointTaylor_constantJet] using h

/-- Before the chain the actual midpoint is frozen at its initial value. -/
theorem scalarMidpoint_left (P : Parameters) {t : ℝ} (ht : t ≤ 0) :
    scalarMidpoint P t = nodeMidpoint P 0 := by
  have h := finiteQuintic_left_jets (midpointJet P) (nodeX_strict P)
    (j := 0) (by omega) (show t ≤ nodeX P 0 by simpa [nodeX] using ht)
  simpa [scalarMidpoint, midpointJet, endpointTaylor_constantJet] using h

/-- After the chain the actual midpoint is frozen at its terminal value. -/
theorem scalarMidpoint_right (P : Parameters) {t : ℝ} (ht : nodeX P P.count ≤ t) :
    scalarMidpoint P t = nodeMidpoint P P.count := by
  have h := finiteQuintic_right_jets (midpointJet P) (nodeX_strict P)
    (j := 0) (by omega) ht
  simpa [scalarMidpoint, midpointJet, endpointTaylor_constantJet] using h

/-- The objective's unit transition to its constant right tail has an explicit quartic formula. -/
theorem scalarObjective_transition (P : Parameters) {t : ℝ}
    (ht : t ∈ Icc (nodeX P P.count) (nodeX P P.count + 1)) :
    scalarObjective P t = nodeValue P P.count - P.eps * (t - nodeX P P.count) +
      P.eps * (t - nodeX P P.count) ^ 3 - P.eps / 2 * (t - nodeX P P.count) ^ 4 := by
  have h := finiteQuintic_cell_jets (extendedObjectiveJet P) (extendedNodeX_strict P)
    (show P.count < P.count + 1 by omega) (j := 0) (by omega)
    (show t ∈ Icc (extendedNodeX P P.count) (extendedNodeX P (P.count + 1)) by
      simpa only [extendedNodeX_of_le P le_rfl, extendedNodeX_last] using ht)
  simp only [iteratedDeriv_zero] at h
  rw [scalarObjective, h, extendedNodeX_of_le P le_rfl, extendedNodeX_last,
    add_sub_cancel_left, quinticCell_eq]
  norm_num [extendedObjectiveJet, objectiveJet, quinticPolynomial,
    Finset.sum_range_succ, quinticCoefficient, quinticResidual, scaledJet, constantJet]
  ring

/-- Normalized coordinates stay in the unit interval on every source cell. -/
theorem cell_coordinate_mem_Icc (P : Parameters) {k : ℕ} (hk : k < P.count) {t : ℝ}
    (ht : t ∈ Icc (nodeX P k) (nodeX P (k + 1))) :
    (t - nodeX P k) / cellLength P k ∈ Icc (0 : ℝ) 1 := by
  have hs := cellLength_pos P hk.le
  constructor
  · exact div_nonneg (sub_nonneg.mpr ht.1) hs.le
  · apply (div_le_one hs).mpr
    rw [nodeX_succ] at ht
    linarith [ht.2]

/-- The actual width remains between the tolerance and twice the tolerance everywhere. -/
theorem scalarWidth_bounds (P : Parameters) (t : ℝ) :
    P.eps ≤ scalarWidth P t ∧ scalarWidth P t ≤ 2 * P.eps := by
  by_cases hl : t ≤ 0
  · rw [scalarWidth_left P hl]
    constructor <;> linarith [P.eps_pos]
  by_cases hr : nodeX P P.count ≤ t
  · rw [scalarWidth_right P hr]
    constructor <;> linarith [P.eps_pos]
  obtain ⟨k, hk, hkt⟩ := exists_adjacent_cell P.count_pos (nodeX P)
    (show t ∈ Icc (nodeX P 0) (nodeX P P.count) by
      simpa [nodeX] using (show t ∈ Icc (0 : ℝ) (nodeX P P.count) from
        ⟨le_of_not_ge hl, le_of_not_ge hr⟩))
  rw [scalarWidth_cell P hk hkt]
  have hS := smoothStep_mem_Icc (cell_coordinate_mem_Icc P hk hkt)
  have h1 := (cellLength_bounds P hk.le).2
  have h2 := (cellLength_bounds P (show k + 1 ≤ P.count by omega)).1
  rw [cellLength_succ] at h2
  have hd := lengthDrop_pos P
  constructor <;> nlinarith [hS.1, hS.2]

/-- The actual width is positive, including on both exterior tails. -/
theorem scalarWidth_pos (P : Parameters) (t : ℝ) : 0 < scalarWidth P t :=
  P.eps_pos.trans_le (scalarWidth_bounds P t).1

/-- Every source nodal value has a uniform lower bound independent of the tolerance and count. -/
theorem nodeValue_lower (P : Parameters) {k : ℕ} (hk : k ≤ P.count) : -4 ≤ nodeValue P k := by
  have hsum : ∑ i ∈ Finset.range k, cellLength P i ^ 2 ≤ (k : ℝ) * (4 * P.eps ^ 2) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, 4 * P.eps ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hb := cellLength_bounds P (show i ≤ P.count by
          have := Finset.mem_range.mp hi
          omega)
        nlinarith [hb.1, hb.2, P.eps_pos]
      _ = _ := by simp [mul_comm]
  have hkR : (k : ℝ) ≤ P.count := Nat.cast_le.mpr hk
  have hscaled := P.scaled_count_upper
  have hsum8 : ∑ i ∈ Finset.range k, cellLength P i ^ 2 ≤ 8 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (sq_nonneg P.eps)]
  dsimp [nodeValue]
  linarith

/-- The decrement is at most the tolerance. -/
theorem lengthDrop_le_eps (P : Parameters) : lengthDrop P ≤ P.eps := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr P.count_pos)).mpr
  have hN : (1 : ℝ) ≤ P.count := by exact_mod_cast P.count_pos
  nlinarith [P.eps_pos]

/-- A uniform, deliberately coarse lower bound on every actual source objective cell. -/
theorem scalarObjective_cell_lower (P : Parameters) {k : ℕ} (hk : k < P.count) {t : ℝ}
    (ht : t ∈ Icc (nodeX P k) (nodeX P (k + 1))) : -22 ≤ scalarObjective P t := by
  let u := (t - nodeX P k) / cellLength P k
  have hu : u ∈ Icc (0 : ℝ) 1 := cell_coordinate_mem_Icc P hk ht
  have h3 : u ^ 3 ≤ 1 := pow_le_one₀ hu.1 hu.2
  have h5 : u ^ 5 ≤ 1 := pow_le_one₀ hu.1 hu.2
  have hp : -7 ≤ -4 * u ^ 3 + 7 * u ^ 4 - 3 * u ^ 5 := by
    nlinarith [pow_nonneg hu.1 4]
  have hs := cellLength_bounds P hk.le
  have hs0 := cellLength_pos P hk.le
  have hd := lengthDrop_pos P
  have hd1 := (lengthDrop_le_eps P).trans P.eps_le_one
  have hs2 : cellLength P k ≤ 2 := by linarith [P.eps_le_one]
  have hsd : cellLength P k * lengthDrop P ≤ 2 := by nlinarith
  have hprod : -14 ≤ cellLength P k * lengthDrop P *
      (-4 * u ^ 3 + 7 * u ^ 4 - 3 * u ^ 5) := by
    have h := mul_le_mul_of_nonneg_left hp (mul_nonneg hs0.le hd.le)
    nlinarith
  have hquad : cellLength P k ^ 2 * u ≤ 4 := by
    nlinarith [sq_nonneg (cellLength P k), mul_nonneg (sq_nonneg (cellLength P k))
      (sub_nonneg.mpr hu.2)]
  rw [scalarObjective_cell P hk ht]
  change -22 ≤ nodeValue P k - cellLength P k ^ 2 * u + cellLength P k * lengthDrop P *
    (-4 * u ^ 3 + 7 * u ^ 4 - 3 * u ^ 5)
  linarith [nodeValue_lower P hk.le]

/-- The genuine scalar objective has a uniform lower bound on the full real line. -/
theorem scalarObjective_lower (P : Parameters) (t : ℝ) : -22 ≤ scalarObjective P t := by
  by_cases hl : t ≤ 0
  · rw [scalarObjective_left P hl]
    nlinarith [P.eps_pos]
  by_cases hr : nodeX P P.count + 1 ≤ t
  · rw [scalarObjective_right P hr]
    linarith [nodeValue_lower P (k := P.count) le_rfl, P.eps_le_one]
  by_cases hlast : nodeX P P.count ≤ t
  · have ht : t ∈ Icc (nodeX P P.count) (nodeX P P.count + 1) :=
      ⟨hlast, le_of_not_ge hr⟩
    rw [scalarObjective_transition P ht]
    have hu : t - nodeX P P.count ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have h4 : (t - nodeX P P.count) ^ 4 ≤ 1 := pow_le_one₀ hu.1 hu.2
    have hlin : P.eps * (t - nodeX P P.count) ≤ 1 := by nlinarith [P.eps_pos, P.eps_le_one]
    have hquart : P.eps / 2 * (t - nodeX P P.count) ^ 4 ≤ 1 / 2 := by
      nlinarith [P.eps_pos, P.eps_le_one, pow_nonneg hu.1 4]
    nlinarith [nodeValue_lower P (k := P.count) le_rfl,
      mul_nonneg P.eps_pos.le (pow_nonneg hu.1 3)]
  obtain ⟨k, hk, hkt⟩ := exists_adjacent_cell P.count_pos (nodeX P)
    (show t ∈ Icc (nodeX P 0) (nodeX P P.count) by
      simpa [nodeX] using (show t ∈ Icc (0 : ℝ) (nodeX P P.count) from
        ⟨le_of_not_ge hl, le_of_not_ge hlast⟩))
  exact scalarObjective_cell_lower P hk hkt

/-- Derivatives through order two of a smoothing cell are the actual rescaled smoothing jets. -/
theorem quinticCell_constantJets_derivatives (x s a b t : ℝ) {j : ℕ}
    (hj : j = 1 ∨ j = 2) :
    iteratedDeriv j (quinticCell x s (constantJet a) (constantJet b)) t =
      (b - a) * (s⁻¹) ^ j * iteratedDeriv j smoothStep ((t - x) / s) := by
  rw [iteratedDeriv_quinticCell]
  change _ = (b - a) * (s⁻¹) ^ j *
    iteratedDeriv j (fun u => smoothStepPolynomial.eval u) ((t - x) / s)
  rw [Polynomial.iteratedDeriv_eval]
  rcases hj with rfl | rfl <;>
    norm_num [quinticPolynomial, Finset.sum_range_succ, quinticCoefficient,
      quinticResidual, scaledJet, constantJet, smoothStepPolynomial,
      Function.iterate_succ_apply', derivative_pow] <;> ring

/-- A nonpositive outward coordinate kills both the value and the actual first derivative
of each correction coefficient, including at the seam. -/
theorem deriv_correctionCoefficient_of_nonpos (i : Fin 3) {q : ℝ} (hq : q ≤ 0) :
    deriv (correctionCoefficient i) q = 0 := by
  have hd := ((contDiff_correctionCoefficient i).differentiable (by norm_num)) q
  have heq : EqOn (correctionCoefficient i) (fun _ => (0 : ℝ)) (Iic q) := by
    intro t ht
    exact correctionCoefficient_of_nonpos i (ht.trans hq)
  rw [← hd.derivWithin (uniqueDiffWithinAt_Iic q),
    derivWithin_congr heq (correctionCoefficient_of_nonpos i hq)]
  simp

/-- A correction whose outward coordinate is nonpositive has zero actual differential,
even at the moving inner seam. -/
theorem hasFDerivAt_correction_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (hq : g x ≤ 0) :
    HasFDerivAt (fun y => correction (f y) (g y)) (0 : E →L[ℝ] ℝ) x := by
  have hc (i : Fin 3) : HasFDerivAt (fun y => correctionCoefficient i (g y)) (0 : E →L[ℝ] ℝ) x := by
    have hi := ((contDiff_correctionCoefficient i).differentiable (by norm_num) (g x)).hasDerivAt
    rw [deriv_correctionCoefficient_of_nonpos i hq] at hi
    simpa [Function.comp_def] using hi.comp_hasFDerivAt x hg
  convert (((hf.pow 2).mul (hc 2)).add (hf.mul (hc 1))).add (hc 0) using 1
  · rfl
  · simp [correctionCoefficient_of_nonpos _ hq]

/-- In the closed quadratic core the actual first differential is that of the quadratic,
including both inner seams. -/
theorem hasFDerivAt_profile_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hl : -f x / 2 ≤ g x) (hu : g x ≤ f x / 2) :
    HasFDerivAt (fun y => profile (f y) (g y)) ((2 * g x) • g') x := by
  have hupper := hasFDerivAt_correction_zero hf (hg.sub (hf.mul_const (1 / 2 : ℝ)))
    (show g x - f x * (1 / 2 : ℝ) ≤ 0 by linarith)
  have hlower := hasFDerivAt_correction_zero hf (hg.neg.sub (hf.mul_const (1 / 2 : ℝ)))
    (show -g x - f x * (1 / 2 : ℝ) ≤ 0 by linarith)
  convert ((hg.pow 2).add hupper).add hlower using 1 <;>
    simp [profile, div_eq_mul_inv]
  rfl

/-- The actual moving-strip term on the Euclidean plane. -/
def euclideanMovingProfile (P : Parameters) (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  profile (scalarWidth P (p 0)) (p 1 - scalarMidpoint P (p 0))

/-- The actual finite two-dimensional valley objective, with its source normalization. -/
def euclideanObjective (P : Parameters) (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (scalarObjective P (p 0) + euclideanMovingProfile P p) / Real.sqrt 2

/-- Composing the genuine profiles yields a genuinely C2 function on the Euclidean plane. -/
theorem contDiff_euclideanMovingProfile (P : Parameters) :
    ContDiff ℝ 2 (euclideanMovingProfile P) := by
  have h0 : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) => p 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  have h1 : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) => p 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff
  exact contDiff_profile.comp (((contDiff_scalarWidth P).comp h0).prodMk
    (h1.sub ((contDiff_scalarMidpoint P).comp h0)))

/-- The actual complete valley objective is globally twice continuously differentiable. -/
theorem contDiff_euclideanObjective (P : Parameters) : ContDiff ℝ 2 (euclideanObjective P) := by
  have h0 : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) => p 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  exact (((contDiff_scalarObjective P).comp h0).add
    (contDiff_euclideanMovingProfile P)).div_const _

/-- The actual complete Euclidean objective has a single uniform lower bound for all
admissible finite parameters, with no assumptions on profile or objective values. -/
theorem euclideanObjective_lower (P : Parameters) (p : EuclideanSpace ℝ (Fin 2)) :
    -22 / Real.sqrt 2 ≤ euclideanObjective P p := by
  apply (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
  exact (scalarObjective_lower P (p 0)).trans (le_add_of_nonneg_right
    (profile_nonneg (scalarWidth_pos P (p 0)).le _))

/-- The actual objective has the prescribed first derivative at each source node. -/
theorem hasDerivAt_scalarObjective_node (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    HasDerivAt (scalarObjective P) (-cellLength P k) (nodeX P k) := by
  have h := ((contDiff_scalarObjective P).differentiable (by norm_num) (nodeX P k)).hasDerivAt
  have he := scalarObjective_node_jets P hk (j := 1) (by omega)
  simp only [iteratedDeriv_one, objectiveJet,
    ite_eq_right (by omega : (1 : ℕ) ≠ 0)] at he
  rwa [he] at h

/-- The actual width has zero first derivative at each source node. -/
theorem hasDerivAt_scalarWidth_node (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    HasDerivAt (scalarWidth P) 0 (nodeX P k) := by
  have h := ((contDiff_scalarWidth P).differentiable (by norm_num) (nodeX P k)).hasDerivAt
  have he := scalarWidth_node_jets P hk (j := 1) (by omega)
  simp only [iteratedDeriv_one, widthJet, constantJet, ite_eq_right (by omega : (1 : ℕ) ≠ 0)] at he
  rwa [he] at h

/-- The actual midpoint has zero first derivative at each source node. -/
theorem hasDerivAt_scalarMidpoint_node (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    HasDerivAt (scalarMidpoint P) 0 (nodeX P k) := by
  have h := ((contDiff_scalarMidpoint P).differentiable (by norm_num) (nodeX P k)).hasDerivAt
  have he := scalarMidpoint_node_jets P hk (j := 1) (by omega)
  simp only [iteratedDeriv_one, midpointJet, constantJet,
    ite_eq_right (by omega : (1 : ℕ) ≠ 0)] at he
  rwa [he] at h

/-- The actual finite chain in the Euclidean plane. -/
def nodePoint (P : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![nodeX P k, nodeY P k]

/-- The displayed gradient vector at a prescribed source node. -/
def nodeGradient (P : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-cellLength P k / Real.sqrt 2,
    -cellSign k * cellLength P k / Real.sqrt 2]

/-- Nodal width is the source cell length. -/
@[simp] theorem scalarWidth_node (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    scalarWidth P (nodeX P k) = cellLength P k := by
  simpa [widthJet, constantJet] using scalarWidth_node_jets P hk (j := 0) (by omega)

/-- Nodal midpoint is the source midpoint. -/
@[simp] theorem scalarMidpoint_node (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    scalarMidpoint P (nodeX P k) = nodeMidpoint P k := by
  simpa [midpointJet, constantJet] using scalarMidpoint_node_jets P hk (j := 0) (by omega)

/-- The two coordinate projections of a node are its specified horizontal and vertical values. -/
@[simp] theorem nodePoint_apply (P : Parameters) (k : ℕ) (i : Fin 2) :
    nodePoint P k i = (![nodeX P k, nodeY P k] : Fin 2 → ℝ) i := rfl

/-- The displayed nodal vector is the genuine Fréchet gradient of the complete objective. -/
theorem hasFDerivAt_euclideanObjective_node (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    HasFDerivAt (euclideanObjective P) (innerSL ℝ (nodeGradient P k)) (nodePoint P k) := by
  let p := nodePoint P k
  let c0 := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
  let c1 := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
  have h0 := c0.hasFDerivAt (x := p)
  have h1 := c1.hasFDerivAt (x := p)
  have hf : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) => scalarObjective P (q 0))
      ((-cellLength P k) • c0) p := by
    simpa [p, c0, Function.comp_def] using
      (hasDerivAt_scalarObjective_node P hk).comp_hasFDerivAt p h0
  have hw : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) => scalarWidth P (q 0))
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) p := by
    simpa [p, c0, Function.comp_def] using (hasDerivAt_scalarWidth_node P hk).comp_hasFDerivAt p h0
  have hm : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) => scalarMidpoint P (q 0))
      (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) p := by
    simpa [p, c0, Function.comp_def] using
      (hasDerivAt_scalarMidpoint_node P hk).comp_hasFDerivAt p h0
  have hz : HasFDerivAt
      (fun q : EuclideanSpace ℝ (Fin 2) => q 1 - scalarMidpoint P (q 0)) c1 p := by
    convert h1.sub hm using 1 <;> simp
    rfl
  have hcore : -scalarWidth P (p 0) / 2 ≤ p 1 - scalarMidpoint P (p 0) ∧
      p 1 - scalarMidpoint P (p 0) ≤ scalarWidth P (p 0) / 2 := by
    simp only [p, nodePoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, scalarWidth_node P hk, scalarMidpoint_node P hk, nodeMidpoint]
    have hs := (cellLength_pos P hk).le
    rcases neg_one_pow_eq_or ℝ k with h | h <;> dsimp [cellSign] <;> rw [h] <;>
      constructor <;> linarith
  have hp := hasFDerivAt_profile_core hw hz hcore.1 hcore.2
  convert (hf.add hp).mul_const ((Real.sqrt 2)⁻¹) using 1
  · rfl
  · ext q
    simp [p, c0, c1, nodeGradient, nodeMidpoint, scalarMidpoint_node P hk,
      innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_two, smul_eq_mul]
    ring

/-- The canonical gradient of the actual objective agrees with its nodal formula. -/
theorem gradient_euclideanObjective_node (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    gradient (euclideanObjective P) (nodePoint P k) = nodeGradient P k :=
  (hasGradientAt_iff_hasFDerivAt.mpr (hasFDerivAt_euclideanObjective_node P hk)).gradient

/-- The true gradient norm at every node is exactly its prescribed cell length. -/
theorem norm_gradient_euclideanObjective_node (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    ‖gradient (euclideanObjective P) (nodePoint P k)‖ = cellLength P k := by
  rw [gradient_euclideanObjective_node P hk]
  have hsign : cellSign k ^ 2 = 1 := by simp [cellSign, ← pow_mul]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : ‖nodeGradient P k‖ ^ 2 = cellLength P k ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, nodeGradient]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (nodeGradient P k), cellLength_pos P hk]

/-- Every source successor is the prescribed negative-gradient step of length square root two. -/
theorem nodePoint_succ (P : Parameters) {k : ℕ} (hk : k < P.count) :
    nodePoint P (k + 1) = nodePoint P k - Real.sqrt 2 •
      gradient (euclideanObjective P) (nodePoint P k) := by
  rw [gradient_euclideanObjective_node P hk.le]
  ext i
  fin_cases i <;> simp [nodePoint, nodeGradient, nodeX_succ, nodeY_succ, smul_eq_mul]
  all_goals field_simp
  all_goals ring

/-- The terminal gradient norm equals the tolerance. -/
theorem terminal_gradient_norm (P : Parameters) :
    ‖gradient (euclideanObjective P) (nodePoint P P.count)‖ = P.eps := by
  rw [norm_gradient_euclideanObjective_node P le_rfl, cellLength_count]

/-- Every earlier gradient norm is strictly larger than the tolerance. -/
theorem preceding_gradient_norm (P : Parameters) {k : ℕ} (hk : k < P.count) :
    P.eps < ‖gradient (euclideanObjective P) (nodePoint P k)‖ := by
  rw [norm_gradient_euclideanObjective_node P hk.le]
  have hN : (0 : ℝ) < P.count := Nat.cast_pos.mpr P.count_pos
  have hkR : (k : ℝ) < P.count := Nat.cast_lt.mpr hk
  have hq : (k : ℝ) / P.count < 1 := (div_lt_one hN).mpr hkR
  dsimp [cellLength]
  nlinarith [P.eps_pos]

end Optimization.SteepestDescentValley
