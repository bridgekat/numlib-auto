import Numlib.Optimization.SteepestDescentValleyScalar

/-!
# Uniform derivatives of the finite width and midpoint

All bounds concern the actual spline derivatives. The inverse cell length losses are
cancelled by the integer count condition, rather than assumed as profile fields.
-/

noncomputable section
open Set Polynomial Hermite

namespace Optimization.SteepestDescentValley

/-- The first normalized length decrement is at most one. -/
theorem lengthDrop_div_length_le_one (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    lengthDrop P / cellLength P k ≤ 1 := by
  exact (div_le_one (cellLength_pos P hk)).mpr
    ((lengthDrop_le_eps P).trans (cellLength_bounds P hk).1)

/-- The squared inverse length loss is also cancelled by the finite count condition. -/
theorem lengthDrop_div_length_sq_le_one (P : Parameters) {k : ℕ} (hk : k ≤ P.count) :
    lengthDrop P / cellLength P k ^ 2 ≤ 1 := by
  apply (div_le_one (sq_pos_of_pos (cellLength_pos P hk))).mpr
  have hdrop : lengthDrop P ≤ P.eps ^ 2 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr P.count_pos)).mpr
    linarith [P.scaled_count_lower, P.eps_le_one]
  have hs := (cellLength_bounds P hk).1
  nlinarith [P.eps_pos]

/-- The actual width derivatives on a source cell are the rescaled smoothing derivatives. -/
theorem scalarWidth_cell_derivatives (P : Parameters) {k j : ℕ} (hk : k < P.count)
    (hj : j = 1 ∨ j = 2) {t : ℝ} (ht : t ∈ Icc (nodeX P k) (nodeX P (k + 1))) :
    iteratedDeriv j (scalarWidth P) t = -lengthDrop P * (cellLength P k)⁻¹ ^ j *
      iteratedDeriv j smoothStep ((t - nodeX P k) / cellLength P k) := by
  rw [scalarWidth, finiteQuintic_cell_jets (widthJet P) (nodeX_strict P) hk
    (by rcases hj with rfl | rfl <;> omega) ht,
    nodeX_succ, add_sub_cancel_left, widthJet, widthJet,
    quinticCell_constantJets_derivatives _ _ _ _ _ hj, cellLength_succ]
  ring

/-- The actual midpoint derivatives on a source cell are its signed smoothing derivatives. -/
theorem scalarMidpoint_cell_derivatives (P : Parameters) {k j : ℕ} (hk : k < P.count)
    (hj : j = 1 ∨ j = 2) {t : ℝ} (ht : t ∈ Icc (nodeX P k) (nodeX P (k + 1))) :
    iteratedDeriv j (scalarMidpoint P) t = cellSign k * lengthDrop P / 2 *
      (cellLength P k)⁻¹ ^ j * iteratedDeriv j smoothStep ((t - nodeX P k) / cellLength P k) := by
  rw [scalarMidpoint, finiteQuintic_cell_jets (midpointJet P) (nodeX_strict P) hk
    (by rcases hj with rfl | rfl <;> omega) ht,
    nodeX_succ, add_sub_cancel_left, midpointJet, midpointJet,
    quinticCell_constantJets_derivatives _ _ _ _ _ hj, nodeMidpoint_succ]
  ring

/-- Width derivatives vanish on both exterior tails, including their endpoints. -/
theorem scalarWidth_exterior_derivatives (P : Parameters) {j : ℕ} (hj : j = 1 ∨ j = 2)
    {t : ℝ} (ht : t ≤ 0 ∨ nodeX P P.count ≤ t) : iteratedDeriv j (scalarWidth P) t = 0 := by
  have hj2 : j ≤ 2 := by rcases hj with rfl | rfl <;> omega
  have hj0 : j ≠ 0 := by rcases hj with rfl | rfl <;> omega
  rcases ht with ht | ht
  · rw [scalarWidth, finiteQuintic_left_jets (widthJet P) (nodeX_strict P) hj2
      (show t ≤ nodeX P 0 by simpa [nodeX] using ht)]
    simp [widthJet, endpointTaylor_constantJet, eval_iterate_derivative_C, constantJet, hj0]
  · rw [scalarWidth, finiteQuintic_right_jets (widthJet P) (nodeX_strict P) hj2 ht]
    simp [widthJet, endpointTaylor_constantJet, eval_iterate_derivative_C, constantJet, hj0]

/-- Midpoint derivatives vanish on both exterior tails, including their endpoints. -/
theorem scalarMidpoint_exterior_derivatives (P : Parameters) {j : ℕ} (hj : j = 1 ∨ j = 2)
    {t : ℝ} (ht : t ≤ 0 ∨ nodeX P P.count ≤ t) : iteratedDeriv j (scalarMidpoint P) t = 0 := by
  have hj2 : j ≤ 2 := by rcases hj with rfl | rfl <;> omega
  have hj0 : j ≠ 0 := by rcases hj with rfl | rfl <;> omega
  rcases ht with ht | ht
  · rw [scalarMidpoint, finiteQuintic_left_jets (midpointJet P) (nodeX_strict P) hj2
      (show t ≤ nodeX P 0 by simpa [nodeX] using ht)]
    simp [midpointJet, endpointTaylor_constantJet, eval_iterate_derivative_C, constantJet, hj0]
  · rw [scalarMidpoint, finiteQuintic_right_jets (midpointJet P) (nodeX_strict P) hj2 ht]
    simp [midpointJet, endpointTaylor_constantJet, eval_iterate_derivative_C, constantJet, hj0]

/-- The first two normalized decrement factors lie in the unit interval. -/
theorem lengthDrop_mul_inv_pow_bounds (P : Parameters) {k j : ℕ} (hk : k ≤ P.count)
    (hj : j = 1 ∨ j = 2) :
    0 ≤ lengthDrop P * (cellLength P k)⁻¹ ^ j ∧
      lengthDrop P * (cellLength P k)⁻¹ ^ j ≤ 1 := by
  refine ⟨by positivity [lengthDrop_pos P, cellLength_pos P hk], ?_⟩
  rcases hj with rfl | rfl
  · simpa only [pow_one, ← div_eq_mul_inv] using lengthDrop_div_length_le_one P hk
  · simpa only [div_eq_mul_inv, inv_pow] using lengthDrop_div_length_sq_le_one P hk

/-- A single constant bounds both actual width and midpoint derivatives of orders one and
two, on the entire real line and before choosing any finite-chain parameters. -/
theorem exists_width_midpoint_derivative_bound :
    ∃ C > 0, ∀ (P : Parameters) (j : ℕ), j = 1 ∨ j = 2 → ∀ t : ℝ,
      |iteratedDeriv j (scalarWidth P) t| ≤ C ∧
        |iteratedDeriv j (scalarMidpoint P) t| ≤ C := by
  have hs : ContDiff ℝ ⊤ smoothStep := by
    change ContDiff ℝ ⊤ (fun t => smoothStep t)
    simp only [smoothStep_eq]
    fun_prop
  have hb (j : ℕ) : ∃ B ≥ (0 : ℝ), ∀ u ∈ Icc (0 : ℝ) 1,
      |iteratedDeriv j smoothStep u| ≤ B := by
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hs.continuous_iteratedDeriv j (by simp)).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun u hu => by
      simpa only [Real.norm_eq_abs] using (hB u hu).trans (le_max_left B 0)⟩
  obtain ⟨B1, hB1, hb1⟩ := hb 1
  obtain ⟨B2, hB2, hb2⟩ := hb 2
  let C := 1 + B1 + B2
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro P j hj t
  by_cases hext : t ≤ 0 ∨ nodeX P P.count ≤ t
  · rw [scalarWidth_exterior_derivatives P hj hext, scalarMidpoint_exterior_derivatives P hj hext]
    simp [hC.le]
  have hcell : t ∈ Icc (nodeX P 0) (nodeX P P.count) := by
    simp only [not_or, not_le] at hext
    simpa [nodeX] using (show t ∈ Icc (0 : ℝ) (nodeX P P.count) from
      ⟨hext.1.le, hext.2.le⟩)
  obtain ⟨k, hk, hkt⟩ := exists_adjacent_cell P.count_pos (nodeX P) hcell
  have hu := cell_coordinate_mem_Icc P hk hkt
  have hD := lengthDrop_mul_inv_pow_bounds P hk.le hj
  have hB : |iteratedDeriv j smoothStep ((t - nodeX P k) / cellLength P k)| ≤ C := by
    rcases hj with rfl | rfl
    · exact (hb1 _ hu).trans (by dsimp [C]; linarith)
    · exact (hb2 _ hu).trans (by dsimp [C]; linarith)
  rw [scalarWidth_cell_derivatives P hk hj hkt, scalarMidpoint_cell_derivatives P hk hj hkt]
  have hW : |-lengthDrop P * (cellLength P k)⁻¹ ^ j *
      iteratedDeriv j smoothStep ((t - nodeX P k) / cellLength P k)| ≤ C := by
    rw [neg_mul, abs_mul, abs_neg, abs_of_nonneg hD.1]
    exact (mul_le_mul_of_nonneg_right hD.2 (abs_nonneg _)).trans (by simpa using hB)
  refine ⟨hW, ?_⟩
  calc
    _ = (1 / 2 : ℝ) * |-lengthDrop P * (cellLength P k)⁻¹ ^ j *
        iteratedDeriv j smoothStep ((t - nodeX P k) / cellLength P k)| := by
      simp only [abs_mul, abs_div, abs_cellSign, abs_neg]
      norm_num
      ring
    _ ≤ (1 / 2 : ℝ) * C := mul_le_mul_of_nonneg_left hW (by norm_num)
    _ ≤ C := by linarith

/-- The actual first derivative of a source objective interpolation cell. -/
theorem deriv_quinticCell_objective (x : ℝ) {s : ℝ} (hs : s ≠ 0) (d v t : ℝ) :
    deriv (quinticCell x s (fun j => if j = 0 then v else if j = 1 then -s else 0)
      (fun j => if j = 0 then v - s ^ 2 else if j = 1 then -(s - d) else 0)) t =
        -s + d * slopeAdjustment ((t - x) / s) := by
  rw [← iteratedDeriv_one, iteratedDeriv_quinticCell, slopeAdjustment_eq]
  norm_num [quinticPolynomial, Finset.sum_range_succ, quinticCoefficient,
    quinticResidual, scaledJet, Function.iterate_succ_apply', derivative_pow]
  field_simp
  ring

/-- The actual second derivative of a source objective interpolation cell. -/
theorem iteratedDeriv_two_quinticCell_objective (x : ℝ) {s : ℝ} (hs : s ≠ 0) (d v t : ℝ) :
    iteratedDeriv 2 (quinticCell x s (fun j => if j = 0 then v else if j = 1 then -s else 0)
      (fun j => if j = 0 then v - s ^ 2 else if j = 1 then -(s - d) else 0)) t =
        d / s * (-24 * ((t - x) / s) + 84 * ((t - x) / s) ^ 2 -
          60 * ((t - x) / s) ^ 3) := by
  rw [iteratedDeriv_quinticCell]
  norm_num [quinticPolynomial, Finset.sum_range_succ, quinticCoefficient,
    quinticResidual, scaledJet, Function.iterate_succ_apply', derivative_pow]
  field_simp
  ring

/-- The first two actual objective derivatives on every source cell. -/
theorem scalarObjective_cell_derivatives (P : Parameters) {k : ℕ} (hk : k < P.count)
    {t : ℝ} (ht : t ∈ Icc (nodeX P k) (nodeX P (k + 1))) :
    deriv (scalarObjective P) t = -cellLength P k + lengthDrop P *
      slopeAdjustment ((t - nodeX P k) / cellLength P k) ∧
    iteratedDeriv 2 (scalarObjective P) t = lengthDrop P / cellLength P k *
      (-24 * ((t - nodeX P k) / cellLength P k) +
        84 * ((t - nodeX P k) / cellLength P k) ^ 2 -
        60 * ((t - nodeX P k) / cellLength P k) ^ 3) := by
  have he (j : ℕ) (hj : j ≤ 2) := finiteQuintic_cell_jets (extendedObjectiveJet P)
    (extendedNodeX_strict P) (show k < P.count + 1 by omega) hj
    (show t ∈ Icc (extendedNodeX P k) (extendedNodeX P (k + 1)) by
      simpa only [extendedNodeX_of_le P hk.le,
        extendedNodeX_of_le P (by omega : k + 1 ≤ P.count)] using ht)
  have hb : objectiveJet P (k + 1) = fun j =>
      if j = 0 then nodeValue P k - cellLength P k ^ 2
      else if j = 1 then -(cellLength P k - lengthDrop P) else 0 := by
    funext j
    simp only [objectiveJet, nodeValue_succ, cellLength_succ]
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  simp only [extendedNodeX_of_le P hk.le,
    extendedNodeX_of_le P (by omega : k + 1 ≤ P.count), extendedObjectiveJet,
    ite_eq_left hk.le, ite_eq_left (by omega : k + 1 ≤ P.count),
    nodeX_succ, add_sub_cancel_left, hb] at h1 h2
  constructor
  · rw [scalarObjective, ← iteratedDeriv_one, h1, iteratedDeriv_one]
    exact deriv_quinticCell_objective _ (ne_of_gt (cellLength_pos P hk.le)) _ _ _
  · rw [scalarObjective, h2]
    exact iteratedDeriv_two_quinticCell_objective _ (ne_of_gt (cellLength_pos P hk.le)) _ _ _

/-- The first two actual objective derivatives on the terminal unit transition. -/
theorem scalarObjective_transition_derivatives (P : Parameters) {t : ℝ}
    (ht : t ∈ Icc (nodeX P P.count) (nodeX P P.count + 1)) :
    deriv (scalarObjective P) t = -P.eps + 3 * P.eps * (t - nodeX P P.count) ^ 2 -
      2 * P.eps * (t - nodeX P P.count) ^ 3 ∧
    iteratedDeriv 2 (scalarObjective P) t =
      6 * P.eps * (t - nodeX P P.count) - 6 * P.eps * (t - nodeX P P.count) ^ 2 := by
  have he (j : ℕ) (hj : j ≤ 2) := finiteQuintic_cell_jets (extendedObjectiveJet P)
    (extendedNodeX_strict P) (show P.count < P.count + 1 by omega) hj
    (show t ∈ Icc (extendedNodeX P P.count) (extendedNodeX P (P.count + 1)) by
      simpa only [extendedNodeX_of_le P le_rfl, extendedNodeX_last] using ht)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  simp only [extendedNodeX_of_le P le_rfl, extendedNodeX_last,
    add_sub_cancel_left, iteratedDeriv_quinticCell] at h1 h2
  constructor
  · rw [scalarObjective, ← iteratedDeriv_one, h1]
    norm_num [extendedObjectiveJet, objectiveJet, constantJet, quinticPolynomial,
      Finset.sum_range_succ, quinticCoefficient, quinticResidual, scaledJet,
      Function.iterate_succ_apply', derivative_pow]
    ring
  · rw [scalarObjective, h2]
    norm_num [extendedObjectiveJet, objectiveJet, constantJet, quinticPolynomial,
      Finset.sum_range_succ, quinticCoefficient, quinticResidual, scaledJet,
      Function.iterate_succ_apply', derivative_pow]
    ring

/-- The actual affine left objective branch has constant slope and vanishing second derivative. -/
theorem scalarObjective_left_derivatives (P : Parameters) {t : ℝ} (ht : t ≤ 0) :
    deriv (scalarObjective P) t = -2 * P.eps ∧ iteratedDeriv 2 (scalarObjective P) t = 0 := by
  have he (j : ℕ) (hj : j ≤ 2) := finiteQuintic_left_jets (extendedObjectiveJet P)
    (extendedNodeX_strict P) hj
    (show t ≤ extendedNodeX P 0 by simpa [extendedNodeX, nodeX] using ht)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  constructor
  · rw [scalarObjective, ← iteratedDeriv_one, h1]
    norm_num [extendedObjectiveJet, objectiveJet, endpointTaylor, jetPoly,
      Finset.sum_range_succ, Function.iterate_succ_apply', derivative_pow]
  · rw [scalarObjective, h2]
    norm_num [extendedObjectiveJet, objectiveJet, endpointTaylor, jetPoly,
      Finset.sum_range_succ, Function.iterate_succ_apply', derivative_pow]

/-- All positive-order derivatives through order two vanish on the constant right objective tail. -/
theorem scalarObjective_right_derivatives (P : Parameters) {j : ℕ} (hj : j = 1 ∨ j = 2)
    {t : ℝ} (ht : nodeX P P.count + 1 ≤ t) : iteratedDeriv j (scalarObjective P) t = 0 := by
  rw [scalarObjective, finiteQuintic_right_jets (extendedObjectiveJet P)
    (extendedNodeX_strict P) (by rcases hj with rfl | rfl <;> omega)
    (show extendedNodeX P (P.count + 1) ≤ t by simpa using ht)]
  have hj0 : j ≠ 0 := by rcases hj with rfl | rfl <;> omega
  simp [extendedObjectiveJet, endpointTaylor_constantJet, eval_iterate_derivative_C,
    constantJet, hj0]

/-- A fixed numerical constant bounds the first two actual objective-profile derivatives
on the whole real line, uniformly in tolerance and integer count. -/
theorem scalarObjective_derivatives_bound (P : Parameters) {j : ℕ} (hj : j = 1 ∨ j = 2) (t : ℝ) :
    |iteratedDeriv j (scalarObjective P) t| ≤ 200 := by
  by_cases hl : t ≤ 0
  · have h := scalarObjective_left_derivatives P hl
    rcases hj with rfl | rfl
    · rw [iteratedDeriv_one, h.1, abs_mul, abs_neg, abs_of_nonneg P.eps_pos.le]
      norm_num
      linarith [P.eps_le_one]
    · rw [h.2]
      norm_num
  by_cases hr : nodeX P P.count + 1 ≤ t
  · rw [scalarObjective_right_derivatives P hj hr]
    norm_num
  by_cases hlast : nodeX P P.count ≤ t
  · have ht : t ∈ Icc (nodeX P P.count) (nodeX P P.count + 1) := ⟨hlast, le_of_not_ge hr⟩
    have hu : t - nodeX P P.count ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have h2 : (t - nodeX P P.count) ^ 2 ≤ 1 := pow_le_one₀ hu.1 hu.2
    have h3 : (t - nodeX P P.count) ^ 3 ≤ 1 := pow_le_one₀ hu.1 hu.2
    have hd := scalarObjective_transition_derivatives P ht
    rcases hj with rfl | rfl
    · rw [iteratedDeriv_one, hd.1, abs_le]
      have h2p := pow_nonneg hu.1 2
      have h3p := pow_nonneg hu.1 3
      constructor <;> nlinarith [P.eps_pos, P.eps_le_one,
        mul_nonneg P.eps_pos.le (sub_nonneg.mpr h2),
        mul_nonneg P.eps_pos.le (sub_nonneg.mpr h3)]
    · rw [hd.2, abs_le]
      constructor <;> nlinarith [P.eps_pos, P.eps_le_one, pow_nonneg hu.1 2,
        mul_nonneg P.eps_pos.le (sub_nonneg.mpr h2),
        mul_nonneg P.eps_pos.le (sub_nonneg.mpr hu.2)]
  obtain ⟨k, hk, hkt⟩ := exists_adjacent_cell P.count_pos (nodeX P)
    (show t ∈ Icc (nodeX P 0) (nodeX P P.count) by
      simpa [nodeX] using (show t ∈ Icc (0 : ℝ) (nodeX P P.count) from
        ⟨le_of_not_ge hl, le_of_not_ge hlast⟩))
  let u := (t - nodeX P k) / cellLength P k
  have hu : u ∈ Icc (0 : ℝ) 1 := cell_coordinate_mem_Icc P hk hkt
  have h2 : u ^ 2 ≤ 1 := pow_le_one₀ hu.1 hu.2
  have h3 : u ^ 3 ≤ 1 := pow_le_one₀ hu.1 hu.2
  have h4 : u ^ 4 ≤ 1 := pow_le_one₀ hu.1 hu.2
  have h2p := pow_nonneg hu.1 2
  have h3p := pow_nonneg hu.1 3
  have h4p := pow_nonneg hu.1 4
  have hd := scalarObjective_cell_derivatives P hk hkt
  rcases hj with rfl | rfl
  · rw [iteratedDeriv_one, hd.1]
    change |-cellLength P k + lengthDrop P * slopeAdjustment u| ≤ 200
    have hD : |slopeAdjustment u| ≤ 55 := by
      rw [slopeAdjustment_eq, abs_le]
      constructor <;> nlinarith
    have hs := cellLength_bounds P hk.le
    have hdpos := lengthDrop_pos P
    have hdrop := lengthDrop_le_eps P
    calc
      _ ≤ |-cellLength P k| + |lengthDrop P * slopeAdjustment u| := abs_add_le _ _
      _ = cellLength P k + lengthDrop P * |slopeAdjustment u| := by
        rw [abs_neg, abs_of_pos (cellLength_pos P hk.le), abs_mul, abs_of_pos hdpos]
      _ ≤ cellLength P k + lengthDrop P * 55 := by gcongr
      _ ≤ 200 := by nlinarith [P.eps_le_one, P.eps_pos]
  · rw [hd.2]
    change |lengthDrop P / cellLength P k * (-24 * u + 84 * u ^ 2 - 60 * u ^ 3)| ≤ 200
    have hD : |-24 * u + 84 * u ^ 2 - 60 * u ^ 3| ≤ 168 := by
      rw [abs_le]
      constructor <;> nlinarith [hu.1, hu.2]
    have hR0 : 0 ≤ lengthDrop P / cellLength P k :=
      div_nonneg (lengthDrop_pos P).le (cellLength_pos P hk.le).le
    rw [abs_mul, abs_of_nonneg hR0]
    calc
      _ ≤ 1 * |-24 * u + 84 * u ^ 2 - 60 * u ^ 3| :=
        mul_le_mul_of_nonneg_right (lengthDrop_div_length_le_one P hk.le) (abs_nonneg _)
      _ ≤ 200 := by linarith

end Optimization.SteepestDescentValley
