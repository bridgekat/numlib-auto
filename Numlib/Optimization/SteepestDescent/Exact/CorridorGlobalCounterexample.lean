import Numlib.Optimization.SteepestDescent.Exact.CorridorGradient

/-!
# The printed corridor does not give global exact line searches

At accuracy one quarter the source's first prescribed endpoint is beaten by a
later point on the same positive negative-gradient ray. The comparison uses only
prescribed node values and the exterior plateau, independently of the chosen
smooth terminal extension. It distinguishes the appendix's first local minimum
argument from the global line search contract (2.2.26).
-/

open Set
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- Actual source scalar values are preserved at all finite nodes. -/
theorem scalarObjective_node (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    scalarObjective P (horizontal P k) = scalarValue P k := by
  have hle : horizontal P k ≤ horizontal P P.horizon := by
    rcases lt_or_eq_of_le hk with hk | rfl
    · exact (horizontal_increasing P k P.horizon hk le_rfl).le
    · exact le_rfl
  have h := scalarObjective_left P (j := 0) (by omega) hle
  simp only [iteratedDeriv_zero] at h
  rw [h]
  have hj := (curve_spec P 2).2.1 k hk 0 (by omega)
  simpa [curveJet,scalarJet] using hj

/-- The genuine corridor value at a source node is one quarter of its squared width. -/
theorem residualCorridor_node (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    residualCorridor P (horizontal P k,vertical P k) = amplitude P k^2/4 := by
  change (fun w : ℝ × ℝ => profile w.1 w.2)
    (corridorCoordinates P (horizontal P k,vertical P k)) = _
  rw [corridorCoordinates_node P hk]
  dsimp only
  rw [profile_central (vertical_sub_center_mem P hk),vertical_sub_center]
  have hs : ((-1 : ℝ)^k)^2=1 := by
    rw [← pow_mul,mul_comm k 2,pow_mul]
    norm_num
  nlinarith [hs]

/-- The actual source objective recovers the prescribed scalar and corridor node values. -/
theorem objective_node (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon) :
    objective P (horizontal P k,vertical P k) =
      (scalarValue P k + amplitude P k^2/4)/Real.sqrt 2 := by
  simp only [objective,scalarObjective_node P hk,residualCorridor_node P hk]

/-- Actual exterior values at a finite source horizontal node use the source plateau. -/
theorem objective_node_exterior (P : Parameters) {k : ℕ} (hk : k ≤ P.horizon)
    {y : ℝ} (hy : amplitude P k / 2 + 1 ≤ y - centerValue P k) :
    objective P (horizontal P k,y) =
      (scalarValue P k+8*amplitude P k^2)/Real.sqrt 2 := by
  unfold objective
  rw [scalarObjective_node P hk]
  change (_ + (fun w : ℝ × ℝ => profile w.1 w.2)
    (corridorCoordinates P (horizontal P k,y)))/Real.sqrt 2 = _
  rw [corridorCoordinates_node P hk]
  dsimp only
  rw [profile_exterior (amplitude_pos P hk).le (Or.inr hy)]

/-- Fixed legal primitive source data for accuracy one quarter and its rounded horizon sixteen. -/
def globalCounterexampleParameters : Parameters where
  accuracy := 1/4
  horizon := 16
  accuracy_pos := by norm_num
  accuracy_le_one := by norm_num
  horizon_pos := by norm_num
  compatibility_lower := by norm_num
  compatibility_upper := by norm_num

/-- The actual first source endpoint has its explicit source value. -/
theorem globalCounterexample_first_value :
    objective globalCounterexampleParameters
      (horizontal globalCounterexampleParameters 1,vertical globalCounterexampleParameters 1) =
      (62401/16384 : ℝ)/Real.sqrt 2 := by
  rw [objective_node _ (by decide)]
  norm_num [scalarValue,amplitude,omega,globalCounterexampleParameters,Finset.sum_range_succ]

/-- A later point on the same initial diagonal ray lies in the exterior plateau
and has a strictly smaller value than the prescribed first endpoint. -/
theorem globalCounterexample_later_value :
    objective globalCounterexampleParameters
      (horizontal globalCounterexampleParameters 16,horizontal globalCounterexampleParameters 16) =
      (1061/512 : ℝ)/Real.sqrt 2 := by
  have hy : amplitude globalCounterexampleParameters 16 / 2 + 1 ≤
      horizontal globalCounterexampleParameters 16 -
        centerValue globalCounterexampleParameters 16 := by
    norm_num [amplitude,omega,horizontal,centerValue,vertical,globalCounterexampleParameters,
      Finset.sum_range_succ]
  rw [objective_node_exterior _ (by decide) hy]
  norm_num [scalarValue,amplitude,omega,globalCounterexampleParameters,Finset.sum_range_succ]

/-- The actual one-dimensional objective on the source negative-gradient ray. -/
def initialRayObjective (P : Parameters) (α : ℝ) : ℝ :=
  euclideanObjective P (gridPoint P 0 - α •
    gradient (euclideanObjective P) (gridPoint P 0))

/-- The prescribed first step on the actual negative-gradient ray reaches the first grid node. -/
theorem initialRayObjective_first (P : Parameters) :
    initialRayObjective P (Real.sqrt 2) = euclideanObjective P (gridPoint P 1) := by
  unfold initialRayObjective
  rw [← gridPoint_succ P (k := 0) P.horizon_pos]

/-- The actual farther source diagonal point lies on the same positive negative-gradient ray. -/
theorem globalCounterexample_far_on_ray :
    gridPoint globalCounterexampleParameters 0 -
      ((49/4 : ℝ)*Real.sqrt 2) • gradient (euclideanObjective globalCounterexampleParameters)
        (gridPoint globalCounterexampleParameters 0) = WithLp.toLp 2
          ![horizontal globalCounterexampleParameters 16,
            horizontal globalCounterexampleParameters 16] := by
  rw [euclideanObjective_gradient_node _ (by decide),gridPoint_zero]
  have hsq : Real.sqrt 2 ≠ 0 := by positivity
  apply PiLp.ext
  intro i
  fin_cases i <;>
    norm_num [gridDirection,globalCounterexampleParameters,amplitude,omega,horizontal,
      Finset.sum_range_succ,PiLp.smul_apply,PiLp.sub_apply]
  all_goals field_simp
  all_goals ring

/-- The exact source initial-ray value at its prescribed first step. -/
theorem globalCounterexample_initialRay_first :
    initialRayObjective globalCounterexampleParameters (Real.sqrt 2) =
      (62401/16384 : ℝ)/Real.sqrt 2 := by
  rw [initialRayObjective_first]
  exact globalCounterexample_first_value

/-- The exact source initial-ray value at a later positive step. -/
theorem globalCounterexample_initialRay_far :
    initialRayObjective globalCounterexampleParameters ((49/4 : ℝ)*Real.sqrt 2) =
      (1061/512 : ℝ)/Real.sqrt 2 := by
  unfold initialRayObjective
  rw [globalCounterexample_far_on_ray]
  exact globalCounterexample_later_value

/-- The first prescribed source endpoint is not a global line-search minimizer.
This refutes the global-SDEX reading of the source's exact-line-search assertion;
it does not refute the separate first-local-minimum property. -/
theorem globalCounterexample_not_global_line_minimum :
    ¬IsMinOn (initialRayObjective globalCounterexampleParameters) (Ici 0) (Real.sqrt 2) := by
  intro h
  have hh := h (by positivity : (0 : ℝ) ≤ (49/4 : ℝ)*Real.sqrt 2)
  change initialRayObjective globalCounterexampleParameters (Real.sqrt 2) ≤
    initialRayObjective globalCounterexampleParameters ((49/4 : ℝ)*Real.sqrt 2) at hh
  rw [globalCounterexample_initialRay_first,globalCounterexample_initialRay_far] at hh
  have hlt : (1061/512 : ℝ)/Real.sqrt 2 < (62401/16384 : ℝ)/Real.sqrt 2 := by
    exact (div_lt_div_iff_of_pos_right (by positivity : 0 < Real.sqrt 2)).mpr (by norm_num)
  exact (not_le_of_gt hlt) hh

/-- The counterexample uses exactly the canonical rounded data at accuracy one quarter. -/
theorem globalCounterexampleParameters_canonical : globalCounterexampleParameters =
    Parameters.ofAccuracy (1/4) (by norm_num) (by norm_num) := by
  norm_num [globalCounterexampleParameters,Parameters.ofAccuracy,roundedHorizon]

end ExactSteepestDescent.Corridor
