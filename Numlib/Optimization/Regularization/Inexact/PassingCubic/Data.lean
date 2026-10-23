import Numlib.Optimization.Regularization.Inexact.PassingCubic.Ghost
import Numlib.Optimization.Regularization.Inexact.Explicit.Run

/-!
# A finite inaccurate cubic execution: computed arrays

All optimality-check arrays are selected from proved genuine computations. The large
initial jet is reused on the rejected trial; subsequent data omit only a small actual
first derivative.
-/

namespace InexactRegularization.PassingCubic
open InexactTrustRegion

/-- The large dyadic initial parameter and permitted parameter expansion factor. -/
noncomputable def height : ℝ := 2 ^ 80
/-- The small positive second derivative defining the passing computed cubic. -/
noncomputable def curvature : ℝ := 16 / height ^ 2
/-- The strictly positive true gradient omitted from the passing computed jet. -/
noncomputable def perturbation : ℝ := (1 / 2 ^ 150) ^ 2

/-- The fixed dyadic constants satisfy every coercivity, jet and perturbation comparison
used in the execution. -/
theorem numeric_bounds :
    4 ≤ height ∧ 0 < curvature ∧ curvature ≤ 1 ∧
    6 * curvature ^ 2 < perturbation ∧ perturbation ≤ 1 ∧
    24 * height + 4 ≤ height ^ 2 ∧ 1 / 3 ≤ curvature * height ^ 2 := by
  norm_num [height, curvature, perturbation]

/-- Only the computed arrays returned by an ordered optimality check; correctness is
separately proved. -/
structure CheckData where
  reduced : Fin 3 → ℝ
  reference : ℝ
  direction : Fin 3 → ℕ → ℝ
  count : Fin 3 → ℕ
  selected : Option (Fin 3)

/-- The actual ordered Step1 computation for unit inherited radii and fixed positive
accuracies. -/
def CheckData.Valid (C : CheckData) (A : FormalMultilinearSeries ℝ ℝ ℝ) (σ : ℝ) : Prop :=
  StepOneComputation A 3 σ (1 / 2) (fun _ => 1 / 2) (fun _ => 1)
    C.reduced C.reference C.direction C.count C.selected

private theorem first_exists : ∃ C : CheckData,
    C.Valid (ghostJet height curvature) height ∧ C.selected = some 0 ∧
    C.reduced = (fun _ => 1) ∧ ‖C.reference‖ ≤ 1 := by
  obtain ⟨r, d, c, h, hr⟩ := ghost_initial_check (le_trans (by norm_num) numeric_bounds.1)
    numeric_bounds.2.1.le numeric_bounds.2.2.1
  exact ⟨⟨fun _ => 1, r, d, c, some 0⟩, h, rfl, rfl, hr⟩

/-- A selected-first initial check constructed from the actual inaccurate cubic
polynomial. -/
noncomputable def firstCheck : CheckData := Classical.choose first_exists

/-- The chosen initial check is genuine, selects first order and retains all unit radii. -/
theorem firstCheck_spec :
    firstCheck.Valid (ghostJet height curvature) height ∧ firstCheck.selected = some 0 ∧
    firstCheck.reduced = (fun _ => 1) ∧ ‖firstCheck.reference‖ ≤ 1 :=
  Classical.choose_spec first_exists

/-- Only the computed check, candidate and solved-radius arrays at the short ghost
iteration. -/
structure ShortData where
  check : CheckData
  step : ℝ
  solved : Fin 3 → ℝ

private theorem short_exists : ∃ S : ShortData,
    S.check.Valid (ghostJet height curvature) (height ^ 2) ∧
    S.check.selected = some 0 ∧
    StepTwoComputation (ghostJet height curvature) 3 modelOrder (height ^ 2)
      (9 / 10) (1 / 2) (fun _ => 1 / 2) S.check.reference S.check.reduced S.step S.solved ∧
    ‖S.step‖ < 1 := by
  obtain ⟨r, v, d, c, s, R, hone, htwo, hs⟩ := ghost_short_components
    (le_trans (by norm_num) numeric_bounds.1) numeric_bounds.2.1.le
    numeric_bounds.2.2.2.2.2.1
  exact ⟨⟨⟨r, v, d, c, some 0⟩, s, R⟩, hone, rfl, htwo, hs⟩

/-- A genuine short ghost return constructed by the actual inner model computation. -/
noncomputable def shortData : ShortData := Classical.choose short_exists

/-- Both primitive computations hold at the ghost return, and actual model comparison
forces its norm below one. -/
theorem shortData_spec :
    shortData.check.Valid (ghostJet height curvature) (height ^ 2) ∧
    shortData.check.selected = some 0 ∧
    StepTwoComputation (ghostJet height curvature) 3 modelOrder (height ^ 2)
      (9 / 10) (1 / 2) (fun _ => 1 / 2) shortData.check.reference shortData.check.reduced
      shortData.step shortData.solved ∧ ‖shortData.step‖ < 1 :=
  Classical.choose_spec short_exists

private theorem passing_exists : ∃ C : CheckData,
    C.Valid (jet curvature) (height ^ 2) ∧ C.selected = none ∧
    0 < C.reduced 2 ∧ C.reduced 2 ≤ 4 * curvature := by
  obtain ⟨r, v, d, c, hone, hb⟩ := exists_passing (by unfold height; positivity)
    numeric_bounds.2.2.2.2.2.2 (fun _ => 1) (fun _ => ⟨zero_lt_one, le_rfl⟩)
  exact ⟨⟨r, v, d, c, none⟩, hone, rfl,
    (hone.radius_bounds (fun _ => ⟨zero_lt_one, le_rfl⟩) 2).1, hb⟩

/-- A passing ordered check constructed from the globally nonnegative computed quartic
model. -/
noncomputable def passingCheck : CheckData := Classical.choose passing_exists

/-- The chosen passing check is genuine and its positive third-order radius is bounded by
four times the small curvature. -/
theorem passingCheck_spec :
    passingCheck.Valid (jet curvature) (height ^ 2) ∧ passingCheck.selected = none ∧
    0 < passingCheck.reduced 2 ∧ passingCheck.reduced 2 ≤ 4 * curvature :=
  Classical.choose_spec passing_exists

private theorem exact_exists : ∃ C : CheckData,
    C.Valid (ftaylorSeries ℝ (objective perturbation curvature) 0) (height ^ 2) := by
  have ht : ∀ i, 2 ≤ i → i ≤ 3 →
      ‖ftaylorSeries ℝ (objective perturbation curvature) 0 i‖ ≤ 1 := by
    intro i hi hi3
    change ‖iteratedFDeriv ℝ i (objective perturbation curvature) 0‖ ≤ 1
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, objective_jets _ _ hi3]
    interval_cases i <;> norm_num [Real.norm_eq_abs, abs_of_pos numeric_bounds.2.1]
    exact numeric_bounds.2.2.1
  obtain ⟨r, v, d, c, sel, hone⟩ := exists_stepOneComputation
    (σ := height ^ 2) (ζ := (1 / 2 : ℝ)) (le_refl 3)
    (ftaylorSeries ℝ (objective perturbation curvature) 0) zero_lt_one (sq_nonneg _)
    (by norm_num) (by norm_num) ht (fun _ => 1 / 2) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => ⟨zero_lt_one, le_rfl⟩)
  exact ⟨⟨r, v, d, c, sel⟩, hone⟩

/-- A genuine ordered check after the endpoint refresh to the exact derivative jet. -/
noncomputable def exactCheck : CheckData := Classical.choose exact_exists

/-- The endpoint check obeys every primitive ordered optimality-loop rule. -/
theorem exactCheck_spec :
    exactCheck.Valid (ftaylorSeries ℝ (objective perturbation curvature) 0) (height ^ 2) :=
  Classical.choose_spec exact_exists

/-- Fixed legal IDA and EDA settings with a large initial oracle allowance and permitted
parameter increase. -/
noncomputable def settings : Explicit.Settings 3 3 where
  stepCoefficient := 1 / 16
  stepCoefficient_pos := by norm_num
  initialCap := 2 * height
  initialCap_nonneg := by unfold height; positivity
  errorBound := 1
  errorBound_nonneg := zero_le_one
  errorCoefficient := fun _ => 1
  errorCoefficient_nonneg := fun _ _ _ => zero_le_one
  errorCoefficient_le := fun _ _ _ => le_rfl
  reduction := 1 / 2
  reduction_pos := by norm_num
  reduction_lt_one := by norm_num
  order_pos := by omega
  order_le := le_rfl
  zeta := 1 / 2
  zeta_pos := by norm_num
  zeta_le_one := by norm_num
  theta := 9 / 10
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  eta1 := 1 / 4
  eta2 := 3 / 4
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := height
  sigmaMin := height
  sigmaInitial := height
  eta1_pos := by norm_num
  eta1_le_eta2 := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by linarith [numeric_bounds.1]
  sigmaMin_pos := by linarith [numeric_bounds.1]
  sigmaMin_le_initial := le_rfl
  known_error_bound := rfl
  function_acceptance_margin := by norm_num
  function_success_margin := by norm_num

/-- The actual initial, short ghost, passing and endpoint optimality-check arrays. -/
noncomputable def check (k : ℕ) : CheckData :=
  if k = 0 then firstCheck else if k = 1 then shortData.check
  else if k ≤ 382 then passingCheck else exactCheck

/-- The reused initial ghost jet, subsequent passing jet, and final exact refreshed jet. -/
noncomputable def computedJet (k : ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  if k < 2 then ghostJet height curvature else if k ≤ 382 then jet curvature
  else ftaylorSeries ℝ (objective perturbation curvature) 0

/-- One permitted increase after the initial rejected trial, followed by unchanged
parameters. -/
noncomputable def parameter (k : ℕ) : ℝ := if k = 0 then height else height ^ 2
/-- The initial large candidate, the proved short ghost return, and unused zero
candidates. -/
noncomputable def trialStep (k : ℕ) : ℝ :=
  if k = 0 then 2 else if k = 1 then shortData.step else 0
/-- The genuine solved radii at the short ghost return and otherwise unused unit radii. -/
noncomputable def solvedRadius (k : ℕ) : Fin 3 → ℝ :=
  if k = 1 then shortData.solved else fun _ => 1
/-- Actual error requests remain unchanged at the first trial and are then halved at every
nontrial iteration. -/
noncomputable def accuracy (k : ℕ) : ℝ := 2 * height / 2 ^ (k - 1)

/-- Actual derivative, objective, check, candidate, ratio and update arrays for the finite
execution. -/
noncomputable def data : Explicit.ExecutionData ℝ 3 where
  jet := computedJet
  trials := {0}
  point := fun _ => 0
  reference := fun k => (check k).reference
  step := trialStep
  parameter := parameter
  ratio := fun k => (objective perturbation curvature 0 -
    objective perturbation curvature (trialStep k)) /
      TaylorModel.jetDecrement (computedJet k) 3 (trialStep k)
  accuracy := fun k _ => accuracy k
  startRadius := fun _ _ => 1
  checkedRadius := fun k => (check k).reduced
  solvedRadius := solvedRadius
  checkDirection := fun k => (check k).direction
  checkCount := fun k => (check k).count
  selected := fun k => (check k).selected
  functionStart := fun _ => objective perturbation curvature 0
  functionTrial := fun k => objective perturbation curvature (trialStep k)
  functionRequest := fun k => TaylorModel.jetDecrement (computedJet k) 3 (trialStep k) / 32

/-- Every completed check, including the endpoint, obeys the actual ordered Step1
computation. -/
theorem computation_one (k : ℕ) :
    StepOneComputation (data.jet k) 3 (data.parameter k) settings.zeta
      (fun _ => 1 / 2) (data.startRadius k) (data.checkedRadius k) (data.reference k)
      (data.checkDirection k) (data.checkCount k) (data.selected k) := by
  change (check k).Valid (computedJet k) (parameter k)
  by_cases h0 : k = 0
  · subst k
    simpa only [check, computedJet, parameter, reduceIte, Nat.zero_lt_succ] using firstCheck_spec.1
  · by_cases h1 : k = 1
    · subst k
      simpa only [check, computedJet, parameter, show ¬(1 : ℕ) = 0 by decide,
        reduceIte, Nat.reduceLT] using shortData_spec.1
    · by_cases hk : k ≤ 382
      · simpa only [check, h0, h1, hk, computedJet, parameter,
          show ¬k < 2 by omega, reduceIte] using passingCheck_spec.1
      · simpa only [check, h0, h1, hk, computedJet, parameter,
          show ¬k < 2 by omega, reduceIte] using exactCheck_spec

end InexactRegularization.PassingCubic
