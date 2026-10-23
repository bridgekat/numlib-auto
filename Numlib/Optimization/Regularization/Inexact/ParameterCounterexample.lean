import Numlib.Optimization.Regularization.Inexact.Parameter
import Numlib.Analysis.Calculus.TaylorModel.Scalar
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A guarded-accuracy counterexample to the printed parameter constant

A zero objective and a computed gradient of minus one thousand produce a
large exact model-minimizing step. The short-step accuracy check is skipped,
the true ratio is zero, and one legal update raises the parameter from 32 to 64.
The printed upper bound is 60. All actual oracle and update rules hold.
-/

namespace InexactRegularization.Counterexample
open Set TaylorModel

/-- The inexact derivative jet is the genuine jet of an auxiliary linear function. -/
noncomputable def data : FormalMultilinearSeries ℝ ℝ ℝ :=
  ftaylorSeries ℝ (fun t : ℝ => -1000 * t) 0

/-- Fixed oracle constants and the initial accuracy cap in the counterexample. -/
noncomputable def settings : OracleSettings 1 where
  stepCoefficient := 1
  stepCoefficient_pos := by norm_num
  initialCap := 1000
  initialCap_nonneg := by norm_num
  errorBound := 1
  errorBound_nonneg := by norm_num
  errorCoefficient := fun _ => 1
  errorCoefficient_nonneg := by intros; norm_num
  errorCoefficient_le := by intros; norm_num
  reduction := 1 / 2
  reduction_pos := by norm_num
  reduction_lt_one := by norm_num

/-- One failed trial doubles the regularization parameter. -/
def parameter (i : ℕ) : ℝ := if i = 0 then 32 else 64

/-- The computed first-order Taylor polynomial is exactly the incorrect linear model. -/
theorem ofJet_data (t : ℝ) : ofJet data 1 t = -1000 * t := by
  change TaylorModel.eval (fun z : ℝ => -1000 * z) 1 0 t = _
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  norm_num [Finset.sum_range_succ]
  ring

/-- The actual regularized computed model is the specified convex quadratic. -/
theorem model_data (σ t : ℝ) : model data 1 σ t = -1000 * t + σ / 2 * t ^ 2 := by
  unfold model ModelDecrease.penalized
  rw [ofJet_data, Real.norm_eq_abs, sq_abs]
  norm_num

/-- The full primitive guarded-accuracy trace takes a large trial, rejects it
using the actual zero objective, and performs the legal update 32→64. -/
theorem trace : ModelTrace (fun _ : ℝ => 0) 1 settings (fun _ => data) univ
    (fun _ => 0) (fun _ => 1) (fun _ => 125 / 4) (fun _ _ => 1000)
    parameter (fun _ => 0) (1 / 4) (1 / 2) (1 / 2) 2 3 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · norm_num
    · constructor
      · norm_num
      · norm_num [parameter]
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · intro i hi _
        have hi0 : i = 0 := by omega
        subst i
        norm_num [parameter]
      · intro i _ hi
        exact (hi (mem_univ i)).elim
    · intro a _ _
      norm_num [settings]
    · intro i _ _ a _ _
      rfl
    · intro i _ hi
      exact (hi (mem_univ i)).elim
    · intro i _ _ a ha hap
      have ha1 : a = 1 := by omega
      subst a
      simp only [settings, data, ftaylorSeries, one_mul]
      change ‖iteratedFDeriv ℝ 1 (fun t : ℝ => -1000 * t) 0 -
        iteratedFDeriv ℝ 1 (fun _ : ℝ => 0) 0‖ ≤ 1000
      simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      norm_num
    · intro i _ _ hs
      norm_num at hs
    · intro i hi _
      have hi0 : i = 0 := by omega
      subst i
      rw [model_data, model_data]
      norm_num [parameter]
    · intro i hi _
      have hi0 : i = 0 := by omega
      subst i
      rw [model_data, model_data]
      norm_num [parameter]
    · intro i _ _
      norm_num
    · intro i _ hi
      exact (hi (mem_univ i)).elim
  · intro i _ _
    simp [data, ftaylorSeries]
  · intro i _ _
    simp [ratio]

/-- The true objective satisfies every source Lipschitz derivative condition
with constant one, including order zero. -/
theorem smoothness : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
    ∀ j ≤ 1, ∀ x y : ℝ,
      ‖iteratedFDeriv ℝ j (fun _ : ℝ => (0 : ℝ)) x -
        iteratedFDeriv ℝ j (fun _ : ℝ => (0 : ℝ)) y‖ ≤ ‖x - y‖ := by
  refine ⟨contDiff_const, ?_⟩
  intro j _ x y
  simp

/-- The reference direction is an exact maximizer of the computed linear
Taylor decrement on the unit ball. -/
theorem reference_maximizes :
    ‖(1 : ℝ)‖ ≤ 1 ∧ ∀ t : ℝ, ‖t‖ ≤ 1 →
      jetDecrement data 1 t ≤ jetDecrement data 1 1 := by
  refine ⟨by norm_num, ?_⟩
  intro t ht
  rw [jetDecrement, jetDecrement, ofJet_data, ofJet_data, ofJet_data]
  have hle : t ≤ 1 := (le_abs_self t).trans (by simpa only [Real.norm_eq_abs] using ht)
  nlinarith

/-- The two exact Step1 tests select the reference direction with
`ζ=δ=1` and requested criticality accuracy `ε=1/2`. -/
theorem reference_tests :
    (1 : ℝ) / 4 < jetDecrement data 1 1 ∧
      (1 : ℝ) / 8 ≤ model data 1 (parameter 0) 0 - model data 1 (parameter 0) 1 := by
  rw [jetDecrement, ofJet_data, ofJet_data, model_data, model_data]
  norm_num [parameter]

/-- The large trial is a genuine global minimizer of the computed model. -/
theorem step_minimizes (t : ℝ) : model data 1 32 (125 / 4) ≤ model data 1 32 t := by
  rw [model_data, model_data]
  nlinarith [sq_nonneg (t - 125 / 4)]

/-- The printed coefficient omits the initial request cap and is violated
by the terminal parameter of this actual one-trial trace. -/
theorem printed_bound_violated :
    max (parameter 0)
      (3 * (2 * (1 : ℝ) + 4 * ((1 + 1 : ℕ).factorial : ℝ) *
        settings.stepCoefficient * settings.errorBound) / (1 - 1 / 2)) < parameter 1 := by
  norm_num [parameter, settings]

end InexactRegularization.Counterexample
