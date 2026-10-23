import Numlib.Optimization.Regularization.HighOrder.OuterReturn
import Numlib.Optimization.Regularization.HighOrder.ObstructionCounterexample
import Numlib.Optimization.Regularization.ZeroReturnCounterexample

/-!
# A literal smooth outer exit without a criticality certificate

The quadratic `(x-2)^2/2`, with model parameter one, allows the large step four
to return the initial model value. This satisfies every literal outer test and
causes immediate termination at zero, where first-order criticality fails at
every positive radius. The return cannot satisfy any positive-global-gap solve.
-/

noncomputable section

namespace HighOrderRegularization.ZeroReturn
open InexactTrustRegion RegularizationZeroReturn
/-- Legal fixed settings for the first-order immediate-exit execution. -/
abbrev settings := ObstructionCounterexample.settings

/-- The computed first-order direction passes relative accuracy and fails termination. -/
theorem initial_check : OptimalityCheck objective settings.zeta (fun _ => 1 / 2)
    (fun _ => 1) 0 (fun _ => 1) (some (0 : Fin 1)) := by
  have ho (a : Fin 1) : modelOrder a = 1 := by fin_cases a; rfl
  constructor
  · intro a _
    norm_num
  · intro a _
    rw [ho, criticality_formula (by norm_num), decrement_formula]
    norm_num [settings, ObstructionCounterexample.settings]
  · intro h
    cases h
  · intro a _
    rw [ho, decrement_formula]
    norm_num [settings, ObstructionCounterexample.settings]
  · intro a _ b hb
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    exact (not_lt_of_ge (bot_le : (0 : Fin 1) ≤ b) hb).elim

/-- The step four satisfies the literal outer contract through its large-step bypass. -/
theorem returned : OuterStepReturn (p := 1) objective settings.theta settings.zeta
    (fun _ : Fin 1 => 1 / 2) 0 4 1 (fun _ => 1) (fun _ => 1) (fun _ => 0) := by
  refine ⟨zero_improvement.le, fun _ => ⟨by norm_num, le_rfl⟩,
    Or.inl ⟨by norm_num, rfl⟩⟩

/-- The complete immediate-exit execution with its actual initial Taylor check. -/
theorem actual_exit : OuterZeroExit objective settings (fun _ => 1 / 2) 0 4
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 0) 0 := by
  exact ⟨fun _ => by norm_num, fun _ => ⟨by norm_num, le_rfl⟩, initial_check,
    returned, zero_improvement⟩

/-- No point produced by this actual exit is an approximate first-order minimizer,
at any positive radius. -/
theorem no_produced_certificate {δ : ℝ} (hd : 0 < δ) : ¬∃ y : ℝ,
    actual_exit.producedPoint y ∧
      TaylorModel.criticality objective 1 y δ ≤ (1 / 2 : ℝ) * δ := by
  rintro ⟨y, hy, hcrit⟩
  change y = 0 at hy
  subst y
  exact not_critical hd hcrit
end HighOrderRegularization.ZeroReturn
