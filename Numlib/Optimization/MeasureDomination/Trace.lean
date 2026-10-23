import Numlib.Optimization.MeasureDomination.TrustRegionBudget
import Numlib.Optimization.MeasureDomination.Superlinear

/-!
# Domination only at actual visited states

Restricting the state domain to visited points preserves all genuine objective
values, measures, rejected points and counters. One separate state realizes the
specified lower bound for the restricted problem; it asserts no minimizer or
root in the original ambient space.
-/

namespace MeasureDomination
open Set Filter Topology
variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ}
  {x : ℕ → E} {S : Set ℕ}

/-- Domination and lower bounds are needed only at actual visited points. -/
structure AlongDomination (f ψ : E → ℝ) (fstar μ κ : ℝ) (x : ℕ → E) : Prop where
  gap_nonneg : ∀ k, 0 ≤ gap f fstar (x k)
  measure_nonneg : ∀ k, 0 ≤ ψ (x k)
  level_ge_one : 1 ≤ μ
  coefficient_pos : 0 < κ
  domination : ∀ k, gap f fstar (x k) ≤ κ * ψ (x k) ^ μ

/-- Actual visited points, together with one distinct lower-bound state. -/
abbrev TraceState (x : ℕ → E) := Option {z : E // z ∈ Set.range x}

/-- The objective is unchanged at every visited state; the separate state has
only the prescribed lower-bound value. -/
def traceObjective (f : E → ℝ) (fstar : ℝ) (x : ℕ → E) : TraceState x → ℝ
  | none => fstar
  | some z => f z.1

/-- Actual measures are unchanged, and the separate lower-bound state has zero measure. -/
def traceMeasure (ψ : E → ℝ) (x : ℕ → E) : TraceState x → ℝ
  | none => 0
  | some z => ψ z.1

/-- Every actual iterate is its original visited point, never the separate state. -/
def traceIterate (x : ℕ → E) (k : ℕ) : TraceState x := some ⟨x k, ⟨k, rfl⟩⟩

/-- The restricted objective equals the actual objective at every actual iterate. -/
@[simp] theorem traceObjective_iterate (k : ℕ) :
    traceObjective f fstar x (traceIterate x k) = f (x k) := rfl

/-- The restricted measure equals the actual measure at every actual iterate. -/
@[simp] theorem traceMeasure_iterate (k : ℕ) :
    traceMeasure ψ x (traceIterate x k) = ψ (x k) := rfl

/-- The restricted gap is the actual original objective gap. -/
@[simp] theorem trace_gap (k : ℕ) :
    gap (traceObjective f fstar x) fstar (traceIterate x k) = gap f fstar (x k) := rfl

/-- The historical minimum is exactly the original actual historical minimum. -/
@[simp] theorem trace_pastMeasure (k : ℕ) :
    pastMeasure (traceMeasure ψ x) (traceIterate x) k = pastMeasure ψ x k := rfl

/-- Restriction and one separate lower-bound state turn along-trace domination
into global domination on the restricted state space. -/
theorem AlongDomination.dominated (hd : AlongDomination f ψ fstar μ κψ x) :
    Dominated (traceObjective f fstar x) (traceMeasure ψ x) fstar μ κψ := by
  refine ⟨⟨⟨none, rfl⟩, ?_⟩, ?_, hd.level_ge_one, hd.coefficient_pos, ?_⟩
  · rintro _ ⟨z, rfl⟩
    rcases z with _ | ⟨z, k, rfl⟩
    · exact le_rfl
    · exact sub_nonneg.mp (hd.gap_nonneg k)
  · rintro (_ | ⟨z, k, rfl⟩)
    · exact le_rfl
    · exact hd.measure_nonneg k
  · rintro (_ | ⟨z, k, rfl⟩)
    · simp only [traceObjective, traceMeasure, sub_self]
      exact mul_nonneg hd.coefficient_pos.le (Real.rpow_nonneg (le_refl 0) μ)
    · exact hd.domination k

/-- Equal actual points have equal restricted states, independently of membership proofs. -/
theorem traceIterate_eq {i j : ℕ} (h : x i = x j) : traceIterate x i = traceIterate x j := by
  apply congrArg some
  exact Subtype.ext h

/-- All primitive adaptive-regularization execution rules survive exact state restriction. -/
theorem ARRun.trace_run (hr : ARRun f ψ x S ν κν κR κA) :
    ARRun (traceObjective f fstar x) (traceMeasure ψ x) (traceIterate x)
      S ν κν κR κA :=
  ⟨hr.exponent_ge_one, hr.coefficient_pos, hr.infinite_success,
    fun k hk => traceIterate_eq (hr.rejected k hk), hr.decrease,
    hr.density_factor, hr.density_additive, hr.density⟩

/-- Historical minima, accepted decreases and the actual zero-stop rule all
survive exact trust-region state restriction. -/
theorem TRRun.trace_run (hr : TRRun f ψ x S ν κν κR κA) :
    TRRun (traceObjective f fstar x) (traceMeasure ψ x) (traceIterate x)
      S ν κν κR κA :=
  ⟨hr.exponent_ge_one, hr.coefficient_pos, hr.infinite_success,
    fun k hk => traceIterate_eq (hr.rejected k hk), hr.decrease,
    hr.density_factor, hr.density_additive, hr.density,
    fun k hk => traceIterate_eq (hr.stopped_point k hk)⟩

end MeasureDomination
