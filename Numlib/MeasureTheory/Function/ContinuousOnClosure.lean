/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions` (the `L^∞` membership)
and `Mathlib.MeasureTheory.Measure.OpenPos` (the almost-everywhere bound on an open set).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Functions continuous on the closure of a set

Two facts about a function continuous on the closure `closure s` of a set `s`, used for the
coefficients and data of boundary value problems on a bounded open set `Ω` (functions continuous
on `Ω̄`):

* it is essentially bounded on `s` when `closure s` is compact — in particular on a bounded set
  of a proper space (`ContinuousOn.memLp_top_restrict_of_isCompact_closure`,
  `ContinuousOn.memLp_top_restrict_of_isBounded`);
* a bound `|g| ≤ C` holding almost everywhere on an open `s`, for a measure positive on open
  sets, holds everywhere on `closure s` (`ContinuousOn.abs_le_on_closure_of_ae_abs_le`), and
  two functions continuous on `s` and ordered almost everywhere on it are ordered everywhere on
  it (`le_on_of_ae_le`).
-/

open MeasureTheory Set
open scoped ENNReal

variable {X F : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X}

section MemLpTop

variable [NormedAddCommGroup F] [SecondCountableTopologyEither X F] {f : X → F} {s : Set X}

/-- A function continuous on the closure of a set with compact closure is essentially bounded on
the set. -/
theorem ContinuousOn.memLp_top_restrict_of_isCompact_closure (hs : IsCompact (closure s))
    (hsm : MeasurableSet s) (hf : ContinuousOn f (closure s)) : MemLp f ⊤ (μ.restrict s) := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf
  refine memLp_top_of_bound ((hf.mono subset_closure).aestronglyMeasurable hsm) C ?_
  filter_upwards [ae_restrict_mem hsm] with x hx
  exact hC x (subset_closure hx)

/-- A function continuous on the closure of a bounded subset of a proper space is essentially
bounded on the subset: the function of an element of `L^∞(s)`. -/
theorem ContinuousOn.memLp_top_restrict_of_isBounded {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {f : X → F}
    [SecondCountableTopologyEither X F] {s : Set X} (hs : Bornology.IsBounded s)
    (hsm : MeasurableSet s) (hf : ContinuousOn f (closure s)) : MemLp f ⊤ (μ.restrict s) :=
  hf.memLp_top_restrict_of_isCompact_closure hs.isCompact_closure hsm

end MemLpTop

omit [OpensMeasurableSpace X] in
/-- **A bound almost everywhere on an open set passes to the closure by continuity**: if `g` is
continuous on `closure s` and `|g| ≤ C` almost everywhere on the open set `s` (for a measure
positive on open sets), then `|g| ≤ C` on `closure s`. -/
theorem ContinuousOn.abs_le_on_closure_of_ae_abs_le [μ.IsOpenPosMeasure] {s : Set X}
    (hs : IsOpen s) {g : X → ℝ} (hg : ContinuousOn g (closure s)) {C : ℝ}
    (hb : ∀ᵐ x ∂(μ.restrict s), |g x| ≤ C) : ∀ x ∈ closure s, |g x| ≤ C := by
  have hc : ContinuousOn (fun x ↦ max (|g x| - C) 0) (closure s) :=
    ContinuousOn.sup ((continuous_abs.comp_continuousOn hg).sub continuousOn_const)
      continuousOn_const
  have h1 : EqOn (fun x ↦ max (|g x| - C) 0) (fun _ ↦ (0 : ℝ)) s := by
    refine Measure.eqOn_open_of_ae_eq (μ := μ) ?_ hs (hc.mono subset_closure) continuousOn_const
    filter_upwards [hb] with x hx
    simp [max_eq_right (sub_nonpos.2 hx)]
  intro x hx
  have h2 := h1.of_subset_closure hc continuousOn_const subset_closure le_rfl hx
  exact sub_nonpos.1 (max_eq_right_iff.1 h2)

omit [OpensMeasurableSpace X] in
/-- Two functions continuous on an open set that are ordered almost everywhere on it, for a
measure positive on open sets, are ordered everywhere on it. -/
theorem le_on_of_ae_le [μ.IsOpenPosMeasure] {s : Set X} (hs : IsOpen s) {g h : X → ℝ}
    (hle : g ≤ᵐ[μ.restrict s] h) (hg : ContinuousOn g s) (hh : ContinuousOn h s) :
    ∀ x ∈ s, g x ≤ h x := by
  have hmin : (fun x ↦ min (g x) (h x)) =ᵐ[μ.restrict s] g := hle.mono fun x hx ↦ min_eq_left hx
  have heq := Measure.eqOn_open_of_ae_eq hmin hs (ContinuousOn.inf hg hh) hg
  intro x hx
  exact min_eq_left_iff.1 (heq hx)
