import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Banach and Hilbert space conventions

Appendix A.4's completeness requirement is Mathlib's `CompleteSpace`. The ambient
`NormedSpace ℝ E` gives the Banach convention; `InnerProductSpace ℝ E` gives the Hilbert
convention. These are aliases of existing typeclasses, with no new space structures.
The `Lp` examples use their usual almost-everywhere equivalence classes.
-/

namespace CartisGouldToint.AppendixA.Section04

/-- The completeness convention shared by Banach and Hilbert spaces over the reals.
With an ambient real normed space this says precisely that the space is Banach;
with an ambient real inner product space it says precisely that it is Hilbert. -/
abbrev BanachHilbertSpaceConventions (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Prop := CompleteSpace E

/-- A Banach space is a complete real normed vector space. -/
abbrev BanachSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  CompleteSpace E

/-- A Hilbert space is a complete real inner product space. -/
abbrev HilbertSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Prop :=
  CompleteSpace E

/-- The norm associated to a Hilbert space makes it a Banach space. -/
theorem hilbertSpace_isBanachSpace (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [HilbertSpace E] : BanachSpace E := inferInstance

/-- The norm-induced metric is the distance between two vectors. -/
theorem dist_eq_norm_sub (E : Type*) [NormedAddCommGroup E] (x y : E) :
    dist x y = ‖x - y‖ := dist_eq_norm x y

/-- Lebesgue `Lp` is Banach for `1 ≤ p`, with no finiteness requirement on the measure. -/
theorem lp_isBanachSpace {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (p : ENNReal) [Fact (1 ≤ p)] :
    BanachSpace (MeasureTheory.Lp ℝ p μ) := inferInstance

/-- Lebesgue `L²` with the standard integral inner product is Hilbert. -/
theorem l2_isHilbertSpace {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) : HilbertSpace (MeasureTheory.Lp ℝ 2 μ) := inferInstance

/-- Square-summable real sequences with their standard inner product are Hilbert. -/
theorem ell2_isHilbertSpace : HilbertSpace (lp (fun _ : ℕ => ℝ) 2) := inferInstance

end CartisGouldToint.AppendixA.Section04
