import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Atkinson–Han §2.1: operators

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.1: operators, their domain, range and null set,
injectivity and surjectivity, continuity and boundedness.

Definition 2.1.1 is `Function.Injective`, `Function.Surjective` and `Function.Bijective`; the
domain, range and null set of an operator are `Set.univ`, `Set.range` and `T ⁻¹' {0}`, or for a
linear map `LinearMap.range` and `LinearMap.ker`. None of these is restated.

## Main results

* `IsBoundedOperator` — Definition 2.1.6, the book's boundedness of a not necessarily linear
  operator: *bounded sets have bounded images*, not "the operator norm is finite". The distinction
  matters, because the two differ for a nonlinear operator and the point of Theorem 2.2.4 is that
  for a linear operator they agree.
* `isBoundedOperator_iff_image_bounded` — the two readings the book gives of Definition 2.1.6.

The bridge to the estimate `‖T v‖ ≤ γ ‖v‖` for a *linear* operator is Proposition 2.2.3, and lives
in §2.2 with the rest of that discussion.

## Not formalized here

Examples 2.1.2–2.1.5 and 2.1.7 concern the differentiation operator on `C¹[0, 1]`; that space is
not in Mathlib as a normed space, and the examples carry no theorem the rest of the book uses.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/

open Bornology Metric

namespace AtkinsonHan.Chapter02

variable {V W : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]

/-- **Definition 2.1.6.** An operator `T : V → W` between normed spaces is *bounded* when it maps
bounded sets to bounded sets: for every `r > 0` there is an `R` with `‖T v‖ ≤ R` whenever
`‖v‖ ≤ r`. This is the book's notion, and it is not "the operator norm of `T` is finite": the two
agree for linear operators (Theorem 2.2.4) and differ in general. -/
def IsBoundedOperator (T : V → W) : Prop :=
  ∀ r > 0, ∃ R : ℝ, ∀ v : V, ‖v‖ ≤ r → ‖T v‖ ≤ R

/-- The two readings the book gives of Definition 2.1.6 agree: `T` is bounded on every ball if and
only if it maps every bounded set to a bounded set. -/
theorem isBoundedOperator_iff_image_bounded (T : V → W) :
    IsBoundedOperator T ↔ ∀ B : Set V, IsBounded B → IsBounded (T '' B) := by
  constructor
  · intro hT B hB
    obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hB
    obtain ⟨R, hR⟩ := hT (max r 1) (lt_of_lt_of_le zero_lt_one (le_max_right r 1))
    refine isBounded_iff_forall_norm_le.mpr ⟨R, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hR v ((hr v hv).trans (le_max_left r 1))
  · intro hT r _
    obtain ⟨R, hR⟩ :=
      isBounded_iff_forall_norm_le.mp (hT (closedBall 0 r) isBounded_closedBall)
    exact ⟨R, fun v hv => hR _ ⟨v, by simpa using hv, rfl⟩⟩

end AtkinsonHan.Chapter02
