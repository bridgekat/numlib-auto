import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Atkinson–Han §2.1: operators

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.1: operators, their domain, range and null set,
injectivity and surjectivity, continuity and boundedness.

Definition 2.1.1 is `Function.Injective`, `Function.Surjective` and `Function.Bijective`; the
domain, range and null set of an operator are `Set.univ`, `Set.range` and `T ⁻¹' {0}`, or for a
linear map `LinearMap.range` and `LinearMap.ker`. None of these is restated.

## Main definitions

* `IsBoundedOperator` — Definition 2.1.6, the book's boundedness of a not necessarily linear
  operator: *bounded sets have bounded images*, not "the operator norm is finite". The distinction
  matters, because the two differ for a nonlinear operator and the point of Theorem 2.2.4 is that
  for a linear operator they agree.

## Main results

* `isBoundedOperator_iff_image_bounded` — the two readings the book gives of Definition 2.1.6.
* `example_2_1_7` — the half of Example 2.1.7 that needs no `C¹[0, 1]`: differentiation is
  *unbounded* for the sup norm on `C[0, 1]`.

The bridge to the estimate `‖T v‖ ≤ γ ‖v‖` for a *linear* operator is Proposition 2.2.3, and lives
in §2.2 with the rest of that discussion.

## Not formalized here

Examples 2.1.2 and 2.1.3, the identity operator and a matrix acting on `ℝⁿ`, illustrate
Definition 2.1.1 and carry no statement the rest of the book uses. Examples 2.1.4 and 2.1.5, and
the *bounded* half of Example 2.1.7, concern the differentiation operator read on `C¹[0, 1]` with
the norm `‖v‖_∞ + ‖v'‖_∞`; Mathlib does not have `C¹[0, 1]` as a normed space, so they are not
stated. The *unbounded* half of Example 2.1.7 needs no such space and is `example_2_1_7`.
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

/-- **Example 2.1.7**, the half that needs no `C¹[0, 1]`: *differentiation is not a bounded
operator for the sup norm on `C[0, 1]`*. There is no `γ` with `‖v'‖_∞ ≤ γ ‖v‖_∞` for every
continuously differentiable `v`, and the book's witnesses show it: `v_n (x) = sin (n x)` has
`‖v_n‖_∞ ≤ 1` while `v_n' (0) = n`.

The statement is the negation in witness form — for every `γ` such a `v` exists — because the
bounded reading of the operator would need `C¹[0, 1]` as a normed space, which Mathlib does not
have; the other half of the Example, that `d/dx` *is* bounded for `‖v‖_∞ + ‖v'‖_∞`, waits on that
space. -/
theorem example_2_1_7 (γ : ℝ) :
    ∃ v v' : ℝ → ℝ, (∀ x, HasDerivAt v (v' x) x) ∧ Continuous v' ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |v x| ≤ 1) ∧ ∃ x ∈ Set.Icc (0 : ℝ) 1, γ < |v' x| := by
  set n : ℝ := max γ 0 + 1 with hn
  have hn1 : γ < n := by simp [hn]; linarith [le_max_left γ 0]
  refine ⟨fun x => Real.sin (n * x), fun x => n * Real.cos (n * x), fun x => ?_,
    by fun_prop, fun x _ => Real.abs_sin_le_one _, 0, by norm_num, ?_⟩
  · have h := (Real.hasDerivAt_sin (n * x)).comp x ((hasDerivAt_id x).const_mul n)
    simpa [Function.comp_def, mul_comm] using h
  · have hn0 : (0 : ℝ) < n := by positivity
    simp only [mul_zero, Real.cos_zero, mul_one]
    rwa [abs_of_pos hn0]

end AtkinsonHan.Chapter02
