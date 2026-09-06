import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

/-!
# A real-valued convex lower semicontinuous function on a Banach space is continuous

`ConvexOn.continuous_of_lowerSemicontinuous`: a function `f : E → ℝ` on a complete real normed
space that is convex and lower semicontinuous *and finite everywhere* is continuous, hence locally
Lipschitz.

The point is that finiteness does the work of a local upper bound.  The sublevel sets `{f ≤ n}` are
closed, by lower semicontinuity, and cover `E`, because `f` is real-valued; Baire's theorem gives
one of them a nonempty interior, so `f` is bounded above near some point, and a convex function
bounded above near one point is continuous everywhere — that last implication is Mathlib's
`ConvexOn.continuousOn_tfae`.

Completeness is what makes the space a Baire space and is the only role it plays; the statement
holds verbatim over any barrelled space.  Without finiteness the conclusion fails at once: an
extended-real convex lower semicontinuous function jumps to `+∞` off its domain.

This is why the hypothesis "`j : V → ℝ` is convex and lower semicontinuous", standard in the theory
of elliptic variational inequalities, silently provides the continuity of `j` that convergence
proofs for their numerical approximation need; see [han2009theoretical], Chapter 11.
-/

open Filter Set Topology

/-- **A convex, lower semicontinuous, real-valued function on a Banach space is continuous.**
Lower semicontinuity makes the sublevel sets `{f ≤ n}` closed and finiteness makes them cover the
space, so Baire's theorem bounds `f` above on a ball; a convex function bounded above on some ball
is continuous. -/
theorem ConvexOn.continuous_of_lowerSemicontinuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : E → ℝ} (hcv : ConvexOn ℝ univ f)
    (hlsc : LowerSemicontinuous f) : Continuous f := by
  have hclosed : ∀ n : ℕ, IsClosed (f ⁻¹' Iic (n : ℝ)) := fun n => hlsc.isClosed_preimage _
  have hcover : ⋃ n : ℕ, f ⁻¹' Iic (n : ℝ) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (f x)
    exact ⟨n, hn⟩
  obtain ⟨n, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have hbdd : (𝓝 x₀).IsBoundedUnder (· ≤ ·) f :=
    ⟨(n : ℝ), eventually_map.2 (mem_interior_iff_mem_nhds.1 hx₀)⟩
  have htfae : (∃ y ∈ (univ : Set E), (𝓝 y).IsBoundedUnder (· ≤ ·) f) ↔ ContinuousOn f univ :=
    (ConvexOn.continuousOn_tfae isOpen_univ ⟨x₀, mem_univ _⟩ hcv).out 4 2
  rw [← continuousOn_univ]
  exact htfae.1 ⟨x₀, mem_univ _, hbdd⟩
