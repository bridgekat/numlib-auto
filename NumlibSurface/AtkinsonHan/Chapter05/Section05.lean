import Numlib.Nonlinear.CompletelyContinuous

/-!
# Atkinson–Han §5.5: completely continuous vector fields

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §5.5.

The section is a summary: Brouwer's theorem (5.5.1), Schauder's theorem (5.5.4) and the properties
P1–P5 of the rotation of a completely continuous vector field are quoted there from Krasnoselskii
and Zeidler without proof, and Mathlib has neither Brouwer's theorem nor degree theory. Two items
are formalized, and they are the ones later chapters use.

## Main results

* `IsCompletelyContinuousOn` — Definition 5.5.3: a compact map that is in addition continuous. The
  first half is the backbone `IsCompactMap` (`Numlib/Nonlinear/CompletelyContinuous`); the two
  halves are separate because for a nonlinear map compactness does not imply continuity, unlike
  for a linear one, where the notion is Mathlib's `IsCompactOperator`.
* `proposition_5_5_5` — the Fréchet derivative of a completely continuous operator at an interior
  point is a compact linear operator, so the Fredholm alternative applies to `I - T'(v₀)`. This is
  what lets §12.7 linearize a nonlinear fixed point problem into a second-kind linear equation.

## Not formalized here

Theorem 5.5.1 (Brouwer), Example 5.5.2 (a Lipschitz self-map of the unit ball of a Hilbert space
without a fixed point), Theorem 5.5.4 (Schauder), and §5.5.1 in its entirety: the rotation of a
completely continuous vector field and its properties P1–P5.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/

namespace AtkinsonHan.Chapter05

/-- **Definition 5.5.3.** An operator `T` is **completely continuous** on `K` when it is a compact
map on `K` — the image of every bounded subset of `K` is relatively compact — and is continuous
on `K`. -/
def IsCompletelyContinuousOn {V W : Type*} [SeminormedAddCommGroup V] [TopologicalSpace W]
    (T : V → W) (K : Set V) : Prop :=
  IsCompactMap T K ∧ ContinuousOn T K

/-- **Proposition 5.5.5.** Let `T` be completely continuous on an open set `K` of a Banach space
and Fréchet differentiable at `v₀ ∈ K`. Then the derivative `T'(v₀)` is a compact linear operator,
and so the Fredholm alternative applies to `I - T'(v₀)`.

The backbone proves more: continuity of `T` is not used, only differentiability at `v₀` together
with compactness on bounded sets. -/
theorem proposition_5_5_5 {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {T : V → W} {K : Set V}
    (hT : IsCompletelyContinuousOn T K) (hK : IsOpen K) {v₀ : V} (hv₀ : v₀ ∈ K) {A : V →L[ℝ] W}
    (hA : HasFDerivAt T A v₀) : IsCompactOperator A :=
  hT.1.isCompactOperator_hasFDerivAt (hK.mem_nhds hv₀) hA

end AtkinsonHan.Chapter05
