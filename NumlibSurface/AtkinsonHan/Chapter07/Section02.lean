import Numlib.Analysis.Sobolev.Domain
import NumlibSurface.AtkinsonHan.Chapter07.Section01

/-!
# Atkinson–Han §7.2: Sobolev spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.2.

Definition 7.2.2, the Sobolev space `W^{k,p}(Ω)` of integer order, is here, built on the weak
derivative of §7.1: `definition_7_2_2 k p Ω v` says that `v ∈ L^p(Ω)` and that for every `|α| ≤ k`
the weak derivative `∂^α v` exists and lies in `L^p(Ω)`, and `definition_7_2_2_iff` reads that off
against `AtkinsonHan.Chapter07.definition_7_1_3`. The norm and seminorm of the definition are
`sobolevNorm` and `sobolevSeminorm`.

The rest of the section is not formalized. Theorem 7.2.3, that `W^{k,p}(Ω)` is a Banach space,
would need `W^{k,p}(Ω)` as a *type* with its norm, hence the closedness of the weak-derivative
relation under `L^p` limits, which is the one analytic ingredient the backbone does not have;
Corollary 7.2.4, that `H^k(Ω)` is a Hilbert space, needs on top of that the multi-index indexing of
the norm, since the operator norm used on the derivative tensors is not an inner-product norm.
Definition 7.2.1 (boundary regularity classes), Definitions 7.2.9, 7.2.11 and 7.2.12
(`W_0^{s,p}(Ω)` and the negative-order duals, which need the Banach structure and, for their
meaning, the trace of §7.3), Definition 7.2.10 (the Sobolev–Slobodeckij spaces) and Definition
7.2.13 (`W^{s,p}(∂Ω)`, which needs surface measure on a Lipschitz boundary) are all open, as are
Examples 7.2.5 to 7.2.8.
-/

open MeasureTheory TopologicalSpace

open scoped ENNReal

namespace AtkinsonHan.Chapter07

variable {d : ℕ}

/-- **Definition 7.2.2**: for `k ≥ 0` an integer and `p ∈ [1, ∞]`, the Sobolev space `W^{k,p}(Ω)`
is the set of `v ∈ L^p(Ω)` such that for each multi-index `α` with `|α| ≤ k` the weak derivative
`∂^α v` exists and lies in `L^p(Ω)`; when `p = 2` one writes `H^k(Ω) ≡ W^{k,2}(Ω)`.

The norm `‖v‖_{k,p,Ω}` of the definition is `sobolevNorm v k p Ω volume` and the seminorm
`|v|_{k,p,Ω}` is `sobolevSeminorm v k p Ω volume`. Both collect the derivatives of a given order
into a single tensor measured in its operator norm instead of summing over the multi-indices `α`
of that order, which is an equivalent but not identical norm; see the implementation notes of
`Numlib/Analysis/Sobolev/Domain.lean`. -/
def definition_7_2_2 (k : ℕ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  MemSobolev v k p Ω volume

/-- Definition 7.2.2 unfolded against the weak derivative of §7.1: `v ∈ W^{k,p}(Ω)` exactly when
`v ∈ L^p(Ω)` and, for every order `n ≤ k`, `v` has a weak derivative of order `n` on `Ω` lying in
`L^p(Ω)`. -/
theorem definition_7_2_2_iff (k : ℕ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2 k p Ω v ↔ MemLp v p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) ∧
      ∀ n ≤ k, ∃ w, definition_7_1_3 n v w Ω ∧
        MemLp w p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) := by
  simp only [definition_7_2_2, MemSobolev, definition_7_1_3, Nat.cast_le]

end AtkinsonHan.Chapter07
