import Numlib.Analysis.Sobolev.Space
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

Theorem 7.2.3, that `W^{k,p}(Ω)` is a Banach space, is here too: `Sobolev ℝ k p Ω volume` is the
same space as a normed type, and `theorem_7_2_3` is its completeness. The two readings agree by
`definition_7_2_2_iff_exists`, and the norm of the type is `sobolevNorm` by `Sobolev.norm_eq`.

The rest of the section is not formalized. Corollary 7.2.4, that `H^k(Ω)` is a Hilbert space, needs
the multi-index indexing of the norm: the operator norm used on the derivative tensors is not an
inner-product norm, so completeness alone does not give it — see the implementation notes of
`Numlib/Analysis/Sobolev/Space.lean`. Definition 7.2.9, `W_0^{k,p}(Ω)`, is here as well, as the
closure of the image of `C_0^∞(Ω)` in that Banach space; what the trace theorems of §7.3 would add
is its reading as a space of boundary conditions, not the definition. Definition 7.2.1 (boundary
regularity classes), Definitions 7.2.11 and 7.2.12 (the real-order `W_0^{s,p}(Ω)` and the
negative-order duals), Definition 7.2.10 (the Sobolev–Slobodeckij spaces) and Definition 7.2.13
(`W^{s,p}(∂Ω)`, which needs surface measure on a Lipschitz boundary) are all open, as are Examples
7.2.5 to 7.2.8.
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

/-- Definition 7.2.2 read on the *type* `Sobolev ℝ k p Ω volume`, which is `W^{k,p}(Ω)` carrying
the norm `‖·‖_{k,p,Ω}`: a function `v` belongs to `W^{k,p}(Ω)` exactly when it agrees, off a null
subset of `Ω`, with the function underlying an element of that type. The element is then unique,
by `Sobolev.ext_of_fn_ae_eq`. -/
theorem definition_7_2_2_iff_exists (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2 k p Ω v ↔ ∃ u : Sobolev ℝ k p Ω volume,
      Sobolev.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))] v :=
  ⟨fun h ↦ h.exists_sobolev, fun ⟨_, hu⟩ ↦ (Sobolev.memSobolev _).congr_ae hu⟩

/-- **Theorem 7.2.3**: the Sobolev space `W^{k,p}(Ω)` is a Banach space.

`Sobolev ℝ k p Ω volume` is `W^{k,p}(Ω)` as a normed space; its elements are the functions of
Definition 7.2.2 by `definition_7_2_2_iff_exists`, and its norm is the `‖·‖_{k,p,Ω}` of that
definition by `Sobolev.norm_eq`. The hypothesis `p ∈ [1, ∞]` of the book is the instance
`Fact (1 ≤ p)`, which is how Mathlib carries it for the `L^p` spaces. -/
theorem theorem_7_2_3 (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : CompleteSpace (Sobolev ℝ k p Ω volume) :=
  inferInstance

/-- **Definition 7.2.9**: `W_0^{k,p}(Ω)` is the closure of `C_0^∞(Ω)` in `W^{k,p}(Ω)`; when
`p = 2` one writes `H_0^k(Ω) ≡ W_0^{k,2}(Ω)`.

`SobolevZero ℝ k p Ω volume` is the closure, inside the Banach space of Theorem 7.2.3, of the
submodule of elements whose function agrees off a null set with a test function on `Ω`; every test
function does give such an element, by `TestFunction.exists_mem_testFunctions`. The book's reading
of the space — the functions whose derivatives of order at most `k - 1` vanish on `∂Ω` — is made
precise only by the trace theorems of §7.3, which are not formalized. -/
noncomputable def definition_7_2_9 (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (Sobolev ℝ k p Ω volume) :=
  SobolevZero ℝ k p Ω volume

end AtkinsonHan.Chapter07
