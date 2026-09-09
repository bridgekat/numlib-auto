import Numlib.Analysis.Sobolev.MultiIndex
import NumlibSurface.AtkinsonHan.Chapter07.Section01

/-!
# Atkinson–Han §7.2: Sobolev spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.2.

Definition 7.2.2, the Sobolev space `W^{k,p}(Ω)` of integer order, is here in the two readings of
§7.1. `definition_7_2_2 k p Ω v` is the bundled one: `v ∈ L^p(Ω)`, and for every order `n ≤ k` the
derivative of order `n`, one object for all the multi-indices of that length, exists and lies in
`L^p(Ω)`. `definition_7_2_2_multiIndex k p Ω v` is the book's: one `∂^α v ∈ L^p(Ω)` for each
multi-index `α` with `|α| ≤ k`. The bundled reading implies the multi-index one,
`definition_7_2_2_multiIndex_of_definition_7_2_2`; the converse holds mathematically but rests on
the symmetry of the derivatives of a `C^∞` test function in its arguments, which Mathlib does not
yet have past order two, so it is not proved here.

The two readings differ in their *norms*, and that is why both are kept. The norm of
Definition 7.2.2 sums the `L^p(Ω)` norms of the `∂^α` over the multi-indices `α` with `|α| ≤ k`;
`sobolevNorm`, the norm of `Sobolev ℝ k p Ω volume`, sums over the orders `n ≤ k` instead and
measures each derivative tensor in its operator norm. The two are equivalent, the derivative
tensors of a Sobolev function being symmetric — mathematically; that equivalence is not formalized
here, so the two clauses of `theorem_7_2_3` are proved separately and neither is derived from the
other. They are not equal, and only the first is induced by an inner product.
`definition_7_2_2_multiIndex_norm` records that the norm of
`SobolevMultiIndex ℝ (stdBasis d) k p Ω volume` is the displayed norm of Definition 7.2.2, and
`Sobolev.norm_eq` that the norm of `Sobolev ℝ k p Ω volume` is `sobolevNorm`.

Corollary 7.2.4 is here: `H^k(Ω) = W^{k,2}(Ω)` is a Hilbert space for the inner product
`(u,v)_k = ∫_Ω ∑_{|α| ≤ k} ∂^α u ∂^α v`, which is the inner product that
`SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume` carries as a submodule of an `ℓ²` product of
`L²(Ω)` spaces. Definition 7.2.9, `W_0^{k,p}(Ω)`, is here as the closure of the image of
`C_0^∞(Ω)` in the Banach space of Theorem 7.2.3; what the trace theorems of §7.3 would add is its
reading as a space of boundary conditions, not the definition.

The rest of the section is not formalized. Definition 7.2.1 (boundary regularity classes),
Definitions 7.2.11 and 7.2.12 (the real-order `W_0^{s,p}(Ω)` and the negative-order duals),
Definition 7.2.10 (the Sobolev–Slobodeckij spaces) and Definition 7.2.13 (`W^{s,p}(∂Ω)`, which
needs surface measure on a Lipschitz boundary) are all open, as are Examples 7.2.5 to 7.2.8.
-/

open MeasureTheory Module TopologicalSpace

open scoped ENNReal

namespace AtkinsonHan.Chapter07

variable {d : ℕ}

/-- **Definition 7.2.2** in the *bundled* reading over `definition_7_1_3`, which is not proved
equal to the book's set: for `k ≥ 0` an integer and `p ∈ [1, ∞]`, the Sobolev space `W^{k,p}(Ω)`
is the set of `v ∈ L^p(Ω)` such that for each multi-index `α` with `|α| ≤ k` the weak derivative
`∂^α v` exists and lies in `L^p(Ω)`; when `p = 2` one writes `H^k(Ω) ≡ W^{k,2}(Ω)`.

All the multi-indices of a given length are carried here by one derivative tensor.
`definition_7_2_2_multiIndex` is the book's reading, one `α` at a time, and is the one to prefer
when the two must be told apart: this one implies it, and the converse, though true, is not
available (see `definition_7_2_2_multiIndex_of_definition_7_2_2`), so as a predicate this one may a
priori be strictly stronger. The norm `‖v‖_{k,p,Ω}` and seminorm `|v|_{k,p,Ω}` attached to this
reading are `sobolevNorm v k p Ω volume` and `sobolevSeminorm v k p Ω volume`; they sum over the
orders `n ≤ k` rather than over the multi-indices, which is an equivalent but not identical norm.
`definition_7_2_2_multiIndex_norm` carries the book's own norm; the *seminorm* `|v|_{k,p,Ω}` has no
multi-index counterpart anywhere yet, `sobolevSeminorm` being the top-order tensor in its operator
norm and not `[∑_{|α| = k} ‖∂^α v‖_{L^p(Ω)}^p]^{1/p}`. -/
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
the norm `sobolevNorm`: a function `v` belongs to `W^{k,p}(Ω)` exactly when it agrees, off a null
subset of `Ω`, with the function underlying an element of that type. The element is then unique,
by `Sobolev.ext_of_fn_ae_eq`. -/
theorem definition_7_2_2_iff_exists (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2 k p Ω v ↔ ∃ u : Sobolev ℝ k p Ω volume,
      Sobolev.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))] v :=
  ⟨fun h ↦ h.exists_sobolev, fun ⟨_, hu⟩ ↦ (Sobolev.memSobolev _).congr_ae hu⟩

/-- **Definition 7.2.2**, in the book's own indexing: `v ∈ W^{k,p}(Ω)` when `v ∈ L^p(Ω)` and, for
each multi-index `α` with `|α| ≤ k`, the weak derivative `∂^α v` exists and lies in `L^p(Ω)`, one
function for each `α`. This is what the norm of the definition sums over, so it is the reading on
which Theorem 7.2.3 and Corollary 7.2.4 are stated with the book's own norm; `definition_7_2_2` is
the bundled reading. -/
def definition_7_2_2_multiIndex (k : ℕ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  MemSobolevMultiIndex (stdBasis d) v k p Ω volume

/-- Definition 7.2.2 in the book's indexing, unfolded against the multi-index weak derivative of
§7.1. -/
theorem definition_7_2_2_multiIndex_iff (k : ℕ) (p : ℝ≥0∞)
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2_multiIndex k p Ω v ↔
      MemLp v p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) ∧
        ∀ α : Fin d → ℕ, ∑ i, α i ≤ k → ∃ w, definition_7_1_3_multiIndex α v w Ω ∧
          MemLp w p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) :=
  Iff.rfl

/-- The bundled reading of Definition 7.2.2 gives the book's: the `∂^α v` are the derivative tensor
of order `|α|` evaluated at the tuple of directions naming `α`.

The converse is true but is not proved here. It builds the tensor of order `n` from its values on
the tuples of coordinate directions, and the value on a tuple that is not in increasing order is
`∂^α` of the reordered tuple, so it needs the symmetry of `iteratedFDeriv ℝ n φ x` under
permutations of its arguments for a `C^∞` test function `φ`; Mathlib has that symmetry only for
`n = 2` and for analytic functions, and a test function is not analytic. -/
theorem definition_7_2_2_multiIndex_of_definition_7_2_2 {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : definition_7_2_2 k p Ω v) : definition_7_2_2_multiIndex k p Ω v :=
  h.memSobolevMultiIndex

/-- Definition 7.2.2 in the book's indexing, read on the *type*
`SobolevMultiIndex ℝ (stdBasis d) k p Ω volume`, which is `W^{k,p}(Ω)` carrying the norm
`‖·‖_{k,p,Ω}` of the definition: a function `v` belongs to `W^{k,p}(Ω)` exactly when it agrees, off
a null subset of `Ω`, with the function underlying an element of that type. The element is then
unique, by `SobolevMultiIndex.ext_of_fn_ae_eq`. -/
theorem definition_7_2_2_multiIndex_iff_exists (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2_multiIndex k p Ω v ↔
      ∃ u : SobolevMultiIndex ℝ (stdBasis d) k p Ω volume,
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))] v :=
  ⟨fun h ↦ h.exists_sobolevMultiIndex,
    fun ⟨_, hu⟩ ↦ (SobolevMultiIndex.memSobolevMultiIndex _).congr_ae hu⟩

/-- **The norm of Definition 7.2.2**, `‖v‖_{k,p,Ω} = [∑_{|α| ≤ k} ‖∂^α v‖_{L^p(Ω)}^p]^{1/p}` for
`1 ≤ p < ∞`, is the norm of the type `SobolevMultiIndex ℝ (stdBasis d) k p Ω volume`. The case
`p = ∞` of the definition, `max_{|α| ≤ k} ‖∂^α v‖_{L^∞(Ω)}`, is
`SobolevMultiIndex.norm_eq_ciSup`. -/
theorem definition_7_2_2_multiIndex_norm (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (u : SobolevMultiIndex ℝ (stdBasis d) k p Ω volume) :
    ‖u‖ = (∑ α : MultiIndexLE (Fin d) k, ‖SobolevMultiIndex.weakDeriv u α‖ ^ p.toReal)
      ^ (1 / p.toReal) :=
  SobolevMultiIndex.norm_eq_sum hp u

/-- **Theorem 7.2.3**: the Sobolev space `W^{k,p}(Ω)` is a Banach space.

The two clauses are the two readings of the norm. `SobolevMultiIndex ℝ (stdBasis d) k p Ω volume`
is `W^{k,p}(Ω)` with the norm the definition displays, by `definition_7_2_2_multiIndex_norm`, and
its elements are the functions of `definition_7_2_2_multiIndex` by
`definition_7_2_2_multiIndex_iff_exists`. `Sobolev ℝ k p Ω volume` is `W^{k,p}(Ω)` with
`sobolevNorm`, by `Sobolev.norm_eq`, which sums over the orders `n ≤ k` instead of over the
multi-indices; its elements are the functions of `definition_7_2_2` by
`definition_7_2_2_iff_exists`. The two norms are equivalent mathematically, but that equivalence is
not formalized — the two clauses are about two unrelated types here, and neither is derived from
the other. Only the first is the book's own norm, and only the first is an inner-product norm at
`p = 2`, which is what Corollary 7.2.4 needs. The hypothesis `p ∈ [1, ∞]` of the book is the
instance `Fact (1 ≤ p)`, which is how Mathlib carries it for the `L^p` spaces. -/
theorem theorem_7_2_3 (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (SobolevMultiIndex ℝ (stdBasis d) k p Ω volume) ∧
      CompleteSpace (Sobolev ℝ k p Ω volume) :=
  ⟨inferInstance, inferInstance⟩

/-- **Corollary 7.2.4**: the Sobolev space `H^k(Ω)` is a Hilbert space with the inner product
`(u, v)_k = ∫_Ω ∑_{|α| ≤ k} ∂^α u(x) ∂^α v(x) dx`.

`H^k(Ω) ≡ W^{k,2}(Ω)` is `SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume`, the space of
Definition 7.2.2 in the book's own indexing. Mathlib bundles no `HilbertSpace`: a Hilbert space is
`CompleteSpace` beside `InnerProductSpace ℝ`, and the three clauses below are that pair spelt out.
The first is the book's inner product — the one the type already carries, being a submodule of an
`ℓ²` product of `L²(Ω)` spaces. The second says the norm of the space is the one that inner product
induces, so that `‖u‖² = ∫_Ω ∑_{|α| ≤ k} |∂^α u|²`, which is `‖u‖_{k,Ω}²`; it is also
`definition_7_2_2_multiIndex_norm` at `p = 2`. The third is the completeness of Theorem 7.2.3.

Completeness alone does not give the corollary. On `Sobolev ℝ k 2 Ω volume`, the same space with
the equivalent norm `sobolevNorm`, no inner product induces the norm once `k ≥ 2` and `d ≥ 2`: that
norm measures the derivative tensor of order `n` by its operator norm, and for `n ≥ 2` and `d ≥ 2`
the operator norm on `ℝ^d [×n]→L[ℝ] ℝ` is a spectral norm and fails the parallelogram law. (For
`k ≤ 1`, or for `d ≤ 1`, the tensors in sight are vectors and linear functionals, whose operator
norm is Euclidean, so that norm is an inner-product norm too — the obstruction is genuinely about
derivatives of order two and higher in two or more variables.) The indexing by multi-indices is
what makes the corollary true for every `k` and `d`. -/
theorem corollary_7_2_4 (k : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin d))) :
    (∀ u v : SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume,
        inner ℝ u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin d))),
          ∑ α : MultiIndexLE (Fin d) k,
            SobolevMultiIndex.weakDeriv u α x * SobolevMultiIndex.weakDeriv v α x) ∧
      (∀ u : SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume, ‖u‖ ^ 2 = inner ℝ u u) ∧
      CompleteSpace (SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume) :=
  ⟨fun u v ↦ by simpa [RCLike.inner_apply, mul_comm] using SobolevMultiIndex.inner_eq u v,
    fun u ↦ (real_inner_self_eq_norm_sq u).symm, inferInstance⟩

/-- **Definition 7.2.9**: `W_0^{k,p}(Ω)` is the closure of `C_0^∞(Ω)` in `W^{k,p}(Ω)`; when
`p = 2` one writes `H_0^k(Ω) ≡ W_0^{k,2}(Ω)`.

`SobolevZero ℝ k p Ω volume` is the closure, inside the Banach space of Theorem 7.2.3, of the
submodule of elements whose function agrees off a null set with a test function on `Ω`; every test
function does give such an element, by `TestFunction.exists_mem_testFunctions`. It is taken in the
bundled reading `Sobolev ℝ k p Ω volume` rather than in the multi-index one; the two norms are
equivalent, so mathematically this is the same subspace of functions, but that equivalence is not
formalized and no comparison of the two closures is available here. The book's reading of the
space — the functions whose derivatives of order at most `k - 1` vanish on `∂Ω` — is made precise
only by the trace theorems of §7.3, which are not formalized. -/
noncomputable def definition_7_2_9 (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (Sobolev ℝ k p Ω volume) :=
  SobolevZero ℝ k p Ω volume

end AtkinsonHan.Chapter07
