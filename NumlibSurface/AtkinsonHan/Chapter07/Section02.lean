import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Numlib.Analysis.Sobolev.Slobodeckij
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

Definition 7.2.1, the regularity of `∂Ω`, opens the section and is a condition on the *domain*
rather than on a space of functions on it. It is restated here from the backbone predicate
`IsBoundaryOfClass` of `Numlib/Analysis/Sobolev/Domain.lean`, whose ambient space is written
`ℝ^{d+1}` so that the graph functions live on `ℝ^d`; its two named cases are the Lipschitz domain
and the `C^n` domain, and `definition_7_2_1_finite_cover` is the finite cover of `∂Ω` that
compactness supplies.

The real-order spaces of §7.2.2 are here as well. Definition 7.2.10, `W^{s,p}(Ω)` for
`s = k + σ`, is the predicate `definition_7_2_10` on functions; the type carrying its norm is the
backbone `SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume` of
`Numlib/Analysis/Sobolev/Slobodeckij.lean`, a `W^{k,p}(Ω)` family paired, in the `ℓ^p` combination,
with the `L^p(Ω × Ω)` difference quotients `(∂^α v(x) - ∂^α v(y)) / ‖x - y‖^{σ + d/p}` of its
top-order members. `definition_7_2_10_iff_exists` identifies the elements of that type with the
functions of the predicate and `definition_7_2_10_norm` shows its norm is the displayed one. That
the space is Banach, reflexive for `p ∈ (1,∞)` and Hilbert for `p = 2` is stated in the book without
proof and is not proved. Definition 7.2.11 is the closure of `C_0^∞(Ω)` in it, in the same shape as
Definition 7.2.9, and Definition 7.2.12 the dual of that closure, in the real-order and the
integer-order case, with `H^{-1}(Ω)` named separately.

Of Example 7.2.5 only the `L^p` half is here, `example_7_2_5_memLp`: `|x|^λ ∈ L^p(Ω)` on the unit
ball exactly when `λ > -d/p`. The equivalence (7.2.1) for `W^{k,p}` needs the weak derivative of
`|x|^λ` through the origin, which neither the book nor this file proves. Example 7.2.6 (the
unbounded `H^1` function of the plane) needs the same step; Examples 7.2.7 and 7.2.8 and
Definition 7.2.13 need surface measure on a Lipschitz boundary, which exists nowhere.
-/

open MeasureTheory Metric Module TopologicalSpace

open scoped ENNReal

namespace AtkinsonHan.Chapter07

variable {d : ℕ}

/-- **Definition 7.2.1**: for `Ω ⊆ ℝ^{d+1}` open and bounded and `V` a function space on `ℝ^d`,
the boundary `∂Ω` is *of class `V`* when each `x_0 ∈ ∂Ω` has an `r > 0` and a `g ∈ V` with
`Ω ∩ B(x_0, r) = {x ∈ B(x_0, r) : x_{d+1} > g(x_1, …, x_d)}` upon a transformation of the
coordinate system if necessary.

The backbone predicate is `IsBoundaryOfClass`, in `Numlib/Analysis/Sobolev/Domain.lean`, and the
transformation of the coordinate system is an affine isometry of `ℝ^{d+1}`, that is, a rigid
motion. The dimension of the ambient space is written `d + 1` so that the graph functions live on
`ℝ^d` without a truncated subtraction; the book's `d` is `d + 1` here.

Openness and boundedness of `Ω`, which the book assumes throughout §7.2, are not part of the
predicate: `Ω : Opens _` carries the first, and `definition_7_2_1_finite_cover` asks for the
second. The two named classes of the definition are `definition_7_2_1_lipschitzDomain` and
`definition_7_2_1_contDiffDomain`. -/
def definition_7_2_1 (V : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  IsBoundaryOfClass V (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))

/-- Definition 7.2.1 unfolded: `∂Ω` is of class `V` exactly when every boundary point `x_0` has a
radius `r > 0`, a rigid motion `T` of `ℝ^{d+1}` and a `g ∈ V` for which `Ω ∩ B(x_0, r)` is the part
of `B(x_0, r)` lying strictly above the graph of `g` in the coordinates `T x`. -/
theorem definition_7_2_1_iff (V : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    definition_7_2_1 V Ω ↔ ∀ x₀ ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ∃ r > 0,
      ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)), ∃ g ∈ V,
        (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ ball x₀ r =
          {x ∈ ball x₀ r | g (EuclideanSpace.init (T x)) < T x (Fin.last d)} :=
  Iff.rfl

/-- **Definition 7.2.1, the Lipschitz case**: an open `Ω` is a *Lipschitz domain* exactly when
`∂Ω` is of class `V` for `V` the Lipschitz continuous functions on `ℝ^d`. The backbone name is
`IsLipschitzDomain`. -/
theorem definition_7_2_1_lipschitzDomain (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    IsLipschitzDomain (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ↔
      definition_7_2_1 {g | ∃ K, LipschitzWith K g} Ω :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨Ω.isOpen, h⟩⟩

/-- **Definition 7.2.1, the `C^n` case**: an open `Ω` is a *`C^n` domain* exactly when `∂Ω` is of
class `V` for `V` the `C^n` functions on `ℝ^d`. The backbone name is `IsContDiffDomain`. -/
theorem definition_7_2_1_contDiffDomain (n : WithTop ℕ∞)
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    IsContDiffDomain n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ↔
      definition_7_2_1 {g | ContDiff ℝ n g} Ω :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨Ω.isOpen, h⟩⟩

/-- **The finite cover of `∂Ω` that follows Definition 7.2.1**: since `∂Ω` is compact when `Ω` is
bounded, finitely many of the balls of the definition already cover `∂Ω`, giving points
`x_1, …, x_I` of `∂Ω`, radii `r_1, …, r_I > 0` and functions `g_1, …, g_I ∈ V` with
`Ω ∩ B(x_i, r_i)` the region above the graph of `g_i` and `∂Ω ⊆ ⋃_i B(x_i, r_i)`. The pairs
`(x_i, r_i)` are collected into one `Finset`. -/
theorem definition_7_2_1_finite_cover {V : Set (EuclideanSpace ℝ (Fin d) → ℝ)}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (h : definition_7_2_1 V Ω) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin (d + 1)) × ℝ),
      (∀ q ∈ s, q.1 ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∧ 0 < q.2 ∧
        IsBoundaryGraphAt V (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) q.1 q.2) ∧
      frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ⋃ q ∈ s, ball q.1 q.2 :=
  h.exists_finite_cover hΩ

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

/-- **Example 7.2.5, the `L^p` half**: on the unit ball `Ω` of `ℝ^d` with `d ≥ 1`, the radial
function `v(x) = |x|^λ` lies in `L^p(Ω)` exactly when `λ > -d/p`, for `p ∈ [1, ∞)`.

The book's computation is `‖v‖_{L^p(Ω)}^p = ∫_Ω |x|^{λp} dx = c_d ∫_0^1 r^{λp + d - 1} dr` with
`c_d` the surface area of the unit sphere, and the last integral converges exactly when
`λp + d - 1 > -1`. The polar decomposition is Mathlib's `integrableOn_fun_norm_addHaar` and the
convergence criterion is `intervalIntegral.integrableOn_Ioo_rpow_iff`.

The rest of the example — the equivalence (7.2.1), `v ∈ W^{k,p}(Ω) ↔ λ > k - d/p`, which the book
leaves to Exercise 7.2.7 — is *not* proved here. It needs the first-order weak derivative
`v_{x_i}(x) = λ |x|^{λ-2} x_i` of `v` on the whole ball, origin included, which is the step the
book also passes over ("it can be verified"): the classical derivative on `Ω \ {0}` has to be shown
to be the weak derivative on `Ω`, which is an integration by parts against a cutoff and is not
available here. Once that step exists, each order of differentiation contributes the exponent
`λ - k` and this lemma supplies the rest. -/
theorem example_7_2_5_memLp (hd : 0 < d) (lam : ℝ) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ lam) p
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) ↔
      -((d : ℝ) / p.toReal) < lam := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; exact hd)
  have ht : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hmeas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ lam)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
    (measurable_norm.pow measurable_const).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas hp0 hpt]
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin d),
      ‖‖x‖ ^ lam‖ ^ p.toReal = ‖x‖ ^ (lam * p.toReal) := fun x ↦ by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),
      ← Real.rpow_mul (norm_nonneg x)]
  simp_rw [hnorm]
  rw [← IntegrableOn, integrableOn_fun_norm_addHaar volume
    (f := fun y : ℝ ↦ y ^ (lam * p.toReal)),
    integrableOn_congr_fun (g := fun y : ℝ ↦ y ^ ((d : ℝ) - 1 + lam * p.toReal))
      ?_ measurableSet_Ioo, intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  · rw [← neg_div, div_lt_iff₀ ht]
    constructor <;> intro h <;> linarith
  · intro y hy
    simp only [hfr, smul_eq_mul]
    rw [← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy.1, Nat.cast_sub hd, Nat.cast_one]

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

/-! ### Sobolev spaces of real order

The book's §7.2.2. Throughout it `p ∈ [1, ∞)`, and the order is `s = k + σ` with `k ≥ 0` an integer
and `σ ∈ (0,1)`; the statements below take `k`, `σ` and `p` as parameters and place no constraint on
`σ`, the constraint being what makes them the book's spaces rather than what makes them well formed.

The machinery is in the backbone, `Numlib/Analysis/Sobolev/Slobodeckij.lean`:
`SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume` is `W^{s,p}(Ω)` as a normed space, and
`SobolevSlobodeckijZero` the closure of the test functions in it. What is here is the book's own
statements over that: the set of Definition 7.2.10 as a predicate on functions, the identification
of the elements of the type with those functions, and the fact that the norm of the type is the
norm the definition displays. -/

variable (d) in
/-- **Definition 7.2.10**: for `s = k + σ` with `k ≥ 0` an integer and `σ ∈ (0,1)`, the Sobolev
space `W^{s,p}(Ω)` is the set of `v ∈ W^{k,p}(Ω)` whose weak derivatives of top order have finite
Sobolev–Slobodeckij seminorm, that is, for which
`(x, y) ↦ (∂^α v(x) - ∂^α v(y)) / ‖x - y‖^{σ + d/p}` lies in `L^p(Ω × Ω)` for every `α` with
`|α| = k`. The book writes the numerator in absolute value, which is immaterial: membership of
`L^p` sees a function only through its norm.

The weak derivative `∂^α v` is determined only almost everywhere on `Ω`, so the condition is
imposed on *every* `w` that is an `α`-th weak derivative of `v`; by `definition_7_2_10_of_exists`
that is the same as imposing it on one.

The norm that comes with the definition lives on the type
`SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume`, whose elements are these functions by
`definition_7_2_10_iff_exists` and whose norm is the displayed one by `definition_7_2_10_norm`. -/
def definition_7_2_10 (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  definition_7_2_2_multiIndex k p Ω v ∧
    ∀ α : Fin d → ℕ, ∑ i, α i = k → ∀ w : EuclideanSpace ℝ (Fin d) → ℝ,
      definition_7_1_3_multiIndex α v w Ω →
        MemLp (fun z ↦ (w z.1 - w z.2) / ‖z.1 - z.2‖ ^ (σ + (d : ℝ) / p.toReal)) p
          (prodRestrict Ω volume)

/-- The difference quotient of Definition 7.2.10 is the backbone `slobodeckijQuotient`: on
`ℝ^d` the dimension in its exponent is `d`, and for a real-valued `w` the scalar multiplication in
its definition is a division. -/
theorem definition_7_2_10_quotient (σ : ℝ) (p : ℝ≥0∞) (w : EuclideanSpace ℝ (Fin d) → ℝ) :
    slobodeckijQuotient σ p w =
      fun z ↦ (w z.1 - w z.2) / ‖z.1 - z.2‖ ^ (σ + (d : ℝ) / p.toReal) := by
  funext z
  simp [slobodeckijQuotient, div_eq_inv_mul]

/-- Definition 7.2.10 asks for the finiteness of the Sobolev–Slobodeckij seminorm of *every*
function that is an `α`-th weak derivative of `v`; it is enough to exhibit *one* for each `α`. Any
two agree off a null set of `Ω`, hence have the same difference quotient off a null set of
`Ω × Ω`, by `slobodeckijQuotient_congr_ae`. -/
theorem definition_7_2_10_of_exists {k : ℕ} {σ : ℝ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (h₁ : definition_7_2_2_multiIndex k p Ω v)
    (h₂ : ∀ α : Fin d → ℕ, ∑ i, α i = k → ∃ w, definition_7_1_3_multiIndex α v w Ω ∧
      MemLp (fun z ↦ (w z.1 - w z.2) / ‖z.1 - z.2‖ ^ (σ + (d : ℝ) / p.toReal)) p
        (prodRestrict Ω volume)) :
    definition_7_2_10 d k σ p Ω v := by
  refine ⟨h₁, fun α hα w' hw' ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h₂ α hα
  rw [← definition_7_2_10_quotient σ p w] at hwp
  rw [← definition_7_2_10_quotient σ p w']
  exact hwp.ae_eq (slobodeckijQuotient_congr_ae (Ω := Ω)
    ((ae_restrict_iff' Ω.isOpen.measurableSet).2 (hw.ae_eq hw')))

/-- Definition 7.2.10 read on the *type* `SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume`, which
is `W^{s,p}(Ω)` carrying the norm of the definition: a function `v` belongs to `W^{s,p}(Ω)` exactly
when it agrees, off a null subset of `Ω`, with the function underlying an element of that type. -/
theorem definition_7_2_10_iff_exists (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_10 d k σ p Ω v ↔
      ∃ U : SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume,
        SobolevSlobodeckij.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))] v := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨u, hu⟩ := MemSobolevMultiIndex.exists_sobolevMultiIndex h1
    have hw : ∀ α : MultiIndexEq (Fin d) k,
        MemLp (slobodeckijQuotient σ p (SobolevMultiIndex.weakDeriv u α.1)) p
          (prodRestrict Ω volume) := fun α ↦ by
      rw [definition_7_2_10_quotient]
      exact h2 α.1.1 α.2 _ ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u α.1).congr_ae hu
        (Filter.EventuallyEq.refl _ _))
    refine ⟨⟨WithLp.toLp p ((u : SobolevMultiIndexTuple ℝ (Fin d) k p Ω volume),
      WithLp.toLp p fun α : MultiIndexEq (Fin d) k ↦ (hw α).toLp _), u.2, fun α ↦ ?_⟩, hu⟩
    exact (hw α).coeFn_toLp
  · rintro ⟨U, hU⟩
    refine ⟨(SobolevMultiIndex.memSobolevMultiIndex
      (SobolevSlobodeckij.toSobolevMultiIndex U)).congr_ae hU, fun α hα w hwd ↦ ?_⟩
    have hae : w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))]
        (SobolevMultiIndex.weakDeriv (SobolevSlobodeckij.toSobolevMultiIndex U)
          ⟨α, hα.le⟩ : _ → ℝ) :=
      (ae_restrict_iff' Ω.isOpen.measurableSet).2
        (hwd.ae_eq ((SobolevMultiIndex.hasWeakIteratedLineDerivOn
          (SobolevSlobodeckij.toSobolevMultiIndex U) ⟨α, hα.le⟩).congr_ae hU
            (Filter.EventuallyEq.refl _ _)))
    rw [← definition_7_2_10_quotient σ p w]
    refine (Lp.memLp ((U : SobolevSlobodeckijTuple ℝ (Fin d) k p Ω volume).snd
      ⟨⟨α, hα.le⟩, hα⟩)).ae_eq ((SobolevSlobodeckij.snd_ae U ⟨⟨α, hα.le⟩, hα⟩).trans ?_)
    exact (slobodeckijQuotient_congr_ae (Ω := Ω) hae).symm

/-- **The norm of Definition 7.2.10**,
`‖v‖_{s,p,Ω} = [‖v‖_{k,p,Ω}^p + ∑_{|α| = k} ∫_{Ω × Ω} |∂^α v(x) - ∂^α v(y)|^p / ‖x - y‖^{σp + d}
dx dy]^{1/p}` for `1 ≤ p < ∞`, is the norm of the type
`SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume`. The first term is the norm of
Definition 7.2.2 in the book's indexing, by `definition_7_2_2_multiIndex_norm`. -/
theorem definition_7_2_10_norm {k : ℕ} {σ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {Ω : Opens (EuclideanSpace ℝ (Fin d))}
    (U : SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume) :
    ‖U‖ = (‖SobolevSlobodeckij.toSobolevMultiIndex U‖ ^ p.toReal
        + ∑ α : MultiIndexEq (Fin d) k,
            ∫ z, |(SobolevMultiIndex.weakDeriv
                    (SobolevSlobodeckij.toSobolevMultiIndex U) α.1 : _ → ℝ) z.1
                - (SobolevMultiIndex.weakDeriv
                    (SobolevSlobodeckij.toSobolevMultiIndex U) α.1 : _ → ℝ) z.2| ^ p.toReal
              / ‖z.1 - z.2‖ ^ (σ * p.toReal + (d : ℝ)) ∂(prodRestrict Ω volume))
      ^ (1 / p.toReal) := by
  have htp : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  rw [SobolevSlobodeckij.norm_eq_add hp, SobolevMultiIndex.norm_eq_sum hp, one_div,
    Real.rpow_inv_rpow (by positivity) htp.ne']
  congr 2
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [SobolevSlobodeckij.norm_snd_rpow hp U α]
  simp only [Real.norm_eq_abs, finrank_euclideanSpace_fin]
  rfl

variable (d) in
/-- **Definition 7.2.11**: for `s = k + σ ≥ 0`, `W_0^{s,p}(Ω)` is the closure of `C_0^∞(Ω)` in
`W^{s,p}(Ω)`; when `p = 2` one writes `H_0^s(Ω) ≡ W_0^{s,2}(Ω)`.

`SobolevSlobodeckijZero ℝ (stdBasis d) k σ p Ω volume` is that closure, taken inside the normed
space `SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume` of Definition 7.2.10, of the submodule of
elements whose function agrees off a null set with a test function on `Ω`. The integer-order case
`σ = 0` of the definition is `definition_7_2_9`, where the closure is taken in `W^{k,p}(Ω)`
instead; the book keeps the two apart because `C_0^∞(Ω)` need not be dense in `W^{s,p}(Ω)`.

That every test function does lie in `W^{s,p}(Ω)` is not proved; see the implementation notes of
`Numlib/Analysis/Sobolev/Slobodeckij.lean`. -/
noncomputable def definition_7_2_11 (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) :
    Submodule ℝ (SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume) :=
  SobolevSlobodeckijZero ℝ (stdBasis d) k σ p Ω volume

variable (d) in
/-- **Definition 7.2.12**: for `s = k + σ ≥ 0` and `p ∈ [1, ∞)` with conjugate exponent `p'`,
`W^{-s,p'}(Ω)` is the dual space of `W_0^{s,p}(Ω)`; when `p = 2` one writes
`H^{-s}(Ω) ≡ W^{-s,2}(Ω)`.

The dual is Mathlib's `StrongDual`, the continuous linear functionals with the operator norm, so
that `‖ℓ‖ = sup_{v ∈ W_0^{s,p}(Ω)} ℓ(v) / ‖v‖` as in the book. The exponent `p'` appears only in
the name of the space: the object depends on `p`, and `p'` is `ENNReal.conjExponent p`. The
integer-order case is `definition_7_2_12_integerOrder`, and the `H^{-1}(Ω)` singled out in the book
is `definition_7_2_12_hMinusOne`.

Not formalized: the book's two further remarks, that `L^2(Ω)` embeds in `H^{-1}(Ω)` by
`⟨f, v⟩ = ∫_Ω f v`, and that every `ℓ ∈ H^{-1}(Ω)` is `ℓ_0 - ∑_i ∂_i ℓ_i` for `L^2(Ω)` functions
`ℓ_0, …, ℓ_d`; the second is stated there without proof. -/
noncomputable abbrev definition_7_2_12 (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Type _ :=
  StrongDual ℝ (definition_7_2_11 d k σ p Ω)

variable (d) in
/-- **Definition 7.2.12 in the integer-order case**: for an integer `s = k ≥ 0` and `p ∈ [1, ∞)`
with conjugate exponent `p'`, `W^{-k,p'}(Ω)` is the dual space of the `W_0^{k,p}(Ω)` of
Definition 7.2.9. -/
noncomputable abbrev definition_7_2_12_integerOrder (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Type _ :=
  StrongDual ℝ (definition_7_2_9 k p Ω)

variable (d) in
/-- **The space `H^{-1}(Ω)`**, the dual of `H_0^1(Ω)`: Definition 7.2.12 at `s = 1` and `p = 2`.
This is the case the book singles out and the one later chapters use. -/
noncomputable abbrev definition_7_2_12_hMinusOne (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Type _ :=
  definition_7_2_12_integerOrder d 1 2 Ω

end AtkinsonHan.Chapter07
