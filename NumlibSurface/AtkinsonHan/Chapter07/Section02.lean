import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Analysis.Sobolev.RemovableSingularity
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
multi-index `α` with `|α| ≤ k`. As predicates the two are equivalent,
`definition_7_2_2_iff_definition_7_2_2_multiIndex`. The easy half is
`definition_7_2_2_multiIndex_of_definition_7_2_2`; the other,
`definition_7_2_2_of_definition_7_2_2_multiIndex`, rests on the symmetry of the derivatives of a
`C^∞` test function in its arguments, which Mathlib does not have past order two and which the
backbone supplies as `ContDiff.iteratedFDeriv_congr_perm`.

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

Example 7.2.5 is here in two halves. `example_7_2_5_memLp` is the `L^p` one: `|x|^λ ∈ L^p(Ω)` on
the unit ball exactly when `λ > -d/p`. `example_7_2_5_memW1p` is the first-order Sobolev one: for
`λ ≠ 0`, `|x|^λ ∈ W^{1,p}(Ω)` exactly when `λ > 1 - d/p`. The step the book passes over with "it
can be verified" — that the classical `v_{x_i}(x) = λ |x|^{λ-2} x_i` on `Ω ∖ {0}` is the weak
derivative on all of `Ω`, the origin included — is `hasWeakIteratedLineDerivOn_normRpow`, an
instance of the removable-singularity lemma `hasWeakFDerivOn_of_hasFDerivAt_compl_singleton` of
`Numlib/Analysis/Sobolev/RemovableSingularity.lean`.

The hypothesis `λ ≠ 0` is not a convenience: **the book's equivalence is false without it**, and so
is the general (7.2.1), `v ∈ W^{k,p}(Ω) ↔ λ > k - d/p`. For `λ` a nonnegative even integer `|x|^λ`
is a polynomial, hence in `W^{k,p}(Ω)` for every `k`, while `λ > k - d/p` fails once
`k ≥ λ + d/p`; already `λ = 0`, `k = 1`, `d = p = 2` is a counterexample, and the case `λ = 0` is
proved here as `example_7_2_5_const`. The doc comment of `example_7_2_5_memW1p` spells this out.
The `W^{k,p}` case for `k ≥ 2` is not formalized: it needs bounds on the derivatives of `|x|^λ` of
every order, which the homogeneity of the function supplies but which are not available here.

Example 7.2.6 is here as `example_7_2_6`: on `Ω = B(0,β) ⊆ ℝ^2` with `0 < β < 1` the function
`v(x) = log(log(1/|x|))` has `∫_Ω |∇v|^2 = -2π/log β`, has finite `L^2(Ω)` norm, lies in
`H^1(Ω) = W^{1,2}(Ω)`, and is unbounded near the origin — an `H^1` function of the plane need not
be continuous. The weak gradient again comes from the removable-singularity lemma,
as `hasWeakIteratedLineDerivOn_logLogNorm`; the value of the gradient integral is
`integral_sq_norm_logLogNormGrad`, whose radial part `∫_0^β dr/(r log^2 r) = -1/log β` is
`integral_inv_mul_log_sq`, an integral improper at the origin that becomes an ordinary one because
its antiderivative `-1/log r` extends continuously by `0` — which is exactly the value Lean's
`Real.log 0 = 0` gives it.

Examples 7.2.7 and 7.2.8 and Definition 7.2.13 need surface measure on a Lipschitz boundary, which
exists nowhere.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace

open scoped ENNReal Real Topology

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
`definition_7_2_2_multiIndex` is the book's reading, one `α` at a time. As predicates the two are
equivalent, `definition_7_2_2_iff_definition_7_2_2_multiIndex`, so the choice between them is one
of *norm* and not of content, and the multi-index reading is the one to prefer when the norm
matters. The norm `‖v‖_{k,p,Ω}` and seminorm `|v|_{k,p,Ω}` attached to this
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
of order `|α|` evaluated at the tuple of directions naming `α`. The converse is
`definition_7_2_2_of_definition_7_2_2_multiIndex`. -/
theorem definition_7_2_2_multiIndex_of_definition_7_2_2 {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : definition_7_2_2 k p Ω v) : definition_7_2_2_multiIndex k p Ω v :=
  h.memSobolevMultiIndex

/-- The book's reading of Definition 7.2.2 gives the bundled one, the converse of
`definition_7_2_2_multiIndex_of_definition_7_2_2`: the derivative tensor of order `n` is built from
its values on the tuples of coordinate directions, `∂^α v` for the multi-index `α` counting the
occurrences of each direction, extended by multilinearity. The value on a tuple that is not in
increasing order is `∂^α v` of the *reordered* tuple, so the argument needs the symmetry of
`iteratedFDeriv ℝ n φ x` under permutations of its arguments for a `C^∞` test function `φ`; Mathlib
has that symmetry only for `n = 2` and for analytic functions, and a test function is not analytic,
so the backbone proves it as `ContDiff.iteratedFDeriv_congr_perm`. -/
theorem definition_7_2_2_of_definition_7_2_2_multiIndex {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : definition_7_2_2_multiIndex k p Ω v) : definition_7_2_2 k p Ω v :=
  MemSobolevMultiIndex.memSobolev h

/-- **The two readings of Definition 7.2.2 describe the same functions.** A function belongs to
`W^{k,p}(Ω)` in the bundled reading exactly when it does in the book's, one multi-index at a time.
What the two readings do not share is the *norm*: `sobolevNorm` sums over the orders `n ≤ k` and
the norm of Definition 7.2.2 over the multi-indices `α` with `|α| ≤ k`, and the equivalence of
those two norms is not formalized. -/
theorem definition_7_2_2_iff_definition_7_2_2_multiIndex {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ} :
    definition_7_2_2 k p Ω v ↔ definition_7_2_2_multiIndex k p Ω v :=
  memSobolev_iff_memSobolevMultiIndex (stdBasis d)

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

/-- A multi-index of order one is carried by a single index. -/
theorem exists_index_of_sum_eq_one {α : Fin d → ℕ} (hα : ∑ i, α i = 1) :
    ∃ i₀, ∀ i, α i ≠ 0 → i = i₀ := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, α i₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp only [h, Finset.sum_const_zero] at hα
    exact one_ne_zero hα.symm
  refine ⟨i₀, fun i hi ↦ ?_⟩
  by_contra hne
  have hpair : α i₀ + α i ≤ ∑ j, α j := by
    rw [← Finset.sum_pair (Ne.symm hne)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [hα] at hpair
  omega

/-- The tuple of directions naming a multi-index of order one is the constant tuple at the single
index the multi-index is carried by. -/
theorem multiIndexTuple_of_sum_eq_one {b : Fin d → EuclideanSpace ℝ (Fin d)} {α : Fin d → ℕ}
    {i₀ : Fin d} (h : ∀ i, α i ≠ 0 → i = i₀) (j : Fin (∑ i, α i)) :
    multiIndexTuple b α j = b i₀ := by
  have hmem : multiIndexTuple b α j ∈ multiIndexDirections b α := List.get_mem _ _
  rw [multiIndexDirections, List.mem_flatMap] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  rw [List.mem_replicate] at hi
  rw [hi.2, h i hi.1]

/-- In `ℝ^d` the sum of the squared coordinates is the squared norm. -/
theorem sum_sq_apply (x : EuclideanSpace ℝ (Fin d)) : ∑ i, x i ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp

/-- In `ℝ^d` a coordinate is bounded by the norm. -/
theorem abs_apply_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have h2 : x i ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sum_sq_apply x]
    exact Finset.single_le_sum (f := fun j ↦ x j ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
  calc |x i| = √(x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖x‖ := by rw [Real.sqrt_sq (norm_nonneg x)]

/-- The classical gradient of `v(x) = |x|^λ` on `ℝ^d ∖ {0}`, read as a linear functional
`h ↦ λ |x|^{λ-2} ⟪x, h⟫`. Its `i`-th component is the `v_{x_i}(x) = λ |x|^{λ-2} x_i` displayed in
Example 7.2.5. -/
noncomputable def normRpowGrad (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  (lam * ‖x‖ ^ (lam - 2)) • innerSL ℝ x

/-- Away from the origin, `normRpowGrad` is the classical derivative of `|x|^λ`. -/
theorem hasFDerivAt_normRpowGrad (lam : ℝ) {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) ↦ ‖y‖ ^ lam) (normRpowGrad lam x) x :=
  hasFDerivAt_norm_rpow_of_ne_zero hx lam

/-- The `i`-th component of `normRpowGrad lam x` is `λ |x|^{λ-2} x_i`, the formula of
Example 7.2.5. -/
theorem normRpowGrad_apply (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    normRpowGrad lam x (stdBasis d i) = lam * ‖x‖ ^ (lam - 2) * x i := by
  simp [normRpowGrad, stdBasis, EuclideanSpace.inner_single_right]

/-- `|∇ |x|^λ| ≤ |λ| |x|^{λ-1}`, with equality away from the origin. -/
theorem norm_normRpowGrad_le (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖normRpowGrad lam x‖ ≤ |lam| * ‖x‖ ^ (lam - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [normRpowGrad, map_zero, smul_zero, norm_zero]
    positivity
  · rw [← (hasFDerivAt_normRpowGrad lam hx).fderiv, norm_fderiv_norm_rpow_of_ne_zero hx lam]

/-- `normRpowGrad lam` is measurable. -/
theorem aestronglyMeasurable_normRpowGrad (lam : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : AEStronglyMeasurable (normRpowGrad lam) μ :=
  AEStronglyMeasurable.smul
    (measurable_const.mul (measurable_norm.pow measurable_const)).aestronglyMeasurable
    (innerSL ℝ).continuous.aestronglyMeasurable

/-- `|x|^q` is integrable on every ball about the origin as soon as `q > -d`. -/
theorem integrableOn_normRpow (hd : 0 < d) {q : ℝ} (hq : -(d : ℝ) < q) (t : ℝ) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ q) (ball 0 t) volume := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  refine integrableOn_norm_rpow_ball_zero (by omega) ?_ t
  rw [hfr]
  exact hq

/-- `∇ |x|^λ` is integrable on every ball about the origin as soon as `λ > 1 - d`. -/
theorem integrableOn_normRpowGrad (hd : 0 < d) {lam : ℝ} (hlam : 1 - (d : ℝ) < lam) (t : ℝ) :
    IntegrableOn (normRpowGrad (d := d) lam) (ball 0 t) volume := by
  refine Integrable.mono' ((integrableOn_normRpow hd (q := lam - 1) (by linarith) t).const_mul
    |lam|) (aestronglyMeasurable_normRpowGrad lam _).restrict
    (Filter.Eventually.of_forall fun x ↦ ?_)
  exact norm_normRpowGrad_le lam x

/-- **The step Example 7.2.5 passes over with "it can be verified"**: for `λ > 1 - d` the classical
derivative `v_{x_i}(x) = λ |x|^{λ-2} x_i` of `v(x) = |x|^λ`, which exists on `Ω ∖ {0}`, is the
weak `∂^α` derivative of `v` on all of `Ω`, the origin included, for every multi-index `α` of
order one carried by the index `i`.

The backbone statement is `hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton` of
`Numlib/Analysis/Sobolev/RemovableSingularity.lean`; its smallness hypothesis
`∫_{B(0,δ)} |v| = o(δ)` holds here because `λ > 1 - d`. -/
theorem hasWeakIteratedLineDerivOn_normRpow (hd : 0 < d) {lam : ℝ} (hlam : 1 - (d : ℝ) < lam)
    (t : ℝ) {α : Fin d → ℕ} {i₀ : Fin d} (hα : ∑ i, α i = 1) (hi₀ : ∀ i, α i ≠ 0 → i = i₀) :
    HasWeakIteratedLineDerivOn (multiIndexTuple (stdBasis d) α)
      (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ lam)
      (fun x ↦ normRpowGrad lam x (stdBasis d i₀)) ⟨ball 0 t, isOpen_ball⟩ volume := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; exact hd)
  refine hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton hα
    (fun j ↦ multiIndexTuple_of_sum_eq_one hi₀ j)
    (fun x _ ↦ ⟨_, self_mem_nhdsWithin, integrableOn_normRpow hd (by linarith) t⟩)
    (fun x _ ↦ ⟨_, self_mem_nhdsWithin, integrableOn_normRpowGrad hd hlam t⟩)
    (fun x _ hx ↦ hasFDerivAt_normRpowGrad lam hx) ?_
  refine tendsto_inv_mul_setIntegral_norm_ball_zero (by omega) (C := 1) (s := lam) (R := 1)
    one_pos (by rw [hfr]; linarith)
    (measurable_norm.pow measurable_const).aestronglyMeasurable fun x _ ↦ ?_
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) lam)]

/-- **Example 7.2.5, the `W^{1,p}` half**: on the unit ball `Ω` of `ℝ^d` with `d ≥ 1`, and for
`p ∈ [1, ∞)`, the radial function `v(x) = |x|^λ` with `λ ≠ 0` lies in `W^{1,p}(Ω)` exactly when
`λ > 1 - d/p`. This is the equivalence the book displays just above (7.2.1).

**The hypothesis `λ ≠ 0` is necessary: the book's statement is false without it.** At `λ = 0` the
function is the constant `1`, which lies in `W^{k,p}(Ω)` for every `k` and every `p`, while
`0 > 1 - d/p` fails as soon as `d ≤ p`; so the displayed equivalence fails at `d = 2`, `p = 2`,
`λ = 0`. The book reads off `|∇v| = |λ| |x|^{λ-1}` and then concludes that `∇v ∈ L^p(Ω)` exactly
when `(λ - 1)p + d > 0`, which is right only when the factor `|λ|` is nonzero.

The case `λ = 0` is `example_7_2_5_const`, which proves the counterexample rather than merely
asserting it. The same defect makes the general equivalence (7.2.1),
`v ∈ W^{k,p}(Ω) ↔ λ > k - d/p`, false as stated: whenever `λ` is a nonnegative even integer,
`|x|^λ = (x · x)^{λ/2}` is a polynomial and so lies in `W^{k,p}(Ω)` for every `k`, while
`λ > k - d/p` fails once `k ≥ λ + d/p`.

The proof is `example_7_2_5_memLp` at the two exponents `λ` and `λ - 1`, together with
`hasWeakIteratedLineDerivOn_normRpow` for the weak derivative through the origin; the converse
direction identifies the weak derivative with the classical one off the origin, where the two
agree by `hasWeakIteratedLineDerivOn_of_hasFDerivAt`, and reads the size of `|x|^{λ-1}` off the
radial component `∑_i (x_i/|x|) v_{x_i}(x) = λ |x|^{λ-1}` of the gradient. -/
theorem example_7_2_5_memW1p (hd : 0 < d) {lam : ℝ} (hlam : lam ≠ 0) (p : ℝ≥0∞) (hp1 : 1 ≤ p)
    (hpt : p ≠ ⊤) :
    definition_7_2_2_multiIndex 1 p ⟨ball 0 1, isOpen_ball⟩
        (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ lam) ↔
      1 - (d : ℝ) / p.toReal < lam := by
  classical
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; exact hd)
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz] at hp1
    simp at hp1
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have h1pr : (1 : ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hpt hp1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdple : (d : ℝ) / p.toReal ≤ (d : ℝ) := by
    rw [div_le_iff₀ hpr]; nlinarith
  have hdppos : (0 : ℝ) < (d : ℝ) / p.toReal := by positivity
  have haevol : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ≠ 0 := by
    simp [ae_iff]
  have haezero : ∀ᵐ x ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)), x ≠ 0 :=
    ae_restrict_of_ae haevol
  constructor
  · intro h
    obtain ⟨hmem, hgrad⟩ := h
    have hlamd : -((d : ℝ) / p.toReal) < lam :=
      (example_7_2_5_memLp hd lam p hp0 hpt).1 hmem
    have hcomp : ∀ i : Fin d, MemLp (fun x ↦ normRpowGrad lam x (stdBasis d i)) p
        (volume.restrict (ball 0 1)) := by
      intro i
      set α : Fin d → ℕ := fun j ↦ if j = i then 1 else 0 with hαdef
      have hα : ∑ j, α j = 1 := by simp [hαdef]
      have hi₀ : ∀ j, α j ≠ 0 → j = i := by
        intro j hj
        by_contra hne
        exact hj (by simp [hαdef, hne])
      obtain ⟨w, hw, hwp⟩ := hgrad α (le_of_eq hα)
      set Ω' : Opens (EuclideanSpace ℝ (Fin d)) :=
        ⟨ball 0 1 ∩ ({(0 : EuclideanSpace ℝ (Fin d))} : Set (EuclideanSpace ℝ (Fin d)))ᶜ,
          isOpen_ball.inter isClosed_singleton.isOpen_compl⟩ with hΩ'
      have hΩ'le : Ω' ≤ (⟨ball 0 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin d))) :=
        Set.inter_subset_left
      have hcont : ContinuousOn (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ lam)
          (Ω' : Set (EuclideanSpace ℝ (Fin d))) := fun x hx ↦
        (hasFDerivAt_normRpowGrad lam hx.2).continuousAt.continuousWithinAt
      have hcontg : ContinuousOn (normRpowGrad (d := d) lam)
          (Ω' : Set (EuclideanSpace ℝ (Fin d))) := by
        refine fun x hx ↦ ContinuousAt.continuousWithinAt ?_
        have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx.2
        exact (continuousAt_const.mul
          (continuous_norm.continuousAt.rpow_const (Or.inl hne))).smul
          (innerSL ℝ).continuous.continuousAt
      have hcl : HasWeakIteratedLineDerivOn (multiIndexTuple (stdBasis d) α)
          (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ lam)
          (fun x ↦ normRpowGrad lam x (stdBasis d i)) Ω' volume :=
        hasWeakIteratedLineDerivOn_of_hasFDerivAt hα
          (fun j ↦ multiIndexTuple_of_sum_eq_one hi₀ j)
          (hcont.locallyIntegrableOn Ω'.isOpen.measurableSet)
          (hcontg.locallyIntegrableOn Ω'.isOpen.measurableSet)
          (fun x hx ↦ hasFDerivAt_normRpowGrad lam hx.2)
      have hae := (hw.mono hΩ'le).ae_eq hcl
      have haeball : w =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)]
          fun x ↦ normRpowGrad lam x (stdBasis d i) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
        filter_upwards [hae, haevol] with x hx hx0 hxb
        exact hx ⟨hxb, hx0⟩
      exact hwp.ae_eq haeball
    have hsum : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ i, (x i / ‖x‖) * normRpowGrad lam x (stdBasis d i)) p
        (volume.restrict (ball 0 1)) := by
      refine memLp_finsetSum _ fun i _ ↦ (hcomp i).of_le ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
      · have hm : Measurable fun x : EuclideanSpace ℝ (Fin d) ↦ x i / ‖x‖ :=
          (PiLp.continuous_apply 2 (fun _ ↦ ℝ) i).measurable.div measurable_norm
        exact hm.aestronglyMeasurable.mul
          ((aestronglyMeasurable_normRpowGrad lam _).apply_continuousLinearMap _)
      · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · rw [abs_div, abs_of_nonneg (norm_nonneg x), div_le_one (norm_pos_iff.2 hx)]
          exact abs_apply_le_norm x i
    have heq : (fun x : EuclideanSpace ℝ (Fin d) ↦
          ∑ i, (x i / ‖x‖) * normRpowGrad lam x (stdBasis d i))
        =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)]
        fun x ↦ lam * ‖x‖ ^ (lam - 1) := by
      filter_upwards [haezero] with x hx
      have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
      have hpow : ‖x‖ ^ (lam - 2) * ‖x‖ = ‖x‖ ^ (lam - 1) := by
        rw [← Real.rpow_add_one hn.ne']
        ring_nf
      simp only [normRpowGrad_apply]
      have hcalc : ∑ i, (x i / ‖x‖) * (lam * ‖x‖ ^ (lam - 2) * x i)
          = (lam * ‖x‖ ^ (lam - 2) / ‖x‖) * ∑ i, x i ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [hcalc, sum_sq_apply]
      calc lam * ‖x‖ ^ (lam - 2) / ‖x‖ * ‖x‖ ^ 2
          = lam * (‖x‖ ^ (lam - 2) * ‖x‖) * (‖x‖ / ‖x‖) := by ring
        _ = lam * ‖x‖ ^ (lam - 1) := by rw [div_self hn.ne', mul_one, hpow]
    have hfin : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ lam * ‖x‖ ^ (lam - 1)) p
        (volume.restrict (ball 0 1)) := hsum.ae_eq heq
    have hfin2 : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ (lam - 1)) p
        (volume.restrict (ball 0 1)) := by
      have hc := hfin.const_mul lam⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hlam] using hc
    have := (example_7_2_5_memLp hd (lam - 1) p hp0 hpt).1 hfin2
    linarith
  · intro hlt
    have hlam1 : 1 - (d : ℝ) < lam := by linarith
    have hlamd : -((d : ℝ) / p.toReal) < lam := by linarith
    have hlamd1 : -((d : ℝ) / p.toReal) < lam - 1 := by linarith
    have hv : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ lam) p
        (volume.restrict (ball 0 1)) := (example_7_2_5_memLp hd lam p hp0 hpt).2 hlamd
    refine ⟨hv, fun α hαle ↦ ?_⟩
    rcases Nat.eq_zero_or_pos (∑ i, α i) with hα0 | hα1
    · exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero hα0 _
        (fun x _ ↦ ⟨_, self_mem_nhdsWithin, integrableOn_normRpow hd (by linarith) 1⟩), hv⟩
    · have hα : ∑ i, α i = 1 := le_antisymm hαle hα1
      obtain ⟨i₀, hi₀⟩ := exists_index_of_sum_eq_one hα
      refine ⟨_, hasWeakIteratedLineDerivOn_normRpow hd hlam1 1 hα hi₀, ?_⟩
      have hgp : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ |lam| * ‖x‖ ^ (lam - 1)) p
          (volume.restrict (ball 0 1)) :=
        ((example_7_2_5_memLp hd (lam - 1) p hp0 hpt).2 hlamd1).const_mul |lam|
      refine hgp.of_le
        ((aestronglyMeasurable_normRpowGrad lam _).apply_continuousLinearMap _)
        (Filter.Eventually.of_forall fun x ↦ ?_)
      have h1 : ‖normRpowGrad lam x (stdBasis d i₀)‖
          ≤ ‖normRpowGrad lam x‖ * ‖stdBasis d i₀‖ := ContinuousLinearMap.le_opNorm _ _
      have h2 : ‖stdBasis d i₀‖ = 1 := by simp [stdBasis]
      rw [h2, mul_one] at h1
      refine h1.trans ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact norm_normRpowGrad_le lam x

/-- Every derivative of a constant function, evaluated at a fixed tuple of directions, is again a
constant function of the point. -/
theorem iteratedFDeriv_one_apply_const {n : ℕ} (y : Fin n → EuclideanSpace ℝ (Fin d))
    (x x' : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℝ n (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℝ)) x y
      = iteratedFDeriv ℝ n (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℝ)) x' y := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [iteratedFDeriv_zero_apply]
  · rw [iteratedFDeriv_const_of_ne hn]
    simp

/-- **The counterexample to (7.2.1)**: at `λ = 0` the function `v(x) = |x|^λ` is the constant `1`,
which lies in `W^{k,p}(Ω)` for every `k` and every `p` on a ball, while the right-hand side of
(7.2.1) reads `0 > k - d/p` and fails as soon as `k ≥ d/p`. So (7.2.1) is false, and so is the
first-order equivalence the book displays above it; `example_7_2_5_memW1p` is the corrected
first-order statement. -/
theorem example_7_2_5_const (k : ℕ) (p : ℝ≥0∞) (t : ℝ) :
    definition_7_2_2_multiIndex k p ⟨ball 0 t, isOpen_ball⟩
      (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ (0 : ℝ)) := by
  have hone : (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ (0 : ℝ)) = fun _ ↦ (1 : ℝ) :=
    funext fun x ↦ Real.rpow_zero _
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  rw [hone]
  refine ⟨memLp_const _, fun α _ ↦
    ⟨fun x ↦ iteratedFDeriv ℝ (∑ i, α i) (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℝ)) x
      (multiIndexTuple (stdBasis d) α), ?_, ?_⟩⟩
  · exact (contDiffOn_const.hasWeakIteratedFDerivOn (Ω := ⟨ball 0 t, isOpen_ball⟩)
      (μ := volume) le_top).lineDeriv (multiIndexTuple (stdBasis d) α)
  · rw [show (fun x ↦ iteratedFDeriv ℝ (∑ i, α i)
        (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℝ)) x (multiIndexTuple (stdBasis d) α))
      = fun _ ↦ iteratedFDeriv ℝ (∑ i, α i)
        (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℝ)) 0 (multiIndexTuple (stdBasis d) α) from
      funext fun x ↦ iteratedFDeriv_one_apply_const _ x 0]
    exact memLp_const _

/-! ### Example 7.2.6: an unbounded `H^1` function of the plane -/

/-- The antiderivative `-1/log r` of the radial integrand `1/(r log^2 r)` of Example 7.2.6 has
that integrand as its derivative wherever `log r ≠ 0`. -/
theorem hasDerivAt_neg_inv_log {y : ℝ} (hy0 : 0 < y) (hy : Real.log y ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ -(Real.log t)⁻¹) (y * Real.log y ^ 2)⁻¹ y := by
  have hl : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy0.ne'
  have h : HasDerivAt (fun t : ℝ ↦ -(Real.log t)⁻¹) (-(-y⁻¹ / Real.log y ^ 2)) y :=
    (hl.inv hy).neg
  have heq : -(-y⁻¹ / Real.log y ^ 2) = (y * Real.log y ^ 2)⁻¹ := by
    rw [mul_inv, neg_div, neg_neg, div_eq_mul_inv]
  rwa [heq] at h

/-- The antiderivative `-1/log r` extends continuously to the origin by `0`, which is the value
Lean's `Real.log 0 = 0` already gives it. This is what makes the improper integral of
Example 7.2.6 an ordinary one. -/
theorem continuousOn_neg_inv_log {β : ℝ} (hβ1 : β < 1) :
    ContinuousOn (fun t : ℝ ↦ -(Real.log t)⁻¹) (Icc 0 β) := by
  intro t ht
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [← continuousWithinAt_sdiff_self]
    have hzero : -(Real.log (0 : ℝ))⁻¹ = 0 := by simp
    rw [ContinuousWithinAt, hzero]
    have hlim : Tendsto (fun t : ℝ ↦ -(Real.log t)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        Real.tendsto_log_nhdsGT_zero.inv_tendsto_atBot
      simpa using h1.neg
    have hsub : (Icc (0 : ℝ) β \ {0}) ⊆ Ioi 0 := fun s hs ↦ lt_of_le_of_ne hs.1.1 (Ne.symm hs.2)
    exact hlim.mono_left (nhdsWithin_mono 0 hsub)
  · refine ContinuousAt.continuousWithinAt ?_
    have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hne : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hpos (ne_of_lt (lt_of_le_of_lt ht.2 hβ1))
    exact ((Real.continuousAt_log ht0).inv₀ hne).neg

/-- The radial integrand `1/(r log^2 r)` of Example 7.2.6 is integrable on `(0, β)` for
`0 < β < 1`, although it is unbounded at the origin: its antiderivative `-1/log r` is continuous
and monotone there. -/
theorem integrableOn_inv_mul_log_sq {β : ℝ} (hβ1 : β < 1) :
    IntegrableOn (fun y : ℝ ↦ (y * Real.log y ^ 2)⁻¹) (Ioo 0 β) := by
  have hd : ∀ y ∈ Ioo (0 : ℝ) β, HasDerivAt (fun t : ℝ ↦ -(Real.log t)⁻¹)
      (y * Real.log y ^ 2)⁻¹ y := fun y hy ↦
    hasDerivAt_neg_inv_log hy.1
      (Real.log_ne_zero_of_pos_of_ne_one hy.1 (ne_of_lt (lt_trans hy.2 hβ1)))
  have hpos : ∀ y ∈ Ioo (0 : ℝ) β, 0 ≤ (y * Real.log y ^ 2)⁻¹ := fun y hy ↦ by
    have := hy.1
    positivity
  exact (intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_neg_inv_log hβ1) hd
    hpos).mono_set Ioo_subset_Ioc_self

/-- **The radial integral of Example 7.2.6**: `∫_0^β dr/(r log^2 r) = -1/log β` for
`0 < β < 1`. -/
theorem integral_inv_mul_log_sq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∫ y in Ioo (0 : ℝ) β, (y * Real.log y ^ 2)⁻¹ = -(Real.log β)⁻¹ := by
  have hd : ∀ y ∈ Ioo (0 : ℝ) β, HasDerivAt (fun t : ℝ ↦ -(Real.log t)⁻¹)
      (y * Real.log y ^ 2)⁻¹ y := fun y hy ↦
    hasDerivAt_neg_inv_log hy.1
      (Real.log_ne_zero_of_pos_of_ne_one hy.1 (ne_of_lt (lt_trans hy.2 hβ1)))
  have hint : IntervalIntegrable (fun y : ℝ ↦ (y * Real.log y ^ 2)⁻¹) volume 0 β := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hβ0.le]
    exact integrableOn_inv_mul_log_sq hβ1
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hβ0.le
    (continuousOn_neg_inv_log hβ1) hd hint
  rw [intervalIntegral.integral_of_le hβ0.le, integral_Ioc_eq_integral_Ioo] at hsub
  rw [hsub]
  simp

/-- The function `v(x) = log(log(1/|x|))` of Example 7.2.6, written with `log(1/r) = -log r`. -/
noncomputable def logLogNorm (x : EuclideanSpace ℝ (Fin 2)) : ℝ := Real.log (-Real.log ‖x‖)

/-- `logLogNorm` is the `v(x) = log(log(1/r))`, `r = |x|`, of Example 7.2.6. -/
theorem logLogNorm_eq (x : EuclideanSpace ℝ (Fin 2)) :
    logLogNorm x = Real.log (Real.log (1 / ‖x‖)) := by
  rw [logLogNorm, one_div, Real.log_inv]

/-- The classical gradient of `v(x) = log(log(1/|x|))` away from the origin, as a linear
functional: `h ↦ ⟪x, h⟫ / (|x|^2 log|x|)`. Its norm is `1/(|x| log(1/|x|))`. -/
noncomputable def logLogNormGrad (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (‖x‖ ^ 2 * Real.log ‖x‖)⁻¹ • innerSL ℝ x

/-- Away from the origin and inside the unit ball, `logLogNormGrad` is the classical derivative of
`logLogNorm`. -/
theorem hasFDerivAt_logLogNorm {x : EuclideanSpace ℝ (Fin 2)} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) :
    HasFDerivAt logLogNorm (logLogNormGrad x) x := by
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg hn hx1
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x :=
    hasFDerivAt_norm_of_ne_zero hx0
  have hl : HasDerivAt Real.log ‖x‖⁻¹ ‖x‖ := Real.hasDerivAt_log hn.ne'
  have hl3 : HasDerivAt Real.log (-Real.log ‖x‖)⁻¹ (-Real.log ‖x‖) :=
    Real.hasDerivAt_log (by linarith)
  have hneg : HasDerivAt (fun t : ℝ ↦ -Real.log t) (-‖x‖⁻¹) ‖x‖ := hl.neg
  have h2 : HasDerivAt (fun t : ℝ ↦ Real.log (-Real.log t))
      ((-Real.log ‖x‖)⁻¹ * -‖x‖⁻¹) ‖x‖ := by
    simpa [Function.comp_def] using hl3.comp ‖x‖ hneg
  have h3 := h2.comp_hasFDerivAt x h1
  have hcoef : ((-Real.log ‖x‖)⁻¹ * -‖x‖⁻¹) • (‖x‖⁻¹ • innerSL ℝ x) = logLogNormGrad x := by
    rw [logLogNormGrad, smul_smul]
    congr 1
    field_simp
  rw [hcoef] at h3
  exact h3

/-- `|∇v|^2 = 1/(|x|^2 log^2 |x|)` for `v(x) = log(log(1/|x|))`; the identity holds at the origin
too, both sides being `0` there under Lean's conventions. -/
theorem sq_norm_logLogNormGrad (x : EuclideanSpace ℝ (Fin 2)) :
    ‖logLogNormGrad x‖ ^ 2 = (‖x‖ ^ 2 * Real.log ‖x‖ ^ 2)⁻¹ := by
  have h : ‖logLogNormGrad x‖ = |(‖x‖ ^ 2 * Real.log ‖x‖)⁻¹| * ‖x‖ := by
    rw [logLogNormGrad, norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
  rw [h, mul_pow, sq_abs, inv_pow, mul_pow]
  rcases eq_or_ne (Real.log ‖x‖) 0 with hL | hL
  · simp [hL]
  rcases eq_or_ne ‖x‖ 0 with hn | hn
  · simp [hn]
  field_simp

/-- `|∇v|^2` is integrable on `B(0, β) ⊆ ℝ^2` for `0 < β < 1`, by the radial computation. -/
theorem integrableOn_sq_norm_logLogNormGrad {β : ℝ} (hβ1 : β < 1) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin 2) ↦ ‖logLogNormGrad x‖ ^ 2)
      (ball 0 β) volume := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  rw [show (fun x : EuclideanSpace ℝ (Fin 2) ↦ ‖logLogNormGrad x‖ ^ 2)
      = fun x : EuclideanSpace ℝ (Fin 2) ↦ (‖x‖ ^ 2 * Real.log ‖x‖ ^ 2)⁻¹ from
    funext sq_norm_logLogNormGrad]
  refine (integrableOn_fun_norm_addHaar volume
    (f := fun y : ℝ ↦ (y ^ 2 * Real.log y ^ 2)⁻¹)).2 ?_
  rw [hfr]
  refine (integrableOn_inv_mul_log_sq hβ1).congr_fun (fun y hy ↦ ?_) measurableSet_Ioo
  simp only [smul_eq_mul]
  rcases eq_or_ne (Real.log y) 0 with hL | hL
  · simp [hL]
  · have hy0 : y ≠ 0 := ne_of_gt hy.1
    field_simp
    ring

/-- **The gradient integral of Example 7.2.6**: on `Ω = B(0,β) ⊆ ℝ^2` with `0 < β < 1`,
`∫_Ω |∇v|^2 dx = -2π/log β`, where `v(x) = log(log(1/|x|))`. -/
theorem integral_sq_norm_logLogNormGrad {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) β, ‖logLogNormGrad x‖ ^ 2)
      = -(2 * π) / Real.log β := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  have hlogβ : Real.log β ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hβ0 (ne_of_lt hβ1)
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (ball 0 1) = π := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_two]
    simp [Real.pi_nonneg]
  set F : ℝ → ℝ := (Iio β).indicator (fun y ↦ (y ^ 2 * Real.log y ^ 2)⁻¹) with hFdef
  have hind : ∀ x : EuclideanSpace ℝ (Fin 2),
      (ball (0 : EuclideanSpace ℝ (Fin 2)) β).indicator
        (fun x ↦ ‖logLogNormGrad x‖ ^ 2) x = F ‖x‖ := by
    intro x
    by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) β
    · have hlt : ‖x‖ ∈ Iio β := mem_ball_zero_iff.1 hx
      rw [indicator_of_mem hx, hFdef, indicator_of_mem hlt, sq_norm_logLogNormGrad]
    · have hlt : ‖x‖ ∉ Iio β := fun h ↦ hx (mem_ball_zero_iff.2 h)
      rw [indicator_of_notMem hx, hFdef, indicator_of_notMem hlt]
  have hstep : ∀ y : ℝ, y ^ (2 - 1) • F y
      = (Iio β).indicator (fun t : ℝ ↦ (t * Real.log t ^ 2)⁻¹) y := by
    intro y
    by_cases hy : y ∈ Iio β
    · rw [hFdef, indicator_of_mem hy, indicator_of_mem hy]
      simp only [smul_eq_mul]
      rcases eq_or_ne (Real.log y) 0 with hL | hL
      · simp [hL]
      rcases eq_or_ne y 0 with hy0 | hy0
      · simp [hy0]
      field_simp
      ring
    · rw [hFdef, indicator_of_notMem hy, indicator_of_notMem hy, smul_zero]
  calc (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) β, ‖logLogNormGrad x‖ ^ 2)
      = ∫ x : EuclideanSpace ℝ (Fin 2), F ‖x‖ := by
        rw [← integral_indicator measurableSet_ball]
        exact integral_congr_ae (Filter.Eventually.of_forall hind)
    _ = finrank ℝ (EuclideanSpace ℝ (Fin 2)) •
          (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (ball 0 1) •
          ∫ y in Ioi (0 : ℝ), y ^ (finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1) • F y :=
        integral_fun_norm_addHaar volume F
    _ = 2 * (π * ∫ y in Ioo (0 : ℝ) β, (y * Real.log y ^ 2)⁻¹) := by
        have hIJ : (∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • F y)
            = ∫ y in Ioo (0 : ℝ) β, (y * Real.log y ^ 2)⁻¹ := by
          rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ ↦ hstep y),
            setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
        rw [hfr, hvol, hIJ, nsmul_eq_mul, smul_eq_mul]
        norm_num
    _ = -(2 * π) / Real.log β := by
        rw [integral_inv_mul_log_sq hβ0 hβ1]
        field_simp

/-- `log(1/r) ≤ 4 r^{-1/4}` for every `r > 0`: the logarithm grows more slowly than any power.
Only `0 < r < 1` is used below, where both sides are positive. -/
theorem neg_log_le_rpow {r : ℝ} (hr0 : 0 < r) : -Real.log r ≤ 4 * r ^ (-1 / 4 : ℝ) := by
  have hs : (0 : ℝ) < r ^ (-1 / 4 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hlog : Real.log (r ^ (-1 / 4 : ℝ)) = (-1 / 4 : ℝ) * Real.log r := Real.log_rpow hr0 _
  have h1 : Real.log (r ^ (-1 / 4 : ℝ)) ≤ r ^ (-1 / 4 : ℝ) - 1 := Real.log_le_sub_one_of_pos hs
  rw [hlog] at h1
  linarith

/-- On `B(0, β)` with `0 < β < 1` the function `v(x) = log(log(1/|x|))` of Example 7.2.6 is
dominated by the power `|x|^{-1/4}`, which is what puts it in `L^2` and makes its integral over a
small ball `o(δ)`. -/
theorem abs_logLogNorm_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) β,
      |logLogNorm x| ≤ (4 + |Real.log (-Real.log β)|) * ‖x‖ ^ (-1 / 4 : ℝ) := by
  intro x hx
  have hxb : ‖x‖ < β := mem_ball_zero_iff.1 hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [logLogNorm]
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
  have hn1 : ‖x‖ < 1 := lt_trans hxb hβ1
  have hlogx : Real.log ‖x‖ < 0 := Real.log_neg hn hn1
  have hlogβ : Real.log β < 0 := Real.log_neg hβ0 hβ1
  have hmono : Real.log (-Real.log β) ≤ Real.log (-Real.log ‖x‖) :=
    Real.log_le_log (by linarith) (by
      have := Real.log_le_log hn hxb.le
      linarith)
  have hupper : logLogNorm x ≤ -Real.log ‖x‖ := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < -Real.log ‖x‖ by linarith)
    simpa [logLogNorm] using this.trans (by linarith)
  have hpow : (1 : ℝ) ≤ ‖x‖ ^ (-1 / 4 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hn hn1.le (by norm_num)
  have habs : |Real.log (-Real.log β)| ≤ |Real.log (-Real.log β)| * ‖x‖ ^ (-1 / 4 : ℝ) :=
    le_mul_of_one_le_right (abs_nonneg _) hpow
  rw [abs_le]
  constructor
  · have : -|Real.log (-Real.log β)| ≤ logLogNorm x :=
      le_trans (neg_abs_le _) hmono
    nlinarith [abs_nonneg (Real.log (-Real.log β)), Real.rpow_nonneg hn.le (-1 / 4 : ℝ)]
  · calc logLogNorm x ≤ -Real.log ‖x‖ := hupper
      _ ≤ 4 * ‖x‖ ^ (-1 / 4 : ℝ) := neg_log_le_rpow hn
      _ ≤ (4 + |Real.log (-Real.log β)|) * ‖x‖ ^ (-1 / 4 : ℝ) := by
          have := abs_nonneg (Real.log (-Real.log β))
          nlinarith [Real.rpow_nonneg hn.le (-1 / 4 : ℝ)]

/-- `v(x) = log(log(1/|x|))` is measurable. -/
theorem measurable_logLogNorm : Measurable logLogNorm :=
  Real.measurable_log.comp (Real.measurable_log.comp measurable_norm).neg

/-- `∇v` is measurable. -/
theorem aestronglyMeasurable_logLogNormGrad (μ : Measure (EuclideanSpace ℝ (Fin 2))) :
    AEStronglyMeasurable logLogNormGrad μ :=
  AEStronglyMeasurable.smul
    (((measurable_norm.pow_const 2).mul (Real.measurable_log.comp measurable_norm)).inv
      ).aestronglyMeasurable
    (innerSL ℝ).continuous.aestronglyMeasurable

/-- The restriction of Lebesgue measure to a ball is finite. -/
theorem isFiniteMeasure_restrict_ball (β : ℝ) :
    IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) β)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩

/-- **`v ∈ L^2(Ω)` in Example 7.2.6**: the function `v(x) = log(log(1/|x|))` lies in `L^2(B(0,β))`
for `0 < β < 1`, being dominated there by `|x|^{-1/4}`. -/
theorem memLp_logLogNorm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    MemLp logLogNorm 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) β)) := by
  have hpow : MemLp (fun x : EuclideanSpace ℝ (Fin 2) ↦ ‖x‖ ^ (-1 / 4 : ℝ)) 2
      (volume.restrict (ball 0 1)) :=
    (example_7_2_5_memLp (d := 2) two_pos (-1 / 4) 2 (by norm_num) (by norm_num)).2 (by norm_num)
  have hpowβ : MemLp (fun x : EuclideanSpace ℝ (Fin 2) ↦
      (4 + |Real.log (-Real.log β)|) * ‖x‖ ^ (-1 / 4 : ℝ)) 2
      (volume.restrict (ball 0 β)) :=
    (hpow.mono_measure (Measure.restrict_mono (ball_subset_ball hβ1.le) le_rfl)).const_mul _
  refine hpowβ.of_le measurable_logLogNorm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 + |Real.log (-Real.log β)|) * ‖x‖ ^ (-1 / 4 : ℝ))]
  exact abs_logLogNorm_le hβ0 hβ1 x hx

/-- **`∇v ∈ L^2(Ω)` in Example 7.2.6**, which is the finiteness of the displayed integral. -/
theorem memLp_logLogNormGrad {β : ℝ} (hβ1 : β < 1) :
    MemLp logLogNormGrad 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) β)) :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_logLogNormGrad _)).2
    (integrableOn_sq_norm_logLogNormGrad hβ1)

/-- `v` is integrable on `B(0, β)`, hence locally integrable there. -/
theorem integrableOn_logLogNorm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntegrableOn logLogNorm (ball (0 : EuclideanSpace ℝ (Fin 2)) β) volume := by
  have := isFiniteMeasure_restrict_ball β
  exact (memLp_logLogNorm hβ0 hβ1).integrable one_le_two

/-- `∇v` is integrable on `B(0, β)`, hence locally integrable there. -/
theorem integrableOn_logLogNormGrad {β : ℝ} (hβ1 : β < 1) :
    IntegrableOn logLogNormGrad (ball (0 : EuclideanSpace ℝ (Fin 2)) β) volume := by
  have := isFiniteMeasure_restrict_ball β
  exact (memLp_logLogNormGrad hβ1).integrable one_le_two

/-- **The step Example 7.2.6 needs and the book passes over**: the classical gradient of
`v(x) = log(log(1/|x|))` on `Ω ∖ {0}` is its weak gradient on all of `Ω = B(0,β)`, the origin
included.

The backbone statement is `hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton` of
`Numlib/Analysis/Sobolev/RemovableSingularity.lean`; its smallness hypothesis
`∫_{B(0,δ)} |v| = o(δ)` holds because `|v| ≤ C |x|^{-1/4}` and `-1/4 > 1 - 2`. -/
theorem hasWeakIteratedLineDerivOn_logLogNorm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {α : Fin 2 → ℕ} {i₀ : Fin 2} (hα : ∑ i, α i = 1) (hi₀ : ∀ i, α i ≠ 0 → i = i₀) :
    HasWeakIteratedLineDerivOn (multiIndexTuple (stdBasis 2) α) logLogNorm
      (fun x ↦ logLogNormGrad x (stdBasis 2 i₀)) ⟨ball 0 β, isOpen_ball⟩ volume := by
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  refine hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton hα
    (fun j ↦ multiIndexTuple_of_sum_eq_one hi₀ j)
    (fun x _ ↦ ⟨_, self_mem_nhdsWithin, integrableOn_logLogNorm hβ0 hβ1⟩)
    (fun x _ ↦ ⟨_, self_mem_nhdsWithin, integrableOn_logLogNormGrad hβ1⟩)
    (fun x hx hx0 ↦ hasFDerivAt_logLogNorm hx0
      (lt_trans (mem_ball_zero_iff.1 hx) hβ1)) ?_
  refine tendsto_inv_mul_setIntegral_norm_ball_zero (by omega)
    (C := 4 + |Real.log (-Real.log β)|) (s := (-1 / 4 : ℝ)) (R := β) hβ0
    (by rw [hfr]; norm_num) measurable_logLogNorm.aestronglyMeasurable fun x hx ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_logLogNorm_le hβ0 hβ1 x hx

/-- `v` is unbounded near the origin: it exceeds every constant somewhere in `B(0,β)`. -/
theorem unbounded_logLogNorm {β : ℝ} (hβ0 : 0 < β) (C : ℝ) :
    ∃ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) β, C < logLogNorm x := by
  set r : ℝ := min (β / 2) (Real.exp (-(Real.exp (C + 1)))) with hrdef
  have hr0 : 0 < r := lt_min (by linarith) (Real.exp_pos _)
  have hrβ : r < β := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hnorm : ‖r • stdBasis 2 (0 : Fin 2)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    simp [stdBasis]
  refine ⟨r • stdBasis 2 (0 : Fin 2), by rw [mem_ball_zero_iff, hnorm]; exact hrβ, ?_⟩
  rw [logLogNorm, hnorm]
  have hle : r ≤ Real.exp (-(Real.exp (C + 1))) := min_le_right _ _
  have hlogr : Real.log r ≤ -(Real.exp (C + 1)) := by
    calc Real.log r ≤ Real.log (Real.exp (-(Real.exp (C + 1)))) := Real.log_le_log hr0 hle
      _ = -(Real.exp (C + 1)) := Real.log_exp _
  have h2 : C + 1 ≤ Real.log (-Real.log r) := by
    calc C + 1 = Real.log (Real.exp (C + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log (-Real.log r) := Real.log_le_log (Real.exp_pos _) (by linarith)
  linarith

/-- **Example 7.2.6**: on `Ω = B(0, β) ⊆ ℝ^2` with `0 < β < 1` the function
`v(x) = log(log(1/|x|))` has `∫_Ω |∇v|^2 dx = -2π/log β < ∞` and `‖v‖_{L^2(Ω)} < ∞`, so that
`v ∈ H^1(Ω)`, while `v` is unbounded near the origin: an `H^1` function of the plane need not be
continuous.

The five clauses are, in order: that `logLogNormGrad` really is the classical gradient `∇v` on
`Ω ∖ {0}`, so that the next clause says what it appears to; the value of the gradient integral; the
finiteness of the `L^2` norm; membership of `H^1(Ω) = W^{1,2}(Ω)` in the sense of Definition 7.2.2;
and unboundedness. The step the book leaves implicit — that the classical gradient on `Ω ∖ {0}` is
the weak gradient on all of `Ω` — is `hasWeakIteratedLineDerivOn_logLogNorm`. -/
theorem example_7_2_6 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) β, x ≠ 0 →
        HasFDerivAt logLogNorm (logLogNormGrad x) x) ∧
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) β, ‖logLogNormGrad x‖ ^ 2)
        = -(2 * π) / Real.log β ∧
      MemLp logLogNorm 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) β)) ∧
      definition_7_2_2_multiIndex 1 2 ⟨ball 0 β, isOpen_ball⟩ logLogNorm ∧
      ∀ C : ℝ, ∃ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) β, C < logLogNorm x := by
  refine ⟨fun x hx hx0 ↦ hasFDerivAt_logLogNorm hx0 (lt_trans (mem_ball_zero_iff.1 hx) hβ1),
    integral_sq_norm_logLogNormGrad hβ0 hβ1, memLp_logLogNorm hβ0 hβ1,
    ⟨memLp_logLogNorm hβ0 hβ1, fun α hαle ↦ ?_⟩, fun C ↦ unbounded_logLogNorm hβ0 C⟩
  rcases Nat.eq_zero_or_pos (∑ i, α i) with hα0 | hα1
  · exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero hα0 _
      (fun x _ ↦ ⟨_, self_mem_nhdsWithin, integrableOn_logLogNorm hβ0 hβ1⟩),
      memLp_logLogNorm hβ0 hβ1⟩
  · have hα : ∑ i, α i = 1 := le_antisymm hαle hα1
    obtain ⟨i₀, hi₀⟩ := exists_index_of_sum_eq_one hα
    refine ⟨_, hasWeakIteratedLineDerivOn_logLogNorm hβ0 hβ1 hα hi₀, ?_⟩
    refine (memLp_logLogNormGrad hβ1).of_le
      ((aestronglyMeasurable_logLogNormGrad _).apply_continuousLinearMap _)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    have h1 : ‖logLogNormGrad x (stdBasis 2 i₀)‖
        ≤ ‖logLogNormGrad x‖ * ‖stdBasis 2 i₀‖ := ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖stdBasis 2 i₀‖ = 1 := by simp [stdBasis]
    rw [h2, mul_one] at h1
    exact h1

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
