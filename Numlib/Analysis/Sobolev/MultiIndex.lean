/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Space.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Operator.ClosedGraph
import Numlib.Analysis.Sobolev.Space
import Numlib.MeasureTheory.Function.LpSpace.Duality

/-!
# `W^{k,p}(Ω)` indexed by multi-indices, and `H^k(Ω)` as a Hilbert space

`SobolevMultiIndex F b k p Ω μ` is the Sobolev space `W^{k,p}(Ω)` of Atkinson and Han, *Theoretical
Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Definition 7.2.2, with the weak
derivatives indexed by the multi-indices `α` of the basis `b`, one `L^p(Ω)` function `∂^α v` for
each `α` with `|α| ≤ k`, and carrying the norm

`‖v‖_{k,p,Ω} = [∑_{|α| ≤ k} ‖∂^α v‖_{L^p(Ω)}^p]^{1/p}`,  `max_{|α| ≤ k} ‖∂^α v‖_{L^∞(Ω)}` for
`p = ∞`,

which is the formula Atkinson–Han display there. `Numlib/Analysis/Sobolev/Space.lean` carries the
same space with all the derivatives of a given order collected into one tensor of
`E [×n]→L[ℝ] F` measured in its operator norm; the two norms are equivalent but not equal, and the
difference matters at `p = 2`, where only the norm here is induced by an inner product once
`k ≥ 2` and `dim E ≥ 2`.

## Main definitions

* `MultiIndexLE ι k`, the multi-indices `α : ι → ℕ` with `|α| = ∑ i, α i ≤ k`, and
  `MultiIndexEq ι k`, those of order exactly `k`;
* `multiIndexDirections b α` and `multiIndexTuple b α`, the `|α|` directions naming `∂^α` — the
  basis vector `b i` repeated `α i` times, the indices in increasing order — as a list and as a
  tuple, so that `∂^α v` is the weak derivative of `v` along `multiIndexTuple b α` in the sense of
  `HasWeakIteratedLineDerivOn`, and `multiIndexCount m`, the multi-index of a tuple `m` of basis
  indices, which counts how often each index occurs in it;
* `basisCoordProd b m`, the continuous multilinear form `y ↦ ∏ j, (b.repr (y j)) (m j)`, with which
  a continuous multilinear map is assembled from its values on tuples of basis vectors;
* `SobolevMultiIndexTuple F ι k p Ω μ`, the ambient space: the `ℓ^p` product over the multi-indices
  `α` with `|α| ≤ k` of the spaces `L^p(Ω)`, with `SobolevMultiIndexTuple.fn` the function a tuple
  carries, namely its component at `α = 0`;
* `SobolevMultiIndex F b k p Ω μ`, the Sobolev space itself, a submodule of that product, with
  `SobolevMultiIndex.fn` and `SobolevMultiIndex.weakDeriv`;
* `MemSobolevMultiIndex b f k p Ω μ`, the same space as a predicate on functions, with
  `MemSobolevMultiIndex.congr_ae` saying that it only sees the function up to a null set of `Ω`;
* `SobolevMultiIndex.testFunctions F b k p Ω μ`, the image of the test functions `C_0^∞(Ω)` in
  `W^{k,p}(Ω)`, and `SobolevMultiIndexZero F b k p Ω μ`, its closure, the space `W_0^{k,p}(Ω)`
  of Atkinson–Han, Definition 7.2.9, in the multi-index formulation — a closed subspace, hence a
  Hilbert space at `p = 2`, which is what `Numlib/Analysis/Sobolev/Interval.lean` takes as
  `H^1_0(a, b)`;
* `MultiIndexLE.single i`, the multi-index `e_i` of the partial derivative `∂_i`,
  `MultiIndexLE.singleLE i` its copy at order `k + 1` and `MultiIndexLE.addSingle i α` the
  multi-index `α + e_i`;
  `SobolevMultiIndex.weakDerivL α` and `SobolevMultiIndex.fnL`, the weak derivative `u ↦ ∂^α u`
  and the inclusion `W^{k,p}(Ω) → L^p(Ω)` as bounded linear maps, with
  `SobolevMultiIndexZero.fnL` the inclusion of `W_0^{k,p}(Ω)`; `SobolevMultiIndex.grad` and
  `SobolevMultiIndex.gradNorm`, the gradient `(∂_i u)_i` of `u ∈ W^{1,p}(Ω)` and its `ℓ^p` norm
  `‖∇u‖_{L^p(Ω)}`;
* `SobolevEuclidean N k p Ω` and `SobolevEuclideanZero N k p Ω`, the spaces `W^{k,p}(Ω)` and
  `W_0^{k,p}(Ω)` of Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
  Equations*, §9.1 and §9.4, on an open `Ω ⊆ ℝ^N` with the standard basis and Lebesgue measure.

## Main statements

* `SobolevMultiIndex.isClosed` and `SobolevMultiIndex.instCompleteSpace`: **`W^{k,p}(Ω)` is a
  Banach space for the norm of Definition 7.2.2**, Atkinson–Han, Theorem 7.2.3; the argument is the
  one of `Sobolev.isClosed`, the integration by parts formula pairing the functions against a fixed
  test function and that pairing being continuous on `L^p(Ω)` by Hölder's inequality;
* `SobolevMultiIndex.norm_eq_sum` and `SobolevMultiIndex.norm_eq_ciSup`: the norm of the type is
  the norm Atkinson–Han display in Definition 7.2.2, with no rewriting of the indexing;
* `SobolevMultiIndex.inner_eq`: **at `p = 2` the norm comes from the inner product
  `(u, v)_k = ∫_Ω ∑_{|α| ≤ k} ⟪∂^α u, ∂^α v⟫`**, so `H^k(Ω) = W^{k,2}(Ω)` is a Hilbert space:
  Atkinson–Han, Corollary 7.2.4. The inner product is not built here; it is the one that
  `PiLp 2` of `L^2(Ω)` spaces carries, restricted to a submodule, and the theorem is that it is the
  book's formula;
* `SobolevMultiIndex.memSobolevMultiIndex`, `MemSobolevMultiIndex.exists_sobolevMultiIndex` and
  `SobolevMultiIndex.ext_of_fn_ae_eq`: the type and the predicate describe the same functions, each
  function coming from exactly one element;
* `memSobolev_iff_memSobolevMultiIndex`, with its two halves `MemSobolev.memSobolevMultiIndex` and
  `MemSobolevMultiIndex.memSobolev`: **the tensor formulation of `W^{k,p}(Ω)` in
  `Numlib/Analysis/Sobolev/Domain.lean` and the multi-index formulation here describe the same
  functions** — one way the `∂^α` are the tensor derivative evaluated at the tuple naming `α`, the
  other way the tensor is assembled from the `∂^α`, and the symmetry of the iterated derivative of
  a `C^∞` function, `ContDiff.iteratedFDeriv_congr_perm` of
  `Numlib/Analysis/Calculus/IteratedFDeriv.lean`, is what lets it be evaluated at an unsorted tuple
  of basis vectors;
* `HasWeakIteratedLineDerivOn.of_perm`, `.cons'` and `.of_cons'`: a weak derivative along a tuple
  of directions is one along every rearrangement of the tuple, and the new direction of a longer
  tuple may be differentiated first as well as last; hence `memSobolevMultiIndex_succ_iff`, **the
  inductive definition `W^{m+1,p} = {u ∈ W^{m,p} : ∂_i u ∈ W^{m,p} ∀ i}` of Brezis agrees with
  the multi-index one**;
* `SobolevMultiIndex.norm_eq_gradNorm` and `SobolevMultiIndex.gradNorm_le_norm`: the norm of
  `W^{1,p}(Ω)` is the `ℓ^p` sum of `‖u‖_p` and `‖∇u‖_p`, and the gradient norm is a seminorm
  bounded by it;
* `SobolevMultiIndex.instSecondCountableTopology`: **`W^{k,p}(Ω)` is separable for
  `1 ≤ p < ∞`** on a second countable Borel space with a σ-finite measure, Brezis's
  Proposition 9.1; reflexivity for `1 < p < ∞` waits on the reflexivity of a finite `ℓ^p` product
  (`NormedSpace.instIsReflexivePiLp`).

## Implementation notes

### Why a second formulation of the same space

The norm of Atkinson–Han's Definition 7.2.2 sums over the multi-indices `α`, and
`Numlib/Analysis/Sobolev/Space.lean` sums over the orders `n = |α|` instead, measuring all the
derivatives of order `n` by the operator norm of one tensor of `E [×n]→L[ℝ] F`. On a
finite-dimensional `E` the two are equivalent, the derivative tensors of a Sobolev function being
symmetric, so mathematically they give the same space and the same topology and either will do for
a Banach space statement. That they contain the same functions is
`MemSobolev.memSobolevMultiIndex` and `MemSobolevMultiIndex.memSobolev` below; that the two norms
are equivalent is not formalized here, and the two formulations remain separate types with separate
proofs.

They are not equal, and at `p = 2` that is the whole difference between a Banach space and a
Hilbert space, once `k ≥ 2` and `dim E ≥ 2`: the operator norm on `E [×n]→L[ℝ] F` fails the
parallelogram law as soon as `n ≥ 2` and `dim E ≥ 2` — for `E = ℝ²` and `F = ℝ` it is the spectral
norm of a `2 × 2` matrix — so no inner product induces it, while the norm here is the `ℓ²` norm of a
finite product of `L²` spaces and its inner product is Atkinson–Han's. (For `k ≤ 1`, or for
`dim E ≤ 1`, the other formulation is an inner product space too; the obstruction is about
derivatives of order two and higher in two or more variables.) Atkinson–Han's Corollary 7.2.4 is
therefore a statement about *this* formulation, and is obtained here from Mathlib's inner product
on `PiLp 2` and on `L²` with nothing added.

The price of the multi-index indexing is that it depends on the basis `b`: unlike the operator norm
of the tensor, `∑_{|α| = n} ‖∂^α v‖²` is not invariant under rotations of `E` once `n ≥ 2`, since
for `E = ℝ²` and `n = 2` it is the sum of the squares of the three distinct entries of the Hessian
and not of its four entries. The book works in the coordinates of `ℝ^d` throughout and so has a
basis fixed; here the basis is an explicit argument.

### The relation to the tensor formulation

`MemSobolev.memSobolevMultiIndex` sends the tensor formulation into this one: the tensor derivative
of order `|α|` evaluated at `multiIndexTuple b α` is `∂^α`, and
`MemSobolevMultiIndex.memSobolev` is the converse — a function with all the `∂^α` in `L^p(Ω)`
has the tensor derivatives too. The proof of the converse recovers the tensor of order `n` from its
values on the tuples of basis vectors, `basisCoordProd` carrying the extension by multilinearity.
The values on a tuple of basis vectors that is not sorted
are `∂^α` of the *reordered* tuple, so the argument needs the symmetry of `iteratedFDeriv ℝ n φ x`
under permutations of its arguments for a `C^∞` function `φ`. Mathlib has that symmetry for `n = 2`
(`ContDiffAt.isSymmSndFDerivAt`) and for analytic functions of any order
(`ContDiffAt.domDomCongr_iteratedFDeriv`, which needs `ω`-smoothness) but not for `C^∞` functions of
order `n ≥ 3`, and a test function is not analytic; `ContDiff.iteratedFDeriv_congr_perm` of
`Numlib/Analysis/Calculus/IteratedFDeriv.lean` supplies it, by transporting the commutation of two
directional derivatives along a `List.Perm`. Only the functions are matched, not the norms.

### Upstream

Like `Numlib/Analysis/Sobolev/WeakDeriv.lean`, `Numlib/Analysis/Sobolev/Domain.lean` and
`Numlib/Analysis/Sobolev/Space.lean`, this file stands in for Mathlib PR 32305 and its continuation
`grunweg/SobolevSlobodeckij` (Michael Rothgang, Filippo Nuccio and Floris van Doorn). It moves
*away* from that API rather than towards it: there, as in the companion files, the weak derivative
is tensor-valued and carries no basis. Nothing here is expected to migrate by a rename; what should
survive a migration is the observation that the Hilbert space structure of `H^k(Ω)` needs the
multi-index indexing, and the shape of the argument, which is `PiLp 2` of `L²` spaces and a closed
submodule of it.
-/

open Filter MeasureTheory Module Set TopologicalSpace

open scoped ContDiff Distributions ENNReal Topology

/-! ### Multi-indices -/

section MultiIndex

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-- The multi-indices of order at most `k` over the finite index type `ι`: the functions
`α : ι → ℕ` with `|α| = ∑ i, α i ≤ k`. -/
abbrev MultiIndexLE (ι : Type*) [Fintype ι] (k : ℕ) : Type _ := {α : ι → ℕ // ∑ i, α i ≤ k}

namespace MultiIndexLE

/-- There are finitely many multi-indices of order at most `k`, because every entry of such a
multi-index is at most `k`. -/
noncomputable instance instFintype : Fintype (MultiIndexLE ι k) := by
  classical
  exact Fintype.ofInjective (fun α i ↦ (⟨α.1 i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (f := α.1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
        α.2)⟩ : Fin (k + 1)))
    fun _ _ h ↦ Subtype.ext (funext fun i ↦ congrArg Fin.val (congrFun h i))

/-- The multi-index `0`, of order `0`; the derivative it names is the function itself. -/
instance instZero : Zero (MultiIndexLE ι k) := ⟨⟨0, by simp⟩⟩

/-- The multi-index `0` is the zero function on the index type. -/
@[simp]
theorem coe_zero : ((0 : MultiIndexLE ι k) : ι → ℕ) = 0 := rfl

/-- The order of the multi-index `0` is `0`. Stated for the zero function rather than for
`(0 : MultiIndexLE ι k)` because that is the form in which the order appears. -/
theorem sum_zero : ∑ _i : ι, (0 : ι → ℕ) _i = 0 := by simp

/-- The multi-indices of order at most `k'` embed into those of order at most `k ≥ k'`. -/
theorem castLE_injective {k' : ℕ} (hk : k' ≤ k) :
    Function.Injective fun α : MultiIndexLE ι k' ↦ (⟨α.1, α.2.trans hk⟩ : MultiIndexLE ι k) :=
  fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)


/-! #### The multi-indices of order one -/

section Single

variable [DecidableEq ι]

/-- The multi-index `e_i = Pi.single i 1` of order one, naming the partial derivative `∂_i`:
`SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)` is the book's `∂u/∂x_i`. -/
def single (i : ι) : MultiIndexLE ι 1 := ⟨Pi.single i 1, by simp⟩

/-- The multi-index `e_i` is the function `Pi.single i 1`. -/
@[simp]
theorem coe_single (i : ι) : ((single i : MultiIndexLE ι 1) : ι → ℕ) = Pi.single i 1 := rfl

/-- The multi-index `e_i` determines `i`. -/
theorem single_injective : Function.Injective (single : ι → MultiIndexLE ι 1) := fun i j h ↦ by
  have := congrArg (fun α : MultiIndexLE ι 1 ↦ (α : ι → ℕ) i) h
  by_contra hij
  simp [Pi.single_eq_of_ne hij] at this

/-- The multi-index `e_i` is not the multi-index `0`. -/
theorem single_ne_zero (i : ι) : (single i : MultiIndexLE ι 1) ≠ 0 := fun h ↦ by
  have := congrArg (fun α : MultiIndexLE ι 1 ↦ (α : ι → ℕ) i) h
  simp at this

/-- A multi-index of order at most one is `0` or some `e_i`: it has at most one nonzero entry, and
that entry is `1`. -/
theorem eq_zero_or_exists_eq_single (α : MultiIndexLE ι 1) : α = 0 ∨ ∃ i, α = single i := by
  by_cases h : ∀ i, (α : ι → ℕ) i = 0
  · exact Or.inl (Subtype.ext (funext h))
  right
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine ⟨i, Subtype.ext (funext fun j ↦ ?_)⟩
  have hle : ∑ j, (α : ι → ℕ) j ≤ 1 := α.2
  have hsingle : (α : ι → ℕ) i ≤ ∑ j, (α : ι → ℕ) j :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hαi : (α : ι → ℕ) i = 1 := by omega
  by_cases hj : j = i
  · subst hj
    simp [hαi]
  · have hsum := Finset.add_sum_erase Finset.univ (α : ι → ℕ) (Finset.mem_univ i)
    have hzero : ∑ j ∈ Finset.univ.erase i, (α : ι → ℕ) j = 0 := by omega
    rw [Finset.sum_eq_zero_iff] at hzero
    simp [Pi.single_eq_of_ne hj, hzero j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)]

/-- A sum over the multi-indices of order at most one is the term at `0` plus the sum over the
`e_i`: `∑_{|α| ≤ 1} f α = f 0 + ∑ i, f (e_i)`. This is what turns the norm of `W^{1,p}(Ω)`, a sum
over the multi-indices `α` with `|α| ≤ 1`, into `‖u‖_p` plus the gradient terms. -/
theorem sum_univ_one {M : Type*} [AddCommMonoid M] (f : MultiIndexLE ι 1 → M) :
    ∑ α, f α = f 0 + ∑ i, f (single i) := by
  classical
  rw [Fintype.sum_eq_add_sum_compl 0 f]
  congr 1
  have h : ({0}ᶜ : Finset (MultiIndexLE ι 1)) = Finset.univ.image single := by
    ext α
    simp only [Finset.mem_compl, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨fun hα ↦ ?_, fun ⟨i, hi⟩ ↦ hi ▸ single_ne_zero i⟩
    rcases eq_zero_or_exists_eq_single α with h0 | ⟨i, rfl⟩
    · exact absurd h0 hα
    · exact ⟨i, rfl⟩
  rw [h, Finset.sum_image single_injective.injOn]

/-- The multi-index `α + e_i` of order at most `k + 1`, for `α` of order at most `k`. -/
def addSingle (i : ι) (α : MultiIndexLE ι k) : MultiIndexLE ι (k + 1) :=
  ⟨α.1 + Pi.single i 1, by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    omega⟩

/-- The multi-index underlying `addSingle i α` is `α + e_i`. -/
@[simp]
theorem coe_addSingle (i : ι) (α : MultiIndexLE ι k) :
    ((MultiIndexLE.addSingle i α : MultiIndexLE ι (k + 1)) : ι → ℕ) = α.1 + Pi.single i 1 :=
  rfl

/-- `α ↦ α + e_i` is injective. -/
theorem addSingle_injective (i : ι) :
    Function.Injective (MultiIndexLE.addSingle i : MultiIndexLE ι k → MultiIndexLE ι (k + 1)) :=
  fun _ _ h ↦ Subtype.ext (add_right_cancel (Subtype.mk.inj h))

/-- The multi-index `e_i` of order at most `k + 1`. -/
def singleLE (i : ι) : MultiIndexLE ι (k + 1) :=
  ⟨Pi.single i 1, by simp⟩

/-- `0 + e_i = e_i`. -/
theorem addSingle_zero (i : ι) :
    MultiIndexLE.addSingle i (0 : MultiIndexLE ι k) = MultiIndexLE.singleLE i :=
  Subtype.ext (zero_add _)

end Single

end MultiIndexLE

/-- The multi-indices of order exactly `k` over the finite index type `ι`, as a subtype of the
multi-indices of order at most `k`: the `α` with `|α| = ∑ i, α i = k`. These are the multi-indices
of *top* order, over which the seminorms built from the highest derivatives are summed. -/
abbrev MultiIndexEq (ι : Type*) [Fintype ι] (k : ℕ) : Type _ :=
  {α : MultiIndexLE ι k // ∑ i, α.1 i = k}

/-- There are finitely many multi-indices of order exactly `k`, there being finitely many of order
at most `k`. -/
noncomputable instance MultiIndexEq.instFintype : Fintype (MultiIndexEq ι k) := Fintype.ofFinite _

end MultiIndex

/-! ### The directions naming a multi-index -/

section Directions

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The directions naming the multi-index `α` in the family `b`, as a list: the vector `b i`
repeated `α i` times, the indices `i` taken in increasing order. Differentiating along this list
takes `∂^α = ∂_{i_1}^{α_{i_1}} ⋯ ∂_{i_m}^{α_{i_m}}`. -/
def multiIndexDirections (b : ι → E) (α : ι → ℕ) : List E :=
  (Finset.univ.sort (· ≤ ·)).flatMap fun i ↦ List.replicate (α i) (b i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- There are `|α| = ∑ i, α i` directions naming the multi-index `α`. -/
theorem length_multiIndexDirections (b : ι → E) (α : ι → ℕ) :
    (multiIndexDirections b α).length = ∑ i, α i := by
  rw [multiIndexDirections, List.length_flatMap]
  simp only [List.length_replicate]
  rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq (Finset.univ : Finset ι) (· ≤ ·),
    Multiset.map_coe, Multiset.sum_coe]

/-- The directions naming the multi-index `α` in the family `b`, as a tuple of length `|α|`. The
weak derivative of `v` along this tuple, in the sense of `HasWeakIteratedLineDerivOn`, is the
`α`-th weak derivative `∂^α v`. -/
def multiIndexTuple (b : ι → E) (α : ι → ℕ) : Fin (∑ i, α i) → E :=
  fun j ↦ (multiIndexDirections b α).get (j.cast (length_multiIndexDirections b α).symm)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The directions naming a multi-index, as a list, are the entries of the tuple naming it. -/
theorem multiIndexDirections_eq_ofFn (b : ι → E) (α : ι → ℕ) :
    multiIndexDirections b α = List.ofFn (multiIndexTuple b α) := by
  refine (List.ext_getElem (by simp [length_multiIndexDirections]) fun i h1 h2 ↦ ?_).symm
  simp [multiIndexTuple]

end Directions

/-! ### The multi-index of a tuple of basis indices -/

section Count

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}

/-- The multi-index counting how often each index occurs in a tuple `m` of indices: the derivative
`∂_{b (m 0)} ⋯ ∂_{b (m (n-1))}` is `∂^α` for `α = multiIndexCount m`, once the directions are put
in increasing order. -/
def multiIndexCount (m : Fin n → ι) : ι → ℕ :=
  fun i ↦ {j ∈ (Finset.univ : Finset (Fin n)) | m j = i}.card

/-- The order of the multi-index of a tuple is the length of the tuple. -/
theorem sum_multiIndexCount (m : Fin n → ι) : ∑ i, multiIndexCount m i = n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := m) (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset ι))
    (fun j _ ↦ Finset.mem_univ (m j))
  simpa [multiIndexCount] using h.symm

/-- The directions naming a multi-index, as a multiset: `α i` copies of `b i` for each index `i`,
the sorting that `multiIndexDirections` performs having been forgotten. -/
theorem coe_multiIndexDirections (b : ι → E) (α : ι → ℕ) :
    ((multiIndexDirections b α : List E) : Multiset E)
      = ∑ i, Multiset.replicate (α i) (b i) := by
  rw [multiIndexDirections, ← Multiset.coe_bind]
  simp only [Finset.sort_eq, Multiset.coe_replicate]
  rfl

/-- The entries of a tuple, as a multiset. -/
theorem Multiset.coe_ofFn (g : Fin n → E) :
    ((List.ofFn g : List E) : Multiset E) = ∑ j, ({g j} : Multiset E) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, ← ih (fun j ↦ g j.succ)]
    simp [Multiset.cons_coe]

/-- **A tuple of basis vectors is a permutation of the directions naming a multi-index**, namely of
the multi-index counting the occurrences of each index in the tuple. Both sides have the same
multiset of entries, `b i` occurring `multiIndexCount m i` times. -/
theorem multiIndexDirections_multiIndexCount_perm (b : ι → E) (m : Fin n → ι) :
    (List.ofFn fun j ↦ b (m j)).Perm (multiIndexDirections b (multiIndexCount m)) := by
  rw [← Multiset.coe_eq_coe, Multiset.coe_ofFn, coe_multiIndexDirections,
    ← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset ι))
      (fun j _ ↦ Finset.mem_univ (m j)) (fun j ↦ ({b (m j)} : Multiset E))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_congr rfl (fun j hj ↦ by rw [(Finset.mem_filter.1 hj).2]),
    Finset.sum_const, Multiset.nsmul_singleton]
  rfl

end Count

/-! ### Products over the tuple naming a multi-index -/

section Products

/-- The product of a finite sum of multisets is the product of the products. -/
theorem prod_multiset_sum {ι M : Type*} [CommMonoid M] [Fintype ι] (f : ι → Multiset M) :
    (∑ i, f i).prod = ∏ i, (f i).prod := by
  classical
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Multiset.prod_add, Finset.prod_cons, ih]

/-- A product over the tuple of directions naming a multi-index `α` is the product over the index
type of the `α i`-th powers, the tuple listing `b i` exactly `α i` times. -/
theorem prod_multiIndexTuple {ι E M : Type*} [Fintype ι] [LinearOrder ι] [CommMonoid M]
    (b : ι → E) (α : ι → ℕ) (g : E → M) :
    (∏ j, g (multiIndexTuple b α j)) = ∏ i, (g (b i)) ^ α i := by
  classical
  have h1 : (∏ j, g (multiIndexTuple b α j))
      = ((multiIndexDirections b α).map g : Multiset M).prod := by
    rw [multiIndexDirections_eq_ofFn]
    simp [← List.prod_ofFn, Function.comp_def]
  rw [h1, show ((List.map g (multiIndexDirections b α) : List M) : Multiset M)
      = Multiset.map g ((multiIndexDirections b α : List E) : Multiset E) from rfl,
    coe_multiIndexDirections b α,
    show Multiset.map g (∑ i, Multiset.replicate (α i) (b i))
        = ∑ i, Multiset.replicate (α i) (g (b i)) by
      induction (Finset.univ : Finset ι) using Finset.cons_induction with
      | empty => simp
      | cons a s ha ih =>
        rw [Finset.sum_cons, Multiset.map_add, ih, Finset.sum_cons, Multiset.map_replicate],
    prod_multiset_sum]
  exact Finset.prod_congr rfl fun i _ ↦ Multiset.prod_replicate _ _

end Products

/-! ### Multilinear maps read in a basis -/

section MultilinearBasis

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous `n`-linear form on `E` that reads off the product of the coordinates named by a
tuple `m` of basis indices: `basisCoordProd b m y = ∏ j, (b.repr (y j)) (m j)`.

Together with `ContinuousMultilinearMap.apply_eq_sum_basis` these forms expand a continuous
multilinear map into its values on tuples of basis vectors, and so assemble one from prescribed such
values; the space is finite-dimensional, the basis being indexed by a `Fintype`, so the coordinate
functionals are automatically continuous. -/
noncomputable def basisCoordProd (b : Basis ι ℝ E) {n : ℕ} (m : Fin n → ι) : E [×n]→L[ℝ] ℝ :=
  letI := b.finiteDimensional_of_finite
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
    fun j ↦ (b.coord (m j)).toContinuousLinearMap

/-- `basisCoordProd b m` is the product, over the slots `j`, of the `m j`-th coordinate of the
`j`-th argument. -/
@[simp]
theorem basisCoordProd_apply (b : Basis ι ℝ E) {n : ℕ} (m : Fin n → ι) (y : Fin n → E) :
    basisCoordProd b m y = ∏ j, b.repr (y j) (m j) := by
  have := b.finiteDimensional_of_finite
  rw [basisCoordProd, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  simp

/-- **A continuous multilinear map is determined by its values on tuples of basis vectors**, as the
sum of those values weighted by the products of coordinates: writing each argument in the basis and
expanding by multilinearity. -/
theorem ContinuousMultilinearMap.apply_eq_sum_basis {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (b : Basis ι ℝ E) {n : ℕ} (T : E [×n]→L[ℝ] G) (y : Fin n → E) :
    T y = ∑ m : Fin n → ι, (∏ j, b.repr (y j) (m j)) • T fun j ↦ b (m j) := by
  classical
  have h1 : T y = T fun j ↦ ∑ i, b.repr (y j) i • b i := by
    congr 1
    funext j
    exact (b.sum_repr (y j)).symm
  rw [h1, show (T fun j ↦ ∑ i, b.repr (y j) i • b i)
      = ∑ m : Fin n → ι, T fun j ↦ b.repr (y j) (m j) • b (m j) from
    T.toMultilinearMap.map_sum fun (j : Fin n) (i : ι) ↦ b.repr (y j) i • b i]
  exact Finset.sum_congr rfl fun m _ ↦ T.toMultilinearMap.map_smul_univ _ _

end MultilinearBasis

/-! ### Weak derivatives along a permuted tuple of directions

The defining identity of a weak derivative along a tuple `y` tests against `∂^n φ x y`, and for a
test function `φ` that is symmetric in the entries of `y` (`ContDiff.iteratedFDeriv_congr_perm`).
So a weak derivative along `y` is a weak derivative along every rearrangement of `y`, and the
new direction of a longer tuple may be differentiated first as well as last: this is what lets
the multi-index `∂^{α + e_i}` be read as `∂^α ∂_i` although `multiIndexTuple` lists the directions
in increasing order of the index. -/

section Perm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {μ : Measure E} {f w : E → F}

namespace HasWeakIteratedLineDerivOn

/-- **A weak derivative along a tuple is a weak derivative along every rearrangement of it**: if
the lists of entries of `y₁` and `y₂` are permutations of each other, a weak derivative of `f`
along `y₁` is one along `y₂`. The lengths are not assumed equal; they are, a permutation
preserving the length. -/
theorem of_perm {n₁ n₂ : ℕ} {y₁ : Fin n₁ → E} {y₂ : Fin n₂ → E}
    (hy : (List.ofFn y₁).Perm (List.ofFn y₂)) (h : HasWeakIteratedLineDerivOn y₁ f w Ω μ) :
    HasWeakIteratedLineDerivOn y₂ f w Ω μ := by
  obtain rfl : n₁ = n₂ := by simpa using hy.length_eq
  refine ⟨h.locallyIntegrableOn, h.locallyIntegrableOn_weakDeriv, fun φ ↦ ?_⟩
  have key : ∀ x, iteratedFDeriv ℝ n₁ (φ : E → ℝ) x y₂ = iteratedFDeriv ℝ n₁ (φ : E → ℝ) x y₁ :=
    fun x ↦ (φ.contDiff.iteratedFDeriv_congr_perm hy x).symm
  simp_rw [key]
  exact h.integral_smul_eq φ

/-- A weak derivative along a tuple of directions is a weak derivative along every permutation
of the tuple. -/
theorem comp_perm {n : ℕ} {y : Fin n → E} (h : HasWeakIteratedLineDerivOn y f w Ω μ)
    (σ : Equiv.Perm (Fin n)) : HasWeakIteratedLineDerivOn (y ∘ σ) f w Ω μ :=
  h.of_perm (σ.ofFn_comp_perm y).symm

/-- **The composition rule with the new direction differentiated first**: if `g` is a weak
derivative of `f` along the single direction `z` and `u` is a weak derivative of `g` along the
tuple `y`, then `u` is a weak derivative of `f` along `z :: y`. Where
`HasWeakIteratedLineDerivOn.cons` differentiates along `z` *after* `y`, this differentiates along
`z` *first*; for a test function the two orders agree (`ContDiff.fderiv_iteratedFDeriv_apply`),
which is all the proof uses. -/
theorem cons' {n : ℕ} {y : Fin n → E} {z : E} {g u : E → F}
    (h : HasWeakIteratedLineDerivOn ![z] f g Ω μ) (h' : HasWeakIteratedLineDerivOn y g u Ω μ) :
    HasWeakIteratedLineDerivOn (Fin.cons z y) f u Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv := h'.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ := by
    have e1 : ∀ x, iteratedFDeriv ℝ (n + 1) (φ : E → ℝ) x (Fin.cons z y)
        = iteratedFDeriv ℝ 1 (φ.iteratedFDerivApply n y : E → ℝ) x ![z] := fun x ↦ by
      rw [iteratedFDeriv_one_apply, TestFunction.iteratedFDerivApply_coe,
        φ.contDiff.fderiv_iteratedFDeriv_apply, φ.contDiff.iteratedFDeriv_cons]
      rfl
    simp_rw [e1]
    rw [h.integral_smul_eq]
    simp only [TestFunction.iteratedFDerivApply_coe]
    rw [h'.integral_smul_eq φ, smul_smul]
    congr 1
    ring

/-- **The converse of `HasWeakIteratedLineDerivOn.cons'`**: if `g` is a weak derivative of `f`
along the single direction `z` and `u` is a weak derivative of `f` along `z :: y`, then `u` is a
weak derivative of `g` along `y`. This is what reads `∂^α (∂_i f)` off `∂^{α + e_i} f`. -/
theorem of_cons' {n : ℕ} {y : Fin n → E} {z : E} {g u : E → F}
    (h : HasWeakIteratedLineDerivOn ![z] f g Ω μ)
    (h' : HasWeakIteratedLineDerivOn (Fin.cons z y) f u Ω μ) :
    HasWeakIteratedLineDerivOn y g u Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn_weakDeriv
  locallyIntegrableOn_weakDeriv := h'.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ := by
    have e1 : ∀ x, iteratedFDeriv ℝ (n + 1) (φ : E → ℝ) x (Fin.cons z y)
        = iteratedFDeriv ℝ 1 (φ.iteratedFDerivApply n y : E → ℝ) x ![z] := fun x ↦ by
      rw [iteratedFDeriv_one_apply, TestFunction.iteratedFDerivApply_coe,
        φ.contDiff.fderiv_iteratedFDeriv_apply, φ.contDiff.iteratedFDeriv_cons]
      rfl
    have k1 := h.integral_smul_eq (φ.iteratedFDerivApply n y)
    have k2 := h'.integral_smul_eq φ
    simp_rw [e1] at k2
    rw [k2, pow_one, neg_one_smul] at k1
    simp only [TestFunction.iteratedFDerivApply_coe] at k1
    rw [← neg_neg (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • g x ∂μ), ← k1,
      pow_succ, mul_neg_one, neg_smul, neg_neg]

end HasWeakIteratedLineDerivOn

end Perm

/-! ### The ambient space -/

section Space

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {f : E → F} {k : ℕ} {p : ℝ≥0∞} {Ω : Opens E} {μ : Measure E}

variable (F ι k p Ω μ) in
/-- The ambient space of `W^{k,p}(Ω)` in the multi-index indexing: families `(w_α)_{|α| ≤ k}` of
`L^p(Ω)` functions, carrying the `ℓ^p` sum of their `L^p(Ω)` norms. `W^{k,p}(Ω)` is the subspace of
those families in which `w_α` is the `α`-th weak derivative of `w_0`. -/
abbrev SobolevMultiIndexTuple : Type _ :=
  PiLp p fun _ : MultiIndexLE ι k ↦ Lp F p (μ.restrict (Ω : Set E))

namespace SobolevMultiIndexTuple

/-- The function underlying a family: its component at the multi-index `0`. -/
noncomputable def fn (u : SobolevMultiIndexTuple F ι k p Ω μ) : E → F := u 0

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [LinearOrder ι] in
/-- The function underlying the zero family vanishes off a null set of `Ω`. -/
theorem fn_zero : (0 : SobolevMultiIndexTuple F ι k p Ω μ).fn =ᵐ[μ.restrict (Ω : Set E)] 0 :=
  Lp.coeFn_zero F p _

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [LinearOrder ι] in
/-- The function underlying a sum is, off a null set of `Ω`, the sum of the functions. -/
theorem fn_add (u v : SobolevMultiIndexTuple F ι k p Ω μ) :
    (u + v).fn =ᵐ[μ.restrict (Ω : Set E)] u.fn + v.fn :=
  Lp.coeFn_add (u 0) (v 0)

omit [NormedSpace ℝ E] [LinearOrder ι] in
/-- The function underlying a scalar multiple is, off a null set of `Ω`, the multiple of the
function. -/
theorem fn_smul (c : ℝ) (u : SobolevMultiIndexTuple F ι k p Ω μ) :
    (c • u).fn =ᵐ[μ.restrict (Ω : Set E)] c • u.fn :=
  Lp.coeFn_smul c (u 0)

end SobolevMultiIndexTuple

/-! ### The space `W^{k,p}(Ω)` -/

variable [OpensMeasurableSpace E]

variable (F b k p Ω μ) in
/-- **The Sobolev space `W^{k,p}(Ω)` with the derivatives indexed by multi-indices**: the subspace
of `SobolevMultiIndexTuple F ι k p Ω μ` consisting of the families `(w_α)_{|α| ≤ k}` in which `w_α`
is the `α`-th weak derivative of `w_0` on `Ω`, the multi-index `α` being read as the tuple of
directions `multiIndexTuple b α`. This is the space of Atkinson and Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Definition 7.2.2, and it carries that
definition's norm: the `ℓ^p` sum, over the multi-indices `α` with `|α| ≤ k`, of the `L^p(Ω)` norms
of the `∂^α`. -/
def SobolevMultiIndex : Submodule ℝ (SobolevMultiIndexTuple F ι k p Ω μ) where
  carrier := {u | ∀ α : MultiIndexLE ι k,
    HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) u.fn (u α) Ω μ}
  zero_mem' _α :=
    HasWeakIteratedLineDerivOn.zero.congr_ae SobolevMultiIndexTuple.fn_zero.symm
      (Lp.coeFn_zero _ _ _).symm
  add_mem' {u v} hu hv α :=
    ((hu α).add (hv α)).congr_ae (SobolevMultiIndexTuple.fn_add u v).symm (Lp.coeFn_add _ _).symm
  smul_mem' c u hu α :=
    ((hu α).const_smul c).congr_ae (SobolevMultiIndexTuple.fn_smul c u).symm
      (Lp.coeFn_smul _ _).symm

namespace SobolevMultiIndex

/-- Membership of `W^{k,p}(Ω)` unfolded: a family lies in it exactly when each of its components is
the weak derivative, for the corresponding multi-index, of the function it carries. -/
theorem mem_def {u : SobolevMultiIndexTuple F ι k p Ω μ} :
    u ∈ SobolevMultiIndex F b k p Ω μ ↔ ∀ α : MultiIndexLE ι k,
      HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) u.fn (u α) Ω μ :=
  Iff.rfl

/-- The function underlying an element of `W^{k,p}(Ω)`. An element is a family, hence a term of a
`Submodule`, so this is spelt `SobolevMultiIndex.fn u` rather than `u.fn`. -/
noncomputable def fn (u : SobolevMultiIndex F b k p Ω μ) : E → F :=
  SobolevMultiIndexTuple.fn (u : SobolevMultiIndexTuple F ι k p Ω μ)

/-- The weak derivative `∂^α` of an element of `W^{k,p}(Ω)`, as an element of `L^p(Ω)`. -/
def weakDeriv (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    Lp F p (μ.restrict (Ω : Set E)) := (u : SobolevMultiIndexTuple F ι k p Ω μ) α

/-- The component at `α` of an element of `W^{k,p}(Ω)` is the `α`-th weak derivative of its
underlying function. -/
theorem hasWeakIteratedLineDerivOn (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) (fn u) (weakDeriv u α) Ω μ :=
  u.2 α

/-- The component at the multi-index `0` is the function itself. -/
theorem weakDeriv_zero (u : SobolevMultiIndex F b k p Ω μ) :
    (weakDeriv u 0 : E → F) = fn u := rfl

/-- The function of the zero element of `W^{k,p}(Ω)` vanishes off a null set of `Ω`. -/
theorem fn_zero : fn (0 : SobolevMultiIndex F b k p Ω μ) =ᵐ[μ.restrict (Ω : Set E)] 0 :=
  SobolevMultiIndexTuple.fn_zero

/-- The function of a sum is, off a null set of `Ω`, the sum of the functions. -/
theorem fn_add (u v : SobolevMultiIndex F b k p Ω μ) :
    fn (u + v) =ᵐ[μ.restrict (Ω : Set E)] fn u + fn v :=
  SobolevMultiIndexTuple.fn_add _ _

/-- The function of a scalar multiple is, off a null set of `Ω`, the multiple of the function. -/
theorem fn_smul (c : ℝ) (u : SobolevMultiIndex F b k p Ω μ) :
    fn (c • u) =ᵐ[μ.restrict (Ω : Set E)] c • fn u :=
  SobolevMultiIndexTuple.fn_smul _ _

/-- The function underlying an element of `W^{k,p}(Ω)` lies in `L^p(Ω)`. -/
theorem memLp (u : SobolevMultiIndex F b k p Ω μ) : MemLp (fn u) p (μ.restrict (Ω : Set E)) :=
  Lp.memLp _

variable [Fact (1 ≤ p)]

/-- Membership of `W^{k,p}(Ω)` in terms of the integration by parts formula alone: the local
integrability that the weak derivative relation also asks for is automatic for `L^p(Ω)`
functions. -/
theorem mem_iff [IsLocallyFiniteMeasure μ] {u : SobolevMultiIndexTuple F ι k p Ω μ} :
    u ∈ SobolevMultiIndex F b k p Ω μ ↔ ∀ (α : MultiIndexLE ι k) (φ : 𝓓(Ω, ℝ)),
      ∫ x in (Ω : Set E),
          iteratedFDeriv ℝ (∑ i, α.1 i) φ x (multiIndexTuple (b : ι → E) α.1) • u.fn x ∂μ
        = (-1 : ℝ) ^ (∑ i, α.1 i) • ∫ x in (Ω : Set E), φ x • u α x ∂μ :=
  ⟨fun h α φ ↦ (h α).integral_smul_eq φ, fun h α ↦
    { locallyIntegrableOn := (Lp.memLp (u 0)).locallyIntegrableOn Fact.out
      locallyIntegrableOn_weakDeriv := (Lp.memLp (u α)).locallyIntegrableOn Fact.out
      integral_smul_eq := h α }⟩

/-! ### Completeness -/

section Complete

variable [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

variable (F ι k p Ω μ) in
/-- Pairing the component at `α` of a family against a test function `φ` on `Ω`,
`u ↦ ∫_Ω φ (u_α)`, as a continuous linear map on the ambient space of `W^{k,p}(Ω)`. Continuity is
Hölder's inequality against `φ`, which lies in every `L^q(Ω)`; this is what makes the weak
derivative relation a closed condition. -/
noncomputable def pairingCLM (α : MultiIndexLE ι k) (φ : 𝓓(Ω, ℝ)) :
    SobolevMultiIndexTuple F ι k p Ω μ →L[ℝ] F :=
  ((TestFunction.memLp φ (ENNReal.conjExponent p) (μ.restrict (Ω : Set E))).integralSmulCLM F) ∘L
    PiLp.proj p _ α

omit [LinearOrder ι] [IsLocallyFiniteMeasure μ] in
/-- `SobolevMultiIndex.pairingCLM` is the integral it was built from. -/
theorem pairingCLM_apply (α : MultiIndexLE ι k) (φ : 𝓓(Ω, ℝ))
    (u : SobolevMultiIndexTuple F ι k p Ω μ) :
    pairingCLM F ι k p Ω μ α φ u = ∫ x in (Ω : Set E), φ x • u α x ∂μ := by
  rw [pairingCLM]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, MemLp.integralSmulCLM_apply,
    PiLp.proj_apply]

/-- **`W^{k,p}(Ω)` is a closed subspace of the `ℓ^p` product of the `L^p(Ω)` spaces**: an `L^p(Ω)`
limit of weak derivatives is a weak derivative, because the integration by parts formula pairs the
functions against a fixed test function and that pairing is continuous on `L^p(Ω)`. This is the
substance of Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
3rd edition, Theorem 7.2.3, here for the norm that definition displays. -/
theorem isClosed :
    IsClosed (SobolevMultiIndex F b k p Ω μ : Set (SobolevMultiIndexTuple F ι k p Ω μ)) := by
  have key : (SobolevMultiIndex F b k p Ω μ : Set (SobolevMultiIndexTuple F ι k p Ω μ)) =
      ⋂ (α : MultiIndexLE ι k) (φ : 𝓓(Ω, ℝ)),
        {u | pairingCLM F ι k p Ω μ 0
            (φ.iteratedFDerivApply (∑ i, α.1 i) (multiIndexTuple (b : ι → E) α.1)) u
          = (-1 : ℝ) ^ (∑ i, α.1 i) • pairingCLM F ι k p Ω μ α φ u} := by
    ext u
    simp only [SetLike.mem_coe, mem_iff, mem_iInter, Set.mem_ofPred_eq, pairingCLM_apply,
      SobolevMultiIndexTuple.fn, TestFunction.iteratedFDerivApply_apply]
  rw [key]
  exact isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
    isClosed_eq (ContinuousLinearMap.continuous _)
      ((ContinuousLinearMap.continuous _).const_smul _)

/-- **The Sobolev space `W^{k,p}(Ω)` is a Banach space for the norm of Definition 7.2.2**: Atkinson
and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Theorem 7.2.3. It is a closed subspace of an `ℓ^p` product of `L^p(Ω)` spaces, so it inherits their
completeness. -/
instance instCompleteSpace : CompleteSpace (SobolevMultiIndex F b k p Ω μ) :=
  SobolevMultiIndex.isClosed.completeSpace_coe

end Complete

/-! ### The norm -/

/-- **The norm of `W^{k,p}(Ω)` is the norm of Atkinson and Han**, *Theoretical Numerical Analysis:
A Functional Analysis Framework*, 3rd edition, Definition 7.2.2, for `p < ∞`: the `ℓ^p` sum, over
the multi-indices `α` with `|α| ≤ k`, of the `L^p(Ω)` norms of the `∂^α`. -/
theorem norm_eq_sum (hp : p ≠ ⊤) (u : SobolevMultiIndex F b k p Ω μ) :
    ‖u‖ = (∑ α : MultiIndexLE ι k, ‖weakDeriv u α‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [← Submodule.norm_coe, PiLp.norm_eq_sum
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp)]
  rfl

omit [Fact (1 ≤ p)] in
/-- **The norm of `W^{k,∞}(Ω)` is the norm of Atkinson and Han**, *Theoretical Numerical Analysis:
A Functional Analysis Framework*, 3rd edition, Definition 7.2.2, for `p = ∞`: the largest, over the
multi-indices `α` with `|α| ≤ k`, of the `L^∞(Ω)` norms of the `∂^α`. -/
theorem norm_eq_ciSup (u : SobolevMultiIndex F b k ⊤ Ω μ) :
    ‖u‖ = ⨆ α : MultiIndexLE ι k, ‖weakDeriv u α‖ := by
  rw [← Submodule.norm_coe, PiLp.norm_eq_ciSup]
  rfl

end SobolevMultiIndex

/-! ### Comparison with the predicate on functions -/

variable (b f k p Ω μ) in
/-- `MemSobolevMultiIndex b f k p Ω μ` says that `f` belongs to the Sobolev space `W^{k,p}(Ω)`: it
lies in `L^p(Ω)` and, for every multi-index `α` with `|α| ≤ k`, the weak derivative `∂^α f` exists
on `Ω` and lies in `L^p(Ω)` as well. This is Atkinson and Han, *Theoretical Numerical Analysis: A
Functional Analysis Framework*, 3rd edition, Definition 7.2.2, read one multi-index at a time. -/
def MemSobolevMultiIndex : Prop :=
  MemLp f p (μ.restrict (Ω : Set E)) ∧ ∀ α : ι → ℕ, ∑ i, α i ≤ k →
    ∃ w : E → F, HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α) f w Ω μ ∧
      MemLp w p (μ.restrict (Ω : Set E))

namespace MemSobolevMultiIndex

omit [OpensMeasurableSpace E] in
/-- A function of `W^{k,p}(Ω)` lies in `L^p(Ω)`. -/
theorem memLp (h : MemSobolevMultiIndex b f k p Ω μ) : MemLp f p (μ.restrict (Ω : Set E)) := h.1

omit [OpensMeasurableSpace E] in
/-- A function of `W^{k,p}(Ω)` has, for every multi-index `α` with `|α| ≤ k`, a weak derivative
`∂^α` in `L^p(Ω)`. -/
theorem exists_hasWeakIteratedLineDerivOn (h : MemSobolevMultiIndex b f k p Ω μ) {α : ι → ℕ}
    (hα : ∑ i, α i ≤ k) :
    ∃ w : E → F, HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α) f w Ω μ ∧
      MemLp w p (μ.restrict (Ω : Set E)) :=
  h.2 α hα

omit [OpensMeasurableSpace E] in
/-- Membership of `W^{k,p}(Ω)` only sees the function up to a null set of `Ω`. -/
theorem congr_ae {f' : E → F} (h : MemSobolevMultiIndex b f k p Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') : MemSobolevMultiIndex b f' k p Ω μ :=
  ⟨h.1.ae_eq hf, fun α hα ↦
    let ⟨w, hw, hwp⟩ := h.2 α hα
    ⟨w, hw.congr_ae hf (Filter.EventuallyEq.refl _ _), hwp⟩⟩

/-- `W^{k,p}(Ω)` is closed under addition. -/
protected theorem add {f g : E → F}
    (hf : MemSobolevMultiIndex b f k p Ω μ)
    (hg : MemSobolevMultiIndex b g k p Ω μ) : MemSobolevMultiIndex b (f + g) k p Ω μ :=
  ⟨hf.1.add hg.1, fun α hα ↦
    let ⟨w₁, hw₁, hw₁p⟩ := hf.2 α hα
    let ⟨w₂, hw₂, hw₂p⟩ := hg.2 α hα
    ⟨w₁ + w₂, hw₁.add hw₂, hw₁p.add hw₂p⟩⟩

omit [OpensMeasurableSpace E] in
/-- `W^{k,p}(Ω)` is closed under negation. -/
protected theorem neg {f : E → F}
    (hf : MemSobolevMultiIndex b f k p Ω μ) :
    MemSobolevMultiIndex b (-f) k p Ω μ :=
  ⟨hf.1.neg, fun α hα ↦
    let ⟨w, hw, hwp⟩ := hf.2 α hα
    ⟨-w, hw.neg, hwp.neg⟩⟩

/-- `W^{k,p}(Ω)` is closed under subtraction. -/
protected theorem sub {f g : E → F}
    (hf : MemSobolevMultiIndex b f k p Ω μ)
    (hg : MemSobolevMultiIndex b g k p Ω μ) : MemSobolevMultiIndex b (f - g) k p Ω μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

omit [OpensMeasurableSpace E] in
/-- `W^{k,p}(Ω)` is closed under scalar multiplication. -/
protected theorem const_smul {f : E → F}
    (hf : MemSobolevMultiIndex b f k p Ω μ) (c : ℝ) :
    MemSobolevMultiIndex b (c • f) k p Ω μ :=
  ⟨hf.1.const_smul c, fun α hα ↦
    let ⟨w, hw, hwp⟩ := hf.2 α hα
    ⟨c • w, hw.const_smul c, hwp.const_smul c⟩⟩

/-- `W^{k,p}(Ω)` is closed under finite sums. -/
protected theorem finset_sum {κ : Type*} (s : Finset κ) {f : κ → E → F}
    (hf : ∀ i ∈ s, MemSobolevMultiIndex b (f i) k p Ω μ) :
    MemSobolevMultiIndex b (∑ i ∈ s, f i) k p Ω μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨MemLp.zero, fun α _ ↦ ⟨0, HasWeakIteratedLineDerivOn.zero, MemLp.zero⟩⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

end MemSobolevMultiIndex

/-- The function underlying an element of `W^{k,p}(Ω)` belongs to `W^{k,p}(Ω)` in the sense of
`MemSobolevMultiIndex`, that is, of Atkinson and Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Definition 7.2.2. -/
theorem SobolevMultiIndex.memSobolevMultiIndex (u : SobolevMultiIndex F b k p Ω μ) :
    MemSobolevMultiIndex b (SobolevMultiIndex.fn u) k p Ω μ :=
  ⟨SobolevMultiIndex.memLp u, fun α hα ↦ ⟨SobolevMultiIndex.weakDeriv u ⟨α, hα⟩,
    SobolevMultiIndex.hasWeakIteratedLineDerivOn u ⟨α, hα⟩, Lp.memLp _⟩⟩

/-- Every function that lies in `W^{k,p}(Ω)` in the sense of `MemSobolevMultiIndex` is, up to a null
set of `Ω`, the function underlying an element of `SobolevMultiIndex F b k p Ω μ`. Together with
`SobolevMultiIndex.memSobolevMultiIndex` this identifies the type with the space of Atkinson and
Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Definition 7.2.2. -/
theorem MemSobolevMultiIndex.exists_sobolevMultiIndex [Fact (1 ≤ p)] [FiniteDimensional ℝ E]
    [BorelSpace E] [CompleteSpace F] (h : MemSobolevMultiIndex b f k p Ω μ) :
    ∃ u : SobolevMultiIndex F b k p Ω μ, SobolevMultiIndex.fn u =ᵐ[μ.restrict (Ω : Set E)] f := by
  choose w hw hwp using h.2
  have hle : ∑ i, (0 : ι → ℕ) i ≤ k := MultiIndexLE.sum_zero (ι := ι) ▸ Nat.zero_le k
  set u : SobolevMultiIndexTuple F ι k p Ω μ :=
    WithLp.toLp p (fun α : MultiIndexLE ι k ↦ (hwp α.1 α.2).toLp (w α.1 α.2)) with hu
  have hfn : SobolevMultiIndexTuple.fn u =ᵐ[μ.restrict (Ω : Set E)] f :=
    (hwp (0 : ι → ℕ) hle).coeFn_toLp.trans ((ae_restrict_iff' Ω.isOpen.measurableSet).2
      ((hw (0 : ι → ℕ) hle).ae_eq_of_length_eq_zero MultiIndexLE.sum_zero))
  exact ⟨⟨u, fun α ↦ (hw α.1 α.2).congr_ae hfn.symm (hwp α.1 α.2).coeFn_toLp.symm⟩, hfn⟩

/-- The whole family of an element of `W^{k,p}(Ω)` is determined by the function it carries: two
elements whose functions agree off a null set of `Ω` are equal. This is the almost everywhere
uniqueness of the weak derivative, `HasWeakIteratedLineDerivOn.ae_eq`. -/
theorem SobolevMultiIndex.ext_of_fn_ae_eq [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    {u v : SobolevMultiIndex F b k p Ω μ}
    (h : SobolevMultiIndex.fn u =ᵐ[μ.restrict (Ω : Set E)] SobolevMultiIndex.fn v) : u = v :=
  Subtype.ext <| PiLp.ext fun α ↦ Lp.ext <|
    (ae_restrict_iff' Ω.isOpen.measurableSet).2
      (((SobolevMultiIndex.hasWeakIteratedLineDerivOn u α).congr_ae h
        (Filter.EventuallyEq.refl _ _)).ae_eq (SobolevMultiIndex.hasWeakIteratedLineDerivOn v α))

omit [OpensMeasurableSpace E] in
/-- **A function of `W^{k,p}(Ω)` in the tensor formulation is one in the multi-index formulation**:
its `α`-th weak derivative is the weak derivative of order `|α|` evaluated at the tuple of
directions naming `α`. -/
theorem MemSobolev.memSobolevMultiIndex (h : MemSobolev f k p Ω μ) :
    MemSobolevMultiIndex b f k p Ω μ := by
  refine ⟨h.memLp, fun α hα ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.exists_hasWeakIteratedFDerivOn (n := ∑ i, α i) (by exact_mod_cast hα)
  exact ⟨_, hw.lineDeriv _, (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α i) ↦ E) F
    (multiIndexTuple (b : ι → E) α)).comp_memLp' hwp⟩

/-- **A function of `W^{k,p}(Ω)` in the multi-index formulation is one in the tensor formulation**,
the converse of `MemSobolev.memSobolevMultiIndex`, so that the two formulations describe the same
functions.

The weak derivative of order `n` is assembled from the `∂^α` with `|α| = n`: it is the continuous
`n`-linear map whose value on a tuple `(b i₁, …, b iₙ)` of basis vectors is `∂^α f` for the
multi-index `α = multiIndexCount` counting the occurrences of each index, extended by multilinearity
through `basisCoordProd`. What has to be checked is the integration by parts formula for an
arbitrary tuple of directions; multilinearity reduces it to the tuples of basis vectors, and there
the definition of `∂^α` supplies it for the *sorted* tuple only. The two agree because
`iteratedFDeriv ℝ n φ x` is symmetric in its arguments for a test function `φ`
(`ContDiff.iteratedFDeriv_congr_perm`), which is what makes this direction harder than the other
one. -/
theorem MemSobolevMultiIndex.memSobolev (h : MemSobolevMultiIndex b f k p Ω μ) :
    MemSobolev f k p Ω μ := by
  classical
  obtain ⟨u₀, hu₀, -⟩ := h.2 0 (by simp)
  have hfloc : LocallyIntegrableOn f (Ω : Set E) μ := hu₀.locallyIntegrableOn
  refine ⟨h.memLp, fun n hn ↦ ?_⟩
  have hnk : n ≤ k := by exact_mod_cast hn
  -- one weak derivative `∂^α` for each tuple `m` of basis indices, `α` counting the indices in `m`
  have hchoice : ∀ m : Fin n → ι, ∃ v : E → F,
      HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) (multiIndexCount m)) f v Ω μ ∧
        MemLp v p (μ.restrict (Ω : Set E)) := fun m ↦
    h.2 (multiIndexCount m) (by rw [sum_multiIndexCount]; exact hnk)
  choose v hv hvp using hchoice
  -- the tensor of order `n` they assemble
  set L : (Fin n → ι) → (F →L[ℝ] (E [×n]→L[ℝ] F)) := fun m ↦
    ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin n ↦ E) F (basisCoordProd b m) with hLdef
  set W : E → E [×n]→L[ℝ] F := fun x ↦ ∑ m : Fin n → ι, L m (v m x) with hWdef
  have hWsum : W = ∑ m : Fin n → ι, (⇑(L m) ∘ v m) := by
    funext x
    simp [hWdef, Finset.sum_apply, Function.comp_def]
  have hWapply : ∀ (x : E) (y : Fin n → E),
      W x y = ∑ m : Fin n → ι, (∏ j, b.repr (y j) (m j)) • v m x := by
    intro x y
    rw [hWdef]
    simp only [sum_apply, hLdef, ContinuousMultilinearMap.smulRightL_apply,
      ContinuousMultilinearMap.smulRight_apply, basisCoordProd_apply]
  have hWp : MemLp W p (μ.restrict (Ω : Set E)) := by
    rw [hWsum]
    exact memLp_finsetSum' _ fun m _ ↦ (L m).comp_memLp' (hvp m)
  have hWloc : LocallyIntegrableOn W (Ω : Set E) μ := by
    rw [hWsum]
    refine Finset.sum_induction _ (fun g ↦ LocallyIntegrableOn g (Ω : Set E) μ)
      (fun a c ha hc ↦ ha.add hc) (locallyIntegrable_zero.locallyIntegrableOn _) fun m _ ↦ ?_
    exact (hv m).locallyIntegrableOn_weakDeriv.comp_continuousLinearMap (L m)
  refine ⟨W, ⟨hfloc, hWloc, fun φ y ↦ ?_⟩, hWp⟩
  -- expand the derivative of the test function over the tuples of basis vectors
  have hexp : ∀ x : E, iteratedFDeriv ℝ n (φ : E → ℝ) x y
      = ∑ m : Fin n → ι,
          (∏ j, b.repr (y j) (m j)) * iteratedFDeriv ℝ n (φ : E → ℝ) x fun j ↦ b (m j) :=
    fun x ↦ by
      simpa [smul_eq_mul] using
        ContinuousMultilinearMap.apply_eq_sum_basis b (iteratedFDeriv ℝ n (φ : E → ℝ) x) y
  have hint : ∀ m : Fin n → ι, IntegrableOn
      (fun x ↦ iteratedFDeriv ℝ n (φ : E → ℝ) x (fun j ↦ b (m j)) • f x) (Ω : Set E) μ := by
    intro m
    have h' := ((hv m).integrable_smul (φ.iteratedFDerivApply n fun j ↦ b (m j))).integrableOn
      (s := (Ω : Set E))
    simpa only [TestFunction.iteratedFDerivApply_apply] using h'
  have hint' : ∀ m : Fin n → ι,
      IntegrableOn (fun x ↦ (φ : E → ℝ) x • v m x) (Ω : Set E) μ :=
    fun m ↦ ((hv m).integrable_smul_weakDeriv φ).integrableOn
  have hintc : ∀ m : Fin n → ι, IntegrableOn
      (fun x ↦ (∏ j, b.repr (y j) (m j)) •
        (iteratedFDeriv ℝ n (φ : E → ℝ) x (fun j ↦ b (m j)) • f x)) (Ω : Set E) μ :=
    fun m ↦ (hint m).smul _
  have hint'c : ∀ m : Fin n → ι, IntegrableOn
      (fun x ↦ (∏ j, b.repr (y j) (m j)) • ((φ : E → ℝ) x • v m x)) (Ω : Set E) μ :=
    fun m ↦ (hint' m).smul _
  -- integration by parts along one tuple of basis vectors, after sorting it
  have hstep : ∀ m : Fin n → ι,
      ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x (fun j ↦ b (m j)) • f x ∂μ
        = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • v m x ∂μ := by
    intro m
    have hperm : (List.ofFn fun j ↦ b (m j)).Perm
        (List.ofFn (multiIndexTuple (b : ι → E) (multiIndexCount m))) := by
      rw [← multiIndexDirections_eq_ofFn]
      exact multiIndexDirections_multiIndexCount_perm (b : ι → E) m
    calc ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x (fun j ↦ b (m j)) • f x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ (∑ i, multiIndexCount m i) (φ : E → ℝ) x
            (multiIndexTuple (b : ι → E) (multiIndexCount m)) • f x ∂μ :=
          setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by
            rw [φ.contDiff.iteratedFDeriv_congr_perm hperm x]
      _ = (-1 : ℝ) ^ (∑ i, multiIndexCount m i) •
            ∫ x in (Ω : Set E), (φ : E → ℝ) x • v m x ∂μ := (hv m).integral_smul_eq φ
      _ = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • v m x ∂μ := by
          rw [sum_multiIndexCount]
  calc ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x ∂μ
      = ∫ x in (Ω : Set E), ∑ m : Fin n → ι, (∏ j, b.repr (y j) (m j)) •
          (iteratedFDeriv ℝ n (φ : E → ℝ) x (fun j ↦ b (m j)) • f x) ∂μ := by
        refine setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ ?_
        rw [hexp x, Finset.sum_smul]
        exact Finset.sum_congr rfl fun m _ ↦ by rw [smul_smul]
    _ = ∑ m : Fin n → ι, (∏ j, b.repr (y j) (m j)) •
          ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x (fun j ↦ b (m j)) • f x ∂μ := by
        rw [integral_finsetSum _ fun m _ ↦ hintc m]
        exact Finset.sum_congr rfl fun m _ ↦ integral_smul _ _
    _ = ∑ m : Fin n → ι, (∏ j, b.repr (y j) (m j)) •
          ((-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • v m x ∂μ) :=
        Finset.sum_congr rfl fun m _ ↦ by rw [hstep m]
    _ = (-1 : ℝ) ^ n • ∑ m : Fin n → ι,
          ∫ x in (Ω : Set E), (∏ j, b.repr (y j) (m j)) • ((φ : E → ℝ) x • v m x) ∂μ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun m _ ↦ by rw [smul_comm, integral_smul]
    _ = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • W x y ∂μ := by
        rw [← integral_finsetSum _ fun m _ ↦ hint'c m]
        refine congrArg _ (setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ ?_)
        rw [hWapply x y, Finset.smul_sum]
        exact Finset.sum_congr rfl fun m _ ↦ smul_comm _ _ _

variable (b) in
/-- **The tensor formulation of `W^{k,p}(Ω)` and the multi-index formulation describe the same
functions.** The two halves are `MemSobolev.memSobolevMultiIndex`, which evaluates the derivative
tensor of order `|α|` at the tuple of directions naming `α`, and `MemSobolevMultiIndex.memSobolev`,
which assembles the tensor of order `n` from the `∂^α` with `|α| = n`. Only the functions are
matched: the two formulations carry different, though equivalent, norms, and that equivalence is
not proved here. -/
theorem memSobolev_iff_memSobolevMultiIndex :
    MemSobolev f k p Ω μ ↔ MemSobolevMultiIndex b f k p Ω μ :=
  ⟨MemSobolev.memSobolevMultiIndex, MemSobolevMultiIndex.memSobolev⟩

end Space

/-! ### `H^k(Ω)` is a Hilbert space -/

section Hilbert

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {Ω : Opens E} {μ : Measure E}

/-- **The inner product of `H^k(Ω) = W^{k,2}(Ω)`**: the norm of the type at `p = 2` is induced by
the inner product `(u, v)_k = ∫_Ω ∑_{|α| ≤ k} ⟪∂^α u, ∂^α v⟫`, which is the inner product of
Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Corollary 7.2.4. The inner product itself is not built here: the ambient space is a `PiLp 2` of
`L²(Ω)` spaces, which carries one, and a submodule of an inner product space carries the induced
one; the content of the statement is that it is the book's formula. Together with
`SobolevMultiIndex.instCompleteSpace` this is the corollary. -/
theorem SobolevMultiIndex.inner_eq (u v : SobolevMultiIndex F b k 2 Ω μ) :
    inner ℝ u v = ∫ x in (Ω : Set E), ∑ α : MultiIndexLE ι k,
      inner ℝ (SobolevMultiIndex.weakDeriv u α x) (SobolevMultiIndex.weakDeriv v α x) ∂μ := by
  rw [Submodule.coe_inner, PiLp.inner_apply,
    integral_finsetSum Finset.univ fun α _ ↦ MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
      (SobolevMultiIndex.weakDeriv u α) (SobolevMultiIndex.weakDeriv v α)]
  exact Finset.sum_congr rfl fun α _ ↦ L2.inner_def _ _

end Hilbert

/-! ### The subspace `W_0^{k,p}(Ω)` -/

section Zero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} {Ω : Opens E}
  {μ : Measure E}

namespace SobolevMultiIndex

variable (F b k p Ω μ) in
/-- The image of the test functions `C_0^∞(Ω)` in `W^{k,p}(Ω)`, in the multi-index formulation:
the elements whose function agrees, off a null set of `Ω`, with a test function on `Ω`. Every test
function does occur, by `TestFunction.exists_mem_sobolevMultiIndex_testFunctions`; this is the
twin of `Sobolev.testFunctions` of `Numlib/Analysis/Sobolev/Space.lean`. -/
def testFunctions : Submodule ℝ (SobolevMultiIndex F b k p Ω μ) where
  carrier := {u | ∃ φ : 𝓓(Ω, F), fn u =ᵐ[μ.restrict (Ω : Set E)] φ}
  zero_mem' := ⟨0, fn_zero⟩
  add_mem' := fun {u v} ⟨φ, hφ⟩ ⟨ψ, hψ⟩ ↦ ⟨φ + ψ, (fn_add u v).trans (hφ.add hψ)⟩
  smul_mem' := fun c u ⟨φ, hφ⟩ ↦ ⟨c • φ, (fn_smul c u).trans (hφ.const_smul c)⟩

/-- Membership of `SobolevMultiIndex.testFunctions` unfolded: the function of the element agrees
with a test function off a null set of `Ω`. -/
theorem mem_testFunctions {u : SobolevMultiIndex F b k p Ω μ} :
    u ∈ testFunctions F b k p Ω μ ↔ ∃ φ : 𝓓(Ω, F), fn u =ᵐ[μ.restrict (Ω : Set E)] φ :=
  Iff.rfl

/-- Every test function on `Ω` is the function of an element of
`SobolevMultiIndex.testFunctions`, so that submodule really is the image of `C_0^∞(Ω)` in
`W^{k,p}(Ω)`: a test function is smooth with compact support, so all its derivatives `∂^α` are
continuous with compact support and lie in `L^p(Ω)`. -/
theorem _root_.TestFunction.exists_mem_sobolevMultiIndex_testFunctions [Fact (1 ≤ p)]
    [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]
    (φ : 𝓓(Ω, F)) :
    ∃ u ∈ testFunctions F b k p Ω μ, fn u =ᵐ[μ.restrict (Ω : Set E)] φ :=
  let ⟨u, hu⟩ :=
    (TestFunction.memSobolev φ).memSobolevMultiIndex (b := b).exists_sobolevMultiIndex
  ⟨u, ⟨φ, hu⟩, hu⟩

end SobolevMultiIndex

variable [Fact (1 ≤ p)]

variable (F b k p Ω μ) in
/-- **The Sobolev space `W_0^{k,p}(Ω)` in the multi-index formulation**, the closure of
`C_0^∞(Ω)` in `SobolevMultiIndex F b k p Ω μ`: Atkinson and Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Definition 7.2.9, on the space whose
norm is that of Definition 7.2.2. `SobolevZero` of `Numlib/Analysis/Sobolev/Space.lean` is the
same closure on the tensor formulation; that type is not an inner product space, while at `p = 2`
this one is a closed subspace of the Hilbert space `H^k(Ω)` (`SobolevMultiIndex.inner_eq`) and so
a Hilbert space itself, which is what the variational theory of `Numlib/Variational/` needs of
`H^1_0(a, b)` in `Numlib/Analysis/Sobolev/Interval.lean`. No comparison between the two closures
is made: the two types carry different, though equivalent, norms. -/
noncomputable def SobolevMultiIndexZero : Submodule ℝ (SobolevMultiIndex F b k p Ω μ) :=
  (SobolevMultiIndex.testFunctions F b k p Ω μ).topologicalClosure

namespace SobolevMultiIndexZero

/-- `W_0^{k,p}(Ω)` is a closed subspace of `W^{k,p}(Ω)`, being a closure. -/
theorem isClosed :
    IsClosed (SobolevMultiIndexZero F b k p Ω μ : Set (SobolevMultiIndex F b k p Ω μ)) :=
  Submodule.isClosed_topologicalClosure _

/-- The test functions lie in `W_0^{k,p}(Ω)`. -/
theorem testFunctions_le :
    SobolevMultiIndex.testFunctions F b k p Ω μ ≤ SobolevMultiIndexZero F b k p Ω μ :=
  Submodule.le_topologicalClosure _

/-- **`W_0^{k,p}(Ω)` is a Banach space**, and at `p = 2` a Hilbert space: a closed subspace of
the complete space `W^{k,p}(Ω)`. -/
instance instCompleteSpace [CompleteSpace F] [IsFiniteMeasureOnCompacts μ]
    [IsLocallyFiniteMeasure μ] : CompleteSpace (SobolevMultiIndexZero F b k p Ω μ) :=
  isClosed.completeSpace_coe

end SobolevMultiIndexZero

end Zero

/-! ### The inductive description of `W^{m+1,p}(Ω)`

Brezis defines `W^{m,p}(Ω)` by induction — `u ∈ W^{m,p}` when `u` and all its first partial
derivatives lie in `W^{m-1,p}` — and remarks that the multi-index description is equivalent. The
equivalence rests on reading `∂^{α + e_i}` as `∂^α ∂_i`, which is
`HasWeakIteratedLineDerivOn.cons'` / `of_cons'` together with the permutation invariance of the
weak derivative, since `multiIndexTuple` lists the directions in increasing order of the index. -/

section Succ

variable {E : Type*} {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The directions naming `α + β` are, as a multiset, those naming `α` together with those
naming `β`. -/
theorem coe_multiIndexDirections_add (b : ι → E) (α β : ι → ℕ) :
    ((multiIndexDirections b (α + β) : List E) : Multiset E)
      = (multiIndexDirections b α : Multiset E) + (multiIndexDirections b β : Multiset E) := by
  simp only [coe_multiIndexDirections, Pi.add_apply, Multiset.replicate_add,
    Finset.sum_add_distrib]

/-- The multi-index `e_i` names the single direction `b i`. -/
theorem coe_multiIndexDirections_single (b : ι → E) (i : ι) :
    ((multiIndexDirections b (Pi.single i 1) : List E) : Multiset E) = {b i} := by
  rw [coe_multiIndexDirections, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- The tuple naming `e_i` is a rearrangement of the one-entry tuple `![b i]`. -/
theorem multiIndexTuple_single_perm (b : ι → E) (i : ι) :
    (List.ofFn (multiIndexTuple b (Pi.single i 1))).Perm (List.ofFn ![b i]) := by
  rw [← Multiset.coe_eq_coe, ← multiIndexDirections_eq_ofFn, coe_multiIndexDirections_single]
  simp

/-- The tuple naming `α + e_i` is a rearrangement of `b i` followed by the tuple naming `α`. -/
theorem multiIndexTuple_add_single_perm (b : ι → E) (α : ι → ℕ) (i : ι) :
    (List.ofFn (Fin.cons (b i) (multiIndexTuple b α))).Perm
      (List.ofFn (multiIndexTuple b (α + Pi.single i 1))) := by
  rw [← Multiset.coe_eq_coe, List.ofFn_cons, ← multiIndexDirections_eq_ofFn,
    ← multiIndexDirections_eq_ofFn, ← Multiset.cons_coe, coe_multiIndexDirections_add,
    coe_multiIndexDirections_single, add_comm, Multiset.singleton_add]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {b : Basis ι ℝ E} {f : E → F} {k : ℕ} {p : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

/-- `W^{k,p}(Ω)` decreases as the order `k` increases. -/
theorem MemSobolevMultiIndex.mono_order {k' : ℕ} (h : MemSobolevMultiIndex b f k p Ω μ)
    (hk : k' ≤ k) : MemSobolevMultiIndex b f k' p Ω μ :=
  ⟨h.1, fun α hα ↦ h.2 α (hα.trans hk)⟩

/-- The zero function lies in `W^{k,p}(Ω)`. -/
protected theorem MemSobolevMultiIndex.zero : MemSobolevMultiIndex b (0 : E → F) k p Ω μ :=
  ⟨MemLp.zero, fun _ _ ↦ ⟨0, HasWeakIteratedLineDerivOn.zero, MemLp.zero⟩⟩

/-- `W^{0,p}(Ω)` is `L^p(Ω)`. -/
theorem memSobolevMultiIndex_zero_iff [OpensMeasurableSpace E] [Fact (1 ≤ p)]
    [IsLocallyFiniteMeasure μ] :
    MemSobolevMultiIndex b f 0 p Ω μ ↔ MemLp f p (μ.restrict (Ω : Set E)) := by
  refine ⟨fun h ↦ h.memLp, fun hf ↦ ⟨hf, fun α hα ↦ ?_⟩⟩
  have h0 : ∑ i, α i = 0 := Nat.le_zero.1 hα
  exact ⟨f, HasWeakIteratedLineDerivOn.of_length_eq_zero h0 _ (hf.locallyIntegrableOn Fact.out),
    hf⟩

/-- **The inductive definition of `W^{m+1,p}(Ω)` agrees with the multi-index one**: `f` lies in
`W^{m+1,p}(Ω)` exactly when `f` lies in `W^{m,p}(Ω)` and, for every basis direction `b i`, `f` has
a weak derivative `∂_i f` along `b i` that lies in `W^{m,p}(Ω)`. This is the equivalence of the two
displayed definitions of `W^{m,p}(Ω)` in [brezis2011functional] §9.1 (the paragraph "The spaces
`W^{m,p}(Ω)`"): the weak derivative `∂^α (∂_i f)` is `∂^{α + e_i} f`, by
`HasWeakIteratedLineDerivOn.cons'` and its converse after rearranging the tuple of directions. -/
theorem memSobolevMultiIndex_succ_iff {m : ℕ} :
    MemSobolevMultiIndex b f (m + 1) p Ω μ ↔ MemSobolevMultiIndex b f m p Ω μ ∧ ∀ i,
      ∃ g : E → F, HasWeakIteratedLineDerivOn ![b i] f g Ω μ ∧
        MemSobolevMultiIndex b g m p Ω μ := by
  constructor
  · intro h
    refine ⟨h.mono_order (Nat.le_succ m), fun i ↦ ?_⟩
    obtain ⟨g, hg, hgp⟩ := h.2 (Pi.single i 1) (by simp)
    have hg' : HasWeakIteratedLineDerivOn ![b i] f g Ω μ :=
      hg.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
    refine ⟨g, hg', hgp, fun β hβ ↦ ?_⟩
    obtain ⟨u, hu, hup⟩ := h.2 (β + Pi.single i 1) (by simp [Finset.sum_add_distrib]; omega)
    exact ⟨u, hg'.of_cons' (hu.of_perm (multiIndexTuple_add_single_perm (b : ι → E) β i).symm),
      hup⟩
  · rintro ⟨hf, hg⟩
    refine ⟨hf.1, fun α hα ↦ ?_⟩
    rcases Nat.lt_or_ge (∑ j, α j) (m + 1) with hlt | hge
    · exact hf.2 α (Nat.lt_succ_iff.1 hlt)
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, α i ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) (by omega)
    obtain ⟨β, rfl⟩ : ∃ β : ι → ℕ, α = β + Pi.single i 1 := by
      refine ⟨α - Pi.single i 1, funext fun j ↦ ?_⟩
      by_cases hj : j = i
      · subst hj
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
        omega
      · simp [Pi.single_eq_of_ne hj]
    have hβ : ∑ j, β j ≤ m := by
      simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
        ite_true] at hα
      omega
    obtain ⟨g, hg1, hg2⟩ := hg i
    obtain ⟨u, hu, hup⟩ := hg2.2 β hβ
    exact ⟨u, (hg1.cons' hu).of_perm (multiIndexTuple_add_single_perm (b : ι → E) β i), hup⟩

end Succ

/-! ### The weak derivatives and the function as bounded linear maps -/

section Operators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

variable (F b k p Ω μ) in
/-- **The weak derivative `u ↦ ∂^α u` as a bounded linear map `W^{k,p}(Ω) → L^p(Ω)`**, of norm at
most one: the coordinate projection of the ambient `ℓ^p` product, restricted to the subspace. The
one-dimensional twin is `SobolevIntervalLp.derivL`. -/
noncomputable def weakDerivL (α : MultiIndexLE ι k) :
    SobolevMultiIndex F b k p Ω μ →L[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  (PiLp.proj p (fun _ : MultiIndexLE ι k ↦ Lp F p (μ.restrict (Ω : Set E))) α) ∘L
    (SobolevMultiIndex F b k p Ω μ).subtypeL

/-- `SobolevMultiIndex.weakDerivL` is the weak derivative. -/
@[simp]
theorem weakDerivL_apply (α : MultiIndexLE ι k) (u : SobolevMultiIndex F b k p Ω μ) :
    weakDerivL F b k p Ω μ α u = weakDeriv u α :=
  rfl

/-- Each weak derivative is bounded in `L^p(Ω)` by the norm of `W^{k,p}(Ω)`: the latter is the
`ℓ^p` norm of the tuple of the former. -/
theorem norm_weakDeriv_le (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    ‖weakDeriv u α‖ ≤ ‖u‖ := by
  rw [← Submodule.norm_coe]
  exact PiLp.norm_apply_le _ _

/-- The operator norm of `SobolevMultiIndex.weakDerivL` is at most one. -/
theorem norm_weakDerivL_le (α : MultiIndexLE ι k) : ‖weakDerivL F b k p Ω μ α‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    rw [one_mul]
    exact norm_weakDeriv_le u α

variable (F b k p Ω μ) in
/-- **The inclusion `W^{k,p}(Ω) → L^p(Ω)`** as a bounded linear map: the weak derivative of order
`0`, which is the function itself. It is injective (`SobolevMultiIndex.fnL_injective`) and of norm
at most one; it is the map along which the embedding theorems of Sobolev spaces are stated. -/
noncomputable def fnL : SobolevMultiIndex F b k p Ω μ →L[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  weakDerivL F b k p Ω μ 0

/-- `SobolevMultiIndex.fnL u` is the function of `u`. -/
@[simp]
theorem fnL_apply (u : SobolevMultiIndex F b k p Ω μ) : (fnL F b k p Ω μ u : E → F) = fn u :=
  rfl

/-- `SobolevMultiIndex.fnL u` is the weak derivative of order `0`. -/
theorem fnL_eq_weakDeriv_zero (u : SobolevMultiIndex F b k p Ω μ) :
    fnL F b k p Ω μ u = weakDeriv u 0 :=
  rfl

/-- The `L^p(Ω)` norm of the function is at most the `W^{k,p}(Ω)` norm. -/
theorem norm_fnL_apply_le (u : SobolevMultiIndex F b k p Ω μ) : ‖fnL F b k p Ω μ u‖ ≤ ‖u‖ :=
  norm_weakDeriv_le u 0

/-- The operator norm of the inclusion `W^{k,p}(Ω) → L^p(Ω)` is at most one. -/
theorem norm_fnL_le : ‖fnL F b k p Ω μ‖ ≤ 1 :=
  norm_weakDerivL_le 0

/-- **The inclusion `W^{k,p}(Ω) → L^p(Ω)` is injective**: an element of `W^{k,p}(Ω)` is determined
by its function, the weak derivatives being unique. -/
theorem fnL_injective [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] :
    Function.Injective (fnL F b k p Ω μ) := fun _ _ h ↦
  ext_of_fn_ae_eq (Filter.EventuallyEq.of_eq (congrArg (fun w : Lp F p _ ↦ (w : E → F)) h))

end SobolevMultiIndex

namespace SobolevMultiIndexZero

variable (F b k p Ω μ) in
/-- **The inclusion `W_0^{k,p}(Ω) → L^p(Ω)`** as a bounded linear map, the restriction of
`SobolevMultiIndex.fnL` to the closed subspace `W_0^{k,p}(Ω)`. An `L^p(Ω)` function "lies in
`W_0^{k,p}(Ω)`" when it is in the range of this map, and the lift is then unique
(`SobolevMultiIndexZero.fnL_injective`); this is how a homogeneous boundary condition `u = 0` on
`∂Ω` is read. -/
noncomputable def fnL : SobolevMultiIndexZero F b k p Ω μ →L[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  (SobolevMultiIndex.fnL F b k p Ω μ).comp (SobolevMultiIndexZero F b k p Ω μ).subtypeL

/-- `SobolevMultiIndexZero.fnL v` is the function of `v`. -/
@[simp]
theorem fnL_apply (v : SobolevMultiIndexZero F b k p Ω μ) :
    (fnL F b k p Ω μ v : E → F) = SobolevMultiIndex.fn (v : SobolevMultiIndex F b k p Ω μ) :=
  rfl

/-- `SobolevMultiIndexZero.fnL` is `SobolevMultiIndex.fnL` on the underlying element. -/
theorem fnL_eq (v : SobolevMultiIndexZero F b k p Ω μ) :
    fnL F b k p Ω μ v = SobolevMultiIndex.fnL F b k p Ω μ (v : SobolevMultiIndex F b k p Ω μ) :=
  rfl

/-- The `L^p(Ω)` norm of the function is at most the `W^{k,p}(Ω)` norm. -/
theorem norm_fnL_apply_le (v : SobolevMultiIndexZero F b k p Ω μ) : ‖fnL F b k p Ω μ v‖ ≤ ‖v‖ :=
  SobolevMultiIndex.norm_fnL_apply_le _

/-- The operator norm of the inclusion `W_0^{k,p}(Ω) → L^p(Ω)` is at most one. -/
theorem norm_fnL_le : ‖fnL F b k p Ω μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    rw [one_mul]
    exact norm_fnL_apply_le v

/-- **The inclusion `W_0^{k,p}(Ω) → L^p(Ω)` is injective.** -/
theorem fnL_injective [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] :
    Function.Injective (fnL F b k p Ω μ) := fun _ _ h ↦
  Subtype.ext (SobolevMultiIndex.fnL_injective h)

end SobolevMultiIndexZero

end Operators

/-! ### The gradient norm on `W^{1,p}(Ω)`

The book's `‖∇u‖_{L^p(Ω)}` in the `ℓ^p` reading: the `ℓ^p(ι)` norm of the tuple of partial
derivatives `(∂_i u)_i`, each measured in `L^p(Ω)`. It is a seminorm on `W^{1,p}(Ω)`, and the norm
of the type is the `ℓ^p` sum of `‖u‖_p` and of it. -/

section Gradient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- **The gradient of `u ∈ W^{1,p}(Ω)`**, the tuple `(∂_i u)_i` of its first partial derivatives
in the basis `b`, as an element of the `ℓ^p` product of copies of `L^p(Ω)`. -/
def grad (u : SobolevMultiIndex F b 1 p Ω μ) :
    PiLp p fun _ : ι ↦ Lp F p (μ.restrict (Ω : Set E)) :=
  WithLp.toLp p fun i ↦ weakDeriv u (MultiIndexLE.single i)

omit [Fact (1 ≤ p)] in
/-- The `i`-th entry of the gradient is the partial derivative `∂_i u`. -/
@[simp]
theorem grad_apply (u : SobolevMultiIndex F b 1 p Ω μ) (i : ι) :
    grad u i = weakDeriv u (MultiIndexLE.single i) :=
  rfl

omit [Fact (1 ≤ p)] in
/-- The gradient is additive. -/
theorem grad_add (u v : SobolevMultiIndex F b 1 p Ω μ) : grad (u + v) = grad u + grad v := by
  ext i
  rfl

omit [Fact (1 ≤ p)] in
/-- The gradient commutes with scalar multiplication. -/
theorem grad_smul (c : ℝ) (u : SobolevMultiIndex F b 1 p Ω μ) : grad (c • u) = c • grad u := by
  ext i
  rfl

/-- **The gradient norm `‖∇u‖_{L^p(Ω)}` on `W^{1,p}(Ω)`**, in the `ℓ^p` reading of
[brezis2011functional] §9.1 and Corollary 9.19: `(∑ i, ‖∂_i u‖_p^p)^{1/p}`, and `⨆ i, ‖∂_i u‖_∞`
at `p = ∞`. It is the norm of the gradient tuple `SobolevMultiIndex.grad u` in the `ℓ^p` product
of copies of `L^p(Ω)`; a seminorm on `W^{1,p}(Ω)` bounded by the norm
(`SobolevMultiIndex.gradNorm_le_norm`), and a norm on `W_0^{1,p}(Ω)` of a bounded open set by
Poincaré's inequality. -/
noncomputable def gradNorm (u : SobolevMultiIndex F b 1 p Ω μ) : ℝ := ‖grad u‖

/-- The gradient norm is nonnegative. -/
theorem gradNorm_nonneg (u : SobolevMultiIndex F b 1 p Ω μ) : 0 ≤ gradNorm u := norm_nonneg _

/-- The gradient norm is subadditive. -/
theorem gradNorm_add_le (u v : SobolevMultiIndex F b 1 p Ω μ) :
    gradNorm (u + v) ≤ gradNorm u + gradNorm v := by
  rw [gradNorm, grad_add]
  exact norm_add_le _ _

/-- The gradient norm is homogeneous. -/
theorem gradNorm_smul (c : ℝ) (u : SobolevMultiIndex F b 1 p Ω μ) :
    gradNorm (c • u) = |c| * gradNorm u := by
  rw [gradNorm, grad_smul, norm_smul, Real.norm_eq_abs]
  rfl

/-- **The gradient norm for `p < ∞`**: `‖∇u‖_p = (∑ i, ‖∂_i u‖_p^p)^{1/p}`. -/
theorem gradNorm_eq_sum (hp : p ≠ ⊤) (u : SobolevMultiIndex F b 1 p Ω μ) :
    gradNorm u = (∑ i, ‖weakDeriv u (MultiIndexLE.single i)‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [gradNorm, PiLp.norm_eq_sum
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp)]
  rfl

/-- **The gradient norm at `p = ∞`**: `‖∇u‖_∞ = ⨆ i, ‖∂_i u‖_∞`. -/
theorem gradNorm_eq_ciSup (u : SobolevMultiIndex F b 1 ⊤ Ω μ) :
    gradNorm u = ⨆ i, ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  rw [gradNorm, PiLp.norm_eq_ciSup]
  rfl

/-- **The norm of `W^{1,p}(Ω)` for `p < ∞`** is the `ℓ^p` sum of the `L^p(Ω)` norm of the function
and of the gradient norm: `‖u‖ = (‖u‖_p^p + ‖∇u‖_p^p)^{1/p}`. -/
theorem norm_eq_gradNorm (hp : p ≠ ⊤) (u : SobolevMultiIndex F b 1 p Ω μ) :
    ‖u‖ = (‖weakDeriv u 0‖ ^ p.toReal + gradNorm u ^ p.toReal) ^ (1 / p.toReal) := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  rw [norm_eq_sum hp, gradNorm_eq_sum hp, MultiIndexLE.sum_univ_one, ← Real.rpow_mul
    (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hP.ne',
    Real.rpow_one]

/-- **The norm of `W^{1,∞}(Ω)`** is the larger of the `L^∞(Ω)` norm of the function and the
gradient norm: `‖u‖ = max ‖u‖_∞ ‖∇u‖_∞`. -/
theorem norm_eq_max_gradNorm (u : SobolevMultiIndex F b 1 ⊤ Ω μ) :
    ‖u‖ = max ‖weakDeriv u 0‖ (gradNorm u) := by
  rw [norm_eq_ciSup, gradNorm_eq_ciSup]
  have hbdd : BddAbove (Set.range fun α : MultiIndexLE ι 1 ↦ ‖weakDeriv u α‖) :=
    Finite.bddAbove_range _
  have hbdd' : BddAbove (Set.range fun i : ι ↦ ‖weakDeriv u (MultiIndexLE.single i)‖) :=
    Finite.bddAbove_range _
  apply le_antisymm
  · refine ciSup_le fun α ↦ ?_
    rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨i, rfl⟩
    · exact le_max_left _ _
    · exact le_trans (le_ciSup hbdd' i) (le_max_right _ _)
  · refine max_le (le_ciSup hbdd 0) ?_
    rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Real.iSup_of_isEmpty]
      exact (norm_nonneg _).trans (le_ciSup hbdd 0)
    · exact ciSup_le fun i ↦ le_ciSup hbdd (MultiIndexLE.single i)

/-- **The gradient norm is bounded by the norm of `W^{1,p}(Ω)`**: dropping the term `‖u‖_p` from
the `ℓ^p` sum does not increase it. -/
theorem gradNorm_le_norm (u : SobolevMultiIndex F b 1 p Ω μ) : gradNorm u ≤ ‖u‖ := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [norm_eq_max_gradNorm]
    exact le_max_right _ _
  · have hP : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
    rw [norm_eq_gradNorm hp]
    calc gradNorm u = (gradNorm u ^ p.toReal) ^ (1 / p.toReal) := by
          rw [← Real.rpow_mul (gradNorm_nonneg u), mul_one_div_cancel hP.ne', Real.rpow_one]
      _ ≤ (‖weakDeriv u 0‖ ^ p.toReal + gradNorm u ^ p.toReal) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (gradNorm_nonneg u) _)
            (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)) (by positivity)

/-- The `L^p(Ω)` norm of each partial derivative is at most the gradient norm. -/
theorem norm_weakDeriv_single_le_gradNorm (u : SobolevMultiIndex F b 1 p Ω μ) (i : ι) :
    ‖weakDeriv u (MultiIndexLE.single i)‖ ≤ gradNorm u :=
  PiLp.norm_apply_le (grad u) i

/-- **The Pythagorean identity in `L²(ν; ℓ²(ι; F))`**: for a finite family `g i` of measurable
functions, the square of the `L²` norm of `x ↦ (g i x)ᵢ` in the `ℓ²` product is the sum of the
squares of the `L²` norms of the `g i`. -/
theorem _root_.MeasureTheory.eLpNorm_toLp_two_sq {X ι F : Type*} [MeasurableSpace X]
    {ν : Measure X} [Fintype ι] [NormedAddCommGroup F] {g : ι → X → F}
    (hg : ∀ i, AEStronglyMeasurable (g i) ν)
    (hm : AEStronglyMeasurable (fun x ↦ (WithLp.toLp 2 fun i ↦ g i x : PiLp 2 fun _ : ι ↦ F)) ν) :
    eLpNorm (fun x ↦ (WithLp.toLp 2 fun i ↦ g i x : PiLp 2 fun _ : ι ↦ F)) 2 ν ^ 2
      = ∑ i, eLpNorm (g i) 2 ν ^ 2 := by
  have hG := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hm
  have hi : ∀ i, eLpNorm (g i) 2 ν ^ 2 = ∫⁻ x, ‖g i x‖ₑ ^ 2 ∂ν := fun i ↦ by
    have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero (hg i)
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using h
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at hG
  rw [hG]
  simp_rw [hi]
  rw [← lintegral_finsetSum' _ fun i _ ↦ (hg i).enorm.pow_const 2]
  refine lintegral_congr fun x ↦ ?_
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_pow, PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt,
    ENNReal.ofNNReal_finsetSum]

/-- **The pointwise gradient** `x ↦ (∂ᵢu(x))ᵢ` of `u ∈ W^{1,p}(Ω)`, as a function with values in
the Euclidean (`ℓ²`) product of copies of `F` — the reading `|∇u(x)|` of the gradient's length of
[brezis2011functional] §9.1, `‖∇u‖_{L^p(Ω)} = (∫_Ω |∇u|^p)^{1/p}`. -/
noncomputable def gradFn (u : SobolevMultiIndex F b 1 p Ω μ) (x : E) : PiLp 2 fun _ : ι ↦ F :=
  WithLp.toLp 2 fun i ↦ weakDeriv u (MultiIndexLE.single i) x

omit [Fact (1 ≤ p)] in
/-- The `i`-th component of the pointwise gradient is `∂ᵢu`. -/
@[simp]
theorem gradFn_apply (u : SobolevMultiIndex F b 1 p Ω μ) (x : E) (i : ι) :
    gradFn u x i = weakDeriv u (MultiIndexLE.single i) x :=
  rfl

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [Fact (1 ≤ p)] in
/-- The pointwise gradient is almost everywhere strongly measurable on `Ω`. -/
theorem aestronglyMeasurable_gradFn (u : SobolevMultiIndex F b 1 p Ω μ) :
    AEStronglyMeasurable (gradFn u) (μ.restrict (Ω : Set E)) :=
  (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable
    (aemeasurable_pi_iff.2 fun _ ↦ (Lp.aestronglyMeasurable _).aemeasurable).aestronglyMeasurable

omit [Fact (1 ≤ p)] in
/-- `∫_Ω |∇u|² = ∑ᵢ ‖∂ᵢu‖²_{L²(Ω)}` for `u ∈ W^{1,2}(Ω)`: the square of the `L²` norm of the
pointwise gradient is the sum of the squares of the `L²` norms of the partial derivatives. -/
theorem eLpNorm_gradFn_two_sq (u : SobolevMultiIndex F b 1 2 Ω μ) :
    eLpNorm (gradFn u) 2 (μ.restrict (Ω : Set E)) ^ 2
      = ∑ i, eLpNorm (weakDeriv u (MultiIndexLE.single i)) 2 (μ.restrict (Ω : Set E)) ^ 2 :=
  MeasureTheory.eLpNorm_toLp_two_sq (fun _ ↦ Lp.aestronglyMeasurable _)
    (aestronglyMeasurable_gradFn u)

omit [Fact (1 ≤ p)] in
/-- **At `p = 2` the two readings of `‖∇u‖_{L²(Ω)}` agree**: the Euclidean reading
`(∫_Ω |∇u|²)^{1/2}` (`eLpNorm (gradFn u) 2`) is the `ℓ²` reading `(∑ᵢ ‖∂ᵢu‖₂²)^{1/2}`
(`SobolevMultiIndex.gradNorm`). -/
theorem gradNorm_eq_toReal_eLpNorm_gradFn (u : SobolevMultiIndex F b 1 2 Ω μ) :
    gradNorm u = (eLpNorm (gradFn u) 2 (μ.restrict (Ω : Set E))).toReal := by
  have hsq : gradNorm u = √(∑ i, ‖weakDeriv u (MultiIndexLE.single i)‖ ^ 2) := by
    rw [gradNorm_eq_sum (p := 2) (by norm_num), Real.sqrt_eq_rpow]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [hsq]
  have h := congrArg ENNReal.toReal (eLpNorm_gradFn_two_sq u)
  rw [ENNReal.toReal_pow, ENNReal.toReal_sum fun i _ ↦ ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _)]
    at h
  simp only [ENNReal.toReal_pow, ← Lp.norm_def] at h
  rw [← h, Real.sqrt_sq ENNReal.toReal_nonneg]


end SobolevMultiIndex

end Gradient

/-! ### Separability -/

section Separable

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (p ≠ ⊤)] {Ω : Opens E} {μ : Measure E}

/-- **`W^{k,p}(Ω)` is separable for `1 ≤ p < ∞`** ([brezis2011functional] Proposition 9.1, and
Proposition 8.1 for the argument): `L^p(Ω)` is second countable for a σ-finite measure on a second
countable Borel space (`MeasureTheory.Lp.SecondCountableTopology`), a finite `ℓ^p` product of
second countable spaces is second countable, and so is a subspace. -/
instance SobolevMultiIndex.instSecondCountableTopology [SecondCountableTopology E] [BorelSpace E]
    [SFinite μ] [SecondCountableTopology F] :
    SecondCountableTopology (SobolevMultiIndex F b k p Ω μ) :=
  inferInstance

/-- **`W_0^{k,p}(Ω)` is separable for `1 ≤ p < ∞`** ([brezis2011functional] §9.4, the sentence
after the definition): a subspace of the second countable `W^{k,p}(Ω)`. -/
instance SobolevMultiIndexZero.instSecondCountableTopology [SecondCountableTopology E]
    [BorelSpace E] [SFinite μ] [SecondCountableTopology F] :
    SecondCountableTopology (SobolevMultiIndexZero F b k p Ω μ) :=
  inferInstance

end Separable

/-! ### Reflexivity -/

section Reflexive

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

/-- **`W^{k,p}(Ω)` is reflexive whenever `L^p(Ω)` is** ([brezis2011functional] Proposition 9.1,
and Proposition 8.1 for the argument): the ambient space is a finite `ℓ^p` product of copies of
`L^p(Ω)`, reflexive by `NormedSpace.instIsReflexivePiLp`, and `W^{k,p}(Ω)` is a closed subspace
of it (`SobolevMultiIndex.isClosed`), so `NormedSpace.isReflexive_of_isClosed` applies. For real
scalars and a σ-finite measure, `L^p(Ω)` is reflexive for `1 < p < ∞` by
`MeasureTheory.Lp.instIsReflexive` (under `[Fact (1 < p)] [Fact (p ≠ ∞)]`); at `p = 2` the
inner-product instance applies as well. -/
instance SobolevMultiIndex.instIsReflexive
    [NormedSpace.IsReflexive ℝ (Lp F p (μ.restrict (Ω : Set E)))] :
    NormedSpace.IsReflexive ℝ (SobolevMultiIndex F b k p Ω μ) :=
  NormedSpace.isReflexive_of_isClosed _ SobolevMultiIndex.isClosed

/-- **`W_0^{k,p}(Ω)` is reflexive whenever `L^p(Ω)` is** ([brezis2011functional] §9.4, the
sentence after the Definition): a closed subspace (`SobolevMultiIndexZero.isClosed`) of the
reflexive `W^{k,p}(Ω)`. -/
instance SobolevMultiIndexZero.instIsReflexive
    [NormedSpace.IsReflexive ℝ (Lp F p (μ.restrict (Ω : Set E)))] :
    NormedSpace.IsReflexive ℝ (SobolevMultiIndexZero F b k p Ω μ) :=
  NormedSpace.isReflexive_of_isClosed _ SobolevMultiIndexZero.isClosed

end Reflexive

/-! ### The spaces `W^{k,p}(Ω)` and `W_0^{k,p}(Ω)` on an open subset of `ℝ^N` -/

section Euclidean

/-- **The Sobolev space `W^{k,p}(Ω)` on an open set `Ω ⊆ ℝ^N`** of [brezis2011functional] §9.1
(the Definition, and the paragraph "The spaces `W^{m,p}(Ω)`"): the multi-index formulation over
the standard basis of `ℝ^N` and Lebesgue measure. Its norm is `(∑_{|α| ≤ k} ‖∂^α u‖_p^p)^{1/p}`
(`SobolevMultiIndex.norm_eq_sum`), the book's second, equivalent norm, and at `p = 2` it is the
Hilbert space `H^k(Ω)` with the book's inner product `∑_{|α| ≤ k} ∫_Ω ∂^α u ∂^α v`
(`SobolevMultiIndex.inner_eq`). The whole space is `Ω = ⊤`. Being an abbreviation, every
`SobolevMultiIndex` lemma applies to it unchanged. -/
noncomputable abbrev SobolevEuclidean (N k : ℕ) (p : ℝ≥0∞)
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  SobolevMultiIndex ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k p Ω volume

/-- **The Sobolev space `W_0^{k,p}(Ω)` on an open set `Ω ⊆ ℝ^N`** of [brezis2011functional] §9.4
(the Definition, and Remark 22 for `k ≥ 2`): the closure of the test functions in
`SobolevEuclidean N k p Ω`. The book closes `C_c^1(Ω)`, respectively `C_c^k(Ω)`, rather than
`C_c^∞(Ω)`; the closures agree because every compactly supported `W^{k,p}(Ω)` function lies in
this closure ([brezis2011functional] Lemma 9.5). -/
noncomputable abbrev SobolevEuclideanZero (N k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) :
    Submodule ℝ (SobolevEuclidean N k p Ω) :=
  SobolevMultiIndexZero ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k p Ω volume

/-- The `i`-th vector of the standard basis of `ℝ^N` is `e_i`. -/
theorem EuclideanSpace.basisFun_toBasis_apply {N : ℕ} (i : Fin N) :
    ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) i
      = EuclideanSpace.single i 1 := by
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]

end Euclidean

/-! ### The closed-graph lifts into `H^k(Ω)` -/

section ClosedGraph

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **A bounded lift into `H^k(Ω)` from the closed graph theorem**: if a continuous linear map
`S : X → L²(Ω)` from a Banach space `X` takes every `x` to the function of some element of
`H^k(Ω)`, then the lift `x ↦ U_x ∈ H^k(Ω)` is a bounded linear map
(`exists_continuousLinearMap_comp_eq_of_injective` along the injective inclusion
`H^k(Ω) → L²(Ω)`, `SobolevMultiIndex.fnL_injective`). -/
theorem SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {k : ℕ}
    {S : X →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hS : ∀ x, ∃ U : SobolevEuclidean N k 2 Ω,
      SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k 2 Ω volume U = S x) :
    ∃ T : X →L[ℝ] SobolevEuclidean N k 2 Ω,
      ∀ x, SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k 2 Ω volume (T x)
        = S x := by
  -- the injectivity with its type spelled out (instance search on the implicit form of
  -- `fnL_injective` exhausts the heartbeat budget)
  have hJ : Function.Injective
      (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k 2 Ω volume) :=
    SobolevMultiIndex.fnL_injective
  exact exists_continuousLinearMap_comp_eq_of_injective hJ hS

/-- **The `H^k` bound from the membership, by the closed graph theorem**: if a continuous linear
solution map `S : X → H¹(Ω)` from a Banach space `X` takes every `f` to the function of some
element of `H^k(Ω)`, then the `H^k` element is bounded by `C ‖f‖`: the lift `f ↦ U_f ∈ H^k(Ω)`
is bounded (`SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq` along
`H¹(Ω) → L²(Ω)`), and the element with the function of `S f` is unique
(`SobolevMultiIndex.ext_of_fn_ae_eq`). -/
theorem SobolevEuclidean.exists_norm_le_of_forall_exists_sobolev {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {k : ℕ}
    {S : X →L[ℝ] SobolevEuclidean N 1 2 Ω}
    (hS : ∀ f, ∃ U : SobolevEuclidean N k 2 Ω, SobolevMultiIndex.fn U
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] SobolevMultiIndex.fn (S f)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : X) (U : SobolevEuclidean N k 2 Ω),
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (S f) → ‖U‖ ≤ C * ‖f‖ := by
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume).comp
      S) (k := k) fun f ↦ by
      obtain ⟨U, hU⟩ := hS f
      exact ⟨U, Lp.ext hU⟩
  refine ⟨‖T‖, norm_nonneg _, fun f U hU ↦ ?_⟩
  have hJ : Function.Injective
      (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k 2 Ω volume) :=
    SobolevMultiIndex.fnL_injective
  have hUT : U = T f := by
    refine hJ ?_
    rw [hT f, ContinuousLinearMap.comp_apply]
    exact Lp.ext hU
  rw [hUT]
  exact T.le_opNorm f

end ClosedGraph
