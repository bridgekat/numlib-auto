/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Space.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Analysis.Sobolev.Space

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
* `listFDeriv l f`, differentiation of `f` along the entries of a list of directions, the vehicle of
  the symmetry statement `ContDiff.iteratedFDeriv_congr_perm`;
* `basisCoordProd b m`, the continuous multilinear form `y ↦ ∏ j, (b.repr (y j)) (m j)`, with which
  a continuous multilinear map is assembled from its values on tuples of basis vectors;
* `SobolevMultiIndexTuple F ι k p Ω μ`, the ambient space: the `ℓ^p` product over the multi-indices
  `α` with `|α| ≤ k` of the spaces `L^p(Ω)`, with `SobolevMultiIndexTuple.fn` the function a tuple
  carries, namely its component at `α = 0`;
* `SobolevMultiIndex F b k p Ω μ`, the Sobolev space itself, a submodule of that product, with
  `SobolevMultiIndex.fn` and `SobolevMultiIndex.weakDeriv`;
* `MemSobolevMultiIndex b f k p Ω μ`, the same space as a predicate on functions, with
  `MemSobolevMultiIndex.congr_ae` saying that it only sees the function up to a null set of `Ω`.

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
* `ContDiff.iteratedFDeriv_congr_perm`: **the iterated derivative of a `C^∞` function is symmetric
  in its arguments**, which Mathlib has only for order two or for analytic functions;
* `MemSobolev.memSobolevMultiIndex` and `memSobolev_of_memSobolevMultiIndex`: **the tensor
  formulation of `W^{k,p}(Ω)` in `Numlib/Analysis/Sobolev/Domain.lean` and the multi-index
  formulation here describe the same functions** — one way the `∂^α` are the tensor derivative
  evaluated at the tuple naming `α`, the other way the tensor is assembled from the `∂^α`, and the
  symmetry above is what lets it be evaluated at an unsorted tuple of basis vectors.

## Implementation notes

### Why a second formulation of the same space

The norm of Atkinson–Han's Definition 7.2.2 sums over the multi-indices `α`, and
`Numlib/Analysis/Sobolev/Space.lean` sums over the orders `n = |α|` instead, measuring all the
derivatives of order `n` by the operator norm of one tensor of `E [×n]→L[ℝ] F`. On a
finite-dimensional `E` the two are equivalent, the derivative tensors of a Sobolev function being
symmetric, so mathematically they give the same space and the same topology and either will do for
a Banach space statement. That they contain the same functions is
`MemSobolev.memSobolevMultiIndex` and `memSobolev_of_memSobolevMultiIndex` below; that the two norms
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
`memSobolev_of_memSobolevMultiIndex` is the converse — a function with all the `∂^α` in `L^p(Ω)`
has the tensor derivatives too. The proof of the converse recovers the tensor of order `n` from its
values on the tuples of basis vectors, `basisCoordProd` carrying the extension by multilinearity.
The values on a tuple of basis vectors that is not sorted
are `∂^α` of the *reordered* tuple, so the argument needs the symmetry of `iteratedFDeriv ℝ n φ x`
under permutations of its arguments for a `C^∞` function `φ`. Mathlib has that symmetry for `n = 2`
(`ContDiffAt.isSymmSndFDerivAt`) and for analytic functions of any order
(`ContDiffAt.domDomCongr_iteratedFDeriv`, which needs `ω`-smoothness) but not for `C^∞` functions of
order `n ≥ 3`, and a test function is not analytic; `ContDiff.iteratedFDeriv_congr_perm` supplies it
here, by transporting the commutation of two directional derivatives along a `List.Perm`. Only the
functions are matched, not the norms.

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

/-! ### Symmetry of the iterated derivative of a smooth function -/

section Symmetry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}

/-- Differentiating `f` successively along the entries of a list of directions, the head of the
list *innermost*: `listFDeriv [v₁, …, vₙ] f = ∂_{vₙ} ⋯ ∂_{v₁} f`.

Indexing by a list rather than by a tuple is what makes `listFDeriv_congr_perm` an induction on
`List.Perm`, whose `swap` constructor is exactly the transposition of the two innermost
derivatives; `ContDiff.listFDeriv_ofFn` identifies this with `iteratedFDeriv`. -/
noncomputable def listFDeriv (l : List E) (f : E → F) : E → F :=
  l.foldl (fun g v ↦ fun z ↦ fderiv ℝ g z v) f

/-- Differentiating along no directions at all leaves the function alone. -/
@[simp]
theorem listFDeriv_nil (f : E → F) : listFDeriv [] f = f := rfl

/-- Peeling the head of the list off `listFDeriv` takes the derivative along it first. -/
theorem listFDeriv_cons (v : E) (l : List E) (f : E → F) :
    listFDeriv (v :: l) f = listFDeriv l (fun z ↦ fderiv ℝ f z v) := rfl

/-- The derivative of a smooth function in a fixed direction is smooth. -/
theorem ContDiff.fderiv_apply_right (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ fun z ↦ fderiv ℝ f z v :=
  (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- Differentiating a smooth function along the entries of `List.ofFn y` is its `n`-th derivative
evaluated at the tuple `y`. Each step is `ContDiff.iteratedFDeriv_succ_apply_left'`, which moves one
derivative from the outside of the iterated derivative to the inside. -/
theorem ContDiff.listFDeriv_ofFn (hf : ContDiff ℝ ∞ f) {n : ℕ} (y : Fin n → E) (x : E) :
    listFDeriv (List.ofFn y) f x = iteratedFDeriv ℝ n f x y := by
  induction n generalizing f with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [List.ofFn_succ, listFDeriv_cons, ih (hf.fderiv_apply_right (y 0)),
      hf.iteratedFDeriv_succ_apply_left' n y x]
    rfl

/-- **Two directional derivatives of a smooth function commute.** This is the symmetry of the
second derivative, in the form in which `listFDeriv_congr_perm` consumes it: an equality of
functions rather than of values, so that it may be applied under a further derivative. -/
theorem ContDiff.fderiv_fderiv_comm (hf : ContDiff ℝ ∞ f) (v w : E) :
    (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y v) z w)
      = fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y w) z v := by
  funext x
  have h1 : (fun z ↦ iteratedFDeriv ℝ 1 f z ![v]) = fun z ↦ fderiv ℝ f z v := by
    funext z; rw [iteratedFDeriv_one_apply]; simp
  have h2 := hf.fderiv_iteratedFDeriv_apply 1 ![v] w x
  rw [h1, iteratedFDeriv_one_apply] at h2
  simpa using h2

/-- **Differentiating a smooth function along a list of directions does not depend on the order of
the list.** The induction is on `List.Perm`: its `swap` constructor is the transposition of the two
innermost derivatives, which is `ContDiff.fderiv_fderiv_comm`, and its `cons` constructor peels one
derivative off and applies the induction hypothesis to the differentiated function, which is smooth
again. -/
theorem listFDeriv_congr_perm {l₁ l₂ : List E} (h : l₁.Perm l₂) {f : E → F}
    (hf : ContDiff ℝ ∞ f) : listFDeriv l₁ f = listFDeriv l₂ f := by
  induction h generalizing f with
  | nil => rfl
  | cons a _ ih => rw [listFDeriv_cons, listFDeriv_cons, ih (hf.fderiv_apply_right a)]
  | swap a b l =>
    rw [listFDeriv_cons, listFDeriv_cons, listFDeriv_cons, listFDeriv_cons,
      hf.fderiv_fderiv_comm b a]
  | trans _ _ ih₁ ih₂ => rw [ih₁ hf, ih₂ hf]

/-- **The iterated derivative of a `C^∞` function is symmetric in its arguments**: it takes the same
value at two tuples of directions that are permutations of each other.

Mathlib has this for order two (`ContDiffAt.isSymmSndFDerivAt`) and, for any order, for analytic
functions (`ContDiffAt.domDomCongr_iteratedFDeriv`, which asks for `ω`-smoothness); this is the
`C^∞` statement of any order, obtained by transporting the commutation of two directional
derivatives along a `List.Perm`. The two tuples are allowed to have different lengths — the
hypothesis forces them to be equal — so that it applies to a pair of tuples whose lengths agree only
propositionally, such as `Fin n` and `Fin (∑ i, α i)`. -/
theorem ContDiff.iteratedFDeriv_congr_perm (hf : ContDiff ℝ ∞ f) {n₁ n₂ : ℕ}
    {y₁ : Fin n₁ → E} {y₂ : Fin n₂ → E} (h : (List.ofFn y₁).Perm (List.ofFn y₂)) (x : E) :
    iteratedFDeriv ℝ n₁ f x y₁ = iteratedFDeriv ℝ n₂ f x y₂ := by
  rw [← hf.listFDeriv_ofFn y₁ x, ← hf.listFDeriv_ofFn y₂ x, listFDeriv_congr_perm h hf]

end Symmetry

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
  rw [Submodule.coe_norm, PiLp.norm_eq_sum
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp)]
  rfl

omit [Fact (1 ≤ p)] in
/-- **The norm of `W^{k,∞}(Ω)` is the norm of Atkinson and Han**, *Theoretical Numerical Analysis:
A Functional Analysis Framework*, 3rd edition, Definition 7.2.2, for `p = ∞`: the largest, over the
multi-indices `α` with `|α| ≤ k`, of the `L^∞(Ω)` norms of the `∂^α`. -/
theorem norm_eq_ciSup (u : SobolevMultiIndex F b k ⊤ Ω μ) :
    ‖u‖ = ⨆ α : MultiIndexLE ι k, ‖weakDeriv u α‖ := by
  rw [Submodule.coe_norm, PiLp.norm_eq_ciSup]
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
one.

The name is `memSobolev_of_memSobolevMultiIndex` and not `MemSobolevMultiIndex.memSobolev` because
`Numlib/Analysis/Sobolev/Tempered.lean` has already taken the latter for the corresponding
statement about Mathlib's Bessel potential spaces. -/
theorem memSobolev_of_memSobolevMultiIndex (h : MemSobolevMultiIndex b f k p Ω μ) :
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
