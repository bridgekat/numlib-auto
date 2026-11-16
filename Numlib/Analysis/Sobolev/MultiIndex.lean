/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# Sobolev spaces with derivatives indexed by multi-indices

Let $E$ be a real normed space with a basis $b = (b_i)_{i \in \iota}$ indexed by a finite linearly
ordered type $\iota$, let $\Omega \subseteq E$ be open, let $\mu$ be a measure on $E$, and let $F$
be a real normed space. A multi-index is a function $\alpha : \iota \to \mathbb{N}$ of order
$|\alpha| = \sum_i \alpha_i$, and $\partial^\alpha$ is the weak derivative along the directions
$b_i$, each repeated $\alpha_i$ times. For $k \in \mathbb{N}$ and $p \in [1, \infty]$, the Sobolev
space $W^{k,p}(\Omega)$ consists of the functions $v \in L^p(\Omega)$ whose weak derivatives
$\partial^\alpha v$ with $|\alpha| \le k$ exist and lie in $L^p(\Omega)$, with the norm
$$\|v\|_{k,p,\Omega} = \Big(\sum_{|\alpha| \le k} \|\partial^\alpha v\|_{L^p(\Omega)}^p\Big)^{1/p},
  \qquad \|v\|_{k,\infty,\Omega} = \max_{|\alpha| \le k} \|\partial^\alpha v\|_{L^\infty(\Omega)}.$$
This is Definition 7.2.2 of [han2009theoretical].

The module proves that $W^{k,p}(\Omega)$ is a Banach space (Theorem 7.2.3 of [han2009theoretical]),
and that for $p = 2$ its norm comes from the inner product $(u, v)_k = \int_\Omega \sum_{|\alpha|
\le k} \langle \partial^\alpha u, \partial^\alpha v \rangle$, so that
$H^k(\Omega) = W^{k,2}(\Omega)$ is a Hilbert space (Corollary 7.2.4). It defines the closed subspace
$W_0^{k,p}(\Omega)$, the closure of the test functions (Definition 7.2.9). It shows that this
formulation and the tensor formulation of `Numlib.Analysis.Sobolev.Domain` contain the same
functions, and that the inductive definition $W^{m+1,p}(\Omega) = \{u \in W^{m,p}(\Omega) :
\partial_i u \in W^{m,p}(\Omega) \text{ for all } i\}$ of [brezis2011functional], §9.1, agrees with
the multi-index definition. It also gives the separability and the reflexivity of the spaces
([brezis2011functional], Proposition 9.1), the gradient norm on $W^{1,p}(\Omega)$, the spaces on an
open subset of $\mathbb{R}^N$, and bounded lifts into these spaces by the closed graph theorem.

## Main definitions

* `MultiIndexLE`: the multi-indices $\alpha : \iota \to \mathbb{N}$ with $|\alpha| \le k$.
* `MultiIndexEq`: the multi-indices with $|\alpha| = k$.
* `multiIndexTuple`: the tuple of the $|\alpha|$ directions that name $\partial^\alpha$, the vector
  $b_i$ repeated $\alpha_i$ times, with the indices in increasing order.
* `multiIndexCount`: the multi-index of a tuple of indices, which counts how often each index occurs
  in the tuple.
* `basisCoordProd`: the continuous multilinear form $y \mapsto \prod_j b^*_{m_j}(y_j)$, with which a
  continuous multilinear map is assembled from its values on tuples of basis vectors.
* `SobolevMultiIndexTuple`: the $\ell^p$ product of copies of $L^p(\Omega)$ over the multi-indices
  $\alpha$ with $|\alpha| \le k$.
* `SobolevMultiIndex`: the space $W^{k,p}(\Omega)$, a submodule of this product.
* `MemSobolevMultiIndex`: the predicate that a function lies in $W^{k,p}(\Omega)$.
* `SobolevMultiIndexZero`: the space $W_0^{k,p}(\Omega)$, the closure of the test functions in
  $W^{k,p}(\Omega)$.
* `SobolevMultiIndex.weakDerivL` and `SobolevMultiIndex.fnL`: the weak derivative
  $u \mapsto \partial^\alpha u$ and the inclusion $W^{k,p}(\Omega) \to L^p(\Omega)$ as bounded
  linear maps.
* `SobolevMultiIndex.gradNorm`: the gradient norm $\|\nabla u\|_{L^p(\Omega)}$ on $W^{1,p}(\Omega)$.
* `SobolevEuclidean` and `SobolevEuclideanZero`: the spaces $W^{k,p}(\Omega)$ and
  $W_0^{k,p}(\Omega)$ of [brezis2011functional], §9.1 and §9.4, on an open set
  $\Omega \subseteq \mathbb{R}^N$ with the standard basis and Lebesgue measure.

## Main results

* `SobolevMultiIndex.instCompleteSpace`: $W^{k,p}(\Omega)$ is a Banach space (Theorem 7.2.3 of
  [han2009theoretical]).
* `SobolevMultiIndex.norm_eq_sum` and `SobolevMultiIndex.norm_eq_ciSup`: the norm of
  $W^{k,p}(\Omega)$ is the norm of Definition 7.2.2 of [han2009theoretical].
* `SobolevMultiIndex.inner_eq`: for $p = 2$, the inner product of $W^{k,2}(\Omega)$ is $(u, v)_k =
  \int_\Omega \sum_{|\alpha| \le k} \langle \partial^\alpha u, \partial^\alpha v \rangle$ (Corollary
  7.2.4 of [han2009theoretical]).
* `SobolevMultiIndex.memSobolevMultiIndex`, `MemSobolevMultiIndex.exists_sobolevMultiIndex` and
  `SobolevMultiIndex.ext_of_fn_ae_eq`: the type and the predicate describe the same functions, and
  each function comes from exactly one element.
* `memSobolev_iff_memSobolevMultiIndex`: the tensor formulation and the multi-index formulation of
  $W^{k,p}(\Omega)$ contain the same functions.
* `HasWeakIteratedLineDerivOn.of_perm`: a weak derivative along a tuple of directions is a weak
  derivative along every rearrangement of the tuple.
* `memSobolevMultiIndex_succ_iff`: $f \in W^{m+1,p}(\Omega)$ if and only if $f \in W^{m,p}(\Omega)$
  and $\partial_i f \in W^{m,p}(\Omega)$ for all $i$.
* `SobolevMultiIndex.norm_eq_gradNorm`: for $p < \infty$, the norm of $W^{1,p}(\Omega)$ is
  $(\|u\|_{L^p(\Omega)}^p + \|\nabla u\|_{L^p(\Omega)}^p)^{1/p}$.
* `SobolevMultiIndex.instSecondCountableTopology`: $W^{k,p}(\Omega)$ is separable for
  $1 \le p < \infty$.
* `SobolevMultiIndex.instIsReflexive`: $W^{k,p}(\Omega)$ is reflexive when $L^p(\Omega)$ is
  reflexive.
* `SobolevMultiIndex.exists_continuousLinearMap_of_forall_memSobolevMultiIndex`: a bounded linear
  map into $L^q(\Omega')$ whose values lie in $W^{k',q}(\Omega')$ lifts to a bounded linear map into
  $W^{k',q}(\Omega')$.

## Proof outline

The space $W^{k,p}(\Omega)$ is closed in the $\ell^p$ product of the spaces $L^p(\Omega)$: for a
fixed test function $\varphi$, the integration by parts formula is an equation between two
functionals of the family, and these functionals are continuous by Hölder's inequality. A function
of the tensor formulation lies in the multi-index formulation, because $\partial^\alpha f$ is the
tensor derivative of order $|\alpha|$ evaluated at the tuple that names $\alpha$. For the converse,
the tensor derivative of order $n$ is assembled from its values on tuples of basis vectors and
extended by multilinearity with `basisCoordProd`. The value on a tuple that is not sorted is
$\partial^\alpha$ of the sorted tuple, so the argument needs the symmetry of the iterated derivative
$D^n \varphi(x)$ of a $C^\infty$ function $\varphi$ under permutations of its arguments
(`ContDiff.iteratedFDeriv_congr_perm`). The inductive description of $W^{m+1,p}(\Omega)$ reads
$\partial^{\alpha + e_i}$ as $\partial^\alpha \partial_i$ by the same symmetry.

## Implementation notes

* The module `Numlib.Analysis.Sobolev.Space` gives the same space in another form: it sums over the
  orders $n = |\alpha|$, and it measures all derivatives of order $n$ together by the operator norm
  of one tensor in `E [×n]→L[ℝ] F`. On a finite-dimensional $E$ the two norms are equivalent,
  because the derivative tensors of a Sobolev function are symmetric. So the two formulations give
  the same space with the same topology. They contain the same functions
  (`MemSobolev.memSobolevMultiIndex` and `MemSobolevMultiIndex.memSobolev`). The equivalence of the
  norms is not formalized, and the two formulations are separate types with separate proofs.
* The two norms are not equal, and for $p = 2$, $k \ge 2$ and $\dim E \ge 2$ the difference is that
  between a Banach space and a Hilbert space. The operator norm on the $n$-linear maps fails the
  parallelogram law when $n \ge 2$ and $\dim E \ge 2$: for $E = \mathbb{R}^2$, $F = \mathbb{R}$ and
  $n = 2$ it is the spectral norm of a $2 \times 2$ matrix. So no inner product induces it. The norm
  here is the $\ell^2$ norm of a finite product of $L^2$ spaces. For $k \le 1$, or for
  $\dim E \le 1$, the tensor formulation is an inner product space too. Corollary 7.2.4 of
  [han2009theoretical] is therefore a statement about this formulation. Its inner product is the
  inner product of `PiLp 2` of $L^2$ spaces, restricted to a submodule, and nothing is added to it.
* The multi-index formulation depends on the basis $b$. Unlike the operator norm of the tensor,
  $\sum_{|\alpha| = n} \|\partial^\alpha v\|^2$ is not invariant under rotations of $E$ when
  $n \ge 2$: for $E = \mathbb{R}^2$ and $n = 2$ it is the sum of the squares of the three distinct
  entries of the Hessian, not of its four entries. [han2009theoretical] works in the coordinates of
  $\mathbb{R}^d$, so its basis is fixed. Here the basis is an explicit argument.
* An element of `SobolevMultiIndex F b k p Ω μ` is the whole family
  $(\partial^\alpha u)_{|\alpha| \le k}$. Its function, the component at $\alpha = 0$, is
  `SobolevMultiIndex.fn`. The type `Lp F p (μ.restrict Ω)` is the space $L^p(\Omega)$.
* Mathlib has the symmetry of the iterated derivative for $n = 2$ (`ContDiffAt.isSymmSndFDerivAt`)
  and for analytic functions of any order (`ContDiffAt.domDomCongr_iteratedFDeriv`, which needs
  $\omega$-smoothness), but not for $C^\infty$ functions of order $n \ge 3$, and a test function is
  not analytic. `ContDiff.iteratedFDeriv_congr_perm` supplies it: it transports the commutation of
  two directional derivatives along a `List.Perm`.
* Like `Numlib.Analysis.Sobolev.WeakDeriv`, `Numlib.Analysis.Sobolev.Domain` and
  `Numlib.Analysis.Sobolev.Space`, this module stands in for Mathlib PR 32305 and its continuation
  `grunweg/SobolevSlobodeckij` (Michael Rothgang, Filippo Nuccio and Floris van Doorn). There, as in
  those modules, the weak derivative is tensor-valued and carries no basis. The Hilbert space
  structure of $H^k(\Omega)$ needs the multi-index indexing, and it is obtained as `PiLp 2` of $L^2$
  spaces and a closed submodule of it.
-/

open Filter MeasureTheory Module Set TopologicalSpace

open scoped ContDiff Distributions ENNReal Topology

/-! ### Multi-indices -/

section MultiIndex

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-- The type of **multi-indices of order at most $k$** over the finite index type $\iota$: the
functions $\alpha : \iota \to \mathbb{N}$ with $|\alpha| = \sum_i \alpha_i \le k$. -/
abbrev MultiIndexLE (ι : Type*) [Fintype ι] (k : ℕ) : Type _ := {α : ι → ℕ // ∑ i, α i ≤ k}

namespace MultiIndexLE

/-- There are finitely many multi-indices of order at most $k$, because each entry of such a
multi-index is at most $k$. -/
noncomputable instance instFintype : Fintype (MultiIndexLE ι k) := by
  classical
  exact Fintype.ofInjective (fun α i ↦ (⟨α.1 i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (f := α.1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
        α.2)⟩ : Fin (k + 1)))
    fun _ _ h ↦ Subtype.ext (funext fun i ↦ congrArg Fin.val (congrFun h i))

/-- The multi-index $0$, of order $0$. The derivative $\partial^0$ that it names is the function
itself. -/
instance instZero : Zero (MultiIndexLE ι k) := ⟨⟨0, by simp⟩⟩

/-- The multi-index $0$ of `MultiIndexLE ι k` is the zero function on $\iota$. -/
@[simp]
theorem coe_zero : ((0 : MultiIndexLE ι k) : ι → ℕ) = 0 := rfl

/-- The zero function $\iota \to \mathbb{N}$ has order $\sum_i 0 = 0$.

The statement is about the zero function and not about `(0 : MultiIndexLE ι k)`, because the
order appears in this form. -/
theorem sum_zero : ∑ _i : ι, (0 : ι → ℕ) _i = 0 := Fintype.sum_eq_zero _ fun _ ↦ rfl

/-- Let $k' \le k$. The inclusion of the multi-indices of order at most $k'$ into the multi-indices
of order at most $k$ is injective. -/
theorem castLE_injective {k' : ℕ} (hk : k' ≤ k) :
    Function.Injective fun α : MultiIndexLE ι k' ↦ (⟨α.1, α.2.trans hk⟩ : MultiIndexLE ι k) :=
  fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)


/-! ### The multi-indices of order one -/

section Single

variable [DecidableEq ι]

/-- The multi-index $e_i$ of order one, which has the entry $1$ at $i$ and the entry $0$ elsewhere.
It names the partial derivative $\partial_i$: `SobolevMultiIndex.weakDeriv u
(MultiIndexLE.single i)` is $\partial u / \partial x_i$. -/
def single (i : ι) : MultiIndexLE ι 1 := ⟨Pi.single i 1, by simp⟩

/-- The multi-index $e_i$ is the function `Pi.single i 1`. -/
@[simp]
theorem coe_single (i : ι) : ((single i : MultiIndexLE ι 1) : ι → ℕ) = Pi.single i 1 := rfl

/-- The map $i \mapsto e_i$ is injective. -/
theorem single_injective : Function.Injective (single : ι → MultiIndexLE ι 1) := fun i j h ↦ by
  have := congrArg (fun α : MultiIndexLE ι 1 ↦ (α : ι → ℕ) i) h
  by_contra hij
  simp [Pi.single_eq_of_ne hij] at this

/-- For every $i \in \iota$, $e_i \neq 0$. -/
theorem single_ne_zero (i : ι) : (single i : MultiIndexLE ι 1) ≠ 0 := fun h ↦ by
  have := congrArg (fun α : MultiIndexLE ι 1 ↦ (α : ι → ℕ) i) h
  simp at this

/-- A multi-index $\alpha$ of order at most one is $0$ or $e_i$ for some $i \in \iota$. -/
theorem eq_zero_or_exists_eq_single (α : MultiIndexLE ι 1) : α = 0 ∨ ∃ i, α = single i := by
  by_cases h : ∀ i, (α : ι → ℕ) i = 0
  · exact Or.inl (Subtype.ext (funext h))
  right
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine ⟨i, Subtype.ext (funext fun j ↦ ?_)⟩
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

/-- Let $M$ be an additive commutative monoid, and let $f$ be a function from the multi-indices of
order at most one to $M$. Then
$$\sum_{|\alpha| \le 1} f(\alpha) = f(0) + \sum_{i \in \iota} f(e_i).$$

This identity turns the norm of $W^{1,p}(\Omega)$, a sum over the multi-indices $\alpha$ with
$|\alpha| \le 1$, into the term of $\|u\|_{L^p(\Omega)}$ plus the terms of the gradient. -/
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

/-- For $i \in \iota$ and a multi-index $\alpha$ of order at most $k$, the multi-index
$\alpha + e_i$ of order at most $k + 1$. -/
def addSingle (i : ι) (α : MultiIndexLE ι k) : MultiIndexLE ι (k + 1) :=
  ⟨α.1 + Pi.single i 1, by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    omega⟩

/-- The function that underlies `MultiIndexLE.addSingle i α` is $\alpha + e_i$. -/
@[simp]
theorem coe_addSingle (i : ι) (α : MultiIndexLE ι k) :
    ((MultiIndexLE.addSingle i α : MultiIndexLE ι (k + 1)) : ι → ℕ) = α.1 + Pi.single i 1 :=
  rfl

/-- For each $i \in \iota$, the map $\alpha \mapsto \alpha + e_i$ from the multi-indices of order at
most $k$ to the multi-indices of order at most $k + 1$ is injective. -/
theorem addSingle_injective (i : ι) :
    Function.Injective (MultiIndexLE.addSingle i : MultiIndexLE ι k → MultiIndexLE ι (k + 1)) :=
  fun _ _ h ↦ Subtype.ext (add_right_cancel (Subtype.mk.inj h))

/-- Every nonzero multi-index $\beta$ of order at most $k + 1$ has the form $\beta = \beta' + e_i$
for some $i \in \iota$ and some multi-index $\beta'$ of order at most $k$. -/
theorem exists_eq_addSingle (β : MultiIndexLE ι (k + 1))
    (hβ : β ≠ 0) : ∃ (i : ι) (β' : MultiIndexLE ι k), β = MultiIndexLE.addSingle i β' := by
  have hex : ∃ i, β.1 i ≠ 0 := by
    by_contra h
    push Not at h
    exact hβ (Subtype.ext (funext h))
  obtain ⟨i, hi⟩ := hex
  have hle : ∀ x, (Pi.single i 1 : ι → ℕ) x ≤ β.1 x := fun x ↦ by
    by_cases hx : x = i
    · subst hx
      simp only [Pi.single_eq_same]
      omega
    · simp [Pi.single_eq_of_ne hx]
  refine ⟨i, ⟨fun x ↦ β.1 x - (Pi.single i 1 : ι → ℕ) x, ?_⟩, Subtype.ext ?_⟩
  · have hsum : ∑ x, (β.1 x - (Pi.single i 1 : ι → ℕ) x) + ∑ x, (Pi.single i 1 : ι → ℕ) x
        = ∑ x, β.1 x := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ tsub_add_cancel_of_le (hle x)
    simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true] at hsum
    change ∑ x, (β.1 x - (Pi.single i 1 : ι → ℕ) x) ≤ k
    omega
  · simp only [MultiIndexLE.coe_addSingle]
    funext x
    exact (tsub_add_cancel_of_le (hle x)).symm

/-- The multi-index $e_i$, as a multi-index of order at most $k + 1$. -/
def singleLE (i : ι) : MultiIndexLE ι (k + 1) :=
  ⟨Pi.single i 1, by simp⟩

/-- For every $i \in \iota$, $0 + e_i = e_i$, where $0$ is the multi-index $0$ of order at most $k$
and $e_i$ is `MultiIndexLE.singleLE i`. -/
theorem addSingle_zero (i : ι) :
    MultiIndexLE.addSingle i (0 : MultiIndexLE ι k) = MultiIndexLE.singleLE i :=
  Subtype.ext (zero_add _)

end Single

end MultiIndexLE

/-- The type of **multi-indices of order exactly $k$** over the finite index type $\iota$: the
multi-indices $\alpha$ of order at most $k$ with $|\alpha| = \sum_i \alpha_i = k$. The seminorms
built from the derivatives of the highest order are sums over these multi-indices. -/
abbrev MultiIndexEq (ι : Type*) [Fintype ι] (k : ℕ) : Type _ :=
  {α : MultiIndexLE ι k // ∑ i, α.1 i = k}

/-- There are finitely many multi-indices of order exactly $k$, because there are finitely many of
order at most $k$. -/
noncomputable instance MultiIndexEq.instFintype : Fintype (MultiIndexEq ι k) := Fintype.ofFinite _

end MultiIndex

/-! ### The directions that name a multi-index -/

section Directions

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $(b_i)_{i \in \iota}$ be a family of vectors of $E$ indexed by a finite linearly ordered
type, and let $\alpha : \iota \to \mathbb{N}$. Let $i_1 < \dots < i_r$ be the elements of
$\iota$. The **directions that name $\alpha$** form the list
$$(\underbrace{b_{i_1}, \dots, b_{i_1}}_{\alpha_{i_1}}, \dots,
  \underbrace{b_{i_r}, \dots, b_{i_r}}_{\alpha_{i_r}}).$$
Differentiation along this list is $\partial^\alpha = \partial_{i_1}^{\alpha_{i_1}} \cdots
\partial_{i_r}^{\alpha_{i_r}}$. -/
def multiIndexDirections (b : ι → E) (α : ι → ℕ) : List E :=
  (Finset.univ.sort (· ≤ ·)).flatMap fun i ↦ List.replicate (α i) (b i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The list of directions that name $\alpha$ has the length $|\alpha| = \sum_i \alpha_i$. -/
theorem length_multiIndexDirections (b : ι → E) (α : ι → ℕ) :
    (multiIndexDirections b α).length = ∑ i, α i := by
  rw [multiIndexDirections, List.length_flatMap]
  simp only [List.length_replicate]
  rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq (Finset.univ : Finset ι) (· ≤ ·),
    Multiset.map_coe, Multiset.sum_coe]

/-- The directions that name the multi-index $\alpha$, as a tuple of length $|\alpha|$. The weak
derivative of $v$ along this tuple, in the sense of `HasWeakIteratedLineDerivOn`, is the weak
derivative $\partial^\alpha v$. -/
def multiIndexTuple (b : ι → E) (α : ι → ℕ) : Fin (∑ i, α i) → E :=
  fun j ↦ (multiIndexDirections b α).get (j.cast (length_multiIndexDirections b α).symm)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The list `multiIndexDirections b α` is the list of the entries of the tuple
`multiIndexTuple b α`. -/
theorem multiIndexDirections_eq_ofFn (b : ι → E) (α : ι → ℕ) :
    multiIndexDirections b α = List.ofFn (multiIndexTuple b α) := by
  refine (List.ext_getElem (by simp [length_multiIndexDirections]) fun i h1 h2 ↦ ?_).symm
  simp [multiIndexTuple]

end Directions

/-! ### The multi-index of a tuple of basis indices -/

section Count

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}

/-- For a tuple $m = (m_0, \dots, m_{n-1})$ of indices in $\iota$, the multi-index $\alpha$ with
$$\alpha_i = \#\{j : m_j = i\},$$
the number of times that $i$ occurs in $m$. After the directions are put in increasing order of
the index, the derivative $\partial_{b_{m_0}} \cdots \partial_{b_{m_{n-1}}}$ is
$\partial^\alpha$. -/
def multiIndexCount (m : Fin n → ι) : ι → ℕ :=
  fun i ↦ {j ∈ (Finset.univ : Finset (Fin n)) | m j = i}.card

/-- The multi-index of a tuple $m$ of length $n$ has the order $n$. -/
theorem sum_multiIndexCount (m : Fin n → ι) : ∑ i, multiIndexCount m i = n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := m) (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset ι))
    (fun j _ ↦ Finset.mem_univ (m j))
  simpa [multiIndexCount] using h.symm

/-- As a multiset, the list of directions that name $\alpha$ consists of $\alpha_i$ copies of $b_i$
for each $i \in \iota$. The multiset forgets the order that `multiIndexDirections` gives to the
directions. -/
theorem coe_multiIndexDirections (b : ι → E) (α : ι → ℕ) :
    ((multiIndexDirections b α : List E) : Multiset E)
      = ∑ i, Multiset.replicate (α i) (b i) := by
  rw [multiIndexDirections, ← Multiset.coe_bind]
  simp only [Finset.sort_eq, Multiset.coe_replicate]
  rfl

/-- For a tuple $g$ of length $n$, the multiset of the entries of `List.ofFn g` is the sum
$\sum_j \{g_j\}$ of the singletons of its entries. -/
theorem Multiset.coe_ofFn (g : Fin n → E) :
    ((List.ofFn g : List E) : Multiset E) = ∑ j, ({g j} : Multiset E) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, ← ih (fun j ↦ g j.succ)]
    simp [Multiset.cons_coe]

/-- Let $m$ be a tuple of $n$ indices in $\iota$. The tuple $(b_{m_0}, \dots, b_{m_{n-1}})$ is a
permutation of the list of directions that name the multi-index `multiIndexCount m`. Both lists
contain $b_i$ exactly $\#\{j : m_j = i\}$ times. -/
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

/-! ### Products over the tuple that names a multi-index -/

section Products

/-- Let $M$ be a commutative monoid and let $(f_i)_{i \in \iota}$ be a finite family of multisets of
elements of $M$. The product of the elements of $\sum_i f_i$ is the product over $i$ of the
products of the elements of $f_i$. -/
theorem prod_multiset_sum {ι M : Type*} [CommMonoid M] [Fintype ι] (f : ι → Multiset M) :
    (∑ i, f i).prod = ∏ i, (f i).prod :=
  Multiset.prod_sum f Finset.univ

/-- Let $M$ be a commutative monoid, let $g$ be a function with values in $M$, and let $t$ be the
tuple of directions that name $\alpha$. Then
$$\prod_j g(t_j) = \prod_{i \in \iota} g(b_i)^{\alpha_i},$$
because $t$ lists $b_i$ exactly $\alpha_i$ times. -/
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

/-! ### Multilinear maps in a basis -/

section MultilinearBasis

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $b$ be a basis of $E$ indexed by the finite type $\iota$, with coordinate functionals
$b^*_i$, and let $m = (m_0, \dots, m_{n-1})$ be a tuple of indices. The continuous $n$-linear
form
$$y \mapsto \prod_j b^*_{m_j}(y_j)$$
on $E$.

With `ContinuousMultilinearMap.apply_eq_sum_basis`, these forms expand a continuous multilinear
map in its values on tuples of basis vectors, and so assemble a continuous multilinear map from
prescribed values on these tuples. The coordinate functionals are continuous because $E$ is
finite-dimensional, its basis being indexed by a finite type. -/
noncomputable def basisCoordProd (b : Basis ι ℝ E) {n : ℕ} (m : Fin n → ι) : E [×n]→L[ℝ] ℝ :=
  letI := b.finiteDimensional_of_finite
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
    fun j ↦ (b.coord (m j)).toContinuousLinearMap

/-- The form `basisCoordProd b m` takes $y$ to $\prod_j b^*_{m_j}(y_j)$, the product over the slots
$j$ of the coordinate $m_j$ of the argument $y_j$. -/
@[simp]
theorem basisCoordProd_apply (b : Basis ι ℝ E) {n : ℕ} (m : Fin n → ι) (y : Fin n → E) :
    basisCoordProd b m y = ∏ j, b.repr (y j) (m j) := by
  rw [basisCoordProd, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  simp

/-- Let $b$ be a basis of $E$ indexed by the finite type $\iota$, let $G$ be a real normed space,
and let $T : E^n \to G$ be continuous and $n$-linear. Then for all $y \in E^n$,
$$T(y) = \sum_{m : \{0, \dots, n-1\} \to \iota} \Big(\prod_j b^*_{m_j}(y_j)\Big)\,
  T(b_{m_0}, \dots, b_{m_{n-1}}).$$
So $T$ is determined by its values on tuples of basis vectors.

The proof writes each argument in the basis and expands by multilinearity. -/
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

/-!
### Weak derivatives along a permuted tuple of directions

The integration by parts formula that defines a weak derivative along a tuple $y$ tests against
$D^n \varphi(x)[y]$, and for a test function $\varphi$ this is symmetric in the entries of $y$
(`ContDiff.iteratedFDeriv_congr_perm`). So a weak derivative along $y$ is a weak derivative along
every rearrangement of $y$, and the new direction of a longer tuple can be differentiated first as
well as last. This lets $\partial^{\alpha + e_i}$ be read as $\partial^\alpha \partial_i$, although
`multiIndexTuple` lists the directions in increasing order of the index.
-/

section Perm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {μ : Measure E} {f w : E → F}

namespace HasWeakIteratedLineDerivOn

/-- Let $y_1 \in E^{n_1}$ and $y_2 \in E^{n_2}$ be tuples of directions whose lists of entries are
permutations of each other. If $w$ is a weak derivative of $f$ along $y_1$ on $\Omega$, then $w$
is a weak derivative of $f$ along $y_2$ on $\Omega$.

The lengths $n_1$ and $n_2$ are not assumed to be equal. They are equal, because a permutation
preserves the length. -/
theorem of_perm {n₁ n₂ : ℕ} {y₁ : Fin n₁ → E} {y₂ : Fin n₂ → E}
    (hy : (List.ofFn y₁).Perm (List.ofFn y₂)) (h : HasWeakIteratedLineDerivOn y₁ f w Ω μ) :
    HasWeakIteratedLineDerivOn y₂ f w Ω μ := by
  obtain rfl : n₁ = n₂ := by simpa using hy.length_eq
  refine ⟨h.locallyIntegrableOn, h.locallyIntegrableOn_weakDeriv, fun φ ↦ ?_⟩
  have key : ∀ x, iteratedFDeriv ℝ n₁ (φ : E → ℝ) x y₂ = iteratedFDeriv ℝ n₁ (φ : E → ℝ) x y₁ :=
    fun x ↦ (φ.contDiff.iteratedFDeriv_congr_perm hy x).symm
  simp_rw [key]
  exact h.integral_smul_eq φ

/-- Let $y \in E^n$ and let $\sigma$ be a permutation of $\{0, \dots, n-1\}$. If $w$ is a weak
derivative of $f$ along $y$ on $\Omega$, then $w$ is a weak derivative of $f$ along
$y \circ \sigma$ on $\Omega$. -/
theorem comp_perm {n : ℕ} {y : Fin n → E} (h : HasWeakIteratedLineDerivOn y f w Ω μ)
    (σ : Equiv.Perm (Fin n)) : HasWeakIteratedLineDerivOn (y ∘ σ) f w Ω μ :=
  h.of_perm (σ.ofFn_comp_perm y).symm

/-- Let $z \in E$ and $y \in E^n$. If $g$ is a weak derivative of $f$ along the single direction $z$
on $\Omega$, and $u$ is a weak derivative of $g$ along $y$ on $\Omega$, then $u$ is a weak
derivative of $f$ along the tuple $(z, y_0, \dots, y_{n-1})$ on $\Omega$.

`HasWeakIteratedLineDerivOn.cons` differentiates along $z$ after $y$. This lemma differentiates
along $z$ first. For a test function the two orders agree
(`ContDiff.fderiv_iteratedFDeriv_apply`), and the proof uses only this fact. -/
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

/-- Let $z \in E$ and $y \in E^n$. If $g$ is a weak derivative of $f$ along the single direction $z$
on $\Omega$, and $u$ is a weak derivative of $f$ along the tuple $(z, y_0, \dots, y_{n-1})$ on
$\Omega$, then $u$ is a weak derivative of $g$ along $y$ on $\Omega$.

This is the converse of `HasWeakIteratedLineDerivOn.cons'`. It reads
$\partial^\alpha (\partial_i f)$ off $\partial^{\alpha + e_i} f$. -/
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
/-- The ambient space of $W^{k,p}(\Omega)$: the families $(w_\alpha)_{|\alpha| \le k}$ of functions
in $L^p(\Omega)$, indexed by the multi-indices of order at most $k$, with the norm
$$\|w\| = \Big(\sum_{|\alpha| \le k} \|w_\alpha\|_{L^p(\Omega)}^p\Big)^{1/p}$$
(the maximum of the norms for $p = \infty$). The space $W^{k,p}(\Omega)$ is the subspace of the
families in which $w_\alpha$ is the weak derivative $\partial^\alpha w_0$.

The type is `PiLp p` of copies of `Lp F p (μ.restrict Ω)`. -/
abbrev SobolevMultiIndexTuple : Type _ :=
  PiLp p fun _ : MultiIndexLE ι k ↦ Lp F p (μ.restrict (Ω : Set E))

namespace SobolevMultiIndexTuple

/-- The function $E \to F$ that a family $(w_\alpha)_{|\alpha| \le k}$ carries: its component $w_0$
at the multi-index $0$. -/
noncomputable def fn (u : SobolevMultiIndexTuple F ι k p Ω μ) : E → F := u 0

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [LinearOrder ι] in
/-- The function of the zero family is zero $\mu$-almost everywhere on $\Omega$. -/
theorem fn_zero : (0 : SobolevMultiIndexTuple F ι k p Ω μ).fn =ᵐ[μ.restrict (Ω : Set E)] 0 :=
  Lp.coeFn_zero F p _

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [LinearOrder ι] in
/-- The function of $u + v$ is, $\mu$-almost everywhere on $\Omega$, the sum of the functions of $u$
and $v$. -/
theorem fn_add (u v : SobolevMultiIndexTuple F ι k p Ω μ) :
    (u + v).fn =ᵐ[μ.restrict (Ω : Set E)] u.fn + v.fn :=
  Lp.coeFn_add (u 0) (v 0)

omit [NormedSpace ℝ E] [LinearOrder ι] in
/-- For $c \in \mathbb{R}$, the function of $c u$ is, $\mu$-almost everywhere on $\Omega$, the
function of $u$ multiplied by $c$. -/
theorem fn_smul (c : ℝ) (u : SobolevMultiIndexTuple F ι k p Ω μ) :
    (c • u).fn =ᵐ[μ.restrict (Ω : Set E)] c • u.fn :=
  Lp.coeFn_smul c (u 0)

end SobolevMultiIndexTuple

/-! ### The space $W^{k,p}(\Omega)$ -/

variable [OpensMeasurableSpace E]

variable (F b k p Ω μ) in
/-- The **Sobolev space $W^{k,p}(\Omega)$** with the derivatives indexed by multi-indices: the
subspace of `SobolevMultiIndexTuple F ι k p Ω μ` of the families $(w_\alpha)_{|\alpha| \le k}$
in which, for each $\alpha$, $w_\alpha$ is a weak derivative of $w_0$ on $\Omega$ along the
tuple of directions `multiIndexTuple b α`, that is, $w_\alpha = \partial^\alpha w_0$. This is
the space of Definition 7.2.2 of [han2009theoretical], and the norm of the ambient space is the
norm of that definition.

The function of an element is `SobolevMultiIndex.fn`, and its weak derivatives are
`SobolevMultiIndex.weakDeriv`. -/
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

/-- A family $u$ lies in $W^{k,p}(\Omega)$ if and only if, for each multi-index $\alpha$ with
$|\alpha| \le k$, the component $u_\alpha$ is a weak derivative of the function $u_0$ on
$\Omega$ along `multiIndexTuple b α`. -/
theorem mem_def {u : SobolevMultiIndexTuple F ι k p Ω μ} :
    u ∈ SobolevMultiIndex F b k p Ω μ ↔ ∀ α : MultiIndexLE ι k,
      HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) u.fn (u α) Ω μ :=
  Iff.rfl

/-- The function $E \to F$ that an element of $W^{k,p}(\Omega)$ carries: its component at the
multi-index $0$.

An element is a term of a submodule, so this function is written `SobolevMultiIndex.fn u` and
not `u.fn`. -/
noncomputable def fn (u : SobolevMultiIndex F b k p Ω μ) : E → F :=
  SobolevMultiIndexTuple.fn (u : SobolevMultiIndexTuple F ι k p Ω μ)

/-- The weak derivative $\partial^\alpha u \in L^p(\Omega)$ of an element $u$ of $W^{k,p}(\Omega)$,
for a multi-index $\alpha$ with $|\alpha| \le k$: the component of $u$ at $\alpha$. -/
def weakDeriv (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    Lp F p (μ.restrict (Ω : Set E)) := (u : SobolevMultiIndexTuple F ι k p Ω μ) α

/-- For $u \in W^{k,p}(\Omega)$ and a multi-index $\alpha$ with $|\alpha| \le k$,
$\partial^\alpha u$ is a weak derivative of the function of $u$ on $\Omega$ along
`multiIndexTuple b α`. -/
theorem hasWeakIteratedLineDerivOn (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) (fn u) (weakDeriv u α) Ω μ :=
  u.2 α

/-- For $u \in W^{k,p}(\Omega)$, the derivative $\partial^0 u$ is the function of $u$. -/
theorem weakDeriv_zero (u : SobolevMultiIndex F b k p Ω μ) :
    (weakDeriv u 0 : E → F) = fn u := rfl

/-- The function of the zero element of $W^{k,p}(\Omega)$ is zero $\mu$-almost everywhere on
$\Omega$. -/
theorem fn_zero : fn (0 : SobolevMultiIndex F b k p Ω μ) =ᵐ[μ.restrict (Ω : Set E)] 0 :=
  SobolevMultiIndexTuple.fn_zero

/-- For $u, v \in W^{k,p}(\Omega)$, the function of $u + v$ is, $\mu$-almost everywhere on $\Omega$,
the sum of the functions of $u$ and $v$. -/
theorem fn_add (u v : SobolevMultiIndex F b k p Ω μ) :
    fn (u + v) =ᵐ[μ.restrict (Ω : Set E)] fn u + fn v :=
  SobolevMultiIndexTuple.fn_add _ _

/-- For $c \in \mathbb{R}$ and $u \in W^{k,p}(\Omega)$, the function of $c u$ is, $\mu$-almost
everywhere on $\Omega$, the function of $u$ multiplied by $c$. -/
theorem fn_smul (c : ℝ) (u : SobolevMultiIndex F b k p Ω μ) :
    fn (c • u) =ᵐ[μ.restrict (Ω : Set E)] c • fn u :=
  SobolevMultiIndexTuple.fn_smul _ _

/-- The function of an element of $W^{k,p}(\Omega)$ lies in $L^p(\Omega)$. -/
theorem memLp (u : SobolevMultiIndex F b k p Ω μ) : MemLp (fn u) p (μ.restrict (Ω : Set E)) :=
  Lp.memLp _

variable [Fact (1 ≤ p)]

/-- Let $p \ge 1$ and let $\mu$ be locally finite. A family $u = (u_\alpha)_{|\alpha| \le k}$ in the
ambient space lies in $W^{k,p}(\Omega)$ if and only if, for every multi-index $\alpha$ with
$|\alpha| \le k$ and every real test function $\varphi$ on $\Omega$,
$$\int_\Omega D^{|\alpha|} \varphi(x)[t_\alpha]\, u_0(x) \, d\mu(x)
  = (-1)^{|\alpha|} \int_\Omega \varphi(x)\, u_\alpha(x) \, d\mu(x),$$
where $t_\alpha$ is `multiIndexTuple b α` and $D^n \varphi(x)$ is the $n$-th derivative of
$\varphi$ at $x$.

The definition of a weak derivative also asks for local integrability. This is automatic for
functions in $L^p(\Omega)$. -/
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
/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be locally finite and finite on compact sets.
For a multi-index $\alpha$ with $|\alpha| \le k$ and a real test function $\varphi$ on $\Omega$,
the continuous linear map
$$u \mapsto \int_\Omega \varphi(x)\, u_\alpha(x) \, d\mu(x)$$
from the ambient space of $W^{k,p}(\Omega)$ to $F$.

Continuity is Hölder's inequality, because $\varphi$ lies in $L^{p'}(\Omega)$ for the conjugate
exponent $p'$ of $p$. This map makes the weak derivative relation a closed condition. -/
noncomputable def pairingCLM (α : MultiIndexLE ι k) (φ : 𝓓(Ω, ℝ)) :
    SobolevMultiIndexTuple F ι k p Ω μ →L[ℝ] F :=
  ((TestFunction.memLp φ (ENNReal.conjExponent p) (μ.restrict (Ω : Set E))).integralSmulCLM F) ∘L
    PiLp.proj p _ α

omit [LinearOrder ι] [IsLocallyFiniteMeasure μ] in
/-- The value of `SobolevMultiIndex.pairingCLM F ι k p Ω μ α φ` at $u$ is $\int_\Omega \varphi(x)\,
u_\alpha(x) \, d\mu(x)$. -/
theorem pairingCLM_apply (α : MultiIndexLE ι k) (φ : 𝓓(Ω, ℝ))
    (u : SobolevMultiIndexTuple F ι k p Ω μ) :
    pairingCLM F ι k p Ω μ α φ u = ∫ x in (Ω : Set E), φ x • u α x ∂μ := by
  rw [pairingCLM]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, MemLp.integralSmulCLM_apply,
    PiLp.proj_apply]

/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be locally finite and finite on compact sets.
Then $W^{k,p}(\Omega)$ is a closed subset of the $\ell^p$ product of the spaces $L^p(\Omega)$.

An $L^p(\Omega)$ limit of weak derivatives is a weak derivative, because the integration by
parts formula pairs the functions against a fixed test function, and this pairing is continuous
on $L^p(\Omega)$ (`SobolevMultiIndex.pairingCLM`). This is the substance of Theorem 7.2.3 of
[han2009theoretical], for the norm of Definition 7.2.2. -/
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

/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be locally finite and finite on compact sets.
Then the Sobolev space $W^{k,p}(\Omega)$, with the norm of Definition 7.2.2 of
[han2009theoretical], is a Banach space. This is Theorem 7.2.3 of [han2009theoretical].

The space is a closed subspace of an $\ell^p$ product of $L^p(\Omega)$ spaces
(`SobolevMultiIndex.isClosed`), so it inherits their completeness. -/
instance instCompleteSpace : CompleteSpace (SobolevMultiIndex F b k p Ω μ) :=
  SobolevMultiIndex.isClosed.completeSpace_coe

end Complete

/-! ### The norm -/

/-- Let $1 \le p < \infty$. For $u \in W^{k,p}(\Omega)$,
$$\|u\| = \Big(\sum_{|\alpha| \le k} \|\partial^\alpha u\|_{L^p(\Omega)}^p\Big)^{1/p}.$$
This is the norm of Definition 7.2.2 of [han2009theoretical]. -/
theorem norm_eq_sum (hp : p ≠ ⊤) (u : SobolevMultiIndex F b k p Ω μ) :
    ‖u‖ = (∑ α : MultiIndexLE ι k, ‖weakDeriv u α‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [← Submodule.norm_coe, PiLp.norm_eq_sum
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp)]
  rfl

omit [Fact (1 ≤ p)] in
/-- For $u \in W^{k,\infty}(\Omega)$,
$$\|u\| = \max_{|\alpha| \le k} \|\partial^\alpha u\|_{L^\infty(\Omega)}.$$
This is the norm of Definition 7.2.2 of [han2009theoretical] for $p = \infty$.

The maximum is written as the supremum `⨆` over the finite type of multi-indices. -/
theorem norm_eq_ciSup (u : SobolevMultiIndex F b k ⊤ Ω μ) :
    ‖u‖ = ⨆ α : MultiIndexLE ι k, ‖weakDeriv u α‖ := by
  rw [← Submodule.norm_coe, PiLp.norm_eq_ciSup]
  rfl

end SobolevMultiIndex

/-! ### Comparison with the predicate on functions -/

variable (b f k p Ω μ) in
/-- A function $f : E \to F$ **lies in $W^{k,p}(\Omega)$** if $f \in L^p(\Omega)$ and, for every
multi-index $\alpha : \iota \to \mathbb{N}$ with $|\alpha| \le k$, some function
$w \in L^p(\Omega)$ is a weak derivative of $f$ on $\Omega$ along `multiIndexTuple b α`, that
is, $w = \partial^\alpha f$. This is Definition 7.2.2 of [han2009theoretical], stated one
multi-index at a time. -/
def MemSobolevMultiIndex : Prop :=
  MemLp f p (μ.restrict (Ω : Set E)) ∧ ∀ α : ι → ℕ, ∑ i, α i ≤ k →
    ∃ w : E → F, HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α) f w Ω μ ∧
      MemLp w p (μ.restrict (Ω : Set E))

namespace MemSobolevMultiIndex

omit [OpensMeasurableSpace E] in
/-- A function in $W^{k,p}(\Omega)$ lies in $L^p(\Omega)$. -/
theorem memLp (h : MemSobolevMultiIndex b f k p Ω μ) : MemLp f p (μ.restrict (Ω : Set E)) := h.1

omit [OpensMeasurableSpace E] in
/-- Let $f$ lie in $W^{k,p}(\Omega)$. For every multi-index $\alpha$ with $|\alpha| \le k$, some
function $w \in L^p(\Omega)$ is a weak derivative of $f$ on $\Omega$ along
`multiIndexTuple b α`. -/
theorem exists_hasWeakIteratedLineDerivOn (h : MemSobolevMultiIndex b f k p Ω μ) {α : ι → ℕ}
    (hα : ∑ i, α i ≤ k) :
    ∃ w : E → F, HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α) f w Ω μ ∧
      MemLp w p (μ.restrict (Ω : Set E)) :=
  h.2 α hα

omit [OpensMeasurableSpace E] in
/-- If $f$ lies in $W^{k,p}(\Omega)$ and $f = f'$ holds $\mu$-almost everywhere on $\Omega$, then
$f'$ lies in $W^{k,p}(\Omega)$. -/
theorem congr_ae {f' : E → F} (h : MemSobolevMultiIndex b f k p Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') : MemSobolevMultiIndex b f' k p Ω μ :=
  ⟨h.1.ae_eq hf, fun α hα ↦
    let ⟨w, hw, hwp⟩ := h.2 α hα
    ⟨w, hw.congr_ae hf (Filter.EventuallyEq.refl _ _), hwp⟩⟩

/-- If $f$ and $g$ lie in $W^{k,p}(\Omega)$, then $f + g$ lies in $W^{k,p}(\Omega)$. -/
protected theorem add {f g : E → F}
    (hf : MemSobolevMultiIndex b f k p Ω μ)
    (hg : MemSobolevMultiIndex b g k p Ω μ) : MemSobolevMultiIndex b (f + g) k p Ω μ :=
  ⟨hf.1.add hg.1, fun α hα ↦
    let ⟨w₁, hw₁, hw₁p⟩ := hf.2 α hα
    let ⟨w₂, hw₂, hw₂p⟩ := hg.2 α hα
    ⟨w₁ + w₂, hw₁.add hw₂, hw₁p.add hw₂p⟩⟩

omit [OpensMeasurableSpace E] in
/-- If $f$ lies in $W^{k,p}(\Omega)$, then $-f$ lies in $W^{k,p}(\Omega)$. -/
protected theorem neg {f : E → F}
    (hf : MemSobolevMultiIndex b f k p Ω μ) :
    MemSobolevMultiIndex b (-f) k p Ω μ :=
  ⟨hf.1.neg, fun α hα ↦
    let ⟨w, hw, hwp⟩ := hf.2 α hα
    ⟨-w, hw.neg, hwp.neg⟩⟩

/-- If $f$ and $g$ lie in $W^{k,p}(\Omega)$, then $f - g$ lies in $W^{k,p}(\Omega)$. -/
protected theorem sub {f g : E → F}
    (hf : MemSobolevMultiIndex b f k p Ω μ)
    (hg : MemSobolevMultiIndex b g k p Ω μ) : MemSobolevMultiIndex b (f - g) k p Ω μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

omit [OpensMeasurableSpace E] in
/-- If $f$ lies in $W^{k,p}(\Omega)$ and $c \in \mathbb{R}$, then $c f$ lies in $W^{k,p}(\Omega)$.
-/
protected theorem const_smul {f : E → F}
    (hf : MemSobolevMultiIndex b f k p Ω μ) (c : ℝ) :
    MemSobolevMultiIndex b (c • f) k p Ω μ :=
  ⟨hf.1.const_smul c, fun α hα ↦
    let ⟨w, hw, hwp⟩ := hf.2 α hα
    ⟨c • w, hw.const_smul c, hwp.const_smul c⟩⟩

/-- Let $s$ be a finite set. If $f_i$ lies in $W^{k,p}(\Omega)$ for every $i \in s$, then
$\sum_{i \in s} f_i$ lies in $W^{k,p}(\Omega)$. -/
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

/-- The function of an element of `SobolevMultiIndex F b k p Ω μ` lies in $W^{k,p}(\Omega)$ in the
sense of `MemSobolevMultiIndex`, which is Definition 7.2.2 of [han2009theoretical]. -/
theorem SobolevMultiIndex.memSobolevMultiIndex (u : SobolevMultiIndex F b k p Ω μ) :
    MemSobolevMultiIndex b (SobolevMultiIndex.fn u) k p Ω μ :=
  ⟨SobolevMultiIndex.memLp u, fun α hα ↦ ⟨SobolevMultiIndex.weakDeriv u ⟨α, hα⟩,
    SobolevMultiIndex.hasWeakIteratedLineDerivOn u ⟨α, hα⟩, Lp.memLp _⟩⟩

/-- Let $E$ be finite-dimensional with its Borel $\sigma$-algebra, and let $F$ be complete. If $f$
lies in $W^{k,p}(\Omega)$ in the sense of `MemSobolevMultiIndex`, then some element $u$ of
`SobolevMultiIndex F b k p Ω μ` has a function that equals $f$ $\mu$-almost everywhere on
$\Omega$.

With `SobolevMultiIndex.memSobolevMultiIndex`, this identifies the type with the space of
Definition 7.2.2 of [han2009theoretical]. -/
theorem MemSobolevMultiIndex.exists_sobolevMultiIndex [FiniteDimensional ℝ E]
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

/-- Let $E$ be finite-dimensional with its Borel $\sigma$-algebra, and let $F$ be complete. If the
functions of two elements $u$ and $v$ of $W^{k,p}(\Omega)$ are equal $\mu$-almost everywhere on
$\Omega$, then $u = v$. So the whole family of an element is determined by its function.

This is the almost everywhere uniqueness of the weak derivative,
`HasWeakIteratedLineDerivOn.ae_eq`. -/
theorem SobolevMultiIndex.ext_of_fn_ae_eq [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    {u v : SobolevMultiIndex F b k p Ω μ}
    (h : SobolevMultiIndex.fn u =ᵐ[μ.restrict (Ω : Set E)] SobolevMultiIndex.fn v) : u = v :=
  Subtype.ext <| PiLp.ext fun α ↦ Lp.ext <|
    (ae_restrict_iff' Ω.isOpen.measurableSet).2
      (((SobolevMultiIndex.hasWeakIteratedLineDerivOn u α).congr_ae h
        (Filter.EventuallyEq.refl _ _)).ae_eq (SobolevMultiIndex.hasWeakIteratedLineDerivOn v α))

omit [OpensMeasurableSpace E] in
/-- If $f$ lies in $W^{k,p}(\Omega)$ in the tensor formulation (`MemSobolev`), then $f$ lies in
$W^{k,p}(\Omega)$ in the multi-index formulation (`MemSobolevMultiIndex`) for the basis $b$.

The weak derivative $\partial^\alpha f$ is the weak derivative of order $|\alpha|$ of the tensor
formulation, evaluated at the tuple of directions that name $\alpha$. -/
theorem MemSobolev.memSobolevMultiIndex (h : MemSobolev f k p Ω μ) :
    MemSobolevMultiIndex b f k p Ω μ := by
  refine ⟨h.memLp, fun α hα ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.exists_hasWeakIteratedFDerivOn (n := ∑ i, α i) (by exact_mod_cast hα)
  exact ⟨_, hw.lineDeriv _, (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α i) ↦ E) F
    (multiIndexTuple (b : ι → E) α)).comp_memLp' hwp⟩

/-- If $f$ lies in $W^{k,p}(\Omega)$ in the multi-index formulation (`MemSobolevMultiIndex`) for the
basis $b$, then $f$ lies in $W^{k,p}(\Omega)$ in the tensor formulation (`MemSobolev`). This is
the converse of `MemSobolev.memSobolevMultiIndex`, so the two formulations describe the same
functions.

The weak derivative of order $n$ is assembled from the $\partial^\alpha f$ with $|\alpha| = n$.
It is the continuous $n$-linear map whose value on a tuple $(b_{i_1}, \dots, b_{i_n})$ of basis
vectors is $\partial^\alpha f$, for the multi-index $\alpha$ (`multiIndexCount`) that counts the
occurrences of each index, extended by multilinearity through `basisCoordProd`. The proof must
check the integration by parts formula for an arbitrary tuple of directions. Multilinearity
reduces it to the tuples of basis vectors, and there the definition of $\partial^\alpha$ gives
it only for the sorted tuple. The two agree because $D^n \varphi(x)$ is symmetric in its
arguments for a test function $\varphi$ (`ContDiff.iteratedFDeriv_congr_perm`). This symmetry is
why this direction is harder than the other one. -/
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
/-- For every basis $b$ of $E$, a function $f$ lies in $W^{k,p}(\Omega)$ in the tensor formulation
(`MemSobolev`) if and only if it lies in $W^{k,p}(\Omega)$ in the multi-index formulation
(`MemSobolevMultiIndex`).

The two directions are `MemSobolev.memSobolevMultiIndex`, which evaluates the derivative tensor
of order $|\alpha|$ at the tuple of directions that name $\alpha$, and
`MemSobolevMultiIndex.memSobolev`, which assembles the tensor of order $n$ from the
$\partial^\alpha f$ with $|\alpha| = n$. Only the functions are matched. The two formulations
carry different norms. These norms are equivalent, but the equivalence is not proved here. -/
theorem memSobolev_iff_memSobolevMultiIndex :
    MemSobolev f k p Ω μ ↔ MemSobolevMultiIndex b f k p Ω μ :=
  ⟨MemSobolev.memSobolevMultiIndex, MemSobolevMultiIndex.memSobolev⟩

end Space

/-! ### $H^k(\Omega)$ is a Hilbert space -/

section Hilbert

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {Ω : Opens E} {μ : Measure E}

/-- Let $F$ be a real inner product space. For $u, v \in W^{k,2}(\Omega)$,
$$\langle u, v \rangle = \int_\Omega \sum_{|\alpha| \le k}
  \langle \partial^\alpha u(x), \partial^\alpha v(x) \rangle \, d\mu(x).$$
So the norm of $H^k(\Omega) = W^{k,2}(\Omega)$ is induced by the inner product of Corollary
7.2.4 of [han2009theoretical]. With `SobolevMultiIndex.instCompleteSpace`, this gives the
corollary: $H^k(\Omega)$ is a Hilbert space.

The inner product is not constructed here. The ambient space is `PiLp 2` of $L^2(\Omega)$
spaces, which carries an inner product, and a submodule of an inner product space carries the
induced inner product. The content of the theorem is that this inner product is the formula of
the book. -/
theorem SobolevMultiIndex.inner_eq (u v : SobolevMultiIndex F b k 2 Ω μ) :
    inner ℝ u v = ∫ x in (Ω : Set E), ∑ α : MultiIndexLE ι k,
      inner ℝ (SobolevMultiIndex.weakDeriv u α x) (SobolevMultiIndex.weakDeriv v α x) ∂μ := by
  rw [Submodule.coe_inner, PiLp.inner_apply,
    integral_finsetSum Finset.univ fun α _ ↦ MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
      (SobolevMultiIndex.weakDeriv u α) (SobolevMultiIndex.weakDeriv v α)]
  exact Finset.sum_congr rfl fun α _ ↦ L2.inner_def _ _

end Hilbert

/-! ### The subspace $W_0^{k,p}(\Omega)$ -/

section Zero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} {Ω : Opens E}
  {μ : Measure E}

namespace SobolevMultiIndex

variable (F b k p Ω μ) in
/-- The image of the test functions $C_0^\infty(\Omega)$ in $W^{k,p}(\Omega)$: the submodule of the
elements whose function equals, $\mu$-almost everywhere on $\Omega$, some test function
$\varphi \in \mathcal{D}(\Omega, F)$.

Every test function occurs, by `TestFunction.exists_mem_sobolevMultiIndex_testFunctions`. The
counterpart in the tensor formulation is `Sobolev.testFunctions`. -/
def testFunctions : Submodule ℝ (SobolevMultiIndex F b k p Ω μ) where
  carrier := {u | ∃ φ : 𝓓(Ω, F), fn u =ᵐ[μ.restrict (Ω : Set E)] φ}
  zero_mem' := ⟨0, fn_zero⟩
  add_mem' := fun {u v} ⟨φ, hφ⟩ ⟨ψ, hψ⟩ ↦ ⟨φ + ψ, (fn_add u v).trans (hφ.add hψ)⟩
  smul_mem' := fun c u ⟨φ, hφ⟩ ↦ ⟨c • φ, (fn_smul c u).trans (hφ.const_smul c)⟩

/-- An element $u$ of $W^{k,p}(\Omega)$ lies in `SobolevMultiIndex.testFunctions F b k p Ω μ` if and
only if its function equals some test function $\varphi \in \mathcal{D}(\Omega, F)$ $\mu$-almost
everywhere on $\Omega$. -/
theorem mem_testFunctions {u : SobolevMultiIndex F b k p Ω μ} :
    u ∈ testFunctions F b k p Ω μ ↔ ∃ φ : 𝓓(Ω, F), fn u =ᵐ[μ.restrict (Ω : Set E)] φ :=
  Iff.rfl

/-- Let $E$ be finite-dimensional with its Borel $\sigma$-algebra, let $F$ be complete, and let
$\mu$ be an additive Haar measure. For every test function $\varphi \in \mathcal{D}(\Omega, F)$,
some element $u$ of `SobolevMultiIndex.testFunctions F b k p Ω μ` has a function that equals
$\varphi$ $\mu$-almost everywhere on $\Omega$. So this submodule is the image of
$C_0^\infty(\Omega)$ in $W^{k,p}(\Omega)$.

A test function is smooth with compact support, so all its derivatives $\partial^\alpha \varphi$
are continuous with compact support and lie in $L^p(\Omega)$. -/
theorem _root_.TestFunction.exists_mem_sobolevMultiIndex_testFunctions
    [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]
    (φ : 𝓓(Ω, F)) :
    ∃ u ∈ testFunctions F b k p Ω μ, fn u =ᵐ[μ.restrict (Ω : Set E)] φ :=
  let ⟨u, hu⟩ :=
    (TestFunction.memSobolev φ).memSobolevMultiIndex (b := b).exists_sobolevMultiIndex
  ⟨u, ⟨φ, hu⟩, hu⟩

end SobolevMultiIndex

variable [Fact (1 ≤ p)]

variable (F b k p Ω μ) in
/-- Let $p \ge 1$. The **Sobolev space $W_0^{k,p}(\Omega)$** is the closure of
`SobolevMultiIndex.testFunctions F b k p Ω μ`, the image of $C_0^\infty(\Omega)$, in
$W^{k,p}(\Omega)$. This is Definition 7.2.9 of [han2009theoretical], in the space with the norm
of Definition 7.2.2.

`SobolevZero` is the same closure in the tensor formulation of `Numlib.Analysis.Sobolev.Space`,
and that type is not an inner product space in general. For $p = 2$ this type is a closed
subspace of the Hilbert space $H^k(\Omega)$ (`SobolevMultiIndex.inner_eq`), so it is a Hilbert
space itself. The variational theory of the library, in the modules under `Numlib.Variational`,
needs this property of $H^1_0(a, b)$ in `Numlib.Analysis.Sobolev.Interval`. The two closures are
not compared, because the two types carry different, though equivalent, norms. -/
noncomputable def SobolevMultiIndexZero : Submodule ℝ (SobolevMultiIndex F b k p Ω μ) :=
  (SobolevMultiIndex.testFunctions F b k p Ω μ).topologicalClosure

namespace SobolevMultiIndexZero

/-- Let $p \ge 1$. The space $W_0^{k,p}(\Omega)$ is a closed subset of $W^{k,p}(\Omega)$, because it
is a closure. -/
theorem isClosed :
    IsClosed (SobolevMultiIndexZero F b k p Ω μ : Set (SobolevMultiIndex F b k p Ω μ)) :=
  Submodule.isClosed_topologicalClosure _

/-- Let $p \ge 1$. The image of the test functions in $W^{k,p}(\Omega)$ is contained in
$W_0^{k,p}(\Omega)$. -/
theorem testFunctions_le :
    SobolevMultiIndex.testFunctions F b k p Ω μ ≤ SobolevMultiIndexZero F b k p Ω μ :=
  Submodule.le_topologicalClosure _

/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be locally finite and finite on compact sets.
Then $W_0^{k,p}(\Omega)$ is a Banach space.

It is a closed subspace of the complete space $W^{k,p}(\Omega)$. For $p = 2$ and a real inner
product space $F$, it is therefore a Hilbert space, with the inner product of $H^k(\Omega)$. -/
instance instCompleteSpace [CompleteSpace F] [IsFiniteMeasureOnCompacts μ]
    [IsLocallyFiniteMeasure μ] : CompleteSpace (SobolevMultiIndexZero F b k p Ω μ) :=
  isClosed.completeSpace_coe

end SobolevMultiIndexZero

end Zero

/-!
### The inductive description of $W^{m+1,p}(\Omega)$

[brezis2011functional] defines $W^{m,p}(\Omega)$ by induction: $u \in W^{m,p}(\Omega)$ when $u$ and
all its first partial derivatives lie in $W^{m-1,p}(\Omega)$. The book remarks that the description
by multi-indices is equivalent. The equivalence rests on reading $\partial^{\alpha + e_i}$ as
$\partial^\alpha \partial_i$. This is `HasWeakIteratedLineDerivOn.cons'` and
`HasWeakIteratedLineDerivOn.of_cons'`, together with the invariance of the weak derivative under
permutations of the directions, since `multiIndexTuple` lists the directions in increasing order of
the index.
-/

section Succ

variable {E : Type*} {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- As multisets, the directions that name $\alpha + \beta$ are the directions that name $\alpha$
together with the directions that name $\beta$. -/
theorem coe_multiIndexDirections_add (b : ι → E) (α β : ι → ℕ) :
    ((multiIndexDirections b (α + β) : List E) : Multiset E)
      = (multiIndexDirections b α : Multiset E) + (multiIndexDirections b β : Multiset E) := by
  simp only [coe_multiIndexDirections, Pi.add_apply, Multiset.replicate_add,
    Finset.sum_add_distrib]

/-- As a multiset, the list of directions that name $e_i$ is $\{b_i\}$. -/
theorem coe_multiIndexDirections_single (b : ι → E) (i : ι) :
    ((multiIndexDirections b (Pi.single i 1) : List E) : Multiset E) = {b i} := by
  rw [coe_multiIndexDirections, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- The tuple that names $e_i$ is a permutation of the tuple $(b_i)$ of length one. -/
theorem multiIndexTuple_single_perm (b : ι → E) (i : ι) :
    (List.ofFn (multiIndexTuple b (Pi.single i 1))).Perm (List.ofFn ![b i]) := by
  rw [← Multiset.coe_eq_coe, ← multiIndexDirections_eq_ofFn, coe_multiIndexDirections_single]
  simp

/-- The tuple $(b_i, t_0, \dots, t_{n-1})$, where $t$ is the tuple that names $\alpha$, is a
permutation of the tuple that names $\alpha + e_i$. -/
theorem multiIndexTuple_add_single_perm (b : ι → E) (α : ι → ℕ) (i : ι) :
    (List.ofFn (Fin.cons (b i) (multiIndexTuple b α))).Perm
      (List.ofFn (multiIndexTuple b (α + Pi.single i 1))) := by
  rw [← Multiset.coe_eq_coe, List.ofFn_cons, ← multiIndexDirections_eq_ofFn,
    ← multiIndexDirections_eq_ofFn, ← Multiset.cons_coe, coe_multiIndexDirections_add,
    coe_multiIndexDirections_single, add_comm, Multiset.singleton_add]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {b : Basis ι ℝ E} {f : E → F} {k : ℕ} {p : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

/-- If $k' \le k$ and $f$ lies in $W^{k,p}(\Omega)$, then $f$ lies in $W^{k',p}(\Omega)$. -/
theorem MemSobolevMultiIndex.mono_order {k' : ℕ} (h : MemSobolevMultiIndex b f k p Ω μ)
    (hk : k' ≤ k) : MemSobolevMultiIndex b f k' p Ω μ :=
  ⟨h.1, fun α hα ↦ h.2 α (hα.trans hk)⟩

/-- The zero function lies in $W^{k,p}(\Omega)$. -/
protected theorem MemSobolevMultiIndex.zero : MemSobolevMultiIndex b (0 : E → F) k p Ω μ :=
  ⟨MemLp.zero, fun _ _ ↦ ⟨0, HasWeakIteratedLineDerivOn.zero, MemLp.zero⟩⟩

/-- Let $p \ge 1$ and let $\mu$ be locally finite. A function $f$ lies in $W^{0,p}(\Omega)$ if and
only if $f \in L^p(\Omega)$. -/
theorem memSobolevMultiIndex_zero_iff [OpensMeasurableSpace E] [Fact (1 ≤ p)]
    [IsLocallyFiniteMeasure μ] :
    MemSobolevMultiIndex b f 0 p Ω μ ↔ MemLp f p (μ.restrict (Ω : Set E)) := by
  refine ⟨fun h ↦ h.memLp, fun hf ↦ ⟨hf, fun α hα ↦ ?_⟩⟩
  have h0 : ∑ i, α i = 0 := Nat.le_zero.1 hα
  exact ⟨f, HasWeakIteratedLineDerivOn.of_length_eq_zero h0 _ (hf.locallyIntegrableOn Fact.out),
    hf⟩

/-- Let $m \in \mathbb{N}$. A function $f$ lies in $W^{m+1,p}(\Omega)$ if and only if $f$ lies in
$W^{m,p}(\Omega)$ and, for every $i \in \iota$, some function $g$ is a weak derivative of $f$
along the direction $b_i$ on $\Omega$ and lies in $W^{m,p}(\Omega)$. So the inductive definition
$W^{m+1,p}(\Omega) = \{u \in W^{m,p}(\Omega) : \partial_i u \in W^{m,p}(\Omega) \text{ for all }
i\}$ agrees with the definition by multi-indices.

This is the equivalence of the two displayed definitions of $W^{m,p}(\Omega)$ in
[brezis2011functional], §9.1 (the paragraph "The spaces $W^{m,p}(\Omega)$"). The proof shows
$\partial^\alpha (\partial_i f) = \partial^{\alpha + e_i} f$ with
`HasWeakIteratedLineDerivOn.cons'` and its converse, after a rearrangement of the tuple of
directions. -/
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
/-- Let $p \ge 1$. For a multi-index $\alpha$ with $|\alpha| \le k$, the weak derivative
$u \mapsto \partial^\alpha u$ as a bounded linear map $W^{k,p}(\Omega) \to L^p(\Omega)$. Its
operator norm is at most one (`SobolevMultiIndex.norm_weakDerivL_le`).

The map is the coordinate projection of the ambient $\ell^p$ product, restricted to the
subspace. The one-dimensional counterpart is `SobolevIntervalLp.derivL`. -/
noncomputable def weakDerivL (α : MultiIndexLE ι k) :
    SobolevMultiIndex F b k p Ω μ →L[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  (PiLp.proj p (fun _ : MultiIndexLE ι k ↦ Lp F p (μ.restrict (Ω : Set E))) α) ∘L
    (SobolevMultiIndex F b k p Ω μ).subtypeL

/-- The map `SobolevMultiIndex.weakDerivL F b k p Ω μ α` takes $u$ to $\partial^\alpha u$. -/
@[simp]
theorem weakDerivL_apply (α : MultiIndexLE ι k) (u : SobolevMultiIndex F b k p Ω μ) :
    weakDerivL F b k p Ω μ α u = weakDeriv u α :=
  rfl

/-- Let $p \ge 1$. For $u \in W^{k,p}(\Omega)$ and $|\alpha| \le k$,
$$\|\partial^\alpha u\|_{L^p(\Omega)} \le \|u\|,$$
because the norm of $W^{k,p}(\Omega)$ is the $\ell^p$ norm of the family of the weak
derivatives. -/
theorem norm_weakDeriv_le (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    ‖weakDeriv u α‖ ≤ ‖u‖ := by
  rw [← Submodule.norm_coe]
  exact PiLp.norm_apply_le _ _

/-- Let $p \ge 1$. The operator norm of $u \mapsto \partial^\alpha u$, from $W^{k,p}(\Omega)$ to
$L^p(\Omega)$, is at most one. -/
theorem norm_weakDerivL_le (α : MultiIndexLE ι k) : ‖weakDerivL F b k p Ω μ α‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    rw [one_mul]
    exact norm_weakDeriv_le u α

variable (F b k p Ω μ) in
/-- Let $p \ge 1$. The inclusion $W^{k,p}(\Omega) \to L^p(\Omega)$, which takes $u$ to its function,
as a bounded linear map. It is the weak derivative of order $0$.

The map is injective when $E$ is finite-dimensional with its Borel $\sigma$-algebra and $F$ is
complete (`SobolevMultiIndex.fnL_injective`), and its operator norm is at most one
(`SobolevMultiIndex.norm_fnL_le`). The embedding theorems of Sobolev spaces are stated along
this map. -/
noncomputable def fnL : SobolevMultiIndex F b k p Ω μ →L[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  weakDerivL F b k p Ω μ 0

/-- The element `SobolevMultiIndex.fnL F b k p Ω μ u` of $L^p(\Omega)$, as a function, is the
function of $u$. -/
@[simp]
theorem fnL_apply (u : SobolevMultiIndex F b k p Ω μ) : (fnL F b k p Ω μ u : E → F) = fn u :=
  rfl

/-- For $u \in W^{k,p}(\Omega)$, the image of $u$ under the inclusion into $L^p(\Omega)$ is
$\partial^0 u$. -/
theorem fnL_eq_weakDeriv_zero (u : SobolevMultiIndex F b k p Ω μ) :
    fnL F b k p Ω μ u = weakDeriv u 0 :=
  rfl

/-- Let $p \ge 1$. For $u \in W^{k,p}(\Omega)$, the $L^p(\Omega)$ norm of the function of $u$ is at
most $\|u\|$. -/
theorem norm_fnL_apply_le (u : SobolevMultiIndex F b k p Ω μ) : ‖fnL F b k p Ω μ u‖ ≤ ‖u‖ :=
  norm_weakDeriv_le u 0

/-- Let $p \ge 1$. The operator norm of the inclusion $W^{k,p}(\Omega) \to L^p(\Omega)$ is at most
one. -/
theorem norm_fnL_le : ‖fnL F b k p Ω μ‖ ≤ 1 :=
  norm_weakDerivL_le 0

/-- Let $p \ge 1$, let $E$ be finite-dimensional with its Borel $\sigma$-algebra, and let $F$ be
complete. Then the inclusion $W^{k,p}(\Omega) \to L^p(\Omega)$ is injective: an element of
$W^{k,p}(\Omega)$ is determined by its function, because weak derivatives are unique. -/
theorem fnL_injective [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] :
    Function.Injective (fnL F b k p Ω μ) := fun _ _ h ↦
  ext_of_fn_ae_eq (Filter.EventuallyEq.of_eq (congrArg (fun w : Lp F p _ ↦ (w : E → F)) h))

end SobolevMultiIndex

namespace SobolevMultiIndexZero

variable (F b k p Ω μ) in
/-- Let $p \ge 1$. The inclusion $W_0^{k,p}(\Omega) \to L^p(\Omega)$ as a bounded linear map: the
restriction of `SobolevMultiIndex.fnL` to the closed subspace $W_0^{k,p}(\Omega)$.

A function in $L^p(\Omega)$ is said to lie in $W_0^{k,p}(\Omega)$ when it is in the range of
this map, and the element of $W_0^{k,p}(\Omega)$ is then unique
(`SobolevMultiIndexZero.fnL_injective`). This is how a homogeneous boundary condition $u = 0$ on
$\partial \Omega$ is read. -/
noncomputable def fnL : SobolevMultiIndexZero F b k p Ω μ →L[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  (SobolevMultiIndex.fnL F b k p Ω μ).comp (SobolevMultiIndexZero F b k p Ω μ).subtypeL

/-- For $v \in W_0^{k,p}(\Omega)$, the element `SobolevMultiIndexZero.fnL F b k p Ω μ v` of
$L^p(\Omega)$, as a function, is the function of $v$. -/
@[simp]
theorem fnL_apply (v : SobolevMultiIndexZero F b k p Ω μ) :
    (fnL F b k p Ω μ v : E → F) = SobolevMultiIndex.fn (v : SobolevMultiIndex F b k p Ω μ) :=
  rfl

/-- For $v \in W_0^{k,p}(\Omega)$, the inclusion of $W_0^{k,p}(\Omega)$ into $L^p(\Omega)$ takes $v$
to the image of $v$ under `SobolevMultiIndex.fnL`. -/
theorem fnL_eq (v : SobolevMultiIndexZero F b k p Ω μ) :
    fnL F b k p Ω μ v = SobolevMultiIndex.fnL F b k p Ω μ (v : SobolevMultiIndex F b k p Ω μ) :=
  rfl

/-- Let $p \ge 1$. For $v \in W_0^{k,p}(\Omega)$, the $L^p(\Omega)$ norm of the function of $v$ is
at most the $W^{k,p}(\Omega)$ norm of $v$. -/
theorem norm_fnL_apply_le (v : SobolevMultiIndexZero F b k p Ω μ) : ‖fnL F b k p Ω μ v‖ ≤ ‖v‖ :=
  SobolevMultiIndex.norm_fnL_apply_le _

/-- Let $p \ge 1$. The operator norm of the inclusion $W_0^{k,p}(\Omega) \to L^p(\Omega)$ is at most
one. -/
theorem norm_fnL_le : ‖fnL F b k p Ω μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    rw [one_mul]
    exact norm_fnL_apply_le v

/-- Let $p \ge 1$, let $E$ be finite-dimensional with its Borel $\sigma$-algebra, and let $F$ be
complete. Then the inclusion $W_0^{k,p}(\Omega) \to L^p(\Omega)$ is injective. -/
theorem fnL_injective [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] :
    Function.Injective (fnL F b k p Ω μ) := fun _ _ h ↦
  Subtype.ext (SobolevMultiIndex.fnL_injective h)

end SobolevMultiIndexZero

end Operators

/-!
### The gradient norm on $W^{1,p}(\Omega)$

The norm $\|\nabla u\|_{L^p(\Omega)}$ of the gradient, read as the $\ell^p(\iota)$ norm of the tuple
of partial derivatives $(\partial_i u)_{i \in \iota}$, each measured in $L^p(\Omega)$. It is a
seminorm on $W^{1,p}(\Omega)$, and the norm of $W^{1,p}(\Omega)$ is the $\ell^p$ sum of
$\|u\|_{L^p(\Omega)}$ and this seminorm. For $p = 2$ it agrees with the $L^2$ norm of the pointwise
Euclidean length $|\nabla u(x)|$.
-/

section Gradient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

/-- Let $p \ge 1$. The **gradient** of $u \in W^{1,p}(\Omega)$: the tuple
$(\partial_i u)_{i \in \iota}$ of the first partial derivatives of $u$ in the basis $b$, as an
element of the $\ell^p$ product of copies of $L^p(\Omega)$ indexed by $\iota$. -/
def grad (u : SobolevMultiIndex F b 1 p Ω μ) :
    PiLp p fun _ : ι ↦ Lp F p (μ.restrict (Ω : Set E)) :=
  WithLp.toLp p fun i ↦ weakDeriv u (MultiIndexLE.single i)

omit [Fact (1 ≤ p)] in
/-- The entry $i$ of the gradient of $u$ is the partial derivative $\partial_i u$. -/
@[simp]
theorem grad_apply (u : SobolevMultiIndex F b 1 p Ω μ) (i : ι) :
    grad u i = weakDeriv u (MultiIndexLE.single i) :=
  rfl

omit [Fact (1 ≤ p)] in
/-- For $u, v \in W^{1,p}(\Omega)$, $\nabla(u + v) = \nabla u + \nabla v$. -/
theorem grad_add (u v : SobolevMultiIndex F b 1 p Ω μ) : grad (u + v) = grad u + grad v := by
  ext i
  rfl

omit [Fact (1 ≤ p)] in
/-- For $c \in \mathbb{R}$ and $u \in W^{1,p}(\Omega)$, $\nabla(c u) = c \nabla u$. -/
theorem grad_smul (c : ℝ) (u : SobolevMultiIndex F b 1 p Ω μ) : grad (c • u) = c • grad u := by
  ext i
  rfl

/-- Let $p \ge 1$. The **gradient norm** of $u \in W^{1,p}(\Omega)$ is the norm of the gradient
$\nabla u$ in the $\ell^p$ product of copies of $L^p(\Omega)$:
$$\|\nabla u\|_{L^p(\Omega)} = \Big(\sum_{i \in \iota} \|\partial_i
  u\|_{L^p(\Omega)}^p\Big)^{1/p},$$
and $\max_i \|\partial_i u\|_{L^\infty(\Omega)}$ for $p = \infty$. This is the $\ell^p$ reading
of $\|\nabla u\|_{L^p(\Omega)}$ in [brezis2011functional], §9.1 and Corollary 9.19.

The gradient norm is a seminorm on $W^{1,p}(\Omega)$ bounded by the norm
(`SobolevMultiIndex.gradNorm_le_norm`). On $W_0^{1,p}(\Omega)$ for a bounded open set $\Omega$
it is a norm, by Poincaré's inequality. -/
noncomputable def gradNorm (u : SobolevMultiIndex F b 1 p Ω μ) : ℝ := ‖grad u‖

/-- The gradient norm is nonnegative: $0 \le \|\nabla u\|_{L^p(\Omega)}$. -/
theorem gradNorm_nonneg (u : SobolevMultiIndex F b 1 p Ω μ) : 0 ≤ gradNorm u := norm_nonneg _

/-- For $u, v \in W^{1,p}(\Omega)$, $\|\nabla(u + v)\|_{L^p(\Omega)} \le \|\nabla
u\|_{L^p(\Omega)} + \|\nabla v\|_{L^p(\Omega)}$. -/
theorem gradNorm_add_le (u v : SobolevMultiIndex F b 1 p Ω μ) :
    gradNorm (u + v) ≤ gradNorm u + gradNorm v := by
  rw [gradNorm, grad_add]
  exact norm_add_le _ _

/-- For $c \in \mathbb{R}$ and $u \in W^{1,p}(\Omega)$, $\|\nabla(c u)\|_{L^p(\Omega)} = |c| \,
\|\nabla u\|_{L^p(\Omega)}$. -/
theorem gradNorm_smul (c : ℝ) (u : SobolevMultiIndex F b 1 p Ω μ) :
    gradNorm (c • u) = |c| * gradNorm u := by
  rw [gradNorm, grad_smul, norm_smul, Real.norm_eq_abs]
  rfl

/-- Let $1 \le p < \infty$. For $u \in W^{1,p}(\Omega)$,
$$\|\nabla u\|_{L^p(\Omega)} = \Big(\sum_{i \in \iota} \|\partial_i
  u\|_{L^p(\Omega)}^p\Big)^{1/p}.$$
-/
theorem gradNorm_eq_sum (hp : p ≠ ⊤) (u : SobolevMultiIndex F b 1 p Ω μ) :
    gradNorm u = (∑ i, ‖weakDeriv u (MultiIndexLE.single i)‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [gradNorm, PiLp.norm_eq_sum
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp)]
  rfl

/-- For $u \in W^{1,\infty}(\Omega)$,
$$\|\nabla u\|_{L^\infty(\Omega)} = \sup_{i \in \iota} \|\partial_i u\|_{L^\infty(\Omega)}.$$
-/
theorem gradNorm_eq_ciSup (u : SobolevMultiIndex F b 1 ⊤ Ω μ) :
    gradNorm u = ⨆ i, ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  rw [gradNorm, PiLp.norm_eq_ciSup]
  rfl

/-- Let $1 \le p < \infty$. For $u \in W^{1,p}(\Omega)$,
$$\|u\| = \big(\|\partial^0 u\|_{L^p(\Omega)}^p + \|\nabla u\|_{L^p(\Omega)}^p\big)^{1/p},$$
where $\partial^0 u$ is the function of $u$. So the norm of $W^{1,p}(\Omega)$ is the $\ell^p$
sum of the $L^p(\Omega)$ norm of the function and of the gradient norm. -/
theorem norm_eq_gradNorm (hp : p ≠ ⊤) (u : SobolevMultiIndex F b 1 p Ω μ) :
    ‖u‖ = (‖weakDeriv u 0‖ ^ p.toReal + gradNorm u ^ p.toReal) ^ (1 / p.toReal) := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  rw [norm_eq_sum hp, gradNorm_eq_sum hp, MultiIndexLE.sum_univ_one, ← Real.rpow_mul
    (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hP.ne',
    Real.rpow_one]

/-- For $u \in W^{1,\infty}(\Omega)$,
$$\|u\| = \max\big(\|\partial^0 u\|_{L^\infty(\Omega)}, \|\nabla u\|_{L^\infty(\Omega)}\big),$$
where $\partial^0 u$ is the function of $u$. -/
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

/-- Let $p \ge 1$. For $u \in W^{1,p}(\Omega)$, $\|\nabla u\|_{L^p(\Omega)} \le \|u\|$: the omission
of the term $\|u\|_{L^p(\Omega)}$ from the $\ell^p$ sum does not increase it. -/
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

/-- Let $p \ge 1$. For $u \in W^{1,p}(\Omega)$ and $i \in \iota$, $\|\partial_i u\|_{L^p(\Omega)}
\le \|\nabla u\|_{L^p(\Omega)}$. -/
theorem norm_weakDeriv_single_le_gradNorm (u : SobolevMultiIndex F b 1 p Ω μ) (i : ι) :
    ‖weakDeriv u (MultiIndexLE.single i)‖ ≤ gradNorm u :=
  PiLp.norm_apply_le (grad u) i

/-- The **Pythagorean identity** in $L^2(\nu; \ell^2(\iota; F))$. Let $\nu$ be a measure on $X$, let
$\iota$ be finite, and let $(g_i)_{i \in \iota}$ be functions $X \to F$ that are almost
everywhere strongly measurable, such that $G : x \mapsto (g_i(x))_{i \in \iota}$, with values in
the $\ell^2$ product of copies of $F$, is almost everywhere strongly measurable. Then
$$\|G\|_{L^2(\nu)}^2 = \sum_{i \in \iota} \|g_i\|_{L^2(\nu)}^2,$$
with the norms taken in $[0, \infty]$ (`MeasureTheory.eLpNorm`). -/
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

/-- Let $p \ge 1$. The **pointwise gradient** $x \mapsto \nabla u(x) = (\partial_i u(x))_{i \in
\iota}$ of $u \in W^{1,p}(\Omega)$, with values in the Euclidean ($\ell^2$) product of copies of
$F$ indexed by $\iota$. Its length $|\nabla u(x)|$ is the one in $\|\nabla u\|_{L^p(\Omega)} =
(\int_\Omega |\nabla u|^p)^{1/p}$ of [brezis2011functional], §9.1. -/
noncomputable def gradFn (u : SobolevMultiIndex F b 1 p Ω μ) (x : E) : PiLp 2 fun _ : ι ↦ F :=
  WithLp.toLp 2 fun i ↦ weakDeriv u (MultiIndexLE.single i) x

omit [Fact (1 ≤ p)] in
/-- The component $i$ of the pointwise gradient of $u$ at $x$ is $\partial_i u(x)$. -/
@[simp]
theorem gradFn_apply (u : SobolevMultiIndex F b 1 p Ω μ) (x : E) (i : ι) :
    gradFn u x i = weakDeriv u (MultiIndexLE.single i) x :=
  rfl

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [Fact (1 ≤ p)] in
/-- Let $F$ be second countable with its Borel $\sigma$-algebra. For $u \in W^{1,p}(\Omega)$, the
pointwise gradient of $u$ is almost everywhere strongly measurable with respect to the
restriction of $\mu$ to $\Omega$. -/
theorem aestronglyMeasurable_gradFn (u : SobolevMultiIndex F b 1 p Ω μ) :
    AEStronglyMeasurable (gradFn u) (μ.restrict (Ω : Set E)) :=
  (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable
    (aemeasurable_pi_iff.2 fun _ ↦ (Lp.aestronglyMeasurable _).aemeasurable).aestronglyMeasurable

omit [Fact (1 ≤ p)] in
/-- Let $F$ be second countable with its Borel $\sigma$-algebra. For $u \in W^{1,2}(\Omega)$,
$$\int_\Omega |\nabla u|^2 \, d\mu = \sum_{i \in \iota} \|\partial_i u\|_{L^2(\Omega)}^2.$$
The statement is about the squares of the $L^2$ norms in $[0, \infty]$
(`MeasureTheory.eLpNorm`): the square of the $L^2$ norm of the pointwise gradient is the sum of
the squares of the $L^2$ norms of the partial derivatives. -/
theorem eLpNorm_gradFn_two_sq (u : SobolevMultiIndex F b 1 2 Ω μ) :
    eLpNorm (gradFn u) 2 (μ.restrict (Ω : Set E)) ^ 2
      = ∑ i, eLpNorm (weakDeriv u (MultiIndexLE.single i)) 2 (μ.restrict (Ω : Set E)) ^ 2 :=
  MeasureTheory.eLpNorm_toLp_two_sq (fun _ ↦ Lp.aestronglyMeasurable _)
    (aestronglyMeasurable_gradFn u)

omit [Fact (1 ≤ p)] in
/-- Let $F$ be second countable with its Borel $\sigma$-algebra. For $u \in W^{1,2}(\Omega)$, the
two readings of $\|\nabla u\|_{L^2(\Omega)}$ agree: the gradient norm $(\sum_i \|\partial_i
u\|_{L^2(\Omega)}^2)^{1/2}$ (`SobolevMultiIndex.gradNorm`) equals
$(\int_\Omega |\nabla u|^2 \, d\mu)^{1/2}$, the $L^2$ norm of the pointwise gradient
(`SobolevMultiIndex.gradFn`). -/
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

/-- Let $1 \le p < \infty$, let $E$ be second countable with its Borel $\sigma$-algebra, let $\mu$
be s-finite, and let $F$ be second countable. Then $W^{k,p}(\Omega)$ is second countable, hence
separable. This is the separability statement of Proposition 9.1 of [brezis2011functional], with
the argument of Proposition 8.1.

The space $L^p(\Omega)$ is second countable under these hypotheses
(`MeasureTheory.Lp.SecondCountableTopology`), a finite $\ell^p$ product of second countable
spaces is second countable, and so is a subspace. -/
instance SobolevMultiIndex.instSecondCountableTopology [SecondCountableTopology E] [BorelSpace E]
    [SFinite μ] [SecondCountableTopology F] :
    SecondCountableTopology (SobolevMultiIndex F b k p Ω μ) :=
  inferInstance

/-- Let $1 \le p < \infty$, let $E$ be second countable with its Borel $\sigma$-algebra, let $\mu$
be s-finite, and let $F$ be second countable. Then $W_0^{k,p}(\Omega)$ is second countable,
hence separable. This is stated in [brezis2011functional], §9.4, in the sentence after the
definition.

The space is a subspace of the second countable space $W^{k,p}(\Omega)$. -/
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

/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be locally finite and finite on compact sets.
If $L^p(\Omega)$ is reflexive, then $W^{k,p}(\Omega)$ is reflexive. This is the reflexivity
statement of Proposition 9.1 of [brezis2011functional], with the argument of Proposition 8.1.

The ambient space is a finite $\ell^p$ product of copies of $L^p(\Omega)$, which is reflexive by
`NormedSpace.instIsReflexivePiLp`, and $W^{k,p}(\Omega)$ is a closed subspace of it
(`SobolevMultiIndex.isClosed`), so `NormedSpace.isReflexive_of_isClosed` applies. For real
scalars and a $\sigma$-finite measure, $L^p(\Omega)$ is reflexive for $1 < p < \infty$ by
`MeasureTheory.Lp.instIsReflexive`, and for $p = 2$ the instance for inner product spaces
applies as well. -/
instance SobolevMultiIndex.instIsReflexive
    [NormedSpace.IsReflexive ℝ (Lp F p (μ.restrict (Ω : Set E)))] :
    NormedSpace.IsReflexive ℝ (SobolevMultiIndex F b k p Ω μ) :=
  NormedSpace.isReflexive_of_isClosed _ SobolevMultiIndex.isClosed

/-- Let $p \ge 1$, let $F$ be complete, and let $\mu$ be locally finite and finite on compact sets.
If $L^p(\Omega)$ is reflexive, then $W_0^{k,p}(\Omega)$ is reflexive. This is stated in
[brezis2011functional], §9.4, in the sentence after the definition.

The space is a closed subspace (`SobolevMultiIndexZero.isClosed`) of the reflexive space
$W^{k,p}(\Omega)$. -/
instance SobolevMultiIndexZero.instIsReflexive
    [NormedSpace.IsReflexive ℝ (Lp F p (μ.restrict (Ω : Set E)))] :
    NormedSpace.IsReflexive ℝ (SobolevMultiIndexZero F b k p Ω μ) :=
  NormedSpace.isReflexive_of_isClosed _ SobolevMultiIndexZero.isClosed

end Reflexive

/-! ### The spaces $W^{k,p}(\Omega)$ and $W_0^{k,p}(\Omega)$ on an open subset of $\mathbb{R}^N$ -/

section Euclidean

/-- The exponent $p = 2$, written `((2 : NNReal) : ℝ≥0∞)`, satisfies $1 \le p$. The Euclidean
theorems that take `p : ℝ≥0` (Rellich–Kondrachov, Deny–Lions, Bramble–Hilbert) state their
results about $H^k(\Omega) = W^{k,2}(\Omega)$ with the exponent in this form. -/
instance fact_one_le_coe_two_ennreal : Fact (1 ≤ ((2 : NNReal) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The **Sobolev space $W^{k,p}(\Omega)$** on an open set $\Omega \subseteq \mathbb{R}^N$ of
[brezis2011functional], §9.1 (the Definition, and the paragraph "The spaces $W^{m,p}(\Omega)$"):
the space `SobolevMultiIndex` of real-valued functions, for the standard basis of $\mathbb{R}^N$
and Lebesgue measure. Its norm is $(\sum_{|\alpha| \le k} \|\partial^\alpha
u\|_{L^p(\Omega)}^p)^{1/p}$ (`SobolevMultiIndex.norm_eq_sum`), the second, equivalent norm of
the book. For $p = 2$ it is the Hilbert space $H^k(\Omega)$ with the inner product
$\sum_{|\alpha| \le k} \int_\Omega \partial^\alpha u \, \partial^\alpha v$ of the book
(`SobolevMultiIndex.inner_eq`).

The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)`, and the whole space is the case
$\Omega = \top$. The type is an abbreviation, so every lemma about `SobolevMultiIndex` applies
to it without change. -/
noncomputable abbrev SobolevEuclidean (N k : ℕ) (p : ℝ≥0∞)
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  SobolevMultiIndex ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k p Ω volume

/-- Let $p \ge 1$. The **Sobolev space $W_0^{k,p}(\Omega)$** on an open set
$\Omega \subseteq \mathbb{R}^N$ of [brezis2011functional], §9.4 (the Definition, and Remark 22
for $k \ge 2$): the closure of the test functions $C_c^\infty(\Omega)$ in
`SobolevEuclidean N k p Ω`.

The book takes the closure of $C_c^1(\Omega)$, or of $C_c^k(\Omega)$ for $k \ge 2$, and not of
$C_c^\infty(\Omega)$. The closures agree, because every function of $W^{k,p}(\Omega)$ with
compact support lies in this closure ([brezis2011functional], Lemma 9.5). -/
noncomputable abbrev SobolevEuclideanZero (N k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) :
    Submodule ℝ (SobolevEuclidean N k p Ω) :=
  SobolevMultiIndexZero ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k p Ω volume

/-- The vector $i$ of the standard basis of $\mathbb{R}^N$ is $e_i$, which is
`EuclideanSpace.single i 1`. -/
theorem EuclideanSpace.basisFun_toBasis_apply {N : ℕ} (i : Fin N) :
    ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) i
      = EuclideanSpace.single i 1 := by
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]

end Euclidean

/-! ### Bounded lifts into $W^{k,p}(\Omega)$ and $H^k(\Omega)$ by the closed graph theorem -/

section ClosedGraph

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {k k' : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Ω Ω' : Opens E}
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ]

namespace SobolevMultiIndex

/-- The **closed graph theorem** for an operator between Sobolev spaces. Let $E$ be
finite-dimensional with its Borel $\sigma$-algebra, let $F$ be complete, let $p, q \ge 1$, let
$\Omega, \Omega' \subseteq E$ be open, and let $\mu$ be locally finite and finite on compact
sets. Let $T : W^{k,p}(\Omega) \to W^{k',q}(\Omega')$ be linear, and let
$G : W^{k,p}(\Omega) \to L^q(\Omega')$ be continuous with $\iota(T u) = G(u)$ for every $u$,
where $\iota : W^{k',q}(\Omega') \to L^q(\Omega')$ is the inclusion `SobolevMultiIndex.fnL`.
Then $T$ is continuous.

Both spaces are Banach spaces, and the graph of $T$ is closed because the inclusions
$W^{k,p} \to L^p$ are continuous and injective. -/
theorem continuous_of_fnL_comp_eq
    (T : SobolevMultiIndex F b k p Ω μ →ₗ[ℝ] SobolevMultiIndex F b k' q Ω' μ)
    {G : SobolevMultiIndex F b k p Ω μ → Lp F q (μ.restrict (Ω' : Set E))} (hG : Continuous G)
    (hT : ∀ u, fnL F b k' q Ω' μ (T u) = G u) : Continuous T := by
  refine T.continuous_of_seq_closed_graph fun u x y hu hTu ↦ ?_
  have h1 : Tendsto (fun n ↦ fnL F b k' q Ω' μ (T (u n))) atTop (𝓝 (fnL F b k' q Ω' μ y)) :=
    ((fnL F b k' q Ω' μ).continuous.tendsto y).comp hTu
  have h2 : Tendsto (fun n ↦ fnL F b k' q Ω' μ (T (u n))) atTop
      (𝓝 (fnL F b k' q Ω' μ (T x))) := by
    simp only [hT]
    exact (hG.tendsto x).comp hu
  exact fnL_injective (tendsto_nhds_unique h1 h2)

/-- Let $E$ be finite-dimensional with its Borel $\sigma$-algebra, let $F$ be complete, let
$p, q \ge 1$, let $\Omega, \Omega' \subseteq E$ be open, and let $\mu$ be locally finite and
finite on compact sets. Let $G : W^{k,p}(\Omega) \to L^q(\Omega')$ be a bounded linear map such
that the function $G(u)$ lies in $W^{k',q}(\Omega')$ for every $u$. Then some bounded linear map
$T : W^{k,p}(\Omega) \to W^{k',q}(\Omega')$ satisfies $\iota(T u) = G(u)$ for every $u$, where
$\iota$ is the inclusion `SobolevMultiIndex.fnL`.

The lift is defined through `MemSobolevMultiIndex.exists_sobolevMultiIndex`. It is linear
because weak derivatives are unique, and it is continuous by the closed graph theorem
(`SobolevMultiIndex.continuous_of_fnL_comp_eq`). -/
theorem exists_continuousLinearMap_of_forall_memSobolevMultiIndex
    (G : SobolevMultiIndex F b k p Ω μ →L[ℝ] Lp F q (μ.restrict (Ω' : Set E)))
    (hG : ∀ u, MemSobolevMultiIndex b (G u) k' q Ω' μ) :
    ∃ T : SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k' q Ω' μ,
      ∀ u, fnL F b k' q Ω' μ (T u) = G u := by
  choose T' hT' using fun u ↦ (hG u).exists_sobolevMultiIndex
  have hfn : ∀ u, fnL F b k' q Ω' μ (T' u) = G u := fun u ↦ by
    apply Lp.ext
    rw [fnL_apply]
    exact hT' u
  have hadd : ∀ u v, T' (u + v) = T' u + T' v := fun u v ↦
    fnL_injective (by rw [map_add, hfn, hfn, hfn, map_add])
  have hsmul : ∀ (c : ℝ) u, T' (c • u) = c • T' u := fun c u ↦
    fnL_injective (by rw [map_smul, hfn, hfn, map_smul])
  obtain ⟨Tₗ, hTₗ⟩ : ∃ Tₗ : SobolevMultiIndex F b k p Ω μ →ₗ[ℝ] SobolevMultiIndex F b k' q Ω' μ,
      ∀ u, Tₗ u = T' u := ⟨{ toFun := T', map_add' := hadd, map_smul' := hsmul }, fun _ ↦ rfl⟩
  have hT : ∀ u, fnL F b k' q Ω' μ (Tₗ u) = G u := fun u ↦ by rw [hTₗ]; exact hfn u
  have hcont : Continuous Tₗ := continuous_of_fnL_comp_eq Tₗ G.continuous hT
  exact ⟨⟨Tₗ, hcont⟩, fun u ↦ hT u⟩

end SobolevMultiIndex

end General

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $X$ be a Banach space, and let
$S : X \to L^2(\Omega)$ be a bounded linear map. Suppose that for every $x \in X$ some
$U \in H^k(\Omega)$ satisfies $\iota(U) = S x$, where $\iota : H^k(\Omega) \to L^2(\Omega)$ is
the inclusion. Then some bounded linear map $T : X \to H^k(\Omega)$ satisfies $\iota(T x) = S x$
for every $x \in X$.

The proof applies the closed graph theorem in the form
`exists_continuousLinearMap_comp_eq_of_injective` along the injective inclusion
$H^k(\Omega) \to L^2(\Omega)$ (`SobolevMultiIndex.fnL_injective`). -/
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

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $X$ be a Banach space, and let
$S : X \to H^1(\Omega)$ be a bounded linear map, for example a solution map. Suppose that for
every $f \in X$ some $U \in H^k(\Omega)$ has a function that equals the function of $S f$ almost
everywhere on $\Omega$. Then there is a constant $C \ge 0$ such that for all $f \in X$ and all
$U \in H^k(\Omega)$ whose function equals the function of $S f$ almost everywhere on $\Omega$,
$$\|U\|_{H^k(\Omega)} \le C \|f\|.$$

The lift $f \mapsto U_f \in H^k(\Omega)$ is bounded, by
`SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq` along the inclusion
$H^1(\Omega) \to L^2(\Omega)$, and the element of $H^k(\Omega)$ with the function of $S f$ is
unique (`SobolevMultiIndex.ext_of_fn_ae_eq`). -/
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
