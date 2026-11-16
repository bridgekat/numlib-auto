/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Analysis.Sobolev.Boundary.GraphMeasure
import Numlib.Analysis.Sobolev.Boundary.PolygonTrace
import Numlib.Analysis.Sobolev.EmbeddingDomain
import Numlib.Analysis.Sobolev.RemovableSingularity
import Numlib.Analysis.Sobolev.Slobodeckij
import NumlibSurface.AtkinsonHan.Chapter07.Section01

/-!
# Atkinson and Han, Section 7.2: Sobolev spaces

This module formalizes Section 7.2 of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be
open, let $k \ge 0$ be an integer and let $p \in [1, \infty]$. The Sobolev space $W^{k,p}(\Omega)$
consists of the functions $v \in L^p(\Omega)$ whose weak derivatives $\partial^\alpha v$ (Section
7.1) exist and lie in $L^p(\Omega)$ for all multi-indices $\alpha$ with $|\alpha| \le k$. For
$p < \infty$ its norm is $$\|v\|_{k,p,\Omega} = \Big[\sum_{|\alpha| \le k} \|\partial^\alpha
v\|_{L^p(\Omega)}^p\Big]^{1/p}.$$ The section proves that $W^{k,p}(\Omega)$ is a Banach space and
that $H^k(\Omega) = W^{k,2}(\Omega)$ is a Hilbert space. Its examples find the powers $|x|^\lambda$
that lie in $W^{k,p}$ of the unit ball, give an unbounded function in $H^1$ of a disc in the plane,
and glue Sobolev functions on the pieces of a partitioned domain. The section then defines
$W_0^{k,p}(\Omega)$, the spaces $W^{s,p}(\Omega)$ of real order $s = k + \sigma$ with the
Sobolev–Slobodeckij seminorm, their subspaces $W_0^{s,p}(\Omega)$ and dual spaces
$W^{-s,p'}(\Omega)$, and the spaces $W^{s,p}(\partial\Omega)$ over the boundary of a domain.
Definition 7.2.1, at the start of the section, is the regularity of the boundary $\partial\Omega$ of
a domain $\Omega \subseteq \mathbb{R}^{d+1}$.

The proofs specialize the backbone modules `Numlib.Analysis.Sobolev.Domain`,
`Numlib.Analysis.Sobolev.MultiIndex`, `Numlib.Analysis.Sobolev.Space`,
`Numlib.Analysis.Sobolev.Slobodeckij`, `Numlib.Analysis.Sobolev.RemovableSingularity`,
`Numlib.Analysis.InnerProductSpace.NormPow`, `Numlib.Analysis.Sobolev.Boundary.PolygonTrace` and
`Numlib.Analysis.Sobolev.Boundary.GraphMeasure`.

## Main definitions

* Definition 7.2.1, `AtkinsonHan.Chapter07.definition_7_2_1`: the boundary of an open set
  $\Omega \subseteq \mathbb{R}^{d+1}$ is of class $V$ if near each boundary point $\Omega$ is the
  region above the graph of a function in $V$.
* Definition 7.2.2, `AtkinsonHan.Chapter07.definition_7_2_2`: $W^{k,p}(\Omega)$ in the bundled
  reading, with one weak derivative tensor for each order $n \le k$.
* Definition 7.2.2, `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`: $W^{k,p}(\Omega)$ in the
  book's reading, with one weak derivative $\partial^\alpha v$ for each multi-index $\alpha$ with
  $|\alpha| \le k$.
* Definition 7.2.9, `AtkinsonHan.Chapter07.definition_7_2_9`: $W_0^{k,p}(\Omega)$, the closure of
  $C_0^\infty(\Omega)$ in $W^{k,p}(\Omega)$.
* Definition 7.2.10, `AtkinsonHan.Chapter07.definition_7_2_10`: $W^{s,p}(\Omega)$ for
  $s = k + \sigma$, the functions of $W^{k,p}(\Omega)$ whose derivatives of order $k$ have a finite
  Sobolev–Slobodeckij seminorm.
* Definition 7.2.11, `AtkinsonHan.Chapter07.definition_7_2_11`: $W_0^{s,p}(\Omega)$, the closure of
  $C_0^\infty(\Omega)$ in $W^{s,p}(\Omega)$.
* Definition 7.2.12, `AtkinsonHan.Chapter07.definition_7_2_12`,
  `AtkinsonHan.Chapter07.definition_7_2_12_integerOrder` and
  `AtkinsonHan.Chapter07.definition_7_2_12_hMinusOne`: the dual space $W^{-s,p'}(\Omega)$ of
  $W_0^{s,p}(\Omega)$, its case of integer order, and $H^{-1}(\Omega)$.
* Definition 7.2.13, `AtkinsonHan.Chapter07.definition_7_2_13_atlas`,
  `AtkinsonHan.Chapter07.definition_7_2_13` and `AtkinsonHan.Chapter07.definition_7_2_13_hs`:
  $W^{s,p}(\partial\Omega)$ over the boundary of a bounded $C^1$ domain, for a given patch system
  and for a chosen one, and $H^s(\partial\Omega)$.
* Definition 7.2.13, `AtkinsonHan.Chapter07.definition_7_2_13_norm`: the norm
  $\max_i \|v \circ g_i\|_{W^{s,p}(D_i)}$ of $W^{s,p}(\partial\Omega)$.

## Main results

* Definition 7.2.1, `AtkinsonHan.Chapter07.definition_7_2_1_iff`,
  `AtkinsonHan.Chapter07.definition_7_2_1_lipschitzDomain` and
  `AtkinsonHan.Chapter07.definition_7_2_1_contDiffDomain`: the definition unfolded, and its two
  named cases, the Lipschitz domains and the $C^n$ domains.
* Definition 7.2.1, `AtkinsonHan.Chapter07.definition_7_2_1_finite_cover`: if $\Omega$ is bounded,
  finitely many balls of the definition cover $\partial\Omega$.
* Definition 7.2.2, `AtkinsonHan.Chapter07.definition_7_2_2_iff_definition_7_2_2_multiIndex`: the
  two readings of the definition give the same functions.
* Definition 7.2.2, `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_norm`: the norm of the normed
  space of the book's reading is the norm $\|\cdot\|_{k,p,\Omega}$ of the definition.
* Theorem 7.2.3, `AtkinsonHan.Chapter07.theorem_7_2_3`: $W^{k,p}(\Omega)$ is a Banach space, for
  each of the two norms.
* Corollary 7.2.4, `AtkinsonHan.Chapter07.corollary_7_2_4`: $H^k(\Omega)$ is a Hilbert space with
  the inner product $(u, v)_k = \int_\Omega \sum_{|\alpha| \le k} \partial^\alpha u \,
  \partial^\alpha v \, dx$.
* Example 7.2.5, `AtkinsonHan.Chapter07.example_7_2_5_memLp`: on the unit ball,
  $|x|^\lambda \in L^p$ if and only if $\lambda > -d/p$.
* Example 7.2.5, `AtkinsonHan.Chapter07.example_7_2_5_memW1p`: on the unit ball and for
  $\lambda \neq 0$, $|x|^\lambda \in W^{1,p}$ if and only if $\lambda > 1 - d/p$.
* Example 7.2.5, `AtkinsonHan.Chapter07.example_7_2_5_const`: $|x|^0 = 1$ lies in every $W^{k,p}$,
  which is a counterexample to (7.2.1).
* Example 7.2.5, `AtkinsonHan.Chapter07.example_7_2_5_mpr`: on the unit ball,
  $|x|^\lambda \in W^{k,p}$ whenever $\lambda > k - d/p$.
* Example 7.2.5, `AtkinsonHan.Chapter07.example_7_2_5_of_forall_ne`: equation (7.2.1) for every real
  $\lambda$ that is not one of $0, 1, \dots, k - 1$.
* Example 7.2.5, `AtkinsonHan.Chapter07.example_7_2_5`: equation (7.2.1) for every real $\lambda$
  that is not a nonnegative even integer.
* Example 7.2.6, `AtkinsonHan.Chapter07.example_7_2_6`: on a disc $B(0, \beta)$ with
  $0 < \beta < 1$, the function $\log(\log(1/|x|))$ lies in $H^1$ and is unbounded.
* Example 7.2.7, `AtkinsonHan.Chapter07.example_7_2_7_continuous` and
  `AtkinsonHan.Chapter07.example_7_2_7`: on a triangulated plane domain, a function that is
  continuous (or $C^k$) up to the boundary and lies in $W^{1,p}$ (or $W^{k+1,p}$) on every element
  lies in $W^{1,p}(\Omega)$ (or $W^{k+1,p}(\Omega)$).
* Example 7.2.8, `AtkinsonHan.Chapter07.example_7_2_8`: if a function of $W^{1,p}(\Omega)$ is
  continuous on each closed element of a triangulation without slits, its pieces agree on every
  interior edge.
* Definition 7.2.10, `AtkinsonHan.Chapter07.definition_7_2_10_iff_exists` and
  `AtkinsonHan.Chapter07.definition_7_2_10_norm`: the elements of the normed space
  `SobolevSlobodeckij` are the functions of the definition, and its norm is the norm that the
  definition displays.

## Proof outline

For Example 7.2.5, the derivatives of order $n$ of $|x|^\lambda$ are bounded by
$C_n |x|^{\lambda - n}$, because the function is homogeneous. A removable-singularity lemma,
`hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton`, shows that the classical derivatives on
$\Omega \setminus \{0\}$ are the weak derivatives on $\Omega$. Sufficiency in (7.2.1) then follows
from the $L^p$ part of the example. Necessity reads the size of $|x|^{\lambda - k}$ off the radial
derivative $D^k |\cdot|^\lambda(x)(x/|x|, \dots, x/|x|) = \lambda(\lambda - 1) \cdots (\lambda -
k + 1) |x|^{\lambda - k}$. Where this vanishes, at $\lambda \in \{0, 1, \dots, k - 1\}$, the proof
uses a direction orthogonal to $x$ when $d \ge 2$, and the jump of
$D^m |x|^m = m! \operatorname{sign} x$ at the origin when $d = 1$. Example 7.2.6 uses the same
removable-singularity lemma. Its radial integral $\int_0^\beta dr/(r \log^2 r) = -1/\log \beta$ is
improper at the origin, but it becomes an ordinary integral because the antiderivative $-1/\log r$
extends continuously by $0$.

## Conventions

* An open set $\Omega \subseteq \mathbb{R}^d$ is an element of the type `TopologicalSpace.Opens`,
  and integrals are taken for the Lebesgue measure `volume`. The standard basis $e_1, \dots, e_d$ of
  $\mathbb{R}^d$ is `AtkinsonHan.Chapter07.stdBasis d`, written `stdBasis d` in the Lean expressions
  below.
* A multi-index is `α : Fin d → ℕ`, and its length $|\alpha| = \sum_i \alpha_i$ is the Lean sum
  `∑ i, α i`. The derivative $\partial^\alpha$ is taken along the tuple of directions
  `multiIndexTuple (stdBasis d) α`, in which the basis vector $e_i$ appears $\alpha_i$ times.
* The exponent $p$ is `p : ℝ≥0∞`. The instance `Fact (1 ≤ p)` says that $p$ is at least $1$, where a
  normed space needs it, and `p ≠ ⊤` says that $p$ is finite.
* The function $|x|^\lambda$ is `‖x‖ ^ lam`, the real power `Real.rpow`. At $x = 0$ its value is $0$
  for $\lambda \neq 0$ and $1$ for $\lambda = 0$.
* In Definitions 7.2.1 and 7.2.13 the domain lies in $\mathbb{R}^{d+1}$, so that the graph functions
  are defined on $\mathbb{R}^d$. The book's $d$ is $d + 1$ there.

## Implementation notes

* Definition 7.2.2 has two readings, and they differ in their norms. The normed space
  `Sobolev ℝ k p Ω volume` of the bundled reading carries the norm `sobolevNorm` (by
  `Sobolev.norm_eq`), which sums over the orders $n \le k$ and measures each derivative tensor in
  its operator norm. The normed space `SobolevMultiIndex ℝ (stdBasis d) k p Ω volume` of the book's
  reading carries the norm $\|\cdot\|_{k,p,\Omega}$ of the definition. The two norms are equivalent,
  because the derivative tensors of a Sobolev function are symmetric, but this equivalence is not
  formalized. Therefore the two clauses of Theorem 7.2.3 are proved separately. Only the norm of the
  book's reading comes from an inner product at $p = 2$, and Corollary 7.2.4 uses it.
* The passage from the book's reading of Definition 7.2.2 to the bundled one needs the symmetry of
  the iterated derivative of a $C^\infty$ test function under permutations of its arguments. Mathlib
  has this symmetry only for order two and for analytic functions. The backbone proves it as
  `ContDiff.iteratedFDeriv_congr_perm`.
* Definition 7.2.9 is a closure in the bundled normed space `Sobolev`, and Definition 7.2.11 is a
  closure in the normed space `SobolevSlobodeckij` of Definition 7.2.10. That every test function
  lies in $W^{s,p}(\Omega)$ is not proved; see the implementation notes of
  `Numlib.Analysis.Sobolev.Slobodeckij`.
* In Definitions 7.2.10 to 7.2.13 the parameters $k$, $\sigma$ and $p$ of the order $s = k + \sigma$
  have no constraint. The constraints of the book make the spaces the book's spaces, but the
  definitions are well formed without them.
* Examples 7.2.7 and 7.2.8 are stated on a plane domain $\Omega$ with a triangulation
  `𝒯 : Triangulation Ω`. The sub-domains are the open triangles `Triangulation.Kopens`, and the
  interfaces are the edges. The integration by parts on each sub-domain is Green's formula on a
  triangle from `Numlib.Analysis.Sobolev.Boundary.PolygonTrace`.
* In Definition 7.2.13 the patch system is a graph atlas `GraphAtlas`, and the surface measure is
  `IsContDiffDomain.boundaryMeasure`, which does not depend on the atlas (`GraphAtlas.measure_eq`).
  The patches are $C^1$.

## Deviations from the source

* **Example 7.2.5, the $L^p$ part** (generalization). The book takes $1 \le p < \infty$. The
  statement holds for every $0 < p < \infty$. See `AtkinsonHan.Chapter07.example_7_2_5_memLp`.
* **Example 7.2.5, the equivalence for $W^{1,p}$** (correction). The book states $|x|^\lambda \in
  W^{1,p}(\Omega) \iff \lambda > 1 - d/p$ for every real $\lambda$. It fails at $\lambda = 0$ when
  $d \le p$. The statement assumes $\lambda \neq 0$. See
  `AtkinsonHan.Chapter07.example_7_2_5_memW1p`.
* **Example 7.2.5, equation (7.2.1)** (correction). The book prints $|x|^\lambda \in W^{k,p}(\Omega)
  \iff \lambda > k - d/p$ with no restriction on $\lambda$. It fails when $\lambda$ is a nonnegative
  even integer, where $|x|^\lambda$ is a polynomial. The statement excludes these values. See
  `AtkinsonHan.Chapter07.example_7_2_5` and `AtkinsonHan.Chapter07.example_7_2_5_const`.
* **Example 7.2.7** (reading). The class $C^k(\bar\Omega)$ is read as the functions that are $C^k$
  on an open set that contains $\bar\Omega$. See `AtkinsonHan.Chapter07.example_7_2_7`.
* **Definition 7.2.13** (reading). The book asks $v \in L^2(\partial\Omega)$ for every $p$. The
  definition asks $v \in L^p(\partial\Omega)$. See `AtkinsonHan.Chapter07.definition_7_2_13_atlas`.

## Not formalized

* **Examples 7.2.7 and 7.2.8 on a Lipschitz domain divided into Lipschitz sub-domains.** Lipschitz
  domains in general are out of scope; the examples are stated on triangulated plane domains.
* **Example 7.2.8, the continuity of $v$ at the vertices.** It needs in addition that the elements
  around each vertex are connected through shared edges, which the axioms of a triangulation do not
  give.
* **Definition 7.2.10, the completeness of $W^{s,p}(\Omega)$, its reflexivity for $1 < p < \infty$,
  and its Hilbert structure for $p = 2$.** The book states these facts without proof.
* **Definition 7.2.12, the embedding of $L^2(\Omega)$ in $H^{-1}(\Omega)$ by
  $\langle f, v \rangle = \int_\Omega f v$, and the representation
  $\ell = \ell_0 - \sum_i \partial_i \ell_i$ of each $\ell \in H^{-1}(\Omega)$ with
  $\ell_0, \dots, \ell_d \in L^2(\Omega)$.** The book states the second without proof.
* **Definition 7.2.13 for patches of class $C^{k,\alpha}$ other than $C^1$.**
* **Definition 7.2.13, the independence of the patch system.** It needs the invariance of the
  Sobolev–Slobodeckij seminorm under $C^1$ changes of variables, which the backbone does not have.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace

open scoped ENNReal Real RealInnerProductSpace Topology

namespace AtkinsonHan.Chapter07

variable {d : ℕ}

/-- **Definition 7.2.1** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open
and let $V$ be a set of real functions on $\mathbb{R}^d$. The boundary $\partial\Omega$ is **of
class $V$** if for each $x_0 \in \partial\Omega$ there are an $r > 0$ and a $g \in V$ such that,
after a transformation of the coordinate system if necessary, $$\Omega \cap B(x_0, r) = \{x \in
B(x_0, r) : x_{d+1} > g(x_1, \dots, x_d)\}.$$

The predicate is the backbone's `IsBoundaryOfClass`. A transformation of the coordinate system
is an affine isometry of $\mathbb{R}^{d+1}$, that is, a rigid motion. The dimension of the
ambient space is written $d + 1$, so that the graph functions are defined on $\mathbb{R}^d$
without a truncated subtraction; the book's $d$ is $d + 1$ here. The book assumes throughout
Section 7.2 that $\Omega$ is open and bounded. Openness is carried by the type
`TopologicalSpace.Opens`. Boundedness is not part of the definition, and
`AtkinsonHan.Chapter07.definition_7_2_1_finite_cover` assumes it. The two named classes of the
definition are `AtkinsonHan.Chapter07.definition_7_2_1_lipschitzDomain` and
`AtkinsonHan.Chapter07.definition_7_2_1_contDiffDomain`. -/
def definition_7_2_1 (V : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  IsBoundaryOfClass V (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))

/-- **Definition 7.2.1** of [han2009theoretical], unfolded. Let $\Omega \subseteq \mathbb{R}^{d+1}$
be open and let $V$ be a set of real functions on $\mathbb{R}^d$. The boundary $\partial\Omega$
is of class $V$ if and only if for every $x_0 \in \partial\Omega$ there are an $r > 0$, a rigid
motion $T$ of $\mathbb{R}^{d+1}$ and a $g \in V$ such that $$\Omega \cap B(x_0, r) = \{x \in
B(x_0, r) : g((Tx)_1, \dots, (Tx)_d) < (Tx)_{d+1}\}.$$

The point $((Tx)_1, \dots, (Tx)_d)$ is `EuclideanSpace.init (T x)`, and $(Tx)_{d+1}$ is
`T x (Fin.last d)`. -/
theorem definition_7_2_1_iff (V : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    definition_7_2_1 V Ω ↔ ∀ x₀ ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ∃ r > 0,
      ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)), ∃ g ∈ V,
        (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ ball x₀ r =
          {x ∈ ball x₀ r | g (EuclideanSpace.init (T x)) < T x (Fin.last d)} :=
  Iff.rfl

/-- **Definition 7.2.1** of [han2009theoretical], Lipschitz domains. An open set
$\Omega \subseteq \mathbb{R}^{d+1}$ is a **Lipschitz domain** if and only if $\partial\Omega$ is
of class $V$ for $V$ the set of Lipschitz continuous functions on $\mathbb{R}^d$.

The backbone predicate is `IsLipschitzDomain`. -/
theorem definition_7_2_1_lipschitzDomain (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    IsLipschitzDomain (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ↔
      definition_7_2_1 {g | ∃ K, LipschitzWith K g} Ω :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨Ω.isOpen, h⟩⟩

/-- **Definition 7.2.1** of [han2009theoretical], $C^n$ domains. Let $n$ be a natural number,
$\infty$ or $\omega$. An open set $\Omega \subseteq \mathbb{R}^{d+1}$ is a **$C^n$ domain** if
and only if $\partial\Omega$ is of class $V$ for $V$ the set of $C^n$ functions on
$\mathbb{R}^d$.

The order $n$ is `n : WithTop ℕ∞`, and the backbone predicate is `IsContDiffDomain n`. -/
theorem definition_7_2_1_contDiffDomain (n : WithTop ℕ∞)
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    IsContDiffDomain n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ↔
      definition_7_2_1 {g | ContDiff ℝ n g} Ω :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨Ω.isOpen, h⟩⟩

/-- **Definition 7.2.1** of [han2009theoretical], the finite cover of the boundary. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open and bounded, and let $\partial\Omega$ be of class
$V$. Then there are finitely many points $x_1, \dots, x_I \in \partial\Omega$ and radii
$r_1, \dots, r_I > 0$ such that $$\partial\Omega \subseteq \bigcup_{i=1}^I B(x_i, r_i),$$ and
such that in each ball $B(x_i, r_i)$, after a rigid motion of the coordinate system, $\Omega$ is
the region strictly above the graph of a function in $V$.

The cover exists because $\partial\Omega$ is compact when $\Omega$ is bounded. The pairs
$(x_i, r_i)$ form one `Finset`, and the condition in each ball is `IsBoundaryGraphAt`. -/
theorem definition_7_2_1_finite_cover {V : Set (EuclideanSpace ℝ (Fin d) → ℝ)}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (h : definition_7_2_1 V Ω) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin (d + 1)) × ℝ),
      (∀ q ∈ s, q.1 ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∧ 0 < q.2 ∧
        IsBoundaryGraphAt V (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) q.1 q.2) ∧
      frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ⋃ q ∈ s, ball q.1 q.2 :=
  h.exists_finite_cover hΩ

/-- **Definition 7.2.2** of [han2009theoretical], in the bundled reading. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let
$p \in [0, \infty]$; the book takes $p \in [1, \infty]$. A function $v$ on $\mathbb{R}^d$
belongs to the **Sobolev space $W^{k,p}(\Omega)$** if $v \in L^p(\Omega)$ and, for every order
$n \le k$, $v$ has a weak derivative of order $n$ on $\Omega$ that lies in $L^p(\Omega)$. When
$p = 2$ one writes $H^k(\Omega) \equiv W^{k,2}(\Omega)$.

A weak derivative of order $n$ is one object for all the multi-indices of length $n$: its value
at a point is a continuous $n$-linear map, as in `AtkinsonHan.Chapter07.definition_7_1_3`. The
definition is `MemSobolev` for the Lebesgue measure. The book's reading, one multi-index at a
time, is `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`. The two readings define the same
functions (`AtkinsonHan.Chapter07.definition_7_2_2_iff_definition_7_2_2_multiIndex`), so they
differ only in their norms, and the book's reading is the one to use when the norm matters. The
norm and seminorm of this reading are `sobolevNorm v k p Ω volume` and
`sobolevSeminorm v k p Ω volume`. They sum over the orders $n \le k$ and not over the
multi-indices, so they are equivalent to, but not equal to, the norm and seminorm of the book.
The book's norm is `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_norm`. The book's seminorm
$|v|_{k,p,\Omega} = [\sum_{|\alpha| = k} \|\partial^\alpha v\|_{L^p(\Omega)}^p]^{1/p}$ is
`SobolevMultiIndex.topSeminorm`, and `Numlib.Analysis.Sobolev.SeminormCompare` compares it with
`sobolevSeminorm` in both directions, with constants that depend only on $k$ and $d$. -/
def definition_7_2_2 (k : ℕ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  MemSobolev v k p Ω volume

/-- **Definition 7.2.2** of [han2009theoretical], unfolded in the bundled reading. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let
$p \in [0, \infty]$. Then $v \in W^{k,p}(\Omega)$ in the bundled reading if and only if
$v \in L^p(\Omega)$ and, for every $n \le k$, there is a weak derivative $w$ of order $n$ of $v$
on $\Omega$, in the sense of Definition 7.1.3, with $w \in L^p(\Omega)$.

The weak derivative is `AtkinsonHan.Chapter07.definition_7_1_3`, whose values are continuous
$n$-linear maps on $\mathbb{R}^d$. -/
theorem definition_7_2_2_iff (k : ℕ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2 k p Ω v ↔ MemLp v p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) ∧
      ∀ n ≤ k, ∃ w, definition_7_1_3 n v w Ω ∧
        MemLp w p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) := by
  simp only [definition_7_2_2, MemSobolev, definition_7_1_3, Nat.cast_le]

/-- **Definition 7.2.2** of [han2009theoretical], on the normed space of the bundled reading. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let
$p \in [1, \infty]$. Then $v \in W^{k,p}(\Omega)$ in the bundled reading if and only if there is
an element $u$ of the normed space `Sobolev ℝ k p Ω volume` whose function agrees with $v$
almost everywhere on $\Omega$.

The element $u$ is then unique, by `Sobolev.ext_of_fn_ae_eq`. The normed space carries the norm
`sobolevNorm`, by `Sobolev.norm_eq`. -/
theorem definition_7_2_2_iff_exists (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2 k p Ω v ↔ ∃ u : Sobolev ℝ k p Ω volume,
      Sobolev.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))] v :=
  ⟨fun h ↦ h.exists_sobolev, fun ⟨_, hu⟩ ↦ (Sobolev.memSobolev _).congr_ae hu⟩

/-- **Definition 7.2.2** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open, let
$k \ge 0$ be an integer and let $p \in [0, \infty]$; the book takes $p \in [1, \infty]$. A
function $v$ on $\mathbb{R}^d$ belongs to the **Sobolev space $W^{k,p}(\Omega)$** if
$v \in L^p(\Omega)$ and, for each multi-index $\alpha$ with $|\alpha| \le k$, the weak
derivative $\partial^\alpha v$ exists on $\Omega$ and lies in $L^p(\Omega)$.

This is the book's reading, with one function for each multi-index $\alpha$;
`AtkinsonHan.Chapter07.definition_7_2_2` is the bundled reading. The norm of the definition sums
over these multi-indices, so Theorem 7.2.3 and Corollary 7.2.4 are stated with the book's norm
on this reading. The definition is `MemSobolevMultiIndex` for the standard basis
`AtkinsonHan.Chapter07.stdBasis d` and the Lebesgue measure. -/
def definition_7_2_2_multiIndex (k : ℕ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  MemSobolevMultiIndex (stdBasis d) v k p Ω volume

/-- **Definition 7.2.2** of [han2009theoretical], unfolded in the book's reading. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let
$p \in [0, \infty]$. Then $v \in W^{k,p}(\Omega)$ in the book's reading if and only if
$v \in L^p(\Omega)$ and, for every multi-index $\alpha$ with $|\alpha| \le k$, there is a weak
derivative $w = \partial^\alpha v$ on $\Omega$, in the sense of Definition 7.1.3, with
$w \in L^p(\Omega)$.

The weak derivative is `AtkinsonHan.Chapter07.definition_7_1_3_multiIndex`. -/
theorem definition_7_2_2_multiIndex_iff (k : ℕ) (p : ℝ≥0∞)
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2_multiIndex k p Ω v ↔
      MemLp v p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) ∧
        ∀ α : Fin d → ℕ, ∑ i, α i ≤ k → ∃ w, definition_7_1_3_multiIndex α v w Ω ∧
          MemLp w p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) :=
  Iff.rfl

/-- **Definition 7.2.2** of [han2009theoretical], from the bundled reading to the book's reading.
Let $\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let
$p \in [0, \infty]$. If $v \in W^{k,p}(\Omega)$ in the bundled reading, then
$v \in W^{k,p}(\Omega)$ in the book's reading.

The derivative $\partial^\alpha v$ is the derivative tensor of order $|\alpha|$ applied to the
tuple of directions that names $\alpha$. The converse is
`AtkinsonHan.Chapter07.definition_7_2_2_of_definition_7_2_2_multiIndex`. -/
theorem definition_7_2_2_multiIndex_of_definition_7_2_2 {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : definition_7_2_2 k p Ω v) : definition_7_2_2_multiIndex k p Ω v :=
  h.memSobolevMultiIndex

/-- **Definition 7.2.2** of [han2009theoretical], from the book's reading to the bundled reading.
Let $\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let
$p \in [0, \infty]$. If $v \in W^{k,p}(\Omega)$ in the book's reading, then
$v \in W^{k,p}(\Omega)$ in the bundled reading.

This is the converse of `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_of_definition_7_2_2`.
The derivative tensor of order $n$ is built from its values on the tuples of coordinate
directions, which are the $\partial^\alpha v$ for the multi-indices $\alpha$ that count the
occurrences of each direction, and is extended by multilinearity. On a tuple that is not in
increasing order the value is $\partial^\alpha v$ of the reordered tuple. So the proof needs the
symmetry of `iteratedFDeriv ℝ n φ x` under permutations of its arguments for a $C^\infty$ test
function $\varphi$. Mathlib has this symmetry only for $n = 2$ and for analytic functions, and a
test function is not analytic, so the backbone proves it as
`ContDiff.iteratedFDeriv_congr_perm`. -/
theorem definition_7_2_2_of_definition_7_2_2_multiIndex {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : definition_7_2_2_multiIndex k p Ω v) : definition_7_2_2 k p Ω v :=
  MemSobolevMultiIndex.memSobolev h

/-- **Definition 7.2.2** of [han2009theoretical], equivalence of the two readings. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let
$p \in [0, \infty]$. Then $v \in W^{k,p}(\Omega)$ in the bundled reading if and only if
$v \in W^{k,p}(\Omega)$ in the book's reading, one multi-index at a time.

The two readings do not share their norms: `sobolevNorm` sums over the orders $n \le k$, and the
norm of Definition 7.2.2 sums over the multi-indices $\alpha$ with $|\alpha| \le k$. The
equivalence of these two norms is not formalized. -/
theorem definition_7_2_2_iff_definition_7_2_2_multiIndex {k : ℕ} {p : ℝ≥0∞}
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ} :
    definition_7_2_2 k p Ω v ↔ definition_7_2_2_multiIndex k p Ω v :=
  memSobolev_iff_memSobolevMultiIndex (stdBasis d)

/-- **Definition 7.2.2** of [han2009theoretical], on the normed space of the book's reading. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let
$p \in [1, \infty]$. Then $v \in W^{k,p}(\Omega)$ in the book's reading if and only if there is
an element $u$ of the normed space `SobolevMultiIndex ℝ (stdBasis d) k p Ω volume` whose
function agrees with $v$ almost everywhere on $\Omega$.

The element $u$ is then unique, by `SobolevMultiIndex.ext_of_fn_ae_eq`. The normed space carries
the norm $\|\cdot\|_{k,p,\Omega}$ of the definition, by
`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_norm`. -/
theorem definition_7_2_2_multiIndex_iff_exists (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    definition_7_2_2_multiIndex k p Ω v ↔
      ∃ u : SobolevMultiIndex ℝ (stdBasis d) k p Ω volume,
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))] v :=
  ⟨fun h ↦ h.exists_sobolevMultiIndex,
    fun ⟨_, hu⟩ ↦ (SobolevMultiIndex.memSobolevMultiIndex _).congr_ae hu⟩

/-- **Definition 7.2.2** of [han2009theoretical], the norm. Let $\Omega \subseteq \mathbb{R}^d$ be
open, let $k \ge 0$ be an integer and let $1 \le p < \infty$. Every element $u$ of the normed
space `SobolevMultiIndex ℝ (stdBasis d) k p Ω volume` has the norm $$\|u\|_{k,p,\Omega} =
\Big[\sum_{|\alpha| \le k} \|\partial^\alpha u\|_{L^p(\Omega)}^p\Big]^{1/p}.$$

The derivative $\partial^\alpha u$ is `SobolevMultiIndex.weakDeriv u α`, and the sum is over
`MultiIndexLE (Fin d) k`. The case $p = \infty$ of the definition, $\|u\|_{k,\infty,\Omega} =
\max_{|\alpha| \le k} \|\partial^\alpha u\|_{L^\infty(\Omega)}$, is
`SobolevMultiIndex.norm_eq_ciSup`. -/
theorem definition_7_2_2_multiIndex_norm (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (u : SobolevMultiIndex ℝ (stdBasis d) k p Ω volume) :
    ‖u‖ = (∑ α : MultiIndexLE (Fin d) k, ‖SobolevMultiIndex.weakDeriv u α‖ ^ p.toReal)
      ^ (1 / p.toReal) :=
  SobolevMultiIndex.norm_eq_sum hp u

/-- **Theorem 7.2.3** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open, let
$k \ge 0$ be an integer and let $p \in [1, \infty]$. Then the Sobolev space $W^{k,p}(\Omega)$ is
a Banach space. This holds both for the norm $\|\cdot\|_{k,p,\Omega}$ of Definition 7.2.2 and
for the norm that sums the $L^p(\Omega)$ norms of the derivative tensors of the orders
$n \le k$.

The two clauses are the two norms. The first is about
`SobolevMultiIndex ℝ (stdBasis d) k p Ω volume`, whose norm is the norm of the definition
(`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_norm`) and whose elements are the functions
of `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`
(`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_iff_exists`). The second is about
`Sobolev ℝ k p Ω volume`, whose norm is `sobolevNorm` (`Sobolev.norm_eq`) and whose elements are
the functions of `AtkinsonHan.Chapter07.definition_7_2_2`
(`AtkinsonHan.Chapter07.definition_7_2_2_iff_exists`). The two norms are equivalent, but this is
not formalized, so the two clauses are about two unrelated types and neither is derived from the
other. Only the first norm is the book's norm, and only the first comes from an inner product at
$p = 2$, which Corollary 7.2.4 needs. The hypothesis $p \ge 1$ is the instance `Fact (1 ≤ p)`,
as for the $L^p$ spaces of Mathlib. -/
theorem theorem_7_2_3 (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (SobolevMultiIndex ℝ (stdBasis d) k p Ω volume) ∧
      CompleteSpace (Sobolev ℝ k p Ω volume) :=
  ⟨inferInstance, inferInstance⟩

/-- **Corollary 7.2.4** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open and let
$k \ge 0$ be an integer. The Sobolev space $H^k(\Omega) \equiv W^{k,2}(\Omega)$ is a Hilbert
space with the inner product $$(u, v)_k = \int_\Omega \sum_{|\alpha| \le k} \partial^\alpha u(x)
\, \partial^\alpha v(x) \, dx.$$ That is, the inner product of the space is $(u, v)_k$, its norm
satisfies $\|u\|^2 = (u, u)_k$, and the space is complete.

The space $H^k(\Omega)$ is `SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume`, the book's reading
of Definition 7.2.2. Mathlib has no bundled Hilbert space: a Hilbert space is a `CompleteSpace`
with an `InnerProductSpace ℝ` structure, and the three clauses spell this out. The first clause
says that the inner product that the type carries, as a submodule of an $\ell^2$ product of
$L^2(\Omega)$ spaces, is the book's inner product. The second says that the norm of the space is
the norm of this inner product, so that $\|u\|_{k,\Omega}^2 = \int_\Omega \sum_{|\alpha| \le k}
|\partial^\alpha u|^2$; this is also `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_norm` at
$p = 2$. The third is the completeness of Theorem 7.2.3. Completeness alone does not give the
corollary. On `Sobolev ℝ k 2 Ω volume`, the same space with the equivalent norm `sobolevNorm`,
no inner product gives the norm once $k \ge 2$ and $d \ge 2$: that norm measures the derivative
tensor of order $n$ by its operator norm, and for $n \ge 2$ and $d \ge 2$ the operator norm on
`ℝ^d [×n]→L[ℝ] ℝ` is a spectral norm and fails the parallelogram law. For $k \le 1$ or $d \le 1$
the tensors are vectors and linear functionals, whose operator norm is Euclidean. The indexing
by multi-indices makes the corollary true for every $k$ and $d$. -/
theorem corollary_7_2_4 (k : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin d))) :
    (∀ u v : SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume,
        inner ℝ u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin d))),
          ∑ α : MultiIndexLE (Fin d) k,
            SobolevMultiIndex.weakDeriv u α x * SobolevMultiIndex.weakDeriv v α x) ∧
      (∀ u : SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume, ‖u‖ ^ 2 = inner ℝ u u) ∧
      CompleteSpace (SobolevMultiIndex ℝ (stdBasis d) k 2 Ω volume) :=
  ⟨fun u v ↦ by simpa [RCLike.inner_apply, mul_comm] using SobolevMultiIndex.inner_eq u v,
    fun u ↦ (real_inner_self_eq_norm_sq u).symm, inferInstance⟩

/-- **Example 7.2.5** of [han2009theoretical], the $L^p$ part. Let $d \ge 1$, let $\Omega$ be the
unit ball of $\mathbb{R}^d$, let $\lambda$ be real and let $0 < p < \infty$. The function
$v(x) = |x|^\lambda$ lies in $L^p(\Omega)$ if and only if $$\lambda > -\frac{d}{p}.$$

**Generalization.** The book takes $1 \le p < \infty$. The statement holds for every
$p \in (0, \infty)$, and the book's statement is its case $p \ge 1$.

The book's computation is $\|v\|_{L^p(\Omega)}^p = \int_\Omega |x|^{\lambda p} \, dx = c_d
\int_0^1 r^{\lambda p + d - 1} \, dr$, with $c_d$ the surface area of the unit sphere, and the
last integral converges exactly when $\lambda p + d - 1 > -1$. The polar decomposition is
`MeasureTheory.integrableOn_fun_norm_addHaar`, and the convergence criterion is
`intervalIntegral.integrableOn_Ioo_rpow_iff`. The Sobolev parts of the example rest on this
result: each order of differentiation lowers the exponent $\lambda$ by one. -/
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

/-- Let $\alpha$ be a multi-index on $\{1, \dots, d\}$ with $|\alpha| = 1$. Then there is an index
$i_0$ such that $\alpha_i = 0$ for every $i \neq i_0$. -/
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

/-- Let $b_1, \dots, b_d$ be vectors and let $\alpha$ be a multi-index with $\alpha_i = 0$ for every
$i \neq i_0$. Then every entry of the tuple of directions `multiIndexTuple b α` that names
$\alpha$ is $b_{i_0}$. -/
theorem multiIndexTuple_of_sum_eq_one {b : Fin d → EuclideanSpace ℝ (Fin d)} {α : Fin d → ℕ}
    {i₀ : Fin d} (h : ∀ i, α i ≠ 0 → i = i₀) (j : Fin (∑ i, α i)) :
    multiIndexTuple b α j = b i₀ := by
  have hmem : multiIndexTuple b α j ∈ multiIndexDirections b α := List.get_mem _ _
  rw [multiIndexDirections, List.mem_flatMap] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  rw [List.mem_replicate] at hi
  rw [hi.2, h i hi.1]

/-- For a real $\lambda$ and $x \in \mathbb{R}^d$, the linear functional $h \mapsto \lambda
|x|^{\lambda - 2} \langle x, h \rangle$ on $\mathbb{R}^d$. Away from the origin it is the
classical gradient of $v(x) = |x|^\lambda$ (`AtkinsonHan.Chapter07.hasFDerivAt_normRpowGrad`),
and its $i$-th component is the derivative $v_{x_i}(x) = \lambda |x|^{\lambda - 2} x_i$ of
Example 7.2.5. At $x = 0$ it is the zero functional. -/
noncomputable def normRpowGrad (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  (lam * ‖x‖ ^ (lam - 2)) • innerSL ℝ x

/-- Let $\lambda$ be real and let $x \in \mathbb{R}^d$ with $x \neq 0$. The function
$y \mapsto |y|^\lambda$ has the Fréchet derivative `AtkinsonHan.Chapter07.normRpowGrad lam x` at
$x$. -/
theorem hasFDerivAt_normRpowGrad (lam : ℝ) {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) ↦ ‖y‖ ^ lam) (normRpowGrad lam x) x :=
  hasFDerivAt_norm_rpow_of_ne_zero hx lam

/-- Let $\lambda$ be real, $x \in \mathbb{R}^d$ and $i \in \{1, \dots, d\}$. The functional
`AtkinsonHan.Chapter07.normRpowGrad lam x` takes the value $\lambda |x|^{\lambda - 2} x_i$ at
the basis vector $e_i$, which is the formula of Example 7.2.5. -/
theorem normRpowGrad_apply (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    normRpowGrad lam x (stdBasis d i) = lam * ‖x‖ ^ (lam - 2) * x i := by
  simp [normRpowGrad, stdBasis, EuclideanSpace.inner_single_right]

/-- Let $\lambda$ be real and $x \in \mathbb{R}^d$. The functional $\nabla |x|^\lambda$ =
`AtkinsonHan.Chapter07.normRpowGrad lam x` has the norm bound $\|\nabla |x|^\lambda\| \le
|\lambda| \, |x|^{\lambda - 1}$. Equality holds away from the origin, but this result states
only the bound. -/
theorem norm_normRpowGrad_le (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖normRpowGrad lam x‖ ≤ |lam| * ‖x‖ ^ (lam - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [normRpowGrad, map_zero, smul_zero, norm_zero]
    positivity
  · rw [← (hasFDerivAt_normRpowGrad lam hx).fderiv, norm_fderiv_norm_rpow_of_ne_zero hx lam]

/-- For a real $\lambda$ and every measure $\mu$ on $\mathbb{R}^d$, the map $x \mapsto$
`AtkinsonHan.Chapter07.normRpowGrad lam x` is almost everywhere strongly measurable for $\mu$. -/
theorem aestronglyMeasurable_normRpowGrad (lam : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : AEStronglyMeasurable (normRpowGrad lam) μ :=
  AEStronglyMeasurable.smul
    (measurable_const.mul (measurable_norm.pow measurable_const)).aestronglyMeasurable
    (innerSL ℝ).continuous.aestronglyMeasurable

/-- Let $d \ge 1$, let $\lambda > 1 - d$ and let $t$ be real. The map
$x \mapsto \nabla |x|^\lambda$ = `AtkinsonHan.Chapter07.normRpowGrad lam x` is integrable on the
ball $B(0, t)$ of $\mathbb{R}^d$. -/
theorem integrableOn_normRpowGrad (hd : 0 < d) {lam : ℝ} (hlam : 1 - (d : ℝ) < lam) (t : ℝ) :
    IntegrableOn (normRpowGrad (d := d) lam) (ball 0 t) volume := by
  refine Integrable.mono' ((integrableOn_normRpow hd (q := lam - 1) (by linarith) t).const_mul
    |lam|) (aestronglyMeasurable_normRpowGrad lam _).restrict
    (Filter.Eventually.of_forall fun x ↦ ?_)
  exact norm_normRpowGrad_le lam x

/-- **Example 7.2.5** of [han2009theoretical], the weak first derivatives. Let $d \ge 1$, let
$\lambda > 1 - d$ and let $t$ be real. Let $\alpha$ be a multi-index with $|\alpha| = 1$ and
$\alpha_i = 0$ for every $i \neq i_0$. Then on the ball $B(0, t)$ of $\mathbb{R}^d$ the function
$v(x) = |x|^\lambda$ has the weak derivative $$\partial^\alpha v(x) = \lambda |x|^{\lambda - 2}
x_{i_0}.$$

The book passes over this step with "it can be verified". The classical derivative exists on
$B(0, t) \setminus \{0\}$, and the result says that it is the weak derivative on the whole ball,
the origin included. The derivative is written as `AtkinsonHan.Chapter07.normRpowGrad lam x`
applied to $e_{i_0}$. The proof is the backbone lemma
`hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton`, whose smallness hypothesis
$\int_{B(0,\delta)} |v| = o(\delta)$ holds because $\lambda > 1 - d$. -/
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

/-- **Example 7.2.5** of [han2009theoretical], the $W^{1,p}$ part. Let $d \ge 1$, let $\Omega$ be
the unit ball of $\mathbb{R}^d$, let $\lambda \neq 0$ be real and let $1 \le p < \infty$. The
function $v(x) = |x|^\lambda$ lies in $W^{1,p}(\Omega)$ if and only if $$\lambda > 1 -
\frac{d}{p}.$$ This is the equivalence that the book displays above (7.2.1).

**Correction.** The book states the equivalence without the hypothesis $\lambda \neq 0$, and it
is false without it. At $\lambda = 0$ the function is the constant $1$, which lies in
$W^{k,p}(\Omega)$ for every $k$ and every $p$, while $0 > 1 - d/p$ fails as soon as $d \le p$.
So the equivalence fails at $d = p = 2$ and $\lambda = 0$;
`AtkinsonHan.Chapter07.example_7_2_5_const` proves this case. The book reads off
$|\nabla v| = |\lambda| \, |x|^{\lambda - 1}$ and concludes that $\nabla v \in L^p(\Omega)$
exactly when $(\lambda - 1)p + d > 0$, which is right only when the factor $|\lambda|$ is
nonzero. The same defect makes the general equivalence (7.2.1),
$v \in W^{k,p}(\Omega) \iff \lambda > k - d/p$, false: when $\lambda$ is a nonnegative even
integer, $|x|^\lambda = (x \cdot x)^{\lambda/2}$ is a polynomial and lies in $W^{k,p}(\Omega)$
for every $k$, while $\lambda > k - d/p$ fails once $k \ge \lambda + d/p$.

Membership of $W^{1,p}(\Omega)$ is in the book's reading,
`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`. The proof applies
`AtkinsonHan.Chapter07.example_7_2_5_memLp` at the exponents $\lambda$ and $\lambda - 1$, with
`AtkinsonHan.Chapter07.hasWeakIteratedLineDerivOn_normRpow` for the weak derivative through the
origin. For the converse, the weak derivative agrees with the classical one off the origin
(`hasWeakIteratedLineDerivOn_of_hasFDerivAt`), and the size of $|x|^{\lambda - 1}$ is read off
the radial component $\sum_i (x_i/|x|) \, v_{x_i}(x) = \lambda |x|^{\lambda - 1}$ of the
gradient. -/
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
          exact (Real.norm_eq_abs (x i)).ge.trans (PiLp.norm_apply_le x i)
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
      rw [hcalc, ← EuclideanSpace.real_norm_sq_eq]
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

/-- Let $n$ be a natural number and let $y$ be a tuple of $n$ vectors of $\mathbb{R}^d$. The $n$-th
derivative of the constant function $1$ on $\mathbb{R}^d$, applied to $y$, takes the same value
at any two points $x$ and $x'$. -/
theorem iteratedFDeriv_one_apply_const {n : ℕ} (y : Fin n → EuclideanSpace ℝ (Fin d))
    (x x' : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℝ n (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℝ)) x y
      = iteratedFDeriv ℝ n (fun _ : EuclideanSpace ℝ (Fin d) ↦ (1 : ℝ)) x' y := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [iteratedFDeriv_zero_apply]
  · rw [iteratedFDeriv_const_of_ne hn]
    simp

/-- **Example 7.2.5** of [han2009theoretical], the counterexample to (7.2.1). Let $k \ge 0$ be an
integer, let $p \in [0, \infty]$ and let $t$ be real. The function $v(x) = |x|^0$, which is the
constant $1$, lies in $W^{k,p}(B(0, t))$ for the ball $B(0, t)$ of $\mathbb{R}^d$.

On the unit ball and for $p < \infty$, the right-hand side of (7.2.1) at $\lambda = 0$ reads
$0 > k - d/p$, and it fails as soon as $k \ge d/p$. So (7.2.1) is false as printed, and so is
the equivalence of first order that the book displays above it. The corrected statements are
`AtkinsonHan.Chapter07.example_7_2_5_memW1p` and `AtkinsonHan.Chapter07.example_7_2_5`.
Membership is in the book's reading, `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`. The
value at $x = 0$ is also $1$, because `Real.rpow` gives $0^0 = 1$. -/
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

/-! ### Example 7.2.5 at every order: the derivatives of $|x|^\lambda$ and (7.2.1) -/

section NormRpowHigher

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Example 7.2.5** of [han2009theoretical], sufficiency in (7.2.1). Let $d \ge 1$, let $\Omega$
be the unit ball of $\mathbb{R}^d$, let $k \ge 0$ be an integer, let $1 \le p < \infty$ and let
$\lambda$ be real with $$\lambda > k - \frac{d}{p}.$$ Then $|x|^\lambda \in W^{k,p}(\Omega)$.

No restriction on $\lambda$ is needed for this half. Each weak derivative of order $n \le k$ is
the classical derivative $D^n |\cdot|^\lambda$ off the origin
(`hasWeakIteratedLineDerivOn_iteratedFDeriv_normRpow`). It is $O(|x|^{\lambda - n})$
(`exists_norm_iteratedFDeriv_normRpow_apply_le`), and hence lies in $L^p(\Omega)$ by
`AtkinsonHan.Chapter07.example_7_2_5_memLp`, because $\lambda - n > -d/p$. Membership is in the
book's reading, `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`. -/
theorem example_7_2_5_mpr (hd : 0 < d) (lam : ℝ) (k : ℕ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (hlam : (k : ℝ) - d / p.toReal < lam) :
    definition_7_2_2_multiIndex k p ⟨ball 0 1, isOpen_ball⟩ (fun x : 𝔼 ↦ ‖x‖ ^ lam) := by
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz] at hp1
    simp at hp1
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have h1pr : (1 : ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hpt hp1
  have hdp : (d : ℝ) / p.toReal ≤ d := div_le_self (by positivity) h1pr
  have hlam' : (k : ℝ) - d < lam := by linarith
  rw [definition_7_2_2_multiIndex_iff]
  refine ⟨(example_7_2_5_memLp hd lam p hp0 hpt).2 (by linarith), fun α hα ↦ ?_⟩
  refine ⟨_, hasWeakIteratedLineDerivOn_iteratedFDeriv_normRpow hd hlam' 1 (∑ i, α i) hα
    (multiIndexTuple (stdBasis d) α), ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_normRpow_apply_le (d := d) lam (∑ i, α i)
    (multiIndexTuple (stdBasis d) α)
  have hαk : ((∑ i, α i : ℕ) : ℝ) ≤ k := by exact_mod_cast hα
  have hmem : MemLp (fun x : 𝔼 ↦ C * ‖x‖ ^ (lam - (∑ i, α i : ℕ))) p
      (volume.restrict (ball 0 1)) :=
    ((example_7_2_5_memLp hd (lam - (∑ i, α i : ℕ)) p hp0 hpt).2 (by linarith)).const_mul C
  have hfr : finrank ℝ 𝔼 = d := finrank_euclideanSpace_fin
  have : Nontrivial 𝔼 := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; exact hd)
  have h0 : ∀ᵐ x : 𝔼 ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  refine hmem.of_le (aestronglyMeasurable_iteratedFDeriv_normRpow_apply hd lam _ _).restrict ?_
  filter_upwards [ae_restrict_of_ae h0] with x hx
  refine (hC x hx).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

/-- **Example 7.2.5** of [han2009theoretical], necessity in (7.2.1), abstract form. Let $d \ge 1$,
let $\Omega$ be the unit ball of $\mathbb{R}^d$, let $k \ge 0$ be an integer, let
$1 \le p < \infty$ and let $\lambda$ be real. Let $c \neq 0$ be a constant such that at every
$x \neq 0$ some unit vectors $y_1, \dots, y_k$ satisfy $$D^k |\cdot|^\lambda(x)(y_1, \dots,
y_k) = c \, |x|^{\lambda - k}.$$ If $|x|^\lambda \in W^{k,p}(\Omega)$, then $\lambda > k - d/p$.

The weak derivative tensor $W$ of order $k$ agrees almost everywhere off the origin with the
classical $D^k |\cdot|^\lambda$. So $\|W(x)\| \ge |c| \, |x|^{\lambda - k}$ almost everywhere on
the ball, and $|x|^{\lambda - k} \in L^p(\Omega)$ means $\lambda - k > -d/p$ by
`AtkinsonHan.Chapter07.example_7_2_5_memLp`. -/
theorem example_7_2_5_mp_of_forall_exists (hd : 0 < d) {lam : ℝ} {k : ℕ} {c : ℝ} (hc : c ≠ 0)
    (hy : ∀ x : 𝔼, x ≠ 0 → ∃ y : Fin k → 𝔼, (∀ i, ‖y i‖ = 1) ∧
      iteratedFDeriv ℝ k (fun z : 𝔼 ↦ ‖z‖ ^ lam) x y = c * ‖x‖ ^ (lam - k))
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (h : definition_7_2_2_multiIndex k p ⟨ball 0 1, isOpen_ball⟩ (fun x : 𝔼 ↦ ‖x‖ ^ lam)) :
    (k : ℝ) - d / p.toReal < lam := by
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz] at hp1
    simp at hp1
  have hfr : finrank ℝ 𝔼 = d := finrank_euclideanSpace_fin
  have hnt : Nontrivial 𝔼 := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; exact hd)
  -- the weak derivative tensor of order `k`
  obtain ⟨W, hW, hWp⟩ := (MemSobolevMultiIndex.memSobolev h).2 k le_rfl
  -- it is the classical derivative off the origin
  set Ω' : Opens 𝔼 := ⟨ball 0 1 ∩ {0}ᶜ, isOpen_ball.inter isOpen_compl_singleton⟩ with hΩ'
  have hΩ'le : Ω' ≤ ⟨ball 0 1, isOpen_ball⟩ := fun x hx ↦ hx.1
  have hcl : HasWeakIteratedFDerivOn k (fun x : 𝔼 ↦ ‖x‖ ^ lam)
      (iteratedFDeriv ℝ k (fun x : 𝔼 ↦ ‖x‖ ^ lam)) Ω' volume :=
    ((contDiffOn_normRpow lam k).mono inter_subset_right).hasWeakIteratedFDerivOn le_rfl
  have hae := (hW.mono hΩ'le).ae_eq hcl
  -- `|x|^{λ-k} ≤ |c|⁻¹ ‖W x‖` almost everywhere on the ball
  have hbound : ∀ᵐ x ∂(volume.restrict (ball (0 : 𝔼) 1)),
      ‖‖x‖ ^ (lam - k)‖ ≤ ‖|c|⁻¹ * ‖W x‖‖ := by
    have h0 : ∀ᵐ x : 𝔼 ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae hae] with x hx hxb hxW
    have hxΩ' : x ∈ (Ω' : Set 𝔼) := ⟨hxb, hx⟩
    obtain ⟨y, hy1, hyx⟩ := hy x hx
    have key : c * ‖x‖ ^ (lam - k) = W x y := by rw [hxW hxΩ', hyx]
    have hle : |c| * ‖x‖ ^ (lam - k) ≤ ‖W x‖ := by
      calc |c| * ‖x‖ ^ (lam - k) = ‖c * ‖x‖ ^ (lam - k)‖ := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        _ = ‖W x y‖ := by rw [key]
        _ ≤ ‖W x‖ * ∏ i, ‖y i‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖W x‖ := by simp [hy1]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul, le_div_iff₀ (abs_pos.2 hc),
      mul_comm]
    exact hle
  have hmem : MemLp (fun x : 𝔼 ↦ ‖x‖ ^ (lam - k)) p (volume.restrict (ball 0 1)) :=
    MemLp.of_le (hWp.norm.const_mul |c|⁻¹)
      (measurable_norm.pow_const _).aestronglyMeasurable hbound
  have := (example_7_2_5_memLp hd (lam - k) p hp0 hpt).1 hmem
  linarith

/-- **Example 7.2.5** of [han2009theoretical], necessity in (7.2.1). Let $d \ge 1$, let $\Omega$ be
the unit ball of $\mathbb{R}^d$, let $k \ge 0$ be an integer, let $1 \le p < \infty$, and let
$\lambda$ be real and not one of $0, 1, \dots, k - 1$. If $|x|^\lambda \in W^{k,p}(\Omega)$,
then $\lambda > k - d/p$.

The radial component of $D^k |\cdot|^\lambda$ is $D^k |\cdot|^\lambda(x)(x/|x|, \dots, x/|x|) =
\lambda(\lambda - 1) \cdots (\lambda - k + 1) \, |x|^{\lambda - k}$
(`iteratedFDeriv_normRpow_apply_unit`). Its coefficient is nonzero, so
`AtkinsonHan.Chapter07.example_7_2_5_mp_of_forall_exists` applies. At the excluded values the
radial component vanishes identically, and the proof needs another direction of differentiation;
see `AtkinsonHan.Chapter07.example_7_2_5_mp_of_two_le` and
`AtkinsonHan.Chapter07.example_7_2_5`. -/
theorem example_7_2_5_mp (hd : 0 < d) {lam : ℝ} {k : ℕ} (hlam : ∀ j : ℕ, j < k → lam ≠ j)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (h : definition_7_2_2_multiIndex k p ⟨ball 0 1, isOpen_ball⟩ (fun x : 𝔼 ↦ ‖x‖ ^ lam)) :
    (k : ℝ) - d / p.toReal < lam :=
  example_7_2_5_mp_of_forall_exists hd (c := ∏ j : Fin k, (lam - j))
    (Finset.prod_ne_zero_iff.2 fun j _ ↦ sub_ne_zero.2 (hlam j j.2))
    (fun x hx ↦ ⟨fun _ ↦ ‖x‖⁻¹ • x, fun _ ↦ by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)],
      iteratedFDeriv_normRpow_apply_unit lam k hx⟩) p hp1 hpt h

/-- **Example 7.2.5** of [han2009theoretical], equation (7.2.1) for
$\lambda \notin \{0, 1, \dots, k - 1\}$. Let $d \ge 1$, let $\Omega$ be the unit ball of
$\mathbb{R}^d$, let $k \ge 0$ be an integer, let $1 \le p < \infty$, and let $\lambda$ be real
and not one of $0, 1, \dots, k - 1$. Then $$|x|^\lambda \in W^{k,p}(\Omega) \iff \lambda > k -
\frac{d}{p}.$$

The two directions are `AtkinsonHan.Chapter07.example_7_2_5_mpr` and
`AtkinsonHan.Chapter07.example_7_2_5_mp`. For an excluded $\lambda$ that is even, $|x|^\lambda$
is a polynomial and the equivalence can fail (`AtkinsonHan.Chapter07.example_7_2_5_const`). For
an excluded $\lambda$ that is odd, the equivalence holds by another argument,
`AtkinsonHan.Chapter07.example_7_2_5`. -/
theorem example_7_2_5_of_forall_ne (hd : 0 < d) {lam : ℝ} {k : ℕ}
    (hlam : ∀ j : ℕ, j < k → lam ≠ j) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) :
    definition_7_2_2_multiIndex k p ⟨ball 0 1, isOpen_ball⟩ (fun x : 𝔼 ↦ ‖x‖ ^ lam) ↔
      (k : ℝ) - d / p.toReal < lam :=
  ⟨example_7_2_5_mp hd hlam p hp1 hpt, example_7_2_5_mpr hd lam k p hp1 hpt⟩

/-- **Example 7.2.5** of [han2009theoretical], necessity in (7.2.1) in dimension $d \ge 2$. Let
$d \ge 2$, let $\Omega$ be the unit ball of $\mathbb{R}^d$, let $k \ge 0$ be an integer, let
$1 \le p < \infty$, and let $\lambda$ be real and not a nonnegative even integer. If
$|x|^\lambda \in W^{k,p}(\Omega)$, then $\lambda > k - d/p$.

At each $x \neq 0$ the proof chooses a unit vector $u \perp x$ and puts
$h(t) = (1 + t^2)^{\lambda/2}$. For even $k$ it uses $D^k |\cdot|^\lambda(x)(u, \dots, u) =
|x|^{\lambda - k} h^{(k)}(0)$ (`iteratedFDeriv_normRpow_apply_perp`). For odd $k$ it uses the
mixed derivative $D^k |\cdot|^\lambda(x)(x/|x|, u, \dots, u) = (\lambda - k + 1) |x|^{\lambda -
k} h^{(k-1)}(0)$ (`iteratedFDeriv_normRpow_apply_cons_perp`). The derivatives of even order of
$h$ at $0$ are products $\prod_i (2i + 1)(\lambda - 2i)$, which are nonzero. So both derivatives
are $c \, |x|^{\lambda - k}$ with a constant $c \neq 0$, and
`AtkinsonHan.Chapter07.example_7_2_5_mp_of_forall_exists` concludes. These derivatives work
where the radial derivative of `AtkinsonHan.Chapter07.example_7_2_5_mp` vanishes, at the odd
integers $\lambda < k$. -/
theorem example_7_2_5_mp_of_two_le (hd : 2 ≤ d) {lam : ℝ} (hlam : ∀ j : ℕ, lam ≠ 2 * j) {k : ℕ}
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (h : definition_7_2_2_multiIndex k p ⟨ball 0 1, isOpen_ball⟩ (fun x : 𝔼 ↦ ‖x‖ ^ lam)) :
    (k : ℝ) - d / p.toReal < lam := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · refine example_7_2_5_mp_of_forall_exists (by omega)
      (iteratedDeriv_one_add_sq_rpow_two_mul_ne_zero hlam j) (fun x hx ↦ ?_) p hp1 hpt h
    obtain ⟨u, hu1, hxu⟩ := exists_norm_eq_one_inner_eq_zero
      (by rw [finrank_euclideanSpace_fin]; exact hd) x
    exact ⟨fun _ ↦ u, fun _ ↦ hu1, by
      rw [iteratedFDeriv_normRpow_apply_perp lam (2 * j) hx hu1 hxu, mul_comm]⟩
  · have hc : (lam - (2 * j : ℕ))
        * iteratedDeriv (2 * j) (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 ≠ 0 :=
      mul_ne_zero (sub_ne_zero.2 (by push_cast; exact hlam j))
        (iteratedDeriv_one_add_sq_rpow_two_mul_ne_zero hlam j)
    refine example_7_2_5_mp_of_forall_exists (by omega) hc (fun x hx ↦ ?_) p hp1 hpt h
    obtain ⟨u, hu1, hxu⟩ := exists_norm_eq_one_inner_eq_zero
      (by rw [finrank_euclideanSpace_fin]; exact hd) x
    have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
    refine ⟨Fin.cons (‖x‖⁻¹ • x) fun _ ↦ u, fun i ↦ ?_, ?_⟩
    · refine Fin.cases ?_ (fun i ↦ ?_) i
      · rw [Fin.cons_zero, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
      · rw [Fin.cons_succ]
        exact hu1
    · rw [iteratedFDeriv_normRpow_apply_cons_perp lam (2 * j) hx hu1 hxu,
        show lam - (((2 * j : ℕ) : ℝ) + 1) = lam - ((2 * j + 1 : ℕ) : ℝ) by push_cast; ring]
      ring

end NormRpowHigher

/-! ### Example 7.2.5 in dimension one: the jump of $D^m |x|^m$ -/

section DimOne

/-- Let $m$ and $n$ be natural numbers and let $x \neq 0$ in $\mathbb{R}^1$. The $n$-th derivative
of $y \mapsto |y|^m$ at $x$, applied to $n$ copies of the coordinate vector $e_1$, is
$$\varepsilon \, m(m - 1) \cdots (m - n + 1) \, |x|^{m - n},$$ where $\varepsilon = 1$ if
$x > 0$ and $\varepsilon = (-1)^n$ if $x < 0$.

These are the radial derivatives of `iteratedFDeriv_normRpow_apply_unit`, with the sign $(-1)^n$
on the negative half-line, where $e_1$ points towards the origin. The vector $e_1$ is
`AtkinsonHan.Chapter07.toE1 1`, and the coordinate of $x$ is `x 0`. -/
theorem iteratedFDeriv_normRpow_apply_toE1 (m n : ℕ) {x : E1} (hx : x ≠ 0) :
    iteratedFDeriv ℝ n (fun y : E1 ↦ ‖y‖ ^ (m : ℝ)) x (fun _ ↦ toE1 1)
      = (if 0 < x 0 then 1 else (-1 : ℝ) ^ n)
        * ((∏ j : Fin n, ((m : ℝ) - j)) * ‖x‖ ^ ((m : ℝ) - n)) := by
  have hx0 : x 0 ≠ 0 := fun h ↦ hx (eq_zero_of_apply_zero h)
  have hxe : x = toE1 (x 0) := by rw [← toE1_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hnx : ‖x‖ = |x 0| := by
    calc ‖x‖ = ‖toE1 (x 0)‖ := by rw [← hxe]
      _ = |x 0| := by rw [LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
  have hunit : ‖x‖⁻¹ • x = toE1 (|x 0|⁻¹ * x 0) := by
    rw [← smul_eq_mul, map_smul, ← hxe, hnx]
  have key := iteratedFDeriv_normRpow_apply_unit (m : ℝ) n hx
  by_cases hpos : 0 < x 0
  · rw [ite_eq_left hpos, one_mul, ← key]
    congr 1
    funext _
    rw [hunit, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  · rw [ite_eq_right hpos]
    have hneg : x 0 < 0 := lt_of_le_of_ne (not_lt.1 hpos) hx0
    have h1 : |x 0|⁻¹ * x 0 = -1 := by
      rw [abs_of_neg hneg]
      field_simp
    rw [h1, map_neg] at hunit
    rw [hunit] at key
    have h2 : (fun _ : Fin n ↦ -toE1 1) = fun _ ↦ (-1 : ℝ) • toE1 1 := by
      funext _
      rw [neg_one_smul]
    rw [h2, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at key
    have hsq : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by
      rw [← mul_pow]
      simp
    calc iteratedFDeriv ℝ n (fun y : E1 ↦ ‖y‖ ^ (m : ℝ)) x (fun _ ↦ toE1 1)
        = ((-1 : ℝ) ^ n * (-1) ^ n)
          * iteratedFDeriv ℝ n (fun y : E1 ↦ ‖y‖ ^ (m : ℝ)) x (fun _ ↦ toE1 1) := by
          rw [hsq, one_mul]
      _ = (-1 : ℝ) ^ n * ((∏ j : Fin n, ((m : ℝ) - j)) * ‖x‖ ^ ((m : ℝ) - n)) := by
          rw [mul_assoc, key]

/-- Let $\Omega_1 \subseteq \mathbb{R}^1$ be open and let $v$ and $w$ be real functions on
$\mathbb{R}^1$. If $w$ is the weak derivative of $v$ on $\Omega_1$ in the direction $e_1$, then
$x \mapsto w(x) \, \pi_1$, with $\pi_1$ the coordinate functional, is the weak Fréchet
derivative of $v$ on $\Omega_1$ in the sense of `HasWeakFDerivOn`. The reason is that every
$y \in \mathbb{R}^1$ is $y_1 e_1$, and both sides of the defining identity scale by $y_1$. -/
theorem hasWeakFDerivOn_of_dimOne {v w : E1 → ℝ} {Ω₁ : Opens E1}
    (h : HasWeakIteratedLineDerivOn ![toE1 1] v w Ω₁ volume) :
    HasWeakFDerivOn v (fun x ↦ w x • (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ)) Ω₁
      volume := by
  rw [hasWeakFDerivOn_iff]
  refine ⟨h.locallyIntegrableOn, h.locallyIntegrableOn_weakDeriv.comp_continuousLinearMap
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ)),
    fun φ y ↦ ?_⟩
  have hy : y = y 0 • toE1 1 := by
    ext i
    fin_cases i
    simp
  have hfd : ∀ x, fderiv ℝ (φ : E1 → ℝ) x y = y 0 * fderiv ℝ (φ : E1 → ℝ) x (toE1 1) :=
    fun x ↦ by
      conv_lhs => rw [hy]
      rw [map_smul, smul_eq_mul]
  have key := h.integral_smul_eq φ
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, pow_one, smul_eq_mul] at key
  calc ∫ x in (Ω₁ : Set E1), fderiv ℝ (φ : E1 → ℝ) x y • v x
      = y 0 * ∫ x in (Ω₁ : Set E1), fderiv ℝ (φ : E1 → ℝ) x (toE1 1) * v x := by
        simp only [hfd, smul_eq_mul, mul_assoc, integral_const_mul]
    _ = -((∫ x in (Ω₁ : Set E1), (φ : E1 → ℝ) x * w x) * y 0) := by
        rw [key]
        ring
    _ = -∫ x in (Ω₁ : Set E1), (φ : E1 → ℝ) x •
          (w x • (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ)) y := by
        simp only [smul_eq_mul, smul_apply, PiLp.proj_apply, ← integral_mul_const, mul_assoc]

/-- **Example 7.2.5** of [han2009theoretical], necessity in (7.2.1) in dimension one at an odd
integer exponent. Let $m$ be an odd natural number, let $k > m$ be an integer and let
$p \in [0, \infty]$. Then $|x|^m \notin W^{k,p}(-1, 1)$.

If $|x|^m$ were in this space, its weak derivative of order $m + 1$ would vanish almost
everywhere, because it is the classical derivative $D^{m+1} |x|^m = 0$ off the origin. So its
weak derivative of order $m$ would be almost everywhere constant on the connected interval
(`HasWeakFDerivOn.ae_eq_const_of_isPreconnected`). But that derivative is $m!$ on $(0, 1)$ and
$-m!$ on $(-1, 0)$, the jump of $D^m |x|^m = m! \operatorname{sign} x$ at the origin. The
derivative of order $m + 1$ in the sense of distributions is $2 \, m! \, \delta_0$, not a
function. The interval $(-1, 1)$ is the unit ball of `AtkinsonHan.Chapter07.E1`, and membership
is in the book's reading, `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`. -/
theorem example_7_2_5_mp_dimOne {m : ℕ} (hm : Odd m) {k : ℕ} (hmk : m < k) (p : ℝ≥0∞)
    (h : definition_7_2_2_multiIndex k p ⟨ball 0 1, isOpen_ball⟩
      (fun x : E1 ↦ ‖x‖ ^ (m : ℝ))) : False := by
  -- the weak derivatives of orders `m` and `m + 1` along the coordinate direction
  obtain ⟨Wm, hWm, -⟩ := (MemSobolevMultiIndex.memSobolev h).2 m (by exact_mod_cast hmk.le)
  obtain ⟨Wm1, hWm1, -⟩ := (MemSobolevMultiIndex.memSobolev h).2 (m + 1) (by exact_mod_cast hmk)
  have hLm := hWm.lineDeriv (fun _ ↦ toE1 1)
  have hLm1 := hWm1.lineDeriv (Fin.cons (toE1 1) fun _ ↦ toE1 1)
  have hcons : (fun _ : Fin (m + 1) ↦ toE1 1) = Fin.cons (toE1 1) (fun _ : Fin m ↦ toE1 1) := by
    funext i
    refine Fin.cases rfl (fun j ↦ rfl) i
  have hchain := hLm.of_cons hLm1
  -- they are the classical derivatives off the origin
  set Ω' : Opens E1 := ⟨ball 0 1 ∩ {0}ᶜ, isOpen_ball.inter isOpen_compl_singleton⟩ with hΩ'
  have hΩ'le : Ω' ≤ ⟨ball 0 1, isOpen_ball⟩ := fun x hx ↦ hx.1
  have hcl : ∀ n, HasWeakIteratedFDerivOn n (fun x : E1 ↦ ‖x‖ ^ (m : ℝ))
      (iteratedFDeriv ℝ n (fun x : E1 ↦ ‖x‖ ^ (m : ℝ))) Ω' volume := fun n ↦
    ((contDiffOn_normRpow (m : ℝ) n).mono inter_subset_right).hasWeakIteratedFDerivOn le_rfl
  have haem := (hWm.mono hΩ'le).ae_eq (hcl m)
  have haem1 := (hWm1.mono hΩ'le).ae_eq (hcl (m + 1))
  have h0 : ∀ᵐ x : E1 ∂volume, x ≠ 0 := by
    filter_upwards [ae_apply_ne_zero] with x hx hx0
    exact hx (by rw [hx0]; rfl)
  -- the derivative of order `m + 1` vanishes almost everywhere on the ball
  have hzero : (fun x ↦ Wm1 x (Fin.cons (toE1 1) fun _ ↦ toE1 1)
        • (EuclideanSpace.proj (0 : Fin 1) : E1 →L[ℝ] ℝ))
      =ᵐ[volume.restrict (ball (0 : E1) 1)] 0 := by
    filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae haem1] with x hx hxΩ hxW
    have hprod : (∏ j : Fin (m + 1), ((m : ℝ) - j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (Fin.last m)) (by simp)
    simp only [Pi.zero_apply]
    rw [hxW ⟨hxΩ, hx⟩, ← hcons, iteratedFDeriv_normRpow_apply_toE1 m (m + 1) hx, hprod,
      zero_mul, mul_zero, zero_smul]
  -- so the derivative of order `m` is almost everywhere constant on the ball
  obtain ⟨c, hc⟩ := (hasWeakFDerivOn_of_dimOne hchain).ae_eq_const_of_isPreconnected hzero
    (convex_ball _ _).isPreconnected
  -- but it takes the values `C` and `-C` on the two half balls
  set C : ℝ := ∏ j : Fin m, ((m : ℝ) - j) with hC
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦
    sub_ne_zero.2 (by exact_mod_cast (ne_of_gt j.2))
  have hval : ∀ᵐ x ∂volume, x ∈ (Ω' : Set E1) →
      Wm x (fun _ ↦ toE1 1) = (if 0 < x 0 then 1 else (-1 : ℝ) ^ m) * C := by
    filter_upwards [haem, h0] with x hx hx0 hxΩ'
    rw [hx hxΩ', iteratedFDeriv_normRpow_apply_toE1 m m hx0, sub_self, Real.rpow_zero, mul_one]
  have hcont : Continuous fun x : E1 ↦ x 0 := (EuclideanSpace.proj (0 : Fin 1)).continuous
  have hSP : volume (ball (0 : E1) 1 ∩ {x | 0 < x 0}) ≠ 0 := by
    refine (isOpen_ball.inter (isOpen_lt continuous_const hcont)).measure_ne_zero volume
      ⟨toE1 (1 / 2), ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
      norm_num
    · simp only [mem_ofPred_eq, toE1_apply]
      norm_num
  have hSN : volume (ball (0 : E1) 1 ∩ {x | x 0 < 0}) ≠ 0 := by
    refine (isOpen_ball.inter (isOpen_lt hcont continuous_const)).measure_ne_zero volume
      ⟨toE1 (-1 / 2), ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
      norm_num
    · simp only [mem_ofPred_eq, toE1_apply]
      norm_num
  have keyP : ∀ᵐ x ∂(volume.restrict (ball (0 : E1) 1 ∩ {x | 0 < x 0})), c = C := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hc,
      ae_restrict_of_ae hval,
      ae_restrict_mem ((isOpen_ball.inter (isOpen_lt continuous_const hcont)).measurableSet)]
      with x h1 h2 h3
    have hx0 : x ≠ 0 := fun hx ↦ by
      have := h3.2
      rw [hx] at this
      simp at this
    have e1 : Wm x (fun _ ↦ toE1 1) = c := h1
    have h32 : 0 < x 0 := h3.2
    rw [← e1, h2 ⟨h3.1, hx0⟩, ite_eq_left h32, one_mul]
  have keyN : ∀ᵐ x ∂(volume.restrict (ball (0 : E1) 1 ∩ {x | x 0 < 0})), c = -C := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hc,
      ae_restrict_of_ae hval,
      ae_restrict_mem ((isOpen_ball.inter (isOpen_lt hcont continuous_const)).measurableSet)]
      with x h1 h2 h3
    have hx0 : x ≠ 0 := fun hx ↦ by
      have := h3.2
      rw [hx] at this
      simp at this
    have e1 : Wm x (fun _ ↦ toE1 1) = c := h1
    have h32 : x 0 < 0 := h3.2
    rw [← e1, h2 ⟨h3.1, hx0⟩, ite_eq_right (not_lt.2 h32.le), hm.neg_one_pow, neg_one_mul]
  have hnbP : (ae (volume.restrict (ball (0 : E1) 1 ∩ {x | 0 < x 0}))).NeBot :=
    ae_neBot.2 fun hz ↦ hSP (Measure.restrict_eq_zero.1 hz)
  have hnbN : (ae (volume.restrict (ball (0 : E1) 1 ∩ {x | x 0 < 0}))).NeBot :=
    ae_neBot.2 fun hz ↦ hSN (Measure.restrict_eq_zero.1 hz)
  obtain ⟨_, hcC⟩ := keyP.exists
  obtain ⟨_, hcC'⟩ := keyN.exists
  exact hC0 (by linarith)

end DimOne

section NormRpowFinal

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Example 7.2.5** of [han2009theoretical], equation (7.2.1). Let $d \ge 1$, let $\Omega$ be the
unit ball of $\mathbb{R}^d$, let $k \ge 0$ be an integer, let $1 \le p < \infty$, and let
$\lambda$ be real and not a nonnegative even integer. Then $$|x|^\lambda \in W^{k,p}(\Omega)
\iff \lambda > k - \frac{d}{p}.$$

**Correction.** The book prints (7.2.1) with no restriction on $\lambda$ and leaves its proof to
Exercise 7.2.7. The equivalence fails when $\lambda$ is one of $0, 2, 4, \dots$: then
$|x|^\lambda$ is a polynomial and lies in $W^{k,p}(\Omega)$ for every $k$, while
$\lambda > k - d/p$ fails once $k \ge \lambda + d/p$. For $\lambda = 0$ this is
`AtkinsonHan.Chapter07.example_7_2_5_const`. The excluded values are exactly the values at which
$|x|^\lambda$ is a polynomial.

Sufficiency is `AtkinsonHan.Chapter07.example_7_2_5_mpr`, for every real $\lambda$. For
$d \ge 2$, necessity is `AtkinsonHan.Chapter07.example_7_2_5_mp_of_two_le`, which uses a
direction orthogonal to $x$. For $d = 1$ it is the radial argument
`AtkinsonHan.Chapter07.example_7_2_5_mp`, unless $\lambda$ is an odd integer $m < k$; then
`AtkinsonHan.Chapter07.example_7_2_5_mp_dimOne` shows directly that
$|x|^m \notin W^{k,p}(-1, 1)$. Membership is in the book's reading,
`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`. -/
theorem example_7_2_5 (hd : 0 < d) {lam : ℝ} (hlam : ∀ j : ℕ, lam ≠ 2 * j) (k : ℕ) (p : ℝ≥0∞)
    (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) :
    definition_7_2_2_multiIndex k p ⟨ball 0 1, isOpen_ball⟩ (fun x : 𝔼 ↦ ‖x‖ ^ lam) ↔
      (k : ℝ) - d / p.toReal < lam := by
  refine ⟨fun h ↦ ?_, example_7_2_5_mpr hd lam k p hp1 hpt⟩
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · obtain rfl : d = 1 := by omega
    by_cases hint : ∀ j : ℕ, j < k → lam ≠ j
    · exact example_7_2_5_mp hd hint p hp1 hpt h
    · obtain ⟨m, hmk, rfl⟩ : ∃ m : ℕ, m < k ∧ lam = m := by
        by_contra hne
        exact hint fun j hj hlj ↦ hne ⟨j, hj, hlj⟩
      have hm : Odd m := Nat.not_even_iff_odd.1 fun ⟨i, hi⟩ ↦ hlam i (by
        rw [hi]
        push_cast
        ring)
      exact (example_7_2_5_mp_dimOne hm hmk p h).elim
  · exact example_7_2_5_mp_of_two_le hd2 hlam p hp1 hpt h

end NormRpowFinal

/-! ### Example 7.2.6: an unbounded $H^1$ function of the plane -/

/-- Let $y > 0$ with $\log y \neq 0$. The function $t \mapsto -1/\log t$ has the derivative
$1/(y \log^2 y)$ at $y$. It is the antiderivative of the radial integrand of Example 7.2.6. -/
theorem hasDerivAt_neg_inv_log {y : ℝ} (hy0 : 0 < y) (hy : Real.log y ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ -(Real.log t)⁻¹) (y * Real.log y ^ 2)⁻¹ y := by
  have hl : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy0.ne'
  have h : HasDerivAt (fun t : ℝ ↦ -(Real.log t)⁻¹) (-(-y⁻¹ / Real.log y ^ 2)) y :=
    (hl.inv hy).neg
  have heq : -(-y⁻¹ / Real.log y ^ 2) = (y * Real.log y ^ 2)⁻¹ := by
    rw [mul_inv, neg_div, neg_neg, div_eq_mul_inv]
  rwa [heq] at h

/-- Let $\beta < 1$. The function $t \mapsto -1/\log t$ is continuous on $[0, \beta]$, with the
value $0$ at $t = 0$. This value comes from the conventions $\log 0 = 0$ and $0^{-1} = 0$ of
Lean, and it is the limit at $0$. So the improper integral of Example 7.2.6 is an ordinary one. -/
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

/-- Let $\beta < 1$. The function $y \mapsto 1/(y \log^2 y)$, the radial integrand of Example 7.2.6,
is integrable on $(0, \beta)$, although it is unbounded at the origin. The reason is that its
antiderivative $-1/\log y$ is continuous and monotone there. -/
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

/-- Let $0 < \beta < 1$. Then $$\int_0^\beta \frac{dr}{r \log^2 r} = -\frac{1}{\log \beta}.$$ This
is the radial integral of Example 7.2.6. -/
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

/-- The function $v(x) = \log(\log(1/|x|))$ on $\mathbb{R}^2$ of Example 7.2.6, written as
$\log(-\log |x|)$. With the conventions of `Real.log`, $v(0) = 0$. -/
noncomputable def logLogNorm (x : EuclideanSpace ℝ (Fin 2)) : ℝ := Real.log (-Real.log ‖x‖)

/-- For every $x \in \mathbb{R}^2$, the function `AtkinsonHan.Chapter07.logLogNorm` takes the value
$\log(\log(1/|x|))$ at $x$. -/
theorem logLogNorm_eq (x : EuclideanSpace ℝ (Fin 2)) :
    logLogNorm x = Real.log (Real.log (1 / ‖x‖)) := by
  rw [logLogNorm, one_div, Real.log_inv]

/-- For $x \in \mathbb{R}^2$, the linear functional $h \mapsto \langle x, h \rangle / (|x|^2 \log
|x|)$. Away from the origin and inside the unit disc it is the classical gradient $\nabla v(x)$
of $v(x) = \log(\log(1/|x|))$ (`AtkinsonHan.Chapter07.hasFDerivAt_logLogNorm`), and for
$0 < |x| < 1$ its norm is $1/(|x| \log(1/|x|))$. At $x = 0$ it is the zero functional. -/
noncomputable def logLogNormGrad (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (‖x‖ ^ 2 * Real.log ‖x‖)⁻¹ • innerSL ℝ x

/-- Let $x \in \mathbb{R}^2$ with $x \neq 0$ and $|x| < 1$. The function $v$ =
`AtkinsonHan.Chapter07.logLogNorm` has the Fréchet derivative
`AtkinsonHan.Chapter07.logLogNormGrad x` at $x$. -/
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

/-- For every $x \in \mathbb{R}^2$, $$\|\nabla v(x)\|^2 = \frac{1}{|x|^2 \log^2 |x|},$$ where
$\nabla v$ is `AtkinsonHan.Chapter07.logLogNormGrad`. At the origin both sides are $0$, by the
convention $0^{-1} = 0$ of Lean. -/
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

/-- Let $\beta < 1$. The function $x \mapsto \|\nabla v(x)\|^2$ is integrable on the disc
$B(0, \beta)$ of $\mathbb{R}^2$; this follows from the radial computation. -/
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

/-- **Example 7.2.6** of [han2009theoretical], the gradient integral. Let $0 < \beta < 1$, let
$\Omega = B(0, \beta) \subseteq \mathbb{R}^2$ and let $v(x) = \log(\log(1/|x|))$. Then
$$\int_\Omega |\nabla v|^2 \, dx = -\frac{2\pi}{\log \beta}.$$

The gradient $\nabla v$ is `AtkinsonHan.Chapter07.logLogNormGrad`, the classical gradient off
the origin. The radial part of the integral is `AtkinsonHan.Chapter07.integral_inv_mul_log_sq`. -/
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

/-- Let $0 < \beta < 1$. For every $x$ in the disc $B(0, \beta)$ of $\mathbb{R}^2$, the function
$v(x) = \log(\log(1/|x|))$ of Example 7.2.6 satisfies $$|v(x)| \le (4 + |\log(-\log \beta)|) \,
|x|^{-1/4}.$$ This bound puts $v$ in $L^2$, and it makes the integral of $|v|$ over a small disc
$B(0, \delta)$ be $o(\delta)$. -/
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
      _ ≤ 4 * ‖x‖ ^ (-1 / 4 : ℝ) := Real.neg_log_le_four_mul_rpow hn
      _ ≤ (4 + |Real.log (-Real.log β)|) * ‖x‖ ^ (-1 / 4 : ℝ) := by
          have := abs_nonneg (Real.log (-Real.log β))
          nlinarith [Real.rpow_nonneg hn.le (-1 / 4 : ℝ)]

/-- The function $v(x) = \log(\log(1/|x|))$ of Example 7.2.6 is measurable. -/
theorem measurable_logLogNorm : Measurable logLogNorm :=
  Real.measurable_log.comp (Real.measurable_log.comp measurable_norm).neg

/-- For every measure $\mu$ on $\mathbb{R}^2$, the gradient $\nabla v$ =
`AtkinsonHan.Chapter07.logLogNormGrad` is almost everywhere strongly measurable for $\mu$. -/
theorem aestronglyMeasurable_logLogNormGrad (μ : Measure (EuclideanSpace ℝ (Fin 2))) :
    AEStronglyMeasurable logLogNormGrad μ :=
  AEStronglyMeasurable.smul
    (((measurable_norm.pow_const 2).mul (Real.measurable_log.comp measurable_norm)).inv
      ).aestronglyMeasurable
    (innerSL ℝ).continuous.aestronglyMeasurable

/-- Let $0 < \beta < 1$. The function $v(x) = \log(\log(1/|x|))$ of Example 7.2.6 lies in
$L^2(B(0, \beta))$, because on this disc it is bounded by a multiple of $|x|^{-1/4}$. -/
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

/-- Let $\beta < 1$. The gradient $\nabla v$ = `AtkinsonHan.Chapter07.logLogNormGrad` lies in
$L^2(B(0, \beta))$. This is the finiteness of the integral in Example 7.2.6. -/
theorem memLp_logLogNormGrad {β : ℝ} (hβ1 : β < 1) :
    MemLp logLogNormGrad 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) β)) :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_logLogNormGrad _)).2
    (integrableOn_sq_norm_logLogNormGrad hβ1)

/-- Let $0 < \beta < 1$. The function $v(x) = \log(\log(1/|x|))$ is integrable on $B(0, \beta)$, and
hence locally integrable there. -/
theorem integrableOn_logLogNorm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntegrableOn logLogNorm (ball (0 : EuclideanSpace ℝ (Fin 2)) β) volume := by
  have := isFiniteMeasure_volume_restrict_ball (0 : EuclideanSpace ℝ (Fin 2)) β
  exact (memLp_logLogNorm hβ0 hβ1).integrable one_le_two

/-- Let $\beta < 1$. The gradient $\nabla v$ = `AtkinsonHan.Chapter07.logLogNormGrad` is integrable
on $B(0, \beta)$, and hence locally integrable there. -/
theorem integrableOn_logLogNormGrad {β : ℝ} (hβ1 : β < 1) :
    IntegrableOn logLogNormGrad (ball (0 : EuclideanSpace ℝ (Fin 2)) β) volume := by
  have := isFiniteMeasure_volume_restrict_ball (0 : EuclideanSpace ℝ (Fin 2)) β
  exact (memLp_logLogNormGrad hβ1).integrable one_le_two

/-- **Example 7.2.6** of [han2009theoretical], the weak gradient. Let $0 < \beta < 1$ and
$\Omega = B(0, \beta) \subseteq \mathbb{R}^2$. Let $\alpha$ be a multi-index with $|\alpha| = 1$
and $\alpha_i = 0$ for every $i \neq i_0$. Then on $\Omega$ the function
$v(x) = \log(\log(1/|x|))$ has the weak derivative $$\partial^\alpha v(x) = \frac{x_{i_0}}{|x|^2
\log |x|},$$ the value of $\nabla v(x)$ at $e_{i_0}$.

The book passes over this step: the classical gradient on $\Omega \setminus \{0\}$ is the weak
gradient on all of $\Omega$, the origin included. The proof is the backbone lemma
`hasWeakIteratedLineDerivOn_of_hasFDerivAt_compl_singleton`. Its smallness hypothesis
$\int_{B(0,\delta)} |v| = o(\delta)$ holds because $|v| \le C |x|^{-1/4}$ and $-1/4 > 1 - 2$. -/
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

/-- Let $\beta > 0$. The function $v(x) = \log(\log(1/|x|))$ is unbounded above near the origin: for
every constant $C$ there is an $x$ in the disc $B(0, \beta)$ of $\mathbb{R}^2$ with $v(x) > C$. -/
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

/-- **Example 7.2.6** of [han2009theoretical]. Let $0 < \beta < 1$, let
$\Omega = B(0, \beta) \subseteq \mathbb{R}^2$ and let $v(x) = \log(\log(1/|x|))$. Then

1. at every $x \in \Omega$ with $x \neq 0$, the classical derivative of $v$ is the functional
   $\nabla v(x)$ = `AtkinsonHan.Chapter07.logLogNormGrad x`;
2. $\int_\Omega |\nabla v|^2 \, dx = -2\pi/\log \beta < \infty$;
3. $v \in L^2(\Omega)$;
4. $v \in H^1(\Omega) = W^{1,2}(\Omega)$ in the sense of Definition 7.2.2;
5. $v$ is unbounded above on $\Omega$.

So a function of $H^1$ of a plane domain need not be continuous.

The first clause makes sure that the second is about the classical gradient. The step that the
book leaves implicit, that the classical gradient on $\Omega \setminus \{0\}$ is the weak
gradient on all of $\Omega$, is `AtkinsonHan.Chapter07.hasWeakIteratedLineDerivOn_logLogNorm`.
Membership of $H^1(\Omega)$ is in the book's reading,
`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`. -/
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

/-!
### Piecewise Sobolev functions on a triangulated polygon

The book states Examples 7.2.7 and 7.2.8 on a bounded Lipschitz domain partitioned into Lipschitz
sub-domains. Here they are stated on a plane domain $\Omega$ with a triangulation
`𝒯 : Triangulation Ω` from `Numlib.Geometry.Triangulation`. The sub-domains are the open triangles
`Triangulation.Kopens`, and the interfaces are the edges. The integration by parts on each
sub-domain, which the book defers to Section 7.4, is Green's formula on a triangle from
`Numlib.Analysis.Sobolev.Boundary.PolygonTrace`. Lipschitz domains in general are out of scope.
-/

section Piecewise

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Example 7.2.7** of [han2009theoretical], the case $k = 0$. Let $\Omega \subseteq \mathbb{R}^2$
be open with a triangulation $\mathcal{T}$, and let $p \in [1, \infty]$. Let $v$ be continuous
on $\bar\Omega$, with $v|_K \in W^{1,p}(K)$ for every open element $K$ of $\mathcal{T}$. Then
$v \in W^{1,p}(\Omega)$.

This is the case to which the book reduces the example. The book's argument integrates by parts
on each element against a test function $\varphi \in C_0^\infty(\Omega)$; the boundary terms
cancel in pairs on the interior edges and vanish on $\partial\Omega$. It is the backbone's
`Triangulation.memSobolevMultiIndex_of_continuousOn_of_forall`. No hypothesis beyond the axioms
of `Triangulation` is needed, because a function that is continuous across a slit does not see
it. The book's Lipschitz domain with Lipschitz sub-domains is replaced by a triangulated plane
domain, and Sobolev membership is in the book's reading,
`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`. -/
theorem example_7_2_7_continuous {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {v : 𝔼₂ → ℝ} (hv : ContinuousOn v (closure (Ω : Set 𝔼₂)))
    (hT : ∀ T : 𝒯.elems, definition_7_2_2_multiIndex 1 p (𝒯.Kopens T) v) :
    definition_7_2_2_multiIndex 1 p Ω v :=
  𝒯.memSobolevMultiIndex_of_continuousOn_of_forall hv hT

/-- **Example 7.2.7** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^2$ be open with a
triangulation $\mathcal{T}$, let $k \ge 0$ be an integer and let $p \in [1, \infty]$. Let $U$ be
an open set that contains $\bar\Omega$, and let $v$ be $C^k$ on $U$, with
$v|_K \in W^{k+1,p}(K)$ for every open element $K$ of $\mathcal{T}$. Then
$v \in W^{k+1,p}(\Omega)$.

**Reading.** The book's hypothesis $v \in C^k(\bar\Omega)$ is read as `ContDiffOn ℝ k v U` on an
open set $U \supseteq \bar\Omega$: $v$ is $C^k$ on a neighbourhood of the closure. Then the
partial derivatives of $v$ up to order $k$ are again of this class, and the book's reduction to
$k = 0$ is an induction.

The induction uses `memSobolevMultiIndex_succ_iff`: $v \in W^{k+2,p}(\Omega)$ if and only if
$v \in W^{k+1,p}(\Omega)$ and each $\partial_i v \in W^{k+1,p}(\Omega)$. Here the classical
$\partial_i v$ is the weak derivative on $\Omega$, and on each element it is the $L^p$ weak
derivative that $v|_K \in W^{k+2,p}(K)$ provides. The case $k = 0$ is
`AtkinsonHan.Chapter07.example_7_2_7_continuous`, which needs only $v \in C(\bar\Omega)$. As
there, the book's Lipschitz domain with Lipschitz sub-domains is replaced by a triangulated
plane domain whose sub-domains are the open triangles. -/
theorem example_7_2_7 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {U : Set 𝔼₂} (hU : IsOpen U) (hΩU : closure (Ω : Set 𝔼₂) ⊆ U) {v : 𝔼₂ → ℝ}
    (hv : ContDiffOn ℝ k v U)
    (hT : ∀ T : 𝒯.elems, definition_7_2_2_multiIndex (k + 1) p (𝒯.Kopens T) v) :
    definition_7_2_2_multiIndex (k + 1) p Ω v := by
  induction k generalizing v with
  | zero =>
    exact 𝒯.memSobolevMultiIndex_of_continuousOn_of_forall (hv.continuousOn.mono hΩU) hT
  | succ k ih =>
    refine memSobolevMultiIndex_succ_iff.2
      ⟨ih (hv.of_le (by exact_mod_cast Nat.le_succ k))
        (fun T ↦ (hT T).mono_order (Nat.le_succ _)), fun i ↦ ?_⟩
    have hv1 : ContDiffOn ℝ 1 v Ω := (hv.of_le (by exact_mod_cast Nat.succ_pos k)).mono
      (subset_closure.trans hΩU)
    -- the classical `∂ᵢ v` is the weak one on `Ω`
    have hw : HasWeakIteratedLineDerivOn ![stdBasis 2 i] v
        (fun x ↦ iteratedFDeriv ℝ 1 v x ![stdBasis 2 i]) Ω volume :=
      (hv1.hasWeakIteratedFDerivOn (m := 1) le_rfl).lineDeriv _
    refine ⟨_, hw, ih ?_ fun T ↦ ?_⟩
    · -- `∂ᵢ v ∈ C^k(U)`
      have h1 : ContDiffOn ℝ k (fun x ↦ fderiv ℝ v x (stdBasis 2 i)) U :=
        (hv.fderiv_of_isOpen hU (by exact_mod_cast le_rfl)).clm_apply contDiffOn_const
      refine h1.congr fun x _ ↦ ?_
      simp [iteratedFDeriv_one_apply]
    · -- on each element, `∂ᵢ v` is the `W^{k+1,p}(K)` weak derivative that `v ∈ W^{k+2,p}(K)` has
      obtain ⟨g, hg, hgk⟩ := (memSobolevMultiIndex_succ_iff.1 (hT T)).2 i
      refine hgk.congr_ae ?_
      have hw' : HasWeakIteratedLineDerivOn ![stdBasis 2 i] v
          (fun x ↦ iteratedFDeriv ℝ 1 v x ![stdBasis 2 i]) (𝒯.Kopens T) volume :=
        ((hv1.mono (𝒯.Kopens_le T)).hasWeakIteratedFDerivOn (m := 1) le_rfl).lineDeriv _
      exact (ae_restrict_iff' (𝒯.Kopens T).isOpen.measurableSet).2 (hg.ae_eq hw')

/-- **Example 7.2.8** of [han2009theoretical], on a triangulated plane domain without slits. Let
$\Omega \subseteq \mathbb{R}^2$ be open with a triangulation $\mathcal{T}$ such that the
relative interior of every interior edge lies in $\Omega$, and let $1 \le p < \infty$. Let
$v \in W^{1,p}(\Omega)$, and for each element $T$ let $w_T$ be a function that is continuous on
the closed element and agrees with $v$ almost everywhere on the open element. If the edge $a$ of
$T$ and the edge $a'$ of another element $T'$ are the same segment, then $w_T = w_{T'}$ on this
closed segment.

The functions $w_T$ are the book's hypothesis "$v \in C(\bar\Omega_n)$ for each $n$". The
no-slit hypothesis is `Triangulation.InteriorEdgesSubset`, and a pair of equal edges is
`Triangulation.IsPartner T a T' a'`. The no-slit hypothesis is what the book's Lipschitz
hypothesis provides here: across a slit, the one-sided limits of a $W^{1,p}$ function are
unrelated. The book's argument, that a nonzero interface integral $\int_\gamma
(v|_{\Omega_{n_1}} - v|_{\Omega_{n_2}}) \varphi \nu_i \, ds$ would contradict the definition of
the weak derivative, is the backbone's `Triangulation.traceL_partner_ae_eq`, in the form
`Triangulation.eqOn_partner_of_memSobolev_of_continuousOn`. The book concludes that
$v \in C(\bar\Omega)$, a single continuous function on the closure. The agreement on the edges
gives continuity on $\bar\Omega$ minus the vertices. The step to the vertices needs in addition
that the elements around each vertex are connected through shared edges. This fails at a pinch
vertex, where two elements meet only at a point, which the axioms of `Triangulation` allow and a
Lipschitz boundary does not; this step is not formalized. The book's version for $C^k$ is the
case $k = 0$ applied to the derivatives $\partial^\beta v$ with $|\beta| \le k$, as in Example
7.2.7. -/
theorem example_7_2_8 {Ω : Opens 𝔼₂} {𝒯 : Triangulation Ω} (hI : 𝒯.InteriorEdgesSubset)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {v : 𝔼₂ → ℝ}
    (hv : definition_7_2_2_multiIndex 1 p Ω v) {w : 𝒯.elems → 𝔼₂ → ℝ}
    (hwc : ∀ T, ContinuousOn (w T) (𝒯.closedK T))
    (hw : ∀ T, v =ᵐ[volume.restrict (𝒯.K T)] w T) {T T' : 𝒯.elems} {a a' : Fin 3}
    (h : 𝒯.IsPartner T a T' a') : EqOn (w T) (w T') (segment ℝ (T.1 a) (T.1 (a + 1))) := by
  obtain ⟨u, hu⟩ := (definition_7_2_2_multiIndex_iff_exists 1 p Ω v).1 hv
  refine 𝒯.eqOn_partner_of_memSobolev_of_continuousOn hI hp u hwc (fun T ↦ ?_) h
  exact (hu.filter_mono (ae_mono (Measure.restrict_mono (𝒯.K_subset T) le_rfl))).trans (hw T)

end Piecewise

/-- **Definition 7.2.9** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open, let
$k \ge 0$ be an integer and let $p \in [1, \infty]$. The space **$W_0^{k,p}(\Omega)$** is the
closure of $C_0^\infty(\Omega)$ in $W^{k,p}(\Omega)$. When $p = 2$ one writes
$H_0^k(\Omega) \equiv W_0^{k,2}(\Omega)$.

The space is `SobolevZero ℝ k p Ω volume`. It is the closure, in the Banach space of Theorem
7.2.3, of the submodule of the elements whose function agrees almost everywhere with a test
function on $\Omega$. Every test function gives such an element, by
`TestFunction.exists_mem_testFunctions`. The closure is taken in the bundled reading
`Sobolev ℝ k p Ω volume` and not in the book's reading. The two norms are equivalent, so
mathematically this is the same subspace, but that equivalence is not formalized and the two
closures are not compared here. The book's description of the space, as the functions whose
derivatives of order at most $k - 1$ vanish on $\partial\Omega$, is made precise by the trace
theorems of Section 7.3 and is not part of this definition. -/
noncomputable def definition_7_2_9 (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (Sobolev ℝ k p Ω volume) :=
  SobolevZero ℝ k p Ω volume

/-!
### Sobolev spaces of real order

This part formalizes Section 7.2.2 of the book. There $p \in [1, \infty)$, and the order is
$s = k + \sigma$ with $k \ge 0$ an integer and $\sigma \in (0, 1)$. The declarations below take $k$,
$\sigma$ and $p$ as parameters and place no constraint on $\sigma$: the constraint makes them the
book's spaces, but they are well formed without it. The backbone module
`Numlib.Analysis.Sobolev.Slobodeckij` gives the normed space $W^{s,p}(\Omega)$, which is
`SobolevSlobodeckij`, and the closure of the test functions in it, which is
`SobolevSlobodeckijZero`. This part states the book's definitions over them: the set of Definition
7.2.10 as a predicate on functions, the identification of the elements of the type with these
functions, and the norm of the definition.
-/

variable (d) in
/-- **Definition 7.2.10** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open, let
$k \ge 0$ be an integer, let $\sigma$ be real and let $p \in [0, \infty]$; the book takes
$\sigma \in (0, 1)$ and $p \in [1, \infty)$, and writes $s = k + \sigma$. The **Sobolev space
$W^{s,p}(\Omega)$** is the set of $v \in W^{k,p}(\Omega)$ such that, for every multi-index
$\alpha$ with $|\alpha| = k$, $$\frac{\partial^\alpha v(x) - \partial^\alpha v(y)}{|x -
y|^{\sigma + d/p}} \in L^p(\Omega \times \Omega).$$ This is the finiteness of the
Sobolev–Slobodeckij seminorm of the derivatives of order $k$.

The space $W^{k,p}(\Omega)$ is in the book's reading,
`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`, and the measure on $\Omega \times \Omega$
is `prodRestrict Ω volume`. The book writes the numerator in absolute value, which does not
matter: membership of $L^p$ depends on a function only through its absolute value. The weak
derivative $\partial^\alpha v$ is determined only almost everywhere on $\Omega$, so the
condition is imposed on every function $w$ that is a weak $\alpha$-th derivative of $v$; by
`AtkinsonHan.Chapter07.definition_7_2_10_of_exists` this is the same as imposing it on one. The
norm of the definition lives on the type `SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume`. Its
elements are these functions by `AtkinsonHan.Chapter07.definition_7_2_10_iff_exists`, and its
norm is the displayed norm by `AtkinsonHan.Chapter07.definition_7_2_10_norm`. -/
def definition_7_2_10 (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  definition_7_2_2_multiIndex k p Ω v ∧
    ∀ α : Fin d → ℕ, ∑ i, α i = k → ∀ w : EuclideanSpace ℝ (Fin d) → ℝ,
      definition_7_1_3_multiIndex α v w Ω →
        MemLp (fun z ↦ (w z.1 - w z.2) / ‖z.1 - z.2‖ ^ (σ + (d : ℝ) / p.toReal)) p
          (prodRestrict Ω volume)

/-- **Definition 7.2.10** of [han2009theoretical], the difference quotient. Let $\sigma$ be real,
let $p \in [0, \infty]$ and let $w$ be a real function on $\mathbb{R}^d$. The backbone's
quotient `slobodeckijQuotient σ p w` is the function $$(x, y) \mapsto \frac{w(x) - w(y)}{|x -
y|^{\sigma + d/p}}$$ on $\mathbb{R}^d \times \mathbb{R}^d$.

The backbone writes the exponent with the dimension of the space, which is $d$ for
$\mathbb{R}^d$, and writes the quotient as a scalar multiplication, which is a division for a
real function $w$. -/
theorem definition_7_2_10_quotient (σ : ℝ) (p : ℝ≥0∞) (w : EuclideanSpace ℝ (Fin d) → ℝ) :
    slobodeckijQuotient σ p w =
      fun z ↦ (w z.1 - w z.2) / ‖z.1 - z.2‖ ^ (σ + (d : ℝ) / p.toReal) := by
  funext z
  simp [slobodeckijQuotient, div_eq_inv_mul]

/-- **Definition 7.2.10** of [han2009theoretical], one weak derivative is enough. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer, let $\sigma$ be real, let
$p \in [0, \infty]$, and let $v \in W^{k,p}(\Omega)$ in the book's reading. Suppose that for
every multi-index $\alpha$ with $|\alpha| = k$ there is a weak $\alpha$-th derivative $w$ of $v$
on $\Omega$ with $$\frac{w(x) - w(y)}{|x - y|^{\sigma + d/p}} \in L^p(\Omega \times \Omega).$$
Then $v \in W^{s,p}(\Omega)$, with $s = k + \sigma$.

Two weak $\alpha$-th derivatives agree almost everywhere on $\Omega$, so their difference
quotients agree almost everywhere on $\Omega \times \Omega$, by `slobodeckijQuotient_congr_ae`. -/
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

/-- **Definition 7.2.10** of [han2009theoretical], on the normed space. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer, let $\sigma$ be real and
let $p \in [1, \infty]$. Then $v \in W^{s,p}(\Omega)$, with $s = k + \sigma$, if and only if
there is an element $U$ of the normed space `SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume`
whose function agrees with $v$ almost everywhere on $\Omega$.

The element $U$ is then unique, by `SobolevSlobodeckij.ext_of_fn_ae_eq`. The normed space
carries the norm of the definition, by `AtkinsonHan.Chapter07.definition_7_2_10_norm`. -/
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

/-- **Definition 7.2.10** of [han2009theoretical], the norm. Let $\Omega \subseteq \mathbb{R}^d$ be
open, let $k \ge 0$ be an integer, let $\sigma$ be real and let $1 \le p < \infty$. Let $U$ be
an element of the normed space `SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume`, with function
$v$. Then $$\|U\|_{s,p,\Omega} = \Big[\|v\|_{k,p,\Omega}^p + \sum_{|\alpha| = k} \int_{\Omega
\times \Omega} \frac{|\partial^\alpha v(x) - \partial^\alpha v(y)|^p}{|x - y|^{\sigma p + d}} \,
dx \, dy\Big]^{1/p}.$$

The norm $\|v\|_{k,p,\Omega}$ is the norm of `SobolevSlobodeckij.toSobolevMultiIndex U`, which
is the norm of Definition 7.2.2 in the book's reading by
`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_norm`. The derivative $\partial^\alpha v$ is
`SobolevMultiIndex.weakDeriv`, and the sum is over `MultiIndexEq (Fin d) k`. -/
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
/-- **Definition 7.2.11** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open, let
$k \ge 0$ be an integer, let $\sigma$ be real, let $p \in [1, \infty]$ and let $s = k + \sigma$.
The space **$W_0^{s,p}(\Omega)$** is the closure of $C_0^\infty(\Omega)$ in $W^{s,p}(\Omega)$.
When $p = 2$ one writes $H_0^s(\Omega) \equiv W_0^{s,2}(\Omega)$.

The space is `SobolevSlobodeckijZero ℝ (stdBasis d) k σ p Ω volume`, the closure in the normed
space of Definition 7.2.10 of the submodule of the elements whose function agrees almost
everywhere with a test function on $\Omega$. The case of integer order corresponds to
`AtkinsonHan.Chapter07.definition_7_2_9`, where the closure is taken in $W^{k,p}(\Omega)$. The
book keeps the two definitions apart because $C_0^\infty(\Omega)$ need not be dense in
$W^{s,p}(\Omega)$. That every test function lies in $W^{s,p}(\Omega)$ is not proved; see the
implementation notes of `Numlib.Analysis.Sobolev.Slobodeckij`. -/
noncomputable def definition_7_2_11 (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) :
    Submodule ℝ (SobolevSlobodeckij ℝ (stdBasis d) k σ p Ω volume) :=
  SobolevSlobodeckijZero ℝ (stdBasis d) k σ p Ω volume

variable (d) in
/-- **Definition 7.2.12** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open, let
$k \ge 0$ be an integer, let $\sigma$ be real, let $p \in [1, \infty]$ with conjugate exponent
$p'$, and let $s = k + \sigma$; the book takes $p < \infty$. The space **$W^{-s,p'}(\Omega)$**
is the dual space of $W_0^{s,p}(\Omega)$: the continuous linear functionals $\ell$ on
$W_0^{s,p}(\Omega)$, with the norm $$\|\ell\| = \sup_{0 \neq v \in W_0^{s,p}(\Omega)}
\frac{\ell(v)}{\|v\|}.$$ When $p = 2$ one writes $H^{-s}(\Omega) \equiv W^{-s,2}(\Omega)$.

The dual space is Mathlib's `StrongDual`, the continuous linear functionals with the operator
norm. The exponent $p'$ appears only in the name of the space: the space depends on $p$, and
$p'$ is `ENNReal.conjExponent p`. The case of integer order is
`AtkinsonHan.Chapter07.definition_7_2_12_integerOrder`, and the space $H^{-1}(\Omega)$ that the
book singles out is `AtkinsonHan.Chapter07.definition_7_2_12_hMinusOne`. The book's two further
remarks are not formalized: that $L^2(\Omega)$ embeds in $H^{-1}(\Omega)$ by
$\langle f, v \rangle = \int_\Omega f v$, and that every $\ell \in H^{-1}(\Omega)$ is
$\ell_0 - \sum_i \partial_i \ell_i$ for functions $\ell_0, \dots, \ell_d \in L^2(\Omega)$. The
book states the second without proof. -/
noncomputable abbrev definition_7_2_12 (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Type _ :=
  StrongDual ℝ (definition_7_2_11 d k σ p Ω)

variable (d) in
/-- **Definition 7.2.12** of [han2009theoretical], the case of integer order. Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let $p \in [1, \infty]$
with conjugate exponent $p'$. The space $W^{-k,p'}(\Omega)$ is the dual space of the space
$W_0^{k,p}(\Omega)$ of Definition 7.2.9. -/
noncomputable abbrev definition_7_2_12_integerOrder (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Type _ :=
  StrongDual ℝ (definition_7_2_9 k p Ω)

variable (d) in
/-- **Definition 7.2.12** of [han2009theoretical], the space $H^{-1}(\Omega)$. Let
$\Omega \subseteq \mathbb{R}^d$ be open. The space $H^{-1}(\Omega)$ is the dual space of
$H_0^1(\Omega) = W_0^{1,2}(\Omega)$, the case $s = 1$, $p = 2$ of the definition. The book
singles out this case, and later chapters use it.

The space $H_0^1(\Omega)$ here is that of Definition 7.2.9, through
`AtkinsonHan.Chapter07.definition_7_2_12_integerOrder`. -/
noncomputable abbrev definition_7_2_12_hMinusOne (Ω : Opens (EuclideanSpace ℝ (Fin d))) : Type _ :=
  definition_7_2_12_integerOrder d 1 2 Ω


/-!
### Sobolev spaces over boundaries

This part formalizes Section 7.2.3 of the book, Definition 7.2.13, on a bounded $C^1$ domain
$\Omega \subseteq \mathbb{R}^{d+1}$. The patch system is a graph atlas `a : GraphAtlas Ω` from
`Numlib.Analysis.Sobolev.Boundary.GraphMeasure`: finitely many balls $B(x_i, r_i)$ that cover
$\partial\Omega$, each with a rigid motion $T_i$ and a $C^1$ function $g_i$ such that
$\Omega \cap B(x_i, r_i)$ is the region above the graph of $g_i$ in the coordinates $T_i$. This is
the finite cover of `AtkinsonHan.Chapter07.definition_7_2_1_finite_cover`. The parameter domains are
$D_i$ = `a.graphDomain i` $\subseteq \mathbb{R}^d$, and the parametrizations are $\Phi_i$ =
`EuclideanSpace.graphParam (a.T i) (a.g i)`, $x' \mapsto T_i^{-1}(x', g_i(x'))$, which are the
book's maps $g_i : D_i \to \partial\Omega$. The surface measure on $\partial\Omega$ is
`IsContDiffDomain.boundaryMeasure`, which on every chart is the pushforward of
$\sqrt{1 + |\nabla g_i|^2} \, dx'$, and $L^p(\partial\Omega)$ is `Lp ℝ p` for this measure. The
space is defined relative to an atlas (`AtkinsonHan.Chapter07.definition_7_2_13_atlas`) and then for
the chosen atlas `IsContDiffDomain.graphAtlas` (`AtkinsonHan.Chapter07.definition_7_2_13`). So its
independence of the patch system, which the book leaves implicit, is a statement; it is not proved,
and `AtkinsonHan.Chapter07.definition_7_2_13` says what it would need. The book's $C^{k,\alpha}$
patches are $C^1$ here, the case $k = 0$, $\alpha = 1$ of the book's range, since a $C^1$ function
is Lipschitz; so the book's range of orders is $0 \le s \le 1$. As for Definition 7.2.10, the order
$s = k + \sigma$ is a parameter with no constraint.
-/

section Boundary

/-- **Definition 7.2.13** of [han2009theoretical], the parameter domains. Let $a$ be a graph atlas
of $\Omega \subseteq \mathbb{R}^{d+1}$ and let $i$ be a chart of $a$. The parameter domain
$D_i \subseteq \mathbb{R}^d$ is the open set of the points $x'$ whose image $\Phi_i(x')$ under
the parametrization of the chart lies in the chart ball $B(x_i, r_i)$. -/
noncomputable def definition_7_2_13_domain {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (a : GraphAtlas Ω) (i : Fin a.k) : Opens (EuclideanSpace ℝ (Fin d)) :=
  ⟨a.graphDomain i, EuclideanSpace.isOpen_graphDomain (a.contDiff_g i).continuous _ _⟩

/-- **Definition 7.2.13** of [han2009theoretical], for a given patch system. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with a graph atlas $a$: in the
coordinates $T_i$, $\partial\Omega \cap B(x_i, r_i) = \{x_{d+1} = g_i(x')\}$ for
$i = 1, \dots, I$, with parameter domains $D_i \subseteq \mathbb{R}^d$. Let $k \ge 0$ be an
integer, let $\sigma$ be real, let $p \in [1, \infty]$ and let $s = k + \sigma$. The **Sobolev
space over the boundary** is $$W^{s,p}(\partial\Omega) = \{v \in L^p(\partial\Omega) : v \circ
g_i \in W^{s,p}(D_i), \ i = 1, \dots, I\},$$ a subspace of $L^p(\partial\Omega)$ for the surface
measure.

**Reading.** The printed definition asks $v \in L^2(\partial\Omega)$ for every $p$. This is read
as $v \in L^p(\partial\Omega)$, the space in which $W^{s,p}(\partial\Omega)$ lies and the space
that the norm $\max_i \|v \circ g_i\|_{W^{s,p}(D_i)}$ controls.

The surface measure is `hΩ.boundaryMeasure hb`. The composition $v \circ g_i$ is
$v \circ \Phi_i$, $x' \mapsto v(T_i^{-1}(x', g_i(x')))$, taken on the representative `⇑v` of the
class $v$; the choice of representative does not matter, by
`IsContDiffDomain.ae_eq_comp_graphParam`. The space $W^{s,p}(D_i)$ is Definition 7.2.10 on the
open bounded set $D_i$. The set is a submodule because each $W^{s,p}(D_i)$ is closed under the
operations (`AtkinsonHan.Chapter07.definition_7_2_10_iff_exists` and the module structure of
`SobolevSlobodeckij`). The norm of the definition is
`AtkinsonHan.Chapter07.definition_7_2_13_norm`. The book's $C^{k,\alpha}$ patches are $C^1$
here. -/
noncomputable def definition_7_2_13_atlas {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (a : GraphAtlas (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (k : ℕ) (σ : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : Submodule ℝ (Lp ℝ p (hΩ.boundaryMeasure hb)) where
  carrier := {v | ∀ i, definition_7_2_10 d k σ p (definition_7_2_13_domain a i)
    (v ∘ EuclideanSpace.graphParam (a.T i) (a.g i))}
  zero_mem' i := by
    rw [definition_7_2_10_iff_exists]
    refine ⟨0, SobolevSlobodeckij.fn_zero.trans ?_⟩
    exact (hΩ.ae_eq_comp_graphParam hb a i (Lp.coeFn_zero ℝ p _)).symm
  add_mem' {v w} hv hw i := by
    obtain ⟨U, hU⟩ := (definition_7_2_10_iff_exists k σ p _ _).1 (hv i)
    obtain ⟨V, hV⟩ := (definition_7_2_10_iff_exists k σ p _ _).1 (hw i)
    refine (definition_7_2_10_iff_exists k σ p _ _).2 ⟨U + V, ?_⟩
    refine (SobolevSlobodeckij.fn_add U V).trans ((hU.add hV).trans ?_)
    exact (hΩ.ae_eq_comp_graphParam hb a i (Lp.coeFn_add v w)).symm
  smul_mem' c {v} hv i := by
    obtain ⟨U, hU⟩ := (definition_7_2_10_iff_exists k σ p _ _).1 (hv i)
    refine (definition_7_2_10_iff_exists k σ p _ _).2 ⟨c • U, ?_⟩
    refine (SobolevSlobodeckij.fn_smul c U).trans ((hU.const_smul c).trans ?_)
    exact (hΩ.ae_eq_comp_graphParam hb a i (Lp.coeFn_smul c v)).symm

/-- **Definition 7.2.13** of [han2009theoretical], unfolded. Let $\Omega \subseteq \mathbb{R}^{d+1}$
be a bounded $C^1$ domain with a graph atlas $a$, let $k \ge 0$ be an integer, let $\sigma$ be
real, let $p \in [1, \infty]$ and let $v \in L^p(\partial\Omega)$. Then
$v \in W^{s,p}(\partial\Omega)$ for the atlas $a$ if and only if, for every chart $i$, the
pull-back $v \circ \Phi_i$ lies in $W^{s,p}(D_i)$ in the sense of Definition 7.2.10. -/
theorem mem_definition_7_2_13_atlas_iff {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (a : GraphAtlas (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (k : ℕ) (σ : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (v : Lp ℝ p (hΩ.boundaryMeasure hb)) :
    v ∈ definition_7_2_13_atlas hΩ hb a k σ p ↔ ∀ i, definition_7_2_10 d k σ p
      (definition_7_2_13_domain a i) (v ∘ EuclideanSpace.graphParam (a.T i) (a.g i)) :=
  Iff.rfl

/-- **Definition 7.2.13** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded $C^1$ domain, let $k \ge 0$ be an integer, let $\sigma$ be real, let $p \in [1, \infty]$
and let $s = k + \sigma$. The **Sobolev space $W^{s,p}(\partial\Omega)$** over the boundary is
the space of `AtkinsonHan.Chapter07.definition_7_2_13_atlas` for the chosen graph atlas
`hΩ.graphAtlas hb` of $\Omega$. When $p = 2$ one writes $H^s(\partial\Omega) \equiv
W^{s,2}(\partial\Omega)$, which is `AtkinsonHan.Chapter07.definition_7_2_13_hs`.

The book states without proof that the space does not depend on the patch system and that two
patch systems give equivalent norms. This is not proved. With the definitions here it is a
statement: for two graph atlases $a$ and $a'$, the two spaces
`definition_7_2_13_atlas hΩ hb a k σ p` and `definition_7_2_13_atlas hΩ hb a' k σ p` are equal,
together with a constant $C > 0$ that bounds the norm
`AtkinsonHan.Chapter07.definition_7_2_13_norm` of each atlas by $C$ times the norm of the other.
Both spaces are submodules of the same $L^p(\partial\Omega)$, because the surface measure does
not depend on the atlas (`GraphAtlas.measure_eq`), and the norms can be computed from
representatives on the patches by `AtkinsonHan.Chapter07.definition_7_2_13_norm_eq`. At $s = 0$
the space is $L^p(\partial\Omega)$ for every atlas and nothing is needed
(`IsContDiffDomain.boundaryMeasure_restrict_ball`). For $0 < s \le 1$ the statement needs the
invariance of the Sobolev–Slobodeckij seminorm under the $C^1$ transition maps
`EuclideanSpace.graphTransition`. This is a bi-Lipschitz change of variables in the double
integral $\iint |v(x) - v(y)|^p / |x - y|^{d + sp} \, dx \, dy$ over the parameter domains in
$\mathbb{R}^d$, localized to the overlaps of the parameter domains of the two atlases, and then
summed over a finite partition of each $D_i$ by these overlaps. The Jacobian bounds that it
would use are `EuclideanSpace.graphDensity_graphTransition`. The module
`Numlib.Analysis.Sobolev.Slobodeckij` has the spaces and their norms, but no change of
variables. The same obstruction keeps out the fractional clauses of Section 7.3, the range
clause of Theorem 7.3.10 and Theorem 7.3.11 as printed; the module doc comment of
`NumlibSurface.AtkinsonHan.Chapter07.Section03` discusses it for all three. Nothing in the
library uses $W^{s,p}(\partial\Omega)$ for a non-integer $s$: the space $H^{1/2}(\Gamma)$ was
wanted only through those two clauses of Section 7.3. -/
noncomputable def definition_7_2_13 {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (k : ℕ) (σ : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (Lp ℝ p (hΩ.boundaryMeasure hb)) :=
  definition_7_2_13_atlas hΩ hb (hΩ.graphAtlas hb) k σ p

/-- **Definition 7.2.13** of [han2009theoretical], the case $p = 2$. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain, let $k \ge 0$ be an integer, let
$\sigma$ be real and let $s = k + \sigma$. The space $H^s(\partial\Omega) \equiv
W^{s,2}(\partial\Omega)$ is `AtkinsonHan.Chapter07.definition_7_2_13` at $p = 2$. The book's
$H^{1/2}(\partial\Omega)$ is the case $k = 0$, $\sigma = 1/2$. -/
noncomputable abbrev definition_7_2_13_hs {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (k : ℕ) (σ : ℝ) :
    Submodule ℝ (Lp ℝ 2 (hΩ.boundaryMeasure hb)) :=
  definition_7_2_13 hΩ hb k σ 2

/-- **Definition 7.2.13** of [han2009theoretical], the norm. Let $\Omega \subseteq \mathbb{R}^{d+1}$
be a bounded $C^1$ domain with a graph atlas $a$, let $k \ge 0$ be an integer, let $\sigma$ be
real and let $p \in [1, \infty]$. For $v \in W^{s,p}(\partial\Omega)$ relative to $a$,
$$\|v\|_{W^{s,p}(\partial\Omega)} = \max_i \|v \circ g_i\|_{W^{s,p}(D_i)},$$ where
$\|v \circ g_i\|_{W^{s,p}(D_i)}$ is the norm of the element of the normed space $W^{s,p}(D_i)$,
the type `SobolevSlobodeckij` on $D_i$, whose function is $v \circ \Phi_i$.

This element is unique by `SobolevSlobodeckij.ext_of_fn_ae_eq`, and
`AtkinsonHan.Chapter07.definition_7_2_13_norm_eq` computes the norm from any family of such
elements. The definition is a supremum over the charts. There are finitely many charts, so the
supremum is the book's maximum (`Finset.sup'_univ_eq_ciSup`). It is $0$ when the atlas has no
charts, which happens exactly when $\partial\Omega$ is empty. -/
noncomputable def definition_7_2_13_norm {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))}
    {hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))}
    {a : GraphAtlas (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))} {k : ℕ} {σ : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (v : definition_7_2_13_atlas hΩ hb a k σ p) : ℝ :=
  ⨆ i, ‖((definition_7_2_10_iff_exists k σ p _ _).1 (v.2 i)).choose‖

/-- **Definition 7.2.13** of [han2009theoretical], the norm from representatives. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with a graph atlas $a$, let
$k \ge 0$ be an integer, let $\sigma$ be real, let $p \in [1, \infty]$ and let
$v \in W^{s,p}(\partial\Omega)$ relative to $a$. Let $U_i \in W^{s,p}(D_i)$, for each chart $i$,
be elements whose functions agree almost everywhere on $D_i$ with the pull-backs
$v \circ \Phi_i$. Then $$\|v\|_{W^{s,p}(\partial\Omega)} = \sup_i \|U_i\|.$$
-/
theorem definition_7_2_13_norm_eq {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))}
    {hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))}
    {a : GraphAtlas (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))} {k : ℕ} {σ : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (v : definition_7_2_13_atlas hΩ hb a k σ p)
    (U : ∀ i, SobolevSlobodeckij ℝ (stdBasis d) k σ p (definition_7_2_13_domain a i) volume)
    (hU : ∀ i, SobolevSlobodeckij.fn (U i) =ᵐ[volume.restrict (a.graphDomain i)]
      (v : Lp ℝ p (hΩ.boundaryMeasure hb)) ∘ EuclideanSpace.graphParam (a.T i) (a.g i)) :
    definition_7_2_13_norm v = ⨆ i, ‖U i‖ := by
  unfold definition_7_2_13_norm
  refine iSup_congr fun i ↦ ?_
  congr 1
  exact SobolevSlobodeckij.ext_of_fn_ae_eq
    (((definition_7_2_10_iff_exists k σ p _ _).1 (v.2 i)).choose_spec.trans (hU i).symm)

end Boundary

end AtkinsonHan.Chapter07
