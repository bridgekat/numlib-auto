/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Atkinson and Han, Section 1.1: Linear spaces

This module formalizes §1.1 of [han2009theoretical], the review of linear spaces over the scalars
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The section defines linear spaces and subspaces, linear
independence, the span of finitely many vectors, bases and dimension, linear maps, isomorphisms and
Cartesian products. It illustrates them on $\mathbb{R}^d$, on spaces of continuous functions and on
spaces of polynomials. Its one theorem says that all bases of a linear space have the same number of
elements.

Mathlib has all of this material: the definitions are `Module`, `Submodule`, `LinearIndependent`,
`Submodule.span`, `Module.Basis` with `FiniteDimensional`, `LinearMap`, `LinearEquiv` and `Prod`.
Each definition is restated here under the number of the book, and each proof is a short reduction
to Mathlib.

## Main definitions

* Definition 1.1.3, `AtkinsonHan.Chapter01.definition_1_1_3`: a subspace is a subset closed under
  addition and scalar multiplication.
* Definition 1.1.5, `AtkinsonHan.Chapter01.definition_1_1_5`: linear independence of
  $v_1, \dots, v_n$.
* Definition 1.1.8, `AtkinsonHan.Chapter01.definition_1_1_8`: the span of $v_1, \dots, v_n$, as the
  set of their linear combinations.
* Definition 1.1.9, `AtkinsonHan.Chapter01.definition_1_1_9`: a finite basis, that is, a maximal
  linearly independent family.
* Definition 1.1.13, `AtkinsonHan.Chapter01.definition_1_1_13`: a linear function is additive and
  homogeneous.
* Definition 1.1.14, `AtkinsonHan.Chapter01.definition_1_1_14`: two spaces are isomorphic if a
  linear bijection joins them.

## Main results

* Definition 1.1.1, `AtkinsonHan.Chapter01.definition_1_1_1`: a Mathlib module over an additive
  commutative group satisfies the eight rules of a linear space.
* Example 1.1.2, `AtkinsonHan.Chapter01.example_1_1_2`: the operations of $\mathbb{R}^d$, $C(D)$ and
  $C_p(2\pi)$ are the componentwise and pointwise ones, and $C^m$ is closed under them.
* Definition 1.1.3, `AtkinsonHan.Chapter01.definition_1_1_3_iff`: a nonempty subset is a subspace if
  and only if it is the carrier of a submodule.
* Example 1.1.4, `AtkinsonHan.Chapter01.example_1_1_4`: the plane $x_3 = 0$ in $\mathbb{R}^3$ is a
  subspace, and the plane $x_3 = 1$ is not.
* Definition 1.1.5, `AtkinsonHan.Chapter01.definition_1_1_5_iff`: Definition 1.1.5 is
  `LinearIndependent`.
* Example 1.1.6, `AtkinsonHan.Chapter01.example_1_1_6`: $d$ vectors in $\mathbb{R}^d$ are linearly
  independent if and only if the matrix with these columns has nonzero determinant.
* Example 1.1.7, `AtkinsonHan.Chapter01.example_1_1_7`: the monomials $1, x, \dots, x^n$ are
  linearly independent in $C[0, 1]$.
* Definition 1.1.8, `AtkinsonHan.Chapter01.definition_1_1_8_iff` and
  `AtkinsonHan.Chapter01.definition_1_1_8_isSubspace`: the span is `Submodule.span`, and it is a
  subspace.
* Definition 1.1.9, `AtkinsonHan.Chapter01.definition_1_1_9_iff` and
  `AtkinsonHan.Chapter01.definition_1_1_9_finiteDimensional_iff`: a basis is a `Module.Basis`, and a
  space with a finite basis is `FiniteDimensional`.
* Theorem 1.1.10, `AtkinsonHan.Chapter01.theorem_1_1_10`: every basis of a linear space has $\dim V$
  elements.
* Example 1.1.11, `AtkinsonHan.Chapter01.example_1_1_11`: the coordinate vectors form a basis of
  $\mathbb{R}^d$, and $\dim \mathbb{R}^d = d$.
* Example 1.1.12, `AtkinsonHan.Chapter01.example_1_1_12`: $\dim \mathbb{F}_n = n + 1$, and the
  subspace $\mathbb{F}_{n,0}$ of polynomials that vanish at $0$ and $1$ has dimension
  $\dim \mathbb{F}_n - 2$.
* Definition 1.1.13, `AtkinsonHan.Chapter01.definition_1_1_13_iff`: Definition 1.1.13 is
  `LinearMap`.
* Definition 1.1.14, `AtkinsonHan.Chapter01.definition_1_1_14_iff`: Definition 1.1.14 is the
  existence of a `LinearEquiv`.
* Example 1.1.15, `AtkinsonHan.Chapter01.example_1_1_15`: the polynomials of degree at most $k$ form
  a subspace of $C[0, 1]$, isomorphic to $\mathbb{R}^{k+1}$.
* Definition 1.1.16, `AtkinsonHan.Chapter01.definition_1_1_16`: the operations of the Cartesian
  product $U \times V$ are componentwise.
* Example 1.1.17, `AtkinsonHan.Chapter01.example_1_1_17`: $\mathbb{R}^2$ is isomorphic to
  $\mathbb{R} \times \mathbb{R}$, and $\mathbb{R}^d$ to the $d$-fold product of $\mathbb{R}$.

## Conventions

* The space $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`, and $\mathbb{F}_k$, the space of real
  polynomials of degree at most $k$, is `Polynomial.degreeLT ℝ (k + 1)`.
* The scalars of the general statements form any division ring `𝕜`. The book's
  $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ are instances.

## Implementation notes

* A definition that names a property of data (subspace, independence, span, basis, linear map,
  isomorphism) is a `def … : Prop` in the words of the book, or a `def … : Set V` for the span. A
  companion theorem with the suffix `_iff` identifies it with the Mathlib notion, and later chapters
  rewrite along it.
* A definition that names a structure carried by a type (here the linear space itself and the
  Cartesian product) is a theorem: in Lean the class is the structure, so the content of the book's
  definition is that the class satisfies the book's axioms.

## Deviations from the source

* **Definition 1.1.3** (reading). The book requires a subspace to be a linear space, which excludes
  the empty set. The definition states only the two closure conditions, and the correspondence with
  `Submodule` assumes that the set is nonempty. See `AtkinsonHan.Chapter01.definition_1_1_3_iff`.

## Not formalized

* **The exercises of §1.1.**
* **The basis of $\mathbb{F}_{n,0}$ in Example 1.1.12.** The book exhibits the basis
  $x(1 - x), \dots, x^{n-1}(1 - x)$; only the dimension count is stated.
-/

open scoped Real

namespace AtkinsonHan.Chapter01

section LinearSpace

variable {𝕜 U V W : Type*} [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V]
  [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

/-- **Definition 1.1.1** of [han2009theoretical]. A **linear space** (vector space) over the scalars
$\mathbb{K}$ is a set $V$ with an addition $(u, v) \mapsto u + v$ and a scalar multiplication
$(\alpha, v) \mapsto \alpha v$ that obey eight rules: $u + v = v + u$;
$(u + v) + w = u + (v + w)$; $0 + v = v$; each $v$ has some $w$ with $v + w = 0$; $1 v = v$;
$\alpha (\beta v) = (\alpha \beta) v$; $\alpha (u + v) = \alpha u + \alpha v$; and
$(\alpha + \beta) v = \alpha v + \beta v$. The theorem states that every module $V$ over a
division ring $\mathbb{K}$, with $V$ an additive commutative group, satisfies these eight rules.

In Lean a linear space is `Module 𝕜 V` over `AddCommGroup V`. The book takes
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. -/
theorem definition_1_1_1 (𝕜 V : Type*) [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] :
    (∀ u v : V, u + v = v + u) ∧
      (∀ u v w : V, u + v + w = u + (v + w)) ∧
      (∀ v : V, (0 : V) + v = v) ∧
      (∀ v : V, ∃ w : V, v + w = 0) ∧
      (∀ v : V, (1 : 𝕜) • v = v) ∧
      (∀ (α β : 𝕜) (v : V), α • β • v = (α * β) • v) ∧
      (∀ (α : 𝕜) (u v : V), α • (u + v) = α • u + α • v) ∧
      (∀ (α β : 𝕜) (v : V), (α + β) • v = α • v + β • v) :=
  ⟨add_comm, add_assoc, zero_add, fun v => ⟨-v, add_neg_cancel v⟩, one_smul 𝕜, smul_smul,
    smul_add, add_smul⟩

/-- **Example 1.1.2** of [han2009theoretical]. Let $d, m \in \mathbb{N}$ and
$D \subseteq \mathbb{R}^d$. The standard linear spaces have the componentwise and pointwise
operations: in $\mathbb{R}^d$, $(x + y)_i = x_i + y_i$ and $(\alpha x)_i = \alpha x_i$; in
$C(D)$ and in the space $C_p(2\pi)$ of continuous $2\pi$-periodic functions,
$(f + g)(x) = f(x) + g(x)$ and $(\alpha f)(x) = \alpha f(x)$. Moreover, if
$f, g : \mathbb{R}^d \to \mathbb{R}$ are $m$ times continuously differentiable, then so are
$f + g$ and $\alpha f$ for every $\alpha \in \mathbb{R}$.

The book also lists $\mathbb{R}$ and $\mathbb{C}$, which are modules over themselves by
instance. The function spaces are `C(D, ℝ)` and `C(AddCircle (2 * π), ℝ)`. The space
$C^m(\Omega)$ is represented by the predicate `ContDiff ℝ m`, for functions on the whole of
$\mathbb{R}^d$ rather than on an open set $\Omega$. -/
theorem example_1_1_2 {d : ℕ} (m : ℕ) (D : Set (EuclideanSpace ℝ (Fin d))) :
    (∀ (x y : EuclideanSpace ℝ (Fin d)) (α : ℝ) (i : Fin d),
        (x + y) i = x i + y i ∧ (α • x) i = α * x i) ∧
      (∀ (f g : C(D, ℝ)) (α : ℝ) (x : D), (f + g) x = f x + g x ∧ (α • f) x = α * f x) ∧
      (∀ (f g : C(AddCircle (2 * π), ℝ)) (α : ℝ) (x : AddCircle (2 * π)),
        (f + g) x = f x + g x ∧ (α • f) x = α * f x) ∧
      (∀ (f g : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ), ContDiff ℝ m f → ContDiff ℝ m g →
        ContDiff ℝ m (f + g) ∧ ContDiff ℝ m (α • f)) :=
  ⟨fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ α hf hg => ⟨hf.add hg, hf.const_smul α⟩⟩

/-- **Definition 1.1.3** of [han2009theoretical]. Let $V$ be a linear space over $\mathbb{K}$. A
subset $W \subseteq V$ is a **subspace** of $V$ if $u + v \in W$ and $\alpha v \in W$ for all
$u, v \in W$ and $\alpha \in \mathbb{K}$.

**Reading.** The book adds that a subspace is itself a linear space, so a subspace is nonempty.
The predicate states only the two closure conditions, and it holds for the empty set. The
correspondence with `Submodule` in `AtkinsonHan.Chapter01.definition_1_1_3_iff` assumes that $W$
is nonempty. -/
def definition_1_1_3 (𝕜 : Type*) {V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (W : Set V) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, u + v ∈ W) ∧ ∀ α : 𝕜, ∀ v ∈ W, α • v ∈ W

/-- Let $W$ be a nonempty subset of a linear space $V$. Then $W$ is a subspace in the sense of
Definition 1.1.3 of [han2009theoretical] if and only if $W$ is the carrier of a submodule of
$V$.

Nonemptiness is the condition that the book leaves implicit: the two closure conditions hold for
the empty set, which is not a linear space. -/
theorem definition_1_1_3_iff {W : Set V} (hW : W.Nonempty) :
    definition_1_1_3 𝕜 W ↔ ∃ p : Submodule 𝕜 V, (p : Set V) = W := by
  constructor
  · rintro ⟨hadd, hsmul⟩
    obtain ⟨w, hw⟩ := hW
    have hzero : (0 : V) ∈ W := by simpa using hsmul 0 w hw
    exact ⟨{ carrier := W
             add_mem' := fun {a b} ha hb => hadd a ha b hb
             zero_mem' := hzero
             smul_mem' := fun c x hx => hsmul c x hx }, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨fun _ hu _ hv => p.add_mem hu hv, fun α _ hv => p.smul_mem α hv⟩

/-- **Example 1.1.4** of [han2009theoretical]. In $\mathbb{R}^3$, the plane $W = \{x : x_3 = 0\}$ is
a subspace, and the plane $\hat W = \{x : x_3 = 1\}$ is not a subspace. Moreover
$\hat W = x_0 + W$ with $x_0 = (0, 0, 1)$: a vector $x$ satisfies $x_3 = 1$ if and only if
$x = x_0 + w$ for some $w$ with $w_3 = 0$.

Coordinates are indexed from $0$ in Lean, so $x_3$ is `x 2` and $x_0$ is
`EuclideanSpace.single 2 1`. -/
theorem example_1_1_4 :
    definition_1_1_3 ℝ {x : EuclideanSpace ℝ (Fin 3) | x 2 = 0} ∧
      ¬ definition_1_1_3 ℝ {x : EuclideanSpace ℝ (Fin 3) | x 2 = 1} ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), x 2 = 1 ↔
        ∃ w : EuclideanSpace ℝ (Fin 3), w 2 = 0 ∧ x = EuclideanSpace.single 2 (1 : ℝ) + w := by
  refine ⟨⟨fun u hu v hv => ?_, fun α v hv => ?_⟩, fun h => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · simp only [Set.mem_ofPred_eq] at hu hv ⊢
    simp [hu, hv]
  · simp only [Set.mem_ofPred_eq] at hv ⊢
    simp [hv]
  · have hx : EuclideanSpace.single (2 : Fin 3) (1 : ℝ) ∈
        {x : EuclideanSpace ℝ (Fin 3) | x 2 = 1} := by simp
    have h0 := h.2 0 _ hx
    simp only [Set.mem_ofPred_eq, zero_smul] at h0
    simp at h0
  · refine ⟨x - EuclideanSpace.single 2 (1 : ℝ), ?_, by abel⟩
    simp [hx]
  · rintro ⟨w, hw, rfl⟩
    simp [hw]

/-- **Definition 1.1.5** of [han2009theoretical]. Vectors $v_1, \dots, v_n$ of a linear space $V$
are **linearly independent** if $\sum_{i=1}^n \alpha_i v_i = 0$ implies
$\alpha_1 = \dots = \alpha_n = 0$. Otherwise they are **linearly dependent**: some combination
$\sum_{i=1}^n \alpha_i v_i = 0$ has a nonzero coefficient.

The vectors form a family `v : Fin n → V`. The predicate is `LinearIndependent` by
`AtkinsonHan.Chapter01.definition_1_1_5_iff`. -/
def definition_1_1_5 (𝕜 : Type*) {V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} (v : Fin n → V) : Prop :=
  ∀ α : Fin n → 𝕜, ∑ i, α i • v i = 0 → ∀ i, α i = 0

/-- A finite family $v_1, \dots, v_n$ in a linear space is linearly independent in the sense of
Definition 1.1.5 of [han2009theoretical] if and only if it is `LinearIndependent`. -/
theorem definition_1_1_5_iff {n : ℕ} (v : Fin n → V) :
    definition_1_1_5 𝕜 v ↔ LinearIndependent 𝕜 v :=
  Fintype.linearIndependent_iff.symm

/-- **Example 1.1.6** of [han2009theoretical]. Let $x^{(1)}, \dots, x^{(d)} \in \mathbb{R}^d$, and
let $X$ be the $d \times d$ matrix with columns $x^{(1)}, \dots, x^{(d)}$. The vectors are
linearly independent if and only if $\det X \neq 0$.

The matrix $X$ is `Matrix.of fun i j => x j i`, whose entry $(i, j)$ is component $i$ of
$x^{(j)}$. -/
theorem example_1_1_6 {d : ℕ} (x : Fin d → EuclideanSpace ℝ (Fin d)) :
    definition_1_1_5 ℝ x ↔ (Matrix.of fun i j => x j i).det ≠ 0 := by
  rw [definition_1_1_5_iff]
  have hker : LinearMap.ker (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).injective
  have hmap := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap.linearIndependent_iff hker
    (v := x)
  rw [← hmap, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_col_iff_isUnit]
  rfl

/-- **Example 1.1.7** of [han2009theoretical]. For every $n \in \mathbb{N}$, the functions
$1, x, x^2, \dots, x^n$ are linearly independent in $C[0, 1]$.

A vanishing linear combination is a polynomial with infinitely many roots, so it is the zero
polynomial, and all its coefficients are zero. -/
theorem example_1_1_7 (n : ℕ) :
    definition_1_1_5 ℝ (fun j : Fin (n + 1) =>
      (⟨fun x => (x : ℝ) ^ (j : ℕ), by fun_prop⟩ : C(Set.Icc (0 : ℝ) 1, ℝ))) := by
  classical
  intro α hα j
  set p : Polynomial ℝ := ∑ j : Fin (n + 1), Polynomial.C (α j) * Polynomial.X ^ (j : ℕ) with hp
  have hroot : {x : ℝ | p.IsRoot x}.Infinite := by
    refine Set.Infinite.mono (fun x hx => ?_) (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1))
    have hev := congrArg (fun f : C(Set.Icc (0 : ℝ) 1, ℝ) => f ⟨x, hx⟩) hα
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      ContinuousMap.coe_mk, smul_eq_mul, ContinuousMap.zero_apply] at hev
    simpa [Polynomial.IsRoot, hp, Polynomial.eval_finsetSum] using hev
  have hzero : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hroot
  have hcoeff : p.coeff (j : ℕ) = α j := by
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Fin.val_inj]
    simp
  rw [← hcoeff, hzero, Polynomial.coeff_zero]

/-- **Definition 1.1.8** of [han2009theoretical]. The **span** of vectors $v_1, \dots, v_n$ of a
linear space $V$ is the set of all their linear combinations, $$\operatorname{span}\{v_1, \dots,
v_n\} = \Big\{\sum_{i=1}^n \alpha_i v_i : \alpha_1, \dots, \alpha_n \in \mathbb{K}\Big\}.$$

The span is the carrier of `Submodule.span 𝕜 (Set.range v)` by
`AtkinsonHan.Chapter01.definition_1_1_8_iff`, and it is a subspace by
`AtkinsonHan.Chapter01.definition_1_1_8_isSubspace`. -/
def definition_1_1_8 (𝕜 : Type*) {V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} (v : Fin n → V) : Set V :=
  {u | ∃ α : Fin n → 𝕜, u = ∑ i, α i • v i}

/-- The span of $v_1, \dots, v_n$ in the sense of Definition 1.1.8 of [han2009theoretical] is the
carrier of the submodule `Submodule.span 𝕜 (Set.range v)` that the vectors generate. -/
theorem definition_1_1_8_iff {n : ℕ} (v : Fin n → V) :
    definition_1_1_8 𝕜 v = (Submodule.span 𝕜 (Set.range v) : Set V) := by
  ext u
  simp only [definition_1_1_8, Set.mem_ofPred_eq, SetLike.mem_coe,
    Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨α, hα⟩ => ⟨α, hα.symm⟩, fun ⟨α, hα⟩ => ⟨α, hα.symm⟩⟩

/-- The span of $v_1, \dots, v_n$ in the sense of Definition 1.1.8 of [han2009theoretical] is a
subspace in the sense of Definition 1.1.3. The book observes this after Definition 1.1.8. -/
theorem definition_1_1_8_isSubspace {n : ℕ} (v : Fin n → V) :
    definition_1_1_3 𝕜 (definition_1_1_8 𝕜 v) := by
  rw [definition_1_1_8_iff]
  exact ⟨fun _ hu _ hv => Submodule.add_mem _ hu hv, fun α _ hv => Submodule.smul_mem _ α hv⟩

/-- **Definition 1.1.9** of [han2009theoretical]. Vectors $v_1, \dots, v_n$ of a linear space $V$
form a **basis** of $V$ if they are a maximal linearly independent set: they are linearly
independent, and for every $v \in V$ the vectors $v_1, \dots, v_n, v$ are linearly dependent.
The space $V$ is **finite dimensional** if it has such a finite basis, and **infinite
dimensional** otherwise.

The predicate is about one family `v : Fin n → V`, and the family $v_1, \dots, v_n, v$ is
`Fin.snoc v w`. The predicate is `Module.Basis` by `AtkinsonHan.Chapter01.definition_1_1_9_iff`,
and the existence of such a family is `FiniteDimensional` by
`AtkinsonHan.Chapter01.definition_1_1_9_finiteDimensional_iff`. -/
def definition_1_1_9 (𝕜 : Type*) {V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} (v : Fin n → V) : Prop :=
  definition_1_1_5 𝕜 v ∧ ∀ w : V, ¬ definition_1_1_5 𝕜 (Fin.snoc v w)

/-- A family $v_1, \dots, v_n$ in a linear space $V$ is a basis in the sense of Definition 1.1.9 of
[han2009theoretical], that is, a maximal linearly independent family, if and only if it is the
family of vectors of a Mathlib basis `Module.Basis (Fin n) 𝕜 V`. -/
theorem definition_1_1_9_iff {n : ℕ} (v : Fin n → V) :
    definition_1_1_9 𝕜 v ↔ ∃ b : Module.Basis (Fin n) 𝕜 V, ⇑b = v := by
  simp only [definition_1_1_9, definition_1_1_5_iff, linearIndependent_finSnoc, not_and, not_not]
  constructor
  · rintro ⟨hli, hmax⟩
    have hspan : ⊤ ≤ Submodule.span 𝕜 (Set.range v) := fun w _ => hmax w hli
    exact ⟨Module.Basis.mk hli hspan, by simp⟩
  · rintro ⟨b, rfl⟩
    refine ⟨b.linearIndependent, fun w _ => ?_⟩
    rw [b.span_eq]
    trivial

/-- A linear space $V$ has a finite basis in the sense of Definition 1.1.9 of [han2009theoretical]
if and only if $V$ is `FiniteDimensional`. -/
theorem definition_1_1_9_finiteDimensional_iff (𝕜 V : Type*) [DivisionRing 𝕜] [AddCommGroup V]
    [Module 𝕜 V] :
    (∃ (n : ℕ) (v : Fin n → V), definition_1_1_9 𝕜 v) ↔ FiniteDimensional 𝕜 V := by
  constructor
  · rintro ⟨n, v, hv⟩
    obtain ⟨b, rfl⟩ := (definition_1_1_9_iff _).mp hv
    exact Module.Finite.of_basis b
  · intro _
    obtain ⟨s, b⟩ := Module.Free.exists_basis (R := 𝕜) (M := V)
    have : Fintype s := FiniteDimensional.fintypeBasisIndex b
    exact ⟨Fintype.card s, _, (definition_1_1_9_iff _).mpr ⟨b.reindex (Fintype.equivFin s), rfl⟩⟩

/-- **Theorem 1.1.10** of [han2009theoretical]. Any two bases of a linear space $V$ have the same
number of elements, and this number is $\dim V$: for every basis $\{b_i\}_{i \in \iota}$ of $V$,
the index set $\iota$ has $\dim V$ elements.

The basis is `Module.Basis ι 𝕜 V` for an arbitrary index type `ι`, the number of elements is
`Nat.card ι`, and the dimension is `Module.finrank 𝕜 V`. If $V$ is infinite dimensional, then `ι`
is infinite and both sides are $0$ by the conventions of `Nat.card` and `Module.finrank`, so the
statement has content only for a finite-dimensional $V$. Two bases are compared through this
equality. -/
theorem theorem_1_1_10 {ι : Type*} (b : Module.Basis ι 𝕜 V) :
    Nat.card ι = Module.finrank 𝕜 V :=
  (Module.finrank_eq_nat_card_basis b).symm

/-- **Example 1.1.11** of [han2009theoretical]. For every $d \in \mathbb{N}$, the coordinate vectors
$e_i = (0, \dots, 0, 1, 0, \dots, 0)$, $i = 1, \dots, d$, form a basis of $\mathbb{R}^d$ in the
sense of Definition 1.1.9, and $\dim \mathbb{R}^d = d$. -/
theorem example_1_1_11 (d : ℕ) :
    definition_1_1_9 ℝ (fun i : Fin d => EuclideanSpace.single i (1 : ℝ)) ∧
      Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
  ⟨(definition_1_1_9_iff _).mpr ⟨(EuclideanSpace.basisFun (Fin d) ℝ).toBasis, by ext i : 1; simp⟩,
    finrank_euclideanSpace_fin⟩

/-- **Example 1.1.12** of [han2009theoretical]. Let $n \ge 1$, let $\mathbb{F}_n$ be the space of
real polynomials of degree at most $n$, and let $W$ be its subspace $\mathbb{F}_{n,0} = \{p \in
\mathbb{F}_n : p(0) = p(1) = 0\}$. Then $\dim \mathbb{F}_n = n + 1$ and $$\dim
\mathbb{F}_{n,0} + 2 = \dim \mathbb{F}_n.$$ The difference $2$ counts the two conditions at $0$
and $1$.

The space $\mathbb{F}_n$ is `Polynomial.degreeLT ℝ (n + 1)`. The subspace is described by the
hypothesis `hW` and is not named. The count is written with $+ 2$ to stay in $\mathbb{N}$. The
book's basis $x(1 - x), \dots, x^{n-1}(1 - x)$ of $\mathbb{F}_{n,0}$ is not part of the
statement. -/
theorem example_1_1_12 {n : ℕ} (hn : 1 ≤ n) (W : Submodule ℝ (Polynomial.degreeLT ℝ (n + 1)))
    (hW : ∀ p : Polynomial.degreeLT ℝ (n + 1),
      p ∈ W ↔ (p : Polynomial ℝ).eval 0 = 0 ∧ (p : Polynomial ℝ).eval 1 = 0) :
    Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) = n + 1 ∧
      Module.finrank ℝ W + 2 = Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  have hdim : Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) = n + 1 := by
    rw [(Polynomial.degreeLTEquiv ℝ (n + 1)).finrank_eq, Module.finrank_fin_fun]
  have _ : FiniteDimensional ℝ (Polynomial.degreeLT ℝ (n + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℝ (n + 1)).symm
  set L : Polynomial.degreeLT ℝ (n + 1) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun p => ((p : Polynomial ℝ).eval 0, (p : Polynomial ℝ).eval 1)
      map_add' := fun p q => by simp
      map_smul' := fun c p => by
        simp [Polynomial.smul_eq_C_mul, Prod.smul_mk] } with hL
  have hWker : W = LinearMap.ker L := by
    ext p
    rw [hW p, LinearMap.mem_ker, hL]
    simp [Prod.ext_iff]
  have hrange : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    have hdeg : (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X) ∈
        Polynomial.degreeLT ℝ (n + 1) := by
      refine Polynomial.mem_degreeLT.2 (lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_)
      refine max_lt (lt_of_le_of_lt Polynomial.degree_C_le ?_)
        (lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_)
      · have h0 : ((0 : ℕ) : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) := by
          exact_mod_cast Nat.succ_pos n
        simpa using h0
      · have h1 : ((1 : ℕ) : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) := by
          exact_mod_cast (by omega : 1 < n + 1)
        simpa using h1
    refine ⟨⟨_, hdeg⟩, ?_⟩
    simp [hL]
  have hcount := L.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self] at hcount
  refine ⟨hdim, ?_⟩
  rw [hWker]
  omega

/-- **Definition 1.1.13** of [han2009theoretical]. Let $V$ and $W$ be linear spaces over
$\mathbb{K}$. A function $L : V \to W$ is a **linear function** (also called a linear mapping,
operator or transformation) if $L(u + v) = Lu + Lv$ and $L(\alpha v) = \alpha L v$ for all
$u, v \in V$ and $\alpha \in \mathbb{K}$.

The predicate is `LinearMap` by `AtkinsonHan.Chapter01.definition_1_1_13_iff`. Chapter 2 of the
book develops the notion further. -/
def definition_1_1_13 (𝕜 : Type*) {V W : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] (L : V → W) : Prop :=
  (∀ u v : V, L (u + v) = L u + L v) ∧ ∀ (α : 𝕜) (v : V), L (α • v) = α • L v

/-- A function $L : V \to W$ between linear spaces is linear in the sense of Definition 1.1.13 of
[han2009theoretical] if and only if it is the function of a linear map `V →ₗ[𝕜] W`. -/
theorem definition_1_1_13_iff (L : V → W) :
    definition_1_1_13 𝕜 L ↔ ∃ T : V →ₗ[𝕜] W, ⇑T = L :=
  ⟨fun h => ⟨⟨⟨L, h.1⟩, h.2⟩, rfl⟩, by rintro ⟨T, rfl⟩; exact ⟨map_add T, map_smul T⟩⟩

/-- **Definition 1.1.14** of [han2009theoretical]. Two linear spaces $U$ and $V$ over $\mathbb{K}$
are **isomorphic** if there is a linear bijection $\ell : U \to V$.

The predicate is the existence of a `LinearEquiv` by
`AtkinsonHan.Chapter01.definition_1_1_14_iff`. -/
def definition_1_1_14 (𝕜 U V : Type*) [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] : Prop :=
  ∃ l : U → V, definition_1_1_13 𝕜 l ∧ Function.Bijective l

/-- Two linear spaces $U$ and $V$ are isomorphic in the sense of Definition 1.1.14 of
[han2009theoretical] if and only if there is a linear equivalence `U ≃ₗ[𝕜] V`. -/
theorem definition_1_1_14_iff (𝕜 U V : Type*) [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] :
    definition_1_1_14 𝕜 U V ↔ Nonempty (U ≃ₗ[𝕜] V) := by
  constructor
  · rintro ⟨l, hl, hbij⟩
    obtain ⟨T, rfl⟩ := (definition_1_1_13_iff (𝕜 := 𝕜) l).mp hl
    exact ⟨LinearEquiv.ofBijective T hbij⟩
  · rintro ⟨e⟩
    exact ⟨e, ⟨map_add e, map_smul e⟩, e.bijective⟩

/-- **Example 1.1.15** of [han2009theoretical]. Let $k \in \mathbb{N}$. The set of functions in
$C[0, 1]$ that agree on $[0, 1]$ with a real polynomial of degree at most $k$ is a subspace of
$C[0, 1]$. The space $\mathbb{F}_k$ of real polynomials of degree at most $k$ is isomorphic to
$\mathbb{R}^{k+1}$.

The book gives the isomorphism $a_0 + a_1 x + \dots + a_k x^k \mapsto (a_0, a_1, \dots, a_k)$.
The statement asserts only that an isomorphism exists. The space $\mathbb{F}_k$ is
`Polynomial.degreeLT ℝ (k + 1)`. -/
theorem example_1_1_15 (k : ℕ) :
    definition_1_1_3 ℝ {f : C(Set.Icc (0 : ℝ) 1, ℝ) |
        ∃ p ∈ Polynomial.degreeLT ℝ (k + 1), ∀ x, f x = p.eval (x : ℝ)} ∧
      definition_1_1_14 ℝ (Polynomial.degreeLT ℝ (k + 1)) (EuclideanSpace ℝ (Fin (k + 1))) := by
  refine ⟨⟨fun f hf g hg => ?_, fun α f hf => ?_⟩, (definition_1_1_14_iff _ _ _).mpr
    ⟨(Polynomial.degreeLTEquiv ℝ (k + 1)).trans (WithLp.linearEquiv 2 ℝ (Fin (k + 1) → ℝ)).symm⟩⟩
  · obtain ⟨p, hp, hfp⟩ := hf
    obtain ⟨q, hq, hgq⟩ := hg
    exact ⟨p + q, Submodule.add_mem _ hp hq, fun x => by simp [hfp x, hgq x]⟩
  · obtain ⟨p, hp, hfp⟩ := hf
    exact ⟨α • p, Submodule.smul_mem _ α hp, fun x => by
      simp only [ContinuousMap.smul_apply, smul_eq_mul, hfp x, Polynomial.smul_eq_C_mul,
        Polynomial.eval_mul, Polynomial.eval_C]⟩

/-- **Definition 1.1.16** of [han2009theoretical]. The **Cartesian product** $U \times V$ of two
linear spaces is the set of pairs $(u, v)$ with $u \in U$ and $v \in V$, with the operations
$$(u_1, v_1) + (u_2, v_2) = (u_1 + u_2, v_1 + v_2), \qquad \alpha (u, v) = (\alpha u, \alpha
v).$$ It is a linear space. The theorem states that the product `U × V` of Mathlib has exactly
these operations.

The linear space structure is the `Module` instance of `Prod`. -/
theorem definition_1_1_16 (u₁ u₂ : U) (v₁ v₂ : V) (α : 𝕜) :
    ((u₁, v₁) + (u₂, v₂) : U × V) = (u₁ + u₂, v₁ + v₂) ∧
      α • ((u₁, v₁) : U × V) = (α • u₁, α • v₁) :=
  ⟨rfl, rfl⟩

/-- **Example 1.1.17** of [han2009theoretical]. The real plane is the Cartesian product of two real
lines: $\mathbb{R}^2$ is isomorphic to $\mathbb{R} \times \mathbb{R}$. More generally, for every
$d \in \mathbb{N}$, $\mathbb{R}^d$ is isomorphic to the $d$-fold product of $\mathbb{R}$.

The $d$-fold product is the function type `Fin d → ℝ`, which underlies
`EuclideanSpace ℝ (Fin d)`. -/
theorem example_1_1_17 (d : ℕ) :
    definition_1_1_14 ℝ (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ) ∧
      definition_1_1_14 ℝ (EuclideanSpace ℝ (Fin d)) (Fin d → ℝ) :=
  ⟨(definition_1_1_14_iff _ _ _).mpr
      ⟨(WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).trans (LinearEquiv.finTwoArrow ℝ ℝ)⟩,
    (definition_1_1_14_iff _ _ _).mpr ⟨WithLp.linearEquiv 2 ℝ (Fin d → ℝ)⟩⟩

end LinearSpace

end AtkinsonHan.Chapter01
