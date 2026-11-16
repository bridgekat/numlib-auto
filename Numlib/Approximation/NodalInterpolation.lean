/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi

/-!
# Nodal interpolation and the reference element

Let $x_1, \dots, x_m$ be finitely many *nodes* in a set $A$, and let $\varphi_1, \dots, \varphi_m
\colon A \to \mathbb{K}$ be *shape functions*. The **nodal interpolation operator** sends a function
$v \colon A \to M$ to $\Pi v = \sum_i \varphi_i \, v(x_i)$. When the shape functions are dual to the
nodes, $\varphi_i(x_j) = \delta_{ij}$, the interpolant agrees with $v$ at every node, which is the
defining property of an interpolation operator.

The main result is that nodal interpolation commutes with a change of variables that carries the
nodes and the shape functions along with it. Let $F \colon A \to B$ have a left inverse $G$.
Interpolation on $B$ at the nodes $F(x_i)$ with the shape functions $\varphi_i \circ G$, followed by
composition with $F$, is interpolation on $A$ at the nodes $x_i$ with the shape functions
$\varphi_i$, applied to $v \circ F$. In the finite element method $F$ is an affine bijection from a
reference element onto an element of the mesh, and the identity is the *reference element technique*
of [han2009theoretical], Theorem 10.3.1. The identity is pure algebra: no norm, no integral and no
smoothness enters.

## Main definitions

* `Approximation.nodalInterp`: the nodal interpolation operator
  $v \mapsto \sum_i \varphi_i \, v(x_i)$.
* `Approximation.IsNodalBasis`: the shape functions satisfy $\varphi_i(x_j) = \delta_{ij}$.

## Main results

* `Approximation.IsNodalBasis.nodalInterp_apply_node`: a nodal interpolant agrees with the data at
  the nodes.
* `Approximation.IsNodalBasis.comp`: transporting the nodes along $F$ and the shape functions along
  a left inverse of $F$ gives a nodal family again.
* `Approximation.nodalInterp_comp`: $(\Pi_B v) \circ F = \Pi_A (v \circ F)$ for the transported
  nodes and shape functions.

## Implementation notes

* The module does not assume that the shape functions span a particular space, or that the
  interpolation problem is unisolvent. `Numlib.Approximation.Unisolvent` treats unisolvence; for a
  unisolvent problem the shape functions dual to the nodes are exactly the basis that it produces.
* The scalars $\mathbb{K}$ form a semiring, and the data take values in a $\mathbb{K}$-module $M$.
  The nodes are indexed by a finite type.
-/

namespace Approximation

variable {ι α β 𝕜 M : Type*} [Fintype ι] [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M]

/-- The **nodal interpolation operator** of the nodes $x_i \in A$ and the shape functions
$\varphi_i \colon A \to \mathbb{K}$, indexed by a finite set, sends $v \colon A \to M$ to the
combination
$$\Pi v = \sum_i \varphi_i \, v(x_i)$$
of the shape functions with the values of $v$ at the nodes. This is (10.3.1) and (10.3.2) of
[han2009theoretical]. -/
def nodalInterp (x : ι → α) (φ : ι → α → 𝕜) (v : α → M) : α → M :=
  fun y => ∑ i, φ i y • v (x i)

/-- The value of the nodal interpolant at a point $y$ is $\sum_i \varphi_i(y) \, v(x_i)$. -/
@[simp]
theorem nodalInterp_apply (x : ι → α) (φ : ι → α → 𝕜) (v : α → M) (y : α) :
    nodalInterp x φ v y = ∑ i, φ i y • v (x i) := rfl

/-- The shape functions $\varphi_i$ are **nodal** for the nodes $x_i$ if
$\varphi_i(x_j) = \delta_{ij}$ for all indices $i$ and $j$. This makes
`Approximation.nodalInterp` an interpolation operator: the interpolant agrees with $v$ at every
node (`Approximation.IsNodalBasis.nodalInterp_apply_node`). -/
structure IsNodalBasis (x : ι → α) (φ : ι → α → 𝕜) : Prop where
  /-- Each shape function takes the value $1$ at its own node: $\varphi_i(x_i) = 1$. -/
  eval_self : ∀ i, φ i (x i) = 1
  /-- Each shape function vanishes at the other nodes: $\varphi_i(x_j) = 0$ for $i \neq j$. -/
  eval_of_ne : ∀ i j, i ≠ j → φ i (x j) = 0

/-- Let the shape functions $\varphi_i$ be nodal for the nodes $x_i$. Then for every function
$v \colon A \to M$ and every index $j$, the interpolant agrees with $v$ at the node $x_j$:
$$(\Pi v)(x_j) = v(x_j).$$
-/
theorem IsNodalBasis.nodalInterp_apply_node {x : ι → α} {φ : ι → α → 𝕜} (h : IsNodalBasis x φ)
    (v : α → M) (j : ι) : nodalInterp x φ v (x j) = v (x j) := by
  rw [nodalInterp_apply, Finset.sum_eq_single j]
  · rw [h.eval_self, one_smul]
  · exact fun i _ hij => by rw [h.eval_of_ne i j hij, zero_smul]
  · exact fun hj => absurd (Finset.mem_univ j) hj

omit [Fintype ι] in
/-- Let the shape functions $\varphi_i$ be nodal for the nodes $x_i \in A$, and let
$F \colon A \to B$ and $G \colon B \to A$ satisfy $G \circ F = \mathrm{id}_A$. Then the shape
functions $\varphi_i \circ G$ are nodal for the nodes $F(x_i)$.

The index type need not be finite here. -/
theorem IsNodalBasis.comp {x : ι → α} {φ : ι → α → 𝕜} (h : IsNodalBasis x φ) {F : α → β} {G : β → α}
    (hG : Function.LeftInverse G F) : IsNodalBasis (F ∘ x) (fun i => φ i ∘ G) where
  eval_self i := by simpa [hG (x i)] using h.eval_self i
  eval_of_ne i j hij := by simpa [hG (x j)] using h.eval_of_ne i j hij

/-- **Nodal interpolation commutes with a change of variables.** Let $x_i \in A$ be nodes, let
$\varphi_i \colon A \to \mathbb{K}$ be shape functions, let $v \colon B \to M$, and let
$F \colon A \to B$ and $G \colon B \to A$ satisfy $G \circ F = \mathrm{id}_A$. Then
interpolating $v$ at the nodes $F(x_i)$ with the shape functions $\varphi_i \circ G$ and
composing with $F$ is the same as interpolating $v \circ F$ at the nodes $x_i$ with the shape
functions $\varphi_i$:
$$\Bigl(\sum_i (\varphi_i \circ G) \, v(F(x_i))\Bigr) \circ F = \sum_i \varphi_i \, (v \circ
  F)(x_i).$$

For an affine bijection $F_K$ of a reference element onto an element $K$ this is Theorem 10.3.1
of [han2009theoretical], $(\Pi_K v) \circ F_K = \hat\Pi (v \circ F_K)$, on which the error
analysis on the reference element rests. Neither nodality of the shape functions nor bijectivity
of $F$ is needed: $F$ cancels against $G$ inside the shape functions. -/
theorem nodalInterp_comp (x : ι → α) (φ : ι → α → 𝕜) (v : β → M) {F : α → β} {G : β → α}
    (hG : Function.LeftInverse G F) :
    nodalInterp (F ∘ x) (fun i => φ i ∘ G) v ∘ F = nodalInterp x φ (v ∘ F) := by
  funext y
  simp [nodalInterp, hG y]

omit [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M] in
/-- For scalar data in a commutative semiring $R$, the interpolant is a linear combination of the
shape functions:
$$\Pi v = \sum_i v(x_i) \, \varphi_i.$$
This is (10.3.1) of [han2009theoretical]. -/
theorem nodalInterp_eq_sum_smul {R : Type*} [CommSemiring R] (x : ι → α) (φ : ι → α → R)
    (v : α → R) : nodalInterp x φ v = ∑ i, v (x i) • φ i := by
  funext y
  simp [nodalInterp_apply, Finset.sum_apply, mul_comm]

end Approximation
