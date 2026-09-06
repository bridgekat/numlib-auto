import Mathlib.Algebra.BigOperators.Module

/-!
# Nodal interpolation and the reference element

Given finitely many *nodes* `x i` in a set and *shape functions* `φ i` on it, the **nodal
interpolation operator** sends a function `v` to `∑ i, φ i · v (x i)`. When the shape functions are
dual to the nodes, `φ i (x j) = δ_ij` (`Approximation.IsNodalBasis`), the interpolant reproduces `v`
at every node, which is the defining property of an interpolation operator.

The point of the file is `Approximation.nodalInterp_comp`: nodal interpolation **commutes with a
change of variables** that carries the nodes and the shape functions along with it. Interpolation on
a set `K`, at the nodes `F (x i)` and with the shape functions `φ i ∘ F⁻¹`, is the same operation as
interpolation on the reference set at the nodes `x i` with the shape functions `φ i`, read through
`F`. This is the *reference element technique* of the finite element method, where `F` is an affine
bijection from a reference element onto an element of the mesh: [han2009theoretical],
Theorem 10.3.1. The identity is pure algebra — no norm, no integral and no smoothness enters —
and the hypothesis on the change of variables is only that it has a left inverse.

Nothing here assumes that the shape functions span a particular space, or that the interpolation
problem is unisolvent; `Numlib/Approximation/Unisolvent.lean` treats that, and for a unisolvent
problem the shape functions dual to the nodes are exactly the basis it produces.
-/

namespace Approximation

variable {ι α β 𝕜 M : Type*} [Fintype ι] [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M]

/-- **The nodal interpolation operator** of the nodes `x` and the shape functions `φ`:

  `nodalInterp x φ v = ∑ i, φ i · v (x i)`,

the combination of the shape functions with the values of `v` at the nodes. It is
[han2009theoretical], (10.3.1) and (10.3.2). -/
def nodalInterp (x : ι → α) (φ : ι → α → 𝕜) (v : α → M) : α → M :=
  fun y => ∑ i, φ i y • v (x i)

@[simp]
theorem nodalInterp_apply (x : ι → α) (φ : ι → α → 𝕜) (v : α → M) (y : α) :
    nodalInterp x φ v y = ∑ i, φ i y • v (x i) := rfl

/-- The shape functions `φ` are **nodal** for the nodes `x` when `φ i (x j) = δ_ij`. This is what
makes `nodalInterp x φ` an interpolation operator: `nodalInterp x φ v` agrees with `v` at every node
(`Approximation.IsNodalBasis.nodalInterp_apply_node`). -/
structure IsNodalBasis (x : ι → α) (φ : ι → α → 𝕜) : Prop where
  /-- Each shape function takes the value `1` at its own node. -/
  eval_self : ∀ i, φ i (x i) = 1
  /-- Each shape function vanishes at the other nodes. -/
  eval_of_ne : ∀ i j, i ≠ j → φ i (x j) = 0

/-- A nodal interpolant reproduces the data at the nodes. -/
theorem IsNodalBasis.nodalInterp_apply_node {x : ι → α} {φ : ι → α → 𝕜} (h : IsNodalBasis x φ)
    (v : α → M) (j : ι) : nodalInterp x φ v (x j) = v (x j) := by
  rw [nodalInterp_apply, Finset.sum_eq_single j]
  · rw [h.eval_self, one_smul]
  · exact fun i _ hij => by rw [h.eval_of_ne i j hij, zero_smul]
  · exact fun hj => absurd (Finset.mem_univ j) hj

omit [Fintype ι] in
/-- Pushing the nodes forward along `F` and the shape functions along a left inverse `G` of `F`
again gives a nodal family. -/
theorem IsNodalBasis.comp {x : ι → α} {φ : ι → α → 𝕜} (h : IsNodalBasis x φ) {F : α → β} {G : β → α}
    (hG : Function.LeftInverse G F) : IsNodalBasis (F ∘ x) (fun i => φ i ∘ G) where
  eval_self i := by simpa [hG (x i)] using h.eval_self i
  eval_of_ne i j hij := by simpa [hG (x j)] using h.eval_of_ne i j hij

/-- **Nodal interpolation commutes with a change of variables.** If `G` is a left inverse of `F`,
then interpolating `v` at the transported nodes `F ∘ x` with the transported shape functions
`φ i ∘ G` and reading the result through `F` is interpolating `v ∘ F` at the original nodes with the
original shape functions:

  `(nodalInterp (F ∘ x) (φ · ∘ G) v) ∘ F = nodalInterp x φ (v ∘ F)`.

For an affine bijection `F` of a reference element onto an element `K` this is
[han2009theoretical], Theorem 10.3.1, `(Π_K v) ∘ F_K = Π̂ (v ∘ F_K)`, on which the reference element
error analysis rests. Both sides are the same sum: `F` cancels against `G` inside the shape
functions, and the data `v (F (x i))` are the values of `v ∘ F` at the nodes. -/
theorem nodalInterp_comp (x : ι → α) (φ : ι → α → 𝕜) (v : β → M) {F : α → β} {G : β → α}
    (hG : Function.LeftInverse G F) :
    nodalInterp (F ∘ x) (fun i => φ i ∘ G) v ∘ F = nodalInterp x φ (v ∘ F) := by
  funext y
  simp [nodalInterp, hG y]

end Approximation
