/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Hom.Basic

/-!
# The order isomorphism between the closed elements of a Galois connection

Let $l \colon \alpha \to \beta$ and $u \colon \beta \to \alpha$ form a Galois connection between
partial orders. The elements $a \in \alpha$ with $u(l(a)) = a$ and the elements $b \in \beta$ with
$l(u(b)) = b$ correspond under an order isomorphism, and $l$ and $u$ exchange them. Mathlib has only
the one-sided `ClosureOperator.gi`.

Every theorem of convex analysis of the form "the operation is an involution on a characterized
class" is an instance. Examples are conjugacy on the closed convex functions on the two sides of a
pairing (Corollary 12.2.1 of [rockafellar1970convex]), polarity on the closed convex cones (Theorem
14.1 of [rockafellar1970convex]), and the gauge and support function correspondences. These
connections are antitone. As in Mathlib, they are presented with one side an `OrderDual`, so the
correspondences are order anti-isomorphisms.

## Main definitions

* `GaloisConnection.closedsOrderIso`: the order isomorphism
  $\{a : u(l(a)) = a\} \cong \{b : l(u(b)) = b\}$ given by $l$, with inverse $u$.

## Implementation notes

* The result is stated for a `GaloisConnection` between two partial orders, with no further
  structure.
-/

namespace GaloisConnection

variable {α β : Type*} [PartialOrder α] [PartialOrder β] {l : α → β} {u : β → α}

/-- Let $l \colon \alpha \to \beta$ and $u \colon \beta \to \alpha$ form a Galois connection between
partial orders. Then $l$ restricts to an order isomorphism
$$\{a \in \alpha : u(l(a)) = a\} \to \{b \in \beta : l(u(b)) = b\},$$
with inverse the restriction of $u$. These are the two classes of elements on which the round
trips $u \circ l$ and $l \circ u$ are the identity. -/
def closedsOrderIso (gc : GaloisConnection l u) :
    {a : α // u (l a) = a} ≃o {b : β // l (u b) = b} where
  toFun a := ⟨l a.1, gc.l_u_l_eq_l a.1⟩
  invFun b := ⟨u b.1, gc.u_l_u_eq_u b.1⟩
  left_inv a := Subtype.ext a.2
  right_inv b := Subtype.ext b.2
  map_rel_iff' {a a'} := by
    change l a.1 ≤ l a'.1 ↔ a.1 ≤ a'.1
    refine ⟨fun h => ?_, fun h => gc.monotone_l h⟩
    have := gc.monotone_u h
    rwa [a.2, a'.2] at this

/-- The order isomorphism `GaloisConnection.closedsOrderIso` maps $a$ to $l(a)$. -/
@[simp] theorem closedsOrderIso_apply (gc : GaloisConnection l u) (a : {a : α // u (l a) = a}) :
    (gc.closedsOrderIso a : β) = l a := rfl

/-- The inverse of the order isomorphism `GaloisConnection.closedsOrderIso` maps $b$ to $u(b)$. -/
@[simp] theorem closedsOrderIso_symm_apply (gc : GaloisConnection l u)
    (b : {b : β // l (u b) = b}) : (gc.closedsOrderIso.symm b : α) = u b := rfl

end GaloisConnection
