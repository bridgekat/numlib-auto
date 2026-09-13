import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Hom.Basic

/-!
# A Galois connection restricts to an order isomorphism between the closed elements

For a Galois connection `l ⊣ u`, the elements of `α` fixed by `u ∘ l` and those of `β` fixed by
`l ∘ u` correspond order-isomorphically, with `l` and `u` exchanging them. Mathlib has only the
one-sided `ClosureOperator.gi`. Stated for a bare `GaloisConnection` on two `PartialOrder`s.

Every "the operation is an involution on a characterised class" theorem of convex analysis is an
instance: conjugacy on the closed convex functions on the two sides of a pairing (Rockafellar's
Corollary 12.2.1), polarity on the closed convex cones (Theorem 14.1), the gauge and
support-function correspondences. Those connections are antitone — presented, as Mathlib presents
them, with one side an `OrderDual` — so the correspondences are order *anti*-isomorphisms.

## Main results

* `GaloisConnection.closedsOrderIso` — the isomorphism.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §12, §14.
-/

namespace GaloisConnection

variable {α β : Type*} [PartialOrder α] [PartialOrder β] {l : α → β} {u : β → α}

/-- `{a // u (l a) = a}` and `{b // l (u b) = b}` are the two classes on which the connection's
round trips are the identity, and `l`/`u` exchange them order-isomorphically. -/
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

@[simp] theorem closedsOrderIso_apply (gc : GaloisConnection l u) (a : {a : α // u (l a) = a}) :
    (gc.closedsOrderIso a : β) = l a := rfl

@[simp] theorem closedsOrderIso_symm_apply (gc : GaloisConnection l u)
    (b : {b : β // l (u b) = b}) : (gc.closedsOrderIso.symm b : α) = u b := rfl

end GaloisConnection
