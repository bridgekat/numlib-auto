import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Saddle points and the minimax equality

For `L : α → β → ℝ` and sets `A ⊆ α`, `B ⊆ β`, a pair `(u, p)` is a *saddle point* of `L` on
`A × B` when

  `L u q ≤ L u p ≤ L v p`  for all `v ∈ A` and `q ∈ B`,

so that `u` minimizes `L · p` over `A` while `p` maximizes `L u ·` over `B`.  The content of this
module is that a saddle point is exactly a point where the two extremal problems

  `min_{v ∈ A} sup_{q ∈ B} L v q`  and  `max_{q ∈ B} inf_{v ∈ A} L v q`

are both solved and have the common value `L u p`.  In the applications the first is a primal
problem and the second its dual, and the equality of the two values is the absence of a duality
gap; this is the shape of the dual formulation of a boundary value problem.

Nothing here is convex analysis: `A` and `B` are bare sets, `L` an arbitrary real function, and
every proof is order arithmetic.  The one trap is that `sSup` and `sInf` take junk values on
unbounded sets, so the two extremal statements carry explicit `BddAbove`/`BddBelow` hypotheses
rather than being phrased with `⨆`/`⨅` over subtypes.

Not proved here: the existence of a saddle point for a convex–concave `L` on closed convex subsets
of a reflexive Banach space, which needs weak compactness of bounded sets in a reflexive space.

The definition and the equivalence are Definition 8.6.1 and Proposition 8.6.2 of
[Atkinson–Han][han2009theoretical].
-/

variable {α β : Type*} {L : α → β → ℝ} {A : Set α} {B : Set β} {u : α} {p : β}

/-- `(u, p)` is a saddle point of `L : α → β → ℝ` on `A × B`: `u ∈ A`, `p ∈ B`, and
`L u q ≤ L u p ≤ L v p` for every `v ∈ A` and `q ∈ B`. -/
structure IsSaddlePoint (L : α → β → ℝ) (A : Set α) (B : Set β) (u : α) (p : β) : Prop where
  /-- The first component lies in the first set. -/
  mem_left : u ∈ A
  /-- The second component lies in the second set. -/
  mem_right : p ∈ B
  /-- `p` maximizes `L u ·` over `B`. -/
  apply_le : ∀ q ∈ B, L u q ≤ L u p
  /-- `u` minimizes `L · p` over `A`. -/
  le_apply : ∀ v ∈ A, L u p ≤ L v p

namespace IsSaddlePoint

/-- Weak duality at a saddle point: `L u q ≤ L v p` for every `v ∈ A` and `q ∈ B`, so no value of
the dual problem exceeds any value of the primal problem. -/
theorem le (h : IsSaddlePoint L A B u p) {v : α} (hv : v ∈ A) {q : β} (hq : q ∈ B) :
    L u q ≤ L v p :=
  (h.apply_le q hq).trans (h.le_apply v hv)

/-- The value of the primal objective at a saddle point: `sup_{q ∈ B} L u q = L u p`. -/
theorem isGreatest_image (h : IsSaddlePoint L A B u p) : IsGreatest (L u '' B) (L u p) :=
  ⟨⟨p, h.mem_right, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact h.apply_le q hq⟩

/-- The value of the dual objective at a saddle point: `inf_{v ∈ A} L v p = L u p`. -/
theorem isLeast_image (h : IsSaddlePoint L A B u p) :
    IsLeast ((fun v => L v p) '' A) (L u p) :=
  ⟨⟨u, h.mem_left, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact h.le_apply v hv⟩

/-- `sSup (L u '' B) = L u p`: the primal objective `v ↦ sup_{q ∈ B} L v q` takes the value
`L u p` at `u`. -/
theorem sSup_image_eq (h : IsSaddlePoint L A B u p) : sSup (L u '' B) = L u p :=
  h.isGreatest_image.csSup_eq

/-- `sInf ((fun v => L v p) '' A) = L u p`: the dual objective `q ↦ inf_{v ∈ A} L v q` takes the
value `L u p` at `p`. -/
theorem sInf_image_eq (h : IsSaddlePoint L A B u p) : sInf ((fun v => L v p) '' A) = L u p :=
  h.isLeast_image.csInf_eq

/-- At a saddle point the primal objective `v ↦ sup_{q ∈ B} L v q` attains its least value on `A`,
at `u`, and that value is `L u p`.  The boundedness hypothesis is what makes each supremum a real
supremum rather than the junk value `sSup ∅ = 0`. -/
theorem isLeast_sSup (h : IsSaddlePoint L A B u p) (hbdd : ∀ v ∈ A, BddAbove (L v '' B)) :
    IsLeast ((fun v => sSup (L v '' B)) '' A) (L u p) := by
  refine ⟨⟨u, h.mem_left, h.sSup_image_eq⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact (h.le_apply v hv).trans (le_csSup (hbdd v hv) ⟨p, h.mem_right, rfl⟩)

/-- At a saddle point the dual objective `q ↦ inf_{v ∈ A} L v q` attains its greatest value on
`B`, at `p`, and that value is again `L u p`.  With `IsSaddlePoint.isLeast_sSup` this is the
minimax equality: the primal minimum and the dual maximum are both `L u p`. -/
theorem isGreatest_sInf (h : IsSaddlePoint L A B u p)
    (hbdd : ∀ q ∈ B, BddBelow ((fun v => L v q) '' A)) :
    IsGreatest ((fun q => sInf ((fun v => L v q) '' A)) '' B) (L u p) := by
  refine ⟨⟨p, h.mem_right, h.sInf_image_eq⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact (csInf_le (hbdd q hq) ⟨u, h.mem_left, rfl⟩).trans (h.apply_le q hq)

end IsSaddlePoint

/-- The converse of `IsSaddlePoint.isLeast_sSup` and `IsSaddlePoint.isGreatest_sInf`: if the
primal objective attains its minimum over `A` at `u`, the dual objective attains its maximum over
`B` at `p`, and the two extremal values agree, then `(u, p)` is a saddle point of `L`.

What the proof needs is only that the primal value at `u` equals the dual value at `p`, and the
three hypotheses on the extremal problems say exactly that: the two `IsLeast`/`IsGreatest`
hypotheses identify the extremal values through `IsLeast.csInf_eq` and `IsGreatest.csSup_eq`, and
their equality is the absence of a duality gap.  The boundedness hypotheses keep `sSup` and `sInf`
away from their junk values. -/
theorem isSaddlePoint_of_isLeast_of_isGreatest (hu : u ∈ A) (hp : p ∈ B)
    (hbddA : BddAbove (L u '' B)) (hbddB : BddBelow ((fun v => L v p) '' A))
    (hleast : IsLeast ((fun v => sSup (L v '' B)) '' A) (sSup (L u '' B)))
    (hgreatest : IsGreatest ((fun q => sInf ((fun v => L v q) '' A)) '' B)
      (sInf ((fun v => L v p) '' A)))
    (heq : sInf ((fun v => sSup (L v '' B)) '' A)
      = sSup ((fun q => sInf ((fun v => L v q) '' A)) '' B)) :
    IsSaddlePoint L A B u p := by
  have hval : sSup (L u '' B) = sInf ((fun v => L v p) '' A) := by
    rw [← hleast.csInf_eq, heq, hgreatest.csSup_eq]
  refine ⟨hu, hp, fun q hq => ?_, fun v hv => ?_⟩
  · calc L u q ≤ sSup (L u '' B) := le_csSup hbddA ⟨q, hq, rfl⟩
      _ = sInf ((fun v => L v p) '' A) := hval
      _ ≤ L u p := csInf_le hbddB ⟨u, hu, rfl⟩
  · calc L u p ≤ sSup (L u '' B) := le_csSup hbddA ⟨p, hp, rfl⟩
      _ = sInf ((fun v => L v p) '' A) := hval
      _ ≤ L v p := csInf_le hbddB ⟨v, hv, rfl⟩
