import Numlib.Analysis.Convex.Concave
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Operations.Image

/-!
# Conjugates of concave functions

The **concave conjugate** of `g : E → EReal` is `g*(y) = inf_x (⟨x, y⟩ - g x)`, the mirror of the
convex conjugate with `inf`, `≥` and `-∞` in place of `sup`, `≤` and `+∞`. Convex and concave
duality are used together throughout — the dual objective of a convex program is the concave
conjugate of `-inf F`, and Fenchel's duality theorem pairs a convex `f` against a concave `g` — so
the concave conjugate needs a name of its own rather than being spelled through `-g` at every use.

**The sign trap.** `g* ≠ -(-g)*`. What is true is `g*(y) = -(-g)*(-y)`: there is a reflection on
the *dual* side as well. `neg_concaveConj` is the dictionary, and every result below is derived
through it.

## Main definitions

* `concaveConj B g`, `biconcaveConj B g` — the concave conjugate `g*` and biconjugate `g**`.
* `clConcave g`, `ClosedConcaveFn g` — the **concave closure** `-(cl (-g))`, the upper
  semicontinuous hull that Rockafellar also writes `cl g`, and the functions fixed by it.

## Main results

* `neg_concaveConj`, `concaveConj_eq_neg_conj_neg`, `conj_eq_neg_concaveConj_neg` — the sign
  dictionary, in both directions, with no side condition.
* `add_concaveConj_le` — **Fenchel's inequality** `g x + g*(y) ≤ ⟨x, y⟩`. Unconditional, unlike
  the convex `le_add_conj`: the collapsing sum `⊤ + ⊥ = ⊥` falls on the *smaller* side here.
* `coe_le_concaveConj_iff`, `le_concaveConj_iff` — `c ≤ g*(y)` says exactly that the affine
  function `x ↦ ⟨x, y⟩ - c` lies *above* `g`; and `concaveConj B` is adjoint to
  `concaveConj B.flip`. Every concave conjugate is concave (`concaveFn_concaveConj`).
* `biconcaveConj_eq_clConcave` — **Fenchel–Moreau for concave functions**: the concave
  biconjugate is the concave closure. The double reflection cancels on the way
  (`biconcaveConj_eq_neg_biconj_neg`: `g** = -(-g)**`, with no sign on the argument).

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §12, §30, §31.
-/

namespace ConvexAnalysis

/-! ### The concave conjugate -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **concave conjugate** of `g` with respect to the pairing `B`:
`g*(y) = inf_x (⟨x, y⟩ - g x)`. This is *not* `-(conj B (-g))`; the dictionary
`g*(y) = -(-g)*(-y)` is `concaveConj_eq_neg_conj_neg`. -/
noncomputable def concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : F → EReal :=
  fun y => ⨅ x : E, ((B x y : ℝ) : EReal) - g x

noncomputable abbrev biconcaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : E → EReal :=
  concaveConj B.flip (concaveConj B g)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : E → EReal} {x : E} {y : F} {c : ℝ}

theorem concaveConj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    concaveConj B g y = ⨅ x : E, ((B x y : ℝ) : EReal) - g x := rfl

theorem biconcaveConj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) :
    biconcaveConj B g x = ⨅ y : F, ((B x y : ℝ) : EReal) - concaveConj B g y := rfl

/-- **Fenchel's inequality for concave functions**, `∞ - ∞`-free: it holds for every `g`, `x`
and `y`. -/
theorem concaveConj_le_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) (y : F) :
    concaveConj B g y ≤ ((B x y : ℝ) : EReal) - g x :=
  iInf_le _ x

/-! ### The sign dictionary -/

/-- **The dictionary between the two conjugates**: `-g*(y) = (-g)*(-y)`. Both the values and the
arguments are reflected; only one of the two reflections is visible in the informal statement
`g*(y) = -(-g)*(-y)`. -/
theorem neg_concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    -(concaveConj B g y) = conj B (fun x => -(g x)) (-y) := by
  rw [concaveConj_apply, EReal.neg_iInf, conj_apply]
  refine iSup_congr fun x => ?_
  have hB : ((B x (-y) : ℝ) : EReal) = -((B x y : ℝ) : EReal) := by
    rw [map_neg, _root_.EReal.coe_neg]
  rw [hB]
  simp only [sub_eq_add_neg]
  rw [_root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _)) (.inl (_root_.EReal.coe_ne_top _))]
  rfl

/-- The dictionary, solved for the concave conjugate: `g*(y) = -(-g)*(-y)`. -/
theorem concaveConj_eq_neg_conj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    concaveConj B g y = -(conj B (fun x => -(g x)) (-y)) := by
  rw [← neg_concaveConj, neg_neg]

/-- The dictionary in the other direction: `f*(y) = -(-f)*(-y)`, where the starred operation on the
right is the *concave* conjugate. -/
theorem conj_eq_neg_concaveConj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    conj B f y = -(concaveConj B (fun x => -(f x)) (-y)) := by
  rw [neg_concaveConj, neg_neg]
  simp only [neg_neg]

/-! ### Order-theoretic API -/

/-- `c ≤ g*(y)` says exactly that the affine function `x ↦ ⟨x, y⟩ - c` lies *above* `g`. The
mirror of `conj_le_coe_iff`, and like it unconditional. -/
theorem coe_le_concaveConj_iff : (c : EReal) ≤ concaveConj B g y ↔ g ≤ affineFn B y c := by
  rw [concaveConj_apply, le_iInf_iff]
  exact forall_congr' fun x => EReal.le_coe_sub_comm

theorem concaveConj_antitone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Antitone (concaveConj B) := fun _ _ hgh _ =>
  le_iInf fun x => (iInf_le _ x).trans (_root_.EReal.sub_le_sub le_rfl (hgh x))

/-- **The adjunction.** `h ≤ g*` and `g ≤ h*` say the same thing, namely that
`g x + h y ≤ ⟨x, y⟩` for all `x` and `y` in the `∞ - ∞`-free reading. -/
theorem le_concaveConj_iff {h : F → EReal} :
    h ≤ concaveConj B g ↔ g ≤ concaveConj B.flip h := by
  simp only [Pi.le_def, concaveConj_apply, le_iInf_iff, LinearMap.flip_apply]
  rw [forall_comm]
  exact forall₂_congr fun _ _ => EReal.le_coe_sub_comm

/-- The biconjugate is always a majorant: `g ≤ g**`, with no hypothesis on `g`. -/
theorem le_biconcaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : g ≤ biconcaveConj B g :=
  le_concaveConj_iff.1 le_rfl

/-! ### The improper cases -/

/-- `g*` takes the value `⊤` at a point exactly when `g ≡ -∞` — a condition independent of the
point. -/
theorem concaveConj_eq_top_iff : concaveConj B g y = ⊤ ↔ ∀ x, g x = ⊥ := by
  rw [concaveConj_eq_neg_conj_neg, _root_.EReal.neg_eq_top_iff, conj_eq_bot_iff]
  exact forall_congr' fun _ => _root_.EReal.neg_eq_top_iff

/-- **If `g` takes the value `+∞` anywhere, its concave conjugate is identically `-∞`.** -/
theorem concaveConj_of_eq_top {x₀ : E} (hx : g x₀ = ⊤) : concaveConj B g = fun _ => ⊥ := by
  funext y
  rw [concaveConj_eq_neg_conj_neg, conj_of_eq_bot (x₀ := x₀) (by rw [hx, _root_.EReal.neg_top]),
    _root_.EReal.neg_top]

theorem concaveConj_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    concaveConj B (fun _ => ⊥) = fun _ => (⊤ : EReal) :=
  funext fun _ => concaveConj_eq_top_iff.2 fun _ => rfl

theorem concaveConj_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    concaveConj B (fun _ => ⊤) = fun _ => (⊥ : EReal) :=
  concaveConj_of_eq_top (x₀ := (0 : E)) rfl

/-- `g*` never takes the value `⊤` when `g` has nonempty effective domain. -/
theorem concaveConj_ne_top (hd : (domConcave g).Nonempty) (y : F) : concaveConj B g y ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hd
  exact fun hc => absurd (concaveConj_eq_top_iff.1 hc x) hx.ne'

/-- **Fenchel's inequality for concave functions**: `g x + g*(y) ≤ ⟨x, y⟩`.

Needs no properness, unlike its convex mirror `le_add_conj`: the collapse `⊤ + ⊥ = ⊥` happens here
on the smaller side of the inequality, where `⊥` is harmless. -/
theorem add_concaveConj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) (y : F) :
    g x + concaveConj B g y ≤ ((B x y : ℝ) : EReal) := by
  rw [add_comm]
  exact (_root_.EReal.le_sub_iff_add_le (.inr (_root_.EReal.coe_ne_bot _))
    (.inr (_root_.EReal.coe_ne_top _))).1 (concaveConj_le_sub B g x y)

/-! ### Concavity of the concave conjugate -/

/-- **The concave conjugate of an arbitrary function is concave**, with no hypothesis on `g`. -/
theorem concaveFn_concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) :
    ConcaveFn (concaveConj B g) := by
  rw [concaveFn_iff_convexFn_neg]
  have hrw : (fun y => -(concaveConj B g y)) = compLin (conj B fun x => -(g x)) (-LinearMap.id) :=
    funext fun y => neg_concaveConj B g y
  rw [hrw]
  exact convexFn_compLin _ (convexFn_conj B _)

/-! ### The biconjugate -/

/-- **The double reflection cancels**: `g** = -(-g)**`, with no sign on the argument, the
reflection introduced on the dual side by the first conjugation being undone by the second. -/
theorem biconcaveConj_eq_neg_biconj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) :
    biconcaveConj B g x = -(biconj B (fun x' => -(g x')) x) := by
  have key : ∀ y : F, ((B x (-y) : ℝ) : EReal) - concaveConj B g (-y)
      = -(((B x y : ℝ) : EReal) - conj B (fun x' => -(g x')) y) := fun y => by
    rw [concaveConj_eq_neg_conj_neg, neg_neg, map_neg, _root_.EReal.coe_neg]
    simp only [sub_eq_add_neg]
    rw [_root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _))
      (.inl (_root_.EReal.coe_ne_top _))]
    rfl
  rw [biconcaveConj_apply, biconj_apply, EReal.neg_iSup]
  refine le_antisymm (le_iInf fun y => ?_) (le_iInf fun y => ?_)
  · exact (iInf_le _ (-y)).trans (key y).le
  · refine (iInf_le _ (-y)).trans (le_of_eq ?_)
    have hy := key (-y)
    rw [neg_neg] at hy
    exact hy.symm

end Defs

/-! ### The concave closure -/

section Closure

variable {E : Type*} [TopologicalSpace E] {g : E → EReal}

/-- The **concave closure**: the counterpart of `clFn` obtained by conjugating it with negation.
Rockafellar writes `cl g` for it too; here it needs a name of its own. -/
noncomputable def clConcave (g : E → EReal) : E → EReal := fun x => -(clFn (fun z => -(g z)) x)

theorem clConcave_apply (g : E → EReal) (x : E) :
    clConcave g x = -(clFn (fun z => -(g z)) x) := rfl

@[simp] theorem neg_clConcave (g : E → EReal) (x : E) :
    -(clConcave g x) = clFn (fun z => -(g z)) x := neg_neg _

theorem clConcave_neg (f : E → EReal) (x : E) : clConcave (fun z => -(f z)) x = -(clFn f x) := by
  rw [clConcave_apply]
  simp only [neg_neg]

theorem clConcave_mono {g₁ g₂ : E → EReal} (h : g₁ ≤ g₂) : clConcave g₁ ≤ clConcave g₂ := by
  intro x
  rw [clConcave_apply, clConcave_apply, _root_.EReal.neg_le_neg_iff]
  exact clFn_mono (fun z => _root_.EReal.neg_le_neg_iff.2 (h z)) x

/-- `g` is **concave-closed** when it equals its concave closure. -/
def ClosedConcaveFn (g : E → EReal) : Prop := clConcave g = g

theorem closedConcaveFn_iff : ClosedConcaveFn g ↔ ClosedFn (fun z => -(g z)) := by
  constructor
  · intro h
    funext x
    rw [← neg_clConcave g x, h]
  · intro h
    funext x
    rw [clConcave_apply, congrFun h x, neg_neg]

theorem le_clConcave (g : E → EReal) : g ≤ clConcave g := by
  intro x
  rw [← _root_.EReal.neg_le_neg_iff, neg_clConcave]
  exact clFn_le _ x

end Closure

section ClosureIdem

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]

theorem closedConcaveFn_clConcave (g : E → EReal) : ClosedConcaveFn (clConcave g) := by
  rw [closedConcaveFn_iff]
  simpa only [neg_clConcave] using closedFn_clFn (fun z => -(g z))

theorem clConcave_idem (g : E → EReal) : clConcave (clConcave g) = clConcave g :=
  closedConcaveFn_clConcave g

end ClosureIdem

section ClosureConcave

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {g : E → EReal}

theorem concaveFn_clConcave (hg : ConcaveFn g) : ConcaveFn (clConcave g) := by
  rw [concaveFn_iff_convexFn_neg]
  simpa only [neg_clConcave] using convexFn_clFn hg.convexFn_neg

end ClosureConcave

/-! ### Fenchel–Moreau for concave functions -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {g : E → EReal}

/-- **Fenchel–Moreau for concave functions.** The concave biconjugate of a concave function is
its concave closure, spelled out as `-(cl (-g))`. -/
theorem biconcaveConj_eq_neg_clFn_neg (hg : ConcaveFn g) :
    biconcaveConj B g = fun x => -(clFn (fun x' => -(g x')) x) := by
  funext x
  rw [biconcaveConj_eq_neg_biconj_neg, biconj_eq_clFn hg.convexFn_neg]

/-- **Fenchel–Moreau for concave functions**, stated against `clConcave`: `g** = cl g`. -/
theorem biconcaveConj_eq_clConcave (hg : ConcaveFn g) : biconcaveConj B g = clConcave g :=
  biconcaveConj_eq_neg_clFn_neg hg

/-- A closed concave function — one whose negative is a closed convex function — is its own
concave biconjugate. -/
theorem biconcaveConj_eq_self (hg : ConcaveFn g) (hc : ClosedFn fun x => -(g x)) :
    biconcaveConj B g = g := by
  rw [biconcaveConj_eq_neg_clFn_neg hg, hc]
  exact funext fun x => neg_neg (g x)

end FenchelMoreau

end ConvexAnalysis
