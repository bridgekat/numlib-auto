import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Order.GaloisConnection

/-!
# Conjugates of convex and concave functions

The **conjugate** of `f : E → EReal` with respect to a pairing `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ` is
`f*(y) = sup_x (⟨x, y⟩ - f x)`. Read through epigraphs, `f*` is a description of the affine
minorants of `f`: `f*(y) ≤ c` says exactly that `x ↦ ⟨x, y⟩ - c` lies below `f`. It is defined for
an arbitrary `f`, and is always a closed convex function. The theorem the rest of the library rests
on is **Fenchel–Moreau**, `f** = cl f` for convex `f`: conjugacy is an involution on the closed
convex functions, and a closed convex function is the pointwise supremum of the affine functions
below it.

The **concave conjugate** `g*(y) = inf_x (⟨x, y⟩ - g x)` is the mirror, with `inf`, `≥` and `-∞`
in place of `sup`, `≤` and `+∞`. Convex and concave duality are used together throughout — the dual
objective of a convex program is the concave conjugate of `-inf F`, and Fenchel's duality theorem
pairs a convex `f` against a concave `g` — so each concave statement sits right after its convex
twin, derived through the sign dictionary `neg_concaveConj`.

## Main definitions

* `convexConj B f`, `convexBiconj B f` — the conjugate `f*` and biconjugate `f**`;
  `concaveConj B g`, `concaveBiconj B g` — their concave twins.
* `convexConjClosure B` — conjugacy as a `ClosureOperator` on `(E → EReal)ᵒᵈ`, whose closed elements
  are exactly the closed convex functions.
* `convexConjEquiv` — conjugacy as an involution on the closed proper convex functions.

## Main results

* `neg_concaveConj`, `concaveConj_eq_neg_convexConj_neg`, `convexConj_eq_neg_concaveConj_neg` — the
  sign dictionary between the two conjugates, with no side condition.
* `sub_le_convexConj`, `convexConj_le_coe_iff`, `convexConj_le_iff` — the unconditional forms of
  Fenchel's inequality. The last says that `convexConj B` and `convexConj B.flip` are an antitone
  Galois connection.
* `le_add_convexConj` — **Fenchel's inequality** `⟨x, y⟩ ≤ f x + f* y`. In `EReal` this needs
  `ProperConvex f`, and the hypothesis is not removable; see the implementation notes.
* `convexFn_convexConj`, `closedConvex_convexConj` — the conjugate of an arbitrary function is
  closed and convex.
* `convexConj_convexCl` — `(cl f)* = f*`: closure does not change the conjugate.
* `exists_affineFn_le_of_lt`, `eq_biSup_affineFn` — a closed convex function is the pointwise
  supremum of the affine functions below it.
* `convexBiconj_eq_convexCl` — the **Fenchel–Moreau theorem**: `f** = cl f` for convex `f`, and
  `concaveBiconj_eq_concaveCl` for concave `g`;
  `properConvex_convexConj_iff` is its properness half. `convexBiconj_eq_convexCl_topDual` and
  `convexBiconj_eq_convexCl_inner` discharge every hypothesis, for a locally convex space paired
  with its own continuous dual and for a real Hilbert space paired with itself, both in the space's
  *own* topology.
* `gc_convexConj_convexConj`, `convexConjClosure`, `convexConjOrderIso` — the Galois connection, the
  closure operator it induces, and the order anti-isomorphism between the biconjugation-fixed
  functions.
* `convexConj_comp_sub`, `convexConj_comp_add`, `convexConj_add_pairing`, `convexConj_sub_pairing`,
  `convexConj_add_const`, `convexConj_comp_linearEquiv` — the four elementary rows (translation,
  tilting, an added constant, an invertible substitution), with `convexConj_comp_affine` composing
  them ([rockafellar1970convex] Theorem 12.3).

## Implementation notes

Fenchel–Moreau does not care which topology `E` carries, so long as its continuous dual is the `F`
side of the pairing: that is `IsCompatiblePairing B`. Its weaker companion `IsContinuousPairing`,
asking only that every `⟨·, y⟩` be continuous, is all the closedness half of this file needs —
`closedConvex_convexConj`, `convexConj_convexCl`, `convexBiconj_le_convexCl` — which matters because
a Banach space paired with its norm-topology dual is continuous on both sides but compatible only if
it is reflexive.

## References

* [rockafellar1970convex] §12.
-/

open Set OrderDual

namespace ConvexAnalysis

/-! ### The conjugate -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **convex conjugate** of `f` with respect to the pairing `B`:
`f*(y) = sup_x (⟨x, y⟩ - f x)`. `epi f*` is the set of pairs `(y, c)` for which the affine function
`x ↦ ⟨x, y⟩ - c` is majorized by `f`. No hypothesis is placed on `f`. -/
noncomputable def convexConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨆ x : E, ((B x y : ℝ) : EReal) - f x

/-- The **biconjugate**, back on `E`. Using `B.flip` rather than a second copy of `B` makes the
correspondence symmetric with no reflexivity assumption; `B.flip.flip = B` holds by `rfl`. -/
noncomputable abbrev convexBiconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : E → EReal :=
  convexConj B.flip (convexConj B f)

/-- The **concave conjugate** of `g` with respect to the pairing `B`:
`g*(y) = inf_x (⟨x, y⟩ - g x)`, the mirror of `convexConj` with `inf` in place of `sup`. This is
*not* `-(convexConj B (-g))`; the dictionary `g*(y) = -(-g)*(-y)` is
`concaveConj_eq_neg_convexConj_neg`. -/
noncomputable def concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : F → EReal :=
  fun y => ⨅ x : E, ((B x y : ℝ) : EReal) - g x

/-- The concave biconjugate: the concave conjugate against `B`, then against `B.flip`. -/
noncomputable abbrev concaveBiconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : E → EReal :=
  concaveConj B.flip (concaveConj B g)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {x : E} {y : F} {c : ℝ}

theorem convexConj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    convexConj B f y = ⨆ x : E, ((B x y : ℝ) : EReal) - f x := rfl

theorem convexBiconj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    convexBiconj B f x = ⨆ y : F, ((B x y : ℝ) : EReal) - convexConj B f y := rfl

theorem concaveConj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    concaveConj B g y = ⨅ x : E, ((B x y : ℝ) : EReal) - g x := rfl

theorem concaveBiconj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) :
    concaveBiconj B g x = ⨅ y : F, ((B x y : ℝ) : EReal) - concaveConj B g y := rfl

/-! #### The sign dictionary

**The sign trap.** `g* ≠ -(-g)*`. What is true is `g*(y) = -(-g)*(-y)`: there is a reflection on
the *dual* side as well. The order-theoretic lemmas below are two lines each whether proved
directly or through the dictionary, and are proved directly; the others go through it. -/

/-- **The dictionary between the two conjugates**: `-g*(y) = (-g)*(-y)`. Both the values and the
arguments are reflected; only one of the two reflections is visible in the informal statement
`g*(y) = -(-g)*(-y)`. -/
theorem neg_concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    -(concaveConj B g y) = convexConj B (fun x => -(g x)) (-y) := by
  rw [concaveConj_apply, EReal.neg_iInf, convexConj_apply]
  refine iSup_congr fun x => ?_
  have hB : ((B x (-y) : ℝ) : EReal) = -((B x y : ℝ) : EReal) := by
    rw [map_neg, EReal.coe_neg]
  rw [hB]
  simp only [sub_eq_add_neg]
  rw [EReal.neg_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
  rfl

/-- The dictionary, solved for the concave conjugate: `g*(y) = -(-g)*(-y)`. -/
theorem concaveConj_eq_neg_convexConj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    concaveConj B g y = -(convexConj B (fun x => -(g x)) (-y)) := by
  rw [← neg_concaveConj, neg_neg]

/-- The dictionary in the other direction: `f*(y) = -(-f)*(-y)`, where the starred operation on the
right is the *concave* conjugate. -/
theorem convexConj_eq_neg_concaveConj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    convexConj B f y = -(concaveConj B (fun x => -(f x)) (-y)) := by
  rw [neg_concaveConj, neg_neg]
  simp only [neg_neg]

/-! #### Fenchel's inequality and the adjunction -/

/-- **Fenchel's inequality, `∞ - ∞`-free**: it holds for every `f`, `x` and `y`, and it is the
form the proofs below use rather than the additive `le_add_convexConj`. -/
theorem sub_le_convexConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) (y : F) :
    ((B x y : ℝ) : EReal) - f x ≤ convexConj B f y :=
  le_iSup (fun x : E => ((B x y : ℝ) : EReal) - f x) x

/-- **Fenchel's inequality for concave functions**, `∞ - ∞`-free: it holds for every `g`, `x`
and `y`. -/
theorem concaveConj_le_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) (y : F) :
    concaveConj B g y ≤ ((B x y : ℝ) : EReal) - g x :=
  iInf_le _ x

/-- `f*(y) ≤ c` says exactly that the affine function `x ↦ ⟨x, y⟩ - c` lies below `f`. -/
theorem convexConj_le_coe_iff : convexConj B f y ≤ (c : EReal) ↔ affineFn B y c ≤ f := by
  rw [convexConj_apply, iSup_le_iff, affineFn_le_iff]

/-- `c ≤ g*(y)` says exactly that the affine function `x ↦ ⟨x, y⟩ - c` lies *above* `g`. The
mirror of `convexConj_le_coe_iff`, and like it unconditional. -/
theorem coe_le_concaveConj_iff : (c : EReal) ≤ concaveConj B g y ↔ g ≤ affineFn B y c := by
  rw [concaveConj_apply, le_iInf_iff]
  exact forall_congr' fun x => EReal.le_coe_sub_comm

theorem convexConj_antitone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Antitone (convexConj B) := fun _ _ h _ =>
  iSup_mono fun x => EReal.sub_le_sub le_rfl (h x)

theorem concaveConj_antitone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Antitone (concaveConj B) := fun _ _ hgh _ =>
  le_iInf fun x => (iInf_le _ x).trans (EReal.sub_le_sub le_rfl (hgh x))

/-- **The adjunction.** `f* ≤ g` and `g* ≤ f` say the same thing — that `⟨x, y⟩ ≤ f x + g y` for
all `x` and `y`, in the `∞ - ∞`-free reading. -/
theorem convexConj_le_iff {g : F → EReal} : convexConj B f ≤ g ↔ convexConj B.flip g ≤ f := by
  simp only [Pi.le_def, convexConj_apply, iSup_le_iff, LinearMap.flip_apply]
  rw [forall_comm]
  exact forall₂_congr fun _ _ => EReal.coe_sub_le_comm

/-- **The concave adjunction.** `h ≤ g*` and `g ≤ h*` say the same thing, namely that
`g x + h y ≤ ⟨x, y⟩` for all `x` and `y` in the `∞ - ∞`-free reading. -/
theorem le_concaveConj_iff {h : F → EReal} :
    h ≤ concaveConj B g ↔ g ≤ concaveConj B.flip h := by
  simp only [Pi.le_def, concaveConj_apply, le_iInf_iff, LinearMap.flip_apply]
  rw [forall_comm]
  exact forall₂_congr fun _ _ => EReal.le_coe_sub_comm

theorem convexBiconj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : convexBiconj B f ≤ f :=
  convexConj_le_iff.1 le_rfl

/-- The concave biconjugate is always a majorant: `g ≤ g**`, with no hypothesis on `g`. -/
theorem le_concaveBiconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : g ≤ concaveBiconj B g :=
  le_concaveConj_iff.1 le_rfl

/-! ### The improper cases -/

/-- `f*` takes the value `⊥` at a point exactly when `f ≡ ⊤` — a condition independent of the
point. So `f*` is either the constant `⊥` or never `⊥`, which is why it is always *closed*. -/
theorem convexConj_eq_bot_iff : convexConj B f y = ⊥ ↔ ∀ x, f x = ⊤ := by
  rw [convexConj_apply, iSup_eq_bot]
  exact forall_congr' fun _ => EReal.coe_sub_eq_bot_iff

/-- `g*` takes the value `⊤` at a point exactly when `g ≡ -∞` — a condition independent of the
point. -/
theorem concaveConj_eq_top_iff : concaveConj B g y = ⊤ ↔ ∀ x, g x = ⊥ := by
  rw [concaveConj_eq_neg_convexConj_neg, EReal.neg_eq_top_iff, convexConj_eq_bot_iff]
  exact forall_congr' fun _ => EReal.neg_eq_top_iff

/-- **If `f` takes the value `⊥` anywhere, its conjugate is identically `⊤`.** -/
theorem convexConj_of_eq_bot {x₀ : E} (h : f x₀ = ⊥) : convexConj B f = fun _ => ⊤ := by
  funext y
  refine top_le_iff.1 (le_trans ?_ (sub_le_convexConj B f x₀ y))
  rw [h, EReal.coe_sub_bot]

/-- **If `g` takes the value `+∞` anywhere, its concave conjugate is identically `-∞`.** -/
theorem concaveConj_of_eq_top {x₀ : E} (hx : g x₀ = ⊤) : concaveConj B g = fun _ => ⊥ := by
  funext y
  rw [concaveConj_eq_neg_convexConj_neg, convexConj_of_eq_bot
      (x₀ := x₀) (by rw [hx, EReal.neg_top]),
    EReal.neg_top]

theorem convexConj_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : convexConj B (fun _ => ⊤) = fun _ => (⊥ : EReal) :=
  funext fun _ => convexConj_eq_bot_iff.2 fun _ => rfl

theorem concaveConj_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    concaveConj B (fun _ => ⊥) = fun _ => (⊤ : EReal) :=
  funext fun _ => concaveConj_eq_top_iff.2 fun _ => rfl

theorem convexConj_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : convexConj B (fun _ => ⊥) = fun _ => (⊤ : EReal) :=
  convexConj_of_eq_bot (x₀ := (0 : E)) rfl

theorem concaveConj_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    concaveConj B (fun _ => ⊤) = fun _ => (⊥ : EReal) :=
  concaveConj_of_eq_top (x₀ := (0 : E)) rfl

theorem convexConj_ne_bot (h : (convexDom f).Nonempty) (y : F) : convexConj B f y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := h
  exact fun hc => absurd (convexConj_eq_bot_iff.1 hc x) hx.ne

/-- `g*` never takes the value `⊤` when `g` has nonempty effective domain. -/
theorem concaveConj_ne_top (hd : (concaveDom g).Nonempty) (y : F) : concaveConj B g y ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hd
  exact fun hc => absurd (concaveConj_eq_top_iff.1 hc x) hx.ne'

/-- **Fenchel's inequality**: `⟨x, y⟩ ≤ f x + f*(y)` for a proper `f`.

Properness is not decorative: if `f ≡ +∞` then `f* ≡ -∞` and the right-hand side is `⊤ + ⊥ = ⊥`,
and if `f` takes `-∞` then it is `⊥ + ⊤ = ⊥`. Use `sub_le_convexConj` when properness is
unavailable. -/
theorem le_add_convexConj (hb : f x ≠ ⊥) (hd : (convexDom f).Nonempty) (y : F) :
    ((B x y : ℝ) : EReal) ≤ f x + convexConj B f y := by
  rw [add_comm]
  exact (EReal.sub_le_iff_le_add (.inl hb) (.inr (convexConj_ne_bot hd y))).1
      (sub_le_convexConj B f x y)

theorem ProperConvex.le_add_convexConj (hp : ProperConvex f) (x : E) (y : F) :
    ((B x y : ℝ) : EReal) ≤ f x + convexConj B f y :=
  _root_.ConvexAnalysis.le_add_convexConj (hp.ne_bot x) hp.convexDom_nonempty y

/-- **Fenchel's inequality for concave functions**: `g x + g*(y) ≤ ⟨x, y⟩`.

Needs no properness, unlike its convex mirror `le_add_convexConj`: the collapse `⊤ + ⊥ = ⊥` happens
here on the smaller side of the inequality, where `⊥` is harmless. -/
theorem add_concaveConj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) (y : F) :
    g x + concaveConj B g y ≤ ((B x y : ℝ) : EReal) := by
  rw [add_comm]
  exact (EReal.le_sub_iff_add_le (.inr (EReal.coe_ne_bot _))
    (.inr (EReal.coe_ne_top _))).1 (concaveConj_le_sub B g x y)

/-- If the conjugate is proper then so is the original function; no hypothesis is needed for this
direction. The converse is `properConvex_convexConj`, and needs closedness. -/
theorem properConvex_of_properConvex_convexConj
    (h : ProperConvex (convexConj B f)) : ProperConvex f := by
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := h.convexDom_nonempty
    by_contra hd
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
    exact absurd (convexConj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x))) (h.ne_bot y)
  · obtain ⟨y, hy⟩ := h.convexDom_nonempty
    rw [convexConj_of_eq_bot hx] at hy
    exact absurd hy (by simp)

/-! ### Convexity of the conjugate -/

/-- The `x`-th term of the supremum defining `f*` is, as a function of `y`, either constant or one
of the affine functions of the flipped pairing, according to the value of `f x`. -/
theorem convexConj_term_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    (fun y => ((B x y : ℝ) : EReal) - f x) = (fun _ => (⊥ : EReal)) ∨
      (fun y => ((B x y : ℝ) : EReal) - f x) = (fun _ => (⊤ : EReal)) ∨
      ∃ t : ℝ, (fun y => ((B x y : ℝ) : EReal) - f x) = affineFn B.flip x t := by
  rcases eq_or_ne (f x) ⊤ with h | h
  · exact Or.inl (funext fun y => by rw [h, EReal.sub_top])
  rcases eq_or_ne (f x) ⊥ with h' | h'
  · exact Or.inr (Or.inl (funext fun y => by rw [h', EReal.coe_sub_bot]))
  · obtain ⟨t, ht⟩ := EReal.exists_coe_of_ne_bot_of_lt_top h' (lt_top_iff_ne_top.2 h)
    exact Or.inr (Or.inr ⟨t, funext fun y => by rw [ht, affineFn_apply, LinearMap.flip_apply]⟩)

/-- **The conjugate of an arbitrary function is convex**: a pointwise supremum of affine functions
and constants. -/
theorem convexFn_convexConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (f : E → EReal) : ConvexFn (convexConj B f) := by
  refine convexFn_iSup fun x => ?_
  rcases convexConj_term_eq B f x with h | h | ⟨t, h⟩ <;> rw [h]
  · exact convexFn_const ⊥
  · exact convexFn_const ⊤
  · exact convexFn_affineFn x t

/-- **The concave conjugate of an arbitrary function is concave**, with no hypothesis on `g`. -/
theorem concaveFn_concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) :
    ConcaveFn (concaveConj B g) := by
  rw [concaveFn_iff_convexFn_neg]
  have hrw : (fun y => -(concaveConj B g y))
      = compLin (convexConj B fun x => -(g x)) (-LinearMap.id) :=
    funext fun y => neg_concaveConj B g y
  rw [hrw]
  exact convexFn_compLin _ (convexFn_convexConj B _)

/-! ### The concave biconjugate -/

/-- **The double reflection cancels**: `g** = -(-g)**`, with no sign on the argument, the
reflection introduced on the dual side by the first conjugation being undone by the second. -/
theorem concaveBiconj_eq_neg_convexBiconj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) :
    concaveBiconj B g x = -(convexBiconj B (fun x' => -(g x')) x) := by
  have key : ∀ y : F, ((B x (-y) : ℝ) : EReal) - concaveConj B g (-y)
      = -(((B x y : ℝ) : EReal) - convexConj B (fun x' => -(g x')) y) := fun y => by
    rw [concaveConj_eq_neg_convexConj_neg, neg_neg, map_neg, EReal.coe_neg]
    simp only [sub_eq_add_neg]
    rw [EReal.neg_add (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))]
    rfl
  rw [concaveBiconj_apply, convexBiconj_apply, EReal.neg_iSup]
  refine le_antisymm (le_iInf fun y => ?_) (le_iInf fun y => ?_)
  · exact (iInf_le _ (-y)).trans (key y).le
  · refine (iInf_le _ (-y)).trans (le_of_eq ?_)
    have hy := key (-y)
    rw [neg_neg] at hy
    exact hy.symm

end Defs

/-! ### Why Fenchel's inequality needs properness

In `EReal` the value `⊥` is absorbing for addition, so `⊤ + ⊥ = ⊥ + ⊤ = ⊥` and the additive form of
Fenchel's inequality collapses at each of the two improper functions. -/

example : ¬ (((innerₗ ℝ) (0 : ℝ) (0 : ℝ) : ℝ) : EReal)
    ≤ (fun _ : ℝ => (⊤ : EReal)) 0 + convexConj (innerₗ ℝ) (fun _ : ℝ => (⊤ : EReal)) 0 := by
  rw [convexConj_top]
  simp

example : ¬ (((innerₗ ℝ) (0 : ℝ) (0 : ℝ) : ℝ) : EReal)
    ≤ (fun _ : ℝ => (⊥ : EReal)) 0 + convexConj (innerₗ ℝ) (fun _ : ℝ => (⊥ : EReal)) 0 := by
  rw [convexConj_bot]
  simp

/-! ### Closedness of the conjugate

The conjugate is closed in *any* topology on `F` for which the pairing is continuous — in
particular in `σ(F, E)`, hence also in the norm topology of a normed space paired with its dual. -/

section ConjClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {f : E → EReal}

theorem lowerSemicontinuous_convexConj : LowerSemicontinuous (convexConj B f) := by
  refine lowerSemicontinuous_iSup fun x => ?_
  rcases convexConj_term_eq B f x with h | h | ⟨t, h⟩ <;> rw [h]
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_affineFn (continuous_pairing B.flip x)

variable [IsTopologicalAddGroup F]

/-- **The conjugate is a closed convex function**, with no hypothesis on `f`: if `f ≡ +∞` it is
the constant `⊥`, and otherwise it is lower semicontinuous and never takes `⊥`. -/
theorem closedConvex_convexConj : ClosedConvex (convexConj B f) := by
  rw [closedConvex_iff]
  by_cases h : ∀ x, f x = ⊤
  · exact Or.inl (funext fun _ => convexConj_eq_bot_iff.2 h)
  · exact Or.inr ⟨lowerSemicontinuous_convexConj, fun _ hy => h (convexConj_eq_bot_iff.1 hy)⟩

/-- **The concave conjugate of an arbitrary function is concave-closed**, the mirror of
`closedConvex_convexConj`: `-g*` is `(-g)*` reflected by the continuous map `y ↦ -y`. -/
theorem closedConcave_concaveConj (g : E → EReal) : ClosedConcave (concaveConj B g) := by
  rw [closedConcave_iff_closedConvex_neg]
  have hrw : (fun y => -(concaveConj B g y))
      = compLin (convexConj B fun x => -(g x)) (-LinearMap.id) :=
    funext fun y => neg_concaveConj B g y
  rw [hrw]
  exact closedConvex_compLin closedConvex_convexConj
    ((continuous_neg : Continuous fun y : F => -y).congr fun _ => rfl)

end ConjClosed

/-! ### The conjugate sees only the closure -/

section ConjClosure

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  [IsContinuousPairing B] {f : E → EReal}

/-- **Closure does not change the conjugate**: `(cl f)* = f*`. The affine functions below `f` and
below `cl f` are the same, because an affine function of a continuous pairing is itself closed. -/
theorem convexConj_convexCl (f : E → EReal) : convexConj B (convexCl f) = convexConj B f := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, convexConj_le_coe_iff]
  exact ⟨fun h => h.trans (convexCl_le f),
    fun h => le_convexCl_of_le (closedConvex_affineFn (continuous_pairing B y)) h⟩

/-- **The concave conjugate sees only the concave closure**: `(cl g)* = g*`. This is
`convexConj_convexCl` read through the sign dictionary. -/
theorem concaveConj_concaveCl (g : E → EReal) :
    concaveConj B (concaveCl g) = concaveConj B g := by
  funext y
  rw [concaveConj_eq_neg_convexConj_neg, concaveConj_eq_neg_convexConj_neg]
  have h : (fun x => -(concaveCl g x)) = convexCl fun z => -(g z) := funext (neg_concaveCl g)
  rw [h, convexConj_convexCl]

/-- The biconjugate is a closed convex minorant of `f`, hence a minorant of `cl f`: the easy half
of Fenchel–Moreau, needing no convexity. -/
theorem convexBiconj_le_convexCl (f : E → EReal) : convexBiconj B f ≤ convexCl f :=
  le_convexCl_of_le (closedConvex_convexConj (B := B.flip)) (convexBiconj_le B f)

end ConjClosure

/-! ### Affine minorants of a closed convex function -/

section AffineMinorants

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The affine-minorant lemma**, in its working form: below any value strictly under a closed
convex function there is an affine minorant of the pairing. -/
theorem exists_affineFn_le_of_lt (hf : ConvexFn f) (hc : ClosedConvex f) {x₀ : E} {α : ℝ}
    (h : (α : EReal) < f x₀) :
    ∃ (y : F) (c : ℝ), affineFn B y c ≤ f ∧ (α : EReal) < affineFn B y c x₀ := by
  by_cases hp : ProperConvex f
  case neg =>
    -- A closed improper function is constant; `f ≡ -∞` contradicts `α < f x₀`, and every affine
    -- function lies below `f ≡ +∞`.
    rcases eq_const_of_closedConvex_of_not_properConvex hc hp with hbot | htop
    · rw [hbot] at h; exact absurd h (by simp)
    · refine ⟨0, -(α + 1), htop ▸ fun _ => le_top, ?_⟩
      rw [affineFn_eq_coe, map_zero, EReal.coe_lt_coe_iff]
      linarith
  case pos =>
  -- A point of the epigraph over any point of the effective domain.
  have hmem : ∀ x, f x < ⊤ → ∃ μ : ℝ, (x, μ) ∈ epi f := by
    intro x hx
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    exact ⟨r, by rw [mk_mem_epi, hr]⟩
  have hnot : ((x₀, α) : E × ℝ) ∉ epi f := fun hcon => absurd (mk_mem_epi.1 hcon) (not_le.2 h)
  have hclosed : IsClosed (epi f) :=
    lowerSemicontinuous_iff_isClosed_epi.1 hc.lowerSemicontinuous
  obtain ⟨L, u, hLs, hLx⟩ := geometric_hahn_banach_closed_point hf.convex_epi hclosed hnot
  set g : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ) with hg
  set c₀ : ℝ := L (0, 1) with hc₀def
  have hL : ∀ (x : E) (μ : ℝ), L (x, μ) = g x + c₀ * μ := dual_prod_apply L
  -- The separating functional cannot be a *lower* half-space: `epi f` is unbounded above.
  obtain ⟨x₁, hx₁⟩ := hp.convexDom_nonempty
  obtain ⟨μ₁, hμ₁⟩ := hmem x₁ hx₁
  have hc₀ : c₀ ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    set t : ℝ := max 0 ((u - g x₁ - c₀ * μ₁) / c₀) with ht
    have ht0 : 0 ≤ t := le_max_left _ _
    have htle : (u - g x₁ - c₀ * μ₁) / c₀ ≤ t := le_max_right _ _
    have hin : ((x₁, μ₁ + t) : E × ℝ) ∈ epi f :=
      mk_mem_epi.2 ((mk_mem_epi.1 hμ₁).trans
        (by exact_mod_cast (by linarith : μ₁ ≤ μ₁ + t)))
    have hbnd := hLs _ hin
    rw [hL] at hbnd
    have := (div_le_iff₀ hpos).1 htle
    nlinarith
  obtain ⟨y₁, hy₁⟩ := exists_pairing_eq B g
  rcases lt_or_eq_of_le hc₀ with hneg | hzero
  · -- Upper half-space: rescale by `-c₀ > 0`.
    have hd : 0 < -c₀ := by linarith
    have hy : ∀ x, B x ((-c₀)⁻¹ • y₁) = (-c₀)⁻¹ * g x := fun x => by
      rw [map_smul, smul_eq_mul, hy₁ x]
    refine ⟨(-c₀)⁻¹ • y₁, u / (-c₀), fun x => ?_, ?_⟩
    · rw [affineFn_eq_coe, hy]
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨μ, hfμ, hμ⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      have hin : ((x, μ) : E × ℝ) ∈ epi f := mk_mem_epi.2 hfμ.le
      have hbnd := hLs _ hin
      rw [hL] at hbnd
      have hμ' : μ < (-c₀)⁻¹ * g x - u / (-c₀) := by exact_mod_cast hμ
      rw [inv_mul_eq_div, div_sub_div_same, lt_div_iff₀ hd] at hμ'
      nlinarith
    · rw [affineFn_eq_coe, hy, EReal.coe_lt_coe_iff, inv_mul_eq_div, div_sub_div_same,
        lt_div_iff₀ hd]
      rw [hL] at hLx
      nlinarith
  · -- Vertical half-space: absorb it into a known affine minorant.
    obtain ⟨w, c₂, hw⟩ := exists_affine_le_of_closed_proper ⟨hf, hc, hp⟩
    obtain ⟨y₂, hy₂⟩ := exists_pairing_eq B w
    have hdom : ∀ x, f x < ⊤ → g x < u := by
      intro x hx
      obtain ⟨μ, hμ⟩ := hmem x hx
      have hbnd := hLs _ hμ
      rw [hL, hzero] at hbnd
      simpa using hbnd
    have hgx₀ : u < g x₀ := by rw [hL, hzero] at hLx; simpa using hLx
    set d : ℝ := g x₀ - u with hdd
    have hdpos : 0 < d := by rw [hdd]; linarith
    set m : ℝ := B x₀ y₂ - c₂ with hm
    set lam : ℝ := max 0 ((α + 1 - m) / d) with hlam
    have hlam0 : 0 ≤ lam := le_max_left _ _
    have hlamle : (α + 1 - m) / d ≤ lam := le_max_right _ _
    refine ⟨lam • y₁ + y₂, lam * u + c₂, fun x => ?_, ?_⟩
    · rw [affineFn_smul_add]
      rcases lt_or_ge (f x) ⊤ with hx | hx
      · have h1 : lam * (B x y₁ - u) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlam0 (by rw [← hy₁ x]; linarith [hdom x hx])
        refine le_trans ?_ (hy₂ x ▸ hw x)
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        linarith
      · rw [top_le_iff.1 hx]; exact le_top
    · rw [affineFn_smul_add, EReal.coe_lt_coe_iff, ← hy₁ x₀, ← hm]
      have := (div_le_iff₀ hdpos).1 hlamle
      nlinarith

/-- A closed convex function is the pointwise supremum of all the affine functions of the pairing
that lie below it. -/
theorem eq_biSup_affineFn (hf : ConvexFn f) (hc : ClosedConvex f) :
    f = fun x => ⨆ p ∈ {p : F × ℝ | affineFn B p.1 p.2 ≤ f}, affineFn B p.1 p.2 x := by
  funext x
  refine le_antisymm ?_ (iSup₂_le fun p hp => hp x)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨α, hα₁, hα₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  obtain ⟨y, c, hle, hlt⟩ := exists_affineFn_le_of_lt (B := B) hf hc hα₂
  exact absurd (lt_of_lt_of_le hlt (le_iSup₂ (f := fun p (_ : p ∈ _) => affineFn B p.1 p.2 x)
    ((y, c) : F × ℝ) hle)) (not_lt.2 hα₁.le)

end AffineMinorants

/-! ### The Fenchel–Moreau theorem -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The Fenchel–Moreau theorem.** For a convex function, `f** = cl f`.

The improper cases are why `convexCl` branches on `lscHull f` rather than on `f`: if `f` takes `-∞`
anywhere then `f* ≡ +∞` and `f** ≡ -∞`, which is `cl f` only under that branching. -/
theorem convexBiconj_eq_convexCl (hf : ConvexFn f) : convexBiconj B f = convexCl f := by
  by_cases hb : ∃ x, f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := hb
    have hbot : lscHull f x₀ = ⊥ := le_bot_iff.1 (hx₀ ▸ lscHull_le f x₀)
    rw [convexCl_of_exists_eq_bot ⟨x₀, hbot⟩]
    change convexConj B.flip (convexConj B f) = _
    rw [convexConj_of_eq_bot hx₀, convexConj_top]
  push Not at hb
  by_cases ht : ∀ x, f x = ⊤
  · have hfeq : f = fun _ => (⊤ : EReal) := funext ht
    rw [hfeq]
    change convexConj B.flip (convexConj B (fun _ => (⊤ : EReal))) = _
    rw [convexConj_top, convexConj_bot]
    exact closedConvex_const_top.symm
  refine le_antisymm (convexBiconj_le_convexCl f) fun x₀ => ?_
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨α, hα₁, hα₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  obtain ⟨y, c, hle, hlt⟩ :=
    exists_affineFn_le_of_lt (B := B) (convexFn_convexCl hf) (closedConvex_convexCl f) hα₂
  have hcy : convexConj B f y ≤ (c : EReal) := convexConj_le_coe_iff.2 (hle.trans (convexCl_le f))
  refine absurd (lt_of_lt_of_le hlt ?_) (not_lt.2 hα₁.le)
  refine le_trans ?_ (sub_le_convexConj B.flip (convexConj B f) y x₀)
  rw [affineFn_apply, LinearMap.flip_apply]
  exact EReal.sub_le_sub le_rfl hcy

/-- **Fenchel–Moreau for concave functions**: the concave biconjugate of a concave function is its
concave closure, `g** = cl g`. The double reflection cancels
(`concaveBiconj_eq_neg_convexBiconj_neg`). -/
theorem concaveBiconj_eq_concaveCl {g : E → EReal} (hg : ConcaveFn g) :
    concaveBiconj B g = concaveCl g := by
  funext x
  rw [concaveBiconj_eq_neg_convexBiconj_neg, convexBiconj_eq_convexCl hg.convexFn_neg,
      concaveCl_apply]

/-- **The properness half**: the conjugate of a closed proper convex function is proper.
With `properConvex_of_properConvex_convexConj`, "`f*` is proper if and only if `f` is". -/
theorem properConvex_convexConj (hf : ClosedProperConvexFn f) : ProperConvex (convexConj B f) := by
  obtain ⟨w, c, hw⟩ := exists_affine_le_of_closed_proper hf
  obtain ⟨y, hy⟩ := exists_pairing_eq B w
  refine ⟨⟨y, lt_of_le_of_lt (convexConj_le_coe_iff.2 fun x => ?_) (EReal.coe_lt_top c)⟩,
    convexConj_ne_bot hf.proper.convexDom_nonempty⟩
  rw [affineFn_apply, ← hy x]
  exact hw x

theorem properConvex_convexConj_iff (hf : ConvexFn f) (hc : ClosedConvex f) :
    ProperConvex (convexConj B f) ↔ ProperConvex f :=
  ⟨properConvex_of_properConvex_convexConj, fun hp => properConvex_convexConj ⟨hf, hc, hp⟩⟩

theorem convexBiconj_eq_self (hf : ConvexFn f) (hc : ClosedConvex f) : convexBiconj B f = f :=
  (convexBiconj_eq_convexCl hf).trans hc

/-- A closed concave function is its own concave biconjugate. -/
theorem concaveBiconj_eq_self {g : E → EReal} (hg : ConcaveFn g) (hc : ClosedConcave g) :
    concaveBiconj B g = g :=
  (concaveBiconj_eq_concaveCl hg).trans hc

end FenchelMoreau

/-! ### Conjugacy as a Galois connection

`convexConj_le_iff` says that `convexConj B` and `convexConj B.flip` are antitonely adjoint;
Fenchel–Moreau then identifies the closed elements of the induced closure operator with the closed
convex functions. The `OrderDual` on the domain is what makes an antitone adjunction fit Mathlib's
monotone `GaloisConnection`. -/

section Galois

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem gc_convexConj_convexConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun f : (E → EReal)ᵒᵈ => convexConj B (ofDual f))
      (fun g : F → EReal => toDual (convexConj B.flip g)) := fun _ _ => convexConj_le_iff

/-- The closure operator `f ↦ f**` induced by the adjunction. Its closed elements are the functions
equal to their own biconjugate, which by Fenchel–Moreau are exactly the closed convex functions. -/
noncomputable def convexConjClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (E → EReal)ᵒᵈ :=
  (gc_convexConj_convexConj B).closureOperator

@[simp] theorem convexConjClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    convexConjClosure B (toDual f) = toDual (convexBiconj B f) := rfl

theorem isClosed_convexConjClosure_iff {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} :
    (convexConjClosure B).IsClosed (toDual f) ↔ convexBiconj B f = f :=
  ⟨fun h => congrArg ofDual h, fun h => congrArg toDual h⟩

/-- Conjugating three times is the same as conjugating once: the triangle identity, which here says
that `f*` is unchanged by closure. -/
theorem convexConj_convexBiconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (f : E → EReal) : convexConj B (convexBiconj B f) = convexConj B f :=
  le_antisymm (convexConj_le_iff.2 (le_refl (convexBiconj B f)))
      (convexConj_antitone B (convexBiconj_le B f))

/-- **Conjugacy is an order anti-isomorphism between the biconjugation-fixed functions.**

Neither this nor `convexConjEquiv` below subsumes the other: this one needs no topology and carries
the order, while `convexConjEquiv` is about the *proper* closed convex functions, a strictly smaller
class that `f** = f` does not pin down — the improper `f ≡ +∞` and `f ≡ -∞` are fixed by
biconjugation too. -/
noncomputable def convexConjOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {f : (E → EReal)ᵒᵈ // toDual (convexConj B.flip (convexConj B (ofDual f))) = f} ≃o
      {g : F → EReal // convexConj B (ofDual (toDual (convexConj B.flip g))) = g} :=
  (gc_convexConj_convexConj B).closedsOrderIso

end Galois

/-! ### The involution on closed proper convex functions

Both spaces carry topologies compatible with the pairing, and everything is symmetric under
`B ↦ B.flip`. -/

section Involution

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] [IsCompatiblePairing B.flip]

/-- Conjugacy is a symmetric one-to-one correspondence between the closed proper convex functions
on `E` and those on `F`. -/
noncomputable def convexConjEquiv :
    {f : E → EReal // ClosedProperConvexFn f} ≃ {g : F → EReal // ClosedProperConvexFn g} where
  toFun f :=
      ⟨convexConj B f.1, convexFn_convexConj B f.1, closedConvex_convexConj,
          properConvex_convexConj f.2⟩
  invFun g :=
      ⟨convexConj B.flip g.1, convexFn_convexConj B.flip g.1, closedConvex_convexConj,
          properConvex_convexConj g.2⟩
  left_inv f := Subtype.ext (convexBiconj_eq_self f.2.convex f.2.closed)
  right_inv g := Subtype.ext (convexBiconj_eq_self (B := B.flip) g.2.convex g.2.closed)

@[simp] theorem convexConjEquiv_apply (f : {f : E → EReal // ClosedProperConvexFn f}) :
    (convexConjEquiv B f : F → EReal) = convexConj B f := rfl

end Involution

/-! ### Translation, tilting, constants and an invertible substitution

The elementary conjugacy operations, those under which `h*` changes by a change of variable rather
than by a change of function. There are four independent rows —

| primal | dual |
|---|---|
| `h (x - a)` | `h* y + ⟨a, y⟩` |
| `h x + ⟨x, b⟩` | `h* (y - b)` |
| `h x + α` | `h* y - α` |
| `h (A x)`, `A` invertible | `h* (A'⁻¹ y)` |

— and `convexConj_comp_affine` composes all four into a single formula. The two *scaling* rows of
the same table are `convexConj_smul` and `convexConj_smulRight` in `Duality/Ops.lean`. Each
identity holds for an arbitrary `h : E → EReal`, improper ones included, with no topology,
properness or convexity: `⟨a, y⟩`, `⟨x, b⟩` and `α` are *real*, so sliding them across the
difference `⟨x, y⟩ - h x` never produces `∞ - ∞`.

Rockafellar writes the substitution row with `A*⁻¹`, presuming that `A` has an adjoint and that the
adjoint is invertible. Over a general pairing neither is automatic, so `convexConj_comp_linearEquiv`
takes the inverse pair `A`, `A'` and the adjointness datum `IsAdjointPair B B' A A'` as
hypotheses; with `B` and `B'` separating, `A'` is determined by `A`, so nothing is lost. -/

section AffineOps

variable {E F G H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}

/-- **The translation row**: translating the argument of `h` by `a` adds the linear function
`⟨a, ·⟩` to the conjugate. -/
theorem convexConj_comp_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (a : E) (y : F) :
    convexConj B (fun x => h (x - a)) y = convexConj B h y + ((B a y : ℝ) : EReal) := by
  have hre := (Equiv.addRight a).iSup_comp
    (g := fun x : E => ((B x y : ℝ) : EReal) - h (x - a))
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at hre
  simp only [convexConj_apply]
  rw [← hre, EReal.iSup_add_coe]
  exact iSup_congr fun u => by
    rw [map_add, LinearMap.add_apply, EReal.coe_add_sub]

/-- **The translation row** with the translation on the left: `h (a + ·)` is
`h (· - (-a))`, so its conjugate is `h* - ⟨a, ·⟩`. -/
theorem convexConj_comp_add (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (a : E) (y : F) :
    convexConj B (fun x => h (a + x)) y = convexConj B h y - ((B a y : ℝ) : EReal) := by
  have hfun : (fun x : E => h (a + x)) = fun x : E => h (x - -a) := by
    funext x; rw [sub_neg_eq_add, add_comm]
  rw [hfun, convexConj_comp_sub, map_neg, LinearMap.neg_apply, EReal.coe_neg,
    ← sub_eq_add_neg]

/-- **The reflection row**: reflecting the argument reflects the conjugate variable. -/
theorem convexConj_comp_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    convexConj B (fun x => f (-x)) y = convexConj B f (-y) := by
  rw [convexConj_apply, convexConj_apply]
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun x => ?_)
  · refine le_trans (le_of_eq ?_) (le_iSup (fun u : E => ((B u (-y) : ℝ) : EReal) - f u) (-x))
    simp
  · refine le_trans (le_of_eq ?_) (le_iSup (fun u : E => ((B u y : ℝ) : EReal) - f (-u)) (-x))
    simp

/-- **The tilting row**: adding the linear function `⟨·, b⟩` to `h` translates the
conjugate by `b`. -/
theorem convexConj_add_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (b : F) (y : F) :
    convexConj B (fun x => h x + ((B x b : ℝ) : EReal)) y = convexConj B h (y - b) := by
  simp only [convexConj_apply]
  exact iSup_congr fun x => by rw [EReal.coe_sub_add_coe, map_sub]

/-- **The tilting row** with the linear term *subtracted*: `h - ⟨·, b⟩` has conjugate
`h* (· + b)`. -/
theorem convexConj_sub_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (b : F) (y : F) :
    convexConj B (fun x => h x - ((B x b : ℝ) : EReal)) y = convexConj B h (y + b) := by
  have hfun : (fun x : E => h x - ((B x b : ℝ) : EReal))
      = fun x : E => h x + ((B x (-b) : ℝ) : EReal) := by
    funext x
    rw [map_neg, EReal.coe_neg, ← sub_eq_add_neg]
  rw [hfun, convexConj_add_pairing, sub_neg_eq_add]

/-- **The constant row**: adding a constant to `h` subtracts it from the conjugate. -/
theorem convexConj_add_const (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (α : ℝ) (y : F) :
    convexConj B (fun x => h x + (α : EReal)) y = convexConj B h y - (α : EReal) := by
  simp only [convexConj_apply]
  rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.iSup_add_coe]
  exact iSup_congr fun x => by
    rw [EReal.coe_sub_add_coe, ← EReal.coe_add_sub, ← sub_eq_add_neg]

/-- **The substitution row**: precomposing `h` with a linear *isomorphism* `A` precomposes the
conjugate with the inverse of the transpose. Contrast `convexConj_mapLin`, which drops invertibility
at the cost of stating the dual side as an image. -/
theorem convexConj_comp_linearEquiv (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F)) (h : G → EReal) (y : F) :
    convexConj B (fun x => h (A x)) y = convexConj B' h (A'.symm y) := by
  have hre := A.toEquiv.iSup_comp
    (g := fun u : G => ((B' u (A'.symm y) : ℝ) : EReal) - h u)
  simp only [LinearEquiv.coe_toEquiv] at hre
  have hAx : ∀ (x : E) (z : H), B' (A x) z = B x (A' z) := hA
  simp only [convexConj_apply]
  rw [← hre]
  exact iSup_congr fun x => by
    rw [hAx x (A'.symm y), LinearEquiv.apply_symm_apply]

/-- **The four rows composed.** For `f x = h (A (x - a)) + ⟨x, a*⟩ + α` with `A` an invertible
linear transformation, `f* y = h* (A*⁻¹ (y - a*)) + ⟨a, y⟩ + α*` where `α* = -α - ⟨a, a*⟩`. -/
theorem convexConj_comp_affine (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F)) (h : G → EReal) (a : E) (b : F)
    (α : ℝ) (y : F) :
    convexConj B (fun x => h (A (x - a)) + ((B x b : ℝ) : EReal) + (α : EReal)) y
      = convexConj B' h (A'.symm (y - b)) + ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal) := by
  have e1 : convexConj B (fun x : E => h (A (x - a)) + ((B x b : ℝ) : EReal) + (α : EReal)) y
      = convexConj B (fun x : E => h (A (x - a)) + ((B x b : ℝ) : EReal)) y - (α : EReal) :=
    convexConj_add_const B (fun x : E => h (A (x - a)) + ((B x b : ℝ) : EReal)) α y
  have e2 : convexConj B (fun x : E => h (A (x - a)) + ((B x b : ℝ) : EReal)) y
      = convexConj B (fun x : E => h (A (x - a))) (y - b) :=
    convexConj_add_pairing B (fun x : E => h (A (x - a))) b y
  have e3 : convexConj B (fun x : E => h (A (x - a))) (y - b)
      = convexConj B (fun x : E => h (A x)) (y - b) + ((B a (y - b) : ℝ) : EReal) :=
    convexConj_comp_sub B (fun x : E => h (A x)) a (y - b)
  have e4 : convexConj B (fun x : E => h (A x)) (y - b) = convexConj B' h (A'.symm (y - b)) :=
    convexConj_comp_linearEquiv A A' hA h (y - b)
  have harith : ((B a y - B a b : ℝ) : EReal) + -(α : EReal)
      = ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal) := by
    rw [← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_eq_coe_iff]
    ring
  have hassoc : ∀ U : EReal, U + ((B a (y - b) : ℝ) : EReal) - (α : EReal)
      = U + ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal) := fun U => by
    rw [map_sub (B a) y b]
    change U + ((B a y - B a b : ℝ) : EReal) + -(α : EReal)
      = U + ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal)
    rw [add_assoc, add_assoc, harith]
  rw [e1, e2, e3, e4, hassoc]

/-- **Translation and tilting composed**: for `f = h (z + ·) - ⟨·, z*⟩`,
`f* = h* (z* + ·) - ⟨z, ·⟩ - ⟨z, z*⟩`. The constant `⟨z, z*⟩` is what makes the two infima it is
used for add to `⟨z, z*⟩` rather than to zero. -/
theorem convexConj_comp_add_sub_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (z : E) (z' : F)
    (y : F) :
    convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) y
      = convexConj B h (z' + y) - ((B z y : ℝ) : EReal) - ((B z z' : ℝ) : EReal) := by
  have hsplit : ∀ (u : EReal) (p q : ℝ),
      u - ((p + q : ℝ) : EReal) = u - (p : EReal) - (q : EReal) := fun u p q => by
    have hneg : -(((p + q : ℝ)) : EReal) = -((p : ℝ) : EReal) + -((q : ℝ) : EReal) := by
      rw [← EReal.coe_neg, neg_add, EReal.coe_add, EReal.coe_neg,
        EReal.coe_neg]
    change u + -(((p + q : ℝ)) : EReal) = u + -((p : ℝ) : EReal) + -((q : ℝ) : EReal)
    rw [hneg, ← add_assoc]
  rw [convexConj_sub_pairing B (fun x => h (z + x)) z' y, convexConj_comp_add B h z (y + z'),
    add_comm y z', map_add, add_comm ((B z) z' : ℝ) ((B z) y), hsplit]

end AffineOps


section TopDual

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- **Fenchel–Moreau for a locally convex space paired with its own topological dual**, in the
original topology of `E` and with no hypothesis beyond convexity. -/
theorem convexBiconj_eq_convexCl_topDual {f : E → EReal} (hf : ConvexFn f) :
    convexBiconj (topDualPairing ℝ E).flip f = convexCl f :=
  convexBiconj_eq_convexCl hf

theorem eq_biSup_affineFn_topDual {f : E → EReal} (hf : ConvexFn f) (hc : ClosedConvex f) :
    f = fun x => ⨆ p ∈ {p : (E →L[ℝ] ℝ) × ℝ | affineFn (topDualPairing ℝ E).flip p.1 p.2 ≤ f},
      affineFn (topDualPairing ℝ E).flip p.1 p.2 x :=
  eq_biSup_affineFn hf hc

end TopDual

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Fenchel–Moreau for a real Hilbert space paired with itself by the inner product**, in the
norm topology. Compatibility is the Fréchet–Riesz representation theorem. -/
theorem convexBiconj_eq_convexCl_inner {f : E → EReal} (hf : ConvexFn f) :
    convexBiconj (innerₗ E) f = convexCl f :=
  convexBiconj_eq_convexCl hf

theorem eq_biSup_affineFn_inner {f : E → EReal} (hf : ConvexFn f) (hc : ClosedConvex f) :
    f = fun x => ⨆ p ∈ {p : E × ℝ | affineFn (innerₗ E) p.1 p.2 ≤ f},
      affineFn (innerₗ E) p.1 p.2 x :=
  eq_biSup_affineFn hf hc

end Hilbert

end ConvexAnalysis
