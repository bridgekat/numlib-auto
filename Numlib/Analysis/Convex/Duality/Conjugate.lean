/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Order.GaloisConnection

/-!
# Conjugates of convex and concave functions

Let $E$ and $F$ be real vector spaces paired by a bilinear form $B$, written
$\langle x, y \rangle = B(x)(y)$, and let $f : E \to [-\infty, +\infty]$. The **conjugate** of $f$
is the function $f^*(y) = \sup_{x \in E} (\langle x, y \rangle - f(x))$ on $F$, and the
**biconjugate** $f^{**}$ is the conjugate of $f^*$ with respect to the flipped pairing. The
inequality $f^*(y) \le c$ says exactly that the affine function $x \mapsto \langle x, y \rangle - c$
lies below $f$, so $f^*$ describes the affine minorants of $f$. The conjugate is defined for every
$f$, and it is always a closed convex function. The main theorem is the **Fenchel–Moreau theorem**:
$f^{**} = \operatorname{cl} f$ for convex $f$. Thus conjugacy is an involution on the closed convex
functions, and a closed convex function is the pointwise supremum of the affine functions below it.
The presentation follows [rockafellar1970convex], §12.

The **concave conjugate** $g^*(y) = \inf_{x \in E} (\langle x, y \rangle - g(x))$ is the mirror
image, with infimum, $\ge$ and $-\infty$ in place of supremum, $\le$ and $+\infty$. It is not the
negative of the convex conjugate of $-g$: the correct relation is $g^*(y) = -(-g)^*(-y)$, with a
reflection on the dual side as well. Convex and concave duality are used together: the dual
objective of a convex program is the concave conjugate of a function $-\inf F$, and Fenchel's
duality theorem pairs a convex function with a concave one. Therefore each concave result follows
its convex counterpart, and most are derived from it through this sign relation.

## Main definitions

* `ConvexAnalysis.convexConj`, `ConvexAnalysis.convexBiconj`: the conjugate $f^*$ and the
  biconjugate $f^{**}$.
* `ConvexAnalysis.concaveConj`, `ConvexAnalysis.concaveBiconj`: the concave conjugate $g^*$ and the
  concave biconjugate $g^{**}$.
* `ConvexAnalysis.convexConjClosure`: the closure operator $f \mapsto f^{**}$ for the reversed
  pointwise order, whose closed elements are the functions with $f^{**} = f$.
* `ConvexAnalysis.convexConjOrderIso`: conjugacy as an order-reversing bijection between the
  functions fixed by biconjugation.
* `ConvexAnalysis.convexConjEquiv`: conjugacy as a bijection between the closed proper convex
  functions on $E$ and those on $F$.

## Main results

* `ConvexAnalysis.neg_concaveConj`, `ConvexAnalysis.concaveConj_eq_neg_convexConj_neg`,
  `ConvexAnalysis.convexConj_eq_neg_concaveConj_neg`: the sign relations $-g^*(y) = (-g)^*(-y)$ and
  $f^*(y) = -(-f)^*(-y)$ between the two conjugates, with no hypothesis.
* `ConvexAnalysis.sub_le_convexConj`: Fenchel's inequality $\langle x, y \rangle - f(x) \le f^*(y)$,
  with no hypothesis.
* `ConvexAnalysis.convexConj_le_coe_iff`: $f^*(y) \le c$ if and only if
  $x \mapsto \langle x, y \rangle - c$ lies below $f$.
* `ConvexAnalysis.convexConj_le_iff`: $f^* \le g$ if and only if $g^* \le f$, so conjugacy is an
  antitone Galois connection.
* `ConvexAnalysis.le_add_convexConj`: Fenchel's inequality $\langle x, y \rangle \le f(x) + f^*(y)$,
  for $f(x) \ne -\infty$ and $f(x_0) < +\infty$ for some $x_0 \in E$.
* `ConvexAnalysis.convexFn_convexConj`, `ConvexAnalysis.closedConvex_convexConj`: the conjugate of
  every function is convex and closed.
* `ConvexAnalysis.convexConj_convexCl`: $(\operatorname{cl} f)^* = f^*$.
* `ConvexAnalysis.exists_affineFn_le_of_lt`, `ConvexAnalysis.eq_biSup_affineFn`: a closed convex
  function is the pointwise supremum of the affine functions below it.
* `ConvexAnalysis.convexBiconj_eq_convexCl`: the Fenchel–Moreau theorem
  $f^{**} = \operatorname{cl} f$ for convex $f$.
* `ConvexAnalysis.concaveBiconj_eq_concaveCl`: the Fenchel–Moreau theorem
  $g^{**} = \operatorname{cl} g$ for concave $g$.
* `ConvexAnalysis.properConvex_convexConj_iff`: for closed convex $f$, the conjugate $f^*$ is proper
  if and only if $f$ is proper.
* `ConvexAnalysis.convexBiconj_eq_convexCl_topDual`,
  `ConvexAnalysis.convexBiconj_eq_convexCl_inner`: the Fenchel–Moreau theorem for a locally convex
  space paired with its continuous dual, and for a real Hilbert space paired with itself, both in
  the topology of the space.
* `ConvexAnalysis.gc_convexConj_convexConj`: conjugacy is a Galois connection between the reversed
  pointwise order on $E$ and the pointwise order on $F$.
* `ConvexAnalysis.convexConj_comp_sub`, `ConvexAnalysis.convexConj_comp_add`,
  `ConvexAnalysis.convexConj_add_pairing`, `ConvexAnalysis.convexConj_sub_pairing`,
  `ConvexAnalysis.convexConj_add_const`, `ConvexAnalysis.convexConj_comp_linearEquiv`: the conjugate
  under translation, tilting, an added constant and an invertible linear substitution.
* `ConvexAnalysis.convexConj_comp_affine`: the four operations composed, which is Theorem 12.3 of
  [rockafellar1970convex].

## Implementation notes

* Functions take values in `EReal`. For real $a$, the difference satisfies $a - (+\infty) = -\infty$
  and $a - (-\infty) = +\infty$, and in a sum $-\infty$ absorbs: $(+\infty) + (-\infty) = -\infty$.
  Therefore the subtractive form of Fenchel's inequality holds for every function, but the additive
  form needs hypotheses.
* The biconjugate uses `B.flip` for the second conjugation. This makes the correspondence symmetric
  with no reflexivity assumption, and `B.flip.flip = B` holds by definition.
* The Fenchel–Moreau theorem does not depend on the topology of $E$, provided that the continuous
  linear functionals on $E$ are exactly the maps $x \mapsto \langle x, y \rangle$. This is
  `ConvexAnalysis.IsCompatiblePairing B`. The weaker condition
  `ConvexAnalysis.IsContinuousPairing B` asks only that each map $x \mapsto \langle x, y \rangle$ is
  continuous. It is enough for the closedness results of this file
  (`ConvexAnalysis.closedConvex_convexConj`, `ConvexAnalysis.convexConj_convexCl`,
  `ConvexAnalysis.convexBiconj_le_convexCl`). This matters because a Banach space paired with its
  dual in the norm topology is continuous on both sides, but compatible on the dual side only if the
  space is reflexive.
-/

open Set OrderDual

namespace ConvexAnalysis

/-! ### The conjugate -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **convex conjugate** of $f : E \to [-\infty, +\infty]$ with respect to the pairing $B$ is
the function on $F$ given by $$f^*(y) = \sup_{x \in E} \bigl(\langle x, y \rangle -
f(x)\bigr).$$ No hypothesis is placed on $f$.

The epigraph of $f^*$ is the set of pairs $(y, c)$ for which the affine function
$x \mapsto \langle x, y \rangle - c$ lies below $f$ (`ConvexAnalysis.convexConj_le_coe_iff`).
The difference is the one of `EReal`: a term with $f(x) = +\infty$ is $-\infty$, and a term with
$f(x) = -\infty$ is $+\infty$. -/
noncomputable def convexConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨆ x : E, ((B x y : ℝ) : EReal) - f x

/-- The **biconjugate** of $f : E \to [-\infty, +\infty]$ is the conjugate of $f^*$ with respect to
the flipped pairing: $$f^{**}(x) = \sup_{y \in F} \bigl(\langle x, y \rangle - f^*(y)\bigr).$$

The second conjugation uses `B.flip` rather than a second pairing. This makes the correspondence
symmetric with no reflexivity assumption, and `B.flip.flip = B` holds by definition. -/
noncomputable abbrev convexBiconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : E → EReal :=
  convexConj B.flip (convexConj B f)

/-- The **concave conjugate** of $g : E \to [-\infty, +\infty]$ with respect to the pairing $B$ is
the function on $F$ given by $$g^*(y) = \inf_{x \in E} \bigl(\langle x, y \rangle -
g(x)\bigr).$$ No hypothesis is placed on $g$.

This is not the negative of the convex conjugate of $-g$. The correct relation
$g^*(y) = -(-g)^*(-y)$ is `ConvexAnalysis.concaveConj_eq_neg_convexConj_neg`. -/
noncomputable def concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : F → EReal :=
  fun y => ⨅ x : E, ((B x y : ℝ) : EReal) - g x

/-- The **concave biconjugate** of $g : E \to [-\infty, +\infty]$ is the concave conjugate of $g^*$
with respect to the flipped pairing: $$g^{**}(x) = \inf_{y \in F} \bigl(\langle x, y \rangle -
g^*(y)\bigr).$$
-/
noncomputable abbrev concaveBiconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : E → EReal :=
  concaveConj B.flip (concaveConj B g)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {x : E} {y : F} {c : ℝ}

/-- The value of the conjugate: $f^*(y) = \sup_{x \in E} (\langle x, y \rangle - f(x))$. -/
theorem convexConj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    convexConj B f y = ⨆ x : E, ((B x y : ℝ) : EReal) - f x := rfl

/-- The value of the biconjugate: $f^{**}(x) = \sup_{y \in F} (\langle x, y \rangle - f^*(y))$. -/
theorem convexBiconj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    convexBiconj B f x = ⨆ y : F, ((B x y : ℝ) : EReal) - convexConj B f y := rfl

/-- The value of the concave conjugate: $g^*(y) = \inf_{x \in E} (\langle x, y \rangle - g(x))$. -/
theorem concaveConj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    concaveConj B g y = ⨅ x : E, ((B x y : ℝ) : EReal) - g x := rfl

/-- The value of the concave biconjugate: $g^{**}(x) = \inf_{y \in F} (\langle x, y \rangle -
g^*(y))$. -/
theorem concaveBiconj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) :
    concaveBiconj B g x = ⨅ y : F, ((B x y : ℝ) : EReal) - concaveConj B g y := rfl

/-!
### The sign relation between the two conjugates

The concave conjugate $g^*$ is not $-(-g)^*$. The correct relation is $g^*(y) = -(-g)^*(-y)$: there
is a reflection on the dual side as well. The order-theoretic results below are proved directly, and
the others are derived through this relation.
-/

/-- **The sign relation between the two conjugates.** For every $g : E \to [-\infty, +\infty]$ and
$y \in F$, $$-g^*(y) = (-g)^*(-y),$$ where $g^*$ is the concave conjugate of $g$ and $(-g)^*$ is
the convex conjugate of $-g$.

Both the values and the argument are reflected. The guess $-g^* = (-g)^*$ omits the reflection
$y \mapsto -y$ of the argument. -/
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

/-- For every $g : E \to [-\infty, +\infty]$ and $y \in F$, $$g^*(y) = -(-g)^*(-y),$$ where $g^*$ is
the concave conjugate of $g$ and $(-g)^*$ is the convex conjugate of $-g$. -/
theorem concaveConj_eq_neg_convexConj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (y : F) :
    concaveConj B g y = -(convexConj B (fun x => -(g x)) (-y)) := by
  rw [← neg_concaveConj, neg_neg]

/-- For every $f : E \to [-\infty, +\infty]$ and $y \in F$, $$f^*(y) = -(-f)^*(-y),$$ where $f^*$ is
the convex conjugate of $f$ and $(-f)^*$ is the concave conjugate of $-f$. -/
theorem convexConj_eq_neg_concaveConj_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    convexConj B f y = -(concaveConj B (fun x => -(f x)) (-y)) := by
  rw [neg_concaveConj, neg_neg]
  simp only [neg_neg]

/-! #### Fenchel's inequality and the adjunction -/

/-- **Fenchel's inequality** in subtractive form. For every $f : E \to [-\infty, +\infty]$,
$x \in E$ and $y \in F$, $$\langle x, y \rangle - f(x) \le f^*(y).$$

This form needs no hypothesis, because the left side never has the form $\infty - \infty$. The
proofs below use it instead of the additive form `ConvexAnalysis.le_add_convexConj`. -/
theorem sub_le_convexConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) (y : F) :
    ((B x y : ℝ) : EReal) - f x ≤ convexConj B f y :=
  le_iSup (fun x : E => ((B x y : ℝ) : EReal) - f x) x

/-- **Fenchel's inequality for concave functions** in subtractive form. For every
$g : E \to [-\infty, +\infty]$, $x \in E$ and $y \in F$, $$g^*(y) \le \langle x, y \rangle -
g(x).$$
-/
theorem concaveConj_le_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) (y : F) :
    concaveConj B g y ≤ ((B x y : ℝ) : EReal) - g x :=
  iInf_le _ x

/-- Let $f : E \to [-\infty, +\infty]$, $y \in F$ and $c \in \mathbb{R}$. Then $f^*(y) \le c$ if and
only if the affine function $x \mapsto \langle x, y \rangle - c$ lies below $f$: $$\langle x, y
\rangle - c \le f(x) \quad \text{for all } x \in E.$$

The affine function is `ConvexAnalysis.affineFn B y c`. -/
theorem convexConj_le_coe_iff : convexConj B f y ≤ (c : EReal) ↔ affineFn B y c ≤ f := by
  rw [convexConj_apply, iSup_le_iff, affineFn_le_iff]

/-- Let $g : E \to [-\infty, +\infty]$, $y \in F$ and $c \in \mathbb{R}$. Then $c \le g^*(y)$ if and
only if the affine function $x \mapsto \langle x, y \rangle - c$ lies above $g$: $$g(x) \le
\langle x, y \rangle - c \quad \text{for all } x \in E.$$

This is the concave counterpart of `ConvexAnalysis.convexConj_le_coe_iff`, and like it has no
hypothesis. -/
theorem coe_le_concaveConj_iff : (c : EReal) ≤ concaveConj B g y ↔ g ≤ affineFn B y c := by
  rw [concaveConj_apply, le_iInf_iff]
  exact forall_congr' fun x => EReal.le_coe_sub_comm

/-- Conjugation reverses the pointwise order: if $f_1 \le f_2$, then $f_2^* \le f_1^*$. -/
theorem convexConj_antitone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Antitone (convexConj B) := fun _ _ h _ =>
  iSup_mono fun x => EReal.sub_le_sub le_rfl (h x)

/-- Concave conjugation reverses the pointwise order: if $g_1 \le g_2$, then $g_2^* \le g_1^*$. -/
theorem concaveConj_antitone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Antitone (concaveConj B) := fun _ _ hgh _ =>
  le_iInf fun x => (iInf_le _ x).trans (EReal.sub_le_sub le_rfl (hgh x))

/-- **The conjugacy adjunction.** Let $f : E \to [-\infty, +\infty]$ and
$g : F \to [-\infty, +\infty]$, and let $g^*$ be the conjugate of $g$ with respect to the
flipped pairing. Then $$f^* \le g \iff g^* \le f.$$ Both conditions say that
$\langle x, y \rangle - f(x) \le g(y)$ and $\langle x, y \rangle - g(y) \le f(x)$ for all
$x \in E$ and $y \in F$, which are the subtractive forms of
$\langle x, y \rangle \le f(x) + g(y)$.

This says that conjugation with respect to $B$ and to the flipped pairing form an antitone
Galois connection (`ConvexAnalysis.gc_convexConj_convexConj`). -/
theorem convexConj_le_iff {g : F → EReal} : convexConj B f ≤ g ↔ convexConj B.flip g ≤ f := by
  simp only [Pi.le_def, convexConj_apply, iSup_le_iff, LinearMap.flip_apply]
  rw [forall_comm]
  exact forall₂_congr fun _ _ => EReal.coe_sub_le_comm

/-- **The concave conjugacy adjunction.** Let $g : E \to [-\infty, +\infty]$ and
$h : F \to [-\infty, +\infty]$, and let $h^*$ be the concave conjugate of $h$ with respect to
the flipped pairing. Then $$h \le g^* \iff g \le h^*.$$ Both conditions say that
$h(y) \le \langle x, y \rangle - g(x)$ and $g(x) \le \langle x, y \rangle - h(y)$ for all
$x \in E$ and $y \in F$, which are the subtractive forms of
$g(x) + h(y) \le \langle x, y \rangle$. -/
theorem le_concaveConj_iff {h : F → EReal} :
    h ≤ concaveConj B g ↔ g ≤ concaveConj B.flip h := by
  simp only [Pi.le_def, concaveConj_apply, le_iInf_iff, LinearMap.flip_apply]
  rw [forall_comm]
  exact forall₂_congr fun _ _ => EReal.le_coe_sub_comm

/-- The biconjugate is a minorant: $f^{**} \le f$ for every $f : E \to [-\infty, +\infty]$. -/
theorem convexBiconj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : convexBiconj B f ≤ f :=
  convexConj_le_iff.1 le_rfl

/-- The concave biconjugate is a majorant: $g \le g^{**}$ for every $g : E \to [-\infty, +\infty]$.
-/
theorem le_concaveBiconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) : g ≤ concaveBiconj B g :=
  le_concaveConj_iff.1 le_rfl

/-! ### The improper cases -/

/-- For $y \in F$, $f^*(y) = -\infty$ if and only if $f(x) = +\infty$ for all $x \in E$. The
condition does not depend on $y$, so $f^*$ is either the constant $-\infty$ or never takes the
value $-\infty$. This is why $f^*$ is always closed. -/
theorem convexConj_eq_bot_iff : convexConj B f y = ⊥ ↔ ∀ x, f x = ⊤ := by
  rw [convexConj_apply, iSup_eq_bot]
  exact forall_congr' fun _ => EReal.coe_sub_eq_bot_iff

/-- For $y \in F$, $g^*(y) = +\infty$ if and only if $g(x) = -\infty$ for all $x \in E$. The
condition does not depend on $y$. -/
theorem concaveConj_eq_top_iff : concaveConj B g y = ⊤ ↔ ∀ x, g x = ⊥ := by
  rw [concaveConj_eq_neg_convexConj_neg, EReal.neg_eq_top_iff, convexConj_eq_bot_iff]
  exact forall_congr' fun _ => EReal.neg_eq_top_iff

/-- If $f(x_0) = -\infty$ for some $x_0 \in E$, then $f^*$ is the constant $+\infty$. -/
theorem convexConj_of_eq_bot {x₀ : E} (h : f x₀ = ⊥) : convexConj B f = fun _ => ⊤ := by
  funext y
  refine top_le_iff.1 (le_trans ?_ (sub_le_convexConj B f x₀ y))
  rw [h, EReal.coe_sub_bot]

/-- If $g(x_0) = +\infty$ for some $x_0 \in E$, then the concave conjugate $g^*$ is the constant
$-\infty$. -/
theorem concaveConj_of_eq_top {x₀ : E} (hx : g x₀ = ⊤) : concaveConj B g = fun _ => ⊥ := by
  funext y
  rw [concaveConj_eq_neg_convexConj_neg, convexConj_of_eq_bot
      (x₀ := x₀) (by rw [hx, EReal.neg_top]),
    EReal.neg_top]

/-- The conjugate of the constant $+\infty$ is the constant $-\infty$. -/
theorem convexConj_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : convexConj B (fun _ => ⊤) = fun _ => (⊥ : EReal) :=
  funext fun _ => convexConj_eq_bot_iff.2 fun _ => rfl

/-- The concave conjugate of the constant $-\infty$ is the constant $+\infty$. -/
theorem concaveConj_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    concaveConj B (fun _ => ⊥) = fun _ => (⊤ : EReal) :=
  funext fun _ => concaveConj_eq_top_iff.2 fun _ => rfl

/-- The conjugate of the constant $-\infty$ is the constant $+\infty$. -/
theorem convexConj_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : convexConj B (fun _ => ⊥) = fun _ => (⊤ : EReal) :=
  convexConj_of_eq_bot (x₀ := (0 : E)) rfl

/-- The concave conjugate of the constant $+\infty$ is the constant $-\infty$. -/
theorem concaveConj_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    concaveConj B (fun _ => ⊤) = fun _ => (⊥ : EReal) :=
  concaveConj_of_eq_top (x₀ := (0 : E)) rfl

/-- If the effective domain $\operatorname{dom} f = \{x : f(x) < +\infty\}$ is nonempty, then
$f^*(y) \ne -\infty$ for every $y \in F$. -/
theorem convexConj_ne_bot (h : (convexDom f).Nonempty) (y : F) : convexConj B f y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := h
  exact fun hc => absurd (convexConj_eq_bot_iff.1 hc x) hx.ne

/-- If the effective domain $\{x : g(x) > -\infty\}$ of $g$ is nonempty, then $g^*(y) \ne +\infty$
for every $y \in F$. -/
theorem concaveConj_ne_top (hd : (concaveDom g).Nonempty) (y : F) : concaveConj B g y ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hd
  exact fun hc => absurd (concaveConj_eq_top_iff.1 hc x) hx.ne'

/-- **Fenchel's inequality.** Let $f : E \to [-\infty, +\infty]$ have nonempty effective domain, and
let $x \in E$ with $f(x) \ne -\infty$. Then for every $y \in F$, $$\langle x, y \rangle \le
f(x) + f^*(y).$$

The hypotheses hold for every $x$ when $f$ is proper
(`ConvexAnalysis.ProperConvex.le_add_convexConj`). They cannot be dropped, because $-\infty$
absorbs in a sum: if $f$ is the constant $+\infty$, then $f^*$ is the constant $-\infty$ and the
right side is $(+\infty) + (-\infty) = -\infty$; if $f(x) = -\infty$, then $f^*$ is the constant
$+\infty$ and the right side is again $-\infty$. Use `ConvexAnalysis.sub_le_convexConj` when the
hypotheses are not available. -/
theorem le_add_convexConj (hb : f x ≠ ⊥) (hd : (convexDom f).Nonempty) (y : F) :
    ((B x y : ℝ) : EReal) ≤ f x + convexConj B f y := by
  rw [add_comm]
  exact (EReal.sub_le_iff_le_add (.inl hb) (.inr (convexConj_ne_bot hd y))).1
      (sub_le_convexConj B f x y)

/-- **Fenchel's inequality** for a proper function: if $f$ is finite somewhere and never takes the
value $-\infty$, then $\langle x, y \rangle \le f(x) + f^*(y)$ for all $x \in E$ and $y \in F$. -/
theorem ProperConvex.le_add_convexConj (hp : ProperConvex f) (x : E) (y : F) :
    ((B x y : ℝ) : EReal) ≤ f x + convexConj B f y :=
  _root_.ConvexAnalysis.le_add_convexConj (hp.ne_bot x) hp.convexDom_nonempty y

/-- **Fenchel's inequality for concave functions.** For every $g : E \to [-\infty, +\infty]$,
$x \in E$ and $y \in F$, $$g(x) + g^*(y) \le \langle x, y \rangle.$$

Unlike the convex form `ConvexAnalysis.le_add_convexConj`, this needs no properness: the
collapse $(+\infty) + (-\infty) = -\infty$ happens on the smaller side of the inequality, where
$-\infty$ does no harm. -/
theorem add_concaveConj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) (y : F) :
    g x + concaveConj B g y ≤ ((B x y : ℝ) : EReal) := by
  rw [add_comm]
  exact (EReal.le_sub_iff_add_le (.inr (EReal.coe_ne_bot _))
    (.inr (EReal.coe_ne_top _))).1 (concaveConj_le_sub B g x y)

/-- If the conjugate $f^*$ is proper, then $f$ is proper. No other hypothesis is needed for this
direction. The converse holds for closed proper convex functions
(`ConvexAnalysis.properConvex_convexConj`). -/
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

/-- For fixed $x \in E$, the function $y \mapsto \langle x, y \rangle - f(x)$ is the constant
$-\infty$, the constant $+\infty$, or an affine function $y \mapsto \langle x, y \rangle - t$ of
the flipped pairing with $t \in \mathbb{R}$. The case is decided by whether $f(x)$ is $+\infty$,
$-\infty$ or real. -/
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

/-- **The conjugate is convex.** For every $f : E \to [-\infty, +\infty]$, the conjugate $f^*$ is a
convex function on $F$: its epigraph is convex.

The reason is that $f^*$ is a pointwise supremum of affine functions and constants
(`ConvexAnalysis.convexConj_term_eq`). -/
theorem convexFn_convexConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (f : E → EReal) : ConvexFn (convexConj B f) := by
  refine convexFn_iSup fun x => ?_
  rcases convexConj_term_eq B f x with h | h | ⟨t, h⟩ <;> rw [h]
  · exact convexFn_const ⊥
  · exact convexFn_const ⊤
  · exact convexFn_affineFn x t

/-- **The concave conjugate is concave.** For every $g : E \to [-\infty, +\infty]$, the concave
conjugate $g^*$ is a concave function on $F$: its hypograph is convex. -/
theorem concaveFn_concaveConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) :
    ConcaveFn (concaveConj B g) := by
  rw [concaveFn_iff_convexFn_neg]
  have hrw : (fun y => -(concaveConj B g y))
      = compLin (convexConj B fun x => -(g x)) (-LinearMap.id) :=
    funext fun y => neg_concaveConj B g y
  rw [hrw]
  exact convexFn_compLin _ (convexFn_convexConj B _)

/-! ### The concave biconjugate -/

/-- For every $g : E \to [-\infty, +\infty]$ and $x \in E$, $$g^{**}(x) = -(-g)^{**}(x),$$ where
$g^{**}$ is the concave biconjugate of $g$ and $(-g)^{**}$ is the convex biconjugate of $-g$.

Here the argument is not reflected: the first conjugation introduces a reflection on the dual
side, and the second conjugation undoes it. -/
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

/-!
### Why Fenchel's inequality needs properness

In `EReal` the value $-\infty$ absorbs in a sum: $(+\infty) + (-\infty) = (-\infty) + (+\infty) =
-\infty$. The two examples below show that the additive form of Fenchel's inequality fails at
$x = y = 0$ for the constant functions $+\infty$ and $-\infty$ on $\mathbb{R}$.
-/

example : ¬ (((innerₗ ℝ) (0 : ℝ) (0 : ℝ) : ℝ) : EReal)
    ≤ (fun _ : ℝ => (⊤ : EReal)) 0 + convexConj (innerₗ ℝ) (fun _ : ℝ => (⊤ : EReal)) 0 := by
  rw [convexConj_top]
  simp

example : ¬ (((innerₗ ℝ) (0 : ℝ) (0 : ℝ) : ℝ) : EReal)
    ≤ (fun _ : ℝ => (⊥ : EReal)) 0 + convexConj (innerₗ ℝ) (fun _ : ℝ => (⊥ : EReal)) 0 := by
  rw [convexConj_bot]
  simp

/-!
### Closedness of the conjugate

The conjugate is closed in every topology on $F$ for which each function
$y \mapsto \langle x, y \rangle$ is continuous. Examples are the weak topology $\sigma(F, E)$ and
the norm topology of the dual of a normed space.
-/

section ConjClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {f : E → EReal}

/-- Let $F$ carry a topology in which each function $y \mapsto \langle x, y \rangle$ is continuous.
Then the conjugate $f^*$ of every $f : E \to [-\infty, +\infty]$ is lower semicontinuous. -/
theorem lowerSemicontinuous_convexConj : LowerSemicontinuous (convexConj B f) := by
  refine lowerSemicontinuous_iSup fun x => ?_
  rcases convexConj_term_eq B f x with h | h | ⟨t, h⟩ <;> rw [h]
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_affineFn (continuous_pairing B.flip x)

variable [IsTopologicalAddGroup F]

/-- **The conjugate is closed.** Let $F$ be a topological additive group in which each function
$y \mapsto \langle x, y \rangle$ is continuous. Then for every $f : E \to [-\infty, +\infty]$
the conjugate is closed: $\operatorname{cl} f^* = f^*$.

If $f$ is the constant $+\infty$, then $f^*$ is the constant $-\infty$. Otherwise $f^*$ is lower
semicontinuous and never takes the value $-\infty$. Closedness is `ConvexAnalysis.ClosedConvex`;
convexity is `ConvexAnalysis.convexFn_convexConj`. -/
theorem closedConvex_convexConj : ClosedConvex (convexConj B f) := by
  rw [closedConvex_iff]
  by_cases h : ∀ x, f x = ⊤
  · exact Or.inl (funext fun _ => convexConj_eq_bot_iff.2 h)
  · exact Or.inr ⟨lowerSemicontinuous_convexConj, fun _ hy => h (convexConj_eq_bot_iff.1 hy)⟩

/-- **The concave conjugate is closed.** Let $F$ be a topological additive group in which each
function $y \mapsto \langle x, y \rangle$ is continuous. Then for every
$g : E \to [-\infty, +\infty]$ the concave conjugate is closed in the concave sense:
$\operatorname{cl} g^* = g^*$, where the concave closure is
$\operatorname{cl} g = -\operatorname{cl}(-g)$.

This is the concave counterpart of `ConvexAnalysis.closedConvex_convexConj`. The proof writes
$-g^*$ as $(-g)^*$ composed with the continuous map $y \mapsto -y$. -/
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

/-- **Closure does not change the conjugate.** Let $E$ be a topological additive group in which each
function $x \mapsto \langle x, y \rangle$ is continuous. Then for every
$f : E \to [-\infty, +\infty]$, $$(\operatorname{cl} f)^* = f^*.$$

The affine functions below $f$ and below $\operatorname{cl} f$ are the same, because each affine
function $x \mapsto \langle x, y \rangle - c$ is itself closed. -/
theorem convexConj_convexCl (f : E → EReal) : convexConj B (convexCl f) = convexConj B f := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [convexConj_le_coe_iff, convexConj_le_coe_iff]
  exact ⟨fun h => h.trans (convexCl_le f),
    fun h => le_convexCl_of_le (closedConvex_affineFn (continuous_pairing B y)) h⟩

/-- **Closure does not change the concave conjugate.** Let $E$ be a topological additive group in
which each function $x \mapsto \langle x, y \rangle$ is continuous. Then for every
$g : E \to [-\infty, +\infty]$, $$(\operatorname{cl} g)^* = g^*,$$ with the concave closure and
the concave conjugate.

This is `ConvexAnalysis.convexConj_convexCl` read through the sign relation. -/
theorem concaveConj_concaveCl (g : E → EReal) :
    concaveConj B (concaveCl g) = concaveConj B g := by
  funext y
  rw [concaveConj_eq_neg_convexConj_neg, concaveConj_eq_neg_convexConj_neg]
  have h : (fun x => -(concaveCl g x)) = convexCl fun z => -(g z) := funext (neg_concaveCl g)
  rw [h, convexConj_convexCl]

/-- Let $E$ be a topological additive group in which each function $x \mapsto \langle x, y \rangle$
is continuous. Then $f^{**} \le \operatorname{cl} f$ for every $f : E \to [-\infty, +\infty]$.
This is the easy half of the Fenchel–Moreau theorem, and it needs no convexity: $f^{**}$ is a
closed convex minorant of $f$. -/
theorem convexBiconj_le_convexCl (f : E → EReal) : convexBiconj B f ≤ convexCl f :=
  le_convexCl_of_le (closedConvex_convexConj (B := B.flip)) (convexBiconj_le B f)

end ConjClosure

/-! ### Affine minorants of a closed convex function -/

section AffineMinorants

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The affine-minorant lemma.** Let $E$ be a locally convex space whose continuous linear
functionals are exactly the maps $x \mapsto \langle x, y \rangle$ with $y \in F$. Let
$f : E \to [-\infty, +\infty]$ be convex and closed, and let $x_0 \in E$ and
$\alpha \in \mathbb{R}$ with $\alpha < f(x_0)$. Then there are $y \in F$ and $c \in \mathbb{R}$
such that $$\langle x, y \rangle - c \le f(x) \quad \text{for all } x \in E, \qquad \alpha <
\langle x_0, y \rangle - c.$$

The hypothesis on the pairing is `ConvexAnalysis.IsCompatiblePairing B`. -/
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

/-- Let $E$ be a locally convex space whose continuous linear functionals are exactly the maps
$x \mapsto \langle x, y \rangle$ with $y \in F$. A closed convex function
$f : E \to [-\infty, +\infty]$ is the pointwise supremum of the affine functions below it:
$$f(x) = \sup \{\langle x, y \rangle - c : y \in F,\ c \in \mathbb{R},\ \langle \cdot, y
\rangle - c \le f\}.$$ If $f$ has no affine minorant, the supremum is $-\infty$. -/
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

/-- The **Fenchel–Moreau theorem**. Let $E$ be a locally convex space whose continuous linear
functionals are exactly the maps $x \mapsto \langle x, y \rangle$ with $y \in F$. Then every
convex function $f : E \to [-\infty, +\infty]$ satisfies $$f^{**} = \operatorname{cl} f.$$

The closure $\operatorname{cl} f$ (`ConvexAnalysis.convexCl`) is the lower semicontinuous hull
of $f$, replaced by the constant $-\infty$ when the hull takes the value $-\infty$ somewhere.
The improper cases are the reason for this replacement. If the hull takes the value $-\infty$
somewhere, for example because $f$ does, then $f$ has no affine minorant, so $f^*$ is the
constant $+\infty$ and $f^{**}$ is the constant $-\infty$. The hull itself can still take the
value $+\infty$ elsewhere, and then it is not equal to $f^{**}$. -/
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

/-- The **Fenchel–Moreau theorem for concave functions**. Let $E$ be a locally convex space whose
continuous linear functionals are exactly the maps $x \mapsto \langle x, y \rangle$ with
$y \in F$. Then every concave function $g : E \to [-\infty, +\infty]$ satisfies $$g^{**} =
\operatorname{cl} g,$$ with the concave biconjugate and the concave closure
$\operatorname{cl} g = -\operatorname{cl}(-g)$.

The proof uses `ConvexAnalysis.concaveBiconj_eq_neg_convexBiconj_neg`, in which the two
reflections of the argument cancel. -/
theorem concaveBiconj_eq_concaveCl {g : E → EReal} (hg : ConcaveFn g) :
    concaveBiconj B g = concaveCl g := by
  funext x
  rw [concaveBiconj_eq_neg_convexBiconj_neg, convexBiconj_eq_convexCl hg.convexFn_neg,
      concaveCl_apply]

/-- Let $E$ be a locally convex space whose continuous linear functionals are exactly the maps
$x \mapsto \langle x, y \rangle$ with $y \in F$. If $f : E \to [-\infty, +\infty]$ is a closed
proper convex function, then $f^*$ is proper. Together with
`ConvexAnalysis.properConvex_of_properConvex_convexConj`, this gives
`ConvexAnalysis.properConvex_convexConj_iff`. -/
theorem properConvex_convexConj (hf : ClosedProperConvexFn f) : ProperConvex (convexConj B f) := by
  obtain ⟨w, c, hw⟩ := exists_affine_le_of_closed_proper hf
  obtain ⟨y, hy⟩ := exists_pairing_eq B w
  refine ⟨⟨y, lt_of_le_of_lt (convexConj_le_coe_iff.2 fun x => ?_) (EReal.coe_lt_top c)⟩,
    convexConj_ne_bot hf.proper.convexDom_nonempty⟩
  rw [affineFn_apply, ← hy x]
  exact hw x

/-- **The properness half of the Fenchel–Moreau theorem.** Let $E$ be a locally convex space whose
continuous linear functionals are exactly the maps $x \mapsto \langle x, y \rangle$ with
$y \in F$, and let $f : E \to [-\infty, +\infty]$ be convex and closed. Then $$f^* \text{ is
proper} \iff f \text{ is proper}.$$
-/
theorem properConvex_convexConj_iff (hf : ConvexFn f) (hc : ClosedConvex f) :
    ProperConvex (convexConj B f) ↔ ProperConvex f :=
  ⟨properConvex_of_properConvex_convexConj, fun hp => properConvex_convexConj ⟨hf, hc, hp⟩⟩

/-- Let $E$ be a locally convex space whose continuous linear functionals are exactly the maps
$x \mapsto \langle x, y \rangle$ with $y \in F$. A closed convex function
$f : E \to [-\infty, +\infty]$ is its own biconjugate: $f^{**} = f$. -/
theorem convexBiconj_eq_self (hf : ConvexFn f) (hc : ClosedConvex f) : convexBiconj B f = f :=
  (convexBiconj_eq_convexCl hf).trans hc

/-- Let $E$ be a locally convex space whose continuous linear functionals are exactly the maps
$x \mapsto \langle x, y \rangle$ with $y \in F$. A closed concave function
$g : E \to [-\infty, +\infty]$ is its own concave biconjugate: $g^{**} = g$. -/
theorem concaveBiconj_eq_self {g : E → EReal} (hg : ConcaveFn g) (hc : ClosedConcave g) :
    concaveBiconj B g = g :=
  (concaveBiconj_eq_concaveCl hg).trans hc

end FenchelMoreau

/-!
### Conjugacy as a Galois connection

By `ConvexAnalysis.convexConj_le_iff`, conjugation with respect to $B$ and conjugation with respect
to the flipped pairing form an antitone Galois connection. The Fenchel–Moreau theorem then
identifies the closed elements of the induced closure operator with the closed convex functions. The
order dual on the domain turns the antitone adjunction into a monotone `GaloisConnection` in the
sense of Mathlib.
-/

section Galois

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **Conjugacy is a Galois connection.** Give the functions $E \to [-\infty, +\infty]$ the reversed
pointwise order and the functions $F \to [-\infty, +\infty]$ the pointwise order. Then
$f \mapsto f^*$ and $g \mapsto g^*$, the second being conjugation with respect to the flipped
pairing, form a Galois connection: $$f^* \le g \iff g^* \le f.$$ No topology is needed.

The reversed order is `OrderDual`. The proof is `ConvexAnalysis.convexConj_le_iff`. -/
theorem gc_convexConj_convexConj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun f : (E → EReal)ᵒᵈ => convexConj B (ofDual f))
      (fun g : F → EReal => toDual (convexConj B.flip g)) := fun _ _ => convexConj_le_iff

/-- The **closure operator of conjugacy**: the map $f \mapsto f^{**}$ on the functions
$E \to [-\infty, +\infty]$ with the reversed pointwise order, induced by the Galois connection
`ConvexAnalysis.gc_convexConj_convexConj`. In the reversed order, the inequality $f^{**} \le f$
says that the operator is extensive.

Its closed elements are the functions with $f^{**} = f$
(`ConvexAnalysis.isClosed_convexConjClosure_iff`). When $E$ is a locally convex space whose
continuous linear functionals are exactly the maps $x \mapsto \langle x, y \rangle$, these are
exactly the closed convex functions, by the Fenchel–Moreau theorem. -/
noncomputable def convexConjClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (E → EReal)ᵒᵈ :=
  (gc_convexConj_convexConj B).closureOperator

/-- The closure operator `ConvexAnalysis.convexConjClosure B` maps $f$ to its biconjugate $f^{**}$.
-/
@[simp] theorem convexConjClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    convexConjClosure B (toDual f) = toDual (convexBiconj B f) := rfl

/-- A function $f$ is a closed element of the closure operator `ConvexAnalysis.convexConjClosure B`
if and only if $f^{**} = f$. -/
theorem isClosed_convexConjClosure_iff {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} :
    (convexConjClosure B).IsClosed (toDual f) ↔ convexBiconj B f = f :=
  ⟨fun h => congrArg ofDual h, fun h => congrArg toDual h⟩

/-- Conjugating three times is the same as conjugating once: $(f^{**})^* = f^*$ for every
$f : E \to [-\infty, +\infty]$. This is the triangle identity of the Galois connection. It says
that $f^*$ does not change when $f$ is replaced by its closure $f^{**}$ under
`ConvexAnalysis.convexConjClosure B`. -/
theorem convexConj_convexBiconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (f : E → EReal) : convexConj B (convexBiconj B f) = convexConj B f :=
  le_antisymm (convexConj_le_iff.2 (le_refl (convexBiconj B f)))
      (convexConj_antitone B (convexBiconj_le B f))

/-- **Conjugacy is an order-reversing bijection between the functions fixed by biconjugation.** Let
$\mathcal{F}_E$ be the set of functions $f : E \to [-\infty, +\infty]$ with $f^{**} = f$, and
let $\mathcal{F}_F$ be the set of functions $g : F \to [-\infty, +\infty]$ that are equal to
their biconjugate with respect to the flipped pairing. Then $f \mapsto f^*$ is a bijection from
$\mathcal{F}_E$ to $\mathcal{F}_F$, and $f_1 \le f_2$ if and only if $f_2^* \le f_1^*$. No
topology is needed.

Neither this result nor `ConvexAnalysis.convexConjEquiv` contains the other. This one needs no
topology and keeps the order. The other one is about the closed proper convex functions, a
strictly smaller class that the condition $f^{**} = f$ does not single out: the improper
constants $+\infty$ and $-\infty$ are also fixed by biconjugation. The Lean statement is an
order isomorphism from a subtype of `(E → EReal)ᵒᵈ`, obtained from
`ConvexAnalysis.gc_convexConj_convexConj`. -/
noncomputable def convexConjOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {f : (E → EReal)ᵒᵈ // toDual (convexConj B.flip (convexConj B (ofDual f))) = f} ≃o
      {g : F → EReal // convexConj B (ofDual (toDual (convexConj B.flip g))) = g} :=
  (gc_convexConj_convexConj B).closedsOrderIso

end Galois

/-!
### The involution on closed proper convex functions

In this section $E$ and $F$ are locally convex spaces, the continuous linear functionals on $E$ are
exactly the maps $x \mapsto \langle x, y \rangle$, and those on $F$ are exactly the maps
$y \mapsto \langle x, y \rangle$. Everything is symmetric under the exchange of $E$ and $F$, which
replaces `B` with `B.flip`.
-/

section Involution

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] [IsCompatiblePairing B.flip]

/-- **Conjugacy is an involution on the closed proper convex functions.** Let $E$ and $F$ be locally
convex spaces such that the continuous linear functionals on $E$ are exactly the maps
$x \mapsto \langle x, y \rangle$ with $y \in F$, and those on $F$ are exactly the maps
$y \mapsto \langle x, y \rangle$ with $x \in E$. Then $f \mapsto f^*$ is a bijection from the
closed proper convex functions on $E$ to the closed proper convex functions on $F$. Its inverse
is conjugation with respect to the flipped pairing.

The inverse property is the Fenchel–Moreau theorem in the form
`ConvexAnalysis.convexBiconj_eq_self`. -/
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

/-- The bijection `ConvexAnalysis.convexConjEquiv B` maps $f$ to its conjugate $f^*$. -/
@[simp] theorem convexConjEquiv_apply (f : {f : E → EReal // ClosedProperConvexFn f}) :
    (convexConjEquiv B f : F → EReal) = convexConj B f := rfl

end Involution

/-!
### Translation, tilting, constants and an invertible substitution

These are the elementary operations under which the conjugate changes by a change of variable, not
by a change of function. For $h : E \to [-\infty, +\infty]$ there are four independent rules:

| primal | dual |
|---|---|
| $h(x - a)$ | $h^*(y) + \langle a, y \rangle$ |
| $h(x) + \langle x, b \rangle$ | $h^*(y - b)$ |
| $h(x) + \alpha$ | $h^*(y) - \alpha$ |
| $h(Ax)$, $A$ invertible | $h^*(A'^{-1} y)$ |

`ConvexAnalysis.convexConj_comp_affine` composes all four into one formula. The two scaling rules of
the same table are `ConvexAnalysis.convexConj_smul` and `ConvexAnalysis.convexConj_smulRight` in
`Numlib.Analysis.Convex.Duality.Ops`. Each identity holds for every $h$, improper functions
included, with no topology, properness or convexity: $\langle a, y \rangle$, $\langle x, b \rangle$
and $\alpha$ are real, so moving them across the difference $\langle x, y \rangle - h(x)$ never
produces $\infty - \infty$.

[rockafellar1970convex] writes the substitution rule with $A^{*-1}$, and so assumes that $A$ has an
adjoint and that the adjoint is invertible. Over a general pairing neither is automatic. Therefore
`ConvexAnalysis.convexConj_comp_linearEquiv` takes the inverse pair $A$, $A'$ and the adjointness
$\langle Ax, z \rangle' = \langle x, A'z \rangle$ as hypotheses. When both pairings are separating,
$A'$ is determined by $A$, so nothing is lost.
-/

section AffineOps

variable {E F G H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}

/-- **Translation.** For every $h : E \to [-\infty, +\infty]$, $a \in E$ and $y \in F$, $$\bigl(x
\mapsto h(x - a)\bigr)^*(y) = h^*(y) + \langle a, y \rangle.$$
-/
theorem convexConj_comp_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (a : E) (y : F) :
    convexConj B (fun x => h (x - a)) y = convexConj B h y + ((B a y : ℝ) : EReal) := by
  have hre := (Equiv.addRight a).iSup_comp
    (g := fun x : E => ((B x y : ℝ) : EReal) - h (x - a))
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at hre
  simp only [convexConj_apply]
  rw [← hre, EReal.iSup_add_coe]
  exact iSup_congr fun u => by
    rw [map_add, LinearMap.add_apply, EReal.coe_add_sub]

/-- **Translation**, with the translation on the left. For every $h : E \to [-\infty, +\infty]$,
$a \in E$ and $y \in F$, $$\bigl(x \mapsto h(a + x)\bigr)^*(y) = h^*(y) - \langle a, y
\rangle.$$ This is `ConvexAnalysis.convexConj_comp_sub` at $-a$. -/
theorem convexConj_comp_add (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (a : E) (y : F) :
    convexConj B (fun x => h (a + x)) y = convexConj B h y - ((B a y : ℝ) : EReal) := by
  have hfun : (fun x : E => h (a + x)) = fun x : E => h (x - -a) := by
    funext x; rw [sub_neg_eq_add, add_comm]
  rw [hfun, convexConj_comp_sub, map_neg, LinearMap.neg_apply, EReal.coe_neg,
    ← sub_eq_add_neg]

/-- **Reflection.** For every $f : E \to [-\infty, +\infty]$ and $y \in F$,
$\bigl(x \mapsto f(-x)\bigr)^*(y) = f^*(-y)$. -/
theorem convexConj_comp_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    convexConj B (fun x => f (-x)) y = convexConj B f (-y) := by
  rw [convexConj_apply, convexConj_apply]
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun x => ?_)
  · refine le_trans (le_of_eq ?_) (le_iSup (fun u : E => ((B u (-y) : ℝ) : EReal) - f u) (-x))
    simp
  · refine le_trans (le_of_eq ?_) (le_iSup (fun u : E => ((B u y : ℝ) : EReal) - f (-u)) (-x))
    simp

/-- **Tilting.** For every $h : E \to [-\infty, +\infty]$ and $b, y \in F$, $$\bigl(x \mapsto h(x) +
\langle x, b \rangle\bigr)^*(y) = h^*(y - b).$$
-/
theorem convexConj_add_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (b : F) (y : F) :
    convexConj B (fun x => h x + ((B x b : ℝ) : EReal)) y = convexConj B h (y - b) := by
  simp only [convexConj_apply]
  exact iSup_congr fun x => by rw [EReal.coe_sub_add_coe, map_sub]

/-- **Tilting**, with the linear term subtracted. For every $h : E \to [-\infty, +\infty]$ and
$b, y \in F$, $$\bigl(x \mapsto h(x) - \langle x, b \rangle\bigr)^*(y) = h^*(y + b).$$
-/
theorem convexConj_sub_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (b : F) (y : F) :
    convexConj B (fun x => h x - ((B x b : ℝ) : EReal)) y = convexConj B h (y + b) := by
  have hfun : (fun x : E => h x - ((B x b : ℝ) : EReal))
      = fun x : E => h x + ((B x (-b) : ℝ) : EReal) := by
    funext x
    rw [map_neg, EReal.coe_neg, ← sub_eq_add_neg]
  rw [hfun, convexConj_add_pairing, sub_neg_eq_add]

/-- **Adding a constant.** For every $h : E \to [-\infty, +\infty]$, $\alpha \in \mathbb{R}$ and
$y \in F$, $$(h + \alpha)^*(y) = h^*(y) - \alpha.$$
-/
theorem convexConj_add_const (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (α : ℝ) (y : F) :
    convexConj B (fun x => h x + (α : EReal)) y = convexConj B h y - (α : EReal) := by
  simp only [convexConj_apply]
  rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.iSup_add_coe]
  exact iSup_congr fun x => by
    rw [EReal.coe_sub_add_coe, ← EReal.coe_add_sub, ← sub_eq_add_neg]

/-- **Invertible linear substitution.** Let $B'$ be a second pairing, of real vector spaces $G$ and
$H$, written $\langle \cdot, \cdot \rangle'$. Let $A : E \to G$ and $A' : H \to F$ be linear
isomorphisms with $\langle Ax, z \rangle' = \langle x, A'z \rangle$ for all $x \in E$ and
$z \in H$. Then for every $h : G \to [-\infty, +\infty]$ and $y \in F$, $$(h \circ A)^*(y) =
h^*(A'^{-1} y),$$ where $h^*$ is the conjugate with respect to $B'$.

In [rockafellar1970convex] the map $A'$ is the adjoint $A^*$. Compare
`ConvexAnalysis.convexConj_mapLin`, which does not need invertibility but states the dual side
as an image. -/
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

/-- **The four rules composed.** Let $A : E \to G$ and $A' : H \to F$ be linear isomorphisms with
$\langle Ax, z \rangle' = \langle x, A'z \rangle$, as in
`ConvexAnalysis.convexConj_comp_linearEquiv`. Let $h : G \to [-\infty, +\infty]$, $a \in E$,
$b \in F$ and $\alpha \in \mathbb{R}$, and let $f(x) = h(A(x - a)) + \langle x, b \rangle +
\alpha$. Then for every $y \in F$, $$f^*(y) = h^*\bigl(A'^{-1}(y - b)\bigr) + \langle a, y
\rangle + \alpha^*, \qquad \alpha^* = -\alpha - \langle a, b \rangle.$$ This is Theorem 12.3 of
[rockafellar1970convex].

The source writes $a^*$ for $b$ and $A^{*-1}$ for $A'^{-1}$. -/
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

/-- **Translation and tilting composed.** For every $h : E \to [-\infty, +\infty]$, $z \in E$ and
$z^*, y \in F$, $$\bigl(x \mapsto h(z + x) - \langle x, z^* \rangle\bigr)^*(y) = h^*(z^* + y) -
\langle z, y \rangle - \langle z, z^* \rangle.$$ The constant $\langle z, z^* \rangle$ is the
reason that the two infima for which this identity is used add to $\langle z, z^* \rangle$ and
not to zero.

In Lean, $z^*$ is `z'`. -/
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

/-- **The Fenchel–Moreau theorem for a locally convex space and its dual.** Let $E$ be a locally
convex space, paired with its continuous dual $E'$ by $\langle x, \varphi \rangle = \varphi(x)$.
Then every convex function $f : E \to [-\infty, +\infty]$ satisfies
$f^{**} = \operatorname{cl} f$, with the closure taken in the topology of $E$. No other
hypothesis is needed.

The pairing is `(topDualPairing ℝ E).flip`. -/
theorem convexBiconj_eq_convexCl_topDual {f : E → EReal} (hf : ConvexFn f) :
    convexBiconj (topDualPairing ℝ E).flip f = convexCl f :=
  convexBiconj_eq_convexCl hf

/-- Let $E$ be a locally convex space with continuous dual $E'$. A closed convex function
$f : E \to [-\infty, +\infty]$ is the pointwise supremum of the continuous affine functions
below it: $$f(x) = \sup \{\varphi(x) - c : \varphi \in E',\ c \in \mathbb{R},\ \varphi - c \le
f\}.$$
-/
theorem eq_biSup_affineFn_topDual {f : E → EReal} (hf : ConvexFn f) (hc : ClosedConvex f) :
    f = fun x => ⨆ p ∈ {p : (E →L[ℝ] ℝ) × ℝ | affineFn (topDualPairing ℝ E).flip p.1 p.2 ≤ f},
      affineFn (topDualPairing ℝ E).flip p.1 p.2 x :=
  eq_biSup_affineFn hf hc

end TopDual

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The Fenchel–Moreau theorem for a real Hilbert space.** Let $E$ be a real Hilbert space, paired
with itself by the inner product. Then every convex function $f : E \to [-\infty, +\infty]$
satisfies $f^{**} = \operatorname{cl} f$, with the closure taken in the norm topology.

The pairing is `innerₗ E`. The compatibility of this pairing with the norm topology is the
Fréchet–Riesz representation theorem. -/
theorem convexBiconj_eq_convexCl_inner {f : E → EReal} (hf : ConvexFn f) :
    convexBiconj (innerₗ E) f = convexCl f :=
  convexBiconj_eq_convexCl hf

/-- Let $E$ be a real Hilbert space. A closed convex function $f : E \to [-\infty, +\infty]$ is the
pointwise supremum of the affine functions below it: $$f(x) = \sup \{\langle x, y \rangle - c :
y \in E,\ c \in \mathbb{R},\ \langle \cdot, y \rangle - c \le f\}.$$
-/
theorem eq_biSup_affineFn_inner {f : E → EReal} (hf : ConvexFn f) (hc : ClosedConvex f) :
    f = fun x => ⨆ p ∈ {p : E × ℝ | affineFn (innerₗ E) p.1 p.2 ≤ f},
      affineFn (innerₗ E) p.1 p.2 x :=
  eq_biSup_affineFn hf hc

end Hilbert

end ConvexAnalysis
