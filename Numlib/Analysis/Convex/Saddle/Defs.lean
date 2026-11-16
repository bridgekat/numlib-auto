/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Adjoint

/-!
# Saddle-functions and partial conjugacy

Let $U$ and $X$ be real vector spaces. A function $K : U \times X \to [-\infty, +\infty]$ is
**concave-convex** if $K(\cdot, x)$ is concave for every $x$ and $K(u, \cdot)$ is convex for every
$u$. It is **convex-concave** if the two roles are exchanged, and a **saddle-function** if it is one
of the two. Its effective domains are $\operatorname{dom}_1 K = \{u \mid K(u, x) > -\infty \text{
for all } x\}$ and $\operatorname{dom}_2 K = \{x \mid K(u, x) < +\infty \text{ for all } u\}$. The
partial closure $\operatorname{cl}_2 K$ is the convex closure of $K(u, \cdot)$ for each $u$, and
$\operatorname{cl}_1 K$ is the concave closure of $K(\cdot, x)$ for each $x$. The presentation
follows [rockafellar1970convex], §33–§34.

Concave-convex functions carry the same information as convex bifunctions. Let
$\langle x, y \rangle$ be a pairing of $X$ with a second space $Y$. A convex bifunction $F$ from $U$
to $X$ gives the **bracket** $$\langle Fu, y \rangle = (Fu)^*(y) = \sup_x \{\langle x, y \rangle -
(Fu)(x)\},$$ which is concave-convex in $(u, y)$ and closed convex in $y$. Conversely, a
concave-convex $K$ on $U \times Y$ gives the convex bifunction $(Fu)(x) = \sup_y \{\langle x, y
\rangle - K(u, y)\}$, and the bracket of this bifunction is $\operatorname{cl}_2 K$. With a pairing
$\langle u, v \rangle$ of $U$ with $V$ and the adjoint $F^*$ of $F$, the module also proves the two
equations $\langle u, F^* y \rangle = \operatorname{cl}_1 \langle Fu, y \rangle$ and
$\operatorname{cl}_2 \langle u, F^* y \rangle = \langle (\operatorname{cl} F) u, y \rangle$ of
Theorem 33.2 of [rockafellar1970convex].

## Main definitions

* `ConvexAnalysis.ConcaveConvexFn`, `ConvexAnalysis.ConvexConcaveFn`, `ConvexAnalysis.SaddleFn`:
  concave-convex functions, convex-concave functions and saddle-functions with values in
  $[-\infty, +\infty]$.
* `ConvexAnalysis.dom₁`, `ConvexAnalysis.dom₂`: the two effective domains, which are intersections
  (not unions) of the effective domains of the slices.
* `ConvexAnalysis.partialCl₂`, `ConvexAnalysis.partialCl₁`: the partial closures
  $\operatorname{cl}_2$ and $\operatorname{cl}_1$. Their fixed points are
  `ConvexAnalysis.PartialClosed₂` and `ConvexAnalysis.PartialClosed₁`.
* `ConvexAnalysis.bracket`, `ConvexAnalysis.concaveBracket`: the bracket $\langle Fu, y \rangle$ of
  a convex bifunction and the bracket $\langle u, Gy \rangle = \inf_v \{\langle u, v \rangle -
  (Gy)(v)\}$ of a concave bifunction. `ConvexAnalysis.partialConj₂` is the conjugate in the second
  variable of a function on a product.
* `ConvexAnalysis.bifunOfSaddle`: the convex bifunction $(Fu)(x) = \sup_y \{\langle x, y \rangle -
  K(u, y)\}$ attached to a saddle-function $K$.
* `ConvexAnalysis.ConcaveConvexOn`: a real-valued $K$ that is concave in $u$ on $C$ and convex in
  $x$ on $D$.
* `ConvexAnalysis.saddleSwap`: the involution that sends $K$ to $(x, u) \mapsto -K(u, x)$, also as
  the order isomorphism `ConvexAnalysis.saddleSwapOrderIso` onto the order dual.

## Main results

* `ConvexAnalysis.concaveConvexFn_bracket`, `ConvexAnalysis.closedConvex_bracket`,
  `ConvexAnalysis.convexCl_eq_convexConj_bracket`: the bracket of a convex bifunction $F$ is
  concave-convex and closed in $y$, and $\operatorname{cl}(Fu)$ is the conjugate of
  $\langle Fu, \cdot \rangle$.
* `ConvexAnalysis.convexBifun_bifunOfSaddle`, `ConvexAnalysis.bracket_bifunOfSaddle`: the bifunction
  attached to a concave-convex $K$ is convex, and its bracket is $\operatorname{cl}_2 K$.
* `ConvexAnalysis.convexFn_partialCl₂`, `ConvexAnalysis.concaveFn_partialCl₁`,
  `ConvexAnalysis.concaveConvexFn_partialCl₂`, `ConvexAnalysis.concaveConvexFn_partialCl₁`: the
  partial closures of a concave-convex function are again concave-convex.
* `ConvexAnalysis.concaveBracket_convexAdjointBifun_eq_partialCl₁`,
  `ConvexAnalysis.partialCl₂_concaveBracket_convexAdjointBifun`: the equations $\langle u, F^* y
  \rangle = \operatorname{cl}_1 \langle Fu, y \rangle$ and $\operatorname{cl}_2 \langle u, F^* y
  \rangle = \langle (\operatorname{cl} F) u, y \rangle$.

## Proof outline

The bracket inherits its properties from one-variable conjugacy, applied uniformly in the parameter
$u$. Convexity and closedness in $y$ hold because $\langle Fu, \cdot \rangle$ is a conjugate, and
the inversion formula for $\operatorname{cl}(Fu)$ is the Fenchel–Moreau theorem. Concavity in $u$
holds because $-\langle Fu, y \rangle$ is the infimal projection of a jointly convex function. The
adjoint satisfies $(F^* y)(v) = \inf_u \{\langle u, v \rangle - \langle Fu, y \rangle\}$, so the
first equation of Theorem 33.2 is the concave Fenchel–Moreau theorem in $u$. The second equation is
the same argument for the concave bifunction $F^*$, followed by $F^{**} = \operatorname{cl} F$. The
closure $\operatorname{cl}_2 K$ is concave-convex because it is a bracket.

## Implementation notes

* The two partial closures are not mirror images. $\operatorname{cl}_2 K$ closes $K(u, \cdot)$ as a
  convex function with `ConvexAnalysis.convexCl`, and $\operatorname{cl}_1 K$ closes $K(\cdot, x)$
  as a concave function with `ConvexAnalysis.concaveCl`.
* `ConvexAnalysis.saddleSwap` exchanges the two variables and the two partial closures. Each
  statement about the first variable is therefore the statement about the second variable, read at
  `ConvexAnalysis.saddleSwap K`. `ConvexAnalysis.swapReal` is the same operation for real-valued
  functions.
* A pairing is a bilinear map such as `Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ`. The two equations of Theorem 33.2
  are one theorem in opposite variables, so their pairing hypotheses differ: the first needs a
  compatible pairing (`ConvexAnalysis.IsCompatiblePairing`) on $U$, and the second needs one on $Y$,
  together with compatible pairings on $U$ and $X$ for the closure of $F$.
-/

namespace ConvexAnalysis

/-! ### Rearrangements in the extended reals -/

section ERealAux

private theorem neg_coe_sub' {c : ℝ} {w : EReal} :
    -((c : EReal) - w) = ((-c : ℝ) : EReal) + w := by
  rw [EReal.neg_coe_sub, add_comm]
  rfl

private theorem coe_sub_eq_neg_add {c : ℝ} {w : EReal} :
    (c : EReal) - w = -w + (c : EReal) := by
  change (c : EReal) + -w = -w + (c : EReal)
  exact add_comm _ _

end ERealAux

/-! ### The two effective domains -/

section SaddleDom

variable {U X : Type*} {K : U × X → EReal}

/-- The **first effective domain** $\operatorname{dom}_1 K$ of
$K : U \times X \to [-\infty, +\infty]$ is the set of $u$ with $K(u, x) > -\infty$ for every
$x$. It is an intersection of the effective domains of the concave slices $K(\cdot, x)$. -/
def dom₁ (K : U × X → EReal) : Set U := {u | ∀ x, ⊥ < K (u, x)}

/-- The **second effective domain** $\operatorname{dom}_2 K$ of
$K : U \times X \to [-\infty, +\infty]$ is the set of $x$ with $K(u, x) < +\infty$ for every
$u$. -/
def dom₂ (K : U × X → EReal) : Set X := {x | ∀ u, K (u, x) < ⊤}

/-- A point $u$ lies in $\operatorname{dom}_1 K$ if and only if $K(u, x) > -\infty$ for every $x$.
-/
@[simp] theorem mem_dom₁ {u : U} : u ∈ dom₁ K ↔ ∀ x, ⊥ < K (u, x) := Iff.rfl

/-- A point $x$ lies in $\operatorname{dom}_2 K$ if and only if $K(u, x) < +\infty$ for every $u$.
-/
@[simp] theorem mem_dom₂ {x : X} : x ∈ dom₂ K ↔ ∀ u, K (u, x) < ⊤ := Iff.rfl

/-- $\operatorname{dom}_1 K = \bigcap_x \operatorname{dom} K(\cdot, x)$, where $\operatorname{dom}$
of a concave function is the set where it is greater than $-\infty$. -/
theorem dom₁_eq_iInter (K : U × X → EReal) :
    dom₁ K = ⋂ x, concaveDom fun u => K (u, x) := by
  ext u
  simp [dom₁, concaveDom]

/-- $\operatorname{dom}_2 K = \bigcap_u \operatorname{dom} K(u, \cdot)$, where $\operatorname{dom}$
of a convex function is the set where it is less than $+\infty$. -/
theorem dom₂_eq_iInter (K : U × X → EReal) : dom₂ K = ⋂ u, convexDom fun x => K (u, x) := by
  ext x
  simp [dom₂, convexDom]

end SaddleDom

/-! ### Concave-convex functions -/

section SaddleDefs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {K : U × X → EReal}

/-- A function $K : U \times X \to [-\infty, +\infty]$ is **concave-convex** if $K(\cdot, x)$ is
concave for every $x \in X$ and $K(u, \cdot)$ is convex for every $u \in U$. -/
structure ConcaveConvexFn (K : U × X → EReal) : Prop where
  /-- The slice $K(\cdot, x)$ is concave for every $x$. -/
  concave_fst : ∀ x, ConcaveFn fun u => K (u, x)
  /-- The slice $K(u, \cdot)$ is convex for every $u$. -/
  convex_snd : ∀ u, ConvexFn fun x => K (u, x)

/-- A function $K : U \times X \to [-\infty, +\infty]$ is **convex-concave** if $K(\cdot, x)$ is
convex for every $x \in X$ and $K(u, \cdot)$ is concave for every $u \in U$. -/
structure ConvexConcaveFn (K : U × X → EReal) : Prop where
  /-- The slice $K(\cdot, x)$ is convex for every $x$. -/
  convex_fst : ∀ x, ConvexFn fun u => K (u, x)
  /-- The slice $K(u, \cdot)$ is concave for every $u$. -/
  concave_snd : ∀ u, ConcaveFn fun x => K (u, x)

/-- A **saddle-function** is a function $K : U \times X \to [-\infty, +\infty]$ that is
concave-convex or convex-concave. -/
def SaddleFn (K : U × X → EReal) : Prop := ConcaveConvexFn K ∨ ConvexConcaveFn K

/-- If $K$ is concave-convex, then $-K$ is convex-concave. -/
theorem ConcaveConvexFn.convexConcaveFn_neg (h : ConcaveConvexFn K) :
    ConvexConcaveFn fun p => -(K p) :=
  ⟨fun x => (h.concave_fst x).convexFn_neg, fun u => (h.convex_snd u).concaveFn_neg⟩

/-- If $K$ is convex-concave, then $-K$ is concave-convex. -/
theorem ConvexConcaveFn.concaveConvexFn_neg (h : ConvexConcaveFn K) :
    ConcaveConvexFn fun p => -(K p) :=
  ⟨fun x => (h.convex_fst x).concaveFn_neg, fun u => (h.concave_snd u).convexFn_neg⟩

/-- A concave-convex function is a saddle-function. -/
theorem ConcaveConvexFn.saddleFn (h : ConcaveConvexFn K) : SaddleFn K := Or.inl h

/-- A convex-concave function is a saddle-function. -/
theorem ConvexConcaveFn.saddleFn (h : ConvexConcaveFn K) : SaddleFn K := Or.inr h

/-- If $K$ is concave-convex, then $\operatorname{dom}_1 K$ is convex, because it is an intersection
of effective domains of concave functions. -/
theorem ConcaveConvexFn.convex_dom₁ (h : ConcaveConvexFn K) : Convex ℝ (dom₁ K) := by
  rw [dom₁_eq_iInter]
  exact convex_iInter fun x => (h.concave_fst x).convex_concaveDom

/-- If $K$ is concave-convex, then $\operatorname{dom}_2 K$ is convex. -/
theorem ConcaveConvexFn.convex_dom₂ (h : ConcaveConvexFn K) : Convex ℝ (dom₂ K) := by
  rw [dom₂_eq_iInter]
  exact convex_iInter fun u => (h.convex_snd u).convex_convexDom

end SaddleDefs

/-! ### Partial conjugacy -/

section PartialConj

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **conjugate in the second variable** of $f : U \times X \to [-\infty, +\infty]$, with
respect to a pairing $\langle x, y \rangle$ of $X$ with $Y$, is the function on $U \times Y$
$$(u, y) \mapsto \sup_x \{\langle x, y \rangle - f(u, x)\},$$ the conjugate of $f(u, \cdot)$
evaluated at $y$.

This is the uncurried form of `ConvexAnalysis.bracket`, as `ConvexAnalysis.partialConj₂_graphFn`
states. Other modules use the curried form. -/
noncomputable def partialConj₂ (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (f : U × X → EReal) : U × Y → EReal :=
  fun p => convexConj Bx (fun x => f (p.1, x)) p.2

/-- The conjugate in the second variable is $(u, y) \mapsto f(u, \cdot)^*(y)$. -/
theorem partialConj₂_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (f : U × X → EReal) (p : U × Y) :
    partialConj₂ Bx f p = convexConj Bx (fun x => f (p.1, x)) p.2 := rfl

end PartialConj

/-! ### Partial closures -/

section PartialCl

variable {U X : Type*}

/-- The **partial closure** $\operatorname{cl}_2 K$ of $K : U \times X \to [-\infty, +\infty]$ in
the second variable: $\operatorname{cl}_2 K(u, x) = (\operatorname{cl} K(u, \cdot))(x)$, where
$\operatorname{cl}$ is the convex closure `ConvexAnalysis.convexCl`. -/
noncomputable def partialCl₂ [TopologicalSpace X] (K : U × X → EReal) : U × X → EReal :=
  fun p => convexCl (fun x => K (p.1, x)) p.2

/-- The **partial closure** $\operatorname{cl}_1 K$ of $K : U \times X \to [-\infty, +\infty]$ in
the first variable: $\operatorname{cl}_1 K(u, x) = (\operatorname{cl} K(\cdot, x))(u)$, where
$\operatorname{cl}$ is the concave closure `ConvexAnalysis.concaveCl`. -/
noncomputable def partialCl₁ [TopologicalSpace U] (K : U × X → EReal) : U × X → EReal :=
  fun p => concaveCl (fun u => K (u, p.2)) p.1

/-- $\operatorname{cl}_2 K(u, x)$ is the convex closure of $K(u, \cdot)$ evaluated at $x$. -/
theorem partialCl₂_apply [TopologicalSpace X] (K : U × X → EReal) (p : U × X) :
    partialCl₂ K p = convexCl (fun x => K (p.1, x)) p.2 := rfl

/-- $\operatorname{cl}_1 K(u, x)$ is the concave closure of $K(\cdot, x)$ evaluated at $u$. -/
theorem partialCl₁_apply [TopologicalSpace U] (K : U × X → EReal) (p : U × X) :
    partialCl₁ K p = concaveCl (fun u => K (u, p.2)) p.1 := rfl

/-- For each $u$, the slice $\operatorname{cl}_2 K(u, \cdot)$ is the convex closure of
$K(u, \cdot)$. -/
theorem partialCl₂_slice [TopologicalSpace X] (K : U × X → EReal) (u : U) :
    (fun x => partialCl₂ K (u, x)) = convexCl fun x => K (u, x) := rfl

/-- For each $x$, the slice $\operatorname{cl}_1 K(\cdot, x)$ is the concave closure of
$K(\cdot, x)$. -/
theorem partialCl₁_slice [TopologicalSpace U] (K : U × X → EReal) (x : X) :
    (fun u => partialCl₁ K (u, x)) = concaveCl fun u => K (u, x) := rfl

/-- $\operatorname{cl}_2 K \le K$. -/
theorem partialCl₂_le [TopologicalSpace X] (K : U × X → EReal) : partialCl₂ K ≤ K :=
  fun p => convexCl_le (fun x => K (p.1, x)) p.2

/-- If $K \le L$, then $\operatorname{cl}_2 K \le \operatorname{cl}_2 L$. -/
theorem partialCl₂_mono [TopologicalSpace X] {K L : U × X → EReal} (h : K ≤ L) :
    partialCl₂ K ≤ partialCl₂ L :=
  fun p => convexCl_mono (fun x => h (p.1, x)) p.2

/-- $K \le \operatorname{cl}_1 K$. -/
theorem le_partialCl₁ [TopologicalSpace U] (K : U × X → EReal) : K ≤ partialCl₁ K :=
  fun p => le_concaveCl (fun u => K (u, p.2)) p.1

/-- If $K \le L$, then $\operatorname{cl}_1 K \le \operatorname{cl}_1 L$. -/
theorem partialCl₁_mono [TopologicalSpace U] {K L : U × X → EReal} (h : K ≤ L) :
    partialCl₁ K ≤ partialCl₁ L :=
  fun p => concaveCl_mono (fun u => h (u, p.2)) p.1

/-- A function $K$ on $U \times X$ is **convex-closed** if $\operatorname{cl}_2 K = K$. -/
def PartialClosed₂ [TopologicalSpace X] (K : U × X → EReal) : Prop := partialCl₂ K = K

/-- A function $K$ on $U \times X$ is **concave-closed** if $\operatorname{cl}_1 K = K$. -/
def PartialClosed₁ [TopologicalSpace U] (K : U × X → EReal) : Prop := partialCl₁ K = K

/-- $K$ is convex-closed if and only if $K(u, \cdot)$ is a closed convex function for every $u$,
that is, it equals its convex closure. -/
theorem partialClosed₂_iff [TopologicalSpace X] {K : U × X → EReal} :
    PartialClosed₂ K ↔ ∀ u, ClosedConvex fun x => K (u, x) := by
  constructor
  · intro h u
    funext x
    exact congrFun h (u, x)
  · intro h
    funext p
    exact congrFun (h p.1) p.2

/-- $K$ is concave-closed if and only if $K(\cdot, x)$ is a closed concave function for every $x$,
that is, it equals its concave closure. -/
theorem partialClosed₁_iff [TopologicalSpace U] {K : U × X → EReal} :
    PartialClosed₁ K ↔ ∀ x, ClosedConcave fun u => K (u, x) := by
  constructor
  · intro h x
    funext u
    exact congrFun h (u, x)
  · intro h
    funext p
    exact congrFun (h p.2) p.1

end PartialCl

/-!
### The swap involution

The map that sends $K$ to $(x, u) \mapsto -K(u, x)$ exchanges the two variables and the two partial
closures. So every statement about the first variable is a statement about the second variable, read
at the swapped function.
-/

section Swap

variable {U X : Type*} {K : U × X → EReal}

/-- The **swap** of $K : U \times X \to [-\infty, +\infty]$ is the function on $X \times U$ given by
$(x, u) \mapsto -K(u, x)$. It is an involution, and it exchanges $\operatorname{cl}_1$ with
$\operatorname{cl}_2$. -/
noncomputable def saddleSwap (K : U × X → EReal) : X × U → EReal := fun q => -(K (q.2, q.1))

/-- The swap of $K$ takes the value $-K(u, x)$ at $(x, u)$. -/
theorem saddleSwap_apply (K : U × X → EReal) (q : X × U) :
    saddleSwap K q = -(K (q.2, q.1)) := rfl

/-- The swap is an involution: swapping $K$ twice gives $K$. -/
@[simp] theorem saddleSwap_saddleSwap (K : U × X → EReal) : saddleSwap (saddleSwap K) = K :=
  funext fun p => neg_neg (K p)

/-- The swap reverses order: if $K \le L$, then the swap of $L$ is at most the swap of $K$. -/
theorem saddleSwap_le_saddleSwap {K L : U × X → EReal} (h : K ≤ L) :
    saddleSwap L ≤ saddleSwap K :=
  fun q => EReal.neg_le_neg_iff.2 (h (q.2, q.1))

/-- The swap as an order isomorphism from the functions on $U \times X$ onto the order dual of the
functions on $X \times U$: $K \le L$ if and only if the swap of $L$ is at most the swap of $K$.

The swap is not an endomorphism, because it exchanges the two factors, so its two-sided inverse
is recorded as an `Equiv`. -/
noncomputable def saddleSwapOrderIso : (U × X → EReal) ≃o (X × U → EReal)ᵒᵈ where
  toFun K := OrderDual.toDual (saddleSwap K)
  invFun K := saddleSwap (OrderDual.ofDual K)
  left_inv := saddleSwap_saddleSwap
  right_inv := saddleSwap_saddleSwap
  map_rel_iff' {K L} := by
    change saddleSwap L ≤ saddleSwap K ↔ K ≤ L
    exact ⟨fun h => by simpa using saddleSwap_le_saddleSwap h, saddleSwap_le_saddleSwap⟩

/-- The order isomorphism `ConvexAnalysis.saddleSwapOrderIso` sends $K$ to its swap. -/
@[simp] theorem saddleSwapOrderIso_apply (K : U × X → EReal) :
    saddleSwapOrderIso K = saddleSwap K := rfl

/-- The swap is injective. -/
theorem saddleSwap_injective :
    Function.Injective (saddleSwap : (U × X → EReal) → X × U → EReal) :=
  (saddleSwapOrderIso (U := U) (X := X)).injective

/-- The **real swap** of $K : U \times X \to \mathbb{R}$ is the function on $X \times U$ given by
$(x, u) \mapsto -K(u, x)$.

The identity `ConvexAnalysis.swapReal_swapReal` is not definitional, because the negation acts
on real values. -/
def swapReal (K : U × X → ℝ) : X × U → ℝ := fun q => -K (q.2, q.1)

/-- The real swap is an involution: swapping $K$ twice gives $K$. -/
@[simp] theorem swapReal_swapReal (K : U × X → ℝ) : swapReal (swapReal K) = K := by
  funext q
  simp [swapReal]

/-- The real swap of $K$ takes the value $-K(u, x)$ at $(x, u)$. -/
theorem swapReal_apply (K : U × X → ℝ) (q : X × U) : swapReal K q = -K (q.2, q.1) := rfl

/-- The first effective domain of the swap of $K$ is $\operatorname{dom}_2 K$. -/
@[simp] theorem dom₁_saddleSwap (K : U × X → EReal) : dom₁ (saddleSwap K) = dom₂ K := by
  ext x
  refine forall_congr' fun u => ?_
  change ⊥ < -(K (u, x)) ↔ K (u, x) < ⊤
  rw [← EReal.neg_top, EReal.neg_lt_neg_iff]

/-- The second effective domain of the swap of $K$ is $\operatorname{dom}_1 K$. -/
@[simp] theorem dom₂_saddleSwap (K : U × X → EReal) : dom₂ (saddleSwap K) = dom₁ K := by
  ext u
  refine forall_congr' fun x => ?_
  change -(K (u, x)) < ⊤ ↔ ⊥ < K (u, x)
  rw [← EReal.neg_bot, EReal.neg_lt_neg_iff]

end Swap

/-! ### Concave-convex functions on a rectangle -/

section ConcaveConvexOn

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- Let $C \subseteq U$ and $D \subseteq X$. A function $K : U \times X \to \mathbb{R}$ is
**concave-convex on $C \times D$** if $K(\cdot, x)$ is concave on $C$ for every $x \in D$ and
$K(u, \cdot)$ is convex on $D$ for every $u \in C$.

This is the finite form, relative to sets, of `ConvexAnalysis.ConcaveConvexFn`. The continuity
theory and the simple-extension theorems of `Numlib.Analysis.Convex.Saddle.Kernel` and
`Numlib.Analysis.Convex.Saddle.Existence` use this hypothesis. -/
structure ConcaveConvexOn (C : Set U) (D : Set X) (K : U × X → ℝ) : Prop where
  /-- The slice $K(\cdot, x)$ is concave on $C$ for every $x \in D$. -/
  concave_fst : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x)
  /-- The slice $K(u, \cdot)$ is convex on $D$ for every $u \in C$. -/
  convex_snd : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x)

variable {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- If $K$ is concave-convex on $C \times D$ and $x \in D$, then $u \mapsto -K(u, x)$ is convex on
$C$. -/
theorem ConcaveConvexOn.convexOn_neg_fst (hK : ConcaveConvexOn C D K) {x : X} (hx : x ∈ D) :
    ConvexOn ℝ C fun u => -K (u, x) :=
  (hK.concave_fst x hx).neg

/-- If $K$ is concave-convex on $C \times D$, then its real swap $(x, u) \mapsto -K(u, x)$ is
concave-convex on $D \times C$.

So every statement about the concave variable is the corresponding statement about the convex
variable, read at the real swap of $K$. -/
theorem ConcaveConvexOn.swapReal (hK : ConcaveConvexOn C D K) :
    ConcaveConvexOn D C (ConvexAnalysis.swapReal K) :=
  ⟨fun w hw => (hK.convex_snd w hw).neg, fun y hy => (hK.concave_fst y hy).neg⟩

end ConcaveConvexOn

section SwapConvex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {K : U × X → EReal}

/-- If $K$ is concave-convex, then its swap $(x, u) \mapsto -K(u, x)$ is concave-convex: negation
exchanges concave and convex, and the swap exchanges the two variables. -/
theorem ConcaveConvexFn.saddleSwap (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (ConvexAnalysis.saddleSwap K) :=
  ⟨fun u => (hK.convex_snd u).concaveFn_neg, fun x => (hK.concave_fst x).convexFn_neg⟩

end SwapConvex

section SwapClosure

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U × X → EReal}

omit [TopologicalSpace U] in
/-- $\operatorname{cl}_1$ of the swap of $K$ is the swap of $\operatorname{cl}_2 K$. -/
theorem partialCl₁_saddleSwap (K : U × X → EReal) :
    partialCl₁ (saddleSwap K) = saddleSwap (partialCl₂ K) :=
  funext fun q => concaveCl_neg (fun x => K (q.2, x)) q.1

omit [TopologicalSpace X] in
/-- $\operatorname{cl}_2$ of the swap of $K$ is the swap of $\operatorname{cl}_1 K$. -/
theorem partialCl₂_saddleSwap (K : U × X → EReal) :
    partialCl₂ (saddleSwap K) = saddleSwap (partialCl₁ K) :=
  funext fun q => (neg_concaveCl (fun u => K (u, q.1)) q.2).symm

end SwapClosure

/-! ### The bracket of a convex bifunction -/

section Bracket

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **bracket** of a bifunction $F$ from $U$ to $X$, with respect to a pairing
$\langle x, y \rangle$ of $X$ with $Y$, is the function $$\langle Fu, y \rangle = (Fu)^*(y) =
\sup_x \{\langle x, y \rangle - (Fu)(x)\}$$ of $(u, y) \in U \times Y$. -/
noncomputable def bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) : U → Y → EReal :=
  fun u y => convexConj Bx (F u) y

/-- $\langle Fu, y \rangle = \sup_x \{\langle x, y \rangle - (Fu)(x)\}$. -/
theorem bracket_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) (y : Y) :
    bracket Bx F u y = ⨆ x, ((Bx x y : ℝ) : EReal) - F u x := rfl

/-- For each $u$, the function $\langle Fu, \cdot \rangle$ is the conjugate $(Fu)^*$. -/
theorem bracket_eq_convexConj (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) :
    bracket Bx F u = convexConj Bx (F u) := rfl

/-- The bracket of $F$ is the conjugate in the second variable of the graph function
$(u, x) \mapsto (Fu)(x)$ of $F$. -/
theorem partialConj₂_graphFn (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (p : U × Y) :
    partialConj₂ Bx (graphFn F) p = bracket Bx F p.1 p.2 := rfl

/-- For every bifunction $F$ and every $u$, the function $\langle Fu, \cdot \rangle$ is convex. -/
theorem convexFn_bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) :
    ConvexFn (bracket Bx F u) :=
  convexFn_convexConj Bx (F u)

end Bracket

section BracketClosed

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx.flip] {F : Bifun U X}

/-- Let $Y$ carry a topology in which it is a topological group, and let the pairing
$\langle x, y \rangle$ of $X$ with $Y$ be such that every $\langle x, \cdot \rangle$ is
continuous on $Y$. For every bifunction $F$ and every $u$, the function
$\langle Fu, \cdot \rangle$ is a closed convex function. -/
theorem closedConvex_bracket (u : U) : ClosedConvex (bracket Bx F u) := closedConvex_convexConj

end BracketClosed

/-! ### The clauses that use convexity of the bifunction -/

section BracketConvex

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X}

/-- If $F$ is a convex bifunction, then $u \mapsto \langle Fu, y \rangle$ is concave for every $y$.

The negative $-\langle Fu, y \rangle = \inf_x \{(Fu)(x) - \langle x, y \rangle\}$ is the infimal
projection of a jointly convex function along $(u, x) \mapsto u$. -/
theorem concaveFn_bracket (hF : ConvexBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) :
    ConcaveFn fun u => bracket Bx F u y := by
  rw [concaveFn_iff_convexFn_neg]
  have hconv : ConvexFn (fun p : U × X => graphFn F p + ((-(Bx p.2 y) : ℝ) : EReal)) := by
    refine convexFn_add_coe hF ?_
    intro p q a b hab
    simp only [Prod.smul_snd, Prod.snd_add, map_add, map_smul, smul_eq_mul, LinearMap.add_apply,
      LinearMap.smul_apply]
    ring
  have hrw : (fun u => -(bracket Bx F u y))
      = fun u => ⨅ x, (graphFn F (u, x) + ((-(Bx x y) : ℝ) : EReal)) := by
    funext u
    rw [bracket_apply, EReal.neg_iSup]
    refine iInf_congr fun x => ?_
    rw [neg_coe_sub']
    exact add_comm _ _
  rw [hrw]
  exact convexFn_iInf_right hconv

/-- If $F$ is a convex bifunction, then its bracket $(u, y) \mapsto \langle Fu, y \rangle$ is
concave-convex. This is part of Theorem 33.1 of [rockafellar1970convex]. -/
theorem concaveConvexFn_bracket (hF : ConvexBifun F) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    ConcaveConvexFn fun p : U × Y => bracket Bx F p.1 p.2 :=
  ⟨fun y => concaveFn_bracket hF Bx y, fun u => convexFn_bracket Bx F u⟩

end BracketConvex

section BracketInversion

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X}

/-- The **inversion formula** for the bracket. Let $X$ be a locally convex topological vector space
with a compatible pairing $\langle x, y \rangle$ with $Y$: every $\langle \cdot, y \rangle$ is
continuous on $X$, and every continuous linear functional on $X$ has this form. If $F$ is a
convex bifunction, then for every $u$ $$\operatorname{cl}(Fu)(x) = \sup_y \{\langle x, y
\rangle - \langle Fu, y \rangle\}.$$ This is part of Theorem 33.1 of [rockafellar1970convex].

The proof is the Fenchel–Moreau theorem, applied uniformly in $u$. -/
theorem convexCl_eq_convexConj_bracket (hF : ConvexBifun F) (u : U) :
    convexCl (F u) = convexConj Bx.flip (bracket Bx F u) :=
  (convexBiconj_eq_convexCl (B := Bx) (hF.convexFn_apply u)).symm

end BracketInversion

/-! ### The bifunction attached to a saddle-function -/

section OfSaddleDefs

variable {U X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The bifunction attached to $K : U \times Y \to [-\infty, +\infty]$, with respect to a pairing
$\langle x, y \rangle$ of $X$ with $Y$, is the bifunction $F$ from $U$ to $X$ with $$(Fu)(x) =
\sup_y \{\langle x, y \rangle - K(u, y)\},$$ the conjugate of $K(u, \cdot)$ with respect to the
flipped pairing. -/
noncomputable def bifunOfSaddle (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) : Bifun U X :=
  fun u x => convexConj Bx.flip (fun y => K (u, y)) x

/-- $(Fu)(x) = \sup_y \{\langle x, y \rangle - K(u, y)\}$ for the bifunction $F$ attached to $K$. -/
theorem bifunOfSaddle_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) (u : U) (x : X) :
    bifunOfSaddle Bx K u x = ⨆ y, ((Bx x y : ℝ) : EReal) - K (u, y) := rfl

end OfSaddleDefs

section OfSaddle

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {K : U × Y → EReal}

/-- If $K$ is concave-convex, then the bifunction attached to $K$ is convex. This is part of Theorem
33.1 of [rockafellar1970convex].

The graph function of the bifunction is a pointwise supremum of jointly convex functions. -/
theorem convexBifun_bifunOfSaddle (hK : ConcaveConvexFn K) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    ConvexBifun (bifunOfSaddle Bx K) := by
  have hconv : ∀ y : Y,
      ConvexFn (fun p : U × X => -(K (p.1, y)) + ((Bx p.2 y : ℝ) : EReal)) := by
    intro y
    refine convexFn_add_coe (f := fun p : U × X => -(K (p.1, y))) ?_ ?_
    · exact convexFn_compLin (LinearMap.fst ℝ U X) ((hK.concave_fst y).convexFn_neg)
    · intro p q a b hab
      simp only [Prod.smul_snd, Prod.snd_add, map_add, map_smul, smul_eq_mul, LinearMap.add_apply,
        LinearMap.smul_apply]
  have hsup : ConvexFn (fun p : U × X => ⨆ y : Y, (-(K (p.1, y)) + ((Bx p.2 y : ℝ) : EReal))) :=
    convexFn_iSup
      (f := fun (y : Y) (p : U × X) => -(K (p.1, y)) + ((Bx p.2 y : ℝ) : EReal)) hconv
  have hrw : graphFn (bifunOfSaddle Bx K)
      = fun p : U × X => ⨆ y : Y, (-(K (p.1, y)) + ((Bx p.2 y : ℝ) : EReal)) := by
    funext p
    rw [graphFn_apply, bifunOfSaddle_apply]
    exact iSup_congr fun y => coe_sub_eq_neg_add
  rw [convexBifun_iff, hrw]
  exact hsup

end OfSaddle

section OfSaddleBracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx.flip] {K : U × Y → EReal}

/-- Let $Y$ be a locally convex topological vector space, and let the pairing $\langle x, y \rangle$
of $X$ with $Y$ be compatible on $Y$: every $\langle x, \cdot \rangle$ is continuous, and every
continuous linear functional on $Y$ has this form. If $K$ is concave-convex on $U \times Y$ and
$F$ is the bifunction attached to $K$, then $\langle Fu, y \rangle = \operatorname{cl}_2 K(u,
y)$ for all $(u, y)$. This is part of Theorem 33.1 of [rockafellar1970convex]. -/
theorem bracket_bifunOfSaddle (hK : ConcaveConvexFn K) (p : U × Y) :
    bracket Bx (bifunOfSaddle Bx K) p.1 p.2 = partialCl₂ K p :=
  congrFun (convexBiconj_eq_convexCl (B := Bx.flip) (hK.convex_snd p.1)) p.2

end OfSaddleBracket

/-! ### Closedness of the partial closures -/

section CorClosed

variable {U X : Type*}

/-- Let $X$ be a commutative topological group. For every $K$ on $U \times X$, the partial closure
$\operatorname{cl}_2 K$ is convex-closed: $\operatorname{cl}_2 \operatorname{cl}_2 K =
\operatorname{cl}_2 K$. -/
theorem partialClosed₂_partialCl₂ [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (K : U × X → EReal) : PartialClosed₂ (partialCl₂ K) :=
  partialClosed₂_iff.2 fun u => closedConvex_convexCl fun x => K (u, x)

/-- Let $U$ be a commutative topological group. For every $K$ on $U \times X$, the partial closure
$\operatorname{cl}_1 K$ is concave-closed: $\operatorname{cl}_1 \operatorname{cl}_1 K =
\operatorname{cl}_1 K$. -/
theorem partialClosed₁_partialCl₁ [TopologicalSpace U] [AddCommGroup U]
    [IsTopologicalAddGroup U] (K : U × X → EReal) : PartialClosed₁ (partialCl₁ K) :=
  partialClosed₁_iff.2 fun x => closedConcave_concaveCl fun u => K (u, x)

end CorClosed

section Cor

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {K : U × X → EReal}

/-- Let $X$ be a topological vector space. If $K$ is concave-convex on $U \times X$, then
$\operatorname{cl}_2 K(u, \cdot)$ is convex for every $u$. -/
theorem convexFn_partialCl₂ [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (hK : ConcaveConvexFn K) (u : U) : ConvexFn fun x => partialCl₂ K (u, x) := by
  rw [partialCl₂_slice]
  exact convexFn_convexCl (hK.convex_snd u)

/-- Let $U$ be a topological vector space. If $K$ is concave-convex on $U \times X$, then
$\operatorname{cl}_1 K(\cdot, x)$ is concave for every $x$. -/
theorem concaveFn_partialCl₁ [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
    (hK : ConcaveConvexFn K) (x : X) : ConcaveFn fun u => partialCl₁ K (u, x) := by
  rw [partialCl₁_slice]
  exact concaveFn_concaveCl (hK.concave_fst x)

end Cor

/-! ### The concave bracket and the bridge to adjoint bifunctions -/

section ConcaveBracket

variable {U V Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- The **bracket** of a bifunction $G$ from $Y$ to $V$, with respect to a pairing
$\langle u, v \rangle$ of $U$ with $V$, is the function $$\langle u, Gy \rangle = \inf_v
\{\langle u, v \rangle - (Gy)(v)\}$$ of $(u, y) \in U \times Y$. It is meant for a concave
bifunction $G$: where `ConvexAnalysis.bracket` takes a convex conjugate in the second variable,
this bracket takes a concave conjugate in the first. -/
noncomputable def concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) : U → Y → EReal :=
  fun u y => concaveConj Bu.flip (G y) u

/-- $\langle u, Gy \rangle = \inf_v \{\langle u, v \rangle - (Gy)(v)\}$. -/
theorem concaveBracket_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) (u : U) (y : Y) :
    concaveBracket Bu G u y = ⨅ v, ((Bu u v : ℝ) : EReal) - G y v := rfl

/-- For each $y$, the function $u \mapsto \langle u, Gy \rangle$ is the concave conjugate of $Gy$
with respect to the flipped pairing. -/
theorem concaveBracket_eq_concaveConj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) (y : Y) :
    (fun u => concaveBracket Bu G u y) = concaveConj Bu.flip (G y) := rfl

end ConcaveBracket

section ConcaveBracketAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Let $G$ be a bifunction from $Y$ to $V$, and let $G^*$ be its adjoint as a concave bifunction,
$(G^* u)(x) = \sup_{(y, v)} \{(Gy)(v) + \langle x, y \rangle - \langle u, v \rangle\}$. Then
$G^*$ is the conjugate in $y$ of the bracket of $G$: $$(G^* u)(x) = \sup_y \{\langle x, y
\rangle - \langle u, Gy \rangle\}.$$

This is the mirror of `ConvexAnalysis.convexAdjointBifun_eq_concaveConj_bracket`, with the two
conjugations in the opposite order. -/
theorem concaveAdjointBifun_eq_convexConj_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (G : Bifun Y V) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx G u x = convexConj Bx.flip (fun y => concaveBracket Bu G u y) x := by
  rw [concaveAdjointBifun_apply, convexConj_apply, iSup_prod]
  refine iSup_congr fun y => ?_
  have hflip : (Bx.flip y x : ℝ) = Bx x y := rfl
  rw [hflip, concaveBracket_apply, coe_sub_eq_neg_add, EReal.neg_iInf,
    EReal.iSup_add_coe]
  refine iSup_congr fun v => ?_
  rw [neg_coe_sub', add_comm (((-(Bu u v) : ℝ) : EReal)) (G y v), add_assoc,
    ← EReal.coe_add]
  congr 2
  ring

end ConcaveBracketAdjoint

section ConcaveBracketConvex

variable {U V Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Y] [Module ℝ Y] {G : Bifun Y V}

omit [AddCommGroup Y] [Module ℝ Y] in
/-- For every bifunction $G$ from $Y$ to $V$ and every $y$, the function
$u \mapsto \langle u, Gy \rangle$ is concave, because it is a concave conjugate. -/
theorem concaveFn_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Bifun Y V) (y : Y) :
    ConcaveFn fun u => concaveBracket Bu G u y :=
  concaveFn_concaveConj Bu.flip (G y)

/-- If $G$ is a concave bifunction from $Y$ to $V$, then $y \mapsto \langle u, Gy \rangle$ is convex
for every $u$.

This is the mirror of `ConvexAnalysis.concaveFn_bracket`. Again the function is an infimal
projection of a jointly convex function. -/
theorem convexFn_concaveBracket (hG : ConcaveBifun G) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u : U) :
    ConvexFn fun y => concaveBracket Bu G u y := by
  have hconv : ConvexFn (fun q : Y × V => -(graphFn G q) + ((Bu u q.2 : ℝ) : EReal)) := by
    refine convexFn_add_coe (concaveBifun_iff.1 hG).convexFn_neg ?_
    intro q r a b hab
    simp only [Prod.smul_snd, Prod.snd_add, map_add, map_smul, smul_eq_mul]
  have hrw : (fun y => concaveBracket Bu G u y)
      = fun y => ⨅ v, (-(graphFn G (y, v)) + ((Bu u v : ℝ) : EReal)) := by
    funext y
    rw [concaveBracket_apply]
    exact iInf_congr fun v => coe_sub_eq_neg_add
  rw [hrw]
  exact convexFn_iInf_right hconv

/-- If $G$ is a concave bifunction from $Y$ to $V$, then its bracket
$(u, y) \mapsto \langle u, Gy \rangle$ is concave-convex. -/
theorem concaveConvexFn_concaveBracket (hG : ConcaveBifun G) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ConcaveConvexFn fun p : U × Y => concaveBracket Bu G p.1 p.2 :=
  ⟨fun y => concaveFn_concaveBracket Bu G y, fun u => convexFn_concaveBracket hG Bu u⟩

end ConcaveBracketConvex

section Adjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **adjoint is the concave conjugate of the bracket**. For every bifunction $F$ from $U$ to
$X$, with pairings of $U$ with $V$ and of $X$ with $Y$, $$(F^* y)(v) = \inf_u \{\langle u, v
\rangle - \langle Fu, y \rangle\}.$$

The bracket and the adjoint are the two halves of one conjugation of the graph function: first
convexly in $x$, then concavely in $u$. So the equation $\langle u, F^* y \rangle =
\operatorname{cl}_1 \langle Fu, y \rangle$ is a case of the concave Fenchel–Moreau theorem. -/
theorem convexAdjointBifun_eq_concaveConj_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (v : V) :
    convexAdjointBifun Bu Bx F y v = concaveConj Bu (fun u => bracket Bx F u y) v := by
  rw [convexAdjointBifun_apply, concaveConj_apply, iInf_prod]
  refine iInf_congr fun u => ?_
  have hneg : ((Bu u v : ℝ) : EReal) - bracket Bx F u y
      = ⨅ x, ((((-(Bx x y) : ℝ) : EReal) + F u x) + ((Bu u v : ℝ) : EReal)) := by
    rw [bracket_apply, coe_sub_eq_neg_add, EReal.neg_iSup, EReal.iInf_add_coe]
    exact iInf_congr fun x => by rw [neg_coe_sub']
  rw [hneg]
  refine iInf_congr fun x => ?_
  rw [add_comm (((-(Bx x y) : ℝ) : EReal)) (F u x), add_assoc, ← EReal.coe_add]
  congr 2
  ring

end Adjoint

/-! ### The adjoint against the two partial closures -/

section AdjointClosureFst

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- Let $U$ be a locally convex topological vector space with a compatible pairing
$\langle u, v \rangle$ with $V$. If $F$ is a convex bifunction from $U$ to $X$, then for every
$y$ the concave conjugate of $F^* y$ is the partial closure of the bracket: $$\inf_v \{\langle
u, v \rangle - (F^* y)(v)\} = \operatorname{cl}_1 \langle Fu, y \rangle \quad \text{for all }
u.$$

The proof identifies $F^* y$ with the concave conjugate of $u \mapsto \langle Fu, y \rangle$
(`ConvexAnalysis.convexAdjointBifun_eq_concaveConj_bracket`) and applies the concave
Fenchel–Moreau theorem to this concave function. -/
theorem concaveConj_convexAdjointBifun_eq_partialCl₁ (hF : ConvexBifun F) (y : Y) :
    concaveConj Bu.flip (fun v => convexAdjointBifun Bu Bx F y v)
      = fun u => partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2) (u, y) := by
  have hbr : (fun v => convexAdjointBifun Bu Bx F y v)
      = concaveConj Bu (fun u => bracket Bx F u y) :=
    funext fun v => convexAdjointBifun_eq_concaveConj_bracket Bu Bx F y v
  rw [hbr]
  exact concaveBiconj_eq_concaveCl (concaveFn_bracket hF Bx y)

/-- Let $U$ be a locally convex topological vector space with a compatible pairing
$\langle u, v \rangle$ with $V$. If $F$ is a convex bifunction from $U$ to $X$, then for every
$y$ $$\langle u, F^* y \rangle = \operatorname{cl}_1 \langle Fu, y \rangle \quad \text{for all }
u,$$ where $\operatorname{cl}_1$ acts on the bracket $(u, y) \mapsto \langle Fu, y \rangle$.
This is the first equation of Theorem 33.2 of [rockafellar1970convex]. -/
theorem concaveBracket_convexAdjointBifun_eq_partialCl₁ (hF : ConvexBifun F) (y : Y) :
    (fun u => concaveBracket Bu (convexAdjointBifun Bu Bx F) u y)
      = fun u => partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2) (u, y) :=
  concaveConj_convexAdjointBifun_eq_partialCl₁ hF y

end AdjointClosureFst

section AdjointClosureConcave

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx.flip]
  {G : Bifun Y V}

/-- Let $Y$ be a locally convex topological vector space, and let the pairing $\langle x, y \rangle$
of $X$ with $Y$ be compatible on $Y$. If $G$ is a concave bifunction from $Y$ to $V$, then for
every $u$ $$\langle G^* u, y \rangle = \operatorname{cl}_2 \langle u, G \cdot \rangle (u, y)
\quad \text{for all } y,$$ where $G^*$ is the adjoint of the concave bifunction $G$.

This is the general form in which the second equation of Theorem 33.2 of [rockafellar1970convex]
is proved: the Fenchel–Moreau theorem on $Y$, applied uniformly in $u$. -/
theorem bracket_concaveAdjointBifun_eq_partialCl₂ (hG : ConcaveBifun G) (u : U) :
    bracket Bx (concaveAdjointBifun Bu Bx G) u
      = fun y => partialCl₂ (fun p : U × Y => concaveBracket Bu G p.1 p.2) (u, y) := by
  have hconj : concaveAdjointBifun Bu Bx G u
      = convexConj Bx.flip (fun y => concaveBracket Bu G u y) :=
    funext fun x => concaveAdjointBifun_eq_convexConj_concaveBracket Bu Bx G u x
  rw [bracket_eq_convexConj, hconj, partialCl₂_slice]
  exact convexBiconj_eq_convexCl (B := Bx.flip) (convexFn_concaveBracket hG Bu u)

end AdjointClosureConcave

section AdjointClosureSnd

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- Let $U$, $X$ and $Y$ be locally convex topological vector spaces. Let the pairing
$\langle u, v \rangle$ of $U$ with $V$ be compatible on $U$, and let the pairing
$\langle x, y \rangle$ of $X$ with $Y$ be compatible on both $X$ and $Y$. If $F$ is a convex
bifunction from $U$ to $X$, then for every $u$ $$\operatorname{cl}_2 \langle u, F^* \cdot
\rangle (u, y) = \langle (\operatorname{cl} F) u, y \rangle \quad \text{for all } y,$$ where
$\operatorname{cl} F$ is the bifunction whose graph function is the closure of the graph
function of $F$. This is the second equation of Theorem 33.2 of [rockafellar1970convex].

The adjoint $F^*$ is concave with no hypothesis on $F$. So the statement is
`ConvexAnalysis.bracket_concaveAdjointBifun_eq_partialCl₂` at $G = F^*$, followed by the
biconjugation identity $F^{**} = \operatorname{cl} F$. -/
theorem partialCl₂_concaveBracket_convexAdjointBifun (hF : ConvexBifun F) (u : U) :
    (fun y => partialCl₂
        (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2) (u, y))
      = bracket Bx (convexClBifun F) u := by
  rw [← concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun (Bu := Bu) (Bx := Bx) hF]
  exact (bracket_concaveAdjointBifun_eq_partialCl₂ (concaveBifun_convexAdjointBifun Bu Bx F) u).symm

end AdjointClosureSnd

/-! ### The clauses that need the correspondence -/

section CorFull

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {K : U × Y → EReal}

omit [AddCommGroup V] [Module ℝ V] in
/-- Let $Y$ be a locally convex topological vector space, and suppose that a pairing
$\langle x, y \rangle$ of some space $X$ with $Y$ is compatible on $Y$. If $K$ is concave-convex
on $U \times Y$, then $\operatorname{cl}_2 K$ is concave-convex. This is part of Corollary
33.1.1 of [rockafellar1970convex].

Concavity in $u$ is not a pointwise property of the closure. The proof writes
$\operatorname{cl}_2 K$ as the bracket of the bifunction attached to $K$, and brackets are
concave-convex. -/
theorem concaveConvexFn_partialCl₂ (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) : ConcaveConvexFn (partialCl₂ K) := by
  have h : (fun p : U × Y => bracket Bx (bifunOfSaddle Bx K) p.1 p.2) = partialCl₂ K :=
    funext fun p => bracket_bifunOfSaddle hK p
  rw [← h]
  exact concaveConvexFn_bracket (convexBifun_bifunOfSaddle hK Bx) Bx

end CorFull

section CorFullFst

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] {K : U × X → EReal}

/-- Let $U$ be a locally convex topological vector space with a compatible pairing
$\langle u, v \rangle$ with some space $V$. If $K$ is concave-convex on $U \times X$, then
$\operatorname{cl}_1 K$ is concave-convex. This is part of Corollary 33.1.1 of
[rockafellar1970convex].

This is the mirror of `ConvexAnalysis.concaveConvexFn_partialCl₂`. The pairing that it needs is
the one on the concave variable. -/
theorem concaveConvexFn_partialCl₁ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (hK : ConcaveConvexFn K) : ConcaveConvexFn (partialCl₁ K) := by
  have h : partialCl₁ K = saddleSwap (partialCl₂ (saddleSwap K)) := by
    rw [partialCl₂_saddleSwap, saddleSwap_saddleSwap]
  rw [h]
  exact (concaveConvexFn_partialCl₂ Bu.flip hK.saddleSwap).saddleSwap

end CorFullFst

end ConvexAnalysis
