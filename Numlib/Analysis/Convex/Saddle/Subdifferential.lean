/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Conjugate

/-!
# Subdifferentials of saddle-functions

Let $U, V, X, Y$ be real vector spaces with pairings $\langle \cdot, \cdot \rangle$ of $U$ with $V$
and of $X$ with $Y$. A saddle-function $K : U \times X \to [-\infty, +\infty]$ is concave in its
first variable and convex in its second, so it has two one-sided subdifferentials: the
superdifferential $\partial_1 K(u, x) \subseteq V$ of the concave slice $K(\cdot, x)$ at $u$, and
the subdifferential $\partial_2 K(u, x) \subseteq Y$ of the convex slice $K(u, \cdot)$ at $x$. Their
product is the subdifferential $\partial K(u, x)$. Two facts make it useful. First,
$(u^*, x^*) \in \partial K(u, x)$ says exactly that $(u, x)$ is a saddle-point of the tilted
function $K - \langle \cdot, u^* \rangle - \langle \cdot, x^* \rangle$. Second, for a closed proper
$K$,
$$\operatorname{ri}(\operatorname{dom} K) \subseteq \operatorname{dom} \partial K \subseteq
  \operatorname{dom} K.$$
The presentation follows [rockafellar1970convex], §23, §35 and §37.

Moreover $\partial K$ depends only on the equivalence class of $K$: for $K$ in the class $\Omega(F)$
of a closed convex bifunction $F$, it is one relation attached to $F$, and the relations of
conjugate classes are inverse to each other. In particular $\partial \bar K^*(0, 0)$ is the set of
saddle-points of $K$, where $\bar K^*$ is the upper conjugate, so $K$ has a saddle-point whenever
the origin lies in $\operatorname{ri}(\operatorname{dom} \bar K^*)$.

## Main definitions

* `ConvexAnalysis.saddleSubdifferential`: $\partial K(u, x) = \partial_1 K(u, x) \times \partial_2
  K(u, x) \subseteq V \times Y$.
* `ConvexAnalysis.domSaddleSubdifferential`: the set $\operatorname{dom} \partial K$ where
  $\partial K$ is nonempty.
* `ConvexAnalysis.saddleTilt`: the tilted function $K - \langle \cdot, u^* \rangle - \langle \cdot,
  x^* \rangle$.
* `ConvexAnalysis.IsBifunSubgradientPair`: the relation $(F u)(x) - \langle x, y \rangle = (F^*
  y)(v) - \langle u, v \rangle$, the subdifferential of a class without a representative.

## Main results

* `ConvexAnalysis.mem_saddleSubdifferential_iff_isSaddlePoint`: subgradients are the tilts at which
  the point is a saddle-point, with no hypotheses on $K$; this is Theorem 37.4 of
  [rockafellar1970convex].
* `ConvexAnalysis.kernelSet_subset_domSaddleSubdifferential_subset_domSaddle`:
  $\operatorname{ri}(\operatorname{dom} K) \subseteq \operatorname{dom} \partial K \subseteq
  \operatorname{dom} K$ for a closed proper $K$.
* `ConvexAnalysis.mem_saddleSubdifferential_iff_isBifunSubgradientPair`,
  `ConvexAnalysis.mem_saddleSubdifferential_upperConjSaddle_iff`: $\partial K$ is one relation
  attached to the class, read from either side; this is Theorem 37.5 of [rockafellar1970convex].
* `ConvexAnalysis.mem_saddleSubdifferential_upperConjSaddle_zero_iff`: $\partial \bar K^*(0, 0)$ is
  the set of saddle-points of $K$.
* `ConvexAnalysis.exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle`: $K$ has a
  saddle-point if $(0, 0) \in \operatorname{ri}(\operatorname{dom} \bar K^*)$.

## Implementation notes

* In $\mathbb{R}^m \times \mathbb{R}^n$ the four spaces coincide. Keeping them apart is what makes
  $\partial \bar K^*$ take values in $U \times Y$.
* The variant $(-v, y) \in \partial f(u, x)$, for the graph function $f$ of $F$, is not equivalent
  to `ConvexAnalysis.IsBifunSubgradientPair` without properness: where
  $(F u)(x) = (F^* y)(v) = +\infty$, the relation reads $+\infty - r = +\infty - s$ and holds, while
  the variant fails. The customary statements do not record this restriction. The form used in
  `Numlib.Analysis.Convex.Saddle.Monotone` assumes `ConvexAnalysis.ProperConvex
  (ConvexAnalysis.graphFn F)`.
-/

namespace ConvexAnalysis

/-! ### Cancelling real coercions across an inequality in `EReal` -/

section ERealSub

/-- Moving a real subtrahend across an inequality in `EReal`: for $z, w \in [-\infty, +\infty]$ and
reals $c, d, e$ with $c - d = e$,
$$z - c \le w - d \iff z \le w + e.$$
There is no side condition, because $c$ and $d$ are finite. The difference $e$ is a parameter
with its defining equation, so that the caller can supply it in any form. -/
theorem sub_coe_le_sub_coe_iff_le_add {z w : EReal} {c d e : ℝ} (he : c - d = e) :
    z - (c : EReal) ≤ w - (d : EReal) ↔ z ≤ w + (e : EReal) := by
  have hw : w - (d : EReal) + (c : EReal) = w + (e : EReal) := by
    induction w with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      linarith
  rw [← (EReal.addLECancellable_coe c).add_le_add_iff_right,
    EReal.sub_add_cancel, hw]

/-- For $z, w \in [-\infty, +\infty]$ and reals $c, d, e$ with $d - c = e$,
$$z - c \le w - d \iff z + e \le w.$$
This is `ConvexAnalysis.sub_coe_le_sub_coe_iff_le_add` with the real number moved to the left. -/
theorem sub_coe_le_sub_coe_iff_add_le {z w : EReal} {c d e : ℝ} (he : d - c = e) :
    z - (c : EReal) ≤ w - (d : EReal) ↔ z + (e : EReal) ≤ w := by
  have hz : z - (c : EReal) + (d : EReal) = z + (e : EReal) := by
    induction z with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      linarith
  rw [← (EReal.addLECancellable_coe d).add_le_add_iff_right,
    EReal.sub_add_cancel, hz]

/-- Subtracting a real number does not change the effective domain: for $z \in [-\infty, +\infty]$
and $c \in \mathbb{R}$, $z - c < +\infty$ if and only if $z < +\infty$. -/
theorem sub_coe_lt_top_iff {z : EReal} {c : ℝ} : z - (c : EReal) < ⊤ ↔ z < ⊤ := by
  induction z with
  | bot => simp
  | top => simp
  | coe r =>
    refine iff_of_true ?_ (EReal.coe_lt_top r)
    rw [← EReal.coe_sub]
    exact EReal.coe_lt_top _

/-- Subtracting a real number does not change the concave effective domain: for
$z \in [-\infty, +\infty]$ and $c \in \mathbb{R}$, $-\infty < z - c$ if and only if
$-\infty < z$. -/
theorem bot_lt_sub_coe_iff {z : EReal} {c : ℝ} : ⊥ < z - (c : EReal) ↔ ⊥ < z := by
  induction z with
  | bot => simp
  | top => simp
  | coe r =>
    refine iff_of_true ?_ (EReal.bot_lt_coe r)
    rw [← EReal.coe_sub]
    exact EReal.bot_lt_coe _

/-- Subtraction from a real number is an involution of `EReal`: for $r \in \mathbb{R}$ and
$z \in [-\infty, +\infty]$, $r - (r - z) = z$. -/
theorem coe_sub_coe_sub_self (r : ℝ) (z : EReal) : (r : EReal) - ((r : EReal) - z) = z := by
  rw [EReal.coe_sub_coe_sub, sub_self, EReal.coe_zero, zero_add]

/-- For $z, w \in [-\infty, +\infty]$ and $r \in \mathbb{R}$, $z = r - w$ if and only if
$r - z = w$. This turns the two conjugate criteria into a common value. -/
theorem eq_coe_sub_iff_coe_sub_eq {z w : EReal} {r : ℝ} :
    z = (r : EReal) - w ↔ (r : EReal) - z = w := by
  constructor
  · intro h
    rw [h, coe_sub_coe_sub_self]
  · intro h
    rw [← h, coe_sub_coe_sub_self]

/-- For $z \in [-\infty, +\infty]$ and $r \in \mathbb{R}$, $-(z - r) = r - z$. -/
theorem neg_sub_coe (z : EReal) (r : ℝ) : -(z - (r : EReal)) = (r : EReal) - z := by
  induction z with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff]
    ring

/-- For $z, w \in [-\infty, +\infty]$ and $r, s \in \mathbb{R}$,
$$z - r = w - s \iff r - z = s - w.$$
-/
theorem sub_coe_eq_sub_coe_comm {z w : EReal} {r s : ℝ} :
    z - (r : EReal) = w - (s : EReal) ↔ (r : EReal) - z = (s : EReal) - w := by
  rw [← neg_sub_coe z r, ← neg_sub_coe w s, _root_.neg_inj]

/-- For $z, w \in [-\infty, +\infty]$ and $r, s \in \mathbb{R}$,
$$z - r = w - s \iff z + s = w + r.$$
-/
theorem sub_coe_eq_sub_coe_iff {z w : EReal} {r s : ℝ} :
    z - (r : EReal) = w - (s : EReal) ↔ z + (s : EReal) = w + (r : EReal) := by
  have hz : z - (r : EReal) + ((r + s : ℝ) : EReal) = z + (s : EReal) := by
    induction z with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      ring
  have hw : w - (s : EReal) + ((r + s : ℝ) : EReal) = w + (r : EReal) := by
    induction w with
    | bot => simp
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_eq_coe_iff]
      ring
  constructor
  · intro h
    rw [← hz, ← hw, h]
  · intro h
    have h2 : z - (r : EReal) + ((r + s : ℝ) : EReal)
        = w - (s : EReal) + ((r + s : ℝ) : EReal) := by rw [hz, hw, h]
    exact le_antisymm
      ((EReal.addLECancellable_coe (r + s)).add_le_add_iff_right.1 h2.le)
      ((EReal.addLECancellable_coe (r + s)).add_le_add_iff_right.1 h2.ge)

/-- **The reflection that exchanges a class with its conjugate class.** For
$z, w \in [-\infty, +\infty]$ and $r, s \in \mathbb{R}$,
$$z - r = w - s \iff -w - r = -z - s.$$
Both sides say $z + s = w + r$. The right side is the left side with the two extended reals
negated and exchanged, which is what conjugation of a bifunction does. -/
theorem sub_coe_eq_sub_coe_iff_neg {z w : EReal} {r s : ℝ} :
    z - (r : EReal) = w - (s : EReal) ↔ -w - (r : EReal) = -z - (s : EReal) := by
  have hw : -w - (r : EReal) = -(w + (r : EReal)) :=
    (EReal.neg_add (.inr (EReal.coe_ne_top r))
      (.inr (EReal.coe_ne_bot r))).symm
  have hz : -z - (s : EReal) = -(z + (s : EReal)) :=
    (EReal.neg_add (.inr (EReal.coe_ne_top s))
      (.inr (EReal.coe_ne_bot s))).symm
  rw [sub_coe_eq_sub_coe_iff, hw, hz, _root_.neg_inj, eq_comm]

end ERealSub

/-! ### The subdifferential of a saddle-function -/

section SaddleSubdifferential

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **subdifferential of a saddle-function** $K : U \times X \to [-\infty, +\infty]$ at
$p = (u, x)$:
$$\partial K(u, x) = \partial_1 K(u, x) \times \partial_2 K(u, x) \subseteq V \times Y,$$
where $\partial_1 K(u, x)$ is the set of supergradients at $u$ of the concave slice
$K(\cdot, x)$ for the pairing $B_u$ of $U$ with $V$, and $\partial_2 K(u, x)$ is the set of
subgradients at $x$ of the convex slice $K(u, \cdot)$ for the pairing $B_x$ of $X$ with $Y$. -/
def saddleSubdifferential (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × X → EReal)
    (p : U × X) : Set (V × Y) :=
  superdifferential Bu (fun u => K (u, p.2)) p.1
    ×ˢ subdifferential Bx (fun x => K (p.1, x)) p.2

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {p : U × X}
  {q : V × Y}

/-- $(v, y) \in \partial K(u, x)$ if and only if $v$ is a supergradient of $K(\cdot, x)$ at $u$ and
$y$ is a subgradient of $K(u, \cdot)$ at $x$. -/
@[simp] theorem mem_saddleSubdifferential :
    q ∈ saddleSubdifferential Bu Bx K p ↔
      q.1 ∈ superdifferential Bu (fun u => K (u, p.2)) p.1 ∧
        q.2 ∈ subdifferential Bx (fun x => K (p.1, x)) p.2 := Iff.rfl

/-- The set $\partial K(u, x)$ is convex, with no hypothesis on $K$. It is even a product of convex
sets, which is what makes the set of saddle-points a convex product set. -/
theorem convex_saddleSubdifferential : Convex ℝ (saddleSubdifferential Bu Bx K p) :=
  Convex.prod convex_superdifferential (convex_subdifferential Bx (fun x => K (p.1, x)) p.2)

/-- The **domain of the subdifferential** of a saddle-function: $\operatorname{dom} \partial K = \{p
\mid \partial K(p) \neq \emptyset\}$. -/
def domSaddleSubdifferential (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) : Set (U × X) :=
  {p | (saddleSubdifferential Bu Bx K p).Nonempty}

/-- $p \in \operatorname{dom} \partial K$ if and only if $\partial K(p)$ is nonempty. -/
@[simp] theorem mem_domSaddleSubdifferential :
    p ∈ domSaddleSubdifferential Bu Bx K ↔ (saddleSubdifferential Bu Bx K p).Nonempty := Iff.rfl

end SaddleSubdifferential

/-! ### Tilting a saddle-function by a linear function -/

section SaddleTilt

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **tilt** of a saddle-function $K : U \times X \to [-\infty, +\infty]$ by
$q = (u^*, x^*) \in V \times Y$:
$$K_q(u, x) = K(u, x) - (\langle u, u^* \rangle + \langle x, x^* \rangle).$$
This is Rockafellar's $K - \langle \cdot, u^* \rangle - \langle \cdot, x^* \rangle$.

The two pairings are added in $\mathbb{R}$ before one real number is subtracted, which keeps the
arithmetic in `EReal` free of side conditions. -/
noncomputable def saddleTilt (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) (q : V × Y) : U × X → EReal :=
  fun p => K p - ((Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : EReal)

/-- The tilt of $K$ by $q = (u^*, x^*)$ takes at $p = (u, x)$ the value $K(u, x) - (\langle u, u^*
\rangle + \langle x, x^* \rangle)$. -/
theorem saddleTilt_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) (q : V × Y) (p : U × X) :
    saddleTilt Bu Bx K q p = K p - ((Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : EReal) := rfl

/-- The tilt of $K$ by $q = 0$ is $K$. -/
@[simp] theorem saddleTilt_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × X → EReal) : saddleTilt Bu Bx K 0 = K := by
  funext p
  rw [saddleTilt_apply]
  norm_num

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {q : V × Y}

/-- Tilting does not change the first effective domain: $\operatorname{dom}_1 K_q =
\operatorname{dom}_1 K$. -/
@[simp] theorem dom₁_saddleTilt : dom₁ (saddleTilt Bu Bx K q) = dom₁ K := by
  ext u
  exact forall_congr' fun x => bot_lt_sub_coe_iff

/-- Tilting does not change the second effective domain: $\operatorname{dom}_2 K_q =
\operatorname{dom}_2 K$. -/
@[simp] theorem dom₂_saddleTilt : dom₂ (saddleTilt Bu Bx K q) = dom₂ K := by
  ext x
  exact forall_congr' fun u => sub_coe_lt_top_iff

/-- The tilt of a proper saddle-function is proper. -/
theorem ProperSaddleFn.saddleTilt (hp : ProperSaddleFn K) :
    ProperSaddleFn (ConvexAnalysis.saddleTilt Bu Bx K q) :=
  ⟨by rw [dom₁_saddleTilt]; exact hp.dom₁_nonempty,
    by rw [dom₂_saddleTilt]; exact hp.dom₂_nonempty⟩

end SaddleTilt

/-! ### Subgradients are saddle-points of the tilted function -/

section TiltCriterion

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal} {p : U × X} {q : V × Y}

/-- Let $K : U \times X \to [-\infty, +\infty]$, $p \in U \times X$ and $q \in V \times Y$. Then
$$q \in \partial K(p) \iff p \text{ is a saddle-point of } K_q,$$
where $K_q = K - \langle \cdot, u^* \rangle - \langle \cdot, x^* \rangle$ is the tilt of $K$ by
$q = (u^*, x^*)$. This is Theorem 37.4 of [rockafellar1970convex].

There are no hypotheses at all: no concavity, no convexity, no properness. Both sides are the
same pair of inequalities, one in each variable, with a real number moved across. -/
theorem mem_saddleSubdifferential_iff_isSaddlePoint :
    q ∈ saddleSubdifferential Bu Bx K p ↔ IsSaddlePoint (saddleTilt Bu Bx K q) p := by
  have h₁ : ∀ u : U, ((Bu u q.1 + Bx p.2 q.2 : ℝ) - (Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : ℝ)
      = Bu (u - p.1) q.1 := by
    intro u
    rw [map_sub, LinearMap.sub_apply]
    ring
  have h₂ : ∀ x : X, ((Bu p.1 q.1 + Bx x q.2 : ℝ) - (Bu p.1 q.1 + Bx p.2 q.2 : ℝ) : ℝ)
      = Bx (x - p.2) q.2 := by
    intro x
    rw [map_sub, LinearMap.sub_apply]
    ring
  have hfst : ∀ u : U,
      saddleTilt Bu Bx K q (u, p.2) ≤ saddleTilt Bu Bx K q p ↔
        K (u, p.2) ≤ K p + ((Bu (u - p.1) q.1 : ℝ) : EReal) := by
    intro u
    rw [saddleTilt_apply, saddleTilt_apply, sub_coe_le_sub_coe_iff_le_add (h₁ u)]
  have hsnd : ∀ x : X,
      saddleTilt Bu Bx K q p ≤ saddleTilt Bu Bx K q (p.1, x) ↔
        K p + ((Bx (x - p.2) q.2 : ℝ) : EReal) ≤ K (p.1, x) := by
    intro x
    rw [saddleTilt_apply, saddleTilt_apply, sub_coe_le_sub_coe_iff_add_le (h₂ x)]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun u => (hfst u).2 (ha u), fun x => (hsnd x).2 (hb x)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun u => (hfst u).1 (ha u), fun x => (hsnd x).1 (hb x)⟩

end TiltCriterion

/-! ### The effective domain of the subdifferential -/

section SubdifferentialDom

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal}

/-- For a proper saddle-function $K$, $\operatorname{dom} \partial K \subseteq \operatorname{dom}
K$; closedness is not needed. A subgradient pair $q$ at $p$ makes $p$ a saddle-point of the tilt
$K_q$, and the saddle-points of a proper saddle-function lie in its effective domain. -/
theorem domSaddleSubdifferential_subset_domSaddle (hp : ProperSaddleFn K) :
    domSaddleSubdifferential Bu Bx K ⊆ domSaddle K := by
  rintro p ⟨q, hq⟩
  have hsp : IsSaddlePoint (saddleTilt Bu Bx K q) p :=
    mem_saddleSubdifferential_iff_isSaddlePoint.1 hq
  have hprop : ProperSaddleFn (saddleTilt Bu Bx K q) := ProperSaddleFn.saddleTilt hp
  have h := IsSaddlePoint.mem_domSaddle hprop hsp
  rw [mem_domSaddle, dom₁_saddleTilt, dom₂_saddleTilt] at h
  exact h

end SubdifferentialDom

section SubdifferentialRelint

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {K : U × X → EReal}

/-- Let $U$ and $X$ be finite-dimensional real normed spaces with compatible pairings $B_u$ and
$B_x$, and let $K$ be a concave-convex function with the structure
`ConvexAnalysis.SaddleStructure` of a closed proper saddle-function. Then
$$\operatorname{ri}(\operatorname{dom}_1 K) \times \operatorname{ri}(\operatorname{dom}_2 K)
  \subseteq \operatorname{dom} \partial K.$$
Over $\operatorname{ri}(\operatorname{dom}_1 K)$ the convex slice $K(u, \cdot)$ is proper with
effective domain exactly $\operatorname{dom}_2 K$, so it has a subgradient at each point of
$\operatorname{ri}(\operatorname{dom}_2 K)$. The concave half is the same statement for
`ConvexAnalysis.saddleSwap K`. -/
theorem kernelSet_subset_domSaddleSubdifferential [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (hK : ConcaveConvexFn K) (hs : SaddleStructure K) :
    kernelSet K ⊆ domSaddleSubdifferential Bu Bx K := by
  rintro ⟨u, x⟩ ⟨hu, hx⟩
  have hudom : u ∈ dom₁ K := intrinsicInterior_subset hu
  have hxdom : x ∈ dom₂ K := intrinsicInterior_subset hx
  have hxr : x ∈ ri (convexDom fun x' => K (u, x')) := by
    rw [hs.1.convexDom_slice u hu]
    exact hx
  obtain ⟨y, hy⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := Bx) (hK.convex_snd u)
    (hs.1.properConvex_slice u hudom) hxr
  have hswapdom : x ∈ dom₁ (saddleSwap K) := by rw [dom₁_saddleSwap]; exact hxdom
  have hswapri : x ∈ ri (dom₁ (saddleSwap K)) := by rw [dom₁_saddleSwap]; exact hx
  have hdomeq : (convexDom fun u' => -(K (u', x))) = dom₁ K := by
    have h := hs.2.convexDom_slice x hswapri
    rw [dom₂_saddleSwap] at h
    exact h
  have hur : u ∈ ri (concaveDom fun u' => K (u', x)) := by
    rw [concaveDom_eq_convexDom_neg, hdomeq]
    exact hu
  have hpr : ProperConvex fun u' => -(K (u', x)) := hs.2.properConvex_slice x hswapdom
  obtain ⟨v, hv⟩ := superdifferential_nonempty_of_mem_relint_concaveDom (B := Bu)
    (hK.concave_fst x) (properConcave_iff_properConvex_neg.2 hpr) hur
  exact ⟨(v, y), hv, hy⟩

/-- Let $U$ and $X$ be finite-dimensional real normed spaces with compatible pairings $B_u$ and
$B_x$, and let $K$ be a closed proper concave-convex function. Then
$$\operatorname{ri}(\operatorname{dom} K) \subseteq \operatorname{dom} \partial K \subseteq
  \operatorname{dom} K.$$

Here $\operatorname{ri}(\operatorname{dom} K)$ is `ConvexAnalysis.kernelSet K`, the product
$\operatorname{ri}(\operatorname{dom}_1 K) \times \operatorname{ri}(\operatorname{dom}_2 K)$,
and $\operatorname{dom} K$ is `ConvexAnalysis.domSaddle K`, the product $\operatorname{dom}_1 K
\times \operatorname{dom}_2 K$. -/
theorem kernelSet_subset_domSaddleSubdifferential_subset_domSaddle [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bx] (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hcl : ClosedSaddleFn K) :
    kernelSet K ⊆ domSaddleSubdifferential Bu Bx K
      ∧ domSaddleSubdifferential Bu Bx K ⊆ domSaddle K :=
  ⟨kernelSet_subset_domSaddleSubdifferential hK ((closedSaddleFn_iff_saddleStructure hK hp).1 hcl),
    domSaddleSubdifferential_subset_domSaddle hp⟩

end SubdifferentialRelint


/-! ### The subdifferential of an equivalence class -/

section BifunPair

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The subgradient relation of a bifunction.** Let $F$ be a bifunction from $U$ to $X$, with
adjoint $F^*$. The point $p = (u, y) \in U \times Y$ and the pair $q = (v, x) \in V \times X$
are in this relation when
$$(F u)(x) - \langle x, y \rangle = (F^* y)(v) - \langle u, v \rangle.$$

This is the case of equality in the chain
$$\langle x, y \rangle - (F u)(x) \le \langle F u, y \rangle \le \langle u, F^* y \rangle \le
  \langle u, v \rangle - (F^* y)(v),$$
where $\langle F u, y \rangle = (F u)^*(y)$ and $\langle u, F^* y \rangle$ are Rockafellar's
brackets. For every $K$ in the class $\Omega(F)$ the relation is exactly membership in
$\partial K$ (`ConvexAnalysis.mem_saddleSubdifferential_iff_isBifunSubgradientPair`). The
adjoint is `ConvexAnalysis.convexAdjointBifun`. -/
def IsBifunSubgradientPair (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (p : U × Y) (q : V × X) : Prop :=
  F p.1 q.2 - ((Bx q.2 p.2 : ℝ) : EReal)
    = convexAdjointBifun Bu Bx F p.2 q.1 - ((Bu p.1 q.1 : ℝ) : EReal)

/-- The subgradient relation, read through the reflection $z \mapsto r - z$: $p = (u, y)$ and
$q = (v, x)$ are in the relation if and only if
$$\langle x, y \rangle - (F u)(x) = \langle u, v \rangle - (F^* y)(v).$$
Both sides are then the common value $K(u, y)$ of the chain. -/
theorem isBifunSubgradientPair_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (p : U × Y) (q : V × X) :
    IsBifunSubgradientPair Bu Bx F p q ↔
      ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2
        = ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 :=
  sub_coe_eq_sub_coe_comm

/-- The defining equation of the subgradient relation: $(F u)(x) - \langle x, y \rangle = (F^*
y)(v) - \langle u, v \rangle$. -/
theorem isBifunSubgradientPair_def (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (p : U × Y) (q : V × X) :
    IsBifunSubgradientPair Bu Bx F p q ↔
      F p.1 q.2 - ((Bx q.2 p.2 : ℝ) : EReal)
        = convexAdjointBifun Bu Bx F p.2 q.1 - ((Bu p.1 q.1 : ℝ) : EReal) := Iff.rfl

end BifunPair

section ClassSubdifferential

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- Let $U, V, X, Y$ be locally convex real topological vector spaces with pairings $B_u$ of $U$
with $V$ and $B_x$ of $X$ with $Y$, such that $B_u$, $B_x$ and their transposes are compatible
pairings. Let $F$ be a closed convex bifunction from $U$ to $X$, and let
$K : U \times Y \to [-\infty, +\infty]$ be in the class $\Omega(F)$. Then for $p = (u, y)$ and
$q = (v, x)$,
$$q \in \partial K(p) \iff (F u)(x) - \langle x, y \rangle = (F^* y)(v) - \langle u, v
  \rangle.$$
In particular $\partial K$ depends only on the class. This is part of Theorem 37.5 of
[rockafellar1970convex].

Here $\partial K$ is `ConvexAnalysis.saddleSubdifferential Bu Bx.flip K`, with values in
$V \times X$. Each half of $\partial K(u, y)$ says that a conjugate of a slice is attained,
$F u$ in the convex variable and $F^* y$ in the concave one, so each says that a difference
equals $K(u, y)$; together they say that the two differences are equal. Conversely the relation
squeezes the chain $\langle x, y \rangle - (F u)(x) \le \langle F u, y \rangle \le K(u, y) \le
\langle u, F^* y \rangle \le \langle u, v \rangle - (F^* y)(v)$ between equal ends. -/
theorem mem_saddleSubdifferential_iff_isBifunSubgradientPair (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (p : U × Y) (q : V × X) :
    q ∈ saddleSubdifferential Bu Bx.flip K p ↔ IsBifunSubgradientPair Bu Bx F p q := by
  have hA : convexConj Bx.flip (fun y => K (p.1, y)) = F p.1 :=
    congrFun (bifunOfSaddle_eq_of_mem_bifunSaddleClass Bu Bx hF hcl hK) p.1
  have hB : concaveConj Bu (fun u => K (u, p.2)) = convexAdjointBifun Bu Bx F p.2 :=
    concaveConj_slice_eq_convexAdjointBifun Bu Bx hF hK p.2
  have h1 : q.1 ∈ superdifferential Bu (fun u => K (u, p.2)) p.1 ↔
      ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 = K p := by
    rw [mem_superdifferential_iff_concaveConj_eq, hB, eq_coe_sub_iff_coe_sub_eq]
  have h2 : q.2 ∈ subdifferential Bx.flip (fun y => K (p.1, y)) p.2 ↔
      ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2 = K p := by
    rw [mem_subdifferential_iff_convexConj_eq, hA, LinearMap.flip_apply, eq_coe_sub_iff_coe_sub_eq]
  rw [isBifunSubgradientPair_iff, mem_saddleSubdifferential, h1, h2]
  constructor
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
  · intro hd
    have hle1 : ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2 ≤ K p :=
      le_trans (sub_le_convexConj Bx (F p.1) q.2 p.2) (hK.1 p)
    have hiinf : concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2
        ≤ ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 := by
      rw [concaveBracket_apply]
      exact iInf_le (fun v => ((Bu p.1 v : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 v) q.1
    have hle2 : K p ≤ ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 :=
      le_trans (hK.2 p) hiinf
    have hle2' : K p ≤ ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2 := by rw [hd]; exact hle2
    have heq1 : ((Bx q.2 p.2 : ℝ) : EReal) - F p.1 q.2 = K p := le_antisymm hle1 hle2'
    have heq2 : ((Bu p.1 q.1 : ℝ) : EReal) - convexAdjointBifun Bu Bx F p.2 q.1 = K p := by
      rw [← hd]; exact heq1
    exact ⟨heq2, heq1⟩

/-- Under the hypotheses of `ConvexAnalysis.mem_saddleSubdifferential_iff_isBifunSubgradientPair`,
let $\bar K^*$ be the upper conjugate of $K$. Then for $p = (u, y)$ and $q = (v, x)$,
$$p \in \partial \bar K^*(q) \iff (F u)(x) - \langle x, y \rangle = (F^* y)(v) - \langle u, v
  \rangle.$$
So the subdifferentials of conjugate classes are inverse to each other, as
$\partial(f^*) = (\partial f)^{-1}$ for convex functions. This is part of Theorem 37.5 of
[rockafellar1970convex].

Here $\partial \bar K^*$ is `ConvexAnalysis.saddleSubdifferential Bu.flip Bx
(ConvexAnalysis.upperConjSaddle Bu Bx K)`, with values in $U \times Y$. The upper conjugate lies
in the class of the bifunction $F_*^*$ for the transposed pairings, and the biadjoint identity
turns the resulting condition into the relation reflected by
`ConvexAnalysis.sub_coe_eq_sub_coe_iff_neg`. -/
theorem mem_saddleSubdifferential_upperConjSaddle_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (p : U × Y) (q : V × X) :
    p ∈ saddleSubdifferential Bu.flip Bx (upperConjSaddle Bu Bx K) q ↔
      IsBifunSubgradientPair Bu Bx F p q := by
  have hGconv : ConvexBifun (lowerAdjointBifun Bu Bx F) := convexBifun_lowerAdjointBifun Bu Bx F
  have := isContinuousPairing_prodPairing_flip Bu Bx
  have hGcl : ClosedConvexBifun (lowerAdjointBifun Bu Bx F) := closedConvexBifun_lowerAdjointBifun
  have hKstar : upperConjSaddle Bu Bx K
      ∈ bifunSaddleClass Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) := by
    rw [saddleClass_conjSaddle Bu Bx hF hcl hK]
    exact mem_saddleClass_right (partialCl₂_upperConjSaddle Bu Bx hF hcl hK)
  have hmain := mem_saddleSubdifferential_iff_isBifunSubgradientPair Bu.flip Bx.flip hGconv hGcl
    hKstar q p
  rw [LinearMap.flip_flip] at hmain
  rw [hmain, isBifunSubgradientPair_def, isBifunSubgradientPair_def,
    convexAdjointBifun_flip_lowerAdjointBifun (Bu := Bu) (Bx := Bx) hF hcl]
  simp only [inverseBifun_apply, LinearMap.flip_apply]
  exact sub_coe_eq_sub_coe_iff_neg.symm

/-- Under the hypotheses of `ConvexAnalysis.mem_saddleSubdifferential_iff_isBifunSubgradientPair`, a
point $p$ belongs to $\partial \bar K^*(0, 0)$ if and only if $p$ is a saddle-point of $K$. That
is, $\partial \bar K^*(0, 0)$ is the set of saddle-points of $K$.

The reading from the conjugate side at $q = 0$ is the direct reading at $q = 0$, which is the
saddle-point property of the untilted $K$. -/
theorem mem_saddleSubdifferential_upperConjSaddle_zero_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (p : U × Y) :
    p ∈ saddleSubdifferential Bu.flip Bx (upperConjSaddle Bu Bx K) 0 ↔ IsSaddlePoint K p := by
  rw [mem_saddleSubdifferential_upperConjSaddle_iff Bu Bx hF hcl hK p 0,
    ← mem_saddleSubdifferential_iff_isBifunSubgradientPair Bu Bx hF hcl hK p 0,
    mem_saddleSubdifferential_iff_isSaddlePoint, saddleTilt_zero]

/-- Under the hypotheses of `ConvexAnalysis.mem_saddleSubdifferential_iff_isBifunSubgradientPair`,
the set of saddle-points of $K$ is convex. -/
theorem convex_setOf_isSaddlePoint (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) : Convex ℝ {p : U × Y | IsSaddlePoint K p} := by
  have hset : {p : U × Y | IsSaddlePoint K p}
      = saddleSubdifferential Bu.flip Bx (upperConjSaddle Bu Bx K) 0 := by
    ext p
    exact (mem_saddleSubdifferential_upperConjSaddle_zero_iff Bu Bx hF hcl hK p).symm
  rw [hset]
  exact convex_saddleSubdifferential

/-- Under the hypotheses of `ConvexAnalysis.mem_saddleSubdifferential_iff_isBifunSubgradientPair`,
$K$ has a saddle-point if and only if $(0, 0) \in \operatorname{dom} \partial \bar K^*$. -/
theorem exists_isSaddlePoint_iff_zero_mem_domSaddleSubdifferential (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    (∃ p, IsSaddlePoint K p) ↔
      (0 : V × X) ∈ domSaddleSubdifferential Bu.flip Bx (upperConjSaddle Bu Bx K) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (mem_saddleSubdifferential_upperConjSaddle_zero_iff Bu Bx hF hcl hK p).2 hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (mem_saddleSubdifferential_upperConjSaddle_zero_iff Bu Bx hF hcl hK p).1 hp⟩

end ClassSubdifferential


/-! ### Existence of a saddle-point -/

section Existence

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- Let $U, V, X, Y$ be real normed spaces, with $V$ and $X$ finite-dimensional, and with pairings
$B_u$ of $U$ with $V$ and $B_x$ of $X$ with $Y$ such that $B_u$, $B_x$ and their transposes are
compatible pairings. Let $F$ be a closed convex bifunction from $U$ to $X$ whose graph function
is proper, and let $K$ be in the class $\Omega(F)$. If
$$(0, 0) \in \operatorname{ri}(\operatorname{dom}_1 \bar K^*) \times
  \operatorname{ri}(\operatorname{dom}_2 \bar K^*),$$
where $\bar K^*$ is the upper conjugate of $K$, then $K$ has a saddle-point.

The product on the right is the relative interior of the effective domain $C^* \times D^*$ of
the conjugate class (`ConvexAnalysis.kernelSet`). The inclusion
$\operatorname{ri}(\operatorname{dom} \bar K^*) \subseteq \operatorname{dom} \partial \bar K^*$
makes $\partial \bar K^*(0, 0)$ nonempty, and this set is the set of saddle-points. The relative
interiors are taken in $V$ and $X$, so only these two spaces need finite dimension. -/
theorem exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h0 : (0 : V × X) ∈ kernelSet (upperConjSaddle Bu Bx K)) : ∃ p, IsSaddlePoint K p := by
  have hcc : ConcaveConvexFn (upperConjSaddle Bu Bx K) :=
    concaveConvexFn_upperConjSaddle Bu Bx hF hcl hK
  have hprop : ProperSaddleFn (upperConjSaddle Bu Bx K) :=
    properSaddleFn_upperConjSaddle Bu Bx hF hcl hpr hK
  have hclosed : ClosedSaddleFn (upperConjSaddle Bu Bx K) :=
    closedSaddleFn_of_mem_saddleClass (partialCl₁_lowerConjSaddle Bu Bx hF hcl hK)
      (partialCl₂_upperConjSaddle Bu Bx hF hcl hK)
      (mem_saddleClass_right (partialCl₂_upperConjSaddle Bu Bx hF hcl hK))
  have hstruct : SaddleStructure (upperConjSaddle Bu Bx K) :=
    (closedSaddleFn_iff_saddleStructure hcc hprop).1 hclosed
  have hmem := kernelSet_subset_domSaddleSubdifferential (Bu := Bu.flip) (Bx := Bx) hcc hstruct h0
  exact (exists_isSaddlePoint_iff_zero_mem_domSaddleSubdifferential Bu Bx hF hcl hK).2 hmem

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- Under the hypotheses of
`ConvexAnalysis.exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle`, if $0$ lies in the
interior of $\operatorname{dom}_1 \bar K^*$ and $0$ lies in the interior of
$\operatorname{dom}_2 \bar K^*$, then $K$ has a saddle-point. This is the hypothesis $(0, 0) \in
\operatorname{int}(\operatorname{dom} \bar K^*) = \operatorname{int} C^* \times
\operatorname{int} D^*$. -/
theorem exists_isSaddlePoint_of_zero_mem_interior_dom_upperConjSaddle
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F))
    (hK : K ∈ bifunSaddleClass Bu Bx F)
    (h₁ : (0 : V) ∈ interior (dom₁ (upperConjSaddle Bu Bx K)))
    (h₂ : (0 : X) ∈ interior (dom₂ (upperConjSaddle Bu Bx K))) : ∃ p, IsSaddlePoint K p :=
  exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle Bu Bx hF hcl hpr hK
    ⟨interior_subset_intrinsicInterior h₁, interior_subset_intrinsicInterior h₂⟩

end Existence

/-! ### The Lagrangian in subgradient form -/

section Lagrangian

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V} {x : X}

/-- Let $U$ be a locally convex real topological vector space with a compatible pairing $B_u$ with
$V$, let $X$ be a real vector space with a topology in which addition is continuous, with any
pairing $B_x$ of $X$ with $Y$, and let $F$ be a closed convex bifunction from $U$ to $X$ whose
graph function is proper. Let $L(v, x) = \inf_u \{\langle u, v \rangle + (F u)(x)\}$ be the
Lagrangian of the problem (P) of minimizing $F 0$. Then $(0, 0) \in \partial L(v, x)$ if and
only if $v$ is a Kuhn–Tucker vector for (P) and $x$ is an optimal solution of (P).

The condition $(0, 0) \in \partial L(v, x)$ says that $(v, x)$ is a saddle-point of $L$, and the
characterization of the Lagrangian gives the rest. The pairing $B_x$ is arbitrary, because the
subgradient tested there is $0$. Here $L$ is `ConvexAnalysis.saddleLagrangian Bu F`, and the
subdifferential uses the transpose of $B_u$. -/
theorem zero_mem_saddleSubdifferential_saddleLagrangian_iff (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) :
    (0 : U × Y) ∈ saddleSubdifferential Bu.flip Bx (saddleLagrangian Bu F) (v, x)
      ↔ v ∈ KuhnTucker Bu F ∧ x ∈ argmin (F 0) := by
  rw [mem_saddleSubdifferential_iff_isSaddlePoint, saddleTilt_zero]
  exact isSaddlePoint_lagrangian_iff hF hcl hpr

end Lagrangian

end ConvexAnalysis
