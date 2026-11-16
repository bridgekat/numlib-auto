/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Extremum.Maximum
import Numlib.Analysis.Convex.Subdifferential.Existence
import Numlib.Analysis.Convex.Subdifferential.Rademacher
import NumlibSurface.Rockafellar.Common.Euclidean
import NumlibSurface.Rockafellar.Chapter02.Section08
import NumlibSurface.Rockafellar.Chapter04.Section19

/-!
# Rockafellar, Section 32: The maximum of a convex function

This module formalizes Section 32 of [rockafellar1970convex] (pp. 342–348): the supremum of a convex
function $f$ on $\mathbb{R}^n$ relative to a set $C$. Maximizing a convex function behaves quite
differently from minimizing one. The maximum principle (Theorem 32.1) says that if $f$ attains its
supremum relative to $C$ at a point of $\operatorname{ri} C$, then $f$ is constant on $C$. So the
supremum is attained on the relative boundary, on a face of $C$, and in the end at an extreme point
(Theorem 32.3 and its four corollaries). Theorem 32.4 expresses the same fact through subgradients:
at a maximizer in $\operatorname{ri}(\operatorname{dom} f)$, every subgradient of $f$ is a non-zero
normal vector to $C$. The proofs specialize the backbone modules
`Numlib.Analysis.Convex.Extremum.Maximum` and `Numlib.Analysis.Convex.Subdifferential.Existence`.

The section has two examples, both with the closed proper convex function
$f(\xi_1, \xi_2) = \xi_1^2 / \xi_2 - \xi_2$ for $\xi_2 > 0$, $f(0, 0) = 0$ and $f = +\infty$
elsewhere, which is the support function of the parabolic set $\{(\xi_1, \xi_2) \mid \xi_1^2 + 4
\xi_2 + 4 \le 0\}$. They show that the hypothesis $C \subseteq \operatorname{ri}(\operatorname{dom}
f)$ of Corollary 32.3.2 cannot be weakened to $C \subseteq \operatorname{dom} f$, even for closed
$f$. On the set $\{\xi_1^2 \le \xi_2 \le 1\}$ the supremum of $f$ is $1$ and is not attained, and on
the set $\{\xi_1^4 \le \xi_2 \le 1\}$ it is $+\infty$.

## Coverage

All 11 numbered results of Section 32 are formalized: Theorems 32.1–32.4 and Corollaries 32.1.1,
32.2.1, 32.3.1–32.3.4 and 32.4.1. The two examples of the section and the unnumbered remarks with
mathematical content are formalized as well.

## Main definitions

* Corollary 32.1.1, `Rockafellar.maximumSet`: the set $W$ of points of $C$ at which the supremum of
  $f$ relative to $C$ is attained.
* Theorem 32.3, `Rockafellar.NoUnboundedHalfLine`: the hypothesis that $C$ contains no half-line on
  which $f$ is unbounded above.
* Corollary 32.3.4, `Rockafellar.linearSystem`: the solution set of a finite system of weak linear
  inequalities $\langle x, a_i \rangle \le \alpha_i$.
* Examples of Section 32, `Rockafellar.parabolicSet`, `Rockafellar.parabolicFn`,
  `Rockafellar.parabolicCap`, `Rockafellar.quarticCap`: the parabolic set, its support function $f$,
  and the two sets $\{\xi_1^2 \le \xi_2 \le 1\}$ and $\{\xi_1^4 \le \xi_2 \le 1\}$.

## Main results

* Theorem 32.1, `Rockafellar.theorem_32_1`, `Rockafellar.theorem_32_1_const`: the maximum principle;
  if a convex $f$ attains its supremum relative to $C \subseteq \operatorname{dom} f$ at a point of
  $\operatorname{ri} C$, then $f$ is constant on $C$.
* Remark after Theorem 32.1, `Rockafellar.theorem_32_1_affineSubspace`,
  `Rockafellar.theorem_32_1_affineSubspace_of_le`: a convex function whose supremum relative to an
  affine set $M$ is attained, or only finite, is constant on $M$.
* Corollary 32.1.1, `Rockafellar.corollary_32_1_1`: the set $W$ is a union of faces of $C$.
* Theorem 32.2, `Rockafellar.theorem_32_2`, `Rockafellar.theorem_32_2_attained`: the supremum of a
  convex function over $\operatorname{conv} S$ equals its supremum over $S$, and the first is
  attained only when the second is.
* Corollary 32.2.1, `Rockafellar.corollary_32_2_1`, `Rockafellar.corollary_32_2_1_attained`: for a
  closed convex set $C$ that is neither an affine set nor a closed half of one, the supremum over
  $C$ equals the supremum over the relative boundary of $C$.
* Theorem 32.3, `Rockafellar.theorem_32_3`, `Rockafellar.theorem_32_3_attained`,
  `Rockafellar.theorem_32_3_containsNoLine`: the supremum over a closed convex
  $C \subseteq \operatorname{dom} f$ with no half-line on which $f$ is unbounded above equals the
  supremum over the extreme points of $C \cap L^\perp$, where $L$ is the lineality space of $C$.
* Corollary 32.3.1, `Rockafellar.corollary_32_3_1`: over a closed convex set that contains no lines,
  an attained supremum is attained at an extreme point.
* Corollary 32.3.2, `Rockafellar.corollary_32_3_2`, `Rockafellar.corollary_32_3_2_finite`,
  `Rockafellar.corollary_32_3_2_iSup`: a proper convex function attains a finite supremum relative
  to a non-empty compact convex $C \subseteq \operatorname{ri}(\operatorname{dom} f)$ at an extreme
  point of $C$.
* Corollary 32.3.3, `Rockafellar.corollary_32_3_3`: over a non-empty polyhedral convex
  $C \subseteq \operatorname{dom} f$ with no half-line on which $f$ is unbounded above, the supremum
  is attained.
* Corollary 32.3.4, `Rockafellar.corollary_32_3_4`, `Rockafellar.corollary_32_3_4_finite`,
  `Rockafellar.corollary_32_3_4_affine`, `Rockafellar.corollary_32_3_4_linearSystem`: a convex
  function bounded above on a non-empty polyhedral convex set with no lines attains its supremum at
  one of the finitely many extreme points; this is the basis of the simplex method.
* Theorem 32.4, `Rockafellar.theorem_32_4_proper`, `Rockafellar.theorem_32_4_nonempty`,
  `Rockafellar.theorem_32_4_normal`, `Rockafellar.theorem_32_4_ne_zero`: at a point
  $x \in \operatorname{ri}(\operatorname{dom} f)$ where $f$ attains its supremum relative to a set
  on which it is not constant, $\partial f(x)$ is non-empty and every $x^* \in \partial f(x)$ is a
  non-zero normal vector to the set at $x$.
* Corollary 32.4.1, `Rockafellar.corollary_32_4_1`: under the same conditions, every
  $x^* \in \partial f(x)$ is non-zero and the linear function $\langle \cdot, x^* \rangle$ attains
  its supremum relative to $S$ at $x$.
* Remark after Theorem 32.4, `Rockafellar.normalCone_closedBall`, `Rockafellar.theorem_32_4_ball`:
  at a maximizer $x$ of $f$ over the Euclidean unit ball, a subgradient has the form $\lambda x$
  with $\lambda > 0$.
* Examples of Section 32, `Rockafellar.parabolicCap_not_attained`,
  `Rockafellar.quarticCap_not_bddAbove`, `Rockafellar.corollary_32_3_2_not_attained_of_subset_dom`,
  `Rockafellar.corollary_32_3_2_not_bddAbove_of_subset_dom`: Corollary 32.3.2 fails, in both
  clauses, when $C \subseteq \operatorname{ri}(\operatorname{dom} f)$ is weakened to
  $C \subseteq \operatorname{dom} f$.

## Conventions

* The effective domain $\operatorname{dom} f = \{x \mid f(x) < +\infty\}$ is
  `ConvexAnalysis.convexDom f`.
* The relative interior $\operatorname{ri} C$ is the backbone notation `ri C`, which stands for the
  Mathlib `intrinsicInterior ℝ C`.
* The supremum of $f$ relative to $C$ is `⨆ x ∈ C, f x` in `EReal`. The supremum over the empty set
  is $-\infty$.
* "$f$ attains its supremum relative to $C$ at $z$" is written `z ∈ C` and `∀ w ∈ C, f w ≤ f z`.
* A proper function is `ConvexAnalysis.ProperConvex f`: $f$ is finite somewhere and never takes the
  value $-\infty$. It does not include convexity, which is the separate hypothesis
  `ConvexAnalysis.ConvexFn f`.
* The coordinates $\xi_1, \xi_2$ of a point `x : Rn 2` are `x 0` and `x 1`.

## Implementation notes

* Theorem 32.3 has two standing hypotheses: $C \subseteq \operatorname{dom} f$, and that $C$
  contains no half-line on which $f$ is unbounded above. The backbone combines them into one
  predicate `ConvexAnalysis.BddAboveOnRays`, which also allows the direction $0$. The statements
  here keep the two hypotheses apart, as the book writes them, and `Rockafellar.bddAboveOnRays_iff`
  relates the two forms.
* The proof of Corollary 32.4.1 applies Theorem 32.4 to $S$ directly, and does not pass to
  $\operatorname{conv} S$ as the book does.

## Deviations from the source

* **Theorem 32.1** (generalization). The book assumes that $C$ is convex. The statement holds for
  every $C \subseteq \operatorname{dom} f$. See `Rockafellar.theorem_32_1`.
* **Corollary 32.3.2**, finiteness of the supremum (correction). The book states that the supremum
  is finite. This fails for the improper function $f \equiv -\infty$. Both declarations of the
  corollary assume that $f$ is proper. See `Rockafellar.corollary_32_3_2_finite`.
* **Theorem 32.4**, normality of subgradients (generalization). Neither the convexity of $f$, nor
  the convexity of $C$, nor $x \in \operatorname{ri}(\operatorname{dom} f)$ is needed. See
  `Rockafellar.theorem_32_4_normal`.
* **Corollary 32.4.1** (generalization). The function $f$ is assumed proper but not convex. See
  `Rockafellar.corollary_32_4_1`.
-/

open scoped Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ} {f : Rn n → EReal} {C : Set (Rn n)}

/-! ### Theorem 32.1: the maximum principle -/

/-- **Theorem 32.1** of [rockafellar1970convex] (the maximum principle). Let $f$ be a convex
function on $\mathbb{R}^n$ and let $C \subseteq \operatorname{dom} f$. If $f$ attains its
supremum relative to $C$ at a point $z \in \operatorname{ri} C$, then $f(x) = f(z)$ for every
$x \in C$.

**Generalization.** The book assumes that $C$ is convex. The proof does not use this. It only
needs that a point of $\operatorname{ri} C$ can be prolonged past itself inside $C$ (Theorem
6.4), so that $z$ is a proper convex combination of $x$ and a further point of $C$. -/
theorem theorem_32_1 (hf : ConvexFn f) (hCdom : C ⊆ convexDom f) {z : Rn n} (hz : z ∈ ri C)
    (hmax : ∀ w ∈ C, f w ≤ f z) {x : Rn n} (hx : x ∈ C) : f x = f z :=
  hf.eq_of_isMaxOn_mem_relint hCdom hz (isMaxOn_iff.2 hmax) hx

/-- **Theorem 32.1** of [rockafellar1970convex], constancy form. Let $f$ be convex on $\mathbb{R}^n$
and let $C \subseteq \operatorname{dom} f$. If $f$ attains its supremum relative to $C$ at a
point of $\operatorname{ri} C$, then $f$ is constant on $C$: $f(x) = f(y)$ for all $x, y \in C$. -/
theorem theorem_32_1_const (hf : ConvexFn f) (hCdom : C ⊆ convexDom f) {z : Rn n} (hz : z ∈ ri C)
    (hmax : ∀ w ∈ C, f w ≤ f z) {x y : Rn n} (hx : x ∈ C) (hy : y ∈ C) : f x = f y := by
  rw [theorem_32_1 hf hCdom hz hmax hx, theorem_32_1 hf hCdom hz hmax hy]

/-- **Section 32** of [rockafellar1970convex], first sentence of the remark after Theorem 32.1. Let
$f$ be convex on $\mathbb{R}^n$ and let $M \subseteq \operatorname{dom} f$ be an affine set. If
$f$ attains its supremum relative to $M$ at $z \in M$, then $f(x) = f(z)$ for every $x \in M$.

This is Theorem 32.1 with $C = M$, where $\operatorname{ri} M = M$. -/
theorem theorem_32_1_affineSubspace (hf : ConvexFn f) {M : AffineSubspace ℝ (Rn n)}
    (hMdom : (M : Set (Rn n)) ⊆ convexDom f) {z : Rn n} (hz : z ∈ M)
    (hmax : ∀ w ∈ (M : Set (Rn n)), f w ≤ f z) {x : Rn n} (hx : x ∈ M) : f x = f z :=
  theorem_32_1 hf hMdom (by rw [AffineSubspace.intrinsicInterior_coe]; exact hz) hmax hx

/-- **Section 32** of [rockafellar1970convex], second sentence of the remark after Theorem 32.1,
which is Corollary 8.6.2. Let $f$ be convex on $\mathbb{R}^n$ and let $M$ be an affine set. If
$f(w) \le \alpha$ for all $w \in M$ and some real $\alpha$, then $f$ is constant on $M$, whether
or not the supremum is attained. -/
theorem theorem_32_1_affineSubspace_of_le (hf : ConvexFn f) {M : AffineSubspace ℝ (Rn n)}
    {α : ℝ} (hM : ∀ w ∈ M, f w ≤ (α : EReal)) {x z : Rn n} (hx : x ∈ M) (hz : z ∈ M) :
    f z = f x :=
  corollary_8_6_2 hf hM hx hz

/-- **Corollary 32.1.1** of [rockafellar1970convex], the set $W$. For
$f : \mathbb{R}^n \to [-\infty, +\infty]$ and $C \subseteq \mathbb{R}^n$, the **maximum set**
$W$ is the set of points $x \in C$ at which the supremum of $f$ relative to $C$ is attained:
$$W = \{x \in C \mid f(w) \le f(x) \text{ for all } w \in C\}.$$
-/
def maximumSet (f : Rn n → EReal) (C : Set (Rn n)) : Set (Rn n) :=
  {x | x ∈ C ∧ ∀ w ∈ C, f w ≤ f x}

/-- A point $x$ is in the maximum set $W$ of $f$ relative to $C$ if and only if $x \in C$ and
$f(w) \le f(x)$ for all $w \in C$. -/
theorem mem_maximumSet {x : Rn n} :
    x ∈ maximumSet f C ↔ x ∈ C ∧ ∀ w ∈ C, f w ≤ f x := Iff.rfl

/-- **Corollary 32.1.1** of [rockafellar1970convex]. Let $f$ be convex on $\mathbb{R}^n$ and let
$C \subseteq \operatorname{dom} f$ be convex. Then the set $W$ of points where the supremum of
$f$ relative to $C$ is attained is a union of faces of $C$:
$$W = \bigcup \{C' \mid C' \text{ is a face of } C \text{ and } C' \subseteq W\}.$$

The set $W$ is `Rockafellar.maximumSet f C`, and a face is `ConvexAnalysis.IsFace`. The
inclusion $\supseteq$ is immediate. For $\subseteq$, Theorem 18.2 gives the face $C'$ of $C$
that has a given maximizer in its relative interior, and Theorem 32.1 applied to $C'$ makes $f$
constant on $C'$. -/
theorem corollary_32_1_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCdom : C ⊆ convexDom f) :
    maximumSet f C = ⋃₀ {C' | IsFace C C' ∧ C' ⊆ maximumSet f C} := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.sUnion_subset fun C' hC' => hC'.2)
  obtain ⟨C', hface, hxC', hconst⟩ :=
    exists_isFace_forall_eq_of_isMaxOn hf hC hCdom hx.1 (isMaxOn_iff.2 hx.2)
  refine ⟨C', ⟨hface, fun y hy => ⟨hface.toIsExtreme.1 hy, fun w hw => ?_⟩⟩, hxC'⟩
  rw [hconst y hy]
  exact hx.2 w hw

/-! ### Theorem 32.2: passing to the convex hull -/

/-- **Theorem 32.2** of [rockafellar1970convex]. Let $f$ be convex on $\mathbb{R}^n$ and let
$S \subseteq \mathbb{R}^n$ be any set. Then
$$\sup_{x \in \operatorname{conv} S} f(x) = \sup_{x \in S} f(x).$$

The sublevel set $\{x \mid f(x) \le \sup_S f\}$ is convex and contains $S$, so it contains
$\operatorname{conv} S$. The proof uses `convexHull_min`, not a Carathéodory decomposition, so
it needs no topology and no bound on the dimension. -/
theorem theorem_32_2 (hf : ConvexFn f) (S : Set (Rn n)) :
    (⨆ x ∈ convexHull ℝ S, f x) = ⨆ x ∈ S, f x :=
  hf.iSup_convexHull S

/-- **Theorem 32.2** of [rockafellar1970convex], attainment. Let $f$ be convex on $\mathbb{R}^n$ and
$S \subseteq \mathbb{R}^n$. If $f$ attains its supremum relative to $\operatorname{conv} S$ at
$x$, then $f(z) = f(x)$ for some $z \in S$. So the first supremum is attained only when the
second (more restrictive) supremum is attained.

The proof uses the strict sublevel set: a convex function that stays strictly below $f(x)$ on
$S$ stays strictly below $f(x)$ on $\operatorname{conv} S$. -/
theorem theorem_32_2_attained (hf : ConvexFn f) {S : Set (Rn n)} {x : Rn n}
    (hx : x ∈ convexHull ℝ S) (hmax : ∀ z ∈ convexHull ℝ S, f z ≤ f x) :
    ∃ z ∈ S, f z = f x :=
  exists_eq_of_isMaxOn_convexHull hf hx (isMaxOn_iff.2 hmax)

/-- **Corollary 32.2.1** of [rockafellar1970convex]. Let $f$ be convex on $\mathbb{R}^n$ and let $C$
be a closed convex set that is neither an affine set nor a closed half of an affine set. Then
$$\sup_{x \in C} f(x) = \sup_{x \in C \setminus \operatorname{ri} C} f(x).$$

The two exceptional cases of the book are one predicate, `ConvexAnalysis.IsAffineHalf`: the
degenerate linear functional $0$ gives the affine sets. The exclusion is necessary: for
$C = [0, \infty)$ the relative boundary is $\{0\}$, while $f(x) = x$ has supremum $+\infty$. The
proof combines Theorem 18.4, in the form $\operatorname{conv}(C \setminus \operatorname{ri} C) =
C$, with Theorem 32.2. -/
theorem corollary_32_2_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) : (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x :=
  hf.iSup_sdiff_relint hC hCcl hhalf

/-- **Corollary 32.2.1** of [rockafellar1970convex], attainment. Let $f$ be convex on $\mathbb{R}^n$
and let $C$ be a closed convex set that is neither an affine set nor a closed half of an affine
set. If $f$ attains its supremum relative to $C$ at $x$, then $f(z) = f(x)$ for some
$z \in C \setminus \operatorname{ri} C$. So the former supremum is attained only when the latter
is attained.

This is the attainment clause of Theorem 32.2 combined with Theorem 18.4. -/
theorem corollary_32_2_1_attained (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) {x : Rn n} (hx : x ∈ C) (hmax : ∀ z ∈ C, f z ≤ f x) :
    ∃ z ∈ C \ ri C, f z = f x :=
  exists_notMem_relint_eq_of_isMaxOn hf hC hCcl hhalf hx (isMaxOn_iff.2 hmax)

/-! ### Theorem 32.3: the extreme point principle -/

/-- **Theorem 32.3** of [rockafellar1970convex], standing hypothesis. A function
$f : \mathbb{R}^n \to [-\infty, +\infty]$ has **no half-line in $C$ on which it is unbounded
above** if for all $u, v$ with $v \neq 0$ and $u + tv \in C$ for all $t \ge 0$, there is a real
$\beta$ with $f(u + tv) \le \beta$ for all $t \ge 0$.

The half-lines are non-degenerate: the direction $v$ is non-zero. Compare
`ConvexAnalysis.BddAboveOnRays`, which also allows $v = 0$. -/
def NoUnboundedHalfLine (f : Rn n → EReal) (C : Set (Rn n)) : Prop :=
  ∀ u v : Rn n, v ≠ 0 → (∀ t : ℝ, 0 ≤ t → u + t • v ∈ C) →
    ∃ β : ℝ, ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)

/-- Let $f : \mathbb{R}^n \to [-\infty, +\infty]$ and $C \subseteq \operatorname{dom} f$. Then $f$
is bounded above on every half-line of $C$ in the sense of the backbone predicate
`ConvexAnalysis.BddAboveOnRays f C` if and only if $C$ contains no half-line on which $f$ is
unbounded above, `Rockafellar.NoUnboundedHalfLine f C`.

The backbone predicate also allows the direction $v = 0$, for which the half-line is the point
$\{u\}$ and the condition says $f(u) < +\infty$. So it combines the two standing hypotheses of
Theorem 32.3 into one. Under $C \subseteq \operatorname{dom} f$ the degenerate case holds
automatically, and the two predicates agree. -/
theorem bddAboveOnRays_iff (hCdom : C ⊆ convexDom f) :
    BddAboveOnRays f C ↔ NoUnboundedHalfLine f C := by
  constructor
  · exact fun h u v _ hray => h u v hray
  · intro h u v hray
    rcases eq_or_ne v 0 with rfl | hv
    · have hu : u ∈ C := by simpa using hray 0 le_rfl
      obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 (mem_convexDom.1 (hCdom hu))
      exact ⟨β, fun t _ => by simpa using hβ.le⟩
    · exact h u v hv hray

/-- **Theorem 32.3** of [rockafellar1970convex]. Let $f$ be convex on $\mathbb{R}^n$ and let
$C \subseteq \operatorname{dom} f$ be a closed convex set. Suppose that there are no half-lines
in $C$ on which $f$ is unbounded above. Let $L$ be the lineality space of $C$ and let $E$ be the
set of extreme points of $C \cap L^\perp$. Then
$$\sup_{x \in C} f(x) = \sup_{x \in E} f(x).$$

The lineality space is `ConvexAnalysis.linealitySubmodule C`, and $L^\perp$ is its orthogonal
complement. The backbone states the theorem for an arbitrary complement $N$ of $L$, because it
does not assume an inner product. This is the case $N = L^\perp$. -/
theorem theorem_32_3 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ convexDom f) (hray : NoUnboundedHalfLine f C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ (C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))).extremePoints ℝ, f x :=
  hf.iSup_extremePoints_inter_of_isCompl hC hCcl ((bddAboveOnRays_iff hCdom).2 hray)
    (Submodule.isCompl_orthogonal _)

/-- **Theorem 32.3** of [rockafellar1970convex], attainment. Under the hypotheses of
`Rockafellar.theorem_32_3`, if $f$ attains its supremum relative to $C$ at $x$, then
$f(z) = f(x)$ for some extreme point $z$ of $C \cap L^\perp$. So the supremum relative to $C$ is
attained only when the supremum relative to $E$ is attained.

The maximizer is moved to $C \cap L^\perp$ along the lineality space, where Corollary 32.3.1
applies. The hypothesis $C \subseteq \operatorname{dom} f$ gives $f(x) < +\infty$ there. -/
theorem theorem_32_3_attained (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ convexDom f) (hray : NoUnboundedHalfLine f C) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ w ∈ C, f w ≤ f x) :
    ∃ z ∈ (C ∩ ((linealitySubmodule C)ᗮ : Set (Rn n))).extremePoints ℝ, f z = f x :=
  exists_mem_extremePoints_inter_eq_of_isMaxOn_of_isCompl hf hC hCcl
    ((bddAboveOnRays_iff hCdom).2 hray) (Submodule.isCompl_orthogonal _) hx (isMaxOn_iff.2 hmax)

/-- **Corollary 32.3.1** of [rockafellar1970convex]. Let $f$ be convex on $\mathbb{R}^n$ and let
$C \subseteq \operatorname{dom} f$ be a closed convex set that contains no lines. If $f$ attains
its supremum relative to $C$ at some $x$, then it also attains it at an extreme point of $C$:
there is an extreme point $z$ of $C$ with $f(z) = f(x)$.

No hypothesis on half-lines is needed, because an attained finite maximum is itself an upper
bound. The hypothesis $C \subseteq \operatorname{dom} f$ gives $f(x) < +\infty$. -/
theorem corollary_32_3_1 (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ convexDom f) (hnl : ContainsNoLine C) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ z ∈ C, f z ≤ f x) : ∃ z ∈ C.extremePoints ℝ, f z = f x :=
  exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine hf hC hCcl hnl hx
    (mem_convexDom.1 (hCdom hx)).ne (isMaxOn_iff.2 hmax)

/-- **Corollary 32.3.2** of [rockafellar1970convex], attainment. Let $f$ be a proper convex function
on $\mathbb{R}^n$ and let $C$ be a non-empty closed bounded convex set with $C \subseteq
\operatorname{ri}(\operatorname{dom} f)$. Then $f$ attains its supremum relative to $C$ at an
extreme point of $C$: there is an extreme point $z$ of $C$ with $f(w) \le f(z)$ for all
$w \in C$.

**Correction.** The book does not assume that $f$ is proper. The hypothesis is needed for the
finiteness clause of the corollary, `Rockafellar.corollary_32_3_2_finite`, and this declaration
carries it too; the attainment clause itself needs no change.

The hypothesis $C \subseteq \operatorname{ri}(\operatorname{dom} f)$ makes $f$ continuous
relative to $C$ (Theorem 10.1). A closed bounded set is compact, and Corollary 32.3.1 moves the
maximizer to an extreme point. -/
theorem corollary_32_3_2 (hf : ConvexFn f) (hp : ProperConvex f) (hne : C.Nonempty)
    (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hCri : C ⊆ ri (convexDom f)) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_isCompact hf hp
    (Metric.isCompact_of_isClosed_isBounded hCcl hCbdd) hCconv hne hCri

/-- **Corollary 32.3.2** of [rockafellar1970convex], finiteness. Let $f$ be a proper convex function
on $\mathbb{R}^n$ and let $C$ be a non-empty closed bounded convex set with $C \subseteq
\operatorname{ri}(\operatorname{dom} f)$. Then the supremum of $f$ relative to $C$ is a real
number.

**Correction.** The book does not assume that $f$ is proper, and the clause is false without it.
For $f \equiv -\infty$ the domain is $\mathbb{R}^n$, so every compact convex $C$ lies in
$\operatorname{ri}(\operatorname{dom} f)$, while the supremum is $-\infty$.

For proper $f$ the supremum is the value at a maximizer, which is real because the maximizer
lies in $\operatorname{dom} f$ and $f$ never takes the value $-\infty$. -/
theorem corollary_32_3_2_finite (hf : ConvexFn f) (hp : ProperConvex f) (hne : C.Nonempty)
    (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hCri : C ⊆ ri (convexDom f)) : ∃ r : ℝ, (⨆ x ∈ C, f x) = (r : EReal) := by
  obtain ⟨z, hz, hzmax⟩ := corollary_32_3_2 hf hp hne hCcl hCbdd hCconv hCri
  have hzC : z ∈ C := extremePoints_subset hz
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z)
    (mem_convexDom.1 (intrinsicInterior_subset (hCri hzC)))
  refine ⟨r, le_antisymm (iSup₂_le fun w hw => hr ▸ hzmax w hw) ?_⟩
  rw [← hr]
  exact le_iSup₂ (f := fun w (_ : w ∈ C) => f w) z hzC

/-- **Corollary 32.3.3** of [rockafellar1970convex]. Let $f$ be convex on $\mathbb{R}^n$ and let
$C \subseteq \operatorname{dom} f$ be a non-empty polyhedral convex set. Suppose that there are
no half-lines in $C$ on which $f$ is unbounded above. Then $f$ attains its supremum relative to
$C$.

The corollary says nothing about extreme points, and it assumes nothing about lines in $C$: a
set that contains a line has no extreme points. -/
theorem corollary_32_3_3 (hf : ConvexFn f) (hC : Polyhedral C) (hne : C.Nonempty)
    (hCdom : C ⊆ convexDom f) (hray : NoUnboundedHalfLine f C) : ∃ z ∈ C, ∀ w ∈ C, f w ≤ f z :=
  exists_isMaxOn_of_polyhedral_of_bddAboveOnRays hf hC hne ((bddAboveOnRays_iff hCdom).2 hray)

/-- **Corollary 32.3.4** of [rockafellar1970convex]. Let $f$ be convex on $\mathbb{R}^n$ and let $C$
be a non-empty polyhedral convex set that contains no lines. If $f(x) \le \beta$ for all
$x \in C$ and some real $\beta$, then $f$ attains its supremum relative to $C$ at one of the
(finitely many) extreme points of $C$.

The corollary combines Corollaries 32.3.1 and 32.3.3. It is the theoretical basis of the simplex
method: it "applies in particular to the problem of maximizing an affine function over the set
of solutions to a finite system of weak linear inequalities", which is
`Rockafellar.corollary_32_3_4_linearSystem`. The real upper bound $\beta$ implies the standing
hypothesis $C \subseteq \operatorname{dom} f$. -/
theorem corollary_32_3_4 (hf : ConvexFn f) (hC : Polyhedral C) (hne : C.Nonempty)
    (hnl : ContainsNoLine C) {β : ℝ} (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_finitelyGenerated hf hC.finitelyGenerated hnl hne hbdd

/-- **Corollary 32.3.4** of [rockafellar1970convex], the parenthetical "(finitely many)". A
polyhedral convex set in $\mathbb{R}^n$ has finitely many extreme points.

A polyhedral set is finitely generated (Theorem 19.1), and the extreme points of
$\operatorname{conv} P + \operatorname{cone} D$ lie in $P$ (Corollary 18.3.1). -/
theorem corollary_32_3_4_finite (hC : Polyhedral C) : (C.extremePoints ℝ).Finite :=
  corollary_19_1_1_extremePoints hC

/-- **Section 32** of [rockafellar1970convex]: "Theorem 32.2 can be applied to a given closed convex
set $C$ by representing $C$ as the convex hull of its extreme points and extreme directions as
in §18." Let $f$ be convex on $\mathbb{R}^n$ and let $C$ be a closed convex set that contains no
lines. Then the supremum of $f$ over $C$ equals its supremum over $\operatorname{ext} C + K$,
where $K$ is the convex cone generated by the extreme directions of $C$.

Unlike Theorem 32.3, this needs no boundedness hypothesis, because the extreme directions are
kept in the index set. The cone $K$ is `PointedCone.hull ℝ (ConvexAnalysis.extremeDirections
C)`, which contains $0$. -/
theorem theorem_32_2_extremePoints_add_coneHull (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set (Rn n)), f x :=
  hf.iSup_extremePoints_add_coneHull hC hCcl hnl

/-- **Section 32** of [rockafellar1970convex], the step of the proof of Theorem 32.3 that cites
Corollary 8.6.2. Let $f$ be convex on $\mathbb{R}^n$ and $C \subseteq \operatorname{dom} f$,
with no half-line in $C$ on which $f$ is unbounded above. Then $f(u + v) = f(u)$ for every
$u \in C$ and every $v$ in the lineality space of $C$: $f$ is constant along every line in $C$. -/
theorem theorem_32_3_const_on_lineality (hf : ConvexFn f) (hCdom : C ⊆ convexDom f)
    (hray : NoUnboundedHalfLine f C) {u v : Rn n} (hu : u ∈ C) (hv : v ∈ linealitySpace C) :
    f (u + v) = f u :=
  hf.add_eq_of_mem_linealitySpace ((bddAboveOnRays_iff hCdom).2 hray) hu hv

/-- **Theorem 32.3** of [rockafellar1970convex], case without lines. Let $f$ be convex on
$\mathbb{R}^n$ and let $C \subseteq \operatorname{dom} f$ be a closed convex set that contains
no lines, with no half-line in $C$ on which $f$ is unbounded above. Then the supremum of $f$
over $C$ equals its supremum over the extreme points of $C$.

Here the lineality space is $\{0\}$ and $C \cap L^\perp = C$. Corollary 32.3.1 is read off from
this form. -/
theorem theorem_32_3_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCdom : C ⊆ convexDom f) (hray : NoUnboundedHalfLine f C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x :=
  hf.iSup_extremePoints_of_containsNoLine hC hCcl hnl ((bddAboveOnRays_iff hCdom).2 hray)

/-- **Corollary 32.3.2** of [rockafellar1970convex], supremum form. Let $f$ be convex on
$\mathbb{R}^n$ and let $C$ be a closed bounded convex set. Then the supremum of $f$ over $C$
equals its supremum over the extreme points of $C$.

This is Minkowski's theorem (Corollary 18.5.1) combined with Theorem 32.2. It needs neither $C
\subseteq \operatorname{ri}(\operatorname{dom} f)$ nor properness; only the attainment clause
does. -/
theorem corollary_32_3_2_iSup (hf : ConvexFn f) (hCcl : IsClosed C)
    (hCbdd : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x :=
  hf.iSup_extremePoints (Metric.isCompact_of_isClosed_isBounded hCcl hCbdd) hCconv

/-- **Corollary 32.3.4** of [rockafellar1970convex], the feasible set of a linear program. For
$a_0, \dots, a_{m-1} \in \mathbb{R}^n$ and real $\alpha_0, \dots, \alpha_{m-1}$, this is the
solution set of the finite system of weak linear inequalities
$$\{x \in \mathbb{R}^n \mid \langle x, a_i \rangle \le \alpha_i \text{ for } i = 0, \dots, m -
  1\}.$$

The index set is `Fin m`, so the indices start at $0$. -/
def linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) : Set (Rn n) :=
  {x : Rn n | ∀ i, pairing n x (a i) ≤ α i}

/-- The solution set of a finite system of weak linear inequalities
$\langle x, a_i \rangle \le \alpha_i$ in $\mathbb{R}^n$ is polyhedral. This is the definition
`ConvexAnalysis.Polyhedral`, written with the index type `Fin m`. -/
theorem polyhedral_linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) :
    Polyhedral (linearSystem a α) := by
  classical
  refine ⟨Finset.image (fun i => (((pairing n).flip (a i) : Rn n →ₗ[ℝ] ℝ), α i)) Finset.univ, ?_⟩
  ext x
  constructor
  · intro hx q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact hx i
  · intro hx i
    exact hx _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)

/-- **Corollary 32.3.4** of [rockafellar1970convex], affine objective. Let $b \in \mathbb{R}^n$,
$\gamma \in \mathbb{R}$, and let $C$ be a non-empty polyhedral convex set that contains no
lines. If $\langle x, b \rangle - \gamma \le \beta$ for all $x \in C$ and some real $\beta$,
then the affine function $x \mapsto \langle x, b \rangle - \gamma$ attains its supremum relative
to $C$ at an extreme point of $C$.

An affine function is convex (`ConvexAnalysis.convexFn_affineFn`) and real-valued, so both
standing hypotheses of the corollary follow from the upper bound. -/
theorem corollary_32_3_4_affine (b : Rn n) (γ : ℝ) (hC : Polyhedral C) (hne : C.Nonempty)
    (hnl : ContainsNoLine C) {β : ℝ} (hbdd : ∀ x ∈ C, pairing n x b - γ ≤ β) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, pairing n w b - γ ≤ pairing n z b - γ := by
  obtain ⟨z, hz, hzmax⟩ := corollary_32_3_4 (convexFn_affineFn b γ) hC hne hnl (β := β)
    fun x hx => by rw [affineFn_eq_coe]; exact_mod_cast hbdd x hx
  refine ⟨z, hz, fun w hw => ?_⟩
  have hle := hzmax w hw
  rw [affineFn_eq_coe, affineFn_eq_coe, EReal.coe_le_coe_iff] at hle
  exact hle

/-- **Corollary 32.3.4** of [rockafellar1970convex], the basis of the simplex method. Let
$a_0, \dots, a_{m-1} \in \mathbb{R}^n$, $\alpha_0, \dots, \alpha_{m-1} \in \mathbb{R}$,
$b \in \mathbb{R}^n$ and $\gamma \in \mathbb{R}$. Let $C = \{x \mid \langle x, a_i \rangle \le
\alpha_i \text{ for all } i\}$ be non-empty and contain no lines. If
$\langle x, b \rangle - \gamma \le \beta$ for all $x \in C$ and some real $\beta$, then there is
an extreme point $z$ of $C$ with
$$\langle w, b \rangle - \gamma \le \langle z, b \rangle - \gamma \quad \text{for all } w \in
  C.$$

The set $C$ is `Rockafellar.linearSystem a α`. -/
theorem corollary_32_3_4_linearSystem {m : ℕ} (a : Fin m → Rn n) (α : Fin m → ℝ) (b : Rn n)
    (γ : ℝ) (hne : (linearSystem a α).Nonempty) (hnl : ContainsNoLine (linearSystem a α))
    {β : ℝ} (hbdd : ∀ x ∈ linearSystem a α, pairing n x b - γ ≤ β) :
    ∃ z ∈ (linearSystem a α).extremePoints ℝ,
      ∀ w ∈ linearSystem a α, pairing n w b - γ ≤ pairing n z b - γ :=
  corollary_32_3_4_affine b γ (polyhedral_linearSystem a α) hne hnl hbdd

/-! ### Theorem 32.4: subgradients at a maximiser -/

/-- **Theorem 32.4** of [rockafellar1970convex], properness. Let $f$ be convex on $\mathbb{R}^n$,
and let $x \in \operatorname{ri}(\operatorname{dom} f)$ with $f(x) \neq -\infty$. Then $f$ is
proper.

The book writes: "here $f$ must be proper by Theorem 7.2, since $f$ is assumed to be finite at a
point of $\operatorname{ri}(\operatorname{dom} f)$". Properness is a consequence of the
hypotheses of the theorem, not one of them. -/
theorem theorem_32_4_proper (hf : ConvexFn f) {x : Rn n} (hxri : x ∈ ri (convexDom f))
    (hxb : f x ≠ ⊥) : ProperConvex f := by
  by_contra himp
  exact hxb (hf.eq_bot_of_mem_relint_convexDom himp hxri)

/-- **Theorem 32.4** of [rockafellar1970convex], non-emptiness of the subdifferential. Let $f$ be
convex on $\mathbb{R}^n$, and let $x \in \operatorname{ri}(\operatorname{dom} f)$ with
$f(x) \neq -\infty$. Then $\partial f(x) \neq \emptyset$ (Theorem 23.4).

This is what gives content to the conclusion of the theorem about every subgradient. -/
theorem theorem_32_4_nonempty (hf : ConvexFn f) {x : Rn n} (hxri : x ∈ ri (convexDom f))
    (hxb : f x ≠ ⊥) : (subdifferential (pairing n) f x).Nonempty :=
  subdifferential_nonempty_of_mem_relint_convexDom hf (theorem_32_4_proper hf hxri hxb) hxri

/-- **Theorem 32.4** of [rockafellar1970convex], normality. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ be finite on $C \subseteq \mathbb{R}^n$, and let $f$
attain its supremum relative to $C$ at $x \in C$. Then every $x^* \in \partial f(x)$ is normal
to $C$ at $x$: $\langle z - x, x^* \rangle \le 0$ for all $z \in C$.

**Generalization.** The book assumes that $f$ is convex, that $C$ is convex and that
$x \in \operatorname{ri}(\operatorname{dom} f)$. Only the finiteness of $f$ on $C$ is used.

The book argues through the sublevel set $D = \{z \mid f(z) \le \alpha\}$ and Theorem 23.7. The
direct argument is one line: for $z \in C$, the subgradient inequality and the maximality of
$f(x)$ give $\langle z - x, x^* \rangle \le f(z) - f(x) \le 0$. The normal cone is
`ConvexAnalysis.normalCone`, and the subdifferential is `ConvexAnalysis.subdifferential` for the
pairing `Rockafellar.pairing n`. -/
theorem theorem_32_4_normal (hfin : ∀ z ∈ C, f z ≠ ⊥ ∧ f z ≠ ⊤) {x : Rn n} (hx : x ∈ C)
    (hmax : ∀ z ∈ C, f z ≤ f x) {y : Rn n} (hy : y ∈ subdifferential (pairing n) f x) :
    y ∈ normalCone (pairing n) C x :=
  mem_normalCone_of_mem_subdifferential_of_isMaxOn (hfin x hx).1 (hfin x hx).2 (isMaxOn_iff.2 hmax)
    hy

/-- **Theorem 32.4** of [rockafellar1970convex], non-zero subgradients. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$, $C \subseteq \mathbb{R}^n$ and $x \in \mathbb{R}^n$
with $f(z) \le f(x)$ for all $z \in C$, and let $z_0 \in C$ with $f(z_0) \neq f(x)$. Then every
$x^* \in \partial f(x)$ is non-zero.

The book argues that $\inf f < f(x)$ because $f$ is not constant on $C$, so
$0 \notin \partial f(x)$. Here the point $z_0$ that shows that $f$ is not constant on $C$ is a
hypothesis, and $x$ need not lie in $C$. -/
theorem theorem_32_4_ne_zero {x : Rn n} (hmax : ∀ z ∈ C, f z ≤ f x) {z₀ : Rn n} (hz₀ : z₀ ∈ C)
    (hne : f z₀ ≠ f x) {y : Rn n} (hy : y ∈ subdifferential (pairing n) f x) : y ≠ 0 :=
  ne_zero_of_mem_subdifferential_of_isMaxOn (isMaxOn_iff.2 hmax) hz₀ hne hy

/-- **Corollary 32.4.1** of [rockafellar1970convex]. Let $f$ be a proper function on $\mathbb{R}^n$,
let $S \subseteq \mathbb{R}^n$, and let $x \in \operatorname{ri}(\operatorname{dom} f)$ with
$f(z) \le f(x)$ for all $z \in S$. Suppose that $f(z_0) \neq f(x)$ for some $z_0 \in S$. Then
every $x^* \in \partial f(x)$ satisfies $x^* \neq 0$ and
$$\langle z, x^* \rangle \le \langle x, x^* \rangle \quad \text{for all } z \in S.$$
When $x \in S$, this says that the linear function $\langle \cdot, x^* \rangle$ attains its
supremum relative to $S$ at $x$.

**Generalization.** The book assumes that $f$ is proper convex. The statement here does not
assume that $f$ is convex.

The book passes to $C = \operatorname{conv} S$ so that Theorem 32.4 applies to a convex set.
This is not necessary: `Rockafellar.theorem_32_4_normal` needs no hypothesis on the set, so it
applies to $S$ itself. -/
theorem corollary_32_4_1 (hp : ProperConvex f) {S : Set (Rn n)} {x : Rn n}
    (hxri : x ∈ ri (convexDom f))
    (hmax : ∀ z ∈ S, f z ≤ f x) {z₀ : Rn n} (hz₀ : z₀ ∈ S) (hne : f z₀ ≠ f x)
    {y : Rn n} (hy : y ∈ subdifferential (pairing n) f x) :
    y ≠ 0 ∧ ∀ z ∈ S, pairing n z y ≤ pairing n x y := by
  refine ⟨ne_zero_of_mem_subdifferential_of_isMaxOn (isMaxOn_iff.2 hmax) hz₀ hne hy,
    fun z hz => ?_⟩
  exact le_of_mem_normalCone (mem_normalCone_of_mem_subdifferential_of_isMaxOn (hp.ne_bot x)
    (mem_convexDom.1 (intrinsicInterior_subset hxri)).ne (isMaxOn_iff.2 hmax) hy) hz

/-- **Section 32** of [rockafellar1970convex], remark after Theorem 32.4. Let $x \in \mathbb{R}^n$
with $|x| = 1$. The vectors normal to the Euclidean unit ball $\{z \mid |z| \le 1\}$ at $x$ are
exactly the vectors $\lambda x$ with $\lambda \ge 0$.

Since `Rockafellar.pairing n` is the inner product `innerₗ (Rn n)`, this is the backbone theorem
`ConvexAnalysis.normalCone_innerₗ_closedBall`, which holds in every real inner product space. -/
theorem normalCone_closedBall {x : Rn n} (hx : ‖x‖ = 1) :
    normalCone (pairing n) (Metric.closedBall (0 : Rn n) 1) x
      = {y : Rn n | ∃ lam : ℝ, 0 ≤ lam ∧ y = lam • x} :=
  normalCone_innerₗ_closedBall hx

/-- **Section 32** of [rockafellar1970convex], remark after Theorem 32.4. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ be finite on the Euclidean unit ball $B$, let $f$
attain its supremum relative to $B$ at $x$ with $|x| = 1$, and let $f$ be non-constant on $B$.
Then every $x^* \in \partial f(x)$ has the form $x^* = \lambda x$ with $\lambda > 0$. So
maximization over $B$ leads to the "eigenvalue" condition $\lambda x \in \partial f(x)$,
$|x| = 1$.

The non-constancy is given by a point $z_0 \in B$ with $f(z_0) \neq f(x)$. -/
theorem theorem_32_4_ball {x : Rn n} (hx : ‖x‖ = 1)
    (hfin : ∀ z ∈ Metric.closedBall (0 : Rn n) 1, f z ≠ ⊥ ∧ f z ≠ ⊤)
    (hmax : ∀ z ∈ Metric.closedBall (0 : Rn n) 1, f z ≤ f x) {z₀ : Rn n}
    (hz₀ : z₀ ∈ Metric.closedBall (0 : Rn n) 1) (hne : f z₀ ≠ f x) {y : Rn n}
    (hy : y ∈ subdifferential (pairing n) f x) : ∃ lam : ℝ, 0 < lam ∧ y = lam • x := by
  have hxmem : x ∈ Metric.closedBall (0 : Rn n) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hx]
  have hyne : y ≠ 0 := theorem_32_4_ne_zero hmax hz₀ hne hy
  have hnormal := theorem_32_4_normal hfin hxmem hmax hy
  rw [normalCone_closedBall hx] at hnormal
  obtain ⟨lam, hlam, rfl⟩ := hnormal
  refine ⟨lam, lt_of_le_of_ne hlam ?_, rfl⟩
  rintro rfl
  exact hyne (by simp)

/-! ### The two examples of Section 32 -/

/-- **Section 32** of [rockafellar1970convex], examples. The **parabolic set** is the closed convex
set
$$K = \{(\xi_1, \xi_2) \in \mathbb{R}^2 \mid \xi_1^2 + 4 \xi_2 + 4 \le 0\}.$$
Its support function is `Rockafellar.parabolicFn`. -/
def parabolicSet : Set (Rn 2) := {y : Rn 2 | y 0 ^ 2 + 4 * y 1 + 4 ≤ 0}

/-- A point $(\xi_1, \xi_2)$ is in the parabolic set if and only if $\xi_1^2 + 4 \xi_2 + 4 \le 0$.
-/
theorem mem_parabolicSet {y : Rn 2} :
    y ∈ parabolicSet ↔ y 0 ^ 2 + 4 * y 1 + 4 ≤ 0 := Iff.rfl

/-- The boundary point $(t, -(t^2 + 4)/4)$ of the parabolic set. -/
private noncomputable def parabolicPoint (t : ℝ) : Rn 2 :=
  WithLp.toLp 2 ![t, -(t ^ 2 + 4) / 4]

private theorem parabolicPoint_zero (t : ℝ) : parabolicPoint t 0 = t := rfl

private theorem parabolicPoint_one (t : ℝ) : parabolicPoint t 1 = -(t ^ 2 + 4) / 4 := rfl

private theorem parabolicPoint_mem (t : ℝ) : parabolicPoint t ∈ parabolicSet := by
  rw [mem_parabolicSet, parabolicPoint_zero, parabolicPoint_one]
  exact le_of_eq (by ring)

/-- The point $(0, s)$ of $\mathbb{R}^2$. -/
private noncomputable def verticalPoint (s : ℝ) : Rn 2 := WithLp.toLp 2 ![0, s]

private theorem verticalPoint_zero (s : ℝ) : verticalPoint s 0 = 0 := rfl

private theorem verticalPoint_one (s : ℝ) : verticalPoint s 1 = s := rfl

private theorem verticalPoint_mem {s : ℝ} (hs : s ≤ -1) : verticalPoint s ∈ parabolicSet := by
  rw [mem_parabolicSet, verticalPoint_zero, verticalPoint_one]
  nlinarith

/-- **Section 32** of [rockafellar1970convex], examples. The function
$f : \mathbb{R}^2 \to (-\infty, +\infty]$ is
$$f(\xi_1, \xi_2) = \begin{cases} \xi_1^2 / \xi_2 - \xi_2 & \text{if } \xi_2 > 0, \\ 0 &
  \text{if } \xi_1 = \xi_2 = 0, \\ +\infty & \text{otherwise.} \end{cases}$$
It is a closed proper convex function, because it is the support function of the parabolic set.

Lean defines $x / 0 = 0$, so the formula of the first case also gives the value $0$ at the
origin. The definition is therefore one infimum `⨅ _ : p, …` over the condition $p$:
$\xi_2 \ge 0$, and $\xi_2 = 0$ implies $\xi_1 = 0$. -/
noncomputable def parabolicFn (x : Rn 2) : EReal :=
  ⨅ _ : 0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0), ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal)

/-- If $\xi_2 \ge 0$, and $\xi_2 = 0$ implies $\xi_1 = 0$, then
$f(\xi_1, \xi_2) = \xi_1^2 / \xi_2 - \xi_2$, with $0 / 0 = 0$. -/
theorem parabolicFn_of_mem {x : Rn 2} (hx : 0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0)) :
    parabolicFn x = ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal) := iInf_pos hx

/-- If neither $\xi_2 > 0$ nor $\xi_1 = \xi_2 = 0$, then $f(\xi_1, \xi_2) = +\infty$. -/
theorem parabolicFn_of_notMem {x : Rn 2} (hx : ¬ (0 ≤ x 1 ∧ (x 1 = 0 → x 0 = 0))) :
    parabolicFn x = ⊤ := iInf_neg hx

/-- **Section 32** of [rockafellar1970convex], examples. The function $f$ is the support function of
the parabolic set $K$: $f(x) = \sup_{y \in K} \langle x, y \rangle$.

This is the verification of convexity and closedness that the book suggests in a parenthesis. -/
theorem supportFn_parabolicSet : supportFn (pairing 2) parabolicSet = parabolicFn := by
  funext y
  by_cases hy : 0 ≤ y 1 ∧ (y 1 = 0 → y 0 = 0)
  · rw [parabolicFn_of_mem hy]
    rcases lt_or_eq_of_le hy.1 with hy1 | hy1
    · have hy1ne : y 1 ≠ 0 := ne_of_gt hy1
      refine le_antisymm (supportFn_le_coe_iff.2 fun x hx => ?_) ?_
      · have hx' : x 0 ^ 2 + 4 * x 1 + 4 ≤ 0 := hx
        rw [pairing_two, le_sub_iff_add_le, le_div_iff₀ hy1]
        nlinarith [sq_nonneg (2 * y 0 - x 0 * y 1),
          mul_nonneg (sq_nonneg (y 1)) (by linarith : (0 : ℝ) ≤ -(x 0 ^ 2 + 4 * x 1 + 4))]
      · have hval : pairing 2 (parabolicPoint (2 * y 0 / y 1)) y = y 0 ^ 2 / y 1 - y 1 := by
          rw [pairing_two, parabolicPoint_zero, parabolicPoint_one]
          field_simp
          ring
        rw [← hval]
        exact le_supportFn (parabolicPoint_mem _) y
    · have hy1' : y 1 = 0 := hy1.symm
      have hy0 : y 0 = 0 := hy.2 hy1'
      have hzero : ∀ x : Rn 2, pairing 2 x y = 0 := by
        intro x; rw [pairing_two, hy0, hy1']; ring
      have hsup : supportFn (pairing 2) parabolicSet y = ((0 : ℝ) : EReal) := by
        refine le_antisymm (supportFn_le_coe_iff.2 fun x _ => le_of_eq (hzero x)) ?_
        rw [← hzero (parabolicPoint 0)]
        exact le_supportFn (parabolicPoint_mem 0) y
      rw [hsup, hy0, hy1']
      norm_num
  · rw [parabolicFn_of_notMem hy, EReal.eq_top_iff_forall_lt]
    intro c
    by_cases hy1 : 0 ≤ y 1
    · have hy1' : y 1 = 0 := by
        by_contra h
        exact hy ⟨hy1, fun hc => absurd hc h⟩
      have hy0 : y 0 ≠ 0 := fun h => hy ⟨hy1, fun _ => h⟩
      have hval : pairing 2 (parabolicPoint ((c + 1) / y 0)) y = c + 1 := by
        rw [pairing_two, parabolicPoint_zero, hy1', mul_zero, add_zero]
        field_simp
      have hle := le_supportFn (B := pairing 2) (parabolicPoint_mem ((c + 1) / y 0)) y
      rw [hval] at hle
      exact lt_of_lt_of_le (by exact_mod_cast (by linarith : c < c + 1)) hle
    · have hyneg : y 1 < 0 := not_le.1 hy1
      have hy1ne : y 1 ≠ 0 := ne_of_lt hyneg
      have hnn : 0 ≤ (|c| + 1) / (-y 1) := div_nonneg (by positivity) (by linarith)
      have hs : -1 - (|c| + 1) / (-y 1) ≤ -1 := by linarith
      have hval : pairing 2 (verticalPoint (-1 - (|c| + 1) / (-y 1))) y = -y 1 + (|c| + 1) := by
        rw [pairing_two, verticalPoint_zero, verticalPoint_one]
        field_simp
        ring
      have hle := le_supportFn (B := pairing 2) (verticalPoint_mem hs) y
      rw [hval] at hle
      refine lt_of_lt_of_le ?_ hle
      exact_mod_cast (by cases abs_cases c <;> linarith : c < -y 1 + (|c| + 1))

/-- The function $f$ of the examples of Section 32 is convex. -/
theorem convexFn_parabolicFn : ConvexFn parabolicFn := by
  rw [← supportFn_parabolicSet]; exact convexFn_supportFn _ _

/-- The function $f$ of the examples of Section 32 is closed. -/
theorem closedConvex_parabolicFn : ClosedConvex parabolicFn := by
  rw [← supportFn_parabolicSet]; exact closedConvex_supportFn

/-- The function $f$ of the examples of Section 32 is proper. -/
theorem properConvex_parabolicFn : ProperConvex parabolicFn := by
  rw [← supportFn_parabolicSet]
  exact properConvex_supportFn ⟨parabolicPoint 0, parabolicPoint_mem 0⟩

/-!
### The two caps

The sets $\{(\xi_1, \xi_2) \mid g(\xi_1) \le \xi_2 \le 1\}$ for $g(t) = t^2$ and $g(t) = t^4$, and
their properties.
-/

private def cap (g : ℝ → ℝ) : Set (Rn 2) := {x : Rn 2 | g (x 0) ≤ x 1 ∧ x 1 ≤ 1}

private theorem zero_mem_cap {g : ℝ → ℝ} (hg0 : g 0 ≤ 0) : (0 : Rn 2) ∈ cap g := by
  have h0 : (0 : Rn 2) 0 = 0 := by simp
  have h1 : (0 : Rn 2) 1 = 0 := by simp
  exact ⟨by rw [h0, h1]; exact hg0, by rw [h1]; norm_num⟩

private theorem isClosed_cap {g : ℝ → ℝ} (hgc : Continuous g) : IsClosed (cap g) := by
  have hc0 : Continuous fun x : Rn 2 => x 0 := by fun_prop
  have hc1 : Continuous fun x : Rn 2 => x 1 := by fun_prop
  have hcg : Continuous fun x : Rn 2 => g (x 0) := hgc.comp hc0
  exact (isClosed_le hcg hc1).inter (isClosed_le hc1 continuous_const)

private theorem isBounded_cap {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgsq : ∀ t : ℝ, g t ≤ 1 → t ^ 2 ≤ 1) : Bornology.IsBounded (cap g) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, fun x hx => ?_⟩
  have hx1nn : 0 ≤ x 1 := le_trans (hgnn _) hx.1
  have hsq : x 0 ^ 2 ≤ 1 := hgsq _ (le_trans hx.1 hx.2)
  have hnorm : ‖x‖ = Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    congr 1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  rw [hnorm]
  have hle : x 0 ^ 2 + x 1 ^ 2 ≤ 4 := by nlinarith [hx.2]
  calc Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hle
    _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- The convexity inequality $(ap + bq)^2 \le a p^2 + b q^2$ for $a, b \ge 0$ with $a + b = 1$. -/
private theorem sq_combo_le {p q a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * p + b * q) ^ 2 ≤ a * p ^ 2 + b * q ^ 2 := by
  have key : a * p ^ 2 + b * q ^ 2 - (a * p + b * q) ^ 2 = a * b * (p - q) ^ 2 := by
    linear_combination (-(a * p ^ 2 + b * q ^ 2)) * hab
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p - q))]

/-- The convexity inequality $(ap + bq)^4 \le a p^4 + b q^4$ for $a, b \ge 0$ with $a + b = 1$. -/
private theorem quartic_combo_le {p q a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * p + b * q) ^ 4 ≤ a * p ^ 4 + b * q ^ 4 :=
  calc (a * p + b * q) ^ 4 = ((a * p + b * q) ^ 2) ^ 2 := by ring
    _ ≤ (a * p ^ 2 + b * q ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) (sq_combo_le ha hb hab) 2
    _ ≤ a * (p ^ 2) ^ 2 + b * (q ^ 2) ^ 2 := sq_combo_le ha hb hab
    _ = a * p ^ 4 + b * q ^ 4 := by ring

private theorem convex_cap {g : ℝ → ℝ}
    (hg : ∀ p q a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      g (a * p + b * q) ≤ a * g p + b * g q) :
    Convex ℝ (cap g) := by
  intro x hx y hy a b ha hb hab
  have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := rfl
  have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := rfl
  have hcv := hg (x 0) (y 0) a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [h0, h1]
    have h₁ := mul_le_mul_of_nonneg_left hx.1 ha
    have h₂ := mul_le_mul_of_nonneg_left hy.1 hb
    linarith
  · rw [h1]
    have h₁ := mul_le_mul_of_nonneg_left hx.2 ha
    have h₂ := mul_le_mul_of_nonneg_left hy.2 hb
    linarith

private theorem parabolicFn_cap {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgz : ∀ t : ℝ, g t ≤ 0 → t = 0) {x : Rn 2} (hx : x ∈ cap g) :
    parabolicFn x = ((x 0 ^ 2 / x 1 - x 1 : ℝ) : EReal) :=
  parabolicFn_of_mem ⟨le_trans (hgnn _) hx.1, fun h => hgz _ (h ▸ hx.1)⟩

private theorem cap_subset_convexDom {g : ℝ → ℝ} (hgnn : ∀ t : ℝ, 0 ≤ g t)
    (hgz : ∀ t : ℝ, g t ≤ 0 → t = 0) : cap g ⊆ convexDom parabolicFn := fun x hx => by
  rw [mem_convexDom, parabolicFn_cap hgnn hgz hx]
  exact EReal.coe_lt_top _

private noncomputable def capPoint (k : ℕ) (t : ℝ) : Rn 2 := WithLp.toLp 2 ![t, t ^ k]

private theorem capPoint_zero (k : ℕ) (t : ℝ) : capPoint k t 0 = t := rfl

private theorem capPoint_one (k : ℕ) (t : ℝ) : capPoint k t 1 = t ^ k := rfl

private theorem capPoint_mem {k : ℕ} {t : ℝ} (ht : t ^ k ≤ 1) :
    capPoint k t ∈ cap (fun s : ℝ => s ^ k) :=
  ⟨le_of_eq (by rw [capPoint_zero, capPoint_one]), by rw [capPoint_one]; exact ht⟩

private theorem sq_nonneg' : ∀ t : ℝ, 0 ≤ t ^ 2 := fun t => sq_nonneg t

private theorem sq_eq_zero' : ∀ t : ℝ, t ^ 2 ≤ 0 → t = 0 := fun t h =>
  pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg t))

private theorem quartic_nonneg : ∀ t : ℝ, 0 ≤ t ^ 4 := fun t => by positivity

private theorem quartic_eq_zero : ∀ t : ℝ, t ^ 4 ≤ 0 → t = 0 := fun t h =>
  pow_eq_zero_iff (by norm_num) |>.1 (le_antisymm h (by positivity))

/-- **Section 32** of [rockafellar1970convex], first example. The set
$$C = \{(\xi_1, \xi_2) \in \mathbb{R}^2 \mid \xi_1^2 \le \xi_2 \le 1\}.$$
-/
def parabolicCap : Set (Rn 2) := {x : Rn 2 | x 0 ^ 2 ≤ x 1 ∧ x 1 ≤ 1}

/-- **Section 32** of [rockafellar1970convex], second example. The set
$$D = \{(\xi_1, \xi_2) \in \mathbb{R}^2 \mid \xi_1^4 \le \xi_2 \le 1\}.$$
-/
def quarticCap : Set (Rn 2) := {x : Rn 2 | x 0 ^ 4 ≤ x 1 ∧ x 1 ≤ 1}

private theorem parabolicCap_eq : parabolicCap = cap (fun t : ℝ => t ^ 2) := rfl

private theorem quarticCap_eq : quarticCap = cap (fun t : ℝ => t ^ 4) := rfl

/-- The origin lies in the set $C = \{\xi_1^2 \le \xi_2 \le 1\}$. -/
theorem zero_mem_parabolicCap : (0 : Rn 2) ∈ parabolicCap := by
  rw [parabolicCap_eq]; exact zero_mem_cap (by norm_num)

/-- The set $C = \{\xi_1^2 \le \xi_2 \le 1\}$ is closed. -/
theorem isClosed_parabolicCap : IsClosed parabolicCap := by
  rw [parabolicCap_eq]; exact isClosed_cap (by fun_prop)

/-- The set $C = \{\xi_1^2 \le \xi_2 \le 1\}$ is bounded. -/
theorem isBounded_parabolicCap : Bornology.IsBounded parabolicCap := by
  rw [parabolicCap_eq]; exact isBounded_cap sq_nonneg' fun _ h => h

/-- The set $C = \{\xi_1^2 \le \xi_2 \le 1\}$ is convex. -/
theorem convex_parabolicCap : Convex ℝ parabolicCap := by
  rw [parabolicCap_eq]; exact convex_cap fun _ _ _ _ ha hb hab => sq_combo_le ha hb hab

/-- The set $C = \{\xi_1^2 \le \xi_2 \le 1\}$ is contained in the domain of the function $f$ of the
examples. -/
theorem parabolicCap_subset_convexDom : parabolicCap ⊆ convexDom parabolicFn := by
  rw [parabolicCap_eq]; exact cap_subset_convexDom sq_nonneg' sq_eq_zero'

/-- The origin lies in the set $D = \{\xi_1^4 \le \xi_2 \le 1\}$. -/
theorem zero_mem_quarticCap : (0 : Rn 2) ∈ quarticCap := by
  rw [quarticCap_eq]; exact zero_mem_cap (by norm_num)

/-- The set $D = \{\xi_1^4 \le \xi_2 \le 1\}$ is closed. -/
theorem isClosed_quarticCap : IsClosed quarticCap := by
  rw [quarticCap_eq]; exact isClosed_cap (by fun_prop)

/-- The set $D = \{\xi_1^4 \le \xi_2 \le 1\}$ is bounded. -/
theorem isBounded_quarticCap : Bornology.IsBounded quarticCap := by
  rw [quarticCap_eq]
  exact isBounded_cap quartic_nonneg fun t h => by nlinarith [sq_nonneg t, sq_nonneg (t ^ 2 - 1)]

/-- The set $D = \{\xi_1^4 \le \xi_2 \le 1\}$ is convex. -/
theorem convex_quarticCap : Convex ℝ quarticCap := by
  rw [quarticCap_eq]; exact convex_cap fun _ _ _ _ ha hb hab => quartic_combo_le ha hb hab

/-- The set $D = \{\xi_1^4 \le \xi_2 \le 1\}$ is contained in the domain of the function $f$ of the
examples. -/
theorem quarticCap_subset_convexDom : quarticCap ⊆ convexDom parabolicFn := by
  rw [quarticCap_eq]; exact cap_subset_convexDom quartic_nonneg quartic_eq_zero

/-! ### The first example: a supremum that is not attained -/

/-- **Section 32** of [rockafellar1970convex], first example: "clearly $f(\xi_1, \xi_2) < 1$
throughout $C$". For every $(\xi_1, \xi_2) \in C = \{\xi_1^2 \le \xi_2 \le 1\}$,
$f(\xi_1, \xi_2) < 1$.

On $C$ one has $\xi_1^2 \le \xi_2$, so $\xi_1^2 / \xi_2 \le 1$ and $f \le 1 - \xi_2 < 1$ when
$\xi_2 > 0$. The case $\xi_2 = 0$ forces the origin, where $f = 0$. -/
theorem parabolicFn_lt_one_of_mem_parabolicCap {x : Rn 2} (hx : x ∈ parabolicCap) :
    parabolicFn x < ((1 : ℝ) : EReal) := by
  rw [parabolicFn_cap (g := fun t : ℝ => t ^ 2) sq_nonneg' sq_eq_zero' hx,
    EReal.coe_lt_coe_iff]
  rcases eq_or_lt_of_le (le_trans (sq_nonneg (x 0)) hx.1) with h | h
  · have hx0 : x 0 = 0 := sq_eq_zero' _ (h ▸ hx.1)
    rw [hx0, ← h]
    norm_num
  · have hdiv : x 0 ^ 2 / x 1 ≤ 1 := (div_le_one h).2 hx.1
    linarith

/-- **Section 32** of [rockafellar1970convex], first example: "the value of $f(\xi_1, \xi_2)$
approaches $1$ as $(\xi_1, \xi_2)$ moves toward $(0, 0)$ along the boundary of $C$". For
$t \neq 0$ with $t^2 \le 1$, the boundary point $(t, t^2)$ of $C$ has $f(t, t^2) = 1 - t^2$. -/
theorem parabolicFn_capPoint {t : ℝ} (ht : t ≠ 0) (ht1 : t ^ 2 ≤ 1) :
    parabolicFn (capPoint 2 t) = ((1 - t ^ 2 : ℝ) : EReal) := by
  rw [parabolicFn_cap sq_nonneg' sq_eq_zero' (capPoint_mem ht1), capPoint_zero, capPoint_one,
    div_self (pow_ne_zero 2 ht)]

/-- **Section 32** of [rockafellar1970convex], first example: "thus $1$ is the supremum of $f$
relative to $C$, and this supremum is not attained". There is no
$z \in C = \{\xi_1^2 \le \xi_2 \le 1\}$ with $f(w) \le f(z)$ for all $w \in C$.

If $z$ were a maximizer with value $r < 1$, the boundary point $(t, t^2)$ with
$t = \min\{1, (1 - r)/2\}$ would lie in $C$ and have the larger value $1 - t^2$. -/
theorem parabolicCap_not_attained :
    ¬ ∃ z ∈ parabolicCap, ∀ w ∈ parabolicCap, parabolicFn w ≤ parabolicFn z := by
  rintro ⟨z, hz, hzmax⟩
  have hfz : parabolicFn z = ((z 0 ^ 2 / z 1 - z 1 : ℝ) : EReal) :=
    parabolicFn_cap (g := fun t : ℝ => t ^ 2) sq_nonneg' sq_eq_zero' hz
  have hr1 : z 0 ^ 2 / z 1 - z 1 < 1 := by
    have hlt := parabolicFn_lt_one_of_mem_parabolicCap hz
    rw [hfz, EReal.coe_lt_coe_iff] at hlt
    exact hlt
  have ht0 : 0 < min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) := lt_min one_pos (by linarith)
  have ht1 : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ≤ 1 := min_le_left _ _
  have ht2 : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ≤ (1 - (z 0 ^ 2 / z 1 - z 1)) / 2 :=
    min_le_right _ _
  have hsq : min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2) ^ 2 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hmem : capPoint 2 (min 1 ((1 - (z 0 ^ 2 / z 1 - z 1)) / 2)) ∈ parabolicCap := by
    rw [parabolicCap_eq]; exact capPoint_mem hsq
  have hle := hzmax _ hmem
  rw [parabolicFn_capPoint (ne_of_gt ht0) hsq, hfz, EReal.coe_le_coe_iff] at hle
  nlinarith

/-! ### The second example: a supremum that is not finite -/

/-- **Section 32** of [rockafellar1970convex], second example: "along the boundary curve
$\xi_1^4 = \xi_2$ of $D$, the value of $f(\xi_1, \xi_2)$ is $\xi_1^{-2} - \xi_2$, and this rises
to $+\infty$ as $(\xi_1, \xi_2)$ moves toward the origin. Thus $f$ is not even bounded above on
$D$." There is no real $r$ with $f(w) \le r$ for all $w \in D = \{\xi_1^4 \le \xi_2 \le 1\}$.

For a candidate bound $r$, the boundary point $(t, t^4)$ with $t = \min\{1, 1/(|r| + 2)\}$ lies
in $D$ and has a value at least $(|r| + 2)^2 - 1 > r$. -/
theorem quarticCap_not_bddAbove :
    ¬ ∃ r : ℝ, ∀ w ∈ quarticCap, parabolicFn w ≤ (r : EReal) := by
  rintro ⟨r, hr⟩
  have hM1 : (1 : ℝ) ≤ |r| + 2 := by cases abs_cases r <;> linarith
  have hM0 : (0 : ℝ) < |r| + 2 := by linarith
  have hrM : r ≤ |r| + 2 - 2 := by cases abs_cases r <;> linarith
  have ht0 : 0 < min 1 (1 / (|r| + 2)) := lt_min one_pos (by positivity)
  have ht1 : min 1 (1 / (|r| + 2)) ≤ 1 := min_le_left _ _
  have htM : min 1 (1 / (|r| + 2)) ≤ 1 / (|r| + 2) := min_le_right _ _
  have hmt : min 1 (1 / (|r| + 2)) * (|r| + 2) ≤ 1 := (le_div_iff₀ hM0).1 htM
  have hq1 : min 1 (1 / (|r| + 2)) ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hmem : capPoint 4 (min 1 (1 / (|r| + 2))) ∈ quarticCap := by
    rw [quarticCap_eq]; exact capPoint_mem hq1
  have hval : parabolicFn (capPoint 4 (min 1 (1 / (|r| + 2))))
      = ((min 1 (1 / (|r| + 2)) ^ 2 / min 1 (1 / (|r| + 2)) ^ 4
          - min 1 (1 / (|r| + 2)) ^ 4 : ℝ) : EReal) := by
    rw [parabolicFn_cap quartic_nonneg quartic_eq_zero (capPoint_mem hq1), capPoint_zero,
      capPoint_one]
  have hsq : min 1 (1 / (|r| + 2)) ^ 2 * (|r| + 2) ^ 2 ≤ 1 := by
    nlinarith [mul_pos ht0 hM0]
  have hbig : (|r| + 2) ^ 2 ≤ min 1 (1 / (|r| + 2)) ^ 2 / min 1 (1 / (|r| + 2)) ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (min 1 (1 / (|r| + 2))), pow_pos ht0 2]
  have hle := hr _ hmem
  rw [hval, EReal.coe_le_coe_iff] at hle
  nlinarith

/-! ### The weakening of Corollary 32.3.2 that the two examples refute -/

/-- **Section 32** of [rockafellar1970convex], first half of the remark that the two examples
illustrate. Corollary 32.3.2 with $C \subseteq \operatorname{ri}(\operatorname{dom} f)$ weakened
to $C \subseteq \operatorname{dom} f$ is false, even for closed proper $f$. It is not true that
for every closed proper convex $g$ on $\mathbb{R}^2$ and every non-empty closed bounded convex
$D \subseteq \operatorname{dom} g$, the function $g$ attains its supremum relative to $D$.

The counterexample is the function `Rockafellar.parabolicFn` on the set
`Rockafellar.parabolicCap`. -/
theorem corollary_32_3_2_not_attained_of_subset_dom :
    ¬ ∀ (g : Rn 2 → EReal) (D : Set (Rn 2)), ConvexFn g → ClosedConvex g → ProperConvex g →
        D.Nonempty → IsClosed D → Bornology.IsBounded D → Convex ℝ D → D ⊆ convexDom g →
        ∃ z ∈ D, ∀ w ∈ D, g w ≤ g z := fun h =>
  parabolicCap_not_attained (h parabolicFn parabolicCap convexFn_parabolicFn
    closedConvex_parabolicFn properConvex_parabolicFn ⟨0, zero_mem_parabolicCap⟩
        isClosed_parabolicCap
    isBounded_parabolicCap convex_parabolicCap parabolicCap_subset_convexDom)

/-- **Section 32** of [rockafellar1970convex], second half of the remark that the two examples
illustrate. It is not true that for every closed proper convex $g$ on $\mathbb{R}^2$ and every
non-empty closed bounded convex $D \subseteq \operatorname{dom} g$, the supremum of $g$ relative
to $D$ is finite: there need not be a real $r$ with $g \le r$ on $D$.

The counterexample is the function `Rockafellar.parabolicFn` on the set
`Rockafellar.quarticCap`, on which it is not bounded above. -/
theorem corollary_32_3_2_not_bddAbove_of_subset_dom :
    ¬ ∀ (g : Rn 2 → EReal) (D : Set (Rn 2)), ConvexFn g → ClosedConvex g → ProperConvex g →
        D.Nonempty → IsClosed D → Bornology.IsBounded D → Convex ℝ D → D ⊆ convexDom g →
        ∃ r : ℝ, ∀ w ∈ D, g w ≤ (r : EReal) := fun h =>
  quarticCap_not_bddAbove (h parabolicFn quarticCap convexFn_parabolicFn
    closedConvex_parabolicFn properConvex_parabolicFn ⟨0, zero_mem_quarticCap⟩ isClosed_quarticCap
    isBounded_quarticCap convex_quarticCap quarticCap_subset_convexDom)

end Rockafellar
