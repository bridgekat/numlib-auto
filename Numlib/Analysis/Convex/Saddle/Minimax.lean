/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Lagrangian
import Numlib.Analysis.Convex.Extremum.Minimum
import Numlib.Analysis.Convex.Extremum.Normal
import Numlib.Analysis.Convex.Saddle.Kernel

/-!
# Minimax problems and conjugate saddle-functions

A function $K \colon U \times X \to [-\infty, +\infty]$ has two iterated extrema,
$\sup_u \inf_x K(u, x)$ and $\inf_x \sup_u K(u, x)$, and the first is never above the second. When
they are equal, their common value is the **saddle-value** of $K$. A **saddle-point** is a point
$(\bar u, \bar x)$ at which $K(\cdot, \bar x)$ attains its maximum and $K(\bar u, \cdot)$ attains
its minimum. This module develops these notions after §36 and §37 of [rockafellar1970convex]: the
saddle-points of the Lagrangian of a convex program, the general Kuhn–Tucker theorem, the
characterization of the Lagrangians of closed convex programs as the upper closed concave-convex
functions, and the lower and upper conjugates of a saddle-function.

The first variable $u$ is the concave variable, which is maximized, and the second variable $x$ is
the convex variable, which is minimized. For a closed proper concave-convex $K$, the extrema over
the whole space equal the extrema over $\operatorname{dom} K = \operatorname{dom}_1 K \times
\operatorname{dom}_2 K$, and they depend only on the equivalence class of $K$. The Lagrangian of the
convex program attached to a convex bifunction $F$ from $U$ to $X$ is $L(v, x) = \inf_u (\langle u,
v \rangle + (Fu)(x))$, and its saddle-points are the pairs (Kuhn–Tucker vector, optimal solution).
The lower and upper conjugates $\underline{K}^*$ and $\overline{K}^*$ of $K$ satisfy
$\inf_x \sup_u K = -\underline{K}^*(0, 0)$ and $\sup_u \inf_x K = -\overline{K}^*(0, 0)$, so the
saddle-value exists if and only if the two conjugates agree at the origin. For every $K$ between the
two brackets of a closed convex bifunction $F$, both conjugates depend only on $F$: the upper one is
the Lagrangian of $F$, and the lower one is the bracket of $F_*^*$.

## Main definitions

* `ConvexAnalysis.IsSaddlePoint`, `ConvexAnalysis.IsSaddlePointOn`: the saddle-point condition, over
  the whole space and relative to a product $C \times D$.
* `ConvexAnalysis.maximin`, `ConvexAnalysis.minimax`, `ConvexAnalysis.HasSaddleValue`: the two
  iterated extrema $\sup_u \inf_x K$ and $\inf_x \sup_u K$, and their equality.
* `ConvexAnalysis.saddleLagrangian`: the Lagrangian $L(v, x) = \inf_u (\langle u, v \rangle +
  (Fu)(x))$, as a function on $V \times X$.
* `ConvexAnalysis.lowerConjSaddle`, `ConvexAnalysis.upperConjSaddle`: the lower conjugate
  $\underline{K}^*$ and the upper conjugate $\overline{K}^*$.
* `ConvexAnalysis.bifunSaddleClass`: the class $\Omega(F)$ of the functions between the two brackets
  of a bifunction $F$.

## Main results

* `ConvexAnalysis.maximin_le_minimax`: $\sup_u \inf_x K \le \inf_x \sup_u K$, with no hypotheses
  (Lemma 36.1).
* `ConvexAnalysis.isSaddlePoint_iff_attained`: a saddle-point is a pair at which both outer extrema
  are attained and the saddle-value exists (Lemma 36.2).
* `ConvexAnalysis.isSaddlePoint_iff_iSup_eq_iInf`: $(\bar u, \bar x)$ is a saddle-point if and only
  if $\sup_u K(u, \bar x) = \inf_x K(\bar u, x)$.
* `ConvexAnalysis.maximin_eq_biSup_biInf`, `ConvexAnalysis.minimax_eq_biInf_biSup`,
  `ConvexAnalysis.isSaddlePoint_iff_isSaddlePointOn_dom`: for a proper concave-convex $K$ with the
  six structural properties of a closed function, the extrema and the saddle-points do not change
  when the whole space is replaced by $\operatorname{dom} K$ (Theorem 36.3).
* `ConvexAnalysis.IsSaddlePoint.mem_domSaddle`: a saddle-point of a proper $K$ lies in
  $\operatorname{dom} K$ (Corollary 36.3.1).
* `ConvexAnalysis.SaddleEquiv.maximin_eq`, `ConvexAnalysis.SaddleEquiv.minimax_eq`: equivalent
  functions have the same iterated extrema (Theorem 36.4).
* `ConvexAnalysis.isSaddlePoint_lagrangian_iff`: $(v, x)$ is a saddle-point of the Lagrangian if and
  only if $v$ is a Kuhn–Tucker vector and $x$ is an optimal solution.
* `ConvexAnalysis.isSaddlePoint_lagrangian_iff_normal_and_optimal`: the same condition in terms of
  normality and the optimality of $x$ and $v$ in the primal and the dual program.
* `ConvexAnalysis.mem_argmin_iff_exists_isSaddlePoint_lagrangian`: the general Kuhn–Tucker theorem
  (Theorem 36.6).
* `ConvexAnalysis.exists_unique_closedConvexBifun_saddleLagrangian_eq`: every upper closed
  concave-convex function is the Lagrangian of exactly one closed convex bifunction (Theorem 36.5).
* `ConvexAnalysis.upperConjSaddle_saddleSwap`, `ConvexAnalysis.lowerConjSaddle_saddleSwap`: the swap
  of the two variables exchanges the two conjugates.
* `ConvexAnalysis.hasSaddleValue_iff_conjSaddle_zero_eq`: the saddle-value exists if and only if
  $\overline{K}^*(0, 0) = \underline{K}^*(0, 0)$.
* `ConvexAnalysis.upperConjSaddle_eq_saddleLagrangian`,
  `ConvexAnalysis.lowerConjSaddle_eq_bracket_lowerAdjointBifun`: the two conjugates of a member of
  $\Omega(F)$, in terms of $F$ alone (Theorem 37.1).
* `ConvexAnalysis.concaveConvexFn_upperConjSaddle`,
  `ConvexAnalysis.concaveConvexFn_lowerConjSaddle`: these conjugates are concave-convex; they are
  also upper closed and lower closed (Corollary 37.1.1).

## Implementation notes

* `ConvexAnalysis.HasSaddleValue K` is the equation $\sup_u \inf_x K = \inf_x \sup_u K$ alone. As in
  the source, the finiteness of the common value is a separate conclusion
  (`ConvexAnalysis.IsSaddlePoint.exists_maximin_eq_coe`).
* The extrema are taken over the whole space. A minimax problem on $C \times D$ becomes a problem on
  the whole product through the extension by $\pm\infty$; `ConvexAnalysis.IsSaddlePointOn` records
  the saddle-points relative to $C \times D$.
* The source writes the Lagrangian as $L(v, x) = \langle v, F_* x \rangle$ and the bifunction of the
  lower conjugate as $F_*^*$, both through the concave inverse $F_*$ of $F$. Here $F_*^*$ is
  `ConvexAnalysis.lowerAdjointBifun Bu Bx F`, defined as the inverse of the adjoint $F^*$. The
  characterization of the Lagrangians goes through `ConvexAnalysis.saddleSwap`, which turns the
  Lagrangian into a bracket of the flipped bifunction `ConvexAnalysis.flipBifun F` for the negated
  pairing, where the theory of convex bifunctions applies without change.
-/

namespace ConvexAnalysis

/-! ### Saddle-points and the two iterated extrema -/

section Basic

variable {U X : Type*} {K : U × X → EReal} {p : U × X}

/-- A point $p = (\bar u, \bar x) \in U \times X$ is a **saddle-point** of
$K \colon U \times X \to [-\infty, +\infty]$ if
$$K(u, \bar x) \le K(\bar u, \bar x) \le K(\bar u, x) \qquad \text{for all } u \in U,\ x \in
  X,$$
that is, $K(\cdot, \bar x)$ attains its maximum and $K(\bar u, \cdot)$ attains its minimum at
$p$.

This is the saddle-point of §36 of [rockafellar1970convex], with the maximization in the first
(concave) variable and the minimization in the second (convex) variable. -/
def IsSaddlePoint (K : U × X → EReal) (p : U × X) : Prop :=
  (∀ u, K (u, p.2) ≤ K p) ∧ ∀ x, K p ≤ K (p.1, x)

/-- A point $p = (\bar u, \bar x)$ is a **saddle-point of $K$ relative to $C \times D$**, for
$C \subseteq U$ and $D \subseteq X$, if $\bar u \in C$, $\bar x \in D$ and
$$K(u, \bar x) \le K(\bar u, \bar x) \le K(\bar u, x) \qquad \text{for all } u \in C,\ x \in
  D.$$

This is the saddle-point with respect to maximizing over $C$ and minimizing over $D$ in §36 of
[rockafellar1970convex]. -/
def IsSaddlePointOn (K : U × X → EReal) (C : Set U) (D : Set X) (p : U × X) : Prop :=
  p.1 ∈ C ∧ p.2 ∈ D ∧ (∀ u ∈ C, K (u, p.2) ≤ K p) ∧ ∀ x ∈ D, K p ≤ K (p.1, x)

/-- The **maximin** of $K \colon U \times X \to [-\infty, +\infty]$ is the iterated extremum
$$\sup_{u \in U} \inf_{x \in X} K(u, x).$$

This is the $\sup \inf$ of §36 of [rockafellar1970convex]. If $U$ is empty, the value is
$-\infty$; if $X$ is empty, every inner infimum is $+\infty$. -/
noncomputable def maximin (K : U × X → EReal) : EReal := ⨆ u, ⨅ x, K (u, x)

/-- The **minimax** of $K \colon U \times X \to [-\infty, +\infty]$ is the iterated extremum
$$\inf_{x \in X} \sup_{u \in U} K(u, x).$$

This is the $\inf \sup$ of §36 of [rockafellar1970convex]. If $X$ is empty, the value is
$+\infty$; if $U$ is empty, every inner supremum is $-\infty$. -/
noncomputable def minimax (K : U × X → EReal) : EReal := ⨅ x, ⨆ u, K (u, x)

/-- The maximin of $K$ is $\sup_u \inf_x K(u, x)$. -/
theorem maximin_apply (K : U × X → EReal) : maximin K = ⨆ u, ⨅ x, K (u, x) := rfl

/-- The minimax of $K$ is $\inf_x \sup_u K(u, x)$. -/
theorem minimax_apply (K : U × X → EReal) : minimax K = ⨅ x, ⨆ u, K (u, x) := rfl

/-- The **saddle-value of $K$ exists** if the two iterated extrema are equal:
$$\sup_{u} \inf_{x} K(u, x) = \inf_{x} \sup_{u} K(u, x).$$
The common value is then the saddle-value.

This is the saddle-value of §36 of [rockafellar1970convex]. As in the source, the common value
can be $\pm\infty$. -/
def HasSaddleValue (K : U × X → EReal) : Prop := maximin K = minimax K

/-- The saddle-value of $K$ exists if and only if $\sup_u \inf_x K(u, x) = \inf_x \sup_u K(u, x)$.
-/
theorem hasSaddleValue_iff : HasSaddleValue K ↔ maximin K = minimax K := Iff.rfl

/-- For every $K \colon U \times X \to [-\infty, +\infty]$,
$$\sup_{u} \inf_{x} K(u, x) \le \inf_{x} \sup_{u} K(u, x).$$

This is Lemma 36.1 of [rockafellar1970convex]. No hypothesis is needed; in particular $U$ and
$X$ can be empty. -/
theorem maximin_le_minimax (K : U × X → EReal) : maximin K ≤ minimax K :=
  iSup_le fun u => le_iInf fun x => (iInf_le (fun x => K (u, x)) x).trans
    (le_iSup (fun u => K (u, x)) u)

/-- For every $u$, $\inf_x K(u, x) \le \sup_{u'} \inf_x K(u', x)$. -/
theorem iInf_slice_le_maximin (K : U × X → EReal) (u : U) : (⨅ x, K (u, x)) ≤ maximin K :=
  le_iSup (fun u => ⨅ x, K (u, x)) u

/-- For every $x$, $\inf_{x'} \sup_u K(u, x') \le \sup_u K(u, x)$. -/
theorem minimax_le_iSup_slice (K : U × X → EReal) (x : X) : minimax K ≤ ⨆ u, K (u, x) :=
  iInf_le (fun x => ⨆ u, K (u, x)) x

/-- For every $p = (\bar u, \bar x)$, $\inf_x K(\bar u, x) \le K(\bar u, \bar x)$. -/
theorem iInf_slice_le_self (K : U × X → EReal) (p : U × X) : (⨅ x, K (p.1, x)) ≤ K p :=
  iInf_le (fun x => K (p.1, x)) p.2

/-- For every $p = (\bar u, \bar x)$, $K(\bar u, \bar x) \le \sup_u K(u, \bar x)$. -/
theorem le_iSup_slice (K : U × X → EReal) (p : U × X) : K p ≤ ⨆ u, K (u, p.2) :=
  le_iSup (fun u => K (u, p.2)) p.1

/-- A point $p = (\bar u, \bar x)$ is a saddle-point of $K$ if and only if
$$\sup_{u} K(u, \bar x) = \inf_{x} K(\bar u, x).$$
Then both sides equal $K(\bar u, \bar x)$.

The results of this module about saddle-points reduce to this equation and to the computation of
$\sup_u K(u, \bar x)$ and $\inf_x K(\bar u, x)$. -/
theorem isSaddlePoint_iff_iSup_eq_iInf :
    IsSaddlePoint K p ↔ (⨆ u, K (u, p.2)) = ⨅ x, K (p.1, x) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm (le_iInf fun x => (iSup_le h1).trans (h2 x))
      ((iInf_slice_le_self K p).trans (le_iSup_slice K p))
  · intro h
    refine ⟨fun u => ?_, fun x => ?_⟩
    · exact ((le_iSup (fun u => K (u, p.2)) u).trans h.le).trans (iInf_slice_le_self K p)
    · exact ((le_iSup_slice K p).trans h.le).trans (iInf_le (fun x => K (p.1, x)) x)

/-- At a saddle-point $(\bar u, \bar x)$, $\sup_u K(u, \bar x) = K(\bar u, \bar x)$. -/
theorem IsSaddlePoint.iSup_eq (h : IsSaddlePoint K p) : (⨆ u, K (u, p.2)) = K p :=
  le_antisymm (iSup_le h.1) (le_iSup_slice K p)

/-- At a saddle-point $(\bar u, \bar x)$, $\inf_x K(\bar u, x) = K(\bar u, \bar x)$. -/
theorem IsSaddlePoint.iInf_eq (h : IsSaddlePoint K p) : (⨅ x, K (p.1, x)) = K p :=
  le_antisymm (iInf_slice_le_self K p) (le_iInf h.2)

/-- A point $p = (\bar u, \bar x)$ is a saddle-point of $K$ if and only if

* the outer supremum of $\sup_u \inf_x K$ is attained at $\bar u$:
  $\inf_x K(\bar u, x) = \sup_u \inf_x K(u, x)$,
* the outer infimum of $\inf_x \sup_u K$ is attained at $\bar x$:
  $\sup_u K(u, \bar x) = \inf_x \sup_u K(u, x)$, and
* the saddle-value of $K$ exists.

This is Lemma 36.2 of [rockafellar1970convex]. -/
theorem isSaddlePoint_iff_attained :
    IsSaddlePoint K p ↔
      (⨅ x, K (p.1, x)) = maximin K ∧ (⨆ u, K (u, p.2)) = minimax K ∧ HasSaddleValue K := by
  constructor
  · intro h
    have h₁ : K p ≤ maximin K := h.iInf_eq ▸ iInf_slice_le_maximin K p.1
    have h₂ : minimax K ≤ K p := h.iSup_eq ▸ minimax_le_iSup_slice K p.2
    have hmm : maximin K = K p := le_antisymm ((maximin_le_minimax K).trans h₂) h₁
    have hMM : minimax K = K p := le_antisymm h₂ (h₁.trans (maximin_le_minimax K))
    exact ⟨by rw [h.iInf_eq, hmm], by rw [h.iSup_eq, hMM], by rw [hasSaddleValue_iff, hmm, hMM]⟩
  · rintro ⟨h1, h2, h3⟩
    exact isSaddlePoint_iff_iSup_eq_iInf.2 (by rw [h1, h2, hasSaddleValue_iff.1 h3])

/-- At a saddle-point $p$ of $K$, $\sup_u \inf_x K(u, x) = K(p)$. -/
theorem IsSaddlePoint.maximin_eq (h : IsSaddlePoint K p) : maximin K = K p :=
  (isSaddlePoint_iff_attained.1 h).1.symm.trans h.iInf_eq

/-- At a saddle-point $p$ of $K$, $\inf_x \sup_u K(u, x) = K(p)$. -/
theorem IsSaddlePoint.minimax_eq (h : IsSaddlePoint K p) : minimax K = K p :=
  (isSaddlePoint_iff_attained.1 h).2.1.symm.trans h.iSup_eq

/-- If $K$ has a saddle-point, then the saddle-value of $K$ exists. -/
theorem IsSaddlePoint.hasSaddleValue (h : IsSaddlePoint K p) : HasSaddleValue K :=
  (isSaddlePoint_iff_attained.1 h).2.2

/-- Let $C \subseteq U$ and $D \subseteq X$, and let $p = (\bar u, \bar x)$ with $\bar u \in C$ and
$\bar x \in D$. Then $p$ is a saddle-point of $K$ relative to $C \times D$ if and only if
$\sup_{u \in C} K(u, \bar x) = \inf_{x \in D} K(\bar u, x)$. -/
theorem isSaddlePointOn_iff_biSup_eq_biInf {C : Set U} {D : Set X} (h₁ : p.1 ∈ C)
    (h₂ : p.2 ∈ D) :
    IsSaddlePointOn K C D p ↔ (⨆ u ∈ C, K (u, p.2)) = ⨅ x ∈ D, K (p.1, x) := by
  have hle : K p ≤ ⨆ u ∈ C, K (u, p.2) := le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, p.2)) p.1 h₁
  have hge : (⨅ x ∈ D, K (p.1, x)) ≤ K p := iInf₂_le (f := fun x (_ : x ∈ D) => K (p.1, x)) p.2 h₂
  constructor
  · rintro ⟨-, -, hu, hx⟩
    exact le_antisymm (le_iInf₂ fun x hx' => (iSup₂_le hu).trans (hx x hx')) (hge.trans hle)
  · intro h
    refine ⟨h₁, h₂, fun u hu => ?_, fun x hx => ?_⟩
    · exact ((le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, p.2)) u hu).trans h.le).trans hge
    · exact (hle.trans h.le).trans (iInf₂_le (f := fun x (_ : x ∈ D) => K (p.1, x)) x hx)

/-- A saddle-point relative to $U \times X$ is a saddle-point. -/
@[simp] theorem isSaddlePointOn_univ_univ :
    IsSaddlePointOn K Set.univ Set.univ p ↔ IsSaddlePoint K p := by
  simp only [IsSaddlePointOn, IsSaddlePoint, Set.mem_univ, true_and, forall_const]

/-! ### Restricting the outer extrema to the effective domains -/

/-- If $u \notin \operatorname{dom}_1 K$, then $\inf_x K(u, x) = -\infty$. -/
theorem iInf_slice_eq_bot_of_notMem_dom₁ {u : U} (hu : u ∉ dom₁ K) : (⨅ x, K (u, x)) = ⊥ := by
  rw [mem_dom₁] at hu
  push Not at hu
  obtain ⟨x, hx⟩ := hu
  exact le_bot_iff.1 ((iInf_le (fun x => K (u, x)) x).trans hx)

/-- If $x \notin \operatorname{dom}_2 K$, then $\sup_u K(u, x) = +\infty$. -/
theorem iSup_slice_eq_top_of_notMem_dom₂ {x : X} (hx : x ∉ dom₂ K) : (⨆ u, K (u, x)) = ⊤ := by
  rw [mem_dom₂] at hx
  push Not at hx
  obtain ⟨u, hu⟩ := hx
  exact top_le_iff.1 (hu.trans (le_iSup (fun u => K (u, x)) u))

/-- For every $K$, $\sup_u \inf_x K(u, x) = \sup_{u \in \operatorname{dom}_1 K} \inf_x K(u, x)$: for
$u \notin \operatorname{dom}_1 K$ the inner infimum is $-\infty$. -/
theorem maximin_eq_biSup_dom₁ (K : U × X → EReal) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ x, K (u, x) := by
  refine le_antisymm (iSup_le fun u => ?_)
    (iSup₂_le fun u _ => le_iSup (fun u => ⨅ x, K (u, x)) u)
  by_cases hu : u ∈ dom₁ K
  · exact le_iSup₂ (f := fun u (_ : u ∈ dom₁ K) => ⨅ x, K (u, x)) u hu
  · rw [iInf_slice_eq_bot_of_notMem_dom₁ hu]
    exact bot_le

/-- For every $K$, $\inf_x \sup_u K(u, x) = \inf_{x \in \operatorname{dom}_2 K} \sup_u K(u, x)$: for
$x \notin \operatorname{dom}_2 K$ the inner supremum is $+\infty$. -/
theorem minimax_eq_biInf_dom₂ (K : U × X → EReal) :
    minimax K = ⨅ x ∈ dom₂ K, ⨆ u, K (u, x) := by
  refine le_antisymm (le_iInf₂ fun x _ => iInf_le (fun x => ⨆ u, K (u, x)) x)
    (le_iInf fun x => ?_)
  by_cases hx : x ∈ dom₂ K
  · exact iInf₂_le (f := fun x (_ : x ∈ dom₂ K) => ⨆ u, K (u, x)) x hx
  · rw [iSup_slice_eq_top_of_notMem_dom₂ hx]
    exact le_top

end Basic

/-! ### The two extrema see only the equivalence class -/

section EquivExtrema

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [TopologicalSpace X]
  [AddCommGroup X] {K L : U × X → EReal} {p : U × X}

omit [TopologicalSpace U] [AddCommGroup U] in
/-- Let $X$ be an additive group with a topology. For every $u$, $\inf_x (\operatorname{cl}_2 K)(u,
x) = \inf_x K(u, x)$. -/
theorem iInf_partialCl₂_slice (K : U × X → EReal) (u : U) :
    (⨅ x, partialCl₂ K (u, x)) = ⨅ x, K (u, x) :=
  iInf_convexCl_eq_iInf fun x => K (u, x)

omit [TopologicalSpace X] [AddCommGroup X] in
/-- Let $U$ be an additive group with a topology. For every $x$, $\sup_u (\operatorname{cl}_1 K)(u,
x) = \sup_u K(u, x)$. -/
theorem iSup_partialCl₁_slice (K : U × X → EReal) (x : X) :
    (⨆ u, partialCl₁ K (u, x)) = ⨆ u, K (u, x) :=
  iSup_concaveCl_eq_iSup fun u => K (u, x)

omit [AddCommGroup U] in
/-- If $K$ and $L$ are equivalent, then $\inf_x K(u, x) = \inf_x L(u, x)$ for every $u$: two convex
functions with the same closure have the same infimum. -/
theorem SaddleEquiv.iInf_slice_eq (h : SaddleEquiv K L) (u : U) :
    (⨅ x, K (u, x)) = ⨅ x, L (u, x) := by
  rw [← iInf_partialCl₂_slice K u, ← iInf_partialCl₂_slice L u, h.2]

omit [AddCommGroup X] in
/-- If $K$ and $L$ are equivalent, then $\sup_u K(u, x) = \sup_u L(u, x)$ for every $x$. -/
theorem SaddleEquiv.iSup_slice_eq (h : SaddleEquiv K L) (x : X) :
    (⨆ u, K (u, x)) = ⨆ u, L (u, x) := by
  rw [← iSup_partialCl₁_slice K x, ← iSup_partialCl₁_slice L x, h.1]

omit [AddCommGroup U] in
/-- Let $U$ be a topological space, let $X$ be an additive group with a topology, and let
$K, L \colon U \times X \to [-\infty, +\infty]$ be equivalent. Then
$$\sup_{u} \inf_{x} K(u, x) = \sup_{u} \inf_{x} L(u, x).$$

This is part of Theorem 36.4 of [rockafellar1970convex]. No convexity is needed: equivalent
functions have the same $\operatorname{cl}_2$, and $\operatorname{cl}_2$ does not change the
inner infima (`ConvexAnalysis.iInf_partialCl₂_slice`). -/
theorem SaddleEquiv.maximin_eq (h : SaddleEquiv K L) : maximin K = maximin L :=
  iSup_congr fun u => h.iInf_slice_eq u

omit [AddCommGroup X] in
/-- Let $U$ be an additive group with a topology, let $X$ be a topological space, and let
$K, L \colon U \times X \to [-\infty, +\infty]$ be equivalent. Then
$$\inf_{x} \sup_{u} K(u, x) = \inf_{x} \sup_{u} L(u, x).$$

This is part of Theorem 36.4 of [rockafellar1970convex]. -/
theorem SaddleEquiv.minimax_eq (h : SaddleEquiv K L) : minimax K = minimax L :=
  iInf_congr fun x => h.iSup_slice_eq x

/-- If $K$ and $L$ are equivalent, then the saddle-value of $K$ exists if and only if the
saddle-value of $L$ exists. -/
theorem SaddleEquiv.hasSaddleValue_iff (h : SaddleEquiv K L) :
    HasSaddleValue K ↔ HasSaddleValue L := by
  change maximin K = minimax K ↔ maximin L = minimax L
  rw [h.maximin_eq, h.minimax_eq]

/-- If $K$ and $L$ are equivalent, then they have the same saddle-points. The saddle-point condition
is an equation between an inner supremum and an inner infimum
(`ConvexAnalysis.isSaddlePoint_iff_iSup_eq_iInf`), and equivalence preserves both. -/
theorem SaddleEquiv.isSaddlePoint_iff (h : SaddleEquiv K L) :
    IsSaddlePoint K p ↔ IsSaddlePoint L p := by
  rw [isSaddlePoint_iff_iSup_eq_iInf, isSaddlePoint_iff_iSup_eq_iInf, h.iSup_slice_eq,
    h.iInf_slice_eq]

end EquivExtrema

/-! ### Saddle-points of a proper saddle-function -/

section ProperSaddlePoints

variable {U X : Type*} {K : U × X → EReal} {p : U × X}

/-- Let $K \colon U \times X \to [-\infty, +\infty]$ be proper, that is, $\operatorname{dom}_1 K$
and $\operatorname{dom}_2 K$ are nonempty. Every saddle-point of $K$ lies in $\operatorname{dom}
K = \operatorname{dom}_1 K \times \operatorname{dom}_2 K$.

This is the first assertion of Corollary 36.3.1 of [rockafellar1970convex]. Only properness is
used. -/
theorem IsSaddlePoint.mem_domSaddle (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    p ∈ domSaddle K := by
  obtain ⟨u₀, hu₀⟩ := hp.dom₁_nonempty
  obtain ⟨x₀, hx₀⟩ := hp.dom₂_nonempty
  have hbot : ⊥ < K p := by
    by_contra hc
    have hKp : K p = ⊥ := le_bot_iff.1 (not_lt.1 hc)
    exact absurd (le_bot_iff.1 (hKp ▸ h.1 u₀)) (ne_of_gt (hu₀ p.2))
  have htop : K p < ⊤ := by
    by_contra hc
    have hKp : K p = ⊤ := top_le_iff.1 (not_lt.1 hc)
    exact absurd (top_le_iff.1 (hKp ▸ h.2 x₀)) (ne_of_lt (hx₀ p.1))
  exact ⟨fun x => lt_of_lt_of_le hbot (h.2 x), fun u => lt_of_le_of_lt (h.1 u) htop⟩

/-- If $K$ is proper and has a saddle-point, then the saddle-value of $K$ is finite:
$\sup_u \inf_x K(u, x)$ is a real number. -/
theorem IsSaddlePoint.exists_maximin_eq_coe (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    ∃ r : ℝ, maximin K = (r : EReal) := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (ne_of_gt (bot_lt_of_mem_domSaddle (h.mem_domSaddle hp)))
    (lt_top_of_mem_domSaddle (h.mem_domSaddle hp))
  exact ⟨r, by rw [h.maximin_eq, hr]⟩

end ProperSaddlePoints

/-! ### Minimising a convex function over a set containing the relative interior -/

section RelintMin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Let $E$ be a finite-dimensional real normed space, let $f \colon E \to [-\infty, +\infty]$ be
convex, and let $S \subseteq E$ contain $\operatorname{ri}(\operatorname{dom} f)$. Then
$\inf_{x \in S} f(x) = \inf_{x \in E} f(x)$. -/
theorem ConvexFn.biInf_eq_iInf_of_relint_convexDom_subset (hf : ConvexFn f) {S : Set E}
    (hS : ri (convexDom f) ⊆ S) : (⨅ x ∈ S, f x) = ⨅ x, f x := by
  refine le_antisymm ?_ (le_iInf₂ fun x _ => iInf_le f x)
  refine EReal.le_of_forall_coe_le fun s hs => ?_
  refine EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_
  replace hq := EReal.coe_lt_coe_iff.1 hq
  have hqc : ((s : ℝ) : EReal) < (q : EReal) := by exact_mod_cast hq
  obtain ⟨x, hx⟩ := iInf_lt_iff.1 (lt_of_le_of_lt hs hqc)
  obtain ⟨z, hz, hzq⟩ := hf.exists_mem_relint_convexDom_lt ⟨x, hx⟩
  exact lt_of_le_of_lt (iInf₂_le (f := fun x (_ : x ∈ S) => f x) z (hS hz)) hzq

end RelintMin

/-!
### The extrema and the saddle-points live on the effective domain

In this section $U$ and $X$ are finite-dimensional real normed spaces, unless a statement says
otherwise. The hypothesis on $K$ is the saddle structure `ConvexAnalysis.SaddleStructure`, which for
a proper concave-convex function is equivalent to closedness
(`ConvexAnalysis.closedSaddleFn_iff_saddleStructure`).
-/

section DomainExtrema

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → EReal}
  {p : U × X}

omit [FiniteDimensional ℝ U] in
/-- Let $X$ be finite-dimensional, and let $K$ be a proper concave-convex function with the saddle
structure. For every $u$, $\inf_{x \in \operatorname{dom}_2 K} K(u, x) = \inf_{x \in X} K(u,
x)$. -/
theorem biInf_dom₂_eq_iInf_slice (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) (u : U) : (⨅ x ∈ dom₂ K, K (u, x)) = ⨅ x, K (u, x) := by
  by_cases hu : u ∈ dom₁ K
  · refine ConvexFn.biInf_eq_iInf_of_relint_convexDom_subset (hK.convex_snd u) ?_
    have hrw : ri (convexDom fun x => K (u, x)) = ri (dom₂ K) :=
      Convex.relint_eq_of_subset_of_subset_closure hK.convex_dom₂ (hK.convex_snd u).convex_convexDom
        (dom₂_subset_convexDom_slice K u) (hs.1.convexDom_slice_subset_closure u hu)
    rw [hrw]
    exact intrinsicInterior_subset
  · obtain ⟨x₀, hx₀⟩ := ProperSaddleFn.relint_dom₂_nonempty hK hp
    have hbot : K (u, x₀) = ⊥ := hs.1.eq_bot_of_notMem_dom₁ u hu x₀ hx₀
    rw [iInf_slice_eq_bot_of_notMem_dom₁ hu]
    exact le_bot_iff.1 ((iInf₂_le (f := fun x (_ : x ∈ dom₂ K) => K (u, x)) x₀
      (intrinsicInterior_subset hx₀)).trans hbot.le)

omit [FiniteDimensional ℝ X] in
/-- Let $U$ be finite-dimensional, and let $K$ be a proper concave-convex function with the saddle
structure. For every $x$, $\sup_{u \in \operatorname{dom}_1 K} K(u, x) = \sup_{u \in U} K(u,
x)$. The proof applies `ConvexAnalysis.biInf_dom₂_eq_iInf_slice` to the swapped function. -/
theorem biSup_dom₁_eq_iSup_slice (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) (x : X) : (⨆ u ∈ dom₁ K, K (u, x)) = ⨆ u, K (u, x) := by
  have h := biInf_dom₂_eq_iInf_slice hK.saddleSwap hs.saddleSwap hp.saddleSwap x
  rw [dom₂_saddleSwap] at h
  have hneg := congrArg (fun z : EReal => -z) h
  simpa only [EReal.neg_iInf, saddleSwap_apply, neg_neg] using hneg

omit [FiniteDimensional ℝ U] in
/-- Let $X$ be a finite-dimensional real normed space, let $U$ be a real normed space, and let
$K \colon U \times X \to [-\infty, +\infty]$ be a proper concave-convex function with the saddle
structure (`ConvexAnalysis.SaddleStructure`). Then, with $C = \operatorname{dom}_1 K$ and
$D = \operatorname{dom}_2 K$,
$$\sup_{u \in U} \inf_{x \in X} K(u, x) = \sup_{u \in C} \inf_{x \in D} K(u, x).$$

This is part of Theorem 36.3 of [rockafellar1970convex], which assumes that $K$ is closed. For a
proper concave-convex function, closedness is equivalent to the saddle structure
(`ConvexAnalysis.closedSaddleFn_iff_saddleStructure`). -/
theorem maximin_eq_biSup_biInf (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) : maximin K = ⨆ u ∈ dom₁ K, ⨅ x ∈ dom₂ K, K (u, x) := by
  rw [maximin_eq_biSup_dom₁]
  exact iSup_congr fun u => iSup_congr fun _ => (biInf_dom₂_eq_iInf_slice hK hs hp u).symm

omit [FiniteDimensional ℝ X] in
/-- Let $U$ be a finite-dimensional real normed space, let $X$ be a real normed space, and let
$K \colon U \times X \to [-\infty, +\infty]$ be a proper concave-convex function with the saddle
structure (`ConvexAnalysis.SaddleStructure`). Then, with $C = \operatorname{dom}_1 K$ and
$D = \operatorname{dom}_2 K$,
$$\inf_{x \in X} \sup_{u \in U} K(u, x) = \inf_{x \in D} \sup_{u \in C} K(u, x).$$

This is part of Theorem 36.3 of [rockafellar1970convex], which assumes that $K$ is closed. -/
theorem minimax_eq_biInf_biSup (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) : minimax K = ⨅ x ∈ dom₂ K, ⨆ u ∈ dom₁ K, K (u, x) := by
  rw [minimax_eq_biInf_dom₂]
  exact iInf_congr fun x => iInf_congr fun _ => (biSup_dom₁_eq_iSup_slice hK hs hp x).symm

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, and let
$K \colon U \times X \to [-\infty, +\infty]$ be a proper concave-convex function with the saddle
structure (`ConvexAnalysis.SaddleStructure`). Then a point is a saddle-point of $K$ if and only
if it is a saddle-point of $K$ relative to $C \times D = \operatorname{dom}_1 K \times
\operatorname{dom}_2 K$.

This is part of Theorem 36.3 of [rockafellar1970convex], which assumes that $K$ is closed. -/
theorem isSaddlePoint_iff_isSaddlePointOn_dom (hK : ConcaveConvexFn K) (hs : SaddleStructure K)
    (hp : ProperSaddleFn K) :
    IsSaddlePoint K p ↔ IsSaddlePointOn K (dom₁ K) (dom₂ K) p := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := h.mem_domSaddle hp
    refine (isSaddlePointOn_iff_biSup_eq_biInf h₁ h₂).2 ?_
    rw [biSup_dom₁_eq_iSup_slice hK hs hp, biInf_dom₂_eq_iInf_slice hK hs hp]
    exact isSaddlePoint_iff_iSup_eq_iInf.1 h
  · intro h
    refine isSaddlePoint_iff_iSup_eq_iInf.2 ?_
    rw [← biSup_dom₁_eq_iSup_slice hK hs hp, ← biInf_dom₂_eq_iInf_slice hK hs hp]
    exact (isSaddlePointOn_iff_biSup_eq_biInf h.1 h.2.1).1 h

end DomainExtrema

/-! ### Slices of a bifunction in its *first* variable -/

section SliceFlip

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- Let $F$ be a convex bifunction from $U$ to $X$. For every $x$, the function $u \mapsto (Fu)(x)$
is convex. This is not a case of `ConvexAnalysis.convexFn_compLin`, because $u \mapsto (u, x)$
is affine, not linear. -/
theorem ConvexBifun.convexFn_flip (hF : ConvexBifun F) (x : X) : ConvexFn fun u => F u x := by
  refine convexFn_of_epi_combo fun u w mu nu hu hw a b ha hb hab => ?_
  have h := hF.epi_combo (x := (u, x)) (y := (w, x)) hu hw ha hb hab
  have hx : a • ((u, x) : U × X) + b • (w, x) = (a • u + b • w, x) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hx] at h

end SliceFlip

section ClosedSliceFlip

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- Let $F$ be a closed convex bifunction from $U$ to $X$, where $U$ and $X$ are topological groups.
For every $x$, the function $u \mapsto (Fu)(x)$ is closed. This is the mirror of
`ConvexAnalysis.ClosedConvexBifun.imageClosedBifun`. -/
theorem ClosedConvexBifun.closedConvex_flip (hF : ClosedConvexBifun F)
    (x : X) : ClosedConvex fun u => F u x := by
  rcases closedConvex_iff.1 (closedConvexBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedConvex_iff.2 (Or.inl (funext fun u => congrFun h (u, x)))
  · exact closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_id.prodMk continuous_const), fun u => hne (u, x)⟩)

end ClosedSliceFlip

/-! ### The Lagrangian as a saddle-function -/

section SaddleLagrangian

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- Let $F$ be a bifunction from $U$ to $X$ and let $\langle \cdot, \cdot \rangle \colon U \times V
\to \mathbb{R}$ be a bilinear pairing. The **Lagrangian** of the convex program attached to $F$,
as a function on $V \times X$, is
$$L(v, x) = \inf_{u \in U} \bigl(\langle u, v \rangle + (Fu)(x)\bigr).$$
The minimax problems for the Lagrangian below are the minimax problems for this function.

This is the Lagrangian of §36 of [rockafellar1970convex], where it is written
$L(v, x) = \langle v, F_* x \rangle$. It is `ConvexAnalysis.lagrangian Bu F` read as a function
of one pair. -/
noncomputable def saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V × X → EReal :=
  fun q => lagrangian Bu F q.1 q.2

/-- The Lagrangian at $(v, x)$ is `ConvexAnalysis.lagrangian Bu F v x`. -/
theorem saddleLagrangian_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (q : V × X) :
    saddleLagrangian Bu F q = lagrangian Bu F q.1 q.2 := rfl

end SaddleLagrangian

/-!
### Saddle-points of the Lagrangian

In this section $U$ is a locally convex real topological vector space with a compatible pairing
$\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$, $X$ is a real vector space that is
a topological group, and $F$ is a bifunction from $U$ to $X$. The program attached to $F$ is (P):
minimize $(F0)(x)$ over $x \in X$.
-/

section LagrangianSaddlePoints

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V} {x : X}

/-- If $F$ is a closed convex bifunction, then $\sup_w L(w, x) = (F0)(x)$ for every $x$: the
supremum of the Lagrangian over the price variable is the objective of (P). -/
theorem iSup_lagrangian_eq (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    (⨆ w, lagrangian Bu F w x) = F 0 x := by
  rw [iSup_lagrangian (hF.convexFn_flip x), congrFun (hcl.closedConvex_flip x) 0]

omit [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [IsCompatiblePairing Bu] [TopologicalSpace X]
  [IsTopologicalAddGroup X] in
/-- Let $U$, $V$ be real vector spaces. If the graph function $(u, x) \mapsto (Fu)(x)$ is proper,
then $\inf_y L(v, y) < +\infty$ for every $v$. -/
theorem iInf_lagrangian_ne_top (hpr : ProperConvex (graphFn F)) :
    (⨅ y, lagrangian Bu F v y) ≠ ⊤ := by
  obtain ⟨q, hq⟩ := hpr.convexDom_nonempty
  refine ne_of_lt (lt_of_le_of_lt (iInf_le (fun y => lagrangian Bu F v y) q.2) ?_)
  refine lt_of_le_of_lt (iInf_le (fun u => ((Bu u v : ℝ) : EReal) + F u q.2) q.1) ?_
  exact EReal.add_lt_top (EReal.coe_ne_top _) (ne_of_lt hq)

/-- Let $U$ be a locally convex real topological vector space with a compatible pairing $\langle
\cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$, let $X$ be a real vector space that is a
topological group, and let $F$ be a closed convex bifunction from $U$ to $X$ whose graph
function $(u, x) \mapsto (Fu)(x)$ is proper. Then $(v, x)$ is a saddle-point of the Lagrangian
$L(v, x) = \inf_u (\langle u, v \rangle + (Fu)(x))$ if and only if

* $v$ is a Kuhn–Tucker vector for (P): $\inf F0$ is finite and $\inf_u \bigl(\langle u, v
  \rangle + \inf Fu\bigr) = \inf F0$, and
* $x$ is an optimal solution of (P): $(F0)(x) \le (F0)(z)$ for every $z$.

Here $\inf Fu = \inf_x (Fu)(x)$, and (P) is the program of minimizing $(F0)(x)$. This is part of
Theorem 36.6 of [rockafellar1970convex]. The proof follows the source: $\inf_y L(v, y) \le \inf
F0 \le (F0)(x) = \sup_w L(w, x)$, where the outer terms are not $+\infty$ and not $-\infty$ by
properness, so the saddle-point condition makes the chain an equality. Kuhn–Tucker vectors are
`ConvexAnalysis.KuhnTucker`, and the optimal solutions are `ConvexAnalysis.argmin (F 0)`. -/
theorem isSaddlePoint_lagrangian_iff (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x)
      ↔ v ∈ KuhnTucker Bu F ∧ x ∈ argmin (F 0) := by
  have hA : (⨅ y, lagrangian Bu F v y) ≤ infBifun F 0 := iInf_lagrangian_le Bu F v
  have hB : infBifun F 0 ≤ F 0 x := iInf_le (fun z => F 0 z) x
  have hsup : (⨆ w, lagrangian Bu F w x) = F 0 x := iSup_lagrangian_eq hF hcl
  have hAtop : (⨅ y, lagrangian Bu F v y) ≠ ⊤ := iInf_lagrangian_ne_top hpr
  have hBbot : F 0 x ≠ ⊥ := hpr.ne_bot (0, x)
  rw [isSaddlePoint_iff_iSup_eq_iInf, mem_kuhnTucker_iff_iInf_lagrangian,
    mem_argmin_iff_le_iInf]
  change (⨆ w, lagrangian Bu F w x) = (⨅ y, lagrangian Bu F v y) ↔ _
  rw [hsup]
  constructor
  · intro h
    have h1 : (⨅ y, lagrangian Bu F v y) = infBifun F 0 :=
      le_antisymm hA (by rw [← h]; exact hB)
    have h2 : F 0 x = infBifun F 0 := by rw [h, h1]
    exact ⟨⟨by rw [← h1]; exact hAtop, by rw [← h2]; exact hBbot, h1⟩, le_of_eq h2⟩
  · rintro ⟨⟨-, -, h1⟩, h2⟩
    rw [h1]
    exact le_antisymm (le_trans h2 (le_of_eq rfl)) hB

end LagrangianSaddlePoints

/-!
### The general Kuhn–Tucker theorem

In this section the spaces and $F$ are as in the previous section, and $\langle \cdot, \cdot \rangle
\colon X \times Y \to \mathbb{R}$ is a bilinear pairing. The dual objective is
$v \mapsto (F^* 0)(v)$, where $F^*$ is the adjoint of $F$.
-/

section KuhnTucker

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V} {x : X}

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [IsCompatiblePairing Bu] [TopologicalSpace X] [IsTopologicalAddGroup X] in
/-- For every $v$, $\inf_y L(v, y) = (F^* 0)(v)$: both sides are $\inf_{u, x} \bigl(\langle u, v
\rangle + (Fu)(x)\bigr)$. So minimizing the Lagrangian in the convex variable evaluates the dual
objective. -/
theorem iInf_lagrangian_eq_convexAdjointBifun_zero (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (⨅ y, lagrangian Bu F v y) = convexAdjointBifun Bu Bx F 0 v := by
  rw [iInf_lagrangian, convexAdjointBifun_zero_apply]

/-- If $F$ is a closed convex bifunction, then $(v, x)$ is a saddle-point of the Lagrangian if and
only if $(F0)(x) \le (F^* 0)(v)$. In that case weak duality gives equality. -/
theorem isSaddlePoint_lagrangian_iff_le_convexAdjointBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ F 0 x ≤ convexAdjointBifun Bu Bx F 0 v := by
  have hge : convexAdjointBifun Bu Bx F 0 v ≤ F 0 x :=
    (convexAdjointBifun_zero_le Bu Bx F v).trans (iInf_le (fun z => F 0 z) x)
  rw [isSaddlePoint_iff_iSup_eq_iInf]
  change (⨆ w, lagrangian Bu F w x) = (⨅ y, lagrangian Bu F v y) ↔ _
  rw [iSup_lagrangian_eq hF hcl, iInf_lagrangian_eq_convexAdjointBifun_zero (Bu := Bu) Bx]
  exact ⟨le_of_eq, fun h => le_antisymm h hge⟩

/-- Let $U$ be a locally convex real topological vector space with a compatible pairing
$U \times V \to \mathbb{R}$, let $X$ be a real vector space that is a topological group, with a
bilinear pairing $X \times Y \to \mathbb{R}$, and let $F$ be a closed convex bifunction from $U$
to $X$ whose graph function is proper. Then $(v, x)$ is a saddle-point of the Lagrangian if and
only if

* $F$ is normal: $(\operatorname{cl} \inf F)(0) = \inf F0$, where $\inf F$ is the function
  $u \mapsto \inf_x (Fu)(x)$;
* $x$ is an optimal solution of the primal program (P): $(F0)(x) \le (F0)(z)$ for every $z$; and
* $v$ is an optimal solution of the dual program (P*): $(F^* 0)(v) = \sup_w (F^* 0)(w)$.

This is the saddle-point form of the optimality conditions of §36 of [rockafellar1970convex].
Normality is `ConvexAnalysis.Normal`, and the adjoint is `ConvexAnalysis.convexAdjointBifun`. -/
theorem isSaddlePoint_lagrangian_iff_normal_and_optimal (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ Normal F ∧ x ∈ argmin (F 0) ∧
      convexAdjointBifun Bu Bx F 0 v = ⨆ w, convexAdjointBifun Bu Bx F 0 w := by
  constructor
  · intro h
    obtain ⟨hv, hx⟩ := (isSaddlePoint_lagrangian_iff hF hcl hpr).1 h
    have hn : Normal F := normal_of_kuhnTucker_nonempty Bx hF ⟨v, hv⟩
    obtain ⟨ht, hb, -⟩ := (mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx := Bx)).1 hv
    exact ⟨hn, hx,
      (mem_kuhnTucker_iff_convexAdjointBifun_zero_eq_iSup (Bu := Bu) Bx hF hn ht hb).1 hv⟩
  · rintro ⟨hn, hx, hv⟩
    refine (isSaddlePoint_lagrangian_iff_le_convexAdjointBifun Bx hF hcl).2 ?_
    rw [hv, (normal_iff_iSup_convexAdjointBifun_eq (Bu := Bu) Bx hF).1 hn]
    exact mem_argmin_iff_le_iInf.1 hx

omit [AddCommGroup Y] [Module ℝ Y] in
/-- Let $U$ be a locally convex real topological vector space with a compatible pairing $\langle
\cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$, let $X$ be a real vector space that is a
topological group, and let $F$ be a closed convex bifunction from $U$ to $X$ whose graph
function is proper. Assume that (P) has at least one Kuhn–Tucker vector. Then $x$ is an optimal
solution of (P) if and only if there is a $v \in V$ such that $(v, x)$ is a saddle-point of the
Lagrangian.

The **general Kuhn–Tucker theorem**, Theorem 36.6 of [rockafellar1970convex], in its
saddle-point form. For an optimal $x$, the $v$ that make $(v, x)$ a saddle-point are exactly the
Kuhn–Tucker vectors (`ConvexAnalysis.isSaddlePoint_lagrangian_iff_mem_kuhnTucker`). -/
theorem mem_argmin_iff_exists_isSaddlePoint_lagrangian (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hkt : (KuhnTucker Bu F).Nonempty) :
    x ∈ argmin (F 0) ↔ ∃ v : V, IsSaddlePoint (saddleLagrangian Bu F) (v, x) := by
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := hkt
    exact ⟨w, (isSaddlePoint_lagrangian_iff hF hcl hpr).2 ⟨hw, hx⟩⟩
  · rintro ⟨w, hw⟩
    exact ((isSaddlePoint_lagrangian_iff hF hcl hpr).1 hw).2

omit [AddCommGroup Y] [Module ℝ Y] in
/-- Let $F$ be a closed convex bifunction whose graph function is proper, and let $x$ be an optimal
solution of (P). Then $(v, x)$ is a saddle-point of the Lagrangian if and only if $v$ is a
Kuhn–Tucker vector for (P). -/
theorem isSaddlePoint_lagrangian_iff_mem_kuhnTucker (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hx : x ∈ argmin (F 0)) :
    IsSaddlePoint (saddleLagrangian Bu F) (v, x) ↔ v ∈ KuhnTucker Bu F :=
  (isSaddlePoint_lagrangian_iff hF hcl hpr).trans ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

end KuhnTucker

section KuhnTuckerSlater

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : Bifun U X}
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {x : X}

/-- Let $U$ be a finite-dimensional real normed space with a compatible pairing
$U \times V \to \mathbb{R}$, where $V$ and $X$ are real normed spaces. Let $F$ be a closed
convex bifunction from $U$ to $X$ whose graph function is proper, assume that the function
$u \mapsto \inf_x (Fu)(x)$ is proper, that $F$ is strongly consistent
($0 \in \operatorname{ri}(\operatorname{dom} F)$), and that $\inf F0 < +\infty$. Then $x$ is an
optimal solution of (P) if and only if there is a $v$ such that $(v, x)$ is a saddle-point of
the Lagrangian.

This is the Kuhn–Tucker theorem under the constraint qualification of strong consistency. -/
theorem mem_argmin_iff_exists_isSaddlePoint_lagrangian_of_stronglyConsistent
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hpr : ProperConvex (graphFn F))
    (hip : ProperConvex (infBifun F)) (hs : StronglyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    x ∈ argmin (F 0) ↔ ∃ v : V, IsSaddlePoint (saddleLagrangian Bu F) (v, x) :=
  mem_argmin_iff_exists_isSaddlePoint_lagrangian hF hcl hpr
    (kuhnTucker_nonempty_of_stronglyConsistent hF hip hs ht)

end KuhnTuckerSlater

/-!
### Lagrangians are exactly the upper closed concave-convex functions

In this section $U$, $V$, $X$ and $Y$ are locally convex real topological vector spaces, unless a
statement says otherwise.
-/

section LagrangianUpperClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {L : V × X → EReal}

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- Let $\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$ be a bilinear pairing and
$F$ a bifunction from $U$ to $X$. The swapped Lagrangian $(x, v) \mapsto -L(v, x)$ is the
bracket of the flipped bifunction $x \mapsto F(\cdot)(x)$ for the negated pairing
$-\langle \cdot, \cdot \rangle$:
$$-L(v, x) = \sup_u \bigl(-\langle u, v \rangle - (Fu)(x)\bigr).$$

The source writes the Lagrangian as $\langle v, F_* x \rangle$, through the inverse bifunction.
In the form above the theory of convex bifunctions applies without change. -/
theorem saddleSwap_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) :
    saddleSwap (saddleLagrangian Bu F)
      = fun q : X × V => bracket (-Bu) (flipBifun F) q.1 q.2 := by
  funext q
  rw [saddleSwap_apply, saddleLagrangian_apply, lagrangian_apply, bracket_apply,
    EReal.neg_iInf]
  refine iSup_congr fun u => ?_
  have hb : (((-Bu) u q.2 : ℝ) : EReal) = ((-(Bu u q.2) : ℝ) : EReal) := rfl
  rw [hb, EReal.coe_neg,
    EReal.neg_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
  rfl

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] in
/-- Let $U$ and $X$ be real vector spaces. If $F$ is a convex bifunction, then its Lagrangian is
concave-convex: the brackets of a convex bifunction are concave-convex, and the swapped
Lagrangian is one of them. -/
theorem concaveConvexFn_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    ConcaveConvexFn (saddleLagrangian Bu F) := by
  have h : ConcaveConvexFn (saddleSwap (saddleLagrangian Bu F)) := by
    rw [saddleSwap_saddleLagrangian]
    exact concaveConvexFn_bracket (convexBifun_flipBifun hF) (-Bu)
  have h2 := h.saddleSwap
  rwa [saddleSwap_saddleSwap] at h2

omit [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- Let $\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$ be a pairing that is
compatible for both $U$ and $V$, and let $X$ have a compatible pairing with a real vector space
$Y$. If $F$ is a closed convex bifunction from $U$ to $X$, then its Lagrangian is upper closed:
$\operatorname{cl}_1 \operatorname{cl}_2 L = L$.

This is part of Theorem 36.5 of [rockafellar1970convex]. -/
theorem upperClosedFn_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) : UpperClosedFn (saddleLagrangian Bu F) := by
  have h : LowerClosedFn (saddleSwap (saddleLagrangian Bu F)) := by
    rw [saddleSwap_saddleLagrangian]
    exact lowerClosedFn_bracket
        Bx (-Bu) (convexBifun_flipBifun hF) (closedConvexBifun_flipBifun hcl)
  have h3 := lowerClosedFn_iff_upperClosedFn_saddleSwap.1 h
  rwa [saddleSwap_saddleSwap] at h3

omit [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- Let $U$, $V$ and $X$ be locally convex real topological vector spaces, let $Y$ be a real vector
space, let $\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$ be a pairing that is
compatible for both $U$ and $V$, and let $\langle \cdot, \cdot \rangle \colon X \times Y \to
\mathbb{R}$ be a compatible pairing. Let $L \colon V \times X \to [-\infty, +\infty]$ be an
upper closed concave-convex function. Then there is exactly one closed convex bifunction $G$
from $U$ to $X$ whose Lagrangian is $L$:
$$L(v, x) = \inf_u \bigl(\langle u, v \rangle + (Gu)(x)\bigr) \qquad \text{for all } v, x.$$

This is Theorem 36.5 of [rockafellar1970convex], the half that says every upper closed
concave-convex function is a Lagrangian, together with uniqueness. The converse half is
`ConvexAnalysis.upperClosedFn_saddleLagrangian` and
`ConvexAnalysis.concaveConvexFn_saddleLagrangian`. The pairing of $X$ with $Y$ appears only in
the proof. -/
theorem exists_unique_closedConvexBifun_saddleLagrangian_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] (hL : ConcaveConvexFn L) (huc : UpperClosedFn L) :
    ∃! G : Bifun U X, ConvexBifun G ∧ ClosedConvexBifun G ∧ saddleLagrangian Bu G = L := by
  have hsw : ConcaveConvexFn (saddleSwap L) := hL.saddleSwap
  have hlc : LowerClosedFn (saddleSwap L) := by
    refine lowerClosedFn_iff_upperClosedFn_saddleSwap.2 ?_
    rwa [saddleSwap_saddleSwap]
  obtain ⟨H, ⟨hHconv, hHcl, hHbr⟩, huniq⟩ :=
    exists_unique_convexBifun_bracket_eq Bx (-Bu) hsw hlc
  refine ⟨flipBifun H, ⟨convexBifun_flipBifun hHconv, closedConvexBifun_flipBifun hHcl, ?_⟩, ?_⟩
  · refine saddleSwap_injective ?_
    rw [saddleSwap_saddleLagrangian, flipBifun_flipBifun]
    exact hHbr
  · rintro G ⟨hGconv, hGcl, hGL⟩
    have hbr : (fun q : X × V => bracket (-Bu) (flipBifun G) q.1 q.2) = saddleSwap L := by
      rw [← saddleSwap_saddleLagrangian, hGL]
    have hHG := huniq (flipBifun G)
      ⟨convexBifun_flipBifun hGconv, closedConvexBifun_flipBifun hGcl, hbr⟩
    rw [← hHG, flipBifun_flipBifun]

end LagrangianUpperClosed

/-!
### Conjugate saddle-functions: the lower and upper conjugates

In this section $\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$ and $\langle \cdot,
\cdot \rangle \colon X \times Y \to \mathbb{R}$ are bilinear pairings, and
$K \colon U \times Y \to [-\infty, +\infty]$. The conjugates of $K$ are functions on $V \times X$.
-/

section ConjugateSaddle

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **lower conjugate** of $K \colon U \times Y \to [-\infty, +\infty]$ is the function on
$V \times X$
$$\underline{K}^*(u^*, x) = \sup_{y \in Y} \inf_{u \in U} \bigl(\langle u, u^* \rangle + \langle
  x, y \rangle - K(u, y)\bigr).$$

This is the lower conjugate of §37 of [rockafellar1970convex]. The supremum over the convex
variable $y$ is the outer extremum. -/
noncomputable def lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) : V × X → EReal :=
  fun q => ⨆ y, ⨅ u, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y))

/-- The **upper conjugate** of $K \colon U \times Y \to [-\infty, +\infty]$ is the function on
$V \times X$
$$\overline{K}^*(u^*, x) = \inf_{u \in U} \sup_{y \in Y} \bigl(\langle u, u^* \rangle + \langle
  x, y \rangle - K(u, y)\bigr).$$

This is the upper conjugate of §37 of [rockafellar1970convex]. The infimum over the concave
variable $u$ is the outer extremum. -/
noncomputable def upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) : V × X → EReal :=
  fun q => ⨅ u, ⨆ y, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y))

/-- The lower conjugate at $(u^*, x)$ is $\sup_y \inf_u \bigl(\langle u, u^* \rangle + \langle x, y
\rangle - K(u, y)\bigr)$. -/
theorem lowerConjSaddle_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) (q : V × X) :
    lowerConjSaddle Bu Bx K q = ⨆ y, ⨅ u, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y)) := rfl

/-- The upper conjugate at $(u^*, x)$ is $\inf_u \sup_y \bigl(\langle u, u^* \rangle + \langle x, y
\rangle - K(u, y)\bigr)$. -/
theorem upperConjSaddle_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) (q : V × X) :
    upperConjSaddle Bu Bx K q = ⨅ u, ⨆ y, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y)) := rfl

/-- The lower conjugate is at most the upper one, $\underline{K}^* \le \overline{K}^*$, by
$\sup \inf \le \inf \sup$. -/
theorem lowerConjSaddle_le_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    lowerConjSaddle Bu Bx K ≤ upperConjSaddle Bu Bx K := fun q =>
  maximin_le_minimax fun p : Y × U => (((Bu p.2 q.1 + Bx q.2 p.1 : ℝ) : EReal) - K (p.2, p.1))

/-- For $r \in \mathbb{R}$ and $z \in [-\infty, +\infty]$, $(-r) - (-z) = z - r$. This sign rule is
used for the swap of the two conjugates. -/
theorem coe_neg_sub_neg (r : ℝ) (z : EReal) :
    ((-r : ℝ) : EReal) - -z = z - ((r : ℝ) : EReal) := by
  induction z using EReal.rec with
  | bot => simp
  | coe s => norm_cast; ring
  | top => simp

/-- Let $\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$ and $\langle \cdot, \cdot
\rangle \colon X \times Y \to \mathbb{R}$ be bilinear pairings, and let
$K \colon U \times Y \to [-\infty, +\infty]$. Let $\tilde K(y, u) = -K(u, y)$ be the swapped
function, and take the conjugates of $\tilde K$ with respect to the negated flipped pairings
$(y, x) \mapsto -\langle x, y \rangle$ and $(v, u) \mapsto -\langle u, v \rangle$. Then for all
$x$ and $u^*$,
$$\overline{\tilde K}^*(x, u^*) = -\underline{K}^*(u^*, x).$$
So the upper conjugate of the swapped function is the swapped lower conjugate.

Negating both pairings turns a supremum of infima into an infimum of suprema. -/
theorem upperConjSaddle_saddleSwap (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) :
    upperConjSaddle (-Bx.flip) (-Bu.flip) (saddleSwap K)
      = saddleSwap (lowerConjSaddle Bu Bx K) := by
  funext q
  rw [upperConjSaddle_apply, saddleSwap_apply, lowerConjSaddle_apply, EReal.neg_iSup]
  refine iInf_congr fun y => ?_
  rw [EReal.neg_iInf]
  refine iSup_congr fun u => ?_
  have hr : ((-Bx.flip) y q.1 + (-Bu.flip) q.2 u : ℝ) = -(Bu u q.2 + Bx q.1 y) := by
    simp only [LinearMap.neg_apply, LinearMap.flip_apply]
    ring
  rw [hr, saddleSwap_apply, coe_neg_sub_neg, EReal.neg_coe_sub]

/-- With the notation of `ConvexAnalysis.upperConjSaddle_saddleSwap`, the lower conjugate of the
swapped function $\tilde K(y, u) = -K(u, y)$, taken with respect to the negated flipped
pairings, is the swapped upper conjugate of $K$: for all $x$ and $u^*$,
$$\underline{\tilde K}^*(x, u^*) = -\overline{K}^*(u^*, x).$$

The proof applies `ConvexAnalysis.upperConjSaddle_saddleSwap` to $\tilde K$: negating and
flipping a pairing twice gives the pairing back. -/
theorem lowerConjSaddle_saddleSwap (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (K : U × Y → EReal) :
    lowerConjSaddle (-Bx.flip) (-Bu.flip) (saddleSwap K)
      = saddleSwap (upperConjSaddle Bu Bx K) := by
  have h := upperConjSaddle_saddleSwap (-Bx.flip) (-Bu.flip) (saddleSwap K)
  have e₁ : -(-Bu.flip).flip = Bu := by ext; simp
  have e₂ : -(-Bx.flip).flip = Bx := by ext; simp
  rw [e₁, e₂, saddleSwap_saddleSwap] at h
  rw [h, saddleSwap_saddleSwap]

/-- Let $F$ be a bifunction from $U$ to $X$. The class $\Omega(F)$ is the set of all
$K \colon U \times Y \to [-\infty, +\infty]$ that lie between the two brackets of $F$:
$$\langle Fu, y \rangle \le K(u, y) \le \langle u, F^* y \rangle \qquad \text{for all } u, y.$$

This is the class $\Omega(F)$ of §34 of [rockafellar1970convex], without the condition that $K$
be concave-convex, which the source also imposes. For a closed convex bifunction $F$, the
concave-convex members of $\Omega(F)$ form one equivalence class of closed functions (Theorem
34.2 of [rockafellar1970convex]). The two brackets are `ConvexAnalysis.bracket` and
`ConvexAnalysis.concaveBracket` of the adjoint `ConvexAnalysis.convexAdjointBifun`. -/
noncomputable def bifunSaddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Set (U × Y → EReal) :=
  saddleClass (fun p : U × Y => bracket Bx F p.1 p.2)
    (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2)

/-- $K \in \Omega(F)$ if and only if $\langle Fu, y \rangle \le K(u, y) \le \langle u, F^* y
\rangle$ for all $u$ and $y$. -/
theorem mem_bifunSaddleClass {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}
    {K : U × Y → EReal} : K ∈ bifunSaddleClass Bu Bx F ↔
      ((fun p : U × Y => bracket Bx F p.1 p.2) ≤ K ∧
        K ≤ fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2) := Iff.rfl

end ConjugateSaddle

/-! ### The saddle-value is a value of the conjugate at the origin -/

section ConjugateSaddleZero

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- For every $K$, $\inf_y \sup_u K(u, y) = -\underline{K}^*(0, 0)$. -/
theorem minimax_eq_neg_lowerConjSaddle_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    minimax K = -(lowerConjSaddle Bu Bx K 0) := by
  have h : lowerConjSaddle Bu Bx K 0 = -(minimax K) := by
    rw [lowerConjSaddle_apply, minimax_apply, EReal.neg_iInf]
    refine iSup_congr fun y => ?_
    rw [EReal.neg_iSup]
    refine iInf_congr fun u => ?_
    have h0 : (Bu u (0 : V × X).1 + Bx (0 : V × X).2 y : ℝ) = 0 := by simp
    rw [h0, EReal.coe_zero]
    change (0 : EReal) + -(K (u, y)) = -(K (u, y))
    rw [zero_add]
  rw [h, neg_neg]

/-- For every $K$, $\sup_u \inf_y K(u, y) = -\overline{K}^*(0, 0)$. -/
theorem maximin_eq_neg_upperConjSaddle_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    maximin K = -(upperConjSaddle Bu Bx K 0) := by
  have h : upperConjSaddle Bu Bx K 0 = -(maximin K) := by
    rw [upperConjSaddle_apply, maximin_apply, EReal.neg_iSup]
    refine iInf_congr fun u => ?_
    rw [EReal.neg_iInf]
    refine iSup_congr fun y => ?_
    have h0 : (Bu u (0 : V × X).1 + Bx (0 : V × X).2 y : ℝ) = 0 := by simp
    rw [h0, EReal.coe_zero]
    change (0 : EReal) + -(K (u, y)) = -(K (u, y))
    rw [zero_add]
  rw [h, neg_neg]

/-- Let $\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$ and $\langle \cdot, \cdot
\rangle \colon X \times Y \to \mathbb{R}$ be bilinear pairings, and let
$K \colon U \times Y \to [-\infty, +\infty]$. The saddle-value of $K$ exists if and only if the
two conjugates agree at the origin:
$$\overline{K}^*(0, 0) = \underline{K}^*(0, 0).$$

So the existence of a saddle-value depends on the position of the origin relative to the
effective domain of the conjugate class. The proof uses
`ConvexAnalysis.minimax_eq_neg_lowerConjSaddle_zero` and
`ConvexAnalysis.maximin_eq_neg_upperConjSaddle_zero`. -/
theorem hasSaddleValue_iff_conjSaddle_zero_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    HasSaddleValue K ↔ upperConjSaddle Bu Bx K 0 = lowerConjSaddle Bu Bx K 0 := by
  rw [hasSaddleValue_iff, maximin_eq_neg_upperConjSaddle_zero Bu Bx K,
    minimax_eq_neg_lowerConjSaddle_zero Bu Bx K, _root_.neg_inj]

end ConjugateSaddleZero

/-!
### The two conjugates of a member of $\Omega(F)$

In this section $U$, $V$, $X$ and $Y$ are locally convex real topological vector spaces, unless a
statement says otherwise.
-/

section ClassConjugates

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

omit [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- The bifunction attached to a function on $U \times Y$, $(Fu)(x) = \sup_y (\langle x, y \rangle -
K(u, y))$ (`ConvexAnalysis.bifunOfSaddle`), is antitone in $K$: if $K \le L$, then the
bifunction of $L$ is at most the bifunction of $K$. -/
theorem bifunOfSaddle_antitone (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {K L : U × Y → EReal} (h : K ≤ L) :
    bifunOfSaddle Bx L ≤ bifunOfSaddle Bx K :=
  fun u x => convexConj_antitone Bx.flip (fun y => h (u, y)) x

omit [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- Let the flipped pairing $Y \times X \to \mathbb{R}$ be compatible for $Y$. The bifunction
attached to $K$ (`ConvexAnalysis.bifunOfSaddle`) is the same for $K$ and for
$\operatorname{cl}_2 K$, because the conjugate of a function equals the conjugate of its convex
closure (`ConvexAnalysis.convexConj_convexCl`), slice by slice. -/
theorem bifunOfSaddle_partialCl₂ (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (K : U × Y → EReal) : bifunOfSaddle Bx (partialCl₂ K) = bifunOfSaddle Bx K :=
  funext fun u => convexConj_convexCl (B := Bx.flip) fun y => K (u, y)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] in
/-- Let $F$ be a closed convex bifunction from $U$ to $X$, let the pairing
$U \times V \to \mathbb{R}$ be compatible, and let the pairing $X \times Y \to \mathbb{R}$ be
compatible for both $X$ and $Y$. For every $K \in \Omega(F)$, the bifunction attached to $K$,
$(u, x) \mapsto \sup_y (\langle x, y \rangle - K(u, y))$, is $F$.

The two brackets of $F$ have the same attached bifunction, because one is $\operatorname{cl}_2$
of the other and the attached bifunction depends only on $\operatorname{cl}_2$. Antitonicity
then gives the same bifunction for every $K$ between them. This is the step that gives the upper
conjugate. -/
theorem bifunOfSaddle_eq_of_mem_bifunSaddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) : bifunOfSaddle Bx K = F := by
  obtain ⟨hlow, hup⟩ := hK
  have hbase : bifunOfSaddle Bx (fun p : U × Y => bracket Bx F p.1 p.2) = F := by
    funext u
    have h : bifunOfSaddle Bx (fun p : U × Y => bracket Bx F p.1 p.2) u
        = convexConj Bx.flip (bracket Bx F u) := rfl
    rw [h, ← convexCl_eq_convexConj_bracket hF u]
    exact hcl.imageClosedBifun u
  have h2 : partialCl₂ (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2)
      = fun p : U × Y => bracket Bx F p.1 p.2 :=
    partialCl₂_concaveBracket_adjoint Bu Bx hF hcl
  have hupper : bifunOfSaddle Bx
      (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2) = F :=
    calc bifunOfSaddle Bx (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2)
        = bifunOfSaddle Bx
            (partialCl₂ fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2) :=
          (bifunOfSaddle_partialCl₂ Bx _).symm
      _ = bifunOfSaddle Bx (fun p : U × Y => bracket Bx F p.1 p.2) := by rw [h2]
      _ = F := hbase
  refine le_antisymm ?_ ?_
  · rw [← hbase]
    exact bifunOfSaddle_antitone Bx hlow
  · rw [← hupper]
    exact bifunOfSaddle_antitone Bx hup

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- Let $F$ be a convex bifunction from $U$ to $X$, let the pairing $U \times V \to \mathbb{R}$ be
compatible for both $U$ and $V$, and let the flipped pairing $Y \times X \to \mathbb{R}$ be
compatible for $Y$. For every $K \in \Omega(F)$ and every $y$, the concave conjugate of the
slice $K(\cdot, y)$ is $F^* y$:
$$\inf_u \bigl(\langle u, v \rangle - K(u, y)\bigr) = (F^* y)(v) \qquad \text{for all } v.$$

The concave conjugate depends only on $\operatorname{cl}_1$, and $\operatorname{cl}_1$ of the
lower bracket is the upper bracket. This is the step that gives the lower conjugate. -/
theorem concaveConj_slice_eq_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) (y : Y) :
    concaveConj Bu (fun u => K (u, y)) = convexAdjointBifun Bu Bx F y := by
  obtain ⟨hlow, hup⟩ := hK
  have hcl1 : (fun u => concaveBracket Bu (convexAdjointBifun Bu Bx F) u y)
      = concaveCl fun u => bracket Bx F u y := by
    funext u
    have h1 : partialCl₁ (fun p : U × Y => bracket Bx F p.1 p.2) (u, y)
        = concaveBracket Bu (convexAdjointBifun Bu Bx F) u y :=
      congrFun (partialCl₁_bracket Bu Bx hF) (u, y)
    rw [← h1]
    exact congrFun (partialCl₁_slice (fun p : U × Y => bracket Bx F p.1 p.2) y) u
  have hends : concaveConj Bu (fun u => concaveBracket Bu (convexAdjointBifun Bu Bx F) u y)
      = concaveConj Bu fun u => bracket Bx F u y := by
    rw [hcl1, concaveConj_concaveCl]
  have hA : concaveConj Bu (fun u => concaveBracket Bu (convexAdjointBifun Bu Bx F) u y)
      ≤ concaveConj Bu fun u => K (u, y) :=
    concaveConj_antitone Bu fun u => hup (u, y)
  have hB : concaveConj Bu (fun u => K (u, y))
      ≤ concaveConj Bu fun u => bracket Bx F u y :=
    concaveConj_antitone Bu fun u => hlow (u, y)
  have hKeq : concaveConj Bu (fun u => K (u, y))
      = concaveConj Bu fun u => concaveBracket Bu (convexAdjointBifun Bu Bx F) u y :=
    le_antisymm (by rw [hends]; exact hB) hA
  rw [hKeq, concaveBracket_eq_concaveConj Bu (convexAdjointBifun Bu Bx F) y]
  exact concaveBiconj_eq_self (B := Bu.flip) (concaveFn_convexAdjointBifun_apply Bu Bx F y)
    (closedConcave_iff_closedConvex_neg.2 (closedConvex_neg_convexAdjointBifun_apply Bu Bx F y))

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] in
/-- Let $U$, $X$ and $Y$ be locally convex real topological vector spaces, let $\langle \cdot, \cdot
\rangle \colon U \times V \to \mathbb{R}$ be a compatible pairing, and let $\langle \cdot, \cdot
\rangle \colon X \times Y \to \mathbb{R}$ be a pairing that is compatible for both $X$ and $Y$.
Let $F$ be a closed convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$. Then the upper
conjugate of $K$ is the Lagrangian of $F$:
$$\overline{K}^*(u^*, x) = \inf_u \bigl(\langle u, u^* \rangle + (Fu)(x)\bigr) \qquad \text{for
  all } u^*, x.$$
In particular $\overline{K}^*$ does not depend on the choice of $K$ in $\Omega(F)$.

This is the first equation of Theorem 37.1 of [rockafellar1970convex], where the right side is
written $\langle u^*, F_* x \rangle$. -/
theorem upperConjSaddle_eq_saddleLagrangian (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    upperConjSaddle Bu Bx K = saddleLagrangian Bu F := by
  have hB := bifunOfSaddle_eq_of_mem_bifunSaddleClass Bu Bx hF hcl hK
  funext q
  rw [upperConjSaddle_apply, saddleLagrangian_apply, lagrangian_apply]
  refine iInf_congr fun u => ?_
  have h1 : ∀ y, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y))
      = (((Bx q.2 y : ℝ) : EReal) - K (u, y)) + ((Bu u q.1 : ℝ) : EReal) := by
    intro y
    rw [EReal.coe_add]
    simp only [sub_eq_add_neg]
    rw [add_assoc, add_comm]
  simp only [h1]
  rw [← EReal.iSup_add_coe]
  have h2 : (⨆ y, (((Bx q.2 y : ℝ) : EReal) - K (u, y))) = F u q.2 := by
    rw [← congrFun (congrFun hB u) q.2, bifunOfSaddle_apply]
  rw [h2, add_comm]

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- Let $U$ and $V$ be locally convex real topological vector spaces, let $Y$ be a real vector space
that is a topological group, let $\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$
be a pairing that is compatible for both $U$ and $V$, and let $\langle \cdot, \cdot \rangle
\colon X \times Y \to \mathbb{R}$ be a pairing whose flip is compatible for $Y$. Let $F$ be a
convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$. Then the lower conjugate of $K$ is
the bracket of $F_*^*$:
$$\underline{K}^*(u^*, x) = \langle F_*^* u^*, x \rangle = \sup_y \bigl(\langle x, y \rangle -
  (F_*^* u^*)(y)\bigr), \qquad (F_*^* u^*)(y) = -(F^* y)(u^*).$$
So $\underline{K}^*$ also depends only on $F$.

This is the second equation of Theorem 37.1 of [rockafellar1970convex]. Here $F$ need not be
closed. The bifunction $F_*^*$ from $V$ to $Y$ is `ConvexAnalysis.lowerAdjointBifun Bu Bx F`,
and the bracket is `ConvexAnalysis.bracket` for the flipped pairing $Y \times X \to \mathbb{R}$. -/
theorem lowerConjSaddle_eq_bracket_lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    lowerConjSaddle Bu Bx K
      = fun q : V × X => bracket Bx.flip (lowerAdjointBifun Bu Bx F) q.1 q.2 := by
  funext q
  rw [lowerConjSaddle_apply, bracket_apply]
  refine iSup_congr fun y => ?_
  have h1 : ∀ u, (((Bu u q.1 + Bx q.2 y : ℝ) : EReal) - K (u, y))
      = (((Bu u q.1 : ℝ) : EReal) - K (u, y)) + ((Bx q.2 y : ℝ) : EReal) := by
    intro u
    rw [EReal.coe_add]
    simp only [sub_eq_add_neg]
    rw [add_right_comm]
  simp only [h1]
  rw [← EReal.iInf_add_coe]
  have h2 : (⨅ u, (((Bu u q.1 : ℝ) : EReal) - K (u, y))) = convexAdjointBifun Bu Bx F y q.1 :=
    congrFun (concaveConj_slice_eq_convexAdjointBifun Bu Bx hF hK y) q.1
  rw [h2]
  have h3 : ((Bx.flip y q.2 : ℝ) : EReal) - lowerAdjointBifun Bu Bx F q.1 y
      = ((Bx q.2 y : ℝ) : EReal) + convexAdjointBifun Bu Bx F y q.1 := by
    rw [lowerAdjointBifun_apply]
    simp only [sub_eq_add_neg, neg_neg]
    rfl
  rw [h3, add_comm]

/-! ### The conjugates are again concave-convex, and closed -/

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] in
/-- Let $U$, $X$ and $Y$ be locally convex real topological vector spaces, let $\langle \cdot, \cdot
\rangle \colon U \times V \to \mathbb{R}$ be a compatible pairing, and let $\langle \cdot, \cdot
\rangle \colon X \times Y \to \mathbb{R}$ be a pairing that is compatible for both $X$ and $Y$.
Let $F$ be a closed convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$. Then the upper
conjugate $\overline{K}^*$ is concave-convex.

This is part of Corollary 37.1.1 of [rockafellar1970convex]. The upper conjugate is the
Lagrangian of $F$ (`ConvexAnalysis.upperConjSaddle_eq_saddleLagrangian`). -/
theorem concaveConvexFn_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    ConcaveConvexFn (upperConjSaddle Bu Bx K) := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK]
  exact concaveConvexFn_saddleLagrangian Bu hF

/-- Let the pairing $U \times V \to \mathbb{R}$ be compatible for both $U$ and $V$, and let the
pairing $X \times Y \to \mathbb{R}$ be compatible for both $X$ and $Y$. If $F$ is a closed
convex bifunction and $K \in \Omega(F)$, then the upper conjugate $\overline{K}^*$ is upper
closed: it is a Lagrangian, and Lagrangians of closed convex bifunctions are upper closed. -/
theorem upperClosedFn_upperConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) : UpperClosedFn (upperConjSaddle Bu Bx K) := by
  rw [upperConjSaddle_eq_saddleLagrangian Bu Bx hF hcl hK]
  exact upperClosedFn_saddleLagrangian Bu Bx hF hcl

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] in
/-- Let $U$ and $V$ be locally convex real topological vector spaces, let $Y$ be a real vector space
that is a topological group, let $\langle \cdot, \cdot \rangle \colon U \times V \to \mathbb{R}$
be a pairing that is compatible for both $U$ and $V$, and let $\langle \cdot, \cdot \rangle
\colon X \times Y \to \mathbb{R}$ be a pairing whose flip is compatible for $Y$. Let $F$ be a
convex bifunction from $U$ to $X$, and let $K \in \Omega(F)$. Then the lower conjugate
$\underline{K}^*$ is concave-convex.

This is part of Corollary 37.1.1 of [rockafellar1970convex]. The lower conjugate is the bracket
of $F_*^*$ (`ConvexAnalysis.lowerConjSaddle_eq_bracket_lowerAdjointBifun`). -/
theorem concaveConvexFn_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip]
    (hF : ConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    ConcaveConvexFn (lowerConjSaddle Bu Bx K) := by
  rw [lowerConjSaddle_eq_bracket_lowerAdjointBifun Bu Bx hF hK]
  exact concaveConvexFn_bracket (convexBifun_lowerAdjointBifun Bu Bx F) Bx.flip

/-- Let the pairing $U \times V \to \mathbb{R}$ be compatible for both $U$ and $V$, and let the
pairing $X \times Y \to \mathbb{R}$ be compatible for both $X$ and $Y$. If $F$ is a convex
bifunction and $K \in \Omega(F)$, then the lower conjugate $\underline{K}^*$ is lower closed: it
is the bracket of the closed convex bifunction $F_*^*$. -/
theorem lowerClosedFn_lowerConjSaddle (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    LowerClosedFn (lowerConjSaddle Bu Bx K) := by
  rw [lowerConjSaddle_eq_bracket_lowerAdjointBifun Bu Bx hF hK]
  have := isContinuousPairing_prodPairing_flip Bu Bx
  exact lowerClosedFn_bracket Bu.flip Bx.flip (convexBifun_lowerAdjointBifun Bu Bx F)
    closedConvexBifun_lowerAdjointBifun

end ClassConjugates

end ConvexAnalysis
