/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.TFAE
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.RelativeInterior
import NumlibSurface.Rockafellar.Common.Euclidean
import NumlibSurface.Rockafellar.Chapter01.Section01

/-!
# Rockafellar, Section 7: Closures of convex functions

This module formalizes §7 of [rockafellar1970convex]: lower semicontinuity, the lower semicontinuous
hull, the closure $\operatorname{cl} f$ of a convex function
$f : \mathbb{R}^n \to [-\infty, +\infty]$, and closed convex functions. The main facts are that an
improper convex function is $-\infty$ throughout $\operatorname{ri}(\operatorname{dom} f)$, that for
proper convex $f$ the closure $\operatorname{cl} f$ is a closed proper convex function that agrees
with $f$ except perhaps on the relative boundary of $\operatorname{dom} f$, that
$(\operatorname{cl} f)(y)$ is the limit of $f$ along a line segment from a point of
$\operatorname{ri}(\operatorname{dom} f)$ to $y$, and that above $\inf f$ the level sets
$\{f \le \alpha\}$ and $\{f < \alpha\}$ have the same closure, relative interior and dimension. The
proofs specialize `Numlib.Analysis.Convex.Closure` and `Numlib.Analysis.Convex.RelativeInterior`.

All 17 numbered results of §7 are formalized. Three unnumbered claims of the text are also stated:
the lower semicontinuous hull is the greatest lower semicontinuous minorant
(`Rockafellar.lscHull_isGreatest`), closedness of a proper convex function is lower semicontinuity
(`Rockafellar.closedConvex_iff_lowerSemicontinuous_of_properConvex`), and the only closed improper
convex functions are the constants $+\infty$ and $-\infty$ (`Rockafellar.closed_improper_eq_const`).

## Main results

* Theorem 7.1, `Rockafellar.theorem_7_1`: lower semicontinuity, closed sublevel sets and a closed
  epigraph are equivalent.
* Theorem 7.2, `Rockafellar.theorem_7_2`: an improper convex function is $-\infty$ on
  $\operatorname{ri}(\operatorname{dom} f)$.
* Corollary 7.2.1, `Rockafellar.corollary_7_2_1`: a lower semicontinuous improper convex function
  has no finite values.
* Corollary 7.2.2, `Rockafellar.corollary_7_2_2`: for improper convex $f$, $\operatorname{cl} f$ is
  closed, improper and convex, and agrees with $f$ on $\operatorname{ri}(\operatorname{dom} f)$.
* Corollary 7.2.3, `Rockafellar.corollary_7_2_3`: if $\operatorname{dom} f$ is relatively open, then
  either $f > -\infty$ everywhere or $f$ has no finite values.
* Lemma 7.3, `Rockafellar.lemma_7_3`: $\operatorname{ri}(\operatorname{epi} f)$ consists of the
  pairs $(x, \mu)$ with $x \in \operatorname{ri}(\operatorname{dom} f)$ and $f(x) < \mu < \infty$.
* Corollary 7.3.1, `Rockafellar.corollary_7_3_1`: if $f(x) < \alpha$ for some $x$, then
  $f(x) < \alpha$ for some $x \in \operatorname{ri}(\operatorname{dom} f)$.
* Corollary 7.3.2, `Rockafellar.corollary_7_3_2`: if $\operatorname{ri} C \subseteq
  \operatorname{dom} f$ and $f(x) < \alpha$ for some $x \in \operatorname{cl} C$, then
  $f(x) < \alpha$ for some $x \in \operatorname{ri} C$.
* Corollary 7.3.3, `Rockafellar.corollary_7_3_3`: if $f$ is finite on a convex set $C$ and
  $f \ge \alpha$ on $C$, then $f \ge \alpha$ on $\operatorname{cl} C$.
* Corollary 7.3.4, `Rockafellar.corollary_7_3_4`: two convex functions with the same
  $\operatorname{ri}(\operatorname{dom} \cdot)$ that agree there have the same closure.
* Theorem 7.4, `Rockafellar.theorem_7_4`: for proper convex $f$, $\operatorname{cl} f$ is closed
  proper convex and agrees with $f$ off the relative boundary of $\operatorname{dom} f$.
* Corollary 7.4.1, `Rockafellar.corollary_7_4_1`: for proper convex $f$,
  $\operatorname{dom}(\operatorname{cl} f)$ lies between $\operatorname{dom} f$ and its closure,
  with the same closure, relative interior and dimension.
* Corollary 7.4.2, `Rockafellar.corollary_7_4_2`: a proper convex function whose effective domain is
  affine is closed.
* Theorem 7.5, `Rockafellar.theorem_7_5`: for proper convex $f$ and
  $x \in \operatorname{ri}(\operatorname{dom} f)$, $(\operatorname{cl} f)(y) = \lim_{\lambda
  \uparrow 1} f((1 - \lambda) x + \lambda y)$ for every $y$; `Rockafellar.theorem_7_5_improper` is
  the improper case for $y \in \operatorname{cl}(\operatorname{dom} f)$.
* Corollary 7.5.1, `Rockafellar.corollary_7_5_1`: for closed proper convex $f$ and
  $x \in \operatorname{dom} f$, $f(y) = \lim_{\lambda \uparrow 1} f((1 - \lambda) x + \lambda y)$
  for every $y$.
* Theorem 7.6, `Rockafellar.theorem_7_6`: for proper convex $f$ and $\inf f < \alpha$, the level
  sets $\{f \le \alpha\}$ and $\{f < \alpha\}$ have the closure
  $\{\operatorname{cl} f \le \alpha\}$, the relative interior $\{x \in
  \operatorname{ri}(\operatorname{dom} f) \mid f(x) < \alpha\}$, and the dimension of
  $\operatorname{dom} f$.
* Corollary 7.6.1, `Rockafellar.corollary_7_6_1`: for closed proper convex $f$ with relatively open
  domain and $\inf f < \alpha < +\infty$, $\operatorname{ri}\{f \le \alpha\} = \{f < \alpha\}$ and
  $\operatorname{cl}\{f < \alpha\} = \{f \le \alpha\}$.

## Implementation notes

* Lower semicontinuity is Mathlib's `LowerSemicontinuous`. The lower semicontinuous hull is
  `ConvexAnalysis.lscHull`, the function whose epigraph is
  $\operatorname{cl}(\operatorname{epi} f)$. The closure is `ConvexAnalysis.convexCl`, and $f$ is
  closed when `ConvexAnalysis.ClosedConvex f` holds, that is, when $\operatorname{cl} f = f$.
* The book defines $\operatorname{cl} f$ by cases: the lower semicontinuous hull when $f$ is nowhere
  $-\infty$, and the constant $-\infty$ otherwise. `ConvexAnalysis.convexCl` branches instead on
  whether the hull takes the value $-\infty$. This is the standard Γ-regularization, and it keeps
  $f^{**} = \operatorname{cl} f$ true in general. For convex $f$ the two definitions agree; for
  proper convex $f$ this is `ConvexAnalysis.ConvexFn.convexCl_eq_lscHull`.
* The space $\mathbb{R}^{n+1}$ that contains the epigraph is `Rockafellar.Rn n × ℝ`. The second
  coordinate of a point of `ConvexAnalysis.epi f` is a real number, so the condition $\mu < \infty$
  of the book is carried by the type.
* The limit $\lambda \uparrow 1$ is a limit along the filter `𝓝[<] (1 : ℝ)`, taken in the topology
  of `EReal`.
* The dimension `Rockafellar.dim` is the one of §1, with $\dim \emptyset = -1$.

## Deviations from the source

* **Definition of $\operatorname{cl} f$** (generalization). The book defines closure for convex
  functions and gives the epigraph-closure identity for proper convex functions. The Lean
  closure extends to arbitrary functions by testing whether the lower semicontinuous hull takes
  the value $-\infty$. See `ConvexAnalysis.convexCl`.
* **Closedness of a proper convex function** (generalization). The book states that closedness is
  lower semicontinuity for a proper convex function; convexity is not needed. See
  `Rockafellar.closedConvex_iff_lowerSemicontinuous_of_properConvex`.
* **Closed improper convex functions** (generalization). The book states that the only closed
  improper convex functions are the constants $+\infty$ and $-\infty$; convexity is not needed. See
  `Rockafellar.closed_improper_eq_const`.
* **Theorem 7.6, dimension argument** (generalization). The strict sublevel set restricted to
  the relative interior of the effective domain has the same affine hull as that domain
  without properness. See `Rockafellar.affineSpan_relint_convexDom_lt`.
-/

open Set Filter Topology

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ} {f g : Rn n → EReal}

/-!
### The definitions of Section 7

The lower semicontinuous hull, the closure of a convex function, and closed convex functions.
-/

/-- **Section 7** of [rockafellar1970convex], definition of the lower semicontinuous hull. For every
$f : \mathbb{R}^n \to [-\infty, +\infty]$, the lower semicontinuous hull of $f$ is the greatest
lower semicontinuous function $g$ with $g \le f$.

The book states this as "there exists a greatest lower semi-continuous function (not necessarily
finite) majorized by $f$". The hull is `ConvexAnalysis.lscHull`. -/
theorem lscHull_isGreatest (f : Rn n → EReal) :
    IsGreatest {g : Rn n → EReal | LowerSemicontinuous g ∧ g ≤ f} (lscHull f) :=
  isGreatest_lscHull f

/-- **Section 7** of [rockafellar1970convex], closedness of proper functions. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ be proper. Then $f$ is closed, that is,
$\operatorname{cl} f = f$, if and only if $f$ is lower semicontinuous.

**Generalization.** The book states: "For a proper convex function, closedness is thus the same
as lower semi-continuity." Convexity is not used.

The proof uses only the condition $f > -\infty$ of properness. -/
theorem closedConvex_iff_lowerSemicontinuous_of_properConvex (hp : ProperConvex f) :
    ClosedConvex f ↔ LowerSemicontinuous f :=
  closedConvex_iff_lowerSemicontinuous hp.ne_bot

/-- **Section 7** of [rockafellar1970convex], closed improper functions. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ be closed and improper. Then $f$ is the constant
$-\infty$ or the constant $+\infty$.

**Generalization.** The book states this for convex functions: "the only closed improper convex
functions are the constant functions $+\infty$ and $-\infty$". Convexity is not needed. -/
theorem closed_improper_eq_const (hc : ClosedConvex f) (himp : ¬ ProperConvex f) :
    f = (fun _ => (⊥ : EReal)) ∨ f = fun _ => (⊤ : EReal) :=
  eq_const_of_closedConvex_of_not_properConvex hc himp

/-!
### Dimension bookkeeping

The form of Corollary 6.3.1 that Corollary 7.4.1 and Theorem 7.6 need. The dimension
`Rockafellar.dim` is the one of §1.
-/

/-- Let $S, T \subseteq \mathbb{R}^n$ be nonempty sets with the same affine hull. Then
$\dim S = \dim T$. -/
theorem dim_eq_of_affineSpan_eq {S T : Set (Rn n)} (hS : S.Nonempty) (hT : T.Nonempty)
    (h : affineSpan ℝ S = affineSpan ℝ T) : dim S = dim T := by
  rw [dim_eq_finrank_direction hS, dim_eq_finrank_direction hT, h]

/-- Let $S, T \subseteq \mathbb{R}^n$ have the same closure. Then $\dim S = \dim T$.

This is the dimension part of Corollary 6.3.1 of [rockafellar1970convex], without the convexity
hypothesis: sets with the same closure have the same affine hull. -/
theorem dim_eq_of_closure_eq {S T : Set (Rn n)} (h : closure S = closure T) : dim S = dim T := by
  have hspan : affineSpan ℝ S = affineSpan ℝ T := by
    rw [← affineSpan_closure S, h, affineSpan_closure]
  rcases Set.eq_empty_or_nonempty S with hS | hS
  · have hT : T = ∅ := (closure_empty_iff T).1 (by rw [← h, hS, closure_empty])
    rw [hS, hT]
  · have hT : T.Nonempty := by
      rcases Set.eq_empty_or_nonempty T with hTe | hTe
      · exact absurd ((closure_empty_iff S).1 (by rw [h, hTe, closure_empty])) hS.ne_empty
      · exact hTe
    exact dim_eq_of_affineSpan_eq hS hT hspan

/-! ### Theorem 7.1 -/

/-- **Theorem 7.1** of [rockafellar1970convex]. Let $f$ be an arbitrary function from $\mathbb{R}^n$
to $[-\infty, +\infty]$. Then the following conditions are equivalent:

(a) $f$ is lower semicontinuous throughout $\mathbb{R}^n$;

(b) $\{x \mid f(x) \le \alpha\}$ is closed for every $\alpha \in \mathbb{R}$;

(c) the epigraph of $f$ is a closed set in $\mathbb{R}^{n+1}$.

Neither convexity nor finite dimension is used. The space $\mathbb{R}^{n+1}$ is
`Rockafellar.Rn n × ℝ`, and the epigraph is `ConvexAnalysis.epi f`. -/
theorem theorem_7_1 (f : Rn n → EReal) :
    List.TFAE [LowerSemicontinuous f, ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)},
      IsClosed (epi f)] := by
  tfae_have 1 ↔ 2 := lowerSemicontinuous_iff_isClosed_le
  tfae_have 1 ↔ 3 := lowerSemicontinuous_iff_isClosed_epi
  tfae_finish

/-! ### Theorem 7.2 and its corollaries -/

/-- **Theorem 7.2** of [rockafellar1970convex]. Let $f$ be an improper convex function on
$\mathbb{R}^n$. Then $f(x) = -\infty$ for every $x \in \operatorname{ri}(\operatorname{dom} f)$.
Thus an improper convex function is necessarily infinite except perhaps at relative boundary
points of its effective domain.

The hypothesis that $f$ is improper is part of the statement, not a restriction: the theorem is
about improper functions. -/
theorem theorem_7_2 (hf : ConvexFn f) (himp : ¬ ProperConvex f) {x : Rn n}
    (hx : x ∈ ri (convexDom f)) :
    f x = ⊥ :=
  hf.eq_bot_of_mem_relint_convexDom himp hx

/-- **Corollary 7.2.1** of [rockafellar1970convex]. Let $f$ be a lower semicontinuous improper
convex function on $\mathbb{R}^n$. Then $f$ has no finite values: $f(x) = -\infty$ or
$f(x) = +\infty$ for every $x$. -/
theorem corollary_7_2_1 (hf : ConvexFn f) (hl : LowerSemicontinuous f) (himp : ¬ ProperConvex f)
    (x : Rn n) : f x = ⊥ ∨ f x = ⊤ := by
  by_cases hx : x ∈ closure (convexDom f)
  · exact Or.inl (hf.eq_bot_of_mem_closure_convexDom hl himp hx)
  · refine Or.inr ?_
    by_contra h
    exact hx (subset_closure (mem_convexDom.2 (lt_of_le_of_ne le_top h)))

/-- **Corollary 7.2.2** of [rockafellar1970convex]. Let $f$ be an improper convex function on
$\mathbb{R}^n$. Then $\operatorname{cl} f$ is a closed improper convex function, and
$(\operatorname{cl} f)(x) = f(x)$ for every $x \in \operatorname{ri}(\operatorname{dom} f)$.

The agreement on $\operatorname{ri}(\operatorname{dom} f)$ is not obtained from
$\operatorname{epi}(\operatorname{cl} f) = \operatorname{cl}(\operatorname{epi} f)$, which fails
exactly in this improper case. -/
theorem corollary_7_2_2 (hf : ConvexFn f) (himp : ¬ ProperConvex f) :
    ConvexFn (convexCl f) ∧ ClosedConvex (convexCl f) ∧ ¬ ProperConvex (convexCl f) ∧
      ∀ x ∈ ri (convexDom f), convexCl f x = f x :=
  ⟨convexFn_convexCl hf, closedConvex_convexCl f, not_properConvex_convexCl himp,
    fun _ hx => hf.convexCl_eq_of_mem_relint_convexDom hx⟩

/-- **Corollary 7.2.3** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$
whose effective domain is relatively open, that is, $\operatorname{ri}(\operatorname{dom} f) =
\operatorname{dom} f$ (for instance if $\operatorname{dom} f = \mathbb{R}^n$). Then either
$f(x) > -\infty$ for every $x$, or $f(x)$ is infinite for every $x$. -/
theorem corollary_7_2_3 (hf : ConvexFn f) (hopen : ri (convexDom f) = convexDom f) :
    (∀ x, f x ≠ ⊥) ∨ ∀ x, f x = ⊥ ∨ f x = ⊤ :=
  hf.forall_ne_bot_or_forall_infinite hopen

/-! ### Lemma 7.3 and its corollaries -/

/-- **Lemma 7.3** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$. Then
$\operatorname{ri}(\operatorname{epi} f)$ consists of the pairs
$(x, \mu) \in \mathbb{R}^n \times \mathbb{R}$ such that
$x \in \operatorname{ri}(\operatorname{dom} f)$ and $f(x) < \mu < \infty$.

The condition $\mu < \infty$ is carried by the type: the second component of a point of
`Rockafellar.Rn n × ℝ` is a real number. -/
theorem lemma_7_3 (hf : ConvexFn f) :
    ri (epi f) = {p : Rn n × ℝ | p.1 ∈ ri (convexDom f) ∧ f p.1 < (p.2 : EReal)} :=
  hf.relint_epi

/-- **Corollary 7.3.1** of [rockafellar1970convex]. Let $\alpha$ be a real number, and let $f$ be a
convex function on $\mathbb{R}^n$ such that $f(x) < \alpha$ for some $x$. Then $f(x) < \alpha$
for some $x \in \operatorname{ri}(\operatorname{dom} f)$. -/
theorem corollary_7_3_1 (hf : ConvexFn f) {α : ℝ} (h : ∃ x, f x < (α : EReal)) :
    ∃ x ∈ ri (convexDom f), f x < (α : EReal) :=
  hf.exists_mem_relint_convexDom_lt h

/-- **Corollary 7.3.2** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$,
let $C \subseteq \mathbb{R}^n$ be a convex set with $\operatorname{ri} C \subseteq
\operatorname{dom} f$, and let $\alpha$ be a real number. If $f(x) < \alpha$ for some
$x \in \operatorname{cl} C$, then $f(x) < \alpha$ for some $x \in \operatorname{ri} C$. -/
theorem corollary_7_3_2 (hf : ConvexFn f) {C : Set (Rn n)} (hC : Convex ℝ C)
    (hsub : ri C ⊆ convexDom f) {α : ℝ} (h : ∃ x ∈ closure C, f x < (α : EReal)) :
    ∃ x ∈ ri C, f x < (α : EReal) := by
  have hgc : ConvexFn (ConvexAnalysis.convexRestrict (closure C) f) := hf.convexRestrict hC.closure
  have hle : convexDom (ConvexAnalysis.convexRestrict (closure C) f) ⊆ closure C := by
    intro z hz
    by_contra hzc
    rw [mem_convexDom, convexRestrict_of_notMem hzc] at hz
    exact absurd hz (lt_irrefl ⊤)
  have hge : ri C ⊆ convexDom (ConvexAnalysis.convexRestrict (closure C) f) := by
    intro z hz
    rw [mem_convexDom, convexRestrict_of_mem (subset_closure (intrinsicInterior_subset hz))]
    exact hsub hz
  have hri : ri (convexDom (ConvexAnalysis.convexRestrict (closure C) f)) = ri C :=
    (Convex.closure_eq_iff_relint_eq hgc.convex_convexDom hC).1
      (Convex.closure_eq_of_relint_subset_of_subset_closure hC hge hle)
  have hex : ∃ y, ConvexAnalysis.convexRestrict (closure C) f y < (α : EReal) := by
    obtain ⟨x, hx, hxα⟩ := h
    exact ⟨x, by rw [convexRestrict_of_mem hx]; exact hxα⟩
  obtain ⟨z, hz, hzα⟩ := hgc.exists_mem_relint_convexDom_lt hex
  rw [hri] at hz
  rw [convexRestrict_of_mem (subset_closure (intrinsicInterior_subset hz))] at hzα
  exact ⟨z, hz, hzα⟩

/-- **Corollary 7.3.3** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$,
let $C \subseteq \mathbb{R}^n$ be a convex set on which $f$ is finite, and let $\alpha$ be a
real number. If $f(x) \ge \alpha$ for every $x \in C$, then $f(x) \ge \alpha$ for every
$x \in \operatorname{cl} C$.

This is the form of the book, which needs $f > -\infty$ only on $C$. The backbone result
`ConvexAnalysis.ConvexFn.le_of_mem_closure` assumes $f > -\infty$ everywhere. -/
theorem corollary_7_3_3 (hf : ConvexFn f) {C : Set (Rn n)} (hC : Convex ℝ C)
    (hfin : ∀ x ∈ C, f x ≠ ⊥ ∧ f x ≠ ⊤) {α : ℝ} (hge : ∀ x ∈ C, (α : EReal) ≤ f x) {x : Rn n}
    (hx : x ∈ closure C) : (α : EReal) ≤ f x := by
  by_contra hlt
  obtain ⟨z, hz, hzα⟩ := corollary_7_3_2 hf hC
    (fun y hy => mem_convexDom.2 (lt_of_le_of_ne le_top (hfin y (intrinsicInterior_subset hy)).2))
    ⟨x, hx, not_le.1 hlt⟩
  exact absurd (hge z (intrinsicInterior_subset hz)) (not_le.2 hzα)

/-- **Corollary 7.3.4** of [rockafellar1970convex]. Let $f$ and $g$ be convex functions on
$\mathbb{R}^n$ with $\operatorname{ri}(\operatorname{dom} f) =
\operatorname{ri}(\operatorname{dom} g)$, and suppose that $f(x) = g(x)$ for every $x$ in this
set. Then $\operatorname{cl} f = \operatorname{cl} g$.

The rest of the book uses this corollary more than the others of Lemma 7.3. The proof needs no
case split on properness, unlike the proof in the book, because `ConvexAnalysis.convexCl`
depends on $f$ only through `ConvexAnalysis.lscHull f`. -/
theorem corollary_7_3_4 (hf : ConvexFn f) (hg : ConvexFn g)
    (hdom : ri (convexDom f) = ri (convexDom g))
    (hagree : ∀ x ∈ ri (convexDom f), f x = g x) : convexCl f = convexCl g := by
  have hri : ri (epi f) = ri (epi g) := by
    rw [hf.relint_epi, hg.relint_epi]
    ext p
    simp only [Set.mem_ofPred_eq, ← hdom]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [← hagree p.1 h1]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [hagree p.1 h1]⟩
  have hcl : closure (epi f) = closure (epi g) :=
    (Convex.closure_eq_iff_relint_eq hf.convex_epi hg.convex_epi).2 hri
  have hhull : lscHull f = lscHull g := epi_injective (by rw [epi_lscHull, epi_lscHull, hcl])
  by_cases hb : ∃ x, lscHull f x = ⊥
  · obtain ⟨x, hx⟩ := hb
    rw [convexCl_of_exists_eq_bot ⟨x, hx⟩,
      convexCl_of_exists_eq_bot ⟨x, by rw [← hhull]; exact hx⟩]
  · rw [convexCl_of_forall_ne_bot (fun x hx => hb ⟨x, hx⟩),
      convexCl_of_forall_ne_bot (fun x hx => hb ⟨x, by rw [hhull]; exact hx⟩), hhull]

/-! ### Theorem 7.4 and its corollaries -/

/-- **Theorem 7.4** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$. Then $\operatorname{cl} f$ is a closed proper convex function. Moreover,
$(\operatorname{cl} f)(x) = f(x)$ except perhaps at relative boundary points of
$\operatorname{dom} f$, that is, for every $x \notin \operatorname{cl}(\operatorname{dom} f)
\setminus \operatorname{ri}(\operatorname{dom} f)$.

"Closed proper convex" is `ConvexAnalysis.ClosedProperConvexFn`. -/
theorem theorem_7_4 (hf : ConvexFn f) (hp : ProperConvex f) :
    ClosedProperConvexFn (convexCl f) ∧ ∀ x ∉ closure (convexDom f) \ ri (convexDom f),
        convexCl f x = f x := by
  refine ⟨⟨convexFn_convexCl hf, closedConvex_convexCl f, hf.properConvex_convexCl hp⟩,
      fun x hx => ?_⟩
  by_cases hc : x ∈ closure (convexDom f)
  · exact hf.convexCl_eq_of_mem_relint_convexDom (by
      by_contra hr
      exact hx ⟨hc, hr⟩)
  · exact hf.convexCl_eq_of_notMem_closure_convexDom hp hc

/-- **Corollary 7.4.1** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$. Then $\operatorname{dom}(\operatorname{cl} f)$ differs from
$\operatorname{dom} f$ at most by some additional relative boundary points of
$\operatorname{dom} f$:
$$\operatorname{dom} f \subseteq \operatorname{dom}(\operatorname{cl} f) \subseteq
  \operatorname{cl}(\operatorname{dom} f).$$
In particular, $\operatorname{dom}(\operatorname{cl} f)$ and $\operatorname{dom} f$ have the
same closure, the same relative interior, and the same dimension.

The dimension clause comes from `Rockafellar.dim_eq_of_closure_eq`, a form of Corollary 6.3.1. -/
theorem corollary_7_4_1 (hf : ConvexFn f) (hp : ProperConvex f) :
    convexDom f ⊆ convexDom (convexCl f) ∧ convexDom (convexCl f) ⊆ closure (convexDom f) ∧
      closure (convexDom (convexCl f)) = closure (convexDom f) ∧ ri (convexDom (convexCl f))
          = ri (convexDom f) ∧
        dim (convexDom (convexCl f)) = dim (convexDom f) := by
  have hsub : convexDom f ⊆ convexDom (convexCl f) := by
    rw [hf.convexCl_eq_lscHull hp]; exact convexDom_subset_convexDom_lscHull f
  have hsup : convexDom (convexCl f) ⊆ closure (convexDom f) := by
    rw [hf.convexCl_eq_lscHull hp]; exact convexDom_lscHull_subset_closure_convexDom f
  have hcl : closure (convexDom (convexCl f)) = closure (convexDom f) :=
    Convex.closure_eq_of_relint_subset_of_subset_closure hf.convex_convexDom
      (intrinsicInterior_subset.trans hsub) hsup
  exact ⟨hsub, hsup, hcl, hf.relint_convexDom_convexCl hp, dim_eq_of_closure_eq hcl⟩

/-- **Corollary 7.4.2** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$ such that $\operatorname{dom} f$ is an affine set (which is true in particular if
$f$ is finite throughout $\mathbb{R}^n$). Then $f$ is closed.

Affine sets are `Rockafellar.IsAffineSet`, from `NumlibSurface.Rockafellar.Chapter01.Section01`,
which also relates them to Mathlib's `AffineSubspace`. -/
theorem corollary_7_4_2 (hf : ConvexFn f) (hp : ProperConvex f) (hdom : IsAffineSet (convexDom f)) :
    ClosedConvex f :=
  hf.closedConvex_of_convexDom_eq_coe hp hdom.coe_toAffineSubspace.symm

/-! ### Theorem 7.5 and its corollary -/

/-- **Theorem 7.5** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $x \in \operatorname{ri}(\operatorname{dom} f)$. Then for every
$y \in \mathbb{R}^n$,
$$(\operatorname{cl} f)(y) = \lim_{\lambda \uparrow 1} f((1 - \lambda) x + \lambda y).$$

The limit $\lambda \uparrow 1$ is the filter `𝓝[<] (1 : ℝ)`, and the limit is taken in
$[-\infty, +\infty]$. The parenthetical clause of the theorem, for improper $f$, is
`Rockafellar.theorem_7_5_improper`. -/
theorem theorem_7_5 (hf : ConvexFn f) (hp : ProperConvex f) {x : Rn n} (hx : x ∈ ri (convexDom f))
    (y : Rn n) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (convexCl f y)) :=
  hf.tendsto_convexCl_along_segment_relint hp hx y

/-- **Theorem 7.5** of [rockafellar1970convex], the improper case. Let $f$ be an improper convex
function on $\mathbb{R}^n$, let $x \in \operatorname{ri}(\operatorname{dom} f)$, and let
$y \in \operatorname{cl}(\operatorname{dom} f)$. Then
$$(\operatorname{cl} f)(y) = \lim_{\lambda \uparrow 1} f((1 - \lambda) x + \lambda y).$$

The hypothesis $y \in \operatorname{cl}(\operatorname{dom} f)$ is necessary: for $y$ outside it,
$f$ is eventually $+\infty$ along the segment. -/
theorem theorem_7_5_improper (hf : ConvexFn f) (himp : ¬ ProperConvex f) {x : Rn n}
    (hx : x ∈ ri (convexDom f)) {y : Rn n} (hy : y ∈ closure (convexDom f)) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (convexCl f y)) := by
  have hxbot : f x = ⊥ := hf.eq_bot_of_mem_relint_convexDom himp hx
  have hhull : lscHull f x = ⊥ := le_bot_iff.1 (by rw [← hxbot]; exact lscHull_le f x)
  rw [convexCl_of_exists_eq_bot ⟨x, hhull⟩]
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
  exact (hf.eq_bot_of_mem_relint_convexDom himp
    (Convex.segment_mem_relint hf.convex_convexDom hx hy ha.1 ha.2)).symm

/-- **Corollary 7.5.1** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$, and let $x \in \operatorname{dom} f$. Then for every $y \in \mathbb{R}^n$,
$$f(y) = \lim_{\lambda \uparrow 1} f((1 - \lambda) x + \lambda y).$$

The proof does not go through Theorem 7.5 and a restriction to a line, so no relative interiors
appear. -/
theorem corollary_7_5_1 (hf : ClosedProperConvexFn f) {x : Rn n} (hx : x ∈ convexDom f) (y : Rn n) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) :=
  tendsto_along_segment_of_closed_proper hf hx y

/-! ### Theorem 7.6 and its corollary -/

/-- Let $f$ be a convex function on $\mathbb{R}^n$, and let $\alpha$ be a real number with
$\inf f < \alpha$. Then the set $\{x \in \operatorname{ri}(\operatorname{dom} f) \mid f(x) <
\alpha\}$ has the same affine hull as $\operatorname{dom} f$.

**Generalization.** The dimension argument of Theorem 7.6 is for proper convex $f$. The affine
hull equality, which implies the dimension equality, holds for every convex $f$.

This gives the dimension clause of Theorem 7.6. The book obtains that clause by counting the
dimensions of slices; this proof uses the line segment principle. -/
theorem affineSpan_relint_convexDom_lt (hf : ConvexFn f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    affineSpan ℝ {x ∈ ri (convexDom f) | f x < (α : EReal)} = affineSpan ℝ (convexDom f) := by
  obtain ⟨y, hy, hyα⟩ := hf.exists_mem_relint_convexDom_lt (iInf_lt_iff.1 hα)
  set R : Set (Rn n) := {x ∈ ri (convexDom f) | f x < (α : EReal)} with hR
  refine le_antisymm (affineSpan_mono ℝ fun z hz => intrinsicInterior_subset hz.1) ?_
  rw [← hf.convex_convexDom.affineSpan_relint, affineSpan_le]
  intro x hx
  by_cases hxα : f x < (α : EReal)
  · exact subset_affineSpan ℝ R ⟨hx, hxα⟩
  obtain ⟨β, hyβ, hβα⟩ := EReal.lt_iff_exists_real_btwn.1 hyα
  obtain ⟨γ, hxγ, -⟩ :=
    EReal.lt_iff_exists_real_btwn.1 (mem_convexDom.1 (intrinsicInterior_subset hx))
  have hβα' : β < α := by exact_mod_cast hβα
  have hpos : (0 : ℝ) < α - β := by linarith
  set t : ℝ := min (1 / 2) ((α - β) / (2 * (|γ - β| + 1))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hpos (by positivity))
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htb : t * (2 * (|γ - β| + 1)) ≤ α - β :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have habs : t * (γ - β) ≤ t * |γ - β| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le
  have hkey : (1 - t) * β + t * γ < α := by nlinarith [htb, habs, ht0, hβα']
  have hzri : (1 - t) • y + t • x ∈ ri (convexDom f) :=
    Convex.segment_mem_relint hf.convex_convexDom hy
      (subset_closure (intrinsicInterior_subset hx)) ht0.le ht1
  have hzα : f ((1 - t) • y + t • x) < (α : EReal) :=
    lt_of_le_of_lt (hf.epi_combo hyβ.le hxγ.le (by linarith) ht0.le (by ring))
      (by exact_mod_cast hkey)
  have hmem := AffineSubspace.combo_mem (M := affineSpan ℝ R)
    (subset_affineSpan ℝ R ⟨hy, hyα⟩) (subset_affineSpan ℝ R ⟨hzri, hzα⟩) t⁻¹
  rwa [combo_prolong y x ht0.ne'] at hmem


/-- **Theorem 7.6** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $\alpha$ be a real number with $\inf f < \alpha$. Then the level sets
$\{x \mid f(x) \le \alpha\}$ and $\{x \mid f(x) < \alpha\}$ have the same closure
$$\{x \mid (\operatorname{cl} f)(x) \le \alpha\},$$
the same relative interior
$$\{x \in \operatorname{ri}(\operatorname{dom} f) \mid f(x) < \alpha\},$$
and the same dimension as $\operatorname{dom} f$.

The infimum $\inf f$ is taken over all of $\mathbb{R}^n$, in $[-\infty, +\infty]$. -/
theorem theorem_7_6 (hf : ConvexFn f) (hp : ProperConvex f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    closure {x | f x ≤ (α : EReal)} = {x | convexCl f x ≤ (α : EReal)} ∧
      closure {x | f x < (α : EReal)} = {x | convexCl f x ≤ (α : EReal)} ∧
        ri {x | f x ≤ (α : EReal)} = {x ∈ ri (convexDom f) | f x < (α : EReal)} ∧
          ri {x | f x < (α : EReal)} = {x ∈ ri (convexDom f) | f x < (α : EReal)} ∧
            dim {x | f x ≤ (α : EReal)} = dim (convexDom f) ∧
              dim {x | f x < (α : EReal)} = dim (convexDom f) := by
  obtain ⟨y, hy, hyα⟩ := hf.exists_mem_relint_convexDom_lt (iInf_lt_iff.1 hα)
  have hdim : ∀ S : Set (Rn n), Convex ℝ S → S.Nonempty →
      ri S = {x ∈ ri (convexDom f) | f x < (α : EReal)} → dim S = dim (convexDom f) := by
    intro S hS hne hri
    refine dim_eq_of_affineSpan_eq hne ⟨y, intrinsicInterior_subset hy⟩ ?_
    rw [← hS.affineSpan_relint, hri, affineSpan_relint_convexDom_lt hf hα]
  exact ⟨hf.closure_setOf_le_convexCl hp hα,
    by rw [hf.closure_setOf_lt hα, hf.convexCl_eq_lscHull hp],
    hf.relint_setOf_le hα, hf.relint_setOf_lt hα,
    hdim _ (hf.convex_le _) ⟨y, hyα.le⟩ (hf.relint_setOf_le hα),
    hdim _ (hf.convex_lt _) ⟨y, hyα⟩ (hf.relint_setOf_lt hα)⟩

/-- **Corollary 7.6.1** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$ whose effective domain is relatively open, that is,
$\operatorname{ri}(\operatorname{dom} f) = \operatorname{dom} f$ (in particular if
$\operatorname{dom} f$ is an affine set), and let $\alpha$ be a real number with
$\inf f < \alpha$. Then
$$\operatorname{ri}\{x \mid f(x) \le \alpha\} = \{x \mid f(x) < \alpha\}, \qquad
  \operatorname{cl}\{x \mid f(x) < \alpha\} = \{x \mid f(x) \le \alpha\}.$$

The condition $\alpha < +\infty$ of the book is carried by the type of $\alpha$. The proof of
the first formula uses only that $\operatorname{dom} f$ is relatively open, and the proof of the
second uses only that $f$ is closed. -/
theorem corollary_7_6_1 (hf : ConvexFn f) (hp : ProperConvex f) (hc : ClosedConvex f)
    (hopen : ri (convexDom f) = convexDom f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    ri {x | f x ≤ (α : EReal)} = {x | f x < (α : EReal)} ∧
      closure {x | f x < (α : EReal)} = {x | f x ≤ (α : EReal)} :=
  ⟨hf.relint_setOf_le_of_relint_convexDom_eq hopen hα, hf.closure_setOf_lt_of_closedConvex hp hc hα⟩

end Rockafellar
