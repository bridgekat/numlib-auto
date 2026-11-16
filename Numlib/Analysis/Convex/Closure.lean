/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Numlib.Analysis.Convex.Homogeneous
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Epi
import Numlib.Analysis.Convex.Separation

/-!
# Closures of convex functions

Let $E$ be a real topological vector space and let $f : E \to [-\infty, +\infty]$. The **lower
semicontinuous hull** $\operatorname{lsc} f$ is the function whose epigraph is the closure
$\operatorname{cl}(\operatorname{epi} f)$; it is the greatest lower semicontinuous minorant of $f$.
The **closure** $\operatorname{cl} f$ of a convex function is $\operatorname{lsc} f$, except that it
is the constant $-\infty$ when $\operatorname{lsc} f$ takes the value $-\infty$ somewhere. A
function is **closed** if $\operatorname{cl} f = f$. The concave counterparts are obtained by
negation: the upper semicontinuous hull of $g$ is $-\operatorname{lsc}(-g)$, and the concave closure
of $g$ is $-\operatorname{cl}(-g)$. The presentation follows §7 of [rockafellar1970convex].

The file proves that $f$ is lower semicontinuous if and only if its epigraph is closed, that
$\operatorname{lsc} f$ has the epigraph $\operatorname{cl}(\operatorname{epi} f)$ with no hypothesis
on $f$, and that $(\operatorname{lsc} f)(x) = \liminf_{y \to x} f(y)$. It characterizes the closed
functions, shows that a closed proper convex function on a locally convex space has a continuous
affine minorant, and computes the closure as a limit along a segment.

## Main definitions

* `ConvexAnalysis.lscHull`: the lower semicontinuous hull $\operatorname{lsc} f$, with epigraph
  $\operatorname{cl}(\operatorname{epi} f)$; `ConvexAnalysis.uscHull` is the upper semicontinuous
  hull $-\operatorname{lsc}(-g)$.
* `ConvexAnalysis.convexCl`: the closure $\operatorname{cl} f$ of a convex function.
* `ConvexAnalysis.ClosedConvex`: $f$ is closed, that is, $\operatorname{cl} f = f$.
* `ConvexAnalysis.concaveCl`, `ConvexAnalysis.ClosedConcave`: the concave closure
  $-\operatorname{cl}(-g)$, which [rockafellar1970convex] also writes $\operatorname{cl} g$, and the
  functions that it fixes; it is the upper semicontinuous hull outside the exceptional case.
* `ConvexAnalysis.ClosedProperConvexFn`: $f$ is closed, proper and convex; this is the standing
  hypothesis of the duality theory. `ConvexAnalysis.ClosedProperConcaveFn` is the concave
  counterpart.
* `ConvexAnalysis.lscHullClosure`, `ConvexAnalysis.convexClClosure`: the two operations as closure
  operators on the order dual of the functions $E \to [-\infty, +\infty]$.

## Main results

* `ConvexAnalysis.lowerSemicontinuous_iff_isClosed_epi`,
  `ConvexAnalysis.lowerSemicontinuous_iff_isClosed_le`: lower semicontinuity, closed sublevel sets
  and a closed epigraph are equivalent.
* `ConvexAnalysis.epi_lscHull`: $\operatorname{epi}(\operatorname{lsc} f) =
  \operatorname{cl}(\operatorname{epi} f)$, with no hypothesis on $f$.
* `ConvexAnalysis.isGreatest_lscHull`: $\operatorname{lsc} f$ is the greatest lower semicontinuous
  minorant of $f$.
* `ConvexAnalysis.closedConvex_iff`: $f$ is closed if and only if $f \equiv -\infty$, or $f$ is
  lower semicontinuous and never $-\infty$.
* `ConvexAnalysis.iInf_convexCl_eq_iInf`: $f$ and $\operatorname{cl} f$ have the same infimum.
* `ConvexAnalysis.ConvexFn.eq_bot_or_eq_top`: a lower semicontinuous convex function that takes the
  value $-\infty$ has no finite values. This replaces the dichotomy for improper functions on the
  relative interior, which needs finite dimension.
* `ConvexAnalysis.exists_affine_le_of_closed_proper`: a closed proper convex function on a locally
  convex space has a continuous affine minorant; this is the main step of the Fenchel–Moreau
  theorem.
* `ConvexAnalysis.tendsto_lscHull_along_segment`,
  `ConvexAnalysis.tendsto_along_segment_of_closed_proper`: the closure as a limit along a segment,
  with the interior of $\operatorname{epi} f$ in place of its relative interior.
* `ConvexAnalysis.lscHull_le_setOf`: $\{x \mid (\operatorname{lsc} f)(x) \le \alpha\} =
  \bigcap_{\mu > \alpha} \operatorname{cl}\{x \mid f(x) \le \mu\}$, the part of the description of
  the level sets of the closure that does not need relative interiors.
* `ConvexAnalysis.lscHull_eq_liminf`, `ConvexAnalysis.convexCl_eq_liminf_or`: the hull and the
  closure as $\liminf_{y \to x} f(y)$.
* `ConvexAnalysis.posHomogeneous_lscHull`, `ConvexAnalysis.posHomogeneous_convexCl`: both hulls
  preserve positive homogeneity.
* `ConvexAnalysis.closedProperConvexFn_coe_affineMap`: a continuous affine function is closed proper
  convex.

## Implementation notes

* The epigraph is `ConvexAnalysis.epi`, the set of pairs $(x, \mu) \in E \times \mathbb{R}$ with
  $f(x) \le \mu$, and a function is recovered from a set of pairs by `ConvexAnalysis.ofEpi`.
* `ConvexAnalysis.convexCl` decides between its two cases by $\operatorname{lsc} f$, not by $f$ as
  [rockafellar1970convex] does. The two choices agree for convex $f$ on $\mathbb{R}^n$ but not in
  general, and the choice by $f$ would make the Fenchel–Moreau theorem false: a discontinuous linear
  functional $g$ on an infinite-dimensional space is convex, finite and proper, but its kernel is
  dense, so $\operatorname{lsc} g \equiv -\infty$ and $g$ has no continuous affine minorant. The
  choice by the hull is the standard $\Gamma$-regularization and makes
  $f^{**} = \operatorname{cl} f$ hold without conditions. The cost is that the implication "$f$
  proper implies $\operatorname{cl} f$ proper" needs finite dimension. It is
  `ConvexAnalysis.ConvexFn.properConvex_convexCl` in `Numlib.Analysis.Convex.RelativeInterior`,
  together with the dichotomy for improper functions on the relative interior.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### Lower semicontinuity -/

section Semicontinuity

variable {E : Type*} [TopologicalSpace E] {f g : E → EReal}

/-- **A function is lower semicontinuous if and only if its epigraph is closed.** Let $E$ be a
topological space and let $f : E \to [-\infty, +\infty]$. Then $f$ is lower semicontinuous if
and only if $\operatorname{epi} f = \{(x, \mu) \in E \times \mathbb{R} \mid f(x) \le \mu\}$ is
closed in $E \times \mathbb{R}$. -/
theorem lowerSemicontinuous_iff_isClosed_epi : LowerSemicontinuous f ↔ IsClosed (epi f) := by
  constructor
  · intro hf
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    rintro ⟨x, μ⟩ hp
    obtain ⟨r, hμr, hrf⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hp)
    refine mem_of_superset
      (prod_mem_nhds (hf x (r : EReal) hrf) (Iio_mem_nhds (by exact_mod_cast hμr))) ?_
    rintro ⟨z, ν⟩ ⟨hz, hν⟩
    have hz' : (r : EReal) < f z := hz
    have hν' : ν < r := hν
    exact not_le.2 (lt_trans (by exact_mod_cast hν') hz')
  · intro hF x y hy
    obtain ⟨r, hyr, hrf⟩ := EReal.lt_iff_exists_real_btwn.1 hy
    have hclosed : IsClosed {z : E | f z ≤ (r : EReal)} := by
      have hpre : {z : E | f z ≤ (r : EReal)} = (fun z : E => (z, r)) ⁻¹' epi f := rfl
      rw [hpre]
      exact hF.preimage (continuous_id.prodMk continuous_const)
    filter_upwards [hclosed.isOpen_compl.mem_nhds (not_le.2 hrf)] with z hz
    exact hyr.trans (not_le.1 hz)

/-- **A function is lower semicontinuous if and only if its sublevel sets are closed.** Let $E$ be a
topological space and let $f : E \to [-\infty, +\infty]$. Then $f$ is lower semicontinuous if
and only if $\{x \mid f(x) \le \alpha\}$ is closed for every $\alpha \in \mathbb{R}$. -/
theorem lowerSemicontinuous_iff_isClosed_le :
    LowerSemicontinuous f ↔ ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)} := by
  constructor
  · intro hf α
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hf x (α : EReal) (not_le.1 hx)] with z hz using not_le.2 hz
  · intro h x y hy
    obtain ⟨r, hyr, hrf⟩ := EReal.lt_iff_exists_real_btwn.1 hy
    filter_upwards [(h r).isOpen_compl.mem_nhds (not_le.2 hrf)] with z hz
    exact hyr.trans (not_le.1 hz)

end Semicontinuity

/-! ### The lower semicontinuous hull and the closure of a convex function -/

section Defs

variable {E : Type*} [TopologicalSpace E] {f g : E → EReal}

/-- The **lower semicontinuous hull** of $f : E \to [-\infty, +\infty]$ is the function
$\operatorname{lsc} f$ with $$(\operatorname{lsc} f)(x) = \inf \{\mu \in \mathbb{R} \mid (x,
\mu) \in \operatorname{cl}(\operatorname{epi} f)\},$$ whose epigraph is the closure of the
epigraph of $f$. The infimum of the empty set is $+\infty$.

It is the greatest lower semicontinuous minorant of $f$ (`ConvexAnalysis.isGreatest_lscHull`).
The definition is `ConvexAnalysis.ofEpi` applied to the closure of `ConvexAnalysis.epi f`. -/
noncomputable def lscHull (f : E → EReal) : E → EReal := ofEpi (closure (epi f))

/-- The **upper semicontinuous hull** of $g : E \to [-\infty, +\infty]$ is the function
$x \mapsto -(\operatorname{lsc}(-g))(x)$, the least upper semicontinuous majorant of $g$. It is
the counterpart of `ConvexAnalysis.lscHull` under negation (`ConvexAnalysis.uscHull_apply`). -/
noncomputable def uscHull (g : E → EReal) : E → EReal := fun x => -(lscHull (fun z => -(g z)) x)

open Classical in
/-- The **closure** $\operatorname{cl} f$ of $f : E \to [-\infty, +\infty]$: if
$(\operatorname{lsc} f)(x) = -\infty$ for some $x$, then $\operatorname{cl} f$ is the constant
function $-\infty$; otherwise $\operatorname{cl} f = \operatorname{lsc} f$.

[rockafellar1970convex] decides between the two cases by whether $f$ itself takes the value
$-\infty$. This is equivalent for convex $f$ on $\mathbb{R}^n$ but not in general; the module
doc comment explains the choice. -/
noncomputable def convexCl (f : E → EReal) : E → EReal :=
  if ∃ x, lscHull f x = ⊥ then (fun _ => ⊥) else lscHull f

/-- A function $f$ is **closed** if it equals its closure: $\operatorname{cl} f = f$. -/
def ClosedConvex (f : E → EReal) : Prop := convexCl f = f

/-- The **concave closure** of $g : E \to [-\infty, +\infty]$ is the function
$x \mapsto -(\operatorname{cl}(-g))(x)$, the counterpart of `ConvexAnalysis.convexCl` under
negation. [rockafellar1970convex] also writes $\operatorname{cl} g$ for it; here it has a name
of its own. -/
noncomputable def concaveCl (g : E → EReal) : E → EReal := fun x => -(convexCl (fun z => -(g z)) x)

/-- A function $g$ is **concave-closed** if it equals its concave closure. -/
def ClosedConcave (g : E → EReal) : Prop := concaveCl g = g

/-! ### Negation exchanges the convex and the concave operations -/

/-- The upper semicontinuous hull of $g$ at $x$ is $-(\operatorname{lsc}(-g))(x)$. -/
theorem uscHull_apply (g : E → EReal) (x : E) :
    uscHull g x = -(lscHull (fun z => -(g z)) x) := rfl

/-- The negative of the upper semicontinuous hull of $g$ at $x$ is $(\operatorname{lsc}(-g))(x)$. -/
@[simp] theorem neg_uscHull (g : E → EReal) (x : E) :
    -(uscHull g x) = lscHull (fun z => -(g z)) x := neg_neg _

/-- The concave closure of $g$ at $x$ is $-(\operatorname{cl}(-g))(x)$. -/
theorem concaveCl_apply (g : E → EReal) (x : E) :
    concaveCl g x = -(convexCl (fun z => -(g z)) x) := rfl

/-- The negative of the concave closure of $g$ at $x$ is $(\operatorname{cl}(-g))(x)$. -/
@[simp] theorem neg_concaveCl (g : E → EReal) (x : E) :
    -(concaveCl g x) = convexCl (fun z => -(g z)) x := neg_neg _

/-- The concave closure of $-f$ at $x$ is $-(\operatorname{cl} f)(x)$. -/
theorem concaveCl_neg (f : E → EReal)
    (x : E) : concaveCl (fun z => -(f z)) x = -(convexCl f x) := by
  rw [concaveCl_apply]
  simp only [neg_neg]

/-- A function $g$ is concave-closed if and only if $-g$ is closed. -/
theorem closedConcave_iff_closedConvex_neg : ClosedConcave g ↔ ClosedConvex (fun z => -(g z)) := by
  constructor
  · intro h
    funext x
    rw [← neg_concaveCl g x, h]
  · intro h
    funext x
    rw [concaveCl_apply, congrFun h x, neg_neg]

/-! ### Basic properties of the hulls -/

/-- If $(\operatorname{lsc} f)(x) \neq -\infty$ for all $x$, then
$\operatorname{cl} f = \operatorname{lsc} f$. -/
theorem convexCl_of_forall_ne_bot (h : ∀ x, lscHull f x ≠ ⊥) : convexCl f = lscHull f := by
  have hc : ¬ ∃ x, lscHull f x = ⊥ := by push Not; exact h
  simp [convexCl, hc]

/-- If $(\operatorname{lsc} f)(x) = -\infty$ for some $x$, then $\operatorname{cl} f$ is the
constant function $-\infty$. -/
theorem convexCl_of_exists_eq_bot (h : ∃ x, lscHull f x = ⊥) : convexCl f = fun _ => ⊥ := by
  simp [convexCl, h]

/-- If the upper semicontinuous hull of $g$ never takes the value $+\infty$, then the concave
closure of $g$ is the upper semicontinuous hull of $g$. -/
theorem concaveCl_of_forall_ne_top (h : ∀ x, uscHull g x ≠ ⊤) : concaveCl g = uscHull g := by
  have h' : ∀ x, lscHull (fun z => -(g z)) x ≠ ⊥ := fun x hx =>
    h x (by rw [uscHull_apply, hx, EReal.neg_bot])
  funext x
  rw [concaveCl_apply, convexCl_of_forall_ne_bot h', uscHull_apply]

/-- If the upper semicontinuous hull of $g$ takes the value $+\infty$ at some point, then the
concave closure of $g$ is the constant function $+\infty$. -/
theorem concaveCl_of_exists_eq_top (h : ∃ x, uscHull g x = ⊤) : concaveCl g = fun _ => ⊤ := by
  obtain ⟨x₀, hx₀⟩ := h
  have h' : ∃ x, lscHull (fun z => -(g z)) x = ⊥ := ⟨x₀, by rw [← neg_uscHull, hx₀, EReal.neg_top]⟩
  funext x
  rw [concaveCl_apply, convexCl_of_exists_eq_bot h', EReal.neg_bot]

/-- The lower semicontinuous hull is a minorant: $\operatorname{lsc} f \le f$. -/
theorem lscHull_le (f : E → EReal) : lscHull f ≤ f := by
  have h := ofEpi_mono (subset_closure (s := epi f))
  rwa [ofEpi_epi] at h

/-- The lower semicontinuous hull is monotone: if $f \le g$, then
$\operatorname{lsc} f \le \operatorname{lsc} g$. -/
theorem lscHull_mono (h : f ≤ g) : lscHull f ≤ lscHull g :=
  ofEpi_mono (closure_mono (epi_anti h))

/-- **The universal property, easy half.** If $g$ is lower semicontinuous and $g \le f$, then
$g \le \operatorname{lsc} f$, because the epigraph of $g$ is a closed set that contains
$\operatorname{epi} f$. -/
theorem le_lscHull_of_le (hg : LowerSemicontinuous g) (hgf : g ≤ f) : g ≤ lscHull f :=
  subset_epi_iff_le_ofEpi.1
    (closure_minimal (epi_anti hgf) (lowerSemicontinuous_iff_isClosed_epi.1 hg))

/-- If $g$ is lower semicontinuous, then $g \le \operatorname{lsc} f$ if and only if $g \le f$. -/
theorem le_lscHull_iff (hg : LowerSemicontinuous g) : g ≤ lscHull f ↔ g ≤ f :=
  ⟨fun h => h.trans (lscHull_le f), le_lscHull_of_le hg⟩

/-- The closure is below the lower semicontinuous hull:
$\operatorname{cl} f \le \operatorname{lsc} f$. The two differ only in the exceptional case. -/
theorem convexCl_le_lscHull (f : E → EReal) : convexCl f ≤ lscHull f := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [convexCl_of_exists_eq_bot h]
    exact fun _ => bot_le
  · rw [convexCl_of_forall_ne_bot (by push Not at h; exact h)]

/-- The closure is a minorant: $\operatorname{cl} f \le f$. -/
theorem convexCl_le (f : E → EReal) : convexCl f ≤ f := (convexCl_le_lscHull f).trans (lscHull_le f)

/-- The concave closure is a majorant: $g$ is at most its concave closure. -/
theorem le_concaveCl (g : E → EReal) : g ≤ concaveCl g := by
  intro x
  rw [← EReal.neg_le_neg_iff, neg_concaveCl]
  exact convexCl_le _ x

/-- If $f(x_0) = -\infty$ for some $x_0$, then $\operatorname{cl} f$ is the constant function
$-\infty$. -/
theorem convexCl_eq_bot_of_eq_bot {x₀ : E} (h : f x₀ = ⊥) : convexCl f = fun _ => (⊥ : EReal) := by
  refine convexCl_of_exists_eq_bot ⟨x₀, le_bot_iff.1 ?_⟩
  calc lscHull f x₀ ≤ f x₀ := lscHull_le f x₀
    _ = ⊥ := h

/-- If $g(x_0) = +\infty$ for some $x_0$, then the concave closure of $g$ is the constant function
$+\infty$. -/
theorem concaveCl_eq_top_of_eq_top {x₀ : E} (h : g x₀ = ⊤) :
    concaveCl g = fun _ => (⊤ : EReal) := by
  funext x
  rw [concaveCl_apply, convexCl_eq_bot_of_eq_bot (x₀ := x₀) (by simp [h]), EReal.neg_bot]

/-- The closure is monotone: if $f \le g$, then $\operatorname{cl} f \le \operatorname{cl} g$. -/
theorem convexCl_mono (h : f ≤ g) : convexCl f ≤ convexCl g := by
  by_cases hg : ∃ x, lscHull g x = ⊥
  · obtain ⟨x, hx⟩ := hg
    have hf : ∃ z, lscHull f z = ⊥ := ⟨x, le_bot_iff.1 (by rw [← hx]; exact lscHull_mono h x)⟩
    rw [convexCl_of_exists_eq_bot hf, convexCl_of_exists_eq_bot ⟨x, hx⟩]
  · have hg' : ∀ x, lscHull g x ≠ ⊥ := by push Not at hg; exact hg
    rw [convexCl_of_forall_ne_bot (f := g) hg']
    exact (convexCl_le_lscHull f).trans (lscHull_mono h)

/-- The concave closure is monotone: if $f \le g$, then the concave closure of $f$ is at most the
concave closure of $g$. -/
theorem concaveCl_mono (h : f ≤ g) : concaveCl f ≤ concaveCl g := by
  intro x
  rw [concaveCl_apply, concaveCl_apply, EReal.neg_le_neg_iff]
  exact convexCl_mono (fun z => EReal.neg_le_neg_iff.2 (h z)) x

end Defs

/-! ### The universal property of the lower semicontinuous hull -/

section Hull

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {f g : E → EReal}

/-- **The epigraph of the lower semicontinuous hull.** Let $E$ be a commutative topological group.
For every $f : E \to [-\infty, +\infty]$, $$\operatorname{epi}(\operatorname{lsc} f) =
\operatorname{cl}(\operatorname{epi} f).$$

There is no hypothesis on $f$: the closure of an epigraph is again an epigraph. Most results of
this file depend on this one. -/
@[simp] theorem epi_lscHull (f : E → EReal) : epi (lscHull f) = closure (epi f) :=
  epi_ofEpi (IsEpiLike.closure (isEpiLike_epi f))

/-- The lower semicontinuous hull $\operatorname{lsc} f$ is lower semicontinuous. -/
theorem lowerSemicontinuous_lscHull (f : E → EReal) : LowerSemicontinuous (lscHull f) :=
  lowerSemicontinuous_iff_isClosed_epi.2 (by rw [epi_lscHull]; exact isClosed_closure)

/-- **The universal property of the lower semicontinuous hull.** Let $E$ be a commutative
topological group. For every $f : E \to [-\infty, +\infty]$, $\operatorname{lsc} f$ is the
greatest element of the set of lower semicontinuous functions $g$ with $g \le f$. -/
theorem isGreatest_lscHull (f : E → EReal) :
    IsGreatest {g : E → EReal | LowerSemicontinuous g ∧ g ≤ f} (lscHull f) :=
  ⟨⟨lowerSemicontinuous_lscHull f, lscHull_le f⟩, fun _ hg => le_lscHull_of_le hg.1 hg.2⟩

/-- The lower semicontinuous hull is idempotent: $\operatorname{lsc}(\operatorname{lsc} f) =
\operatorname{lsc} f$. -/
theorem lscHull_idem (f : E → EReal) : lscHull (lscHull f) = lscHull f :=
  epi_injective (by rw [epi_lscHull, epi_lscHull, closure_closure])

/-- A function equals its lower semicontinuous hull if and only if it is lower semicontinuous. -/
theorem lscHull_eq_self_iff : lscHull f = f ↔ LowerSemicontinuous f :=
  ⟨fun h => h ▸ lowerSemicontinuous_lscHull f,
    fun h => le_antisymm (lscHull_le f) (le_lscHull_of_le h le_rfl)⟩

omit [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The epigraph of the constant function $-\infty$ is all of $E \times \mathbb{R}$. -/
@[simp] theorem epi_const_bot : epi (fun _ : E => (⊥ : EReal)) = univ := by
  ext p; simp [epi]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The lower semicontinuous hull of the constant function $-\infty$ is the constant function
$-\infty$. -/
@[simp] theorem lscHull_const_bot : lscHull (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ := by
  simp only [lscHull, epi_const_bot, closure_univ, ofEpi_univ]
  rfl

omit [IsTopologicalAddGroup E] in
/-- The closure of the constant function $-\infty$ is the constant function $-\infty$. -/
@[simp] theorem convexCl_const_bot : convexCl (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ :=
  convexCl_of_exists_eq_bot ⟨0, by rw [lscHull_const_bot]⟩

/-- The closure is idempotent: $\operatorname{cl}(\operatorname{cl} f) = \operatorname{cl} f$. -/
theorem convexCl_idem (f : E → EReal) : convexCl (convexCl f) = convexCl f := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [convexCl_of_exists_eq_bot h, convexCl_const_bot]
  · have h' : ∀ x, lscHull f x ≠ ⊥ := by push Not at h; exact h
    have h'' : ∀ x, lscHull (lscHull f) x ≠ ⊥ := by rw [lscHull_idem]; exact h'
    rw [convexCl_of_forall_ne_bot h', convexCl_of_forall_ne_bot h'', lscHull_idem]

/-- The closure $\operatorname{cl} f$ of every function $f$ is closed. -/
theorem closedConvex_convexCl (f : E → EReal) : ClosedConvex (convexCl f) := convexCl_idem f

/-- The concave closure of every function $g$ is concave-closed. -/
theorem closedConcave_concaveCl (g : E → EReal) : ClosedConcave (concaveCl g) := by
  rw [closedConcave_iff_closedConvex_neg]
  simpa only [neg_concaveCl] using closedConvex_convexCl (fun z => -(g z))

/-- The concave closure is idempotent. -/
theorem concaveCl_idem (g : E → EReal) : concaveCl (concaveCl g) = concaveCl g :=
  closedConcave_concaveCl g

/-- **Characterization of closed functions.** Let $E$ be a commutative topological group and let
$f : E \to [-\infty, +\infty]$. Then $f$ is closed if and only if either $f$ is the constant
function $-\infty$, or $f$ is lower semicontinuous and $f(x) \neq -\infty$ for all $x$. -/
theorem closedConvex_iff :
    ClosedConvex f ↔ f = (fun _ => ⊥) ∨ (LowerSemicontinuous f ∧ ∀ x, f x ≠ ⊥) := by
  constructor
  · intro hc
    by_cases h : ∃ x, lscHull f x = ⊥
    · exact Or.inl (by rw [← hc, convexCl_of_exists_eq_bot h])
    · have h' : ∀ x, lscHull f x ≠ ⊥ := by push Not at h; exact h
      have hs : lscHull f = f := by rw [← convexCl_of_forall_ne_bot h']; exact hc
      exact Or.inr ⟨lscHull_eq_self_iff.1 hs, fun x => by rw [← hs]; exact h' x⟩
  · rintro (rfl | ⟨hlsc, hne⟩)
    · exact convexCl_const_bot
    · have hs : lscHull f = f := lscHull_eq_self_iff.2 hlsc
      have h' : ∀ x, lscHull f x ≠ ⊥ := fun x => by rw [hs]; exact hne x
      exact (convexCl_of_forall_ne_bot h').trans hs

/-- If $f(x) \neq -\infty$ for all $x$, in particular if $f$ is proper, then $f$ is closed if and
only if $f$ is lower semicontinuous. -/
theorem closedConvex_iff_lowerSemicontinuous (h : ∀ x, f x ≠ ⊥) :
    ClosedConvex f ↔ LowerSemicontinuous f := by
  rw [closedConvex_iff]
  refine ⟨?_, fun hl => Or.inr ⟨hl, h⟩⟩
  rintro (rfl | ⟨hl, -⟩)
  · exact absurd rfl (h 0)
  · exact hl

/-- A closed function is lower semicontinuous. -/
theorem ClosedConvex.lowerSemicontinuous (hc : ClosedConvex f) : LowerSemicontinuous f := by
  rcases closedConvex_iff.1 hc with rfl | ⟨hl, -⟩
  · exact lowerSemicontinuous_const
  · exact hl

/-- **The only closed improper functions are the constant functions $+\infty$ and $-\infty$.** If
$f$ is closed and not proper, then $f \equiv -\infty$ or $f \equiv +\infty$. Convexity is not
needed. -/
theorem eq_const_of_closedConvex_of_not_properConvex (hc : ClosedConvex f) (hp : ¬ ProperConvex f) :
    f = (fun _ => ⊥) ∨ f = fun _ => ⊤ := by
  rcases closedConvex_iff.1 hc with h | ⟨-, hne⟩
  · exact Or.inl h
  · exact Or.inr (funext fun x => top_le_iff.1 (not_lt.1 fun hx => hp ⟨⟨x, hx⟩, hne⟩))

/-- The constant function $+\infty$ is closed. -/
theorem closedConvex_const_top : ClosedConvex (fun _ : E => (⊤ : EReal)) :=
  closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_const, fun _ => by simp⟩)

omit [IsTopologicalAddGroup E] in
/-- The constant function $-\infty$ is closed. -/
theorem closedConvex_const_bot : ClosedConvex (fun _ : E => (⊥ : EReal)) := convexCl_const_bot

/-- The closure of the constant function $+\infty$ is the constant function $+\infty$. -/
@[simp] theorem convexCl_const_top : convexCl (fun _ : E => (⊤ : EReal)) = fun _ => ⊤ :=
  closedConvex_const_top

/-- The concave closure of the constant function $-\infty$ is the constant function $-\infty$. -/
@[simp] theorem concaveCl_const_bot : concaveCl (fun _ : E => (⊥ : EReal)) = fun _ => ⊥ := by
  funext x
  simp [concaveCl_apply]

/-! ### Infima, effective domains and level sets -/

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **A function and its lower semicontinuous hull have the same infimum**:
$\inf_x (\operatorname{lsc} f)(x) = \inf_x f(x)$. A constant function is lower semicontinuous,
so $\inf_x f(x)$ is a minorant of $\operatorname{lsc} f$. -/
theorem iInf_lscHull_eq_iInf (f : E → EReal) : ⨅ x, lscHull f x = ⨅ x, f x :=
  le_antisymm (iInf_mono fun x => lscHull_le f x)
    (le_iInf fun x =>
      le_lscHull_of_le (g := fun _ => ⨅ y, f y) lowerSemicontinuous_const (fun y => iInf_le f y) x)

omit [IsTopologicalAddGroup E] in
/-- **A function and its closure have the same infimum.** Let $E$ be a topological space with a
commutative group structure and let $f : E \to [-\infty, +\infty]$. Then $$\inf_{x \in E}
(\operatorname{cl} f)(x) = \inf_{x \in E} f(x).$$

Convexity of $f$ is not needed. -/
theorem iInf_convexCl_eq_iInf (f : E → EReal) : ⨅ x, convexCl f x = ⨅ x, f x := by
  have : Nonempty E := ⟨0⟩
  by_cases h : ∃ x, lscHull f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := h
    have hb : ⨅ x, f x = ⊥ := by
      rw [← iInf_lscHull_eq_iInf]
      exact le_bot_iff.1 (by rw [← hx₀]; exact iInf_le (fun x => lscHull f x) x₀)
    rw [hb, convexCl_of_exists_eq_bot ⟨x₀, hx₀⟩]
    simp
  · rw [convexCl_of_forall_ne_bot (by push Not at h; exact h)]
    exact iInf_lscHull_eq_iInf f

omit [IsTopologicalAddGroup E] in
/-- **A function and its concave closure have the same supremum.** Let $E$ be a topological space
with a commutative group structure and let $g : E \to [-\infty, +\infty]$. Then the supremum of
the concave closure of $g$ equals $\sup_{x \in E} g(x)$.

This is the counterpart of `ConvexAnalysis.iInf_convexCl_eq_iInf` under negation. Concavity of
$g$ is not needed. -/
theorem iSup_concaveCl_eq_iSup (g : E → EReal) : (⨆ x, concaveCl g x) = ⨆ x, g x := by
  have h : (⨆ x, concaveCl g x) = -⨅ x, convexCl (fun z => -(g z)) x := by
    rw [EReal.neg_iInf]
    exact iSup_congr fun x => rfl
  rw [h, iInf_convexCl_eq_iInf, EReal.neg_iInf]
  exact iSup_congr fun x => neg_neg _

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The effective domain of $f$ is contained in the effective domain of its lower semicontinuous
hull: $\operatorname{dom} f \subseteq \operatorname{dom}(\operatorname{lsc} f)$, where
$\operatorname{dom} f = \{x \mid f(x) < +\infty\}$. -/
theorem convexDom_subset_convexDom_lscHull (f : E → EReal) : convexDom f ⊆ convexDom (lscHull f) :=
  fun _ hx => lt_of_le_of_lt (lscHull_le f _) hx

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The effective domain of the lower semicontinuous hull is contained in the closure of the
effective domain: $\operatorname{dom}(\operatorname{lsc} f) \subseteq
\operatorname{cl}(\operatorname{dom} f)$, with no hypothesis on $f$. Together with
`ConvexAnalysis.convexDom_subset_convexDom_lscHull`, this gives $\operatorname{dom} f \subseteq
\operatorname{dom}(\operatorname{lsc} f) \subseteq \operatorname{cl}(\operatorname{dom} f)$.

The proof projects `ConvexAnalysis.convexDom_eq_fst_image_epi` along the continuous map
`Prod.fst`. -/
theorem convexDom_lscHull_subset_closure_convexDom
    (f : E → EReal) : convexDom (lscHull f) ⊆ closure (convexDom f) := by
  intro x hx
  obtain ⟨μ, hμ, -⟩ := ofEpi_lt_iff.1 (hx : lscHull f x < ⊤)
  have h2 := image_closure_subset_closure_image (f := (Prod.fst : E × ℝ → E)) continuous_fst
    (mem_image_of_mem _ hμ)
  rwa [← convexDom_eq_fst_image_epi] at h2

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **The closure of an improper function is improper.** If $f$ is not proper, then
$\operatorname{cl} f$ is not proper. Neither convexity nor finite dimension is used. The
converse direction, that properness is preserved, needs both; it is
`ConvexAnalysis.ConvexFn.properConvex_convexCl` in `Numlib.Analysis.Convex.RelativeInterior`. -/
theorem not_properConvex_convexCl (himp : ¬ ProperConvex f) : ¬ ProperConvex (convexCl f) := by
  intro hpr
  refine himp ⟨?_, fun z hz => hpr.ne_bot z (le_bot_iff.1 (by rw [← hz]; exact convexCl_le f z))⟩
  obtain ⟨y, hy⟩ := hpr.convexDom_nonempty
  have hb : ∀ x, lscHull f x ≠ ⊥ := fun x hx =>
    hpr.ne_bot x (le_bot_iff.1 (by rw [← hx]; exact convexCl_le_lscHull f x))
  rw [convexCl_of_forall_ne_bot hb] at hy
  have hyd : y ∈ closure (convexDom f) := convexDom_lscHull_subset_closure_convexDom f hy
  rcases Set.eq_empty_or_nonempty (convexDom f) with h | h
  · rw [h, closure_empty] at hyd
    exact absurd hyd (Set.notMem_empty y)
  · exact h

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- If $(x, \mu) \in \operatorname{cl}(\operatorname{epi} f)$ and $\mu < \nu$, then
$x \in \operatorname{cl}\{z \mid f(z) \le \nu\}$. This is the pointwise content of the
description in [rockafellar1970convex] of $(\operatorname{cl} f)(x)$ as the infimum of the $\mu$
with $x \in \operatorname{cl}\{z \mid f(z) \le \mu\}$. -/
theorem mem_closure_le_of_mem_closure_epi {x : E} {μ ν : ℝ}
    (h : ((x, μ) : E × ℝ) ∈ closure (epi f)) (hμν : μ < ν) :
    x ∈ closure {z | f z ≤ (ν : EReal)} := by
  rw [mem_closure_iff] at h ⊢
  intro U hU hxU
  obtain ⟨p, hp1, hp2⟩ := h (U ×ˢ Iio ν) (hU.prod isOpen_Iio) ⟨hxU, hμν⟩
  have hp2' : f p.1 ≤ (p.2 : EReal) := hp2
  have hp1' : p.2 < ν := hp1.2
  exact ⟨p.1, hp1.1, hp2'.trans (by exact_mod_cast hp1'.le)⟩

/-- For every $\alpha \in \mathbb{R}$, the closure of the sublevel set $\{x \mid f(x) \le \alpha\}$
is contained in $\{x \mid (\operatorname{lsc} f)(x) \le \alpha\}$. -/
theorem closure_le_subset_lscHull_le (f : E → EReal) (α : ℝ) :
    closure {x | f x ≤ (α : EReal)} ⊆ {x | lscHull f x ≤ (α : EReal)} := by
  intro x hx
  have hsub : (fun z : E => (z, α)) '' {z | f z ≤ (α : EReal)} ⊆ epi f := by
    rintro _ ⟨z, hz, rfl⟩; exact hz
  have h1 := image_closure_subset_closure_image
    (f := fun z : E => (z, α)) (continuous_id.prodMk continuous_const) (mem_image_of_mem _ hx)
  have h2 := closure_mono hsub h1
  rw [← epi_lscHull] at h2
  exact h2

/-- **The level sets of the lower semicontinuous hull.** Let $E$ be a commutative topological group
and let $f : E \to [-\infty, +\infty]$. For every $\alpha \in \mathbb{R}$, $$\{x \mid
(\operatorname{lsc} f)(x) \le \alpha\} = \bigcap_{\mu > \alpha} \operatorname{cl}\{x \mid f(x)
\le \mu\}.$$

[rockafellar1970convex] states this for $\operatorname{cl} f$. It is stated here for the hull,
which is where the content is. The part of the classical description that uses relative
interiors needs finite dimension and is not proved here. -/
theorem lscHull_le_setOf (f : E → EReal) (α : ℝ) :
    {x | lscHull f x ≤ (α : EReal)} = ⋂ μ ∈ Ioi α, closure {x | f x ≤ (μ : EReal)} := by
  refine subset_antisymm (fun x hx => mem_iInter₂.2 fun μ hμ => ?_) fun x hx => ?_
  · have hlt : lscHull f x < (μ : EReal) :=
      lt_of_le_of_lt hx (by exact_mod_cast (hμ : α < μ))
    obtain ⟨ν, hν, hνμ⟩ := ofEpi_lt_iff.1 hlt
    exact mem_closure_le_of_mem_closure_epi hν (by exact_mod_cast hνμ)
  · refine EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_
    replace hq := EReal.coe_lt_coe_iff.1 hq
    obtain ⟨μ, hαμ, hμq⟩ := exists_between hq
    exact lt_of_le_of_lt
      (closure_le_subset_lscHull_le f μ (mem_iInter₂.1 hx μ hαμ)) (by exact_mod_cast hμq)


/-!
### The lower semicontinuous hull and the closure as closure operators

Both operations are monotone, idempotent and decreasing, so each is a closure operator on the order
dual of the functions $E \to [-\infty, +\infty]$. This makes the `ClosureOperator` interface of
Mathlib available, and identifies `LowerSemicontinuous` and `ConvexAnalysis.ClosedConvex` as the two
predicates of closed elements. The hypotheses of the constructor are the universal property.
-/

open OrderDual in
/-- The lower semicontinuous hull as a closure operator on the order dual of the functions
$E \to [-\infty, +\infty]$. Its closed elements are the lower semicontinuous functions. -/
noncomputable def lscHullClosure : ClosureOperator (E → EReal)ᵒᵈ :=
  ClosureOperator.ofPred (fun g => toDual (lscHull (ofDual g)))
    (fun g => LowerSemicontinuous (ofDual g))
    (fun g => lscHull_le (ofDual g))
    (fun g => lowerSemicontinuous_lscHull (ofDual g))
    (fun _ _ hgh hh => le_lscHull_of_le hh hgh)

/-- The closure operator `ConvexAnalysis.lscHullClosure` sends $f$ to $\operatorname{lsc} f$. -/
@[simp] theorem lscHullClosure_apply (f : E → EReal) :
    lscHullClosure (OrderDual.toDual f) = OrderDual.toDual (lscHull f) := rfl

/-- A function is lower semicontinuous if and only if it is a closed element of
`ConvexAnalysis.lscHullClosure`. -/
theorem lowerSemicontinuous_iff_lscHullClosure_isClosed :
    LowerSemicontinuous f ↔ lscHullClosure.IsClosed (OrderDual.toDual f) := Iff.rfl

open OrderDual in
/-- The closure of functions as a closure operator on the order dual of the functions
$E \to [-\infty, +\infty]$. Its closed elements are exactly the closed functions, so
`ConvexAnalysis.ClosedConvex` is the predicate of closed elements of a closure operator. -/
noncomputable def convexClClosure : ClosureOperator (E → EReal)ᵒᵈ :=
  ClosureOperator.ofPred (fun g => toDual (convexCl (ofDual g)))
    (fun g => ClosedConvex (ofDual g))
    (fun g => convexCl_le (ofDual g))
    (fun g => convexCl_idem (ofDual g))
    (fun _ _ hgh hh => hh.symm.trans_le (convexCl_mono hgh))

/-- The closure operator `ConvexAnalysis.convexClClosure` sends $f$ to $\operatorname{cl} f$. -/
@[simp] theorem convexClClosure_apply (f : E → EReal) :
    convexClClosure (OrderDual.toDual f) = OrderDual.toDual (convexCl f) := rfl

/-- A function is closed if and only if it is a closed element of `ConvexAnalysis.convexClClosure`.
-/
theorem closedConvex_iff_convexClClosure_isClosed :
    ClosedConvex f ↔ convexClClosure.IsClosed (OrderDual.toDual f) := Iff.rfl

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **The universal property of the closure.** If $g$ is closed and $g \le f$, then
$g \le \operatorname{cl} f$. Thus $\operatorname{cl} f$ is the greatest closed minorant of $f$.
This is the minimality property of `ConvexAnalysis.convexClClosure`, without the order dual. -/
theorem le_convexCl_of_le (hg : ClosedConvex g) (hgf : g ≤ f) : g ≤ convexCl f :=
  hg.symm.trans_le (convexCl_mono hgf)


/-! ### Indicator functions -/

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The lower semicontinuous hull of the indicator function $\delta(\cdot \mid s)$, which is $0$ on
$s$ and $+\infty$ off $s$, is the indicator function $\delta(\cdot \mid \operatorname{cl} s)$ of
the closure. -/
@[simp] theorem lscHull_indicatorFn (s : Set E) :
    lscHull (indicatorFn s) = indicatorFn (closure s) := by
  have h : closure (epi (indicatorFn s)) = epi (indicatorFn (closure s)) := by
    rw [epi_indicatorFn, epi_indicatorFn, closure_prod_eq, isClosed_Ici.closure_eq]
  rw [lscHull, h, ofEpi_epi]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- **The closure of an indicator function is the indicator function of the closure**:
$\operatorname{cl} \delta(\cdot \mid s) = \delta(\cdot \mid \operatorname{cl} s)$. -/
@[simp] theorem convexCl_indicatorFn (s : Set E) :
    convexCl (indicatorFn s) = indicatorFn (closure s) := by
  rw [convexCl_of_forall_ne_bot fun x => by
    rw [lscHull_indicatorFn]; exact indicatorFn_ne_bot _ _, lscHull_indicatorFn]

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- The indicator function of a closed set is closed. -/
theorem closedConvex_indicatorFn {s : Set E} (hs : IsClosed s) : ClosedConvex (indicatorFn s) := by
  change convexCl (indicatorFn s) = indicatorFn s
  rw [convexCl_indicatorFn, hs.closure_eq]

/-! ### Finite continuous functions on closed sets -/

omit [AddCommGroup E] [IsTopologicalAddGroup E] in
/-- Let $s \subseteq E$ be closed and let $g : E \to \mathbb{R}$ be continuous on $s$. Then the
function equal to $g$ on $s$ and to $+\infty$ off $s$ has a closed epigraph. -/
theorem isClosed_epi_convexRestrict_coe {s : Set E} {g : E → ℝ} (hs : IsClosed s)
    (hg : ContinuousOn g s) : IsClosed (epi (convexRestrict s fun x => (g x : EReal))) := by
  rw [epi_convexRestrict_coe]
  have hcont : ContinuousOn (fun p : E × ℝ => g p.1 - p.2) (s ×ˢ (Set.univ : Set ℝ)) :=
    (hg.comp continuousOn_fst Set.mapsTo_fst_prod).sub continuousOn_snd
  have h := hcont.preimage_isClosed_of_isClosed (hs.prod isClosed_univ)
    (isClosed_Iic (a := (0 : ℝ)))
  convert h using 1
  ext p
  simp [Set.mem_prod]

/-- Let $s \subseteq E$ be closed and let $g : E \to \mathbb{R}$ be continuous on $s$. Then the
function equal to $g$ on $s$ and to $+\infty$ off $s$ is closed. -/
theorem closedConvex_convexRestrict_coe {s : Set E} {g : E → ℝ} (hs : IsClosed s)
    (hg : ContinuousOn g s) : ClosedConvex (convexRestrict s fun x => (g x : EReal)) := by
  have hne : ∀ x, (convexRestrict s fun x => (g x : EReal)) x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  exact (closedConvex_iff_lowerSemicontinuous hne).2
    (lowerSemicontinuous_iff_isClosed_epi.2 (isClosed_epi_convexRestrict_coe hs hg))

/-- Let $s \subseteq E$ be closed and let $g : E \to \mathbb{R}$ be continuous on $s$. Then the
function equal to $g$ on $s$ and to $-\infty$ off $s$ is concave-closed. -/
theorem closedConcave_concaveRestrict_coe {s : Set E} {g : E → ℝ} (hs : IsClosed s)
    (hg : ContinuousOn g s) : ClosedConcave (concaveRestrict s fun x => (g x : EReal)) := by
  rw [closedConcave_iff_closedConvex_neg, neg_concaveRestrict]
  simp only [← EReal.coe_neg]
  exact closedConvex_convexRestrict_coe hs hg.neg

end Hull

/-!
### Approaching the endpoint of a segment

The three lemmas below are facts about the limit $a \to 1$ from below (the filter `𝓝[<] (1 : ℝ)`),
which the dichotomy for improper functions and the limit formulas for the closure both use.
-/

section Segment

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Let $E$ be a real topological vector space and let $x, y \in E$. Then $(1 - a) x + a y \to y$ as
$a \to 1$ from below. -/
theorem tendsto_segment (x y : E) :
    Tendsto (fun a : ℝ => (1 - a) • x + a • y) (𝓝[<] (1 : ℝ)) (𝓝 y) := by
  have hcont : Continuous fun a : ℝ => (1 - a) • x + a • y :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have h : Tendsto (fun a : ℝ => (1 - a) • x + a • y) (𝓝[<] (1 : ℝ))
      (𝓝 ((1 - (1 : ℝ)) • x + (1 : ℝ) • y)) := (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  simpa using h

/-- For all $a < 1$ close enough to $1$, $0 \le a < 1$. -/
theorem eventually_mem_Ico_nhdsLT_one : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ a ∧ a < 1 := by
  filter_upwards [(eventually_ge_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with a ha ha1 using ⟨ha, ha1⟩

/-- For $\alpha, \beta \in \mathbb{R}$, $(1 - a) \alpha + a \beta \to \beta$ as $a \to 1$ from
below. -/
theorem tendsto_affine_nhdsLT_one (α β : ℝ) :
    Tendsto (fun a : ℝ => (1 - a) * α + a * β) (𝓝[<] (1 : ℝ)) (𝓝 β) :=
  tendsto_segment α β

end Segment

/-! ### Convexity of the hull and of the closure -/

section Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f g : E → EReal}

/-- The lower semicontinuous hull of a convex function is convex. The closure of a convex set is
convex (`Convex.closure`), and `ConvexAnalysis.convexFn_ofEpi` turns this back into a statement
about functions. -/
theorem convexFn_lscHull (hf : ConvexFn f) : ConvexFn (lscHull f) :=
  convexFn_ofEpi hf.convex_epi.closure

/-- **The closure of a convex function is convex**, in both cases of the definition. -/
theorem convexFn_convexCl (hf : ConvexFn f) : ConvexFn (convexCl f) := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [convexCl_of_exists_eq_bot h]
    exact ⟨by rw [epi_const_bot]; exact convex_univ⟩
  · rw [convexCl_of_forall_ne_bot (by push Not at h; exact h)]
    exact convexFn_lscHull hf

/-- The concave closure of a concave function is concave. -/
theorem concaveFn_concaveCl (hg : ConcaveFn g) : ConcaveFn (concaveCl g) := by
  rw [concaveFn_iff_convexFn_neg]
  simpa only [neg_concaveCl] using convexFn_convexCl hg.convexFn_neg

/-!
### The dichotomy for improper convex functions

The statement "an improper convex function is $-\infty$ on
$\operatorname{ri}(\operatorname{dom} f)$" needs finite dimension. Its consequence for lower
semicontinuous functions below does not, and it holds in every real topological vector space. It is
also the sharp form: the stronger statement "a lower semicontinuous convex function that takes the
value $-\infty$ somewhere is identically $-\infty$" is false. See
`ConvexAnalysis.eq_bot_of_lsc_of_eq_bot` and the example at the end of this module.
-/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The algebraic core of the dichotomy, in any real vector space. Let $f$ be convex with
$f(x_0) = -\infty$, and let $y \in \operatorname{dom} f$. Then $f((1 - a) x_0 + a y) = -\infty$
for all $0 \le a < 1$, so $f$ is $-\infty$ on the half-open segment $[x_0, y)$.

The hypothesis $y \in \operatorname{dom} f$ is necessary: for the function that is $-\infty$ at
$x_0$ and $+\infty$ elsewhere (`ConvexAnalysis.convexRestrict {x₀} (fun _ => ⊥)`), the segment
meets $\operatorname{dom} f$ only at $x_0$. -/
theorem ConvexFn.eq_bot_of_lt_one (hf : ConvexFn f) {x₀ y : E} (h₀ : f x₀ = ⊥)
    (hy : y ∈ convexDom f)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) : f ((1 - a) • x₀ + a • y) = ⊥ := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simpa using h₀
  · obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 (hy : f y < ⊤)
    have hb : (0 : ℝ) < 1 - a := by linarith
    refine le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun r _ => ?_)
    have hb' : (1 : ℝ) - a ≠ 0 := ne_of_gt hb
    have harith : (1 - a) * ((r - a * β) / (1 - a)) + a * β = r := by
      field_simp
      ring
    have hx₀ : f x₀ < (((r - a * β) / (1 - a) : ℝ) : EReal) := by rw [h₀]; simp
    have hkey := (convexFn_iff_forall_lt f).1 hf x₀ y (1 - a) a hb ha' (by ring) _ β hx₀ hβ
    rw [harith] at hkey
    exact hkey.le

/-- **A lower semicontinuous convex function that takes the value $-\infty$ somewhere takes it at
every point of its effective domain.** Let $f$ be convex and lower semicontinuous with
$f(x_0) = -\infty$, and let $y \in \operatorname{dom} f$. Then $f(y) = -\infty$.

Only lower semicontinuity at $y$ is used, through the limit $a \to 1$ from below along the
segment from $x_0$ to $y$. -/
theorem ConvexFn.eq_bot_of_mem_convexDom (hf : ConvexFn f) (hl : LowerSemicontinuous f) {x₀ : E}
    (h₀ : f x₀ = ⊥) {y : E} (hy : y ∈ convexDom f) : f y = ⊥ := by
  by_contra hne
  have h1 : ∀ᶠ a in 𝓝[<] (1 : ℝ), (⊥ : EReal) < f ((1 - a) • x₀ + a • y) :=
    (tendsto_segment x₀ y).eventually (hl y ⊥ (bot_lt_iff_ne_bot.2 hne))
  have hbot : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), f ((1 - a) • x₀ + a • y) = ⊥ := by
    filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
    exact hf.eq_bot_of_lt_one h₀ hy ha.1 ha.2
  obtain ⟨a, hlt, heq⟩ := (h1.and hbot).exists
  rw [heq] at hlt
  exact absurd hlt (lt_irrefl ⊥)

/-- **A lower semicontinuous improper convex function has no finite values.** Let $E$ be a real
topological vector space, and let $f : E \to [-\infty, +\infty]$ be convex and lower
semicontinuous with $f(x_0) = -\infty$ for some $x_0$. Then for every $x \in E$,
$f(x) = -\infty$ or $f(x) = +\infty$.

Thus $f$ is $-\infty$ on its effective domain and $+\infty$ off it. -/
theorem ConvexFn.eq_bot_or_eq_top (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (h : ∃ x₀, f x₀ = ⊥) (x : E) : f x = ⊥ ∨ f x = ⊤ := by
  obtain ⟨x₀, h₀⟩ := h
  rcases eq_top_or_lt_top (f x) with hx | hx
  · exact Or.inr hx
  · exact Or.inl (hf.eq_bot_of_mem_convexDom hl h₀ hx)

/-- Let $f$ be convex and lower semicontinuous with $f(x_0) = -\infty$ for some $x_0$. Then
$\operatorname{dom} f = \{x \mid f(x) = -\infty\}$, so this set is closed. -/
theorem ConvexFn.convexDom_eq_setOf_eq_bot (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (h : ∃ x₀, f x₀ = ⊥) : convexDom f = {x | f x = ⊥} := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨x₀, h₀⟩ := h
    exact hf.eq_bot_of_mem_convexDom hl h₀ hx
  · have hx' : f x = ⊥ := hx
    exact mem_convexDom.2 (lt_of_le_of_lt (le_of_eq hx') bot_lt_top)

/-- **The dichotomy, in its correct form.** Let $f$ be convex and lower semicontinuous with
$f(x) < +\infty$ for all $x$, and let $f(x_0) = -\infty$ for some $x_0$. Then $f$ is the
constant function $-\infty$.

The hypothesis $f < +\infty$ cannot be removed; see the example at the end of this module. The
sharp form without this hypothesis is `ConvexAnalysis.ConvexFn.eq_bot_or_eq_top`. -/
theorem eq_bot_of_lsc_of_eq_bot (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (hdom : ∀ x, f x < ⊤) (h : ∃ x₀, f x₀ = ⊥) : f = fun _ => ⊥ := by
  obtain ⟨x₀, h₀⟩ := h
  exact funext fun x => hf.eq_bot_of_mem_convexDom hl h₀ (hdom x)

end Convex

/-! ### Positively homogeneous functions -/

section PosHomogeneous

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- **The lower semicontinuous hull of a positively homogeneous function is positively
homogeneous.** Let $E$ be a real topological vector space. If $f(a x) = a f(x)$ for all $a > 0$
and $x \in E$, then the same holds for $\operatorname{lsc} f$.

Positive homogeneity says that the epigraph is a cone,
$\operatorname{epi}(\operatorname{lsc} f)$ is the closure of $\operatorname{epi} f$, and the
closure of a cone is a cone. Convexity is not used. -/
theorem posHomogeneous_lscHull (hf : PosHomogeneous f) : PosHomogeneous (lscHull f) := by
  rw [posHomogeneous_iff_isCone_epi] at hf ⊢
  intro a ha
  rw [epi_lscHull]
  exact smul_closure_eq_of_isCone (isCone_iff_smul_eq.2 hf) a ha

/-- **The closure of a positively homogeneous function is positively homogeneous.** Let $E$ be a
real topological vector space. If $f(a x) = a f(x)$ for all $a > 0$ and $x \in E$, then the same
holds for $\operatorname{cl} f$.

In the exceptional case $\operatorname{cl} f$ is the constant $-\infty$, and
$a \cdot (-\infty) = -\infty$ for $a > 0$. For convex $f$ the result also follows when
$\operatorname{cl} f$ is written as a support function; here neither the pairing that this needs
nor convexity is required. -/
theorem posHomogeneous_convexCl (hf : PosHomogeneous f) : PosHomogeneous (convexCl f) := by
  by_cases h : ∃ x, lscHull f x = ⊥
  · rw [convexCl_of_exists_eq_bot h]
    exact fun a ha _ => (EReal.coe_mul_bot_of_pos ha).symm
  · rw [convexCl_of_forall_ne_bot (by push Not at h; exact h)]
    exact posHomogeneous_lscHull hf

end PosHomogeneous

/-! ### Nonnegative scalar multiples -/

section ScalarMultiple

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {f : E → EReal}

omit [IsTopologicalAddGroup E] in
/-- **The map `ConvexAnalysis.scaleSnd c` is continuous.** It sends
$(x, \mu) \in E \times \mathbb{R}$ to $(x, c \mu)$, so it needs only the topology of $E$, and no
continuity of scalar multiplication on $E$. -/
theorem continuous_scaleSnd (c : ℝ) : Continuous (scaleSnd (E := E) c) := by
  have h : (scaleSnd (E := E) c : E × ℝ → E × ℝ) = fun p => (p.1, c * p.2) := rfl
  rw [h]
  exact continuous_fst.prodMk (continuous_const.mul continuous_snd)

/-- **A nonnegative multiple of a closed function is closed**, if the function never takes the value
$-\infty$. Let $c \ge 0$ and let $f$ be closed with $f(x) \neq -\infty$ for all $x$. Then
$x \mapsto c f(x)$ is closed.

Since $f$ is never $-\infty$, closedness of $c f$ is equivalent to lower semicontinuity of
$c f$. For $c > 0$ the epigraph of $c f$ is the preimage of $\operatorname{epi} f$ under the
continuous map $(x, \mu) \mapsto (x, \mu / c)$, and for $c = 0$ the product is the constant $0$. -/
theorem closedConvex_coe_mul {c : ℝ} (hc : 0 ≤ c) (hf : ClosedConvex f) (hb : ∀ x, f x ≠ ⊥) :
    ClosedConvex (fun x => (c : EReal) * f x) := by
  have hb' : ∀ x, (c : EReal) * f x ≠ ⊥ := fun x => EReal.coe_mul_ne_bot hc (hb x)
  rw [closedConvex_iff_lowerSemicontinuous hb', lowerSemicontinuous_iff_isClosed_epi]
  rcases eq_or_lt_of_le hc with h | h
  · have hz : (fun x => (c : EReal) * f x) = fun _ : E => (0 : EReal) := by
      funext x; rw [← h]; simp
    rw [hz, ← lowerSemicontinuous_iff_isClosed_epi]
    exact lowerSemicontinuous_const
  · rw [epi_coe_mul h f]
    refine IsClosed.preimage (continuous_scaleSnd _) ?_
    rw [← lowerSemicontinuous_iff_isClosed_epi]
    exact (closedConvex_iff_lowerSemicontinuous hb).1 hf

end ScalarMultiple

/-! ### Closed proper convex functions -/

section ClosedProperConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {f : E → EReal}

/-- A **closed proper convex function** is a function $f : E \to [-\infty, +\infty]$ that is convex,
closed and proper.

This is the standing hypothesis of the duality theory, and the class of functions that
`ConvexAnalysis.convexConjEquiv` and `ConvexAnalysis.supportEquiv` put in bijection. The three
conditions occur together throughout the duality theory, so they are bundled. -/
structure ClosedProperConvexFn (f : E → EReal) : Prop where
  /-- The function is convex: its epigraph is convex. -/
  convex : ConvexFn f
  /-- The function is closed: it equals its closure. -/
  closed : ClosedConvex f
  /-- The function is proper: it is less than $+\infty$ somewhere and never $-\infty$. -/
  proper : ProperConvex f

/-- A **closed proper concave function** is a function $g : E \to [-\infty, +\infty]$ that is
concave, concave-closed and proper. This is the counterpart of
`ConvexAnalysis.ClosedProperConvexFn` and the standing hypothesis on the concave side of
Fenchel's duality theorem. -/
structure ClosedProperConcaveFn (g : E → EReal) : Prop where
  /-- The function is concave: its hypograph is convex. -/
  concave : ConcaveFn g
  /-- The function equals its concave closure. -/
  closed : ClosedConcave g
  /-- The function is proper: it is greater than $-\infty$ somewhere and never $+\infty$. -/
  proper : ProperConcave g

omit [IsTopologicalAddGroup E] in
/-- **Negation exchanges closed proper concave and closed proper convex functions.** Let $E$ be a
real vector space with a topology and let $g : E \to [-\infty, +\infty]$. Then $g$ is closed
proper concave if and only if $-g$ is closed proper convex, and the equivalence holds condition
by condition. -/
theorem closedProperConcaveFn_iff_closedProperConvexFn_neg {g : E → EReal} :
    ClosedProperConcaveFn g ↔ ClosedProperConvexFn fun x => -(g x) :=
  ⟨fun h => ⟨h.concave.convexFn_neg, closedConcave_iff_closedConvex_neg.1 h.closed,
      h.proper.properConvex_neg⟩,
    fun h => ⟨concaveFn_iff_convexFn_neg.2 h.convex, closedConcave_iff_closedConvex_neg.2 h.closed,
      properConcave_iff_properConvex_neg.2 h.proper⟩⟩

omit [IsTopologicalAddGroup E] in
/-- If $g$ is closed proper concave, then $-g$ is closed proper convex. -/
theorem ClosedProperConcaveFn.closedProperConvexFn_neg {g : E → EReal}
    (hg : ClosedProperConcaveFn g) : ClosedProperConvexFn fun x => -(g x) :=
  closedProperConcaveFn_iff_closedProperConvexFn_neg.1 hg

/-- A closed proper convex function is lower semicontinuous. -/
theorem ClosedProperConvexFn.lowerSemicontinuous (hf : ClosedProperConvexFn f) :
    LowerSemicontinuous f :=
  hf.closed.lowerSemicontinuous

/-- A closed proper convex function has a closed epigraph. -/
theorem ClosedProperConvexFn.isClosed_epi (hf : ClosedProperConvexFn f) : IsClosed (epi f) :=
  lowerSemicontinuous_iff_isClosed_epi.1 hf.lowerSemicontinuous

/-- A convex proper function with a closed epigraph is closed proper convex. For a proper function a
closed epigraph is the same as closedness, and the recession theory uses this form of the
constructor. -/
theorem ClosedProperConvexFn.of_isClosed_epi (hconv : ConvexFn f) (hc : IsClosed (epi f))
    (hp : ProperConvex f) : ClosedProperConvexFn f :=
  ⟨hconv, (closedConvex_iff_lowerSemicontinuous hp.ne_bot).2
    (lowerSemicontinuous_iff_isClosed_epi.2 hc), hp⟩

/-- A proper function $f$ is closed proper convex if and only if $f$ is convex and has a closed
epigraph. -/
theorem closedProperConvexFn_iff_isClosed_epi (hp : ProperConvex f) :
    ClosedProperConvexFn f ↔ ConvexFn f ∧ IsClosed (epi f) :=
  ⟨fun hf => ⟨hf.convex, hf.isClosed_epi⟩,
    fun ⟨hconv, hc⟩ => ClosedProperConvexFn.of_isClosed_epi hconv hc hp⟩

/-- **A continuous affine function is closed proper convex.** Let $E$ be a real vector space with a
topology that makes it a topological additive group, and let $g : E \to \mathbb{R}$ be a
continuous affine function. Then $g$, as a function into $[-\infty, +\infty]$, is closed proper
convex.

Affine constraints need this: an equality constraint $a(x) = 0$ enters the theory as the pair of
convex functions $a$ and $-a$. Continuity is a hypothesis and not a consequence: on an
infinite-dimensional space a discontinuous linear functional is convex, finite everywhere and
proper, but not closed. In finite dimension `AffineMap.continuous_of_finiteDimensional` gives
the continuity. -/
theorem closedProperConvexFn_coe_affineMap {g : E →ᵃ[ℝ] ℝ} (hg : Continuous g) :
    ClosedProperConvexFn (fun x => ((g x : ℝ) : EReal)) := by
  have hcont : Continuous fun x : E => ((g x : ℝ) : EReal) := EReal.continuous_coe_iff.2 hg
  refine ⟨?_, ?_, ⟨⟨0, mem_convexDom.2 (EReal.coe_lt_top _)⟩,
    fun _ => EReal.coe_ne_bot _⟩⟩
  · refine convexFn_of_epi_combo fun x y p q hx hy s t hs ht hst => ?_
    rw [EReal.coe_le_coe_iff] at hx hy ⊢
    rw [Convex.combo_affine_apply hst]
    simp only [smul_eq_mul]
    nlinarith
  · exact (closedConvex_iff_lowerSemicontinuous fun _ => EReal.coe_ne_bot _).2
      hcont.lowerSemicontinuous

end ClosedProperConvex

/-!
### Why the dichotomy needs a hypothesis

The example below shows why `ConvexAnalysis.eq_bot_of_lsc_of_eq_bot` assumes $f(x) < +\infty$ for
all $x$. The function on $\mathbb{R}$ that is $-\infty$ at the origin and $+\infty$ elsewhere has
the vertical line $\{0\} \times \mathbb{R}$ as its epigraph. So it is convex and lower
semicontinuous and takes the value $-\infty$, but it is not the constant $-\infty$.
-/

example : ∃ f : ℝ → EReal,
    ConvexFn f ∧ LowerSemicontinuous f ∧ (∃ x, f x = ⊥) ∧ f ≠ fun _ => ⊥ := by
  have hepi : epi (ConvexAnalysis.convexRestrict ({0} : Set ℝ) fun _ => (⊥ : EReal))
      = (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' {0} := by
    ext p
    by_cases h : p.1 ∈ ({0} : Set ℝ) <;> simp [epi, h]
  refine ⟨ConvexAnalysis.convexRestrict ({0} : Set ℝ) fun _ => ⊥, ⟨?_⟩, ?_, ⟨0, by simp⟩, ?_⟩
  · rw [hepi]
    exact (convex_singleton (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  · refine lowerSemicontinuous_iff_isClosed_epi.2 ?_
    rw [hepi]
    exact isClosed_singleton.preimage continuous_fst
  · intro hcontra
    have h1 := congrFun hcontra 1
    rw [ConvexAnalysis.convexRestrict_of_notMem (by norm_num : (1 : ℝ) ∉ ({0} : Set ℝ))] at h1
    exact absurd h1 (by simp)


/-! ### Affine minorants of closed proper convex functions -/

section LocallyConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {f : E → EReal}

/-- **A closed proper convex function has a continuous affine minorant.** Let $E$ be a real locally
convex topological vector space and let $f : E \to [-\infty, +\infty]$ be closed proper convex.
Then there are a continuous linear functional $y$ on $E$ and $c \in \mathbb{R}$ such that
$$y(x) - c \le f(x) \quad \text{for all } x \in E.$$

This is the main step of the Fenchel–Moreau theorem. Closedness is essential: for a proper
convex $f$ that is not closed, the statement is false in infinite dimension. A discontinuous
linear functional $g$ has a dense kernel, so $\operatorname{lsc} g \equiv -\infty$, but $g$ is
convex, finite everywhere and proper. The proof separates the closed convex set
$\operatorname{epi} f$ from the point $(x_0, f(x_0) - 1)$. The separating functional cannot be
vertical, because a functional $(y, 0)$ takes the same value at $(x_0, f(x_0) - 1)$ and at
$(x_0, f(x_0)) \in \operatorname{epi} f$. -/
theorem exists_affine_le_of_closed_proper (hf : ClosedProperConvexFn f) :
    ∃ (y : E →L[ℝ] ℝ) (c : ℝ), ∀ x, ((y x : ℝ) : EReal) - c ≤ f x := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.convexDom_nonempty
  obtain ⟨t, ht⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x₀) hx₀
  obtain ⟨y, b, hy, _⟩ :=
    exists_affine_le_of_isClosed_epi hf.convex hf.isClosed_epi (ν := t) (μ := t - 1) (le_of_eq ht)
      (by rw [ht]; exact_mod_cast (by linarith : t - 1 < t))
  exact ⟨y, b, hy⟩

end LocallyConvex

/-! ### Limits along a segment -/

section SegmentLimit

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- The common part of the limit formulas along a segment. Let $x, y \in E$ and
$\alpha \in \mathbb{R}$. Suppose that for every $\beta \in \mathbb{R}$ with $(y, \beta) \in
\operatorname{cl}(\operatorname{epi} f)$ and every $0 \le a < 1$, the point
$(1 - a)(x, \alpha) + a (y, \beta)$ is in $\operatorname{epi} f$. Then $f((1 - a) x + a y) \to
(\operatorname{lsc} f)(y)$ as $a \to 1$ from below.

Lower semicontinuity of the hull gives the lower bound, and the combinations give the upper
bound. `ConvexAnalysis.tendsto_lscHull_along_segment` gets the hypothesis from an interior point
of $\operatorname{epi} f$, and `ConvexAnalysis.ConvexFn.tendsto_lscHull_along_segment_relint`
from a point of its relative interior. -/
theorem tendsto_lscHull_along_segment_of_combo_mem {x y : E} {α : ℝ}
    (hcombo : ∀ β : ℝ, ((y, β) : E × ℝ) ∈ closure (epi f) → ∀ a : ℝ, 0 ≤ a → a < 1 →
      (1 - a) • ((x, α) : E × ℝ) + a • (y, β) ∈ epi f) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (lscHull f y)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [(tendsto_segment x y).eventually (lowerSemicontinuous_lscHull f y b hb)]
      with a ha
    exact lt_of_lt_of_le ha (lscHull_le f _)
  · intro b hb
    obtain ⟨β, hβ1, hβ2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    obtain ⟨γ, hγ1, hγ2⟩ := EReal.lt_iff_exists_real_btwn.1 hβ2
    have hβγ : β < γ := by exact_mod_cast hγ1
    have hyβ : ((y, β) : E × ℝ) ∈ closure (epi f) := by
      rw [← epi_lscHull]; exact hβ1.le
    filter_upwards [(tendsto_affine_nhdsLT_one α β).eventually_lt_const hβγ,
      eventually_mem_Ico_nhdsLT_one] with a hlt ha
    have hmem := hcombo β hyβ a ha.1 ha.2
    have hpair : (1 - a) • ((x, α) : E × ℝ) + a • (y, β)
        = ((1 - a) • x + a • y, (1 - a) * α + a * β) := by
      simp [smul_eq_mul]
    rw [hpair] at hmem
    have hle : f ((1 - a) • x + a • y) ≤ (((1 - a) * α + a * β : ℝ) : EReal) := mk_mem_epi.1 hmem
    exact lt_of_le_of_lt hle (lt_trans (by exact_mod_cast hlt) hγ2)

/-- **The lower semicontinuous hull as a limit along a segment.** Let $E$ be a real topological
vector space, let $f : E \to [-\infty, +\infty]$ be convex, let $(x, \alpha)$ be an interior
point of $\operatorname{epi} f$, and let $y \in E$. Then $$f((1 - a) x + a y) \to
(\operatorname{lsc} f)(y) \quad \text{as } a \to 1 \text{ from below}.$$

The classical hypothesis is $x \in \operatorname{ri}(\operatorname{dom} f)$, which says that the
vertical line over $x$ meets the relative interior of $\operatorname{epi} f$. Relative interiors
need finite dimension, so the general statement uses the interior of $\operatorname{epi} f$. In
finite dimension the interior of $\operatorname{epi} f$ can be empty when the relative interior
is not, so this form is a restriction as well as a generalization. -/
theorem tendsto_lscHull_along_segment (hf : ConvexFn f) {x : E} {α : ℝ}
    (hx : (x, α) ∈ interior (epi f)) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (lscHull f y)) :=
  tendsto_lscHull_along_segment_of_combo_mem fun _ hyβ a ha0 ha1 => interior_subset
    (hf.convex_epi.combo_interior_closure_mem_interior hx hyβ (by linarith) ha0 (by ring))

/-- **The closure as a limit along a segment.** Let $f$ be convex with
$(\operatorname{lsc} f)(z) \neq -\infty$ for all $z$, let $(x, \alpha)$ be an interior point of
$\operatorname{epi} f$, and let $y \in E$. Then $f((1 - a) x + a y) \to (\operatorname{cl}
f)(y)$ as $a \to 1$ from below.

The exceptional case must be excluded, and it can occur: for the function that is $-\infty$ on a
closed ball and $+\infty$ outside it, $\operatorname{cl} f \equiv -\infty$, but the limit along
a segment that ends outside the ball is $+\infty$. The classical statement has the corresponding
restriction $y \in \operatorname{cl}(\operatorname{dom} f)$ in the improper case. -/
theorem convexCl_eq_limit_along_segment (hf : ConvexFn f) (hne : ∀ z, lscHull f z ≠ ⊥)
    {x : E} {α : ℝ}
    (hx : (x, α) ∈ interior (epi f)) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (convexCl f y)) := by
  rw [convexCl_of_forall_ne_bot hne]
  exact tendsto_lscHull_along_segment hf hx y

/-- **A closed proper convex function is the limit of its values along a segment.** Let $E$ be a
real topological vector space, let $f$ be closed proper convex, let
$x \in \operatorname{dom} f$, and let $y \in E$. Then $$f((1 - a) x + a y) \to f(y) \quad
\text{as } a \to 1 \text{ from below}.$$

No relative interiors are involved. Lower semicontinuity gives the bound for the $\liminf$ for
every $y$, including $f(y) = +\infty$, and convexity applied to the finite values $f(x)$ and
$f(y)$ gives the bound for the $\limsup$. -/
theorem tendsto_along_segment_of_closed_proper (hf : ClosedProperConvexFn f)
    {x : E} (hx : x ∈ convexDom f) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) := by
  have hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  rw [tendsto_order]
  refine ⟨fun b hb => (tendsto_segment x y).eventually (hlsc y b hb), fun b hb => ?_⟩
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hx
  obtain ⟨r, hr⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot y) (lt_of_lt_of_le hb le_top)
  obtain ⟨γ, hγ1, hγ2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  have hrγ : r < γ := by rw [hr] at hγ1; exact_mod_cast hγ1
  filter_upwards [(tendsto_affine_nhdsLT_one s r).eventually_lt_const hrγ,
    eventually_mem_Ico_nhdsLT_one] with a hlt ha
  have hle := hf.convex.epi_combo hs.le hr.le (by linarith [ha.2] : (0 : ℝ) ≤ 1 - a) ha.1 (by ring)
  exact lt_of_le_of_lt hle (lt_trans (by exact_mod_cast hlt) hγ2)

end SegmentLimit

/-!
### The lower semicontinuous hull as a limit inferior

[rockafellar1970convex] writes $(\operatorname{cl} f)(x) = \liminf_{y \to x} f(y)$. In a complete
lattice, $\liminf_{y \to x} f(y) = \sup_{U \ni x} \inf_{y \in U} f(y)$, with $U$ ranging over the
neighbourhoods of $x$, and this is the value of $\operatorname{lsc} f$ at $x$. So the identity needs
no convexity and no hypothesis on $f$.
-/

section Liminf

variable {E : Type*} [TopologicalSpace E] {f : E → EReal}

/-- The limit inferior of $f$ at $x$ is at most $f(x)$: $\liminf_{y \to x} f(y) \le f(x)$, because
every neighbourhood of $x$ contains $x$. -/
theorem liminf_nhds_le (f : E → EReal) (x : E) : liminf f (𝓝 x) ≤ f x := by
  rw [liminf_eq_iSup_iInf]
  exact iSup₂_le fun s hs => iInf₂_le x (mem_of_mem_nhds hs)

/-- The limit superior of $g$ at $x$ is at least $g(x)$: $g(x) \le \limsup_{y \to x} g(y)$. -/
theorem le_limsup_nhds (g : E → EReal) (x : E) : g x ≤ limsup g (𝓝 x) := by
  have h := liminf_nhds_le (-g) x
  rw [EReal.liminf_neg, Pi.neg_apply] at h
  exact EReal.neg_le_neg_iff.1 h

/-- The function $x \mapsto \liminf_{y \to x} f(y)$ is lower semicontinuous. A neighbourhood that
gives the bound at $x$ gives it, through its interior, at every nearby point. -/
theorem lowerSemicontinuous_liminf_nhds (f : E → EReal) :
    LowerSemicontinuous fun x => liminf f (𝓝 x) := by
  intro x c hc
  have hc' : c < liminf f (𝓝 x) := hc
  rw [liminf_eq_iSup_iInf] at hc'
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 hc'
  obtain ⟨hsmem, hlt⟩ := lt_iSup_iff.1 hs
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hsmem)] with z hz
  change c < liminf f (𝓝 z)
  refine lt_of_lt_of_le hlt ?_
  rw [liminf_eq_iSup_iInf]
  refine le_trans ?_
    (le_iSup₂ (f := fun t (_ : t ∈ 𝓝 z) => ⨅ a ∈ t, f a) (interior s)
      (isOpen_interior.mem_nhds hz))
  exact le_iInf₂ fun a ha => iInf₂_le a (interior_subset ha)

end Liminf

section LiminfHull

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {f : E → EReal}

/-- **The lower semicontinuous hull is a limit inferior.** Let $E$ be a commutative topological
group and let $f : E \to [-\infty, +\infty]$. For every $x \in E$, $$(\operatorname{lsc} f)(x) =
\liminf_{y \to x} f(y).$$

The function $x \mapsto \liminf_{y \to x} f(y)$ is a lower semicontinuous minorant of $f$, and a
lower semicontinuous function is at most its own limit inferior. The limit inferior is
`liminf f (𝓝 x)`. -/
theorem lscHull_eq_liminf (f : E → EReal) (x : E) : lscHull f x = liminf f (𝓝 x) := by
  refine le_antisymm ?_ (le_lscHull_of_le (lowerSemicontinuous_liminf_nhds f) (liminf_nhds_le f) x)
  refine le_trans (LowerSemicontinuous.le_liminf (lowerSemicontinuous_lscHull f) x) ?_
  rw [liminf_eq_iSup_iInf, liminf_eq_iSup_iInf]
  exact iSup₂_mono fun s _ => iInf₂_mono fun a _ => lscHull_le f a

/-- **The identity $\operatorname{cl} f = \liminf f$ of [rockafellar1970convex], regular case.** If
$(\operatorname{lsc} f)(z) \neq -\infty$ for all $z$, then $(\operatorname{cl} f)(x) =
\liminf_{y \to x} f(y)$ for every $x$. -/
theorem convexCl_eq_liminf (h : ∀ z, lscHull f z ≠ ⊥) (x : E) : convexCl f x = liminf f (𝓝 x) := by
  rw [convexCl_of_forall_ne_bot h, lscHull_eq_liminf]

end LiminfHull

section LiminfConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal}

/-- **The identity $\operatorname{cl} f = \liminf f$ of [rockafellar1970convex].** Let $E$ be a real
topological vector space and let $f : E \to [-\infty, +\infty]$ be convex. For every $x \in E$,
either $$(\operatorname{cl} f)(x) = \liminf_{y \to x} f(y),$$ or
$(\operatorname{cl} f)(x) = -\infty$ and $\liminf_{y \to x} f(y) = +\infty$.

The second case can occur only in the exceptional case of `ConvexAnalysis.convexCl`, where the
dichotomy leaves $\operatorname{lsc} f$ with only the values $-\infty$ and $+\infty$. -/
theorem convexCl_eq_liminf_or (hf : ConvexFn f) (x : E) :
    convexCl f x = liminf f (𝓝 x) ∨ (convexCl f x = ⊥ ∧ liminf f (𝓝 x) = ⊤) := by
  by_cases h : ∃ z, lscHull f z = ⊥
  · have hcl : convexCl f x = ⊥ := by rw [convexCl_of_exists_eq_bot h]
    rcases ConvexFn.eq_bot_or_eq_top (convexFn_lscHull hf) (lowerSemicontinuous_lscHull f) h x with
      hb | ht
    · exact Or.inl (by rw [hcl, ← lscHull_eq_liminf, hb])
    · exact Or.inr ⟨hcl, by rw [← lscHull_eq_liminf]; exact ht⟩
  · push Not at h
    exact Or.inl (by rw [convexCl_of_forall_ne_bot h, lscHull_eq_liminf])

/-- **The concave counterpart of $\operatorname{cl} f = \liminf f$.** Let $E$ be a real topological
vector space and let $g : E \to [-\infty, +\infty]$ be concave. For every $x \in E$, either the
concave closure of $g$ at $x$ equals $\limsup_{y \to x} g(y)$, or it is $+\infty$ and
$\limsup_{y \to x} g(y) = -\infty$. -/
theorem concaveCl_eq_limsup_or {g : E → EReal} (hg : ConcaveFn g) (x : E) :
    concaveCl g x = limsup g (𝓝 x) ∨ (concaveCl g x = ⊤ ∧ limsup g (𝓝 x) = ⊥) := by
  have hkey : liminf (fun z => -(g z)) (𝓝 x) = -(limsup g (𝓝 x)) := EReal.liminf_neg
  rcases convexCl_eq_liminf_or hg.convexFn_neg x with heq | ⟨hbot, htop⟩
  · exact Or.inl (by rw [concaveCl_apply, heq, hkey, neg_neg])
  · refine Or.inr ⟨by rw [concaveCl_apply, hbot, EReal.neg_bot], ?_⟩
    rw [hkey] at htop
    exact EReal.neg_eq_top_iff.1 htop

end LiminfConvex

end ConvexAnalysis
