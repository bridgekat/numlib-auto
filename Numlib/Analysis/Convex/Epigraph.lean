/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function
import Numlib.Order.EReal

/-!
# Extended-real-valued convex and concave functions

This module gives the basic theory of convex functions $f : E \to [-\infty, +\infty]$ on a real
vector space $E$, and of concave functions $g : E \to [-\infty, +\infty]$, following §4 of
[rockafellar1970convex] and, for the concave conventions, §30. Convexity is defined geometrically,
as convexity of the **epigraph** $\operatorname{epi} f = \{(x, \mu) \in E \times \mathbb{R} \mid
f(x) \le \mu\}$, and not by the inequality $f(ax + by) \le a f(x) + b f(y)$: the right side can be
the undefined $+\infty - \infty$ when $f$ takes both infinite values, and improper functions are
admitted throughout. Concavity is defined in the same way, as convexity of the **hypograph**
$\operatorname{hypo} g = \{(x, \mu) \in E \times \mathbb{R} \mid \mu \le g(x)\}$. The relation "$g$
is concave exactly when $-g$ is convex" is then a theorem. [rockafellar1970convex] mixes the two
theories often from Part VI on, so the concave notions have names of their own.

Sign transfer is not free on the extended reals, because negation does not distribute over addition:
$-\bigl((-\infty) + (+\infty)\bigr) = +\infty$, while $\bigl(-(-\infty)\bigr) +
\bigl(-(+\infty)\bigr) = -\infty$. Therefore `ConvexAnalysis.concaveFn_iff_le` needs
$g(x) \neq +\infty$ for all $x$, as `ConvexAnalysis.convexFn_iff_le` needs $f(x) \neq -\infty$,
while `ConvexAnalysis.concaveFn_iff_convexFn_neg`, which forms no sum, needs no hypothesis.

## Main definitions

* `ConvexAnalysis.epi`, `ConvexAnalysis.hypo`: the epigraph of $f$ and the hypograph of $g$, subsets
  of $E \times \mathbb{R}$.
* `ConvexAnalysis.convexDom`, `ConvexAnalysis.concaveDom`: the effective domain
  $\{x \mid f(x) < +\infty\}$ of $f$, and the effective domain $\{x \mid g(x) > -\infty\}$ of $g$.
* `ConvexAnalysis.ProperConvex`, `ConvexAnalysis.ProperConcave`: $f$ is finite somewhere and never
  $-\infty$; $g$ is finite somewhere and never $+\infty$.
* `ConvexAnalysis.convexRestrict`, `ConvexAnalysis.concaveRestrict`: $f$ restricted to a set $s$ and
  extended by $+\infty$, and $g$ restricted to $s$ and extended by $-\infty$.
* `ConvexAnalysis.ConvexFn`, `ConvexAnalysis.ConcaveFn`: $f$ is convex when $\operatorname{epi} f$
  is convex; $g$ is concave when $\operatorname{hypo} g$ is convex.
* `ConvexAnalysis.scaleSnd`: the vertical scaling $(x, \mu) \mapsto (x, c\mu)$ of
  $E \times \mathbb{R}$, through which a scalar multiple of $f$ acts on epigraphs.

## Main results

* `ConvexAnalysis.hypo_neg`, `ConvexAnalysis.epi_neg`, `ConvexAnalysis.concaveDom_eq_convexDom_neg`,
  `ConvexAnalysis.properConcave_iff_properConvex_neg`, `ConvexAnalysis.concaveFn_iff_convexFn_neg`:
  the sign dictionary. The statement "$g$ is concave when $-g$ is convex" is a theorem, together
  with the transfer of effective domains and of properness.
* `ConvexAnalysis.convexFn_iff_forall_lt`, `ConvexAnalysis.concaveFn_iff_forall_gt`: convexity and
  concavity by strict inequalities, a form that avoids $+\infty - \infty$.
* `ConvexAnalysis.convexFn_iff_le`, `ConvexAnalysis.concaveFn_iff_le`: the familiar inequality,
  valid when $f$ never takes the value $-\infty$, and the reversed inequality, valid when $g$ never
  takes the value $+\infty$.
* `ConvexAnalysis.convexFn_add_coe`, `ConvexAnalysis.ConvexFn.comp_add_left`: adding a real-valued
  affine function and translating the argument preserve convexity.
* `ConvexAnalysis.ConvexFn.convex_lt`, `ConvexAnalysis.ConvexFn.convex_le`,
  `ConvexAnalysis.ConvexFn.convex_convexDom`: the sublevel sets and the effective domain of a convex
  function are convex. `ConvexAnalysis.ConcaveFn.convex_gt`, `ConvexAnalysis.ConcaveFn.convex_ge`
  and `ConvexAnalysis.ConcaveFn.convex_concaveDom` are the same for superlevel sets of a concave
  function.
* `ConvexAnalysis.convexFn_coe_mul`, `ConvexAnalysis.convexDom_coe_mul`,
  `ConvexAnalysis.properConvex_coe_mul`: for $c \ge 0$, the multiple $cf$ of a convex function is
  convex and the multiple of a proper function is proper; for $c > 0$, $cf$ has the same effective
  domain as $f$.
* `ConvexAnalysis.convexOn_iff_convexFn`, `ConvexAnalysis.concaveOn_iff_concaveFn`: the relation to
  Mathlib's `ConvexOn` and `ConcaveOn`. With them, the dictionary between real-valued and
  extended-real-valued functions: `ConvexAnalysis.convexDom_coe`, `ConvexAnalysis.properConvex_coe`,
  `ConvexAnalysis.convexDom_convexRestrict_coe`, `ConvexAnalysis.properConvex_convexRestrict_coe`,
  `ConvexOn.convexFn_convexRestrict_coe`, `ConvexOn.convexFn_coe`, and their concave counterparts.
* `ConvexAnalysis.ConvexFn.sum_le`: Jensen's inequality for a finite convex combination.

## Implementation notes

* The epigraph is a subset of $E \times \mathbb{R}$, not of $E \times [-\infty, +\infty]$: the
  second coordinate ranges over the reals. Mathlib's `ConvexOn.convex_epigraph` uses the codomain of
  the function instead.
* [rockafellar1970convex] writes $\operatorname{epi} g$ also for the hypograph of a concave
  function. Here the two sets have different names.
* Where mathematics has a natural pair of dual words, the convex and the concave side use them:
  `epi` and `hypo`, `ConvexFn` and `ConcaveFn`, `infConv` and `supConv`, and in other modules
  `lscHull` and `uscHull`, `subdifferential` and `superdifferential`. Elsewhere both sides carry the
  same pattern: `convexDom` and `concaveDom`, `ProperConvex` and `ProperConcave`, `convexRestrict`
  and `concaveRestrict`, and in other modules `convexCl` and `concaveCl`, `ClosedConvex` and
  `ClosedConcave`, `convexConj` and `concaveConj`. Lemma names carry these tokens, as in
  `ConvexAnalysis.mem_convexDom`.
* Each concave declaration comes right after its convex counterpart. It is proved from the convex
  one through the sign dictionary where this is not longer than a direct proof.
-/

open Set

namespace ConvexAnalysis

/-! ### Epigraphs, hypographs, domains, properness -/

section Basic

variable {E : Type*}

/-- The **epigraph** of a function $f : E \to [-\infty, +\infty]$ is
$$\operatorname{epi} f = \{(x, \mu) \in E \times \mathbb{R} \mid f(x) \le \mu\}.$$

The second coordinate ranges over the reals, not over the extended reals. -/
def epi (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

/-- A pair $p = (x, \mu) \in E \times \mathbb{R}$ lies in $\operatorname{epi} f$ if and only if
$f(x) \le \mu$. -/
@[simp]
theorem mem_epi {f : E → EReal} {p : E × ℝ} : p ∈ epi f ↔ f p.1 ≤ (p.2 : EReal) := Iff.rfl

/-- For $x \in E$ and $\mu \in \mathbb{R}$, $(x, \mu) \in \operatorname{epi} f$ if and only if
$f(x) \le \mu$. -/
theorem mk_mem_epi {f : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ epi f ↔ f x ≤ (μ : EReal) := Iff.rfl

/-- The **hypograph** of a function $g : E \to [-\infty, +\infty]$ is
$$\operatorname{hypo} g = \{(x, \mu) \in E \times \mathbb{R} \mid \mu \le g(x)\}.$$

[rockafellar1970convex] writes this set as $\operatorname{epi} g$, reusing the notation of the
epigraph; here the two names are kept apart. As for `ConvexAnalysis.epi`, the second coordinate
ranges over the reals. -/
def hypo (g : E → EReal) : Set (E × ℝ) := {p | (p.2 : EReal) ≤ g p.1}

/-- A pair $p = (x, \mu) \in E \times \mathbb{R}$ lies in $\operatorname{hypo} g$ if and only if
$\mu \le g(x)$. -/
@[simp]
theorem mem_hypo {g : E → EReal} {p : E × ℝ} : p ∈ hypo g ↔ (p.2 : EReal) ≤ g p.1 := Iff.rfl

/-- For $x \in E$ and $\mu \in \mathbb{R}$, $(x, \mu) \in \operatorname{hypo} g$ if and only if
$\mu \le g(x)$. -/
theorem mk_mem_hypo {g : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ hypo g ↔ (μ : EReal) ≤ g x := Iff.rfl

/-- The epigraph is antitone in the function: if $f \le g$, then $\operatorname{epi} g \subseteq
\operatorname{epi} f$. -/
theorem epi_anti {f g : E → EReal} (h : f ≤ g) : epi g ⊆ epi f := fun _ hp => (h _).trans hp

/-- The epigraph determines the function: $f \le g$ if and only if $\operatorname{epi} g \subseteq
\operatorname{epi} f$. -/
theorem le_iff_epi_subset {f g : E → EReal} : f ≤ g ↔ epi g ⊆ epi f := by
  refine ⟨epi_anti, fun h x => ?_⟩
  by_contra hx
  obtain ⟨q, hgq, hqf⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  exact absurd (h (show (x, q) ∈ epi g from hgq.le)) (not_le.2 hqf)

/-- The hypograph is monotone in the function: if $g \le h$, then $\operatorname{hypo} g \subseteq
\operatorname{hypo} h$. -/
theorem hypo_mono {g h : E → EReal} (hgh : g ≤ h) : hypo g ⊆ hypo h := fun _ hp => hp.trans (hgh _)

/-- The hypograph determines the function: $g \le h$ if and only if $\operatorname{hypo} g \subseteq
\operatorname{hypo} h$. -/
theorem le_iff_hypo_subset {g h : E → EReal} : g ≤ h ↔ hypo g ⊆ hypo h := by
  refine ⟨hypo_mono, fun hs x => ?_⟩
  by_contra hx
  obtain ⟨q, hhq, hqg⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  exact absurd (hs (show (x, q) ∈ hypo g from hqg.le)) (not_le.2 hhq)

/-- The **effective domain** of a function $f : E \to [-\infty, +\infty]$ is
$$\operatorname{dom} f = \{x \in E \mid f(x) < +\infty\}.$$

It is the projection of $\operatorname{epi} f$ on $E$
(`ConvexAnalysis.convexDom_eq_fst_image_epi`). -/
def convexDom (f : E → EReal) : Set E := {x | f x < ⊤}

/-- A point $x$ lies in the effective domain of $f$ if and only if $f(x) < +\infty$. -/
@[simp] theorem mem_convexDom {f : E → EReal} {x : E} : x ∈ convexDom f ↔ f x < ⊤ := Iff.rfl

/-- The **effective domain of a concave function** $g : E \to [-\infty, +\infty]$ is
$$\operatorname{dom} g = \{x \in E \mid g(x) > -\infty\}.$$

It is the projection of the hypograph on $E$ (`ConvexAnalysis.concaveDom_eq_fst_image_hypo`). -/
def concaveDom (g : E → EReal) : Set E := {x | ⊥ < g x}

/-- A point $x$ lies in the concave effective domain of $g$ if and only if $g(x) > -\infty$. -/
@[simp] theorem mem_concaveDom {g : E → EReal} {x : E} : x ∈ concaveDom g ↔ ⊥ < g x := Iff.rfl

/-- A function $f : E \to [-\infty, +\infty]$ is **proper** if it is finite somewhere and never
takes the value $-\infty$: $f(x) < +\infty$ for some $x$, and $f(x) > -\infty$ for every $x$.

Equivalently, $\operatorname{epi} f$ is nonempty and contains no vertical line. Convexity is not
part of the definition. -/
structure ProperConvex (f : E → EReal) : Prop where
  /-- The effective domain of $f$ is nonempty: $f$ is not identically $+\infty$. -/
  convexDom_nonempty : (convexDom f).Nonempty
  /-- The function $f$ never takes the value $-\infty$. -/
  ne_bot : ∀ x, f x ≠ ⊥

/-- A function $g : E \to [-\infty, +\infty]$ is **proper** in the concave sense if it is finite
somewhere and never takes the value $+\infty$: $g(x) > -\infty$ for some $x$, and
$g(x) < +\infty$ for every $x$.

Equivalently, $-g$ is proper (`ConvexAnalysis.properConcave_iff_properConvex_neg`). -/
structure ProperConcave (g : E → EReal) : Prop where
  /-- The concave effective domain of $g$ is nonempty: $g$ is not identically $-\infty$. -/
  concaveDom_nonempty : (concaveDom g).Nonempty
  /-- The function $g$ never takes the value $+\infty$. -/
  ne_top : ∀ x, g x ≠ ⊤

/-- The **restriction** of $f : E \to [-\infty, +\infty]$ to a set $s \subseteq E$, extended by
$+\infty$ outside $s$:
$$x \mapsto \begin{cases} f(x) & x \in s, \\ +\infty & x \notin s. \end{cases}$$

This is the standard encoding of a convex function that is given on a convex set. The definition
is an infimum over the proofs of $x \in s$, which avoids a decidability hypothesis;
`ConvexAnalysis.convexRestrict_of_mem` and `ConvexAnalysis.convexRestrict_of_notMem` are the
defining equations. -/
noncomputable def convexRestrict (s : Set E) (f : E → EReal) : E → EReal :=
    fun x => ⨅ _ : x ∈ s, f x

/-- On $s$, the restriction of $f$ to $s$ agrees with $f$. -/
@[simp] theorem convexRestrict_of_mem {s : Set E} {f : E → EReal} {x : E} (hx : x ∈ s) :
    convexRestrict s f x = f x := iInf_pos hx

/-- Outside $s$, the restriction of $f$ to $s$ is $+\infty$. -/
@[simp] theorem convexRestrict_of_notMem {s : Set E} {f : E → EReal} {x : E} (hx : x ∉ s) :
    convexRestrict s f x = ⊤ := iInf_neg hx

/-- The **concave restriction** of $g : E \to [-\infty, +\infty]$ to a set $s \subseteq E$, extended
by $-\infty$ outside $s$:
$$x \mapsto \begin{cases} g(x) & x \in s, \\ -\infty & x \notin s. \end{cases}$$

This is the concave counterpart of `ConvexAnalysis.convexRestrict`, which extends by $+\infty$.
The definition is a supremum over the proofs of $x \in s$, which avoids a decidability
hypothesis; `ConvexAnalysis.concaveRestrict_of_mem` and
`ConvexAnalysis.concaveRestrict_of_notMem` are the defining equations. -/
noncomputable def concaveRestrict (s : Set E) (g : E → EReal) : E → EReal :=
  fun x => ⨆ _ : x ∈ s, g x

/-- On $s$, the concave restriction of $g$ to $s$ agrees with $g$. -/
@[simp] theorem concaveRestrict_of_mem {s : Set E} {g : E → EReal} {x : E} (hx : x ∈ s) :
    concaveRestrict s g x = g x := iSup_pos hx

/-- Outside $s$, the concave restriction of $g$ to $s$ is $-\infty$. -/
@[simp] theorem concaveRestrict_of_notMem {s : Set E} {g : E → EReal} {x : E} (hx : x ∉ s) :
    concaveRestrict s g x = ⊥ := iSup_neg hx

/-!
### The sign dictionary

Every concave notion above is the reflection of its convex counterpart under $g \mapsto -g$. None of
these transfers involves a sum of extended reals, so none needs a side condition.
-/

/-- **The hypograph is the reflected epigraph of the negative.** For every
$g : E \to [-\infty, +\infty]$, $\operatorname{hypo} g$ is the preimage of
$\operatorname{epi}(-g)$ under the vertical reflection $(x, \mu) \mapsto (x, -\mu)$:
$$(x, \mu) \in \operatorname{hypo} g \iff (x, -\mu) \in \operatorname{epi}(-g).$$

This theorem, not a definition, is the statement "$g$ is concave when $-g$ is convex" of
[rockafellar1970convex] at the level of sets. -/
theorem hypo_neg (g : E → EReal) :
    hypo g = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) ⁻¹' epi fun x => -(g x) := by
  ext ⟨x, μ⟩
  change (μ : EReal) ≤ g x ↔ -(g x) ≤ ((-μ : ℝ) : EReal)
  rw [EReal.coe_neg, EReal.neg_le_neg_iff]

/-- **The epigraph of the negative is the reflected hypograph.** For every
$g : E \to [-\infty, +\infty]$, $\operatorname{epi}(-g)$ is the preimage of
$\operatorname{hypo} g$ under the vertical reflection $(x, \mu) \mapsto (x, -\mu)$:
$$(x, \mu) \in \operatorname{epi}(-g) \iff (x, -\mu) \in \operatorname{hypo} g.$$

This is the converse direction of `ConvexAnalysis.hypo_neg`; the reflection is an involution. -/
theorem epi_neg (g : E → EReal) :
    epi (fun x => -(g x)) = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) ⁻¹' hypo g := by
  rw [hypo_neg, ← Set.preimage_comp]
  ext ⟨x, μ⟩
  simp

/-- For every $g : E \to [-\infty, +\infty]$, $\operatorname{hypo} g$ is the image of
$\operatorname{epi}(-g)$ under the vertical reflection $(x, \mu) \mapsto (x, -\mu)$. This is
`ConvexAnalysis.hypo_neg` with an image in place of a preimage. -/
theorem hypo_eq_image_epi_neg (g : E → EReal) :
    hypo g = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) '' epi fun x => -(g x) := by
  have hinv : Function.LeftInverse (Prod.map (id : E → E) (Neg.neg : ℝ → ℝ))
      (Prod.map (id : E → E) (Neg.neg : ℝ → ℝ)) := fun p => by simp [Prod.map]
  rw [Set.image_eq_preimage_of_inverse hinv hinv, hypo_neg]

/-- The concave effective domain of $g$ is the effective domain of $-g$: $\{x \mid g(x) >
-\infty\} = \{x \mid -g(x) < +\infty\}$. -/
theorem concaveDom_eq_convexDom_neg (g : E → EReal) : concaveDom g = convexDom fun x => -(g x) := by
  ext x
  change ⊥ < g x ↔ -(g x) < ⊤
  exact (EReal.neg_lt_comm (a := g x) (b := ⊤)).symm

/-- The concave effective domain of $-h$ is the effective domain of $h$. -/
theorem concaveDom_neg (h : E → EReal) : concaveDom (fun z => -(h z)) = convexDom h := by
  simpa using concaveDom_eq_convexDom_neg fun z => -(h z)

/-- **Properness of a concave function is properness of its negative.** A function
$g : E \to [-\infty, +\infty]$ is proper in the concave sense if and only if $-g$ is proper.
This is the definition of properness for a concave function in [rockafellar1970convex]. -/
theorem properConcave_iff_properConvex_neg {g : E → EReal} :
    ProperConcave g ↔ ProperConvex fun x => -(g x) := by
  constructor
  · refine fun h => ⟨?_, fun x => ?_⟩
    · rw [← concaveDom_eq_convexDom_neg]; exact h.concaveDom_nonempty
    · simp [h.ne_top x]
  · refine fun h => ⟨?_, fun x => ?_⟩
    · rw [concaveDom_eq_convexDom_neg]; exact h.convexDom_nonempty
    · simpa using h.ne_bot x

/-- If $g$ is proper in the concave sense, then $-g$ is proper. This is the forward direction of
`ConvexAnalysis.properConcave_iff_properConvex_neg`. -/
theorem ProperConcave.properConvex_neg {g : E → EReal} (hg : ProperConcave g) :
    ProperConvex fun x => -(g x) :=
  properConcave_iff_properConvex_neg.1 hg

/-- Extension by $-\infty$ and extension by $+\infty$ correspond under negation: the negative of the
concave restriction of $g$ to $s$ is the restriction of $-g$ to $s$. -/
theorem neg_concaveRestrict (s : Set E) (g : E → EReal) :
    (fun x => -(concaveRestrict s g x)) = convexRestrict s fun x => -(g x) := by
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

/-! ### Effective domains as projections -/

/-- **The effective domain is the projection of the epigraph.** For every
$f : E \to [-\infty, +\infty]$, $\operatorname{dom} f$ is the image of $\operatorname{epi} f$
under $(x, \mu) \mapsto x$.

There is no hypothesis on $f$, and improper functions are included. This is why
`ConvexAnalysis.convexDom` is not restricted to functions that avoid $-\infty$: the relative
interior $\operatorname{ri}(\operatorname{dom} f)$ appears in statements about improper $f$ too. -/
theorem convexDom_eq_fst_image_epi (f : E → EReal) : convexDom f = Prod.fst '' epi f := by
  ext x
  constructor
  · intro hx
    rcases eq_or_lt_of_le (bot_le : (⊥ : EReal) ≤ f x) with h | h
    · exact ⟨(x, 0), by simp [epi, ← h], rfl⟩
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top h.ne' hx
      exact ⟨(x, r), by simp [epi, hr], rfl⟩
  · rintro ⟨⟨y, μ⟩, hy, rfl⟩
    exact lt_of_le_of_lt hy (EReal.coe_lt_top μ)

/-- **The concave effective domain is the projection of the hypograph.** For every
$g : E \to [-\infty, +\infty]$, $\{x \mid g(x) > -\infty\}$ is the image of
$\operatorname{hypo} g$ under $(x, \mu) \mapsto x$. There is no hypothesis on $g$. -/
theorem concaveDom_eq_fst_image_hypo (g : E → EReal) : concaveDom g = Prod.fst '' hypo g := by
  rw [concaveDom_eq_convexDom_neg, convexDom_eq_fst_image_epi, hypo_eq_image_epi_neg,
      Set.image_image]
  rfl

/-- The epigraph of $f$ is nonempty if and only if the effective domain of $f$ is nonempty: both say
that $f$ is not identically $+\infty$. -/
theorem epi_nonempty_iff (f : E → EReal) : (epi f).Nonempty ↔ (convexDom f).Nonempty := by
  rw [convexDom_eq_fst_image_epi, Set.image_nonempty]

/-- The epigraph of $f$ is empty if and only if the effective domain of $f$ is empty. -/
theorem epi_eq_empty_iff (f : E → EReal) : epi f = ∅ ↔ convexDom f = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, epi_nonempty_iff]

/-- The epigraph of the constant function $+\infty$ is empty. -/
@[simp] theorem epi_top : epi (⊤ : E → EReal) = ∅ := by
  ext p
  simp [epi, Pi.top_apply]

/-!
### Nonnegative scalar multiples

The extended reals satisfy $0 \cdot (\pm\infty) = 0$, so $0 \cdot f$ is the constant $0$, which is
proper and convex. Only the statement about the effective domain needs $c > 0$, because
$\operatorname{dom}(0 \cdot f)$ is all of $E$.
-/

/-- **A positive multiple of $f$ has the same effective domain as $f$.** Let $c > 0$ and
$f : E \to [-\infty, +\infty]$. Then
$$\operatorname{dom}(cf) = \operatorname{dom} f.$$

The hypothesis is $c > 0$, not $c \ge 0$: for $c = 0$ the product is the constant $0$ and its
effective domain is all of $E$. -/
theorem convexDom_coe_mul {c : ℝ} (hc : 0 < c) (f : E → EReal) :
    convexDom (fun x => (c : EReal) * f x) = convexDom f := by
  ext x
  rw [mem_convexDom, mem_convexDom]
  refine ⟨fun h => ?_, fun h => lt_of_le_of_ne le_top (EReal.coe_mul_ne_top hc h.ne)⟩
  by_contra hcon
  rw [top_le_iff.1 (not_lt.1 hcon), EReal.coe_mul_top_of_pos hc] at h
  exact lt_irrefl _ h

/-- **A nonnegative multiple of a proper function is proper.** Let $c \ge 0$ and let
$f : E \to [-\infty, +\infty]$ be proper. Then $cf$ is proper.

For $c = 0$ the product is the constant $0$, which is finite everywhere; for $c > 0$ the
effective domain does not change (`ConvexAnalysis.convexDom_coe_mul`). -/
theorem properConvex_coe_mul {c : ℝ} (hc : 0 ≤ c) {f : E → EReal} (hp : ProperConvex f) :
    ProperConvex (fun x => (c : EReal) * f x) := by
  refine ⟨?_, fun x => EReal.coe_mul_ne_bot hc (hp.ne_bot x)⟩
  obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
  refine ⟨x₀, ?_⟩
  rcases eq_or_lt_of_le hc with h | h
  · rw [mem_convexDom, ← h]; simp
  · exact mem_convexDom.2 (lt_of_le_of_ne le_top (EReal.coe_mul_ne_top h (mem_convexDom.1 hx₀).ne))

end Basic

/-! ### Convex and concave functions -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A function $f : E \to [-\infty, +\infty]$ is **convex** if its epigraph $\operatorname{epi} f$
is a convex subset of $E \times \mathbb{R}$.

There is no properness condition. The analytic forms of the definition are
`ConvexAnalysis.convexFn_iff_forall_lt` and `ConvexAnalysis.convexFn_iff_le`. -/
structure ConvexFn (f : E → EReal) : Prop where
  /-- The epigraph of $f$ is a convex set. -/
  convex_epi : Convex ℝ (epi f)

/-- A function $f$ is convex if and only if $\operatorname{epi} f$ is a convex set. -/
@[simp] theorem convexFn_iff_convex_epi {f : E → EReal} : ConvexFn f ↔ Convex ℝ (epi f) :=
  ⟨fun h => h.convex_epi, fun h => ⟨h⟩⟩

/-- A function $g : E \to [-\infty, +\infty]$ is **concave** if its hypograph
$\operatorname{hypo} g$ is a convex subset of $E \times \mathbb{R}$.

This mirrors `ConvexAnalysis.ConvexFn`. It agrees with the definition "$-g$ is convex" by
`ConvexAnalysis.concaveFn_iff_convexFn_neg`. -/
structure ConcaveFn (g : E → EReal) : Prop where
  /-- The hypograph of $g$ is a convex set. -/
  convex_hypo : Convex ℝ (hypo g)

/-- A function $g$ is concave if and only if $\operatorname{hypo} g$ is a convex set. -/
@[simp] theorem concaveFn_iff_convex_hypo {g : E → EReal} : ConcaveFn g ↔ Convex ℝ (hypo g) :=
  ⟨fun h => h.convex_hypo, fun h => ⟨h⟩⟩

/-- A property of convex combinations reduces to the case of two positive coefficients. Let $P$ be a
property of points of $E$ with $P(x)$ and $P(y)$, and let $a, b \ge 0$ with $a + b = 1$. If
$P(ax + by)$ holds whenever $a > 0$ and $b > 0$, then $P(ax + by)$ holds. -/
theorem combo_of_pos {P : E → Prop} {x y : E} {a b : ℝ} (hx : P x) (hy : P y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (h : 0 < a → 0 < b → P (a • x + b • y)) :
    P (a • x + b • y) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; simpa using hy
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1; simpa using hx
  exact h ha' hb'

/-- **Convex combinations of points of the epigraph stay in the epigraph.** Let $f$ be convex, let
$f(x) \le \mu$ and $f(y) \le \nu$ for real $\mu, \nu$, and let $a, b \ge 0$ with $a + b = 1$.
Then
$$f(ax + by) \le a\mu + b\nu.$$
-/
theorem ConvexFn.epi_combo {f : E → EReal} (hf : ConvexFn f) {x y : E} {μ ν : ℝ}
    (hx : f x ≤ (μ : EReal)) (hy : f y ≤ (ν : EReal)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal) :=
  hf.convex_epi (show (x, μ) ∈ epi f from hx) (show (y, ν) ∈ epi f from hy) ha hb hab

/-- **Convex combinations of points of the hypograph stay in the hypograph.** Let $g$ be concave,
let $\mu \le g(x)$ and $\nu \le g(y)$ for real $\mu, \nu$, and let $a, b \ge 0$ with
$a + b = 1$. Then
$$a\mu + b\nu \le g(ax + by).$$
-/
theorem ConcaveFn.hypo_combo {g : E → EReal} (hg : ConcaveFn g) {x y : E} {μ ν : ℝ}
    (hx : (μ : EReal) ≤ g x) (hy : (ν : EReal) ≤ g y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : ((a * μ + b * ν : ℝ) : EReal) ≤ g (a • x + b • y) :=
  hg.convex_hypo (show (x, μ) ∈ hypo g from hx) (show (y, ν) ∈ hypo g from hy) ha hb hab

/-- A function $f : E \to [-\infty, +\infty]$ is convex if $f(ax + by) \le a\mu + b\nu$ whenever
$f(x) \le \mu$, $f(y) \le \nu$ for real $\mu, \nu$, and $a, b \ge 0$ with $a + b = 1$. This is
the converse of `ConvexAnalysis.ConvexFn.epi_combo`. -/
theorem convexFn_of_epi_combo {f : E → EReal}
    (h : ∀ (x y : E) (μ ν : ℝ), f x ≤ (μ : EReal) → f y ≤ (ν : EReal) →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal)) :
    ConvexFn f := by
  refine ⟨?_⟩
  rintro ⟨x, μ⟩ hx ⟨y, ν⟩ hy a b ha hb hab
  exact h x y μ ν hx hy a b ha hb hab

/-- A function $g : E \to [-\infty, +\infty]$ is concave if $a\mu + b\nu \le g(ax + by)$ whenever
$\mu \le g(x)$, $\nu \le g(y)$ for real $\mu, \nu$, and $a, b \ge 0$ with $a + b = 1$. This is
the converse of `ConvexAnalysis.ConcaveFn.hypo_combo`. -/
theorem concaveFn_of_hypo_combo {g : E → EReal}
    (h : ∀ (x y : E) (μ ν : ℝ), (μ : EReal) ≤ g x → (ν : EReal) ≤ g y →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → ((a * μ + b * ν : ℝ) : EReal) ≤ g (a • x + b • y)) :
    ConcaveFn g := by
  refine ⟨?_⟩
  rintro ⟨x, μ⟩ hx ⟨y, ν⟩ hy a b ha hb hab
  exact h x y μ ν hx hy a b ha hb hab

/-! ### The sign dictionary for convexity -/

/-- **A function is concave exactly when its negative is convex.** For every
$g : E \to [-\infty, +\infty]$, $g$ is concave if and only if $-g$ is convex.

As for `ConvexAnalysis.hypo_neg`, there is no side condition: the reflection
$(x, \mu) \mapsto (x, -\mu)$ is linear and carries each of the two sets to the other. -/
theorem concaveFn_iff_convexFn_neg {g : E → EReal} : ConcaveFn g ↔ ConvexFn fun x => -(g x) := by
  rw [concaveFn_iff_convex_hypo, convexFn_iff_convex_epi]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [epi_neg]; exact h.linear_preimage (LinearMap.prodMap LinearMap.id (-LinearMap.id))
  · rw [hypo_neg]; exact h.linear_preimage (LinearMap.prodMap LinearMap.id (-LinearMap.id))

/-- If $g$ is concave, then $-g$ is convex. This is the forward direction of
`ConvexAnalysis.concaveFn_iff_convexFn_neg`. -/
theorem ConcaveFn.convexFn_neg {g : E → EReal} (hg : ConcaveFn g) : ConvexFn fun x => -(g x) :=
  concaveFn_iff_convexFn_neg.1 hg

/-- If $f$ is convex, then $-f$ is concave. -/
theorem ConvexFn.concaveFn_neg {f : E → EReal} (hf : ConvexFn f) : ConcaveFn fun x => -(f x) :=
  concaveFn_iff_convexFn_neg.2 (by simpa using hf)

/-! ### Affine perturbations -/

/-- **Adding a real-valued affine function keeps a function convex.** Let
$f : E \to [-\infty, +\infty]$ be convex, and let $l : E \to \mathbb{R}$ satisfy
$l(ax + by) = a\,l(x) + b\,l(y)$ for all $x, y \in E$ and all $a, b \in \mathbb{R}$ with
$a + b = 1$. Then $x \mapsto f(x) + l(x)$ is convex.

The hypothesis is the affine combination law rather than linearity, so the same lemma applies to
a coordinate of a pairing, a projection of a product and an affine function. -/
theorem convexFn_add_coe {f : E → EReal} (hf : ConvexFn f) {l : E → ℝ}
    (hl : ∀ (x y : E) (a b : ℝ), a + b = 1 → l (a • x + b • y) = a * l x + b * l y) :
    ConvexFn (fun x => f x + ((l x : ℝ) : EReal)) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
  have hcomb := hf.epi_combo (EReal.add_coe_le_coe_iff.1 hx)
    (EReal.add_coe_le_coe_iff.1 hy) ha hb hab
  refine EReal.add_coe_le_coe_iff.2 (hcomb.trans (le_of_eq ?_))
  rw [EReal.coe_eq_coe_iff, hl x y a b hab]
  ring

/-- **Translating the argument preserves convexity.** If $f : E \to [-\infty, +\infty]$ is convex
and $a \in E$, then $x \mapsto f(a + x)$ is convex. The epigraph of the translate is a translate
of the epigraph. -/
theorem ConvexFn.comp_add_left {f : E → EReal} (hf : ConvexFn f) (a : E) :
    ConvexFn (fun x => f (a + x)) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy s t hs ht hst => ?_
  have hcombo := hf.epi_combo (x := a + x) (y := a + y) hx hy hs ht hst
  have hkey : s • (a + x) + t • (a + y) = a + (s • x + t • y) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hst, one_smul]
  rwa [hkey] at hcombo

/-! ### Non-negative scalar multiples -/

/-- The **vertical scaling** by $c \in \mathbb{R}$: the linear map $(x, \mu) \mapsto (x, c\mu)$ of
$E \times \mathbb{R}$. For $c > 0$ it relates $\operatorname{epi} f$ and
$\operatorname{epi}(cf)$ (`ConvexAnalysis.epi_coe_mul`). -/
noncomputable def scaleSnd (c : ℝ) : (E × ℝ) →ₗ[ℝ] (E × ℝ) :=
  LinearMap.prod (LinearMap.fst ℝ E ℝ) (c • LinearMap.snd ℝ E ℝ)

/-- The vertical scaling by $c$ sends $(x, \mu)$ to $(x, c\mu)$. -/
theorem scaleSnd_apply (c : ℝ) (p : E × ℝ) : scaleSnd c p = (p.1, c * p.2) := rfl

/-- **The epigraph of a positive multiple.** Let $c > 0$ and $f : E \to [-\infty, +\infty]$. Then
$\operatorname{epi}(cf)$ is the preimage of $\operatorname{epi} f$ under the vertical scaling
$(x, \mu) \mapsto (x, \mu / c)$:
$$(x, \mu) \in \operatorname{epi}(cf) \iff (x, \mu / c) \in \operatorname{epi} f.$$

This makes convexity and closedness of $cf$ arguments about preimages. The identity fails for
$c = 0$, where the left side is $E \times [0, +\infty)$. -/
theorem epi_coe_mul {c : ℝ} (hc : 0 < c) (f : E → EReal) :
    epi (fun x => (c : EReal) * f x) = scaleSnd c⁻¹ ⁻¹' epi f := by
  ext p
  rw [Set.mem_preimage, mem_epi, mem_epi, scaleSnd_apply]
  change (c : EReal) * f p.1 ≤ (p.2 : EReal) ↔ f p.1 ≤ ((c⁻¹ * p.2 : ℝ) : EReal)
  rw [show c⁻¹ * p.2 = p.2 / c from (div_eq_inv_mul p.2 c).symm]
  exact EReal.coe_mul_le_coe_iff hc

/-- **A nonnegative multiple of a convex function is convex.** Let $c \ge 0$ and let
$f : E \to [-\infty, +\infty]$ be convex. Then $cf$ is convex, with the extended-real convention
$0 \cdot (\pm\infty) = 0$. -/
theorem convexFn_coe_mul {c : ℝ} (hc : 0 ≤ c) {f : E → EReal} (hf : ConvexFn f) :
    ConvexFn (fun x => (c : EReal) * f x) := by
  rcases eq_or_lt_of_le hc with h | h
  · have hz : (fun x => (c : EReal) * f x) = fun _ : E => (0 : EReal) := by
      funext x; rw [← h]; simp
    rw [hz]
    refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
    have hμ : (0 : ℝ) ≤ μ := by exact_mod_cast hx
    have hν : (0 : ℝ) ≤ ν := by exact_mod_cast hy
    exact_mod_cast add_nonneg (mul_nonneg ha hμ) (mul_nonneg hb hν)
  · refine ⟨?_⟩
    rw [epi_coe_mul h f]
    exact hf.convex_epi.linear_preimage _

/-! ### Convexity as a strict inequality on values -/

/-- **Convexity in strict inequalities.** A function $f : E \to [-\infty, +\infty]$ is convex if and
only if, for all $x, y \in E$, all $a, b > 0$ with $a + b = 1$ and all real $\alpha, \beta$,
$$f(x) < \alpha,\ f(y) < \beta \implies f(ax + by) < a\alpha + b\beta.$$

The strict inequalities keep $\alpha$ and $\beta$ real, so the undefined $+\infty - \infty$
never arises. -/
theorem convexFn_iff_forall_lt (f : E → EReal) :
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, f x < (α : EReal) → f y < (β : EReal) →
        f (a • x + b • y) < ((a * α + b * β : ℝ) : EReal) := by
  constructor
  · intro hf x y a b ha hb hab α β hx hy
    obtain ⟨α', hxα', hα'⟩ := EReal.exists_between_coe_real hx
    obtain ⟨β', hyβ', hβ'⟩ := EReal.exists_between_coe_real hy
    rw [EReal.coe_lt_coe_iff] at hα' hβ'
    refine lt_of_le_of_lt (hf.epi_combo hxα'.le hyβ'.le ha.le hb.le hab) ?_
    exact_mod_cast add_lt_add (by nlinarith) (by nlinarith)
  · intro h
    refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    rcases eq_or_lt_of_le hb with rfl | hb'
    · have ha1 : a = 1 := by linarith
      subst ha1; simpa using hx
    · refine EReal.le_of_forall_lt_iff_le.1 (fun q hq => le_of_lt ?_)
      replace hq := EReal.coe_lt_coe_iff.1 hq
      have hx' : f x < ((μ + (q - (a * μ + b * ν)) : ℝ) : EReal) :=
        lt_of_le_of_lt hx (by exact_mod_cast (by linarith : μ < μ + (q - (a * μ + b * ν))))
      have hy' : f y < ((ν + (q - (a * μ + b * ν)) : ℝ) : EReal) :=
        lt_of_le_of_lt hy (by exact_mod_cast (by linarith : ν < ν + (q - (a * μ + b * ν))))
      have key := h x y a b ha' hb' hab _ _ hx' hy'
      have harith : a * (μ + (q - (a * μ + b * ν))) + b * (ν + (q - (a * μ + b * ν))) = q := by
        linear_combination (q - (a * μ + b * ν)) * hab
      rwa [harith] at key

/-- **Concavity in strict inequalities.** A function $g : E \to [-\infty, +\infty]$ is concave if
and only if, for all $x, y \in E$, all $a, b > 0$ with $a + b = 1$ and all real $\alpha, \beta$,
$$g(x) > \alpha,\ g(y) > \beta \implies g(ax + by) > a\alpha + b\beta.$$

The strict inequalities keep $\alpha$ and $\beta$ real, so no $+\infty - \infty$ arises and no
hypothesis on $g$ is needed. -/
theorem concaveFn_iff_forall_gt (g : E → EReal) :
    ConcaveFn g ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, (α : EReal) < g x → (β : EReal) < g y →
        ((a * α + b * β : ℝ) : EReal) < g (a • x + b • y) := by
  rw [concaveFn_iff_convexFn_neg, convexFn_iff_forall_lt]
  constructor
  · intro h x y a b ha hb hab α β hx hy
    have hx' : -(g x) < ((-α : ℝ) : EReal) := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_neg_iff.2 hx
    have hy' : -(g y) < ((-β : ℝ) : EReal) := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_neg_iff.2 hy
    have key := h x y a b ha hb hab _ _ hx' hy'
    rw [show (a * -α + b * -β : ℝ) = -(a * α + b * β) by ring, EReal.coe_neg] at key
    exact EReal.neg_lt_neg_iff.1 key
  · intro h x y a b ha hb hab α β hx hy
    have hx' : ((-α : ℝ) : EReal) < g x := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_comm.1 hx
    have hy' : ((-β : ℝ) : EReal) < g y := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_comm.1 hy
    have key := h x y a b ha hb hab _ _ hx' hy'
    rw [show (a * -α + b * -β : ℝ) = -(a * α + b * β) by ring, EReal.coe_neg] at key
    exact EReal.neg_lt_comm.1 key

/-! ### Convexity as an inequality on values -/

/-- **Convexity is the familiar inequality for functions that never take the value $-\infty$.** Let
$f : E \to (-\infty, +\infty]$, that is, $f(x) \neq -\infty$ for every $x$. Then $f$ is convex
if and only if, for all $x, y \in E$ and all $a, b > 0$ with $a + b = 1$,
$$f(ax + by) \le a f(x) + b f(y).$$
-/
theorem convexFn_iff_le {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
  rw [convexFn_iff_forall_lt]
  have hacoe : ∀ {c : ℝ}, 0 < c → (0 : EReal) < (c : EReal) := fun hc => by exact_mod_cast hc
  constructor
  · intro h x y a b ha hb hab
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, EReal.mul_top_of_pos (hacoe ha)]
      rcases eq_top_or_lt_top (f y) with hy | hy
      · rw [hy, EReal.mul_top_of_pos (hacoe hb), EReal.top_add_top]; exact le_top
      · obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf y) hy
        rw [hq, ← EReal.coe_mul, EReal.top_add_coe]; exact le_top
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf x) hx
    rcases eq_top_or_lt_top (f y) with hy | hy
    · rw [hy, EReal.mul_top_of_pos (hacoe hb), hp, ← EReal.coe_mul, EReal.coe_add_top]
      exact le_top
    obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf y) hy
    rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    refine EReal.le_of_forall_lt_iff_le.1 (fun r hr => le_of_lt ?_)
    replace hr := EReal.coe_lt_coe_iff.1 hr
    have hx' : f x < ((p + (r - (a * p + b * q)) : ℝ) : EReal) := by
      rw [hp]; exact_mod_cast (by linarith : p < p + (r - (a * p + b * q)))
    have hy' : f y < ((q + (r - (a * p + b * q)) : ℝ) : EReal) := by
      rw [hq]; exact_mod_cast (by linarith : q < q + (r - (a * p + b * q)))
    have key := h x y a b ha hb hab _ _ hx' hy'
    have harith : a * (p + (r - (a * p + b * q))) + b * (q + (r - (a * p + b * q))) = r := by
      linear_combination (r - (a * p + b * q)) * hab
    rwa [harith] at key
  · intro h x y a b ha hb hab α β hx hy
    obtain ⟨p, hp⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (hf x) (hx.trans (EReal.coe_lt_top α))
    obtain ⟨q, hq⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (hf y) (hy.trans (EReal.coe_lt_top β))
    refine lt_of_le_of_lt (h x y a b ha hb hab) ?_
    rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    rw [hp] at hx; rw [hq] at hy
    have hpα : p < α := by exact_mod_cast hx
    have hqβ : q < β := by exact_mod_cast hy
    exact_mod_cast (by nlinarith : a * p + b * q < a * α + b * β)

/-- **Concavity is the familiar reversed inequality for functions that never take the value
$+\infty$.** Let $g : E \to [-\infty, +\infty)$, that is, $g(x) \neq +\infty$ for every $x$.
Then $g$ is concave if and only if, for all $x, y \in E$ and all $a, b > 0$ with $a + b = 1$,
$$a g(x) + b g(y) \le g(ax + by).$$

The hypothesis makes the right side of the convex form for $-g$ negate to the left side here: on
the extended reals, $-(u + v) = -u + (-v)$ fails when one summand is $+\infty$ and the other is
$-\infty$. -/
theorem concaveFn_iff_le {g : E → EReal} (hg : ∀ x, g x ≠ ⊤) :
    ConcaveFn g ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      (a : EReal) * g x + (b : EReal) * g y ≤ g (a • x + b • y) := by
  have hneg : ∀ x, -(g x) ≠ ⊥ := fun x => by simp [hg x]
  rw [concaveFn_iff_convexFn_neg, convexFn_iff_le hneg]
  refine forall₂_congr fun x y => forall₂_congr fun a b => ?_
  refine forall₃_congr fun ha hb _ => ?_
  rw [EReal.neg_combo ha hb (hg x) (hg y), EReal.neg_le_neg_iff]

/-! ### Level sets and the effective domain -/

/-- **Strict sublevel sets of a convex function are convex.** If $f$ is convex, then
$\{x \mid f(x) < \alpha\}$ is convex for every $\alpha \in [-\infty, +\infty]$. -/
theorem ConvexFn.convex_lt {f : E → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x < α} := by
  intro x hx y hy a b ha hb hab
  refine combo_of_pos (P := fun z => z ∈ {x | f x < α}) hx hy ha hb hab (fun ha' hb' => ?_)
  have hx' : f x < α := hx
  have hy' : f y < α := hy
  change f (a • x + b • y) < α
  obtain ⟨p, hxp, hpα⟩ := EReal.lt_iff_exists_real_btwn.1 hx'
  obtain ⟨q, hyq, hqα⟩ := EReal.lt_iff_exists_real_btwn.1 hy'
  refine lt_of_le_of_lt (hf.epi_combo hxp.le hyq.le ha'.le hb'.le hab) ?_
  induction α with
  | bot => exact absurd hpα (by simp)
  | top => exact EReal.coe_lt_top _
  | coe r =>
    have hp : p < r := by exact_mod_cast hpα
    have hq : q < r := by exact_mod_cast hqα
    have h1 : a * p < a * r := mul_lt_mul_of_pos_left hp ha'
    have h2 : b * q < b * r := mul_lt_mul_of_pos_left hq hb'
    have h3 : a * r + b * r = r := by linear_combination r * hab
    exact_mod_cast (by linarith : a * p + b * q < r)

/-- **Strict superlevel sets of a concave function are convex.** If $g$ is concave, then
$\{x \mid g(x) > \alpha\}$ is convex for every $\alpha \in [-\infty, +\infty]$. -/
theorem ConcaveFn.convex_gt {g : E → EReal} (hg : ConcaveFn g) (α : EReal) :
    Convex ℝ {x | α < g x} := by
  have hset : {x | α < g x} = {x | -(g x) < -α} := by ext x; simp
  rw [hset]
  exact hg.convexFn_neg.convex_lt (-α)

/-- **Sublevel sets of a convex function are convex.** If $f$ is convex, then
$\{x \mid f(x) \le \alpha\}$ is convex for every $\alpha \in [-\infty, +\infty]$. -/
theorem ConvexFn.convex_le {f : E → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x ≤ α} := by
  intro x hx y hy a b ha hb hab
  refine combo_of_pos (P := fun z => z ∈ {x | f x ≤ α}) hx hy ha hb hab (fun ha' hb' => ?_)
  have hx' : f x ≤ α := hx
  have hy' : f y ≤ α := hy
  change f (a • x + b • y) ≤ α
  induction α with
  | bot =>
    refine le_of_eq (le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun r _ => ?_))
    have := hf.epi_combo (μ := r) (ν := r) (hx'.trans bot_le) (hy'.trans bot_le) ha'.le hb'.le hab
    refine this.trans (le_of_eq ?_)
    exact_mod_cast (by linear_combination r * hab : a * r + b * r = r)
  | top => exact le_top
  | coe r =>
    have := hf.epi_combo hx' hy' ha'.le hb'.le hab
    refine this.trans (le_of_eq ?_)
    exact_mod_cast (by linear_combination r * hab : a * r + b * r = r)

/-- **Superlevel sets of a concave function are convex.** If $g$ is concave, then
$\{x \mid g(x) \ge \alpha\}$ is convex for every $\alpha \in [-\infty, +\infty]$. These are the
sets whose closedness characterizes upper semicontinuity. -/
theorem ConcaveFn.convex_ge {g : E → EReal} (hg : ConcaveFn g) (α : EReal) :
    Convex ℝ {x | α ≤ g x} := by
  have hset : {x | α ≤ g x} = {x | -(g x) ≤ -α} := by ext x; simp
  rw [hset]
  exact hg.convexFn_neg.convex_le (-α)

/-- The effective domain $\{x \mid f(x) < +\infty\}$ of a convex function $f$ is convex. -/
theorem ConvexFn.convex_convexDom {f : E → EReal} (hf : ConvexFn f) : Convex ℝ (convexDom f) :=
  hf.convex_lt ⊤

/-- The concave effective domain $\{x \mid g(x) > -\infty\}$ of a concave function $g$ is convex. -/
theorem ConcaveFn.convex_concaveDom {g : E → EReal} (hg : ConcaveFn g) : Convex ℝ (concaveDom g) :=
  hg.convex_gt ⊥

/-! ### The bridges to Mathlib's `ConvexOn` and `ConcaveOn` -/

omit [AddCommGroup E] [Module ℝ E] in
/-- For a set $s \subseteq E$ and a real-valued function $g$ on $E$, the epigraph of the restriction
of $g$ to $s$, extended by $+\infty$, is $\{(x, \mu) \mid x \in s,\ g(x) \le \mu\}$. This is the
form that Mathlib's `convexOn_iff_convex_epigraph` expects. -/
theorem epi_convexRestrict_coe (s : Set E) (g : E → ℝ) :
    epi (convexRestrict s fun x => (g x : EReal)) = {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epi, hp]

omit [AddCommGroup E] [Module ℝ E] in
/-- For a set $s \subseteq E$ and a real-valued function $g$ on $E$, the hypograph of the concave
restriction of $g$ to $s$, extended by $-\infty$, is $\{(x, \mu) \mid x \in s,\ \mu \le g(x)\}$.
This is the form that Mathlib's `concaveOn_iff_convex_hypograph` expects. -/
theorem hypo_concaveRestrict_coe (s : Set E) (g : E → ℝ) :
    hypo (concaveRestrict s fun x => (g x : EReal)) = {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [hypo, hp]

/-- **Real-valued convex functions on a set.** Let $s \subseteq E$ and let $g : E \to \mathbb{R}$.
Then $g$ is convex on $s$ in the sense of Mathlib's `ConvexOn`, which includes convexity of $s$,
if and only if the restriction of $g$ to $s$, extended by $+\infty$, is a convex function on
$E$.

This is the interface through which the surface layer reuses Mathlib. -/
theorem convexOn_iff_convexFn (s : Set E) (g : E → ℝ) :
    ConvexOn ℝ s g ↔ ConvexFn (convexRestrict s fun x => (g x : EReal)) := by
  rw [convexFn_iff_convex_epi, epi_convexRestrict_coe]
  exact ⟨fun h => h.convex_epigraph, fun h => convexOn_of_convex_epigraph h⟩

/-- **Real-valued concave functions on a set.** Let $s \subseteq E$ and let $g : E \to \mathbb{R}$.
Then $g$ is concave on $s$ in the sense of Mathlib's `ConcaveOn`, which includes convexity of
$s$, if and only if the concave restriction of $g$ to $s$, extended by $-\infty$, is a concave
function on $E$. Compare `ConvexAnalysis.convexOn_iff_convexFn`. -/
theorem concaveOn_iff_concaveFn (s : Set E) (g : E → ℝ) :
    ConcaveOn ℝ s g ↔ ConcaveFn (concaveRestrict s fun x => (g x : EReal)) := by
  rw [concaveFn_iff_convex_hypo, hypo_concaveRestrict_coe]
  exact ⟨fun h => h.convex_hypograph, fun h => concaveOn_of_convex_hypograph h⟩

end Module

/-!
### Real-valued functions as extended-real-valued ones

A convex function in a textbook is often real-valued on a convex set $s$ or on the whole space,
while the backbone uses functions with values in $[-\infty, +\infty]$. The dictionary is as follows.
A real-valued $g$ on $s$ is `convexRestrict s fun x => (g x : EReal)`. It is proper with effective
domain $s$ when $s$ is nonempty, and it is convex exactly when $g$ is `ConvexOn ℝ s`. On the whole
space the restriction is not needed. A concave $g$ on $s$ is
`concaveRestrict s fun x => (g x : EReal)`, with the same dictionary.
-/

section RealValued

variable {E : Type*}

/-- The restriction of $f$ to the whole space is $f$. -/
@[simp] theorem convexRestrict_univ (f : E → EReal) : convexRestrict univ f = f :=
  funext fun x => convexRestrict_of_mem (mem_univ x)

/-- The concave restriction of $g$ to the whole space is $g$. -/
@[simp] theorem concaveRestrict_univ (g : E → EReal) : concaveRestrict univ g = g :=
  funext fun x => concaveRestrict_of_mem (mem_univ x)

/-- A real-valued function, read as a function into $[-\infty, +\infty]$, has effective domain $E$.
-/
@[simp] theorem convexDom_coe (g : E → ℝ) : convexDom (fun x => ((g x : ℝ) : EReal)) = univ :=
  eq_univ_of_forall fun _ => mem_convexDom.2 (EReal.coe_lt_top _)

/-- A real-valued function, read as a function into $[-\infty, +\infty]$, has concave effective
domain $E$. -/
@[simp] theorem concaveDom_coe (g : E → ℝ) : concaveDom (fun x => ((g x : ℝ) : EReal)) = univ :=
  eq_univ_of_forall fun _ => mem_concaveDom.2 (EReal.bot_lt_coe _)

/-- Let $E$ be nonempty. A real-valued function on $E$, read as a function into
$[-\infty, +\infty]$, is proper. -/
theorem properConvex_coe [Nonempty E] (g : E → ℝ) : ProperConvex (fun x => ((g x : ℝ) : EReal)) :=
  ⟨by simp, fun _ => EReal.coe_ne_bot _⟩

/-- Let $E$ be nonempty. A real-valued function on $E$, read as a function into
$[-\infty, +\infty]$, is proper in the concave sense. -/
theorem properConcave_coe [Nonempty E] (g : E → ℝ) :
    ProperConcave (fun x => ((g x : ℝ) : EReal)) :=
  ⟨by simp, fun _ => EReal.coe_ne_top _⟩

/-- For a set $s \subseteq E$ and a real-valued function $g$ on $E$, the restriction of $g$ to $s$,
extended by $+\infty$, has effective domain $s$. -/
theorem convexDom_convexRestrict_coe (s : Set E) (g : E → ℝ) :
    convexDom (convexRestrict s fun x => (g x : EReal)) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- For a set $s \subseteq E$ and a real-valued function $g$ on $E$, the concave restriction of $g$
to $s$, extended by $-\infty$, has concave effective domain $s$. -/
theorem concaveDom_concaveRestrict_coe (s : Set E) (g : E → ℝ) :
    concaveDom (concaveRestrict s fun x => (g x : EReal)) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- For a nonempty set $s \subseteq E$ and a real-valued function $g$ on $E$, the restriction of $g$
to $s$, extended by $+\infty$, is proper: its effective domain is $s$, and it never takes the
value $-\infty$. -/
theorem properConvex_convexRestrict_coe {s : Set E} (hs : s.Nonempty) (g : E → ℝ) :
    ProperConvex (convexRestrict s fun x => (g x : EReal)) := by
  refine ⟨by rwa [convexDom_convexRestrict_coe], fun x => ?_⟩
  by_cases hx : x ∈ s
  · rw [convexRestrict_of_mem hx]; exact EReal.coe_ne_bot _
  · rw [convexRestrict_of_notMem hx]; exact top_ne_bot

/-- For a nonempty set $s \subseteq E$ and a real-valued function $g$ on $E$, the concave
restriction of $g$ to $s$, extended by $-\infty$, is proper in the concave sense. -/
theorem properConcave_concaveRestrict_coe {s : Set E} (hs : s.Nonempty) (g : E → ℝ) :
    ProperConcave (concaveRestrict s fun x => (g x : EReal)) := by
  refine ⟨by rwa [concaveDom_concaveRestrict_coe], fun x => ?_⟩
  by_cases hx : x ∈ s
  · rw [concaveRestrict_of_mem hx]; exact EReal.coe_ne_top _
  · rw [concaveRestrict_of_notMem hx]; exact bot_ne_top

variable [AddCommGroup E] [Module ℝ E]

/-- If a real-valued function $g$ is convex on $s$ in the sense of Mathlib's `ConvexOn`, then its
restriction to $s$, extended by $+\infty$, is convex. This is the forward direction of
`ConvexAnalysis.convexOn_iff_convexFn`. -/
theorem _root_.ConvexOn.convexFn_convexRestrict_coe {s : Set E} {g : E → ℝ} (h : ConvexOn ℝ s g) :
    ConvexFn (convexRestrict s fun x => (g x : EReal)) :=
  (convexOn_iff_convexFn s g).1 h

/-- If a real-valued function $g$ is concave on $s$ in the sense of Mathlib's `ConcaveOn`, then its
concave restriction to $s$, extended by $-\infty$, is concave. This is the forward direction of
`ConvexAnalysis.concaveOn_iff_concaveFn`. -/
theorem _root_.ConcaveOn.concaveFn_concaveRestrict_coe {s : Set E} {g : E → ℝ}
    (h : ConcaveOn ℝ s g) : ConcaveFn (concaveRestrict s fun x => (g x : EReal)) :=
  (concaveOn_iff_concaveFn s g).1 h

/-- A real-valued function that is convex on the whole space, in the sense of Mathlib's `ConvexOn`,
is convex as a function into $[-\infty, +\infty]$. -/
theorem _root_.ConvexOn.convexFn_coe {g : E → ℝ} (h : ConvexOn ℝ univ g) :
    ConvexFn fun x => (g x : EReal) := by
  simpa using h.convexFn_convexRestrict_coe

/-- A real-valued function that is concave on the whole space, in the sense of Mathlib's
`ConcaveOn`, is concave as a function into $[-\infty, +\infty]$. -/
theorem _root_.ConcaveOn.concaveFn_coe {g : E → ℝ} (h : ConcaveOn ℝ univ g) :
    ConcaveFn fun x => (g x : EReal) := by
  simpa using h.concaveFn_concaveRestrict_coe

end RealValued

/-! ### Jensen's inequality for finite convex combinations -/

section Jensen

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal}

/-- **Jensen's inequality** for a convex function with values in $[-\infty, +\infty]$, in the form
that the epigraph gives. Let $f$ be convex, let $t$ be a finite index set, and let $u_j \in E$
and $m_j \in \mathbb{R}$ with $f(u_j) \le m_j$ for $j \in t$. Let $w_j \ge 0$ with
$\sum_{j \in t} w_j = 1$. Then
$$f\Bigl(\sum_{j \in t} w_j u_j\Bigr) \le \sum_{j \in t} w_j m_j.$$

The bound is by reals $m_j$, not by the values $f(u_j)$. The form
$f(\sum_j w_j u_j) \le \sum_j w_j f(u_j)$ needs the convention $0 \cdot (+\infty) = 0$ at
indices with $w_j = 0$ and $f(u_j) = +\infty$. The alias is `ConvexAnalysis.jensen`. -/
theorem ConvexFn.sum_le {ι : Type*} (hf : ConvexFn f) (t : Finset ι) (u : ι → E) (m wt : ι → ℝ)
    (hm : ∀ j ∈ t, f (u j) ≤ ((m j : ℝ) : EReal)) (hw : ∀ j ∈ t, 0 ≤ wt j)
    (hw1 : ∑ j ∈ t, wt j = 1) :
    f (∑ j ∈ t, wt j • u j) ≤ ((∑ j ∈ t, wt j * m j : ℝ) : EReal) := by
  have hmem := hf.convex_epi.sum_mem hw hw1 (fun j hj => mk_mem_epi.2 (hm j hj))
  have hsum : (∑ j ∈ t, wt j • ((u j, m j) : E × ℝ))
      = ((∑ j ∈ t, wt j • u j, ∑ j ∈ t, wt j * m j) : E × ℝ) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, smul_eq_mul]
  rw [hsum] at hmem
  exact mk_mem_epi.1 hmem

end Jensen

end ConvexAnalysis
