/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Recession.Cone

/-!
# Recession functions

Let $E$ be a real vector space and $f : E \to [-\infty, +\infty]$. Write $\operatorname{epi} f =
\{(x, \mu) \in E \times \mathbb{R} : f(x) \le \mu\}$ for the epigraph,
$\operatorname{dom} f = \{x : f(x) < +\infty\}$ for the effective domain, $0^+C = \{y : x + a y \in
C \text{ for all } x \in C,\ a \ge 0\}$ for the recession cone of a set $C$, and
$\operatorname{lin} C = 0^+C \cap (-0^+C)$ for its lineality space. The **recession function**
$f0^+$ of $f$ is the function whose epigraph is $0^+(\operatorname{epi} f)$. It measures how fast
$f$ can grow in each direction: $(f0^+)(y) \le \nu$ means that $f(x + a y) \le f(x) + a\nu$ for all
$x \in E$ and $a \ge 0$. The directions $y$ with $(f0^+)(y) \le 0$ form the **recession cone** of
$f$, the directions with $(f0^+)(y) \le 0$ and $(f0^+)(-y) \le 0$ form its **constancy space**, and
the directions with $(f0^+)(-y) = -(f0^+)(y)$ form its **lineality space**. The presentation follows
[rockafellar1970convex], §8.

Most of the theory needs no topology on $E$. Closedness of $\operatorname{epi} f$ enters exactly
where a property must not depend on a base point $x$. For a convex $f$ with closed epigraph, the
recession condition can be tested along one half-line, and $(f0^+)(y)$ is the limit of the
difference quotients $(f(x + a y) - f(x))/a$ as $a \to +\infty$, for any one
$x \in \operatorname{dom} f$.

## Main definitions

* `ConvexAnalysis.recessionFn`: the recession function $f0^+$, whose epigraph is
  $0^+(\operatorname{epi} f)$.
* `ConvexAnalysis.recessionConeFn` and `ConvexAnalysis.recessionPointedConeFn`: the recession cone
  $\{y : (f0^+)(y) \le 0\}$ of $f$, as a set and as a pointed cone.
* `ConvexAnalysis.constancySpace` and `ConvexAnalysis.constancySubmodule`: the constancy space of
  $f$, as a set and as a subspace.
* `ConvexAnalysis.linealitySpaceFn`, `ConvexAnalysis.linealitySubmoduleFn` and
  `ConvexAnalysis.linealityFn`: the lineality space of $f$, as a set and as a subspace, and its
  dimension.

## Main results

* `ConvexAnalysis.epi_recessionFn`: $\operatorname{epi}(f0^+) = 0^+(\operatorname{epi} f)$ for every
  $f$.
* `ConvexAnalysis.posHomogeneous_recessionFn`, `ConvexAnalysis.convexFn_recessionFn`,
  `ConvexAnalysis.properConvex_recessionFn` and `ConvexAnalysis.closedConvex_recessionFn`: $f0^+$ is
  positively homogeneous and convex for every $f$, proper when $f$ is proper, and closed when
  moreover $\operatorname{epi} f$ is closed.
* `ConvexAnalysis.recessionFn_apply_eq_iSup_sub` and
  `ConvexAnalysis.recessionFn_apply_eq_iSup_inv_mul`: for a convex $f$ that is nowhere $-\infty$,
  $(f0^+)(y) = \sup\{f(x + y) - f(x) : x \in \operatorname{dom} f\}$; if moreover
  $\operatorname{epi} f$ is closed, then $(f0^+)(y) = \sup_{a > 0} (f(x + a y) - f(x))/a$ for any
  one $x \in \operatorname{dom} f$. Together with the previous item, these formulas form Theorem 8.5
  of [rockafellar1970convex].
* `ConvexAnalysis.recessionFn_isLeast`: for a proper convex $f$, $f0^+$ is the least function $h$
  with $f(z) \le f(x) + h(z - x)$ for all $x, z$.
* `ConvexAnalysis.tendsto_smulRight_recessionFn`: for a closed proper convex $f$ and
  $y \in \operatorname{dom} f$, $(f0^+)(y) = \lim_{a \downarrow 0} (fa)(y)$.
* `ConvexAnalysis.antitone_along_of_liminf_lt_top` and
  `ConvexAnalysis.forall_antitone_iff_recessionFn_nonpos`: a convex $f$ whose $\liminf$ along a
  half-line is less than $+\infty$ is nonincreasing along the whole line, and $(f0^+)(y) \le 0$
  holds exactly when $a \mapsto f(x + a y)$ is nonincreasing for every $x$.
* `ConvexAnalysis.ConvexFn.eq_of_le_on_affineSubspace`: a convex function that is bounded above on
  an affine set is constant on it.
* `ConvexAnalysis.recessionCone_setOf_le` and `ConvexAnalysis.linealitySpace_setOf_le`: for a convex
  $f$ with closed epigraph, every nonempty level set $\{x : f(x) \le \alpha\}$ has the recession
  cone of $f$ as its recession cone and the constancy space of $f$ as its lineality space.
* `ConvexAnalysis.isBounded_setOf_le`: in finite dimension, if one nonempty level set of a convex
  $f$ with closed epigraph is bounded, then every nonempty level set is bounded.
* `ConvexAnalysis.lt_recessionFn_of_isBounded_convexDom`: if $\operatorname{dom} f$ is nonempty and
  bounded, then $(f0^+)(w) > 0$ for every $w \neq 0$.
* `ConvexAnalysis.forall_eq_add_iff_mk_mem_linealitySpace_epi` and
  `ConvexAnalysis.linealitySpaceFn_eq_image`: $f(x + a y) = f(x) + a\nu$ for all $x$ and all real
  $a$ exactly when $(y, \nu) \in \operatorname{lin}(\operatorname{epi} f)$; for proper $f$, the
  projection of $\operatorname{lin}(\operatorname{epi} f)$ onto $E$ is the lineality space of $f$.

## Implementation notes

* Functions take values in `EReal`, the extended real line $[-\infty, +\infty]$.
* The recession function is defined as `ConvexAnalysis.ofEpi` of $0^+(\operatorname{epi} f)$, that
  is, $(f0^+)(y) = \inf\{\nu : (y, \nu) \in 0^+(\operatorname{epi} f)\}$. Rockafellar defines $f0^+$
  by its epigraph; here the identity of the epigraphs is the theorem
  `ConvexAnalysis.epi_recessionFn`, which holds with no hypothesis on $f$.
* `ConvexAnalysis.ProperConvex f` says only that $f$ is proper: $f(x) < +\infty$ for some $x$, and
  $f$ never takes the value $-\infty$. Convexity is the separate hypothesis
  `ConvexAnalysis.ConvexFn f`, which says that $\operatorname{epi} f$ is convex. Several results
  need neither, or need only that $f$ is nowhere $-\infty$.
* Closedness is mostly the hypothesis `IsClosed (epi f)`, not `ConvexAnalysis.ClosedConvex f`. The
  closure `ConvexAnalysis.convexCl` replaces a function by the constant $-\infty$ when its lower
  semicontinuous hull takes the value $-\infty$ somewhere, so `ClosedConvex f` is a different
  condition for improper $f$. The results about a closed proper convex function take the hypothesis
  `ConvexAnalysis.ClosedProperConvexFn f`, which contains `ClosedConvex f`.
* The right scalar multiple $fa$ is `ConvexAnalysis.smulRight f a`. For $a > 0$ it is
  $(fa)(x) = a f(a^{-1} x)$.
* The lineality `ConvexAnalysis.linealityFn` is a `Module.finrank`, which is $0$ for an
  infinite-dimensional subspace.
-/

open Filter Pointwise Set Topology

namespace ConvexAnalysis

/-! ### The recession function -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f g : E → EReal} {x y : E} {ν : ℝ}

/-- Let $f : E \to [-\infty, +\infty]$. The **recession function** $f0^+$ of $f$ is the function
whose epigraph is the recession cone $0^+(\operatorname{epi} f)$ of the epigraph of $f$:
$$(f0^+)(y) = \inf\{\nu \in \mathbb{R} : (y, \nu) \in 0^+(\operatorname{epi} f)\},$$ with
$\inf \emptyset = +\infty$.

The definition is `ConvexAnalysis.ofEpi` of $0^+(\operatorname{epi} f)$. It can be written down
before one knows that this cone is an epigraph. `ConvexAnalysis.epi_recessionFn` then proves
$\operatorname{epi}(f0^+) = 0^+(\operatorname{epi} f)$, which Rockafellar takes as the
definition. -/
noncomputable def recessionFn (f : E → EReal) : E → EReal := ofEpi (recessionCone (epi f))

/-- Let $y \in E$ and $\nu \in \mathbb{R}$. Then $(y, \nu) \in 0^+(\operatorname{epi} f)$ if and
only if $f(x + a y) \le \mu + a\nu$ for all $x \in E$, all real $\mu$ with $f(x) \le \mu$, and
all $a \ge 0$. -/
theorem mk_mem_recessionCone_epi :
    ((y, ν) : E × ℝ) ∈ recessionCone (epi f) ↔
      ∀ (x : E) (μ : ℝ), f x ≤ (μ : EReal) →
        ∀ a : ℝ, 0 ≤ a → f (x + a • y) ≤ ((μ + a * ν : ℝ) : EReal) := by
  constructor
  · intro h x μ hx a ha
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using h (x, μ) (mk_mem_epi.2 hx) a ha
  · rintro h ⟨x, μ⟩ hp a ha
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using h x μ (mk_mem_epi.1 hp) a ha

/-- Let $y \in E$ and $\nu \in \mathbb{R}$. Then $(y, \nu) \in 0^+(\operatorname{epi} f)$ if and
only if $$f(x + a y) \le f(x) + a\nu \quad \text{for all } x \in E \text{ and } a \ge 0,$$ in
the arithmetic of $[-\infty, +\infty]$.

The equivalence holds also where $f$ is infinite, because $-\infty + r = -\infty$ for real $r$,
which matches the condition that $f(x) \le \mu$ for every real $\mu$. -/
theorem mk_mem_recessionCone_epi_iff :
    ((y, ν) : E × ℝ) ∈ recessionCone (epi f) ↔
      ∀ (x : E) (a : ℝ), 0 ≤ a → f (x + a • y) ≤ f x + ((a * ν : ℝ) : EReal) := by
  rw [mk_mem_recessionCone_epi]
  constructor
  · intro h x a ha
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top
    by_cases hb : f x = ⊥
    · rw [hb, EReal.bot_add, le_bot_iff]
      refine le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun s _ => ?_)
      simpa using h x (s - a * ν) (hb ▸ bot_le) a ha
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb hx
      rw [hr, ← EReal.coe_add]
      exact h x r hr.le a ha
  · intro h x μ hx a ha
    rw [EReal.coe_add]
    exact (h x a ha).trans (add_le_add hx le_rfl)

/-- If $(y, \nu) \in 0^+(\operatorname{epi} f)$ and $\nu \le \rho$, then
$(y, \rho) \in 0^+(\operatorname{epi} f)$. Thus the vertical sections of
$0^+(\operatorname{epi} f)$ are closed upward.

This is one of the two conditions of `ConvexAnalysis.isEpiLike_iff_forall`. -/
theorem mk_mem_recessionCone_epi_of_le (h : ((y, ν) : E × ℝ) ∈ recessionCone (epi f)) {ρ : ℝ}
    (hνρ : ν ≤ ρ) : ((y, ρ) : E × ℝ) ∈ recessionCone (epi f) := by
  rw [mk_mem_recessionCone_epi] at h ⊢
  intro x μ hx a ha
  refine (h x μ hx a ha).trans ?_
  have hstep : μ + a * ν ≤ μ + a * ρ := by nlinarith
  exact_mod_cast hstep

/-- For every $f : E \to [-\infty, +\infty]$, the recession cone $0^+(\operatorname{epi} f)$ is the
epigraph of a function.

The vertical sections of the cone are closed upward, because $\mu + a\nu$ increases with $\nu$.
They are closed from below, because $f(x + a y) \le \mu + a\rho$ for every $\rho > \nu$ implies
$f(x + a y) \le \mu + a\nu$. Neither property needs $\operatorname{epi} f$ to be closed or
convex. -/
theorem isEpiLike_recessionCone_epi (f : E → EReal) : IsEpiLike (recessionCone (epi f)) := by
  refine isEpiLike_of_forall (fun _ _ _ hμ hμν => mk_mem_recessionCone_epi_of_le hμ hμν)
    fun y ν h => ?_
  rw [mk_mem_recessionCone_epi]
  intro x μ hx a ha
  refine EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_
  replace hq := EReal.coe_lt_coe_iff.1 hq
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_smul, add_zero, zero_mul] at hq ⊢
    exact lt_of_le_of_lt hx (by exact_mod_cast hq)
  · have hd : 0 < (q - (μ + a * ν)) / (2 * a) := div_pos (by linarith) (by linarith)
    have hle := mk_mem_recessionCone_epi.1 (h (ν + (q - (μ + a * ν)) / (2 * a)) (by linarith))
      x μ hx a ha
    refine lt_of_le_of_lt hle ?_
    have heq : μ + a * (ν + (q - (μ + a * ν)) / (2 * a)) = μ + a * ν + (q - (μ + a * ν)) / 2 := by
      field_simp
      ring
    rw [heq]
    exact_mod_cast (by linarith : μ + a * ν + (q - (μ + a * ν)) / 2 < q)

/-- For every $f : E \to [-\infty, +\infty]$, the epigraph of the recession function is the
recession cone of the epigraph: $$\operatorname{epi}(f0^+) = 0^+(\operatorname{epi} f).$$

Rockafellar takes this identity as the definition of $f0^+$. Here it is a theorem, with no
hypothesis on $f$. -/
@[simp]
theorem epi_recessionFn (f : E → EReal) : epi (recessionFn f) = recessionCone (epi f) :=
  epi_ofEpi (isEpiLike_recessionCone_epi f)

/-- For $y \in E$ and $\nu \in \mathbb{R}$, $(f0^+)(y) \le \nu$ if and only if
$(y, \nu) \in 0^+(\operatorname{epi} f)$. -/
theorem recessionFn_le_coe_iff :
    recessionFn f y ≤ (ν : EReal) ↔ ((y, ν) : E × ℝ) ∈ recessionCone (epi f) := by
  rw [← epi_recessionFn]
  exact mk_mem_epi.symm

/-- For $g : E \to [-\infty, +\infty]$, $g \le f0^+$ pointwise if and only if
$0^+(\operatorname{epi} f) \subseteq \operatorname{epi} g$. Thus $f0^+$ is the greatest function
whose epigraph contains $0^+(\operatorname{epi} f)$. -/
theorem le_recessionFn_iff : g ≤ recessionFn f ↔ recessionCone (epi f) ⊆ epi g :=
  subset_epi_iff_le_ofEpi.symm

/-- For $y \in E$ and $\nu \in \mathbb{R}$, $(f0^+)(y) \le \nu$ if and only if
$f(x + a y) \le f(x) + a\nu$ for all $x \in E$ and $a \ge 0$. -/
theorem recessionFn_le_coe_iff_forall :
    recessionFn f y ≤ (ν : EReal) ↔
      ∀ (x : E) (a : ℝ), 0 ≤ a → f (x + a • y) ≤ f x + ((a * ν : ℝ) : EReal) := by
  rw [recessionFn_le_coe_iff, mk_mem_recessionCone_epi_iff]

/-- Let $f$ be convex, $y \in E$ and $\nu \in \mathbb{R}$. Then $(f0^+)(y) \le \nu$ if and only if
$f(x + y) \le f(x) + \nu$ for all $x \in E$. Thus for a convex function it is enough to test the
recession inequality at $a = 1$.

The reason is that a convex set recedes in a direction as soon as it is stable under one step in
that direction. -/
theorem recessionFn_le_coe_iff_of_convexFn (hf : ConvexFn f) :
    recessionFn f y ≤ (ν : EReal) ↔ ∀ x : E, f (x + y) ≤ f x + (ν : EReal) := by
  rw [recessionFn_le_coe_iff, mem_recessionCone_iff_forall_add_mem hf.convex_epi]
  constructor
  · intro h x
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top
    by_cases hb : f x = ⊥
    · rw [hb, EReal.bot_add, le_bot_iff]
      refine le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun s _ => ?_)
      have hmem := h (x, s - ν) (mk_mem_epi.2 (hb ▸ bot_le))
      rw [Prod.mk_add_mk] at hmem
      simpa using mk_mem_epi.1 hmem
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb hx
      have hmem := h (x, r) (mk_mem_epi.2 hr.le)
      rw [Prod.mk_add_mk] at hmem
      rw [hr, ← EReal.coe_add]
      exact mk_mem_epi.1 hmem
  · rintro h ⟨x, μ⟩ hp
    rw [Prod.mk_add_mk]
    refine mk_mem_epi.2 ?_
    rw [EReal.coe_add]
    exact (h x).trans (add_le_add (mk_mem_epi.1 hp) le_rfl)

/-! ### The recession function is positively homogeneous and convex -/

/-- Let $C \subseteq E$ and $a > 0$. Then $a \cdot 0^+C = 0^+C$, so $0^+C$ is a cone.

This is the scaling property of `ConvexAnalysis.recessionPointedCone`, in the form
$a \cdot s = s$ that `ConvexAnalysis.posHomogeneous_iff_isCone_epi` requires. -/
theorem smul_recessionCone {a : ℝ} (ha : 0 < a) (C : Set E) :
    a • recessionCone C = recessionCone C := by
  refine Set.Subset.antisymm ?_ fun z hz => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact smul_mem_recessionCone ha.le hw
  · exact ⟨a⁻¹ • z, smul_mem_recessionCone (by positivity) hz, smul_inv_smul₀ ha.ne' z⟩

/-- For every $f : E \to [-\infty, +\infty]$, the recession function is positively homogeneous:
$$(f0^+)(a y) = a \, (f0^+)(y) \quad \text{for all } a > 0 \text{ and } y \in E.$$

No hypothesis on $f$ is needed, because $0^+(\operatorname{epi} f)$ is a cone for every $f$.
This is part of Theorem 8.5 of [rockafellar1970convex]. -/
theorem posHomogeneous_recessionFn (f : E → EReal) : PosHomogeneous (recessionFn f) := by
  rw [posHomogeneous_iff_isCone_epi]
  intro a ha
  rw [epi_recessionFn]
  exact smul_recessionCone ha (epi f)

/-- For every $f : E \to [-\infty, +\infty]$, the recession function $f0^+$ is convex, that is,
$\operatorname{epi}(f0^+)$ is convex.

No hypothesis on $f$ is needed, because $0^+C$ is convex for every set $C$, convex or not. This
is part of Theorem 8.5 of [rockafellar1970convex]. -/
theorem convexFn_recessionFn (f : E → EReal) : ConvexFn (recessionFn f) :=
  convexFn_iff_convex_epi.2 (by rw [epi_recessionFn]; exact convex_recessionCone (epi f))

/-- For every $f$, the carrier of the pointed cone `ConvexAnalysis.recessionPointedCone (epi f)` is
$\operatorname{epi}(f0^+)$.

The two theorems above also give $\operatorname{epi}(f0^+)$ as a `ConvexCone ℝ (E × ℝ)`, through
`ConvexAnalysis.PosHomogeneous.epiCone`. The pointed cone `ConvexAnalysis.recessionPointedCone`
carries the same set with no hypothesis, so this is the bundled form recorded here. -/
@[simp]
theorem coe_recessionPointedCone_epi (f : E → EReal) :
    (recessionPointedCone (epi f) : Set (E × ℝ)) = epi (recessionFn f) := by
  rw [coe_recessionPointedCone, epi_recessionFn]

/-- For every $f$, $(f0^+)(0) \le 0$, because $0$ lies in the recession cone of every set. -/
theorem recessionFn_apply_zero_le (f : E → EReal) : recessionFn f 0 ≤ 0 := by
  have h : ((0 : E), (0 : ℝ)) ∈ recessionCone (epi f) := by
    rw [Prod.mk_zero_zero]
    exact zero_mem_recessionCone (epi f)
  simpa using recessionFn_le_coe_iff.2 h

/-- Let $f$ be proper. Then $(f0^+)(y) \neq -\infty$ for every $y \in E$.

Both parts of properness are needed. For $f \equiv +\infty$ the epigraph is empty,
$0^+\emptyset = E \times \mathbb{R}$, and $f0^+ \equiv -\infty$. If $f$ takes the value
$-\infty$ somewhere, a vertical section of $0^+(\operatorname{epi} f)$ can be all of
$\mathbb{R}$. -/
theorem recessionFn_ne_bot (hp : ProperConvex f) (y : E) : recessionFn f y ≠ ⊥ := by
  intro hbot
  obtain ⟨x, hx⟩ := hp.convexDom_nonempty
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  refine hp.ne_bot (x + y) (le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun s _ => ?_))
  have hmem : ((y, s - r) : E × ℝ) ∈ recessionCone (epi f) :=
    recessionFn_le_coe_iff.1 (hbot ▸ bot_le)
  have hle := mk_mem_recessionCone_epi.1 hmem x r hr.le 1 zero_le_one
  simpa using hle

/-- If $f$ is proper, then $(f0^+)(0) = 0$. -/
@[simp]
theorem recessionFn_apply_zero (hp : ProperConvex f) : recessionFn f 0 = 0 := by
  refine le_antisymm (recessionFn_apply_zero_le f) (EReal.le_of_forall_coe_le fun r hr => ?_)
  obtain ⟨x, hx⟩ := hp.convexDom_nonempty
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hle := mk_mem_recessionCone_epi.1 (recessionFn_le_coe_iff.1 hr) x s hs.le 1 zero_le_one
  rw [smul_zero, add_zero, hs] at hle
  have hss : s ≤ s + 1 * r := by exact_mod_cast hle
  exact_mod_cast (by linarith : (0 : ℝ) ≤ r)

/-- Let $f : E \to [-\infty, +\infty]$ be proper, that is, $f(x) < +\infty$ for some $x$ and $f$
never takes the value $-\infty$. Then the recession function $f0^+$ is proper.

The hypothesis `ConvexAnalysis.ProperConvex f` is properness alone; convexity of $f$ is not
assumed. This is part of Theorem 8.5 of [rockafellar1970convex]. -/
theorem properConvex_recessionFn (hp : ProperConvex f) : ProperConvex (recessionFn f) where
  convexDom_nonempty :=
      ⟨0, by rw [mem_convexDom, recessionFn_apply_zero hp]; exact EReal.zero_lt_top⟩
  ne_bot := recessionFn_ne_bot hp

/-! ### The difference formula and the least-function property -/

omit [Module ℝ E] in
/-- Let $f$ never take the value $-\infty$, and let $y \in E$ and $r \in \mathbb{R}$. Then
$f(x + y) \le f(x) + r$ for all $x \in E$ if and only if $f(x + y) - f(x) \le r$ for all
$x \in \operatorname{dom} f$.

The hypothesis on $f$ makes $f(x)$ real on $\operatorname{dom} f$. Off $\operatorname{dom} f$
the first inequality holds trivially, because $+\infty + r = +\infty$, so only points of
$\operatorname{dom} f$ carry a condition. -/
theorem forall_le_add_coe_iff (hbot : ∀ x, f x ≠ ⊥) {r : ℝ} :
    (∀ x : E, f (x + y) ≤ f x + (r : EReal)) ↔ ∀ x ∈ convexDom f, f (x + y) - f x ≤
        (r : EReal) := by
  constructor
  · intro h x hx
    obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
    rw [hs, EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot s))
      (Or.inl (EReal.coe_ne_top s)), add_comm ((r : ℝ) : EReal) ((s : ℝ) : EReal), ← hs]
    exact h x
  · intro h x
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top
    · obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
      have hstep := h x hx
      rw [hs] at hstep ⊢
      rwa [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot s))
        (Or.inl (EReal.coe_ne_top s)),
        add_comm ((r : ℝ) : EReal) ((s : ℝ) : EReal)] at hstep

/-- The **difference formula**. Let $f$ be convex and never $-\infty$. Then for every $y \in E$,
$$(f0^+)(y) = \sup\{f(x + y) - f(x) : x \in \operatorname{dom} f\}.$$

Convexity lets the recession condition be tested at $a = 1$ only, and the hypothesis that $f$ is
never $-\infty$ gives the differences a meaning. Properness is not needed: for
$f \equiv +\infty$ both sides are $-\infty$, the supremum because
$\operatorname{dom} f = \emptyset$. This formula is part of Theorem 8.5 of
[rockafellar1970convex]. -/
theorem recessionFn_apply_eq_iSup_sub (hf : ConvexFn f) (hbot : ∀ x, f x ≠ ⊥) (y : E) :
    recessionFn f y = ⨆ x ∈ convexDom f, (f (x + y) - f x) := by
  refine EReal.eq_of_forall_le_coe_iff fun r => ?_
  rw [recessionFn_le_coe_iff_of_convexFn hf, forall_le_add_coe_iff hbot, iSup₂_le_iff]

/-- Let $f$ be proper and convex. Then $f(x + y) \le f(x) + (f0^+)(y)$ for all $x, y \in E$. -/
theorem le_add_recessionFn (hf : ConvexFn f) (hp : ProperConvex f) (x y : E) :
    f (x + y) ≤ f x + recessionFn f y := by
  rcases eq_top_or_lt_top (f x) with hx | hx
  · rw [hx, EReal.top_add_of_ne_bot (recessionFn_ne_bot hp y)]
    exact le_top
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hterm : f (x + y) - f x ≤ recessionFn f y := by
    rw [recessionFn_apply_eq_iSup_sub hf hp.ne_bot]
    exact le_iSup₂ (f := fun x' (_ : x' ∈ convexDom f) => f (x' + y) - f x') x hx
  calc f (x + y) = f (x + y) - f x + f x := by rw [hs]; exact EReal.sub_add_cancel.symm
    _ ≤ recessionFn f y + f x := add_le_add hterm le_rfl
    _ = f x + recessionFn f y := add_comm _ _

/-- Let $f$ be proper and convex. Then $f0^+$ is the least function $h : E \to [-\infty, +\infty]$
such that $$f(z) \le f(x) + h(z - x) \quad \text{for all } x, z \in E.$$ That is, $f0^+$ has
this property, and $f0^+ \le h$ pointwise for every $h$ with this property. -/
theorem recessionFn_isLeast (hf : ConvexFn f) (hp : ProperConvex f) :
    IsLeast {h : E → EReal | ∀ x z : E, f z ≤ f x + h (z - x)} (recessionFn f) := by
  refine ⟨fun x z => ?_, fun h hh y => ?_⟩
  · have hxz : x + (z - x) = z := by abel
    have hle := le_add_recessionFn hf hp x (z - x)
    rwa [hxz] at hle
  · rw [recessionFn_apply_eq_iSup_sub hf hp.ne_bot]
    refine iSup₂_le fun x hx => ?_
    obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    have hstep := hh x (x + y)
    rw [add_sub_cancel_left, hs, add_comm ((s : ℝ) : EReal) (h y)] at hstep
    rw [hs]
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot s))
      (Or.inl (EReal.coe_ne_top s))).2 hstep

/-! ### Directions of recession -/

/-- If $(f0^+)(y) \le 0$, then $f(x + a y) \le f(x)$ for all $x \in E$ and $a \ge 0$: moving in the
direction $y$ never increases $f$. -/
theorem add_smul_le_of_recessionFn_nonpos (h : recessionFn f y ≤ 0) (x : E) {a : ℝ} (ha : 0 ≤ a) :
    f (x + a • y) ≤ f x := by
  have h0 : recessionFn f y ≤ ((0 : ℝ) : EReal) := by rwa [EReal.coe_zero]
  simpa using recessionFn_le_coe_iff_forall.1 h0 x a ha

/-- $(f0^+)(y) \le 0$ if and only if $f(x + a y) \le f(x)$ for all $x \in E$ and $a \ge 0$. -/
theorem recessionFn_nonpos_iff :
    recessionFn f y ≤ 0 ↔ ∀ (x : E) (a : ℝ), 0 ≤ a → f (x + a • y) ≤ f x := by
  refine ⟨fun h x a ha => add_smul_le_of_recessionFn_nonpos h x ha, fun h => ?_⟩
  have h0 : recessionFn f y ≤ ((0 : ℝ) : EReal) :=
    recessionFn_le_coe_iff_forall.2 fun x a ha => by simpa using h x a ha
  rwa [EReal.coe_zero] at h0

/-- For every $f : E \to [-\infty, +\infty]$ and $y \in E$, the function $a \mapsto f(x + a y)$ on
$\mathbb{R}$ is nonincreasing for every $x \in E$ if and only if $(f0^+)(y) \le 0$.

This equivalence needs no hypothesis on $f$, neither convexity nor properness. The usual
statement assumes $f$ proper and convex, because it is stated together with other implications
that need these hypotheses. -/
theorem forall_antitone_iff_recessionFn_nonpos :
    (∀ x : E, Antitone fun a : ℝ => f (x + a • y)) ↔ recessionFn f y ≤ 0 := by
  rw [recessionFn_nonpos_iff]
  constructor
  · intro h x a ha
    have hstep := h x ha
    simpa using hstep
  · intro h x a₁ a₂ h12
    have hcoef : a₁ + (a₂ - a₁) = a₂ := by ring
    have hstep := h (x + a₁ • y) (a₂ - a₁) (by linarith)
    rwa [add_assoc, ← add_smul, hcoef] at hstep

/-- Let $f$ be convex and let $x, y \in E$. If $$\liminf_{a \to +\infty} f(x + a y) < +\infty,$$
then $a \mapsto f(x + a y)$ is nonincreasing on all of $\mathbb{R}$. Thus a convex function that
does not tend to $+\infty$ along one half-line is nonincreasing along the whole line.

The proof is elementary and needs no closure, no relative interior and no finite dimension. Let
$\lambda_1 < \lambda_2$ and let $\mu$ be a real bound on $f(x + \lambda_1 y)$. For a large
$\lambda$ with $f(x + \lambda y) < \alpha$, where $\alpha$ is a fixed real number, the point
$x + \lambda_2 y$ is a convex combination of $x + \lambda_1 y$ and $x + \lambda y$; the weight
on the second point tends to $0$ as $\lambda \to \infty$, so convexity gives
$f(x + \lambda_2 y) \le \mu$. -/
theorem antitone_along_of_liminf_lt_top (hf : ConvexFn f) (x y : E)
    (h : liminf (fun a : ℝ => f (x + a • y)) atTop < ⊤) :
    Antitone fun a : ℝ => f (x + a • y) := by
  obtain ⟨α, hα, -⟩ := EReal.lt_iff_exists_real_btwn.1 h
  have hfreq : ∃ᶠ a : ℝ in atTop, f (x + a • y) < (α : EReal) :=
    frequently_lt_of_liminf_lt (h := hα)
  intro a₁ a₂ h12
  refine EReal.le_of_forall_coe_le fun μ hμ => ?_
  refine EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_
  replace hq := EReal.coe_lt_coe_iff.1 hq
  rcases h12.eq_or_lt with rfl | hlt
  · exact lt_of_le_of_lt hμ (by exact_mod_cast hq)
  have hp0 : (0 : ℝ) < q - μ := by linarith
  obtain ⟨l, hlα, hlB⟩ := (hfreq.and_eventually (eventually_ge_atTop
    (max (a₂ + 1) (a₁ + (a₂ - a₁) * (|α - μ| + 1) / (q - μ))))).exists
  have hl2 : a₂ + 1 ≤ l := le_trans (le_max_left _ _) hlB
  have hl1 : a₁ + (a₂ - a₁) * (|α - μ| + 1) / (q - μ) ≤ l := le_trans (le_max_right _ _) hlB
  have hlpos : (0 : ℝ) < l - a₁ := by linarith
  have ht0 : (0 : ℝ) < (a₂ - a₁) / (l - a₁) := div_pos (by linarith) hlpos
  have ht1 : (a₂ - a₁) / (l - a₁) < 1 := (div_lt_one hlpos).2 (by linarith)
  have hmul : (a₂ - a₁) / (l - a₁) * (l - a₁) = a₂ - a₁ := div_mul_cancel₀ _ hlpos.ne'
  have htc : (a₂ - a₁) / (l - a₁) * (|α - μ| + 1) ≤ q - μ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hlpos]
    have hstep := (div_le_iff₀ hp0).1
      (by linarith : (a₂ - a₁) * (|α - μ| + 1) / (q - μ) ≤ l - a₁)
    linarith
  have hpt : (1 - (a₂ - a₁) / (l - a₁)) * μ + (a₂ - a₁) / (l - a₁) * α < q := by
    have hlt' : α - μ < |α - μ| + 1 := by linarith [le_abs_self (α - μ)]
    have h1 : (a₂ - a₁) / (l - a₁) * (α - μ) < (a₂ - a₁) / (l - a₁) * (|α - μ| + 1) :=
      mul_lt_mul_of_pos_left hlt' ht0
    have hex : (1 - (a₂ - a₁) / (l - a₁)) * μ + (a₂ - a₁) / (l - a₁) * α
        = μ + (a₂ - a₁) / (l - a₁) * (α - μ) := by ring
    rw [hex]
    linarith
  have hcombo := hf.epi_combo hμ hlα.le (by linarith : (0 : ℝ) ≤ 1 - (a₂ - a₁) / (l - a₁))
    ht0.le (by ring)
  have harg : (1 - (a₂ - a₁) / (l - a₁)) • (x + a₁ • y)
      + ((a₂ - a₁) / (l - a₁)) • (x + l • y) = x + a₂ • y := by
    have hcoef : (1 - (a₂ - a₁) / (l - a₁)) * a₁ + (a₂ - a₁) / (l - a₁) * l = a₂ := by
      have hex : (1 - (a₂ - a₁) / (l - a₁)) * a₁ + (a₂ - a₁) / (l - a₁) * l
          = a₁ + (a₂ - a₁) / (l - a₁) * (l - a₁) := by ring
      rw [hex, hmul]
      ring
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, ← add_smul,
      show (1 : ℝ) - (a₂ - a₁) / (l - a₁) + (a₂ - a₁) / (l - a₁) = 1 by ring, one_smul, hcoef]
  rw [harg] at hcombo
  exact lt_of_le_of_lt hcombo (by exact_mod_cast hpt)

/-- $f(x + a y) = f(x)$ for all $x \in E$ and all real $a$ if and only if $(f0^+)(y) \le 0$ and
$(f0^+)(-y) \le 0$. -/
theorem forall_eq_iff_recessionFn_nonpos :
    (∀ (x : E) (a : ℝ), f (x + a • y) = f x) ↔
      recessionFn f y ≤ 0 ∧ recessionFn f (-y) ≤ 0 := by
  constructor
  · intro h
    refine ⟨recessionFn_nonpos_iff.2 fun x a _ => (h x a).le,
      recessionFn_nonpos_iff.2 fun x a _ => ?_⟩
    rw [smul_neg, ← neg_smul]
    exact (h x (-a)).le
  · rintro ⟨h1, h2⟩
    have h2' : ∀ (x : E) (a : ℝ), 0 ≤ a → f (x - a • y) ≤ f x := by
      intro x a ha
      have := recessionFn_nonpos_iff.1 h2 x a ha
      rwa [smul_neg, ← sub_eq_add_neg] at this
    intro x a
    rcases le_or_gt 0 a with ha | ha
    · refine le_antisymm (recessionFn_nonpos_iff.1 h1 x a ha) ?_
      have := h2' (x + a • y) a ha
      rwa [add_sub_cancel_right] at this
    · have hna : 0 ≤ -a := by linarith
      refine le_antisymm ?_ ?_
      · have := h2' x (-a) hna
        rwa [neg_smul, sub_neg_eq_add] at this
      · have := recessionFn_nonpos_iff.1 h1 (x + a • y) (-a) hna
        rwa [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at this

/-- Let $f$ be convex, $x, z \in E$ and $\alpha \in \mathbb{R}$. If $f(x + a(z - x)) \le \alpha$ for
all real $a$, then $f(z) = f(x)$. Thus a convex function that is bounded above on a whole line
is constant on it. -/
theorem ConvexFn.eq_of_forall_le_along_line (hf : ConvexFn f) {x z : E} {α : ℝ}
    (h : ∀ a : ℝ, f (x + a • (z - x)) ≤ (α : EReal)) : f z = f x := by
  have key : ∀ (u v : E), (∀ a : ℝ, f (u + a • (v - u)) ≤ (α : EReal)) → f v ≤ f u := by
    intro u v hu
    have hlim : liminf (fun a : ℝ => f (u + a • (v - u))) atTop ≤ (α : EReal) :=
      liminf_le_of_frequently_le' (Frequently.of_forall hu)
    have hanti := antitone_along_of_liminf_lt_top hf u (v - u)
      (lt_of_le_of_lt hlim (EReal.coe_lt_top α))
    have hstep := hanti (zero_le_one' ℝ)
    simpa using hstep
  have hzx : ∀ a : ℝ, f (z + a • (x - z)) ≤ (α : EReal) := by
    intro a
    have harg : z + a • (x - z) = x + (1 - a) • (z - x) := by
      rw [sub_smul, one_smul, smul_sub, smul_sub]
      abel
    rw [harg]
    exact h (1 - a)
  exact le_antisymm (key x z h) (key z x hzx)

/-- Let $f$ be convex, let $M \subseteq E$ be an affine subspace, and let $\alpha \in \mathbb{R}$
with $f(w) \le \alpha$ for all $w \in M$. Then $f(z) = f(x)$ for all $x, z \in M$. Thus a convex
function that is bounded above on an affine set is constant on it.

The proof applies `ConvexAnalysis.ConvexFn.eq_of_forall_le_along_line` to the line through two
points of $M$, so it needs no closure and no relative interior. The function $f$ need not be
finite on $M$. -/
theorem ConvexFn.eq_of_le_on_affineSubspace (hf : ConvexFn f) {M : AffineSubspace ℝ E} {α : ℝ}
    (hM : ∀ w ∈ M, f w ≤ (α : EReal)) {x z : E} (hx : x ∈ M) (hz : z ∈ M) : f z = f x := by
  refine hf.eq_of_forall_le_along_line fun a => hM _ ?_
  have hmem := M.smul_vsub_vadd_mem a hz hx hx
  simpa [vsub_eq_sub, vadd_eq_add, add_comm] using hmem

/-! ### The recession cone, constancy space and lineality space of a function -/

/-- The **recession cone** of $f$ is the set $$\{y \in E : (f0^+)(y) \le 0\}.$$ It is the horizontal
section $\{y : (y, 0) \in 0^+(\operatorname{epi} f)\}$ of the recession cone of the epigraph,
and it consists of the directions in which $f$ recedes.

It is not the recession cone of $\operatorname{epi} f$, which is a subset of
$E \times \mathbb{R}$. -/
def recessionConeFn (f : E → EReal) : Set E := {y | recessionFn f y ≤ 0}

/-- $y$ lies in the recession cone of $f$ if and only if $(f0^+)(y) \le 0$. -/
@[simp]
theorem mem_recessionConeFn : y ∈ recessionConeFn f ↔ recessionFn f y ≤ 0 := Iff.rfl

/-- $y$ lies in the recession cone of $f$ if and only if $(y, 0) \in 0^+(\operatorname{epi} f)$. -/
theorem mem_recessionConeFn_iff_mk :
    y ∈ recessionConeFn f ↔ ((y, (0 : ℝ)) : E × ℝ) ∈ recessionCone (epi f) := by
  rw [mem_recessionConeFn, ← recessionFn_le_coe_iff, EReal.coe_zero]

/-- The recession cone of $f$, bundled as a `PointedCone ℝ E`: it contains $0$ and is closed under
addition and under multiplication by nonnegative scalars.

No hypothesis on $f$ is needed. -/
def recessionPointedConeFn (f : E → EReal) : PointedCone ℝ E where
  carrier := recessionConeFn f
  zero_mem' := recessionFn_apply_zero_le f
  add_mem' {y z} hy hz := by
    have h := add_mem_recessionCone (mem_recessionConeFn_iff_mk.1 hy)
      (mem_recessionConeFn_iff_mk.1 hz)
    rw [Prod.mk_add_mk, add_zero] at h
    exact mem_recessionConeFn_iff_mk.2 h
  smul_mem' c y hy := by
    have h := smul_mem_recessionCone c.2 (mem_recessionConeFn_iff_mk.1 hy)
    rw [Prod.smul_mk, smul_eq_mul, mul_zero] at h
    exact mem_recessionConeFn_iff_mk.2 h

/-- The carrier of `ConvexAnalysis.recessionPointedConeFn f` is the recession cone
`ConvexAnalysis.recessionConeFn f`. -/
@[simp]
theorem coe_recessionPointedConeFn (f : E → EReal) :
    (recessionPointedConeFn f : Set E) = recessionConeFn f := rfl

/-- $y$ lies in `ConvexAnalysis.recessionPointedConeFn f` if and only if $y$ lies in the recession
cone of $f$. -/
@[simp]
theorem mem_recessionPointedConeFn : y ∈ recessionPointedConeFn f ↔ y ∈ recessionConeFn f :=
  Iff.rfl

/-- The recession cone of $f$ is convex. -/
theorem convex_recessionConeFn (f : E → EReal) : Convex ℝ (recessionConeFn f) :=
  ((recessionPointedConeFn f : ConvexCone ℝ E)).convex

/-- The **constancy space** of $f$ is the set $$\{y \in E : (f0^+)(y) \le 0 \text{ and } (f0^+)(-y)
\le 0\},$$ the intersection $K \cap (-K)$ of the recession cone $K$ of $f$ with its negative.

It consists of the directions in which $f$ is constant
(`ConvexAnalysis.mem_constancySpace_iff_forall_eq`), and it is the largest subspace inside $K$
(`ConvexAnalysis.constancySubmodule_isGreatest`). -/
def constancySpace (f : E → EReal) : Set E := recessionConeFn f ∩ (-recessionConeFn f)

/-- $y$ lies in the constancy space of $f$ if and only if $(f0^+)(y) \le 0$ and $(f0^+)(-y) \le 0$.
-/
theorem mem_constancySpace :
    y ∈ constancySpace f ↔ recessionFn f y ≤ 0 ∧ recessionFn f (-y) ≤ 0 := by
  simp [constancySpace]

/-- $y$ lies in the constancy space of $f$ if and only if $f(x + a y) = f(x)$ for all $x \in E$ and
all real $a$. -/
theorem mem_constancySpace_iff_forall_eq :
    y ∈ constancySpace f ↔ ∀ (x : E) (a : ℝ), f (x + a • y) = f x := by
  rw [mem_constancySpace, ← forall_eq_iff_recessionFn_nonpos]

/-- The constancy space of $f$ as a subspace of $E$.

It is defined as `PointedCone.lineal` of the recession cone $K$ of $f$, the largest subspace
$K \cap (-K)$ inside $K$. -/
noncomputable def constancySubmodule (f : E → EReal) : Submodule ℝ E :=
  (recessionPointedConeFn f).lineal

/-- The carrier of `ConvexAnalysis.constancySubmodule f` is the constancy space
`ConvexAnalysis.constancySpace f`. -/
@[simp]
theorem coe_constancySubmodule (f : E → EReal) :
    (constancySubmodule f : Set E) = constancySpace f := by
  ext z; simp [constancySubmodule, constancySpace]

/-- $y$ lies in `ConvexAnalysis.constancySubmodule f` if and only if $y$ lies in the constancy space
of $f$. -/
@[simp]
theorem mem_constancySubmodule : y ∈ constancySubmodule f ↔ y ∈ constancySpace f := by
  rw [← SetLike.mem_coe, coe_constancySubmodule]

/-- The constancy space of $f$ is the largest subspace of $E$ that is contained in the recession
cone of $f$. -/
theorem constancySubmodule_isGreatest (f : E → EReal) :
    IsGreatest {L : Submodule ℝ E | (L : Set E) ⊆ recessionConeFn f} (constancySubmodule f) := by
  refine ⟨?_, fun L hL z hz => ?_⟩
  · intro z hz
    rw [SetLike.mem_coe, mem_constancySubmodule, mem_constancySpace] at hz
    exact hz.1
  · exact mem_constancySubmodule.2 (mem_constancySpace.2 ⟨hL hz, hL (L.neg_mem hz)⟩)

/-! ### Directions in which `f` is affine -/

/-- Let $f$ be proper, and let $\nu, \rho \in \mathbb{R}$ with $(f0^+)(y) \le \nu$ and
$(f0^+)(-y) \le \rho$. Then $\nu + \rho \ge 0$.

The sum of the two directions of recession gives
$(0, \nu + \rho) \in 0^+(\operatorname{epi} f)$, and $(f0^+)(0) = 0$. -/
theorem zero_le_add_of_recessionFn_le (hp : ProperConvex f) {ν ρ : ℝ}
    (h1 : recessionFn f y ≤ (ν : EReal)) (h2 : recessionFn f (-y) ≤ (ρ : EReal)) : 0 ≤ ν + ρ := by
  have hsum := add_mem_recessionCone (recessionFn_le_coe_iff.1 h1) (recessionFn_le_coe_iff.1 h2)
  rw [Prod.mk_add_mk, add_neg_cancel] at hsum
  have hle : recessionFn f 0 ≤ ((ν + ρ : ℝ) : EReal) := recessionFn_le_coe_iff.2 hsum
  rw [recessionFn_apply_zero hp] at hle
  exact_mod_cast hle

/-- Let $f$ be proper and $\nu \in \mathbb{R}$. If $(f0^+)(-y) \le -\nu$, then $\nu \le (f0^+)(y)$.
-/
theorem le_recessionFn_of_neg_le (hp : ProperConvex f) {ν : ℝ}
    (h : recessionFn f (-y) ≤ ((-ν : ℝ) : EReal)) : (ν : EReal) ≤ recessionFn f y :=
  EReal.le_of_forall_coe_le fun r hr => by
    have hsum := zero_le_add_of_recessionFn_le hp hr h
    exact_mod_cast (by linarith : ν ≤ r)

/-- Let $f$ be proper and $\nu \in \mathbb{R}$. Then $(y, \nu) \in
\operatorname{lin}(\operatorname{epi} f)$ if and only if $(f0^+)(y) = \nu$ and
$(f0^+)(-y) = -\nu$.

Properness turns the inequalities $(f0^+)(y) \le \nu$ and $(f0^+)(-y) \le -\nu$ into equalities. -/
theorem mk_mem_linealitySpace_epi_iff (hp : ProperConvex f) {ν : ℝ} :
    ((y, ν) : E × ℝ) ∈ linealitySpace (epi f) ↔
      recessionFn f y = (ν : EReal) ∧ recessionFn f (-y) = ((-ν : ℝ) : EReal) := by
  rw [mem_linealitySpace]
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f) := h2
    have hle1 : recessionFn f y ≤ (ν : EReal) := recessionFn_le_coe_iff.2 h1
    have hle2 : recessionFn f (-y) ≤ ((-ν : ℝ) : EReal) := recessionFn_le_coe_iff.2 h2'
    refine ⟨le_antisymm hle1 (le_recessionFn_of_neg_le hp hle2), le_antisymm hle2 ?_⟩
    have hback : recessionFn f (-(-y)) ≤ ((-(-ν) : ℝ) : EReal) := by
      rw [neg_neg, neg_neg]
      exact hle1
    exact le_recessionFn_of_neg_le hp hback
  · rintro ⟨h1, h2⟩
    refine ⟨recessionFn_le_coe_iff.1 h1.le, ?_⟩
    exact (recessionFn_le_coe_iff.1 h2.le : ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f))

/-- If $(y, \nu) \in \operatorname{lin}(\operatorname{epi} f)$, then $f(x + a y) = f(x) + a\nu$ for
all $x \in E$ and $a \ge 0$. -/
theorem eq_add_of_mk_mem_linealitySpace_epi (h : ((y, ν) : E × ℝ) ∈ linealitySpace (epi f))
    (x : E) {a : ℝ} (ha : 0 ≤ a) : f (x + a • y) = f x + ((a * ν : ℝ) : EReal) := by
  rw [mem_linealitySpace] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f) := h2
  refine le_antisymm (mk_mem_recessionCone_epi_iff.1 h1 x a ha) ?_
  have hback := mk_mem_recessionCone_epi_iff.1 h2' (x + a • y) a ha
  rw [smul_neg, add_neg_cancel_right] at hback
  have hstep : f x + ((a * ν : ℝ) : EReal)
      ≤ f (x + a • y) + (((a * -ν : ℝ) : EReal) + ((a * ν : ℝ) : EReal)) := by
    rw [← add_assoc]
    exact add_le_add hback le_rfl
  rwa [← EReal.coe_add, show a * -ν + a * ν = 0 by ring, EReal.coe_zero,
    add_zero] at hstep

/-- For every $f : E \to [-\infty, +\infty]$, $y \in E$ and $\nu \in \mathbb{R}$, $$f(x + a y) =
f(x) + a\nu \quad \text{for all } x \in E \text{ and all } a \in \mathbb{R}$$ if and only if
$(y, \nu) \in \operatorname{lin}(\operatorname{epi} f)$. Thus $f$ is affine with slope $\nu$
along every line in the direction $y$ exactly when $(y, \nu)$ lies in the lineality space of
$\operatorname{epi} f$.

No hypothesis on $f$ is needed. -/
theorem forall_eq_add_iff_mk_mem_linealitySpace_epi :
    (∀ (x : E) (a : ℝ), f (x + a • y) = f x + ((a * ν : ℝ) : EReal)) ↔
      ((y, ν) : E × ℝ) ∈ linealitySpace (epi f) := by
  rw [mem_linealitySpace]
  constructor
  · intro h
    refine ⟨mk_mem_recessionCone_epi_iff.2 fun x a _ => (h x a).le, ?_⟩
    refine (mk_mem_recessionCone_epi_iff.2 fun x a _ => ?_ :
      ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f))
    have hstep := h x (-a)
    rw [neg_smul, ← smul_neg, show -a * ν = a * -ν by ring] at hstep
    exact hstep.le
  · rintro ⟨h1, h2⟩
    have h2' : ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f) := h2
    have hmem : ((y, ν) : E × ℝ) ∈ linealitySpace (epi f) := mem_linealitySpace.2 ⟨h1, h2⟩
    have hmem' : ((-y, -ν) : E × ℝ) ∈ linealitySpace (epi f) := by
      refine mem_linealitySpace.2 ⟨h2', ?_⟩
      have hnn : -((-y, -ν) : E × ℝ) = ((y, ν) : E × ℝ) := by
        rw [show ((-y, -ν) : E × ℝ) = -((y, ν) : E × ℝ) from rfl, neg_neg]
      rw [hnn]
      exact h1
    intro x a
    rcases le_or_gt 0 a with hpos | hneg
    · exact eq_add_of_mk_mem_linealitySpace_epi hmem x hpos
    · have hstep := eq_add_of_mk_mem_linealitySpace_epi hmem' x (a := -a) (by linarith)
      rwa [neg_smul_neg, show -a * -ν = a * ν by ring] at hstep

/-- Let $f$ be proper. Then $f(x + a y) = f(x) + a\nu$ for all $x \in E$ and all real $a$ if and
only if $(f0^+)(y) = \nu$ and $(f0^+)(-y) = -\nu$. -/
theorem forall_eq_add_iff_recessionFn (hp : ProperConvex f) :
    (∀ (x : E) (a : ℝ), f (x + a • y) = f x + ((a * ν : ℝ) : EReal)) ↔
      recessionFn f y = (ν : EReal) ∧ recessionFn f (-y) = ((-ν : ℝ) : EReal) :=
  forall_eq_add_iff_mk_mem_linealitySpace_epi.trans (mk_mem_linealitySpace_epi_iff hp)

/-- The **lineality space** of $f$ is the set $$\{y \in E : (f0^+)(-y) = -(f0^+)(y)\}.$$

For proper $f$ it consists of the directions in which $f$ is affine; see
`ConvexAnalysis.forall_eq_add_iff_recessionFn` and `ConvexAnalysis.linealitySpaceFn_eq_image`. -/
def linealitySpaceFn (f : E → EReal) : Set E := {y | recessionFn f (-y) = -recessionFn f y}

/-- $y$ lies in the lineality space of $f$ if and only if $(f0^+)(-y) = -(f0^+)(y)$. -/
@[simp]
theorem mem_linealitySpaceFn :
    y ∈ linealitySpaceFn f ↔ recessionFn f (-y) = -recessionFn f y := Iff.rfl

/-- Let $f$ be proper. Then the lineality space of $f$ is the image of
$\operatorname{lin}(\operatorname{epi} f)$ under the projection $(y, \nu) \mapsto y$. -/
theorem linealitySpaceFn_eq_image (hp : ProperConvex f) :
    linealitySpaceFn f = Prod.fst '' linealitySpace (epi f) := by
  ext z
  constructor
  · intro hz
    have hz' : recessionFn f (-z) = -recessionFn f z := hz
    have hne : recessionFn f z ≠ ⊤ := by
      intro hc
      rw [hc] at hz'
      exact recessionFn_ne_bot hp (-z) (by rwa [EReal.neg_top] at hz')
    obtain ⟨ν, hν⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (recessionFn_ne_bot hp z) (lt_top_iff_ne_top.2 hne)
    refine ⟨(z, ν), (mk_mem_linealitySpace_epi_iff hp).2 ⟨hν, ?_⟩, rfl⟩
    rw [hz', hν, ← EReal.coe_neg]
  · rintro ⟨⟨w, ν⟩, hw, rfl⟩
    obtain ⟨h1, h2⟩ := (mk_mem_linealitySpace_epi_iff hp).1 hw
    change recessionFn f (-w) = -recessionFn f w
    rw [h1, h2, EReal.coe_neg]

/-- The lineality space of $f$ as a subspace of $E$: the image of the subspace
$\operatorname{lin}(\operatorname{epi} f)$ of $E \times \mathbb{R}$ under the projection
$(y, \nu) \mapsto y$.

The definition by the projection gives the subspace structure directly. For proper $f$,
`ConvexAnalysis.coe_linealitySubmoduleFn` identifies its carrier with the lineality space
`ConvexAnalysis.linealitySpaceFn f`. -/
noncomputable def linealitySubmoduleFn (f : E → EReal) : Submodule ℝ E :=
  Submodule.map (LinearMap.fst ℝ E ℝ) (linealitySubmodule (epi f))

/-- Let $f$ be proper. Then the carrier of `ConvexAnalysis.linealitySubmoduleFn f` is the lineality
space of $f$. -/
theorem coe_linealitySubmoduleFn (hp : ProperConvex f) :
    (linealitySubmoduleFn f : Set E) = linealitySpaceFn f := by
  rw [linealitySpaceFn_eq_image hp, linealitySubmoduleFn, Submodule.map_coe,
    coe_linealitySubmodule]
  rfl

/-- The **lineality** of $f$ is the dimension of its lineality space
`ConvexAnalysis.linealitySubmoduleFn f`.

The dimension is `Module.finrank`, which is $0$ when the subspace is infinite-dimensional. -/
noncomputable def linealityFn (f : E → EReal) : ℕ := Module.finrank ℝ (linealitySubmoduleFn f)

/-- Let $f$ be proper, and let $y$ lie both in the recession cone and in the lineality space of $f$.
Suppose that there are $x \in \operatorname{dom} f$ and $\beta \in \mathbb{R}$ with
$\beta \le f(x + a y)$ for all $a \ge 0$. Then $y$ lies in the constancy space of $f$. Thus an
affine direction of recession along which $f$ is bounded below is a direction of constancy.

Because $f$ is affine along $y$, $f(x + a y) = f(x) + a\nu$ with $\nu = (f0^+)(y) \le 0$, and
the lower bound forces $\nu = 0$. -/
theorem mem_constancySpace_of_mem_linealitySpaceFn (hp : ProperConvex f)
    (hy : y ∈ recessionConeFn f) (hlin : y ∈ linealitySpaceFn f) {x : E} (hx : x ∈ convexDom f)
    {β : ℝ} (hbdd : ∀ a : ℝ, 0 ≤ a → (β : EReal) ≤ f (x + a • y)) : y ∈ constancySpace f := by
  have hle : recessionFn f y ≤ 0 := hy
  obtain ⟨ν, hν⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (recessionFn_ne_bot hp y)
    (hle.trans_lt (by simp))
  have hνle : ν ≤ 0 := by exact_mod_cast hν ▸ hle
  have hneg : recessionFn f (-y) = ((-ν : ℝ) : EReal) := by
    rw [mem_linealitySpaceFn.1 hlin, hν, ← EReal.coe_neg]
  have haff := (forall_eq_add_iff_recessionFn hp).2 ⟨hν, hneg⟩
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
  have hkey : ∀ a : ℝ, 0 ≤ a → β ≤ μ + a * ν := by
    intro a ha
    have hval := hbdd a ha
    rw [haff x a, hμ, ← EReal.coe_add] at hval
    exact_mod_cast hval
  have hν0 : ν = 0 := by
    rcases lt_or_eq_of_le hνle with hlt | heq
    · exfalso
      have hb0 : β ≤ μ := by simpa using hkey 0 le_rfl
      have hpos : 0 < -ν := by linarith
      have hcancel : (μ - β + 1) / (-ν) * (-ν) = μ - β + 1 := div_mul_cancel₀ _ hpos.ne'
      have hstep := hkey ((μ - β + 1) / (-ν)) (by positivity)
      nlinarith
    · exact heq
  refine mem_constancySpace.2 ⟨?_, ?_⟩
  · rw [hν, hν0]; simp
  · rw [hneg, hν0]; simp

end Defs

/-! ### Difference quotients -/

section Quotient

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x y : E}

/-- Let $f$ never take the value $-\infty$, let $x \in \operatorname{dom} f$, $a > 0$ and
$\nu \in \mathbb{R}$. Then $$\frac{f(x + a y) - f(x)}{a} \le \nu \iff f(x + a y) \le f(x) +
a\nu.$$

The right side says that $(x, f(x)) + a(y, \nu) \in \operatorname{epi} f$. This turns the
difference-quotient formula into a statement about a single half-line. The quotient is written
as $a^{-1}(f(x + a y) - f(x))$ in `EReal`. -/
theorem coe_inv_mul_sub_le_coe_iff (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ convexDom f) {a ν : ℝ}
    (ha : 0 < a) :
    ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x) ≤ (ν : EReal) ↔
      f (x + a • y) ≤ f x + ((a * ν : ℝ) : EReal) := by
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
  rw [hs]
  constructor
  · intro hle
    have h2 : ((a : ℝ) : EReal) * (((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - (s : EReal)))
        ≤ ((a : ℝ) : EReal) * ((ν : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_left hle (by exact_mod_cast ha.le)
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ha.ne', EReal.coe_one,
      one_mul, ← EReal.coe_mul] at h2
    rw [add_comm ((s : ℝ) : EReal) ((a * ν : ℝ) : EReal)]
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot s))
      (Or.inl (EReal.coe_ne_top s))).1 h2
  · intro hle
    rw [add_comm ((s : ℝ) : EReal) ((a * ν : ℝ) : EReal)] at hle
    have h2 := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot s))
      (Or.inl (EReal.coe_ne_top s))).2 hle
    have h3 : ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - (s : EReal))
        ≤ ((a⁻¹ : ℝ) : EReal) * ((a * ν : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_left h2 (by exact_mod_cast (inv_pos.2 ha).le)
    rwa [← EReal.coe_mul, show a⁻¹ * (a * ν) = ν by field_simp] at h3

/-- Let $f$ be convex and never $-\infty$, let $x \in \operatorname{dom} f$ and $y \in E$. Then the
difference quotient $(f(x + a y) - f(x))/a$ is nondecreasing in $a > 0$: for $0 < a_1 \le a_2$,
$$\frac{f(x + a_1 y) - f(x)}{a_1} \le \frac{f(x + a_2 y) - f(x)}{a_2}.$$

The proof uses only convexity: $x + a_1 y$ is a convex combination of $x$ and $x + a_2 y$. -/
theorem monotone_coe_inv_mul_sub (hf : ConvexFn f) (hbot : ∀ z, f z ≠ ⊥)
    (hx : x ∈ convexDom f) (y : E)
    {a₁ a₂ : ℝ} (h1 : 0 < a₁) (h12 : a₁ ≤ a₂) :
    ((a₁⁻¹ : ℝ) : EReal) * (f (x + a₁ • y) - f x)
      ≤ ((a₂⁻¹ : ℝ) : EReal) * (f (x + a₂ • y) - f x) := by
  have h2 : 0 < a₂ := lt_of_lt_of_le h1 h12
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
  refine EReal.le_of_forall_coe_le fun ν hν => ?_
  rw [coe_inv_mul_sub_le_coe_iff hbot hx h1]
  have hν' := (coe_inv_mul_sub_le_coe_iff hbot hx h2).1 hν
  rw [hs] at hν' ⊢
  have hmem2 : f (x + a₂ • y) ≤ ((s + a₂ * ν : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact hν'
  have hq0 : (0 : ℝ) ≤ a₁ / a₂ := div_nonneg h1.le h2.le
  have hq1 : a₁ / a₂ ≤ 1 := (div_le_one h2).2 h12
  have hcombo := hf.epi_combo hs.le hmem2 (by linarith : (0 : ℝ) ≤ 1 - a₁ / a₂) hq0 (by ring)
  have harg : (1 - a₁ / a₂) • x + (a₁ / a₂) • (x + a₂ • y) = x + a₁ • y := by
    rw [smul_add, smul_smul, ← add_assoc, ← add_smul,
      show (1 : ℝ) - a₁ / a₂ + a₁ / a₂ = 1 by ring, one_smul,
      show a₁ / a₂ * a₂ = a₁ by field_simp]
  have hval : (1 - a₁ / a₂) * s + a₁ / a₂ * (s + a₂ * ν) = s + a₁ * ν := by
    field_simp
    ring
  rwa [harg, hval, EReal.coe_add] at hcombo

end Quotient

/-! ### The recession function of an indicator -/

section Indicator

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- Let $C \subseteq E$ be nonempty. Then $$0^+(C \times [0, \infty)) = 0^+C \times [0, \infty).$$

The set $C \times [0, \infty)$ is the epigraph of the indicator function $\delta(\cdot \mid C)$. -/
theorem recessionCone_prod_Ici (hC : C.Nonempty) :
    recessionCone (C ×ˢ Set.Ici (0 : ℝ)) = recessionCone C ×ˢ Set.Ici (0 : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := hC
  ext ⟨y, ν⟩
  constructor
  · intro h
    refine ⟨fun x hx a ha => ?_, ?_⟩
    · simpa using (h (x, 0) ⟨hx, le_refl (0 : ℝ)⟩ a ha).1
    · have hstep := (h (x₀, 0) ⟨hx₀, le_refl (0 : ℝ)⟩ 1 zero_le_one).2
      have h2 : (0 : ℝ) ≤ 0 + 1 * ν := hstep
      change (0 : ℝ) ≤ ν
      linarith
  · rintro ⟨hy, hν⟩ ⟨x, μ⟩ ⟨hx, hμ⟩ a ha
    have hμ' : (0 : ℝ) ≤ μ := hμ
    have hν' : (0 : ℝ) ≤ ν := hν
    refine ⟨by simpa using hy x hx a ha, ?_⟩
    have : (0 : ℝ) ≤ μ + a * ν := by nlinarith
    simpa using this

/-- Let $C \subseteq E$ be nonempty. The recession function of the indicator function
$\delta(\cdot \mid C)$, which is $0$ on $C$ and $+\infty$ off $C$, is the indicator function of
the recession cone: $$\delta(\cdot \mid C) 0^+ = \delta(\cdot \mid 0^+C).$$

Nonemptiness of $C$ is needed. For $C = \emptyset$ the epigraph of
$\delta(\cdot \mid \emptyset)$ is empty and $0^+\emptyset = E \times \mathbb{R}$, so the left
side is the constant $-\infty$, while the right side is the constant $0$. -/
theorem recessionFn_indicatorFn (hC : C.Nonempty) :
    recessionFn (indicatorFn C) = indicatorFn (recessionCone C) :=
  (eq_ofEpi_of_epi_eq (by
    rw [epi_indicatorFn, epi_indicatorFn, recessionCone_prod_Ici hC])).symm

/-- Let $C \subseteq E$ be nonempty. The recession cone of the indicator function
$\delta(\cdot \mid C)$ is the recession cone $0^+C$ of the set. -/
theorem recessionConeFn_indicatorFn (hC : C.Nonempty) :
    recessionConeFn (indicatorFn C) = recessionCone C := by
  ext y
  rw [mem_recessionConeFn, recessionFn_indicatorFn hC]
  by_cases hy : y ∈ recessionCone C
  · rw [indicatorFn_of_mem hy]
    simp [hy]
  · rw [indicatorFn_of_notMem hy]
    simp [hy]

end Indicator

/-! ### Closed functions: the limit formula, and testing at a single base point -/

section Topological

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {f : E → EReal} {x y : E}

/-- Let $E$ be a real topological vector space. If $\operatorname{epi} f$ is closed, then
$\operatorname{epi}(f0^+)$ is closed.

Only closedness of $\operatorname{epi} f$ is used; neither convexity nor nonemptiness is needed. -/
theorem isClosed_epi_recessionFn (hc : IsClosed (epi f)) : IsClosed (epi (recessionFn f)) := by
  rw [epi_recessionFn]
  exact isClosed_recessionCone hc

/-- If $\operatorname{epi} f$ is closed, then $f0^+$ is lower semicontinuous. -/
theorem lowerSemicontinuous_recessionFn (hc : IsClosed (epi f)) :
    LowerSemicontinuous (recessionFn f) :=
  lowerSemicontinuous_iff_isClosed_epi.2 (isClosed_epi_recessionFn hc)

/-- Let $f$ be proper with closed epigraph. Then $f0^+$ is a closed function: it equals its closure
`ConvexAnalysis.convexCl`. This is part of Theorem 8.5 of [rockafellar1970convex]. -/
theorem closedConvex_recessionFn (hp : ProperConvex f)
    (hc : IsClosed (epi f)) : ClosedConvex (recessionFn f) :=
  (closedConvex_iff_lowerSemicontinuous (recessionFn_ne_bot hp)).2
      (lowerSemicontinuous_recessionFn hc)

/-- If $\operatorname{epi} f$ is closed, then the recession cone of $f$ is closed. -/
theorem isClosed_recessionConeFn (hc : IsClosed (epi f)) : IsClosed (recessionConeFn f) := by
  have hpre : recessionConeFn f = (fun z : E => (z, (0 : ℝ))) ⁻¹' recessionCone (epi f) := by
    ext z
    exact mem_recessionConeFn_iff_mk
  rw [hpre]
  exact (isClosed_recessionCone hc).preimage (by fun_prop)

/-- Let $f$ be convex with closed epigraph, and let $x \in E$ and $\mu, \nu \in \mathbb{R}$. If
$f(x + a y) \le \mu + a\nu$ for all $a \ge 0$, then $(y, \nu) \in 0^+(\operatorname{epi} f)$.
Thus a single half-line in $\operatorname{epi} f$ already gives a direction of recession. -/
theorem mk_mem_recessionCone_epi_of_ray (hf : ConvexFn f) (hc : IsClosed (epi f)) (x : E) (μ : ℝ)
    {ν : ℝ} (h : ∀ a : ℝ, 0 ≤ a → f (x + a • y) ≤ ((μ + a * ν : ℝ) : EReal)) :
    ((y, ν) : E × ℝ) ∈ recessionCone (epi f) := by
  refine mem_recessionCone_of_exists_ray hf.convex_epi hc ⟨(x, μ), fun a ha => ?_⟩
  rw [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  exact mk_mem_epi.2 (h a ha)

/-- Let $f$ be convex with closed epigraph and never $-\infty$, and let $x \in \operatorname{dom} f$
and $\nu \in \mathbb{R}$. Then $(f0^+)(y) \le \nu$ if and only if $f(x + a y) \le f(x) + a\nu$
for all $a > 0$. Thus the recession condition can be tested at a single point of
$\operatorname{dom} f$.

The difference-quotient formula `ConvexAnalysis.recessionFn_apply_eq_iSup_inv_mul` rests on
this. -/
theorem recessionFn_le_coe_iff_of_isClosed (hf : ConvexFn f) (hc : IsClosed (epi f))
    (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ convexDom f) {ν : ℝ} :
    recessionFn f y ≤ (ν : EReal) ↔
      ∀ a : ℝ, 0 < a → f (x + a • y) ≤ f x + ((a * ν : ℝ) : EReal) := by
  refine ⟨fun h a ha => recessionFn_le_coe_iff_forall.1 h x a ha.le, fun h => ?_⟩
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
  refine recessionFn_le_coe_iff.2 (mk_mem_recessionCone_epi_of_ray hf hc x s fun a ha => ?_)
  rcases ha.eq_or_lt with rfl | ha'
  · simpa using hs.le
  · have hstep := h a ha'
    rwa [hs, ← EReal.coe_add] at hstep

/-- The **difference-quotient formula**. Let $f$ be convex with closed epigraph and never $-\infty$,
and let $x \in \operatorname{dom} f$. Then for every $y \in E$, $$(f0^+)(y) = \sup_{a > 0}
\frac{f(x + a y) - f(x)}{a}.$$

Closedness makes the right side independent of $x$. The quotient is written as
$a^{-1}(f(x + a y) - f(x))$ in `EReal`. This formula is part of Theorem 8.5 of
[rockafellar1970convex]. -/
theorem recessionFn_apply_eq_iSup_inv_mul (hf : ConvexFn f) (hc : IsClosed (epi f))
    (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ convexDom f) (y : E) :
    recessionFn f y = ⨆ a : ℝ, ⨆ _ : 0 < a, ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x) := by
  refine EReal.eq_of_forall_le_coe_iff fun ν => ?_
  rw [recessionFn_le_coe_iff_of_isClosed hf hc hbot hx, iSup₂_le_iff]
  exact forall₂_congr fun a ha => (coe_inv_mul_sub_le_coe_iff (y := y) hbot hx ha).symm

/-- The **limit formula**. Let $f$ be convex with closed epigraph and never $-\infty$, and let
$x \in \operatorname{dom} f$. Then for every $y \in E$, $$(f0^+)(y) = \lim_{a \to +\infty}
\frac{f(x + a y) - f(x)}{a}.$$

The quotient is nondecreasing in $a$ (`ConvexAnalysis.monotone_coe_inv_mul_sub`), and this turns
the supremum of `ConvexAnalysis.recessionFn_apply_eq_iSup_inv_mul` into a limit. -/
theorem tendsto_coe_inv_mul_sub_atTop (hf : ConvexFn f) (hc : IsClosed (epi f))
    (hbot : ∀ z, f z ≠ ⊥) (hx : x ∈ convexDom f) (y : E) :
    Tendsto (fun a : ℝ => ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x)) atTop
      (𝓝 (recessionFn f y)) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    rw [recessionFn_apply_eq_iSup_inv_mul hf hc hbot hx y, lt_iSup_iff] at hb
    obtain ⟨a₀, hb⟩ := hb
    rw [lt_iSup_iff] at hb
    obtain ⟨ha₀, hb⟩ := hb
    filter_upwards [eventually_ge_atTop a₀] with a ha
    exact lt_of_lt_of_le hb (monotone_coe_inv_mul_sub hf hbot hx y ha₀ ha)
  · intro b hb
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    refine lt_of_le_of_lt ?_ hb
    rw [recessionFn_apply_eq_iSup_inv_mul hf hc hbot hx y]
    exact le_iSup₂ (f := fun a (_ : 0 < a) => ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x)) a ha

/-- Let $f$ be a closed proper convex function and $x \in \operatorname{dom} f$. If
$a \mapsto f(x + a y)$ is nonincreasing on $\mathbb{R}$, then $(f0^+)(y) \le 0$. Thus for closed
$f$ one base point in $\operatorname{dom} f$ is enough. -/
theorem recessionFn_nonpos_of_antitone (hf : ClosedProperConvexFn f)
    (hx : x ∈ convexDom f) (h : Antitone fun a : ℝ => f (x + a • y)) : recessionFn f y ≤ 0 := by
  have h0 : recessionFn f y ≤ ((0 : ℝ) : EReal) := by
    rw [recessionFn_le_coe_iff_of_isClosed hf.convex hf.isClosed_epi hf.proper.ne_bot hx]
    intro a ha
    have hstep := h ha.le
    simp only [zero_smul, add_zero] at hstep
    simpa using hstep
  rwa [EReal.coe_zero] at h0

/-- Let $f$ be a closed proper convex function, $x \in \operatorname{dom} f$ and
$\nu \in \mathbb{R}$. If $f(x + a y) = f(x) + a\nu$ for all real $a$, then $(f0^+)(y) = \nu$ and
$(f0^+)(-y) = -\nu$. Thus for closed $f$ one base point in $\operatorname{dom} f$ is enough. -/
theorem recessionFn_eq_of_affine_along (hf : ClosedProperConvexFn f)
    (hx : x ∈ convexDom f) {ν : ℝ} (h : ∀ a : ℝ, f (x + a • y) = f x + ((a * ν : ℝ) : EReal)) :
    recessionFn f y = (ν : EReal) ∧ recessionFn f (-y) = ((-ν : ℝ) : EReal) := by
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hx
  refine (mk_mem_linealitySpace_epi_iff hf.proper).1 (mem_linealitySpace.2 ⟨?_, ?_⟩)
  · refine mk_mem_recessionCone_epi_of_ray hf.convex hf.isClosed_epi x s fun a _ => ?_
    rw [h a, hs, ← EReal.coe_add]
  · refine (mk_mem_recessionCone_epi_of_ray hf.convex hf.isClosed_epi x s fun a _ => ?_ :
      ((-y, -ν) : E × ℝ) ∈ recessionCone (epi f))
    have hstep := h (-a)
    rw [neg_smul, ← smul_neg, hs, ← EReal.coe_add] at hstep
    rw [hstep, show s + -a * ν = s + a * -ν by ring]

/-- Let $f$ be convex with closed epigraph, and let $\alpha \in \mathbb{R}$ be such that the level
set $\{x : f(x) \le \alpha\}$ is nonempty. Then its recession cone is the recession cone of $f$:
$$0^+\{x : f(x) \le \alpha\} = \{y : (f0^+)(y) \le 0\}.$$ Thus all nonempty level sets of $f$
have the same recession cone. -/
theorem recessionCone_setOf_le (hf : ConvexFn f) (hc : IsClosed (epi f)) {α : ℝ}
    (hne : {z : E | f z ≤ (α : EReal)}.Nonempty) :
    recessionCone {z : E | f z ≤ (α : EReal)} = recessionConeFn f := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := hne
    refine mem_recessionConeFn_iff_mk.2 (mk_mem_recessionCone_epi_of_ray hf hc w α fun a ha => ?_)
    have hmem : f (w + a • z) ≤ (α : EReal) := hz w hw a ha
    rwa [show α + a * 0 = α by ring]
  · intro hz w hw a ha
    exact le_trans (add_smul_le_of_recessionFn_nonpos hz w ha) hw

/-- Let $f$ be convex with closed epigraph, and let $\alpha \in \mathbb{R}$ be such that the level
set $\{x : f(x) \le \alpha\}$ is nonempty. Then the lineality space of this level set is the
constancy space of $f$: $$\operatorname{lin}\{x : f(x) \le \alpha\} = \{y : (f0^+)(y) \le 0
\text{ and } (f0^+)(-y) \le 0\}.$$
-/
theorem linealitySpace_setOf_le (hf : ConvexFn f) (hc : IsClosed (epi f)) {α : ℝ}
    (hne : {z : E | f z ≤ (α : EReal)}.Nonempty) :
    linealitySpace {z : E | f z ≤ (α : EReal)} = constancySpace f := by
  simp only [linealitySpace, constancySpace, recessionCone_setOf_le hf hc hne]

/-!
### The limit of the right scalar multiples

For $a > 0$ the right scalar multiple of $f$ is $(fa)(x) = a f(a^{-1} x)$. The identity
$(f0^+)(y) = \lim_{a \downarrow 0} (fa)(y)$ is proved here directly from the properties of $f0^+$
above, and not through the homogenization of $f$. That route would need the closure of the
homogenization, because at height $0$ the homogenization is the indicator function
$\delta(\cdot \mid \{0\})$ and not $f0^+$. The proof splits into a lower and an upper estimate, and
only the upper estimate needs a point of $\operatorname{dom} f$ on the line through $y$.
-/

/-- Let $f$ be convex with closed epigraph, and let $b < (f0^+)(y)$. Then $b < (fa)(y)$ for all
sufficiently small $a > 0$.

This is the lower estimate, and the one that needs closedness. It applies the sequential
criterion for a direction of recession to points $a_n^{-1}(y, \beta)$ of $\operatorname{epi} f$. -/
theorem eventually_lt_smulRight (hf : ConvexFn f) (hc : IsClosed (epi f)) {b : EReal}
    (hb : b < recessionFn f y) : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), b < smulRight f a y := by
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨β, hbβ, hβL⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a ∧ smulRight f a y ≤ (β : EReal) :=
    (hcon.and_eventually hpos).mono fun a ha =>
      ⟨ha.2, le_of_lt (lt_of_le_of_lt (not_lt.1 ha.1) hbβ)⟩
  obtain ⟨u, hu, hup⟩ := Filter.exists_seq_forall_of_frequently hfreq
  have hu0 : Tendsto u atTop (𝓝 (0 : ℝ)) := hu.mono_right nhdsWithin_le_nhds
  have hmem : ∀ n, (u n)⁻¹ • ((y, β) : E × ℝ) ∈ epi f := by
    intro n
    have hun := (hup n).1
    have hle := (hup n).2
    rw [smulRight_apply_pos hun] at hle
    rw [Prod.smul_mk, smul_eq_mul]
    refine mk_mem_epi.2 ?_
    have h3 : (((u n)⁻¹ : ℝ) : EReal) * (((u n : ℝ) : EReal) * f ((u n)⁻¹ • y))
        ≤ (((u n)⁻¹ : ℝ) : EReal) * ((β : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_left hle (by exact_mod_cast (inv_pos.2 hun).le)
    rwa [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hun.ne', EReal.coe_one,
      one_mul, ← EReal.coe_mul] at h3
  have hconst : (fun n => u n • ((u n)⁻¹ • ((y, β) : E × ℝ))) = fun _ => ((y, β) : E × ℝ) := by
    funext n
    rw [smul_smul, mul_inv_cancel₀ (hup n).1.ne', one_smul]
  have hmemrec : ((y, β) : E × ℝ) ∈ recessionCone (epi f) :=
    mem_recessionCone_of_tendsto hf.convex_epi hc hmem (fun n => (hup n).1) hu0
      (by rw [hconst]; exact tendsto_const_nhds)
  exact absurd (recessionFn_le_coe_iff.2 hmemrec) (not_le.2 hβL)

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Let $f$ be proper, let $\theta \in \mathbb{R}$ with $\theta y \in \operatorname{dom} f$, and let
$(f0^+)(y) < b$. Then $(fa)(y) < b$ for all sufficiently small $a > 0$.

This is the upper estimate. The case $\theta = 1$ is $y \in \operatorname{dom} f$, and the case
$\theta = 0$ is $0 \in \operatorname{dom} f$. No other point of $\operatorname{dom} f$ helps,
because the half-line must start on the line through $y$. This estimate needs no topology on $E$
and no convexity of $f$. -/
theorem eventually_smulRight_lt (hp : ProperConvex f) {θ : ℝ} (hθ : θ • y ∈ convexDom f) {b : EReal}
    (hb : recessionFn f y < b) :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), smulRight f a y < b := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot (θ • y)) hθ
  obtain ⟨β, hLβ, hβb⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  obtain ⟨γ, hβγ, hγb⟩ := EReal.lt_iff_exists_real_btwn.1 hβb
  have hβγ' : β < γ := by exact_mod_cast hβγ
  have hray := mk_mem_recessionCone_epi.1 (recessionFn_le_coe_iff.1 hLβ.le) (θ • y) r hr.le
  have hcont : Tendsto (fun a : ℝ => a * r + (1 - a * θ) * β) (𝓝[>] (0 : ℝ)) (𝓝 β) := by
    have hcf : Continuous fun a : ℝ => a * r + (1 - a * θ) * β := by fun_prop
    simpa using (hcf.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  have hlt : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), a * θ < 1 := by
    have hcf : Continuous fun a : ℝ => a * θ := by fun_prop
    have h0 : Tendsto (fun a : ℝ => a * θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (hcf.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact h0.eventually_lt_const one_pos
  filter_upwards [hcont.eventually_lt_const hβγ', hpos, hlt] with a hva hapos haθ
  have hid : a * a⁻¹ = 1 := mul_inv_cancel₀ hapos.ne'
  have hnn : 0 ≤ a⁻¹ - θ := by nlinarith
  have harg : θ • y + (a⁻¹ - θ) • y = a⁻¹ • y := by
    rw [← add_smul]
    congr 1
    ring
  have hkey : f (a⁻¹ • y) ≤ ((r + (a⁻¹ - θ) * β : ℝ) : EReal) := by
    have hstep := hray (a⁻¹ - θ) hnn
    rwa [harg] at hstep
  rw [smulRight_apply_pos hapos]
  have h2 : ((a : ℝ) : EReal) * f (a⁻¹ • y)
      ≤ ((a : ℝ) : EReal) * ((r + (a⁻¹ - θ) * β : ℝ) : EReal) :=
    mul_le_mul_of_nonneg_left hkey (by exact_mod_cast hapos.le)
  refine lt_of_le_of_lt h2 ?_
  rw [← EReal.coe_mul,
    show a * (r + (a⁻¹ - θ) * β) = a * r + (1 - a * θ) * β by field_simp]
  exact lt_trans (by exact_mod_cast hva) hγb

/-- Let $f$ be a closed proper convex function and $y \in \operatorname{dom} f$. Then $$(f0^+)(y) =
\lim_{a \downarrow 0} (fa)(y),$$ where $(fa)(y) = a f(a^{-1} y)$ is the right scalar multiple.

By `ConvexAnalysis.tendsto_smulRight_recessionFn_of_zero_mem_convexDom`, the limit formula holds
at every $y$ when $0 \in \operatorname{dom} f$. The limit is taken along `𝓝[>] 0`. -/
theorem tendsto_smulRight_recessionFn (hf : ClosedProperConvexFn f) (hy : y ∈ convexDom f) :
    Tendsto (fun a : ℝ => smulRight f a y) (𝓝[>] (0 : ℝ)) (𝓝 (recessionFn f y)) := by
  rw [tendsto_order]
  exact ⟨fun _ hb => eventually_lt_smulRight hf.convex hf.isClosed_epi hb,
    fun _ hb => eventually_smulRight_lt hf.proper (θ := 1) (by rwa [one_smul]) hb⟩

/-- Let $f$ be a closed proper convex function with $0 \in \operatorname{dom} f$. Then
$(f0^+)(y) = \lim_{a \downarrow 0} (fa)(y)$ for every $y \in E$. -/
theorem tendsto_smulRight_recessionFn_of_zero_mem_convexDom (hf : ClosedProperConvexFn f)
    (h0 : (0 : E) ∈ convexDom f) (y : E) :
    Tendsto (fun a : ℝ => smulRight f a y) (𝓝[>] (0 : ℝ)) (𝓝 (recessionFn f y)) := by
  rw [tendsto_order]
  exact ⟨fun _ hb => eventually_lt_smulRight hf.convex hf.isClosed_epi hb,
    fun _ hb => eventually_smulRight_lt hf.proper (θ := 0) (by rwa [zero_smul]) hb⟩

end Topological

/-!
### Slices of a function of two variables

Let $G : U \times X \to [-\infty, +\infty]$ be convex with closed epigraph. Then all slices
$x \mapsto G(u, x)$ with nonempty effective domain have the same recession function. This is the
principle that one half-line is enough, applied to $\operatorname{epi} G$.
-/

section Slice

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] {G : U × X → EReal} {u₀ : U} {x₀ y : X} {ν : ℝ}

/-- Let $U$ and $X$ be real topological vector spaces, and let
$G : U \times X \to [-\infty, +\infty]$ be convex with closed epigraph. Let $u_0 \in U$ and
$x_0 \in X$ with $G(u_0, x_0) < +\infty$, and let $y \in X$ and $\nu \in \mathbb{R}$. If the
recession function of the slice $G(u_0, \cdot)$ satisfies $(G(u_0, \cdot)0^+)(y) \le \nu$, then
$(G(u, \cdot)0^+)(y) \le \nu$ for every $u \in U$.

The slice inequality at one point gives a half-line of $\operatorname{epi} G$ in the direction
$((0, y), \nu)$, and for a closed convex set one half-line is enough. No hypothesis is placed on
$u$: when $G(u, \cdot) \equiv +\infty$ the conclusion holds trivially. -/
theorem recessionFn_le_coe_of_slice (hG : ConvexFn G) (hc : IsClosed (epi G))
    (hx₀ : G (u₀, x₀) ≠ ⊤) (h : recessionFn (fun x => G (u₀, x)) y ≤ (ν : EReal)) (u : U) :
    recessionFn (fun x => G (u, x)) y ≤ (ν : EReal) := by
  obtain ⟨μ, hμ, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 hx₀)
  have hdir : (((0 : U), y), ν) ∈ recessionCone (epi G) := by
    refine mem_recessionCone_of_exists_ray hG.convex_epi hc ⟨((u₀, x₀), μ), fun a ha => ?_⟩
    have hstep := recessionFn_le_coe_iff_forall.1 h x₀ a ha
    have hbound : G (u₀, x₀ + a • y) ≤ ((μ + a * ν : ℝ) : EReal) := by
      refine hstep.trans ?_
      rw [EReal.coe_add]
      exact add_le_add hμ.le le_rfl
    simpa [Prod.smul_mk, smul_zero] using hbound
  refine recessionFn_le_coe_iff.2 fun p hp a ha => ?_
  have hmem : ((u, p.1), p.2) ∈ epi G := hp
  simpa [Prod.smul_mk, smul_zero] using hdir _ hmem a ha

/-- Let $G : U \times X \to [-\infty, +\infty]$ be convex with closed epigraph, and let
$u_0, u_1 \in U$ be such that each of the slices $G(u_0, \cdot)$ and $G(u_1, \cdot)$ is less
than $+\infty$ somewhere. Then the two slices have the same recession function. -/
theorem recessionFn_slice_eq (hG : ConvexFn G) (hc : IsClosed (epi G)) {u₁ : U}
    (h₀ : ∃ x, G (u₀, x) ≠ ⊤) (h₁ : ∃ x, G (u₁, x) ≠ ⊤) :
    recessionFn (fun x => G (u₀, x)) = recessionFn (fun x => G (u₁, x)) := by
  obtain ⟨x₀, hx₀⟩ := h₀
  obtain ⟨x₁, hx₁⟩ := h₁
  funext z
  refine EReal.eq_of_forall_le_coe_iff fun r => ⟨fun h => ?_, fun h => ?_⟩
  · exact recessionFn_le_coe_of_slice hG hc hx₀ h u₁
  · exact recessionFn_le_coe_of_slice hG hc hx₁ h u₀

end Slice

/-! ### Bounded level sets -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be convex with closed epigraph.
Let $\alpha, \beta \in \mathbb{R}$ be such that the level sets $\{x : f(x) \le \alpha\}$ and
$\{x : f(x) \le \beta\}$ are nonempty. If $\{x : f(x) \le \alpha\}$ is bounded, then
$\{x : f(x) \le \beta\}$ is bounded.

Finite dimension enters only through the criterion
`ConvexAnalysis.isBounded_iff_recessionCone_eq_zero`: a nonempty closed convex set is bounded if
and only if its recession cone is $\{0\}$. -/
theorem isBounded_setOf_le (hf : ConvexFn f) (hc : IsClosed (epi f)) {α β : ℝ}
    (hneα : {z : E | f z ≤ (α : EReal)}.Nonempty)
    (hbd : Bornology.IsBounded {z : E | f z ≤ (α : EReal)})
    (hneβ : {z : E | f z ≤ (β : EReal)}.Nonempty) :
    Bornology.IsBounded {z : E | f z ≤ (β : EReal)} := by
  have hclα : IsClosed {z : E | f z ≤ (α : EReal)} :=
    lowerSemicontinuous_iff_isClosed_le.1
      (lowerSemicontinuous_iff_isClosed_epi.2 hc) α
  have hclβ : IsClosed {z : E | f z ≤ (β : EReal)} :=
    lowerSemicontinuous_iff_isClosed_le.1
      (lowerSemicontinuous_iff_isClosed_epi.2 hc) β
  have hzero : recessionCone {z : E | f z ≤ (α : EReal)} = {0} :=
    (isBounded_iff_recessionCone_eq_zero (hf.convex_le _) hclα hneα).1 hbd
  refine (isBounded_iff_recessionCone_eq_zero (hf.convex_le _) hclβ hneβ).2 ?_
  rw [recessionCone_setOf_le hf hc hneβ, ← recessionCone_setOf_le hf hc hneα]
  exact hzero

end FiniteDimensional

/-! ### Bounded effective domains -/

section Bounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}

/-- Let $E$ be a real normed space, and let $\operatorname{dom} f$ be nonempty and bounded. Then
$(f0^+)(w) > 0$ for every $w \neq 0$, so $f$ has no nonzero direction of recession.

No convexity is assumed. If $(f0^+)(w) \le 0$, then $f$ is nonincreasing along $w$, so the whole
ray from a point of $\operatorname{dom} f$ stays in $\operatorname{dom} f$; but a ray in a
direction $w \neq 0$ leaves every ball. -/
theorem lt_recessionFn_of_isBounded_convexDom (hne : (convexDom f).Nonempty)
    (hb : Bornology.IsBounded (convexDom f)) {w : E} (hw : w ≠ 0) : 0 < recessionFn f w := by
  rw [lt_iff_not_ge]
  intro h
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.1 hb
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
  have hy₀r : ‖y₀‖ ≤ r := hr y₀ hy₀
  have hy₀nn : (0 : ℝ) ≤ ‖y₀‖ := norm_nonneg y₀
  set a : ℝ := (r + ‖y₀‖ + 1) / ‖w‖ with hadef
  have hann : (0 : ℝ) ≤ a := by
    rw [hadef]
    exact div_nonneg (by linarith) hwpos.le
  have hmem : y₀ + a • w ∈ convexDom f :=
    lt_of_le_of_lt (add_smul_le_of_recessionFn_nonpos h y₀ hann) hy₀
  have h1 : ‖y₀ + a • w‖ ≤ r := hr _ hmem
  have h2 : a * ‖w‖ = r + ‖y₀‖ + 1 := div_mul_cancel₀ _ (ne_of_gt hwpos)
  have h3 : ‖a • w‖ ≤ ‖y₀ + a • w‖ + ‖y₀‖ := by
    have hsub : (y₀ + a • w) - y₀ = a • w := add_sub_cancel_left y₀ (a • w)
    calc ‖a • w‖ = ‖(y₀ + a • w) - y₀‖ := by rw [hsub]
      _ ≤ ‖y₀ + a • w‖ + ‖y₀‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hann, h2] at h3
  linarith

end Bounded

end ConvexAnalysis
