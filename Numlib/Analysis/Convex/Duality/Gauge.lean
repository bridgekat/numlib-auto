/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Recession.Cone
import Numlib.LinearAlgebra.Subspace
import Mathlib.Analysis.Convex.EGauge
import Mathlib.Analysis.Convex.Gauge

/-!
# Gauges, polars of convex functions, and obverses

Let $E$ and $F$ be real vector spaces paired by a bilinear form $\langle x, y \rangle = B(x, y)$.
The **gauge** of a set $C \subseteq E$ is $\gamma(x \mid C) = \inf \{a \ge 0 : x \in aC\}$, the
least dilate of $C$ that contains $x$, with the value $+\infty$ when no dilate does. The gauges are
the nonnegative positively homogeneous convex functions that vanish at $0$, and
$C \mapsto \gamma(\cdot \mid C)$ is a bijection from the closed convex sets containing $0$ to the
closed gauges. Three operations of polarity act here, each an involution on its class: the polar
$k^\circ(y) = \inf \{\mu \ge 0 : \langle x, y \rangle \le \mu k(x) \ \forall x\}$ of a gauge $k$,
the polar $f^\circ(y) = \inf \{\mu \ge 0 : \langle x, y \rangle \le 1 + \mu f(x) \ \forall x\}$ of a
nonnegative closed convex function $f$ with $f(0) = 0$, and the obverse $\operatorname{ob}(f)(x) =
\inf \{\lambda > 0 : \lambda f(x / \lambda) \le 1\}$. On a gauge the two polars agree, and the
obverse connects them with the Fenchel conjugate: $f^* = \operatorname{ob}(f^\circ)$. The
presentation follows [rockafellar1970convex], §14 and §15.

The module also proves facts about polar sets for which the gauge gives short proofs. For a closed
convex set $C$ that contains $0$, the recession cone $0^+ C$ is the polar cone of $C^\circ$, the
lineality space of $C$ is the annihilator of $C^\circ$, and in finite dimension
$\dim C^\circ + \operatorname{lin} C = n$. For a nonnegative convex function $f$ with $f(0) \le 0$
and $\alpha > 0$, the polar of $\{f \le \alpha\}$ and the set $\alpha^{-1} \{f^* \le \alpha\}$ agree
up to a factor of $2$.

## Main definitions

* `ConvexAnalysis.UpClosed`: a set $S \subseteq \mathbb{R}$ is upward closed; every set of
  admissible scalars in this module has this form.
* `ConvexAnalysis.gaugeFn`: the gauge $\gamma(\cdot \mid C)$ of a set, with values in
  $[0, +\infty]$.
* `ConvexAnalysis.IsGauge`: $k$ is nonnegative, positively homogeneous, convex, and $k(0) = 0$.
* `ConvexAnalysis.polarGauge`: the polar $k^\circ$ of a gauge.
* `ConvexAnalysis.polarFn`: the polar $f^\circ$ of a function, defined as an infimum over the
  epigraph of $f$.
* `ConvexAnalysis.IsPolarFn`: $f$ is nonnegative, closed and convex, with $f(0) = 0$; on this class
  $f \mapsto f^\circ$ is an involution.
* `ConvexAnalysis.obverse`: the obverse $\operatorname{ob}(f)$.
* `ConvexAnalysis.epiPairing`, `ConvexAnalysis.vNeg`: the pairing $\langle (x, \nu), (y, \mu)
  \rangle = \langle x, y \rangle + \nu \mu$ of $E \times \mathbb{R}$ with $F \times \mathbb{R}$, and
  the reflection $(x, \mu) \mapsto (x, -\mu)$.
* `ConvexAnalysis.AbsorbsAll`, `ConvexAnalysis.RayFree`: every point lies in a dilate of $C$; no ray
  from $0$ lies in $C$.
* `ConvexAnalysis.IsNorm`: a gauge that is finite, symmetric, and positive away from $0$.
* `ConvexAnalysis.IsNorm.toSeminorm`: a norm in this sense as a Mathlib `Seminorm`.

## Main results

* `ConvexAnalysis.isGauge_iff`: the gauges are the functions $\gamma(\cdot \mid C)$ with $C$
  nonempty and convex.
* `ConvexAnalysis.gaugeEquiv`: $k = \gamma(\cdot \mid C)$ and $C = \{k \le 1\}$ is a bijection
  between the closed convex sets that contain $0$ and the closed gauges.
* `ConvexAnalysis.gaugeFn_polarSet`, `ConvexAnalysis.supportFn_polarSet`: $\gamma(\cdot \mid
  C^\circ) = \delta^*(\cdot \mid C)$ and $\delta^*(\cdot \mid C^\circ) = \gamma(\cdot \mid C)$
  (Theorem 14.5 of [rockafellar1970convex]).
* `ConvexAnalysis.recessionCone_eq_polarCone_polarSet`, `ConvexAnalysis.polarCone_recessionCone`,
  `ConvexAnalysis.linealitySpace_eq_setOf_pairing_eq_zero`,
  `ConvexAnalysis.polarCone_linealitySpace`: the recession cone and the lineality space of a closed
  convex set $C \ni 0$ as polars (Theorem 14.6 of [rockafellar1970convex]).
* `ConvexAnalysis.finrank_vectorSpan_polarSet_add_lineality`,
  `ConvexAnalysis.finrank_vectorSpan_add_lineality_polarSet`:
  $\dim C^\circ + \operatorname{lin} C = n$ and $\dim C + \operatorname{lin} C^\circ = n$ (Corollary
  14.6.1 of [rockafellar1970convex]).
* `ConvexAnalysis.polarSet_setOf_le_subset_and_subset`: $\{f \le \alpha\}^\circ \subseteq
  \alpha^{-1} \{f^* \le \alpha\} \subseteq 2 \{f \le \alpha\}^\circ$ (Theorem 14.7 of
  [rockafellar1970convex]).
* `ConvexAnalysis.polarGauge_eq_supportFn`, `ConvexAnalysis.polarGauge_polarGauge`,
  `ConvexAnalysis.polarGaugeEquiv`: $k^\circ$ is the support function of $\{k \le 1\}$,
  $k^{\circ\circ} = \operatorname{cl} k$, and $k \mapsto k^\circ$ is a symmetric bijection on the
  closed gauges (Theorem 15.1 and Corollary 15.1.1 of [rockafellar1970convex]).
* `ConvexAnalysis.isNorm_iff`: the norms are the gauges of the symmetric convex sets that absorb
  every point and contain no ray (Theorem 15.2 of [rockafellar1970convex]).
* `ConvexAnalysis.polarFn_polarFn`, `ConvexAnalysis.polarFnEquiv`:
  $f^{\circ\circ} = \operatorname{cl} f$, and $f \mapsto f^\circ$ is a symmetric bijection on the
  nonnegative closed convex functions that vanish at $0$ (Theorem 15.4 and Corollary 15.4.1 of
  [rockafellar1970convex]).
* `ConvexAnalysis.obverse_obverse`, `ConvexAnalysis.convexConj_eq_obverse_polarFn`,
  `ConvexAnalysis.polarFn_eq_obverse_convexConj`: the obverse is an involution, and $f^*$ and
  $f^\circ$ are obverses of each other (Theorem 15.5 of [rockafellar1970convex]).
* `ConvexAnalysis.polarFn_convexConj_eq_convexConj_polarFn`: $f^{*\circ} = f^{\circ *}$ (Corollary
  15.5.1 of [rockafellar1970convex]).
* `ConvexAnalysis.setOf_obverse_le`, `ConvexAnalysis.setOf_polarFn_le`: $\{\operatorname{ob}(f) \le
  \alpha\} = \alpha \{f \le \alpha^{-1}\}$ and $\{f^\circ \le \alpha^{-1}\} = \alpha^{-1} \{f^* \le
  \alpha\}$ for $\alpha > 0$.

## Proof outline

The epigraph of $f^\circ$ is the reflection $(y, \mu) \mapsto (y, -\mu)$ of the polar of
$\operatorname{epi} f$ in $F \times \mathbb{R}$, so the bipolar theorem for sets gives
$f^{\circ\circ} = \operatorname{cl} f$. On a gauge the two polars agree, so
$k^{\circ\circ} = \operatorname{cl} k$ is a special case. The obverse is a gauge value one dimension
higher, $\operatorname{ob}(f)(x) = \gamma((x, 1) \mid \operatorname{epi} f)$, and its properties
follow from those of the gauge. The identity $f^* = \operatorname{ob}(f^\circ)$ is a comparison of
sublevel sets, and the other identities between $f^*$, $f^\circ$ and $\operatorname{ob}(f)$ follow
from it and the two involutions. Where [rockafellar1970convex] uses the polarity of the unit
sublevel set, a cone in $\mathbb{R}^{n+2}$, or the recession cone as the largest closed convex cone
in $C$, the proofs here use these identifications instead.

## Notation

* $\langle x, y \rangle$: the pairing `B x y`.
* $C^\circ$: the polar set `ConvexAnalysis.polarSet B C`, that is $\{y : \langle x, y \rangle \le 1
  \ \forall x \in C\}$.
* $\delta^*(\cdot \mid C)$: the support function `ConvexAnalysis.supportFn B C`.
* $f^*$: the convex conjugate `ConvexAnalysis.convexConj B f`.
* $\operatorname{cl} f$: the closure `ConvexAnalysis.convexCl f`.
* $(f\lambda)(x) = \lambda f(\lambda^{-1} x)$: right scalar multiplication
  `ConvexAnalysis.smulRight f λ`.

## Implementation notes

* All functions take values in `EReal`. `ConvexAnalysis.gaugeFn` takes the infimum over the scalars
  $a \ge 0$, so it is $+\infty$ off $\bigcup_{a \ge 0} aC$; this makes
  $\{\gamma(\cdot \mid C) \le c\}$ equal to $cC$ for closed $C$ and $c > 0$. Mathlib's `gauge` takes
  the infimum over $a > 0$ in $\mathbb{R}$ and has the value $0$ where no dilate contains $x$; the
  two agree for an absorbent set (`ConvexAnalysis.gaugeFn_eq_gauge`). Mathlib's `egauge` is the same
  infimum with values in `ℝ≥0∞`.
* The admissible set $\{\mu \ge 0 : \langle x, y \rangle \le 1 + \mu f(x) \ \forall x\}$ of the
  source formula for $f^\circ$ is not closed. At $\mu = 0$ the convention $0 \cdot (+\infty) = 0$
  imposes $\langle x, y \rangle \le 1$ where $f(x) = +\infty$, which nearby positive $\mu$ do not.
  `ConvexAnalysis.polarFn` quantifies over $\operatorname{epi} f$ instead; this gives a closed
  upward closed set with the same infimum (`ConvexAnalysis.polarFn_apply_eq`).
* Several results need fewer hypotheses than [rockafellar1970convex] states. The inclusions of
  `ConvexAnalysis.polarSet_setOf_le_subset_and_subset` hold for any nonnegative convex $f$ with
  $f(0) \le 0$, without closedness. `ConvexAnalysis.gaugeFn_level_one` needs only nonnegativity,
  positive homogeneity and $k(0) = 0$. `ConvexAnalysis.gaugeFn_polarSet` needs only $0 \in C$.
* `ConvexAnalysis.isNorm_iff` uses `ConvexAnalysis.AbsorbsAll` and `ConvexAnalysis.RayFree` where
  the source has $0 \in \operatorname{int} C$ and $C$ bounded; the two readings are equivalent in
  $\mathbb{R}^n$. It does not assert that a norm is closed: the source obtains this from the
  continuity of a finite convex function on $\mathbb{R}^n$, which is a finite-dimensional fact.
-/

open Set Pointwise
open scoped NNReal ENNReal

namespace ConvexAnalysis

/-!
### Infima of upward closed sets of reals

Every definition in this module is an infimum $\inf_{a \in S} a$ in `EReal` of a set
$S \subseteq \mathbb{R}$ of admissible scalars. The two lemmas here convert $\inf S \le c$ into a
statement about membership in $S$: if $S$ is upward closed, it is equivalent to "every $d > c$ is in
$S$", and if $S$ is also closed, it is equivalent to $c \in S$.
-/

section UpClosed

variable {S : Set ℝ}

/-- A set $S \subseteq \mathbb{R}$ is **upward closed** if $a \in S$ and $a \le b$ imply $b \in S$.

The admissible-scalar sets of `ConvexAnalysis.gaugeFn`, `ConvexAnalysis.polarGauge`,
`ConvexAnalysis.polarFn` and `ConvexAnalysis.obverse` have this form. -/
def UpClosed (S : Set ℝ) : Prop := ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, a ≤ b → b ∈ S

/-- If $S \subseteq \mathbb{R}$ is upward closed and $c \in \mathbb{R}$, then $\inf S \le c$ in
`EReal` if and only if every $d > c$ belongs to $S$. -/
theorem biInf_coe_le_coe_iff_forall_lt (hS : UpClosed S) (c : ℝ) :
    (⨅ a ∈ S, (a : EReal)) ≤ (c : EReal) ↔ ∀ d : ℝ, c < d → d ∈ S := by
  constructor
  · intro h d hd
    have hlt : (⨅ a ∈ S, (a : EReal)) < (d : EReal) :=
      lt_of_le_of_lt h (EReal.coe_lt_coe_iff.2 hd)
    rw [iInf_lt_iff] at hlt
    obtain ⟨a, ha⟩ := hlt
    rw [iInf_lt_iff] at ha
    obtain ⟨haS, halt⟩ := ha
    exact hS haS (EReal.coe_lt_coe_iff.1 halt).le
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨d, hcd, hd⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    exact absurd (iInf₂_le d (h d (EReal.coe_lt_coe_iff.1 hcd))) (not_le.2 hd)

/-- If $S \subseteq \mathbb{R}$ is upward closed and closed and $c \in \mathbb{R}$, then
$\inf S \le c$ in `EReal` if and only if $c \in S$. -/
theorem biInf_coe_le_coe_iff (hS : UpClosed S) (hcl : IsClosed S) (c : ℝ) :
    (⨅ a ∈ S, (a : EReal)) ≤ (c : EReal) ↔ c ∈ S := by
  refine ⟨fun h => ?_, fun h => iInf₂_le c h⟩
  rw [biInf_coe_le_coe_iff_forall_lt hS] at h
  have hten : Filter.Tendsto (fun n : ℕ => c + 1 / (n + 1 : ℝ)) Filter.atTop (nhds c) := by
    have : Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add this
  refine hcl.mem_of_tendsto hten (Filter.Eventually.of_forall fun n => h _ ?_)
  have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  linarith

/-- If every element of $S \subseteq \mathbb{R}$ is nonnegative, then the infimum of $S$ in `EReal`
is nonnegative. -/
theorem zero_le_biInf_coe (h : ∀ a ∈ S, (0 : ℝ) ≤ a) : 0 ≤ ⨅ a ∈ S, (a : EReal) :=
  le_iInf₂ fun a ha => EReal.coe_nonneg.2 (h a ha)

/-- Let $z \in [-\infty, +\infty]$ and $r \in \mathbb{R}$. If $z \le d$ for every real $d > r$, then
$z \le r$. This is Mathlib's `EReal.le_of_forall_lt_iff_le` with the hypothesis stated over
$\mathbb{R}$. -/
theorem le_coe_of_forall_gt_le {z : EReal} {r : ℝ} (h : ∀ d : ℝ, r < d → z ≤ (d : EReal)) :
    z ≤ (r : EReal) :=
  EReal.le_of_forall_lt_iff_le.1 fun d hd => h d (EReal.coe_lt_coe_iff.1 hd)

end UpClosed

/-!
### The gauge of a set

The gauge is $\gamma(x \mid C) = \inf \{a \ge 0 : x \in aC\}$. The scalar $a = 0$ is admitted, and
$0 \cdot C = \{0\}$ for nonempty $C$. Hence $\gamma(0 \mid C) = 0$ for every nonempty $C$, also when
$C$ does not contain $0$.
-/

section GaugeFn

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C D : Set E} {x : E} {a c t : ℝ}

/-- The **gauge** of a set $C \subseteq E$ is the function $E \to [-\infty, +\infty]$
$$\gamma(x \mid C) = \inf \{a \in \mathbb{R} : a \ge 0,\ x \in aC\},$$
with the value $+\infty$ when no dilate $aC$ with $a \ge 0$ contains $x$.

The name `gaugeFn` distinguishes it from Mathlib's `gauge` and `egauge`.
`ConvexAnalysis.gaugeFn_eq_gauge` relates it to `gauge`; the module doc comment explains why the
values are taken in `EReal`. -/
noncomputable def gaugeFn (C : Set E) : E → EReal :=
  fun x => ⨅ a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}, (a : EReal)

/-- The defining formula $\gamma(x \mid C) = \inf \{a \ge 0 : x \in aC\}$. -/
theorem gaugeFn_apply (C : Set E) (x : E) :
    gaugeFn C x = ⨅ a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}, (a : EReal) := rfl

/-- If $a \ge 0$ and $x \in aC$, then $\gamma(x \mid C) \le a$. -/
theorem gaugeFn_le_of_mem_smul (ha : 0 ≤ a) (h : x ∈ a • C) : gaugeFn C x ≤ (a : EReal) :=
  iInf₂_le a ⟨ha, h⟩

/-- The gauge is nonnegative: $0 \le \gamma(x \mid C)$. -/
theorem gaugeFn_nonneg (C : Set E) (x : E) : 0 ≤ gaugeFn C x :=
  zero_le_biInf_coe fun _ ha => ha.1

/-- The gauge never takes the value $-\infty$. -/
theorem gaugeFn_ne_bot (C : Set E) (x : E) : gaugeFn C x ≠ ⊥ :=
  fun h => by simpa [h] using gaugeFn_nonneg C x

/-- For $z \in [-\infty, +\infty]$, $\gamma(x \mid C) < z$ if and only if there is $a \ge 0$ with
$x \in aC$ and $a < z$.

The infimum is not attained in general, so this is the way to extract an admissible scalar from
a bound on the gauge. -/
theorem gaugeFn_lt_iff {z : EReal} :
    gaugeFn C x < z ↔ ∃ a : ℝ, 0 ≤ a ∧ x ∈ a • C ∧ (a : EReal) < z := by
  rw [gaugeFn_apply, iInf_lt_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [iInf_lt_iff] at ha
    obtain ⟨⟨ha0, hmem⟩, halt⟩ := ha
    exact ⟨a, ha0, hmem, halt⟩
  · rintro ⟨a, ha0, hmem, halt⟩
    exact ⟨a, by rw [iInf_lt_iff]; exact ⟨⟨ha0, hmem⟩, halt⟩⟩

/-- The gauge is antitone in the set: if $C \subseteq D$, then
$\gamma(\cdot \mid D) \le \gamma(\cdot \mid C)$. -/
theorem gaugeFn_anti (h : C ⊆ D) : gaugeFn D ≤ gaugeFn C :=
  fun _ => iInf₂_mono' fun a ha => ⟨a, ⟨ha.1, smul_set_mono h ha.2⟩, le_rfl⟩

/-- The gauge of the empty set is the constant $+\infty$. -/
@[simp] theorem gaugeFn_empty : gaugeFn (∅ : Set E) = fun _ => (⊤ : EReal) := by
  funext x
  simp [gaugeFn_apply]

/-- If $C$ is nonempty, then $\gamma(0 \mid C) = 0$, because $0 \in 0 \cdot C$. -/
@[simp] theorem gaugeFn_zero (hne : C.Nonempty) : gaugeFn C 0 = 0 := by
  refine le_antisymm ?_ (gaugeFn_nonneg C 0)
  obtain ⟨z, hz⟩ := hne
  simpa using gaugeFn_le_of_mem_smul (C := C) le_rfl ⟨z, hz, by simp⟩

/-- For $t > 0$, $\gamma(tx \mid C) \le t\, \gamma(x \mid C)$. -/
theorem gaugeFn_smul_le (ht : 0 < t) (C : Set E) (x : E) :
    gaugeFn C (t • x) ≤ (t : EReal) * gaugeFn C x := by
  rw [gaugeFn_apply C x, EReal.coe_mul_iInf ht]
  refine le_iInf fun a => ?_
  rw [EReal.coe_mul_iInf ht]
  refine le_iInf fun ha => ?_
  rw [← EReal.coe_mul]
  obtain ⟨z, hz, hzx⟩ := ha.2
  refine gaugeFn_le_of_mem_smul (mul_nonneg ht.le ha.1) ⟨z, hz, ?_⟩
  change (t * a) • z = t • x
  rw [mul_smul]
  exact congrArg (t • ·) hzx

/-- The gauge of any set is positively homogeneous: $\gamma(tx \mid C) = t\, \gamma(x \mid C)$ for
$t > 0$. -/
theorem posHomogeneous_gaugeFn (C : Set E) : PosHomogeneous (gaugeFn C) := by
  intro t ht x
  refine le_antisymm (gaugeFn_smul_le ht C x) ?_
  have h := gaugeFn_smul_le (inv_pos.2 ht) C (t • x)
  rw [inv_smul_smul₀ ht.ne'] at h
  have h2 : (t : EReal) * gaugeFn C x ≤ (t : EReal) * ((t⁻¹ : ℝ) * gaugeFn C (t • x)) :=
    mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 ht.le)
  rwa [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht.ne', EReal.coe_one, one_mul] at h2

/-- The gauge of a convex set is a convex function. -/
theorem convexFn_gaugeFn (hC : Convex ℝ C) : ConvexFn (gaugeFn C) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hx
  refine EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_
  replace hq := EReal.coe_lt_coe_iff.1 hq
  set ε : ℝ := q - (a * μ + b * ν) with hε
  have hε0 : 0 < ε := by simp only [hε]; linarith
  have hxs : gaugeFn C x < ((μ + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hx (EReal.coe_lt_coe_iff.2 (by linarith))
  have hys : gaugeFn C y < ((ν + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hy (EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨s, hs0, hsC, hslt⟩ := gaugeFn_lt_iff.1 hxs
  obtain ⟨u, hu0, huC, hult⟩ := gaugeFn_lt_iff.1 hys
  have hslt' : s < μ + ε := EReal.coe_lt_coe_iff.1 hslt
  have hult' : u < ν + ε := EReal.coe_lt_coe_iff.1 hult
  have hmem : a • x + b • y ∈ (a * s + b * u) • C := by
    rw [hC.add_smul (by positivity) (by positivity)]
    exact ⟨a • x, by rw [mul_smul]; exact smul_mem_smul_set hsC,
      b • y, by rw [mul_smul]; exact smul_mem_smul_set huC, rfl⟩
  refine lt_of_le_of_lt (gaugeFn_le_of_mem_smul (by positivity) hmem)
    (EReal.coe_lt_coe_iff.2 ?_)
  have h1 : a * s < a * (μ + ε) := mul_lt_mul_of_pos_left hslt' ha'
  have h2 : b * u < b * (ν + ε) := mul_lt_mul_of_pos_left hult' hb'
  have h3 : a * (μ + ε) + b * (ν + ε) = a * μ + b * ν + ε := by
    have : a * ε + b * ε = ε := by linear_combination ε * hab
    nlinarith [this]
  simp only [hε] at h3 ⊢
  linarith

end GaugeFn

/-!
### Gauges

A **gauge** is a nonnegative positively homogeneous convex function that vanishes at $0$.
Equivalently, its epigraph is a convex cone that contains the origin and no point $(x, \mu)$ with
$\mu < 0$. By `ConvexAnalysis.isGauge_iff`, the gauges are exactly the functions
$\gamma(\cdot \mid C)$ for nonempty convex sets $C$.
-/

section IsGauge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {k : E → EReal} {x : E} {a b c : ℝ}

/-- A function $k : E \to [-\infty, +\infty]$ is a **gauge** if it is nonnegative, positively
homogeneous and convex, and $k(0) = 0$. -/
structure IsGauge (k : E → EReal) : Prop where
  /-- A gauge is nonnegative. -/
  nonneg : ∀ x, 0 ≤ k x
  /-- A gauge is positively homogeneous: $k(ax) = a\, k(x)$ for $a > 0$. -/
  posHomogeneous : PosHomogeneous k
  /-- A gauge is convex. -/
  convexFn : ConvexFn k
  /-- A gauge vanishes at the origin. This condition excludes the constant $+\infty$, which
  satisfies the other three. -/
  map_zero : k 0 = 0

/-- A gauge never takes the value $-\infty$. -/
theorem IsGauge.ne_bot (hk : IsGauge k) (x : E) : k x ≠ ⊥ :=
  fun h => by simpa [h] using hk.nonneg x

/-- The gauge $\gamma(\cdot \mid C)$ of a nonempty convex set $C$ is a gauge. -/
theorem isGauge_gaugeFn (hC : Convex ℝ C) (hne : C.Nonempty) : IsGauge (gaugeFn C) where
  nonneg := gaugeFn_nonneg C
  posHomogeneous := posHomogeneous_gaugeFn C
  convexFn := convexFn_gaugeFn hC
  map_zero := gaugeFn_zero hne

/-- The unit sublevel set $\{x : k(x) \le 1\}$ of a gauge is convex. -/
theorem IsGauge.convex_level_one (hk : IsGauge k) : Convex ℝ {x : E | k x ≤ 1} :=
  hk.convexFn.convex_le 1

/-- The unit sublevel set $\{x : k(x) \le 1\}$ of a gauge contains $0$. -/
theorem IsGauge.zero_mem_level_one (hk : IsGauge k) : (0 : E) ∈ {x : E | k x ≤ 1} := by
  change k 0 ≤ 1
  rw [hk.map_zero]
  exact zero_le_one

/-- Let $k : E \to [-\infty, +\infty]$ be nonnegative and positively homogeneous with $k(0) = 0$.
Then $k$ is the gauge of its unit sublevel set:
$$\gamma(\cdot \mid \{x : k(x) \le 1\}) = k.$$

Convexity of $k$ is not needed. This half of the correspondence between gauges and sets needs no
topology; the other half, `ConvexAnalysis.setOf_gaugeFn_le_one`, needs closedness. -/
theorem gaugeFn_level_one (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    gaugeFn {x : E | k x ≤ 1} = k := by
  set D : Set E := {x : E | k x ≤ 1} with hD
  have h0D : (0 : E) ∈ D := by change k 0 ≤ 1; rw [h0]; exact zero_le_one
  funext x
  refine le_antisymm ?_ ?_
  · rcases eq_or_lt_of_le (le_top (a := k x)) with htop | hlt
    · rw [htop]; exact le_top
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hlt
    have hr0 : (0 : ℝ) ≤ r := by
      have := hnn x; rw [hr] at this; exact EReal.coe_nonneg.1 this
    rcases eq_or_lt_of_le hr0 with rfl | hrpos
    · rw [hr]
      refine le_coe_of_forall_gt_le fun d hd => ?_
      refine gaugeFn_le_of_mem_smul hd.le ⟨d⁻¹ • x, ?_, smul_inv_smul₀ hd.ne' x⟩
      change k (d⁻¹ • x) ≤ 1
      rw [hph d⁻¹ (inv_pos.2 hd) x, hr]
      simp
    · rw [hr]
      refine gaugeFn_le_of_mem_smul hr0 ⟨r⁻¹ • x, ?_, smul_inv_smul₀ hrpos.ne' x⟩
      change k (r⁻¹ • x) ≤ 1
      rw [hph r⁻¹ (inv_pos.2 hrpos) x, hr, ← EReal.coe_mul, inv_mul_cancel₀ hrpos.ne']
      exact le_rfl
  · rw [gaugeFn_apply]
    refine le_iInf₂ fun a ha => ?_
    obtain ⟨ha0, z, hz, hzx⟩ := ha
    rcases eq_or_lt_of_le ha0 with rfl | hapos
    · have : x = 0 := by rw [← hzx]; simp
      rw [this, h0]
      exact le_rfl
    · have hzx' : a • z = x := hzx
      rw [← hzx', hph a hapos z]
      have hz1 : k z ≤ 1 := hz
      calc (a : EReal) * k z ≤ (a : EReal) * 1 :=
            mul_le_mul_of_nonneg_left hz1 (EReal.coe_nonneg.2 ha0)
        _ = (a : EReal) := by rw [mul_one]

/-- A function $k : E \to [-\infty, +\infty]$ is a gauge if and only if $k = \gamma(\cdot \mid C)$
for some nonempty convex set $C \subseteq E$.

The proof takes $C = \{x : k(x) \le 1\}$. This is the only choice of $C$ that is closed and
contains $0$ (`ConvexAnalysis.gaugeEquiv`). -/
theorem isGauge_iff : IsGauge k ↔ ∃ C : Set E, C.Nonempty ∧ Convex ℝ C ∧ k = gaugeFn C := by
  refine ⟨fun hk => ⟨{x | k x ≤ 1}, ⟨0, hk.zero_mem_level_one⟩, hk.convex_level_one,
      (gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero).symm⟩, ?_⟩
  rintro ⟨C, hne, hC, rfl⟩
  exact isGauge_gaugeFn hC hne

end IsGauge

/-!
### Gauges of sets that contain the origin

If $C$ is convex and contains $0$, then $aC \subseteq bC$ for $0 \le a \le b$. Hence the admissible
set $\{a \ge 0 : x \in aC\}$ is upward closed, and the sublevel sets of $\gamma(\cdot \mid C)$ are
intersections of dilates of $C$.
-/

section ZeroMem

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {x : E} {a b c : ℝ}

/-- If $C$ is convex and contains $0$, and $0 \le a \le b$, then $aC \subseteq bC$. -/
theorem smul_subset_smul_of_le (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (ha : 0 ≤ a) (hab : a ≤ b) :
    a • C ⊆ b • C := by
  rintro _ ⟨z, hz, rfl⟩
  rcases eq_or_lt_of_le ha with rfl | hapos
  · simpa using ⟨0, h0, by simp⟩
  · have hbpos : 0 < b := lt_of_lt_of_le hapos hab
    refine ⟨(a / b) • z, hC.smul_mem_of_zero_mem h0 hz ⟨by positivity, by
      rw [div_le_one hbpos]; exact hab⟩, ?_⟩
    change b • (a / b) • z = a • z
    rw [smul_smul, mul_div_cancel₀ _ hbpos.ne']

/-- If $C$ is convex and contains $0$, then for every $x$ the set $\{a \ge 0 : x \in aC\}$ is upward
closed. -/
theorem upClosed_gaugeSet (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (x : E) :
    UpClosed {a : ℝ | 0 ≤ a ∧ x ∈ a • C} :=
  fun _ ha _ hab => ⟨ha.1.trans hab, smul_subset_smul_of_le hC h0 ha.1 hab ha.2⟩

/-- Let $C$ be convex with $0 \in C$, and let $c \ge 0$. Then $\gamma(x \mid C) \le c$ if and only
if $x \in dC$ for every $d > c$. -/
theorem gaugeFn_le_coe_iff_forall_lt (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hc : 0 ≤ c) :
    gaugeFn C x ≤ (c : EReal) ↔ ∀ d : ℝ, c < d → x ∈ d • C := by
  rw [gaugeFn_apply, biInf_coe_le_coe_iff_forall_lt (upClosed_gaugeSet hC h0 x)]
  exact forall₂_congr fun d hd => ⟨fun h => h.2, fun h => ⟨le_of_lt (lt_of_le_of_lt hc hd), h⟩⟩

/-- Let $C$ be convex with $0 \in C$, and let $c \ge 0$. Then
$$\{x : \gamma(x \mid C) \le c\} = \bigcap_{d > c} dC.$$
-/
theorem setOf_gaugeFn_le (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hc : 0 ≤ c) :
    {x : E | gaugeFn C x ≤ (c : EReal)} = ⋂ d ∈ Ioi c, d • C := by
  ext x
  rw [mem_iInter₂]
  exact gaugeFn_le_coe_iff_forall_lt hC h0 hc

end ZeroMem

/-!
### Closed gauges

If $C$ is closed and convex and contains $0$, the sublevel sets of the gauge are the dilates
themselves, $\{x : \gamma(x \mid C) \le c\} = cC$ for $c > 0$, and the gauge is closed.
`ConvexAnalysis.gaugeEquiv` is the resulting bijection.
-/

section ClosedGauge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  {C : Set E} {x : E} {c : ℝ}

/-- Let $E$ carry a topology in which scalar multiplication is continuous, let $C \subseteq E$ be
closed and convex with $0 \in C$, and let $c > 0$. Then $\gamma(x \mid C) \le c$ if and only if
$x \in cC$.

The condition $c > 0$ is necessary: $\{x : \gamma(x \mid C) \le 0\}$ is the recession cone of
$C$, not $0 \cdot C = \{0\}$. -/
theorem gaugeFn_le_coe_iff (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) (hc : 0 < c) :
    gaugeFn C x ≤ (c : EReal) ↔ x ∈ c • C := by
  refine ⟨fun h => ?_, fun h => gaugeFn_le_of_mem_smul hc.le h⟩
  rw [gaugeFn_le_coe_iff_forall_lt hC h0 hc.le] at h
  rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne' C x]
  have hseq : Filter.Tendsto (fun n : ℕ => (c + 1 / (n + 1 : ℝ))⁻¹ • x) Filter.atTop
      (nhds (c⁻¹ • x)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => c + 1 / (n + 1 : ℝ)) Filter.atTop (nhds c) := by
      simpa using Filter.Tendsto.const_add c tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Continuous fun r : ℝ => r • x := continuous_id.smul continuous_const
    exact (h2.tendsto (c⁻¹)).comp (h1.inv₀ hc.ne')
  refine hcl.mem_of_tendsto hseq (Filter.Eventually.of_forall fun n => ?_)
  have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  have hd : c < c + 1 / (n + 1 : ℝ) := by linarith
  exact (mem_smul_set_iff_inv_smul_mem₀ (by linarith : c + 1 / (n + 1 : ℝ) ≠ 0) C x).1 (h _ hd)

/-- Let $C$ be a closed convex set with $0 \in C$, and let $c > 0$. Then
$\{x : \gamma(x \mid C) \le c\} = cC$. -/
theorem setOf_gaugeFn_le_pos (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) (hc : 0 < c) :
    {x : E | gaugeFn C x ≤ (c : EReal)} = c • C :=
  Set.ext fun _ => gaugeFn_le_coe_iff hC h0 hcl hc

/-- If $C$ is a closed convex set with $0 \in C$, then $\{x : \gamma(x \mid C) \le 1\} = C$.

Together with `ConvexAnalysis.gaugeFn_level_one`, this gives the bijection between the closed
gauges and the closed convex sets that contain $0$. -/
theorem setOf_gaugeFn_le_one (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) :
    {x : E | gaugeFn C x ≤ 1} = C := by
  have h := setOf_gaugeFn_le_pos hC h0 hcl one_pos
  rw [EReal.coe_one] at h
  rw [h, one_smul]

/-- The gauge of a closed convex set $C$ with $0 \in C$ is lower semicontinuous, because each of its
sublevel sets is an intersection of dilates of $C$. -/
theorem lowerSemicontinuous_gaugeFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) :
    LowerSemicontinuous (gaugeFn C) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro z
  have hset : gaugeFn C ⁻¹' Iic z = {x : E | gaugeFn C x ≤ z} := rfl
  rw [hset]
  induction z using EReal.rec with
  | bot =>
    have : {x : E | gaugeFn C x ≤ (⊥ : EReal)} = ∅ := by
      ext x
      simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, le_bot_iff]
      exact gaugeFn_ne_bot C x
    rw [this]; exact isClosed_empty
  | coe r =>
    rcases lt_or_ge r 0 with hr | hr
    · have : {x : E | gaugeFn C x ≤ (r : EReal)} = ∅ := by
        ext x
        simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false]
        exact fun hx => absurd (le_trans (gaugeFn_nonneg C x) hx)
          (not_le.2 (by exact_mod_cast hr))
      rw [this]; exact isClosed_empty
    · rw [setOf_gaugeFn_le hC h0 hr]
      exact isClosed_biInter fun d hd => hcl.smul_of_ne_zero (by
        have : (0 : ℝ) < d := lt_of_le_of_lt hr hd
        exact this.ne')
  | top =>
    have : {x : E | gaugeFn C x ≤ (⊤ : EReal)} = univ := by ext x; simp
    rw [this]; exact isClosed_univ

variable [IsTopologicalAddGroup E]

/-- Let $E$ be a topological vector space. The gauge of a closed convex set $C$ with $0 \in C$ is
closed in the sense of `ConvexAnalysis.ClosedConvex`: it equals its closure. -/
theorem closedConvex_gaugeFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) :
    ClosedConvex (gaugeFn C) :=
  (closedConvex_iff_lowerSemicontinuous (gaugeFn_ne_bot C)).2
      (lowerSemicontinuous_gaugeFn hC h0 hcl)

omit [Module ℝ E] [ContinuousSMul ℝ E] in
/-- If $k$ is closed in the sense of `ConvexAnalysis.ClosedConvex`, then the sublevel set
$\{x : k(x) \le 1\}$ is closed. -/
theorem isClosed_setOf_le_one {k : E → EReal} (hc : ClosedConvex k) :
    IsClosed {x : E | k x ≤ 1} :=
  ClosedConvex.lowerSemicontinuous hc |>.isClosed_preimage 1

/-- The **gauge correspondence**. Let $E$ be a topological vector space. The maps
$C \mapsto \gamma(\cdot \mid C)$ and $k \mapsto \{x : k(x) \le 1\}$ are inverse bijections
between the closed convex subsets of $E$ that contain $0$ and the closed gauges on $E$.

This is the counterpart for gauges of `ConvexAnalysis.supportEquiv` in
`Numlib.Analysis.Convex.Duality.Support`. [rockafellar1970convex] states this correspondence in
§15, before Corollary 15.1.1. -/
noncomputable def gaugeEquiv (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousSMul ℝ E] [IsTopologicalAddGroup E] :
    {C : Set E // Convex ℝ C ∧ IsClosed C ∧ (0 : E) ∈ C} ≃
      {k : E → EReal // IsGauge k ∧ ClosedConvex k} where
  toFun C := ⟨gaugeFn C.1, isGauge_gaugeFn C.2.1 ⟨0, C.2.2.2⟩,
    closedConvex_gaugeFn C.2.1 C.2.2.2 C.2.2.1⟩
  invFun k := ⟨{x | k.1 x ≤ 1}, k.2.1.convex_level_one, isClosed_setOf_le_one k.2.2,
    k.2.1.zero_mem_level_one⟩
  left_inv C := Subtype.ext (setOf_gaugeFn_le_one C.2.1 C.2.2.2 C.2.2.1)
  right_inv k := Subtype.ext
    (gaugeFn_level_one k.2.1.nonneg k.2.1.posHomogeneous k.2.1.map_zero)

end ClosedGauge

/-!
### The gauge of a polar set

The gauge of $C^\circ$ is the support function of $C$. [rockafellar1970convex] states this for a
closed convex set $C$ that contains $0$; the proof here uses only $0 \in C$.
-/

section GaugePolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

/-- Let $C \subseteq E$ with $0 \in C$. Then the gauge of the polar set is the support function of
$C$:
$$\gamma(\cdot \mid C^\circ) = \delta^*(\cdot \mid C).$$
This is part of Theorem 14.5 of [rockafellar1970convex].

[rockafellar1970convex] assumes that $C$ is closed and convex. Here only $0 \in C$ is needed: it
makes $\delta^*(\cdot \mid C)$ nonnegative, and then the two infima agree scalar by scalar. -/
theorem gaugeFn_polarSet (h0 : (0 : E) ∈ C) : gaugeFn (polarSet B C) = supportFn B C := by
  funext y
  have hsupp0 : (0 : EReal) ≤ supportFn B C y := by
    have h := le_supportFn (B := B) h0 y
    rwa [map_zero, LinearMap.zero_apply, EReal.coe_zero] at h
  refine le_antisymm ?_ ?_
  · by_cases htop : supportFn B C y = ⊤
    · rw [htop]; exact le_top
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simp [h] at hsupp0) (lt_top_iff_ne_top.2 htop)
    have hr0 : (0 : ℝ) ≤ r := by rw [hr] at hsupp0; exact EReal.coe_nonneg.1 hsupp0
    have hbound : ∀ x ∈ C, B x y ≤ r := supportFn_le_coe_iff.1 (le_of_eq hr)
    rw [hr]
    refine le_coe_of_forall_gt_le fun d hd => ?_
    have hd0 : (0 : ℝ) < d := lt_of_le_of_lt hr0 hd
    refine gaugeFn_le_of_mem_smul hd0.le ⟨d⁻¹ • y, fun x hx => ?_, smul_inv_smul₀ hd0.ne' y⟩
    rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hd0, mul_one]
    exact le_of_lt (lt_of_le_of_lt (hbound x hx) hd)
  · rw [gaugeFn_apply]
    refine le_iInf₂ fun a ha => ?_
    obtain ⟨ha0, w, hw, hwy⟩ := ha
    rw [supportFn_le_coe_iff]
    intro x hx
    have hy : a • w = y := hwy
    rw [← hy, map_smul, smul_eq_mul]
    calc a * B x w ≤ a * 1 := by
          exact mul_le_mul_of_nonneg_left (hw x hx) ha0
      _ = a := mul_one a

/-- Let $E$ be a locally convex space, let the pairing $B$ be compatible with the topology of $E$,
and let $C \subseteq E$ be closed and convex with $0 \in C$. Then the support function of the
polar set, taken with respect to the flipped pairing, is the gauge of $C$:
$$\delta^*(\cdot \mid C^\circ) = \gamma(\cdot \mid C).$$
This is part of Theorem 14.5 of [rockafellar1970convex].

The proof applies `ConvexAnalysis.gaugeFn_polarSet` to $C^\circ$, which contains $0$, and uses
the bipolar theorem $C^{\circ\circ} = C$. -/
theorem supportFn_polarSet [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [IsCompatiblePairing B] (hconv : Convex ℝ C) (hcl : IsClosed C)
    (h0 : (0 : E) ∈ C) : supportFn B.flip (polarSet B C) = gaugeFn C := by
  conv_rhs => rw [← polarSet_polarSet (B := B) hconv hcl h0]
  exact (gaugeFn_polarSet (zero_mem_polarSet B C)).symm

end GaugePolar

/-!
### The recession cone and the lineality space as polars

For a closed convex set $C$ that contains $0$, the recession cone $0^+ C$ and the closed convex cone
generated by $C^\circ$ are polar to each other, and the lineality space of $C$ is the annihilator of
$C^\circ$. The proof in [rockafellar1970convex] identifies $0^+ C$ as the largest closed convex cone
in $C$; the proof here identifies it directly as a polar, which needs only the bipolar theorem.
-/

section RecessionLineality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- If $0 \in C$, then every recession direction $x$ of $C$ satisfies $\langle x, y \rangle \le 0$
for every $y \in C^\circ$:
$$0^+ C \subseteq \{x : \langle x, y \rangle \le 0 \ \forall y \in C^\circ\}.$$
-/
theorem recessionCone_subset_polarCone_polarSet (h0 : (0 : E) ∈ C) :
    recessionCone C ⊆ polarCone B.flip (polarSet B C) := by
  intro v hv y hy
  rw [LinearMap.flip_apply]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨t, ht⟩ := exists_gt (1 / B v y)
  have ht0 : (0 : ℝ) ≤ t := le_trans (by positivity) ht.le
  have hmem : (0 : E) + t • v ∈ C := hv 0 h0 t ht0
  rw [zero_add] at hmem
  have := hy _ hmem
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  rw [div_lt_iff₀ hcon] at ht
  nlinarith

/-- Let $E$ be a locally convex space, let the pairing $B$ be compatible with the topology of $E$,
and let $C \subseteq E$ be closed and convex with $0 \in C$. Then the recession cone of $C$ is
the polar cone of $C^\circ$:
$$0^+ C = \{x : \langle x, y \rangle \le 0 \ \forall y \in C^\circ\}.$$
This is part of Theorem 14.6 of [rockafellar1970convex]. -/
theorem recessionCone_eq_polarCone_polarSet [IsCompatiblePairing B] (hconv : Convex ℝ C)
    (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    recessionCone C = polarCone B.flip (polarSet B C) := by
  refine subset_antisymm (recessionCone_subset_polarCone_polarSet h0) fun v hv x hx a ha => ?_
  rw [← polarSet_polarSet (B := B) hconv hcl h0]
  intro y hy
  simp only [LinearMap.flip_apply, map_add, map_smul, smul_eq_mul]
  have h1 : B x y ≤ 1 := by
    have := hx
    rw [← polarSet_polarSet (B := B) hconv hcl h0] at this
    exact this y hy
  have h2 : B v y ≤ 0 := hv y hy
  nlinarith

/-- Let $E$ and $F$ be locally convex spaces, let $B$ and its flip be compatible pairings, and let
$C \subseteq E$ be closed and convex with $0 \in C$. Then the recession cone of $C^\circ$ is the
polar cone of $C$:
$$0^+(C^\circ) = \{y : \langle x, y \rangle \le 0 \ \forall x \in C\}.$$

The proof applies `ConvexAnalysis.recessionCone_eq_polarCone_polarSet` to $C^\circ$, whose polar
is $C$ (`ConvexAnalysis.polarSet_polarSet`). Both spaces need a topology because the recession
cone lies in $F$. -/
theorem recessionCone_polarSet [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    recessionCone (polarSet B C) = polarCone B C := by
  have h := recessionCone_eq_polarCone_polarSet (B := B.flip) (C := polarSet B C)
    (convex_polarSet B C) isClosed_polarSet (zero_mem_polarSet B C)
  rwa [LinearMap.flip_flip, polarSet_polarSet (B := B) hconv hcl h0] at h

/-- Let $E$ and $F$ be locally convex spaces, let $B$ and its flip be compatible pairings, and let
$C \subseteq E$ be closed and convex with $0 \in C$. Then the polar cone of $0^+ C$ is the
closed convex cone generated by $C^\circ$:
$$(0^+ C)^\circ = \operatorname{cl} \operatorname{cone} C^\circ.$$
This is part of Theorem 14.6 of [rockafellar1970convex].

The cone generated by $C^\circ$ is `PointedCone.hull ℝ (polarSet B C)`, and the polar cone is
`ConvexAnalysis.polarCone`. -/
theorem polarCone_recessionCone [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    polarCone B (recessionCone C) =
      closure (PointedCone.hull ℝ (polarSet B C) : Set F) := by
  rw [recessionCone_eq_polarCone_polarSet (B := B) hconv hcl h0,
    ← polarCone_hull B.flip (polarSet B C)]
  have h := polarCone_polarCone (B := B.flip)
    (K := (PointedCone.hull ℝ (polarSet B C) : Set F))
    ((PointedCone.hull ℝ (polarSet B C) : ConvexCone ℝ F).convex)
    (isCone_coe_pointedCone _) ⟨0, (PointedCone.hull ℝ (polarSet B C)).zero_mem⟩
  rwa [LinearMap.flip_flip] at h

/-- Let $E$ be a locally convex space, let the pairing $B$ be compatible with the topology of $E$,
and let $C \subseteq E$ be closed and convex with $0 \in C$. Then the lineality space of $C$ is
the annihilator of its polar:
$$\operatorname{lin} C = \{x : \langle x, y \rangle = 0 \ \forall y \in C^\circ\}.$$
This is part of Theorem 14.6 of [rockafellar1970convex]. -/
theorem linealitySpace_eq_setOf_pairing_eq_zero [IsCompatiblePairing B] (hconv : Convex ℝ C)
    (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    linealitySpace C = {x : E | ∀ y ∈ polarSet B C, B x y = 0} := by
  ext v
  rw [mem_linealitySpace, recessionCone_eq_polarCone_polarSet (B := B) hconv hcl h0]
  constructor
  · rintro ⟨h1, h2⟩ y hy
    have e1 : B v y ≤ 0 := h1 y hy
    have e2 : B (-v) y ≤ 0 := h2 y hy
    rw [map_neg, LinearMap.neg_apply] at e2
    linarith
  · intro h
    exact ⟨fun y hy => le_of_eq (h y hy), fun y hy => by
      rw [LinearMap.flip_apply, map_neg, LinearMap.neg_apply, h y hy, neg_zero]⟩

/-- Let $E$ and $F$ be locally convex spaces, let $B$ and its flip be compatible pairings, and let
$C \subseteq E$ be closed and convex with $0 \in C$. Then the polar cone of the lineality space
of $C$ is the closed linear span of $C^\circ$:
$$(\operatorname{lin} C)^\circ = \operatorname{cl} \operatorname{span} C^\circ.$$
This is part of Theorem 14.6 of [rockafellar1970convex]. -/
theorem polarCone_linealitySpace [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    polarCone B (linealitySpace C) =
      closure (Submodule.span ℝ (polarSet B C) : Set F) := by
  have hlin : linealitySpace C =
      polarCone B.flip (Submodule.span ℝ (polarSet B C) : Set F) := by
    rw [linealitySpace_eq_setOf_pairing_eq_zero (B := B) hconv hcl h0,
      polarCone_coe_submodule' B.flip (Submodule.span ℝ (polarSet B C))]
    ext v
    simp only [Set.mem_ofPred, LinearMap.flip_apply]
    refine ⟨fun h y hy => ?_, fun h y hy => h y (Submodule.subset_span hy)⟩
    exact Submodule.span_induction (fun z hz => h z hz) (map_zero (B v))
      (fun z w _ _ hz hw => by rw [map_add, hz, hw, add_zero])
      (fun a z _ hz => by rw [map_smul, hz, smul_zero]) hy
  rw [hlin]
  have h := polarCone_polarCone (B := B.flip)
    (K := (Submodule.span ℝ (polarSet B C) : Set F))
    (Submodule.span ℝ (polarSet B C)).convex
    (isCone_coe_submodule _) ⟨0, (Submodule.span ℝ (polarSet B C)).zero_mem⟩
  rwa [LinearMap.flip_flip] at h

end RecessionLineality

/-!
### The dimension relations for a polar set

In finite dimension $n$, $\dim C^\circ = n - \operatorname{lin} C$ and
$\operatorname{lin} C^\circ = n - \dim C$. These are the orthogonality relations above, read through
`Module.finrank`: the polar of a subspace is its annihilator, and the annihilator of a subspace has
the complementary dimension. For a set that contains $0$, the affine span and the linear span agree;
this is `vectorSpan_eq_span_of_zero_mem` in `Numlib.LinearAlgebra.Subspace`.
-/

section PolarDimension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

/-- Let $E$ and $F$ be finite-dimensional normed spaces, let $B$ be a compatible pairing, and let
$M \subseteq E$ be a subspace. Then the polar $M^\perp = \{y : \langle x, y \rangle = 0 \
\forall x \in M\}$ has the complementary dimension:
$$\dim M + \dim M^\perp = \dim F.$$

The proof is the rank–nullity theorem for the map $F \to M^*$ that the pairing induces. This map
is onto, because $y \mapsto \langle \cdot, y \rangle$ is onto $E^*$ (by compatibility, and
because every linear functional is continuous in finite dimension) and restriction $E^* \to M^*$
is onto. Its kernel is $M^\perp$. -/
theorem finrank_add_finrank_polarSubmodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    (M : Submodule ℝ E) :
    Module.finrank ℝ M + Module.finrank ℝ (polarSubmodule B M) = Module.finrank ℝ F := by
  classical
  have hflip : Function.Surjective (B.flip : F →ₗ[ℝ] Module.Dual ℝ E) := by
    intro g
    obtain ⟨y, hy⟩ := exists_pairing_eq B (LinearMap.toContinuousLinearMap g)
    refine ⟨y, LinearMap.ext fun x => ?_⟩
    have h := hy x
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    rw [LinearMap.flip_apply, ← h]
  have hsurj : Function.Surjective ((Submodule.subtype M).dualMap.comp B.flip) :=
    (LinearMap.dualMap_surjective_of_injective (Submodule.injective_subtype M)).comp hflip
  have hker : LinearMap.ker ((Submodule.subtype M).dualMap.comp B.flip) = polarSubmodule B M := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, polarSubmodule, Submodule.mem_comap,
      Submodule.mem_dualAnnihilator, LinearMap.flip_apply]
    constructor
    · intro h w hw
      have hval := congrArg (fun g : Module.Dual ℝ M => g ⟨w, hw⟩) h
      simpa using hval
    · intro h
      ext m
      simpa using h (m : E) m.2
  have hrk := LinearMap.finrank_range_add_finrank_ker ((Submodule.subtype M).dualMap.comp B.flip)
  rw [LinearMap.range_eq_top.2 hsurj, hker, finrank_top, Subspace.dual_finrank_eq] at hrk
  exact hrk

/-- Let $E$ and $F$ be finite-dimensional normed spaces, let $B$ and its flip be compatible
pairings, and let $C \subseteq E$ be closed and convex with $0 \in C$. Then
$$\dim C^\circ + \operatorname{lin} C = \dim F,$$
where $\dim C^\circ$ is the dimension of the affine span of $C^\circ$ and $\operatorname{lin} C$
is the dimension of the lineality space of $C$. This is
$\dim C^\circ = n - \operatorname{lin} C$ of Corollary 14.6.1 of [rockafellar1970convex],
written without truncated subtraction.

The linear span of $C^\circ$ is the polar of the lineality space of $C$
(`ConvexAnalysis.polarCone_linealitySpace`; the closure is redundant in finite dimension), and
the affine span of $C^\circ$ is its linear span because $0 \in C^\circ$. -/
theorem finrank_vectorSpan_polarSet_add_lineality [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    Module.finrank ℝ (vectorSpan ℝ (polarSet B C)) + lineality C = Module.finrank ℝ F := by
  have hspan : vectorSpan ℝ (polarSet B C) = Submodule.span ℝ (polarSet B C) :=
    vectorSpan_eq_span_of_zero_mem (zero_mem_polarSet B C)
  have hpol : polarSubmodule B (linealitySubmodule C) = Submodule.span ℝ (polarSet B C) := by
    refine SetLike.coe_injective ?_
    rw [coe_polarSubmodule, coe_linealitySubmodule,
      polarCone_linealitySpace (B := B) hconv hcl h0,
      (Submodule.closed_of_finiteDimensional (Submodule.span ℝ (polarSet B C))).closure_eq]
  rw [hspan, ← hpol, lineality, add_comm]
  exact finrank_add_finrank_polarSubmodule B (linealitySubmodule C)

/-- Let $E$ and $F$ be finite-dimensional normed spaces, let $B$ and its flip be compatible
pairings, and let $C \subseteq E$ be closed and convex with $0 \in C$. Then
$$\dim C + \operatorname{lin} C^\circ = \dim E,$$
where $\dim C$ is the dimension of the affine span of $C$. This is
$\operatorname{lin} C^\circ = n - \dim C$ of Corollary 14.6.1 of [rockafellar1970convex],
written without truncated subtraction.

The proof applies `ConvexAnalysis.finrank_vectorSpan_polarSet_add_lineality` to the polar pair
in the other order, with $C^{\circ\circ} = C$. The third relation of the source,
$\operatorname{rank} C^\circ = \operatorname{rank} C$, follows from the two: both
$\dim C^\circ + \operatorname{lin} C$ and $\dim C + \operatorname{lin} C^\circ$ equal $n$. -/
theorem finrank_vectorSpan_add_lineality_polarSet [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    Module.finrank ℝ (vectorSpan ℝ C) + lineality (polarSet B C) = Module.finrank ℝ E := by
  have hcvx : Convex ℝ (polarSet B C) := by
    intro y hy z hz s t hs ht hst x hx
    have h1 : B x y ≤ 1 := hy x hx
    have h2 : B x z ≤ 1 := hz x hx
    have hval : B x (s • y + t • z) = s * B x y + t * B x z := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hval]
    nlinarith
  have h := finrank_vectorSpan_polarSet_add_lineality (B := B.flip) (C := polarSet B C)
    hcvx isClosed_polarSet (zero_mem_polarSet B C)
  rwa [polarSet_polarSet (B := B) hconv hcl h0] at h

end PolarDimension

/-!
### The polar of a sublevel set

For a nonnegative convex function $f$ with $f(0) \le 0$ and $\alpha > 0$, the polar of
$\{f \le \alpha\}$ and the set $\alpha^{-1} \{f^* \le \alpha\}$ agree up to a factor of $2$.
-/

section SublevelPolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {α : ℝ}

/-- Let $f$ be convex with $f(0) \le 0$, and let $0 \le t \le 1$. If $f(x) \le r$, then
$f(tx) \le tr$. -/
theorem ConvexFn.smul_le_coe (hconv : ConvexFn f) (h0 : f 0 ≤ 0) {t r : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {x : E} (hx : f x ≤ (r : EReal)) : f (t • x) ≤ ((t * r : ℝ) : EReal) := by
  have h0' : f 0 ≤ ((0 : ℝ) : EReal) := by rwa [EReal.coe_zero]
  have h := hconv.epi_combo hx h0' (a := t) (b := 1 - t) ht0 (by linarith) (by ring)
  simpa using h

/-- If $f(0) \le 0$, then the conjugate $f^*$ is nonnegative. -/
theorem zero_le_convexConj (h0 : f 0 ≤ 0) (y : F) : 0 ≤ convexConj B f y := by
  refine le_trans ?_ (sub_le_convexConj B f 0 y)
  rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_sub, EReal.le_neg,
    neg_zero]
  exact h0

/-- If $f$ is nonnegative and $f(0) \le 0$, then $f^*(0) = 0$. -/
theorem convexConj_zero_eq_zero (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0) : convexConj B f 0 = 0 := by
  refine le_antisymm ?_ (zero_le_convexConj h0 0)
  rw [convexConj_apply]
  refine iSup_le fun x => ?_
  rw [map_zero, EReal.coe_zero, zero_sub, EReal.neg_le, neg_zero]
  exact hnn x

/-- Let $f$ be convex and nonnegative with $f(0) \le 0$, and let $\alpha > 0$. Then
$$\alpha \{x : f(x) \le \alpha\}^\circ \subseteq \{y : f^*(y) \le \alpha\}.$$
This is the first inclusion of `ConvexAnalysis.polarSet_setOf_le_subset_and_subset`, scaled by
$\alpha$.

[rockafellar1970convex] proves this with the positively homogeneous function generated by
$f^* + \alpha$. The proof here is direct: if $f(x) > \alpha$, the point $(\alpha / f(x))\, x$
lies in the sublevel set, and rescaling its inequality gives $\langle x, y \rangle \le f(x)$. -/
theorem smul_polarSet_setOf_le_subset (hconv : ConvexFn f) (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0)
    (hα : 0 < α) :
    α • polarSet B {x : E | f x ≤ (α : EReal)} ⊆ {y : F | convexConj B f y ≤ (α : EReal)} := by
  rintro _ ⟨w, hw, rfl⟩
  change convexConj B f (α • w) ≤ (α : EReal)
  rw [convexConj_apply]
  refine iSup_le fun x => ?_
  have hBx : B x (α • w) = α * B x w := by rw [map_smul, smul_eq_mul]
  by_cases hfx : f x ≤ (α : EReal)
  · have h1 : B x w ≤ 1 := hw x hfx
    have h2 : B x (α • w) ≤ α := by rw [hBx]; nlinarith
    calc ((B x (α • w) : ℝ) : EReal) - f x
        ≤ ((α : ℝ) : EReal) - 0 := EReal.sub_le_sub (EReal.coe_le_coe_iff.2 h2) (hnn x)
      _ = (α : EReal) := by rw [sub_zero]
  · rw [not_le] at hfx
    rcases eq_or_lt_of_le (le_top (a := f x)) with htop | hlt
    · rw [htop]
      simp
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hlt
    rw [hr] at hfx
    have hαr : α < r := EReal.coe_lt_coe_iff.1 hfx
    have hr0 : (0 : ℝ) < r := lt_trans hα hαr
    have ht : f ((α / r) • x) ≤ ((α : ℝ) : EReal) := by
      have := ConvexFn.smul_le_coe hconv h0 (t := α / r) (r := r) (by positivity)
        (by rw [div_le_one hr0]; linarith) (le_of_eq hr)
      rwa [div_mul_cancel₀ _ hr0.ne'] at this
    have h1 : B ((α / r) • x) w ≤ 1 := hw _ ht
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : B x (α • w) ≤ r := by
      have hkey : α * B x w = r * (α / r * B x w) := by field_simp
      rw [hBx, hkey]
      exact mul_le_of_le_one_right hr0.le h1
    rw [hr]
    calc ((B x (α • w) : ℝ) : EReal) - (r : EReal)
        ≤ ((r : ℝ) : EReal) - (r : EReal) := EReal.sub_le_sub
          (EReal.coe_le_coe_iff.2 h2) le_rfl
      _ = 0 := by rw [← EReal.coe_sub, sub_self, EReal.coe_zero]
      _ ≤ (α : EReal) := EReal.coe_nonneg.2 hα.le

/-- Let $f$ be nonnegative, and let $\alpha > 0$. Then
$$\{y : f^*(y) \le \alpha\} \subseteq 2\alpha \{x : f(x) \le \alpha\}^\circ.$$
This is the second inclusion of `ConvexAnalysis.polarSet_setOf_le_subset_and_subset`, scaled by
$\alpha$. Its proof uses only Fenchel's inequality. -/
theorem setOf_convexConj_le_subset_smul_polarSet (hnn : ∀ x, 0 ≤ f x) (hα : 0 < α) :
    {y : F | convexConj B f y ≤ (α : EReal)} ⊆ (2 * α) • polarSet B
        {x : E | f x ≤ (α : EReal)} := by
  intro y hy
  have hy' : convexConj B f y ≤ (α : EReal) := hy
  have h2α : (2 * α) ≠ 0 := by positivity
  rw [mem_smul_set_iff_inv_smul_mem₀ h2α]
  intro x hx
  have hx' : f x ≤ (α : EReal) := hx
  rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 * α), mul_one]
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (fun h => by simpa [h] using hnn x) (lt_of_le_of_lt hx' (EReal.coe_lt_top α))
  have hrα : r ≤ α := by rw [hr] at hx'; exact EReal.coe_le_coe_iff.1 hx'
  have hsub := le_trans (sub_le_convexConj B f x y) hy'
  rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hsub
  linarith

/-- Let $f : E \to [-\infty, +\infty]$ be convex and nonnegative with $f(0) \le 0$, and let
$\alpha > 0$. Then
$$\{x : f(x) \le \alpha\}^\circ \subseteq \alpha^{-1} \{y : f^*(y) \le \alpha\} \subseteq 2 \{x
  : f(x) \le \alpha\}^\circ.$$
This is Theorem 14.7 of [rockafellar1970convex].

[rockafellar1970convex] assumes that $f$ is closed and $f(0) = 0$; the inclusions need neither
closedness nor more than $f(0) \le 0$. The two inclusions are
`ConvexAnalysis.smul_polarSet_setOf_le_subset` and
`ConvexAnalysis.setOf_convexConj_le_subset_smul_polarSet`. -/
theorem polarSet_setOf_le_subset_and_subset (hconv : ConvexFn f) (hnn : ∀ x, 0 ≤ f x)
    (h0 : f 0 ≤ 0) (hα : 0 < α) :
    polarSet B {x : E | f x ≤ (α : EReal)} ⊆ α⁻¹ • {y : F | convexConj B f y ≤ (α : EReal)} ∧
      α⁻¹ • {y : F | convexConj B f y ≤ (α : EReal)} ⊆
        (2 : ℝ) • polarSet B {x : E | f x ≤ (α : EReal)} := by
  constructor
  · intro y hy
    have h : α⁻¹ • (α • polarSet B {x : E | f x ≤ (α : EReal)}) ⊆
        α⁻¹ • {y : F | convexConj B f y ≤ (α : EReal)} :=
      smul_set_mono (smul_polarSet_setOf_le_subset hconv hnn h0 hα)
    rw [smul_smul, inv_mul_cancel₀ hα.ne', one_smul] at h
    exact h hy
  · intro y hy
    have h : α⁻¹ • {y : F | convexConj B f y ≤ (α : EReal)} ⊆
        α⁻¹ • ((2 * α) • polarSet B {x : E | f x ≤ (α : EReal)}) :=
      smul_set_mono (setOf_convexConj_le_subset_smul_polarSet (B := B) hnn hα)
    rw [smul_smul] at h
    have hcalc : α⁻¹ * (2 * α) = 2 := by field_simp
    rw [hcalc] at h
    exact h hy

end SublevelPolar

/-!
### The polar of a gauge

The polar of a gauge is $k^\circ(y) = \inf \{\mu \ge 0 : \langle x, y \rangle \le \mu k(x) \ \forall
x\}$. This section shows that $k^\circ$ is the support function of $\{k \le 1\}$, hence a closed
gauge, and that $k^\circ = \gamma(\cdot \mid C^\circ)$ when $k = \gamma(\cdot \mid C)$.
-/

section PolarGauge

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {k : E → EReal} {C : Set E} {y : F}

/-- The **polar** of a function $k : E \to [-\infty, +\infty]$ with respect to the pairing $B$ is
the function on $F$
$$k^\circ(y) = \inf \{\mu \in \mathbb{R} : \mu \ge 0,\ \langle x, y \rangle \le \mu k(x) \
  \forall x \in E\}.$$
It is intended for gauges $k$.

The product $\mu k(x)$ is multiplication in `EReal`, so $0 \cdot (+\infty) = 0$. Hence $\mu = 0$
is admissible only when $\langle x, y \rangle \le 0$ for every $x$, which is the classical
reading of the case $k^\circ(y) = 0$. The infimum does not depend on this convention, because
the admissible set is upward closed in $[0, \infty)$. -/
noncomputable def polarGauge (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (k : E → EReal) : F → EReal :=
  fun y => ⨅ μ ∈ {μ : ℝ | 0 ≤ μ ∧ ∀ x : E, ((B x y : ℝ) : EReal) ≤ (μ : EReal) * k x}, (μ : EReal)

/-- The defining formula $k^\circ(y) = \inf \{\mu \ge 0 : \langle x, y \rangle \le \mu k(x) \
\forall x\}$. -/
theorem polarGauge_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (k : E → EReal) (y : F) :
    polarGauge B k y =
      ⨅ μ ∈ {μ : ℝ | 0 ≤ μ ∧ ∀ x : E, ((B x y : ℝ) : EReal) ≤ (μ : EReal) * k x}, (μ : EReal) :=
  rfl

/-- If $\mu \ge 0$ and $\langle x, y \rangle \le \mu k(x)$ for every $x$, then $k^\circ(y) \le \mu$.
-/
theorem polarGauge_le_of_forall {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ∀ x : E, ((B x y : ℝ) : EReal) ≤ (μ : EReal) * k x) : polarGauge B k y ≤ (μ : EReal) :=
  iInf₂_le μ ⟨hμ, h⟩

/-- The polar $k^\circ$ of any function $k$ is nonnegative. -/
theorem polarGauge_nonneg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (k : E → EReal) (y : F) :
    0 ≤ polarGauge B k y :=
  zero_le_biInf_coe fun _ hμ => hμ.1

/-- Let $k$ be nonnegative and positively homogeneous with $k(0) = 0$. Then the polar of $k$ is the
support function of its unit sublevel set:
$$k^\circ = \delta^*(\cdot \mid \{x : k(x) \le 1\}).$$
This is part of Theorem 15.1 of [rockafellar1970convex].

Convexity of $k$ is not used. -/
theorem polarGauge_eq_supportFn (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    polarGauge B k = supportFn B {x : E | k x ≤ 1} := by
  have h0D : (0 : E) ∈ {x : E | k x ≤ 1} := by change k 0 ≤ 1; rw [h0]; exact zero_le_one
  funext y
  have hs0 : (0 : EReal) ≤ supportFn B {x : E | k x ≤ 1} y := by
    have h := le_supportFn (B := B) h0D y
    rwa [map_zero, LinearMap.zero_apply, EReal.coe_zero] at h
  refine le_antisymm ?_ ?_
  · by_cases htop : supportFn B {x : E | k x ≤ 1} y = ⊤
    · rw [htop]; exact le_top
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simp [h] at hs0) (lt_top_iff_ne_top.2 htop)
    have hr0 : (0 : ℝ) ≤ r := by rw [hr] at hs0; exact EReal.coe_nonneg.1 hs0
    have hbound : ∀ x, k x ≤ 1 → B x y ≤ r := supportFn_le_coe_iff.1 (le_of_eq hr)
    rw [hr]
    refine le_coe_of_forall_gt_le fun d hd => ?_
    have hd0 : (0 : ℝ) < d := lt_of_le_of_lt hr0 hd
    refine polarGauge_le_of_forall hd0.le fun x => ?_
    rcases eq_or_lt_of_le (le_top (a := k x)) with htopx | hltx
    · rw [htopx, EReal.coe_mul_top_of_pos hd0]
      exact le_top
    obtain ⟨sx, hsx⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hltx
    have hsx0 : (0 : ℝ) ≤ sx := by
      have := hnn x; rw [hsx] at this; exact EReal.coe_nonneg.1 this
    rw [hsx, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    rcases eq_or_lt_of_le hsx0 with hzero | hpos
    · have hray : ∀ t : ℝ, 0 < t → t * B x y ≤ r := by
        intro t ht
        have hkt : k (t • x) ≤ 1 := by
          rw [hph t ht x, hsx, ← hzero]
          simp
        have hb := hbound _ hkt
        rwa [map_smul, LinearMap.smul_apply, smul_eq_mul] at hb
      have hle0 : B x y ≤ 0 := by
        by_contra hcon
        rw [not_le] at hcon
        have ht : (0 : ℝ) < (r + 1) / B x y := by positivity
        have hb := hray _ ht
        rw [div_mul_cancel₀ _ hcon.ne'] at hb
        linarith
      rw [← hzero]
      nlinarith
    · have hmem : k (sx⁻¹ • x) ≤ 1 := by
        rw [hph _ (inv_pos.2 hpos) x, hsx, ← EReal.coe_mul, inv_mul_cancel₀ hpos.ne']
        exact le_rfl
      have hb := hbound _ hmem
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hpos] at hb
      nlinarith
  · rw [polarGauge_apply]
    refine le_iInf₂ fun μ hμ => ?_
    obtain ⟨hμ0, hμk⟩ := hμ
    rw [supportFn_le_coe_iff]
    intro x hx
    have h2 : (μ : EReal) * k x ≤ (μ : EReal) * 1 :=
      mul_le_mul_of_nonneg_left hx (EReal.coe_nonneg.2 hμ0)
    rw [mul_one] at h2
    exact EReal.coe_le_coe_iff.1 (le_trans (hμk x) h2)

/-- Let $k$ be nonnegative and positively homogeneous with $k(0) = 0$. Then $k^\circ$ is a gauge.
This is part of Theorem 15.1 of [rockafellar1970convex]. -/
theorem isGauge_polarGauge (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    IsGauge (polarGauge B k) := by
  have h0D : (0 : E) ∈ {x : E | k x ≤ 1} := by change k 0 ≤ 1; rw [h0]; exact zero_le_one
  rw [polarGauge_eq_supportFn hnn hph h0]
  refine ⟨fun y => ?_, posHomogeneous_supportFn B _, convexFn_supportFn B _,
    supportFn_zero ⟨0, h0D⟩⟩
  have h := le_supportFn (B := B) h0D y
  rwa [map_zero, LinearMap.zero_apply, EReal.coe_zero] at h

/-- Let $F$ be a topological additive group, let every $\langle x, \cdot \rangle$ be continuous on
$F$, and let $k$ be nonnegative and positively homogeneous with $k(0) = 0$. Then $k^\circ$ is
closed in the sense of `ConvexAnalysis.ClosedConvex`. This is part of Theorem 15.1 of
[rockafellar1970convex]. -/
theorem closedConvex_polarGauge [TopologicalSpace F] [IsTopologicalAddGroup F]
    [IsContinuousPairing B.flip] (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    ClosedConvex (polarGauge B k) := by
  rw [polarGauge_eq_supportFn hnn hph h0]
  exact closedConvex_supportFn

/-- For every set $C \subseteq E$, the unit sublevel set of its gauge has the same polar as $C$:
$$\{x : \gamma(x \mid C) \le 1\}^\circ = C^\circ.$$
-/
theorem polarSet_setOf_gaugeFn_le_one (C : Set E) :
    polarSet B {x : E | gaugeFn C x ≤ 1} = polarSet B C := by
  refine subset_antisymm (polarSet_anti fun x hx => ?_) fun y hy x hx => ?_
  · exact gaugeFn_le_of_mem_smul zero_le_one ⟨x, hx, one_smul ℝ x⟩
  · have hx' : gaugeFn C x ≤ 1 := hx
    refine le_of_forall_gt_imp_ge_of_dense fun q hq => ?_
    have hlt : gaugeFn C x < ((q : ℝ) : EReal) := by
      refine lt_of_le_of_lt hx' ?_
      rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) by rw [EReal.coe_one]]
      exact EReal.coe_lt_coe_iff.2 hq
    obtain ⟨a, ha0, ⟨z, hz, hza⟩, halt⟩ := gaugeFn_lt_iff.1 hlt
    have haq : a < q := EReal.coe_lt_coe_iff.1 halt
    have hzx : a • z = x := hza
    have hzy : B z y ≤ 1 := hy z hz
    rw [← hzx, map_smul, LinearMap.smul_apply, smul_eq_mul]
    nlinarith

/-- Let $C$ be nonempty and convex. Then the polar of the gauge of $C$ is the gauge of the polar
set:
$$\gamma(\cdot \mid C)^\circ = \gamma(\cdot \mid C^\circ).$$
This is part of Theorem 15.1 of [rockafellar1970convex].

$C$ need not contain $0$ or be closed, because $C$ and $\{x : \gamma(x \mid C) \le 1\}$ have the
same polar, and the second set contains $0$. -/
theorem polarGauge_gaugeFn (hC : Convex ℝ C) (hne : C.Nonempty) :
    polarGauge B (gaugeFn C) = gaugeFn (polarSet B C) := by
  have hg := isGauge_gaugeFn hC hne
  rw [polarGauge_eq_supportFn hg.nonneg hg.posHomogeneous hg.map_zero,
    ← polarSet_setOf_gaugeFn_le_one (B := B) C,
    gaugeFn_polarSet (B := B) (C := {x : E | gaugeFn C x ≤ 1}) hg.zero_mem_level_one]

/-- Let $C$ be convex with $0 \in C$. Then the polar of the gauge of $C$ is the support function of
$C$:
$$\gamma(\cdot \mid C)^\circ = \delta^*(\cdot \mid C).$$
This is Corollary 15.1.2 of [rockafellar1970convex], without the closedness of $C$ that the
source assumes. -/
theorem polarGauge_gaugeFn_eq_supportFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    polarGauge B (gaugeFn C) = supportFn B C := by
  rw [polarGauge_gaugeFn hC ⟨0, h0⟩, gaugeFn_polarSet h0]

end PolarGauge

/-!
### The pairing of $E \times \mathbb{R}$ with $F \times \mathbb{R}$

The polar of a function is described by the polar of its epigraph, one dimension higher. This needs
a pairing of $E \times \mathbb{R}$ with $F \times \mathbb{R}$. `ConvexAnalysis.prodPairing` in
`Numlib.Analysis.Convex.Duality.Pairing` gives it from a pairing of $\mathbb{R}$ with itself, and
`ConvexAnalysis.mulPairing` is that pairing.
-/

section EpiPairing

/-- The pairing of $\mathbb{R}$ with itself by multiplication, $\langle a, b \rangle = ab$. -/
def mulPairing : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := LinearMap.mul ℝ ℝ

/-- The pairing `ConvexAnalysis.mulPairing` maps $(a, b)$ to $ab$. -/
@[simp] theorem mulPairing_apply (a b : ℝ) : mulPairing a b = a * b := rfl

/-- The pairing `ConvexAnalysis.mulPairing` is its own flip. -/
@[simp] theorem mulPairing_flip : mulPairing.flip = mulPairing :=
  LinearMap.ext fun a => LinearMap.ext fun b => mul_comm b a

instance : IsContinuousPairing mulPairing where
  continuous_left b := by simpa using continuous_mul_const b

instance : IsCompatiblePairing mulPairing where
  toIsContinuousPairing := inferInstance
  surjective_eval g := ⟨g 1, ContinuousLinearMap.ext fun a => by
    rw [evalCLM_apply, mulPairing_apply]
    have h : g (a • (1 : ℝ)) = a • g 1 := map_smul g a 1
    rw [smul_eq_mul, mul_one] at h
    rw [h, smul_eq_mul]⟩

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The pairing of $E \times \mathbb{R}$ with $F \times \mathbb{R}$ under which epigraphs are
polarized:
$$\langle (x, \nu), (y, \mu) \rangle = \langle x, y \rangle + \nu \mu.$$

It is an `abbrev` for `ConvexAnalysis.prodPairing B ConvexAnalysis.mulPairing`, so that instance
search sees the instances for `ConvexAnalysis.prodPairing`; a `def` would hide them. -/
abbrev epiPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (E × ℝ) →ₗ[ℝ] (F × ℝ) →ₗ[ℝ] ℝ :=
  prodPairing B mulPairing

/-- The pairing `ConvexAnalysis.epiPairing B` maps $((x, \nu), (y, \mu))$ to
$\langle x, y \rangle + \nu \mu$. -/
@[simp] theorem epiPairing_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (p : E × ℝ) (q : F × ℝ) :
    epiPairing B p q = B p.1 q.1 + p.2 * q.2 := rfl

/-- The flip of `ConvexAnalysis.epiPairing B` is `ConvexAnalysis.epiPairing` of the flip of $B$. -/
theorem epiPairing_flip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (epiPairing B).flip = epiPairing B.flip := by
  rw [epiPairing, prodPairing_flip, mulPairing_flip]

/-- The **vertical reflection** of $X \times \mathbb{R}$, the linear map
$(x, \mu) \mapsto (x, -\mu)$. -/
def vNeg (X : Type*) [AddCommGroup X] [Module ℝ X] : (X × ℝ) →ₗ[ℝ] X × ℝ :=
  LinearMap.prodMap LinearMap.id (-LinearMap.id)

/-- The vertical reflection maps $(x, \mu)$ to $(x, -\mu)$. -/
@[simp] theorem vNeg_apply (X : Type*) [AddCommGroup X] [Module ℝ X] (p : X × ℝ) :
    vNeg X p = (p.1, -p.2) := rfl

/-- The vertical reflection is an involution. -/
@[simp] theorem vNeg_vNeg (X : Type*) [AddCommGroup X] [Module ℝ X] (p : X × ℝ) :
    vNeg X (vNeg X p) = p := by
  simp

/-- The image of a set under the vertical reflection equals its preimage. -/
theorem image_vNeg_eq_preimage (X : Type*) [AddCommGroup X] [Module ℝ X] (S : Set (X × ℝ)) :
    vNeg X '' S = vNeg X ⁻¹' S := by
  ext p
  refine ⟨?_, fun hp => ⟨vNeg X p, hp, vNeg_vNeg X p⟩⟩
  rintro ⟨q, hq, rfl⟩
  simpa using hq

/-- Reflecting a set twice gives the set back. -/
@[simp] theorem image_vNeg_image_vNeg (X : Type*) [AddCommGroup X] [Module ℝ X]
    (S : Set (X × ℝ)) : vNeg X '' (vNeg X '' S) = S := by
  rw [image_vNeg_eq_preimage, image_vNeg_eq_preimage]
  ext p
  simp

/-- Polarity commutes with the vertical reflection $A$: for $S \subseteq E \times \mathbb{R}$, the
polar of $AS$ with respect to `ConvexAnalysis.epiPairing` is $A(S^\circ)$. The reason is that
$A$ is self-adjoint for this pairing. -/
theorem polarSet_image_vNeg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : Set (E × ℝ)) :
    polarSet (epiPairing B) (vNeg E '' S) = vNeg F '' polarSet (epiPairing B) S := by
  rw [image_vNeg_eq_preimage F (polarSet (epiPairing B) S)]
  ext q
  simp only [Set.mem_preimage, mem_polarSet, Set.forall_mem_image, epiPairing_apply, vNeg_apply]
  exact forall₂_congr fun z _ => ⟨fun h => by linarith, fun h => by linarith⟩

end EpiPairing

/-!
### The polar of a nonnegative convex function

The source defines $f^\circ(y) = \inf \{\mu \ge 0 : \langle x, y \rangle \le 1 + \mu f(x) \ \forall
x\}$. The definition below avoids the value $+\infty$: it quantifies over the epigraph of $f$, and
$\mu$ is admissible when $\langle x, y \rangle - \nu \mu \le 1$ for every
$(x, \nu) \in \operatorname{epi} f$. This condition says that $(y, -\mu)$ lies in the polar of
$\operatorname{epi} f$, which is what the classical proof uses. `ConvexAnalysis.polarFn_apply_eq`
shows that the two formulas agree.
-/

section PolarFn

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {y : F} {μ : ℝ}

/-- The **polar** of a function $f : E \to [-\infty, +\infty]$ is the function on $F$
$$f^\circ(y) = \inf \{\mu \in \mathbb{R} : \langle x, y \rangle - \nu \mu \le 1 \text{ for all }
  (x, \nu) \in \operatorname{epi} f\}.$$
It is intended for nonnegative convex functions with $f(0) = 0$.

The infimum is over all real $\mu$. If $f(0) \le 0$, every admissible $\mu$ is nonnegative
(`ConvexAnalysis.polarFn_nonneg`). If $f$ is the constant $+\infty$, every $\mu$ is admissible
and $f^\circ$ is the constant $-\infty$. For nonnegative $f$ with $f(0) \le 0$,
`ConvexAnalysis.polarFn_apply_eq` gives the source formula $f^\circ(y) = \inf \{\mu \ge 0 :
\langle x, y \rangle \le 1 + \mu f(x) \ \forall x\}$. -/
noncomputable def polarFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨅ μ ∈ {μ : ℝ | ∀ (x : E) (ν : ℝ), f x ≤ (ν : EReal) → B x y - ν * μ ≤ 1}, (μ : EReal)

/-- The set of admissible multipliers of `ConvexAnalysis.polarFn` at $y$: the $\mu \in \mathbb{R}$
with $\langle x, y \rangle - \nu \mu \le 1$ for every $(x, \nu) \in \operatorname{epi} f$. -/
def polarFnSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) : Set ℝ :=
  {μ : ℝ | ∀ (x : E) (ν : ℝ), f x ≤ (ν : EReal) → B x y - ν * μ ≤ 1}

/-- The polar $f^\circ(y)$ is the infimum of `ConvexAnalysis.polarFnSet B f y`. -/
theorem polarFn_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    polarFn B f y = ⨅ μ ∈ polarFnSet B f y, (μ : EReal) := rfl

/-- If $f$ is nonnegative, the set of admissible multipliers is upward closed, because the second
coordinates of points of $\operatorname{epi} f$ are nonnegative. -/
theorem upClosed_polarFnSet (hnn : ∀ x, 0 ≤ f x) (y : F) : UpClosed (polarFnSet B f y) := by
  intro a ha b hab x ν hν
  have hν0 : (0 : ℝ) ≤ ν := by
    have := le_trans (hnn x) hν
    exact EReal.coe_nonneg.1 this
  have h := ha x ν hν
  nlinarith

/-- The set of admissible multipliers is closed, because it is an intersection of closed half-lines.
-/
theorem isClosed_polarFnSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    IsClosed (polarFnSet B f y) := by
  have hrw : polarFnSet B f y =
      ⋂ x : E, ⋂ ν : ℝ, ⋂ _ : f x ≤ (ν : EReal), {μ : ℝ | B x y - ν * μ ≤ 1} := by
    ext μ
    simp [polarFnSet]
  rw [hrw]
  exact isClosed_iInter fun x => isClosed_iInter fun ν => isClosed_iInter fun _ =>
    isClosed_le (continuous_const.sub (continuous_const.mul continuous_id)) continuous_const

/-- Let $f$ be nonnegative and $\mu \in \mathbb{R}$. Then $f^\circ(y) \le \mu$ if and only if
$\langle x, y \rangle - \nu \mu \le 1$ for every $(x, \nu) \in \operatorname{epi} f$. -/
theorem polarFn_le_coe_iff (hnn : ∀ x, 0 ≤ f x) :
    polarFn B f y ≤ (μ : EReal) ↔ ∀ (x : E) (ν : ℝ), f x ≤ (ν : EReal) → B x y - ν * μ ≤ 1 :=
  biInf_coe_le_coe_iff (upClosed_polarFnSet hnn y) (isClosed_polarFnSet B f y) μ

/-- If $f(0) \le 0$, then $f^\circ$ is nonnegative. -/
theorem polarFn_nonneg (h0 : f 0 ≤ 0) (y : F) : 0 ≤ polarFn B f y := by
  refine zero_le_biInf_coe fun a ha => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hna : (0 : ℝ) < -a := by linarith
  have hb : ∀ ν : ℝ, 0 ≤ ν → ν * -a ≤ 1 := by
    intro ν hν
    have h0' : f 0 ≤ ((ν : ℝ) : EReal) := by
      refine le_trans h0 ?_
      rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
      exact hν
    have h := ha 0 ν h0'
    rw [map_zero, LinearMap.zero_apply] at h
    rw [mul_neg]
    linarith
  have hkey := hb (2 / -a) (div_nonneg (by norm_num) hna.le)
  rw [div_mul_cancel₀ (2 : ℝ) hna.ne'] at hkey
  linarith

/-- If $f(0) \le 0$, then $f^\circ(0) = 0$. -/
@[simp] theorem polarFn_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (h0 : f 0 ≤ 0) :
    polarFn B f 0 = 0 := by
  refine le_antisymm ?_ (polarFn_nonneg h0 0)
  have h : (0 : ℝ) ∈ polarFnSet B f 0 := by
    intro x ν _
    simp
  have h2 := iInf₂_le (f := fun (μ : ℝ) (_ : μ ∈ polarFnSet B f 0) => (μ : EReal)) (0 : ℝ) h
  rw [polarFn_apply, ← EReal.coe_zero]
  exact h2

/-- Let $f$ be nonnegative with $f(0) \le 0$. Then $f^\circ$ is given by the formula of the source:
$$f^\circ(y) = \inf \{\mu \in \mathbb{R} : \mu \ge 0,\ \langle x, y \rangle \le 1 + \mu f(x) \
  \forall x \in E\}.$$

The two admissible sets differ only at $\mu = 0$. There the convention $0 \cdot (+\infty) = 0$
imposes $\langle x, y \rangle \le 1$ outside the effective domain of $f$, which the epigraph
form does not. Both sets are upward closed in $[0, \infty)$, so the infima agree. -/
theorem polarFn_apply_eq (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0) (y : F) :
    polarFn B f y =
      ⨅ μ ∈ {μ : ℝ | 0 ≤ μ ∧ ∀ x : E, ((B x y : ℝ) : EReal) ≤ 1 + (μ : EReal) * f x},
        (μ : EReal) := by
  set T : Set ℝ := {μ : ℝ | 0 ≤ μ ∧ ∀ x : E, ((B x y : ℝ) : EReal) ≤ 1 + (μ : EReal) * f x}
    with hT
  have hTS : T ⊆ polarFnSet B f y := by
    intro μ hμ x ν hν
    have hle : (μ : EReal) * f x ≤ (μ : EReal) * (ν : EReal) :=
      mul_le_mul_of_nonneg_left hν (EReal.coe_nonneg.2 hμ.1)
    have := le_trans (hμ.2 x) (add_le_add (le_refl (1 : EReal)) hle)
    rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) by rw [EReal.coe_one],
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    nlinarith
  have hpos : ∀ μ : ℝ, 0 < μ → μ ∈ polarFnSet B f y → μ ∈ T := by
    intro μ hμ0 hμ
    refine ⟨hμ0.le, fun x => ?_⟩
    rcases eq_or_lt_of_le (le_top (a := f x)) with htop | hlt
    · rw [htop, EReal.coe_mul_top_of_pos hμ0,
        show ((1 : EReal)) = ((1 : ℝ) : EReal) by rw [EReal.coe_one],
        EReal.coe_add_top]
      exact le_top
    obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hlt
    have := hμ x s (le_of_eq hs)
    rw [hs, ← EReal.coe_mul, show ((1 : EReal)) = ((1 : ℝ) : EReal) by
      rw [EReal.coe_one], ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith
  refine le_antisymm (le_iInf₂ fun μ hμ => iInf₂_le μ (hTS hμ)) ?_
  refine le_iInf₂ fun μ hμ => ?_
  have hμ0 : 0 ≤ μ := by
    have := polarFn_nonneg (B := B) h0 y
    exact EReal.coe_nonneg.1 (le_trans this (iInf₂_le μ hμ))
  rcases eq_or_lt_of_le hμ0 with hzero | hlt
  · rw [← hzero]
    refine le_coe_of_forall_gt_le fun d hd => ?_
    exact iInf₂_le d (hpos d hd (upClosed_polarFnSet hnn y hμ (by linarith)))
  · exact iInf₂_le μ (hpos μ hlt hμ)

end PolarFn

/-!
### Closures of nonnegative functions

A nonnegative function has a nonnegative lower semicontinuous hull. Hence the exceptional branch of
`ConvexAnalysis.convexCl`, where the hull takes the value $-\infty$, does not occur, and
$\operatorname{cl} f$ is the function whose epigraph is the closure of $\operatorname{epi} f$.
-/

section NonnegClosure

variable {E : Type*} [TopologicalSpace E] {f : E → EReal}

/-- If $f$ is nonnegative, every point $(x, \nu)$ of the closure of $\operatorname{epi} f$ has
$\nu \ge 0$. -/
theorem nonneg_of_mem_closure_epi (hnn : ∀ x, 0 ≤ f x) {p : E × ℝ} (hp : p ∈ closure (epi f)) :
    0 ≤ p.2 := by
  refine closure_minimal (fun q hq => ?_) (isClosed_le continuous_const continuous_snd) hp
  have h : (0 : EReal) ≤ (q.2 : EReal) := le_trans (hnn q.1) hq
  exact_mod_cast h

/-- The lower semicontinuous hull of a nonnegative function is nonnegative. -/
theorem lscHull_nonneg (hnn : ∀ x, 0 ≤ f x) (x : E) : 0 ≤ lscHull f x := by
  refine le_ofEpi fun μ hμ => ?_
  have h := nonneg_of_mem_closure_epi hnn hμ
  exact_mod_cast h

/-- For a nonnegative function $f$, the closure $\operatorname{cl} f$ is the lower semicontinuous
hull of $f$. -/
theorem convexCl_eq_lscHull_of_nonneg (hnn : ∀ x, 0 ≤ f x) : convexCl f = lscHull f :=
  convexCl_of_forall_ne_bot fun x h => by
    have h0 := lscHull_nonneg hnn x
    rw [h, le_bot_iff] at h0
    exact absurd h0 (by simp)

/-- The closure of a nonnegative function is nonnegative. -/
theorem convexCl_nonneg (hnn : ∀ x, 0 ≤ f x) (x : E) : 0 ≤ convexCl f x := by
  rw [convexCl_eq_lscHull_of_nonneg hnn]
  exact lscHull_nonneg hnn x

/-- A nonnegative function with a closed epigraph is closed in the sense of
`ConvexAnalysis.ClosedConvex`. -/
theorem closedConvex_of_isClosed_epi (hnn : ∀ x, 0 ≤ f x)
    (hcl : IsClosed (epi f)) : ClosedConvex f := by
  rw [ClosedConvex, convexCl_eq_lscHull_of_nonneg hnn]
  exact le_antisymm (lscHull_le f)
    (le_lscHull_of_le (lowerSemicontinuous_iff_isClosed_epi.2 hcl) le_rfl)

end NonnegClosure

section NonnegClosureGroup

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {f : E → EReal}

/-- For a nonnegative function $f$ on a topological group, $\operatorname{epi}(\operatorname{cl} f)$
is the closure of $\operatorname{epi} f$. -/
theorem epi_convexCl_of_nonneg (hnn : ∀ x, 0 ≤ f x) : epi (convexCl f) = closure (epi f) := by
  rw [convexCl_eq_lscHull_of_nonneg hnn, epi_lscHull]

/-- A nonnegative function that is closed in the sense of `ConvexAnalysis.ClosedConvex` has a closed
epigraph. -/
theorem isClosed_epi_of_closedConvex (hnn : ∀ x, 0 ≤ f x)
    (hcl : ClosedConvex f) : IsClosed (epi f) := by
  have h : epi f = closure (epi f) := by rw [← epi_convexCl_of_nonneg hnn, hcl]
  rw [h]
  exact isClosed_closure

/-- A nonnegative function is closed in the sense of `ConvexAnalysis.ClosedConvex` if and only if
its epigraph is closed. -/
theorem closedConvex_iff_isClosed_epi (hnn : ∀ x, 0 ≤ f x) : ClosedConvex f ↔ IsClosed (epi f) :=
  ⟨isClosed_epi_of_closedConvex hnn, closedConvex_of_isClosed_epi hnn⟩

end NonnegClosureGroup

/-!
### The bipolar of a function

The epigraph of $f^\circ$ is the vertical reflection of the polar of $\operatorname{epi} f$. The
bipolar theorem for sets in `Numlib.Analysis.Convex.Duality.Polar`, applied in
$E \times \mathbb{R}$, then gives $f^{\circ\circ} = \operatorname{cl} f$.
-/

section PolarEpi

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- Let $f$ be nonnegative, and let $A$ be the vertical reflection `ConvexAnalysis.vNeg`. Then
$$\operatorname{epi} f^\circ = A\big((\operatorname{epi} f)^\circ\big),$$
where the polar is taken with respect to `ConvexAnalysis.epiPairing B`. -/
theorem epi_polarFn (hnn : ∀ x, 0 ≤ f x) :
    epi (polarFn B f) = vNeg F '' polarSet (epiPairing B) (epi f) := by
  rw [image_vNeg_eq_preimage]
  ext q
  simp only [Set.mem_preimage, mem_epi, mem_polarSet, vNeg_apply, epiPairing_apply,
    polarFn_le_coe_iff hnn]
  constructor
  · rintro h ⟨x, ν⟩ hp
    have h2 := h x ν hp
    simp only
    linarith
  · intro h x ν hν
    have h2 := h (x, ν) hν
    simp only at h2
    linarith

/-- The polar of a nonnegative function is convex, because its epigraph is the reflection of a polar
set. -/
theorem convexFn_polarFn (hnn : ∀ x, 0 ≤ f x) : ConvexFn (polarFn B f) := by
  rw [convexFn_iff_convex_epi, epi_polarFn hnn, image_vNeg_eq_preimage]
  exact (convex_polarSet _ _).linear_preimage (vNeg F)

end PolarEpi

section PolarClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {f : E → EReal}

/-- Let $F$ carry a topology in which every $\langle x, \cdot \rangle$ is continuous. If $f$ is
nonnegative and $f(0) \le 0$, then $f^\circ$ is closed in the sense of
`ConvexAnalysis.ClosedConvex`, because polar sets are closed. This is part of Theorem 15.4 of
[rockafellar1970convex]. -/
theorem closedConvex_polarFn (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0) : ClosedConvex (polarFn B f) := by
  have : IsContinuousPairing (epiPairing B).flip := by
    rw [epiPairing_flip]
    infer_instance
  refine closedConvex_of_isClosed_epi (fun y => polarFn_nonneg h0 y) ?_
  rw [epi_polarFn hnn, image_vNeg_eq_preimage]
  have hc : Continuous fun p : F × ℝ => ((p.1, -p.2) : F × ℝ) :=
    continuous_fst.prodMk continuous_snd.neg
  exact isClosed_polarSet.preimage hc

end PolarClosed

section BipolarFn

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- Let $E$ be a locally convex space, let the pairing $B$ be compatible with the topology of $E$,
and let $f : E \to [-\infty, +\infty]$ be convex and nonnegative with $f(0) \le 0$. Then the
bipolar of $f$ is its closure:
$$f^{\circ\circ} = \operatorname{cl} f.$$
This is part of Theorem 15.4 of [rockafellar1970convex].

The outer polar is taken with respect to the flipped pairing, because $f^\circ$ is a function on
$F$. -/
theorem polarFn_polarFn (hconv : ConvexFn f) (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0) :
    polarFn B.flip (polarFn B f) = convexCl f := by
  have hnn' : ∀ y, 0 ≤ polarFn B f y := fun y => polarFn_nonneg h0 y
  have hmem : (0 : E × ℝ) ∈ closure (epi f) := by
    refine subset_closure ?_
    rw [mem_epi]
    simpa using h0
  have hepi : epi (polarFn B.flip (polarFn B f)) = closure (epi f) := by
    rw [epi_polarFn hnn', epi_polarFn hnn, polarSet_image_vNeg B.flip, image_vNeg_image_vNeg,
      ← epiPairing_flip B, ← polarSet_closure (B := epiPairing B) (epi f)]
    exact polarSet_polarSet hconv.convex_epi.closure isClosed_closure hmem
  have hof := congrArg ofEpi hepi
  rwa [ofEpi_epi, ← epi_convexCl_of_nonneg hnn, ofEpi_epi] at hof

end BipolarFn

/-!
### The class on which the polar is an involution

The nonnegative closed convex functions that vanish at the origin.
-/

section PolarClass

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {f : E → EReal}

/-- A function $f : E \to [-\infty, +\infty]$ is in the **polar class** if it is nonnegative, closed
and convex, and $f(0) = 0$.

These are the functions that arise as polars (`ConvexAnalysis.isPolarFn_polarFn` and
`ConvexAnalysis.polarFn_polarFn`), and $f \mapsto f^\circ$ is an involution on them. -/
structure IsPolarFn (f : E → EReal) : Prop where
  /-- The function is nonnegative. -/
  nonneg : ∀ x, 0 ≤ f x
  /-- The function vanishes at the origin. -/
  map_zero : f 0 = 0
  /-- The function is convex. -/
  convexFn : ConvexFn f
  /-- The function is closed in the sense of `ConvexAnalysis.ClosedConvex`. -/
  closedConvex : ClosedConvex f

/-- A function in the polar class satisfies $f(0) \le 0$. -/
theorem IsPolarFn.map_zero_le (h : IsPolarFn f) : f 0 ≤ 0 := le_of_eq h.map_zero

/-- A closed gauge is in the polar class `ConvexAnalysis.IsPolarFn`. -/
theorem IsGauge.isPolarFn (h : IsGauge f) (hcl : ClosedConvex f) : IsPolarFn f :=
  ⟨h.nonneg, h.map_zero, h.convexFn, hcl⟩

end PolarClass

section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip]
  {f : E → EReal}

/-- Let $E$ and $F$ carry topologies, with every $\langle x, \cdot \rangle$ continuous on $F$. If
$f$ is in the polar class `ConvexAnalysis.IsPolarFn`, then so is $f^\circ$. This is part of
Theorem 15.4 of [rockafellar1970convex]. -/
theorem isPolarFn_polarFn (h : IsPolarFn f) : IsPolarFn (polarFn B f) where
  nonneg y := polarFn_nonneg h.map_zero_le y
  map_zero := polarFn_zero B f h.map_zero_le
  convexFn := convexFn_polarFn h.nonneg
  closedConvex := closedConvex_polarFn h.nonneg h.map_zero_le

end

section PolarInvolution

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

/-- Let $E$ and $F$ be locally convex spaces, and let $B$ and its flip be compatible pairings. The
map $f \mapsto f^\circ$ is a bijection from the nonnegative closed convex functions on $E$ that
vanish at $0$ to those on $F$, and its inverse is the polar with respect to the flipped pairing.
This is Corollary 15.4.1 of [rockafellar1970convex]. -/
noncomputable def polarFnEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] :
    {f : E → EReal // IsPolarFn f} ≃ {g : F → EReal // IsPolarFn g} where
  toFun f := ⟨polarFn B f.1, isPolarFn_polarFn f.2⟩
  invFun g := ⟨polarFn B.flip g.1, isPolarFn_polarFn g.2⟩
  left_inv f := Subtype.ext <| by
    change polarFn B.flip (polarFn B f.1) = f.1
    rw [polarFn_polarFn f.2.convexFn f.2.nonneg f.2.map_zero_le]
    exact f.2.closedConvex
  right_inv g := Subtype.ext <| by
    change polarFn B (polarFn B.flip g.1) = g.1
    have h := polarFn_polarFn (B := B.flip) g.2.convexFn g.2.nonneg g.2.map_zero_le
    rw [LinearMap.flip_flip] at h
    rw [h]
    exact g.2.closedConvex

end PolarInvolution

/-!
### The involution $k^{\circ\circ} = \operatorname{cl} k$

[rockafellar1970convex] derives this from the polarity of the unit sublevel set. Here it is a
special case of `ConvexAnalysis.polarFn_polarFn`, because the two polar operations agree on a gauge
(`ConvexAnalysis.polarFn_eq_polarGauge`): the term $1 +$ in the definition of $f^\circ$ has no
effect on a positively homogeneous function.
-/

section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {k : E → EReal}

/-- Let $k$ be nonnegative and positively homogeneous with $k(0) = 0$. Then the polar of $k$ as a
function equals its polar as a gauge: `ConvexAnalysis.polarFn B k = ConvexAnalysis.polarGauge B
k`.

The admissible set of `ConvexAnalysis.polarGauge` is contained in that of
`ConvexAnalysis.polarFn`, and the two differ at most at $0$. Both are upward closed in
$[0, \infty)$, so the infima agree. -/
theorem polarFn_eq_polarGauge (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    polarFn B k = polarGauge B k := by
  funext y
  refine le_antisymm ?_ ?_
  · rw [polarGauge_apply]
    refine le_iInf₂ fun μ hμ => ?_
    refine (polarFn_le_coe_iff hnn).2 fun x ν hν => ?_
    have h1 : ((B x y : ℝ) : EReal) ≤ ((μ * ν : ℝ) : EReal) := by
      refine le_trans (hμ.2 x) ?_
      rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left hν (EReal.coe_nonneg.2 hμ.1)
    rw [EReal.coe_le_coe_iff] at h1
    linarith [mul_comm μ ν]
  · rw [polarFn_apply]
    refine le_iInf₂ fun μ hμ => ?_
    have hμ0 : (0 : ℝ) ≤ μ := by
      have hle : polarFn B k y ≤ (μ : EReal) :=
        iInf₂_le (f := fun (μ : ℝ) (_ : μ ∈ polarFnSet B k y) => (μ : EReal)) μ hμ
      exact EReal.coe_nonneg.1 (le_trans (polarFn_nonneg (le_of_eq h0) y) hle)
    refine le_coe_of_forall_gt_le fun d hd => ?_
    have hd0 : (0 : ℝ) < d := lt_of_le_of_lt hμ0 hd
    have hdmem : d ∈ polarFnSet B k y := upClosed_polarFnSet hnn y hμ hd.le
    refine polarGauge_le_of_forall hd0.le fun x => ?_
    rcases eq_or_lt_of_le (le_top (a := k x)) with htopx | hltx
    · rw [htopx, EReal.coe_mul_top_of_pos hd0]
      exact le_top
    obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hltx
    rw [hc, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    by_contra hcon
    rw [not_le] at hcon
    have ha0 : (0 : ℝ) < B x y - d * c := by linarith
    have ht : (0 : ℝ) < 2 / (B x y - d * c) := by positivity
    have hkt : k ((2 / (B x y - d * c)) • x) ≤ (((2 / (B x y - d * c)) * c : ℝ) : EReal) :=
      le_of_eq (by rw [hph _ ht x, hc, ← EReal.coe_mul])
    have hb := hdmem _ _ hkt
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hb
    have hexp : 2 / (B x y - d * c) * B x y - 2 / (B x y - d * c) * c * d
        = 2 / (B x y - d * c) * (B x y - d * c) := by ring
    rw [hexp, div_mul_cancel₀ (2 : ℝ) ha0.ne'] at hb
    linarith

end

section GaugeInvolution

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {k : E → EReal}

/-- Let $E$ be a locally convex space, let the pairing $B$ be compatible with the topology of $E$,
and let $k$ be a gauge on $E$. Then
$$k^{\circ\circ} = \operatorname{cl} k,$$
where the outer polar is taken with respect to the flipped pairing. This is part of Theorem 15.1
of [rockafellar1970convex]. -/
theorem polarGauge_polarGauge (hk : IsGauge k) :
    polarGauge B.flip (polarGauge B k) = convexCl k := by
  have hpk : IsGauge (polarGauge B k) := isGauge_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero
  rw [← polarFn_eq_polarGauge hpk.nonneg hpk.posHomogeneous hpk.map_zero,
    ← polarFn_eq_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero]
  exact polarFn_polarFn hk.convexFn hk.nonneg (le_of_eq hk.map_zero)

end GaugeInvolution

/-! ### Polarity as a bijection, for gauges and for sets -/

section GaugeCorrespondence

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

/-- Let $E$ and $F$ be locally convex spaces, and let $B$ and its flip be compatible pairings. The
map $k \mapsto k^\circ$ is a bijection from the closed gauges on $E$ to the closed gauges on
$F$, and its inverse is the polar with respect to the flipped pairing. This is the first
assertion of Corollary 15.1.1 of [rockafellar1970convex]. -/
noncomputable def polarGaugeEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] :
    {k : E → EReal // IsGauge k ∧ ClosedConvex k} ≃
        {j : F → EReal // IsGauge j ∧ ClosedConvex j} where
  toFun k := ⟨polarGauge B k.1,
    isGauge_polarGauge k.2.1.nonneg k.2.1.posHomogeneous k.2.1.map_zero,
    closedConvex_polarGauge k.2.1.nonneg k.2.1.posHomogeneous k.2.1.map_zero⟩
  invFun j := ⟨polarGauge B.flip j.1,
    isGauge_polarGauge j.2.1.nonneg j.2.1.posHomogeneous j.2.1.map_zero,
    closedConvex_polarGauge j.2.1.nonneg j.2.1.posHomogeneous j.2.1.map_zero⟩
  left_inv k := Subtype.ext <| by
    change polarGauge B.flip (polarGauge B k.1) = k.1
    rw [polarGauge_polarGauge k.2.1]
    exact k.2.2
  right_inv j := Subtype.ext <| by
    change polarGauge B (polarGauge B.flip j.1) = j.1
    have h := polarGauge_polarGauge (B := B.flip) j.2.1
    rw [LinearMap.flip_flip] at h
    rw [h]
    exact j.2.2

end GaugeCorrespondence

section SetCorrespondence

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [ContinuousSMul ℝ F]

/-- Let $F$ carry a topology in which scalar multiplication and every $\langle x, \cdot \rangle$ are
continuous. Let $C \subseteq E$ be convex with $0 \in C$, and let $D \subseteq F$ be closed and
convex with $0 \in D$. Then $C^\circ = D$ if and only if $\gamma(\cdot \mid C)^\circ =
\gamma(\cdot \mid D)$. This is the second assertion of Corollary 15.1.1 of
[rockafellar1970convex].

The source assumes that both sets are closed; $C$ need not be. -/
theorem polarSet_eq_iff_polarGauge_gaugeFn_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsContinuousPairing B.flip] {C : Set E} {D : Set F}
    (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hD : Convex ℝ D) (hDcl : IsClosed D)
    (hD0 : (0 : F) ∈ D) :
    polarSet B C = D ↔ polarGauge B (gaugeFn C) = gaugeFn D := by
  rw [polarGauge_gaugeFn hC ⟨0, h0⟩]
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have hpc : {y : F | gaugeFn (polarSet B C) y ≤ 1} = {y : F | gaugeFn D y ≤ 1} := by rw [h]
  rwa [setOf_gaugeFn_le_one (convex_polarSet B C) (fun x _ => by simp) isClosed_polarSet,
    setOf_gaugeFn_le_one hD hD0 hDcl] at hpc

end SetCorrespondence

/-!
### The obverse

The obverse is $\operatorname{ob}(f)(x) = \inf \{\lambda > 0 : (f\lambda)(x) \le 1\}$. In place of
the geometric argument of [rockafellar1970convex], this section observes that it is a gauge value
one dimension higher: $\operatorname{ob}(f)(x) = \gamma((x, 1) \mid \operatorname{epi} f)$. The
properties of the obverse then follow from those of the gauge.
-/

section Obverse

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {a : ℝ}

/-- Let $a > 0$. Then $(x, r) \in a \operatorname{epi} f$ if and only if $f(a^{-1} x) \le a^{-1} r$.
-/
theorem mk_mem_smul_epi_iff (ha : 0 < a) (f : E → EReal) (x : E) (r : ℝ) :
    (x, r) ∈ a • epi f ↔ f (a⁻¹ • x) ≤ ((a⁻¹ * r : ℝ) : EReal) := by
  rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne']
  exact Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
/-- The point $(x, 1)$ lies in $\operatorname{epi} f$ if and only if $f(x) \le 1$. -/
theorem mk_one_mem_epi_iff (f : E → EReal) (x : E) : (x, (1 : ℝ)) ∈ epi f ↔ f x ≤ 1 := by
  rw [mem_epi]
  exact_mod_cast Iff.rfl

/-- The **obverse** of a function $f : E \to [-\infty, +\infty]$ is the function
$$\operatorname{ob}(f)(x) = \inf \{\lambda \in \mathbb{R} : \lambda > 0,\ (f\lambda)(x) \le
  1\},$$
where $(f\lambda)(x) = \lambda f(\lambda^{-1} x)$ is right scalar multiplication. The term is
Rockafellar's. -/
noncomputable def obverse (f : E → EReal) : E → EReal :=
  fun x => ⨅ l ∈ {l : ℝ | 0 < l ∧ smulRight f l x ≤ 1}, (l : EReal)

/-- The defining formula $\operatorname{ob}(f)(x) = \inf \{\lambda > 0 : (f\lambda)(x) \le 1\}$. -/
theorem obverse_apply (f : E → EReal) (x : E) :
    obverse f x = ⨅ l ∈ {l : ℝ | 0 < l ∧ smulRight f l x ≤ 1}, (l : EReal) := rfl

/-- The admissible set of the obverse at $x$ is the admissible set of the gauge of
$\operatorname{epi} f$ at $(x, 1)$:
$$\{\lambda > 0 : (f\lambda)(x) \le 1\} = \{a \ge 0 : (x, 1) \in a \operatorname{epi} f\}.$$
The scalar $0$ is never admissible on the right, because
$(x, 1) \notin 0 \cdot \operatorname{epi} f$. -/
theorem obverseSet_eq (f : E → EReal) (x : E) :
    {l : ℝ | 0 < l ∧ smulRight f l x ≤ 1} = {a : ℝ | 0 ≤ a ∧ (x, (1 : ℝ)) ∈ a • epi f} := by
  ext l
  constructor
  · rintro ⟨hl, hle⟩
    exact ⟨hl.le, by rw [← epi_smulRight hl]; exact (mk_one_mem_epi_iff _ x).2 hle⟩
  · rintro ⟨hl0, hmem⟩
    rcases eq_or_lt_of_le hl0 with hzero | hl
    · exfalso
      obtain ⟨p, -, hp⟩ := hmem
      rw [← hzero] at hp
      simpa using congrArg Prod.snd hp
    · exact ⟨hl, (mk_one_mem_epi_iff _ x).1 (by rw [← epi_smulRight hl] at hmem; exact hmem)⟩

/-- The obverse is a gauge value one dimension higher: $\operatorname{ob}(f)(x) = \gamma((x, 1) \mid
\operatorname{epi} f)$. -/
theorem obverse_eq_gaugeFn (f : E → EReal) (x : E) :
    obverse f x = gaugeFn (epi f) (x, (1 : ℝ)) := by
  rw [obverse_apply, gaugeFn_apply, obverseSet_eq]

/-- The epigraph of the obverse is a slice of the epigraph of the gauge of $\operatorname{epi} f$:
$(x, \mu) \in \operatorname{epi} \operatorname{ob}(f)$ if and only if $((x, 1), \mu) \in
\operatorname{epi} \gamma(\cdot \mid \operatorname{epi} f)$. -/
theorem epi_obverse (f : E → EReal) :
    epi (obverse f) = (fun p : E × ℝ => ((p.1, (1 : ℝ)), p.2)) ⁻¹' epi (gaugeFn (epi f)) := by
  ext p
  simp only [Set.mem_preimage, mem_epi, obverse_eq_gaugeFn]

/-- The obverse is nonnegative. -/
theorem obverse_nonneg (f : E → EReal) (x : E) : 0 ≤ obverse f x := by
  rw [obverse_eq_gaugeFn]
  exact gaugeFn_nonneg _ _

/-- The obverse never takes the value $-\infty$. -/
theorem obverse_ne_bot (f : E → EReal) (x : E) : obverse f x ≠ ⊥ := by
  rw [obverse_eq_gaugeFn]
  exact gaugeFn_ne_bot _ _

end Obverse

/-! ### Two lemmas on extended reals for the obverse -/

section ErealAux

/-- If $z \in [-\infty, +\infty]$ and $z \ge 0$, then $\inf \{\nu \in \mathbb{R} : \nu > 0,\ z \le
\nu\} = z$. For $z = +\infty$ the set is empty and both sides are $+\infty$. -/
theorem biInf_coe_pos_ge_eq {z : EReal} (hz : 0 ≤ z) :
    (⨅ ν ∈ {ν : ℝ | 0 < ν ∧ z ≤ (ν : EReal)}, (ν : EReal)) = z := by
  refine le_antisymm ?_ (le_iInf₂ fun ν hν => hν.2)
  rcases eq_or_lt_of_le (le_top (a := z)) with htop | hlt
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (fun hb => by simp [hb] at hz) hlt
  have hr0 : (0 : ℝ) ≤ r := by rw [hr] at hz; exact EReal.coe_nonneg.1 hz
  refine le_of_le_of_eq (le_coe_of_forall_gt_le fun d hd => ?_) hr.symm
  refine iInf₂_le (f := fun (ν : ℝ) (_ : ν ∈ {ν : ℝ | 0 < ν ∧ z ≤ (ν : EReal)}) => (ν : EReal))
    d ⟨lt_of_le_of_lt hr0 hd, ?_⟩
  rw [hr]
  exact_mod_cast hd.le

/-- Let $A, B \in [-\infty, +\infty]$ be nonnegative. If $A \le \nu \iff B \le \nu$ for every real
$\nu > 0$, then $A = B$. -/
theorem eq_of_forall_pos_le_iff {A B : EReal} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ ν : ℝ, 0 < ν → (A ≤ (ν : EReal) ↔ B ≤ (ν : EReal))) : A = B := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    obtain ⟨ν, hBν, hνA⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    have hν0 : (0 : ℝ) < ν := by
      have hlt : (0 : EReal) < (ν : EReal) := lt_of_le_of_lt hB hBν
      rw [← EReal.coe_zero, EReal.coe_lt_coe_iff] at hlt
      exact hlt
    exact absurd ((h ν hν0).2 hBν.le) (not_le.2 hνA)
  · by_contra hcon
    obtain ⟨ν, hAν, hνB⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    have hν0 : (0 : ℝ) < ν := by
      have hlt : (0 : EReal) < (ν : EReal) := lt_of_le_of_lt hA hAν
      rw [← EReal.coe_zero, EReal.coe_lt_coe_iff] at hlt
      exact hlt
    exact absurd ((h ν hν0).1 hAν.le) (not_le.2 hνB)

end ErealAux

/-! ### The obverse of a nonnegative closed convex function -/

section ObverseClosed

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup E] {f : E → EReal} {ν : ℝ}

omit [ContinuousSMul ℝ E] in
/-- If $f$ is in the polar class `ConvexAnalysis.IsPolarFn`, then $\operatorname{epi} f$ is convex
and closed and contains the origin. These are the hypotheses of the theory of closed gauges. -/
theorem IsPolarFn.epi_closed_convex_zero (h : IsPolarFn f) :
    Convex ℝ (epi f) ∧ IsClosed (epi f) ∧ (0 : E × ℝ) ∈ epi f :=
  ⟨h.convexFn.convex_epi, isClosed_epi_of_closedConvex h.nonneg h.closedConvex, by
    rw [mem_epi]; simpa using h.map_zero.le⟩

/-- Let $f$ be in the polar class `ConvexAnalysis.IsPolarFn`, and let $\nu > 0$. Then
$\operatorname{ob}(f)(z) \le \nu$ if and only if $f(\nu^{-1} z) \le \nu^{-1}$, that is,
$(f\nu)(z) \le 1$. -/
theorem obverse_le_coe_iff (h : IsPolarFn f) (hν : 0 < ν) (z : E) :
    obverse f z ≤ (ν : EReal) ↔ f (ν⁻¹ • z) ≤ ((ν⁻¹ : ℝ) : EReal) := by
  obtain ⟨hC, hCcl, hC0⟩ := h.epi_closed_convex_zero
  rw [obverse_eq_gaugeFn, gaugeFn_le_coe_iff hC hC0 hCcl hν, mk_mem_smul_epi_iff hν, mul_one]

/-- If $f$ is in the polar class `ConvexAnalysis.IsPolarFn`, then $\operatorname{ob}(f)(0) = 0$. -/
@[simp] theorem obverse_zero (h : IsPolarFn f) : obverse f 0 = 0 := by
  refine le_antisymm (le_coe_of_forall_gt_le fun d hd => ?_) (obverse_nonneg f 0)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [obverse_le_coe_iff h hd0, smul_zero, h.map_zero]
  exact_mod_cast le_of_lt (inv_pos.2 hd0)

omit [ContinuousSMul ℝ E] [IsTopologicalAddGroup E] in
/-- If $f$ is in the polar class `ConvexAnalysis.IsPolarFn`, then $\operatorname{ob}(f)$ is convex.
-/
theorem convexFn_obverse (h : IsPolarFn f) : ConvexFn (obverse f) := by
  have hk : ConvexFn (gaugeFn (epi f)) := convexFn_gaugeFn h.convexFn.convex_epi
  refine convexFn_iff_convex_epi.2 fun p hp q hq s t hs ht hst => ?_
  rw [mem_epi, obverse_eq_gaugeFn] at hp hq ⊢
  have hcomb := hk.convex_epi (show ((p.1, (1 : ℝ)), p.2) ∈ epi (gaugeFn (epi f)) from hp)
    (show ((q.1, (1 : ℝ)), q.2) ∈ epi (gaugeFn (epi f)) from hq) hs ht hst
  have hkey : s • (((p.1, (1 : ℝ))), p.2) + t • (((q.1, (1 : ℝ))), q.2)
      = ((((s • p + t • q).1, (1 : ℝ))), (s • p + t • q).2) := by
    simp [hst]
  rw [hkey] at hcomb
  exact hcomb

/-- If $f$ is in the polar class `ConvexAnalysis.IsPolarFn`, then $\operatorname{ob}(f)$ is closed
in the sense of `ConvexAnalysis.ClosedConvex`. -/
theorem closedConvex_obverse (h : IsPolarFn f) : ClosedConvex (obverse f) := by
  obtain ⟨hC, hCcl, hC0⟩ := h.epi_closed_convex_zero
  refine closedConvex_of_isClosed_epi (obverse_nonneg f) ?_
  rw [epi_obverse]
  refine IsClosed.preimage ?_
    (isClosed_epi_of_closedConvex (gaugeFn_nonneg _) (closedConvex_gaugeFn hC hC0 hCcl))
  exact (continuous_fst.prodMk continuous_const).prodMk continuous_snd

/-- If $f$ is in the polar class `ConvexAnalysis.IsPolarFn`, then so is its obverse. This is part of
Theorem 15.5 of [rockafellar1970convex]. -/
theorem isPolarFn_obverse (h : IsPolarFn f) : IsPolarFn (obverse f) where
  nonneg := obverse_nonneg f
  map_zero := obverse_zero h
  convexFn := convexFn_obverse h
  closedConvex := closedConvex_obverse h

/-- Let $E$ be a topological vector space, and let $f$ be a nonnegative closed convex function on
$E$ with $f(0) = 0$. Then the obverse is an involution:
$$\operatorname{ob}(\operatorname{ob}(f)) = f.$$
This is part of Theorem 15.5 of [rockafellar1970convex]. -/
theorem obverse_obverse (h : IsPolarFn f) : obverse (obverse f) = f := by
  funext z
  rw [obverse_apply, obverseSet_eq]
  have hset : {a : ℝ | 0 ≤ a ∧ (z, (1 : ℝ)) ∈ a • epi (obverse f)}
      = {a : ℝ | 0 < a ∧ f z ≤ (a : EReal)} := by
    ext a
    constructor
    · rintro ⟨ha0, hmem⟩
      rcases eq_or_lt_of_le ha0 with hzero | ha
      · exfalso
        obtain ⟨p, -, hp⟩ := hmem
        rw [← hzero] at hp
        simpa using congrArg Prod.snd hp
      refine ⟨ha, ?_⟩
      rw [mk_mem_smul_epi_iff ha, mul_one, obverse_le_coe_iff h (inv_pos.2 ha), inv_inv,
        smul_inv_smul₀ ha.ne'] at hmem
      exact hmem
    · rintro ⟨ha, hle⟩
      refine ⟨ha.le, ?_⟩
      rw [mk_mem_smul_epi_iff ha, mul_one, obverse_le_coe_iff h (inv_pos.2 ha), inv_inv,
        smul_inv_smul₀ ha.ne']
      exact hle
  rw [hset]
  exact biInf_coe_pos_ge_eq (h.nonneg z)

end ObverseClosed

/-!
### The polar, the conjugate and the obverse

[rockafellar1970convex] obtains these identities from the symmetry of a closed convex cone in
$\mathbb{R}^{n+2}$ under the exchange of two coordinates. Here the identity
$f^* = \operatorname{ob}(f^\circ)$ (`ConvexAnalysis.convexConj_eq_obverse_polarFn`) does the work.
It is a comparison of sublevel sets, and the other identities follow from it with
`ConvexAnalysis.obverse_obverse` and `ConvexAnalysis.polarFn_polarFn`.
-/

section ConjEpi

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {y : F}

/-- Let $f$ be nonnegative and $\nu \in \mathbb{R}$. Then $f^*(y) \le \nu$ if and only if
$\langle x, y \rangle - \alpha \le \nu$ for every $(x, \alpha) \in \operatorname{epi} f$. Points
where $f = +\infty$ impose no condition. -/
theorem convexConj_le_coe_iff_epi (hnn : ∀ x, 0 ≤ f x) {ν : ℝ} :
    convexConj B f y ≤ (ν : EReal) ↔ ∀ (x : E) (α : ℝ), f x ≤ (α : EReal) → B x y - α ≤ ν := by
  rw [convexConj_apply, iSup_le_iff]
  constructor
  · intro h x α hα
    have h2 : ((B x y : ℝ) : EReal) - (α : EReal) ≤ ((B x y : ℝ) : EReal) - f x :=
      EReal.sub_le_sub le_rfl hα
    have h3 := le_trans h2 (h x)
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h3
    exact h3
  · intro h x
    rcases eq_or_lt_of_le (le_top (a := f x)) with htop | hlt
    · rw [htop, EReal.sub_top]
      exact bot_le
    obtain ⟨c, hc⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (fun hb => by simpa [hb] using hnn x) hlt
    rw [hc, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    exact h x c (le_of_eq hc)

end ConjEpi

section ConjPolarClass

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  [IsContinuousPairing B.flip] {f : E → EReal}

/-- Let $E$ carry a topology, let $F$ be a topological additive group, and let every
$\langle x, \cdot \rangle$ be continuous on $F$. If $f$ is in the polar class
`ConvexAnalysis.IsPolarFn`, then so is $f^*$. -/
theorem isPolarFn_convexConj (h : IsPolarFn f) : IsPolarFn (convexConj B f) where
  nonneg := zero_le_convexConj h.map_zero.le
  map_zero := convexConj_zero_eq_zero h.nonneg h.map_zero.le
  convexFn := convexFn_convexConj B f
  closedConvex := closedConvex_convexConj

end ConjPolarClass

section ObverseFormula

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F] [IsTopologicalAddGroup F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {f : E → EReal}

/-- Let $F$ be a topological vector space, let every $\langle x, \cdot \rangle$ be continuous on
$F$, and let $f$ be a nonnegative closed convex function on $E$ with $f(0) = 0$. Then the
conjugate is the obverse of the polar:
$$f^* = \operatorname{ob}(f^\circ).$$
This is part of Theorem 15.5 of [rockafellar1970convex].

Both sides are nonnegative, so it suffices to compare their sublevel sets at positive reals
$\nu$. There both conditions reduce to $\langle x, y \rangle - \alpha \le \nu$ for every
$(x, \alpha) \in \operatorname{epi} f$. -/
theorem convexConj_eq_obverse_polarFn
    (h : IsPolarFn f) : convexConj B f = obverse (polarFn B f) := by
  funext y
  refine eq_of_forall_pos_le_iff (zero_le_convexConj h.map_zero.le y) (obverse_nonneg _ y)
      fun ν hν => ?_
  rw [obverse_le_coe_iff (isPolarFn_polarFn h) hν, polarFn_le_coe_iff h.nonneg,
    convexConj_le_coe_iff_epi h.nonneg]
  refine forall_congr' fun x => forall_congr' fun α => imp_congr_right fun _ => ?_
  rw [map_smul, smul_eq_mul]
  have hrw : ν⁻¹ * B x y - α * ν⁻¹ = ν⁻¹ * (B x y - α) := by ring
  rw [hrw, inv_mul_le_iff₀ hν, mul_one]

/-- Let $F$ be a topological vector space, let every $\langle x, \cdot \rangle$ be continuous on
$F$, and let $f$ be a nonnegative closed convex function on $E$ with $f(0) = 0$. Then the polar
is the obverse of the conjugate:
$$f^\circ = \operatorname{ob}(f^*).$$
This is part of Theorem 15.5 of [rockafellar1970convex].

With `ConvexAnalysis.convexConj_eq_obverse_polarFn`, this shows that $f^\circ$ and $f^*$ are
obverses of each other. -/
theorem polarFn_eq_obverse_convexConj
    (h : IsPolarFn f) : polarFn B f = obverse (convexConj B f) := by
  rw [convexConj_eq_obverse_polarFn h, obverse_obverse (isPolarFn_polarFn h)]

end ObverseFormula

section PolarConjObverse

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : E → EReal}

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Let $E$ be a locally convex space, let $B$ and its flip be compatible pairings, and let $f$ be
in the polar class `ConvexAnalysis.IsPolarFn`. Then the obverse of $f$ is the polar of its
conjugate, $\operatorname{ob}(f) = f^{*\circ}$, where the polar is taken with respect to the
flipped pairing. This is part of Theorem 15.5 of [rockafellar1970convex], the expression from
which the source derives the formula $\operatorname{ob}(f)(x) = \inf \{\lambda > 0 :
(f\lambda)(x) \le 1\}$. -/
theorem obverse_eq_polarFn_convexConj (h : IsPolarFn f) :
    obverse f = polarFn B.flip (convexConj B f) := by
  rw [polarFn_eq_obverse_convexConj (B := B.flip) (isPolarFn_convexConj (B := B) h)]
  have h2 : convexConj B.flip (convexConj B f) = f := by
    change convexBiconj B f = f
    rw [convexBiconj_eq_convexCl h.convexFn]
    exact h.closedConvex
  rw [h2]

/-- Let $E$ and $F$ be locally convex spaces, let $B$ and its flip be compatible pairings, and let
$f$ be in the polar class `ConvexAnalysis.IsPolarFn`. Then $\operatorname{ob}(f)^\circ = f^*$.
This is part of Theorem 15.5 of [rockafellar1970convex]. -/
theorem polarFn_obverse (h : IsPolarFn f) : polarFn B (obverse f) = convexConj B f := by
  have hc : IsPolarFn (convexConj B f) := isPolarFn_convexConj (B := B) h
  rw [obverse_eq_polarFn_convexConj (B := B) h]
  have h3 := polarFn_polarFn (B := B.flip) hc.convexFn hc.nonneg hc.map_zero_le
  rw [LinearMap.flip_flip] at h3
  rw [h3]
  exact hc.closedConvex

/-- Let $E$ and $F$ be locally convex spaces, let $B$ and its flip be compatible pairings, and let
$f$ be in the polar class `ConvexAnalysis.IsPolarFn`. Then $\operatorname{ob}(f)^* = f^\circ$.
This is part of Theorem 15.5 of [rockafellar1970convex]. -/
theorem convexConj_obverse (h : IsPolarFn f) : convexConj B (obverse f) = polarFn B f := by
  rw [convexConj_eq_obverse_polarFn (isPolarFn_obverse h), polarFn_obverse (B := B) h,
    ← polarFn_eq_obverse_convexConj (B := B) h]

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Let $E$ be a locally convex space, let $B$ and its flip be compatible pairings, and let $f$ be a
nonnegative closed convex function on $E$ with $f(0) = 0$. Then polarity and conjugacy commute:
$$f^{*\circ} = f^{\circ *},$$
where the outer operation on each side is taken with respect to the flipped pairing. This is
Corollary 15.5.1 of [rockafellar1970convex]. -/
theorem polarFn_convexConj_eq_convexConj_polarFn (h : IsPolarFn f) :
    polarFn B.flip (convexConj B f) = convexConj B.flip (polarFn B f) := by
  rw [← obverse_eq_polarFn_convexConj (B := B) h,
    convexConj_eq_obverse_polarFn (B := B.flip) (isPolarFn_polarFn (B := B) h),
    polarFn_polarFn h.convexFn h.nonneg h.map_zero_le, h.closedConvex]

omit [LocallyConvexSpace ℝ E] in
/-- Let $E$ be a topological vector space, let $f$ be a nonnegative closed convex function on $E$
with $f(0) = 0$, and let $\alpha > 0$. Then the sublevel sets of the obverse are
$$\{x : \operatorname{ob}(f)(x) \le \alpha\} = \alpha \{x : f(x) \le \alpha^{-1}\}.$$
[rockafellar1970convex] states this in §15, after Theorem 15.5. -/
theorem setOf_obverse_le (h : IsPolarFn f) {α : ℝ} (hα : 0 < α) :
    {x : E | obverse f x ≤ (α : EReal)} = α • {x : E | f x ≤ ((α⁻¹ : ℝ) : EReal)} := by
  ext z
  rw [Set.mem_ofPred_eq, obverse_le_coe_iff h hα, mem_smul_set_iff_inv_smul_mem₀ hα.ne']
  exact Iff.rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [LocallyConvexSpace ℝ F] [IsCompatiblePairing B] in
/-- Let $F$ be a topological vector space, let the flipped pairing be compatible with the topology
of $F$, let $f$ be a nonnegative closed convex function on $E$ with $f(0) = 0$, and let
$\alpha > 0$. Then
$$\{y : f^\circ(y) \le \alpha^{-1}\} = \alpha^{-1} \{y : f^*(y) \le \alpha\}.$$
[rockafellar1970convex] states this at the end of §15. It is the middle set of
`ConvexAnalysis.polarSet_setOf_le_subset_and_subset`. -/
theorem setOf_polarFn_le (h : IsPolarFn f) {α : ℝ} (hα : 0 < α) :
    {y : F | polarFn B f y ≤ ((α⁻¹ : ℝ) : EReal)}
      = α⁻¹ • {y : F | convexConj B f y ≤ (α : EReal)} := by
  rw [polarFn_eq_obverse_convexConj (B := B) h,
    setOf_obverse_le (isPolarFn_convexConj (B := B) h) (inv_pos.2 hα), inv_inv]

end PolarConjObverse

/-!
### Norms

A gauge that is finite everywhere, symmetric, and positive away from the origin is a **norm**.
[rockafellar1970convex] states the correspondence with the symmetric closed bounded convex sets $C$
with $0 \in \operatorname{int} C$. Two of these conditions are finite-dimensional forms of
conditions that make sense in general, and the general forms are proved here:

* $0 \in \operatorname{int} C$, which in $\mathbb{R}^n$ says that $C$ contains a positive multiple
  of every vector, becomes `ConvexAnalysis.AbsorbsAll`;
* "$C$ is bounded", which in $\mathbb{R}^n$ says that $C$ contains no half-line from the origin,
  becomes `ConvexAnalysis.RayFree`.

Closedness is not part of the correspondence here. The source obtains it from the continuity of a
finite convex function on $\mathbb{R}^n$, which is a finite-dimensional fact; in an
infinite-dimensional space a finite symmetric positive gauge need not be lower semicontinuous.
-/

section Norm

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {k : E → EReal}

/-- A set $C$ **absorbs every point** if every $x \in E$ lies in $aC$ for some $a \ge 0$.

This is the form in which absorbency enters the gauge. `ConvexAnalysis.absorbsAll_of_absorbent`
derives it from Mathlib's `Absorbent`. -/
def AbsorbsAll (C : Set E) : Prop := ∀ x : E, ∃ a : ℝ, 0 ≤ a ∧ x ∈ a • C

/-- A set $C$ **contains no ray** if for every $x \neq 0$ there is $\lambda > 0$ with
$\lambda x \notin C$. -/
def RayFree (C : Set E) : Prop := ∀ x : E, x ≠ 0 → ∃ l : ℝ, 0 < l ∧ l • x ∉ C

/-- A **norm**, in the sense of [rockafellar1970convex], is a gauge $k$ that is finite everywhere,
symmetric ($k(-x) = k(x)$), and positive away from the origin. -/
structure IsNorm (k : E → EReal) : Prop extends IsGauge k where
  /-- A norm is finite everywhere. -/
  ne_top : ∀ x, k x ≠ ⊤
  /-- A norm is symmetric: $k(-x) = k(x)$. -/
  map_neg : ∀ x, k (-x) = k x
  /-- A norm is positive away from the origin. -/
  pos : ∀ x, x ≠ 0 → 0 < k x

/-- The gauge of $-C$ at $x$ is the gauge of $C$ at $-x$. -/
theorem gaugeFn_neg_set (C : Set E) (x : E) : gaugeFn (-C) x = gaugeFn C (-x) := by
  have hset : {a : ℝ | 0 ≤ a ∧ x ∈ a • (-C)} = {a : ℝ | 0 ≤ a ∧ -x ∈ a • C} := by
    ext a
    simp only [Set.mem_ofPred, Set.smul_set_neg, Set.mem_neg]
  rw [gaugeFn_apply, gaugeFn_apply, hset]

/-- If $C$ is symmetric ($-C = C$), then $\gamma(-x \mid C) = \gamma(x \mid C)$. -/
theorem gaugeFn_map_neg (hsymm : -C = C) (x : E) : gaugeFn C (-x) = gaugeFn C x := by
  rw [← gaugeFn_neg_set, hsymm]

/-- The gauge is finite at $x$ if and only if $x \in aC$ for some $a \ge 0$. -/
theorem gaugeFn_ne_top_iff (C : Set E) (x : E) :
    gaugeFn C x ≠ ⊤ ↔ ∃ a : ℝ, 0 ≤ a ∧ x ∈ a • C := by
  rw [← lt_top_iff_ne_top, gaugeFn_lt_iff]
  constructor
  · rintro ⟨a, ha0, hmem, -⟩
    exact ⟨a, ha0, hmem⟩
  · rintro ⟨a, ha0, hmem⟩
    exact ⟨a, ha0, hmem, EReal.coe_lt_top a⟩

/-- Let $C$ be convex with $0 \in C$. Then $\gamma(x \mid C) = 0$ if and only if $\lambda x \in C$
for every $\lambda > 0$: the gauge vanishes exactly on the rays in $C$. -/
theorem gaugeFn_eq_zero_iff (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (x : E) :
    gaugeFn C x = 0 ↔ ∀ l : ℝ, 0 < l → l • x ∈ C := by
  constructor
  · intro h l hl
    have hle : gaugeFn C x ≤ ((0 : ℝ) : EReal) := by rw [h, EReal.coe_zero]
    rw [gaugeFn_le_coe_iff_forall_lt hC h0 le_rfl] at hle
    have hmem := hle l⁻¹ (inv_pos.2 hl)
    rwa [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne') C x, inv_inv] at hmem
  · intro h
    refine le_antisymm ?_ (gaugeFn_nonneg C x)
    rw [← EReal.coe_zero, gaugeFn_le_coe_iff_forall_lt hC h0 le_rfl]
    intro d hd
    rw [mem_smul_set_iff_inv_smul_mem₀ hd.ne' C x]
    exact h d⁻¹ (inv_pos.2 hd)

/-- Let $C$ be convex and symmetric with $0 \in C$. If $C$ absorbs every point and contains no ray,
then $\gamma(\cdot \mid C)$ is a norm. -/
theorem isNorm_gaugeFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hsymm : -C = C)
    (habs : AbsorbsAll C) (hray : RayFree C) : IsNorm (gaugeFn C) where
  toIsGauge := isGauge_gaugeFn hC ⟨0, h0⟩
  ne_top x := (gaugeFn_ne_top_iff C x).2 (habs x)
  map_neg x := gaugeFn_map_neg hsymm x
  pos x hx := by
    refine lt_of_le_of_ne (gaugeFn_nonneg C x) fun hcon => ?_
    obtain ⟨l, hl, hlx⟩ := hray x hx
    exact hlx (((gaugeFn_eq_zero_iff hC h0 x).1 hcon.symm) l hl)

/-- The unit sublevel set $\{x : k(x) \le 1\}$ of a norm $k$ is convex and symmetric, contains $0$,
absorbs every point, and contains no ray. -/
theorem IsNorm.level_one (hk : IsNorm k) :
    Convex ℝ {x : E | k x ≤ 1} ∧ (0 : E) ∈ {x : E | k x ≤ 1} ∧ -{x : E | k x ≤ 1} =
      {x : E | k x ≤ 1} ∧ AbsorbsAll {x : E | k x ≤ 1} ∧ RayFree {x : E | k x ≤ 1} := by
  refine ⟨hk.toIsGauge.convex_level_one, hk.toIsGauge.zero_mem_level_one, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_neg, Set.mem_ofPred, hk.map_neg]
  · intro x
    obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hk.toIsGauge.ne_bot x)
      (lt_top_iff_ne_top.2 (hk.ne_top x))
    refine ⟨max c 1, le_trans zero_le_one (le_max_right c 1), ?_⟩
    have hmax : (0 : ℝ) < max c 1 := lt_of_lt_of_le zero_lt_one (le_max_right c 1)
    rw [mem_smul_set_iff_inv_smul_mem₀ hmax.ne']
    change k ((max c 1)⁻¹ • x) ≤ 1
    rw [hk.posHomogeneous _ (inv_pos.2 hmax) x, hc, ← EReal.coe_one,
      ← EReal.coe_mul, EReal.coe_le_coe_iff, inv_mul_le_iff₀ hmax, mul_one]
    exact le_max_left c 1
  · intro x hx
    obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hk.toIsGauge.ne_bot x)
      (lt_top_iff_ne_top.2 (hk.ne_top x))
    have hcpos : (0 : ℝ) < c := by
      have := hk.pos x hx; rw [hc, ← EReal.coe_zero, EReal.coe_lt_coe_iff] at this
      exact this
    refine ⟨2 / c, by positivity, ?_⟩
    intro hmem
    have hle : k ((2 / c) • x) ≤ 1 := hmem
    rw [hk.posHomogeneous _ (by positivity) x, hc, ← EReal.coe_one,
      ← EReal.coe_mul, EReal.coe_le_coe_iff, div_mul_cancel₀ (2 : ℝ) hcpos.ne'] at hle
    linarith

/-- A function $k$ is a norm if and only if $k = \gamma(\cdot \mid C)$ for a convex symmetric set
$C$ with $0 \in C$ that absorbs every point and contains no ray. This is part of Theorem 15.2 of
[rockafellar1970convex].

The source states the correspondence for closed bounded sets with $0 \in \operatorname{int} C$;
see the module doc comment for the relation between the conditions. -/
theorem isNorm_iff :
    IsNorm k ↔ ∃ C : Set E, Convex ℝ C ∧ (0 : E) ∈ C ∧ -C = C ∧ AbsorbsAll C ∧ RayFree C ∧
      k = gaugeFn C := by
  constructor
  · intro hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hk.level_one
    exact ⟨{x : E | k x ≤ 1}, h1, h2, h3, h4, h5,
      (gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero).symm⟩
  · rintro ⟨C, hC, h0, hsymm, habs, hray, rfl⟩
    exact isNorm_gaugeFn hC h0 hsymm habs hray

/-!
### A norm is a `Seminorm`

Mathlib's `Seminorm` is purely algebraic: subadditive and absolutely homogeneous, with no topology.
Hence a norm in the sense of [rockafellar1970convex] is a `Seminorm`. It is not the norm of a
`NormedSpace` unless it is continuous, which it need not be.
-/

/-- For a norm $k$, the real number $k(x)$, embedded back in `EReal`, is $k(x)$. -/
theorem IsNorm.coe_toReal (hk : IsNorm k) (x : E) : (((k x).toReal : ℝ) : EReal) = k x :=
  EReal.coe_toReal (hk.ne_top x) (hk.toIsGauge.ne_bot x)

/-- A norm is absolutely homogeneous: $k(ax) = |a|\, k(x)$ for every real $a$. Symmetry extends
positive homogeneity from $a > 0$ to all $a$. -/
theorem IsNorm.apply_smul (hk : IsNorm k) (a : ℝ) (x : E) :
    k (a • x) = ((|a| : ℝ) : EReal) * k x := by
  rcases lt_trichotomy a 0 with h | h | h
  · have hx : a • x = -((-a) • x) := by rw [neg_smul, neg_neg]
    rw [hx, hk.map_neg, hk.toIsGauge.posHomogeneous (-a) (neg_pos.2 h) x, abs_of_neg h]
  · subst h
    simp [hk.toIsGauge.map_zero]
  · rw [hk.toIsGauge.posHomogeneous a h x, abs_of_pos h]

/-- A norm $k$ in the sense of [rockafellar1970convex] defines a Mathlib `Seminorm`
$x \mapsto k(x)$, with the values taken in $\mathbb{R}$.

`Seminorm ℝ E` asks for subadditivity (which follows from convexity and positive homogeneity),
invariance under negation, and absolute homogeneity. `ConvexAnalysis.IsNorm` gives all three,
and none of them involves a topology. The construction does not give a `NormedSpace`: that needs
a continuous norm, and the continuity of a finite convex function is a finite-dimensional fact. -/
noncomputable def IsNorm.toSeminorm (hk : IsNorm k) : Seminorm ℝ E where
  toFun x := (k x).toReal
  map_zero' := by simp [hk.toIsGauge.map_zero]
  add_le' x y := by
    have hsub :=
      (PosHomogeneous.convexFn_iff_subadditive hk.toIsGauge.posHomogeneous
        hk.toIsGauge.ne_bot).1 hk.toIsGauge.convexFn x y
    have hcoe : (((k (x + y)).toReal : ℝ) : EReal)
        ≤ (((k x).toReal + (k y).toReal : ℝ) : EReal) := by
      rw [hk.coe_toReal, EReal.coe_add, hk.coe_toReal, hk.coe_toReal]
      exact hsub
    exact_mod_cast hcoe
  neg' x := by rw [hk.map_neg]
  smul' a x := by
    rw [hk.apply_smul a x, EReal.toReal_mul, EReal.toReal_coe, Real.norm_eq_abs]

/-- The value of `ConvexAnalysis.IsNorm.toSeminorm` at $x$, embedded in `EReal`, is $k(x)$. -/
@[simp] theorem IsNorm.coe_toSeminorm (hk : IsNorm k) (x : E) :
    ((hk.toSeminorm x : ℝ) : EReal) = k x := hk.coe_toReal x

end Norm

/-! ### The polar of a norm -/

section NormPolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

/-- If $C$ is symmetric ($-C = C$), then so is its polar: $-C^\circ = C^\circ$. -/
theorem polarSet_neg_eq (hsymm : -C = C) : -polarSet B C = polarSet B C := by
  have hnegC : ∀ x ∈ C, -x ∈ C := fun x hx => by
    rw [← hsymm]
    exact Set.neg_mem_neg.2 hx
  have hb : ∀ (x : E) (y : F), B (-x) (-y) = B x y := fun x y => by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  have hb2 : ∀ (x : E) (y : F), B x (-y) = B (-x) y := fun x y => by
    simp only [map_neg, LinearMap.neg_apply]
  ext y
  simp only [Set.mem_neg, mem_polarSet]
  constructor
  · intro h x hx
    have hle := h (-x) (hnegC x hx)
    rwa [hb] at hle
  · intro h x hx
    have hle := h (-x) (hnegC x hx)
    rwa [← hb2] at hle

/-- If for every $y \in F$ the function $\langle \cdot, y \rangle$ is bounded above on $C$, then
$C^\circ$ absorbs every point. -/
theorem absorbsAll_polarSet (hbdd : ∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c) :
    AbsorbsAll (polarSet B C) := by
  intro y
  obtain ⟨c, hc⟩ := hbdd y
  refine ⟨max c 1, le_trans zero_le_one (le_max_right c 1), ?_⟩
  have hmax : (0 : ℝ) < max c 1 := lt_of_lt_of_le zero_lt_one (le_max_right c 1)
  rw [mem_smul_set_iff_inv_smul_mem₀ hmax.ne']
  intro x hx
  rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hmax, mul_one]
  exact le_trans (hc x hx) (le_max_left c 1)

/-- Let $C$ be symmetric. If for every $y \neq 0$ there is $x \in C$ with
$\langle x, y \rangle \neq 0$, then $C^\circ$ contains no ray. -/
theorem rayFree_polarSet (hsymm : -C = C)
    (hsep : ∀ y : F, y ≠ 0 → ∃ x ∈ C, B x y ≠ 0) : RayFree (polarSet B C) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hsep y hy
  have hpos : ∃ z ∈ C, 0 < B z y := by
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · refine ⟨-x, by rw [← hsymm]; exact Set.neg_mem_neg.2 hx, ?_⟩
      simp only [map_neg, LinearMap.neg_apply]
      linarith
    · exact ⟨x, hx, hgt⟩
  obtain ⟨z, hz, hzy⟩ := hpos
  refine ⟨2 / B z y, by positivity, fun hmem => ?_⟩
  have h := hmem z hz
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ (2 : ℝ) hzy.ne'] at h
  linarith

/-- Let $C$ be convex and symmetric with $0 \in C$. Assume that for every $y \in F$ the function
$\langle \cdot, y \rangle$ is bounded above on $C$, and that for every $y \neq 0$ there is
$x \in C$ with $\langle x, y \rangle \neq 0$. Then the polar $\gamma(\cdot \mid C)^\circ$ of the
gauge of $C$ is a norm. This is part of Theorem 15.2 of [rockafellar1970convex].

The two hypotheses are general forms of "$C$ is bounded" and "$0 \in \operatorname{int} C$".
Boundedness of the pairing on $C$ makes the polar absorb every point, and separation of the
points of $F$ by $C$ makes the polar contain no ray. -/
theorem isNorm_polarGauge_gaugeFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hsymm : -C = C)
    (hbdd : ∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c)
    (hsep : ∀ y : F, y ≠ 0 → ∃ x ∈ C, B x y ≠ 0) :
    IsNorm (polarGauge B (gaugeFn C)) := by
  rw [polarGauge_gaugeFn hC ⟨0, h0⟩]
  exact isNorm_gaugeFn (convex_polarSet B C) (fun x _ => by simp) (polarSet_neg_eq hsymm)
    (absorbsAll_polarSet hbdd) (rayFree_polarSet hsymm hsep)

end NormPolar

/-! ### Relation to Mathlib's `gauge` -/

section MathlibGauge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- If $C$ is absorbent, then $\gamma(x \mid C)$ equals Mathlib's `gauge C x`.

Mathlib's `gauge` takes the infimum over positive scalars in $\mathbb{R}$, so at a point that no
dilate of $C$ contains it has the value $\inf \emptyset = 0$ instead of $+\infty$. For an
absorbent set there is no such point. -/
theorem gaugeFn_eq_gauge (hC : Absorbent ℝ C) (x : E) : gaugeFn C x = (gauge C x : EReal) := by
  refine le_antisymm (le_coe_of_forall_gt_le fun d hd => ?_) ?_
  · obtain ⟨b, hb0, hbd, hbx⟩ := exists_lt_of_gauge_lt hC hd
    exact le_trans (gaugeFn_le_of_mem_smul hb0.le hbx) (by exact_mod_cast hbd.le)
  · rw [gaugeFn_apply]
    refine le_iInf₂ (f := fun (a : ℝ) (_ : a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}) => (a : EReal))
      fun a ha => ?_
    exact_mod_cast gauge_le_of_mem ha.1 ha.2

/-- The gauge of an absorbent set is finite everywhere. -/
theorem gaugeFn_lt_top_of_absorbent (hC : Absorbent ℝ C) (x : E) : gaugeFn C x < ⊤ := by
  rw [gaugeFn_eq_gauge hC]
  exact EReal.coe_lt_top _

/-- An absorbent set in the sense of Mathlib's `Absorbent` absorbs every point in the sense of
`ConvexAnalysis.AbsorbsAll`. -/
theorem absorbsAll_of_absorbent (hC : Absorbent ℝ C) : AbsorbsAll C := fun x => by
  obtain ⟨r, hr0, hr⟩ := (hC x).exists_pos
  exact ⟨r, hr0.le, hr r (Real.norm_of_nonneg hr0.le).ge rfl⟩

end MathlibGauge


end ConvexAnalysis
