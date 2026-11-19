/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.GaugeLike
import Numlib.Analysis.Convex.Recession.Cone
import NumlibSurface.Rockafellar.Chapter03.Section13

/-!
# Rockafellar, Section 15: Polars of convex functions

This module formalizes Section 15 of [rockafellar1970convex]. A gauge is a non-negative positively
homogeneous convex function $k$ with $k(0) = 0$; the gauge of a set $C$ is $\gamma(x \mid C) = \inf
\{\mu \ge 0 \mid x \in \mu C\}$. The polar of a gauge is $k^\circ(x^*) = \inf \{\mu^* \ge 0 \mid
\langle x, x^* \rangle \le \mu^* k(x) \text{ for all } x\}$. The section shows that
$k^{\circ\circ} = \operatorname{cl} k$, so that polarity is a symmetric one-to-one correspondence on
the closed gauges; characterizes the norms as the gauges of symmetric closed bounded convex sets
with the origin in the interior; describes the gauge-like closed proper convex functions and their
conjugates; and extends polarity to non-negative convex functions $f$ with $f(0) = 0$ through
$f^\circ(x^*) = \inf \{\mu^* \ge 0 \mid \langle x, x^* \rangle \le 1 + \mu^* f(x) \text{ for all }
x\}$ and the obverse of $f$. All 11 numbered results of the section are formalized. The proofs
specialize `Numlib.Analysis.Convex.Duality.Gauge` and `Numlib.Analysis.Convex.Duality.GaugeLike` to
the self-pairing of $\mathbb{R}^n$.

The unnumbered text of the section is formalized as well: a gauge is the gauge of its own unit level
set, and a closed gauge determines the closed convex set containing the origin; gauges polar to each
other satisfy $\langle x, x^* \rangle \le k(x) k^\circ(x^*)$, with the Schwarz inequality as the
case of the Euclidean norm, which is its own polar; norms correspond to Minkowski metrics; and the
level sets of the obverse and of $f^\circ$ are described, ending with $\{x^* \mid f^\circ(x^*) \le
\alpha^{-1}\} = \alpha^{-1} \{x^* \mid f^*(x^*) \le \alpha\}$.

## Main definitions

* `Rockafellar.IsMinkowskiMetric`: a metric on $\mathbb{R}^n$ that is invariant under translation
  and linear along line segments.
* `Rockafellar.corollary_15_1_1_gaugeEquiv`: the correspondence $C \mapsto \gamma(\cdot \mid C)$
  between the closed convex sets containing the origin and the closed gauges.

## Main results

* Theorem 15.1, `Rockafellar.theorem_15_1_isGauge`, `Rockafellar.theorem_15_1_closedFn`,
  `Rockafellar.theorem_15_1_polar_polar`, `Rockafellar.theorem_15_1_gaugeFn`: the polar of a gauge
  is a closed gauge, $k^{\circ\circ} = \operatorname{cl} k$, and $\gamma(\cdot \mid C)^\circ =
  \gamma(\cdot \mid C^\circ)$ for a non-empty convex set $C$.
* Corollary 15.1.1, `Rockafellar.corollary_15_1_1`, `Rockafellar.corollary_15_1_1_sets`:
  $k \mapsto k^\circ$ is a symmetric one-to-one correspondence on the closed gauges, and two closed
  convex sets containing the origin are polar to each other if and only if their gauges are.
* Corollary 15.1.2, `Rockafellar.corollary_15_1_2`, `Rockafellar.corollary_15_1_2_symm`: the gauge
  and the support function of a closed convex set containing the origin are polar to each other.
* Theorem 15.2, `Rockafellar.theorem_15_2_isNorm`, `Rockafellar.theorem_15_2_setOf_le_one`,
  `Rockafellar.theorem_15_2_gaugeFn`, `Rockafellar.theorem_15_2_setOf_gaugeFn_le_one`,
  `Rockafellar.theorem_15_2_polar`: the norms are exactly the gauges of the symmetric closed bounded
  convex sets with the origin in the interior, and the polar of a norm is a norm.
* Theorem 15.3, `Rockafellar.theorem_15_3`, `Rockafellar.theorem_15_3_conj`,
  `Rockafellar.theorem_15_3_isGaugeLike_conj`: the gauge-like closed proper convex functions are the
  functions $g \circ k$ with $k$ a closed gauge and $g$ a suitable function on $[0, +\infty]$, and
  then $f^* = g^+ \circ k^\circ$ is gauge-like too.
* Corollary 15.3.1, `Rockafellar.corollary_15_3_1`, `Rockafellar.corollary_15_3_1_conj`: the closed
  proper convex functions positively homogeneous of degree $p > 1$ are the functions $(1/p) k^p$
  with $k$ a closed gauge, and $[(1/p) k^p]^* = (1/q) (k^\circ)^q$.
* Corollary 15.3.2, `Rockafellar.corollary_15_3_2_isGauge`, `Rockafellar.corollary_15_3_2`,
  `Rockafellar.corollary_15_3_2_inequality`, `Rockafellar.corollary_15_3_2_polarSet`: for such $f$,
  $(pf)^{1/p}$ is a closed gauge with polar $(qf^*)^{1/q}$, with the corresponding inequality and
  polarity of level sets.
* Theorem 15.4, `Rockafellar.theorem_15_4_nonneg`, `Rockafellar.theorem_15_4_map_zero`,
  `Rockafellar.theorem_15_4_convexFn`, `Rockafellar.theorem_15_4_closedFn`,
  `Rockafellar.theorem_15_4_polar_polar`: $f^\circ$ is a non-negative closed convex function
  vanishing at the origin, and $f^{\circ\circ} = \operatorname{cl} f$.
* Corollary 15.4.1, `Rockafellar.corollary_15_4_1`: $f \mapsto f^\circ$ is a symmetric one-to-one
  correspondence on the non-negative closed convex functions vanishing at the origin.
* Theorem 15.5, `Rockafellar.theorem_15_5_isPolarFn`, `Rockafellar.theorem_15_5_obverse_obverse`,
  `Rockafellar.theorem_15_5_polarFn_eq_conj_obverse`,
  `Rockafellar.theorem_15_5_conj_eq_polarFn_obverse`,
  `Rockafellar.theorem_15_5_conj_eq_obverse_polarFn`,
  `Rockafellar.theorem_15_5_polarFn_eq_obverse_conj`: the obverse $g$ of $f$ is in the same class,
  $f$ is the obverse of $g$, $f^\circ = g^*$ and $f^* = g^\circ$, and $f^*$ and $f^\circ$ are
  obverses of each other.
* Corollary 15.5.1, `Rockafellar.corollary_15_5_1`: $f^{*\circ} = f^{\circ *}$.

## Conventions

* A gauge is `ConvexAnalysis.IsGauge`.
* The gauge $\gamma(\cdot \mid C)$ of a set $C$ is `ConvexAnalysis.gaugeFn C`.
* The polar $k^\circ$ of a gauge $k$ is `ConvexAnalysis.polarGauge (Rockafellar.pairing n) k`.
* A norm in the sense of the book is `ConvexAnalysis.IsNorm`: a gauge that is finite everywhere,
  symmetric and positive away from the origin. These are the conditions (a)–(d) of the book.
  `ConvexAnalysis.IsNorm.toSeminorm` turns such a norm into a Mathlib `Seminorm`.
* A gauge-like function is `ConvexAnalysis.IsGaugeLike`: $f(0) = \inf f$, and the level sets
  $\{x \mid f(x) \le \alpha\}$ for $\alpha > f(0)$ are all positive multiples of one set. Positive
  homogeneity of degree $p$ is `ConvexAnalysis.PosHomogeneousDeg`.
* The polar $f^\circ$ of a non-negative convex function vanishing at the origin is
  `ConvexAnalysis.polarFn (Rockafellar.pairing n) f`, and the class of non-negative closed convex
  functions vanishing at the origin is `ConvexAnalysis.IsPolarFn`.
* The obverse of $f$ is `ConvexAnalysis.obverse f`, $g(x) = \inf \{\lambda > 0 \mid (f\lambda)(x)
  \le 1\}$, where $f\lambda$ is the right scalar multiple of Section 5.
* All infima are taken in $[-\infty, +\infty]$, and the infimum of the empty set is $+\infty$.

## Deviations from the source

* **Section 15, gauge and polar formulas** (generalization). `Rockafellar.gaugeFn_apply_rn`
  admits arbitrary sets, `Rockafellar.polarGauge_apply_rn` admits arbitrary functions, and
  `Rockafellar.polarFn_apply_rn` applies to nonnegative functions vanishing at zero without
  requiring convexity.
* **Section 15, obverse formula** (generalization). `Rockafellar.obverse_apply_rn` states the
  formula for arbitrary extended-real functions. The book introduces it for nonnegative
  closed convex functions vanishing at zero.
* **Corollary 15.1.1**, polar sets and polar gauges (generalization). The set $C$ need not be
  closed. See `Rockafellar.corollary_15_1_1_sets`.
* **Corollary 15.1.2** (generalization). The identity $\gamma(\cdot \mid C)^\circ = \delta^*(\cdot
  \mid C)$ holds for every convex set $C$ containing the origin. See `Rockafellar.corollary_15_1_2`.
* **Theorem 15.2**, the gauge of $C$ is a norm (generalization). The set $C$ need not be closed. See
  `Rockafellar.theorem_15_2_isNorm`.
* **Theorem 15.3**, the formula $f^* = g^+ \circ k^\circ$ (generalization). The function $g$ need
  not be non-constant. See `Rockafellar.theorem_15_3_conj`.
* **Theorem 15.4**, first assertion (generalization). The properties of $f^\circ$ need fewer
  hypotheses than the book gives: non-negativity and $f^\circ(0) = 0$ need only $f(0) = 0$,
  convexity needs only $f \ge 0$, and closedness needs $f \ge 0$ and $f(0) = 0$; convexity of $f$ is
  never needed. See `Rockafellar.theorem_15_4_nonneg`, `Rockafellar.theorem_15_4_map_zero`,
  `Rockafellar.theorem_15_4_convexFn` and `Rockafellar.theorem_15_4_closedFn`.

## Not formalized

* **Existence of a norm inducing a given Minkowski metric.**
  `Rockafellar.minkowskiMetric_eq_sub` identifies the only possible norm, and
  `Rockafellar.isMinkowskiMetric_of_isNorm` proves that each norm induces such a metric.
-/

open Set Pointwise Bornology

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### The definitions of Section 15 -/

/-- **Section 15** of [rockafellar1970convex], the gauge function (p. 128). For
$C \subseteq \mathbb{R}^n$ and $x \in \mathbb{R}^n$,
$$\gamma(x \mid C) = \inf \{\mu \ge 0 \mid x \in \mu C\},$$
with $\inf \emptyset = +\infty$.

The gauge is `ConvexAnalysis.gaugeFn C`.

**Generalization.** The book uses the formula for nonempty convex $C$. The Lean formula
also applies to arbitrary sets. -/
theorem gaugeFn_apply_rn (C : Set (Rn n)) (x : Rn n) :
    gaugeFn C x = ⨅ a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}, (a : EReal) :=
  gaugeFn_apply C x

/-- **Section 15** of [rockafellar1970convex], gauges as gauge functions (p. 128). A function
$k : \mathbb{R}^n \to [-\infty, +\infty]$ is a gauge if and only if $k = \gamma(\cdot \mid C)$
for some non-empty convex set $C$. -/
theorem gauge_iff_exists_gaugeFn {k : Rn n → EReal} :
    IsGauge k ↔ ∃ C : Set (Rn n), C.Nonempty ∧ Convex ℝ C ∧ k = gaugeFn C :=
  isGauge_iff

/-- **Section 15** of [rockafellar1970convex] (p. 128). Let $k$ be a gauge on $\mathbb{R}^n$. Then
$k = \gamma(\cdot \mid C)$ for $C = \{x \mid k(x) \le 1\}$. The book states that one always has
this identity. Closedness of $k$ is not needed. -/
theorem gaugeFn_setOf_le_one {k : Rn n → EReal} (hk : IsGauge k) :
    gaugeFn {x : Rn n | k x ≤ 1} = k :=
  gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero

/-- **Section 15** of [rockafellar1970convex], the polar of a gauge (p. 128). For
$k : \mathbb{R}^n \to [-\infty, +\infty]$ and $x^* \in \mathbb{R}^n$,
$$k^\circ(x^*) = \inf \{\mu^* \ge 0 \mid \langle x, x^* \rangle \le \mu^* k(x) \text{ for all }
  x\}.$$

The polar is `ConvexAnalysis.polarGauge (Rockafellar.pairing n) k`, and this equation is its
definition unfolded. The product $\mu^* k(x)$ is taken in `EReal`, where
$0 \cdot (+\infty) = 0$.

**Generalization.** The book assumes $k$ is a gauge. The formula is defined here for
arbitrary functions. -/
theorem polarGauge_apply_rn (k : Rn n → EReal) (y : Rn n) :
    polarGauge (pairing n) k y
      = ⨅ m ∈ {m : ℝ | 0 ≤ m ∧ ∀ x : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ (m : EReal) * k x},
          (m : EReal) :=
  polarGauge_apply (pairing n) k y

/-- **Section 15** of [rockafellar1970convex], the polar of a non-negative convex function vanishing
at the origin (p. 136). Let $f : \mathbb{R}^n \to [-\infty, +\infty]$ be non-negative with
$f(0) = 0$. Then for every $x^*$,
$$f^\circ(x^*) = \inf \{\mu^* \ge 0 \mid \langle x, x^* \rangle \le 1 + \mu^* f(x) \text{ for
  all } x\}.$$

The backbone definition `ConvexAnalysis.polarFn` quantifies over the points of
$\operatorname{epi} f$ instead of over $x$, because the admissible set of the book is not closed
at $\mu^* = 0$. `ConvexAnalysis.polarFn_apply_eq` identifies the two forms.

**Generalization.** The book assumes $f$ convex. The displayed formula only needs
nonnegativity and $f(0) = 0$. -/
theorem polarFn_apply_rn {f : Rn n → EReal} (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 = 0) (y : Rn n) :
    polarFn (pairing n) f y
      = ⨅ m ∈ {m : ℝ | 0 ≤ m ∧ ∀ x : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ 1 + (m : EReal) * f x},
          (m : EReal) :=
  polarFn_apply_eq hnn h0.le y

/-- **Section 15** of [rockafellar1970convex], the obverse (p. 137). For
$f : \mathbb{R}^n \to [-\infty, +\infty]$ and $x \in \mathbb{R}^n$, the obverse $g$ of $f$ is
$$g(x) = \inf \{\lambda > 0 \mid (f\lambda)(x) \le 1\},$$
where $(f\lambda)(x) = \lambda f(\lambda^{-1} x)$ is the right scalar multiple of Section 5
(`ConvexAnalysis.smulRight`).

**Generalization.** The book introduces the formula for nonnegative closed convex $f$
vanishing at zero. The infimum formula applies to any $f$. -/
theorem obverse_apply_rn (f : Rn n → EReal) (x : Rn n) :
    obverse f x = ⨅ l ∈ {l : ℝ | 0 < l ∧ smulRight f l x ≤ 1}, (l : EReal) :=
  obverse_apply f x

/-! ### Theorem 15.1 -/

/-- **Theorem 15.1** of [rockafellar1970convex], third assertion. Let $C \subseteq \mathbb{R}^n$ be
a non-empty convex set and $k = \gamma(\cdot \mid C)$. Then
$k^\circ = \gamma(\cdot \mid C^\circ)$. -/
theorem theorem_15_1_gaugeFn {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty) :
    polarGauge (pairing n) (gaugeFn C) = gaugeFn (polarSet (pairing n) C) :=
  polarGauge_gaugeFn hC hne

/-- **Theorem 15.1** of [rockafellar1970convex], first assertion. If $k$ is a gauge on
$\mathbb{R}^n$, then $k^\circ$ is a gauge. -/
theorem theorem_15_1_isGauge {k : Rn n → EReal} (hk : IsGauge k) :
    IsGauge (polarGauge (pairing n) k) :=
  isGauge_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero

/-- **Theorem 15.1** of [rockafellar1970convex], first assertion. If $k$ is a gauge on
$\mathbb{R}^n$, then $k^\circ$ is closed. -/
theorem theorem_15_1_closedFn {k : Rn n → EReal} (hk : IsGauge k) :
    ClosedConvex (polarGauge (pairing n) k) :=
  closedConvex_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero

/-- **Theorem 15.1** of [rockafellar1970convex], second assertion. If $k$ is a gauge on
$\mathbb{R}^n$, then $k^{\circ\circ} = \operatorname{cl} k$.

The backbone proves this from Theorem 15.4, not by the route of the book through Theorem 14.5
and the unit level set. -/
theorem theorem_15_1_polar_polar {k : Rn n → EReal} (hk : IsGauge k) :
    polarGauge (pairing n) (polarGauge (pairing n) k) = convexCl k := by
  have h := polarGauge_polarGauge (B := pairing n) hk
  rwa [flip_pairing] at h

/-! ### Corollary 15.1.1 -/

/-- **Section 15** of [rockafellar1970convex], the correspondence between sets and gauges (p. 128).
The maps $C \mapsto \gamma(\cdot \mid C)$ and $k \mapsto \{x \mid k(x) \le 1\}$ are inverse
one-to-one correspondences between the closed convex sets in $\mathbb{R}^n$ containing the
origin and the closed gauges on $\mathbb{R}^n$. Corollary 15.1.1 quantifies over this class of
gauges.

The correspondence is `ConvexAnalysis.gaugeEquiv`. -/
noncomputable def corollary_15_1_1_gaugeEquiv (n : ℕ) :
    {C : Set (Rn n) // Convex ℝ C ∧ IsClosed C ∧ (0 : Rn n) ∈ C} ≃
      {k : Rn n → EReal // IsGauge k ∧ ClosedConvex k} :=
  gaugeEquiv (Rn n)

/-- **Corollary 15.1.1** of [rockafellar1970convex], first assertion. The map $k \mapsto k^\circ$
induces a symmetric one-to-one correspondence in the class of all closed gauges on
$\mathbb{R}^n$.

The correspondence is `ConvexAnalysis.polarGaugeEquiv` for `Rockafellar.pairing n`. -/
noncomputable def corollary_15_1_1 (n : ℕ) :
    {k : Rn n → EReal // IsGauge k ∧ ClosedConvex k} ≃
      {j : Rn n → EReal // IsGauge j ∧ ClosedConvex j} :=
  polarGaugeEquiv (pairing n)

/-- **Corollary 15.1.1** of [rockafellar1970convex], second assertion. Let
$C, D \subseteq \mathbb{R}^n$ be convex sets containing the origin, with $D$ closed. Then
$C^\circ = D$ if and only if $\gamma(\cdot \mid C)^\circ = \gamma(\cdot \mid D)$.

**Generalization.** The book states the assertion for two closed convex sets containing the
origin. The set $C$ need not be closed. -/
theorem corollary_15_1_1_sets {C D : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C)
    (hD : Convex ℝ D) (hDcl : IsClosed D) (hD0 : (0 : Rn n) ∈ D) :
    polarSet (pairing n) C = D ↔ polarGauge (pairing n) (gaugeFn C) = gaugeFn D :=
  polarSet_eq_iff_polarGauge_gaugeFn_eq (pairing n) hC h0 hD hDcl hD0

/-! ### Corollary 15.1.2 -/

/-- **Corollary 15.1.2** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be a convex set
containing the origin. Then the polar of the gauge function of $C$ is the support function of
$C$:
$$\gamma(\cdot \mid C)^\circ = \delta^*(\cdot \mid C).$$

**Generalization.** The book states the corollary for a closed convex set $C$ containing the
origin. Closedness is not needed for this half; the other half is
`Rockafellar.corollary_15_1_2_symm`. -/
theorem corollary_15_1_2 {C : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C) :
    polarGauge (pairing n) (gaugeFn C) = supportFn (pairing n) C :=
  polarGauge_gaugeFn_eq_supportFn hC h0

/-- **Corollary 15.1.2** of [rockafellar1970convex], the other half. Let $C \subseteq \mathbb{R}^n$
be a closed convex set containing the origin. Then the polar of the support function of $C$ is
the gauge function of $C$:
$$\delta^*(\cdot \mid C)^\circ = \gamma(\cdot \mid C).$$
With `Rockafellar.corollary_15_1_2` this says that the two gauges are polar to each other.

The proof applies `Rockafellar.theorem_15_1_polar_polar` to `Rockafellar.corollary_15_1_2`; the
gauge of a closed set is closed, so the closure disappears. -/
theorem corollary_15_1_2_symm {C : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C)
    (hcl : IsClosed C) :
    polarGauge (pairing n) (supportFn (pairing n) C) = gaugeFn C := by
  rw [← corollary_15_1_2 hC h0, theorem_15_1_polar_polar (isGauge_gaugeFn hC ⟨0, h0⟩)]
  exact closedConvex_gaugeFn hC h0 hcl

/-! ### The polar-pair inequality -/

/-- **Section 15** of [rockafellar1970convex], the polar-pair inequality (p. 129). Let $k$ be a
closed gauge on $\mathbb{R}^n$, and let $x, x^* \in \mathbb{R}^n$ with $k(x) = c$ and
$k^\circ(x^*) = d$ finite. Then $\langle x, x^* \rangle \le c d$.

The book states the inequality for $x \in \operatorname{dom} k$ and
$x^* \in \operatorname{dom} k^\circ$. The two finite values are named as real numbers $c$ and
$d$, so that the right-hand side is a product of reals. -/
theorem pairing_le_mul_rn {k : Rn n → EReal} (hk : IsGauge k) (hkc : ClosedConvex k) {x y : Rn n}
    {c d : ℝ} (hx : k x = (c : EReal)) (hy : polarGauge (pairing n) k y = (d : EReal)) :
    (inner ℝ x y : ℝ) ≤ c * d :=
  pairing_le_mul_of_gauge hk hkc hx hy

/-! ### Theorem 15.2 -/

section Norms

variable {k : Rn n → EReal}

/-- **Section 15** of [rockafellar1970convex], the beginning of the proof of Theorem 15.2 (p. 131).
A norm on $\mathbb{R}^n$ is continuous, because it is a finite convex function (Theorem 10.1).

The proof uses `ConvexAnalysis.ConvexFn.continuous_of_convexDom_eq_univ`, the backbone form of
Corollary 10.1.1. -/
theorem isNorm_continuous_rn (hk : IsNorm k) : Continuous k := by
  refine hk.toIsGauge.convexFn.continuous_of_convexDom_eq_univ
    ⟨⟨0, lt_of_le_of_ne le_top (hk.ne_top 0)⟩, hk.toIsGauge.ne_bot⟩ ?_
  exact Set.eq_univ_of_forall fun x => lt_of_le_of_ne le_top (hk.ne_top x)

/-- **Section 15** of [rockafellar1970convex] (p. 131). A norm on $\mathbb{R}^n$ is a closed
function.

The backbone does not prove this in general: closedness of a norm comes from Theorem 10.1, which
is finite-dimensional. -/
theorem isNorm_closedConvex_rn (hk : IsNorm k) : ClosedConvex k :=
  (closedConvex_iff_lowerSemicontinuous hk.toIsGauge.ne_bot).2
    (isNorm_continuous_rn hk).lowerSemicontinuous

/-- Let $k$ be a norm on $\mathbb{R}^n$. Then the origin lies in the interior of
$\{x \mid k(x) \le 1\}$. This is the condition $0 \in \operatorname{int} C$ of Theorem 15.2; the
proof uses continuity of $k$ in place of Corollary 6.4.1. -/
theorem isNorm_zero_mem_interior_rn (hk : IsNorm k) :
    (0 : Rn n) ∈ interior {x : Rn n | k x ≤ 1} := by
  refine mem_interior.2 ⟨{x : Rn n | k x < 1}, fun x (hx : k x < 1) => le_of_lt hx, ?_, ?_⟩
  · exact (isNorm_continuous_rn hk).isOpen_preimage _ isOpen_Iio
  · change k 0 < 1
    rw [hk.toIsGauge.map_zero]
    exact zero_lt_one

/-- Let $k$ be a norm on $\mathbb{R}^n$. Then $\{x \mid k(x) \le 1\}$ is bounded. This is the
condition "$C$ is bounded" of Theorem 15.2; the proof uses Theorem 8.4
(`ConvexAnalysis.isBounded_iff_recessionCone_eq_zero`) and the fact that the set contains no
half-line. -/
theorem isNorm_isBounded_setOf_le_one_rn (hk : IsNorm k) :
    IsBounded {x : Rn n | k x ≤ 1} := by
  obtain ⟨hconv, h0, -, -, hray⟩ := hk.level_one
  refine (isBounded_iff_recessionCone_eq_zero hconv
    (isClosed_setOf_le_one (isNorm_closedConvex_rn hk)) ⟨0, h0⟩).2
    (Set.Subset.antisymm (fun y hy => ?_) ?_)
  · by_contra hy0
    obtain ⟨l, hl, hlm⟩ := hray y (by simpa using hy0)
    exact hlm (by simpa using hy 0 h0 l hl.le)
  · rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact fun x hx a _ => by simpa using hx

/-- **Theorem 15.2** of [rockafellar1970convex], first half. Let $C \subseteq \mathbb{R}^n$ be a
bounded convex set with $-C = C$ and $0 \in \operatorname{int} C$. Then the gauge function
$\gamma(\cdot \mid C)$ is a norm.

**Generalization.** The book states the theorem for a closed set $C$. Closedness is not needed
for this half.

The two set conditions of the book are translated into the backbone conditions
`ConvexAnalysis.AbsorbsAll` and `ConvexAnalysis.RayFree`, by Corollary 6.4.1 and Theorem 8.4 in
the easy direction. -/
theorem theorem_15_2_isNorm {C : Set (Rn n)} (hC : Convex ℝ C) (hsymm : -C = C)
    (hint : (0 : Rn n) ∈ interior C) (hbdd : IsBounded C) : IsNorm (gaugeFn C) := by
  refine isNorm_gaugeFn hC (interior_subset hint) hsymm
    (absorbsAll_of_absorbent (absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hint)))
    fun x hx => ?_
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine ⟨(|R| + 1) / ‖x‖, by positivity, fun hmem => ?_⟩
  have h := mem_closedBall_zero_iff.1 (hR hmem)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hxn.ne'] at h
  have hRa : R ≤ |R| := le_abs_self R
  linarith

/-- **Theorem 15.2** of [rockafellar1970convex], second half. Let $k$ be a norm on $\mathbb{R}^n$.
Then $C = \{x \mid k(x) \le 1\}$ is convex, closed and bounded, $-C = C$, and
$0 \in \operatorname{int} C$. -/
theorem theorem_15_2_setOf_le_one (hk : IsNorm k) :
    Convex ℝ {x : Rn n | k x ≤ 1} ∧ IsClosed {x : Rn n | k x ≤ 1} ∧
      IsBounded {x : Rn n | k x ≤ 1} ∧ -{x : Rn n | k x ≤ 1} = {x : Rn n | k x ≤ 1} ∧
      (0 : Rn n) ∈ interior {x : Rn n | k x ≤ 1} :=
  ⟨hk.toIsGauge.convex_level_one, isClosed_setOf_le_one (isNorm_closedConvex_rn hk),
    isNorm_isBounded_setOf_le_one_rn hk, hk.level_one.2.2.1, isNorm_zero_mem_interior_rn hk⟩

/-- **Theorem 15.2** of [rockafellar1970convex], the correspondence from norms to sets. Let $k$ be a
norm on $\mathbb{R}^n$. Then $\gamma(\cdot \mid \{x \mid k(x) \le 1\}) = k$. -/
theorem theorem_15_2_gaugeFn (hk : IsNorm k) : gaugeFn {x : Rn n | k x ≤ 1} = k :=
  gaugeFn_setOf_le_one hk.toIsGauge

/-- **Theorem 15.2** of [rockafellar1970convex], the correspondence from sets to gauges. Let
$C \subseteq \mathbb{R}^n$ be a closed convex set containing the origin. Then
$\{x \mid \gamma(x \mid C) \le 1\} = C$.

This is also the uniqueness statement of Section 15 (p. 128): a closed gauge determines the
closed convex set containing the origin of which it is the gauge. -/
theorem theorem_15_2_setOf_gaugeFn_le_one {C : Set (Rn n)} (hC : Convex ℝ C)
    (h0 : (0 : Rn n) ∈ C) (hcl : IsClosed C) : {x : Rn n | gaugeFn C x ≤ 1} = C :=
  setOf_gaugeFn_le_one hC h0 hcl

/-- **Theorem 15.2** of [rockafellar1970convex], last assertion. The polar $k^\circ$ of a norm $k$
on $\mathbb{R}^n$ is a norm.

In terms of the pairing, the two conditions that make $k^\circ$ finite and positive away from
the origin correspond to "$C$ is bounded" and "$0 \in \operatorname{int} C$" for
$C = \{x \mid k(x) \le 1\}$. -/
theorem theorem_15_2_polar (hk : IsNorm k) : IsNorm (polarGauge (pairing n) k) := by
  obtain ⟨hconv, h0, hsymm, -, -⟩ := hk.level_one
  have hmain := isNorm_polarGauge_gaugeFn (B := pairing n) hconv h0 hsymm ?_ ?_
  · rwa [theorem_15_2_gaugeFn hk] at hmain
  · intro y
    obtain ⟨R, hR⟩ := (isNorm_isBounded_setOf_le_one_rn hk).subset_closedBall 0
    refine ⟨|R| * ‖y‖, fun x hx => ?_⟩
    have hx' : ‖x‖ ≤ |R| := le_trans (mem_closedBall_zero_iff.1 (hR hx)) (le_abs_self R)
    calc pairing n x y = (inner ℝ x y : ℝ) := rfl
      _ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
      _ ≤ |R| * ‖y‖ := mul_le_mul_of_nonneg_right hx' (norm_nonneg y)
  · intro y hy
    obtain ⟨e, he, hsub⟩ :=
      Metric.isOpen_iff.1 isOpen_interior 0 (isNorm_zero_mem_interior_rn hk)
    have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
    have ht0 : 0 < e / (2 * ‖y‖) := by positivity
    refine ⟨(e / (2 * ‖y‖)) • y, interior_subset (hsub ?_), ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have hval : e / (2 * ‖y‖) * ‖y‖ = e / 2 := by field_simp
      rw [hval]
      linarith
    · have hval : pairing n ((e / (2 * ‖y‖)) • y) y = e / (2 * ‖y‖) * (‖y‖ * ‖y‖) := by
        rw [pairing_apply, real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      rw [hval]
      exact ne_of_gt (mul_pos ht0 (mul_pos hyn hyn))

end Norms

/-! ### The Euclidean norm, and the Schwarz inequality -/

/-- **Section 15** of [rockafellar1970convex] (p. 130). The Euclidean norm $x \mapsto |x|$ is a norm
on $\mathbb{R}^n$ in the sense of the book. -/
theorem isNorm_euclideanNorm (n : ℕ) : IsNorm (fun x : Rn n => ((‖x‖ : ℝ) : EReal)) := by
  have hph : PosHomogeneous fun x : Rn n => ((‖x‖ : ℝ) : EReal) := by
    intro a ha x
    change ((‖a • x‖ : ℝ) : EReal) = ((a : ℝ) : EReal) * ((‖x‖ : ℝ) : EReal)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, ← EReal.coe_mul]
  have hbot : ∀ x : Rn n, ((‖x‖ : ℝ) : EReal) ≠ ⊥ := fun x => EReal.coe_ne_bot _
  have hconv : ConvexFn fun x : Rn n => ((‖x‖ : ℝ) : EReal) := by
    refine (PosHomogeneous.convexFn_iff_subadditive hph hbot).2 fun x y => ?_
    rw [← EReal.coe_add]
    exact_mod_cast norm_add_le x y
  exact ⟨⟨fun x => by exact_mod_cast norm_nonneg x, hph, hconv, by simp⟩,
    fun _ => EReal.coe_ne_top _, fun x => by rw [norm_neg],
    fun x hx => by exact_mod_cast norm_pos_iff.2 hx⟩

/-- **Section 15** of [rockafellar1970convex] (p. 130). The Euclidean norm is its own polar: the
polar of $x \mapsto |x|$ is $x^* \mapsto |x^*|$. The reason is that the Euclidean norm is both
the gauge function and the support function of the Euclidean unit ball. -/
theorem polarGauge_euclideanNorm (n : ℕ) :
    polarGauge (pairing n) (fun x : Rn n => ((‖x‖ : ℝ) : EReal))
      = fun y : Rn n => ((‖y‖ : ℝ) : EReal) := by
  have hk := isNorm_euclideanNorm n
  have hset : {x : Rn n | ((‖x‖ : ℝ) : EReal) ≤ 1} = Metric.closedBall (0 : Rn n) 1 := by
    ext x
    rw [mem_closedBall_zero_iff]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  rw [polarGauge_eq_supportFn hk.toIsGauge.nonneg hk.toIsGauge.posHomogeneous
    hk.toIsGauge.map_zero, hset]
  funext y
  exact supportFn_unitBall y

/-- **Section 15** of [rockafellar1970convex], the Schwarz inequality (p. 130). For all
$x, y \in \mathbb{R}^n$, $\langle x, y \rangle \le |x| \, |y|$. This is the polar-pair
inequality for the Euclidean norm. -/
theorem schwarz_rn (x y : Rn n) : (inner ℝ x y : ℝ) ≤ ‖x‖ * ‖y‖ := by
  have hk := isNorm_euclideanNorm n
  refine pairing_le_mul_rn hk.toIsGauge (isNorm_closedConvex_rn hk) rfl ?_
  rw [polarGauge_euclideanNorm n]

/-! ### Minkowski metrics -/

/-- **Section 15** of [rockafellar1970convex], Minkowski metrics (p. 132). A function $\rho :
\mathbb{R}^n \times \mathbb{R}^n \to \mathbb{R}$ is a **Minkowski metric** if it is a metric,
that is (a) $\rho(x, y) > 0$ for $x \ne y$ and $\rho(x, x) = 0$, (b) $\rho(x, y) = \rho(y, x)$,
and (c) $\rho(x, z) \le \rho(x, y) + \rho(y, z)$, and in addition (d)
$\rho(x + z, y + z) = \rho(x, y)$, and (e) $\rho(x, (1 - \lambda) x + \lambda y) = \lambda
\rho(x, y)$ for $0 \le \lambda \le 1$. -/
structure IsMinkowskiMetric (rho : Rn n → Rn n → ℝ) : Prop where
  /-- Condition (a), first part: $\rho(x, y) > 0$ when $x \ne y$. -/
  pos : ∀ x y, x ≠ y → 0 < rho x y
  /-- Condition (a), second part: $\rho(x, x) = 0$. -/
  self : ∀ x, rho x x = 0
  /-- Condition (b): $\rho$ is symmetric, $\rho(x, y) = \rho(y, x)$. -/
  comm : ∀ x y, rho x y = rho y x
  /-- Condition (c), the triangle inequality: $\rho(x, z) \le \rho(x, y) + \rho(y, z)$. -/
  triangle : ∀ x y z, rho x z ≤ rho x y + rho y z
  /-- Condition (d), invariance under translation: $\rho(x + z, y + z) = \rho(x, y)$. -/
  vadd : ∀ x y z, rho (x + z) (y + z) = rho x y
  /-- Condition (e), linearity along line segments: $\rho(x, (1 - \lambda) x + \lambda y) = \lambda
  \rho(x, y)$ for $0 \le \lambda \le 1$. -/
  segment : ∀ x y, ∀ l ∈ Set.Icc (0 : ℝ) 1, rho x ((1 - l) • x + l • y) = l * rho x y

/-- **Section 15** of [rockafellar1970convex], Minkowski metrics from norms (p. 132). Let $k$ be a
norm on $\mathbb{R}^n$. Then $\rho(x, y) = k(x - y)$ is a Minkowski metric.

The book leaves the verification to the reader. The real-valued function $\rho$ is written
through `ConvexAnalysis.IsNorm.toSeminorm`; its subadditivity is Theorem 4.7 and its absolute
homogeneity is `ConvexAnalysis.IsNorm.apply_smul`. -/
theorem isMinkowskiMetric_of_isNorm {k : Rn n → EReal} (hk : IsNorm k) :
    IsMinkowskiMetric fun x y : Rn n => hk.toSeminorm (x - y) where
  pos x y hxy := by
    have h : (0 : EReal) < k (x - y) := hk.pos _ (sub_ne_zero_of_ne hxy)
    rw [← hk.coe_toSeminorm (x - y)] at h
    exact_mod_cast h
  self x := by simp
  comm x y := by rw [← map_neg_eq_map hk.toSeminorm (x - y), neg_sub]
  triangle x y z := by
    have h : x - z = (x - y) + (y - z) := by abel
    rw [h]
    exact map_add_le_add hk.toSeminorm _ _
  vadd x y z := by rw [add_sub_add_right_eq_sub]
  segment x y l hl := by
    have h : x - ((1 - l) • x + l • y) = l • (x - y) := by module
    rw [h, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hl.1]

/-- **Section 15** of [rockafellar1970convex], norms from Minkowski metrics (p. 132). Let $\rho$ be
a Minkowski metric on $\mathbb{R}^n$. Then $\rho(x, y) = \rho(x - y, 0)$ for all $x, y$, so
$\rho$ is determined by the function $x \mapsto \rho(x, 0)$. This gives the candidate norm
from the uniqueness part of the correspondence. -/
theorem minkowskiMetric_eq_sub {rho : Rn n → Rn n → ℝ} (h : IsMinkowskiMetric rho) (x y : Rn n) :
    rho x y = rho (x - y) 0 := by
  have hv := h.vadd (x - y) 0 y
  rwa [sub_add_cancel, zero_add] at hv

/-! ### Theorem 15.3 -/

/-- **Theorem 15.3** of [rockafellar1970convex], first assertion. A function $f$ on $\mathbb{R}^n$
is a gauge-like closed proper convex function if and only if $f = g \circ k$, where $k$ is a
closed gauge and $g$ is a non-constant non-decreasing lower semicontinuous convex function on
$[0, +\infty)$, extended by $g(+\infty) = +\infty$, such that $g(\zeta)$ is finite for some
$\zeta > 0$.

The function $g$ is a function on $\mathbb{R}$ in the class `ConvexAnalysis.MonotoneHalfLineFn`:
$+\infty$ on the negative axis, non-decreasing on $[0, +\infty)$, convex, closed, and finite at
$0$. Finiteness at $0$ follows from finiteness at some $\zeta > 0$. "Non-constant" is
$g(0) < g(t)$ for some $t > 0$. The composite $g \circ k$ is `ConvexAnalysis.monotoneComp g k`. -/
theorem theorem_15_3 {f : Rn n → EReal} :
    (ClosedProperConvexFn f ∧ IsGaugeLike f) ↔
      ∃ (g : ℝ → EReal) (k : Rn n → EReal),
        (MonotoneHalfLineFn g ∧ (∃ t : ℝ, 0 < t ∧ g 0 < g t) ∧ (∃ z : ℝ, 0 < z ∧ g z ≠ ⊤)) ∧
        (IsGauge k ∧ ClosedConvex k) ∧ f = monotoneComp g k :=
  closedProperConvexFn_and_isGaugeLike_iff (pairing n)

/-- **Theorem 15.3** of [rockafellar1970convex], second assertion. Let $k$ be a closed gauge on
$\mathbb{R}^n$, and let $g$ be a non-decreasing lower semicontinuous convex function on
$[0, +\infty)$ such that $g(\zeta)$ is finite for some $\zeta > 0$. Then
$$(g \circ k)^* = g^+ \circ k^\circ,$$
where $g^+(s) = \sup \{ts - g(t) \mid t \ge 0\}$ is the monotone conjugate of $g$.

**Generalization.** The book states the formula for $f = g \circ k$ as in the first assertion,
where $g$ is non-constant. The formula does not need $g$ to be non-constant.

The monotone conjugate is `ConvexAnalysis.monotoneConj g`, taken to be $+\infty$ on the negative
axis. -/
theorem theorem_15_3_conj {g : ℝ → EReal} {k : Rn n → EReal} (hk : IsGauge k) (hkc : ClosedConvex k)
    (hg : MonotoneHalfLineFn g) (hfin : ∃ z : ℝ, 0 < z ∧ g z ≠ ⊤) :
    convexConj (pairing n) (monotoneComp g k)
      = monotoneComp (monotoneConj g) (polarGauge (pairing n) k) :=
  convexConj_monotoneComp hk hkc hg hfin

/-- **Theorem 15.3** of [rockafellar1970convex], second assertion. Let $k$ be a closed gauge on
$\mathbb{R}^n$, and let $g$ be a non-constant non-decreasing lower semicontinuous convex
function on $[0, +\infty)$ such that $g(\zeta)$ is finite for some $\zeta > 0$. Then
$(g \circ k)^*$ is gauge-like. In the words of the book: if $f$ is of this type, then $f^*$ is
gauge-like too. -/
theorem theorem_15_3_isGaugeLike_conj {g : ℝ → EReal} {k : Rn n → EReal} (hk : IsGauge k)
    (hkc : ClosedConvex k) (hg : MonotoneHalfLineFn g) (hfin : ∃ z : ℝ, 0 < z ∧ g z ≠ ⊤)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) :
    IsGaugeLike (convexConj (pairing n) (monotoneComp g k)) :=
  isGaugeLike_convexConj_monotoneComp (pairing n) hk hkc hg hfin hne

/-! ### Corollary 15.3.1 -/

/-- **Corollary 15.3.1** of [rockafellar1970convex], first assertion. Let $1 < p < \infty$, and let
$f$ be a closed proper convex function on $\mathbb{R}^n$. Then $f$ is positively homogeneous of
degree $p$, that is $f(\lambda x) = \lambda^p f(x)$ for all $\lambda > 0$, if and only if
$f = (1/p) k^p$ for some closed gauge $k$.

The function $(1/p) k^p$ is `ConvexAnalysis.monotoneComp (ConvexAnalysis.powHalfLine p) k`: it
is $k(x)^p / p$ where $k(x)$ is finite and $+\infty$ where $k(x) = +\infty$. -/
theorem corollary_15_3_1 {p : ℝ} {f : Rn n → EReal} (hp : 1 < p) (hf : ClosedProperConvexFn f) :
    PosHomogeneousDeg p f ↔
      ∃ k : Rn n → EReal, IsGauge k ∧ ClosedConvex k ∧ f = monotoneComp (powHalfLine p) k :=
  posHomogeneousDeg_iff_exists_isGauge hp hf.convex hf.closed hf.proper

/-- **Corollary 15.3.1** of [rockafellar1970convex], second assertion. Let $p, q > 0$ with
$1/p + 1/q = 1$, and let $k$ be a closed gauge on $\mathbb{R}^n$. Then
$$\left[\tfrac{1}{p} k^p\right]^* = \tfrac{1}{q} (k^\circ)^q.$$

The hypothesis on $p$ and $q$ is `Real.HolderConjugate p q`; it implies $p, q > 1$. -/
theorem corollary_15_3_1_conj {p q : ℝ} {k : Rn n → EReal} (hpq : p.HolderConjugate q)
    (hk : IsGauge k) (hkc : ClosedConvex k) :
    convexConj (pairing n) (monotoneComp (powHalfLine p) k)
      = monotoneComp (powHalfLine q) (polarGauge (pairing n) k) :=
  convexConj_monotoneComp_powHalfLine hpq hk hkc

/-! ### Corollary 15.3.2 -/

section Cor1532

variable {p q : ℝ} {f : Rn n → EReal}

/-- **Corollary 15.3.2** of [rockafellar1970convex], first assertion. Let $1 < p$, and let $f$ be a
closed proper convex function on $\mathbb{R}^n$ that is positively homogeneous of degree $p$.
Then $(pf)^{1/p}$ is a closed gauge.

The function $(pf)^{1/p}$ is `ConvexAnalysis.degGauge p f`: it is $(p f(x))^{1/p}$ where $f(x)$
is finite and $+\infty$ where $f(x) = +\infty$. -/
theorem corollary_15_3_2_isGauge (hp : 1 < p) (hf : ClosedProperConvexFn f)
    (hph : PosHomogeneousDeg p f) : IsGauge (degGauge p f) ∧ ClosedConvex (degGauge p f) := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have h0 : f 0 = 0 :=
    PosHomogeneousDeg.map_zero_eq_zero hp0 hf.closed hf.proper hph
  have hnn : ∀ z, 0 ≤ f z :=
    PosHomogeneousDeg.nonneg hp hf.convex hf.proper.ne_bot hph h0
  exact ⟨isGauge_degGauge hp0 hf.convex hnn hph h0,
    closedConvex_degGauge hp0 hf.convex hf.closed hnn hph h0⟩

/-- **Corollary 15.3.2** of [rockafellar1970convex]. Let $p, q > 0$ with $1/p + 1/q = 1$, and let
$f$ be a closed proper convex function on $\mathbb{R}^n$ that is positively homogeneous of
degree $p$. Then the polar of the closed gauge $(pf)^{1/p}$ is $(qf^*)^{1/q}$. -/
theorem corollary_15_3_2 (hpq : p.HolderConjugate q) (hf : ClosedProperConvexFn f)
    (hph : PosHomogeneousDeg p f) :
    polarGauge (pairing n) (degGauge p f) = degGauge q (convexConj (pairing n) f) :=
  polarGauge_degGauge hpq hf.convex hf.closed hf.proper hph

/-- **Corollary 15.3.2** of [rockafellar1970convex], the inequality. Let $p, q > 0$ with
$1/p + 1/q = 1$, and let $f$ be a closed proper convex function on $\mathbb{R}^n$ that is
positively homogeneous of degree $p$. If $f(x) = a$ and $f^*(x^*) = b$ are finite, then
$$\langle x, x^* \rangle \le (p a)^{1/p} (q b)^{1/q}.$$
This is the inequality on $\operatorname{dom} f \times \operatorname{dom} f^*$ of the book. -/
theorem corollary_15_3_2_inequality (hpq : p.HolderConjugate q) (hf : ClosedProperConvexFn f)
    (hph : PosHomogeneousDeg p f) {x y : Rn n} {a b : ℝ} (hx : f x = (a : EReal))
    (hy : convexConj (pairing n) f y = (b : EReal)) :
    (inner ℝ x y : ℝ) ≤ (p * a) ^ p⁻¹ * (q * b) ^ q⁻¹ :=
  pairing_le_rpow_mul_rpow hpq hf.convex hf.closed hf.proper hph hx hy

/-- **Corollary 15.3.2** of [rockafellar1970convex], last assertion. Let $p, q > 0$ with
$1/p + 1/q = 1$, and let $f$ be a closed proper convex function on $\mathbb{R}^n$ that is
positively homogeneous of degree $p$. Then the closed convex sets $\{x \mid f(x) \le 1/p\}$ and
$\{x^* \mid f^*(x^*) \le 1/q\}$ are polar to each other:
$$\{x \mid f(x) \le 1/p\}^\circ = \{x^* \mid f^*(x^*) \le 1/q\}.$$
-/
theorem corollary_15_3_2_polarSet (hpq : p.HolderConjugate q) (hf : ClosedProperConvexFn f)
    (hph : PosHomogeneousDeg p f) :
    polarSet (pairing n) {x : Rn n | f x ≤ ((p⁻¹ : ℝ) : EReal)}
      = {y : Rn n | convexConj (pairing n) f y ≤ ((q⁻¹ : ℝ) : EReal)} :=
  polarSet_setOf_le_inv hpq hf.convex hf.closed hf.proper hph

end Cor1532

/-! ### Theorem 15.4 -/

section Thm154

variable {f : Rn n → EReal}

/-- **Theorem 15.4** of [rockafellar1970convex], non-negativity. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ satisfy $f(0) = 0$. Then $f^\circ(x^*) \ge 0$ for
every $x^*$.

**Generalization.** The book states the theorem for a non-negative convex function $f$ with
$f(0) = 0$. Only $f(0) = 0$ is needed here. -/
theorem theorem_15_4_nonneg (h0 : f 0 = 0) (y : Rn n) : 0 ≤ polarFn (pairing n) f y :=
  polarFn_nonneg h0.le y

/-- **Theorem 15.4** of [rockafellar1970convex], value at the origin. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ satisfy $f(0) = 0$. Then $f^\circ(0) = 0$.

**Generalization.** The book states the theorem for a non-negative convex function $f$ with
$f(0) = 0$. Only $f(0) = 0$ is needed here. -/
theorem theorem_15_4_map_zero (h0 : f 0 = 0) : polarFn (pairing n) f 0 = 0 :=
  polarFn_zero (pairing n) f h0.le

/-- **Theorem 15.4** of [rockafellar1970convex], convexity. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ be non-negative. Then $f^\circ$ is convex.

**Generalization.** The book states the theorem for a non-negative convex function $f$ with
$f(0) = 0$. Only $f \ge 0$ is needed here. -/
theorem theorem_15_4_convexFn (hnn : ∀ x, 0 ≤ f x) : ConvexFn (polarFn (pairing n) f) :=
  convexFn_polarFn hnn

/-- **Theorem 15.4** of [rockafellar1970convex], closedness. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ be non-negative with $f(0) = 0$. Then $f^\circ$ is
closed.

**Generalization.** The book states the theorem for a non-negative convex function $f$ with
$f(0) = 0$. Convexity of $f$ is not needed. -/
theorem theorem_15_4_closedFn (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 = 0) :
    ClosedConvex (polarFn (pairing n) f) :=
  closedConvex_polarFn hnn h0.le

/-- **Theorem 15.4** of [rockafellar1970convex], second assertion. Let $f$ be a non-negative convex
function on $\mathbb{R}^n$ with $f(0) = 0$. Then $f^{\circ\circ} = \operatorname{cl} f$.

The function $f$ is not assumed to be closed. This statement makes $f \mapsto f^\circ$ an
involution on the closed members of the class. -/
theorem theorem_15_4_polar_polar (hconv : ConvexFn f) (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 = 0) :
    polarFn (pairing n) (polarFn (pairing n) f) = convexCl f := by
  have h := polarFn_polarFn (B := pairing n) hconv hnn h0.le
  rwa [flip_pairing] at h

end Thm154

/-- **Corollary 15.4.1** of [rockafellar1970convex]. The map $f \mapsto f^\circ$ induces a symmetric
one-to-one correspondence in the class of all non-negative closed convex functions on
$\mathbb{R}^n$ that vanish at the origin.

The class is `ConvexAnalysis.IsPolarFn`, and the correspondence is `ConvexAnalysis.polarFnEquiv`
for `Rockafellar.pairing n`. -/
noncomputable def corollary_15_4_1 (n : ℕ) :
    {f : Rn n → EReal // IsPolarFn f} ≃ {g : Rn n → EReal // IsPolarFn g} :=
  polarFnEquiv (pairing n)

/-! ### Theorem 15.5 -/

section Thm155

variable {f : Rn n → EReal}

/-- **Theorem 15.5** of [rockafellar1970convex], first assertion. Let $f$ be a non-negative closed
convex function on $\mathbb{R}^n$ with $f(0) = 0$, and let $g$ be the obverse of $f$. Then $g$
is also a non-negative closed convex function with $g(0) = 0$. -/
theorem theorem_15_5_isPolarFn (h : IsPolarFn f) : IsPolarFn (obverse f) :=
  isPolarFn_obverse h

/-- **Theorem 15.5** of [rockafellar1970convex], first assertion. Let $f$ be a non-negative closed
convex function on $\mathbb{R}^n$ with $f(0) = 0$. Then $f$ is the obverse of its obverse. -/
theorem theorem_15_5_obverse_obverse (h : IsPolarFn f) : obverse (obverse f) = f :=
  obverse_obverse h

/-- **Theorem 15.5** of [rockafellar1970convex]. Let $f$ be a non-negative closed convex function on
$\mathbb{R}^n$ with $f(0) = 0$, and let $g$ be the obverse of $f$. Then $f^\circ = g^*$. -/
theorem theorem_15_5_polarFn_eq_conj_obverse (h : IsPolarFn f) :
    convexConj (pairing n) (obverse f) = polarFn (pairing n) f :=
  convexConj_obverse h

/-- **Theorem 15.5** of [rockafellar1970convex]. Let $f$ be a non-negative closed convex function on
$\mathbb{R}^n$ with $f(0) = 0$, and let $g$ be the obverse of $f$. Then $f^* = g^\circ$. -/
theorem theorem_15_5_conj_eq_polarFn_obverse (h : IsPolarFn f) :
    polarFn (pairing n) (obverse f) = convexConj (pairing n) f :=
  polarFn_obverse h

/-- **Theorem 15.5** of [rockafellar1970convex], last assertion. Let $f$ be a non-negative closed
convex function on $\mathbb{R}^n$ with $f(0) = 0$. Then $f^*$ is the obverse of $f^\circ$. -/
theorem theorem_15_5_conj_eq_obverse_polarFn (h : IsPolarFn f) :
    convexConj (pairing n) f = obverse (polarFn (pairing n) f) :=
  convexConj_eq_obverse_polarFn h

/-- **Theorem 15.5** of [rockafellar1970convex], last assertion. Let $f$ be a non-negative closed
convex function on $\mathbb{R}^n$ with $f(0) = 0$. Then $f^\circ$ is the obverse of $f^*$. -/
theorem theorem_15_5_polarFn_eq_obverse_conj (h : IsPolarFn f) :
    polarFn (pairing n) f = obverse (convexConj (pairing n) f) :=
  polarFn_eq_obverse_convexConj h

/-- **Corollary 15.5.1** of [rockafellar1970convex]. Let $f$ be a non-negative closed convex
function on $\mathbb{R}^n$ with $f(0) = 0$. Then $f^{*\circ} = f^{\circ *}$. -/
theorem corollary_15_5_1 (h : IsPolarFn f) :
    polarFn (pairing n) (convexConj (pairing n) f)
        = convexConj (pairing n) (polarFn (pairing n) f) := by
  have hp := polarFn_convexConj_eq_convexConj_polarFn (B := pairing n) h
  rwa [flip_pairing] at hp

/-! ### The level sets at the end of Section 15 -/

/-- **Section 15** of [rockafellar1970convex], level sets of the obverse (p. 139). Let $f$ be a
non-negative closed convex function on $\mathbb{R}^n$ with $f(0) = 0$, let $g$ be the obverse of
$f$, and let $\alpha > 0$. Then
$$\{x \mid g(x) \le \alpha\} = \alpha \{x \mid f(x) \le \alpha^{-1}\}.$$
-/
theorem setOf_obverse_le_rn (h : IsPolarFn f) {alpha : ℝ} (ha : 0 < alpha) :
    {x : Rn n | obverse f x ≤ (alpha : EReal)}
      = alpha • {x : Rn n | f x ≤ ((alpha⁻¹ : ℝ) : EReal)} :=
  setOf_obverse_le h ha

/-- **Section 15** of [rockafellar1970convex], the last display of the section. Let $f$ be a
non-negative closed convex function on $\mathbb{R}^n$ with $f(0) = 0$, and let $\alpha > 0$.
Then
$$\{x^* \mid f^\circ(x^*) \le \alpha^{-1}\} = \alpha^{-1} \{x^* \mid f^*(x^*) \le \alpha\}.$$
This set is the middle set of the inclusions of Theorem 14.7. -/
theorem setOf_polarFn_le_rn (h : IsPolarFn f) {alpha : ℝ} (ha : 0 < alpha) :
    {y : Rn n | polarFn (pairing n) f y ≤ ((alpha⁻¹ : ℝ) : EReal)}
      = alpha⁻¹ • {y : Rn n | convexConj (pairing n) f y ≤ (alpha : EReal)} :=
  setOf_polarFn_le h ha

end Thm155

end Rockafellar
