/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.Monotone
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Gradient
import Numlib.Analysis.Convex.Subdifferential.OneDim

/-!
# Points of differentiability of a convex function

This module turns the continuity theory of one-sided derivatives into an existence theory for
derivatives. Let $f : \mathbb{R} \to [-\infty, +\infty]$ be proper and convex, with right derivative
$f'_+$ and left derivative $f'_-$. Then $f$ is differentiable at every point of
$\operatorname{int}(\operatorname{dom} f)$ outside a countable set, and the points of
differentiability are dense in $\operatorname{int}(\operatorname{dom} f)$. If $f$ is also closed,
the derivative is continuous where it exists. In a real normed space $E$ and a fixed direction $y$,
the two-sided directional derivative, $f'(x; y) = -f'(x; -y)$, exists at an interior point $x$ of
$\operatorname{dom} f$ exactly where $x \mapsto f'(x; y)$ is continuous, and these points are dense
in $\operatorname{int}(\operatorname{dom} f)$. The presentation follows [rockafellar1970convex],
§25.

## Main results

* `ConvexAnalysis.continuousAt_rightDeriv_iff`, `ConvexAnalysis.continuousAt_leftDeriv_iff`: for a
  closed proper convex $f$ on $\mathbb{R}$, $f'_+$ (or $f'_-$) is continuous at $x$ exactly when
  $f'_-(x) = f'_+(x)$.
* `ConvexAnalysis.countable_leftDeriv_ne_rightDeriv`: the set where $f'_- \ne f'_+$ is countable.
* `ConvexAnalysis.differentiableAtFn_iff_leftDeriv_eq_rightDeriv`: on $\mathbb{R}$, $f$ is
  differentiable at an interior point of $\operatorname{dom} f$ exactly when the two one-sided
  derivatives agree there.
* `ConvexAnalysis.countable_not_differentiableAtFn`,
  `ConvexAnalysis.continuousAt_rightDeriv_of_differentiableAtFn`,
  `ConvexAnalysis.subset_closure_differentiableAtFn`: the set of points of nondifferentiability in
  $\operatorname{int}(\operatorname{dom} f)$ is countable, the derivative is continuous where it
  exists (for closed $f$), and the points of differentiability are dense. This is Theorem 25.3 of
  [rockafellar1970convex].
* `ConvexAnalysis.continuousAt_dirDeriv_iff`, `ConvexAnalysis.subset_closure_twoSided_dirDeriv`: the
  same in a fixed direction $y$. This is Theorem 25.4 of [rockafellar1970convex].

## Implementation notes

* `ConvexAnalysis.rightDeriv f` is defined on all of $\mathbb{R}$, not only on the set $D$ where the
  derivative exists. So the continuity statements here are ordinary continuity at a point on
  $\mathbb{R}$ (`ContinuousAt`), which is stronger than continuity relative to $D$ in
  [rockafellar1970convex]. Monotonicity of $f'_+$ also holds on all of $\mathbb{R}$.
* Three of the classical hypotheses are not needed. The countability and density statements need no
  closedness of $f$, because they use only the easy half of the continuity criterion; closedness
  enters only in the converse, through the formulas for the one-sided limits of $f'_+$. The
  statements in a fixed direction need no $y \ne 0$, since both sides hold at $y = 0$. The density
  statement in a fixed direction is proved by restriction to a line, not with Lebesgue measure, so
  it needs no finite dimension.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### A continuity criterion for the right derivative -/

section Line

variable {f : ℝ → EReal} {x : ℝ}

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be proper and convex. If $f'_+$ is continuous at
$x$, then $f'_-(x) = f'_+(x)$.

By monotonicity, $f'_+(z)$ tends to $\sup_{z < x} f'_+(z)$ as $z \uparrow x$. Continuity
identifies this supremum with $f'_+(x)$, and every $f'_+(z)$ with $z < x$ is at most $f'_-(x)$.
Unlike the converse, this needs no closedness. -/
theorem leftDeriv_eq_rightDeriv_of_continuousAt (hf : ConvexFn f) (hp : ProperConvex f)
    (hc : ContinuousAt (rightDeriv f) x) : leftDeriv f x = rightDeriv f x := by
  have hsup : ⨆ z ∈ Iio x, rightDeriv f z = rightDeriv f x :=
    tendsto_nhds_unique
      (by simpa only [sSup_image] using (monotone_rightDeriv hf hp).tendsto_nhdsLT x)
      (Filter.Tendsto.mono_left hc nhdsWithin_le_nhds)
  refine le_antisymm (leftDeriv_le_rightDeriv hf hp x) ?_
  rw [← hsup]
  exact iSup₂_le fun z hz => rightDeriv_le_leftDeriv hp hz

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be closed, proper and convex, and let
$x \in \mathbb{R}$. Then the nondecreasing function $f'_+$ is continuous at $x$ if and only if
$$f'_-(x) = f'_+(x).$$

The right and left derivatives are `ConvexAnalysis.rightDeriv` and `ConvexAnalysis.leftDeriv`,
with values in $[-\infty, +\infty]$; continuity is for the order topology of `EReal`. -/
theorem continuousAt_rightDeriv_iff (hf : ClosedProperConvexFn f) (x : ℝ) :
    ContinuousAt (rightDeriv f) x ↔ leftDeriv f x = rightDeriv f x := by
  refine ⟨leftDeriv_eq_rightDeriv_of_continuousAt hf.convex hf.proper, fun h => ?_⟩
  have h1 : Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (rightDeriv f x)) := by
    rw [← h]
    exact tendsto_rightDeriv_nhdsWithin_Iio hf x
  have h2 : Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
    tendsto_rightDeriv_nhdsWithin_Ioi hf x
  have h3 : Tendsto (rightDeriv f) (pure x) (𝓝 (rightDeriv f x)) := tendsto_pure_nhds _ x
  have hsup : Tendsto (rightDeriv f) (𝓝[≠] x ⊔ pure x) (𝓝 (rightDeriv f x)) := by
    rw [← nhdsLT_sup_nhdsGT]
    exact (h1.sup h2).sup h3
  rwa [nhdsNE_sup_pure] at hsup

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be closed, proper and convex, and let
$x \in \mathbb{R}$. Then $f'_-$ is continuous at $x$ if and only if
$$f'_-(x) = f'_+(x).$$

This is the reflection of `ConvexAnalysis.continuousAt_rightDeriv_iff`. -/
theorem continuousAt_leftDeriv_iff (hf : ClosedProperConvexFn f) (x : ℝ) :
    ContinuousAt (leftDeriv f) x ↔ leftDeriv f x = rightDeriv f x := by
  have key : ContinuousAt (leftDeriv f) x ↔ ContinuousAt (rightDeriv fun t => f (-t)) (-x) := by
    rw [show leftDeriv f = fun z => -rightDeriv (fun t => f (-t)) (-z) from
      funext (leftDeriv_eq_neg_rightDeriv_comp_neg f)]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa [Function.comp_def] using ((continuous_neg (G := EReal)).continuousAt.comp
        h).comp_of_eq continuous_neg.continuousAt (neg_neg x)
    · exact (continuous_neg (G := EReal)).continuousAt.comp (h.comp continuous_neg.continuousAt)
  rw [key, continuousAt_rightDeriv_iff hf.comp_neg, leftDeriv_eq_neg_rightDeriv_comp_neg f,
    rightDeriv_eq_neg_leftDeriv_comp_neg f, neg_inj, eq_comm]

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be proper and convex. Then the set
$$\{x \in \mathbb{R} \mid f'_-(x) \ne f'_+(x)\}$$
is countable.

The function $f'_+$ is nondecreasing with values in the second-countable order topology of
`EReal`, so its set of discontinuities is countable, and that set contains the set where
$f'_- \ne f'_+$ by `ConvexAnalysis.leftDeriv_eq_rightDeriv_of_continuousAt`. -/
theorem countable_leftDeriv_ne_rightDeriv (hf : ConvexFn f) (hp : ProperConvex f) :
    {x : ℝ | leftDeriv f x ≠ rightDeriv f x}.Countable := by
  refine Set.Countable.mono ?_ (monotone_rightDeriv hf hp).countable_not_continuousAt
  intro z hz
  have hz' : leftDeriv f z ≠ rightDeriv f z := hz
  exact fun hcon => hz' (leftDeriv_eq_rightDeriv_of_continuousAt hf hp hcon)

/-! ### The two-sided derivative on the line -/

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be proper and convex, let
$x \in \operatorname{int}(\operatorname{dom} f)$, and let $f'_-(x) = f'_+(x)$. Then
$f'(x; v) = f'_+(x) \, v$ for every $v \in \mathbb{R}$, where $f'_+(x)$ is finite.

By positive homogeneity, $f'(x; v)$ reduces to the directions $\pm 1$, where the values are
$f'_+(x)$ and $-f'_-(x)$. -/
theorem dirDeriv_eq_of_leftDeriv_eq_rightDeriv (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) (h : leftDeriv f x = rightDeriv f x) (v : ℝ) :
    dirDeriv f x v = (((rightDeriv f x).toReal * v : ℝ) : EReal) := by
  obtain ⟨hbot, htop⟩ := rightDeriv_finite_of_mem_interior_convexDom hf hp hx
  set c : ℝ := (rightDeriv f x).toReal with hcdef
  have hrc : rightDeriv f x = (c : EReal) := (EReal.coe_toReal htop hbot).symm
  have hfx : f x < ⊤ := mem_convexDom.1 (interior_subset hx)
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  have h1 : dirDeriv f x 1 = (c : EReal) := by rw [← rightDeriv_eq_dirDeriv hfx hfb, hrc]
  have hm1 : dirDeriv f x (-1) = ((-c : ℝ) : EReal) := by
    have hL := leftDeriv_eq_neg_dirDeriv hfx hfb
    rw [h, hrc] at hL
    rw [EReal.coe_neg, hL, neg_neg]
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · have hvv : v = (-v) • (-1 : ℝ) := by rw [smul_eq_mul]; ring
    rw [hvv, posHomogeneous_dirDeriv f x (-v) (by linarith) (-1), hm1, ← EReal.coe_mul]
    congr 1
    ring
  · rw [dirDeriv_zero hfx.ne hfb]
    simp
  · have hvv : v = v • (1 : ℝ) := by rw [smul_eq_mul]; ring
    rw [hvv, posHomogeneous_dirDeriv f x v hv 1, h1, ← EReal.coe_mul]
    congr 1
    ring

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be proper and convex, and let
$x \in \operatorname{int}(\operatorname{dom} f)$. Then $f$ is differentiable at $x$ if and only
if
$$f'_-(x) = f'_+(x).$$

Differentiability is `ConvexAnalysis.DifferentiableAtFn`: near $x$, $f$ agrees with a real
function that is differentiable at $x$. -/
theorem differentiableAtFn_iff_leftDeriv_eq_rightDeriv (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) :
    DifferentiableAtFn f x ↔ leftDeriv f x = rightDeriv f x := by
  have hfx : f x < ⊤ := mem_convexDom.1 (interior_subset hx)
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  constructor
  · rintro ⟨y₀, hy₀⟩
    have hd := hy₀.dirDeriv_eq hf
    rw [rightDeriv_eq_dirDeriv hfx hfb, leftDeriv_eq_neg_dirDeriv hfx hfb, hd 1, hd (-1),
      ← EReal.coe_neg]
    congr 1
    have hneg : y₀ (-1 : ℝ) = -y₀ (1 : ℝ) := by rw [← map_neg]
    rw [hneg, neg_neg]
  · intro h
    exact ⟨(rightDeriv f x).toReal • ContinuousLinearMap.id ℝ ℝ,
      hasGradientAtFn_of_dirDeriv_eq hf hfx.ne hfb fun v => by
        rw [dirDeriv_eq_of_leftDeriv_eq_rightDeriv hf hp hx h v]
        norm_num⟩

/-! ### Differentiability outside a countable set -/

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be proper and convex. Then $f$ is differentiable at
all points of $\operatorname{int}(\operatorname{dom} f)$ except countably many:
$$\{x \in \operatorname{int}(\operatorname{dom} f) \mid f \text{ is not differentiable at } x\}
  \text{ is countable.}$$

This is the first assertion of Theorem 25.3 of [rockafellar1970convex]. No closedness is needed,
so the usual first step, the extension of $f$ to a closed proper convex function on
$\mathbb{R}$, is not made. -/
theorem countable_not_differentiableAtFn (hf : ConvexFn f) (hp : ProperConvex f) :
    {x ∈ interior (convexDom f) | ¬DifferentiableAtFn f x}.Countable := by
  refine Set.Countable.mono ?_ (countable_leftDeriv_ne_rightDeriv hf hp)
  rintro z ⟨hz, hzd⟩
  exact fun hcon => hzd ((differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf hp hz).2 hcon)

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be closed, proper and convex, let
$x \in \operatorname{int}(\operatorname{dom} f)$, and let $f$ be differentiable at $x$. Then
$f'_+$ is continuous at $x$.

This is the second assertion of Theorem 25.3 of [rockafellar1970convex]: the derivative is
continuous where it exists. The statement is stronger than continuity relative to the set of
points of differentiability, since `ConvexAnalysis.rightDeriv f` is continuous at $x$ as a
function on all of $\mathbb{R}$. -/
theorem continuousAt_rightDeriv_of_differentiableAtFn (hf : ClosedProperConvexFn f)
    (hx : x ∈ interior (convexDom f)) (hd : DifferentiableAtFn f x) :
    ContinuousAt (rightDeriv f) x :=
  (continuousAt_rightDeriv_iff hf x).2
    ((differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf.convex hf.proper hx).1 hd)

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be closed, proper and convex, let
$x \in \operatorname{int}(\operatorname{dom} f)$, and let $f$ be differentiable at $x$. Then
$f'_-$ is continuous at $x$.

This is the counterpart of `ConvexAnalysis.continuousAt_rightDeriv_of_differentiableAtFn` for
the left derivative. -/
theorem continuousAt_leftDeriv_of_differentiableAtFn (hf : ClosedProperConvexFn f)
    (hx : x ∈ interior (convexDom f)) (hd : DifferentiableAtFn f x) :
    ContinuousAt (leftDeriv f) x :=
  (continuousAt_leftDeriv_iff hf x).2
    ((differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf.convex hf.proper hx).1 hd)

/-- Let $f : \mathbb{R} \to [-\infty, +\infty]$ be proper and convex. Then the points of
differentiability of $f$ are dense in the interior of its effective domain:
$$\operatorname{int}(\operatorname{dom} f) \subseteq \operatorname{cl} \{z \in \mathbb{R} \mid f
  \text{ is differentiable at } z\}.$$

This is the third assertion of Theorem 25.3 of [rockafellar1970convex]. A countable subset of
$\mathbb{R}$ has a dense complement. -/
theorem subset_closure_differentiableAtFn (hf : ConvexFn f) (hp : ProperConvex f) :
    interior (convexDom f) ⊆ closure {z : ℝ | DifferentiableAtFn f z} := by
  intro z hz
  rw [mem_closure_iff]
  intro U hU hzU
  obtain ⟨w, hw, hwU⟩ :=
    (Set.Countable.dense_compl ℝ (countable_leftDeriv_ne_rightDeriv hf hp)).exists_mem_open
      (hU.inter isOpen_interior) ⟨z, hzU, hz⟩
  exact ⟨w, hwU.1,
    (differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf hp hwU.2).2 (not_not.1 hw)⟩

end Line

/-! ### Restriction to a line -/

section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x y : E}

/-- Let $f : E \to [-\infty, +\infty]$ be convex. Then for all $x, y \in E$ the restriction
$t \mapsto f(x + t y)$ is a convex function on $\mathbb{R}$. -/
theorem convexFn_lineRestrict (hf : ConvexFn f) (x y : E) :
    ConvexFn fun t : ℝ => f (x + t • y) := by
  refine convexFn_of_epi_combo fun t₁ t₂ μ ν h₁ h₂ a b ha hb hab => ?_
  have hpt : x + (a • t₁ + b • t₂) • y = a • (x + t₁ • y) + b • (x + t₂ • y) := by
    rw [smul_eq_mul, smul_eq_mul]
    match_scalars <;> linarith [hab]
  rw [hpt]
  exact hf.epi_combo h₁ h₂ ha hb hab

/-- Let $f$ be proper, let $x \in \operatorname{dom} f$, and let $y \in E$. Then the restriction
$t \mapsto f(x + t y)$ is proper. -/
theorem properConvex_lineRestrict (hp : ProperConvex f) (hx : x ∈ convexDom f) (y : E) :
    ProperConvex fun t : ℝ => f (x + t • y) :=
  ⟨⟨0, by simpa using hx⟩, fun t => hp.ne_bot _⟩

/-- Let $f : E \to [-\infty, +\infty]$, let $x, y \in E$, and let $g(s) = f(x + s y)$. Then for all
$t, v \in \mathbb{R}$
$$g'(t; v) = f'(x + t y; v y).$$
This lets the theory of one variable be applied in a fixed direction. No hypothesis is needed. -/
theorem dirDeriv_lineRestrict (f : E → EReal) (x y : E) (t v : ℝ) :
    dirDeriv (fun s : ℝ => f (x + s • y)) t v = dirDeriv f (x + t • y) (v • y) := by
  have harg : ∀ a : ℝ, x + (t + a • v) • y = x + t • y + a • (v • y) := by
    intro a
    rw [smul_eq_mul, smul_smul]
    module
  simp only [dirDeriv_apply, harg]

end Restrict

/-! ### The two-sided derivative in a fixed direction -/

section TwoSided

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x : E}

/-- Let $E$ be finite-dimensional, let $f$ be proper and convex, let
$x \in \operatorname{int}(\operatorname{dom} f)$, and let $y \in E$. Then $z \mapsto f'(z; y)$
is upper semicontinuous at $x$.

This is `ConvexAnalysis.upperSemicontinuousAt_dirDeriv`, the joint upper semicontinuity of
$(z, v) \mapsto f'(z; v)$, restricted to the first variable. -/
theorem upperSemicontinuousAt_dirDeriv_fst [FiniteDimensional ℝ E] (hf : ConvexFn f)
    (hp : ProperConvex f) (hx : x ∈ interior (convexDom f)) (y : E) :
    UpperSemicontinuousAt (fun z => dirDeriv f z y) x := by
  intro c hc
  have hcont : Continuous fun z : E => (z, y) := by fun_prop
  exact (hcont.tendsto x).eventually (upperSemicontinuousAt_dirDeriv hf hp hx y c hc)

/-- Let $f$ be proper, let $f(x) < +\infty$, let $y \in E$, and let $\lambda > 0$. Then
$$f'(x - \lambda y; y) \le -f'(x; -y).$$

The proof passes through $(f(x) - f(x - \lambda y)) / \lambda$. This quotient bounds the left
side, because it is the term with step $\lambda$ of the infimum that defines
$f'(x - \lambda y; y)$. It is bounded by the right side, because its negative is the term with
step $\lambda$ of the infimum that defines $f'(x; -y)$. No convexity and no interiority are
used. -/
theorem dirDeriv_sub_smul_le (hp : ProperConvex f) (hfx : f x < ⊤) (y : E) {l : ℝ} (hl : 0 < l) :
    dirDeriv f (x - l • y) y ≤ -dirDeriv f x (-y) := by
  rcases eq_or_lt_of_le (le_top : f (x - l • y) ≤ ⊤) with hu | hu
  · rw [dirDeriv_eq_bot_of_eq_top hu]
    exact bot_le
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hfx
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot (x - l • y)) hu
  have h1 : dirDeriv f (x - l • y) y ≤ (((r - s) / l : ℝ) : EReal) := by
    have hq := dirDeriv_le f (x - l • y) y hl
    rwa [show x - l • y + l • y = x from by abel, hr, hs, ← EReal.coe_sub,
      ← EReal.coe_div] at hq
  have h2 : dirDeriv f x (-y) ≤ (((s - r) / l : ℝ) : EReal) := by
    have hq := dirDeriv_le f x (-y) hl
    rwa [show x + l • (-y) = x - l • y from by module, hr, hs, ← EReal.coe_sub,
      ← EReal.coe_div] at hq
  refine h1.trans ?_
  have h3 := EReal.neg_le_neg_iff.2 h2
  rwa [← EReal.coe_neg, show -((s - r) / l) = (r - s) / l from by ring] at h3

/-- Let $E$ be a finite-dimensional real normed space, let $f : E \to [-\infty, +\infty]$ be proper
and convex, let $x \in \operatorname{int}(\operatorname{dom} f)$, and let $y \in E$. Then
$z \mapsto f'(z; y)$ is continuous at $x$ if and only if the two-sided directional derivative in
the direction $y$ exists at $x$:
$$f'(x; y) = -f'(x; -y).$$

This is the first assertion of Theorem 25.4 of [rockafellar1970convex]. The hypothesis $y \ne 0$
is not needed, because both sides hold at $y = 0$. -/
theorem continuousAt_dirDeriv_iff [FiniteDimensional ℝ E] (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) (y : E) :
    ContinuousAt (fun z => dirDeriv f z y) x ↔ dirDeriv f x y = -dirDeriv f x (-y) := by
  have hfx : f x < ⊤ := mem_convexDom.1 (interior_subset hx)
  constructor
  · intro hc
    refine le_antisymm ?_ (neg_dirDeriv_neg_le hf hfx.ne (hp.ne_bot x) y)
    have hray : Tendsto (fun l : ℝ => x - l • y) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have hcont : Continuous fun l : ℝ => x - l • y := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hc' : Tendsto (fun z : E => dirDeriv f z y) (𝓝 x) (𝓝 (dirDeriv f x y)) := hc
    have hlim : Tendsto (fun l : ℝ => dirDeriv f (x - l • y) y) (𝓝[>] (0 : ℝ))
        (𝓝 (dirDeriv f x y)) := hc'.comp hray
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact dirDeriv_sub_smul_le hp hfx y (mem_Ioi.1 hl)
  · intro h
    refine tendsto_order.2 ⟨fun a ha => ?_, fun c hc => ?_⟩
    · have ha' : a < dirDeriv f x y := ha
      rw [h] at ha'
      have hev := upperSemicontinuousAt_dirDeriv_fst hf hp hx (-y) (-a)
        (EReal.lt_neg_of_lt_neg ha')
      filter_upwards [hev, isOpen_interior.mem_nhds hx] with z hz hzi
      have hz' : dirDeriv f z (-y) < -a := hz
      have hzt : f z < ⊤ := mem_convexDom.1 (interior_subset hzi)
      exact lt_of_lt_of_le (EReal.lt_neg_of_lt_neg hz')
        (neg_dirDeriv_neg_le hf hzt.ne (hp.ne_bot z) y)
    · have hc' : dirDeriv f x y < c := hc
      exact upperSemicontinuousAt_dirDeriv_fst hf hp hx y c hc'

/-- Let $E$ be a real normed space, let $f : E \to [-\infty, +\infty]$ be proper and convex, and let
$y \in E$. Then the points of $\operatorname{int}(\operatorname{dom} f)$ at which the two-sided
directional derivative in the direction $y$ exists are dense in
$\operatorname{int}(\operatorname{dom} f)$:
$$\operatorname{int}(\operatorname{dom} f) \subseteq \operatorname{cl} \{z \in
  \operatorname{int}(\operatorname{dom} f) \mid f'(z; y) = -f'(z; -y)\}.$$

This is part of Theorem 25.4 of [rockafellar1970convex]. The proof works on a line, not with
Lebesgue measure, so $E$ need not be finite-dimensional. The function $t \mapsto f(x + t y)$ is
a proper convex function of one variable, its one-sided derivatives at $t$ are $f'(x + t y; y)$
and $-f'(x + t y; -y)$, and the set where they differ is countable. -/
theorem subset_closure_twoSided_dirDeriv (hf : ConvexFn f) (hp : ProperConvex f) (y : E) :
    interior (convexDom f) ⊆
      closure {z ∈ interior (convexDom f) | dirDeriv f z y = -dirDeriv f z (-y)} := by
  intro x hx
  rw [mem_closure_iff]
  intro U hU hxU
  have hgc : ConvexFn fun t : ℝ => f (x + t • y) := convexFn_lineRestrict hf x y
  have hgp : ProperConvex fun t : ℝ => f (x + t • y) :=
    properConvex_lineRestrict hp (interior_subset hx) y
  have hVopen : IsOpen {t : ℝ | x + t • y ∈ U ∩ interior (convexDom f)} := by
    have hcont : Continuous fun t : ℝ => x + t • y := by fun_prop
    exact hcont.isOpen_preimage _ (hU.inter isOpen_interior)
  have hV0 : (0 : ℝ) ∈ {t : ℝ | x + t • y ∈ U ∩ interior (convexDom f)} := by
    simpa using And.intro hxU hx
  obtain ⟨t, ht, htV⟩ :=
    (Set.Countable.dense_compl ℝ (countable_leftDeriv_ne_rightDeriv hgc hgp)).exists_mem_open
      hVopen ⟨0, hV0⟩
  have hgt : f (x + t • y) < ⊤ := mem_convexDom.1 (interior_subset htV.2)
  have hgb : f (x + t • y) ≠ ⊥ := hp.ne_bot _
  have heq : leftDeriv (fun s : ℝ => f (x + s • y)) t
      = rightDeriv (fun s : ℝ => f (x + s • y)) t := not_not.1 ht
  rw [rightDeriv_eq_dirDeriv hgt hgb, leftDeriv_eq_neg_dirDeriv hgt hgb, dirDeriv_lineRestrict,
    dirDeriv_lineRestrict] at heq
  simp only [one_smul, neg_one_smul] at heq
  exact ⟨x + t • y, htV.1, htV.2, heq.symm⟩

end TwoSided

end ConvexAnalysis
