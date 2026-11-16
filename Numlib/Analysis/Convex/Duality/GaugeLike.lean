/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Numlib.Analysis.Convex.Duality.Gauge
import Numlib.Analysis.Convex.Operations.Closed

/-!
# Monotone conjugacy on the half-line, and the convex functions built from a gauge

This module connects two correspondences. The first is conjugacy for nondecreasing closed convex
functions $g$ of one nonnegative variable: on this class the **monotone conjugate**
$g^+(s) = \sup \{ts - g(t) : t \ge 0\}$, restricted to $s \ge 0$, is again such a function, and
$g^{++} = g$. The second composes such a function with a closed gauge $k$ on a vector space $E$
paired with $F$. The composite $g \circ k$ is a closed proper convex function whose sublevel sets
are dilates of one another, and its conjugate is $(g \circ k)^* = g^+ \circ k^\circ$, the first
correspondence applied level by level with $k$ replaced by its polar. For $g(\zeta) = \zeta^p / p$
this gives the functions that are positively homogeneous of degree $p$, and their conjugates are
positively homogeneous of the Hölder conjugate degree $q$; that the two powers are exchanged is
Young's inequality, read as a conjugacy. The presentation follows [rockafellar1970convex], §12 and
§15.

The functions $g \circ k$ are exactly the **gauge-like** closed proper convex functions $f$: those
with $f(0) = \inf f$ whose sublevel sets above the infimum are positive multiples of one set
(Theorem 15.3 of [rockafellar1970convex]).

## Main definitions

* `ConvexAnalysis.MonotoneHalfLineFn`: $g : \mathbb{R} \to [-\infty, +\infty]$ is $+\infty$ on the
  negative axis, nondecreasing on $[0, \infty)$, convex, closed, and finite at $0$.
* `ConvexAnalysis.monotoneConj`: the monotone conjugate $g^+$, with the value $+\infty$ for $s < 0$.
* `ConvexAnalysis.monotoneComp`: the composite $g \circ k$, with the convention
  $g(+\infty) = +\infty$.
* `ConvexAnalysis.levelSup`: the crossing level $\sup \{\zeta \ge 0 : g(\zeta) \le \alpha\}$, the
  dilation factor of the sublevel set $\{g \circ k \le \alpha\}$.
* `ConvexAnalysis.powHalfLine`: the function $\zeta \mapsto \zeta^p / p$ on $[0, \infty)$, extended
  by $+\infty$.
* `ConvexAnalysis.PosHomogeneousDeg`: $f(\lambda x) = \lambda^p f(x)$ for every $\lambda > 0$.
* `ConvexAnalysis.degGauge`: the gauge $(p f)^{1/p}$ attached to a function $f$ that is positively
  homogeneous of degree $p$.
* `ConvexAnalysis.IsGaugeLike`: $f(0) = \inf f$, and the sublevel sets above the infimum are
  positive multiples of one set.

## Main results

* `ConvexAnalysis.monotoneHalfLineFn_monotoneConj`, `ConvexAnalysis.monotoneConj_monotoneConj`: the
  class `ConvexAnalysis.MonotoneHalfLineFn` is stable under $g \mapsto g^+$, and $g^{++} = g$; this
  is the one-dimensional case of Theorem 12.4 of [rockafellar1970convex].
* `ConvexAnalysis.setOf_monotoneComp_le_eq_smul`: for a closed gauge $k$ and a non-constant $g$ that
  is finite at a positive point, the sublevel sets of $g \circ k$ are dilates of $\{k \le 1\}$.
* `ConvexAnalysis.convexConj_monotoneComp`: $(g \circ k)^* = g^+ \circ k^\circ$ for a closed gauge
  $k$.
* `ConvexAnalysis.closedProperConvexFn_monotoneComp`: for non-constant $g$, the composite
  $g \circ k$ is a closed proper convex function.
* `ConvexAnalysis.monotoneConj_powHalfLine`: the monotone conjugate of $\zeta \mapsto \zeta^p / p$
  is $\sigma \mapsto \sigma^q / q$.
* `ConvexAnalysis.posHomogeneousDeg_iff_exists_isGauge`: a closed proper convex function is
  positively homogeneous of degree $p > 1$ if and only if it is $(1/p) k^p$ for a closed gauge $k$
  (Corollary 15.3.1 of [rockafellar1970convex]).
* `ConvexAnalysis.convexConj_monotoneComp_powHalfLine`: $[(1/p) k^p]^* = (1/q) (k^\circ)^q$
  (Corollary 15.3.1 of [rockafellar1970convex]).
* `ConvexAnalysis.polarGauge_degGauge`, `ConvexAnalysis.pairing_le_rpow_mul_rpow`,
  `ConvexAnalysis.polarSet_setOf_le_inv`: the gauges $(p f)^{1/p}$ and $(q f^*)^{1/q}$ are polar to
  each other, $\langle x, y \rangle \le (p f(x))^{1/p} (q f^*(y))^{1/q}$, and the sets
  $\{f \le 1/p\}$ and $\{f^* \le 1/q\}$ are polar to each other (Corollary 15.3.2 of
  [rockafellar1970convex]).
* `ConvexAnalysis.IsGaugeLike.exists_eq_monotoneComp`: a gauge-like closed proper convex function is
  $g \circ k$ for a closed gauge $k$ and a suitable $g$.
* `ConvexAnalysis.closedProperConvexFn_and_isGaugeLike_iff`: a function is closed, proper, convex
  and gauge-like if and only if it is $g \circ k$ for a closed gauge $k$ and a non-constant $g$ in
  `ConvexAnalysis.MonotoneHalfLineFn` that is finite at a positive point (Theorem 15.3 of
  [rockafellar1970convex]).

## Notation

* $\langle x, y \rangle$: the pairing `B x y` of $E$ with $F$.
* $k^\circ$: the polar `ConvexAnalysis.polarGauge B k` of a gauge.
* $f^*$: the convex conjugate `ConvexAnalysis.convexConj B f`.
* $g \circ k$: the composite `ConvexAnalysis.monotoneComp g k`.

## Implementation notes

* A function in `ConvexAnalysis.MonotoneHalfLineFn` can be constant, and then $g \circ k$ need not
  be closed: its sublevel sets are the effective domain of $k$, which for a closed gauge need not be
  closed. The hypothesis that $g$ is not constant excludes this. It enters only through
  `ConvexAnalysis.MonotoneHalfLineFn.exists_monotoneConj_ne_top`; the conjugacy formula
  `ConvexAnalysis.convexConj_monotoneComp` does not need it.
* The one-variable conjugate is taken with respect to the pairing `ConvexAnalysis.mulPairing` of
  $\mathbb{R}$ with itself.
-/

open scoped Pointwise

namespace ConvexAnalysis

/-! ### Restriction to a closed set -/

section RestrictClosed

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- Let $f$ be closed in the sense of `ConvexAnalysis.ClosedConvex` and never $-\infty$, and let $s$
be a closed set. Then the restriction of $f$ to $s$, extended by $+\infty$ outside $s$, is
closed. -/
theorem ClosedConvex.convexRestrict {f : E → EReal} {s : Set E} (hf : ClosedConvex f)
    (hne : ∀ x, f x ≠ ⊥)
    (hs : IsClosed s) : ClosedConvex (ConvexAnalysis.convexRestrict s f) := by
  have hne' : ∀ x, ConvexAnalysis.convexRestrict s f x ≠ ⊥ := fun x => by
    by_cases hx : x ∈ s
    · rw [convexRestrict_of_mem hx]; exact hne x
    · rw [convexRestrict_of_notMem hx]; exact top_ne_bot
  have hepi : IsClosed (epi f) := lowerSemicontinuous_iff_isClosed_epi.1 hf.lowerSemicontinuous
  refine (closedConvex_iff_lowerSemicontinuous hne').2 ?_
  rw [lowerSemicontinuous_iff_isClosed_epi, epi_convexRestrict]
  exact hepi.inter (hs.prod isClosed_univ)

end RestrictClosed

/-!
### The self-pairing of the line, flipped

`ConvexAnalysis.mulPairing` is equal to its own flip, but not by definition. Hence the results
stated for the flipped pairing need the instances for the flipped copy as well.
-/

instance : IsContinuousPairing mulPairing.flip := by rw [mulPairing_flip]; infer_instance

instance : IsCompatiblePairing mulPairing.flip := by rw [mulPairing_flip]; infer_instance

/-! ### Nondecreasing convex functions on the half-line -/

section MonotoneHalfLine

variable {g : ℝ → EReal} {s t : ℝ}

/-- A function $g : \mathbb{R} \to [-\infty, +\infty]$ is a **nondecreasing closed convex function
on the half-line** if it is $+\infty$ on $(-\infty, 0)$, nondecreasing on $[0, \infty)$, convex,
closed, and finite at $0$.

Convexity and closedness are conditions on $g$ as a function on all of $\mathbb{R}$. Because $g$
is $+\infty$ to the left of $0$, they are the same conditions on the half-line. This is the
class on which monotone conjugacy is an involution. -/
structure MonotoneHalfLineFn (g : ℝ → EReal) : Prop where
  /-- The function is $+\infty$ to the left of the origin. -/
  top_of_neg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤
  /-- The function is nondecreasing on $[0, \infty)$. -/
  monotoneOn : MonotoneOn g (Set.Ici 0)
  /-- The function is convex. -/
  convex : ConvexFn g
  /-- The function is closed in the sense of `ConvexAnalysis.ClosedConvex`. -/
  closed : ClosedConvex g
  /-- The function is finite at the origin. -/
  zero_ne_top : g 0 ≠ ⊤

namespace MonotoneHalfLineFn

/-- A function in `ConvexAnalysis.MonotoneHalfLineFn` never takes the value $-\infty$.

The function is $+\infty$ somewhere, so the exceptional branch of `ConvexAnalysis.convexCl` does
not apply to it. -/
theorem ne_bot (hg : MonotoneHalfLineFn g) (t : ℝ) : g t ≠ ⊥ := by
  by_cases hb : ∃ x, lscHull g x = ⊥
  · have h : convexCl g = g := hg.closed
    rw [convexCl_of_exists_eq_bot hb] at h
    have hcon : (⊤ : EReal) = ⊥ := by
      rw [← hg.top_of_neg (t := -1) (by norm_num), ← h]
    exact absurd hcon top_ne_bot
  · push Not at hb
    exact fun hbt => hb t (le_bot_iff.1 (hbt ▸ lscHull_le g t))

/-- The infimum of a function $g$ in `ConvexAnalysis.MonotoneHalfLineFn` is attained at $0$:
$\inf_t g(t) = g(0)$. -/
theorem iInf_eq_zero (hg : MonotoneHalfLineFn g) : ⨅ t : ℝ, g t = g 0 :=
  le_antisymm (iInf_le _ 0) <| le_iInf fun t => by
    rcases le_or_gt 0 t with ht | ht
    · exact hg.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
    · rw [hg.top_of_neg ht]; exact le_top

/-- For $g$ in `ConvexAnalysis.MonotoneHalfLineFn`, $g(0) \le g(t)$ for every $t$. -/
theorem zero_le (hg : MonotoneHalfLineFn g) (t : ℝ) : g 0 ≤ g t :=
  hg.iInf_eq_zero ▸ iInf_le _ t

/-- A function in `ConvexAnalysis.MonotoneHalfLineFn` is proper. -/
theorem proper (hg : MonotoneHalfLineFn g) : ProperConvex g :=
  ⟨⟨0, lt_top_iff_ne_top.2 hg.zero_ne_top⟩, hg.ne_bot⟩

end MonotoneHalfLineFn

/-! ### The monotone conjugate -/

/-- The **monotone conjugate** of $g : \mathbb{R} \to [-\infty, +\infty]$ is
$$g^+(s) = \sup \{ts - g(t) : t \ge 0\} \quad (s \ge 0), \qquad g^+(s) = +\infty \quad (s <
  0).$$

The value $+\infty$ to the left of the origin, as for $g$ itself, makes $g \mapsto g^+$ an
involution on `ConvexAnalysis.MonotoneHalfLineFn` and not only a bijection onto a smaller class. -/
noncomputable def monotoneConj (g : ℝ → EReal) : ℝ → EReal :=
  ConvexAnalysis.convexRestrict (Set.Ici 0) fun s =>
    ⨆ t : ℝ, ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t

/-- For $s \ge 0$, $g^+(s) = \sup \{ts - g(t) : t \ge 0\}$. -/
theorem monotoneConj_of_nonneg (g : ℝ → EReal) (hs : 0 ≤ s) :
    monotoneConj g s = ⨆ t : ℝ, ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t :=
  convexRestrict_of_mem hs

/-- For $s < 0$, $g^+(s) = +\infty$. -/
theorem monotoneConj_of_neg (g : ℝ → EReal) (hs : s < 0) : monotoneConj g s = ⊤ :=
  convexRestrict_of_notMem (by simpa using hs)

/-- If $g$ is $+\infty$ on $(-\infty, 0)$, then its ordinary conjugate with respect to
`ConvexAnalysis.mulPairing` is $g^*(s) = \sup \{ts - g(t) : t \ge 0\}$ for every $s$. Hence
$g^+$ is $g^*$ restricted to $[0, \infty)$. -/
theorem convexConj_mulPairing_apply (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) (s : ℝ) :
    convexConj mulPairing g s = ⨆ t : ℝ, ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t := by
  rw [convexConj_apply]
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun t => iSup_le fun ht => ?_)
  · rcases le_or_gt 0 t with ht | ht
    · exact le_trans (le_iSup (fun _ : (0 : ℝ) ≤ t => ((t * s : ℝ) : EReal) - g t) ht)
        (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t) t)
    · rw [mulPairing_apply, hg ht, EReal.sub_top]; exact bot_le
  · exact le_iSup (fun t : ℝ => ((mulPairing t s : ℝ) : EReal) - g t) t

/-- If $g$ is $+\infty$ on $(-\infty, 0)$, then $g^+$ is the restriction of the ordinary conjugate
$g^*$ to $[0, \infty)$, extended by $+\infty$. -/
theorem monotoneConj_eq_convexRestrict_convexConj (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) :
    monotoneConj g = ConvexAnalysis.convexRestrict (Set.Ici 0) (convexConj mulPairing g) := by
  rw [monotoneConj, funext fun s => (convexConj_mulPairing_apply hg s).symm]

/-- If $g$ is $+\infty$ on $(-\infty, 0)$ and $s \ge 0$, then $g^+(s) = g^*(s)$. -/
theorem monotoneConj_of_nonneg' (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) (hs : 0 ≤ s) :
    monotoneConj g s = convexConj mulPairing g s := by
  rw [monotoneConj_eq_convexRestrict_convexConj hg, convexRestrict_of_mem (Set.mem_Ici.2 hs)]

/-- If $g$ is $+\infty$ on $(-\infty, 0)$, then $g^* \le g^+$, because $g^+ = +\infty$ where the two
differ. -/
theorem convexConj_le_monotoneConj (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) (s : ℝ) :
    convexConj mulPairing g s ≤ monotoneConj g s := by
  rcases le_or_gt 0 s with hs | hs
  · exact (monotoneConj_of_nonneg' hg hs).ge
  · rw [monotoneConj_of_neg _ hs]; exact le_top

/-- If $g$ is $+\infty$ on $(-\infty, 0)$, then its ordinary conjugate $g^*$ is nondecreasing,
because only $t \ge 0$ contribute to the supremum. -/
theorem monotone_convexConj_mulPairing (hg : ∀ ⦃t : ℝ⦄, t < 0 → g t = ⊤) :
    Monotone (convexConj mulPairing g) := by
  intro s s' hss
  rw [convexConj_mulPairing_apply hg, convexConj_mulPairing_apply hg]
  refine iSup_le fun t => iSup_le fun ht => le_trans ?_
    (le_trans (le_iSup (fun _ : (0 : ℝ) ≤ t => ((t * s' : ℝ) : EReal) - g t) ht)
      (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t, ((t * s' : ℝ) : EReal) - g t) t))
  exact EReal.sub_le_sub (by exact_mod_cast mul_le_mul_of_nonneg_left hss ht) le_rfl

/-- For $g$ in `ConvexAnalysis.MonotoneHalfLineFn` and $s \le 0$, the ordinary conjugate is
$g^*(s) = -g(0)$. -/
theorem convexConj_mulPairing_of_nonpos (hg : MonotoneHalfLineFn g) (hs : s ≤ 0) :
    convexConj mulPairing g s = -g 0 := by
  rw [convexConj_mulPairing_apply hg.top_of_neg]
  refine le_antisymm (iSup_le fun t => iSup_le fun ht => ?_) ?_
  · refine le_trans (EReal.sub_le_sub (y := (0 : EReal)) ?_ le_rfl) ?_
    · exact_mod_cast mul_nonpos_of_nonneg_of_nonpos ht hs
    · rw [sub_eq_add_neg, zero_add, EReal.neg_le_neg_iff]; exact hg.zero_le t
  · refine le_trans (le_of_eq ?_)
      (le_trans (le_iSup (fun _ : (0 : ℝ) ≤ (0 : ℝ) => ((0 * s : ℝ) : EReal) - g 0) le_rfl)
        (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t, ((t * s : ℝ) : EReal) - g t) (0 : ℝ)))
    rw [zero_mul, EReal.coe_zero, sub_eq_add_neg, zero_add]

/-- For $g$ in `ConvexAnalysis.MonotoneHalfLineFn`, $g^+(0) = -g(0)$. -/
theorem monotoneConj_zero (hg : MonotoneHalfLineFn g) : monotoneConj g 0 = -g 0 := by
  rw [monotoneConj_of_nonneg' hg.top_of_neg le_rfl, convexConj_mulPairing_of_nonpos hg le_rfl]

/-- If $g$ is in `ConvexAnalysis.MonotoneHalfLineFn`, then so is its monotone conjugate $g^+$. This
is part of Theorem 12.4 of [rockafellar1970convex], in one variable. -/
theorem monotoneHalfLineFn_monotoneConj (hg : MonotoneHalfLineFn g) :
    MonotoneHalfLineFn (monotoneConj g) where
  top_of_neg _ ht := monotoneConj_of_neg g ht
  monotoneOn s hs s' hs' hss := by
    rw [monotoneConj_of_nonneg' hg.top_of_neg hs, monotoneConj_of_nonneg' hg.top_of_neg hs']
    exact monotone_convexConj_mulPairing hg.top_of_neg hss
  convex := by
    rw [monotoneConj_eq_convexRestrict_convexConj hg.top_of_neg]
    exact (convexFn_convexConj mulPairing g).convexRestrict (convex_Ici 0)
  closed := by
    rw [monotoneConj_eq_convexRestrict_convexConj hg.top_of_neg]
    exact closedConvex_convexConj.convexRestrict
        (fun _ => convexConj_ne_bot hg.proper.convexDom_nonempty _) isClosed_Ici
  zero_ne_top := by
    rw [monotoneConj_zero hg]
    exact fun h => hg.ne_bot 0 (EReal.neg_eq_top_iff.1 h)

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn` and $t \ge 0$. Then
$$\sup_{s \in \mathbb{R}} \big(st - g^+(s)\big) = \sup_{s \in \mathbb{R}} \big(st -
  g^*(s)\big).$$
At $t \ge 0$ the negative half-line adds nothing to the second conjugate: $g^*$ is constant
there, and the constant is already the term at $s = 0$. -/
theorem iSup_sub_monotoneConj (hg : MonotoneHalfLineFn g) (ht : 0 ≤ t) :
    (⨆ s : ℝ, ((s * t : ℝ) : EReal) - monotoneConj g s)
      = ⨆ s : ℝ, ((s * t : ℝ) : EReal) - convexConj mulPairing g s := by
  refine le_antisymm
    (iSup_mono fun s => EReal.sub_le_sub le_rfl (convexConj_le_monotoneConj hg.top_of_neg s))
    (iSup_le fun s => ?_)
  rcases le_or_gt 0 s with hs | hs
  · exact le_trans (le_of_eq (by rw [monotoneConj_of_nonneg' hg.top_of_neg hs]))
      (le_iSup (fun s : ℝ => ((s * t : ℝ) : EReal) - monotoneConj g s) s)
  · have hz : (((0 : ℝ) * t : ℝ) : EReal) - monotoneConj g (0 : ℝ) = g 0 := by
      rw [monotoneConj_zero hg, zero_mul, EReal.coe_zero, sub_eq_add_neg, neg_neg, zero_add]
    refine le_trans ?_ (le_trans hz.ge
      (le_iSup (fun s : ℝ => ((s * t : ℝ) : EReal) - monotoneConj g s) (0 : ℝ)))
    rw [convexConj_mulPairing_of_nonpos hg hs.le, sub_eq_add_neg, neg_neg]
    calc ((s * t : ℝ) : EReal) + g 0
        ≤ (0 : EReal) + g 0 :=
          add_le_add (by exact_mod_cast mul_nonpos_of_nonpos_of_nonneg hs.le ht) le_rfl
      _ = g 0 := zero_add _

/-- **Monotone conjugacy is an involution**: for $g$ in `ConvexAnalysis.MonotoneHalfLineFn`,
$$g^{++} = g.$$
This is part of Theorem 12.4 of [rockafellar1970convex], in one variable.

The proof is the Fenchel–Moreau theorem for `ConvexAnalysis.mulPairing` together with
`ConvexAnalysis.iSup_sub_monotoneConj`, which says that the restriction of the conjugate to the
half-line does not change the second conjugate at a nonnegative argument. -/
theorem monotoneConj_monotoneConj (hg : MonotoneHalfLineFn g) :
    monotoneConj (monotoneConj g) = g := by
  have hG := monotoneHalfLineFn_monotoneConj hg
  funext t
  rcases lt_or_ge t 0 with ht | ht
  · rw [monotoneConj_of_neg _ ht, hg.top_of_neg ht]
  have h1 : monotoneConj (monotoneConj g) t
      = ⨆ s : ℝ, ((s * t : ℝ) : EReal) - monotoneConj g s :=
    monotoneConj_of_nonneg' hG.top_of_neg ht
  have h2 : convexBiconj mulPairing g t = ⨆ s : ℝ,
      ((t * s : ℝ) : EReal) - convexConj mulPairing g s := rfl
  rw [h1, iSup_sub_monotoneConj hg ht,
    iSup_congr (g := fun s : ℝ => ((t * s : ℝ) : EReal) - convexConj mulPairing g s)
      fun s => by rw [mul_comm], ← h2, convexBiconj_eq_convexCl hg.convex, hg.closed]

end MonotoneHalfLine

/-! ### Composing a gauge with a function on the half-line -/

section MonotoneComp

variable {E : Type*} {g : ℝ → EReal} {k : E → EReal} {x : E} {c : ℝ}

/-- The **composite** of $g : \mathbb{R} \to [-\infty, +\infty]$ with $k : E \to [-\infty, +\infty]$
is
$$(g \circ k)(x) = \inf \{g(t) : t \in \mathbb{R},\ k(x) \le t\}.$$
It is intended for $k$ with values in $[0, +\infty]$ and $g$ nondecreasing on $[0, \infty)$.
Then it is $g(k(x))$ with the convention $g(+\infty) = +\infty$.

The infimum over the real levels above $k(x)$ avoids an extension of $g$ to `EReal` and a case
split. It makes both defining equations short: $(g \circ k)(x) = g(c)$ when $k(x) = c \ge 0$ and
$g$ is nondecreasing on $[0, \infty)$ (`ConvexAnalysis.monotoneComp_of_eq_coe`), and
$(g \circ k)(x) = +\infty$ when $k(x) = +\infty$ (`ConvexAnalysis.monotoneComp_of_eq_top`). -/
noncomputable def monotoneComp (g : ℝ → EReal) (k : E → EReal) : E → EReal :=
  fun x => ⨅ t : ℝ, ⨅ _ : k x ≤ (t : EReal), g t

/-- The defining formula $(g \circ k)(x) = \inf \{g(t) : k(x) \le t\}$. -/
theorem monotoneComp_apply (g : ℝ → EReal) (k : E → EReal) (x : E) :
    monotoneComp g k x = ⨅ t : ℝ, ⨅ _ : k x ≤ (t : EReal), g t := rfl

/-- If $k(x) \le c$ for a real $c$, then $(g \circ k)(x) \le g(c)$. -/
theorem monotoneComp_le (h : k x ≤ (c : EReal)) : monotoneComp g k x ≤ g c :=
  iInf_le_of_le c (le_of_eq (iInf_pos h))

/-- If $k(x) = +\infty$, then $(g \circ k)(x) = +\infty$, because no real level lies above
$+\infty$. -/
theorem monotoneComp_of_eq_top (g : ℝ → EReal) (h : k x = ⊤) : monotoneComp g k x = ⊤ :=
  iInf_eq_top.2 fun t => iInf_neg fun hc => EReal.coe_ne_top t (top_le_iff.1 (h ▸ hc))

/-- Let $g$ be nondecreasing on $[0, \infty)$, and let $k(x) = c$ with $c \ge 0$. Then
$(g \circ k)(x) = g(c)$: the infimum is attained at $t = c$. No semicontinuity is needed. -/
theorem monotoneComp_of_eq_coe (hg : MonotoneOn g (Set.Ici 0)) (hc : 0 ≤ c)
    (h : k x = (c : EReal)) : monotoneComp g k x = g c := by
  refine le_antisymm (monotoneComp_le (h.le.trans_eq rfl)) (le_iInf fun t => le_iInf fun ht => ?_)
  rw [h, EReal.coe_le_coe_iff] at ht
  exact hg (Set.mem_Ici.2 hc) (Set.mem_Ici.2 (hc.trans ht)) ht

/-- An extended real $z \ge 0$ is either $+\infty$ or a real number $c \ge 0$. -/
theorem eq_top_or_exists_coe_of_nonneg {z : EReal} (hz : 0 ≤ z) :
    z = ⊤ ∨ ∃ c : ℝ, 0 ≤ c ∧ z = (c : EReal) := by
  rcases eq_or_lt_of_le (le_top (a := z)) with htop | hlt
  · exact Or.inl htop
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (fun h => by simp [h] at hz) hlt
  exact Or.inr ⟨c, EReal.coe_nonneg.1 (hc ▸ hz), hc⟩

end MonotoneComp


/-! ### Convexity and properness of the composite -/

section MonotoneCompConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {g : ℝ → EReal} {k : E → EReal}

/-- If $g$ and $k$ are convex, then $g \circ k$ is convex.

No monotonicity of $g$ is needed, because the infimum over the real levels above $k(x)$ already
makes the composite monotone in the level. The strict form of convexity
(`ConvexAnalysis.convexFn_iff_forall_lt`) gives a level for each of the two points. -/
theorem convexFn_monotoneComp (hg : ConvexFn g) (hk : ConvexFn k) :
    ConvexFn (monotoneComp g k) := by
  refine (convexFn_iff_forall_lt _).2 fun x y a b ha hb hab α β hx hy => ?_
  rw [monotoneComp_apply, iInf_lt_iff] at hx hy
  obtain ⟨t, ht⟩ := hx
  rw [iInf_lt_iff] at ht
  obtain ⟨hkt, hgt⟩ := ht
  obtain ⟨s, hs⟩ := hy
  rw [iInf_lt_iff] at hs
  obtain ⟨hks, hgs⟩ := hs
  exact lt_of_le_of_lt (monotoneComp_le (hk.epi_combo hkt hks ha.le hb.le hab))
    ((convexFn_iff_forall_lt g).1 hg t s a b ha hb hab α β hgt hgs)

/-- If $g$ is in `ConvexAnalysis.MonotoneHalfLineFn` and $k$ is a gauge, then $g \circ k$ is proper:
it has the finite value $g(0)$ at the origin, and it is bounded below by $g(0)$. -/
theorem properConvex_monotoneComp (hg : MonotoneHalfLineFn g) (hk : IsGauge k) :
    ProperConvex (monotoneComp g k) where
  convexDom_nonempty := ⟨0, by
    have h : monotoneComp g k (0 : E) = g 0 :=
      monotoneComp_of_eq_coe hg.monotoneOn le_rfl (by rw [hk.map_zero, EReal.coe_zero])
    change monotoneComp g k (0 : E) < ⊤
    rw [h]
    exact lt_top_iff_ne_top.2 hg.zero_ne_top⟩
  ne_bot x := by
    have h : g 0 ≤ monotoneComp g k x := le_iInf fun t => le_iInf fun _ => hg.zero_le t
    intro hc
    rw [hc, le_bot_iff] at h
    exact hg.ne_bot 0 h

end MonotoneCompConvex

/-!
### Growth of a non-constant function of the half-line

A nondecreasing convex function of the half-line that is not constant grows at least linearly. Hence
its monotone conjugate is finite at small positive arguments. This is what the hypothesis "not
constant" contributes: it makes $g \circ k$ closed.
-/

section Growth

variable {g : ℝ → EReal} {c₀ r t₂ : ℝ}

/-- A convex function of the half-line lies above the extended secant through the origin. Let $g$ be
convex and never $-\infty$, with $g(0) \le c_0$, and let $t_2 > 0$ with $r \le g(t_2)$. Then for
every $t \ge t_2$,
$$c_0 + \frac{r - c_0}{t_2}\, t \le g(t).$$
-/
theorem coe_add_mul_le_of_convex (hg : ConvexFn g) (hnb : ∀ z, g z ≠ ⊥) (h0 : g 0 ≤ (c₀ : EReal))
    (ht₂ : 0 < t₂) (hr : (r : EReal) ≤ g t₂) {t : ℝ} (ht : t₂ ≤ t) :
    ((c₀ + (r - c₀) / t₂ * t : ℝ) : EReal) ≤ g t := by
  have ht0 : 0 < t := lt_of_lt_of_le ht₂ ht
  rcases eq_or_lt_of_le (le_top (a := g t)) with htop | hlt
  · rw [htop]; exact le_top
  obtain ⟨v, hv⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hnb t) hlt
  set l : ℝ := t₂ / t with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one ht0]; exact ht
  have hcombo := hg.epi_combo (x := (0 : ℝ)) (y := t) (μ := c₀) (ν := v) h0 (le_of_eq hv)
    (by linarith : (0 : ℝ) ≤ 1 - l) hl0.le (by ring)
  rw [smul_zero, zero_add, smul_eq_mul, hl, div_mul_cancel₀ _ ht0.ne'] at hcombo
  have hb : r ≤ (1 - l) * c₀ + l * v := by
    have h := le_trans hr hcombo
    exact EReal.coe_le_coe_iff.1 h
  rw [hv, EReal.coe_le_coe_iff]
  have hlv : l * v = t₂ / t * v := by rw [hl]
  have hkey : (r - c₀) * t ≤ t₂ * (v - c₀) := by
    have h3 : (r - c₀) * t ≤ l * (v - c₀) * t := by nlinarith
    have h4 : l * (v - c₀) * t = t₂ * (v - c₀) := by
      rw [hl]; field_simp
    linarith [h3, h4.le, h4.ge]
  rw [div_mul_eq_mul_div, ← sub_nonneg]
  have h5 : v - (c₀ + (r - c₀) * t / t₂) = (t₂ * (v - c₀) - (r - c₀) * t) / t₂ := by
    field_simp; ring
  rw [h5]
  positivity

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn`, and let $g(0) < g(t)$ for some $t > 0$. Then
$g(0)$ is a real number $c_0$, and there are $m > 0$ and $t_2 > 0$ with
$$c_0 + m t \le g(t) \quad \text{for every } t \ge t_2.$$
This is the quantitative form of $g(\zeta) \to +\infty$. -/
theorem MonotoneHalfLineFn.exists_affine_minorant (hg : MonotoneHalfLineFn g)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) :
    ∃ m c₀ t₂ : ℝ, 0 < m ∧ 0 < t₂ ∧ g 0 = (c₀ : EReal) ∧
      ∀ t : ℝ, t₂ ≤ t → ((c₀ + m * t : ℝ) : EReal) ≤ g t := by
  obtain ⟨t₂, ht₂, hlt⟩ := hne
  obtain ⟨c₀, hc₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot 0)
    (lt_top_iff_ne_top.2 hg.zero_ne_top)
  obtain ⟨r, hrc, hrg⟩ : ∃ r : ℝ, c₀ < r ∧ (r : EReal) ≤ g t₂ := by
    rcases eq_or_lt_of_le (le_top (a := g t₂)) with htop | hlt'
    · exact ⟨c₀ + 1, by linarith, by rw [htop]; exact le_top⟩
    · obtain ⟨v, hv⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot t₂) hlt'
      exact ⟨v, by rw [hc₀, hv] at hlt; exact_mod_cast hlt, le_of_eq hv.symm⟩
  exact ⟨(r - c₀) / t₂, c₀, t₂, by positivity, ht₂, hc₀,
    fun t ht => coe_add_mul_le_of_convex hg.convex hg.ne_bot (le_of_eq hc₀) ht₂ hrg ht⟩

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn`, and let $g(0) < g(t)$ for some $t > 0$. Then
$g^+(\zeta) < +\infty$ for some $\zeta > 0$.

The proof takes $\zeta$ below the slope of the affine minorant of
`ConvexAnalysis.MonotoneHalfLineFn.exists_affine_minorant`. -/
theorem MonotoneHalfLineFn.exists_monotoneConj_ne_top (hg : MonotoneHalfLineFn g)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) : ∃ ζ : ℝ, 0 < ζ ∧ monotoneConj g ζ ≠ ⊤ := by
  obtain ⟨m, c₀, t₂, hm0, ht₂, hc₀, hmin⟩ := MonotoneHalfLineFn.exists_affine_minorant hg hne
  refine ⟨m / 2, by positivity, ?_⟩
  have hbound : monotoneConj g (m / 2) ≤ ((t₂ * (m / 2) - c₀ : ℝ) : EReal) := by
    rw [monotoneConj_of_nonneg g (by positivity)]
    refine iSup_le fun t => iSup_le fun ht => ?_
    rcases le_or_gt t₂ t with hcase | hcase
    · refine le_trans (EReal.sub_le_sub (le_refl ((t * (m / 2) : ℝ) : EReal))
        (hmin t hcase)) ?_
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      nlinarith
    · refine le_trans (EReal.sub_le_sub (le_refl ((t * (m / 2) : ℝ) : EReal))
        (show ((c₀ : ℝ) : EReal) ≤ g t by rw [← hc₀]; exact hg.zero_le t)) ?_
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      nlinarith
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hbound

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn`, and let $g(\zeta) < +\infty$ for some
$\zeta > 0$. Then $g^+$ is not constant: $g^+(0) < g^+(s)$ for some $s > 0$.

The term of the defining supremum at $\zeta$ is an affine function of $s$ with positive slope,
so $g^+$ grows without bound. With
`ConvexAnalysis.MonotoneHalfLineFn.exists_monotoneConj_ne_top`, this is the statement of
[rockafellar1970convex] that $g^+$ satisfies the same conditions as $g$; it shows that conjugacy
exchanges the two side conditions. -/
theorem MonotoneHalfLineFn.exists_lt_monotoneConj (hg : MonotoneHalfLineFn g)
    (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤) :
    ∃ s : ℝ, 0 < s ∧ monotoneConj g 0 < monotoneConj g s := by
  obtain ⟨ζ, hζ, hζt⟩ := hfin
  obtain ⟨b, hb⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot 0)
    (lt_top_iff_ne_top.2 hg.zero_ne_top)
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot ζ)
    (lt_top_iff_ne_top.2 hζt)
  refine ⟨max 1 ((c - b + 1) / ζ), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  have hs0 : (0 : ℝ) ≤ max 1 ((c - b + 1) / ζ) := le_trans zero_le_one (le_max_left _ _)
  have hkey : c - b < ζ * max 1 ((c - b + 1) / ζ) := by
    have h1 := (div_le_iff₀ hζ).1 (le_max_right 1 ((c - b + 1) / ζ))
    linarith
  have hterm : ((ζ * max 1 ((c - b + 1) / ζ) : ℝ) : EReal) - g ζ
      ≤ monotoneConj g (max 1 ((c - b + 1) / ζ)) := by
    rw [monotoneConj_of_nonneg g hs0]
    exact le_trans (le_iSup (fun _ : (0 : ℝ) ≤ ζ =>
        ((ζ * max 1 ((c - b + 1) / ζ) : ℝ) : EReal) - g ζ) hζ.le)
      (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t,
        ((t * max 1 ((c - b + 1) / ζ) : ℝ) : EReal) - g t) ζ)
  refine lt_of_lt_of_le ?_ hterm
  rw [monotoneConj_zero hg, hb, hc, ← EReal.coe_neg, ← EReal.coe_sub,
    EReal.coe_lt_coe_iff]
  linarith

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn`, and let $g(0) < g(t)$ for some $t > 0$. Then
for every real $\alpha$ the set $\{t \ge 0 : g(t) \le \alpha\}$ is bounded above. -/
theorem MonotoneHalfLineFn.bddAbove_setOf_le (hg : MonotoneHalfLineFn g)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) (α : ℝ) :
    BddAbove {t : ℝ | 0 ≤ t ∧ g t ≤ (α : EReal)} := by
  obtain ⟨m, c₀, t₂, hm0, ht₂, hc₀, hmin⟩ := MonotoneHalfLineFn.exists_affine_minorant hg hne
  refine ⟨max t₂ ((α - c₀) / m), fun t ht => ?_⟩
  obtain ⟨-, htα⟩ := ht
  rcases le_or_gt t t₂ with h | h
  · exact le_trans h (le_max_left _ _)
  · refine le_trans ?_ (le_max_right t₂ ((α - c₀) / m))
    have hb := le_trans (hmin t h.le) htα
    rw [EReal.coe_le_coe_iff] at hb
    rw [le_div_iff₀ hm0]
    linarith

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn`, and let $g(\zeta) < +\infty$ for some
$\zeta > 0$. If $g(0) < \alpha$, then $g(t) \le \alpha$ for some $t > 0$.

This is a form of continuity from the right at the origin. Without finiteness at a positive
point, $g$ can jump to $+\infty$ immediately to the right of $0$. -/
theorem MonotoneHalfLineFn.exists_pos_le (hg : MonotoneHalfLineFn g)
    (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤) {α : ℝ} (hα : g 0 < (α : EReal)) :
    ∃ t : ℝ, 0 < t ∧ g t ≤ (α : EReal) := by
  obtain ⟨ζ, hζ, hζt⟩ := hfin
  obtain ⟨c₀, hc₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot 0)
    (lt_top_iff_ne_top.2 hg.zero_ne_top)
  obtain ⟨v, hv⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot ζ)
    (lt_top_iff_ne_top.2 hζt)
  have hcα : c₀ < α := by rw [hc₀] at hα; exact_mod_cast hα
  set d : ℝ := max (v - c₀) 1 with hd
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set l : ℝ := min 1 ((α - c₀) / d) with hl
  have hl0 : 0 < l := lt_min zero_lt_one (by positivity)
  have hl1 : l ≤ 1 := min_le_left _ _
  have hkey : (1 - l) * c₀ + l * v ≤ α := by
    have h1 : l * (v - c₀) ≤ l * d :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hl0.le
    have h2 : l * d ≤ α - c₀ := by
      have := min_le_right (1 : ℝ) ((α - c₀) / d)
      calc l * d ≤ ((α - c₀) / d) * d := by nlinarith
        _ = α - c₀ := by field_simp
    nlinarith
  refine ⟨l * ζ, by positivity, ?_⟩
  have hcombo := hg.convex.epi_combo (x := (0 : ℝ)) (y := ζ) (μ := c₀) (ν := v)
    (le_of_eq hc₀) (le_of_eq hv) (by linarith : (0 : ℝ) ≤ 1 - l) hl0.le (by ring)
  rw [smul_zero, zero_add, smul_eq_mul] at hcombo
  exact le_trans hcombo (EReal.coe_le_coe_iff.2 hkey)

/-- The **crossing level** of $g : \mathbb{R} \to [-\infty, +\infty]$ at $\alpha \in \mathbb{R}$ is
the real number
$$\sup \{t \ge 0 : g(t) \le \alpha\}.$$
It is the dilation factor of the sublevel set $\{g \circ k \le \alpha\}$.

The supremum is `sSup` in $\mathbb{R}$, so it is $0$ when the set is empty or not bounded above. -/
noncomputable def levelSup (g : ℝ → EReal) (α : ℝ) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ g t ≤ (α : EReal)}

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn` with $g(0) < g(t)$ for some $t > 0$, and let
$g(0) \le \alpha$. Then the crossing level $\lambda$ at $\alpha$ is attained: $\lambda \ge 0$
and $g(\lambda) \le \alpha$. The reason is that the set of levels is closed and bounded. -/
theorem levelSup_mem (hg : MonotoneHalfLineFn g) (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) {α : ℝ}
    (hα : g 0 ≤ (α : EReal)) : 0 ≤ levelSup g α ∧ g (levelSup g α) ≤ (α : EReal) := by
  have hset : {t : ℝ | 0 ≤ t ∧ g t ≤ (α : EReal)} = Set.Ici 0 ∩ g ⁻¹' Set.Iic (α : EReal) := rfl
  have hcl : IsClosed {t : ℝ | 0 ≤ t ∧ g t ≤ (α : EReal)} := by
    rw [hset]
    exact isClosed_Ici.inter
      (lowerSemicontinuous_iff_isClosed_preimage.1 (ClosedConvex.lowerSemicontinuous hg.closed) _)
  exact hcl.csSup_mem ⟨0, le_rfl, hα⟩ (MonotoneHalfLineFn.bddAbove_setOf_le hg hne α)

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn` with $g(0) < g(t)$ for some $t > 0$. If
$t \ge 0$ and $g(t) \le \alpha$, then $t$ is at most the crossing level at $\alpha$. -/
theorem le_levelSup (hg : MonotoneHalfLineFn g) (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) {α t : ℝ}
    (ht : 0 ≤ t) (htα : g t ≤ (α : EReal)) : t ≤ levelSup g α :=
  le_csSup (MonotoneHalfLineFn.bddAbove_setOf_le hg hne α) ⟨ht, htα⟩

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn` with $g(0) < g(t)$ for some $t > 0$ and
$g(\zeta) < +\infty$ for some $\zeta > 0$. If $g(0) < \alpha$, then the crossing level at
$\alpha$ is positive. -/
theorem levelSup_pos (hg : MonotoneHalfLineFn g) (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t)
    (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤) {α : ℝ} (hα : g 0 < (α : EReal)) : 0 < levelSup g α := by
  obtain ⟨t, ht0, htα⟩ := MonotoneHalfLineFn.exists_pos_le hg hfin hα
  exact lt_of_lt_of_le ht0 (le_levelSup hg hne ht0.le htα)

end Growth

/-!
### The sublevel sets of $g \circ k$ are dilates of one another

This is the geometric content of the term "gauge-like" of [rockafellar1970convex]. Every sublevel
set $\{g \circ k \le \alpha\}$ with $\alpha$ above the minimum is the dilate $\lambda \{k \le 1\}$,
where $\lambda$ is the crossing level of $g$ at $\alpha$.
-/

section GaugeLikeLevels

variable {E : Type*} {g : ℝ → EReal} {k : E → EReal} {α : ℝ}

/-- Let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn` with $g(0) < g(t)$ for some $t > 0$, let $k$
be nonnegative, and let $g(0) \le \alpha$. Then $(g \circ k)(x) \le \alpha$ if and only if
$k(x) \le \lambda$, where $\lambda$ is the crossing level of $g$ at $\alpha$. -/
theorem monotoneComp_le_coe_iff (hg : MonotoneHalfLineFn g) (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t)
    (hknn : ∀ z, 0 ≤ k z) (hα : g 0 ≤ (α : EReal)) (x : E) :
    monotoneComp g k x ≤ (α : EReal) ↔ k x ≤ ((levelSup g α : ℝ) : EReal) := by
  obtain ⟨hl0, hlα⟩ := levelSup_mem hg hne hα
  constructor
  · intro h
    rcases eq_top_or_exists_coe_of_nonneg (hknn x) with hx | ⟨c, hc0, hx⟩
    · rw [monotoneComp_of_eq_top g hx] at h
      exact absurd (top_le_iff.1 h) (EReal.coe_ne_top α)
    · rw [monotoneComp_of_eq_coe hg.monotoneOn hc0 hx] at h
      rw [hx, EReal.coe_le_coe_iff]
      exact le_levelSup hg hne hc0 h
  · intro h
    obtain ⟨c, hc0, hx⟩ : ∃ c : ℝ, 0 ≤ c ∧ k x = (c : EReal) := by
      rcases eq_top_or_exists_coe_of_nonneg (hknn x) with hx | h'
      · exact absurd (hx ▸ h) (by simp)
      · exact h'
    rw [monotoneComp_of_eq_coe hg.monotoneOn hc0 hx]
    rw [hx, EReal.coe_le_coe_iff] at h
    exact le_trans (hg.monotoneOn (Set.mem_Ici.2 hc0) (Set.mem_Ici.2 hl0) h) hlα

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- Let $E$ be a topological vector space, let $k$ be a closed gauge on $E$, and let $g$ be in
`ConvexAnalysis.MonotoneHalfLineFn` with $g(0) < g(t)$ for some $t > 0$ and $g(\zeta) < +\infty$
for some $\zeta > 0$. If $g(0) < \alpha$, then
$$\{x : (g \circ k)(x) \le \alpha\} = \lambda \{x : k(x) \le 1\},$$
where $\lambda$ is the crossing level of $g$ at $\alpha$. This says that $g \circ k$ is
gauge-like in the sense of [rockafellar1970convex]. -/
theorem setOf_monotoneComp_le_eq_smul (hk : IsGauge k) (hkc : ClosedConvex k)
    (hg : MonotoneHalfLineFn g)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤)
    (hα : g 0 < (α : EReal)) :
    {x : E | monotoneComp g k x ≤ (α : EReal)} = levelSup g α • {x : E | k x ≤ 1} := by
  have hpos : 0 < levelSup g α := levelSup_pos hg hne hfin hα
  have hkC : gaugeFn {z : E | k z ≤ 1} = k :=
    gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero
  rw [← setOf_gaugeFn_le_pos (IsGauge.convex_level_one hk) (IsGauge.zero_mem_level_one hk)
    (isClosed_setOf_le_one hkc) hpos, hkC]
  ext x
  exact monotoneComp_le_coe_iff hg hne hk.nonneg hα.le x

end GaugeLikeLevels

/-!
### The conjugate of a gauge composed with a function on the half-line

The composite $g \circ k$ of a closed gauge with a nondecreasing closed convex function on the
half-line has the conjugate $g^+ \circ k^\circ$. The proof groups the supremum that defines the
conjugate by the level $\zeta = k(x)$. On the dilate $\zeta \{k \le 1\}$ the composite is at most
$g(\zeta)$, and the supremum of the pairing over this dilate is $\zeta k^\circ(y)$. Closedness of
$k$ enters only through `ConvexAnalysis.convexConj_monotoneComp_le`.
-/

section GaugeCompLower

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : ℝ → EReal} {k : E → EReal} {x : E} {y : F} {c : ℝ}

/-- Let $k$ be a gauge with $k(x) = 0$, and let $k^\circ(y)$ be finite. Then
$\langle x, y \rangle \le 0$.

The set $\{k = 0\}$ is the recession cone of $\{k \le 1\}$, which in general is not $\{0\}$, so
the bound comes from scaling: $k(l^{-1} x) = 0 \le 1$ for every $l > 0$, hence
$\langle x, y \rangle \le l k^\circ(y)$, and $l \to 0$ gives $\langle x, y \rangle \le 0$.
Finiteness of $k^\circ(y)$ is necessary, because $0 \cdot (+\infty) = 0$ in `EReal`. -/
theorem pairing_nonpos_of_gauge_eq_zero (hk : IsGauge k) (hx : k x = 0)
    (hc : polarGauge B k y = (c : EReal)) : B x y ≤ 0 := by
  have hc0 : (0 : ℝ) ≤ c := by
    have h := polarGauge_nonneg B k y
    rw [hc] at h
    exact EReal.coe_nonneg.1 h
  have hsupp : supportFn B {z : E | k z ≤ 1} y = (c : EReal) := by
    rw [← hc, polarGauge_eq_supportFn hk.nonneg hk.posHomogeneous hk.map_zero]
  have hray : ∀ l : ℝ, 0 < l → B x y ≤ l * c := by
    intro l hl
    have hmem : l⁻¹ • x ∈ {z : E | k z ≤ 1} := by
      change k (l⁻¹ • x) ≤ 1
      rw [hk.posHomogeneous l⁻¹ (inv_pos.2 hl) x, hx, mul_zero]
      exact zero_le_one
    have hb := supportFn_le_coe_iff.1 hsupp.le _ hmem
    rwa [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hl] at hb
  by_contra hcon
  rw [not_le] at hcon
  have hb := hray _ (div_pos hcon (by linarith : (0 : ℝ) < 2 * (c + 1)))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (c + 1))] at hb
  nlinarith

/-- Let $k$ be a gauge, let $\zeta > 0$, and let $g(\zeta)$ be finite. Then
$$\zeta k^\circ(y) - g(\zeta) \le (g \circ k)^*(y).$$

On the dilate $\zeta \{k \le 1\}$ the composite is at most $g(\zeta)$, and the supremum of the
pairing over the dilate is $\zeta k^\circ(y)$. Nothing else is assumed about $g$ or $k$. This
lemma gives the inequality $\ge$ of the conjugacy formula and, where $k^\circ(y) = +\infty$, the
value $+\infty$ of the conjugate. -/
theorem coe_mul_polarGauge_sub_le_convexConj (hk : IsGauge k) {ζ r : ℝ} (hζ : 0 < ζ)
    (hr : g ζ = (r : EReal)) :
    (ζ : EReal) * polarGauge B k y - g ζ ≤ convexConj B (monotoneComp g k) y := by
  have hkC : gaugeFn {z : E | k z ≤ 1} = k :=
    gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero
  have hsmul : (ζ : EReal) * polarGauge B k y = supportFn B (ζ • {z : E | k z ≤ 1}) y := by
    rw [polarGauge_eq_supportFn hk.nonneg hk.posHomogeneous hk.map_zero, supportFn_smul B hζ]
  have hbound : ∀ z ∈ ζ • {z : E | k z ≤ 1},
      ((B z y : ℝ) : EReal) + ((-r : ℝ) : EReal) ≤ convexConj B (monotoneComp g k) y := by
    intro z hz
    have hkz : k z ≤ (ζ : EReal) := by
      rw [← hkC]; exact gaugeFn_le_of_mem_smul hζ.le hz
    have hfz : monotoneComp g k z ≤ (r : EReal) := by
      rw [← hr]; exact monotoneComp_le hkz
    refine le_trans ?_ (sub_le_convexConj B (monotoneComp g k) z y)
    rw [EReal.coe_neg, ← sub_eq_add_neg]
    exact EReal.sub_le_sub le_rfl hfz
  rw [hsmul, hr, sub_eq_add_neg, ← EReal.coe_neg, supportFn_apply,
    EReal.biSup_add_coe]
  exact iSup₂_le hbound

/-- Let $k$ be a gauge, and let $g$ be nondecreasing on $[0, \infty)$. Then
$0 - g(0) \le (g \circ k)^*(y)$; the origin realizes the level $\zeta = 0$, because a gauge
vanishes there. -/
theorem sub_apply_zero_le_convexConj (hk : IsGauge k) (hg : MonotoneOn g (Set.Ici 0)) :
    (0 : EReal) - g 0 ≤ convexConj B (monotoneComp g k) y := by
  have hf0 : monotoneComp g k (0 : E) = g 0 :=
    monotoneComp_of_eq_coe hg le_rfl (by rw [hk.map_zero, EReal.coe_zero])
  have h := sub_le_convexConj B (monotoneComp g k) (0 : E) y
  rwa [hf0, map_zero, LinearMap.zero_apply, EReal.coe_zero] at h

/-- Let $k$ be a gauge, let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn`, and let $k^\circ(y) = c$
be finite. Then $g^+(c) \le (g \circ k)^*(y)$. This is the inequality $\ge$ of the conjugacy
formula at a point where the polar gauge is finite. -/
theorem monotoneConj_le_convexConj_monotoneComp (hk : IsGauge k) (hg : MonotoneHalfLineFn g)
    (hc : polarGauge B k y = (c : EReal)) :
    monotoneConj g c ≤ convexConj B (monotoneComp g k) y := by
  have hc0 : (0 : ℝ) ≤ c := by
    have h := polarGauge_nonneg B k y
    rw [hc] at h
    exact EReal.coe_nonneg.1 h
  rw [monotoneConj_of_nonneg g hc0]
  refine iSup_le fun t => iSup_le fun ht => ?_
  by_cases htop : g t = ⊤
  · rw [htop, EReal.sub_top]; exact bot_le
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot t)
    (lt_top_iff_ne_top.2 htop)
  rcases eq_or_lt_of_le ht with rfl | ht'
  · rw [zero_mul, EReal.coe_zero]
    exact sub_apply_zero_le_convexConj hk hg.monotoneOn
  · have h := coe_mul_polarGauge_sub_le_convexConj (B := B) (y := y) hk ht' hr
    rwa [hc, ← EReal.coe_mul] at h

end GaugeCompLower

section GaugeComp

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : ℝ → EReal} {k : E → EReal} {x : E} {y : F} {c : ℝ}

/-- **Inequality for a gauge and its polar.** Let $E$ be a topological vector space, and let $k$ be
a closed gauge on $E$. If $k(x) = c$ and $k^\circ(y) = d$ are finite, then
$$\langle x, y \rangle \le c d.$$

For $c > 0$ this follows from $x \in c \{k \le 1\}$ and the identification of $k^\circ$ with the
support function of $\{k \le 1\}$. For $c = 0$ the product would be $0 \cdot k^\circ(y)$, and
the bound is `ConvexAnalysis.pairing_nonpos_of_gauge_eq_zero`. -/
theorem pairing_le_mul_of_gauge (hk : IsGauge k) (hkc : ClosedConvex k) {d : ℝ}
    (hx : k x = (c : EReal)) (hy : polarGauge B k y = (d : EReal)) : B x y ≤ c * d := by
  have hc0 : (0 : ℝ) ≤ c := by
    have h := hk.nonneg x
    rw [hx] at h
    exact EReal.coe_nonneg.1 h
  have hsupp : supportFn B {z : E | k z ≤ 1} y = (d : EReal) := by
    rw [← hy, polarGauge_eq_supportFn hk.nonneg hk.posHomogeneous hk.map_zero]
  rcases eq_or_lt_of_le hc0 with rfl | hpos
  · rw [zero_mul]
    exact pairing_nonpos_of_gauge_eq_zero hk (by rw [hx, EReal.coe_zero]) hy
  · have hkC : gaugeFn {z : E | k z ≤ 1} = k :=
      gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero
    have hmem : x ∈ c • {z : E | k z ≤ 1} := by
      rw [← setOf_gaugeFn_le_pos (IsGauge.convex_level_one hk) (IsGauge.zero_mem_level_one hk)
        (isClosed_setOf_le_one hkc) hpos]
      change gaugeFn {z : E | k z ≤ 1} x ≤ (c : EReal)
      rw [hkC, hx]
    have hb := le_supportFn (B := B) hmem y
    rwa [supportFn_smul B hpos, hsupp, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hb

/-- Let $E$ be a topological vector space, let $k$ be a closed gauge on $E$, let $g$ be in
`ConvexAnalysis.MonotoneHalfLineFn`, and let $k^\circ(y) = c$ be finite. Then
$(g \circ k)^*(y) \le g^+(c)$. This is the inequality $\le$ of the conjugacy formula at a point
where the polar gauge is finite.

The supremum over $x$ is grouped by the level $\zeta = k(x)$, and on each level the pairing is
bounded by `ConvexAnalysis.pairing_le_mul_of_gauge`. -/
theorem convexConj_monotoneComp_le (hk : IsGauge k) (hkc : ClosedConvex k)
    (hg : MonotoneHalfLineFn g)
    (hc : polarGauge B k y = (c : EReal)) :
    convexConj B (monotoneComp g k) y ≤ monotoneConj g c := by
  have hc0 : (0 : ℝ) ≤ c := by
    have h := polarGauge_nonneg B k y
    rw [hc] at h
    exact EReal.coe_nonneg.1 h
  rw [convexConj_apply, monotoneConj_of_nonneg g hc0]
  refine iSup_le fun z => ?_
  rcases eq_top_or_exists_coe_of_nonneg (hk.nonneg z) with hz | ⟨c', hc'0, hc'⟩
  · rw [monotoneComp_of_eq_top g hz, EReal.sub_top]; exact bot_le
  have hfz : monotoneComp g k z = g c' := monotoneComp_of_eq_coe hg.monotoneOn hc'0 hc'
  have hpair : B z y ≤ c' * c := pairing_le_mul_of_gauge hk hkc hc' hc
  calc ((B z y : ℝ) : EReal) - monotoneComp g k z
      ≤ ((c' * c : ℝ) : EReal) - g c' := by
        rw [hfz]
        exact EReal.sub_le_sub (EReal.coe_le_coe_iff.2 hpair) le_rfl
    _ ≤ ⨆ t : ℝ, ⨆ _ : (0 : ℝ) ≤ t, ((t * c : ℝ) : EReal) - g t :=
        le_trans (le_iSup (fun _ : (0 : ℝ) ≤ c' => ((c' * c : ℝ) : EReal) - g c') hc'0)
          (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t, ((t * c : ℝ) : EReal) - g t) c')

/-- **The conjugacy formula.** Let $E$ be a topological vector space, let $k$ be a closed gauge on
$E$, and let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn` with $g(\zeta) < +\infty$ for some
$\zeta > 0$. Then
$$(g \circ k)^* = g^+ \circ k^\circ.$$
This is the conjugacy formula of Theorem 15.3 of [rockafellar1970convex].

The finiteness hypothesis is used only where $k^\circ(y) = +\infty$, to show that the conjugate
is $+\infty$ there; both inequalities at finite $k^\circ(y)$ hold without it. It cannot be
omitted: for $g$ the indicator of $\{0\}$, the left side is $\delta^*(\cdot \mid \{k \le 0\})$,
which vanishes on the polar of the recession cone of $\{k \le 1\}$, while the right side is
$+\infty$ outside the barrier cone of $\{k \le 1\}$, and these two cones differ. The pairing
need not be continuous or compatible, and $g$ need not be non-constant; the topology of $E$
enters only through the closedness of $k$. -/
theorem convexConj_monotoneComp (hk : IsGauge k) (hkc : ClosedConvex k) (hg : MonotoneHalfLineFn g)
    (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤) :
    convexConj B (monotoneComp g k) = monotoneComp (monotoneConj g) (polarGauge B k) := by
  funext y
  rcases eq_top_or_exists_coe_of_nonneg (polarGauge_nonneg B k y) with htop | ⟨c, hc0, hc⟩
  · rw [monotoneComp_of_eq_top _ htop]
    obtain ⟨ζ, hζ, hζt⟩ := hfin
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.ne_bot ζ)
      (lt_top_iff_ne_top.2 hζt)
    have h := coe_mul_polarGauge_sub_le_convexConj (B := B) (y := y) hk hζ hr
    rw [htop, hr, EReal.coe_mul_top_of_pos hζ, EReal.top_sub_coe] at h
    exact top_le_iff.1 h
  · rw [monotoneComp_of_eq_coe (monotoneHalfLineFn_monotoneConj hg).monotoneOn hc0 hc]
    exact le_antisymm (convexConj_monotoneComp_le hk hkc hg hc)
      (monotoneConj_le_convexConj_monotoneComp hk hg hc)

end GaugeComp

/-!
### The composite $g \circ k$ is a closed proper convex function

Closedness is obtained as in [rockafellar1970convex], by two applications of the conjugacy formula:
$(g \circ k)^{**} = g^{++} \circ k^{\circ\circ} = g \circ k$, and a convex function equal to its
biconjugate is closed. The second application needs $g^+$ to be finite at a positive point, and this
is what the hypothesis that $g$ is not constant gives.
-/

section MonotoneCompClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {g : ℝ → EReal} {k : E → EReal}

/-- Let $E$ be a locally convex space, and let $B$ be a pairing of $E$ with a topological vector
space $F$ that is compatible with the topology of $E$ and for which every
$\langle x, \cdot \rangle$ is continuous. Let $k$ be a closed gauge on $E$, and let $g$ be in
`ConvexAnalysis.MonotoneHalfLineFn` with $g(\zeta) < +\infty$ for some $\zeta > 0$ and
$g(0) < g(t)$ for some $t > 0$. Then $g \circ k$ is closed in the sense of
`ConvexAnalysis.ClosedConvex`.

The conclusion does not mention $B$; the pairing serves the proof, which applies the conjugacy
formula twice. The hypothesis that $g$ is not constant is necessary and enters through
`ConvexAnalysis.MonotoneHalfLineFn.exists_monotoneConj_ne_top`: for constant $g$, the composite
is $g(0)$ on the effective domain of $k$ and $+\infty$ outside it, and the effective domain need
not be closed. -/
theorem closedConvex_monotoneComp (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsContinuousPairing B.flip] (hk : IsGauge k) (hkc : ClosedConvex k) (hg : MonotoneHalfLineFn g)
    (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤) (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) :
    ClosedConvex (monotoneComp g k) := by
  have hpk : IsGauge (polarGauge B k) :=
    isGauge_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero
  have hpkc : ClosedConvex (polarGauge B k) :=
    closedConvex_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero
  have hkc' : convexCl k = k := hkc
  have h1 : convexConj B (monotoneComp g k) = monotoneComp (monotoneConj g) (polarGauge B k) :=
    convexConj_monotoneComp hk hkc hg hfin
  have h2 : convexConj B.flip (monotoneComp (monotoneConj g) (polarGauge B k))
      = monotoneComp (monotoneConj (monotoneConj g)) (polarGauge B.flip (polarGauge B k)) :=
    convexConj_monotoneComp hpk hpkc (monotoneHalfLineFn_monotoneConj hg)
      (MonotoneHalfLineFn.exists_monotoneConj_ne_top hg hne)
  have hbi : convexBiconj B (monotoneComp g k) = monotoneComp g k := by
    change convexConj B.flip (convexConj B (monotoneComp g k)) = monotoneComp g k
    rw [h1, h2, monotoneConj_monotoneConj hg, polarGauge_polarGauge hk, hkc']
  change convexCl (monotoneComp g k) = monotoneComp g k
  rw [← convexBiconj_eq_convexCl (B := B) (convexFn_monotoneComp hg.convex hk.convexFn), hbi]

/-- Let $E$ be a locally convex space, and let $B$ be a pairing of $E$ with a topological vector
space $F$ that is compatible with the topology of $E$ and for which every
$\langle x, \cdot \rangle$ is continuous. Let $k$ be a closed gauge on $E$, and let $g$ be in
`ConvexAnalysis.MonotoneHalfLineFn` with $g(\zeta) < +\infty$ for some $\zeta > 0$ and
$g(0) < g(t)$ for some $t > 0$. Then $g \circ k$ is a closed proper convex function.

The conclusion does not mention $B$; the pairing serves the proof of closedness. -/
theorem closedProperConvexFn_monotoneComp (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsContinuousPairing B.flip] (hk : IsGauge k) (hkc : ClosedConvex k)
    (hg : MonotoneHalfLineFn g) (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) : ClosedProperConvexFn (monotoneComp g k) :=
  ⟨convexFn_monotoneComp hg.convex hk.convexFn,
    closedConvex_monotoneComp B hk hkc hg hfin hne, properConvex_monotoneComp hg hk⟩

end MonotoneCompClosed

/-!
### The powers of the half-line

The functions $\zeta \mapsto \zeta^p / p$ for $1 < p < \infty$. Monotone conjugacy maps the one for
$p$ to the one for the Hölder conjugate exponent $q$; this is Young's inequality, read as a
conjugacy.
-/

section PowHalfLine

variable {p q ζ : ℝ}

/-- The function $\zeta \mapsto \zeta^p / p$ for $\zeta \ge 0$, extended by $+\infty$ to
$(-\infty, 0)$. The power is `Real.rpow`. -/
noncomputable def powHalfLine (p : ℝ) : ℝ → EReal :=
  ConvexAnalysis.convexRestrict (Set.Ici 0) fun ζ => ((ζ ^ p / p : ℝ) : EReal)

/-- For $\zeta \ge 0$, the value is $\zeta^p / p$. -/
@[simp] theorem powHalfLine_of_nonneg (p : ℝ) (hζ : 0 ≤ ζ) :
    powHalfLine p ζ = ((ζ ^ p / p : ℝ) : EReal) := convexRestrict_of_mem hζ

/-- For $\zeta < 0$, the value is $+\infty$. -/
theorem powHalfLine_of_neg (p : ℝ) (hζ : ζ < 0) : powHalfLine p ζ = ⊤ :=
  convexRestrict_of_notMem (by simpa using hζ)

/-- For $\zeta \ge 0$, the value is finite. -/
theorem powHalfLine_ne_top (p : ℝ) (hζ : 0 ≤ ζ) : powHalfLine p ζ ≠ ⊤ := by
  rw [powHalfLine_of_nonneg p hζ]; exact EReal.coe_ne_top _

/-- For $p > 0$, the value at $0$ is $0$. -/
theorem powHalfLine_zero (hp : 0 < p) : powHalfLine p 0 = 0 := by
  rw [powHalfLine_of_nonneg p le_rfl, Real.zero_rpow hp.ne', zero_div, EReal.coe_zero]

/-- For $p > 0$, the function $\zeta \mapsto \zeta^p / p$ is nondecreasing on $[0, \infty)$. -/
theorem monotoneOn_powHalfLine (hp : 0 < p) : MonotoneOn (powHalfLine p) (Set.Ici 0) := by
  intro a ha b hb hab
  rw [powHalfLine_of_nonneg p ha, powHalfLine_of_nonneg p hb, EReal.coe_le_coe_iff]
  have h := Real.rpow_le_rpow ha hab hp.le
  gcongr

/-- For $p > 0$ and $z \ge 0$, $(z^{1/p})^p = z$. -/
theorem rpow_inv_rpow (hp : 0 < p) {z : ℝ} (hz : 0 ≤ z) : (z ^ p⁻¹) ^ p = z := by
  rw [← Real.rpow_mul hz, inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-- For $p > 0$ and $z \ge 0$, $(z^p)^{1/p} = z$. -/
theorem rpow_rpow_inv (hp : 0 < p) {z : ℝ} (hz : 0 ≤ z) : (z ^ p) ^ p⁻¹ = z := by
  rw [← Real.rpow_mul hz, mul_inv_cancel₀ hp.ne', Real.rpow_one]

/-- For $p > 0$ and $z \ge 0$, $z^{1/p} \le 1$ if and only if $z \le 1$. -/
theorem rpow_inv_le_one_iff (hp : 0 < p) {z : ℝ} (hz : 0 ≤ z) : z ^ p⁻¹ ≤ 1 ↔ z ≤ 1 := by
  constructor
  · intro h
    have := Real.rpow_le_rpow (Real.rpow_nonneg hz _) h hp.le
    rwa [rpow_inv_rpow hp hz, Real.one_rpow] at this
  · intro h
    have := Real.rpow_le_rpow hz h (by positivity : (0 : ℝ) ≤ p⁻¹)
    rwa [Real.one_rpow] at this

/-- For $p \ge 1$, the function $\zeta \mapsto \zeta^p / p$ is in
`ConvexAnalysis.MonotoneHalfLineFn`, the class on which monotone conjugacy is an involution. -/
theorem monotoneHalfLineFn_powHalfLine (hp : 1 ≤ p) : MonotoneHalfLineFn (powHalfLine p) where
  top_of_neg _ h := powHalfLine_of_neg p h
  monotoneOn := monotoneOn_powHalfLine (lt_of_lt_of_le zero_lt_one hp)
  convex := by
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
    have h := (convexOn_rpow hp).smul (le_of_lt (one_div_pos.2 hp0))
    have heq : (fun x : ℝ => (1 / p) • x ^ p) = fun x : ℝ => x ^ p / p := by
      funext x; rw [smul_eq_mul, one_div, inv_mul_eq_div]
    rw [heq] at h
    exact (convexOn_iff_convexFn (Set.Ici 0) fun x : ℝ => x ^ p / p).1 h
  closed := by
    have hcont : Continuous fun ζ : ℝ => ((ζ ^ p / p : ℝ) : EReal) :=
      EReal.continuous_coe_iff.2 ((Real.continuous_rpow_const (by linarith)).div_const p)
    exact ClosedConvex.convexRestrict
      ((closedConvex_iff_lowerSemicontinuous fun _ => EReal.coe_ne_bot _).2
        hcont.lowerSemicontinuous)
      (fun _ => EReal.coe_ne_bot _) isClosed_Ici
  zero_ne_top := powHalfLine_ne_top p le_rfl

/-- **Young's inequality as a conjugacy.** Let $p$ and $q$ be Hölder conjugate exponents: $p, q > 1$
and $1/p + 1/q = 1$. Then the monotone conjugate of $\zeta \mapsto \zeta^p / p$ is
$\sigma \mapsto \sigma^q / q$.

The supremum $\sup \{\zeta \sigma - \zeta^p / p : \zeta \ge 0\}$ is at most $\sigma^q / q$ by
Young's inequality, and it is attained at $\zeta = \sigma^{q - 1}$, where
$\zeta \sigma = \zeta^p = \sigma^q$. -/
theorem monotoneConj_powHalfLine (hpq : p.HolderConjugate q) :
    monotoneConj (powHalfLine p) = powHalfLine q := by
  have hp0 : (0 : ℝ) < p := hpq.pos
  have hq0 : (0 : ℝ) < q := hpq.symm.pos
  funext s
  rcases lt_or_ge s 0 with hs | hs
  · rw [monotoneConj_of_neg _ hs, powHalfLine_of_neg _ hs]
  rw [monotoneConj_of_nonneg _ hs, powHalfLine_of_nonneg _ hs]
  refine le_antisymm (iSup_le fun t => iSup_le fun ht => ?_) ?_
  · rw [powHalfLine_of_nonneg p ht, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have := Real.young_inequality_of_nonneg ht hs hpq
    linarith
  · have hq1 : (0 : ℝ) < q - 1 := hpq.symm.sub_one_pos
    have ht₀0 : (0 : ℝ) ≤ s ^ (q - 1) := Real.rpow_nonneg hs _
    have hval : s ^ (q - 1) * s - (s ^ (q - 1)) ^ p / p = s ^ q / q := by
      rcases eq_or_lt_of_le hs with rfl | hspos
      · rw [Real.zero_rpow hq1.ne', Real.zero_rpow hq0.ne', Real.zero_rpow hp0.ne']
        ring
      · have h1 : s ^ (q - 1) * s = s ^ q := by
          have hadd := Real.rpow_add hspos (q - 1) 1
          rw [Real.rpow_one] at hadd
          rw [← hadd]
          norm_num
        have h2 : (s ^ (q - 1)) ^ p = s ^ q := by
          rw [← Real.rpow_mul hs, hpq.symm.sub_one_mul_conj]
        rw [h1, h2]
        have h3 : (1 : ℝ) - p⁻¹ = q⁻¹ := hpq.one_sub_inv
        have h4 : s ^ q - s ^ q / p = s ^ q * (1 - p⁻¹) := by ring
        rw [h4, h3]; ring
    refine le_trans (le_of_eq ?_)
      (le_trans (le_iSup (fun _ : (0 : ℝ) ≤ s ^ (q - 1) =>
          ((s ^ (q - 1) * s : ℝ) : EReal) - powHalfLine p (s ^ (q - 1))) ht₀0)
        (le_iSup (fun t : ℝ => ⨆ _ : (0 : ℝ) ≤ t,
          ((t * s : ℝ) : EReal) - powHalfLine p t) (s ^ (q - 1))))
    rw [powHalfLine_of_nonneg p ht₀0, ← EReal.coe_sub, hval]

end PowHalfLine

/-!
### Positive homogeneity of degree $p$

A function is positively homogeneous of degree $p$ if $f(\lambda x) = \lambda^p f(x)$ for
$\lambda > 0$. For $1 < p < \infty$ the closed proper convex functions of this kind are exactly the
functions $(1/p) k^p$ of a closed gauge $k$, and the gauge is recovered as $(p f)^{1/p}$.
-/

section PosHomogeneousDeg

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f k : E → EReal} {x : E} {p : ℝ}

/-- A function $f : E \to [-\infty, +\infty]$ is **positively homogeneous of degree $p$** if
$f(\lambda x) = \lambda^p f(x)$ for every $\lambda > 0$ and every $x$.

Degree $1$ is `ConvexAnalysis.PosHomogeneous`. As there, only positive scalars are constrained,
so the value at the origin is not determined. -/
def PosHomogeneousDeg (p : ℝ) (f : E → EReal) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ x, f (a • x) = ((a ^ p : ℝ) : EReal) * f x

/-- If $p > 0$ and $f$ is positively homogeneous of degree $p$, then $f(0)$ is $0$, $+\infty$ or
$-\infty$. -/
theorem PosHomogeneousDeg.map_zero_trichotomy (hp : 0 < p) (hf : PosHomogeneousDeg p f) :
    f 0 = 0 ∨ f 0 = ⊤ ∨ f 0 = ⊥ := by
  have h2 : ((2 : ℝ) ^ p) ≠ 1 := by
    have h := Real.rpow_lt_rpow_left_iff (x := 2) (y := 0) (z := p) (by norm_num)
    rw [Real.rpow_zero] at h
    exact ne_of_gt (h.2 hp)
  refine EReal.eq_zero_or_eq_top_or_eq_bot h2 ?_
  have h := hf 2 two_pos 0
  rw [smul_zero] at h
  exact h.symm

/-- Let $p > 1$, and let $f$ be convex, never $-\infty$, positively homogeneous of degree $p$, with
$f(0) = 0$. Then $f$ is nonnegative.

Convexity gives $\lambda^p f(x) \le \lambda f(x)$ for $0 < \lambda < 1$, and
$\lambda^p < \lambda$ there. -/
theorem PosHomogeneousDeg.nonneg (hp : 1 < p) (hconv : ConvexFn f) (hne : ∀ z, f z ≠ ⊥)
    (hf : PosHomogeneousDeg p f) (h0 : f 0 = 0) (x : E) : 0 ≤ f x := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hne x)
    (hcon.trans (by simp : (0 : EReal) < ⊤))
  have ha0 : a < 0 := by rw [ha] at hcon; exact_mod_cast hcon
  have hzero : f (0 : E) ≤ ((0 : ℝ) : EReal) := by rw [h0, EReal.coe_zero]
  have hcombo := hconv.epi_combo (x := x) (y := (0 : E)) (μ := a) (ν := 0) (le_of_eq ha) hzero
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [smul_zero, add_zero, hf _ (by norm_num) x, ha, ← EReal.coe_mul,
    EReal.coe_le_coe_iff] at hcombo
  have hlt : ((1 : ℝ) / 2) ^ p < 1 / 2 := by
    have h := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1) hp
    rwa [Real.rpow_one] at h
  nlinarith [mul_lt_mul_of_neg_left hlt ha0]

/-- If $p > 0$ and $k$ is a gauge, then $(1/p) k^p$ (the composite of $\zeta \mapsto \zeta^p / p$
with $k$) is positively homogeneous of degree $p$. -/
theorem posHomogeneousDeg_monotoneComp_powHalfLine (hp : 0 < p) (hk : IsGauge k) :
    PosHomogeneousDeg p (monotoneComp (powHalfLine p) k) := by
  intro a ha z
  rcases eq_top_or_exists_coe_of_nonneg (hk.nonneg z) with hz | ⟨c, hc0, hz⟩
  · have haz : k (a • z) = ⊤ := by
      rw [hk.posHomogeneous a ha z, hz, EReal.coe_mul_top_of_pos ha]
    rw [monotoneComp_of_eq_top _ haz, monotoneComp_of_eq_top _ hz,
      EReal.coe_mul_top_of_pos (Real.rpow_pos_of_pos ha p)]
  · have haz : k (a • z) = ((a * c : ℝ) : EReal) := by
      rw [hk.posHomogeneous a ha z, hz, ← EReal.coe_mul]
    rw [monotoneComp_of_eq_coe (monotoneOn_powHalfLine hp) (by positivity) haz,
      monotoneComp_of_eq_coe (monotoneOn_powHalfLine hp) hc0 hz,
      powHalfLine_of_nonneg p (by positivity : (0 : ℝ) ≤ a * c), powHalfLine_of_nonneg p hc0,
      ← EReal.coe_mul]
    exact congrArg _ (by rw [Real.mul_rpow ha.le hc0]; ring)

/-- The **gauge attached** to a function $f$ that is positively homogeneous of degree $p$ is
$(p f)^{1/p}$, with $(+\infty)^{1/p} = +\infty$.

It is the composite `ConvexAnalysis.monotoneComp` of $a \mapsto (p a)^{1/p}$ with $f$. For
$p > 0$ it is $(p a)^{1/p}$ where $f$ has the finite value $a \ge 0$, and $+\infty$ where
$f = +\infty$. -/
noncomputable def degGauge (p : ℝ) (f : E → EReal) : E → EReal :=
  monotoneComp (fun a : ℝ => (((p * a) ^ p⁻¹ : ℝ) : EReal)) f

/-- For $p > 0$, the function $a \mapsto (p a)^{1/p}$ is nondecreasing on $[0, \infty)$. -/
theorem monotoneOn_degGaugeFn (hp : 0 < p) :
    MonotoneOn (fun a : ℝ => (((p * a) ^ p⁻¹ : ℝ) : EReal)) (Set.Ici 0) := by
  intro a ha b _ hab
  have ha0 : (0 : ℝ) ≤ a := Set.mem_Ici.1 ha
  rw [EReal.coe_le_coe_iff]
  exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)

omit [AddCommGroup E] [Module ℝ E] in
/-- If $p > 0$ and $f(x) = a$ with $a \ge 0$, then $(p f)^{1/p}(x) = (p a)^{1/p}$. -/
theorem degGauge_of_eq_coe (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) (h : f x = (a : EReal)) :
    degGauge p f x = (((p * a) ^ p⁻¹ : ℝ) : EReal) :=
  monotoneComp_of_eq_coe (monotoneOn_degGaugeFn hp) ha h

omit [AddCommGroup E] [Module ℝ E] in
/-- If $f(x) = +\infty$, then $(p f)^{1/p}(x) = +\infty$. -/
theorem degGauge_of_eq_top (p : ℝ) (h : f x = ⊤) : degGauge p f x = ⊤ :=
  monotoneComp_of_eq_top _ h

omit [AddCommGroup E] [Module ℝ E] in
/-- If $p > 0$ and $f$ is nonnegative, then $(p f)^{1/p}$ is nonnegative. -/
theorem degGauge_nonneg (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) (x : E) : 0 ≤ degGauge p f x := by
  rcases eq_top_or_exists_coe_of_nonneg (hnn x) with hx | ⟨a, ha0, hx⟩
  · rw [degGauge_of_eq_top p hx]; exact le_top
  · rw [degGauge_of_eq_coe hp ha0 hx]
    exact EReal.coe_nonneg.2 (Real.rpow_nonneg (by positivity) _)

omit [Module ℝ E] in
/-- If $p > 0$ and $f(0) = 0$, then $(p f)^{1/p}$ vanishes at $0$. -/
theorem degGauge_map_zero (hp : 0 < p) (h0 : f 0 = 0) : degGauge p f 0 = 0 := by
  rw [degGauge_of_eq_coe hp le_rfl (by rw [h0, EReal.coe_zero]), mul_zero,
    Real.zero_rpow (by positivity), EReal.coe_zero]

/-- If $p > 0$ and $f$ is nonnegative and positively homogeneous of degree $p$, then $(p f)^{1/p}$
is positively homogeneous of degree $1$. -/
theorem posHomogeneous_degGauge (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) (hf : PosHomogeneousDeg p f) :
    PosHomogeneous (degGauge p f) := by
  intro a ha z
  rcases eq_top_or_exists_coe_of_nonneg (hnn z) with hz | ⟨c, hc0, hz⟩
  · have haz : f (a • z) = ⊤ := by
      rw [hf a ha z, hz, EReal.coe_mul_top_of_pos (Real.rpow_pos_of_pos ha p)]
    rw [degGauge_of_eq_top p haz, degGauge_of_eq_top p hz,
      EReal.coe_mul_top_of_pos ha]
  · have haz : f (a • z) = ((a ^ p * c : ℝ) : EReal) := by
      rw [hf a ha z, hz, ← EReal.coe_mul]
    have hac : (0 : ℝ) ≤ a ^ p * c := by positivity
    rw [degGauge_of_eq_coe hp hac haz, degGauge_of_eq_coe hp hc0 hz, ← EReal.coe_mul]
    refine congrArg _ ?_
    have hrw : p * (a ^ p * c) = a ^ p * (p * c) := by ring
    rw [hrw, Real.mul_rpow (Real.rpow_nonneg ha.le p) (by positivity), rpow_rpow_inv hp ha.le]

omit [AddCommGroup E] [Module ℝ E] in
/-- If $p > 0$ and $f$ is nonnegative, then the unit sublevel set of $(p f)^{1/p}$ is
$\{x : f(x) \le 1/p\}$. -/
theorem setOf_degGauge_le_one (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) :
    {x : E | degGauge p f x ≤ 1} = {x : E | f x ≤ ((p⁻¹ : ℝ) : EReal)} := by
  ext z
  rcases eq_top_or_exists_coe_of_nonneg (hnn z) with hz | ⟨a, ha0, hz⟩
  · simp only [Set.mem_ofPred, degGauge_of_eq_top p hz, hz]
    have h1 : ¬ ((⊤ : EReal) ≤ 1) := by
      rw [top_le_iff, ← EReal.coe_one]
      exact EReal.coe_ne_top 1
    have h2 : ¬ ((⊤ : EReal) ≤ ((p⁻¹ : ℝ) : EReal)) := by
      rw [top_le_iff]; exact EReal.coe_ne_top _
    exact iff_of_false h1 h2
  · have hpa : (0 : ℝ) ≤ p * a := by positivity
    have h1 : degGauge p f z ≤ 1 ↔ (p * a) ^ p⁻¹ ≤ 1 := by
      rw [degGauge_of_eq_coe hp ha0 hz,
        show ((1 : EReal)) = ((1 : ℝ) : EReal) from (EReal.coe_one).symm,
        EReal.coe_le_coe_iff]
    have h2 : f z ≤ ((p⁻¹ : ℝ) : EReal) ↔ a ≤ p⁻¹ := by rw [hz, EReal.coe_le_coe_iff]
    change degGauge p f z ≤ 1 ↔ f z ≤ ((p⁻¹ : ℝ) : EReal)
    rw [h1, h2, rpow_inv_le_one_iff hp hpa, ← le_div_iff₀' hp, one_div]

/-- If $p > 0$ and $f$ is nonnegative, positively homogeneous of degree $p$, with $f(0) = 0$, then
$(p f)^{1/p}$ is the gauge $\gamma(\cdot \mid \{x : f(x) \le 1/p\})$. -/
theorem degGauge_eq_gaugeFn (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) (hf : PosHomogeneousDeg p f)
    (h0 : f 0 = 0) : degGauge p f = gaugeFn {x : E | f x ≤ ((p⁻¹ : ℝ) : EReal)} := by
  rw [← setOf_degGauge_le_one hp hnn]
  exact (gaugeFn_level_one (degGauge_nonneg hp hnn) (posHomogeneous_degGauge hp hnn hf)
    (degGauge_map_zero hp h0)).symm

/-- If $p > 0$ and $f$ is convex, nonnegative, positively homogeneous of degree $p$, with
$f(0) = 0$, then $(p f)^{1/p}$ is a gauge.

Convexity follows from the identification with the gauge of the convex set $\{f \le 1/p\}$, not
from the formula. -/
theorem isGauge_degGauge (hp : 0 < p) (hconv : ConvexFn f) (hnn : ∀ z, 0 ≤ f z)
    (hf : PosHomogeneousDeg p f) (h0 : f 0 = 0) : IsGauge (degGauge p f) where
  nonneg := degGauge_nonneg hp hnn
  posHomogeneous := posHomogeneous_degGauge hp hnn hf
  convexFn := by
    rw [degGauge_eq_gaugeFn hp hnn hf h0]
    exact convexFn_gaugeFn (hconv.convex_le _)
  map_zero := degGauge_map_zero hp h0

omit [AddCommGroup E] [Module ℝ E] in
/-- If $p > 0$ and $f$ is nonnegative, then $(1/p) \big[(p f)^{1/p}\big]^p = f$: the attached gauge
recovers $f$. -/
theorem monotoneComp_powHalfLine_degGauge (hp : 0 < p) (hnn : ∀ z, 0 ≤ f z) :
    monotoneComp (powHalfLine p) (degGauge p f) = f := by
  funext z
  rcases eq_top_or_exists_coe_of_nonneg (hnn z) with hz | ⟨a, ha0, hz⟩
  · rw [monotoneComp_of_eq_top _ (degGauge_of_eq_top p hz), hz]
  · have hpa : (0 : ℝ) ≤ p * a := by positivity
    have hd0 : (0 : ℝ) ≤ (p * a) ^ p⁻¹ := Real.rpow_nonneg hpa _
    have hval : ((p * a) ^ p⁻¹) ^ p / p = a := by
      rw [rpow_inv_rpow hp hpa]
      field_simp
    rw [monotoneComp_of_eq_coe (monotoneOn_powHalfLine hp) hd0 (degGauge_of_eq_coe hp ha0 hz),
      powHalfLine_of_nonneg p hd0, hval, hz]

/-- If $p > 0$ and $k$ is a gauge, then $\big(p \cdot (1/p) k^p\big)^{1/p} = k$. Hence the gauge in
the representation $f = (1/p) k^p$ is unique. -/
theorem degGauge_monotoneComp_powHalfLine (hp : 0 < p) (hk : IsGauge k) :
    degGauge p (monotoneComp (powHalfLine p) k) = k := by
  funext z
  rcases eq_top_or_exists_coe_of_nonneg (hk.nonneg z) with hz | ⟨c, hc0, hz⟩
  · rw [degGauge_of_eq_top p (monotoneComp_of_eq_top _ hz), hz]
  · have hval : p * (c ^ p / p) = c ^ p := by field_simp
    rw [degGauge_of_eq_coe (f := monotoneComp (powHalfLine p) k) hp (a := c ^ p / p)
        (by positivity)
        (by rw [monotoneComp_of_eq_coe (monotoneOn_powHalfLine hp) hc0 hz,
          powHalfLine_of_nonneg p hc0]),
      hval, rpow_rpow_inv hp hc0, hz]

end PosHomogeneousDeg

/-!
### Homogeneity of degree $p$ for closed functions

Closedness determines the value at the origin, and with it the sign.
-/

section PosHomogeneousDegClosed

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal} {p : ℝ}

/-- Let $E$ be a topological vector space and $p > 0$. If $f$ is closed, proper, and positively
homogeneous of degree $p$, then $f(0) = 0$.

Along a ray into the origin the values are $\lambda^p f(x_0) \to 0$, so the closed epigraph
contains $(0, 0)$ and $f(0) \le 0$. Homogeneity allows only the values $0$, $+\infty$ and
$-\infty$ at the origin. The bound $f(0) \le 0$ excludes $+\infty$, and properness excludes
$-\infty$. -/
theorem PosHomogeneousDeg.map_zero_eq_zero (hp : 0 < p) (hcl : ClosedConvex f)
    (hpr : ProperConvex f)
    (hf : PosHomogeneousDeg p f) : f 0 = 0 := by
  obtain ⟨x₀, hx₀⟩ := hpr.convexDom_nonempty
  obtain ⟨b, hb⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hpr.ne_bot x₀) hx₀
  have hepi : IsClosed (epi f) :=
    lowerSemicontinuous_iff_isClosed_epi.1 (ClosedConvex.lowerSemicontinuous hcl)
  have hmem : ∀ n : ℕ, ((1 / (n + 1 : ℝ)) • x₀, (1 / (n + 1 : ℝ)) ^ p * b) ∈ epi f := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have h : f ((1 / (n + 1 : ℝ)) • x₀) = (((1 / (n + 1 : ℝ)) ^ p * b : ℝ) : EReal) := by
      rw [hf _ hpos x₀, hb, ← EReal.coe_mul]
    exact le_of_eq h
  have h1 : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) • x₀) Filter.atTop (nhds (0 : E)) := by
    have hc : Continuous fun r : ℝ => r • x₀ := continuous_id.smul continuous_const
    have h := (hc.tendsto (0 : ℝ)).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [zero_smul] at h
  have h2 : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ p * b) Filter.atTop
      (nhds (0 : ℝ)) := by
    have hc : Continuous fun r : ℝ => r ^ p * b :=
      (Real.continuous_rpow_const hp.le).mul continuous_const
    have h := (hc.tendsto (0 : ℝ)).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [Real.zero_rpow hp.ne', zero_mul] at h
  have htend : Filter.Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ)) • x₀, (1 / (n + 1 : ℝ)) ^ p * b))
      Filter.atTop (nhds ((0 : E), (0 : ℝ))) := by
    rw [nhds_prod_eq]
    exact Filter.Tendsto.prodMk h1 h2
  have hzero := hepi.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)
  have hle : f (0 : E) ≤ 0 := by
    have h : f (0 : E) ≤ ((0 : ℝ) : EReal) := hzero
    rwa [EReal.coe_zero] at h
  rcases PosHomogeneousDeg.map_zero_trichotomy hp hf with h | h | h
  · exact h
  · rw [h] at hle; exact absurd hle (by simp)
  · exact absurd h (hpr.ne_bot 0)

/-- Let $E$ be a topological vector space and $p > 0$. If $f$ is convex, closed, nonnegative,
positively homogeneous of degree $p$, with $f(0) = 0$, then $(p f)^{1/p}$ is closed, because it
is the gauge of the closed convex set $\{f \le 1/p\}$. -/
theorem closedConvex_degGauge (hp : 0 < p) (hconv : ConvexFn f) (hcl : ClosedConvex f)
    (hnn : ∀ z, 0 ≤ f z) (hf : PosHomogeneousDeg p f) (h0 : f 0 = 0) :
    ClosedConvex (degGauge p f) := by
  rw [degGauge_eq_gaugeFn hp hnn hf h0]
  refine closedConvex_gaugeFn (hconv.convex_le _) ?_
    (lowerSemicontinuous_iff_isClosed_preimage.1 (ClosedConvex.lowerSemicontinuous hcl) _)
  change f 0 ≤ ((p⁻¹ : ℝ) : EReal)
  rw [h0]
  exact EReal.coe_nonneg.2 (by positivity)

/-- Let $E$ be a topological vector space and $p > 1$. If $f$ is a closed proper convex function
that is positively homogeneous of degree $p$, then
$$f = (1/p) \big[(p f)^{1/p}\big]^p.$$
-/
theorem monotoneComp_powHalfLine_degGauge_eq_self (hp : 1 < p) (hconv : ConvexFn f)
    (hcl : ClosedConvex f) (hpr : ProperConvex f) (hf : PosHomogeneousDeg p f) :
    monotoneComp (powHalfLine p) (degGauge p f) = f :=
  monotoneComp_powHalfLine_degGauge (lt_trans zero_lt_one hp)
    (PosHomogeneousDeg.nonneg hp hconv hpr.ne_bot hf
      (PosHomogeneousDeg.map_zero_eq_zero (lt_trans zero_lt_one hp) hcl hpr hf))

/-- Let $E$ be a topological vector space, let $p > 1$, and let $f$ be a closed proper convex
function on $E$. Then $f$ is positively homogeneous of degree $p$ if and only if $f = (1/p) k^p$
for a closed gauge $k$. This is the first assertion of Corollary 15.3.1 of
[rockafellar1970convex].

The gauge is unique: it is $(p f)^{1/p}$, by `ConvexAnalysis.degGauge_monotoneComp_powHalfLine`.
Here $(1/p) k^p$ is `ConvexAnalysis.monotoneComp (ConvexAnalysis.powHalfLine p) k`. -/
theorem posHomogeneousDeg_iff_exists_isGauge (hp : 1 < p) (hconv : ConvexFn f)
    (hcl : ClosedConvex f)
    (hpr : ProperConvex f) :
    PosHomogeneousDeg p f ↔
      ∃ k : E → EReal, IsGauge k ∧ ClosedConvex k ∧ f = monotoneComp (powHalfLine p) k := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  refine ⟨fun hf => ?_, ?_⟩
  · have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hp0 hcl hpr hf
    have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hp hconv hpr.ne_bot hf h0
    exact ⟨degGauge p f, isGauge_degGauge hp0 hconv hnn hf h0,
      closedConvex_degGauge hp0 hconv hcl hnn hf h0,
      (monotoneComp_powHalfLine_degGauge hp0 hnn).symm⟩
  · rintro ⟨k, hk, -, rfl⟩
    exact posHomogeneousDeg_monotoneComp_powHalfLine hp0 hk

end PosHomogeneousDegClosed

/-!
### Conjugacy for the functions homogeneous of degree $p$

Corollaries 15.3.1 and 15.3.2 of [rockafellar1970convex]: $[(1/p) k^p]^* = (1/q) (k^\circ)^q$, the
gauge $(p f)^{1/p}$ is polar to $(q f^*)^{1/q}$, and the sets $\{f \le 1/p\}$ and $\{f^* \le 1/q\}$
are polar to each other.
-/

section PowConj

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f k : E → EReal} {x : E} {y : F} {p q : ℝ}

/-- Let $E$ be a topological vector space, let $p$ and $q$ be Hölder conjugate exponents, and let
$k$ be a closed gauge on $E$. Then
$$\big[(1/p) k^p\big]^* = (1/q) (k^\circ)^q.$$
This is the second assertion of Corollary 15.3.1 of [rockafellar1970convex].

The proof is `ConvexAnalysis.convexConj_monotoneComp` with
`ConvexAnalysis.monotoneConj_powHalfLine`. -/
theorem convexConj_monotoneComp_powHalfLine (hpq : p.HolderConjugate q) (hk : IsGauge k)
    (hkc : ClosedConvex k) :
    convexConj B (monotoneComp (powHalfLine p) k)
        = monotoneComp (powHalfLine q) (polarGauge B k) := by
  rw [convexConj_monotoneComp hk hkc (monotoneHalfLineFn_powHalfLine hpq.lt.le)
      ⟨1, one_pos, powHalfLine_ne_top p zero_le_one⟩,
    monotoneConj_powHalfLine hpq]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If $k$ is a gauge, then the unit sublevel set of $k^\circ$ is the polar of the unit sublevel set
of $k$: $\{y : k^\circ(y) \le 1\} = \{x : k(x) \le 1\}^\circ$. -/
theorem setOf_polarGauge_le_one (hk : IsGauge k) :
    {y : F | polarGauge B k y ≤ 1} = polarSet B {x : E | k x ≤ 1} := by
  rw [polarGauge_eq_supportFn hk.nonneg hk.posHomogeneous hk.map_zero]
  ext z
  change supportFn B {x : E | k x ≤ 1} z ≤ 1 ↔ z ∈ polarSet B {x : E | k x ≤ 1}
  rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) from (EReal.coe_one).symm,
    supportFn_le_coe_iff, mem_polarSet]

variable (hpq : p.HolderConjugate q) (hconv : ConvexFn f) (hcl : ClosedConvex f)
    (hpr : ProperConvex f)
  (hf : PosHomogeneousDeg p f)
include hpq hconv hcl hpr hf

/-- Let $E$ be a topological vector space, let $p$ and $q$ be Hölder conjugate exponents, and let
$f$ be a closed proper convex function on $E$ that is positively homogeneous of degree $p$. Then
$f^* = (1/q) (k^\circ)^q$ for the gauge $k = (p f)^{1/p}$. In particular $f^*$ is positively
homogeneous of degree $q$. -/
theorem convexConj_eq_monotoneComp_powHalfLine :
    convexConj B f = monotoneComp (powHalfLine q) (polarGauge B (degGauge p f)) := by
  have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hpq.pos hcl hpr hf
  have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hpq.lt hconv hpr.ne_bot hf h0
  conv_lhs => rw [← monotoneComp_powHalfLine_degGauge hpq.pos hnn]
  exact convexConj_monotoneComp_powHalfLine hpq (isGauge_degGauge hpq.pos hconv hnn hf h0)
    (closedConvex_degGauge hpq.pos hconv hcl hnn hf h0)

/-- Let $E$ be a topological vector space, let $p$ and $q$ be Hölder conjugate exponents, and let
$f$ be a closed proper convex function on $E$ that is positively homogeneous of degree $p$. Then
the polar of the closed gauge $(p f)^{1/p}$ is $(q f^*)^{1/q}$:
$$\big((p f)^{1/p}\big)^\circ = (q f^*)^{1/q}.$$
This is Corollary 15.3.2 of [rockafellar1970convex]. -/
theorem polarGauge_degGauge : polarGauge B (degGauge p f) = degGauge q (convexConj B f) := by
  have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hpq.pos hcl hpr hf
  have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hpq.lt hconv hpr.ne_bot hf h0
  rw [convexConj_eq_monotoneComp_powHalfLine (B := B) hpq hconv hcl hpr hf,
    degGauge_monotoneComp_powHalfLine hpq.symm.pos
      (isGauge_polarGauge (B := B) (degGauge_nonneg hpq.pos hnn)
        (posHomogeneous_degGauge hpq.pos hnn hf) (degGauge_map_zero hpq.pos h0))]

/-- **Hölder-type inequality.** Let $E$ be a topological vector space, let $p$ and $q$ be Hölder
conjugate exponents, and let $f$ be a closed proper convex function on $E$ that is positively
homogeneous of degree $p$. If $f(x) = a$ and $f^*(y) = b$ are finite, then
$$\langle x, y \rangle \le (p a)^{1/p} (q b)^{1/q}.$$
This is part of Corollary 15.3.2 of [rockafellar1970convex]. -/
theorem pairing_le_rpow_mul_rpow {a b : ℝ} (hx : f x = (a : EReal))
    (hy : convexConj B f y = (b : EReal)) : B x y ≤ (p * a) ^ p⁻¹ * (q * b) ^ q⁻¹ := by
  have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hpq.pos hcl hpr hf
  have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hpq.lt hconv hpr.ne_bot hf h0
  have ha0 : (0 : ℝ) ≤ a := by
    have h := hnn x
    rw [hx] at h
    exact EReal.coe_nonneg.1 h
  have hb0 : (0 : ℝ) ≤ b := by
    have h := zero_le_convexConj (B := B) (le_of_eq h0) y
    rw [hy] at h
    exact EReal.coe_nonneg.1 h
  refine pairing_le_mul_of_gauge (isGauge_degGauge hpq.pos hconv hnn hf h0)
    (closedConvex_degGauge hpq.pos hconv hcl hnn hf h0) (degGauge_of_eq_coe hpq.pos ha0 hx) ?_
  rw [polarGauge_degGauge hpq hconv hcl hpr hf]
  exact degGauge_of_eq_coe hpq.symm.pos hb0 hy

/-- Let $E$ be a topological vector space, let $p$ and $q$ be Hölder conjugate exponents, and let
$f$ be a closed proper convex function on $E$ that is positively homogeneous of degree $p$. Then
the closed convex sets $\{f \le 1/p\}$ and $\{f^* \le 1/q\}$ are polar to each other:
$$\{x : f(x) \le 1/p\}^\circ = \{y : f^*(y) \le 1/q\}.$$
This is part of Corollary 15.3.2 of [rockafellar1970convex]. -/
theorem polarSet_setOf_le_inv :
    polarSet B {x : E | f x ≤ ((p⁻¹ : ℝ) : EReal)}
      = {y : F | convexConj B f y ≤ ((q⁻¹ : ℝ) : EReal)} := by
  have h0 : f 0 = 0 := PosHomogeneousDeg.map_zero_eq_zero hpq.pos hcl hpr hf
  have hnn : ∀ z, 0 ≤ f z := PosHomogeneousDeg.nonneg hpq.lt hconv hpr.ne_bot hf h0
  have hcnn : ∀ z, 0 ≤ convexConj B f z := fun z => zero_le_convexConj (le_of_eq h0) z
  rw [← setOf_degGauge_le_one hpq.pos hnn, ← setOf_polarGauge_le_one
      (isGauge_degGauge hpq.pos hconv hnn hf h0),
    polarGauge_degGauge hpq hconv hcl hpr hf, setOf_degGauge_le_one hpq.symm.pos hcnn]

end PowConj


/-!
### Gauge-like functions, and the converse

A function $f$ is **gauge-like** if $f(0) = \inf f$ and the sublevel sets $\{f \le \alpha\}$ above
the infimum are positive multiples of one set. By `ConvexAnalysis.setOf_monotoneComp_le_eq_smul`,
$g \circ k$ is gauge-like. This section proves the converse: a gauge-like closed proper convex
function is such a composite.

The gauge is $k = \gamma(\cdot \mid \{f \le f(0) + 1\})$. Every sublevel set of $f$ above the
infimum is then a sublevel set of $k$ (`ConvexAnalysis.IsGaugeLike.exists_isGauge_setOf_le_eq`), so
$f(x)$ depends on $x$ only through $k(x)$. The factor on the half-line is read off along a ray,
$g(\zeta) = f(\zeta x_1)$ with $k(x_1) = 1$, which makes $g$ convex and closed. Such a ray exists
unless $k$ takes only the values $0$ and $+\infty$, that is, unless the sublevel sets are one cone.
In that case $f$ is $f(0)$ on the cone and $+\infty$ outside it, and the factor on the half-line is
the step function $f(0) + \delta(\cdot \mid [0, 1])$.
-/

section IsGaugeLike

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f k : E → EReal} {a₀ : ℝ}

/-- A function $f : E \to [-\infty, +\infty]$ is **gauge-like**, in the sense of
[rockafellar1970convex], if its infimum is attained at the origin and there is a set $C$ such
that every sublevel set $\{f \le \alpha\}$ with $\alpha > f(0)$ is $\lambda C$ for some
$\lambda > 0$. -/
structure IsGaugeLike (f : E → EReal) : Prop where
  /-- The infimum of $f$ is $f(0)$. -/
  map_zero_eq_iInf : f 0 = ⨅ x, f x
  /-- There is a set $C$ such that for every real $\alpha > f(0)$ the sublevel set
  $\{f \le \alpha\}$ is $\lambda C$ for some $\lambda > 0$. -/
  exists_setOf_le_eq_smul : ∃ C : Set E, ∀ α : ℝ, f 0 < (α : EReal) →
    ∃ l : ℝ, 0 < l ∧ {x : E | f x ≤ (α : EReal)} = l • C

/-- The origin minimizes a gauge-like function: $f(0) \le f(x)$. -/
theorem IsGaugeLike.map_zero_le (hgl : IsGaugeLike f) (x : E) : f 0 ≤ f x := by
  rw [hgl.map_zero_eq_iInf]
  exact iInf_le f x

/-- Let $f$ be gauge-like, and let $\alpha, \beta > f(0)$ be real. Then
$\{f \le \alpha\} = c \{f \le \beta\}$ for some $c > 0$. This form needs no reference to the
auxiliary set. -/
theorem IsGaugeLike.exists_setOf_le_eq_smul_setOf_le (hgl : IsGaugeLike f) {α β : ℝ}
    (hα : f 0 < (α : EReal)) (hβ : f 0 < (β : EReal)) :
    ∃ c : ℝ, 0 < c ∧ {x : E | f x ≤ (α : EReal)} = c • {x : E | f x ≤ (β : EReal)} := by
  obtain ⟨C, hC⟩ := hgl.exists_setOf_le_eq_smul
  obtain ⟨a, ha, hseta⟩ := hC α hα
  obtain ⟨b, hb, hsetb⟩ := hC β hβ
  refine ⟨a / b, by positivity, ?_⟩
  rw [hseta, hsetb, smul_smul, div_mul_cancel₀ _ hb.ne']

/-- If $f$ is gauge-like and proper, then $f(0)$ is a real number. It is not $-\infty$ because $f$
is proper, and it is not $+\infty$ because it is at most every value of $f$. -/
theorem IsGaugeLike.exists_map_zero_eq_coe (hgl : IsGaugeLike f) (hpr : ProperConvex f) :
    ∃ a : ℝ, f 0 = (a : EReal) := by
  obtain ⟨x, hx⟩ := hpr.convexDom_nonempty
  exact EReal.exists_coe_of_ne_bot_of_lt_top (hpr.ne_bot 0)
    (lt_of_le_of_lt (hgl.map_zero_le x) (mem_convexDom.1 hx))

omit [AddCommGroup E] [Module ℝ E] in
/-- Let $f$ be never $-\infty$, with $a_0 \le f(x)$ for every $x$. Assume that for every real
$\alpha > a_0$ there is $c > 0$ with $\{f \le \alpha\} = \{k \le c\}$. Then $k(u) \le k(v)$
implies $f(u) \le f(v)$: $f$ is a nondecreasing function of $k$. -/
theorem le_of_forall_setOf_le_eq (hbot : ∀ x, f x ≠ ⊥) (hmin : ∀ x, (a₀ : EReal) ≤ f x)
    (hlev : ∀ α : ℝ, a₀ < α → ∃ c : ℝ, 0 < c ∧
      {x : E | f x ≤ (α : EReal)} = {x : E | k x ≤ (c : EReal)})
    (u v : E) (huv : k u ≤ k v) : f u ≤ f v := by
  rcases eq_or_lt_of_le (le_top (a := f v)) with htop | hlt
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot v) hlt
  rw [hr]
  refine le_coe_of_forall_gt_le fun d hd => ?_
  have ha₀ : a₀ < d := by
    have hr' : (a₀ : EReal) ≤ (r : EReal) := by rw [← hr]; exact hmin v
    exact lt_of_le_of_lt (EReal.coe_le_coe_iff.1 hr') hd
  obtain ⟨c, -, hset⟩ := hlev d ha₀
  have hv : k v ≤ (c : EReal) := by
    have hmem : v ∈ {x : E | f x ≤ (d : EReal)} := by
      change f v ≤ (d : EReal)
      rw [hr]
      exact_mod_cast hd.le
    rwa [hset] at hmem
  have hu : u ∈ {x : E | f x ≤ (d : EReal)} := by
    rw [hset]
    exact le_trans huv hv
  exact hu

omit [AddCommGroup E] [Module ℝ E] in
/-- Under the hypotheses of `ConvexAnalysis.le_of_forall_setOf_le_eq`, $k(u) = +\infty$ implies
$f(u) = +\infty$. A finite value of $f$ at $u$ would put $u$ in a sublevel set of $k$. -/
theorem eq_top_of_forall_setOf_le_eq (hbot : ∀ x, f x ≠ ⊥) (hmin : ∀ x, (a₀ : EReal) ≤ f x)
    (hlev : ∀ α : ℝ, a₀ < α → ∃ c : ℝ, 0 < c ∧
      {x : E | f x ≤ (α : EReal)} = {x : E | k x ≤ (c : EReal)})
    (u : E) (hu : k u = ⊤) : f u = ⊤ := by
  by_contra hne
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot u) (lt_top_iff_ne_top.2 hne)
  have ha₀ : a₀ ≤ r := by
    have hr' : (a₀ : EReal) ≤ (r : EReal) := by rw [← hr]; exact hmin u
    exact EReal.coe_le_coe_iff.1 hr'
  obtain ⟨c, -, hset⟩ := hlev (r + 1) (by linarith)
  have hmem : u ∈ {x : E | f x ≤ ((r + 1 : ℝ) : EReal)} := by
    change f u ≤ ((r + 1 : ℝ) : EReal)
    rw [hr]
    exact_mod_cast (by linarith : r ≤ r + 1)
  rw [hset] at hmem
  have hc : (⊤ : EReal) ≤ (c : EReal) := by
    have hmem' : k u ≤ (c : EReal) := hmem
    rwa [hu] at hmem'
  exact absurd (top_le_iff.1 hc) (EReal.coe_ne_top c)

/-- A gauge $k$ either takes the value $1$ at some point, or takes only the values $0$ and
$+\infty$. In the second case its sublevel sets are one cone. -/
theorem IsGauge.exists_eq_one_or_forall_eq_zero_or_eq_top (hk : IsGauge k) :
    (∃ x₁ : E, k x₁ = 1) ∨ ∀ x : E, k x = 0 ∨ k x = ⊤ := by
  by_cases hray : ∃ x₁ : E, k x₁ = 1
  · exact Or.inl hray
  refine Or.inr fun x => ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨hne0, hnetop⟩ := hcon
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hk.ne_bot x)
    (lt_top_iff_ne_top.2 hnetop)
  have hr0 : (0 : ℝ) ≤ r := by
    have h := hk.nonneg x
    rw [hr] at h
    exact_mod_cast h
  have hrne : r ≠ 0 := fun h => hne0 (by rw [hr, h, EReal.coe_zero])
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
  refine hray ⟨r⁻¹ • x, ?_⟩
  rw [hk.posHomogeneous r⁻¹ (inv_pos.2 hrpos) x, hr, ← EReal.coe_mul,
    inv_mul_cancel₀ hrne, EReal.coe_one]

end IsGaugeLike

section IsGaugeLikeTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {f : E → EReal} {g : ℝ → EReal} {k : E → EReal}

/-- Let $E$ be a topological vector space, and let $f$ be gauge-like, convex and closed with
$f(0) = a_0$ real. Then there is a closed gauge $k$ such that for every real $\alpha > a_0$
there is $c > 0$ with $\{f \le \alpha\} = \{k \le c\}$. -/
theorem IsGaugeLike.exists_isGauge_setOf_le_eq (hgl : IsGaugeLike f) (hconv : ConvexFn f)
    (hcl : ClosedConvex f) {a₀ : ℝ} (h0 : f 0 = (a₀ : EReal)) :
    ∃ k : E → EReal, IsGauge k ∧ ClosedConvex k ∧ ∀ α : ℝ, a₀ < α → ∃ c : ℝ, 0 < c ∧
      {x : E | f x ≤ (α : EReal)} = {x : E | k x ≤ (c : EReal)} := by
  have hβ : f 0 < ((a₀ + 1 : ℝ) : EReal) := by
    rw [h0]
    exact_mod_cast lt_add_one a₀
  have hD0 : (0 : E) ∈ {x : E | f x ≤ ((a₀ + 1 : ℝ) : EReal)} := le_of_lt hβ
  have hDconv : Convex ℝ {x : E | f x ≤ ((a₀ + 1 : ℝ) : EReal)} := hconv.convex_le _
  have hDcl : IsClosed {x : E | f x ≤ ((a₀ + 1 : ℝ) : EReal)} :=
    (ClosedConvex.lowerSemicontinuous hcl).isClosed_preimage _
  refine ⟨gaugeFn {x : E | f x ≤ ((a₀ + 1 : ℝ) : EReal)}, isGauge_gaugeFn hDconv ⟨0, hD0⟩,
    closedConvex_gaugeFn hDconv hD0 hDcl, fun α hα => ?_⟩
  have hα' : f 0 < (α : EReal) := by
    rw [h0]
    exact_mod_cast hα
  obtain ⟨c, hc, hset⟩ := hgl.exists_setOf_le_eq_smul_setOf_le hα' hβ
  exact ⟨c, hc, by rw [hset, setOf_gaugeFn_le_pos hDconv hD0 hDcl hc]⟩

/-- Let $E$ be a topological vector space, and let $f$ be a gauge-like closed proper convex function
on $E$. Then $f = g \circ k$ for a closed gauge $k$ and a function $g$ in
`ConvexAnalysis.MonotoneHalfLineFn` with $g(0) < g(t)$ for some $t > 0$ and $g(\zeta) < +\infty$
for some $\zeta > 0$. This is the converse half of Theorem 15.3 of [rockafellar1970convex]. -/
theorem IsGaugeLike.exists_eq_monotoneComp (hgl : IsGaugeLike f) (hconv : ConvexFn f)
    (hcl : ClosedConvex f) (hpr : ProperConvex f) :
    ∃ (g : ℝ → EReal) (k : E → EReal), MonotoneHalfLineFn g ∧
      (∃ t : ℝ, 0 < t ∧ g 0 < g t) ∧ (∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤) ∧
      IsGauge k ∧ ClosedConvex k ∧ f = monotoneComp g k := by
  obtain ⟨a₀, h0⟩ := hgl.exists_map_zero_eq_coe hpr
  obtain ⟨k, hkg, hkc, hlev⟩ := hgl.exists_isGauge_setOf_le_eq hconv hcl h0
  have hmin : ∀ x, (a₀ : EReal) ≤ f x := fun x => by
    rw [← h0]
    exact hgl.map_zero_le x
  have hmono : ∀ u v : E, k u ≤ k v → f u ≤ f v :=
    le_of_forall_setOf_le_eq hpr.ne_bot hmin hlev
  have htop : ∀ u : E, k u = ⊤ → f u = ⊤ :=
    eq_top_of_forall_setOf_le_eq hpr.ne_bot hmin hlev
  obtain ⟨c₁, hc₁, hset₁⟩ := hlev (a₀ + 1) (lt_add_one a₀)
  rcases hkg.exists_eq_one_or_forall_eq_zero_or_eq_top with ⟨x₁, hx₁⟩ | hcone
  · -- The generic case: `k` takes the value `1`, and the half-line factor is `f` along the ray.
    have hkray : ∀ t : ℝ, 0 ≤ t → k (t • x₁) = (t : EReal) := by
      intro t ht
      rcases eq_or_lt_of_le ht with rfl | htpos
      · rw [zero_smul, hkg.map_zero, EReal.coe_zero]
      · rw [hkg.posHomogeneous t htpos x₁, hx₁, mul_one]
    have hAcont : Continuous ((LinearMap.toSpanSingleton ℝ E x₁ : ℝ →ₗ[ℝ] E) : ℝ → E) := by
      have hc : Continuous fun t : ℝ => t • x₁ := continuous_id.smul continuous_const
      exact hc
    set gray : ℝ → EReal :=
      ConvexAnalysis.convexRestrict (Set.Ici 0) (compLin f (LinearMap.toSpanSingleton ℝ E x₁))
      with hgray
    have hgval : ∀ t : ℝ, 0 ≤ t → gray t = f (t • x₁) := fun t ht =>
      convexRestrict_of_mem (Set.mem_Ici.2 ht)
    have hgmono : MonotoneOn gray (Set.Ici 0) := by
      intro s hs t ht hst
      rw [hgval s (Set.mem_Ici.1 hs), hgval t (Set.mem_Ici.1 ht)]
      refine hmono _ _ ?_
      rw [hkray s (Set.mem_Ici.1 hs), hkray t (Set.mem_Ici.1 ht)]
      exact_mod_cast hst
    have hg0 : gray 0 = (a₀ : EReal) := by rw [hgval 0 le_rfl, zero_smul, h0]
    refine ⟨gray, k, ⟨fun t ht => convexRestrict_of_notMem (by simpa using not_le.2 ht), hgmono,
      ConvexFn.convexRestrict (convexFn_compLin _ hconv) (convex_Ici 0),
      ClosedConvex.convexRestrict (closedConvex_compLin hcl hAcont) (fun _ => hpr.ne_bot _)
          isClosed_Ici,
      by rw [hg0]; exact EReal.coe_ne_top a₀⟩, ⟨c₁ + 1, by linarith, ?_⟩,
      ⟨c₁, hc₁, ?_⟩, hkg, hkc, ?_⟩
    · have hnot : ¬ k ((c₁ + 1) • x₁) ≤ (c₁ : EReal) := by
        rw [hkray _ (by linarith : (0 : ℝ) ≤ c₁ + 1)]
        exact_mod_cast (by linarith : ¬ c₁ + 1 ≤ c₁)
      have hnotf : ¬ f ((c₁ + 1) • x₁) ≤ ((a₀ + 1 : ℝ) : EReal) := fun hmem => hnot (by
        have hmem' : ((c₁ + 1) • x₁) ∈ {x : E | f x ≤ ((a₀ + 1 : ℝ) : EReal)} := hmem
        rwa [hset₁] at hmem')
      rw [hg0, hgval _ (by linarith : (0 : ℝ) ≤ c₁ + 1)]
      refine lt_of_lt_of_le ?_ (not_le.1 hnotf).le
      exact_mod_cast lt_add_one a₀
    · have hkm : (c₁ • x₁) ∈ {x : E | k x ≤ (c₁ : EReal)} := le_of_eq (hkray _ hc₁.le)
      rw [← hset₁] at hkm
      have hkm' : f (c₁ • x₁) ≤ ((a₀ + 1 : ℝ) : EReal) := hkm
      rw [hgval _ hc₁.le]
      exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hkm'
    · funext x
      rcases eq_top_or_exists_coe_of_nonneg (hkg.nonneg x) with hx | ⟨c, hc0, hx⟩
      · rw [monotoneComp_of_eq_top _ hx]
        exact htop x hx
      · rw [monotoneComp_of_eq_coe hgmono hc0 hx, hgval c hc0]
        refine le_antisymm (hmono _ _ (le_of_eq ?_)) (hmono _ _ (le_of_eq ?_))
        · rw [hx, hkray c hc0]
        · rw [hx, hkray c hc0]
  · -- The degenerate case: the sublevel sets are a single cone, and the factor is a step function.
    set gstep : ℝ → EReal :=
      ConvexAnalysis.convexRestrict (Set.Icc (0 : ℝ) 1) (fun _ => (a₀ : EReal)) with hgstep
    have hgin : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → gstep t = (a₀ : EReal) :=
      fun _ ht => convexRestrict_of_mem ht
    have hgout : ∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → gstep t = ⊤ :=
        fun _ ht => convexRestrict_of_notMem ht
    have hzero : gstep 0 = (a₀ : EReal) := hgin 0 (Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩)
    have hgmono : MonotoneOn gstep (Set.Ici 0) := by
      intro s hs t _ hst
      by_cases htm : t ∈ Set.Icc (0 : ℝ) 1
      · rw [hgin t htm,
          hgin s (Set.mem_Icc.2 ⟨Set.mem_Ici.1 hs, le_trans hst (Set.mem_Icc.1 htm).2⟩)]
      · rw [hgout t htm]
        exact le_top
    refine ⟨gstep, k, ⟨fun t ht => hgout t fun h => absurd (Set.mem_Icc.1 h).1 (not_le.2 ht),
      hgmono, ConvexFn.convexRestrict (convexFn_const _) (convex_Icc 0 1),
      ClosedConvex.convexRestrict ((closedConvex_iff_lowerSemicontinuous
        (fun _ => EReal.coe_ne_bot a₀)).2 lowerSemicontinuous_const)
        (fun _ => EReal.coe_ne_bot a₀) isClosed_Icc,
      by rw [hzero]; exact EReal.coe_ne_top a₀⟩, ⟨2, by norm_num, ?_⟩,
      ⟨1, one_pos, ?_⟩, hkg, hkc, ?_⟩
    · rw [hzero, hgout 2 (by norm_num)]
      exact EReal.coe_lt_top a₀
    · rw [hgin 1 (Set.mem_Icc.2 ⟨zero_le_one, le_rfl⟩)]
      exact EReal.coe_ne_top a₀
    · funext x
      rcases hcone x with hx | hx
      · rw [monotoneComp_of_eq_coe hgmono le_rfl (by rw [hx, EReal.coe_zero]), hzero, ← h0]
        exact le_antisymm (hmono x 0 (by rw [hx, hkg.map_zero])) (hgl.map_zero_le x)
      · rw [monotoneComp_of_eq_top _ hx]
        exact htop x hx

/-- Let $E$ be a topological vector space, let $k$ be a closed gauge on $E$, and let $g$ be in
`ConvexAnalysis.MonotoneHalfLineFn` with $g(0) < g(t)$ for some $t > 0$ and $g(\zeta) < +\infty$
for some $\zeta > 0$. Then $g \circ k$ is gauge-like. This is
`ConvexAnalysis.setOf_monotoneComp_le_eq_smul` with the auxiliary set named. -/
theorem isGaugeLike_monotoneComp (hk : IsGauge k) (hkc : ClosedConvex k) (hg : MonotoneHalfLineFn g)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤) :
    IsGaugeLike (monotoneComp g k) := by
  have h0 : monotoneComp g k (0 : E) = g 0 :=
    monotoneComp_of_eq_coe hg.monotoneOn le_rfl (by rw [hk.map_zero, EReal.coe_zero])
  refine ⟨?_, ⟨{x : E | k x ≤ 1}, fun α hα => ?_⟩⟩
  · refine le_antisymm (le_iInf fun x => ?_) (iInf_le _ 0)
    rw [h0]
    exact le_iInf fun t => le_iInf fun _ => hg.zero_le t
  · rw [h0] at hα
    exact ⟨levelSup g α, levelSup_pos hg hne hfin hα,
      setOf_monotoneComp_le_eq_smul hk hkc hg hne hfin hα⟩

end IsGaugeLikeTopology

/-!
### The characterization of gauge-like functions

The two halves together. The pairing enters only through the forward implication, where the
closedness of $g \circ k$ comes from the Fenchel–Moreau theorem.
-/

section Characterisation

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {f : E → EReal}

omit [LocallyConvexSpace ℝ E] in
/-- Let $E$ and $F$ be topological vector spaces, let every $\langle x, \cdot \rangle$ be continuous
on $F$, let $k$ be a closed gauge on $E$, and let $g$ be in `ConvexAnalysis.MonotoneHalfLineFn`
with $g(\zeta) < +\infty$ for some $\zeta > 0$ and $g(0) < g(t)$ for some $t > 0$. Then the
conjugate $(g \circ k)^*$ is gauge-like. This is part of Theorem 15.3 of
[rockafellar1970convex].

`ConvexAnalysis.convexConj_monotoneComp` identifies the conjugate as $g^+ \circ k^\circ$. It
remains to check that $g^+$ satisfies the two side conditions of $g$, and conjugacy exchanges
them: $g$ finite at a positive point makes $g^+$ non-constant, and $g$ non-constant makes $g^+$
finite at a positive point. -/
theorem isGaugeLike_convexConj_monotoneComp (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B.flip]
    {g : ℝ → EReal} {k : E → EReal} (hk : IsGauge k) (hkc : ClosedConvex k)
    (hg : MonotoneHalfLineFn g) (hfin : ∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) : IsGaugeLike (convexConj B (monotoneComp g k)) := by
  rw [convexConj_monotoneComp hk hkc hg hfin]
  exact isGaugeLike_monotoneComp (isGauge_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero)
    (closedConvex_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero)
    (monotoneHalfLineFn_monotoneConj hg) (MonotoneHalfLineFn.exists_lt_monotoneConj hg hfin)
    (MonotoneHalfLineFn.exists_monotoneConj_ne_top hg hne)

/-- Let $E$ be a locally convex space, and let $B$ be a pairing of $E$ with a topological vector
space $F$ that is compatible with the topology of $E$ and for which every
$\langle x, \cdot \rangle$ is continuous. A function $f$ on $E$ is a gauge-like closed proper
convex function if and only if $f = g \circ k$ for a closed gauge $k$ and a function $g$ in
`ConvexAnalysis.MonotoneHalfLineFn` with $g(0) < g(t)$ for some $t > 0$ and $g(\zeta) < +\infty$
for some $\zeta > 0$. This is the first assertion of Theorem 15.3 of [rockafellar1970convex].

The conclusion does not mention $B$; the pairing serves the proof of closedness in the forward
direction. The conjugacy formula of the theorem is `ConvexAnalysis.convexConj_monotoneComp`,
$(g \circ k)^* = g^+ \circ k^\circ$, which needs neither the hypotheses on the pairing nor that
$g$ is non-constant. -/
theorem closedProperConvexFn_and_isGaugeLike_iff (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsContinuousPairing B.flip] :
    (ClosedProperConvexFn f ∧ IsGaugeLike f) ↔
      ∃ (g : ℝ → EReal) (k : E → EReal),
        (MonotoneHalfLineFn g ∧ (∃ t : ℝ, 0 < t ∧ g 0 < g t) ∧ (∃ ζ : ℝ, 0 < ζ ∧ g ζ ≠ ⊤)) ∧
        (IsGauge k ∧ ClosedConvex k) ∧ f = monotoneComp g k := by
  constructor
  · rintro ⟨⟨hconv, hcl, hpr⟩, hgl⟩
    obtain ⟨g, k, hgm, hne, hfin, hkg, hkc, hf⟩ := hgl.exists_eq_monotoneComp hconv hcl hpr
    exact ⟨g, k, ⟨hgm, hne, hfin⟩, ⟨hkg, hkc⟩, hf⟩
  · rintro ⟨g, k, ⟨hgm, hne, hfin⟩, ⟨hkg, hkc⟩, rfl⟩
    exact ⟨closedProperConvexFn_monotoneComp B hkg hkc hgm hfin hne,
      isGaugeLike_monotoneComp hkg hkc hgm hne hfin⟩

end Characterisation

end ConvexAnalysis
