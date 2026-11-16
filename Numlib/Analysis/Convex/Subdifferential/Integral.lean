/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Numlib.Analysis.Convex.Subdifferential.Differentiability

/-!
# A convex function of one variable is the integral of its derivative

On an open interval where it is finite, a convex function $f$ on the line is the integral of either
of its one-sided derivatives $f'_+$ and $f'_-$:
$$f(y) - f(x) = \int_x^y f'_+(t) \, dt = \int_x^y f'_-(t) \, dt.$$
This is Corollary 24.2.1 of [rockafellar1970convex]. The module proves it first for a real-valued
convex function with Mathlib's one-sided derivatives, and then translates it to a function with
values in $[-\infty, +\infty]$ and the one-sided derivatives `ConvexAnalysis.rightDeriv` and
`ConvexAnalysis.leftDeriv`.

## Main results

* `ConvexAnalysis.sub_eq_intervalIntegral_derivWithin_Ioi`: a real-valued convex function on an open
  convex subset of the line is the integral of its right derivative.
* `ConvexAnalysis.rightDeriv_eq_coe_derivWithin`, `ConvexAnalysis.leftDeriv_eq_coe_derivWithin`: at
  an interior point of $\operatorname{dom} f$, the extended-real right (left) derivative is
  Mathlib's derivative within the interval to the right (left) of the point.
* `ConvexAnalysis.sub_eq_intervalIntegral_rightDeriv`,
  `ConvexAnalysis.sub_eq_intervalIntegral_leftDeriv`: a proper convex function is the integral of
  $f'_+$, and of $f'_-$, between interior points of its effective domain ([rockafellar1970convex],
  Corollary 24.2.1).

## Implementation notes

* The fundamental theorem of calculus applies as it is. A convex function is continuous on the
  interior of its effective domain and has a right derivative at every interior point, and this
  derivative is nondecreasing, so it is integrable on compact intervals. No almost-everywhere
  differentiability is needed.
* `ConvexAnalysis.rightDeriv f t` is an infimum of difference quotients, while Mathlib's right
  derivative is a limit. The two agree at interior points of $\operatorname{dom} f$. Therefore the
  results ask that the points be interior, not only that $f$ be finite there.
-/

open Set MeasureTheory intervalIntegral

namespace ConvexAnalysis

/-! ### Real-valued functions -/

section Real

variable {S : Set ℝ} {g : ℝ → ℝ} {x y : ℝ}

/-- Let $S \subseteq \mathbb{R}$ be open, and let $g \colon \mathbb{R} \to \mathbb{R}$ be convex on
$S$ (which includes that $S$ is convex). Then for all $x, y \in S$,
$$g(y) - g(x) = \int_x^y g'_+(t) \, dt,$$
where $g'_+(t)$ is the right derivative `derivWithin g (Ioi t) t`.

In $\mathbb{R}$, an open convex set is the same as an open interval, possibly empty or
unbounded. -/
theorem sub_eq_intervalIntegral_derivWithin_Ioi (hg : ConvexOn ℝ S g) (hS : IsOpen S)
    (hx : x ∈ S) (hy : y ∈ S) :
    g y - g x = ∫ t in x..y, derivWithin g (Ioi t) t := by
  have hsub' : uIcc x y ⊆ interior S := by
    rw [hS.interior_eq]
    exact (convex_iff_ordConnected.1 hg.1).uIcc_subset hx hy
  have hcont : ContinuousOn g (uIcc x y) := hg.continuousOn_interior.mono hsub'
  have hderiv : ∀ t ∈ Ioo (min x y) (max x y),
      HasDerivWithinAt g (derivWithin g (Ioi t) t) (Ioi t) t := fun t ht =>
    hg.hasDerivWithinAt_rightDeriv_of_mem_interior (hsub' (Ioo_subset_Icc_self ht))
  have hint : IntervalIntegrable (fun t => derivWithin g (Ioi t) t) volume x y :=
    (hg.monotoneOn_rightDeriv.mono hsub').intervalIntegrable
  exact (integral_eq_sub_of_hasDeriv_right hcont hderiv hint).symm

end Real

/-! ### One-sided derivatives as Mathlib derivatives -/

section Bridge

variable {f : ℝ → EReal} {t : ℝ}

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be finite at $t$ and at $z$. Then the
difference quotient $(f(t + (z - t) \cdot 1) - f(t))/(z - t)$, computed in $[-\infty, +\infty]$,
is the real slope of the real-valued function `fun w => (f w).toReal` between $t$ and $z$. No
order between $t$ and $z$ is needed. -/
theorem sub_div_eq_coe_slope (hb : f t ≠ ⊥) (ht : f t ≠ ⊤) {z : ℝ} (hz : z ∈ convexDom f)
    (hzb : f z ≠ ⊥) :
    (f (t + (z - t) • (1 : ℝ)) - f t) / ((z - t : ℝ) : EReal)
      = ((slope (fun w => (f w).toReal) t z : ℝ) : EReal) := by
  have hzt : t + (z - t) • (1 : ℝ) = z := by rw [smul_eq_mul, mul_one]; ring
  rw [hzt, ← EReal.coe_toReal (mem_convexDom.1 hz).ne hzb, ← EReal.coe_toReal ht hb,
    ← EReal.coe_sub, ← EReal.coe_div, slope_def_field]

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a proper convex function, and let $t$ be in
the interior of $\operatorname{dom} f$. Then $f'_+(t)$ is real, and it is the right derivative
of the real-valued function $f$ at $t$:
$$f'_+(t) = \lim_{z \downarrow t} \frac{f(z) - f(t)}{z - t}.$$

The left-hand side is `ConvexAnalysis.rightDeriv f t`, an infimum of difference quotients in
$[-\infty, +\infty]$. The right-hand side is `derivWithin (fun z => (f z).toReal) (Ioi t) t`.
Both are the infimum of the slopes from $t$ to the points $z > t$ at which $f$ is finite. -/
theorem rightDeriv_eq_coe_derivWithin (hf : ConvexFn f) (hp : ProperConvex f)
    (ht : t ∈ interior (convexDom f)) :
    rightDeriv f t = ((derivWithin (fun z => (f z).toReal) (Ioi t) t : ℝ) : EReal) := by
  have htdom : t ∈ convexDom f := interior_subset ht
  have httop : f t ≠ ⊤ := (mem_convexDom.1 htdom).ne
  have htbot : f t ≠ ⊥ := hp.ne_bot t
  have hgc : ConvexOn ℝ (convexDom f) fun z => (f z).toReal := hf.convexOn_toReal_convexDom hp
  have hsInf : derivWithin (fun z => (f z).toReal) (Ioi t) t
      = sInf (slope (fun z => (f z).toReal) t '' {z | z ∈ convexDom f ∧ t < z}) :=
    hgc.rightDeriv_eq_sInf_slope_of_mem_interior ht
  have hbdd : BddBelow (slope (fun z => (f z).toReal) t '' {z | z ∈ convexDom f ∧ t < z}) :=
    bddBelow_slope_lt_of_mem_interior hgc ht
  -- `t` is interior, so `dom f` has points immediately to the right of it.
  obtain ⟨u, v, htuv, huvs⟩ := mem_nhds_iff_exists_Ioo_subset.1 (mem_interior_iff_mem_nhds.1 ht)
  obtain ⟨w, htw, hwv⟩ := exists_between htuv.2
  have hwT : w ∈ {z | z ∈ convexDom f ∧ t < z} := ⟨huvs ⟨htuv.1.trans htw, hwv⟩, htw⟩
  have hne : (slope (fun z => (f z).toReal) t '' {z | z ∈ convexDom f ∧ t < z}).Nonempty :=
    ⟨_, ⟨w, hwT, rfl⟩⟩
  rw [rightDeriv_of_exists ⟨w, htw, mem_convexDom.1 hwT.1⟩]
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨m, hm1, hm2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    rw [hsInf, EReal.coe_lt_coe_iff] at hm1
    obtain ⟨-, ⟨z, hzT, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hm1
    have hle := dirDeriv_le f t 1 (sub_pos.2 hzT.2)
    rw [sub_div_eq_coe_slope htbot httop hzT.1 (hp.ne_bot z)] at hle
    exact absurd (hle.trans_lt (by exact_mod_cast hlt)) (not_lt.2 hm2.le)
  · refine le_dirDeriv fun a ha => ?_
    have hstep : t + a • (1 : ℝ) = t + a := by rw [smul_eq_mul, mul_one]
    by_cases hz : t + a • (1 : ℝ) ∈ convexDom f
    · have hmem : t + a ∈ {z | z ∈ convexDom f ∧ t < z} := ⟨by rwa [hstep] at hz, by linarith⟩
      have hquot := sub_div_eq_coe_slope (f := f) htbot httop hmem.1 (hp.ne_bot _)
      rw [show t + a - t = a by ring] at hquot
      rw [hquot, hsInf, EReal.coe_le_coe_iff]
      exact csInf_le hbdd ⟨t + a, hmem, rfl⟩
    · rw [top_le_iff.1 (not_lt.1 fun h => hz (mem_convexDom.2 h)),
        ← EReal.coe_toReal httop htbot, EReal.top_sub_coe,
        EReal.top_div_of_pos_ne_top (by exact_mod_cast ha) (EReal.coe_ne_top a)]
      exact le_top

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a proper convex function, and let $t$ be in
the interior of $\operatorname{dom} f$. Then $f'_-(t)$ is real, and it is the left derivative of
the real-valued function $f$ at $t$:
$$f'_-(t) = \lim_{z \uparrow t} \frac{f(z) - f(t)}{z - t}.$$

The left-hand side is `ConvexAnalysis.leftDeriv f t`, and the right-hand side is
`derivWithin (fun z => (f z).toReal) (Iio t) t`. The proof applies
`ConvexAnalysis.rightDeriv_eq_coe_derivWithin` to the reflected function $t \mapsto f(-t)$. -/
theorem leftDeriv_eq_coe_derivWithin (hf : ConvexFn f) (hp : ProperConvex f)
    (ht : t ∈ interior (convexDom f)) :
    leftDeriv f t = ((derivWithin (fun z => (f z).toReal) (Iio t) t : ℝ) : EReal) := by
  have ht' : -t ∈ interior ((Homeomorph.neg ℝ) ⁻¹' convexDom f) := by
    rw [← Homeomorph.preimage_interior]; simpa using ht
  rw [leftDeriv_eq_neg_rightDeriv_comp_neg,
    rightDeriv_eq_coe_derivWithin (f := fun z => f (-z)) hf.comp_neg
      hp.comp_neg ht',
    derivWithin_comp_neg (f := fun z => (f z).toReal), neg_neg, neg_Ioi, neg_neg, EReal.coe_neg,
    neg_neg]

end Bridge

/-! ### Extended-real-valued functions -/

section EReal

variable {f : ℝ → EReal} {x y : ℝ}

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a proper convex function, and let $x$ and
$y$ be in the interior of $\operatorname{dom} f$. Then
$$f(y) - f(x) = \int_x^y f'_+(t) \, dt.$$
This is Corollary 24.2.1 of [rockafellar1970convex] for the right derivative.

The values $f(x)$, $f(y)$ and $f'_+(t)$ are finite, and the statement is for their real parts
`EReal.toReal`. -/
theorem sub_eq_intervalIntegral_rightDeriv (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) (hy : y ∈ interior (convexDom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (rightDeriv f t).toReal := by
  have hconv : Convex ℝ (interior (convexDom f)) := hf.convex_convexDom.interior
  have hg : ConvexOn ℝ (interior (convexDom f)) fun z => (f z).toReal :=
    (hf.convexOn_toReal_convexDom hp).subset interior_subset hconv
  rw [sub_eq_intervalIntegral_derivWithin_Ioi hg isOpen_interior hx hy]
  refine integral_congr fun t ht => ?_
  have htint : t ∈ interior (convexDom f) := (convex_iff_ordConnected.1 hconv).uIcc_subset hx hy ht
  rw [rightDeriv_eq_coe_derivWithin hf hp htint, EReal.toReal_coe]

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a proper convex function, and let $x$ and
$y$ be in the interior of $\operatorname{dom} f$. Then
$$f(y) - f(x) = \int_x^y f'_-(t) \, dt.$$
This is Corollary 24.2.1 of [rockafellar1970convex] for the left derivative.

The two one-sided derivatives differ only on a countable set, which has measure zero. The values
are read as real numbers with `EReal.toReal`. -/
theorem sub_eq_intervalIntegral_leftDeriv (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) (hy : y ∈ interior (convexDom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (leftDeriv f t).toReal := by
  rw [sub_eq_intervalIntegral_rightDeriv hf hp hx hy]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ t : ℝ, leftDeriv f t = rightDeriv f t :=
    MeasureTheory.ae_iff.2 ((countable_leftDeriv_ne_rightDeriv hf hp).measure_zero volume)
  filter_upwards [hae] with t ht _
  rw [ht]

end EReal

end ConvexAnalysis
