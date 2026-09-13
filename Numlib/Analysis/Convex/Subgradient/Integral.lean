import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Numlib.Analysis.Convex.Subgradient.Differentiability

/-!
# A convex function of one variable is the integral of its derivative

On an open interval where it is finite, a convex function is recovered from either of its one-sided
derivatives by integration, `f y - f x = ∫ₓʸ f'₊(t) dt = ∫ₓʸ f'₋(t) dt`.

## Main results

* `sub_eq_intervalIntegral_derivWithin_Ioi` — the statement for a real-valued convex function on
  an open convex subset of the line. This is the theorem; the rest is translation.
* `rightDeriv_eq_coe_derivWithin` — at an interior point of `dom f`, the `EReal`-valued
  `rightDeriv` is the coercion of Mathlib's `derivWithin f (Ioi t) t`.
* `sub_eq_intervalIntegral_rightDeriv`, `sub_eq_intervalIntegral_leftDeriv` — both halves for an
  `EReal`-valued `f` (Corollary 24.2.1 in [^1]).

## Implementation notes

The fundamental theorem of calculus applies unchanged: a convex function is continuous on the
interior of its domain, has a right derivative at every interior point, and that derivative is
nondecreasing, hence integrable on compacts. No a.e. differentiability is needed. `rightDeriv f t`
is an infimum of difference quotients where Mathlib's right derivative is a limit; the two agree at
*interior* points of `dom f`, which is why interiority rather than finiteness of `f t` is asked.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24.
-/

open Set MeasureTheory intervalIntegral

namespace ConvexAnalysis

/-! ### The real-valued case -/

section Real

variable {S : Set ℝ} {g : ℝ → ℝ} {x y : ℝ}

/-- A real-valued convex function on an open convex subset of the line is the integral of its right
derivative. `S` is asked to be open and convex rather than a non-empty open interval; in `ℝ` these
are the same. -/
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

/-! ### The bridge to `rightDeriv` -/

section Bridge

variable {f : ℝ → EReal} {t : ℝ}

/-- A difference quotient of `f` in the direction `1`, taken between two points where `f` is
finite, is the coercion of Mathlib's `slope`. No order relation between the points is needed. -/
theorem sub_div_eq_coe_slope (hb : f t ≠ ⊥) (ht : f t ≠ ⊤) {z : ℝ} (hz : z ∈ dom f)
    (hzb : f z ≠ ⊥) :
    (f (t + (z - t) • (1 : ℝ)) - f t) / ((z - t : ℝ) : EReal)
      = ((slope (fun w => (f w).toReal) t z : ℝ) : EReal) := by
  have hzt : t + (z - t) • (1 : ℝ) = z := by rw [smul_eq_mul, mul_one]; ring
  rw [hzt, ← EReal.coe_toReal (mem_dom.1 hz).ne hzb, ← EReal.coe_toReal ht hb,
    ← EReal.coe_sub, ← EReal.coe_div, slope_def_field]

/-- At an interior point of `dom f`, the `EReal` infimum of difference quotients `rightDeriv f t`
is the coercion of Mathlib's `derivWithin f (Ioi t) t`. Both are the infimum of the slopes
`slope f t z` over the `z > t` at which `f` is finite. -/
theorem rightDeriv_eq_coe_derivWithin (hf : ConvexFn f) (hp : Proper f)
    (ht : t ∈ interior (dom f)) :
    rightDeriv f t = ((derivWithin (fun z => (f z).toReal) (Ioi t) t : ℝ) : EReal) := by
  have htdom : t ∈ dom f := interior_subset ht
  have httop : f t ≠ ⊤ := (mem_dom.1 htdom).ne
  have htbot : f t ≠ ⊥ := hp.ne_bot t
  have hgc : ConvexOn ℝ (dom f) fun z => (f z).toReal := hf.convexOn_toReal_dom hp
  have hsInf : derivWithin (fun z => (f z).toReal) (Ioi t) t
      = sInf (slope (fun z => (f z).toReal) t '' {z | z ∈ dom f ∧ t < z}) :=
    hgc.rightDeriv_eq_sInf_slope_of_mem_interior ht
  have hbdd : BddBelow (slope (fun z => (f z).toReal) t '' {z | z ∈ dom f ∧ t < z}) :=
    bddBelow_slope_lt_of_mem_interior hgc ht
  -- `t` is interior, so `dom f` has points immediately to the right of it.
  obtain ⟨u, v, htuv, huvs⟩ := mem_nhds_iff_exists_Ioo_subset.1 (mem_interior_iff_mem_nhds.1 ht)
  obtain ⟨w, htw, hwv⟩ := exists_between htuv.2
  have hwT : w ∈ {z | z ∈ dom f ∧ t < z} := ⟨huvs ⟨htuv.1.trans htw, hwv⟩, htw⟩
  have hne : (slope (fun z => (f z).toReal) t '' {z | z ∈ dom f ∧ t < z}).Nonempty :=
    ⟨_, ⟨w, hwT, rfl⟩⟩
  rw [rightDeriv_of_exists ⟨w, htw, mem_dom.1 hwT.1⟩]
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
    by_cases hz : t + a • (1 : ℝ) ∈ dom f
    · have hmem : t + a ∈ {z | z ∈ dom f ∧ t < z} := ⟨by rwa [hstep] at hz, by linarith⟩
      have hquot := sub_div_eq_coe_slope (f := f) htbot httop hmem.1 (hp.ne_bot _)
      rw [show t + a - t = a by ring] at hquot
      rw [hquot, hsInf, EReal.coe_le_coe_iff]
      exact csInf_le hbdd ⟨t + a, hmem, rfl⟩
    · rw [top_le_iff.1 (not_lt.1 fun h => hz (mem_dom.2 h)),
        ← EReal.coe_toReal httop htbot, EReal.top_sub_coe,
        EReal.top_div_of_pos_ne_top (by exact_mod_cast ha) (EReal.coe_ne_top a)]
      exact le_top

end Bridge

/-! ### The `EReal`-valued form -/

section EReal

variable {f : ℝ → EReal} {x y : ℝ}

/-- **Right-derivative half**: on the interior of its effective domain, a proper convex function on
the line is the integral of `f'₊`. -/
theorem sub_eq_intervalIntegral_rightDeriv (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) (hy : y ∈ interior (dom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (rightDeriv f t).toReal := by
  have hconv : Convex ℝ (interior (dom f)) := hf.convex_dom.interior
  have hg : ConvexOn ℝ (interior (dom f)) fun z => (f z).toReal :=
    (hf.convexOn_toReal_dom hp).subset interior_subset hconv
  rw [sub_eq_intervalIntegral_derivWithin_Ioi hg isOpen_interior hx hy]
  refine integral_congr fun t ht => ?_
  have htint : t ∈ interior (dom f) := (convex_iff_ordConnected.1 hconv).uIcc_subset hx hy ht
  rw [rightDeriv_eq_coe_derivWithin hf hp htint, EReal.toReal_coe]

/-- **Left-derivative half**. The two one-sided derivatives differ only on the jump set of `f'₊`,
which is countable and therefore null. -/
theorem sub_eq_intervalIntegral_leftDeriv (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) (hy : y ∈ interior (dom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (leftDeriv f t).toReal := by
  rw [sub_eq_intervalIntegral_rightDeriv hf hp hx hy]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ t : ℝ, leftDeriv f t = rightDeriv f t :=
    MeasureTheory.ae_iff.2 ((countable_leftDeriv_ne_rightDeriv hf hp).measure_zero volume)
  filter_upwards [hae] with t ht _
  rw [ht]

end EReal

end ConvexAnalysis
