/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/MultiIndex.lean`; the slab inequality for `C^1` functions belongs beside
`Mathlib.Analysis.FunctionalSpaces.SobolevInequality`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Chart
import Numlib.Analysis.Sobolev.Cutoff

/-!
# Poincaré's inequality on `W_0^{1,p}(Ω)`

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Corollary 9.19
and the second clause of Remark 21: for `1 ≤ p < ∞` and a bounded open set `Ω ⊆ ℝ^N` — or merely
one with a bounded projection on the last axis, `Ω ⊆ {a < x_N < b}` — every `u ∈ W_0^{1,p}(Ω)`
satisfies `‖u‖_{L^p(Ω)} ≤ C ‖∇u‖_{L^p(Ω)}`, so that `‖∇u‖_p` is a norm on `W_0^{1,p}(Ω)` equivalent
to the norm of `W^{1,p}(Ω)`.

The book states the corollary without proof (in the printed text it follows Remark 20, which
routes it through the Sobolev embedding of `W_0^{1,p}`); the proof here is the elementary one,
which needs neither the extension operator nor compactness. For a `C^1` function `u` supported
in the slab `{a < x_N < b}`, the fundamental theorem of calculus along the last coordinate gives
`u(x', x_N) = ∫_a^{x_N} ∂_N u(x', t) dt`, so `|u(x)| ≤ ∫_a^b |∂_N u(x', t)| dt`, Jensen's inequality
gives `|u(x)|^p ≤ (b − a)^{p−1} ∫_a^b |∂_N u(x', t)|^p dt`, and integrating over `x` (Fubini along
the last coordinate, `EuclideanSpace.lintegral_lastInit`) gives `‖u‖_p ≤ (b − a) ‖∂_N u‖_p`. The
test functions are dense in `W_0^{1,p}(Ω)` by definition and both sides are continuous on
`W^{1,p}(Ω)`, which gives the inequality on `W_0^{1,p}(Ω)`. The constant is the width `b − a` of
the slab, hence `2R` for `Ω ⊆ B(0, R)`; the book says only "`C` depending on `Ω` and `p`".

## Main results

* `eLpNorm_le_eLpNorm_fderiv_apply_of_subset_slab`: the inequality for a `C^1` function supported
  in a slab, with constant `b − a`;
* `SobolevEuclideanZero.norm_fnL_le_of_subset_slab` and
  `SobolevEuclideanZero.eLpNorm_fn_le_of_subset_slab`: Corollary 9.19 / Remark 21 (bounded
  projection on the last axis) on `W_0^{1,p}(Ω)`;
* `SobolevEuclideanZero.eLpNorm_fn_le_of_isBounded`: **Corollary 9.19**, `Ω ⊆ B(0, R)`, with
  `C = 2R`;
* `SobolevEuclideanZero.norm_le_gradNorm`: the gradient norm is an equivalent norm on
  `W_0^{1,p}(Ω)` for bounded `Ω`, `‖u‖ ≤ (1 + (2R)^p)^{1/p} ‖∇u‖_p`.

## References

[brezis2011functional], Corollary 9.19 and Remark 21.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

/-! ### The slab inequality for `C^1` functions -/

section Slab

variable {d : ℕ} {p : ℝ≥0∞}

/-- The slab `{a < x_N < b}` of `ℝ^{d+1}`, the set of points whose last coordinate lies in
`(a, b)`. -/
def EuclideanSpace.slab (d : ℕ) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x | a < x (Fin.last d) ∧ x (Fin.last d) < b}

/-- Membership of the slab, unfolded. -/
theorem EuclideanSpace.mem_slab {a b : ℝ} {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ EuclideanSpace.slab d a b ↔ a < x (Fin.last d) ∧ x (Fin.last d) < b :=
  Iff.rfl

/-- A point of the slab, written through the last-coordinate splitting, has its last coordinate
in `(a, b)`. -/
theorem EuclideanSpace.snocLast_mem_slab_iff {a b t : ℝ} {x' : EuclideanSpace ℝ (Fin d)} :
    EuclideanSpace.snocLast x' t ∈ EuclideanSpace.slab d a b ↔ a < t ∧ t < b := by
  simp [EuclideanSpace.mem_slab]

/-- Moving along the last coordinate from `snocLast x' 0`. -/
theorem EuclideanSpace.snocLast_eq_add_smul_single (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    EuclideanSpace.snocLast x' t
      = EuclideanSpace.snocLast x' 0 + t • EuclideanSpace.single (Fin.last d) 1 := by
  ext i
  induction i using Fin.lastCases <;> simp [Fin.castSucc_ne_last]

/-- **Poincaré's inequality for a `C^1` function supported in a slab**: for `1 ≤ p < ∞` and
`u : ℝ^{d+1} → ℝ` of class `C^1` with `tsupport u ⊆ {a < x_N < b}`,
`‖u‖_p ≤ (b − a) ‖∂_N u‖_p`, where `∂_N u = fderiv ℝ u · e_N`. The fundamental theorem of
calculus along the last coordinate from `a`, where `u = 0`, Jensen's inequality on `(a, b)`, and
Fubini along the last coordinate (`EuclideanSpace.lintegral_lastInit`). This is the argument of
[brezis2011functional] Corollary 9.19 in its elementary form. -/
theorem eLpNorm_le_eLpNorm_fderiv_apply_of_subset_slab (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hu : ContDiff ℝ 1 u) {a b : ℝ}
    (hsupp : tsupport u ⊆ EuclideanSpace.slab d a b) :
    eLpNorm u p volume ≤ ENNReal.ofReal (b - a) *
      eLpNorm (fun x ↦ fderiv ℝ u x (EuclideanSpace.single (Fin.last d) 1)) p volume := by
  set e : EuclideanSpace ℝ (Fin (d + 1)) := EuclideanSpace.single (Fin.last d) 1 with hedef
  set g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ := fun x ↦ fderiv ℝ u x e with hgdef
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hP1 : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have huc : Continuous u := hu.continuous
  have hgc : Continuous g := (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- `u` vanishes off the slab
  have hzero : ∀ x, x ∉ EuclideanSpace.slab d a b → u x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp h)
  -- the derivative of `u` along the last coordinate
  have hderiv : ∀ (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ),
      HasDerivAt (fun s ↦ u (EuclideanSpace.snocLast x' s))
        (g (EuclideanSpace.snocLast x' t)) t := by
    intro x' t
    have h1 : HasDerivAt (fun s : ℝ ↦ EuclideanSpace.snocLast x' s) e t := by
      have heq : (fun s : ℝ ↦ EuclideanSpace.snocLast x' s)
          = fun s ↦ EuclideanSpace.snocLast x' 0 + s • e := by
        funext s
        exact EuclideanSpace.snocLast_eq_add_smul_single x' s
      rw [heq]
      exact (((hasDerivAt_id' t).smul_const e).const_add (EuclideanSpace.snocLast x' 0)).congr_deriv
        (one_smul ℝ e)
    have h2 := (hu.differentiable one_ne_zero (EuclideanSpace.snocLast x' t)).hasFDerivAt
    exact h2.comp_hasDerivAt t h1
  -- the pointwise bound by the integral over `(a, b)`
  have hpt : ∀ (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ), ‖u (EuclideanSpace.snocLast x' t)‖ₑ
      ≤ ∫⁻ s in Ioc a b, ‖g (EuclideanSpace.snocLast x' s)‖ₑ := by
    intro x' t
    by_cases ht : a < t ∧ t < b
    · have hint : IntervalIntegrable (fun s ↦ g (EuclideanSpace.snocLast x' s)) volume a t :=
        (hgc.comp (EuclideanSpace.continuous_snocLast.comp
          (Continuous.prodMk_right x'))).intervalIntegrable _ _
      have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s ↦ u (EuclideanSpace.snocLast x' s)) (fun s _ ↦ hderiv x' s) hint
      have hua : u (EuclideanSpace.snocLast x' a) = 0 :=
        hzero _ (by simp [EuclideanSpace.snocLast_mem_slab_iff])
      rw [hua, sub_zero] at hfund
      rw [← hfund, intervalIntegral.integral_of_le ht.1.le]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      exact lintegral_mono_set (Ioc_subset_Ioc_right ht.2.le)
    · rw [hzero _ (by simpa [EuclideanSpace.snocLast_mem_slab_iff] using ht), enorm_zero]
      exact zero_le
  -- Jensen's inequality on `(a, b)`
  have hIab : (volume : Measure ℝ) (Ioc a b) = ENNReal.ofReal (b - a) := Real.volume_Ioc
  have hjensen : ∀ x' : EuclideanSpace ℝ (Fin d),
      (∫⁻ s in Ioc a b, ‖g (EuclideanSpace.snocLast x' s)‖ₑ) ^ p.toReal
        ≤ ENNReal.ofReal (b - a) ^ (p.toReal - 1)
          * ∫⁻ s in Ioc a b, ‖g (EuclideanSpace.snocLast x' s)‖ₑ ^ p.toReal := by
    intro x'
    have hgm : Measurable fun s : ℝ ↦ ‖g (EuclideanSpace.snocLast x' s)‖ₑ :=
      (hgc.comp (EuclideanSpace.continuous_snocLast.comp
        (Continuous.prodMk_right x'))).measurable.enorm
    have key := ENNReal.rpow_lintegral_mul_le (μ := volume) hP1
      (w := (Ioc a b).indicator fun _ ↦ (1 : ℝ≥0∞))
      (h := fun s ↦ ‖g (EuclideanSpace.snocLast x' s)‖ₑ)
      (measurable_const.indicator measurableSet_Ioc).aemeasurable hgm.aemeasurable
    have e1 : ∀ h : ℝ → ℝ≥0∞, (∫⁻ s, (Ioc a b).indicator (fun _ ↦ (1 : ℝ≥0∞)) s * h s)
        = ∫⁻ s in Ioc a b, h s := fun h ↦ by
      rw [← lintegral_indicator measurableSet_Ioc]
      congr 1
      funext s
      by_cases hs : s ∈ Ioc a b <;> simp [hs]
    have e2 : (∫⁻ s, (Ioc a b).indicator (fun _ ↦ (1 : ℝ≥0∞)) s) = ENNReal.ofReal (b - a) := by
      rw [lintegral_indicator_const measurableSet_Ioc, one_mul, hIab]
    rw [e1, e1, e2] at key
    exact key
  -- the integrand of `‖u‖_p^p` along each line
  have hline : ∀ x' : EuclideanSpace ℝ (Fin d),
      (∫⁻ t, ‖u (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal)
        ≤ ENNReal.ofReal (b - a) ^ p.toReal
          * ∫⁻ t, ‖g (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal := by
    intro x'
    have hbound : ∀ t, ‖u (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal
        ≤ (Ioc a b).indicator (fun _ ↦
          (∫⁻ s in Ioc a b, ‖g (EuclideanSpace.snocLast x' s)‖ₑ) ^ p.toReal) t := by
      intro t
      by_cases ht : t ∈ Ioc a b
      · rw [Set.indicator_of_mem ht]
        exact ENNReal.rpow_le_rpow (hpt x' t) hP.le
      · rw [Set.indicator_of_notMem ht, hzero _ ?_, enorm_zero, ENNReal.zero_rpow_of_pos hP]
        rw [EuclideanSpace.snocLast_mem_slab_iff]
        rintro ⟨h1, h2⟩
        exact ht ⟨h1, h2.le⟩
    calc (∫⁻ t, ‖u (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal)
        ≤ ∫⁻ t, (Ioc a b).indicator (fun _ ↦
            (∫⁻ s in Ioc a b, ‖g (EuclideanSpace.snocLast x' s)‖ₑ) ^ p.toReal) t :=
          lintegral_mono hbound
      _ = ENNReal.ofReal (b - a)
            * (∫⁻ s in Ioc a b, ‖g (EuclideanSpace.snocLast x' s)‖ₑ) ^ p.toReal := by
          rw [lintegral_indicator_const measurableSet_Ioc, hIab, mul_comm]
      _ ≤ ENNReal.ofReal (b - a) * (ENNReal.ofReal (b - a) ^ (p.toReal - 1)
            * ∫⁻ s in Ioc a b, ‖g (EuclideanSpace.snocLast x' s)‖ₑ ^ p.toReal) := by
          gcongr
          exact hjensen x'
      _ = ENNReal.ofReal (b - a) ^ p.toReal
            * ∫⁻ s in Ioc a b, ‖g (EuclideanSpace.snocLast x' s)‖ₑ ^ p.toReal := by
          rw [← mul_assoc]
          congr 1
          have hrp : ENNReal.ofReal (b - a) * ENNReal.ofReal (b - a) ^ (p.toReal - 1)
              = ENNReal.ofReal (b - a) ^ p.toReal := by
            conv_rhs => rw [show p.toReal = 1 + (p.toReal - 1) by ring]
            rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
          exact hrp
      _ ≤ ENNReal.ofReal (b - a) ^ p.toReal
            * ∫⁻ t, ‖g (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal := by
          gcongr
          exact Measure.restrict_le_self
  -- Fubini along the last coordinate
  have hum : AEMeasurable fun x ↦ ‖u x‖ₑ ^ p.toReal :=
    (huc.measurable.enorm.pow_const _).aemeasurable
  have hgm : AEMeasurable fun x ↦ ‖g x‖ₑ ^ p.toReal :=
    (hgc.measurable.enorm.pow_const _).aemeasurable
  have hmain : (∫⁻ x, ‖u x‖ₑ ^ p.toReal)
      ≤ ENNReal.ofReal (b - a) ^ p.toReal * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
    rw [EuclideanSpace.lintegral_lastInit _ hum, EuclideanSpace.lintegral_lastInit _ hgm,
      ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top)]
    exact lintegral_mono fun x' ↦ hline x'
  -- conclusion
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' huc.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hgc.aestronglyMeasurable]
  calc (∫⁻ x, ‖u x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal (b - a) ^ p.toReal * ∫⁻ x, ‖g x‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = ENNReal.ofReal (b - a) * (∫⁻ x, ‖g x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hP.ne', ENNReal.rpow_one]

end Slab

/-! ### Poincaré's inequality on `W_0^{1,p}(Ω)` -/

/-! ### Poincaré's inequality on `W_0^{1,p}(Ω)` -/

section Typed

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The last vector of the standard basis of `ℝ^{d+1}` is `e_N`. -/
theorem EuclideanSpace.basisFun_toBasis_last :
    ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis :
        Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1))) (Fin.last d)
      = EuclideanSpace.single (Fin.last d) 1 := by
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]

/-- A subset of the ball of radius `R` lies in the slab `{−R < x_N < R}`. -/
theorem EuclideanSpace.subset_slab_of_subset_ball {R : ℝ} {s : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hs : s ⊆ ball 0 R) : s ⊆ EuclideanSpace.slab d (-R) R := by
  intro x hx
  have hnorm : ‖x‖ < R := by simpa using hs hx
  have hcoord : |x (Fin.last d)| ≤ ‖x‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le x (Fin.last d)
  rw [EuclideanSpace.mem_slab]
  exact abs_lt.1 (hcoord.trans_lt hnorm)

namespace SobolevEuclideanZero

/-- **Poincaré's inequality for a test function in a slab, on the typed space**: for an element
`w` of `W^{1,p}(Ω)` whose function is a test function on `Ω ⊆ {a < x_N < b}`,
`‖w‖_{L^p(Ω)} ≤ (b − a) ‖∂_N w‖_{L^p(Ω)}`. The slab inequality applied to the test function, which
is a `C^1` function on `ℝ^{d+1}` supported in `Ω`. -/
theorem norm_fnL_le_of_mem_testFunctions (hp' : p ≠ ⊤) {a b : ℝ} (hab : a ≤ b)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ EuclideanSpace.slab d a b)
    {w : SobolevEuclidean (d + 1) 1 p Ω}
    (hw : w ∈ SobolevMultiIndex.testFunctions ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      1 p Ω volume) :
    ‖SobolevMultiIndex.fnL ℝ _ 1 p Ω volume w‖
      ≤ (b - a) * ‖SobolevMultiIndex.weakDeriv w (MultiIndexLE.single (Fin.last d))‖ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨φ, hφ⟩ := hw
  have hmeas := Ω.isOpen.measurableSet
  -- the partial derivative `∂_N w` is `fderiv φ · e_N`
  have hd : (SobolevMultiIndex.weakDeriv w (MultiIndexLE.single (Fin.last d)) :
      EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[volume.restrict (Ω : Set _)]
        fun x ↦ fderiv ℝ φ x (EuclideanSpace.single (Fin.last d) 1) := by
    refine (SobolevMultiIndex.weakDeriv_ae_eq_iteratedFDeriv_of_fn_ae_eq w φ.contDiff hφ
      (MultiIndexLE.single (Fin.last d))).trans (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [MultiIndexLE.coe_single, φ.contDiff.iteratedFDeriv_congr_perm
      (multiIndexTuple_single_perm
        ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis : Fin (d + 1) → _) (Fin.last d)) x,
      iteratedFDeriv_one_apply, Matrix.cons_val_zero, EuclideanSpace.basisFun_toBasis_last]
  -- both functions vanish outside `Ω`, so the norms over `Ω` are the norms over `ℝ^{d+1}`
  have hφΩ : eLpNorm (φ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) p (volume.restrict (Ω : Set _))
      = eLpNorm (φ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) p volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hmeas]
    congr 1
    exact Set.indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx ↦
      φ.eq_zero_of_notMem hx)
  have hdΩ : eLpNorm (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single (Fin.last d) 1)) p
      (volume.restrict (Ω : Set _))
      = eLpNorm (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single (Fin.last d) 1)) p volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hmeas]
    congr 1
    exact Set.indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx ↦
      (φ.fderivApply (EuclideanSpace.single (Fin.last d) 1)).eq_zero_of_notMem hx)
  have key := eLpNorm_le_eLpNorm_fderiv_apply_of_subset_slab hp hp'
    (φ.contDiff.of_le (by simp)) (φ.tsupport_subset.trans hΩ)
  rw [← hφΩ, ← hdΩ, ← eLpNorm_congr_ae hφ, ← eLpNorm_congr_ae hd] at key
  rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal (sub_nonneg.2 hab), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)) key

/-- **Corollary 9.19 / Remark 21 (bounded projection on the last axis), typed**: for
`1 ≤ p < ∞`, `Ω ⊆ {a < x_N < b}` and `u ∈ W_0^{1,p}(Ω)`,
`‖u‖_{L^p(Ω)} ≤ (b − a) ‖∂_N u‖_{L^p(Ω)}`. By density: `u` is a limit of test functions, for which
`SobolevEuclideanZero.norm_fnL_le_of_mem_testFunctions` applies, and both sides are continuous in
the `W^{1,p}` norm ([brezis2011functional] Corollary 9.19 and Remark 21). -/
theorem norm_fnL_le_of_subset_slab (hp' : p ≠ ⊤) {a b : ℝ} (hab : a ≤ b)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ EuclideanSpace.slab d a b)
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) :
    ‖SobolevMultiIndex.fnL ℝ _ 1 p Ω volume (u : SobolevEuclidean (d + 1) 1 p Ω)‖
      ≤ (b - a) * ‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 p Ω)
          (MultiIndexLE.single (Fin.last d))‖ := by
  have hmem : (u : SobolevEuclidean (d + 1) 1 p Ω) ∈ closure (SobolevMultiIndex.testFunctions ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume : Set _) := by
    rw [← Submodule.topologicalClosure_coe]
    exact u.2
  obtain ⟨w, hwT, hw⟩ := mem_closure_iff_seq_limit.1 hmem
  have h1 : Tendsto (fun n ↦ ‖SobolevMultiIndex.fnL ℝ _ 1 p Ω volume (w n)‖) atTop
      (𝓝 ‖SobolevMultiIndex.fnL ℝ _ 1 p Ω volume (u : SobolevEuclidean (d + 1) 1 p Ω)‖) :=
    ((SobolevMultiIndex.fnL ℝ _ 1 p Ω volume).continuous.tendsto _).comp hw |>.norm
  have h2 : Tendsto (fun n ↦ (b - a) *
      ‖SobolevMultiIndex.weakDerivL ℝ _ 1 p Ω volume (MultiIndexLE.single (Fin.last d)) (w n)‖)
      atTop (𝓝 ((b - a) * ‖SobolevMultiIndex.weakDerivL ℝ _ 1 p Ω volume
        (MultiIndexLE.single (Fin.last d)) (u : SobolevEuclidean (d + 1) 1 p Ω)‖)) :=
    (((SobolevMultiIndex.weakDerivL ℝ _ 1 p Ω volume _).continuous.tendsto _).comp hw
      |>.norm).const_mul _
  exact le_of_tendsto_of_tendsto' h1 h2 fun n ↦
    norm_fnL_le_of_mem_testFunctions hp' hab hΩ (hwT n)

/-- **Corollary 9.19 / Remark 21, `L^p` form**: for `1 ≤ p < ∞`, `Ω ⊆ {a < x_N < b}` and
`u ∈ W_0^{1,p}(Ω)`,
`eLpNorm (fn u) p (volume.restrict Ω) ≤ ofReal (b − a) * eLpNorm (∂_N u) p (volume.restrict Ω)`. -/
theorem eLpNorm_fn_le_of_subset_slab (hp' : p ≠ ⊤) {a b : ℝ} (hab : a ≤ b)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ EuclideanSpace.slab d a b)
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) :
    eLpNorm (SobolevMultiIndex.fn (u : SobolevEuclidean (d + 1) 1 p Ω)) p
        (volume.restrict (Ω : Set _))
      ≤ ENNReal.ofReal (b - a) * eLpNorm (SobolevMultiIndex.weakDeriv
          (u : SobolevEuclidean (d + 1) 1 p Ω) (MultiIndexLE.single (Fin.last d))) p
            (volume.restrict (Ω : Set _)) := by
  have h := norm_fnL_le_of_subset_slab hp' hab hΩ u
  rw [Lp.norm_def, Lp.norm_def] at h
  have hfin : ENNReal.ofReal (b - a) * eLpNorm (SobolevMultiIndex.weakDeriv
      (u : SobolevEuclidean (d + 1) 1 p Ω) (MultiIndexLE.single (Fin.last d))) p
        (volume.restrict (Ω : Set _)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)
  exact (ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top
    (SobolevMultiIndex.fnL ℝ _ 1 p Ω volume (u : SobolevEuclidean (d + 1) 1 p Ω))) hfin).1
    (by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]; exact h)

/-- **Corollary 9.19 (Poincaré's inequality)**: for `1 ≤ p < ∞`, a bounded open set
`Ω ⊆ B(0, R)` with `0 ≤ R`, and `u ∈ W_0^{1,p}(Ω)`,
`‖u‖_{L^p(Ω)} ≤ 2R ‖∂_N u‖_{L^p(Ω)}`; in particular `‖u‖_p ≤ C ‖∇u‖_p` for any reading of the
gradient norm dominating one partial derivative, with the constant `C = 2R` that the book leaves
unspecified ("depending on `Ω` and `p`"). The ball lies in the slab `{−R < x_N < R}`. -/
theorem eLpNorm_fn_le_of_isBounded (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) :
    eLpNorm (SobolevMultiIndex.fn (u : SobolevEuclidean (d + 1) 1 p Ω)) p
        (volume.restrict (Ω : Set _))
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (SobolevMultiIndex.weakDeriv
          (u : SobolevEuclidean (d + 1) 1 p Ω) (MultiIndexLE.single (Fin.last d))) p
            (volume.restrict (Ω : Set _)) := by
  have := eLpNorm_fn_le_of_subset_slab hp' (by linarith)
    (EuclideanSpace.subset_slab_of_subset_ball hΩ) u
  rwa [show R - -R = 2 * R by ring] at this

/-- **The gradient norm is an equivalent norm on `W_0^{1,p}(Ω)` for a bounded `Ω`**
([brezis2011functional] Corollary 9.19, "the expression `‖∇u‖_{L^p(Ω)}` is a norm on
`W_0^{1,p}(Ω)`, and it is equivalent to the norm `‖u‖_{W^{1,p}}`"): for `1 ≤ p < ∞`,
`Ω ⊆ B(0, R)` and `u ∈ W_0^{1,p}(Ω)`, `‖u‖ ≤ (1 + (2R)^p)^{1/p} ‖∇u‖_p`; with
`SobolevMultiIndex.gradNorm_le_norm` this is the two-sided equivalence, and at `p = 2` it is the
coercivity `‖u‖_{H^1}^2 ≤ (1 + 4R^2) ‖∇u‖_2^2` of the Dirichlet form on `H_0^1(Ω)`. -/
theorem norm_le_gradNorm (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) :
    ‖(u : SobolevEuclidean (d + 1) 1 p Ω)‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal)
      * SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 p Ω) := by
  have hP : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp'
  have h0 : ‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 p Ω) 0‖
      ≤ 2 * R * SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 p Ω) := by
    have h := norm_fnL_le_of_subset_slab hp' (by linarith)
      (EuclideanSpace.subset_slab_of_subset_ball hΩ) u
    rw [SobolevMultiIndex.fnL_eq_weakDeriv_zero, show R - -R = 2 * R by ring] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (SobolevMultiIndex.norm_weakDeriv_single_le_gradNorm _ _) (by positivity))
  have hg0 : 0 ≤ SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 p Ω) :=
    SobolevMultiIndex.gradNorm_nonneg _
  rw [SobolevMultiIndex.norm_eq_gradNorm hp']
  calc (‖SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 p Ω) 0‖ ^ p.toReal
        + SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 p Ω) ^ p.toReal)
          ^ (1 / p.toReal)
      ≤ ((2 * R * SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 p Ω)) ^ p.toReal
        + SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 p Ω) ^ p.toReal)
          ^ (1 / p.toReal) := by
        gcongr
    _ = ((1 + (2 * R) ^ p.toReal)
          * SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 p Ω) ^ p.toReal)
            ^ (1 / p.toReal) := by
        congr 1
        rw [Real.mul_rpow (by positivity) hg0]
        ring
    _ = (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal)
          * SobolevMultiIndex.gradNorm (u : SobolevEuclidean (d + 1) 1 p Ω) := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hg0 _), ← Real.rpow_mul hg0,
          mul_one_div_cancel hP.ne', Real.rpow_one]

end SobolevEuclideanZero

end Typed
