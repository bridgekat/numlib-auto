import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The exponential of a Banach algebra: perturbation and conditioning

Upstreaming candidate: natural home `Mathlib/Analysis/Normed/Algebra/Exponential`, whose name this
module mirrors.

In a complete normed `ℝ`-algebra `𝔸` (complex matrices are one through
`NormedAlgebra.complexToReal`), this module develops the first-order perturbation theory of
`t ↦ exp (t • a)` beyond Mathlib's `NormedSpace.exp`:

* `NormedSpace.exp_smul_add_sub_exp_smul`: the **variation-of-constants identity**
  `e^{t(a+e)} - e^{ta} = ∫₀ᵗ e^{(t-s)a} e e^{s(a+e)} ds`, with the norm bound
  `NormedSpace.norm_exp_smul_add_sub_exp_smul_le`;
* `NormedSpace.eq_exp_smul_of_hasDerivAt`: `t ↦ e^{ta}` is the unique solution of `X' = aX`,
  `X(0) = 1`;
* `NormedSpace.expFrechet a t`: the Fréchet derivative `e ↦ ∫₀ᵗ e^{(t-s)a} e e^{sa} ds` of
  `a ↦ e^{ta}` (`NormedSpace.hasFDerivAt_exp_smul`), as an integral of continuous linear maps;
* `NormedSpace.expCondNumber a t = ‖L(a, t)‖ ‖a‖ / ‖e^{ta}‖`: Van Loan's relative condition number
  of the exponential ([golub2013matrix] §9.3.2), the relative condition number of `a ↦ e^{ta}` in
  the sense of Higham, *Functions of Matrices*, §3.1, with its lower bound
  `NormedSpace.mul_norm_le_expCondNumber` and the equality criterion
  `NormedSpace.expCondNumber_eq_of_norm_exp_smul_eq`;
* `norm_resolvent_le_of_norm_exp_smul_le`: in a complex Banach algebra, `‖e^{ta}‖ ≤ M` for `t ≥ 0`
  gives `‖(z - a)⁻¹‖ ≤ M / Re z` for `Re z > 0`, the resolvent being the Laplace transform
  `∫₀^∞ e^{-zt} e^{ta} dt` ([golub2013matrix] (9.3.6)).

The equality criterion is the correct form of [golub2013matrix] §9.3.2's "`ν(A, t) = t‖A‖₂` iff
`A` is normal": equality holds whenever `‖e^{sa}‖ = e^{cs}` on `[0, t]`, which normal matrices
satisfy with `c` the spectral abscissa, but so does the non-normal `[1] ⊕ [[0, 1], [0, 0]]`.
-/

open Filter Topology MeasureTheory

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The exponential is continuous (from its analyticity over `ℝ`). -/
private theorem continuous_exp_real : Continuous (exp : 𝔸 → 𝔸) :=
  continuous_iff_continuousAt.mpr fun x => (exp_analytic (𝕂 := ℝ) x).continuousAt

/-- `s ↦ exp (c(s) • a)` is continuous for continuous `c`. -/
private theorem continuous_exp_smul {X : Type*} [TopologicalSpace X] {c : X → ℝ}
    (hc : Continuous c) (a : 𝔸) : Continuous fun s => exp (c s • a) :=
  continuous_exp_real.comp (hc.smul continuous_const)

/-- `exp (x + y) = exp x * exp y` for commuting `x`, `y` in a real normed algebra (Mathlib's
`exp_add_of_commute` asks for a `ℚ`-algebra structure). -/
private theorem exp_add_of_commute_real {x y : 𝔸} (h : Commute x y) :
    exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

/-- The derivative of `s ↦ exp ((t - s) • a)`. -/
private theorem hasDerivAt_exp_sub_smul (a : 𝔸) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((t - s) • a)) (-(a * exp ((t - s) • a))) s := by
  have h := (hasDerivAt_exp_smul_const' a (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
  simpa [Function.comp_def] using h

omit [CompleteSpace 𝔸] in
private theorem commute_exp_smul (a : 𝔸) (r : ℝ) : Commute a (exp (r • a)) :=
  ((Commute.refl a).smul_right r).exp_right

private theorem continuous_variation (a e b : 𝔸) (t : ℝ) :
    Continuous fun s : ℝ => exp ((t - s) • a) * e * exp (s • b) :=
  ((continuous_exp_smul (continuous_const.sub continuous_id) a).mul continuous_const).mul
    (continuous_exp_smul continuous_id b)

/-- **The variation-of-constants identity**:
`e^{t(a+e)} - e^{ta} = ∫₀ᵗ e^{(t-s)a} e e^{s(a+e)} ds`. The integrand is the derivative of
`s ↦ e^{(t-s)a} e^{s(a+e)}`, the `a`-terms cancelling because `a` commutes with `e^{(t-s)a}`. -/
theorem exp_smul_add_sub_exp_smul (a e : 𝔸) (t : ℝ) :
    exp (t • (a + e)) - exp (t • a) =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • a) * e * exp (s • (a + e)) := by
  have hderiv : ∀ s, HasDerivAt (fun s : ℝ => exp ((t - s) • a) * exp (s • (a + e)))
      (exp ((t - s) • a) * e * exp (s • (a + e))) s := by
    intro s
    have h := HasDerivAt.mul (hasDerivAt_exp_sub_smul a t s) (hasDerivAt_exp_smul_const' (a + e) s)
    convert h using 1
    rw [neg_mul, (commute_exp_smul a (t - s)).eq]
    noncomm_ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    ((continuous_variation a e (a + e) t).intervalIntegrable _ _)]
  simp

/-- The norm bound of the variation-of-constants identity, for `t ≥ 0`. -/
theorem norm_exp_smul_add_sub_exp_smul_le (a e : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • (a + e)) - exp (t • a)‖ ≤
      ‖e‖ * ∫ s in (0 : ℝ)..t, ‖exp ((t - s) • a)‖ * ‖exp (s • (a + e))‖ := by
  rw [exp_smul_add_sub_exp_smul, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans
    (intervalIntegral.integral_mono_on ht ?_ ?_ fun s _ => ?_)
  · exact (continuous_variation a e (a + e) t).norm.intervalIntegrable _ _
  · exact (continuous_const.mul ((continuous_exp_smul (continuous_const.sub continuous_id)
      a).norm.mul (continuous_exp_smul continuous_id (a + e)).norm)).intervalIntegrable _ _
  · calc ‖exp ((t - s) • a) * e * exp (s • (a + e))‖
        ≤ ‖exp ((t - s) • a)‖ * ‖e‖ * ‖exp (s • (a + e))‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖e‖ * (‖exp ((t - s) • a)‖ * ‖exp (s • (a + e))‖) := by ring

/-- **`e^{ta}` is the unique solution of `X' = aX`, `X(0) = 1`** ([golub2013matrix] §9.3.2). That
`t ↦ exp (t • a)` is a solution is Mathlib's `hasDerivAt_exp_smul_const'`. -/
theorem eq_exp_smul_of_hasDerivAt {a : 𝔸} {X : ℝ → 𝔸} (hX : ∀ t, HasDerivAt X (a * X t) t)
    (h0 : X 0 = 1) (t : ℝ) : X t = exp (t • a) := by
  have hψ : ∀ s, HasDerivAt (fun s => exp ((0 - s) • a) * X s) 0 s := by
    intro s
    have := HasDerivAt.mul (hasDerivAt_exp_sub_smul a 0 s) (hX s)
    convert this using 1
    rw [neg_mul, (commute_exp_smul a (0 - s)).eq]
    noncomm_ring
  have hconst : exp ((0 - t) • a) * X t = 1 := by
    have := is_const_of_deriv_eq_zero (fun s => (hψ s).differentiableAt) (fun s => (hψ s).deriv)
      t 0
    simpa [h0] using this
  have hinv : exp (t • a) * exp ((0 - t) • a) = 1 := by
    rw [← exp_add_of_commute_real (((Commute.refl a).smul_left t).smul_right _), ← add_smul]
    simp
  calc X t = exp (t • a) * exp ((0 - t) • a) * X t := by rw [hinv, one_mul]
    _ = exp (t • a) := by rw [mul_assoc, hconst, mul_one]

/-! ### The Fréchet derivative and the condition number -/

/-- The integrand of the Fréchet derivative, as continuous linear maps
`e ↦ e^{(t-s)a} e e^{sa}`. -/
private noncomputable def frechetIntegrand (a : 𝔸) (t s : ℝ) : 𝔸 →L[ℝ] 𝔸 :=
  (ContinuousLinearMap.mul ℝ 𝔸 (exp ((t - s) • a))).comp
    ((ContinuousLinearMap.mul ℝ 𝔸).flip (exp (s • a)))

private theorem continuous_frechetIntegrand (a : 𝔸) (t : ℝ) :
    Continuous (frechetIntegrand a t) :=
  ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp
    (continuous_exp_smul (continuous_const.sub continuous_id) a)).clm_comp
    ((ContinuousLinearMap.mul ℝ 𝔸).flip.continuous.comp (continuous_exp_smul continuous_id a))

/-- **The Fréchet derivative of `a ↦ e^{ta}`**: `expFrechet a t e = ∫₀ᵗ e^{(t-s)a} e e^{sa} ds`
(`NormedSpace.expFrechet_apply`, `NormedSpace.hasFDerivAt_exp_smul`); [golub2013matrix] §9.3.2,
the first-order term of the variation-of-constants identity; Higham, *Functions of Matrices*,
(10.15). -/
noncomputable def expFrechet (a : 𝔸) (t : ℝ) : 𝔸 →L[ℝ] 𝔸 :=
  ∫ s in (0 : ℝ)..t, frechetIntegrand a t s

theorem expFrechet_apply (a : 𝔸) (t : ℝ) (e : 𝔸) :
    expFrechet a t e = ∫ s in (0 : ℝ)..t, exp ((t - s) • a) * e * exp (s • a) := by
  rw [expFrechet, ContinuousLinearMap.intervalIntegral_apply
    ((continuous_frechetIntegrand a t).intervalIntegrable _ _)]
  simp [frechetIntegrand, mul_assoc]

/-- The Fréchet derivative in the direction `1` is `t e^{ta}`. -/
theorem expFrechet_one (a : 𝔸) (t : ℝ) : expFrechet a t 1 = t • exp (t • a) := by
  rw [expFrechet_apply]
  have h : ∀ s : ℝ, exp ((t - s) • a) * exp (s • a) = exp (t • a) := fun s => by
    rw [← exp_add_of_commute_real (((Commute.refl a).smul_left _).smul_right _), ← add_smul,
      sub_add_cancel]
  simp [h]

/-- In a direction commuting with `a`, the Fréchet derivative of the exponential is
`t e^{ta} e`. -/
theorem expFrechet_apply_of_commute {a e : 𝔸} (h : Commute a e) (t : ℝ) :
    expFrechet a t e = t • (exp (t • a) * e) := by
  rw [expFrechet_apply]
  have hc : ∀ s : ℝ, exp ((t - s) • a) * e * exp (s • a) = exp (t • a) * e := fun s => by
    rw [mul_assoc, ((h.smul_left s).exp_left).eq.symm, ← mul_assoc,
      ← exp_add_of_commute_real (((Commute.refl a).smul_left _).smul_right _), ← add_smul,
      sub_add_cancel]
  simp [hc]

/-- **`expFrechet a t` is the Fréchet derivative of `a ↦ e^{ta}`.** The exponential is analytic,
hence differentiable; its derivative in a direction `e` is computed from the variation-of-constants
identity, `e^{t(a+εe)} - e^{ta} = ε ∫₀ᵗ e^{(t-s)a} e e^{s(a+εe)} ds`, the integral being continuous
in `ε`. -/
theorem hasFDerivAt_exp_smul (a : 𝔸) (t : ℝ) :
    HasFDerivAt (fun b : 𝔸 => exp (t • b)) (expFrechet a t) a := by
  have hdiff : DifferentiableAt ℝ (fun b : 𝔸 => exp (t • b)) a :=
    (exp_analytic (𝕂 := ℝ) (t • a)).differentiableAt.comp a
      ((differentiableAt_id).const_smul t)
  convert hdiff.hasFDerivAt using 1
  ext e
  -- the derivative along the line `ε ↦ a + ε • e`
  have hline : HasDerivAt (fun ε : ℝ => exp (t • (a + ε • e)))
      (fderiv ℝ (fun b : 𝔸 => exp (t • b)) a e) 0 := by
    have hg : HasDerivAt (fun ε : ℝ => a + ε • e) e 0 := by
      simpa using HasDerivAt.const_add a (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) e)
    have hf' : HasFDerivAt (fun b : 𝔸 => exp (t • b)) (fderiv ℝ (fun b : 𝔸 => exp (t • b)) a)
        (a + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]
      exact hdiff.hasFDerivAt
    simpa [Function.comp_def] using hf'.comp_hasDerivAt (0 : ℝ) hg
  -- the same derivative from the variation-of-constants identity
  set I : ℝ → 𝔸 := fun ε => ∫ s in (0 : ℝ)..t, exp ((t - s) • a) * e * exp (s • (a + ε • e))
  have hIcont : Continuous I := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun ε s => exp ((t - s) • a) * e * exp (s • (a + ε • e))) ?_ 0 t
    have h1 : Continuous fun p : ℝ × ℝ => p.2 • (a + p.1 • e) := by fun_prop
    exact ((continuous_exp_smul (continuous_const.sub continuous_snd) a).mul
      continuous_const).mul (continuous_exp_real.comp h1)
  have hI : HasDerivAt (fun ε : ℝ => exp (t • (a + ε • e))) (I 0) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine (hIcont.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : ε ≠ 0 := hε
    rw [slope_def_module, zero_smul, add_zero, sub_zero, exp_smul_add_sub_exp_smul]
    simp only [smul_mul_assoc, mul_smul_comm, intervalIntegral.integral_smul]
    rw [smul_smul, inv_mul_cancel₀ hε', one_smul]
  rw [hline.unique hI, expFrechet_apply]
  simp [I]

/-- **Van Loan's condition number of the exponential** ([golub2013matrix] §9.3.2):
`ν(a, t) = ‖L(a, t)‖ ‖a‖ / ‖e^{ta}‖`, with `L(a, t) = expFrechet a t` the Fréchet derivative of
`a ↦ e^{ta}`. The book's `max_{‖E‖ ≤ 1} ‖∫₀ᵗ e^{A(t-s)} E e^{As} ds‖` is this operator norm. -/
noncomputable def expCondNumber (a : 𝔸) (t : ℝ) : ℝ :=
  ‖expFrechet a t‖ * ‖a‖ / ‖exp (t • a)‖

variable [NormOneClass 𝔸]

/-- **`ν(a, t) ≥ t ‖a‖`** ([golub2013matrix] §9.3.2): the Fréchet derivative in the direction `1`
is `t e^{ta}`. -/
theorem mul_norm_le_expCondNumber (a : 𝔸) {t : ℝ} (ht : 0 ≤ t) : t * ‖a‖ ≤ expCondNumber a t := by
  have : Nontrivial 𝔸 := NormOneClass.nontrivial
  have hunit : IsUnit (exp (t • a)) := by
    refine ⟨⟨exp (t • a), exp (-(t • a)), ?_, ?_⟩, rfl⟩
    · rw [← exp_add_of_commute_real ((Commute.refl _).neg_right), add_neg_cancel, exp_zero]
    · rw [← exp_add_of_commute_real ((Commute.refl _).neg_left), neg_add_cancel, exp_zero]
  have hpos : 0 < ‖exp (t • a)‖ := norm_pos_iff.mpr hunit.ne_zero
  have hL : t * ‖exp (t • a)‖ ≤ ‖expFrechet a t‖ := by
    have := (expFrechet a t).le_opNorm 1
    rwa [expFrechet_one, norm_one, mul_one, norm_smul, Real.norm_of_nonneg ht] at this
  rw [expCondNumber, le_div_iff₀ hpos]
  calc t * ‖a‖ * ‖exp (t • a)‖ = t * ‖exp (t • a)‖ * ‖a‖ := by ring
    _ ≤ ‖expFrechet a t‖ * ‖a‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)

/-- **The equality case of Van Loan's condition number**: if `‖e^{sa}‖ = e^{cs}` for all
`s ∈ [0, t]`, then `ν(a, t) = t ‖a‖`. It holds for normal matrices with `c` the spectral abscissa
([golub2013matrix] (9.3.4)), and also for some non-normal ones (`[1] ⊕ [[0, 1], [0, 0]]`), which is
why [golub2013matrix] §9.3.2's "iff `A` is normal" fails. -/
theorem expCondNumber_eq_of_norm_exp_smul_eq (a : 𝔸) {t c : ℝ} (ht : 0 ≤ t)
    (h : ∀ s ∈ Set.Icc 0 t, ‖exp (s • a)‖ = Real.exp (c * s)) :
    expCondNumber a t = t * ‖a‖ := by
  refine le_antisymm ?_ (mul_norm_le_expCondNumber a ht)
  have hpos : 0 < ‖exp (t • a)‖ := by
    rw [h t ⟨ht, le_rfl⟩]
    exact Real.exp_pos _
  have hL : ‖expFrechet a t‖ ≤ t * ‖exp (t • a)‖ := by
    refine (expFrechet a t).opNorm_le_bound (by positivity) fun e => ?_
    rw [expFrechet_apply]
    have hbound : ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖exp ((t - s) • a) * e * exp (s • a)‖ ≤ ‖exp (t • a)‖ * ‖e‖ := by
      intro s hs
      have h1 := h (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have h2 := h s hs
      calc ‖exp ((t - s) • a) * e * exp (s • a)‖
          ≤ ‖exp ((t - s) • a)‖ * ‖e‖ * ‖exp (s • a)‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ = ‖exp (t • a)‖ * ‖e‖ := by
            rw [h1, h2, h t ⟨ht, le_rfl⟩, mul_right_comm, ← Real.exp_add]
            ring_nf
    calc ‖∫ s in (0 : ℝ)..t, exp ((t - s) • a) * e * exp (s • a)‖
        ≤ ‖exp (t • a)‖ * ‖e‖ * |t - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun s hs =>
            hbound s ⟨(Set.uIoc_of_le ht ▸ hs).1.le, (Set.uIoc_of_le ht ▸ hs).2⟩
      _ = t * ‖exp (t • a)‖ * ‖e‖ := by rw [sub_zero, abs_of_nonneg ht]; ring
  rw [expCondNumber, div_le_iff₀ hpos]
  calc ‖expFrechet a t‖ * ‖a‖ ≤ t * ‖exp (t • a)‖ * ‖a‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = t * ‖a‖ * ‖exp (t • a)‖ := by ring

end NormedSpace

open NormedSpace

/-! ### The resolvent as a Laplace transform -/

section Resolvent

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- **The Laplace-transform resolvent bound** behind [golub2013matrix] (9.3.6): in a complex Banach
algebra, if `‖e^{ta}‖ ≤ M` for all real `t ≥ 0` and `Re z > 0`, then `z` is not in the spectrum of
`a` and `‖(z - a)⁻¹‖ ≤ M / Re z`. The inverse is `∫₀^∞ e^{-zt} e^{ta} dt`. -/
theorem norm_resolvent_le_of_norm_exp_smul_le {a : 𝔸} {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → ‖exp (t • a)‖ ≤ M) {z : ℂ} (hz : 0 < z.re) :
    z ∉ spectrum ℂ a ∧ ‖Ring.inverse (algebraMap ℂ 𝔸 z - a)‖ ≤ M / z.re := by
  set w := algebraMap ℂ 𝔸 z - a
  set E : ℝ → 𝔸 := fun t => Complex.exp (-(z * t)) • exp (t • a)
  have hcomm : ∀ t : ℝ, Commute (E t) w := fun t => by
    have h1 : Commute (exp (t • a)) a := ((Commute.refl a).smul_right t).exp_right.symm
    exact ((Algebra.commute_algebraMap_right z _).sub_right h1).smul_left _
  have hcont : Continuous E :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).smul
      (continuous_exp_smul continuous_id a)
  have hnormE : ∀ t : ℝ, 0 ≤ t → ‖E t‖ ≤ M * Real.exp (-z.re * t) := fun t ht => by
    simp only [E, norm_smul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [mul_comm, neg_mul]
    exact mul_le_mul_of_nonneg_right (hM t ht) (Real.exp_pos _).le
  have hgint : IntegrableOn (fun t : ℝ => M * Real.exp (-z.re * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hz) 0).const_mul M
  have hEint : IntegrableOn E (Set.Ioi 0) :=
    hgint.mono' hcont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht =>
        hnormE t (le_of_lt ht)))
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt (fun t => -E t) (E t * w) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(z * t)))
        (Complex.exp (-(z * t)) * -(z * 1)) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul z).neg.cexp
    have h2 := h1.smul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) a t)
    have h3 : Commute a (exp (t • a)) := ((Commute.refl a).smul_right t).exp_right
    convert h2.neg using 1
    simp only [E, w, mul_sub, smul_mul_assoc, h3.eq]
    rw [← Algebra.commutes z (exp (t • a)), ← Algebra.smul_def]
    module
  have hlim : Filter.Tendsto (fun t => -E t) Filter.atTop (nhds 0) := by
    rw [← neg_zero]
    refine Filter.Tendsto.neg (squeeze_zero_norm' (a := fun t => M * Real.exp (-z.re * t)) ?_ ?_)
    · exact Filter.eventually_atTop.mpr ⟨0, fun t ht => hnormE t ht⟩
    · have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop hz)).const_mul M
      simpa [Function.comp_def, neg_mul] using this
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hEint.mul_const w) hlim
  have hE0 : E 0 = 1 := by simp [E]
  rw [hE0, zero_sub, neg_neg, integral_mul_const_of_integrable hEint] at hFTC
  set R := ∫ t in Set.Ioi (0 : ℝ), E t
  have hRw : w * R = 1 := by
    rw [← hFTC, ← integral_const_mul_of_integrable hEint,
      ← integral_mul_const_of_integrable hEint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => (hcomm t).eq.symm)
  have hu : IsUnit w := ⟨⟨w, R, hRw, hFTC⟩, rfl⟩
  refine ⟨fun h => (spectrum.mem_iff.mp h) hu, ?_⟩
  rw [show Ring.inverse w = R from by
    rw [Ring.inverse_unit ⟨w, R, hRw, hFTC⟩]
    rfl]
  have hint : ∫ t in Set.Ioi (0 : ℝ), M * Real.exp (-z.re * t) = M / z.re := by
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hz)]
    field_simp
    simp
  rw [← hint]
  exact norm_integral_le_of_norm_le hgint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht =>
      hnormE t (le_of_lt ht)))

end Resolvent
