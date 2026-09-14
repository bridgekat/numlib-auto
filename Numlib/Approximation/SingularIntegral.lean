import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Singular integrals: endpoint singularities and unbounded intervals

The elementary analysis behind the numerical treatment of singular integrals in
[quarteroni2000numerical] §9.8: an integrand `φ(x)/(x - a)^μ`, `0 ≤ μ < 1`, with `φ` bounded or
smooth, and integrals over `[a, ∞)`.

## Main results

* `Quadrature.intervalIntegrable_div_rpow`, `Quadrature.abs_integral_div_rpow_le` — for bounded
  measurable `φ`, `φ(x)/(x - a)^μ` is integrable on `[a, b]` and
  `|∫_a^b φ(x)/(x - a)^μ| ≤ M (b - a)^{1-μ}/(1 - μ)`, the a priori bound of §9.8.2.
* `Quadrature.integral_pow_div_rpow`, `Quadrature.integral_sum_mul_pow_div_rpow` — the closed
  forms `∫_a^b (x - a)^k/(x - a)^μ = (b - a)^{k+1-μ}/(k + 1 - μ)` and, for a polynomial in
  `x - a`, the sum that (9.51) displays for the Taylor polynomial.
* `Quadrature.taylorWithinEval_univ_eq_sum`, `Quadrature.exists_sub_taylorWithinEval_univ_eq` —
  the Taylor polynomial `Φ_p(x) = ∑_{k≤p} φ^{(k)}(a)(x - a)^k/k!` as Mathlib's
  `taylorWithinEval φ p univ a`, and the Lagrange form of the remainder (9.47) with the
  unrestricted derivative `φ^{(p+1)}(ξ)`, for `φ` smooth on an open set containing the segment.
* `Quadrature.abs_integral_taylorRemainder_div_rpow_le` — the truncation estimate (9.48) of
  Method 1: `|∫_a^{a+ε} (φ - Φ_p)/(x - a)^μ| ≤ ε^{p+2-μ}/((p + 1)! (p + 2 - μ)) max |φ^{(p+1)}|`.
* `Quadrature.integrableOn_Ioi_of_tendsto_rpow_mul`,
  `Quadrature.tendsto_intervalIntegral_of_tendsto_rpow_mul` — the decay criterion of §9.8.3:
  `x^{1+ρ} f(x) → 0` for some `ρ > 0` makes a continuous `f` integrable on `[a, ∞)`, and then
  `∫_a^∞ f = lim_{t→∞} ∫_a^t f` (9.53).
* `Quadrature.integral_Ioi_eq_integral_Ioo_inv` — the inversion `x = 1/t` (9.55),
  `∫_c^∞ f = ∫_0^{1/c} f(1/t)/t² dt`.

Nothing here is a quadrature rule: these are the identities and regularity facts that let the
composite Newton–Cotes error formulae of `Numlib/Approximation/NewtonCotes` be applied to a
regularized integrand. The operator-level theory of product integration for weakly singular
kernels is `Numlib/IntegralEquations/ProductIntegration` and is not repeated.

## Not yet proved

The regularity of the subtracted integrand `(φ - Φ_p)/(x - a)^μ` up to the endpoint — the claim
after (9.52) that it is `C^p` on `[a, b]` with vanishing derivatives at `a` when `φ ∈ C^{p+1}` — is
the module's one delicate statement (`Quadrature.contDiffOn_taylorRemainder_div_rpow`, open in
the plan): away from `a` it is the quotient rule, at `a` the Leibniz formula with Taylor's theorem
for each derivative of the remainder and one-sided differentiability from the difference
quotients.

## Conventions

Smoothness of `φ` is `ContDiffOn ℝ (p + 1) φ U` on an open `U` containing the closed interval, as
the quadrature error formulae of `Numlib/Approximation/NewtonCotes` state it, so that the
derivatives `iteratedDeriv k φ` are the two-sided ones. Mathlib supplies the power integrals
(`integral_rpow`, `intervalIntegrable_rpow'`, `integrableOn_Ioi_rpow_of_lt`), Taylor's theorem
(`taylor_mean_remainder_lagrange_iteratedDeriv`), the improper integrals
(`intervalIntegral_tendsto_integral_Ioi`) and the change of variables `integral_comp_rpow_Ioi`.
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace Quadrature

/-! ### The a priori bound -/

section Endpoint

variable {a b μ : ℝ} {φ : ℝ → ℝ}

/-- The weight `x ↦ (x - a)^{-μ}`, `μ < 1`, is integrable over `[a, b]`. -/
theorem intervalIntegrable_rpow_neg_sub (hμ : μ < 1) :
    IntervalIntegrable (fun x => (x - a) ^ (-μ)) volume a b := by
  have h := (intervalIntegrable_rpow' (a := 0) (b := b - a) (by linarith : (-1 : ℝ) < -μ))
    |>.comp_sub_right a
  simpa using h

/-- `∫_a^b (x - a)^{-μ} = (b - a)^{1-μ}/(1 - μ)` for `a ≤ b`, `μ < 1`. -/
theorem integral_rpow_neg_sub (hμ : μ < 1) :
    ∫ x in a..b, (x - a) ^ (-μ) = (b - a) ^ (1 - μ) / (1 - μ) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ (-μ)) a, sub_self,
    integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith), sub_zero,
    show -μ + 1 = 1 - μ by ring]

/-- **Integrability of `φ(x)/(x - a)^μ`** for `0 ≤ μ < 1` and `φ` measurable and bounded on
`(a, b]`. -/
theorem intervalIntegrable_div_rpow (hab : a < b) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hφ : AEStronglyMeasurable φ (volume.restrict (Ioc a b))) {M : ℝ}
    (hM : ∀ x ∈ Ioc a b, |φ x| ≤ M) :
    IntervalIntegrable (fun x => φ x / (x - a) ^ μ) volume a b := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM b ⟨hab, le_rfl⟩)
  have hI : IntervalIntegrable (fun x => M * (x - a) ^ (-μ)) volume a b :=
    (intervalIntegrable_rpow_neg_sub hμ1).const_mul M
  have hc : Continuous fun x : ℝ => (x - a) ^ μ :=
    (continuous_id.sub continuous_const).rpow_const fun _ => Or.inr hμ0
  refine hI.mono_fun ?_ ?_
  · rw [uIoc_of_le hab.le]
    exact (hφ.aemeasurable.div hc.measurable.aemeasurable).aestronglyMeasurable
  · rw [uIoc_of_le hab.le, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    have hxa : 0 < x - a := by linarith [hx.1]
    have hpos : 0 < (x - a) ^ μ := Real.rpow_pos_of_pos hxa μ
    simp only [Real.norm_eq_abs]
    rw [abs_div, abs_of_pos hpos, abs_mul, abs_of_nonneg hM0,
      abs_of_pos (Real.rpow_pos_of_pos hxa (-μ)), Real.rpow_neg hxa.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM x hx) (inv_nonneg.2 hpos.le)

/-- **The a priori bound of [quarteroni2000numerical] §9.8.2.** For `μ < 1` and `φ` with
`|φ| ≤ M` on `(a, b]`, `|∫_a^b φ(x)/(x - a)^μ dx| ≤ M (b - a)^{1-μ}/(1 - μ)` (the integral exists
by `intervalIntegrable_div_rpow` when `φ` is measurable; the bound needs no more than the
pointwise estimate). -/
theorem abs_integral_div_rpow_le (hab : a < b) (hμ1 : μ < 1) {M : ℝ}
    (hM : ∀ x ∈ Ioc a b, |φ x| ≤ M) :
    |∫ x in a..b, φ x / (x - a) ^ μ| ≤ M * (b - a) ^ (1 - μ) / (1 - μ) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM b ⟨hab, le_rfl⟩)
  have hI : IntervalIntegrable (fun x => M * (x - a) ^ (-μ)) volume a b :=
    (intervalIntegrable_rpow_neg_sub hμ1).const_mul M
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun x => φ x / (x - a) ^ μ) (g := fun x => M * (x - a) ^ (-μ)) hab.le ?_ hI
  · rw [Real.norm_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_rpow_neg_sub hμ1, ← mul_div_assoc]
  · refine Eventually.of_forall fun x hx => ?_
    have hxa : 0 < x - a := by linarith [hx.1]
    have hpos : 0 < (x - a) ^ μ := Real.rpow_pos_of_pos hxa μ
    simp only [Real.norm_eq_abs]
    rw [abs_div, abs_of_pos hpos, Real.rpow_neg hxa.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM x hx) (inv_nonneg.2 hpos.le)

/-! ### The closed forms (9.51) -/

/-- `∫_a^b (x - a)^k/(x - a)^μ dx = (b - a)^{k+1-μ}/(k + 1 - μ)` for `a ≤ b`, `k : ℕ`, `μ < 1`. -/
theorem integral_pow_div_rpow (hab : a ≤ b) (hμ1 : μ < 1) (k : ℕ) :
    ∫ x in a..b, (x - a) ^ k / (x - a) ^ μ = (b - a) ^ (k + 1 - μ) / (k + 1 - μ) := by
  rw [intervalIntegral.integral_comp_sub_right (fun t => t ^ k / t ^ μ) a, sub_self]
  have hcongr : ∫ t in (0 : ℝ)..(b - a), t ^ k / t ^ μ = ∫ t in (0 : ℝ)..(b - a), t ^ (k - μ) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le (by linarith)] at ht
    rw [← Real.rpow_natCast, Real.rpow_sub ht.1]
  rw [hcongr, integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith), sub_zero,
    show (k : ℝ) - μ + 1 = k + 1 - μ by ring]

/-- **The singular part integrates in closed form** ([quarteroni2000numerical] (9.51)): for a
polynomial `∑_{k≤p} c_k (x - a)^k` in `x - a`,
`∫_a^b (∑_{k≤p} c_k (x - a)^k)/(x - a)^μ dx = (b - a)^{1-μ} ∑_{k≤p} (b - a)^k c_k/(k + 1 - μ)`;
with `c_k = φ^{(k)}(a)/k!` this is (9.51). -/
theorem integral_sum_mul_pow_div_rpow (hab : a ≤ b) (hμ1 : μ < 1) (c : ℕ → ℝ) (p : ℕ) :
    ∫ x in a..b, (∑ k ∈ Finset.range (p + 1), c k * (x - a) ^ k) / (x - a) ^ μ
      = (b - a) ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1), (b - a) ^ k * c k / (k + 1 - μ) := by
  have hint : ∀ k ∈ Finset.range (p + 1),
      IntervalIntegrable (fun x => c k * ((x - a) ^ k / (x - a) ^ μ)) volume a b := by
    intro k _
    have h1 : IntervalIntegrable (fun x => (x - a) ^ ((k : ℝ) - μ)) volume a b := by
      simpa using ((intervalIntegrable_rpow' (a := 0) (b := b - a)
        (by linarith : (-1 : ℝ) < k - μ)).comp_sub_right a)
    refine (h1.congr_ae ?_).const_mul (c k)
    rw [Filter.EventuallyEq, uIoc_of_le hab, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    have hxa : 0 < x - a := by linarith [hx.1]
    rw [← Real.rpow_natCast, Real.rpow_sub hxa]
  have e : ∀ x, (∑ k ∈ Finset.range (p + 1), c k * (x - a) ^ k) / (x - a) ^ μ
      = ∑ k ∈ Finset.range (p + 1), c k * ((x - a) ^ k / (x - a) ^ μ) := by
    intro x
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow_div_rpow hab hμ1 k]
  have hne : (k : ℝ) + 1 - μ ≠ 0 := by linarith
  rw [show (k : ℝ) + 1 - μ = k + (1 - μ) by ring, Real.rpow_add' (by linarith) (by
    rw [show (k : ℝ) + (1 - μ) = k + 1 - μ by ring]; exact hne), Real.rpow_natCast]
  rw [show (k : ℝ) + (1 - μ) = k + 1 - μ by ring]
  ring

/-! ### The Taylor polynomial and the remainder (9.47) -/

/-- The Taylor polynomial `Φ_p(x) = ∑_{k≤p} φ^{(k)}(a)(x - a)^k/k!` of `φ` at `a`
([quarteroni2000numerical] (9.47)) is Mathlib's `taylorWithinEval φ p univ a x`. -/
theorem taylorWithinEval_univ_eq_sum (φ : ℝ → ℝ) (p : ℕ) (a x : ℝ) :
    taylorWithinEval φ p univ a x
      = ∑ k ∈ Finset.range (p + 1), iteratedDeriv k φ a * (x - a) ^ k / k.factorial := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedDerivWithin_univ, smul_eq_mul]
  ring

/-- **Taylor's formula with the Lagrange remainder** ([quarteroni2000numerical] (9.47)): for `φ`
of class `C^{p+1}` on an open set containing the segment from `a` to `x ≠ a`,
`φ(x) = Φ_p(x) + φ^{(p+1)}(ξ)(x - a)^{p+1}/(p + 1)!` for some `ξ` strictly between `a` and `x`,
with `Φ_p = taylorWithinEval φ p univ a` the Taylor polynomial in the two-sided derivatives.
Mathlib's `taylor_mean_remainder_lagrange_iteratedDeriv`, whose Taylor polynomial is taken within
the segment, and the agreement of the within-derivatives at `a` with the two-sided ones. -/
theorem exists_sub_taylorWithinEval_univ_eq {a x : ℝ} (hax : a ≠ x) {p : ℕ} {U : Set ℝ}
    (hU : IsOpen U) (hsub : uIcc a x ⊆ U) (hφ : ContDiffOn ℝ (p + 1 : ℕ) φ U) :
    ∃ ξ ∈ uIoo a x, φ x - taylorWithinEval φ p univ a x
      = iteratedDeriv (p + 1) φ ξ * (x - a) ^ (p + 1) / (p + 1).factorial := by
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax (hφ.mono hsub)
  refine ⟨ξ, hξ, ?_⟩
  rw [← h, taylor_within_apply, taylor_within_apply]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : (k : WithTop ℕ∞) ≤ (p + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [iteratedDerivWithin_univ, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hax)
    ((hφ.contDiffAt (hU.mem_nhds (hsub left_mem_uIcc))).of_le hk') left_mem_uIcc]

/-- **The truncation estimate of Method 1** ([quarteroni2000numerical] (9.48)). For `ε > 0`,
`μ < 1`, `φ` of class `C^{p+1}` on an open set containing `[a, a + ε]` and
`|φ^{(p+1)}| ≤ M` on `[a, a + ε]`,
`|∫_a^{a+ε} (φ(x) - Φ_p(x))/(x - a)^μ dx| ≤ ε^{p+2-μ}/((p + 1)! (p + 2 - μ)) · M`:
the Lagrange remainder gives `|φ(x) - Φ_p(x)| ≤ M (x - a)^{p+1}/(p + 1)!`, and
`(x - a)^{p+1-μ}` integrates to `ε^{p+2-μ}/(p + 2 - μ)`. -/
theorem abs_integral_taylorRemainder_div_rpow_le {ε : ℝ} (hε : 0 < ε) (hμ1 : μ < 1)
    {p : ℕ} {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a (a + ε) ⊆ U)
    (hφ : ContDiffOn ℝ (p + 1 : ℕ) φ U) {M : ℝ}
    (hM : ∀ x ∈ Icc a (a + ε), |iteratedDeriv (p + 1) φ x| ≤ M) :
    |∫ x in a..(a + ε), (φ x - taylorWithinEval φ p univ a x) / (x - a) ^ μ|
      ≤ ε ^ (p + 2 - μ) / ((p + 1).factorial * (p + 2 - μ)) * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a ⟨le_rfl, by linarith⟩)
  have hI : IntervalIntegrable (fun x => M / (p + 1).factorial * ((x - a) ^ (p + 1) / (x - a) ^ μ))
      volume a (a + ε) := by
    refine IntervalIntegrable.const_mul ?_ _
    have h1 : IntervalIntegrable (fun x => (x - a) ^ ((p : ℝ) + 1 - μ)) volume a (a + ε) := by
      have h0 := (intervalIntegrable_rpow' (a := 0) (b := ε)
        (by linarith : (-1 : ℝ) < p + 1 - μ)).comp_sub_right a
      rwa [zero_add, add_comm ε a] at h0
    refine h1.congr_ae ?_
    rw [Filter.EventuallyEq, uIoc_of_le (by linarith), ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    have hxa : 0 < x - a := by linarith [hx.1]
    rw [← Real.rpow_natCast, Real.rpow_sub hxa]
    push_cast
    rfl
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun x => (φ x - taylorWithinEval φ p univ a x) / (x - a) ^ μ)
    (g := fun x => M / (p + 1).factorial * ((x - a) ^ (p + 1) / (x - a) ^ μ)) (by linarith) ?_ hI
  · rw [Real.norm_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_pow_div_rpow (by linarith) hμ1,
      add_sub_cancel_left, show ((p + 1 : ℕ) : ℝ) + 1 - μ = p + 2 - μ by push_cast; ring]
    have : (0 : ℝ) < p + 2 - μ := by linarith
    field_simp
  · refine Eventually.of_forall fun x hx => ?_
    have hxa : 0 < x - a := by linarith [hx.1]
    obtain ⟨ξ, hξ, hrem⟩ := exists_sub_taylorWithinEval_univ_eq (φ := φ) (p := p)
      (ne_of_lt hx.1) hU (by rw [uIcc_of_le hx.1.le]; exact (Icc_subset_Icc_right hx.2).trans hsub)
      hφ
    rw [uIoo_of_lt hx.1] at hξ
    have hξM : |iteratedDeriv (p + 1) φ ξ| ≤ M :=
      hM ξ ⟨hξ.1.le, hξ.2.le.trans hx.2⟩
    have hfac : (0 : ℝ) < (p + 1).factorial := by positivity
    have hpos : 0 < (x - a) ^ μ := Real.rpow_pos_of_pos hxa μ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, hrem, abs_div, abs_mul, abs_of_pos hfac,
      abs_of_pos (pow_pos hxa (p + 1))]
    have e : |iteratedDeriv (p + 1) φ ξ| * (x - a) ^ (p + 1) / (p + 1).factorial / (x - a) ^ μ
        = |iteratedDeriv (p + 1) φ ξ| / (p + 1).factorial
          * ((x - a) ^ (p + 1) / (x - a) ^ μ) := by
      field_simp
    rw [e]
    gcongr

end Endpoint

/-! ### Unbounded intervals -/

section Unbounded

variable {a c ρ : ℝ} {f : ℝ → ℝ}

/-- **The decay criterion of [quarteroni2000numerical] §9.8.3.** If `f` is continuous on
`[a, ∞)` and `x^{1+ρ} f(x) → 0` as `x → ∞` for some `ρ > 0` — `f` is infinitesimal of order
`> 1` with respect to `1/x` — then `f` is integrable over `(a, ∞)`: eventually
`|f(x)| ≤ x^{-(1+ρ)}`, which is integrable at infinity, and the compact piece is integrable by
continuity. -/
theorem integrableOn_Ioi_of_tendsto_rpow_mul (hf : ContinuousOn f (Ici a)) (hρ : 0 < ρ)
    (hlim : Tendsto (fun x => x ^ (1 + ρ) * f x) atTop (𝓝 0)) : IntegrableOn f (Ioi a) := by
  -- eventually `|x^{1+ρ} f x| ≤ 1`
  have hev : ∀ᶠ x in atTop, |x ^ (1 + ρ) * f x| ≤ 1 := by
    have := hlim.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    simpa [Real.dist_eq] using this
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  set c := max c₀ (max a 1) with hc
  have hca : a ≤ c := le_max_of_le_right (le_max_left _ _)
  have hc1 : (1 : ℝ) ≤ c := le_max_of_le_right (le_max_right _ _)
  have hcpos : 0 < c := by linarith
  have hcc₀ : c₀ ≤ c := le_max_left _ _
  -- the tail
  have htail : IntegrableOn f (Ioi c) := by
    have hpow : IntegrableOn (fun x : ℝ => x ^ (-(1 + ρ))) (Ioi c) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hcpos
    refine hpow.mono' ((hf.mono fun x hx => le_trans hca (le_of_lt hx)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hcpos.trans hx
    have h1 := hc₀ x (hcc₀.trans hx.le)
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at h1
    rw [Real.norm_eq_abs, Real.rpow_neg hx0.le, ← one_div, le_div_iff₀
      (Real.rpow_pos_of_pos hx0 _), mul_comm]
    exact h1
  -- the compact piece
  have hcomp : IntegrableOn f (Ioc a c) :=
    (hf.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← Ioc_union_Ioi_eq_Ioi hca]
  exact hcomp.union htail

/-- Under the decay criterion, the improper integral is the limit of the proper ones,
`∫_a^∞ f = lim_{t→∞} ∫_a^t f` ([quarteroni2000numerical] (9.53)). -/
theorem tendsto_intervalIntegral_of_tendsto_rpow_mul (hf : ContinuousOn f (Ici a)) (hρ : 0 < ρ)
    (hlim : Tendsto (fun x => x ^ (1 + ρ) * f x) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 (∫ x in Ioi a, f x)) :=
  intervalIntegral_tendsto_integral_Ioi a (integrableOn_Ioi_of_tendsto_rpow_mul hf hρ hlim)
    tendsto_id

/-- **The inversion `x = 1/t`** ([quarteroni2000numerical] (9.55)): for `c > 0`,
`∫_c^∞ f(x) dx = ∫_0^{1/c} f(1/t)/t² dt`. Mathlib's `integral_comp_rpow_Ioi` with `p = -1` on the
indicator of `(c, ∞)`, whose preimage under `t ↦ 1/t` on `(0, ∞)` is `(0, 1/c)`. -/
theorem integral_Ioi_eq_integral_Ioo_inv (hc : 0 < c) (f : ℝ → ℝ) :
    ∫ x in Ioi c, f x = ∫ t in Ioo 0 (1 / c), f (1 / t) / t ^ 2 := by
  have key := integral_comp_rpow_Ioi ((Ioi c).indicator f) (p := -1) (by norm_num)
  have hsub : Ioi c ⊆ Ioi 0 := Ioi_subset_Ioi hc.le
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 hsub] at key
  have hIoo : Ioo 0 (1 / c) = Ioi 0 ∩ Ioo 0 (1 / c) := (inter_eq_right.2 Ioo_subset_Ioi_self).symm
  rw [← key, hIoo, ← setIntegral_indicator measurableSet_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hpow : t ^ (-1 : ℝ) = 1 / t := by rw [Real.rpow_neg_one, one_div]
  have hpow2 : t ^ ((-1 : ℝ) - 1) = 1 / t ^ 2 := by
    rw [show (-1 : ℝ) - 1 = -(2 : ℕ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast,
      one_div]
  simp only [abs_neg, abs_one, one_mul, hpow, hpow2, smul_eq_mul]
  by_cases hmem : t ∈ Ioo 0 (1 / c)
  · have hmem' : 1 / t ∈ Ioi c := by
      rw [mem_Ioi, lt_one_div hc ht0]
      exact hmem.2
    rw [indicator_of_mem hmem, indicator_of_mem hmem']
    ring
  · have hmem' : 1 / t ∉ Ioi c := by
      intro h
      rw [mem_Ioi, lt_one_div hc ht0] at h
      exact hmem ⟨ht0, h⟩
    rw [indicator_of_notMem hmem, indicator_of_notMem hmem', mul_zero]

end Unbounded

end Quadrature
