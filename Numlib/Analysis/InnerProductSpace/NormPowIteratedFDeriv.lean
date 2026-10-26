import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Analysis.InnerProductSpace.NormPow

/-!
# Derivatives of all orders of `‖x‖^λ`

The derivatives of `x ↦ ‖x‖ ^ λ` on a real inner product space, everywhere including the origin,
with sharp operator-norm bounds ([cartis2022evaluation], Lemma B.4.1). These are the
regularization terms `σ/(p+1)! ‖s‖^{p+1}` (and `‖s‖^{p+β}`) of adaptive-regularization models.
Write `π_j(λ) = λ(λ-1)⋯(λ-j+1) = ∏_{i<j} (λ - i)`.

## Main statements

Real exponents:
* `exists_integral_abs_inner_rpow_eq`: the averaging identity
  `∫_{‖ω‖<1} |⟪y, ω⟫|^λ dω = κ ‖y‖^λ` on a finite-dimensional space (rotation invariance).
* `iteratedFDeriv_normRpow_eq_integral`: for `j ≤ λ`, `D^j(‖·‖^λ)(x)[v₁,…,v_j]` is
  `π_j(λ)/κ ∫ |⟪x,ω⟫|^{λ-j} sign(⟪x,ω⟫)^j ∏ᵢ ⟪vᵢ,ω⟫ dω` (differentiation under the integral).
* `norm_iteratedFDeriv_normRpow_le`, `norm_iteratedFDeriv_normRpow`: (B.4.1), the operator norm
  of `D^j(‖·‖^λ)(x)` is `π_j(λ) ‖x‖^{λ-j}` for `j ≤ λ`, on any real inner product space.
* `contDiff_normRpow_of_lt`, `iteratedFDeriv_normRpow_zero`: `‖·‖^λ` is `C^j` for `j < λ`, with
  vanishing derivatives at the origin.
* `iteratedFDeriv_normRpow_apply_self`: (B.4.2), the radial values `π_j(λ) ‖x‖^λ`.
* `not_norm_iteratedFDeriv_normRpow_eq_radial`: (B.4.3) is false for `β < 1`.
* `convexOn_iteratedFDeriv_normRpow`: the convexity claims of Lemma B.4.1.

Natural exponents `‖s‖ ^ r` (`r : ℕ`), the form in which regularized models are written:
* `contDiff_norm_pow` (`C^{r-1}`), `contDiff_norm_pow_of_even`, `contDiffAt_norm_pow`;
* `iteratedFDeriv_norm_pow_apply_self`, `norm_iteratedFDeriv_norm_pow_le`,
  `norm_iteratedFDeriv_norm_pow`, `abs_iteratedFDeriv_norm_pow_apply_le`:
  `‖D^ℓ(‖·‖^r)(s)‖ ≤ r!/(r-ℓ)! ‖s‖^{r-ℓ}` for `ℓ ≤ r`;
* `iteratedFDerivLipschitzOn_norm_pow`: `∇^{r-1} ‖·‖^r` is `r!`-Lipschitz ((B.4.3) for `β = 1`);
* `abs_norm_pow_sub_taylorPolynomial_le`: `|‖s+d‖^r - T_{r-1}(s,d)| ≤ ‖d‖^r`.

## Implementation notes

The book's proof of (B.4.1) maximizes over the radial direction, which is not justified as written
(the terms of (B.4.9) have mixed signs). Instead, on a finite-dimensional space rotation invariance
of Lebesgue measure on the unit ball gives `‖y‖^λ = κ⁻¹ ∫_{‖ω‖<1} |⟪y,ω⟫|^λ dω`. Differentiating
`j ≤ λ` times under the integral sign (the integrand is Lipschitz in `y` since `λ - k ≥ 1` at each
step, and differentiable off a null hyperplane) gives `iteratedFDeriv_normRpow_eq_integral`, and
the weighted AM–GM inequality with weights `(λ-j)/λ, 1/λ, …, 1/λ`, integrated, gives the
operator-norm bound with the sharp constant `π_j(λ)`. In particular no result on symmetric
multilinear forms (Banach's theorem) is needed. A general inner product space reduces to the
finite-dimensional span of the point and the arguments
(`Submodule.iteratedFDeriv_comp_subtypeL_apply`), and
smoothness at the origin follows from the bound by an explicit Taylor series
(`hasFTaylorSeriesUpTo_normRpow`).
-/

open Filter Metric MeasureTheory Module Set Topology
open scoped Nat RealInnerProductSpace

namespace NormPowIteratedFDeriv

/-- The signed power `|u|^a sign(u)^k`, the one-variable profile of the derivatives of `‖·‖^λ`. -/
noncomputable def sgnPow (a : ℝ) (k : ℕ) (u : ℝ) : ℝ := |u| ^ a * (SignType.sign u : ℝ) ^ k

/-- Unfolding `sgnPow`. -/
theorem sgnPow_def (a : ℝ) (k : ℕ) (u : ℝ) : sgnPow a k u = |u| ^ a * (SignType.sign u : ℝ) ^ k :=
  rfl

/-- Powers of a sign have absolute value at most `1`. -/
theorem abs_sign_pow_le (k : ℕ) (u : ℝ) : |(SignType.sign u : ℝ) ^ k| ≤ 1 := by
  rw [abs_pow]
  refine pow_le_one₀ (abs_nonneg _) ?_
  rcases lt_trichotomy u 0 with h | h | h <;> simp [sign_neg, sign_pos, h]

/-- `|sgnPow a k u| ≤ |u|^a`. -/
theorem abs_sgnPow_le (a : ℝ) (k : ℕ) (u : ℝ) : |sgnPow a k u| ≤ |u| ^ a := by
  rw [sgnPow, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) a)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg u) a) (abs_sign_pow_le k u)

/-- The sign function `ℝ → ℝ` is measurable (it is monotone). -/
theorem measurable_sign_real : Measurable fun u : ℝ ↦ (SignType.sign u : ℝ) := by
  refine Monotone.measurable fun u v huv ↦ ?_
  rcases lt_trichotomy u 0 with hu | hu | hu <;> rcases lt_trichotomy v 0 with hv | hv | hv <;>
    simp [sign_neg, sign_pos, hu, hv] <;> linarith

/-- `sgnPow a k` is measurable. -/
theorem measurable_sgnPow (a : ℝ) (k : ℕ) : Measurable (sgnPow a k) :=
  (continuous_abs.measurable.pow_const a).mul (measurable_sign_real.pow_const k)

/-- Away from `0`, `d/du (|u|^a sign(u)^k) = a |u|^{a-1} sign(u)^{k+1}`. -/
theorem hasDerivAt_sgnPow (a : ℝ) (k : ℕ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (sgnPow a k) (a * sgnPow (a - 1) (k + 1) u) u := by
  rcases hu.lt_or_gt with hu | hu
  · have hev : sgnPow a k =ᶠ[𝓝 u] fun t ↦ (-t) ^ a * (-1) ^ k := by
      filter_upwards [Iio_mem_nhds hu] with t ht
      simp [sgnPow, sign_neg (show t < 0 from ht), abs_of_neg (show t < 0 from ht)]
    have h := (((hasDerivAt_id u).neg).rpow_const (p := a) (Or.inl (by simp; linarith))).mul_const
      ((-1 : ℝ) ^ k)
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [sgnPow, sign_neg hu, abs_of_neg hu, SignType.coe_neg, SignType.coe_one, Pi.neg_apply,
      id_eq]
    ring
  · have hev : sgnPow a k =ᶠ[𝓝 u] fun t ↦ t ^ a := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      simp [sgnPow, sign_pos (show 0 < t from ht), abs_of_pos (show 0 < t from ht)]
    refine ((Real.hasDerivAt_rpow_const (Or.inl hu.ne')).congr_of_eventuallyEq hev).congr_deriv ?_
    simp [sgnPow, sign_pos hu, abs_of_pos hu]

/-- For `a > 0`, `sgnPow a k` is continuous (also at `0`, where it vanishes). -/
theorem continuous_sgnPow {a : ℝ} (ha : 0 < a) (k : ℕ) : Continuous (sgnPow a k) := by
  refine continuous_iff_continuousAt.2 fun u ↦ ?_
  rcases eq_or_ne u 0 with rfl | hu
  · have h0 : sgnPow a k 0 = 0 := by simp [sgnPow, Real.zero_rpow ha.ne']
    rw [ContinuousAt, h0]
    exact squeeze_zero_norm (a := fun t ↦ |t| ^ a) (fun t ↦ abs_sgnPow_le a k t) (by
      simpa [Real.zero_rpow ha.ne'] using
        ((continuous_abs.rpow_const fun _ ↦ Or.inr ha.le).tendsto (0 : ℝ)))
  · exact (hasDerivAt_sgnPow a k hu).continuousAt

/-- Mean value inequality for a continuous function differentiable off `0`, on `[-R, R]`. -/
theorem abs_sub_le_of_hasDerivAt_ne_zero {g g' : ℝ → ℝ} (hc : Continuous g)
    (hd : ∀ t ≠ 0, HasDerivAt g (g' t) t) {L R : ℝ} (hb : ∀ t, t ≠ 0 → |t| ≤ R → |g' t| ≤ L)
    {u v : ℝ} (hu : |u| ≤ R) (hv : |v| ≤ R) : |g u - g v| ≤ L * |u - v| := by
  -- the case of an interval not containing `0` in its interior
  have key : ∀ u v : ℝ, |u| ≤ R → |v| ≤ R → v ≤ u → (0 ≤ v ∨ u ≤ 0) →
      |g u - g v| ≤ L * |u - v| := by
    intro u v hu hv hvu h0
    rcases hvu.eq_or_lt with rfl | hvu
    · simp
    obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope g g' hvu hc.continuousOn
      fun x hx ↦ hd x (by rcases h0 with h0 | h0 <;> [linarith [hx.1]; linarith [hx.2]])
    have hc0 : c ≠ 0 := by rcases h0 with h0 | h0 <;> [linarith [hc'.1]; linarith [hc'.2]]
    have hcR : |c| ≤ R := abs_le.2 ⟨by linarith [(abs_le.1 hv).1, hc'.1],
      by linarith [(abs_le.1 hu).2, hc'.2]⟩
    have hpos : 0 < u - v := sub_pos.2 hvu
    rw [eq_div_iff hpos.ne'] at hcd
    rw [← hcd, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (hb c hc0 hcR) hpos.le
  -- reduce to `v ≤ u`, then split at `0`
  wlog hvu : v ≤ u generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]
    exact this hv hu (le_of_not_ge hvu)
  by_cases h0 : 0 ≤ v ∨ u ≤ 0
  · exact key u v hu hv hvu h0
  push Not at h0
  have h0R : |(0 : ℝ)| ≤ R := by rw [abs_zero]; exact (abs_nonneg _).trans hu
  calc |g u - g v| ≤ |g u - g 0| + |g 0 - g v| := abs_sub_le _ _ _
    _ ≤ L * |u - 0| + L * |0 - v| :=
        add_le_add (key u 0 hu h0R h0.2.le (Or.inl le_rfl)) (key 0 v h0R hv h0.1.le (Or.inr le_rfl))
    _ = L * |u - v| := by
        rw [sub_zero, zero_sub, abs_neg, abs_of_pos h0.2, abs_of_neg h0.1,
          abs_of_pos (by linarith)]
        ring

/-- For `a ≥ 1`, `u ↦ |u|^a sign(u)^k` is `a R^{a-1}`-Lipschitz on `[-R, R]`. -/
theorem abs_sgnPow_sub_le {a : ℝ} (ha : 1 ≤ a) (k : ℕ) {R u v : ℝ} (hu : |u| ≤ R) (hv : |v| ≤ R) :
    |sgnPow a k u - sgnPow a k v| ≤ a * R ^ (a - 1) * |u - v| := by
  refine abs_sub_le_of_hasDerivAt_ne_zero (continuous_sgnPow (by linarith) k)
    (fun t ht ↦ hasDerivAt_sgnPow a k ht) (fun t _ ht ↦ ?_) hu hv
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a)]
  refine mul_le_mul_of_nonneg_left ((abs_sgnPow_le _ _ t).trans ?_) (by linarith)
  exact Real.rpow_le_rpow (abs_nonneg t) ht (by linarith)

end NormPowIteratedFDeriv

/-! ### Elementary estimates -/

section Elementary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NormPowIteratedFDeriv

/-- On the unit ball, `|⟪y, ω⟫| ≤ ‖y‖`. -/
theorem abs_inner_le_of_mem_ball {y ω : E} (hω : ω ∈ ball (0 : E) 1) : |⟪y, ω⟫| ≤ ‖y‖ := by
  have : ‖ω‖ ≤ 1 := by simpa using (mem_ball_zero_iff.1 hω).le
  calc |⟪y, ω⟫| ≤ ‖y‖ * ‖ω‖ := abs_real_inner_le_norm y ω
    _ ≤ ‖y‖ := mul_le_of_le_one_right (norm_nonneg y) this

/-- `|⟪y, ω⟫| = ‖y‖ |⟪ŷ, ω⟫|` with `ŷ = ‖y‖⁻¹ y` (also for `y = 0`). -/
theorem abs_inner_eq_norm_mul (y ω : E) : |⟪y, ω⟫| = ‖y‖ * |⟪‖y‖⁻¹ • y, ω⟫| := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [real_inner_smul_left, abs_mul, abs_inv, abs_norm, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 hy), one_mul]

/-- The normalization `‖y‖⁻¹ y` has norm at most `1` (it is `0` for `y = 0`). -/
theorem norm_inv_smul_self_le (y : E) : ‖‖y‖⁻¹ • y‖ ≤ 1 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]

/-- The derivative of `z ↦ ⟪z, ω⟫` is `innerSL ℝ ω`. -/
theorem hasFDerivAt_inner_left (ω y : E) :
    HasFDerivAt (fun z : E ↦ ⟪z, ω⟫) (innerSL ℝ ω) y := by
  have h := (innerSL ℝ ω).hasFDerivAt (x := y)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp [real_inner_comm]

/-- `ω ↦ ∏ᵢ ⟪vᵢ, ω⟫` is continuous. -/
theorem continuous_prod_inner {j : ℕ} (v : Fin j → E) : Continuous fun ω : E ↦ ∏ i, ⟪v i, ω⟫ :=
  continuous_finsetProd _ fun _ _ ↦ continuous_const.inner continuous_id

/-- On the unit ball, `|∏ᵢ ⟪vᵢ, ω⟫| ≤ ∏ᵢ ‖vᵢ‖`. -/
theorem abs_prod_inner_le {j : ℕ} (v : Fin j → E) {ω : E} (hω : ω ∈ ball (0 : E) 1) :
    |∏ i, ⟪v i, ω⟫| ≤ ∏ i, ‖v i‖ := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ abs_inner_le_of_mem_ball hω

/-- Weighted AM–GM in the shape used for the derivatives of `‖·‖^λ`: for `a + j = λ > 0`,
`s^a ∏ tᵢ ≤ (a/λ) s^λ + ∑ λ⁻¹ tᵢ^λ`. -/
theorem rpow_mul_prod_le_of_add_eq {a lam : ℝ} {j : ℕ} (ha : 0 ≤ a) (hlam : a + j = lam)
    (hpos : 0 < lam) {s : ℝ} (hs : 0 ≤ s) {t : Fin j → ℝ} (ht : ∀ i, 0 ≤ t i) :
    s ^ a * ∏ i, t i ≤ a / lam * s ^ lam + ∑ i, lam⁻¹ * t i ^ lam := by
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin (j + 1)))
    (Fin.cons (a / lam) fun _ ↦ lam⁻¹) (Fin.cons (s ^ lam) fun i ↦ t i ^ lam) ?_ ?_ ?_
  · simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h
    have hmul : lam * (a / lam) = a := by field_simp
    rw [← Real.rpow_mul hs, hmul] at h
    simpa only [Real.rpow_rpow_inv (ht _) hpos.ne'] using h
  · intro i _
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simpa using div_nonneg ha hpos.le
    · simpa using hpos.le
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    linarith
  · intro i _
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simpa using Real.rpow_nonneg hs lam
    · simpa using Real.rpow_nonneg (ht i) lam

/-- `λ(λ-1)⋯(λ-j+1) ≥ 0` for `j ≤ λ`. -/
theorem prod_range_sub_nonneg {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam) :
    0 ≤ ∏ i ∈ Finset.range j, (lam - i) :=
  Finset.prod_nonneg fun i hi ↦ by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast Finset.mem_range.1 hi
    linarith

end NormPowIteratedFDeriv

end Elementary

/-! ### The averaging identity -/

section Averaging

open NormPowIteratedFDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace NormPowIteratedFDeriv

/-- A measurable function bounded on the unit ball is integrable on it. -/
theorem integrableOn_ball_of_le {F : Type*} [NormedAddCommGroup F] {g : E → F}
    (hg : AEStronglyMeasurable g volume) (C : ℝ) (hb : ∀ ω ∈ ball (0 : E) 1, ‖g ω‖ ≤ C) :
    IntegrableOn g (ball (0 : E) 1) :=
  Measure.integrableOn_of_bounded measure_ball_lt_top.ne hg
    (ae_restrict_of_forall_mem measurableSet_ball hb)

omit [FiniteDimensional ℝ E] in
/-- `ω ↦ |⟪y, ω⟫|^a` is measurable. -/
theorem measurable_abs_inner_rpow (y : E) (a : ℝ) : Measurable fun ω : E ↦ |⟪y, ω⟫| ^ a :=
  (continuous_abs.comp (continuous_const.inner continuous_id)).measurable.pow_const a

/-- For `a ≥ 0`, `ω ↦ |⟪y, ω⟫|^a` is integrable on the unit ball. -/
theorem integrableOn_abs_inner_rpow (y : E) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun ω : E ↦ |⟪y, ω⟫| ^ a) (ball (0 : E) 1) :=
  integrableOn_ball_of_le (measurable_abs_inner_rpow y a).aestronglyMeasurable (‖y‖ ^ a)
    fun ω hω ↦ by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) a)]
      exact Real.rpow_le_rpow (abs_nonneg _) (abs_inner_le_of_mem_ball hω) ha

/-- Rotation invariance: `∫_{‖ω‖<1} |⟪u, ω⟫|^λ dω` is the same for all unit vectors `u`. -/
theorem integral_abs_inner_rpow_eq_of_norm_eq (lam : ℝ) {e u : E} (he : ‖e‖ = 1) (hu : ‖u‖ = 1) :
    ∫ ω in ball (0 : E) 1, |⟪u, ω⟫| ^ lam = ∫ ω in ball (0 : E) 1, |⟪e, ω⟫| ^ lam := by
  set T : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (e - u))ᗮ.reflection with hT
  have hTe : T e = u := Submodule.reflection_sub (he.trans hu.symm)
  have hpre : (T : E → E) ⁻¹' ball (0 : E) 1 = ball (0 : E) 1 := by
    rw [LinearIsometryEquiv.preimage_ball, map_zero]
  have h := T.measurePreserving.setIntegral_preimage_emb T.toHomeomorph.measurableEmbedding
    (fun ω ↦ |⟪u, ω⟫| ^ lam) (ball (0 : E) 1)
  rw [hpre] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_ball fun ω _ ↦ ?_
  rw [← hTe, LinearIsometryEquiv.inner_map_map]

end NormPowIteratedFDeriv

open NormPowIteratedFDeriv in
/-- **Averaging identity.** On a finite-dimensional real inner product space, rotation invariance
of Lebesgue measure gives `∫_{‖ω‖<1} |⟪y, ω⟫|^λ dω = κ ‖y‖^λ` for a constant `κ > 0` (the value of
the integral at any unit vector). -/
theorem exists_integral_abs_inner_rpow_eq {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ κ > 0, ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- on the zero space every `y` is `0` and the integrand is constant
    refine ⟨volume.real (ball (0 : E) 1), ?_, fun y ↦ ?_⟩
    · exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
    · rw [Subsingleton.elim y 0]
      simp [mul_comm]
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  refine ⟨∫ ω in ball (0 : E) 1, |⟪e, ω⟫| ^ lam, ?_, fun y ↦ ?_⟩
  · change 0 < _
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun ω ↦ Real.rpow_nonneg (abs_nonneg _) lam)
      (integrableOn_abs_inner_rpow e hlam)]
    have hU : IsOpen ({ω : E | 0 < ⟪e, ω⟫} ∩ ball (0 : E) 1) :=
      (isOpen_lt continuous_const (continuous_const.inner continuous_id)).inter isOpen_ball
    have hne : ((1 / 2 : ℝ) • e) ∈ {ω : E | 0 < ⟪e, ω⟫} ∩ ball (0 : E) 1 := by
      refine ⟨?_, ?_⟩
      · simp [real_inner_smul_right, he]
      · simp [norm_smul, he]
        norm_num
    refine (hU.measure_pos volume ⟨_, hne⟩).trans_le (measure_mono ?_)
    rintro ω ⟨hω, hb⟩
    refine ⟨?_, hb⟩
    simp only [Function.mem_support]
    exact (Real.rpow_pos_of_pos (abs_pos.2 (ne_of_gt hω)) lam).ne'
  · rcases eq_or_ne y 0 with rfl | hy
    · rcases hlam.eq_or_lt with h0 | h0
      · simp [← h0]
      · simp [Real.zero_rpow h0.ne']
    have hu : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
    rw [← integral_abs_inner_rpow_eq_of_norm_eq lam he hu, mul_comm, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun ω _ ↦ ?_
    rw [abs_inner_eq_norm_mul y ω, Real.mul_rpow (norm_nonneg _) (abs_nonneg _)]

namespace NormPowIteratedFDeriv

/-- For `x ≠ 0` the hyperplane `⟪x, ·⟫ = 0` is Lebesgue-null. -/
theorem ae_inner_ne_zero {x : E} (hx : x ≠ 0) : ∀ᵐ ω ∂(volume : Measure E), ⟪x, ω⟫ ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have h := Measure.addHaar_submodule (volume : Measure E) (LinearMap.ker (innerₛₗ ℝ x)) ?_
  · convert h using 2
    ext ω
    simp
  intro htop
  have : x ∈ LinearMap.ker (innerₛₗ ℝ x) := htop ▸ Submodule.mem_top
  simp [hx] at this

omit [FiniteDimensional ℝ E] in
/-- `ω ↦ |⟪x, ω⟫|^a ∏ᵢ |⟪vᵢ, ω⟫|` is measurable. -/
theorem measurable_abs_inner_rpow_mul_prod (x : E) (a : ℝ) {j : ℕ} (v : Fin j → E) :
    Measurable fun ω : E ↦ |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫| :=
  (measurable_abs_inner_rpow x a).mul <| Finset.measurable_prod _ fun _ _ ↦
    (continuous_abs.comp (continuous_const.inner continuous_id)).measurable

/-- For `a ≥ 0`, `ω ↦ |⟪x, ω⟫|^a ∏ᵢ |⟪vᵢ, ω⟫|` is integrable on the unit ball. -/
theorem integrableOn_abs_inner_rpow_mul_prod (x : E) {a : ℝ} (ha : 0 ≤ a) {j : ℕ}
    (v : Fin j → E) :
    IntegrableOn (fun ω : E ↦ |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫|) (ball (0 : E) 1) := by
  refine integrableOn_ball_of_le (measurable_abs_inner_rpow_mul_prod x a v).aestronglyMeasurable
    (‖x‖ ^ a * ∏ i, ‖v i‖) fun ω hω ↦ ?_
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) a)
    (Finset.prod_nonneg fun i _ ↦ abs_nonneg _))]
  exact mul_le_mul (Real.rpow_le_rpow (abs_nonneg _) (abs_inner_le_of_mem_ball hω) ha)
    (Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ abs_inner_le_of_mem_ball hω)
    (Finset.prod_nonneg fun i _ ↦ abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) a)

/-- **The Hölder step.** If `∫_{‖ω‖<1} |⟪y, ω⟫|^λ dω = κ ‖y‖^λ` for all `y`, and `a + j = λ > 0`
with `a ≥ 0`, then `∫ |⟪x, ω⟫|^a ∏ᵢ |⟪vᵢ, ω⟫| ≤ κ ‖x‖^a ∏ᵢ ‖vᵢ‖`: by homogeneity reduce to
vectors of norm at most `1`, then integrate the weighted AM–GM inequality. -/
theorem integral_abs_inner_rpow_mul_prod_le {lam a κ : ℝ} {j : ℕ} (ha : 0 ≤ a)
    (hlam : a + j = lam) (hpos : 0 < lam) (hκ0 : 0 ≤ κ)
    (hκ : ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam) (x : E)
    (v : Fin j → E) :
    ∫ ω in ball (0 : E) 1, |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫| ≤ κ * (‖x‖ ^ a * ∏ i, ‖v i‖) := by
  set xh : E := ‖x‖⁻¹ • x
  set vh : Fin j → E := fun i ↦ ‖v i‖⁻¹ • v i
  set c : ℝ := ‖x‖ ^ a * ∏ i, ‖v i‖ with hc
  have hc0 : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) a)
    (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)
  have hpt : ∀ ω, |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫|
      = c * (|⟪xh, ω⟫| ^ a * ∏ i, |⟪vh i, ω⟫|) := by
    intro ω
    rw [abs_inner_eq_norm_mul x ω, Real.mul_rpow (norm_nonneg _) (abs_nonneg _),
      Finset.prod_congr rfl fun i _ ↦ abs_inner_eq_norm_mul (v i) ω, Finset.prod_mul_distrib, hc]
    ring
  have hle : ∀ y : E, ‖‖y‖⁻¹ • y‖ ^ lam ≤ 1 := fun y ↦
    Real.rpow_le_one (norm_nonneg _) (norm_inv_smul_self_le y) hpos.le
  have hint : ∀ y : E, IntegrableOn (fun ω : E ↦ |⟪y, ω⟫| ^ lam) (ball (0 : E) 1) :=
    fun y ↦ integrableOn_abs_inner_rpow y hpos.le
  calc ∫ ω in ball (0 : E) 1, |⟪x, ω⟫| ^ a * ∏ i, |⟪v i, ω⟫|
      = c * ∫ ω in ball (0 : E) 1, |⟪xh, ω⟫| ^ a * ∏ i, |⟪vh i, ω⟫| := by
        rw [← integral_const_mul]
        simp_rw [hpt]
    _ ≤ c * ∫ ω in ball (0 : E) 1,
          (a / lam * |⟪xh, ω⟫| ^ lam + ∑ i, lam⁻¹ * |⟪vh i, ω⟫| ^ lam) := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono
          (integrableOn_abs_inner_rpow_mul_prod xh ha vh)
          (((hint xh).const_mul _).add (integrable_finsetSum _ fun i _ ↦
            (hint (vh i)).const_mul _)) fun ω ↦ ?_) hc0
        exact rpow_mul_prod_le_of_add_eq ha hlam hpos (abs_nonneg _) fun i ↦ abs_nonneg _
    _ = c * (a / lam * (κ * ‖xh‖ ^ lam) + ∑ i, lam⁻¹ * (κ * ‖vh i‖ ^ lam)) := by
        rw [integral_add ((hint xh).const_mul _) (integrable_finsetSum _ fun i _ ↦
          (hint (vh i)).const_mul _), integral_finsetSum _ fun i _ ↦ (hint (vh i)).const_mul _,
          integral_const_mul, hκ]
        simp_rw [integral_const_mul, hκ]
    _ ≤ c * (a / lam * (κ * 1) + ∑ _i : Fin j, lam⁻¹ * (κ * 1)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ (Finset.sum_le_sum fun i _ ↦ ?_)) hc0
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle x) hκ0)
            (div_nonneg ha hpos.le)
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle (v i)) hκ0)
            (inv_nonneg.2 hpos.le)
    _ = κ * c := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp
        rw [← hlam]
        ring

/-- **Differentiation under the integral.** For `a ≥ 1`, a continuous weight `P` bounded on the
unit ball and `y ≠ 0`, `z ↦ ∫_{‖ω‖<1} |⟪z,ω⟫|^a sign(⟪z,ω⟫)^k P(ω) dω` has derivative
`h ↦ ∫ a |⟪y,ω⟫|^{a-1} sign(⟪y,ω⟫)^{k+1} P(ω) ⟪ω, h⟫ dω` at `y`. The integrand is Lipschitz in `z`
and differentiable off the null hyperplane `⟪y, ·⟫ = 0`. -/
theorem hasFDerivAt_integral_sgnPow_mul {a : ℝ} (ha : 1 ≤ a) (k : ℕ) {P : E → ℝ}
    (hP : Continuous P) {C : ℝ} (hPC : ∀ ω ∈ ball (0 : E) 1, |P ω| ≤ C) {y : E} (hy : y ≠ 0) :
    Integrable (fun ω ↦ (a * sgnPow (a - 1) (k + 1) ⟪y, ω⟫ * P ω) • innerSL ℝ ω)
        (volume.restrict (ball (0 : E) 1)) ∧
      HasFDerivAt (fun z ↦ ∫ ω in ball (0 : E) 1, sgnPow a k ⟪z, ω⟫ * P ω)
        (∫ ω in ball (0 : E) 1, (a * sgnPow (a - 1) (k + 1) ⟪y, ω⟫ * P ω) • innerSL ℝ ω) y := by
  have hmeas : ∀ z : E, Measurable fun ω : E ↦ sgnPow a k ⟪z, ω⟫ * P ω := fun z ↦
    ((measurable_sgnPow a k).comp (continuous_const.inner continuous_id).measurable).mul
      hP.measurable
  set R : ℝ := ‖y‖ + 1
  refine hasFDerivAt_integral_of_dominated_loc_of_lip' (bound := fun _ ↦ a * R ^ (a - 1) * C)
    (ball_mem_nhds y one_pos) (fun z _ ↦ (hmeas z).aestronglyMeasurable) ?_ ?_ ?_ ?_ ?_
  · refine integrableOn_ball_of_le (hmeas y).aestronglyMeasurable (‖y‖ ^ a * C) fun ω hω ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_sgnPow_le a k _).trans (Real.rpow_le_rpow (abs_nonneg _)
      (abs_inner_le_of_mem_ball hω) (by linarith))) (hPC ω hω) (abs_nonneg _)
      (Real.rpow_nonneg (norm_nonneg _) a)
  · exact ((((measurable_sgnPow (a - 1) (k + 1)).comp (continuous_const.inner
      continuous_id).measurable).const_mul a).mul hP.measurable).aestronglyMeasurable.smul
      (innerSL ℝ).continuous.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_ball fun ω hω z hz ↦ ?_
    have hz' : ‖z‖ ≤ R := by
      have := norm_le_norm_add_norm_sub' z y
      have : ‖z - y‖ < 1 := by simpa [dist_eq_norm] using hz
      linarith
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    have h1 : |sgnPow a k ⟪z, ω⟫ - sgnPow a k ⟪y, ω⟫| ≤ a * R ^ (a - 1) * ‖z - y‖ := by
      refine (abs_sgnPow_sub_le ha k ((abs_inner_le_of_mem_ball hω).trans hz')
        ((abs_inner_le_of_mem_ball hω).trans (by linarith))).trans ?_
      rw [← inner_sub_left]
      exact mul_le_mul_of_nonneg_left (abs_inner_le_of_mem_ball hω)
        (mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _))
    calc |sgnPow a k ⟪z, ω⟫ - sgnPow a k ⟪y, ω⟫| * |P ω|
        ≤ (a * R ^ (a - 1) * ‖z - y‖) * C :=
          mul_le_mul h1 (hPC ω hω) (abs_nonneg _) (by positivity)
      _ = a * R ^ (a - 1) * C * ‖z - y‖ := by ring
  · exact integrableOn_ball_of_le aestronglyMeasurable_const |a * R ^ (a - 1) * C|
      fun _ _ ↦ le_rfl
  · refine ae_restrict_of_ae ((ae_inner_ne_zero hy).mono fun ω hω ↦ ?_)
    have h := ((hasDerivAt_sgnPow a k hω).comp_hasFDerivAt y (hasFDerivAt_inner_left ω y)).mul_const
      (P ω)
    refine h.congr_fderiv ?_
    ext h'
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
    ring

/-- The integral formula off the origin (the inductive core of
`iteratedFDeriv_normRpow_eq_integral`). -/
theorem iteratedFDeriv_normRpow_eq_integral_of_ne_zero {lam κ : ℝ}
    (hκ : ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam) (hκ0 : κ ≠ 0) :
    ∀ (j : ℕ), (j : ℝ) ≤ lam → ∀ {x : E}, x ≠ 0 → ∀ v : Fin j → E,
      iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x v
        = (∏ i ∈ Finset.range j, (lam - i)) / κ *
          ∫ ω in ball (0 : E) 1, sgnPow (lam - j) j ⟪x, ω⟫ * ∏ i, ⟪v i, ω⟫ := by
  intro j
  induction j with
  | zero =>
    intro _ x _ v
    simp only [iteratedFDeriv_zero_apply, Finset.range_zero, Finset.prod_empty, CharP.cast_eq_zero,
      sub_zero, Finset.univ_eq_empty, mul_one, sgnPow, pow_zero, hκ]
    field_simp
  | succ j ih =>
    intro hj x hx v
    have hj' : (j : ℝ) ≤ lam := by push_cast at hj; linarith
    have ha : 1 ≤ lam - j := by push_cast at hj; linarith
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam)) x :=
      ((contDiffOn_normRpow lam (j + 1)).contDiffAt (isOpen_compl_singleton.mem_nhds hx))
        |>.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)
    rw [hdiff.iteratedFDeriv_succ_apply_left']
    have hev : (fun y ↦ iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) y (Fin.tail v)) =ᶠ[𝓝 x]
        fun y ↦ (∏ i ∈ Finset.range j, (lam - i)) / κ *
          ∫ ω in ball (0 : E) 1, sgnPow (lam - j) j ⟪y, ω⟫ * ∏ i, ⟪Fin.tail v i, ω⟫ :=
      eventually_of_mem (isOpen_compl_singleton.mem_nhds hx) fun y hy ↦ ih hj' hy _
    obtain ⟨hint, hder⟩ := hasFDerivAt_integral_sgnPow_mul ha j (continuous_prod_inner (Fin.tail v))
      (fun ω hω ↦ abs_prod_inner_le (Fin.tail v) hω) hx
    rw [hev.fderiv_eq, (hder.const_mul _).fderiv, smul_apply,
      ContinuousLinearMap.integral_apply hint]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only [Finset.prod_range_succ, Fin.prod_univ_succ, Fin.tail, Nat.cast_succ,
      show lam - j - 1 = lam - (j + 1) by ring, real_inner_comm ω (v 0)]
    field_simp

/-- An integral of `g(⟪x,ω⟫) ∏ᵢ ⟪vᵢ,ω⟫` with `|g(u)| ≤ |u|^a` is bounded by `κ ‖x‖^a ∏ᵢ ‖vᵢ‖`. -/
theorem abs_integral_mul_prod_le {lam a κ : ℝ} {j : ℕ} (ha : 0 ≤ a)
    (hlam : a + j = lam) (hpos : 0 < lam) (hκ0 : 0 ≤ κ)
    (hκ : ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam) {g : E → ℝ}
    (x : E) (hg : ∀ ω, |g ω| ≤ |⟪x, ω⟫| ^ a) (v : Fin j → E) :
    |∫ ω in ball (0 : E) 1, g ω * ∏ i, ⟪v i, ω⟫| ≤ κ * (‖x‖ ^ a * ∏ i, ‖v i‖) := by
  refine abs_integral_le_integral_abs.trans <| (integral_mono_of_nonneg
    (ae_of_all _ fun ω ↦ abs_nonneg _) (integrableOn_abs_inner_rpow_mul_prod x ha v)
    (ae_of_all _ fun ω ↦ ?_)).trans (integral_abs_inner_rpow_mul_prod_le ha hlam hpos hκ0 hκ x v)
  simp only
  rw [abs_mul, Finset.abs_prod]
  exact mul_le_mul_of_nonneg_right (hg ω) (Finset.prod_nonneg fun i _ ↦ abs_nonneg _)

end NormPowIteratedFDeriv

open NormPowIteratedFDeriv in
/-- The operator-norm bound on a finite-dimensional space, off the origin (the general case is
`norm_iteratedFDeriv_normRpow_le`). -/
theorem norm_iteratedFDeriv_normRpow_le_of_finiteDimensional {lam : ℝ} {j : ℕ}
    (hj : (j : ℝ) ≤ lam) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x‖
      ≤ (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) := by
  have hlam0 : 0 ≤ lam := (Nat.cast_nonneg j).trans hj
  rcases hlam0.eq_or_lt with hlam | hlam
  · have hj0 : j = 0 := by exact_mod_cast le_antisymm (hlam ▸ hj) (Nat.cast_nonneg j)
    subst hj0
    simp [← hlam]
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨κ, hκpos, hκ⟩ := exists_integral_abs_inner_rpow_eq (E := E) hlam0
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (prod_range_sub_nonneg hj) (Real.rpow_nonneg (norm_nonneg _) _)) fun v ↦ ?_
  rw [Real.norm_eq_abs, iteratedFDeriv_normRpow_eq_integral_of_ne_zero hκ hκpos.ne' j hj hx v,
    abs_mul, abs_div, abs_of_nonneg (prod_range_sub_nonneg hj), abs_of_pos hκpos]
  have h := abs_integral_mul_prod_le (sub_nonneg.2 hj) (by ring) hlam hκpos.le hκ x
    (g := fun ω ↦ sgnPow (lam - j) j ⟪x, ω⟫) (fun ω ↦ abs_sgnPow_le _ _ _) v
  calc (∏ i ∈ Finset.range j, (lam - i)) / κ *
        |∫ ω in ball (0 : E) 1, sgnPow (lam - j) j ⟪x, ω⟫ * ∏ i, ⟪v i, ω⟫|
      ≤ (∏ i ∈ Finset.range j, (lam - i)) / κ * (κ * (‖x‖ ^ (lam - j) * ∏ i, ‖v i‖)) :=
        mul_le_mul_of_nonneg_left h (div_nonneg (prod_range_sub_nonneg hj) hκpos.le)
    _ = _ := by field_simp


end Averaging

/-! ### Reduction to finite-dimensional subspaces -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NormPowIteratedFDeriv

/-- Iterated derivatives of the restriction of a function to a subspace, at a point of an open set
where the function is `C^n`, are the restrictions of its iterated derivatives. -/
theorem _root_.Submodule.iteratedFDeriv_comp_subtypeL_apply (K : Submodule ℝ E) {f : E → ℝ}
    {s : Set E}
    (hs : IsOpen s) {n : ℕ} (hf : ContDiffOn ℝ n f s) {x : K} (hx : (x : E) ∈ s)
    (v : Fin n → K) :
    iteratedFDeriv ℝ n (fun y : K ↦ f y) x v = iteratedFDeriv ℝ n f x fun i ↦ (v i : E) := by
  have hpo : IsOpen (K.subtypeL ⁻¹' s) := hs.preimage K.subtypeL.continuous
  have h1 := K.subtypeL.iteratedFDerivWithin_comp_right hf hs.uniqueDiffOn hpo.uniqueDiffOn hx
    le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpo hx] at h1
  rw [K.coe_subtypeL, Submodule.coe_subtype, iteratedFDerivWithin_of_isOpen n hs hx] at h1
  have h2 := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ K) ℝ ↦ T v) h1
  simpa [Function.comp_def] using h2

/-- A finite-dimensional subspace containing `x` and the vectors `v i`. -/
theorem exists_finiteDimensional_submodule (x : E) {n : ℕ} (v : Fin n → E) :
    ∃ K : Submodule ℝ E, FiniteDimensional ℝ K ∧ x ∈ K ∧ ∀ i, v i ∈ K :=
  ⟨Submodule.span ℝ (insert x (Set.range v)),
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range v).insert x),
    Submodule.subset_span (Set.mem_insert _ _),
    fun i ↦ Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩

end NormPowIteratedFDeriv

open NormPowIteratedFDeriv in
/-- The operator-norm bound `norm_iteratedFDeriv_normRpow_le` off the origin, on any inner
product space: restrict to the finite-dimensional span of `x` and the arguments. -/
theorem norm_iteratedFDeriv_normRpow_le_of_ne_zero {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam)
    {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x‖
      ≤ (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (prod_range_sub_nonneg hj) (Real.rpow_nonneg (norm_nonneg _) _)) fun v ↦ ?_
  obtain ⟨K, hK, hxK, hvK⟩ := exists_finiteDimensional_submodule x v
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have hx' : (⟨x, hxK⟩ : K) ≠ 0 := by simpa using hx
  have h := K.iteratedFDeriv_comp_subtypeL_apply isOpen_compl_singleton (contDiffOn_normRpow lam j)
    (x := ⟨x, hxK⟩) hx (fun i ↦ ⟨v i, hvK i⟩)
  simp only at h
  rw [← h]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_normRpow_le_of_finiteDimensional hj hx')
    (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)

namespace NormPowIteratedFDeriv

/-- A function bounded by `C ‖y‖^b` with `b > 1` has derivative `0` at the origin. -/
theorem _root_.hasFDerivAt_zero_of_norm_le_rpow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {C b : ℝ} (hb : 1 < b) (hg : ∀ y, ‖g y‖ ≤ C * ‖y‖ ^ b) :
    HasFDerivAt g (0 : E →L[ℝ] F) 0 := by
  have hg0 : g 0 = 0 := by
    simpa [Real.zero_rpow (by linarith : b ≠ 0)] using hg 0
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, hg0, sub_zero, zero_apply]
  have h1 : (fun y : E ↦ ‖y‖ ^ (b - 1)) =o[𝓝 0] fun _ ↦ (1 : ℝ) := by
    rw [Asymptotics.isLittleO_one_iff]
    have h := (continuous_norm.rpow_const (p := b - 1) fun _ ↦ Or.inr (by linarith)).tendsto (0 : E)
    rwa [norm_zero, Real.zero_rpow (by linarith : b - 1 ≠ 0)] at h
  have h2 := h1.mul_isBigO (Asymptotics.isBigO_refl (fun y : E ↦ ‖y‖) (𝓝 0))
  have h3 : (fun y : E ↦ ‖y‖ ^ b) =o[𝓝 0] fun y ↦ y := by
    refine (Asymptotics.isLittleO_norm_right.1 ?_)
    refine h2.congr' (Eventually.of_forall fun y ↦ ?_) (Eventually.of_forall fun y ↦ one_mul _)
    rcases eq_or_ne y 0 with rfl | hy
    · simp [Real.zero_rpow (by linarith : b ≠ 0), Real.zero_rpow (by linarith : b - 1 ≠ 0)]
    · change ‖y‖ ^ (b - 1) * ‖y‖ = ‖y‖ ^ b
      rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hy), sub_add_cancel]
  refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound C
    (Eventually.of_forall fun y ↦ ?_)) h3
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact hg y

open Classical in
/-- The Taylor series of `‖·‖^λ` used to prove its smoothness at the origin: the iterated
derivatives off the origin, and `0` at the origin in positive orders. -/
noncomputable def taylorNormRpow (lam : ℝ) (y : E) : FormalMultilinearSeries ℝ E ℝ :=
  fun m ↦ if y = 0 ∧ m ≠ 0 then 0 else iteratedFDeriv ℝ m (fun y : E ↦ ‖y‖ ^ lam) y

/-- Off the origin `taylorNormRpow` is the family of iterated derivatives. -/
theorem taylorNormRpow_of_ne_zero (lam : ℝ) {y : E} (hy : y ≠ 0) (m : ℕ) :
    taylorNormRpow lam y m = iteratedFDeriv ℝ m (fun y : E ↦ ‖y‖ ^ lam) y := by
  simp [taylorNormRpow, hy]

/-- For `λ > 0`, `taylorNormRpow` vanishes at the origin in every order. -/
theorem taylorNormRpow_zero {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    taylorNormRpow lam (0 : E) m = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · ext v
    simp [taylorNormRpow, Real.zero_rpow hlam.ne']
  · simp [taylorNormRpow, hm]

/-- The bound `‖taylorNormRpow λ y m‖ ≤ λ(λ-1)⋯(λ-m+1) ‖y‖^{λ-m}` for `m ≤ λ`. -/
theorem norm_taylorNormRpow_le {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : (m : ℝ) ≤ lam) (y : E) :
    ‖taylorNormRpow lam y m‖ ≤ (∏ i ∈ Finset.range m, (lam - i)) * ‖y‖ ^ (lam - m) := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [taylorNormRpow_zero hlam, norm_zero]
    exact mul_nonneg (prod_range_sub_nonneg hm) (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [taylorNormRpow_of_ne_zero lam hy]
    exact norm_iteratedFDeriv_normRpow_le_of_ne_zero hm hy

/-- For `n < λ`, `taylorNormRpow λ` is a Taylor series of `‖·‖^λ` up to order `n` on the whole
space: each term of order `m < n` is differentiable at the origin with derivative `0` since it is
`O(‖y‖^{λ-m})` with `λ - m > 1`, and each term of order `m ≤ n` is continuous there. -/
theorem hasFTaylorSeriesUpTo_normRpow {lam : ℝ} {n : ℕ} (hn : (n : ℝ) < lam) :
    HasFTaylorSeriesUpTo n (fun y : E ↦ ‖y‖ ^ lam) (taylorNormRpow lam) := by
  have hlam : 0 < lam := (Nat.cast_nonneg n).trans_lt hn
  have hsmooth : ∀ {y : E}, y ≠ 0 → ContDiffAt ℝ (n + 1 : ℕ) (fun y : E ↦ ‖y‖ ^ lam) y :=
    fun hy ↦ (contDiffOn_normRpow lam (n + 1)).contDiffAt (isOpen_compl_singleton.mem_nhds hy)
  have hev : ∀ {y : E}, y ≠ 0 → ∀ m,
      (fun z ↦ taylorNormRpow lam z m) =ᶠ[𝓝 y] iteratedFDeriv ℝ m (fun y : E ↦ ‖y‖ ^ lam) :=
    fun hy m ↦ eventually_of_mem (isOpen_compl_singleton.mem_nhds hy) fun z hz ↦
      taylorNormRpow_of_ne_zero lam hz m
  refine ⟨fun y ↦ ?_, fun m hm y ↦ ?_, fun m hm ↦ ?_⟩
  · simp [taylorNormRpow]
  · have hm' : m < n := by exact_mod_cast hm
    rcases eq_or_ne y 0 with rfl | hy
    · rw [taylorNormRpow_zero hlam]
      have h0 : (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) ↦ E) ℝ).curryLeft = 0 := by
        ext; simp
      rw [h0]
      have hmlam : (m : ℝ) ≤ lam := by
        have : (m : ℝ) < n := by exact_mod_cast hm'
        linarith
      refine hasFDerivAt_zero_of_norm_le_rpow (C := ∏ i ∈ Finset.range m, (lam - i))
        (b := lam - m) ?_ fun z ↦ ?_
      · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm'
        linarith
      · exact norm_taylorNormRpow_le hlam hmlam z
    · have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ m (fun y : E ↦ ‖y‖ ^ lam)) y :=
        (hsmooth hy).differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_of_lt hm')
      refine (hd.hasFDerivAt.congr_of_eventuallyEq (hev hy m)).congr_fderiv ?_
      rw [fderiv_iteratedFDeriv, taylorNormRpow_of_ne_zero lam hy]
      ext h v
      simp
  · have hm' : m ≤ n := by exact_mod_cast hm
    have hmlam : (m : ℝ) < lam := lt_of_le_of_lt (by exact_mod_cast hm') hn
    refine continuous_iff_continuousAt.2 fun y ↦ ?_
    rcases eq_or_ne y 0 with rfl | hy
    · rw [ContinuousAt, taylorNormRpow_zero hlam]
      refine squeeze_zero_norm (fun z ↦ norm_taylorNormRpow_le hlam hmlam.le z) ?_
      simpa [Real.zero_rpow (sub_pos.2 hmlam).ne'] using
        (((continuous_norm.rpow_const fun _ ↦ Or.inr (sub_pos.2 hmlam).le).const_mul
          (∏ i ∈ Finset.range m, (lam - i))).tendsto (0 : E))
    · exact ((hsmooth hy).continuousAt_iteratedFDeriv (by exact_mod_cast
        (hm'.trans (Nat.le_succ n) : m ≤ n + 1))).congr (hev hy m).symm

end NormPowIteratedFDeriv

open NormPowIteratedFDeriv in
/-- **Global smoothness of `‖·‖^λ`.** For `j : ℕ` with `j < λ`, `x ↦ ‖x‖^λ` is `C^j` on the whole
space, including the origin. -/
theorem contDiff_normRpow_of_lt {lam : ℝ} {j : ℕ} (hj : (j : ℝ) < lam) :
    ContDiff ℝ j (fun y : E ↦ ‖y‖ ^ lam) :=
  (hasFTaylorSeriesUpTo_normRpow hj).contDiff

open NormPowIteratedFDeriv in
/-- The derivatives of `‖·‖^λ` of orders `i < λ` vanish at the origin. -/
theorem iteratedFDeriv_normRpow_zero {lam : ℝ} {i : ℕ} (hi : (i : ℝ) < lam) :
    iteratedFDeriv ℝ i (fun y : E ↦ ‖y‖ ^ lam) 0 = 0 := by
  rw [← (hasFTaylorSeriesUpTo_normRpow hi).eq_iteratedFDeriv le_rfl,
    taylorNormRpow_zero ((Nat.cast_nonneg i).trans_lt hi)]

/-- **Sharp operator-norm bound on the derivatives of `‖·‖^λ`** ([cartis2022evaluation],
Lemma B.4.1, (B.4.1)): for `j ≤ λ`,
`‖D^j(‖·‖^λ)(x)‖ ≤ λ(λ-1)⋯(λ-j+1) ‖x‖^{λ-j}` at every `x ≠ 0`, and also at `x = 0` when `j < λ`
(where the derivative vanishes). On a finite-dimensional subspace the derivative is an average of
`|⟪x,ω⟫|^{λ-j} sign(⟪x,ω⟫)^j ∏ᵢ ⟪vᵢ,ω⟫` over the unit ball (`iteratedFDeriv_normRpow_eq_integral`),
and a weighted AM–GM (Hölder-type) inequality bounds that average. -/
theorem norm_iteratedFDeriv_normRpow_le {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam) {x : E}
    (hx : x ≠ 0 ∨ (j : ℝ) < lam) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x‖
      ≤ (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [iteratedFDeriv_normRpow_zero (hx.resolve_left (not_not.2 rfl)), norm_zero]
    exact mul_nonneg (NormPowIteratedFDeriv.prod_range_sub_nonneg hj)
      (Real.rpow_nonneg (norm_nonneg _) _)
  · exact norm_iteratedFDeriv_normRpow_le_of_ne_zero hj hx0

/-- The diagonal form of `norm_iteratedFDeriv_normRpow_le`:
`|D^j(‖·‖^λ)(x)[v]^j| ≤ λ(λ-1)⋯(λ-j+1) ‖x‖^{λ-j} ‖v‖^j`. -/
theorem abs_iteratedFDeriv_normRpow_apply_le {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam) {x : E}
    (hx : x ≠ 0 ∨ (j : ℝ) < lam) (v : E) :
    |iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ v)|
      ≤ (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) * ‖v‖ ^ j := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_normRpow_le hj hx)
    (pow_nonneg (norm_nonneg _) _)

namespace NormPowIteratedFDeriv

/-- `π_j(λ) = λ(λ-1)⋯(λ-j+1)` is the descending Pochhammer polynomial evaluated at `λ`. -/
theorem prod_range_sub_eq_descPochhammer (lam : ℝ) (j : ℕ) :
    ∏ i ∈ Finset.range j, (lam - i) = (descPochhammer ℝ j).eval lam := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.prod_range_succ, ih, descPochhammer_succ_eval]

/-- `∏_{i<k} (n - i) = n!/(n-k)!` (the descending factorial; both sides vanish for `k > n`). -/
theorem prod_range_natCast_sub (n k : ℕ) :
    ∏ i ∈ Finset.range k, ((n : ℝ) - i) = n.descFactorial k := by
  rw [prod_range_sub_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]

/-- `n.descFactorial k = n!/(n-k)!` in `ℝ`, for `k ≤ n`. -/
theorem descFactorial_eq_div (n k : ℕ) (hk : k ≤ n) :
    (n.descFactorial k : ℝ) = n ! / (n - k) ! := by
  rw [eq_div_iff (by positivity), mul_comm, ← Nat.cast_mul, Nat.factorial_mul_descFactorial hk]

end NormPowIteratedFDeriv

/-- `(p+β)! = (p+β)(p+β-1)⋯(p+β-j+1) · (p-j+β)!` for `j ≤ p`, with
`(k+β)! = holderFactorial k β`. -/
theorem holderFactorial_eq_prod_range_mul {p j : ℕ} (hj : j ≤ p) (β : ℝ) :
    holderFactorial p β
      = (∏ i ∈ Finset.range j, ((p : ℝ) + β - i)) * holderFactorial (p - j) β := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih (by omega), Finset.prod_range_succ]
    obtain ⟨k, hk⟩ : ∃ k, p - j = k + 1 := ⟨p - j - 1, by omega⟩
    rw [hk, holderFactorial_succ, show p - (j + 1) = k by omega]
    have : (k : ℝ) + 1 = p - j := by
      have : ((k + 1 : ℕ) : ℝ) = ((p - j : ℕ) : ℝ) := by rw [hk]
      push_cast [Nat.cast_sub (show j ≤ p by omega)] at this
      exact this
    rw [this]
    ring

/-- **The factorial ratio of Lemma B.4.1** ([cartis2022evaluation]): for `j ≤ p` and `β > -1`,
`(p+β)!/(p-j+β)! = π_j(p+β) = ∏_{i<j} (p + β - i)`, where `(k+β)! = holderFactorial k β`. -/
theorem holderFactorial_div_holderFactorial_sub {p j : ℕ} (hj : j ≤ p) {β : ℝ} (hβ : -1 < β) :
    holderFactorial p β / holderFactorial (p - j) β = ∏ i ∈ Finset.range j, ((p : ℝ) + β - i) := by
  have hpos : 0 < holderFactorial (p - j) β := by
    induction p - j with
    | zero => simp
    | succ k ih =>
      rw [holderFactorial_succ]
      exact mul_pos ih (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  rw [holderFactorial_eq_prod_range_mul hj β, mul_div_cancel_right₀ _ hpos.ne']

/-- `∏_{i ≤ p} (p + β - i) = β (p+β)!`, with `(k+β)! = holderFactorial k β`. -/
theorem prod_fin_succ_eq_mul_holderFactorial (p : ℕ) (β : ℝ) :
    ∏ i : Fin (p + 1), ((p : ℝ) + β - i) = β * holderFactorial p β := by
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ (p : ℝ) + β - i), Finset.prod_range_succ,
    holderFactorial_eq_prod_range_mul (le_refl p) β, Nat.sub_self, holderFactorial_zero,
    mul_one]
  ring

namespace NormPowIteratedFDeriv

end NormPowIteratedFDeriv

end General

/-! ### The integral formula and the Lipschitz bound in finite dimension -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open NormPowIteratedFDeriv in
/-- **Integral formula for the derivatives of `‖·‖^λ`.** Let `κ ≠ 0` with
`∫_{‖ω‖<1} |⟪y, ω⟫|^λ dω = κ ‖y‖^λ` for all `y` (`exists_integral_abs_inner_rpow_eq`). For
`j ≤ λ`, and `x ≠ 0` or `j < λ`:
`D^j(‖·‖^λ)(x)[v₁,…,v_j] = λ(λ-1)⋯(λ-j+1)/κ ∫_{‖ω‖<1} |⟪x,ω⟫|^{λ-j} sign(⟪x,ω⟫)^j ∏ᵢ ⟪vᵢ,ω⟫ dω`.
Proved by differentiating under the integral sign, one order at a time. -/
theorem iteratedFDeriv_normRpow_eq_integral {lam κ : ℝ}
    (hκ : ∀ y : E, ∫ ω in ball (0 : E) 1, |⟪y, ω⟫| ^ lam = κ * ‖y‖ ^ lam) (hκ0 : κ ≠ 0)
    {j : ℕ} (hj : (j : ℝ) ≤ lam) {x : E} (hx : x ≠ 0 ∨ (j : ℝ) < lam) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x v
      = (∏ i ∈ Finset.range j, (lam - i)) / κ *
        ∫ ω in ball (0 : E) 1,
          |⟪x, ω⟫| ^ (lam - j) * (SignType.sign ⟪x, ω⟫ : ℝ) ^ j * ∏ i, ⟪v i, ω⟫ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hlt := hx.resolve_left (not_not.2 rfl)
    rw [iteratedFDeriv_normRpow_zero hlt]
    simp [Real.zero_rpow (sub_pos.2 hlt).ne']
  · exact iteratedFDeriv_normRpow_eq_integral_of_ne_zero hκ hκ0 j hj hx0 v

namespace NormPowIteratedFDeriv

/-- The finite-dimensional core of `iteratedFDerivLipschitzOn_norm_pow`:
`|D^j(‖·‖^{j+1})(x)[v] - D^j(‖·‖^{j+1})(y)[v]| ≤ (j+1)! ‖x - y‖ ∏ᵢ ‖vᵢ‖`. -/
theorem abs_iteratedFDeriv_normRpow_sub_le_of_finiteDimensional (j : ℕ) (x y : E)
    (v : Fin j → E) :
    |iteratedFDeriv ℝ j (fun z : E ↦ ‖z‖ ^ ((j : ℝ) + 1)) x v
        - iteratedFDeriv ℝ j (fun z : E ↦ ‖z‖ ^ ((j : ℝ) + 1)) y v|
      ≤ (j + 1)! * ‖x - y‖ * ∏ i, ‖v i‖ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, abs_zero]
    positivity
  have : Nontrivial E := ⟨⟨x - y, 0, sub_ne_zero.2 hxy⟩⟩
  set lam : ℝ := (j : ℝ) + 1
  have hlam : 0 < lam := by positivity
  have hjl : (j : ℝ) < lam := lt_add_one _
  obtain ⟨κ, hκpos, hκ⟩ := exists_integral_abs_inner_rpow_eq (E := E) hlam.le
  have hsub : lam - j = 1 := by ring
  have hc : ∏ i ∈ Finset.range j, (lam - i) = (j + 1)! := by
    have h := prod_range_natCast_sub (j + 1) j
    rw [descFactorial_eq_div _ _ (Nat.le_succ j), show j + 1 - j = 1 by omega, Nat.factorial_one,
      Nat.cast_one, div_one] at h
    simpa [lam] using h
  have hint : ∀ z : E, Integrable (fun ω ↦ |⟪z, ω⟫| ^ (lam - j) *
      (SignType.sign ⟪z, ω⟫ : ℝ) ^ j * ∏ i, ⟪v i, ω⟫) (volume.restrict (ball (0 : E) 1)) := by
    intro z
    refine integrableOn_ball_of_le ((((measurable_sgnPow (lam - j) j).comp
      (continuous_const.inner continuous_id).measurable).mul
      (continuous_prod_inner v).measurable).aestronglyMeasurable) (‖z‖ ^ (lam - j) *
        ∏ i, ‖v i‖) fun ω hω ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_sgnPow_le _ _ _).trans (Real.rpow_le_rpow (abs_nonneg _)
      (abs_inner_le_of_mem_ball hω) (by rw [hsub]; exact zero_le_one)))
      (abs_prod_inner_le v hω) (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [iteratedFDeriv_normRpow_eq_integral hκ hκpos.ne' hjl.le (Or.inr hjl),
    iteratedFDeriv_normRpow_eq_integral hκ hκpos.ne' hjl.le (Or.inr hjl), ← mul_sub,
    ← integral_sub (hint x) (hint y), hc, abs_mul, abs_div, abs_of_pos hκpos,
    Nat.abs_cast]
  have h := abs_integral_mul_prod_le (a := 1) zero_le_one (by ring) hlam hκpos.le hκ (x - y)
    (g := fun ω ↦ sgnPow 1 j ⟪x, ω⟫ - sgnPow 1 j ⟪y, ω⟫) (fun ω ↦ ?_) v
  · simp only [Real.rpow_one] at h
    rw [show (fun ω ↦ |⟪x, ω⟫| ^ (lam - j) * (SignType.sign ⟪x, ω⟫ : ℝ) ^ j * ∏ i, ⟪v i, ω⟫ -
        |⟪y, ω⟫| ^ (lam - j) * (SignType.sign ⟪y, ω⟫ : ℝ) ^ j * ∏ i, ⟪v i, ω⟫)
        = fun ω ↦ (sgnPow 1 j ⟪x, ω⟫ - sgnPow 1 j ⟪y, ω⟫) * ∏ i, ⟪v i, ω⟫ by
          funext ω; rw [hsub, sgnPow, sgnPow]; ring]
    calc ((j + 1)! : ℝ) / κ *
          |∫ ω in ball (0 : E) 1, (sgnPow 1 j ⟪x, ω⟫ - sgnPow 1 j ⟪y, ω⟫) * ∏ i, ⟪v i, ω⟫|
        ≤ (j + 1)! / κ * (κ * (‖x - y‖ * ∏ i, ‖v i‖)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by field_simp
  · have h1 := abs_sgnPow_sub_le (le_refl (1 : ℝ)) j (le_max_left |⟪x, ω⟫| |⟪y, ω⟫|)
      (le_max_right |⟪x, ω⟫| |⟪y, ω⟫|)
    rw [sub_self, Real.rpow_zero, one_mul, one_mul, ← inner_sub_left] at h1
    rwa [Real.rpow_one]

end NormPowIteratedFDeriv

end FiniteDimensional

/-! ### Radial values, the norm, and the Lipschitz bound on any inner product space -/

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open NormPowIteratedFDeriv

/-- **Radial values** ([cartis2022evaluation], (B.4.2)): for every real `λ`, every `j` and
`x ≠ 0`, `D^j(‖·‖^λ)(x)[x]^j = λ(λ-1)⋯(λ-j+1) ‖x‖^λ`. -/
theorem iteratedFDeriv_normRpow_apply_self (lam : ℝ) (j : ℕ) {x : E} (hx : x ≠ 0) :
    iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ x)
      = (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ lam := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hxu : (fun _ : Fin j ↦ x) = fun _ ↦ ‖x‖ • (‖x‖⁻¹ • x) := by
    funext
    rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  rw [hxu, ContinuousMultilinearMap.map_smul_univ, iteratedFDeriv_normRpow_apply_unit lam j hx,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.prod_range,
    ← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hnx, add_sub_cancel]

/-- **The operator norm of the derivatives of `‖·‖^λ`** ([cartis2022evaluation], (B.4.1) as an
equality): for `j ≤ λ` and `x ≠ 0`, `‖D^j(‖·‖^λ)(x)‖ = λ(λ-1)⋯(λ-j+1) ‖x‖^{λ-j}`, attained in the
radial direction. For `λ = j = p + 1` this is `‖∇^{p+1} ‖x‖^{p+1}‖ = (p+1)!`, the case `β = 1` of
the book's (B.4.3). -/
theorem norm_iteratedFDeriv_normRpow {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam) {x : E}
    (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x‖
      = (∏ i ∈ Finset.range j, (lam - i)) * ‖x‖ ^ (lam - j) := by
  refine le_antisymm (norm_iteratedFDeriv_normRpow_le hj (Or.inl hx)) ?_
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x)
    fun _ ↦ ‖x‖⁻¹ • x
  rw [iteratedFDeriv_normRpow_apply_unit lam j hx, ← Finset.prod_range (fun i ↦ lam - i)] at h
  simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne', Finset.prod_const_one,
    mul_one] at h
  exact (le_abs_self _).trans h

/-- `‖·‖^{j+1}` has `(j+1)!`-Lipschitz `j`-th derivative on the whole space. -/
theorem iteratedFDerivLipschitzOn_normRpow_add_one (j : ℕ) :
    IteratedFDerivLipschitzOn (fun z : E ↦ ‖z‖ ^ ((j : ℝ) + 1)) j ((j + 1)! : ℝ) univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro x _ y _
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  obtain ⟨K, hK, hxK, hvK⟩ := exists_finiteDimensional_submodule x (Fin.cons y v)
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have hyK : y ∈ K := by simpa using hvK 0
  have hvK' : ∀ i, v i ∈ K := fun i ↦ by simpa using hvK i.succ
  have hf : ContDiffOn ℝ j (fun z : E ↦ ‖z‖ ^ ((j : ℝ) + 1)) univ :=
    (contDiff_normRpow_of_lt (lt_add_one _)).contDiffOn
  have hx' := K.iteratedFDeriv_comp_subtypeL_apply isOpen_univ hf (x := ⟨x, hxK⟩) (mem_univ _)
    (fun i ↦ ⟨v i, hvK' i⟩)
  have hy' := K.iteratedFDeriv_comp_subtypeL_apply isOpen_univ hf (x := ⟨y, hyK⟩) (mem_univ _)
    (fun i ↦ ⟨v i, hvK' i⟩)
  simp only at hx' hy'
  rw [sub_apply, ← hx', ← hy', Real.norm_eq_abs]
  exact abs_iteratedFDeriv_normRpow_sub_le_of_finiteDimensional (E := K) j ⟨x, hxK⟩ ⟨y, hyK⟩
    fun i ↦ ⟨v i, hvK' i⟩

end Radial

/-! ### Natural exponents -/

section NaturalPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open NormPowIteratedFDeriv

namespace NormPowIteratedFDeriv

omit [InnerProductSpace ℝ E] in
/-- The natural power `‖s‖^r` as the real power `‖s‖^(r : ℝ)`. -/
theorem norm_pow_eq_normRpow (r : ℕ) :
    (fun s : E ↦ ‖s‖ ^ r) = fun s : E ↦ ‖s‖ ^ (r : ℝ) :=
  funext fun s ↦ (Real.rpow_natCast ‖s‖ r).symm

/-- `∏_{i<ℓ} (r - i) = r!/(r-ℓ)!` for natural `ℓ ≤ r`. -/
theorem prod_range_natCast_sub_eq_div {r ℓ : ℕ} (h : ℓ ≤ r) :
    ∏ i ∈ Finset.range ℓ, ((r : ℝ) - i) = r ! / (r - ℓ) ! := by
  rw [prod_range_natCast_sub, descFactorial_eq_div r ℓ h]

omit [InnerProductSpace ℝ E] in
/-- `‖s‖^{(r:ℝ) - ℓ} = ‖s‖^{r-ℓ}` for natural `ℓ ≤ r`. -/
theorem norm_rpow_natCast_sub {r ℓ : ℕ} (h : ℓ ≤ r) (s : E) :
    ‖s‖ ^ ((r : ℝ) - ℓ) = ‖s‖ ^ (r - ℓ) := by
  rw [← Nat.cast_sub h, Real.rpow_natCast]

end NormPowIteratedFDeriv

/-- **Smoothness of `‖·‖^r` for natural `r ≥ 1`**: it is `C^{r-1}` on the whole space. In
particular the regularization term `‖s‖^{p+1}` is `C^p`. -/
theorem contDiff_norm_pow {r : ℕ} (hr : 1 ≤ r) :
    ContDiff ℝ (r - 1 : ℕ) (fun s : E ↦ ‖s‖ ^ r) := by
  rw [norm_pow_eq_normRpow]
  refine contDiff_normRpow_of_lt ?_
  rw [Nat.cast_sub hr]
  simp

/-- For even `r`, `‖s‖^r = (‖s‖²)^{r/2}` is a polynomial, hence analytic. -/
theorem contDiff_norm_pow_of_even {r : ℕ} (hr : Even r) :
    ContDiff ℝ ⊤ (fun s : E ↦ ‖s‖ ^ r) := by
  obtain ⟨m, rfl⟩ := hr
  simp_rw [← two_mul, pow_mul]
  exact contDiff_norm_sq ℝ |>.pow m

/-- Away from the origin `‖·‖^r` is analytic, for every natural `r`. -/
theorem contDiffAt_norm_pow (r : ℕ) {s : E} (hs : s ≠ 0) :
    ContDiffAt ℝ ⊤ (fun s : E ↦ ‖s‖ ^ r) s :=
  (contDiffAt_norm ℝ hs).pow r

/-- **Radial values for natural exponents** ([cartis2022evaluation], (B.4.2) with `β = 1`): for
`ℓ ≤ r`, and `s ≠ 0` or `ℓ < r`,
`D^ℓ(‖·‖^r)(s)[s]^ℓ = r!/(r-ℓ)! ‖s‖^r`. -/
theorem iteratedFDeriv_norm_pow_apply_self {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E}
    (hs : s ≠ 0 ∨ ℓ < r) :
    iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s (fun _ ↦ s) = r ! / (r - ℓ) ! * ‖s‖ ^ r := by
  rw [norm_pow_eq_normRpow]
  rcases eq_or_ne s 0 with rfl | hs0
  · have hlt := hs.resolve_left (not_not.2 rfl)
    rw [iteratedFDeriv_normRpow_zero (by exact_mod_cast hlt)]
    simp [(Nat.zero_le ℓ).trans_lt hlt |>.ne']
  · rw [iteratedFDeriv_normRpow_apply_self _ _ hs0, prod_range_natCast_sub_eq_div hℓ,
      Real.rpow_natCast]

/-- **Sharp operator-norm bound for natural exponents** ([cartis2022evaluation], Lemma B.4.1
with `β = 1`): for `ℓ ≤ r`, and `s ≠ 0` or `ℓ < r`,
`‖D^ℓ(‖·‖^r)(s)‖ ≤ r!/(r-ℓ)! ‖s‖^{r-ℓ}`, with equality for `s ≠ 0`
(`norm_iteratedFDeriv_norm_pow`). -/
theorem norm_iteratedFDeriv_norm_pow_le {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E} (hs : s ≠ 0 ∨ ℓ < r) :
    ‖iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s‖ ≤ r ! / (r - ℓ) ! * ‖s‖ ^ (r - ℓ) := by
  rw [norm_pow_eq_normRpow, ← prod_range_natCast_sub_eq_div hℓ, ← norm_rpow_natCast_sub hℓ]
  exact norm_iteratedFDeriv_normRpow_le (by exact_mod_cast hℓ) (by exact_mod_cast hs)

/-- The equality case of `norm_iteratedFDeriv_norm_pow_le`: for `ℓ ≤ r` and `s ≠ 0`,
`‖D^ℓ(‖·‖^r)(s)‖ = r!/(r-ℓ)! ‖s‖^{r-ℓ}`. -/
theorem norm_iteratedFDeriv_norm_pow {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E} (hs : s ≠ 0) :
    ‖iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s‖ = r ! / (r - ℓ) ! * ‖s‖ ^ (r - ℓ) := by
  rw [norm_pow_eq_normRpow, ← prod_range_natCast_sub_eq_div hℓ, ← norm_rpow_natCast_sub hℓ]
  exact norm_iteratedFDeriv_normRpow (by exact_mod_cast hℓ) hs

/-- Diagonal form of `norm_iteratedFDeriv_norm_pow_le`: for `ℓ ≤ r`, and `s ≠ 0` or `ℓ < r`,
`|D^ℓ(‖·‖^r)(s)[d]^ℓ| ≤ r!/(r-ℓ)! ‖s‖^{r-ℓ} ‖d‖^ℓ`, with equality for `d = s`
(`iteratedFDeriv_norm_pow_apply_self`). -/
theorem abs_iteratedFDeriv_norm_pow_apply_le {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E}
    (hs : s ≠ 0 ∨ ℓ < r) (d : E) :
    |iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s (fun _ ↦ d)|
      ≤ r ! / (r - ℓ) ! * ‖s‖ ^ (r - ℓ) * ‖d‖ ^ ℓ := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_norm_pow_le hℓ hs)
    (pow_nonneg (norm_nonneg _) _)

/-- **Lipschitz continuity of `∇^{r-1} ‖·‖^r`** ([cartis2022evaluation], (B.4.3) with `β = 1`):
for `r ≥ 1` the `(r-1)`-th derivative of `‖·‖^r` is `r!`-Lipschitz on the whole space. -/
theorem iteratedFDerivLipschitzOn_norm_pow {r : ℕ} (hr : 1 ≤ r) :
    IteratedFDerivLipschitzOn (fun s : E ↦ ‖s‖ ^ r) (r - 1) (r ! : ℝ) univ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hr
  rw [norm_pow_eq_normRpow, Nat.add_sub_cancel]
  simpa using iteratedFDerivLipschitzOn_normRpow_add_one (E := E) j

/-- **Taylor remainder of `‖·‖^r`** at order `r - 1`: for `r ≥ 1` and all `s, d`,
`|‖s + d‖^r - T_{r-1}(s, d)| ≤ ‖d‖^r`, where `T_{r-1}` is the Taylor polynomial of `‖·‖^r` at
`s`. -/
theorem abs_norm_pow_sub_taylorPolynomial_le {r : ℕ} (hr : 1 ≤ r) (s d : E) :
    |‖s + d‖ ^ r - taylorPolynomial (fun s : E ↦ ‖s‖ ^ r) (r - 1) s d| ≤ ‖d‖ ^ r := by
  have h := abs_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ ↦ (contDiff_norm_pow (E := E) hr).contDiffAt) (iteratedFDerivLipschitzOn_norm_pow hr)
    (mem_univ s) (mem_univ (s + d))
  rwa [Nat.sub_add_cancel hr, div_self (by positivity), one_mul] at h

/-- On the unit ball, `‖∇^ℓ ‖·‖^r (s)‖ ≤ r!` for `ℓ ≤ r` (and `s ≠ 0` or `ℓ < r`). -/
theorem norm_iteratedFDeriv_norm_pow_le_factorial {r ℓ : ℕ} (hℓ : ℓ ≤ r) {s : E}
    (hs0 : s ≠ 0 ∨ ℓ < r)
    (hs : ‖s‖ ≤ 1) : ‖iteratedFDeriv ℝ ℓ (fun s : E ↦ ‖s‖ ^ r) s‖ ≤ r ! := by
  refine (norm_iteratedFDeriv_norm_pow_le hℓ hs0).trans ?_
  have h1 : ‖s‖ ^ (r - ℓ) ≤ 1 := pow_le_one₀ (norm_nonneg _) hs
  have h2 : (r ! : ℝ) / (r - ℓ)! ≤ r ! :=
    div_le_self (by positivity)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  calc (r ! : ℝ) / (r - ℓ)! * ‖s‖ ^ (r - ℓ) ≤ (r ! : ℝ) / (r - ℓ)! * 1 := by gcongr
    _ ≤ r ! := by rw [mul_one]; exact h2


end NaturalPower

/-! ### Counterexample to (B.4.3) for `β < 1`, and the convexity claims of Lemma B.4.1 -/

section Convexity

open NormPowIteratedFDeriv

/-- **(B.4.3) is false for fractional `β`.** For `p = 1`, `β = 1/2` (so `λ = p + β = 3/2`) and
`x = e₀ ∈ ℝ²`, the operator norm of `D²(‖·‖^{3/2})(x)` exceeds the book's value
`β (p+β)! ‖x‖^{β-1} = 3/4`: the derivative in the direction `e₁ ⊥ x` is already `3/2`. -/
theorem not_norm_iteratedFDeriv_normRpow_eq_radial :
    (1 / 2 : ℝ) * holderFactorial 1 (1 / 2)
        * ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖ ^ ((1 / 2 : ℝ) - 1)
      < ‖iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ (3 / 2 : ℝ))
          (EuclideanSpace.single 0 1)‖ := by
  set x : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  set u : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  have hx : ‖x‖ = 1 := by simp [x]
  have hu : ‖u‖ = 1 := by simp [u]
  have hxu : ⟪x, u⟫ = 0 := by simp [x, u, EuclideanSpace.inner_single_left]
  have hx0 : x ≠ 0 := fun h ↦ by simp [h] at hx
  have h := iteratedFDeriv_normRpow_apply_perp (3 / 2 : ℝ) 2 hx0 hu hxu
  have h2 := iteratedDeriv_one_add_sq_rpow_two_mul (3 / 2 : ℝ) 1
  simp only [mul_one, Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero, CharP.cast_eq_zero,
    mul_zero, zero_add, sub_zero, Finset.prod_singleton, one_mul] at h2
  rw [h2, hx, Real.one_rpow, one_mul] at h
  have hle := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) ↦ ‖y‖ ^ (3 / 2 : ℝ)) x) fun _ ↦ u
  rw [h, hu] at hle
  have hβ : holderFactorial 1 (1 / 2) = 3 / 2 := by
    simp [holderFactorial]
    norm_num
  rw [hβ, hx, Real.one_rpow]
  norm_num at hle ⊢
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NormPowIteratedFDeriv

/-- The odd-order derivatives of the even function `(1 + t²)^{λ/2}` vanish at `0`. -/
theorem iteratedDeriv_one_add_sq_rpow_two_mul_add_one (lam : ℝ) (m : ℕ) :
    iteratedDeriv (2 * m + 1) (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, iteratedDeriv_one_add_sq_rpow_succ_succ, ih,
      mul_zero]

/-- The derivatives of `(1 + t²)^{λ/2}` at `0` of orders `j ≤ λ + 2` are nonnegative. -/
theorem iteratedDeriv_one_add_sq_rpow_nonneg {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam + 2) :
    0 ≤ iteratedDeriv j (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [iteratedDeriv_one_add_sq_rpow_two_mul]
    refine Finset.prod_nonneg fun i _ ↦ mul_nonneg (by positivity) ?_
    have : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
    push_cast at hj
    linarith
  · rw [iteratedDeriv_one_add_sq_rpow_two_mul_add_one]

/-- The derivatives of `‖·‖^λ` at `x ≠ 0` in a direction `d ⊥ x`:
`D^j(‖·‖^λ)(x)[d]^j = ‖x‖^{λ-j} h^{(j)}(0) ‖d‖^j` with `h(t) = (1 + t²)^{λ/2}`. -/
theorem iteratedFDeriv_normRpow_apply_of_inner_eq_zero (lam : ℝ) (j : ℕ) {x d : E}
    (hx : x ≠ 0) (hxd : ⟪x, d⟫ = 0) :
    iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ d)
      = ‖x‖ ^ (lam - j) * iteratedDeriv j (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 * ‖d‖ ^ j := by
  obtain ⟨K, hK, hxK, hdK⟩ := exists_finiteDimensional_submodule x fun _ : Fin 1 ↦ d
  have h := K.iteratedFDeriv_comp_subtypeL_apply isOpen_compl_singleton (contDiffOn_normRpow lam j)
    (x := ⟨x, hxK⟩) hx (fun _ ↦ ⟨d, hdK 0⟩)
  simp only at h
  rw [← h]
  set x' : K := ⟨x, hxK⟩
  set d' : K := ⟨d, hdK 0⟩
  have hx' : x' ≠ 0 := by simpa [x'] using hx
  change iteratedFDeriv ℝ j (fun y : K ↦ ‖y‖ ^ lam) x' (fun _ ↦ d')
    = ‖x'‖ ^ (lam - j) * _ * ‖d'‖ ^ j
  rcases eq_or_ne d' 0 with hd | hd
  · rcases j.eq_zero_or_pos with rfl | hj
    · simp
    · rw [hd, ContinuousMultilinearMap.map_coord_zero _ ⟨0, hj⟩ rfl, norm_zero,
        zero_pow hj.ne', mul_zero]
  have hnd : 0 < ‖d'‖ := norm_pos_iff.2 hd
  have hu : ‖‖d'‖⁻¹ • d'‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnd.ne']
  have hxu : ⟪x', ‖d'‖⁻¹ • d'⟫ = 0 := by
    rw [real_inner_smul_right]
    change ‖d'‖⁻¹ * ⟪x, d⟫ = 0
    rw [hxd, mul_zero]
  have hdu : (fun _ : Fin j ↦ d') = fun _ ↦ ‖d'‖ • (‖d'‖⁻¹ • d') := by
    funext
    rw [smul_smul, mul_inv_cancel₀ hnd.ne', one_smul]
  rw [hdu, ContinuousMultilinearMap.map_smul_univ, iteratedFDeriv_normRpow_apply_perp lam j hx' hu
    hxu, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end NormPowIteratedFDeriv

/-- **The convexity claims of Lemma B.4.1** ([cartis2022evaluation]). Let `x ≠ 0` and
`j ≤ λ + 2`.
(a) On the orthogonal complement of `x`, `d ↦ D^j(‖·‖^λ)(x)[d]^j` is convex: it equals
`c ‖d‖^j` with `c = ‖x‖^{λ-j} h^{(j)}(0) ≥ 0`, `h(t) = (1 + t²)^{λ/2}` (and `c = 0` for odd `j`).
(b) For even `j ≤ λ + 1`, `t ↦ D^j(‖·‖^λ)(x)[t x]^j = t^j λ(λ-1)⋯(λ-j+1) ‖x‖^λ` is convex
on `ℝ`.
For `λ = p + β` the range `j ≤ λ + 1` of (b) covers the derivatives `j ≤ p + 1` that the lemma is
about; beyond it the coefficient `λ(λ-1)⋯(λ-j+1)` can be negative. -/
theorem convexOn_iteratedFDeriv_normRpow {lam : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ lam + 2) {x : E}
    (hx : x ≠ 0) :
    ConvexOn ℝ ((ℝ ∙ x)ᗮ : Set E)
        (fun d ↦ iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ d)) ∧
      (Even j → (j : ℝ) ≤ lam + 1 → ConvexOn ℝ univ
        (fun t : ℝ ↦ iteratedFDeriv ℝ j (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ t • x))) := by
  refine ⟨?_, fun hje hj1 ↦ ?_⟩
  · have hc : 0 ≤ ‖x‖ ^ (lam - j) * iteratedDeriv j (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (iteratedDeriv_one_add_sq_rpow_nonneg hj)
    refine (((convexOn_norm (ℝ ∙ x)ᗮ.convex).pow fun d _ ↦ norm_nonneg d) j).smul hc
      |>.congr fun d hd ↦ ?_
    rw [iteratedFDeriv_normRpow_apply_of_inner_eq_zero lam j hx
      ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 hd)]
    simp [smul_eq_mul, mul_assoc]
  · have hπ : 0 ≤ ∏ i ∈ Finset.range j, (lam - i) := Finset.prod_nonneg fun i hi ↦ by
      have : (i : ℝ) + 1 ≤ j := by exact_mod_cast Finset.mem_range.1 hi
      linarith
    refine (hje.convexOn_pow.smul (mul_nonneg hπ (Real.rpow_nonneg (norm_nonneg x) lam)))
      |>.congr fun t _ ↦ ?_
    simp only [smul_eq_mul]
    rw [ContinuousMultilinearMap.map_smul_univ, iteratedFDeriv_normRpow_apply_self lam j hx,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring

end Convexity
