import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Exact Gaussian projection and product-moment bounds

Projection and scaling laws identify every absolute projected moment with the
corresponding scalar Gaussian moment times a norm power. Positivity and
integrability hold in every natural degree. Normalization followed by AM-GM
gives a sharp product bound even for dependent projections; repeated directions
give its mixed-power form.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A standard Gaussian projected onto a direction has the same law as a
standard real Gaussian scaled by that direction norm. -/
theorem stdGaussian_inner_map (x : E) :
    (stdGaussian E).map (innerSL ℝ x) =
      (gaussianReal 0 1).map (fun t : ℝ => ‖x‖ * t) := by
  rw [IsGaussian.map_eq_gaussianReal, gaussianReal_map_const_mul]
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  simp

/-- The absolute projected moment of a standard Gaussian is the corresponding
real Gaussian moment times the direction norm to that power. -/
theorem integral_abs_inner_pow_stdGaussian (m : ℕ) (x : E) :
    ∫ z : E, |inner ℝ x z| ^ m ∂(stdGaussian E) =
      ‖x‖ ^ m * ∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1) := by
  have hm := stdGaussian_inner_map x
  calc
    ∫ z : E, |inner ℝ x z| ^ m ∂(stdGaussian E) =
        ∫ t : ℝ, |t| ^ m ∂((stdGaussian E).map (innerSL ℝ x)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ∫ t : ℝ, |‖x‖ * t| ^ m ∂(gaussianReal 0 1) := by
      rw [hm, integral_map (by fun_prop) (by fun_prop)]
    _ = _ := by
      simp_rw [abs_mul, abs_of_nonneg (norm_nonneg x), mul_pow]
      rw [integral_const_mul]

/-- Every natural absolute moment of a standard real Gaussian is integrable. -/
theorem integrable_abs_pow_gaussianReal (m : ℕ) :
    Integrable (fun t : ℝ => |t| ^ m) (gaussianReal 0 1) := by
  have hh := (memLp_id_gaussianReal (μ := 0) (v := 1) (m : ℝ≥0)).integrable_norm_pow'
  simpa using hh

/-- Every natural absolute moment of a standard real Gaussian is strictly positive. -/
theorem integral_abs_pow_gaussianReal_pos (m : ℕ) :
    0 < ∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1) := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hpos : ∀ᵐ t : ℝ ∂(gaussianReal 0 1), 0 < |t| ^ m :=
    ((gaussianReal 0 1).ae_ne 0).mono fun t ht => pow_pos (abs_pos.mpr ht) m
  have hs : Function.support (fun t : ℝ => |t| ^ m) =ᵐ[gaussianReal 0 1] Set.univ := by
    filter_upwards [hpos] with t ht
    simp [Function.mem_support, ht.ne']
  rw [integral_pos_iff_support_of_nonneg (fun t => pow_nonneg (abs_nonneg t) m)
    (integrable_abs_pow_gaussianReal m), measure_congr hs]
  simp

/-- A natural norm power is exactly a positive normalized Gaussian average
of the corresponding absolute linear power. -/
theorem norm_pow_eq_integral_abs_inner_pow_stdGaussian (m : ℕ) (x : E) :
    ‖x‖ ^ m = (∫ z : E, |inner ℝ x z| ^ m ∂(stdGaussian E)) /
      (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) := by
  apply (eq_div_iff (integral_abs_pow_gaussianReal_pos m).ne').mpr
  exact (integral_abs_inner_pow_stdGaussian m x).symm

/-- Every natural absolute moment of a Gaussian projection is integrable. -/
theorem integrable_abs_inner_pow_stdGaussian (m : ℕ) (x : E) :
    Integrable (fun z : E => |inner ℝ x z| ^ m) (stdGaussian E) := by
  have hm : MemLp (innerSL ℝ x) m (stdGaussian E) :=
    IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) m (by simp)
  have hh := hm.integrable_norm_pow'
  simpa only [Real.norm_eq_abs, innerSL_apply_apply] using hh

private theorem prod_le_mean_pow {m : ℕ} (hm : 0 < m)
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∏ i, a i ≤ (m : ℝ)⁻¹ * ∑ i, a i ^ m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hh := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin m => (m : ℝ)⁻¹) (fun i => a i ^ m)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg m))
    (by simp [hm0]) (fun i _ => pow_nonneg (ha i) m)
  have hp (i : Fin m) : (a i ^ m) ^ ((m : ℝ)⁻¹) = a i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (ha i), mul_inv_cancel₀ hm0, Real.rpow_one]
  simp_rw [hp] at hh
  simpa only [← Finset.mul_sum] using hh

/-- Every finite product of absolute Gaussian projections is integrable. -/
theorem integrable_prod_abs_inner_stdGaussian {m : ℕ} (v : Fin m → E) :
    Integrable (fun z : E => ∏ i, |inner ℝ (v i) z|) (stdGaussian E) := by
  by_cases hm : m = 0
  · subst m
    simp
  have hsum : Integrable (fun z : E => (m : ℝ)⁻¹ * ∑ i, |inner ℝ (v i) z| ^ m)
      (stdGaussian E) :=
    (integrable_finsetSum _ fun i _ => integrable_abs_inner_pow_stdGaussian m (v i)).const_mul _
  apply hsum.mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => abs_nonneg _)]
    exact prod_le_mean_pow (Nat.pos_of_ne_zero hm) _ (fun _ => abs_nonneg _)

/-- The mean product of m absolute unit-direction Gaussian projections is
bounded by the mth absolute moment of a standard real Gaussian. -/
theorem integral_prod_abs_inner_stdGaussian_le_of_unit {m : ℕ} (v : Fin m → E)
    (hv : ∀ i, ‖v i‖ = 1) :
    ∫ z : E, ∏ i, |inner ℝ (v i) z| ∂(stdGaussian E) ≤
      ∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1) := by
  by_cases hm : m = 0
  · subst m
    simp
  have hsum : Integrable (fun z : E => (m : ℝ)⁻¹ * ∑ i, |inner ℝ (v i) z| ^ m)
      (stdGaussian E) :=
    (integrable_finsetSum _ fun i _ => integrable_abs_inner_pow_stdGaussian m (v i)).const_mul _
  calc
    _ ≤ ∫ z : E, (m : ℝ)⁻¹ * ∑ i, |inner ℝ (v i) z| ^ m ∂(stdGaussian E) :=
      integral_mono (integrable_prod_abs_inner_stdGaussian v) hsum
        (fun z => prod_le_mean_pow (Nat.pos_of_ne_zero hm) _ (fun _ => abs_nonneg _))
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      · simp only [integral_abs_inner_pow_stdGaussian, hv, one_pow, one_mul,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_mul]
      · intro i _
        exact integrable_abs_inner_pow_stdGaussian m (v i)

/-- A Gaussian product-moment bound with the exact common absolute moment
and the product of direction norms. The directions need not be independent. -/
theorem integral_prod_abs_inner_stdGaussian_le {m : ℕ} (v : Fin m → E) :
    ∫ z : E, ∏ i, |inner ℝ (v i) z| ∂(stdGaussian E) ≤
      (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) * ∏ i, ‖v i‖ := by
  classical
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hz
    have hp (z : E) : ∏ j, |inner ℝ (v j) z| = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    have hpn : ∏ j, ‖v j‖ = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    simp only [hp, integral_zero, hpn, mul_zero, le_refl]
  have hn (i : Fin m) : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr (fun hh => hz ⟨i, hh⟩)
  let u : Fin m → E := fun i => ‖v i‖⁻¹ • v i
  have hu (i : Fin m) : ‖u i‖ = 1 := by
    simp only [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (hn i)
  have hvu (i : Fin m) : ‖v i‖ • u i = v i := by
    simp [u, smul_smul, hn i]
  have hp (z : E) : (∏ i, ‖v i‖) * ∏ i, |inner ℝ (u i) z| =
      ∏ i, |inner ℝ (v i) z| := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    calc
      ‖v i‖ * |inner ℝ (u i) z| = |inner ℝ (‖v i‖ • u i) z| := by
        simp only [real_inner_smul_left, abs_mul, abs_of_nonneg (norm_nonneg (v i))]
      _ = _ := by rw [hvu]
  calc
    _ = (∏ i, ‖v i‖) * ∫ z : E, ∏ i, |inner ℝ (u i) z| ∂(stdGaussian E) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hp z).symm)
    _ ≤ (∏ i, ‖v i‖) * ∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1) :=
      mul_le_mul_of_nonneg_left (integral_prod_abs_inner_stdGaussian_le_of_unit u hu)
        (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = _ := mul_comm _ _

/-- A mixed Gaussian moment with one direction repeated k times satisfies
the exact degree-(k+j) moment bound and product of direction norms. -/
theorem integral_abs_inner_pow_mul_prod_stdGaussian_le (k j : ℕ) (x : E) (v : Fin j → E) :
    ∫ z : E, |inner ℝ x z| ^ k * ∏ i, |inner ℝ (v i) z| ∂(stdGaussian E) ≤
      (∫ t : ℝ, |t| ^ (k + j) ∂(gaussianReal 0 1)) * ‖x‖ ^ k * ∏ i, ‖v i‖ := by
  have hh := integral_prod_abs_inner_stdGaussian_le (Fin.append (fun _ : Fin k => x) v)
  simpa only [Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_assoc] using hh

end ProbabilityTheory
