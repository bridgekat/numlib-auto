import Numlib.Optimization.SecondOrder.SharpnessHistory

/-!
# Uniform Hermite residuals for second-order method histories

Actual method-generated displacements are bounded above and below by fixed
multiples of the square-root accuracy. The prescribed objective and derivative
jets therefore satisfy uniform quadratic-Hermite residual estimates.
-/

namespace ShiftedNewton.Sharpness
open Polynomial

/-- The three prescribed scalar jets, with every higher unused slot zero. -/
noncomputable def jet (t : ℝ) (k j : ℕ) : ℝ :=
  if j = 0 then value t k else if j = 1 then first t k else if j = 2 then second t k else 0

/-- Consecutive prescribed objective levels have the exact cubic-scale decrement. -/
theorem value_succ (t : ℝ) (k : ℕ) : value t (k + 1) = value t k - t ^ 3 / 2 := by
  simp only [value, Nat.cast_add, Nat.cast_one]
  ring

/-- The quadratic initial polynomial is the genuine prescribed Taylor polynomial. -/
theorem initialPolynomial_jet (t : ℝ) (k : ℕ) :
    Hermite.initialPolynomial 2 (jet t k) =
      C (value t k) + C (first t k) * X + C (second t k / 2) * X ^ 2 := by
  change ∑ i ∈ Finset.range 3, C (jet t k i / i.factorial) * (X - C 0) ^ i = _
  norm_num [Finset.sum_range_succ, jet]

/-- Uniformly scaled positive steps bound the zeroth quadratic-Hermite residual. -/
theorem residual_zero_bound {t v s C : ℝ} (ht : 0 < t) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hstep : s ≤ C * t) :
    |-t ^ 3 / 2 + 2 * t ^ 2 * v * s - 2 * t * v ^ 2 * s ^ 2| ≤
      (1 / 2 + 2 * C + 2 * C ^ 2) * t ^ 3 := by
  have hv2 : v ^ 2 ≤ 1 := pow_le_one₀ hv hv1
  have hA := mul_le_mul_of_nonneg_right hv1 (show 0 ≤ 2 * t ^ 2 * s by positivity)
  have hB := mul_le_mul_of_nonneg_right hv2 (show 0 ≤ 2 * t * s ^ 2 by positivity)
  have hU := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 2 * t ^ 2 by positivity)
  have hs2 : s ^ 2 ≤ (C * t) ^ 2 := (sq_le_sq₀ hs (by positivity)).mpr hstep
  have hU2 := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ 2 * t by positivity)
  have hA0 : 0 ≤ 2 * t ^ 2 * v * s := by positivity
  have hB0 : 0 ≤ 2 * t * v ^ 2 * s ^ 2 := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The first quadratic-Hermite residual has the uniform squared-step scale. -/
theorem residual_one_bound {t v s C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hs : 0 ≤ s) (hstep : s ≤ C * t) :
    |t ^ 5 - 4 * t * v ^ 2 * s| ≤ (1 + 4 * C) * t ^ 2 := by
  have hv2 : v ^ 2 ≤ 1 := pow_le_one₀ hv hv1
  have hA := mul_le_mul_of_nonneg_right hv2 (show 0 ≤ 4 * t * s by positivity)
  have hU := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 4 * t by positivity)
  have hP := mul_le_mul_of_nonneg_left
    (pow_le_one₀ (n := 3) ht.le ht1) (sq_nonneg t)
  have hA0 : 0 ≤ 4 * t * v ^ 2 * s := by positivity
  have ht5 : 0 ≤ t ^ 5 := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The second quadratic-Hermite residual has the uniform linear-step scale. -/
theorem residual_two_bound {t v w : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hnext : w = v - t ^ 3 / 2) : |4 * t * (w ^ 2 - v ^ 2)| ≤ 4 * t := by
  have he : 4 * t * (w ^ 2 - v ^ 2) = -(2 * t ^ 4 * (w + v)) := by rw [hnext];ring
  rw [he, abs_neg, abs_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left (show w + v ≤ 2 by linarith)
    (show 0 ≤ 2 * t ^ 4 by positivity)
  have hp := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := 3) ht.le ht1) ht.le
  nlinarith

/-- A fixed lower spacing scale converts a uniform accuracy-scale residual to
the genuine local Hermite displacement scale. -/
theorem residual_le_scaled_step {c t s A K R : ℝ} {m : ℕ}
    (hc : 0 < c) (ht : 0 ≤ t) (hK : 0 ≤ K) (hstep : c * t ≤ s)
    (hA : A / c ^ m ≤ K) (hres : R ≤ A * t ^ m) : R ≤ K * s ^ m := by
  have ha := (div_le_iff₀ (pow_pos hc m)).mp hA
  have hm := mul_le_mul_of_nonneg_right ha (pow_nonneg ht m)
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg hc.le ht) hstep m) hK
  exact hres.trans ((hm.trans_eq (by ring)).trans hp)

/-- The exact three residuals of the prescribed genuine quadratic Taylor data. -/
theorem residual_formulas (t : ℝ) (k : ℕ) (s : ℝ) :
    jet t (k + 1) 0 - (Hermite.initialPolynomial 2 (jet t k)).eval s =
      -t ^ 3 / 2 + 2 * t ^ 2 * value t k * s - 2 * t * (value t k) ^ 2 * s ^ 2 ∧
    jet t (k + 1) 1 - (derivative (Hermite.initialPolynomial 2 (jet t k))).eval s =
      t ^ 5 - 4 * t * (value t k) ^ 2 * s ∧
    jet t (k + 1) 2 - (derivative (derivative (Hermite.initialPolynomial 2 (jet t k)))).eval s =
      4 * t * ((value t (k + 1)) ^ 2 - (value t k) ^ 2) := by
  rw [initialPolynomial_jet]
  norm_num [jet, first, second, value_succ, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow]
  constructor
  · ring
  constructor <;> ring

/-- The prescribed jets have a common bound independent of accuracy or method. -/
theorem jet_bound {t : ℝ} (ht : 0 < t) (ht1 : t < 1) {k : ℕ}
    (hk : k ≤ horizon t) {j : ℕ} (hj : j ≤ 2) : |jet t k j| ≤ 4 := by
  obtain ⟨hv, hv1⟩ := value_bounds ht ht1 hk
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1.le
  have hv2 : (value t k) ^ 2 ≤ 1 := pow_le_one₀ hv.le hv1
  have hg : 0 ≤ 2 * t ^ 2 * value t k := by positivity
  have hH : 0 ≤ 4 * t * (value t k) ^ 2 := by positivity
  interval_cases j
  · simp only [jet, ite_true, abs_of_pos hv];linarith
  · norm_num only [jet, show ¬(1 : ℕ)=0 by decide, ite_false, ite_true]
    rw [first, show - 2 * t ^ 2 * value t k = -(2 * t ^ 2 * value t k) by ring,
      abs_neg, abs_of_nonneg hg]
    nlinarith [mul_le_mul_of_nonneg_left hv1 (sq_nonneg t)]
  · norm_num only [jet, show ¬(2 : ℕ)=0 by decide, show ¬(2 : ℕ)=1 by decide,
      ite_false, ite_true]
    rw [second, abs_of_nonneg hH]
    nlinarith [mul_le_mul_of_nonneg_left hv2 ht.le]

/-- Positive uniform spacing and bounded step factors give the exact normalized
Hermite hypotheses with a single accuracy-independent constant. -/
theorem history_interpolation_data {M : ScalarMethod} {t κrg κrs κlambda K : ℝ}
    (ht : 0 < t) (ht1 : t < 1)
    (hM : IsScalarMethodClass M (t ^ 2) κrg κrs κlambda)
    (hK : 0 ≤ K) (hK4 : 4 ≤ K) (hKC : 1 + κrg ≤ K)
    (hK0 : (1 / 2 + 2 * (1 + κrg) + 2 * (1 + κrg) ^ 2) / ((1 - κrg) / (2 * κlambda)) ^ 3 ≤ K)
    (hK1 : (1 + 4 * (1 + κrg)) / ((1 - κrg) / (2 * κlambda)) ^ 2 ≤ K)
    (hK2 : 4 / ((1 - κrg) / (2 * κlambda)) ≤ K) :
    (∀ i j, i < j → j ≤ horizon t →
      (history M t i).point < (history M t j).point) ∧
    (∀ k < horizon t, ∀ j ≤ 2,
      |jet t (k + 1) j - (derivative^[j] (Hermite.initialPolynomial 2 (jet t k))).eval
        ((history M t (k + 1)).point - (history M t k).point)| ≤
      K * ((history M t (k + 1)).point - (history M t k).point) ^ (2 - j + 1)) ∧
    (∀ k < horizon t, ∀ j ≤ 2, |jet t k j| ≤ K) ∧
    (∀ k < horizon t, (history M t (k + 1)).point - (history M t k).point ≤ K) := by
  have hs := history_step_bounds ht hM
  have hc : 0 < (1 - κrg) / (2 * κlambda) := by
    have := hM.residual_fraction_lt_one
    have := hM.spectral_gt_one
    positivity
  have hC : 0 ≤ 1 + κrg := by have := hM.residual_fraction_nonneg;linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmono := strictMonoOn_Iic_of_lt_succ (n := horizon t)
      (ψ := fun i => (history M t i).point) (fun k hk => sub_pos.mp (hs k hk).1)
    intro i j hij hj
    exact hmono (show i ∈ Set.Iic (horizon t) from (le_of_lt hij).trans hj) hj hij
  · intro k hk j hj
    obtain ⟨hv, hv1⟩ := value_bounds ht ht1 hk.le
    obtain ⟨hw, hw1⟩ := value_bounds ht ht1 (Nat.succ_le_of_lt hk)
    obtain ⟨hspos, hslow, hsup⟩ := hs k hk
    have hform := residual_formulas t k
      ((history M t (k + 1)).point - (history M t k).point)
    interval_cases j
    · simp only [Function.iterate_zero, id_eq, Nat.sub_zero]
      rw [hform.1]
      exact residual_le_scaled_step hc ht.le hK hslow hK0
        (residual_zero_bound ht hv.le hv1 hspos.le hC hsup)
    · change |jet t (k + 1) 1 - (derivative (Hermite.initialPolynomial 2 (jet t k))).eval _| ≤ _
      rw [hform.2.1]
      exact residual_le_scaled_step hc ht.le hK hslow hK1
        (residual_one_bound ht ht1.le hv.le hv1 hspos.le hsup)
    · change |jet t (k + 1) 2-
          (derivative (derivative (Hermite.initialPolynomial 2 (jet t k)))).eval _| ≤ _
      rw [hform.2.2]
      exact residual_le_scaled_step hc ht.le hK hslow (by simpa using hK2)
        (by simpa using residual_two_bound ht ht1.le hv.le hv1 hw.le hw1 (value_succ t k))
  · intro k hk j hj
    exact (jet_bound ht ht1 hk.le hj).trans hK4
  · intro k hk
    exact (hs k hk).2.2.trans
      ((mul_le_mul_of_nonneg_left ht1.le hC).trans (by simpa using hKC))

end ShiftedNewton.Sharpness
