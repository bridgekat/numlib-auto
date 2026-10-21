import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Heterogeneous tolerances for a coupled cubic

A dyadic squared curvature parameter separates the order-specific trust-region decrease
payment from the uniform worst-order payment. Every coefficient in the family is explicit;
the asymptotic statements quantify a single positive comparison constant before the index.
-/

noncomputable section
namespace Optimization.CoupledCubicTrustRegionRates

/-- The squared curvature scale after a finite sequence of dyadic contractions. -/
def scale (N : ℕ) : ℝ := (1 / 2) ^ (N + 1)

/-- The positive curvature magnitude associated with the dyadic scale. -/
def curvature (N : ℕ) : ℝ := Real.sqrt (scale N)

/-- First- and second-order tolerances for the coupled cubic trust-region family. -/
def tolerance (N j : ℕ) : ℝ :=
  if j = 1 then scale N / 2 else if j = 2 then curvature N / 2 else 1

/-- Every dyadic scale is strictly positive. -/
theorem scale_pos (N : ℕ) : 0 < scale N := by
  exact pow_pos (by norm_num) _

/-- The initial dyadic scale is one half. -/
@[simp] theorem scale_zero : scale 0 = 1 / 2 := by norm_num [scale]

/-- A further contraction halves the dyadic scale. -/
theorem scale_succ (N : ℕ) : scale (N + 1) = scale N / 2 := by
  simp only [scale, pow_succ]; ring

/-- Dyadic contraction makes the scale antitone. -/
theorem scale_antitone : Antitone scale := by
  apply antitone_nat_of_succ_le
  intro N
  rw [scale_succ]
  linarith [scale_pos N]

/-- Every scale is at most its initial value. -/
theorem scale_le_half (N : ℕ) : scale N ≤ 1 / 2 := by
  simpa using scale_antitone (Nat.zero_le N)

/-- At least one contraction makes the scale at most one quarter. -/
theorem scale_le_quarter {N : ℕ} (hN : 1 ≤ N) : scale N ≤ 1 / 4 := by
  have h := scale_antitone hN
  norm_num [scale] at h ⊢
  exact h

/-- Squaring the curvature recovers the scale exactly. -/
@[simp] theorem curvature_sq (N : ℕ) : curvature N ^ 2 = scale N :=
  Real.sq_sqrt (scale_pos N).le

/-- Curvatures in the dyadic family are strictly positive. -/
theorem curvature_pos (N : ℕ) : 0 < curvature N :=
  Real.sqrt_pos.2 (scale_pos N)

/-- At least one contraction makes the curvature at most one half. -/
theorem curvature_le_half {N : ℕ} (hN : 1 ≤ N) : curvature N ≤ 1 / 2 := by
  nlinarith [curvature_sq N, curvature_pos N, scale_le_quarter hN]

/-- The dyadic scale is no larger than its curvature. -/
theorem scale_le_curvature (N : ℕ) : scale N ≤ curvature N := by
  have hs := scale_le_half N
  have hc := curvature_pos N
  have he := curvature_sq N
  nlinarith [sq_nonneg (curvature N - 1)]

/-- The first tolerance is half the dyadic scale. -/
@[simp] theorem tolerance_one (N : ℕ) : tolerance N 1 = scale N / 2 := by
  simp [tolerance]

/-- The second tolerance is half the curvature magnitude. -/
@[simp] theorem tolerance_two (N : ℕ) : tolerance N 2 = curvature N / 2 := by
  simp [tolerance]

/-- Every tolerance is positive, including the unused orders. -/
theorem tolerance_pos (N j : ℕ) : 0 < tolerance N j := by
  have hs := scale_pos N
  have hc := curvature_pos N
  unfold tolerance
  split_ifs <;> positivity

/-- Both requested tolerances lie in the unit interval. -/
theorem tolerance_le_one {N j : ℕ} (hN : 1 ≤ N) : tolerance N j ≤ 1 := by
  unfold tolerance
  split_ifs
  · linarith [scale_le_half N]
  · linarith [curvature_le_half hN]
  · exact le_rfl

/-- Tolerances satisfy the source positivity and unit-cap conditions. -/
theorem tolerance_bounds {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    0 < tolerance N j ∧ tolerance N j ≤ 1 :=
  ⟨tolerance_pos N j, tolerance_le_one hN⟩

/-- The first-order tolerance is the smaller requested tolerance. -/
theorem tolerance_one_le_two (N : ℕ) : tolerance N 1 ≤ tolerance N 2 := by
  simpa only [tolerance_one, tolerance_two] using div_le_div_of_nonneg_right
    (scale_le_curvature N) (by norm_num : (0 : ℝ) ≤ 2)

/-- The literal order-specific payment is the square of the first tolerance. -/
theorem min_payment {N : ℕ} (hN : 1 ≤ N) :
    min (tolerance N 1 ^ 2) (tolerance N 2 ^ 3) = scale N ^ 2 / 4 := by
  rw [tolerance_one, tolerance_two]
  have hc := curvature_pos N
  have he := curvature_sq N
  have hh := curvature_le_half hN
  have hnonneg : 0 ≤ 1 - 2 * curvature N := by linarith
  have h : (scale N / 2) ^ 2 ≤ (curvature N / 2) ^ 3 := by
    rw [← he]
    nlinarith [mul_nonneg (sq_nonneg (curvature N))
      (show 0 ≤ curvature N * (1 - 2 * curvature N) by positivity)]
  rw [min_eq_left h]
  ring

/-- The proposed bad-step decrease divided by the literal payment is half the curvature. -/
theorem decrease_div_payment {N : ℕ} (hN : 1 ≤ N) :
    (curvature N * scale N ^ 2 / 8) /
      min (tolerance N 1 ^ 2) (tolerance N 2 ^ 3) = curvature N / 2 := by
  rw [min_payment hN]
  have hs := (scale_pos N).ne'
  field_simp
  ring

/-- A sufficiently late curvature is smaller than any fixed positive comparison constant. -/
theorem exists_curvature_lt {κ : ℝ} (hκ : 0 < κ) :
    ∃ N : ℕ, 1 ≤ N ∧ curvature N / 2 < κ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < (2 * κ) ^ 2 by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n + 1, by omega, ?_⟩
  have hscale : scale (n + 1) < (2 * κ) ^ 2 := by
    calc
      scale (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ < _ := hn
  nlinarith [curvature_sq (n + 1), curvature_pos (n + 1)]

/-- No positive tolerance-independent coefficient bounds all bad-step payments below. -/
theorem no_uniform_payment :
    ¬∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N →
      κ * min (tolerance N 1 ^ 2) (tolerance N 2 ^ 3) ≤
        curvature N * scale N ^ 2 / 8 := by
  rintro ⟨κ, hκ, h⟩
  obtain ⟨N, hN, hlt⟩ := exists_curvature_lt hκ
  have hpay : 0 < min (tolerance N 1 ^ 2) (tolerance N 2 ^ 3) := by
    rw [min_payment hN]
    exact div_pos (sq_pos_of_pos (scale_pos N)) (by norm_num)
  have hdiv := (le_div_iff₀ hpay).2 (h N hN)
  rw [decrease_div_payment hN] at hdiv
  exact (not_le_of_gt hlt) hdiv

/-- Distinct contraction indices give distinct scales. -/
theorem scale_injective : Function.Injective scale := by
  intro m n h
  have hpow := pow_right_injective₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≠ 1) h
  omega

/-- A tolerance vector determines its dyadic contraction index uniquely. -/
theorem tolerance_injective : Function.Injective tolerance := by
  intro m n h
  apply scale_injective
  have he := congrFun h 1
  simp only [tolerance_one] at he
  linarith

end Optimization.CoupledCubicTrustRegionRates
