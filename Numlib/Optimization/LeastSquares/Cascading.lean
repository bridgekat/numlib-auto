import Numlib.Analysis.SpecialFunctions.Pow.Cascading
import Numlib.Optimization.LeastSquares.Decrease

/-!
# Cascading residual-power decreases

An actual accepted regularization trial strictly reduces the residual norm.
The weighted objective decrease then transfers to exact dyadic-root bounds
with the coefficients and residual exponents of Section 5.1.
-/

namespace LeastSquares
open HighOrderRegularization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F]

/-- A successful actual regularization trial strictly decreases the residual norm. -/
theorem RegularizationTrace.residual_lt
    {r : E → F} {ℓ η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ} {p N i : ℕ}
    {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    (h : RegularizationTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hℓ : 0 < ℓ) (hi : i < N) (hs : η₁ ≤ ρ i) :
    ‖r (x (i + 1))‖ < ‖r (x i)‖ := by
  have hd := h.successful_decrease hi hs
  have hc : 0 ≤ η₁ * σmin / ((p + 1).factorial : ℝ) * ‖s i‖ ^ (p + 1) :=
    mul_nonneg (div_nonneg (mul_nonneg h.updates.eta1_pos.le h.updates.min_pos.le)
      (by positivity)) (by positivity)
  have hdrop := lt_of_le_of_lt hc hd
  by_contra hn
  have hnorm : ‖r (x i)‖ ≤ ‖r (x (i + 1))‖ := le_of_not_gt hn
  have hm := div_le_div_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) hnorm hℓ.le) hℓ.le
  change powerObjective r ℓ (x i) ≤ powerObjective r ℓ (x (i + 1)) at hm
  linarith

/-- The residual exponent in (5.1.21), (5.1.23), and (5.1.25). -/
noncomputable def cascadingExponent (p : ℕ) (ℓ : ℝ) (i j : ℕ) : ℝ :=
  ((2 : ℝ) ^ i - 1) / (2 : ℝ) ^ i - j * (ℓ - 1) / (p + 1 - j : ℕ)

/-- The precise successful-decrease coefficient after taking a dyadic root. -/
noncomputable def cascadingConstant (κ β ℓ : ℝ) (p i j : ℕ) : ℝ :=
  κ * β ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)) / (2 : ℝ) ^ i

/-- These coefficients are strictly positive for positive beta and original coefficient. -/
theorem cascadingConstant_pos {κ β ℓ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (p i j : ℕ) :
    0 < cascadingConstant κ β ℓ p i j := by
  unfold cascadingConstant
  exact div_pos (mul_pos hκ (Real.rpow_pos_of_pos hβ _)) (by positivity)

/-- A full weighted residual-power decrease gives its exact dyadic-root bound. -/
theorem cascading_decrease_of_power {a b β ℓ κ u : ℝ} {p i j : ℕ}
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) (hβ : 0 < β)
    (hβa : β * a ≤ b) (hℓ : 1 ≤ ℓ) (hκ : 0 ≤ κ) (hu : 0 ≤ u)
    (hjp : j ≤ p)
    (hd : κ * ℓ * u ^ (((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)) *
      b ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)) ≤ a ^ ℓ - b ^ ℓ) :
    cascadingConstant κ β ℓ p i j * u ^ (((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)) /
      a ^ cascadingExponent p ℓ i j ≤ a ^ (1 / (2 : ℝ) ^ i) -
        b ^ (1 / (2 : ℝ) ^ i) := by
  have htwo : 0 < (2 : ℝ) ^ i := by positivity
  have htwo1 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have hq : 0 < (1 : ℝ) / 2 ^ i := one_div_pos.mpr htwo
  have hqℓ : (1 : ℝ) / 2 ^ i ≤ ℓ :=
    ((div_le_one htwo).mpr htwo1).trans hℓ
  have hm : 0 < (p + 1 - j : ℕ) := by omega
  have hmR : 0 < ((p + 1 - j : ℕ) : ℝ) := by exact_mod_cast hm
  have hcast : ((p + 1 - j : ℕ) : ℝ) = (p : ℝ) + 1 - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have he : 0 ≤ (ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ) := by positivity
  have ht := Real.cascading_decrease ha hb hba hβ.le hβa hq hqℓ hκ hu he hd
  have hexp : ℓ - 1 / (2 : ℝ) ^ i -
      (ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ) =
      cascadingExponent p ℓ i j := by
    unfold cascadingExponent
    rw [hcast]
    push_cast
    field_simp [show (p : ℝ) + 1 - j ≠ 0 by rw [← hcast]; exact hmR.ne']
    ring
  rw [hexp] at ht
  convert ht using 1
  unfold cascadingConstant
  ring
end LeastSquares
