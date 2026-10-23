import Numlib.Algebra.Order.Field.Basic
import Numlib.Optimization.LeastSquares.Run
import Numlib.Optimization.LeastSquares.SmallCurvature

/-!
# Uniform successful dyadic-root residual budgets

Four actual endpoint obstructions yield the source common positive decrease
coefficient. The exact fractional-power accuracy factor, initial numerator
and reciprocal maximum are explicit and independent of any claimed count.
-/

namespace LeastSquares
open HighOrderRegularization EvaluationComplexity

/-- The minimum of the four positive accuracy powers in the residual complexity bound. -/
noncomputable def rootAccuracyFactor (p i : ℕ) (ε₀ ε₁ ε₂ ε₃ : ℝ) : ℝ :=
  min (ε₀ ^ (1 / (2 : ℝ) ^ i))
    (min (ε₁ ^ (((p + 1 : ℕ) : ℝ) / p))
      (min (ε₂ ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
        (ε₃ ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)))))

/-- The common initial-residual denominator for all three derivative decrease branches. -/
noncomputable def rootDenominator (p : ℕ) (ℓ : ℝ) (i : ℕ) (R : ℝ) : ℝ :=
  max 1 (max (R ^ cascadingExponent p ℓ i 1)
    (max (R ^ cascadingExponent p ℓ i 2) (R ^ cascadingExponent p ℓ i 3)))

/-- The exact minimum of the four successful dyadic-root decrease coefficients. -/
noncomputable def rootDecreaseCoefficient (p : ℕ) (ℓ : ℝ) (i : ℕ)
    (σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ) : ℝ :=
  let σmax := max σ₀ (γ₃ * L / (1 - η₂))
  min (1 - β ^ (1 / (2 : ℝ) ^ i))
    (min (cascadingConstant (decreaseConstant p p η₁ σmin L σmax θ₁) β ℓ p i 1)
      (min (cascadingConstant (decreaseConstant p (p - 1) η₁ σmin L σmax θ₂) β ℓ p i 2)
        (cascadingConstant (decreaseConstant p (p - 2) η₁ σmin L σmax θ₃) β ℓ p i 3)))

/-- Positive accuracies give a strictly positive minimum accuracy factor. -/
theorem rootAccuracyFactor_pos (p i : ℕ) {ε₀ ε₁ ε₂ ε₃ : ℝ}
    (h₀ : 0 < ε₀) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    0 < rootAccuracyFactor p i ε₀ ε₁ ε₂ ε₃ := by
  unfold rootAccuracyFactor
  positivity

/-- A measure obstruction consumes the common positive weighted decrease budget. -/
theorem budget_le_of_measure {c A D κ u ε α den drop : ℝ}
    (hA : 0 ≤ A) (hD : 0 < D) (hκ : 0 ≤ κ)
    (hcκ : c ≤ κ) (hAε : A ≤ ε ^ α) (hε : 0 ≤ ε) (hεu : ε ≤ u)
    (hα : 0 ≤ α) (hden : 0 < den) (hdenD : den ≤ D)
    (hdrop : κ * u ^ α / den ≤ drop) : c * A / D ≤ drop := by
  have hu : 0 ≤ u := hε.trans hεu
  have hnum : c * A ≤ κ * u ^ α :=
    mul_le_mul hcκ (hAε.trans (Real.rpow_le_rpow hε hεu hα)) hA hκ
  have hdrop0 : 0 ≤ drop :=
    (div_nonneg (mul_nonneg hκ (Real.rpow_nonneg hu _)) hden.le).trans hdrop
  apply (div_le_iff₀ hD).mpr
  exact hnum.trans (((div_le_iff₀ hden).mp hdrop).trans
    (mul_le_mul_of_nonneg_left hdenD hdrop0))

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
namespace FiniteRun
variable {r : E → F} {ℓ : ℝ} {p : ℕ} {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ}
  {M : ℕ → Set E} {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁
    ε₂ ε₃ : ℝ} {N : ℕ}

/-- Failure of the repaired actual stopping test gives one of the four true endpoint
  obstructions. -/
theorem endpoint_obstruction
    (h : FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N) {i : ℕ} (hi : i < N) :
    ε₁ < firstMeasure r ℓ (x i) ∨ secondMeasure r ℓ (x i) (μ i) < -ε₂ ∨
      ∃ v ∈ M i, ε₃ < thirdMeasure r ℓ (x i) v ∨
        ε₂ < directionalSecondMeasure r ℓ (x i) v := by
  have hn : ¬finiteStop r ℓ (x i) (μ i) (M i) ε₀ ε₁ ε₂ ε₃ := by
    exact (stop_false_coe_iff _ _ _ _ _ _ _ _ _).not.mp (h.not_terminated i hi)
  by_cases hg : firstMeasure r ℓ (x i) ≤ ε₁
  · by_cases hμ : -ε₂ ≤ secondMeasure r ℓ (x i) (μ i)
    · right; right
      have hh : ¬∀ v ∈ M i, thirdMeasure r ℓ (x i) v ≤ ε₃ ∧
          directionalSecondMeasure r ℓ (x i) v ≤ ε₂ := by
        intro hh
        exact hn (Or.inr ⟨hg, Or.inr ⟨hμ, hh⟩⟩)
      push Not at hh
      obtain ⟨v, hv, hfail⟩ := hh
      refine ⟨v, hv, ?_⟩
      by_cases hthird : thirdMeasure r ℓ (x i) v ≤ ε₃
      · exact Or.inr (hfail hthird)
      · exact Or.inl (lt_of_not_ge hthird)
    · exact Or.inr (Or.inl (lt_of_not_ge hμ))
  · exact Or.inl (lt_of_not_ge hg)
end FiniteRun
end LeastSquares

namespace LeastSquares.FiniteRun
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
variable {r : E → F} {ℓ L β : ℝ} {p : ℕ} {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ}
  {M : ℕ → Set E} {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁
    ε₂ ε₃ : ℝ} {N : ℕ}

/-- Every accepted step with a nonterminal endpoint consumes the exact common dyadic-root budget. -/
theorem successful_root_decrease
    (h : FiniteRun false r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    (hβ : 0 < β) (hβ1 : β < 1) (a : ℕ)
    (hι₁ : 0 ≤ cascadingExponent p ℓ a 1) (hι₂ : 0 ≤ cascadingExponent p ℓ a 2)
    (hι₃ : 0 ≤ cascadingExponent p ℓ a 3)
    {i : ℕ} (hi : i + 1 < N) (hs : η₁ ≤ ρ i) :
    rootDecreaseCoefficient p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β *
      rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃ / rootDenominator p ℓ a ‖r (x 0)‖ ≤
      ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) - ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a) := by
  let σmax := max (σ 0) (γ₃ * L / (1 - η₂))
  let K₁ := decreaseConstant p p η₁ σmin L σmax θ₁
  let K₂ := decreaseConstant p (p - 1) η₁ σmin L σmax θ₂
  let K₃ := decreaseConstant p (p - 2) η₁ σmin L σmax θ₃
  let c := rootDecreaseCoefficient p ℓ a (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β
  let A := rootAccuracyFactor p a ε₀ ε₁ ε₂ ε₃
  let D := rootDenominator p ℓ a ‖r (x 0)‖
  have hp3 : 3 ≤ p := h.third_order (by simp)
  have hp2 : 2 ≤ p := by omega
  have hℓ : 0 < ℓ := by linarith [h.residual_order]
  have hℓ1 : 1 ≤ ℓ := by linarith [h.residual_order]
  have hm : 0 ≤ σmax :=
    (h.trace.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hK₁ : 0 < K₁ := decreaseConstant_pos p p h.trace.updates.eta1_pos
    h.trace.updates.min_pos hL hm h.theta_first_pos.le
  have hK₂ : 0 < K₂ := decreaseConstant_pos p (p - 1) h.trace.updates.eta1_pos
    h.trace.updates.min_pos hL hm h.theta_second_pos.le
  have hK₃ : 0 < K₃ := decreaseConstant_pos p (p - 2) h.trace.updates.eta1_pos
    h.trace.updates.min_pos hL hm h.theta_third_pos.le
  have hA : 0 < A := rootAccuracyFactor_pos p a h.accuracy_global_pos h.accuracy_first_pos
    (h.accuracy_second_pos ε₂ rfl) (h.accuracy_third_pos ε₃ rfl)
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hc₀ : c ≤ 1 - β ^ (1 / (2 : ℝ) ^ a) := min_le_left _ _
  have hc₁ : c ≤ cascadingConstant K₁ β ℓ p a 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hc₂ : c ≤ cascadingConstant K₂ β ℓ p a 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc₃ : c ≤ cascadingConstant K₃ β ℓ p a 3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hD₁ : ‖r (x 0)‖ ^ cascadingExponent p ℓ a 1 ≤ D :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hD₂ : ‖r (x 0)‖ ^ cascadingExponent p ℓ a 2 ≤ D :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hD₃ : ‖r (x 0)‖ ^ cascadingExponent p ℓ a 3 ≤ D :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hiN : i < N := by omega
  have hx : 0 < ‖r (x i)‖ := h.accuracy_global_pos.trans (h.residual_gt_accuracy hiN)
  have hb := h.residual_step_le hiN
  have hq : 0 < (1 : ℝ) / 2 ^ a := by positivity
  have hAcc₀ : A ≤ ε₀ ^ (1 / (2 : ℝ) ^ a) := min_le_left _ _
  have hAcc₁ : A ≤ ε₁ ^ (((p + 1 : ℕ) : ℝ) / p) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hAcc₂ : A ≤ ε₂ ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hAcc₃ : A ≤ ε₃ ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  by_cases hrel : β * ‖r (x i)‖ < ‖r (x (i + 1))‖
  · have branch (j : ℕ) (hjp : j ≤ p) (K eps v : ℝ)
        (hcK : c ≤ cascadingConstant K β ℓ p a j) (hK : 0 ≤ K) (hv : 0 ≤ v)
        (heps : 0 ≤ eps) (hepsv : eps ≤ v)
        (hAcc : A ≤ eps ^ (((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)))
        (hι : 0 ≤ cascadingExponent p ℓ a j)
        (hDj : ‖r (x 0)‖ ^ cascadingExponent p ℓ a j ≤ D)
        (hd : K * ℓ * v ^ (((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)) *
          ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p + 1 - j : ℕ)) ≤
            ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ) : c * A / D ≤
          ‖r (x i)‖ ^ (1 / (2 : ℝ) ^ a) - ‖r (x (i + 1))‖ ^ (1 / (2 : ℝ) ^ a) := by
      have ht := cascading_decrease_of_power (i := a) hx (norm_nonneg _) hb hβ hrel.le
        hℓ1 hK hv hjp hd
      apply budget_le_of_measure hA.le hD (show 0 ≤ cascadingConstant K β ℓ p a j by
        unfold cascadingConstant; positivity) hcK hAcc heps hepsv (by positivity)
        (Real.rpow_pos_of_pos hx _) _ ht
      exact (Real.rpow_le_rpow (norm_nonneg _) (h.residual_le_initial (by omega)) hι).trans hDj
    rcases h.endpoint_obstruction hi with hg | hμ | ⟨v, hv, hthird | hsecond⟩
    · apply branch 1 h.trace.order_pos K₁ ε₁ (firstMeasure r ℓ (x (i + 1)))
        hc₁ hK₁.le (div_nonneg (norm_nonneg _) (derivativeWeight_nonneg _ _ _))
        h.accuracy_first_pos.le hg.le (by simpa only [Nat.add_sub_cancel] using hAcc₁)
          hι₁ hD₁
      simpa only [Nat.add_sub_cancel] using h.trace.decrease_first hℓ hf hL
        h.theta_first_pos.le hlip hiN hs (h.stationary_first i hiN)
    · apply branch 2 hp2 K₂ ε₂ (max 0 (-secondMeasure r ℓ (x (i + 1)) (μ (i + 1))))
        hc₂ hK₂.le (le_max_left _ _) (h.accuracy_second_pos ε₂ rfl).le
        (le_trans (by linarith : ε₂ ≤ -secondMeasure r ℓ (x (i + 1)) (μ (i + 1)))
          (le_max_right _ _)) (by simpa only [show p + 1 - 2 = p - 1 by omega] using hAcc₂)
        hι₂ hD₂
      simpa only [show p + 1 - 2 = p - 1 by omega] using h.trace.decrease_second hp2 hℓ hf hL
        h.theta_second_pos.le hlip hiN hs (h.stationary_second i hiN (by simp))
        (h.least_eigenpair (i + 1) (by omega) (by simp))
    · have hv' : v ∈ smallModelDirections (powerObjective r ℓ) p (x i) (s i) (σ i) θ₂ := by
        rwa [h.model_directions i hiN (by simp)] at hv
      apply branch 3 hp3 K₃ ε₃ (thirdMeasure r ℓ (x (i + 1)) v)
        hc₃ hK₃.le (div_nonneg (abs_nonneg _) (derivativeWeight_nonneg _ _ _))
        (h.accuracy_third_pos ε₃ rfl).le hthird.le
        (by simpa only [show p + 1 - 3 = p - 2 by omega] using hAcc₃) hι₃ hD₃
      simpa only [show p + 1 - 3 = p - 2 by omega] using h.trace.decrease_third hp3 hℓ hf hL
        h.theta_third_pos.le hlip hiN hs (h.stationary_third i hiN (by simp)) hv'
    · have hv' : v ∈ smallModelDirections (powerObjective r ℓ) p (x i) (s i) (σ i) θ₂ := by
        rwa [h.model_directions i hiN (by simp)] at hv
      apply branch 2 hp2 K₂ ε₂ (directionalSecondMeasure r ℓ (x (i + 1)) v)
        hc₂ hK₂.le (div_nonneg (abs_nonneg _) (derivativeWeight_nonneg _ _ _))
        (h.accuracy_second_pos ε₂ rfl).le hsecond.le
        (by simpa only [show p + 1 - 2 = p - 1 by omega] using hAcc₂) hι₂ hD₂
      simpa only [show p + 1 - 2 = p - 1 by omega] using
        h.trace.decrease_directional_second hp2 hℓ hf hL h.theta_second_pos.le hlip hiN hs hv'
  · have hh := Real.relative_cascading_decrease (norm_nonneg _) hb hβ.le hβ1
      (not_lt.mp hrel) hq
    have hκ₀ : 0 ≤ 1 - β ^ (1 / (2 : ℝ) ^ a) := hh.1.le
    apply budget_le_of_measure hA.le hD hκ₀ hc₀ hAcc₀ h.accuracy_global_pos.le
      (h.residual_gt_accuracy hi).le hq.le zero_lt_one (le_max_left _ _)
    simpa only [div_one] using hh.2.2.trans hh.2.1
end LeastSquares.FiniteRun

namespace LeastSquares
open HighOrderRegularization EvaluationComplexity

/-- The exact successful-count constant, the maximum reciprocal of the four source coefficients. -/
noncomputable def rootSuccessfulIterationConstant (p : ℕ) (ℓ : ℝ) (i : ℕ)
    (σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ) : ℝ :=
  let σmax := max σ₀ (γ₃ * L / (1 - η₂))
  max (1 / (1 - β ^ (1 / (2 : ℝ) ^ i)))
    (max (1 / cascadingConstant (decreaseConstant p p η₁ σmin L σmax θ₁) β ℓ p i 1)
      (max (1 / cascadingConstant (decreaseConstant p (p - 1) η₁ σmin L σmax θ₂)
        β ℓ p i 2)
        (1 / cascadingConstant (decreaseConstant p (p - 2) η₁ σmin L σmax θ₃) β
          ℓ p i 3)))

/-- The exact maximum initial-residual numerator in (5.1.44) and (5.1.45). -/
noncomputable def rootBudget (p : ℕ) (ℓ : ℝ) (i : ℕ) (R : ℝ) : ℝ :=
  max (R ^ (1 / (2 : ℝ) ^ i))
    (max (R ^ (1 - (ℓ - 1) / p))
      (max (R ^ (1 - 2 * (ℓ - 1) / (p - 1 : ℕ)))
        (R ^ (1 - 3 * (ℓ - 1) / (p - 2 : ℕ)))))

/-- The common residual denominator is strictly positive without any residual restrictions. -/
theorem rootDenominator_pos (p : ℕ) (ℓ : ℝ) (i : ℕ) (R : ℝ) :
    0 < rootDenominator p ℓ i R := zero_lt_one.trans_le (le_max_left _ _)

/-- Every source decrease coefficient is positive before accuracies or execution enter. -/
theorem rootDecreaseCoefficient_pos (p : ℕ) (ℓ : ℝ) (i : ℕ)
    {σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ}
    (hσ : 0 < σ₀) (hmin : 0 < σmin) (hη : 0 < η₁) (hL : 0 < L)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃) (hβ : 0 < β) (hβ1 : β < 1) :
    0 < rootDecreaseCoefficient p ℓ i σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β := by
  have hm : 0 ≤ max σ₀ (γ₃ * L / (1 - η₂)) := hσ.le.trans (le_max_left _ _)
  unfold rootDecreaseCoefficient
  refine lt_min (sub_pos.mpr (Real.rpow_lt_one hβ.le hβ1 (by positivity)))
    (lt_min ?_ (lt_min ?_ ?_))
  · exact cascadingConstant_pos (decreaseConstant_pos p p hη hmin hL hm hθ₁.le) hβ p i 1
  · exact cascadingConstant_pos (decreaseConstant_pos p (p - 1) hη hmin hL hm hθ₂.le) hβ p i 2
  · exact cascadingConstant_pos (decreaseConstant_pos p (p - 2) hη hmin hL hm hθ₃.le) hβ p i 3

/-- Adding the dyadic potential exponent cancels exactly the subtraction in the root transfer. -/
theorem dyadic_add_cascadingExponent (p : ℕ) (ℓ : ℝ) (i j : ℕ) :
    1 / (2 : ℝ) ^ i + cascadingExponent p ℓ i j =
      1 - j * (ℓ - 1) / (p + 1 - j : ℕ) := by
  unfold cascadingExponent
  field_simp
  ring

/-- Multiplying the dyadic potential by the common denominator gives the exact printed numerator. -/
theorem rootBudget_eq {R : ℝ} (hR : 0 < R) (p : ℕ) (ℓ : ℝ) (i : ℕ) :
    R ^ (1 / (2 : ℝ) ^ i) * rootDenominator p ℓ i R = rootBudget p ℓ i R := by
  unfold rootDenominator rootBudget
  rw [mul_max_of_nonneg _ _ (Real.rpow_nonneg hR.le _),
    mul_max_of_nonneg _ _ (Real.rpow_nonneg hR.le _),
    mul_max_of_nonneg _ _ (Real.rpow_nonneg hR.le _)]
  simp only [mul_one, ← Real.rpow_add hR, dyadic_add_cascadingExponent,
    Nat.cast_one, one_mul, Nat.add_sub_cancel,
    show p + 1 - 2 = p - 1 by omega, show p + 1 - 3 = p - 2 by omega,
    Nat.cast_ofNat]

/-- The exact numerator is nonnegative for every nonnegative initial residual. -/
theorem rootBudget_nonneg {R : ℝ} (hR : 0 ≤ R) (p : ℕ) (ℓ : ℝ) (i : ℕ) :
    0 ≤ rootBudget p ℓ i R := (Real.rpow_nonneg hR _).trans (le_max_left _ _)

/-- The printed successful-count constant is the reciprocal minimum decrease coefficient. -/
theorem inverse_rootDecreaseCoefficient (p : ℕ) (ℓ : ℝ) (i : ℕ)
    {σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β : ℝ}
    (hσ : 0 < σ₀) (hmin : 0 < σmin) (hη : 0 < η₁) (hL : 0 < L)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃) (hβ : 0 < β) (hβ1 : β < 1) :
    1 / rootDecreaseCoefficient p ℓ i σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ β =
      rootSuccessfulIterationConstant p ℓ i σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂
        θ₃ β := by
  have hm : 0 ≤ max σ₀ (γ₃ * L / (1 - η₂)) := hσ.le.trans (le_max_left _ _)
  have h₀ : 0 < 1 - β ^ (1 / (2 : ℝ) ^ i) :=
    sub_pos.mpr (Real.rpow_lt_one hβ.le hβ1 (by positivity))
  have h₁ := cascadingConstant_pos (ℓ := ℓ)
    (decreaseConstant_pos p p hη hmin hL hm hθ₁.le) hβ p i 1
  have h₂ := cascadingConstant_pos (ℓ := ℓ)
    (decreaseConstant_pos p (p - 1) hη hmin hL hm hθ₂.le) hβ p i 2
  have h₃ := cascadingConstant_pos (ℓ := ℓ)
    (decreaseConstant_pos p (p - 2) hη hmin hL hm hθ₃.le) hβ p i 3
  unfold rootDecreaseCoefficient rootSuccessfulIterationConstant
  rw [one_div_min_eq_max h₀ (lt_min h₁ (lt_min h₂ h₃)),
    one_div_min_eq_max h₁ (lt_min h₂ h₃), one_div_min_eq_max h₂ h₃]
end LeastSquares

namespace LeastSquares
/-- The inverse common accuracy factor is exactly the maximum of the four printed inverse powers. -/
theorem inv_rootAccuracyFactor_eq (p i : ℕ) {ε₀ ε₁ ε₂ ε₃ : ℝ}
    (h₀ : 0 < ε₀) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    1 / rootAccuracyFactor p i ε₀ ε₁ ε₂ ε₃ =
      max (ε₀ ^ (-(1 / (2 : ℝ) ^ i)))
        (max (ε₁ ^ (-((p + 1 : ℕ) : ℝ) / p))
          (max (ε₂ ^ (-((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
            (ε₃ ^ (-((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))))) := by
  have hpow₀ := Real.rpow_pos_of_pos h₀ (1 / (2 : ℝ) ^ i)
  have hpow₁ := Real.rpow_pos_of_pos h₁ (((p + 1 : ℕ) : ℝ) / p)
  have hpow₂ := Real.rpow_pos_of_pos h₂ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))
  have hpow₃ := Real.rpow_pos_of_pos h₃ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))
  rw [rootAccuracyFactor, one_div_min_eq_max hpow₀ (lt_min hpow₁ (lt_min hpow₂ hpow₃)),
    one_div_min_eq_max hpow₁ (lt_min hpow₂ hpow₃), one_div_min_eq_max hpow₂ hpow₃]
  simp_rw [one_div, ← Real.rpow_neg h₀.le, ← Real.rpow_neg h₁.le,
    ← Real.rpow_neg h₂.le, ← Real.rpow_neg h₃.le, neg_div]
end LeastSquares
