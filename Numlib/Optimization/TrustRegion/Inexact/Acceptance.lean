import Numlib.Optimization.TrustRegion.Inexact.Selection
import Numlib.Analysis.Calculus.TaylorModel.Holder

/-!
# Acceptance of inexact Taylor trials at small radii

Actual derivative errors and the Lipschitz Taylor remainder control the true
objective ratio. The computed polynomial and its comparison step are retained
throughout; no acceptance condition is part of the trial specification.
-/

namespace InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform remainder coefficient for implicit derivative accuracy. -/
noncomputable def acceptanceCoefficient (q : ℕ) (L K : ℝ) : ℝ :=
  L + 4 * ((q + 1).factorial : ℝ) * K

/-- Actual tensor errors and Lipschitz derivatives control the computed model value. -/
theorem model_value_error_le {f : E → ℝ} {q j : ℕ} (hj : 0 < j) (hjq : j ≤ q)
    (hf : ContDiff ℝ q f) {L K : ℝ} (hL : 1 ≤ L) (hK : 0 ≤ K)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (A : FormalMultilinearSeries ℝ E ℝ) (x s : E) (hs : ‖s‖ ≤ 1)
    (hzero : A 0 (fun _ => 0) = f x)
    (herr : ∀ a, 1 ≤ a → a ≤ j →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ K * ‖s‖ ^ (q - a + 1)) :
    |f (x + s) - TaylorModel.ofJet A j s| ≤
      acceptanceCoefficient q L K * ‖s‖ ^ (j + 1) / j.factorial := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have ht := TaylorModel.abs_sub_eval_le_lipschitz isOpen_univ (fun _ h => h)
    (convex_univ : Convex ℝ (Set.univ : Set E))
    (hf.of_le (by exact_mod_cast hjq)).contDiffOn (by linarith : 0 ≤ L)
    (fun u _ v _ => hlip (p + 1) (by omega) hjq u v)
    (Set.mem_univ x) (Set.mem_univ (x + s))
  have he := TaylorModel.norm_ofJet_sub_eval_le_power A f x s hjq hK hzero herr
  have hp : ‖s‖ ^ (q + 1) ≤ ‖s‖ ^ (p + 1 + 1) :=
    pow_le_pow_of_le_one (norm_nonneg s) hs (by omega)
  have hfac : (0 : ℝ) < (p + 1).factorial := by positivity
  have hfac' : ((p + 1).factorial : ℝ) ≤ ((q + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : p + 1 ≤ q + 1)
  have hcoef : L / ((p + 2).factorial : ℝ) + 2 * K ≤
      acceptanceCoefficient q L K / (p + 1).factorial := by
    rw [acceptanceCoefficient, add_div]
    apply add_le_add
    · exact div_le_div_of_nonneg_left (by linarith)
        hfac (by exact_mod_cast Nat.factorial_le (by omega : p + 1 ≤ p + 2))
    · apply (le_div_iff₀ hfac).mpr
      nlinarith
  have htri : |f (x + s) - TaylorModel.ofJet A (p + 1) s| ≤
      |f (x + s) - TaylorModel.eval f (p + 1) x s| +
        ‖TaylorModel.ofJet A (p + 1) s - TaylorModel.eval f (p + 1) x s‖ := by
    simpa only [Real.norm_eq_abs, abs_sub_comm] using
      norm_sub_le_norm_sub_add_norm_sub (f (x + s)) (TaylorModel.eval f (p + 1) x s)
        (TaylorModel.ofJet A (p + 1) s)
  calc _ ≤ L * ‖s‖ ^ (p + 2) / (p + 2).factorial +
        2 * K * ‖s‖ ^ (q + 1) := htri.trans (add_le_add ht he)
    _ ≤ L * ‖s‖ ^ (p + 2) / (p + 2).factorial +
        2 * K * ‖s‖ ^ (p + 1 + 1) := by gcongr
    _ = (L / ((p + 2).factorial : ℝ) + 2 * K) * ‖s‖ ^ (p + 1 + 1) := by ring
    _ ≤ (acceptanceCoefficient q L K / (p + 1).factorial) *
        ‖s‖ ^ (p + 1 + 1) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by simpa only [Nat.succ_eq_add_one] using
        (show acceptanceCoefficient q L K / (p + 1).factorial * ‖s‖ ^ (p + 1 + 1) =
          acceptanceCoefficient q L K * ‖s‖ ^ (p + 1 + 1) / (p + 1).factorial by ring)

namespace SelectedTrials
variable {q : ℕ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {j : ℕ → Fin q} {Δ : ℕ → ℝ} {d s : ℕ → E} {ε : Fin q → ℝ} {ζ θ : ℝ}

/-- A small radius makes the true objective ratio very successful, despite the
inexact derivative tensors used by the selected computed polynomial. -/
theorem very_successful (h : SelectedTrials A T j Δ d s ε ζ θ)
    {f : E → ℝ} (hf : ContDiff ℝ q f) {L K η₂ : ℝ}
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hη : η₂ < 1)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (x : ℕ → E) {i : ℕ} (hi : i ∈ T)
    (hzero : A i 0 (fun _ => 0) = f (x i))
    (herr : ∀ a, 1 ≤ a → a ≤ modelOrder (j i) →
      ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ K * ‖s i‖ ^ (q - a + 1))
    (hsmall : Δ i ≤ min θ ((1 - η₂) / acceptanceCoefficient q L K *
      scaledGap A j Δ d θ i)) :
    η₂ ≤ (f (x i) - f (x i + s i)) / decrement (A i) (modelOrder (j i)) (s i) := by
  have hjq : modelOrder (j i) ≤ q := by
    dsimp [modelOrder]
    exact (j i).isLt
  have hj : 0 < modelOrder (j i) := by simp [modelOrder]
  have hcap : Δ i ≤ θ := hsmall.trans (min_le_left _ _)
  have hδ : optimalityRadius θ (Δ i) = Δ i := min_eq_right hcap
  have hsnorm : ‖s i‖ ≤ 1 := (h.step_feasible i hi).trans (hcap.trans h.cap_le_one)
  have hcoef : 0 < acceptanceCoefficient q L K := by
    dsimp [acceptanceCoefficient]
    positivity
  have hgap : 0 < scaledGap A j Δ d θ i :=
    (mul_pos (div_pos h.zeta_pos (by norm_num))
      (minimumAccuracy_pos h.order_pos h.accuracy_pos)).trans_le (h.scaledGap_lower hi)
  have hmodel := h.model_decrease hi
  rw [hδ] at hmodel
  have hfac : (0 : ℝ) < (modelOrder (j i)).factorial := by positivity
  have hdenom : 0 < decrement (A i) (modelOrder (j i)) (s i) :=
    (div_pos (mul_pos hgap (pow_pos (h.radius_pos i hi) _)) hfac).trans_le hmodel
  have hsmall' : acceptanceCoefficient q L K * Δ i ≤
      (1 - η₂) * scaledGap A j Δ d θ i := by
    have hh := hsmall.trans (min_le_right _ _)
    have hh' : Δ i ≤ ((1 - η₂) * scaledGap A j Δ d θ i) /
        acceptanceCoefficient q L K := by convert hh using 1; ring
    simpa only [mul_comm] using (le_div_iff₀ hcoef).mp hh'
  have he := model_value_error_le hj hjq hf hL hK hlip (A i) (x i) (s i)
    hsnorm hzero herr
  have he' : |f (x i + s i) - TaylorModel.ofJet (A i) (modelOrder (j i)) (s i)| ≤
      (1 - η₂) * decrement (A i) (modelOrder (j i)) (s i) := by
    calc _ ≤ acceptanceCoefficient q L K * ‖s i‖ ^ (modelOrder (j i) + 1) /
          (modelOrder (j i)).factorial := he
      _ ≤ acceptanceCoefficient q L K * Δ i ^ (modelOrder (j i) + 1) /
          (modelOrder (j i)).factorial := by gcongr; exact h.step_feasible i hi
      _ = (acceptanceCoefficient q L K * Δ i) * Δ i ^ modelOrder (j i) /
          (modelOrder (j i)).factorial := by rw [pow_succ]; ring
      _ ≤ ((1 - η₂) * scaledGap A j Δ d θ i) * Δ i ^ modelOrder (j i) /
          (modelOrder (j i)).factorial := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsmall' (pow_nonneg (h.radius_pos i hi).le _))
              hfac.le
      _ = (1 - η₂) * (scaledGap A j Δ d θ i * Δ i ^ modelOrder (j i) /
          (modelOrder (j i)).factorial) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmodel (sub_nonneg.mpr hη.le)
  apply (le_div_iff₀ hdenom).mpr
  have hupper := (le_abs_self (f (x i + s i) -
    TaylorModel.ofJet (A i) (modelOrder (j i)) (s i))).trans he'
  rw [decrement_eq, TaylorModel.ofJet_zero, hzero] at hupper ⊢
  linarith

end SelectedTrials
end InexactTrustRegion
