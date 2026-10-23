import Numlib.Optimization.Regularization.GlobalStep
import Numlib.Optimization.Regularization.HighOrder.Origin
import Numlib.Optimization.Regularization.ModelCriticality
import Numlib.Optimization.TrustRegion.Inexact.Selection

/-!
# Zero-decrease termination of a high-order regularized model solve

A genuine approximate-global model step returning zero model decrease makes
zero a true global model minimizer. Its low-order criticality vanishes, while
its higher-order criticality is small on positive radii by the actual model
smoothness and Peano bound. The derived origin identities transfer these facts
to the objective, without any radius or stationarity certificate as input.
-/

namespace HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open InexactTrustRegion

/-- If Step1 has an actual failing computed Taylor test, a zero-decrease
approximate-global Step2 return can occur only for order at least three. It
certifies genuine all-order approximate optimality at positive radii. -/
theorem zero_step_termination {f : E → ℝ} {p q : ℕ} {x s : E}
    (hqp : q ≤ p) (hf : ContDiffAt ℝ p f x) {σ μ : ℝ} (hμ : 0 < μ)
    (hsolve : ModelDecrease.ApproximateGlobalStep (model f p x σ) μ s)
    (hzero : model f p x σ 0 = model f p x σ s)
    (ε δ₀ : Fin q → ℝ) (hε : ∀ a, 0 < ε a) (hδ₀ : ∀ a, 0 < δ₀ a)
    (direction : Fin q → E) (hfeasible : ∀ a, ‖direction a‖ ≤ δ₀ a)
    {ζ : ℝ} (hζ : 0 < ζ)
    (hfailed : ∃ a, ζ * ε a * δ₀ a ^ modelOrder a / (modelOrder a).factorial <
      TaylorModel.decrement f (modelOrder a) x (direction a)) :
    3 ≤ q ∧ ∃ δ : Fin q → ℝ, (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      ∀ a, TaylorModel.criticality f (modelOrder a) x (δ a) ≤
        ε a * δ a ^ modelOrder a / (modelOrder a).factorial := by
  have hmin : IsLocalMin (model f p x σ) 0 :=
    Filter.Eventually.of_forall (hsolve.isGlobalMin_zero hμ hzero)
  have haj (a : Fin q) : modelOrder a ≤ p := (Nat.succ_le_iff.mpr a.isLt).trans hqp
  have hmodel (a : Fin q) : ContDiff ℝ (modelOrder a) (model f p x σ) :=
    ModelDecrease.contDiff_penalized_ofJet (ftaylorSeries ℝ f x) p
      (modelOrder a) (haj a) σ
  have hq3 : 3 ≤ q := by
    by_contra hq
    obtain ⟨a, ha⟩ := hfailed
    have horder : modelOrder a = 1 ∨ modelOrder a = 2 := by
      unfold modelOrder
      omega
    have hz : TaylorModel.criticality (model f p x σ) (modelOrder a) 0 (δ₀ a) = 0 := by
      rcases horder with h1 | h2
      · rw [h1]
        exact TaylorModel.criticality_one_eq_zero_of_isLocalMin hmin (hδ₀ a).le
      · have hm := hmodel a
        rw [h2] at hm ⊢
        exact TaylorModel.criticality_two_eq_zero_of_isLocalMin hm hmin (hδ₀ a).le
    rw [criticality_model_zero hf (haj a) σ (δ₀ a)] at hz
    have hd := TaylorModel.decrement_le_criticality f (modelOrder a) x (hfeasible a)
    rw [hz] at hd
    have hpos : 0 < ζ * ε a * δ₀ a ^ modelOrder a / (modelOrder a).factorial :=
      div_pos (mul_pos (mul_pos hζ (hε a)) (pow_pos (hδ₀ a) _)) (by positivity)
    linarith
  refine ⟨hq3, ?_⟩
  have hex : ∀ a : Fin q, ∃ δ : ℝ, (0 < δ ∧ δ ≤ 1) ∧
      TaylorModel.criticality f (modelOrder a) x δ ≤
        ε a * δ ^ modelOrder a / (modelOrder a).factorial := by
    intro a
    obtain ⟨r, hr, hbound⟩ := TaylorModel.exists_pos_criticality_le_mul_pow
      (show 0 < modelOrder a by unfold modelOrder; omega) (hmodel a) hmin
      (div_pos (hε a) (by positivity : (0 : ℝ) < (modelOrder a).factorial))
    refine ⟨min 1 (r / 2), ⟨lt_min (by norm_num) (half_pos hr), min_le_left _ _⟩, ?_⟩
    have hb := hbound (min 1 (r / 2))
      (le_min (by norm_num) (half_pos hr).le)
      ((min_le_right _ _).trans_lt (half_lt_self hr))
    rw [criticality_model_zero hf (haj a)] at hb
    convert hb using 1; ring
  choose δ hδ hb using hex
  exact ⟨δ, hδ, hb⟩

end HighOrderRegularization
