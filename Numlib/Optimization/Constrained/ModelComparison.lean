import Numlib.Optimization.Regularization.HighOrder.Parameter
import Numlib.Optimization.Constrained.FirstOrderModel
import Numlib.Optimization.Regularization.Inexact.CriticalityError

/-!
# All-order Taylor comparison on feasible displacement balls

Translation identifies the actual feasible directions for an objective at its
trial point and its model at the displacement. Tensor errors therefore control
constrained Taylor criticality in every order, without interiority or convexity.
-/

namespace TaylorModel
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A constrained criticality bound is exactly the bound on every actual
feasible Taylor displacement in the testing ball. -/
theorem constrainedCriticality_le_iff (f : E → ℝ) (j : ℕ) {X : Set E}
    (hX : IsClosed X) {x : E} (hx : x ∈ X) {δ b : ℝ} (hδ : 0 ≤ δ) :
    constrainedCriticality f j X x δ ≤ b ↔
      ∀ d : E, x + d ∈ X → ‖d‖ ≤ δ → decrement f j x d ≤ b := by
  refine ⟨fun hb d hd hn => (decrement_le_constrainedCriticality f j hX hd hn).trans hb, ?_⟩
  intro hh
  obtain ⟨d, hd, hn, he⟩ := exists_decrement_eq_constrainedCriticality f j hX hx hδ
  rw [←he]
  exact hh d hd hn

/-- Actual tensor-error bounds transfer constrained criticality to a trial
model on exactly the same feasible displacement ball, at every finite order. -/
theorem constrainedCriticality_le_model_add_error (f m : E → ℝ) (j : ℕ)
    {X : Set E} (hX : IsClosed X) {x s : E} (hxs : x + s ∈ X)
    {δ : ℝ} (hδ : 0 ≤ δ) (e : ℕ → ℝ)
    (he : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDeriv ℝ i f (x + s) - iteratedFDeriv ℝ i m s‖ ≤ e i) :
    constrainedCriticality f j X (x + s) δ ≤
      constrainedCriticality m j (feasibleDisplacements X x) s δ +
        ∑ i ∈ Finset.range j, e (i + 1) * δ ^ (i + 1) / (i + 1).factorial := by
  obtain ⟨d, hd, hn, heq⟩ := exists_decrement_eq_constrainedCriticality f j hX hxs hδ
  have hC : IsClosed (feasibleDisplacements X x) :=
    hX.preimage (continuous_const.add continuous_id)
  have hfeas : s + d ∈ feasibleDisplacements X x := by
    simpa only [mem_feasibleDisplacements, add_assoc] using hd
  have hm := decrement_le_constrainedCriticality m j hC hfeas hn
  have herr := norm_jetDecrement_sub_le_radius (ftaylorSeries ℝ f (x + s))
    (ftaylorSeries ℝ m s) j e he hn
  change |decrement f j (x + s) d - decrement m j s d| ≤ _ at herr
  rw [heq] at herr
  linarith [(abs_le.mp herr).2]

/-- The absolute constrained-criticality error is bounded by actual tensor
errors on the common translated feasible ball, with no regularity assumptions. -/
theorem abs_constrainedCriticality_sub_model_le (f m : E → ℝ) (j : ℕ)
    {X : Set E} (hX : IsClosed X) {x s : E} (hxs : x + s ∈ X)
    {δ : ℝ} (hδ : 0 ≤ δ) (e : ℕ → ℝ)
    (he : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDeriv ℝ i f (x + s) - iteratedFDeriv ℝ i m s‖ ≤ e i) :
    |constrainedCriticality f j X (x + s) δ -
      constrainedCriticality m j (feasibleDisplacements X x) s δ| ≤
        ∑ i ∈ Finset.range j, e (i + 1) * δ ^ (i + 1) / (i + 1).factorial := by
  have hu := constrainedCriticality_le_model_add_error f m j hX hxs hδ e he
  have hC : IsClosed (feasibleDisplacements X x) :=
    hX.preimage (continuous_const.add continuous_id)
  have hs : s ∈ feasibleDisplacements X x := hxs
  obtain ⟨d, hd, hn, heq⟩ := exists_decrement_eq_constrainedCriticality m j hC hs hδ
  have hfeas : (x + s) + d ∈ X := by
    simpa only [mem_feasibleDisplacements, add_assoc] using hd
  have hf := decrement_le_constrainedCriticality f j hX hfeas hn
  have herr := norm_jetDecrement_sub_le_radius (ftaylorSeries ℝ f (x + s))
    (ftaylorSeries ℝ m s) j e he hn
  change |decrement f j (x + s) d - decrement m j s d| ≤ _ at herr
  rw [heq] at herr
  exact abs_le.mpr ⟨by linarith [(abs_le.mp herr).1], by linarith⟩

end TaylorModel

namespace TaylorModel
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The genuine regularized Taylor model controls constrained criticality by
the sharp derivative-error powers on every feasible trial ball and every order. -/
theorem constrainedCriticality_le_regularized_model_add_error (f : E → ℝ)
    {p j : ℕ} (hf : ContDiff ℝ p f) (hjp : j ≤ p) {L σ δ : ℝ}
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {X : Set E} (hX : IsClosed X) {x s : E} (hxs : x + s ∈ X) :
    constrainedCriticality f j X (x + s) δ ≤
      constrainedCriticality (HighOrderRegularization.model f p x σ) j
        (feasibleDisplacements X x) s δ +
        (L + σ) * ∑ i ∈ Finset.range j,
          δ ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
  have he := constrainedCriticality_le_model_add_error f
    (HighOrderRegularization.model f p x σ) j hX hxs hδ
    (fun i => (L + σ) * ‖s‖ ^ (p - i + 1)) (fun i hi hij => by
      have hb := InexactRegularization.norm_derivative_sub_model_le_power f hf hi
        (hij.trans hjp) hL (K := 0) le_rfl hσ hlip (ftaylorSeries ℝ f x) x s
        (fun a _ _ => by change ‖iteratedFDeriv ℝ a f x - _‖ ≤ _; simp)
      simp only [mul_zero, add_zero] at hb
      convert! hb using 1)
  convert he using 1
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end TaylorModel
