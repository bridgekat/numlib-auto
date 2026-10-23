import Numlib.Optimization.Regularization.HighOrder.Parameter

/-!
# Actual regularization parameter bounds on convex domains

The sharp Taylor remainder only needs smoothness on an open neighborhood of the
feasible convex domain. Actual feasible iterates and trial endpoints suffice
for the ratio and parameter cap; no global smoothness extension is imposed.
-/

namespace HighOrderRegularization
open Set TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sharp actual degree-p Taylor value remainder on a convex source domain. -/
theorem value_error_le_on {f : E → ℝ} {p : ℕ} (hp : 0 < p) {C S : Set E}
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - eval f p x s| ≤ L * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact abs_sub_eval_le_lipschitz hS hCS hC hf hL hlip hx hxs

/-- The actual ratio error bound requires source regularity only on the
convex domain containing the actual iterate and feasible trial endpoint. -/
theorem ratio_error_le_on {f : E → ℝ} {p : ℕ} (hp : 0 < p) {C S : Set E}
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 < σ)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C)
    (hs : model f p x σ s < model f p x σ 0) :
    |ratio f p x s - 1| ≤ L / σ := by
  have hd := decrement_pos hσ.le hs
  have hdec := (penalty_lt_decrement f p x s σ hs).le
  have herr := value_error_le_on hp hS hCS hC hf hL hlip hx hxs
  rw [ratio_error_eq hd]
  apply (div_le_iff₀ hd).2
  have hm := mul_le_mul_of_nonneg_left hdec (div_nonneg hL hσ.le)
  have heq : (L / σ) * (σ / (p + 1).factorial * ‖s‖ ^ (p + 1)) =
      L * ‖s‖ ^ (p + 1) / (p + 1).factorial := by field_simp
  rw [heq] at hm
  exact herr.trans hm

/-- Source-domain regularity gives the same very-successful threshold at each
actual feasible trial, including a last trial in a finite execution prefix. -/
theorem ModelTrace.very_successful_on {f : E → ℝ} {p : ℕ}
    {x s : ℕ → E} {σ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N : ℕ}
    (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N) {C S : Set E}
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hx : x i ∈ C) (hxs : x i + s i ∈ C)
    (hlarge : L / (1 - η₂) ≤ σ i) : η₂ ≤ ρ i := by
  have herr := ratio_error_le_on h.order_pos hS hCS hC hf hL
    (h.updates.pos (show i ≤ N by omega)) hlip hx hxs (h.improvement i hi)
  rw [←h.ratio i hi] at herr
  have hσ := h.updates.pos (show i ≤ N by omega)
  have hη : 0 < 1 - η₂ := sub_pos.mpr h.updates.eta2_lt_one
  have hm := (div_le_iff₀ hη).mp hlarge
  have hc : L / σ i ≤ 1 - η₂ := (div_le_iff₀ hσ).2 (by nlinarith)
  linarith [(abs_le.mp herr).1]

/-- Every actual feasible trace parameter obeys the source cap using only
Cp on an open neighborhood and highest-derivative Lipschitzness on the convex domain. -/
theorem ModelTrace.parameter_le_on {f : E → ℝ} {p : ℕ}
    {x s : ℕ → E} {σ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N : ℕ}
    (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N) {C S : Set E}
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hx : ∀ i < N, x i ∈ C) (hxs : ∀ i < N, x i + s i ∈ C)
    {i : ℕ} (hi : i ≤ N) : σ i ≤ max (σ 0) (γ₃ * L / (1 - η₂)) := by
  simpa only [mul_div_assoc] using h.updates.le_max_initial_threshold
    (fun k hk hlarge => h.very_successful_on hS hCS hC hf hL hlip hk
      (hx k hk) (hxs k hk) hlarge) hi

end HighOrderRegularization
