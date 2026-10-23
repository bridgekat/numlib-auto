import Numlib.Optimization.Composite.ModelCriticality
import Numlib.Optimization.Regularization.HighOrder.Origin
import Numlib.Optimization.Regularization.GlobalStep

/-!
# Composite model identities and zero-decrease termination

Actual origin derivatives of the residual polynomial and smooth penalized part
recover the original objective jets. A positive-fraction global-gap solver
returning zero decrease derives global minimality of zero. Genuine generalized
criticality then transfers to the objective at positive radii.
-/

namespace Composite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
/-- Equal genuine generalized decrements give equal actual composite criticality. -/
theorem criticality_eq_of_decrement_eq (f₁ f₂ : E → ℝ) (c₁ c₂ : E → F) (h : F → ℝ)
    (j : ℕ) (x₁ x₂ : E) (δ : ℝ)
    (he : ∀ d, decrement f₁ c₁ h j x₁ d = decrement f₂ c₂ h j x₂ d) :
    criticality f₁ c₁ h j x₁ δ = criticality f₂ c₂ h j x₂ δ := by
  unfold criticality
  congr 2
  exact funext he

omit [FiniteDimensional ℝ E] in
/-- The genuine Taylor polynomial of the residual polynomial at zero recovers
its original truncation. -/
theorem eval_residualModel_zero {c : E → F} {p j : ℕ} {x : E}
    (hc : ContDiffAt ℝ p c x) (hjp : j ≤ p) (d : E) :
    TaylorModel.eval (residualModel c p x) j 0 d = TaylorModel.eval c j x d := by
  rw [TaylorModel.eval_eq_sum, TaylorModel.eval_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hap : a ≤ p := (Nat.le_of_lt_succ (Finset.mem_range.mp ha)).trans hjp
  have he := TaylorModel.iteratedFDeriv_eval hc hap (s := (0 : E))
  rw [TaylorModel.eval_zero] at he
  change _ • (iteratedFDeriv ℝ a (TaylorModel.eval c p x) 0) _ = _
  rw [he]

/-- At zero, the genuine generalized model Taylor polynomial equals the
original generalized objective Taylor polynomial through the model degree. -/
theorem taylorModel_regularizedModel_zero {f : E → ℝ} {c : E → F} (h : F → ℝ)
    {p j : ℕ} {x : E} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (hjp : j ≤ p) (σ : ℝ) (d : E) :
    taylorModel (smoothModel f p x σ) (residualModel c p x) h j 0 d =
      taylorModel f c h j x d := by
  unfold taylorModel
  rw [eval_residualModel_zero hc hjp]
  congr 1
  exact HighOrderRegularization.eval_model_zero hf hjp σ d

/-- At zero, actual regularized model and objective generalized criticality agree. -/
theorem criticality_regularizedModel_zero {f : E → ℝ} {c : E → F} (h : F → ℝ)
    {p j : ℕ} {x : E} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (hjp : j ≤ p) (σ δ : ℝ) :
    criticality (smoothModel f p x σ) (residualModel c p x) h j 0 δ =
      criticality f c h j x δ := by
  apply criticality_eq_of_decrement_eq
  intro d
  unfold decrement
  rw [taylorModel_regularizedModel_zero h hf hc hjp,
    taylorModel_regularizedModel_zero h hf hc hjp]

/-- A zero-decrease approximate-global solver return gives genuine approximate
objective optimality at positive radii and cannot follow a failing first-order
test when the outer function is convex. -/
theorem zero_step_termination {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p q : ℕ} (hqp : q ≤ p) {x s : E}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    {Df Dc σ μ ζ : ℝ} {K : NNReal} (hDf : 0 ≤ Df) (hDc : 0 ≤ Dc)
    (hσ : 0 < σ) (hμ : 0 < μ) (hζ : 0 < ζ) (hh : LipschitzWith K h)
    (hAf : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ Df)
    (hAc : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a c x‖ ≤ Dc)
    (hsolve : ModelDecrease.ApproximateGlobalStep (regularizedModel f c h p x σ) μ s)
    (hzero : regularizedModel f c h p x σ 0 = regularizedModel f c h p x σ s)
    (ε δ₀ : Fin q → ℝ) (hε : ∀ a, 0 < ε a) (hδ₀ : ∀ a, 0 < δ₀ a)
    (direction : Fin q → E) (hfeasible : ∀ a, ‖direction a‖ ≤ δ₀ a)
    (hfailed : ∃ a, ζ * ε a * δ₀ a ^ (a.val + 1) / (a.val + 1).factorial <
      decrement f c h (a.val + 1) x (direction a)) :
    (q = 1 → ¬ConvexOn ℝ Set.univ h) ∧
      ∃ δ : Fin q → ℝ, (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
        ∀ a, criticality f c h (a.val + 1) x (δ a) ≤
          ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial := by
  have hmin := hsolve.isGlobalMin_zero hμ hzero
  have haj (a : Fin q) : a.val + 1 ≤ p := (Nat.succ_le_of_lt a.isLt).trans hqp
  constructor
  · intro hq hconv
    obtain ⟨a, ha⟩ := hfailed
    have h1 : a.val + 1 = 1 := by omega
    have hz := criticality_one_regularizedModel_eq_zero f c
      (h1 ▸ haj a) hh hconv x 0 hmin (hδ₀ a).le
    rw [criticality_regularizedModel_zero h hf hc (h1 ▸ haj a)] at hz
    have hd := decrement_le_criticality f c hh.continuous (a.val + 1) x (hfeasible a)
    change decrement f c h (a.val + 1) x (direction a) ≤ _ at hd
    rw [h1, hz] at hd
    have hp : 0 < ζ * ε a * δ₀ a ^ (a.val + 1) / ((a.val + 1).factorial : ℝ) :=
      div_pos (mul_pos (mul_pos hζ (hε a)) (pow_pos (hδ₀ a) _)) (by positivity)
    rw [h1] at ha hp
    linarith
  · let B := 3 * (Df + (K : ℝ) * Dc) + σ
    have hB : 0 < B := by dsimp [B]; positivity
    have hex : ∀ a : Fin q, ∃ δ : ℝ, (0 < δ ∧ δ ≤ 1) ∧
        criticality f c h (a.val + 1) x δ ≤
          ε a * δ ^ (a.val + 1) / (a.val + 1).factorial := by
      intro a
      let r := min 1 (ε a / (4 * B))
      have hr : 0 < r := lt_min (by norm_num) (div_pos (hε a) (by positivity))
      have hb := criticality_lt_of_isMin_regularizedModel f c (by omega) (haj a)
        hDf hDc hσ hh x 0 (by simp) hAf hAc hmin (hε a) hr (min_le_left _ _)
          (min_le_right _ _)
      rw [criticality_regularizedModel_zero h hf hc (haj a)] at hb
      exact ⟨r, ⟨hr, min_le_left _ _⟩, hb.le⟩
    choose δ hδ hb using hex
    exact ⟨δ, hδ, hb⟩
end Composite
