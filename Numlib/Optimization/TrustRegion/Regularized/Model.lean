import Numlib.Analysis.Calculus.TaylorModel.Holder
import Numlib.Optimization.EvaluationComplexity.ParameterUpdates

/-!
# Regularized quadratic trust-region models

The model, ratio and radius components use the actual second-order Taylor
polynomial with a fixed positive quadratic regularization weight. Strict model
improvement gives a positive Taylor decrement. The sharp cubic value remainder
then guarantees very successful trials at small radii and a uniform radius floor.
-/

namespace RegularizedTrustRegion
open TaylorModel EvaluationComplexity Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual quadratic Taylor model with fixed quadratic regularization. -/
noncomputable def model (f : E → ℝ) (x : E) (ε : ℝ) (s : E) : ℝ :=
  eval f 2 x s + ε / 2 * ‖s‖ ^ 2

/-- The regularized model at the zero step equals the actual objective. -/
@[simp] theorem model_zero (f : E → ℝ) (x : E) (ε : ℝ) : model f x ε 0 = f x := by
  simp [model]

/-- Strict regularized-model improvement gives a strict Taylor decrease. -/
theorem model_decrease {f : E → ℝ} {x s : E} {ε : ℝ}
    (hs : model f x ε s < model f x ε 0) :
    ε / 2 * ‖s‖ ^ 2 < eval f 2 x 0 - eval f 2 x s := by
  simp only [model, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hs
  linarith


/-- The model-improvement, ratio and radius-update components of TR epsilon.
Stopping and model stationarity are separate from this component specification. -/
structure ModelTrace (f : E → ℝ) (x s : ℕ → E) (Δ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ ε : ℝ) (N : ℕ) : Prop where
  regularization_pos : 0 < ε
  initial_radius : ε < Δ 0
  updates : TrustRegionRadiusUpdates Δ ρ η₁ η₂ γ₁ γ₂ γ₃ N
  feasible : ∀ i < N, ‖s i‖ ≤ Δ i
  improvement : ∀ i < N, model f (x i) ε (s i) < model f (x i) ε 0
  ratio : ∀ i < N, ρ i = (f (x i) - f (x i + s i)) /
    (eval f 2 (x i) 0 - eval f 2 (x i) (s i))

namespace ModelTrace
variable {f : E → ℝ} {x s : ℕ → E} {Δ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ ε L : ℝ} {N : ℕ}

/-- Every computed regularized step is nonzero by actual strict model improvement. -/
theorem step_ne_zero (h : ModelTrace f x s Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    {i : ℕ} (hi : i < N) : s i ≠ 0 := by
  intro hs
  have hb := h.improvement i hi
  rw [hs] at hb
  exact (lt_irrefl _ hb)

/-- The actual acceptance ratio has a strictly positive denominator. -/
theorem denominator_pos (h : ModelTrace f x s Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    {i : ℕ} (hi : i < N) : 0 < eval f 2 (x i) 0 - eval f 2 (x i) (s i) := by
  have hε := h.regularization_pos
  exact (show 0 ≤ ε / 2 * ‖s i‖ ^ 2 by positivity).trans_lt
    (model_decrease (h.improvement i hi))

/-- Small feasible radii guarantee very successful trials by the sharp actual
Taylor value remainder and the regularization-induced model decrement. -/
theorem very_successful (h : ModelTrace f x s Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hf : ContDiff ℝ 2 f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N)
    (hsmall : Δ i < 3 * (1 - η₂) / L * ε) : η₂ ≤ ρ i := by
  have hη : 0 < 1 - η₂ := sub_pos.mpr h.updates.eta2_lt_one
  have hmul : L * Δ i < 3 * (1 - η₂) * ε := by
    have hh : Δ i < (3 * (1 - η₂) * ε) / L := by
      convert hsmall using 1
      ring
    have hh' := (lt_div_iff₀ hL).mp hh
    nlinarith
  have hstep : L * ‖s i‖ ≤ 3 * (1 - η₂) * ε :=
    (mul_le_mul_of_nonneg_left (h.feasible i hi) hL.le).trans hmul.le
  have herr := abs_sub_eval_le_lipschitz (p := 1) (C := univ) (D := univ)
    isOpen_univ (Subset.refl _) convex_univ hf.contDiffOn hL.le
    (fun y _ z _ => hlip y z) (mem_univ (x i)) (mem_univ (x i + s i))
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at herr
  have hd := model_decrease (h.improvement i hi)
  have he : f (x i + s i) - eval f 2 (x i) (s i) ≤
      (1 - η₂) * (eval f 2 (x i) 0 - eval f 2 (x i) (s i)) := by
    have h1 := (abs_le.mp herr).2
    have h2 := mul_le_mul_of_nonneg_right hstep (sq_nonneg ‖s i‖)
    have h3 := mul_le_mul_of_nonneg_left hd.le hη.le
    nlinarith
  rw [h.ratio i hi]
  apply (le_div_iff₀ (h.denominator_pos hi)).mpr
  rw [eval_zero] at he ⊢
  linarith

/-- At a small radius the trial is accepted and its next radius does not shrink. -/
theorem successful_and_nondecreasing
    (h : ModelTrace f x s Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hf : ContDiff ℝ 2 f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N)
    (hsmall : Δ i < 3 * (1 - η₂) / L * ε) :
    η₂ ≤ ρ i ∧ η₁ ≤ ρ i ∧ Δ i ≤ Δ (i + 1) := by
  have hv := h.very_successful hf hL hlip hi hsmall
  have hu := h.updates.update i hi
  rw [ite_eq_left hv] at hu
  exact ⟨hv, h.updates.eta1_le_eta2.trans hv, hu.1⟩

/-- All radii stay above the smaller of the initial radius and the
small-radius threshold multiplied by the maximum contraction factor. -/
theorem radius_floor_min (h : ModelTrace f x s Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hf : ContDiff ℝ 2 f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i ≤ N) :
    min (Δ 0) (γ₁ * (3 * (1 - η₂) / L * ε)) ≤ Δ i :=
  h.updates.min_initial_threshold_le
    (fun _ hj hs => h.very_successful hf hL hlip hj hs) hi

/-- With the source normalization `L ≥ 1`, the prescribed initial radius
implies the printed uniform floor at every endpoint. -/
theorem radius_floor (h : ModelTrace f x s Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i ≤ N) :
    (1 - η₂) * γ₁ / L * ε ≤ Δ i := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hε := h.regularization_pos
  have hγpos := h.updates.gamma1_pos
  have hη : 0 < 1 - η₂ := sub_pos.mpr h.updates.eta2_lt_one
  have hηpos : 0 < η₂ := h.updates.eta1_pos.trans_le h.updates.eta1_le_eta2
  have hγ : γ₁ < 1 := h.updates.gamma1_le_gamma2.trans_lt h.updates.gamma2_lt_one
  have hcoeff : (1 - η₂) * γ₁ / L ≤ 1 := by
    apply (div_le_one hLpos).mpr
    nlinarith [h.updates.gamma1_pos]
  apply le_trans _ (h.radius_floor_min hf hLpos hlip hi)
  apply le_min
  · exact ((mul_le_mul_of_nonneg_right hcoeff h.regularization_pos.le).trans
      (by simpa using h.initial_radius.le))
  · have hbase : 0 ≤ (1 - η₂) * γ₁ / L * ε := by positivity
    have heq : γ₁ * (3 * (1 - η₂) / L * ε) =
        3 * ((1 - η₂) * γ₁ / L * ε) := by ring
    rw [heq]
    linarith

end ModelTrace
end RegularizedTrustRegion
