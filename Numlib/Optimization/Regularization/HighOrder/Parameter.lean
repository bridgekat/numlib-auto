import Numlib.Optimization.HighOrder.ModelDecrease
import Numlib.Analysis.Calculus.TaylorModel.Holder
import Numlib.Optimization.EvaluationComplexity.ParameterUpdates

/-!
# Actual high-order regularization models and parameter bounds

The actual degree-`p` Taylor polynomial receives its factorial-normalized
norm-power penalty. Strict model improvement makes the prediction denominator
positive. The sharp actual Taylor remainder bounds the objective-based ratio,
and the source's three update intervals then bound every regularization parameter.
Only these operational components are needed; stationarity and stopping rules
are separate from this model-trace specification.
-/

namespace HighOrderRegularization
open TaylorModel ModelDecrease EvaluationComplexity Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual factorial-normalized norm-power regularization of a Taylor model. -/
noncomputable def model (f : E → ℝ) (p : ℕ) (x : E) (σ : ℝ) (s : E) : ℝ :=
  penalized (eval f p x) p σ s

/-- The actual regularized model is the Taylor sum plus its norm-power penalty. -/
theorem model_eq (f : E → ℝ) (p : ℕ) (x : E) (σ : ℝ) (s : E) :
    model f p x σ s = eval f p x s + σ / (p + 1).factorial * ‖s‖ ^ (p + 1) := rfl

/-- At zero displacement the regularized model is the actual objective value. -/
@[simp] theorem model_zero (f : E → ℝ) (p : ℕ) (x : E) (σ : ℝ) :
    model f p x σ 0 = f x := by simp [model]

/-- Nonincrease of the actual regularized model yields the norm-power prediction floor. -/
theorem penalty_le_decrement (f : E → ℝ) (p : ℕ) (x s : E) (σ : ℝ)
    (hs : model f p x σ s ≤ model f p x σ 0) :
    σ / (p + 1).factorial * ‖s‖ ^ (p + 1) ≤ decrement f p x s :=
  ModelDecrease.penalty_le_decrement (eval f p x) p σ s hs

/-- Strict regularized-model improvement gives a strict prediction floor. -/
theorem penalty_lt_decrement (f : E → ℝ) (p : ℕ) (x s : E) (σ : ℝ)
    (hs : model f p x σ s < model f p x σ 0) :
    σ / (p + 1).factorial * ‖s‖ ^ (p + 1) < decrement f p x s :=
  ModelDecrease.penalty_lt_decrement (eval f p x) p σ s hs

/-- A strictly improving actual step has a positive prediction denominator. -/
theorem decrement_pos {f : E → ℝ} {p : ℕ} {x s : E} {σ : ℝ} (hσ : 0 ≤ σ)
    (hs : model f p x σ s < model f p x σ 0) : 0 < decrement f p x s := by
  have hp : 0 ≤ σ / (p + 1).factorial * ‖s‖ ^ (p + 1) := by positivity
  exact hp.trans_lt (penalty_lt_decrement f p x s σ hs)

/-- The acceptance ratio uses the actual objective reduction and actual Taylor prediction. -/
noncomputable def ratio (f : E → ℝ) (p : ℕ) (x s : E) : ℝ :=
  (f x - f (x + s)) / decrement f p x s

/-- The ratio is the actual objective drop divided by the Taylor decrement. -/
theorem ratio_eq (f : E → ℝ) (p : ℕ) (x s : E) :
    ratio f p x s = (f x - f (x + s)) / decrement f p x s := rfl

/-- The ratio error is exactly the normalized actual Taylor value error. -/
theorem ratio_error_eq {f : E → ℝ} {p : ℕ} {x s : E}
    (hd : 0 < decrement f p x s) :
    |ratio f p x s - 1| = |f (x + s) - eval f p x s| / decrement f p x s := by
  have heq : f x - f (x + s) - decrement f p x s = -(f (x + s) - eval f p x s) := by
    rw [decrement_eq]
    ring
  rw [ratio, div_sub_one hd.ne', heq, abs_div, abs_neg, abs_of_pos hd]

/-- The sharp actual degree-`p` Taylor value remainder on the whole normed space. -/
theorem value_error_le {f : E → ℝ} {p : ℕ} (hp : 0 < p) (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (x s : E) : |f (x + s) - eval f p x s| ≤ L * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact abs_sub_eval_le_lipschitz (p := n) (C := univ) (D := univ)
    isOpen_univ (Subset.refl _) convex_univ hf.contDiffOn hL
    (fun y _ z _ => hlip y z) (mem_univ x) (mem_univ (x + s))

/-- A strictly improving regularized step has ratio error at most `L/σ`. -/
theorem ratio_error_le {f : E → ℝ} {p : ℕ} (hp : 0 < p) (hf : ContDiff ℝ p f)
    {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 < σ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s : E} (hs : model f p x σ s < model f p x σ 0) :
    |ratio f p x s - 1| ≤ L / σ := by
  have hd := decrement_pos hσ.le hs
  have hdec := (penalty_lt_decrement f p x s σ hs).le
  have herr := value_error_le hp hf hL hlip x s
  rw [ratio_error_eq hd]
  apply (div_le_iff₀ hd).2
  have hm := mul_le_mul_of_nonneg_left hdec (div_nonneg hL hσ.le)
  have heq : (L / σ) * (σ / (p + 1).factorial * ‖s‖ ^ (p + 1)) =
      L * ‖s‖ ^ (p + 1) / (p + 1).factorial := by field_simp
  rw [heq] at hm
  exact herr.trans hm

/-- A parameter above the Lipschitz threshold gives very successful acceptance. -/
theorem very_successful {f : E → ℝ} {p : ℕ} (hp : 0 < p) (hf : ContDiff ℝ p f)
    {L σ η₂ : ℝ} (hL : 0 ≤ L) (hσ : 0 < σ) (hη₂ : η₂ < 1)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s : E} (hs : model f p x σ s < model f p x σ 0)
    (hlarge : L / (1 - η₂) ≤ σ) : η₂ ≤ ratio f p x s := by
  have hh := (abs_le.mp (ratio_error_le hp hf hL hσ hlip hs)).1
  have hη : 0 < 1 - η₂ := sub_pos.mpr hη₂
  have hm := (div_le_iff₀ hη).mp hlarge
  have hc : L / σ ≤ 1 - η₂ := (div_le_iff₀ hσ).2 (by nlinarith)
  linarith

/-- The model/acceptance/update components of an arbitrary-order regularization
execution. All models and ratios are genuine. Stationarity and stopping tests are
separate components; no parameter bound or decrease estimate is a field. -/
structure ModelTrace (f : E → ℝ) (p : ℕ) (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop where
  order_pos : 0 < p
  updates : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  improvement : ∀ i < N, model f p (x i) (σ i) (s i) < model f p (x i) (σ i) 0
  ratio : ∀ i < N, ρ i = HighOrderRegularization.ratio f p (x i) (s i)
  point_update : ∀ i < N, x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i

namespace ModelTrace
variable {f : E → ℝ} {p : ℕ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N : ℕ}

/-- Every shorter prefix obeys the same primitive operational rules. -/
theorem restrict (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {M : ℕ} (hM : M ≤ N) : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin M where
  order_pos := h.order_pos
  updates := {h.updates with update := fun i hi => h.updates.update i (hi.trans_le hM)}
  improvement := fun i hi => h.improvement i (hi.trans_le hM)
  ratio := fun i hi => h.ratio i (hi.trans_le hM)
  point_update := fun i hi => h.point_update i (hi.trans_le hM)

/-- Every nonterminal trial has the strict Taylor-decrement floor. -/
theorem model_decrease (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) :
    σ i / (p + 1).factorial * ‖s i‖ ^ (p + 1) < decrement f p (x i) (s i) :=
  penalty_lt_decrement f p (x i) (s i) (σ i) (h.improvement i hi)

/-- Actual prediction denominators are positive throughout the execution. -/
theorem denominator_pos (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) : 0 < decrement f p (x i) (s i) :=
  HighOrderRegularization.decrement_pos (h.updates.pos (by omega)).le (h.improvement i hi)

/-- The source ratio error bound holds at each genuine nonterminal trial. -/
theorem ratio_error_le (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ p f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) : |ρ i - 1| ≤ L / σ i := by
  rw [h.ratio i hi]
  exact HighOrderRegularization.ratio_error_le h.order_pos hf hL (h.updates.pos (by omega))
    hlip (h.improvement i hi)

/-- The Lipschitz threshold forces the source's very successful update branch. -/
theorem very_successful (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ p f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hlarge : L / (1 - η₂) ≤ σ i) : η₂ ≤ ρ i := by
  rw [h.ratio i hi]
  exact HighOrderRegularization.very_successful h.order_pos hf hL (h.updates.pos (by omega))
    h.updates.eta2_lt_one hlip (h.improvement i hi) hlarge

/-- Above the Lipschitz threshold the actual next parameter cannot increase. -/
theorem next_le_of_large (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ p f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hlarge : L / (1 - η₂) ≤ σ i) : σ (i + 1) ≤ σ i := by
  have hg := h.very_successful hf hL hlip hi hlarge
  have hu := h.updates.update i hi
  rw [ite_eq_left hg] at hu
  exact hu.2

/-- The exact three update intervals give the source's uniform parameter upper bound,
including the initial and terminal endpoints of every finite prefix. -/
theorem parameter_le (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ p f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i ≤ N) : σ i ≤ max (σ 0) (γ₃ * L / (1 - η₂)) := by
  simpa only [mul_div_assoc] using h.updates.le_max_initial_threshold
    (fun k hk hlarge => h.very_successful hf hL hlip hk hlarge) hi

/-- Every accepted step decreases the actual objective by at least its
factorial-normalized parameter-floor penalty. -/
theorem successful_decrease (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) :
    η₁ * σmin / (p + 1).factorial * ‖s i‖ ^ (p + 1) < f (x i) - f (x (i + 1)) := by
  have hσ := h.updates.min_le (show i ≤ N by omega)
  have hη := h.updates.eta1_pos
  have hr : η₁ * decrement f p (x i) (s i) ≤ f (x i) - f (x i + s i) := by
    have hh := hs
    rw [h.ratio i hi, ratio_eq] at hh
    exact (le_div_iff₀ (h.denominator_pos hi)).1 hh
  have hd := mul_lt_mul_of_pos_left (h.model_decrease hi) hη
  have hflo : η₁ * σmin / (p + 1).factorial * ‖s i‖ ^ (p + 1) ≤
      η₁ * (σ i / (p + 1).factorial * ‖s i‖ ^ (p + 1)) := by
    have hm := mul_le_mul_of_nonneg_left hσ
      (show 0 ≤ η₁ / (p + 1).factorial * ‖s i‖ ^ (p + 1) by positivity)
    convert hm using 1 <;> ring
  rw [h.point_update i hi, ite_eq_left hs]
  exact hflo.trans_lt (hd.trans_le hr)

end ModelTrace
end HighOrderRegularization
