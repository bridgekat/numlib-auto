import Numlib.Optimization.EvaluationComplexity.ParameterUpdates
import Numlib.Optimization.LineSearch.LipschitzGradient
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# First-order adaptive regularization

The quadratic regularization of a linear model has an explicit minimizer along
the negative gradient. Finite algorithm traces record the actual trial points,
acceptance ratios, acceptance decisions and regularization updates.
-/

namespace FirstOrderRegularization

open EvaluationComplexity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear model regularized by a quadratic squared-norm penalty, omitting
the irrelevant constant objective value. -/
noncomputable def model (g : E) (σ : ℝ) (s : E) : ℝ := inner ℝ g s + σ / 2 * ‖s‖ ^ 2

/-- The value of the regularized linear model at its explicit minimizer. -/
theorem model_neg_inv_smul (g : E) {σ : ℝ} (hσ : 0 < σ) :
    model g σ (-(σ⁻¹ • g)) = -‖g‖ ^ 2 / (2 * σ) := by
  simp only [model, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hσ.le)]
  field_simp
  ring

/-- The negative-gradient inverse-parameter step is a global minimizer of the
regularized linear model. -/
theorem isMinOn_model (g : E) {σ : ℝ} (hσ : 0 < σ) :
    IsMinOn (model g σ) Set.univ (-(σ⁻¹ • g)) := by
  intro s _
  rw [model_neg_inv_smul g hσ]
  change -‖g‖ ^ 2 / (2 * σ) ≤ inner ℝ g s + σ / 2 * ‖s‖ ^ 2
  have hi : - (‖g‖ * ‖s‖) ≤ inner ℝ g s :=
    (abs_le.mp (abs_real_inner_le_norm g s)).1
  apply (div_le_iff₀ (by positivity : 0 < 2 * σ)).mpr
  nlinarith [sq_nonneg (σ * ‖s‖ - ‖g‖),
    mul_nonneg hσ.le (show 0 ≤ inner ℝ g s + ‖g‖ * ‖s‖ by linarith)]

/-- A finite nonterminated prefix of first-order adaptive regularization. The
trial step is the model minimizer proved above; all other fields are operational
rules of the algorithm. No bound on the regularization parameter or iteration
count is included. -/
structure Run (f : E → ℝ) (g : E → E) (x : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin ε : ℝ) (N : ℕ) : Prop where
  derivative : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y
  updates : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  accuracy_pos : 0 < ε
  not_terminated : ∀ i < N, ε < ‖g (x i)‖
  ratio : ∀ i < N, ρ i = σ i * (f (x i) - f (x i - (σ i)⁻¹ • g (x i))) /
    ‖g (x i)‖ ^ 2
  step : ∀ i < N, x (i + 1) =
    if η₁ ≤ ρ i then x i - (σ i)⁻¹ • g (x i) else x i

namespace Run

variable {f : E → ℝ} {g : E → E} {x : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin ε L : ℝ} {N : ℕ}

/-- A large enough regularization parameter guarantees that the trial is very
successful. The proof uses the actual objective at the model-minimizing step. -/
theorem very_successful (h : Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) {i : ℕ} (hi : i < N)
    (hlarge : L / (2 * (1 - η₂)) ≤ σ i) : η₂ ≤ ρ i := by
  have hσ : 0 < σ i := h.updates.pos (by omega)
  have hη : 0 < 2 * (1 - η₂) := by linarith [h.updates.eta2_lt_one]
  have hmul : L ≤ 2 * (1 - η₂) * σ i := by
    have ht := (div_le_iff₀ hη).mp hlarge
    nlinarith
  have ht : L * (σ i)⁻¹ ≤ 2 * (1 - η₂) := by
    calc
      L * (σ i)⁻¹ ≤ (2 * (1 - η₂) * σ i) * (σ i)⁻¹ :=
        mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hσ.le)
      _ = 2 * (1 - η₂) := by field_simp
  have ha := LineSearch.armijo_neg_gradient_of_lipschitz h.derivative hL
    (inv_nonneg.mpr hσ.le) ht (x i)
  have hdecrease : η₂ * (σ i)⁻¹ * ‖g (x i)‖ ^ 2 ≤
      f (x i) - f (x i - (σ i)⁻¹ • g (x i)) := by
    simpa [LineSearch.Armijo, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      smul_neg, sub_eq_add_neg] using (show _ ≤ _ from sub_le_sub_left ha (f (x i)))
  have hnorm : 0 < ‖g (x i)‖ := h.accuracy_pos.trans (h.not_terminated i hi)
  rw [h.ratio i hi]
  apply (le_div_iff₀ (sq_pos_of_pos hnorm)).mpr
  calc
    η₂ * ‖g (x i)‖ ^ 2 = σ i * (η₂ * (σ i)⁻¹ * ‖g (x i)‖ ^ 2) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecrease hσ.le

/-- The regularization parameter has a uniform bound depending only on the
initial parameter, the gradient Lipschitz constant and the update constants. -/
theorem parameter_le (h : Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) {i : ℕ} (hi : i ≤ N) :
    σ i ≤ max (σ 0) (γ₃ * L / (2 * (1 - η₂))) := by
  simpa [mul_div_assoc] using h.updates.le_max_initial_threshold
    (fun j hj hlarge => h.very_successful hL hj hlarge) hi

/-- At a successful iteration the objective reduction is at least the
acceptance threshold times the squared gradient divided by the parameter. -/
theorem successful_decrease (h : Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) :
    η₁ * ‖g (x i)‖ ^ 2 / σ i ≤ f (x i) - f (x (i + 1)) := by
  have hσ : 0 < σ i := h.updates.pos (by omega)
  have hnorm : 0 < ‖g (x i)‖ := h.accuracy_pos.trans (h.not_terminated i hi)
  have he := (eq_div_iff (sq_pos_of_pos hnorm).ne').mp (h.ratio i hi)
  rw [h.step i hi, ite_eq_left hs]
  apply (div_le_iff₀ hσ).mpr
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖g (x i)‖)
  nlinarith

/-- Unsuccessful iterations keep the current point and hence its objective. -/
theorem objective_eq_of_unsuccessful (h : Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    {i : ℕ} (hi : i < N) (hu : ¬η₁ ≤ ρ i) : f (x (i + 1)) = f (x i) := by
  rw [h.step i hi, ite_eq_right hu]

/-- Every nonterminated prefix contains at most the objective gap divided by
the uniform successful decrease. The bound is independent of the requested
accuracy except for its explicit factor `ε⁻²`. -/
theorem successful_card_le (h : Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) {flow : ℝ} (hlow : flow ≤ f (x N)) :
    ((EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      (max (σ 0) (γ₃ * L / (2 * (1 - η₂))) / η₁) *
        (f (x 0) - flow) / ε ^ 2 := by
  let σmax := max (σ 0) (γ₃ * L / (2 * (1 - η₂)))
  have hmaxpos : 0 < σmax := (h.updates.pos (Nat.zero_le N)).trans_le (le_max_left _ _)
  have hη := h.updates.eta1_pos
  have hε := h.accuracy_pos
  have hd : 0 < η₁ * ε ^ 2 / σmax := by positivity
  have hc := EvaluationComplexity.card_successful_le_gap_div
    (S := {i | η₁ ≤ ρ i}) (f := fun i => f (x i)) hd hlow
    (fun i hi hs => ?_) (fun i hi hu => (h.objective_eq_of_unsuccessful hi hu).le)
  · convert hc using 1
    dsimp [σmax]
    field_simp
  · have hnorm := h.not_terminated i hi
    have hsq : ε ^ 2 ≤ ‖g (x i)‖ ^ 2 := by nlinarith [norm_nonneg (g (x i))]
    have hσ := h.updates.pos (show i ≤ N by omega)
    calc
      η₁ * ε ^ 2 / σmax ≤ η₁ * ‖g (x i)‖ ^ 2 / σmax :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hη.le) hmaxpos.le
      _ ≤ η₁ * ‖g (x i)‖ ^ 2 / σ i :=
        div_le_div_of_nonneg_left (mul_nonneg hη.le (sq_nonneg _)) hσ (h.parameter_le hL (by omega))
      _ ≤ _ := h.successful_decrease hi hs

/-- Combining the successful-iteration budget and the logarithmic update bound
controls the total length of every nonterminated prefix. -/
theorem iterations_le (h : Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) {flow : ℝ} (hlow : flow ≤ f (x N)) :
    (N : ℝ) ≤
      (max (σ 0) (γ₃ * L / (2 * (1 - η₂))) / η₁) *
          (f (x 0) - flow) / ε ^ 2 * (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max (σ 0) (γ₃ * L / (2 * (1 - η₂))) / σ 0) / Real.log γ₂ := by
  have hc := EvaluationComplexity.iteration_bound_of_parameter_upper
    (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.updates.pos hi)
    h.updates.gamma1_pos h.updates.gamma1_lt_one h.updates.one_lt_gamma2
    (h.parameter_le hL le_rfl) (fun _ hi hs => h.updates.successful_ge hi hs)
    (fun _ hi hu => h.updates.unsuccessful_ge hi hu)
  have hlog := Real.log_pos h.updates.one_lt_gamma2
  have ha : 0 ≤ 1 + |Real.log γ₁| / Real.log γ₂ := by positivity
  exact hc.trans (add_le_add (mul_le_mul_of_nonneg_right
    (h.successful_card_le hL hlow) ha) le_rfl)

end Run

/-- A consistent execution whose prefixes obey the algorithm rules until the
stopping test succeeds must terminate. This does not assume a bound on any
iteration count or successful-iteration count. -/
theorem exists_termination {f : E → ℝ} {g : E → E} {x : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin ε L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖g (x i)‖) →
      Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hlow : ∀ y, flow ≤ f y) :
    ∃ K, ‖g (x K)‖ ≤ ε ∧ Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε K := by
  have hex : ∃ K, ‖g (x K)‖ ≤ ε := by
    by_contra hnone
    push Not at hnone
    let B := (max (σ 0) (γ₃ * L / (2 * (1 - η₂))) / η₁) *
          (f (x 0) - flow) / ε ^ 2 * (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max (σ 0) (γ₃ * L / (2 * (1 - η₂))) / σ 0) / Real.log γ₂
    obtain ⟨N, hN⟩ := exists_nat_gt B
    have hr := hprefix N (fun i _ => hnone i)
    have hb := hr.iterations_le hL (hlow _)
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_⟩
  intro i hi
  exact lt_of_not_ge (Nat.find_min hex hi)

end FirstOrderRegularization
