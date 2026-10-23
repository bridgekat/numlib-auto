import Numlib.Optimization.Regularization.HighOrder.Run
import Numlib.Optimization.EvaluationComplexity.Decrease


/-!
# Full third-order high-order regularization evaluation complexity

The corrected stopping test omits only the source's false nonempty-direction
condition. Actual gradient, Hessian, third-derivative and small-Hessian endpoint
obstructions consume the uniform successful-step objective budget. The exact
source constants precede every requested accuracy and execution. Actual
regularization updates give total trials, first-stop termination, and all
initialized function and derivative evaluation counts. A strict-Hessian exit
returns no third-order directions; every other exit returns its actual inherited
model direction set and certifies the source's true small-curvature containment.
-/

namespace HighOrderRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The common minimum of the three source fractional accuracy powers. -/
noncomputable def finiteAccuracyFactor (p : ℕ) (ε₁ ε₂ ε₃ : ℝ) : ℝ :=
  min (ε₁ ^ (((p + 1 : ℕ) : ℝ) / p))
    (min (ε₂ ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
      (ε₃ ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))))

/-- The common accuracy-independent minimum of the three exact decrease constants. -/
noncomputable def finiteDecreaseCoefficient (p : ℕ)
    (σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ : ℝ) : ℝ :=
  let σmax := max σ₀ (γ₃ * L / (1 - η₂))
  min (decreaseConstant p p η₁ σmin L σmax θ₁)
    (min (decreaseConstant p (p - 1) η₁ σmin L σmax θ₂)
      (decreaseConstant p (p - 2) η₁ σmin L σmax θ₃))

/-- The reciprocal of each successful-decrease coefficient has its printed source form. -/
theorem inv_decreaseConstant_eq (p m : ℕ) {η₁ σmin L σmax θ : ℝ}
    (hL : 0 < L) (hσ : 0 ≤ σmax) (hθ : 0 ≤ θ) :
    1 / decreaseConstant p m η₁ σmin L σmax θ =
      (p + 1).factorial / (η₁ * σmin) *
        ((L + σmax + θ * m.factorial) / m.factorial) ^ (((p + 1 : ℕ) : ℝ) / m) := by
  have hk := stepConstant_pos m hL hσ hθ
  unfold decreaseConstant
  rw [one_div, mul_inv_rev, ←Real.inv_rpow hk.le]
  simp only [stepConstant, inv_div]
  ring

private theorem one_div_min_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / min a b = max (1 / a) (1 / b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (one_div_le_one_div_of_le ha h)]
  · rw [min_eq_right h, max_eq_right (one_div_le_one_div_of_le hb h)]

/-- The inverse minimum accuracy power is exactly the source maximum of inverse powers. -/
theorem inv_finiteAccuracyFactor_eq (p : ℕ) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) :
    1 / finiteAccuracyFactor p ε₁ ε₂ ε₃ =
      max (ε₁ ^ (-((p + 1 : ℕ) : ℝ) / p))
        (max (ε₂ ^ (-((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
          (ε₃ ^ (-((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)))) := by
  have hpow₁ := Real.rpow_pos_of_pos h₁ (((p + 1 : ℕ) : ℝ) / p)
  have hpow₂ := Real.rpow_pos_of_pos h₂ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))
  have hpow₃ := Real.rpow_pos_of_pos h₃ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))
  rw [finiteAccuracyFactor,one_div_min_of_pos hpow₁ (lt_min hpow₂ hpow₃),
    one_div_min_of_pos hpow₂ hpow₃]
  simp_rw [one_div, ←Real.rpow_neg h₁.le,
    ←Real.rpow_neg h₂.le, ←Real.rpow_neg h₃.le, neg_div]

/-- The exact successful-iteration constant (4.1.45), independent of all accuracies. -/
noncomputable def successfulIterationConstant (p : ℕ)
    (σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ : ℝ) : ℝ :=
  let σmax := max σ₀ (γ₃ * L / (1 - η₂))
  (p + 1).factorial / (η₁ * σmin) *
    max (((L + σmax + θ₁ * p.factorial) / p.factorial) ^ (((p + 1 : ℕ) : ℝ) / p))
      (max (((L + σmax + θ₂ * (p - 1).factorial) / (p - 1).factorial) ^
        (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
        (((L + σmax + θ₃ * (p - 2).factorial) / (p - 2).factorial) ^
          (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))))

/-- The printed iteration constant is positive for fixed legal parameter data. -/
theorem successfulIterationConstant_pos (p : ℕ)
    {σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ : ℝ}
    (hσ : 0 < σ₀) (hmin : 0 < σmin) (hη : 0 < η₁) (hL : 0 < L)
    (hθ₁ : 0 < θ₁) :
    0 < successfulIterationConstant p σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ := by
  have hm : 0 < max σ₀ (γ₃ * L / (1 - η₂)) := hσ.trans_le (le_max_left _ _)
  unfold successfulIterationConstant
  positivity

/-- The strict-Hessian branch returns no third-order directions; otherwise the
algorithm returns its actual inherited model direction set. -/
def returnedDirections (μ ε₂ : ℝ) (M : Set E) : Set E := if ε₂ < μ then ∅ else M

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Returned directions are inherited directions unless the strict-Hessian branch applies. -/
theorem mem_returnedDirections_iff {μ ε₂ : ℝ} {M : Set E} {v : E} :
    v ∈ returnedDirections μ ε₂ M ↔ μ ≤ ε₂ ∧ v ∈ M := by
  by_cases h : ε₂ < μ <;> simp [returnedDirections,h,not_lt.mp,not_le.mpr]

omit [CompleteSpace E] in
/-- Repaired finite termination guarantees both true derivative bounds and all
requested directional bounds in the actual returned set. -/
theorem finiteStop_guarantees {f : E → ℝ} {x : E} {μ ε₁ ε₂ ε₃ : ℝ} {M : Set E}
    (h : finiteStop f x μ M ε₁ ε₂ ε₃) (hε₂ : 0 ≤ ε₂) :
    ‖fderiv ℝ f x‖ ≤ ε₁ ∧ -ε₂ ≤ μ ∧
      ∀ v ∈ returnedDirections μ ε₂ M,
        |iteratedFDeriv ℝ 3 f x (fun _ => v)| ≤ ε₃ ∧
          |iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ ε₂ := by
  refine ⟨h.1,?_,?_⟩
  · rcases h.2 with hs | hn
    · linarith
    · exact hn.1
  · intro v hv
    have hv' := mem_returnedDirections_iff.mp hv
    rcases h.2 with hs | hn
    · exact False.elim (not_lt_of_ge hv'.1 hs)
    · exact hn.2 v hv'.2

namespace FiniteRun
variable {f : E → ℝ} {p : ℕ} {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ} {M : ℕ → Set E}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ L : ℝ} {N : ℕ}

/-- Every inherited model direction is a genuine unit vector, including initialization. -/
theorem directions_unit
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    {i : ℕ} (hi : i ≤ N) {v : E} (hv : v ∈ M i) : ‖v‖ = 1 := by
  cases i with
  | zero => rw [h.initial_directions] at hv; exact hv.1
  | succ i => rw [h.model_directions i (by omega)] at hv; exact hv.1

/-- The strict-Hessian exit has no true unit small-curvature direction. -/
theorem initialDirections_eq_empty_of_strict
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N) (hs : ε₂ < μ N) :
    initialDirections f (x N) ε₂ = ∅ := by
  ext v
  simp only [mem_initialDirections_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hv,hD⟩
  have hb := (h.least_eigenpair N le_rfl).least v hv
  linarith [(abs_le.mp hD).2]

/-- The returned model directions lie in the true unit small-Hessian set at termination. -/
theorem terminal_guarantees
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hs : finiteStop f (x N) (μ N) (M N) ε₁ ε₂ ε₃) :
    ‖fderiv ℝ f (x N)‖ ≤ ε₁ ∧ -ε₂ ≤ μ N ∧
      returnedDirections (μ N) ε₂ (M N) ⊆ initialDirections f (x N) ε₂ ∧
      ∀ v ∈ returnedDirections (μ N) ε₂ (M N),
        |iteratedFDeriv ℝ 3 f (x N) (fun _ => v)| ≤ ε₃ := by
  obtain ⟨hg,hμ,hd⟩ := finiteStop_guarantees hs h.accuracy_second_pos.le
  refine ⟨hg,hμ,?_,fun v hv => (hd v hv).1⟩
  intro v hv
  exact ⟨h.directions_unit le_rfl (mem_returnedDirections_iff.mp hv).2,(hd v hv).2⟩

/-- Every source coefficient is strictly positive before accuracies enter the bound. -/
theorem decrease_coefficients_pos
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hL : 0 < L) :
    0 < decreaseConstant p p η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₁ ∧
    0 < decreaseConstant p (p - 1) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ ∧
    0 < decreaseConstant p (p - 2) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₃ := by
  have hm : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.trace.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  exact ⟨decreaseConstant_pos p p h.trace.updates.eta1_pos h.trace.updates.min_pos hL hm
      h.theta_first_pos.le,
    decreaseConstant_pos p (p - 1) h.trace.updates.eta1_pos h.trace.updates.min_pos hL hm
      h.theta_second_pos.le,
    decreaseConstant_pos p (p - 2) h.trace.updates.eta1_pos h.trace.updates.min_pos hL hm
      h.theta_third_pos.le⟩

/-- The minimum source decrease coefficient is positive. -/
theorem finiteDecreaseCoefficient_pos
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hL : 0 < L) :
    0 < finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ := by
  obtain ⟨h₁,h₂,h₃⟩ := h.decrease_coefficients_pos hL
  exact lt_min h₁ (lt_min h₂ h₃)

/-- The three requested positive accuracies give a positive common accuracy factor. -/
theorem finiteAccuracyFactor_pos
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N) :
    0 < finiteAccuracyFactor p ε₁ ε₂ ε₃ := by
  have h₁ := h.accuracy_first_pos
  have h₂ := h.accuracy_second_pos
  have h₃ := h.accuracy_third_pos
  unfold finiteAccuracyFactor
  positivity

/-- The common budget is bounded by the first, second and third threshold budgets. -/
theorem threshold_budgets
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hL : 0 < L) :
    let c := finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃
    let a := finiteAccuracyFactor p ε₁ ε₂ ε₃
    c * a ≤ decreaseConstant p p η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₁ *
      ε₁ ^ (((p + 1 : ℕ) : ℝ) / p) ∧
    c * a ≤
      decreaseConstant p (p - 1) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ *
      ε₂ ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ∧
    c * a ≤
      decreaseConstant p (p - 2) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₃ *
      ε₃ ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) := by
  obtain ⟨h₁,h₂,h₃⟩ := h.decrease_coefficients_pos hL
  have ha := h.finiteAccuracyFactor_pos.le
  refine ⟨mul_le_mul (min_le_left _ _) (min_le_left _ _) ha h₁.le,?_,?_⟩
  · exact mul_le_mul ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_left _ _)) ha h₂.le
  · exact mul_le_mul ((min_le_right _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) ha h₃.le

/-- The reciprocal minimum coefficient is exactly the source constant (4.1.45). -/
theorem inv_finiteDecreaseCoefficient_eq
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hL : 0 < L) :
    1 / finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ =
      (p + 1).factorial / (η₁ * σmin) *
        max (((L + max (σ 0) (γ₃ * L / (1 - η₂)) + θ₁ * p.factorial) / p.factorial) ^
          (((p + 1 : ℕ) : ℝ) / p))
          (max (((L + max (σ 0) (γ₃ * L / (1 - η₂)) + θ₂ * (p - 1).factorial) /
            (p - 1).factorial) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
            (((L + max (σ 0) (γ₃ * L / (1 - η₂)) + θ₃ * (p - 2).factorial) /
              (p - 2).factorial) ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)))) := by
  obtain ⟨h₁,h₂,h₃⟩ := h.decrease_coefficients_pos hL
  have hm : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.trace.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  unfold finiteDecreaseCoefficient
  rw [one_div_min_of_pos h₁ (lt_min h₂ h₃), one_div_min_of_pos h₂ h₃,
    inv_decreaseConstant_eq p p hL hm h.theta_first_pos.le,
    inv_decreaseConstant_eq p (p - 1) hL hm h.theta_second_pos.le,
    inv_decreaseConstant_eq p (p - 2) hL hm h.theta_third_pos.le]
  have hc : 0 ≤ (p + 1).factorial / (η₁ * σmin : ℝ) :=
    div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg h.trace.updates.eta1_pos.le h.trace.updates.min_pos.le)
  rw [mul_max_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc]

/-- The inverse decrease coefficient equals the named printed successful-iteration constant. -/
theorem inverse_coefficient
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hL : 0 < L) :
    1 / finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ =
      successfulIterationConstant p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ :=
  h.inv_finiteDecreaseCoefficient_eq hL

/-- Every accepted trial whose endpoint is still nonterminal
consumes the uniform objective budget. -/
theorem nonterminal_successful_decrease
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hf : ContDiff ℝ p f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i + 1 < N) (hs : η₁ ≤ ρ i) :
    finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ *
      finiteAccuracyFactor p ε₁ ε₂ ε₃ ≤ f (x i) - f (x (i + 1)) := by
  have hi' : i < N := by omega
  have hp := h.order_ge_three
  have hm : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.trace.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hk₁ := stepConstant_pos p hL hm h.theta_first_pos.le
  have hk₂ := stepConstant_pos (p - 1) hL hm h.theta_second_pos.le
  have hk₃ := stepConstant_pos (p - 2) hL hm h.theta_third_pos.le
  obtain ⟨hB₁,hB₂,hB₃⟩ := h.threshold_budgets hL
  by_cases hg : ε₁ < ‖fderiv ℝ f (x (i + 1))‖
  · have hb := (mul_le_mul_of_nonneg_left hg.le hk₁.le).trans
      (h.trace.step_lower_first hf hL h.theta_first_pos.le hlip hi' hs
        (h.stationary i hi').first)
    exact hB₁.trans (h.trace.decrease_of_step_lower hi' hs h.trace.order_pos hk₁.le
      h.accuracy_first_pos.le hb)
  have hg' : ‖fderiv ℝ f (x (i + 1))‖ ≤ ε₁ := le_of_not_gt hg
  by_cases hc : μ (i + 1) < -ε₂
  · have hε : ε₂ ≤ max 0 (-μ (i + 1)) := by linarith [le_max_right 0 (-μ (i + 1))]
    have hb := (mul_le_mul_of_nonneg_left hε hk₂.le).trans
      (h.trace.step_lower_second (by omega) hf hL h.theta_second_pos.le hlip hi' hs
        (h.stationary i hi').second (h.least_eigenpair (i + 1) hi.le))
    exact hB₂.trans (h.trace.decrease_of_step_lower hi' hs (by omega : 0 < p - 1) hk₂.le
      h.accuracy_second_pos.le hb)
  have hc' : -ε₂ ≤ μ (i + 1) := le_of_not_gt hc
  by_cases ht : ∀ v ∈ M (i + 1), |iteratedFDeriv ℝ 3 f (x (i + 1)) (fun _ => v)| ≤ ε₃
  · have hfail : ∃ v ∈ M (i + 1),
        ε₂ < |iteratedFDeriv ℝ 2 f (x (i + 1)) (fun _ => v)| := by
      by_contra! hn
      exact h.not_terminated (i + 1) hi
        ⟨hg', Or.inr ⟨hc', fun v hv => ⟨ht v hv,hn v hv⟩⟩⟩
    obtain ⟨v,hv,hbig⟩ := hfail
    rw [h.model_directions i hi'] at hv
    have hcurv := h.trace.small_curvature_le (by omega) hf hL.le hlip hi' hs hv
    have hb := mul_le_mul_of_nonneg_left (hbig.le.trans hcurv) hk₂.le
    have he : stepConstant (p - 1) L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ *
        (1 / stepConstant (p - 1) L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ *
          ‖s i‖ ^ (p - 1)) = ‖s i‖ ^ (p - 1) := by field_simp
    rw [he] at hb
    exact hB₂.trans (h.trace.decrease_of_step_lower hi' hs (by omega : 0 < p - 1) hk₂.le
      h.accuracy_second_pos.le hb)
  · push Not at ht
    obtain ⟨v,hv,hbig⟩ := ht
    rw [h.model_directions i hi'] at hv
    have hb := (mul_le_mul_of_nonneg_left hbig.le hk₃.le).trans
      (h.trace.step_lower_third h.order_ge_three hf hL h.theta_third_pos.le hlip hi' hs
        (h.stationary i hi').third hv)
    exact hB₃.trans (h.trace.decrease_of_step_lower hi' hs (by omega : 0 < p - 2) hk₃.le
      h.accuracy_third_pos.le hb)

/-- Failed trials preserve the actual objective value. -/
theorem objective_eq_of_unsuccessful
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    {i : ℕ} (hi : i < N) (hu : ¬η₁ ≤ ρ i) : f (x (i + 1)) = f (x i) := by
  rw [h.trace.point_update i hi, ite_eq_right hu]

/-- At most one final accepted endpoint escapes the nonterminal objective budget. -/
theorem successful_card_le
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hf : ContDiff ℝ p f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤ (f (x 0) - flow) /
      (finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ *
        finiteAccuracyFactor p ε₁ ε₂ ε₃) + 1 := by
  have hgap : 0 ≤ f (x 0) - flow := sub_nonneg.mpr (hlow _)
  have hdpos := mul_pos (h.finiteDecreaseCoefficient_pos hL) h.finiteAccuracyFactor_pos
  cases N with
  | zero => simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]; positivity
  | succ k =>
    have hc := card_successful_le_gap_div
      (S := {i | η₁ ≤ ρ i}) (f := fun i => f (x i)) hdpos (hlow (x k))
      (fun i hi hs => h.nonterminal_successful_decrease hf hL hlip (by omega) hs)
      (fun i hi hu => (h.objective_eq_of_unsuccessful (by omega) hu).le)
    have hsucc : ((successfulIterations {i | η₁ ≤ ρ i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | η₁ ≤ ρ i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | η₁ ≤ ρ i} k
    exact hsucc.trans (add_le_add hc le_rfl)

/-- Actual regularization updates bound all trials by the successful objective budget. -/
theorem iterations_le
    (h : FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hf : ContDiff ℝ p f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    (N : ℝ) ≤ ((f (x 0) - flow) /
      (finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ *
        finiteAccuracyFactor p ε₁ ε₂ ε₃) + 1) *
        (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂ := by
  have ht := iteration_bound_of_parameter_upper
    (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.trace.updates.pos hi)
    h.trace.updates.gamma1_pos h.trace.updates.gamma1_lt_one
    h.trace.updates.one_lt_gamma2 (h.trace.parameter_le hf hL.le hlip le_rfl)
    (fun _ hi hs => h.trace.updates.successful_ge hi hs)
    (fun _ hi hu => h.trace.updates.unsuccessful_ge hi hu)
  have hlog := Real.log_pos h.trace.updates.one_lt_gamma2
  have hA : 0 ≤ 1 + |Real.log γ₁| / Real.log γ₂ := by positivity
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.successful_card_le hf hL hlip hlow) hA) le_rfl)

end FiniteRun

/-- Consistent actual ARp execution prefixes reach the first repaired finite-third-order stop. -/
theorem exists_finite_termination {f : E → ℝ} {p : ℕ}
    {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ} {M : ℕ → Set E}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ¬finiteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃) →
      FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
        θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N)
    (hf : ContDiff ℝ p f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, finiteStop f (x K) (μ K) (M K) ε₁ ε₂ ε₃ ∧
      FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
        θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ K ∧
      ∀ i < K, ¬finiteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃ := by
  classical
  have hex : ∃ K, finiteStop f (x K) (μ K) (M K) ε₁ ε₂ ε₃ := by
    by_contra hn
    have hnon : ∀ i, ¬finiteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃ := not_exists.mp hn
    let bound := ((f (x 0) - flow) /
      (finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ *
        finiteAccuracyFactor p ε₁ ε₂ ε₃) + 1) * (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
    obtain ⟨N,hN⟩ := exists_nat_gt bound
    exact (not_le_of_gt hN)
      ((hprefix N (fun i _ => hnon i)).iterations_le hf hL hlip hlow)
  have hnon : ∀ i < Nat.find hex, ¬finiteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃ :=
    fun i hi => Nat.find_min hex hi
  exact ⟨Nat.find hex,Nat.find_spec hex,hprefix _ hnon,hnon⟩

/-- Fixed printed constants precede every accuracy request and every actual corrected ARp execution.
The first stopping point satisfies all true optimality clauses
and all initialized evaluation bounds. -/
theorem exists_uniform_finite_complexity {f : E → ℝ} (p : ℕ)
    {σinit σmin η₁ η₂ γ₁ γ₂ γ₃ L θ₁ θ₂ θ₃ flow : ℝ}
    (hf : ContDiff ℝ p f) (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) (hσ : 0 < σinit) (hmin : 0 < σmin) (hη : 0 < η₁)
    (hγ₂ : 1 < γ₂) (hθ₁ : 0 < θ₁) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = successfulIterationConstant p σinit σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = |Real.log γ₁| / Real.log γ₂ +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2 ∧
      ∀ ε₁ ε₂ ε₃ : ℝ, ∀ x s u : ℕ → E,
      ∀ μ σ ρ : ℕ → ℝ, ∀ M : ℕ → Set E,
        σ 0 = σinit →
        (∀ N, (∀ i < N, ¬finiteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃) →
          FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
            θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N) →
        ∃ K, finiteStop f (x K) (μ K) (M K) ε₁ ε₂ ε₃ ∧
          FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
            θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ K ∧
          (∀ i < K, ¬finiteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃) ∧
          ‖fderiv ℝ f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K ∧
          returnedDirections (μ K) ε₂ (M K) ⊆ initialDirections f (x K) ε₂ ∧
          (∀ v ∈ returnedDirections (μ K) ε₂ (M K),
            |iteratedFDeriv ℝ 3 f (x K) (fun _ => v)| ≤ ε₃) ∧
          (functionEvaluations K : ℝ) ≤
            κA * (f (x 0) - flow) / finiteAccuracyFactor p ε₁ ε₂ ε₃ + κC ∧
          (derivativeEvaluations ρ η₁ K : ℝ) ≤
            κS * (f (x 0) - flow) / finiteAccuracyFactor p ε₁ ε₂ ε₃ + 2 := by
  let S := successfulIterationConstant p σinit σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃
  let A := 1 + |Real.log γ₁| / Real.log γ₂
  let C := Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂
  have hS : 0 < S := successfulIterationConstant_pos p hσ hmin hη hL hθ₁
  have hlog := Real.log_pos hγ₂
  have hA : 0 < A := by dsimp [A]; positivity
  have hratio : 1 ≤ max σinit (γ₃ * L / (1 - η₂)) / σinit := by
    apply (le_div_iff₀ hσ).mpr
    simpa only [one_mul] using le_max_left σinit (γ₃ * L / (1 - η₂))
  have hC : 0 ≤ C := div_nonneg (Real.log_nonneg hratio) hlog.le
  refine ⟨S,hS,S * A,mul_pos hS hA,A + C + 1,by positivity,rfl,rfl,?_,?_⟩
  · dsimp [A,C]
    ring
  intro ε₁ ε₂ ε₃ x s u μ σ ρ M hσ0 hprefix
  obtain ⟨K,hstop,hK,hfirst⟩ := exists_finite_termination hprefix hf hL hlip hlow
  obtain ⟨hg,hμ,hM,hthird⟩ := hK.terminal_guarantees hstop
  have hcinv := hK.inverse_coefficient hL
  rw [hσ0] at hcinv
  have hF := hK.iterations_le hf hL hlip hlow
  have hD := hK.successful_card_le hf hL hlip hlow
  refine ⟨K,hstop,hK,hfirst,hg,hμ,hM,hthird,?_,?_⟩
  · simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
    have hb := add_le_add hF (le_refl (1 : ℝ))
    rw [hσ0] at hb
    convert hb using 1
    dsimp [S,A,C]
    rw [←hcinv]
    ring
  · simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
    have hb : ((successfulIterations {i | η₁ ≤ ρ i} K).card : ℝ) + 1 ≤
        (f (x 0) - flow) /
          (finiteDecreaseCoefficient p (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ *
            finiteAccuracyFactor p ε₁ ε₂ ε₃) + 2 := by linarith
    rw [hσ0] at hb
    convert hb using 1
    dsimp [S]
    rw [←hcinv]
    ring

end HighOrderRegularization
