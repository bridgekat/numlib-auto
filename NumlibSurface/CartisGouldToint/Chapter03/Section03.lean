import Numlib.Optimization.Regularization.Cubic.FirstOrder
import NumlibSurface.CartisGouldToint.Chapter02.Section03
import Numlib.Analysis.Calculus.Gradient

/-!
# Cartis–Gould–Toint, Section 3.3: cubic model decrease and parameter bounds

These results use precisely the model-improvement, acceptance-ratio and
parameter-update components of AR2. The model is built from actual Taylor
derivative tensors. Step stationarity, second-order tests and termination are
irrelevant to Lemmas 3.3.1–2. Lemma 3.3.3 additionally uses the actual model
stationarity and accepted-step rules; the complete AR2 trace remains separately planned.
-/

namespace CartisGouldToint

/-- The actual AR2 cubic model (3.3.1), with coefficient `σ/6`. -/
noncomputable abbrev ar2Model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (σ : ℝ) (s : E) : ℝ := CubicRegularization.model f x σ s

/-- The model, actual-ratio and update components of AR2 used in Lemma 3.3.2.
This does not stand in for the complete algorithm trace. -/
abbrev ar2ModelTrace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
  CubicRegularization.ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N

/-- **Lemma 3.3.1.** Strict decrease of the actual cubic model, as required
by Step 2 of AR2, gives the Taylor decrease (3.3.13). -/
theorem lemma_3_3_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x s : E) (σ : ℝ) (hs : ar2Model f x σ s < ar2Model f x σ 0) :
    σ / 6 * ‖s‖ ^ 3 < TaylorModel.eval f 2 x 0 - TaylorModel.eval f 2 x s := by
  convert ModelDecrease.penalty_lt_decrement (TaylorModel.eval f 2 x) 2 σ s hs
    using 1
  norm_num

/-- **Lemma 3.3.2.** Actual second-derivative Lipschitz continuity and the
AR2 model/ratio/update rules imply the uniform bound (3.3.14). -/
theorem lemma_3_3_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N : ℕ}
    (h : ar2ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖) :
    ∀ i ≤ N, σ i ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
  fun _ hi => h.parameter_le hf hL hlip hi

/-- **Lemma 3.3.3.** First-order stationarity of the actual cubic model
implies the step-length bound (3.3.15) at every accepted trial. -/
theorem lemma_3_3_3 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₁ : ℝ} {N i : ℕ}
    (h : ar2ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hθ : 0 < θ₁)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hstep : ∀ j < N, x (j + 1) = if η₁ ≤ ρ j then x j + s j else x j)
    (hi : i < N) (hs : η₁ ≤ ρ i)
    (hstat : ‖gradient (ar2Model f (x i) (σ i)) (s i)‖ ≤ θ₁ / 2 * ‖s i‖ ^ 2) :
    2 / (L + θ₁ + max (σ 0) (γ₃ * L / (1 - η₂))) *
      ‖gradient f (x (i + 1))‖ ≤ ‖s i‖ ^ 2 := by
  rw [hstep i hi, ite_eq_left hs, EuclideanSpace.norm_gradient_eq]
  rw [EuclideanSpace.norm_gradient_eq] at hstat
  exact h.step_length_lower hf hL hθ.le hlip hi hstat

/-- The first-order-only branch of AR2. The second tolerance is explicitly
infinite; finite second-order tests remain part of the separately planned full trace. -/
abbrev ar2FirstOrderRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε : ℝ) (ε₂ : WithTop ℝ) (N : ℕ) : Prop :=
  CubicRegularization.FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε ε₂ N

/-- **Lemma 3.3.4.** The actual AR2 trace has at most the successful-trial
budget (3.3.19), with its printed explicit constant. One final successful trial
is counted separately because its endpoint can satisfy the stopping test. -/
theorem lemma_3_3_4 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε L flow : ℝ} {N : ℕ}
    (h : ar2FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε ⊤ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0,
      κS = 6 * (L + θ₁ + max (σ 0) (γ₃ * L / (1 - η₂))) ^ (3 / 2 : ℝ) /
        ((2 : ℝ) ^ (3 / 2 : ℝ) * η₁ * σmin) ∧
      κS = 1 / CubicRegularization.decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ ∧
      ((successfulIterations ρ η₁ N).card : ℝ) ≤ κS * (f (x 0) - flow) /
        ε ^ (3 / 2 : ℝ) + 1 := by
  refine ⟨_, div_pos zero_lt_one (h.decreaseCoefficient_pos hL),
    CubicRegularization.inv_decreaseCoefficient_eq
      (h.trace.updates.pos (Nat.zero_le N)) h.trace.updates.min_pos
      h.trace.updates.eta1_pos hL h.theta_pos, rfl, ?_⟩
  convert h.successful_card_le hf hL hlip hlow using 1
  · rfl
  · ring

/-- **Theorem 3.3.5.** First-order AR2 terminates within the stated function,
gradient and Hessian evaluation budgets. Function calls are initial plus trials;
derivative calls are initial plus accepted trials. The four explicit positive
constants are independent of the requested accuracy. -/
theorem theorem_3_3_5 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖gradient f (x i)‖) →
      ar2FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε ⊤ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = 6 * (L + θ₁ + max (σ 0) (γ₃ * L / (1 - η₂))) ^ (3 / 2 : ℝ) /
        ((2 : ℝ) ^ (3 / 2 : ℝ) * η₁ * σmin) ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂ + 1 ∧
      ∃ K, ‖gradient f (x K)‖ ≤ ε ∧
        ar2FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε ⊤ K ∧
        ((K + 1 : ℕ) : ℝ) ≤ κA * (f (x 0) - flow) / ε ^ (3 / 2 : ℝ) + κC ∧
        (((successfulIterations ρ η₁ K).card + 1 : ℕ) : ℝ) ≤
          κS * (f (x 0) - flow) / ε ^ (3 / 2 : ℝ) + 2 ∧
        (((successfulIterations ρ η₁ K).card + 1 : ℕ) : ℝ) ≤
          κS * (f (x 0) - flow) / ε ^ (3 / 2 : ℝ) + 2 := by
  have hprefix' : ∀ N, (∀ i < N, ε < ‖fderiv ℝ f (x i)‖) →
      ar2FirstOrderRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε ⊤ N := by
    intro N hN
    exact hprefix N (fun i hi => by simpa only [EuclideanSpace.norm_gradient_eq] using hN i hi)
  obtain ⟨K, hstop, hK⟩ := CubicRegularization.exists_firstOrder_termination
    hprefix' hf hL hlip hlow
  obtain ⟨κS, hSpos, hSeq, hSinv, hScount⟩ := lemma_3_3_4 hK hf hL hlip hlow
  let A := 1 + |Real.log γ₁| / Real.log γ₂
  let C := Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
  have hlog := Real.log_pos hK.trace.updates.one_lt_gamma2
  have hA : 0 < A := by dsimp [A]; positivity
  have hσ₀ := hK.trace.updates.pos (Nat.zero_le K)
  have hratio : 1 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0 := by
    apply (le_div_iff₀ hσ₀).mpr
    simpa only [one_mul] using le_max_left (σ 0) (γ₃ * L / (1 - η₂))
  have hC : 0 ≤ C := div_nonneg (Real.log_nonneg hratio) hlog.le
  have hstop' : ‖gradient f (x K)‖ ≤ ε := by
    simpa only [EuclideanSpace.norm_gradient_eq] using hstop
  have hderivs : (((successfulIterations ρ η₁ K).card + 1 : ℕ) : ℝ) ≤
      κS * (f (x 0) - flow) / ε ^ (3 / 2 : ℝ) + 2 := by
    push_cast
    linarith
  refine ⟨κS, hSpos, κS * A, mul_pos hSpos hA, A + C + 1, by positivity,
    hSeq, rfl, rfl, K, hstop', hK, ?_, hderivs, hderivs⟩
  have hb := hK.iterations_le hf hL hlip hlow
  push_cast
  calc
    (K : ℝ) + 1 ≤ ((f (x 0) - flow) /
        (CubicRegularization.decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ *
          ε ^ (3 / 2 : ℝ)) + 1) * A + C + 1 := add_le_add hb le_rfl
    _ = _ := by rw [hSinv]; ring

end CartisGouldToint
