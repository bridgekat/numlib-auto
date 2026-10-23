import Numlib.Optimization.Regularization.HighOrder.Sharpness.Witness
import Numlib.Optimization.Regularization.HighOrder.Complexity
import Numlib.Optimization.Regularization.HighOrder.EmptyDirections
import Numlib.Analysis.Calculus.Gradient
import Numlib.Optimization.Regularization.HighOrder.Step
import Numlib.Optimization.Regularization.HighOrder.Parameter
import Numlib.Analysis.Calculus.TaylorModel

/-!
# Taylor models for high-order regularization

The Taylor polynomial used in Chapter 4 and throughout the later high-order algorithms is the
finite sum of iterated Fréchet derivatives with their factorial normalization.
-/

namespace CartisGouldToint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The degree-`p` Taylor model `T_{f,p}(x,s)` of equation (4.1.1). The vector-valued form also
provides the component Taylor models used in composite optimization. -/
noncomputable def taylorModel (f : E → F) (p : ℕ) (x s : E) : F :=
  TaylorModel.eval f p x s

@[simp] theorem taylorModel_zero (f : E → F) (p : ℕ) (x : E) :
    taylorModel f p x 0 = f x := TaylorModel.eval_zero _ _ _

/-- The decrease in the Taylor model relative to zero displacement. -/
noncomputable def taylorDecrement (f : E → ℝ) (p : ℕ) (x s : E) : ℝ :=
  taylorModel f p x 0 - taylorModel f p x s

end CartisGouldToint

namespace CartisGouldToint
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual regularized Taylor model of equation (4.1.2). -/
noncomputable abbrev arpModel (f : E → ℝ) (p : ℕ) (x : E) (σ : ℝ) (s : E) : ℝ :=
  HighOrderRegularization.model f p x σ s

/-- The strict model-improvement, actual objective-ratio, iterate-update and
three-case parameter-update components of ARp. Stationarity and stopping tests
are separate components of the full method. -/
abbrev arpModelTrace (f : E → ℝ) (p : ℕ) (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
  HighOrderRegularization.ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N

/-- **Lemma 4.1.1 (decrease of the Taylor model).** Nonincrease of the actual
regularized model gives the factorial-normalized prediction bound (4.1.18).
The algebraic conclusion needs neither smoothness nor positive regularization. -/
theorem lemma_4_1_1 (f : E → ℝ) (p : ℕ) (x s : E) (σ : ℝ)
    (hs : arpModel f p x σ s ≤ arpModel f p x σ 0) :
    σ / (p + 1).factorial * ‖s‖ ^ (p + 1) ≤ taylorDecrement f p x s :=
  HighOrderRegularization.penalty_le_decrement f p x s σ hs

/-- **Lemma 4.1.2 (upper bound on regularization).** The sharp actual Taylor
remainder and the operational three-case parameter updates imply (4.1.19),
including initialization and the endpoint of every finite execution prefix.
The parameter bound is derived; it is not an invariant assumed by the trace. -/
theorem lemma_4_1_2 {f : E → ℝ} {p N : ℕ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ}
    (h : arpModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖) :
    ∀ i ≤ N, σ i ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
  fun _ hi => h.parameter_le hf (zero_le_one.trans hL) hlip hi

end CartisGouldToint

namespace CartisGouldToint
open HighOrderRegularization

/-- The actual small-curvature directions of the preceding ARp model, as in (4.1.14). -/
abbrev arpSmallModelDirections {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (p : ℕ) (x s : E) (σ θ₂ : ℝ) : Set E :=
  smallModelDirections f p x s σ θ₂

/-- **Lemma 4.1.3.** All four successful-step bounds (4.1.20)–(4.1.23).
The higher-order clauses apply when their model tests are enabled. The curvature
certificate uses the least eigenvalue of the actual endpoint Hessian, and the
third-order clause uses precisely the model directions (4.1.14). -/
theorem lemma_4_1_3 {n p N i : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₁ θ₂ θ₃ : ℝ} {ε₂ ε₃ : WithTop ℝ}
    (h : arpModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp₂ : ε₂ ≠ ⊤ → 2 ≤ p) (hp₃ : ε₃ ≠ ⊤ → 3 ≤ p)
    (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hs : η₁ ≤ ρ i)
    (hfirst : ‖fderiv ℝ (arpModel f p (x i) (σ i)) (s i)‖ ≤ θ₁ * ‖s i‖ ^ p)
    (hsecond : ε₂ ≠ ⊤ → ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
      -θ₂ * ‖s i‖ ^ (p - 1) ≤
        iteratedFDeriv ℝ 2 (arpModel f p (x i) (σ i)) (s i) (fun _ => v))
    (hthird : ε₃ ≠ ⊤ → ∀ v ∈ arpSmallModelDirections f p (x i) (s i) (σ i) θ₂,
      |iteratedFDeriv ℝ 3 (arpModel f p (x i) (σ i)) (s i) (fun _ => v)| ≤
        θ₃ * ‖s i‖ ^ (p - 2)) :
    let σmax := max (σ 0) (γ₃ * L / (1 - η₂))
    p.factorial / (L + σmax + θ₁ * p.factorial) * ‖gradient f (x (i + 1))‖ ≤
      ‖s i‖ ^ p ∧
    (ε₂ ≠ ⊤ → ∀ (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)),
      SecondOrderTrustRegion.IsLeastEigenpair f (x (i + 1)) μ u →
      (p - 1).factorial / (L + σmax + θ₂ * (p - 1).factorial) * max 0 (-μ) ≤
        ‖s i‖ ^ (p - 1)) ∧
    (ε₃ ≠ ⊤ → ∀ v ∈ arpSmallModelDirections f p (x i) (s i) (σ i) θ₂,
      (p - 2).factorial / (L + σmax + θ₃ * (p - 2).factorial) *
        |iteratedFDeriv ℝ 3 f (x (i + 1)) (fun _ => v)| ≤ ‖s i‖ ^ (p - 2) ∧
      |iteratedFDeriv ℝ 2 f (x (i + 1)) (fun _ => v)| ≤
        1 / ((p - 1).factorial / (L + σmax + θ₂ * (p - 1).factorial)) *
          ‖s i‖ ^ (p - 1)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  refine ⟨?_, ?_, ?_⟩
  · simpa only [EuclideanSpace.norm_gradient_eq, stepConstant] using
      h.step_lower_first hf hLp hθ₁.le hlip hi hs hfirst
  · intro hε μ u hu
    exact h.step_lower_second (hp₂ hε) hf hLp hθ₂.le hlip hi hs (hsecond hε) hu
  · intro hε v hv
    exact ⟨h.step_lower_third (hp₃ hε) hf hLp hθ₃.le hlip hi hs (hthird hε) hv,
      h.small_curvature_le (by have := hp₃ hε; omega) hf hLp.le hlip hi hs hv⟩

/-- **Lemma 4.1.4.** All three objective decrease bounds (4.1.31)–(4.1.36),
with the printed factorial coefficients and real fractional exponents. The
accepted decrease follows from the actual objective ratio and parameter floor. -/
theorem lemma_4_1_4 {n p N i : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₁ θ₂ θ₃ : ℝ} {ε₂ ε₃ : WithTop ℝ}
    (h : arpModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp₂ : ε₂ ≠ ⊤ → 2 ≤ p) (hp₃ : ε₃ ≠ ⊤ → 3 ≤ p)
    (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hθ₃ : 0 < θ₃)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hs : η₁ ≤ ρ i)
    (hfirst : ‖fderiv ℝ (arpModel f p (x i) (σ i)) (s i)‖ ≤ θ₁ * ‖s i‖ ^ p)
    (hsecond : ε₂ ≠ ⊤ → ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
      -θ₂ * ‖s i‖ ^ (p - 1) ≤
        iteratedFDeriv ℝ 2 (arpModel f p (x i) (σ i)) (s i) (fun _ => v))
    (hthird : ε₃ ≠ ⊤ → ∀ v ∈ arpSmallModelDirections f p (x i) (s i) (σ i) θ₂,
      |iteratedFDeriv ℝ 3 (arpModel f p (x i) (σ i)) (s i) (fun _ => v)| ≤
        θ₃ * ‖s i‖ ^ (p - 2)) :
    let σmax := max (σ 0) (γ₃ * L / (1 - η₂))
    let κ₁ := η₁ * σmin / (p + 1).factorial *
      (p.factorial / (L + σmax + θ₁ * p.factorial)) ^ (((p + 1 : ℕ) : ℝ) / p)
    let κ₂ := η₁ * σmin / (p + 1).factorial *
      ((p - 1).factorial / (L + σmax + θ₂ * (p - 1).factorial)) ^
        (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))
    let κ₃ := η₁ * σmin / (p + 1).factorial *
      ((p - 2).factorial / (L + σmax + θ₃ * (p - 2).factorial)) ^
        (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ))
    κ₁ * ‖gradient f (x (i + 1))‖ ^ (((p + 1 : ℕ) : ℝ) / p) ≤
      f (x i) - f (x (i + 1)) ∧
    (ε₂ ≠ ⊤ → ∀ (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)),
      SecondOrderTrustRegion.IsLeastEigenpair f (x (i + 1)) μ u →
      κ₂ * (max 0 (-μ)) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ≤
        f (x i) - f (x (i + 1))) ∧
    (ε₃ ≠ ⊤ → ∀ v ∈ arpSmallModelDirections f p (x i) (s i) (σ i) θ₂,
      κ₃ * |iteratedFDeriv ℝ 3 f (x (i + 1)) (fun _ => v)| ^
        (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) ≤ f (x i) - f (x (i + 1))) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  refine ⟨?_, ?_, ?_⟩
  · simpa only [EuclideanSpace.norm_gradient_eq, decreaseConstant, stepConstant] using
      h.decrease_first hf hLp hθ₁.le hlip hi hs hfirst
  · intro hε μ u hu
    exact h.decrease_second (hp₂ hε) hf hLp hθ₂.le hlip hi hs (hsecond hε) hu
  · intro hε v hv
    exact h.decrease_third (hp₃ hε) hf hLp hθ₃.le hlip hi hs (hthird hε) hv

end CartisGouldToint

namespace CartisGouldToint
open HighOrderRegularization HighOrderRegularization.EmptyDirections
/-- The literal nonempty-direction guard in Algorithm 4.1.1 can prevent
termination at a stationary point after a legal accepted trial. Thus Theorem
4.1.5 needs a repaired stopping test. Removing the guard allows the empty set
in the theorem's stated terminal conclusion `Mε ⊆ Zε`.
The objective is bounded and C³ with globally Lipschitz D³; all settings and
actual model stationarity tests are legal. -/
theorem theorem_4_1_5_nonempty_guard_counterexample :
    ∃ (f : ℝ → ℝ) (L B : ℝ), 1 ≤ L ∧ 0 < B ∧ ContDiff ℝ 3 f ∧
      (∀ x, |f x| ≤ B) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 3 f x - iteratedFDeriv ℝ 3 f y‖ ≤ L * ‖x - y‖) ∧
      ModelTrace f 3 point (fun _ => 1) (fun _ => 12) (fun _ => 2)
        (1 / 4) (3 / 4) (1 / 2) 2 3 12 1 ∧
      StepConditions f 3 0 1 12 1 1 1 ∧
      smallModelDirections f 3 0 1 12 1 = ∅ ∧
      (∀ M : Set ℝ, ¬ literalStop f 0 M 1 1 1) ∧
      ¬ literalStop f 1 (smallModelDirections f 3 0 1 12 1) 1 1 1 ∧
      (∀ j ≤ 3, iteratedDeriv j f 1 = 0) ∧
      SecondOrderTrustRegion.IsLeastEigenpair f 1 0 1 ∧
      (∀ σ : ℝ, 0 ≤ σ → ¬ ∃ s : ℝ, model f 3 1 σ s < model f 3 1 σ 0) :=
  exists_stuck_execution

end CartisGouldToint

namespace CartisGouldToint
open HighOrderRegularization HighOrderRegularization.Sharpness

/-- **Theorem 4.1.6.** All three sharp evaluation lower bounds, with uniform
objective and highest-derivative Lipschitz budgets chosen before the accuracies.
The actual algorithm settings are fixed: `σ=p!/(p²+1)`, `σmin=σ`, unit model
termination tolerances and legal constant update settings. First-order models
allow every `p≥1`, second-order models every `p≥2`, and third-order models `p≥3`.

Each witness follows genuine model derivative tests, objective-based ratios and
parameter updates, and its actual evaluation counters are `N+1`, where `N` is at
least the printed inverse-accuracy rate or maximum of rates. The third-order
terminal derivative bound holds in every unit direction, hence on `Zε`. Its
terminal inherited set is nonempty; failure of the weaker repaired stopping test
before `N` and the terminal nonempty guard make it a literal algorithm execution
as well. The construction bounds the true final jet change in the Hermite
residuals rather than treating that change as zero. -/
theorem theorem_4_1_6 (p : ℕ) :
    (1 ≤ p →
      ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ f : ℝ → ℝ,
          let N := length p 1 ε
          let x := iterate p 1 ε
          ContDiff ℝ p f ∧ (∀ z, |f z| ≤ B) ∧
          (∀ z w, ‖iteratedFDeriv ℝ p f z - iteratedFDeriv ℝ p f w‖ ≤
            L * ‖z - w‖) ∧
          FirstOrderRun f p x (fun _ => step p 1 ε)
            (fun _ => parameter p) (fun _ => 1)
            (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 ε ⊤ ⊤ N ∧
          ‖fderiv ℝ f (x N)‖ = ε ∧
          rate p 1 ε ≤ (N : ℝ) ∧
          functionEvaluations N = N + 1 ∧
          derivativeEvaluations (fun _ => 1) (1 / 4) N = N + 1) ∧
    (2 ≤ p →
      ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
        ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < ε₂ → ε₂ ≤ 1 →
        ∃ r : ℕ, 0 < r ∧ r ≤ 2 ∧ ∃ f : ℝ → ℝ,
          let ε := selectedAccuracy r ε₁ ε₂ 1
          let N := length p r ε
          let x := iterate p r ε
          ContDiff ℝ p f ∧ (∀ z, |f z| ≤ B) ∧
          (∀ z w, ‖iteratedFDeriv ℝ p f z - iteratedFDeriv ℝ p f w‖ ≤
            L * ‖z - w‖) ∧
          SecondOrderRun f p x (fun _ => step p r ε) (fun _ => 1)
            (fun k => iteratedDeriv 2 f (x k)) (fun _ => parameter p) (fun _ => 1)
            (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 1 ε₁ ε₂ ⊤ N ∧
          ‖fderiv ℝ f (x N)‖ ≤ ε₁ ∧ -ε₂ ≤ iteratedDeriv 2 f (x N) ∧
          max (rate p 1 ε₁) (rate p 2 ε₂) ≤ (N : ℝ) ∧
          functionEvaluations N = N + 1 ∧
          derivativeEvaluations (fun _ => 1) (1 / 4) N = N + 1) ∧
    (3 ≤ p →
      ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
        ∀ ε₁ ε₂ ε₃ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < ε₂ → ε₂ ≤ 1 →
          0 < ε₃ → ε₃ ≤ 1 →
        ∃ r : ℕ, 0 < r ∧ r ≤ 3 ∧ ∃ f : ℝ → ℝ,
          let ε := selectedAccuracy r ε₁ ε₂ ε₃
          let N := length p r ε
          let x := iterate p r ε
          let M := directions f p r ε ε₂
          ContDiff ℝ p f ∧ (∀ z, |f z| ≤ B) ∧
          (∀ z w, ‖iteratedFDeriv ℝ p f z - iteratedFDeriv ℝ p f w‖ ≤
            L * ‖z - w‖) ∧
          FiniteRun f p x (fun _ => step p r ε) (fun _ => 1)
            (fun k => iteratedDeriv 2 f (x k)) (fun _ => parameter p) (fun _ => 1) M
            (1 / 4) (3 / 4) (1 / 2) 2 3 (parameter p) 1 1 1 ε₁ ε₂ ε₃ N ∧
          finiteStop f (x N) (iteratedDeriv 2 f (x N)) (M N) ε₁ ε₂ ε₃ ∧
          (M N).Nonempty ∧
          HighOrderRegularization.EmptyDirections.literalStop f (x N) (M N) ε₁ ε₂ ε₃ ∧
          (∀ k < N, ¬HighOrderRegularization.EmptyDirections.literalStop
            f (x k) (M k) ε₁ ε₂ ε₃) ∧
          ‖fderiv ℝ f (x N)‖ ≤ ε₁ ∧ -ε₂ ≤ iteratedDeriv 2 f (x N) ∧
          (∀ v : ℝ, ‖v‖ = 1 →
            |iteratedFDeriv ℝ 2 f (x N) (fun _ => v)| ≤ ε₂ ∧
            |iteratedFDeriv ℝ 3 f (x N) (fun _ => v)| ≤ ε₃) ∧
          max (max (rate p 1 ε₁) (rate p 2 ε₂)) (rate p 3 ε₃) ≤ (N : ℝ) ∧
          functionEvaluations N = N + 1 ∧
          derivativeEvaluations (fun _ => 1) (1 / 4) N = N + 1) :=
  ⟨fun hp => exists_first_order_witness hp,
    fun hp => exists_second_order_witness hp,
    fun hp => exists_third_order_witness hp⟩

end CartisGouldToint

namespace CartisGouldToint
open HighOrderRegularization

/-- First-order ARp with both higher stopping tests explicitly disabled. -/
abbrev arpFirstOrderRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε₁ : ℝ)
    (ε₂ ε₃ : WithTop ℝ) (N : ℕ) : Prop :=
  FirstOrderRun f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε₁ ε₂ ε₃ N

/-- Finite-second-order ARp with its third stopping test explicitly disabled. -/
abbrev arpSecondOrderRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x s u : ℕ → EuclideanSpace ℝ (Fin n)) (μ σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ : ℝ)
    (ε₃ : WithTop ℝ) (N : ℕ) : Prop :=
  SecondOrderRun f p x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin
    θ₁ θ₂ ε₁ ε₂ ε₃ N

/-- Full finite-third-order ARp after removing only the false nonempty-set guard.
The original model, acceptance, parameter and model-direction updates
remain primitive fields. -/
abbrev arpFiniteRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x s u : ℕ → EuclideanSpace ℝ (Fin n)) (μ σ ρ : ℕ → ℝ)
    (M : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ : ℝ)
    (N : ℕ) : Prop :=
  FiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
    θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N

/-- The actual repaired third-order stopping test; the strict-Hessian branch is retained. -/
abbrev arpFiniteStop {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (M : Set (EuclideanSpace ℝ (Fin n)))
    (ε₁ ε₂ ε₃ : ℝ) : Prop := finiteStop f x μ M ε₁ ε₂ ε₃

/-- **Theorem 4.1.5, corrected stopping rule.** Removing the nonempty-direction
condition in Step 1 yields the full source complexity bounds (4.1.38), including
all derivative orders, the printed constants (4.1.45)–(4.1.46), and the first
actual stopping point. Constants precede all accuracy requests and executions.
The strict-Hessian branch returns the empty direction set; otherwise the returned
set is precisely the algorithm's inherited model directions. The literal source
version is disproved by `theorem_4_1_5_nonempty_guard_counterexample`. -/
theorem theorem_4_1_5_corrected {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {σinit σmin η₁ η₂ γ₁ γ₂ γ₃ L θ₁ θ₂ θ₃ flow : ℝ}
    (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) (hσ : 0 < σinit) (hmin : 0 < σmin) (hη : 0 < η₁)
    (hγ₂ : 1 < γ₂) (hθ₁ : 0 < θ₁) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = successfulIterationConstant p σinit σmin η₁ η₂ γ₃ L θ₁ θ₂ θ₃ ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = |Real.log γ₁| / Real.log γ₂ +
        Real.log (max σinit (γ₃ * L / (1 - η₂)) / σinit) / Real.log γ₂ + 2 ∧
      ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ 1 →
      ∀ ε₃ : ℝ, 0 < ε₃ → ε₃ ≤ 1 →
      ∀ x s u : ℕ → EuclideanSpace ℝ (Fin n), ∀ μ σ ρ : ℕ → ℝ,
      ∀ M : ℕ → Set (EuclideanSpace ℝ (Fin n)), σ 0 = σinit →
        (∀ N, (∀ i < N, ¬arpFiniteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃) →
          arpFiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
            θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ N) →
        ∃ K, arpFiniteStop f (x K) (μ K) (M K) ε₁ ε₂ ε₃ ∧
          arpFiniteRun f p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
            θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ K ∧
          (∀ i < K, ¬arpFiniteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃) ∧
          ‖gradient f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K ∧
          returnedDirections (μ K) ε₂ (M K) ⊆
            {v | ‖v‖ = 1 ∧ |iteratedFDeriv ℝ 2 f (x K) (fun _ => v)| ≤ ε₂} ∧
          (∀ v ∈ returnedDirections (μ K) ε₂ (M K),
            |iteratedFDeriv ℝ 3 f (x K) (fun _ => v)| ≤ ε₃) ∧
          (functionEvaluations K : ℝ) ≤
            κA * (f (x 0) - flow) / finiteAccuracyFactor p ε₁ ε₂ ε₃ + κC ∧
          (derivativeEvaluations ρ η₁ K : ℝ) ≤
            κS * (f (x 0) - flow) / finiteAccuracyFactor p ε₁ ε₂ ε₃ + 2 := by
  obtain ⟨κS,hS,κA,hA,κC,hC,hSeq,hAeq,hCeq,hRun⟩ := exists_uniform_finite_complexity p
    hf (zero_lt_one.trans_le hL) hlip hlow hσ hmin hη hγ₂ hθ₁
  refine ⟨κS,hS,κA,hA,κC,hC,hSeq,hAeq,hCeq,?_⟩
  intro ε₁ _ _ ε₂ _ _ ε₃ _ _ x s u μ σ ρ M hσ0 hprefix
  obtain ⟨K,hstop,hK,hfirst,hg,hμ,hM,hthird,hF,hD⟩ :=
    hRun ε₁ ε₂ ε₃ x s u μ σ ρ M hσ0 hprefix
  exact ⟨K,hstop,hK,hfirst,by simpa only [EuclideanSpace.norm_gradient_eq] using hg,
    hμ,hM,hthird,hF,hD⟩

end CartisGouldToint
