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
    (hp : 3 ≤ p) (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
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
    exact h.step_lower_second hp hf hLp hθ₂.le hlip hi hs (hsecond hε) hu
  · intro hε v hv
    exact ⟨h.step_lower_third hp hf hLp hθ₃.le hlip hi hs (hthird hε) hv,
      h.small_curvature_le hp hf hLp.le hlip hi hs hv⟩

/-- **Lemma 4.1.4.** All three objective decrease bounds (4.1.31)–(4.1.36),
with the printed factorial coefficients and real fractional exponents. The
accepted decrease follows from the actual objective ratio and parameter floor. -/
theorem lemma_4_1_4 {n p N i : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₁ θ₂ θ₃ : ℝ} {ε₂ ε₃ : WithTop ℝ}
    (h : arpModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 3 ≤ p) (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
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
    exact h.decrease_second hp hf hLp hθ₂.le hlip hi hs (hsecond hε) hu
  · intro hε v hv
    exact h.decrease_third hp hf hLp hθ₃.le hlip hi hs (hthird hε) hv

end CartisGouldToint
