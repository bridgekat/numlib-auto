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
