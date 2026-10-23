import Numlib.Optimization.Sharpness.SecondOrder
import Numlib.Optimization.Regularization.Cubic.Finite
import Numlib.Optimization.Regularization.Cubic.SecondOrder
import Numlib.Optimization.Regularization.Cubic.ModifiedGradient
import Numlib.Optimization.Regularization.Cubic.FirstOrder
import Numlib.Optimization.Regularization.Cubic.Sharpness
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
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) :
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

/-- **Theorem 3.3.6.** A one-dimensional, twice-smooth nonnegative objective
can force `⌈ε⁻³ᐟ²⌉` genuine first-order AR2 iterations. The Hessian Lipschitz
constant and initial objective gap are uniform in `ε`. Every trial is accepted,
so objective calls and both derivative-call counts meet the same lower bound.
The integer ceiling makes the source's suppressed rounding explicit. -/
theorem theorem_3_3_6 {η₁ η₂ γ₁ γ₂ γ₃ θ₁ σmin : ℝ}
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃)
    (hθ : 0 < θ₁) (hσ : 0 < σmin) :
    ∃ L ≥ 1, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : ℝ → ℝ) (x : ℕ → ℝ) (t : ℝ) (ρ : ℕ → ℝ) (N : ℕ),
        ContDiff ℝ 2 f ∧ (∀ z, 0 ≤ f z) ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖) ∧
        f (x 0) ≤ 8 / Real.sqrt σmin ∧
        N = ⌈1 / ε ^ (3 / 2 : ℝ)⌉₊ ∧
        CubicRegularization.FirstOrderRun f x (fun _ => t) (fun _ => σmin) ρ
          η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε ⊤ N ∧
        (∀ i < N, η₂ ≤ ρ i) ∧ ‖gradient f (x N)‖ = ε ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ N ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ (((successfulIterations ρ η₁ N).card + 1 : ℕ) : ℝ) ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ (((successfulIterations ρ η₁ N).card + 1 : ℕ) : ℝ) := by
  obtain ⟨L, hL, h⟩ := CubicRegularization.exists_slow_firstOrderRun
    hη₁ hη hη₂ hγ₁ hγ₁1 hγ₂ hγ₃ hθ hσ
  refine ⟨L, hL, ?_⟩
  intro ε hε hε1
  obtain ⟨f, x, t, ρ, N, hf, hlow, hlip, hgap, hN, hrun, hvery, hstop,
    hcount, hfun, hderiv⟩ := h ε hε hε1
  refine ⟨f, x, t, ρ, N, hf, hlow, hlip, hgap, hN, hrun, hvery, ?_,
    hcount, hfun, hderiv, hderiv⟩
  change ‖(InnerProductSpace.toDual ℝ ℝ).symm (fderiv ℝ f (x N))‖ = ε
  rwa [LinearIsometryEquiv.norm_map]

/-- **Lemma 3.3.7.** The modified AR2 test (3.3.23), imposed on the actual
quadratic Taylor polynomial, yields (3.3.24) at every accepted trial. The
regularization bound is derived from the actual model/ratio/update trace. -/
theorem lemma_3_3_7 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₁ : ℝ} {N i : ℕ}
    (h : ar2ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hθ : 1 < θ₁)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hstep : ∀ j < N, x (j + 1) = if η₁ ≤ ρ j then x j + s j else x j)
    (hi : i < N) (hs : η₁ ≤ ρ i)
    (hstat : ‖gradient (TaylorModel.eval f 2 (x i)) (s i)‖ ≤
      θ₁ * σ i / 2 * ‖s i‖ ^ 2) :
    2 / (L + θ₁ * max (σ 0) (γ₃ * L / (1 - η₂))) *
      ‖gradient f (x (i + 1))‖ ≤ ‖s i‖ ^ 2 := by
  rw [hstep i hi, ite_eq_left hs, EuclideanSpace.norm_gradient_eq]
  rw [EuclideanSpace.norm_gradient_eq] at hstat
  exact h.step_length_lower_of_modified hf hL (by linarith) hlip hi hstat

/-- The finite-second-order AR2 model test (3.3.6) on the actual cubic-model
Hessian, expressed equivalently on every unit direction. -/
abbrev ar2SecondOrderStationary {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : E → ℝ) (x s : E) (σ θ₂ : ℝ) : Prop :=
  CubicRegularization.SecondOrderStationary f x s σ θ₂

/-- **Lemma 3.3.8.** The actual model curvature test and the accepted-step
rule imply (3.3.25) for the least actual Hessian eigenvalue at the next iterate.
The proof differentiates the cubic penalty genuinely, including at a zero step.
The source's unnumbered Hessian formula after (3.3.2) omits a factor `1/2`;
the corrected derivative gives precisely the printed bound (3.3.25). -/
theorem lemma_3_3_8 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ₂ μ : ℝ} {N i : ℕ}
    (h : ar2ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hθ : 0 < θ₂)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hstep : ∀ j < N, x (j + 1) = if η₁ ≤ ρ j then x j + s j else x j)
    (hi : i < N) (hs : η₁ ≤ ρ i)
    (hstat : ar2SecondOrderStationary f (x i) (s i) (σ i) θ₂)
    (u : EuclideanSpace ℝ (Fin n))
    (hleast : SecondOrderTrustRegion.IsLeastEigenpair f (x (i + 1)) μ u) (hμ : μ < 0) :
    |μ| / (L + θ₂ + max (σ 0) (γ₃ * L / (1 - η₂))) ≤ ‖s i‖ := by
  have he := hleast.eigenvector
  rw [hstep i hi, ite_eq_left hs] at he
  exact h.step_length_lower_secondOrder hf hL hθ hlip hi hstat u hleast.unit he hμ

/-- The full operational AR2 branch with both finite stopping tolerances. -/
abbrev ar2FiniteRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s u : ℕ → EuclideanSpace ℝ (Fin n)) (μ σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ : ℝ) (N : ℕ) : Prop :=
  CubicRegularization.FiniteRun f x s u μ σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N

/-- **Theorem 3.3.9.** Finite-second-order AR2 reaches both actual stopping
thresholds within the function, gradient and Hessian bounds (3.3.29)–(3.3.30),
with the printed accuracy-independent constants. The display (3.3.30) prints
`+1` and later `+2`; its proof bounds accepted trials by the objective budget
plus one, and initialization requires the corrected derivative allowance `+2`.
The listed but unused source constant `κE` is normalized to one. The constant
`κF` is written in the equivalent form using `σmax/σ₀`. -/
theorem theorem_3_3_9 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s u : ℕ → EuclideanSpace ℝ (Fin n)} {μ σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂) →
      ar2FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κT > 0, ∃ κD > 0, ∃ κE > 0, ∃ κF > 0,
      κT = 6 * (L + max 1 (max θ₁ θ₂) + max (σ 0) (γ₃ * L / (1 - η₂))) ^ 3 /
        (η₁ * σmin) ∧
      κD = κT * (1 + |Real.log γ₁| / Real.log γ₂) ∧ κE = 1 ∧
      κF = (1 + |Real.log γ₁| / Real.log γ₂) +
        Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂ + 1 ∧
      ∃ K, ‖gradient f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K ∧
        ar2FiniteRun f x s u μ σ ρ
          η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ K ∧
        (∀ i < K, ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε₂) ∧
        (CubicRegularization.functionEvaluations K : ℝ) ≤
          κD * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (ε₂ ^ 3) + κF ∧
        (CubicRegularization.gradientEvaluations ρ η₁ K : ℝ) ≤
          κT * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (ε₂ ^ 3) + 2 ∧
        (CubicRegularization.hessianEvaluations ρ η₁ K : ℝ) ≤
          κT * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (ε₂ ^ 3) + 2 := by
  have hprefix' : ∀ N, (∀ i < N, ε₁ < ‖fderiv ℝ f (x i)‖ ∨ μ i < -ε₂) →
      ar2FiniteRun f x s u μ σ ρ
        η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N := by
    intro N hN
    exact hprefix N (fun i hi => by
      simpa only [EuclideanSpace.norm_gradient_eq] using hN i hi)
  obtain ⟨K, hg, hμ, hK, hfirst⟩ := CubicRegularization.exists_finite_termination
    hprefix' hf hL hlip hlow
  let c := CubicRegularization.finiteDecreaseCoefficient
    (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂
  let A := 1 + |Real.log γ₁| / Real.log γ₂
  let C := Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
  have hc := hK.finiteDecreaseCoefficient_pos hL
  have hlog := Real.log_pos hK.trace.updates.one_lt_gamma2
  have hA : 0 < A := by dsimp [A]; positivity
  have hσ₀ := hK.trace.updates.pos (Nat.zero_le K)
  have hratio : 1 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0 := by
    apply (le_div_iff₀ hσ₀).mpr
    simpa only [one_mul] using le_max_left (σ 0) (γ₃ * L / (1 - η₂))
  have hC : 0 ≤ C := div_nonneg (Real.log_nonneg hratio) hlog.le
  have hD :
      (((EvaluationComplexity.successfulIterations
        {i | η₁ ≤ ρ i} K).card : ℕ) : ℝ) + 1 ≤
      (1 / c) * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (ε₂ ^ 3) + 2 := by
    have hh := hK.successful_card_le hf hL hlip hlow
    convert add_le_add_right hh 1 using 1 <;>
      (try dsimp [c, CubicRegularization.finiteAccuracyFactor]) <;> ring
  refine ⟨1 / c, div_pos zero_lt_one hc, (1 / c) * A,
    mul_pos (div_pos zero_lt_one hc) hA, 1, zero_lt_one, A + C + 1, by positivity,
    hK.inv_finiteDecreaseCoefficient_eq hL, rfl, rfl, rfl, K, ?_, hμ, hK, ?_, ?_, ?_, ?_⟩
  · simpa only [EuclideanSpace.norm_gradient_eq] using hg
  · intro i hi
    simpa only [EuclideanSpace.norm_gradient_eq] using hfirst i hi
  · have hh := hK.iterations_le hf hL hlip hlow
    simp only [CubicRegularization.functionEvaluations, Nat.cast_add, Nat.cast_one]
    convert add_le_add_right hh 1 using 1 <;>
      (try dsimp [c, A, C, CubicRegularization.finiteAccuracyFactor]) <;> ring
  · simpa only [CubicRegularization.gradientEvaluations,
      CubicRegularization.derivativeEvaluations, Nat.cast_add, Nat.cast_one] using hD
  · simpa only [CubicRegularization.hessianEvaluations,
      CubicRegularization.derivativeEvaluations, Nat.cast_add, Nat.cast_one] using hD

/-- **Theorem 3.3.10.** Genuine finite-second-order AR2 can require the maximum
of the first- and second-accuracy lower bounds in iterations and in every initialized
objective, gradient and Hessian evaluation counter. Global smoothness and objective-gap
constants precede both accuracies. The algorithm settings and the initial/minimum
regularization parameter `4` are fixed. The actual smooth plateau supplies the
first-accuracy branch, and a global Hermite curvature interpolant supplies the other.
Both actual stopping tests hold first at the displayed terminal iterate. -/
theorem theorem_3_3_10 :
    ∃ B > 0,
    ∃ L' ≥ 1, ∃ G > 0,
      ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ 1 →
      ∃ (f : ℝ → ℝ) (x : ℕ → ℝ) (t : ℝ) (ρ μ : ℕ → ℝ) (N : ℕ),
        x 0 = 0 ∧ ContDiff ℝ 2 f ∧ (∀ z, -B ≤ f z) ∧ f 0 - (-B) ≤ G ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤
          L' * ‖z - w‖) ∧
        CubicRegularization.FiniteRun f x (fun _ => t) (fun _ => 1) μ
          (fun _ => 4) ρ (1/4) (1/2) (1/2) 2 3 4 1 1 ε₁ ε₂ N ∧
        (∀ i < N, ¬(‖fderiv ℝ f (x i)‖ ≤ ε₁ ∧ -ε₂ ≤ μ i)) ∧
        ‖fderiv ℝ f (x N)‖ ≤ ε₁ ∧ -ε₂ ≤ μ N ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤ (N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.functionEvaluations N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.gradientEvaluations ρ (1/4) N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.hessianEvaluations ρ (1/4) N : ℝ) :=
  CurvatureSharpness.exists_slow_cubicRun

end CartisGouldToint
