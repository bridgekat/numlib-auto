import NumlibSurface.CartisGouldToint.Chapter02.Section03
import Numlib.Optimization.Regularization.FirstOrder
import Numlib.Optimization.Regularization.FirstOrder.Sharpness
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Section 2.4: regularization iteration counts

Lemma 2.4.1 follows from the three-case update (2.4.4) independently of the chosen
objective model. Successful-iteration counts use the preceding section's prefix
convention, with `N` updates from `σ₀` to `σ_N`.
-/

namespace CartisGouldToint

/-- A finite prefix of Algorithm 2.4.1 before termination. The trial step is
`−σ⁻¹∇f`, the global minimizer of its regularized linear model. The trace specifies
the actual gradient, trial objective value, ratio, acceptance and parameter update.
Positivity and complexity bounds are derived from these rules. -/
def ar1Run {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin ε : ℝ) (N : ℕ) : Prop :=
  FirstOrderRegularization.Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N

/-- **Lemma 2.4.1.** An upper bound on the current regularization parameter and
the AR1 update rule control the total updates in terms of successful updates.
Only the exact parameter-update component of AR1 is required. -/
theorem lemma_2_4_1 {σ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin σmax : ℝ} {N : ℕ}
    (h : EvaluationComplexity.RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hmax : σ N ≤ σmax) :
    (N : ℝ) ≤ (successfulIterations ρ η₁ N).card *
        (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (σmax / σ 0) / Real.log γ₂ :=
  EvaluationComplexity.iteration_bound_of_parameter_upper (S := {i | η₁ ≤ ρ i})
    (fun _ hi => h.pos hi) h.gamma1_pos h.gamma1_lt_one h.one_lt_gamma2 hmax
    (fun _ hi hs => h.successful_ge hi hs)
    (fun _ hi hu => h.unsuccessful_ge hi hu)

/-- **Lemma 2.4.2.** Every parameter in an AR1 prefix is at most the maximum in
(2.4.9), with the Lipschitz and update constants fixed independently of `ε`. -/
theorem lemma_2_4_2 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin ε L : ℝ} {N : ℕ}
    (h : ar1Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (_hL1 : 1 ≤ L) :
    ∀ i ≤ N, σ i ≤ max (σ 0) (γ₃ * L / (2 * (1 - η₂))) :=
  fun _ hi => h.parameter_le hL hi

/-- **Lemma 2.4.3.** The number of successful iterations before termination is
bounded by `κˢ (f(x₀) - f_low)/ε²`, with the explicit positive constant from
(2.4.9) and (2.4.11). This statement applies to every nonterminated finite prefix. -/
theorem lemma_2_4_3 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin ε L flow : ℝ} {N : ℕ}
    (h : ar1Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (_hL1 : 1 ≤ L)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, κS = max (σ 0) (γ₃ * L / (2 * (1 - η₂))) / η₁ ∧
      ((successfulIterations ρ η₁ N).card : ℝ) ≤ κS * (f (x 0) - flow) / ε ^ 2 := by
  refine ⟨_, div_pos ?_ h.updates.eta1_pos, rfl, h.successful_card_le hL (hlow _)⟩
  exact (h.updates.pos (Nat.zero_le N)).trans_le (le_max_left _ _)

/-- **Theorem 2.4.4.** AR1 reaches the requested gradient tolerance, with at most
`κA (f(x₀) - f_low)/ε² + κC` function evaluations and
`κS (f(x₀) - f_low)/ε² + 1` gradient evaluations. The constants are given explicitly
by formulas independent of `ε`. Each iteration evaluates one trial objective;
the initial evaluation adds one. Gradients are evaluated initially and at accepted
points. An execution is specified by its consistent valid prefixes up to stopping.
The constants below use the sharper parameter bound (2.4.9). -/
theorem theorem_2_4_4 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin ε L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖g (x i)‖) →
      ar1Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (_hL1 : 1 ≤ L)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0,
      κS = max (σ 0) (γ₃ * L / (2 * (1 - η₂))) / η₁ ∧
      κA = κS * (1 + |Real.log γ₁| / Real.log γ₂) ∧
      κC = Real.log (max (σ 0) (γ₃ * L / (2 * (1 - η₂))) / σ 0) / Real.log γ₂ + 1 ∧
      ∃ K, ‖g (x K)‖ ≤ ε ∧ ar1Run f g x σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε K ∧
        ((K + 1 : ℕ) : ℝ) ≤ κA * (f (x 0) - flow) / ε ^ 2 + κC ∧
        (((successfulIterations ρ η₁ K).card + 1 : ℕ) : ℝ) ≤
          κS * (f (x 0) - flow) / ε ^ 2 + 1 := by
  have h0 := hprefix 0 (by simp)
  have hσ0 : 0 < σ 0 := h0.updates.pos le_rfl
  let M := max (σ 0) (γ₃ * L / (2 * (1 - η₂)))
  let κS := M / η₁
  let A := 1 + |Real.log γ₁| / Real.log γ₂
  let C := Real.log (M / σ 0) / Real.log γ₂
  have hlog : 0 < Real.log γ₂ := Real.log_pos h0.updates.one_lt_gamma2
  have hM : 0 < M := hσ0.trans_le (le_max_left _ _)
  have hS : 0 < κS := div_pos hM h0.updates.eta1_pos
  have hA : 0 < A := by dsimp [A]; positivity
  have hratio : 1 ≤ M / σ 0 := (le_div_iff₀ hσ0).mpr (by
    simpa only [one_mul] using
      (le_max_left (σ 0) (γ₃ * L / (2 * (1 - η₂))) : σ 0 ≤ M))
  have hC : 0 ≤ C := div_nonneg (Real.log_nonneg hratio) hlog.le
  obtain ⟨K, hstop, hK⟩ := FirstOrderRegularization.exists_termination hprefix hL hlow
  refine ⟨κS, hS, κS * A, mul_pos hS hA, C + 1, by linarith,
    rfl, rfl, rfl, K, hstop, hK, ?_, ?_⟩
  · have hb := hK.iterations_le hL (hlow _)
    push_cast
    calc
      (K : ℝ) + 1 ≤ M / η₁ * (f (x 0) - flow) / ε ^ 2 * A + C + 1 :=
        add_le_add hb le_rfl
      _ = _ := by dsimp [κS]; ring
  · simpa [κS, M, successfulIterations] using
      add_le_add (hK.successful_card_le hL (hlow _)) (le_rfl : (1 : ℝ) ≤ 1)

/-- **Theorem 2.4.5 (slow AR1 convergence).** With parameters fixed before the
accuracy is chosen, AR1 can require at least `ε⁻²` objective and gradient evaluations
on a nonnegative `C¹` objective with uniformly Lipschitz gradient and bounded initial
gap. The actual ratios are all at least `η₂`, and the regularization parameter stays
at its positive floor. The explicit one-dimensional plateau objective gives
`N = ceil(ε⁻²)` iterations; both evaluation counts are `N + 1`, including initialization
and the terminal gradient test. -/
theorem theorem_2_4_5 {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ}
    (hσ : 0 < σmin) (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁0 : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ) (ρ : ℕ → ℝ) (N : ℕ),
        ContDiff ℝ 1 f ∧ (∀ y, HasFDerivAt f (innerSL ℝ (g y)) y) ∧
        (∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) ∧
        (∀ y, 0 ≤ f y) ∧ f (x 0) ≤ 8 / σmin ∧ x 0 = 0 ∧
        N = ⌈1 / ε ^ 2⌉₊ ∧
        FirstOrderRegularization.Run f g x (fun _ => σmin) ρ η₁ η₂ γ₁ γ₂ γ₃ σmin ε N ∧
        (∀ i < N, η₂ ≤ ρ i) ∧ ‖g (x N)‖ = ε ∧ (1 / ε ^ 2 : ℝ) ≤ N ∧
        FirstOrderRegularization.Run.functionEvaluations N = N + 1 ∧
        FirstOrderRegularization.Run.gradientEvaluations ρ η₁ N = N + 1 ∧
        (1 / ε ^ 2 : ℝ) ≤ FirstOrderRegularization.Run.functionEvaluations N ∧
        (1 / ε ^ 2 : ℝ) ≤ FirstOrderRegularization.Run.gradientEvaluations ρ η₁ N :=
  FirstOrderRegularization.exists_slow_run hσ hη₁ hη hη₂ hγ₁0 hγ₁1 hγ₂ hγ₃

end CartisGouldToint
