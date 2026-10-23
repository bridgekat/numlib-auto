import Numlib.Optimization.TrustRegion.Inexact.FunctionDecrease
import Numlib.Optimization.Regularization.Inexact.GuardedCounterexample.PrintedConstants
import Numlib.Optimization.Regularization.Inexact.Explicit.CurrentBudget
import Numlib.Optimization.Regularization.Inexact.Explicit.Complexity
import Numlib.Optimization.HighOrder.CriticalityRadius
import Numlib.Optimization.Regularization.Inexact.Explicit.Stopping
import Numlib.Optimization.Regularization.Inexact.VerifiedOptimality
import Numlib.Optimization.TrustRegion.Inexact.FunctionRadius
import Numlib.Optimization.TrustRegion.Inexact.Budget
import Numlib.Optimization.Regularization.Inexact.ParameterFunctionCounterexample
import Numlib.Optimization.TrustRegion.Inexact.FunctionValues
import Numlib.Optimization.TrustRegion.Inexact.VerifiedOptimality
import Numlib.Optimization.EvaluationComplexity.TrialUpdates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Explicit dynamic accuracy

The acceptance numerator uses actual approximate objective evaluations, with
known absolute errors bounded by the requested relative accuracy. The computed
Taylor decrement uses the actual approximate derivative tensors; its constant
coefficient cancels. Both objective errors enter the acceptance proof.
-/

namespace CartisGouldToint

/-- Lemma 13.3.1: the stated small-radius condition makes a TRqEDA trial very
successful and prevents radius contraction. Each tensor oracle has the known
unit constant (13.3.3), and both approximate objective values satisfy the actual
absolute-error bounds (13.3.1)–(13.3.2) with the relative request (13.3.9). -/
theorem lemma_13_3_1 {n q : ℕ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ}
    {d s x : ℕ → EuclideanSpace ℝ (Fin n)} {ε : Fin q → ℝ} {ζ θ : ℝ}
    (h : InexactTrustRegion.SelectedTrials A T j Δ d s ε ζ θ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ q f)
    {L κs η₁ η₂ γ₁ γ₂ γ₃ Δmax : ℝ} {N k : ℕ}
    (hu : EvaluationComplexity.TrialTrustRegionUpdates T Δ ρ η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hkN : k < N) (hk : k ∈ T) (hL : 1 ≤ L) (hκs : 0 ≤ κs)
    (hκsmall : κs ≤ (1 - η₂) / 4)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (accuracy : ℕ → ℝ)
    (horacle : ∀ a, 1 ≤ a → a ≤ q →
      ‖A k a - iteratedFDeriv ℝ a f (x k)‖ ≤ accuracy a)
    (hrequest : ∀ a, 1 ≤ a → a ≤ q →
      accuracy a ≤ κs * ‖s k‖ ^ (q - a + 1))
    (F₀ F₁ h₀ : ℝ) (hF₀ : |F₀ - f (x k)| ≤ h₀)
    (hF₁ : |F₁ - f (x k + s k)| ≤ h₀)
    (h₀bound : h₀ ≤ κs * InexactTrustRegion.decrement (A k)
      (InexactTrustRegion.modelOrder (j k)) (s k))
    (hratio : ρ k = (F₀ - F₁) /
      InexactTrustRegion.decrement (A k) (InexactTrustRegion.modelOrder (j k)) (s k))
    (hsmall : Δ k ≤ min θ ((1 - η₂) /
      (L + 4 * ((q + 1).factorial : ℝ) * κs) *
      InexactTrustRegion.scaledGap A j Δ d θ k)) :
    η₂ ≤ ρ k ∧ Δ k ≤ Δ (k + 1) := by
  have herr : ∀ a, 1 ≤ a → a ≤ InexactTrustRegion.modelOrder (j k) →
      ‖A k a - iteratedFDeriv ℝ a f (x k)‖ ≤ κs * ‖s k‖ ^ (q - a + 1) := by
    intro a ha haj
    have haq : a ≤ q := haj.trans (by exact (j k).isLt)
    exact (horacle a ha haq).trans (hrequest a ha haq)
  have hs := h.very_successful_inexact_values hf hL hκs hu.eta2_lt_one hκsmall
    hlip x hk herr hsmall F₀ F₁ (hF₀.trans h₀bound) (hF₁.trans h₀bound)
  rw [← hratio] at hs
  exact ⟨hs, (show Δ (k + 1) ∈ Set.Icc (Δ k) (min Δmax (γ₃ * Δ k)) by
    simpa only [ite_eq_left hs] using hu.update k hkN hk).1⟩

end CartisGouldToint

namespace CartisGouldToint

/-- The explicit finite error-budget verification used by the EDA stopping tests. -/
noncomputable abbrev explicitAccuracyVerifier (accuracy : ℕ → ℝ) (q : ℕ)
    (δ tolerance : ℝ) : Prop :=
  InexactTrustRegion.tensorErrorBudget accuracy q δ ≤ tolerance

/-- The computed selection, passing tests and verified finite derivative-error
budget at the end of Step 1 of TRqEDA. This is the termination-check component,
not a specification of the whole algorithm. -/
abbrev edaTerminationCheck {n q : ℕ}
    (A : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (δ ζ : ℝ) (ε : Fin q → ℝ) (d : Fin q → EuclideanSpace ℝ (Fin n))
    (accuracy : ℕ → ℝ) : Prop :=
  InexactTrustRegion.TerminationCheck A δ ζ ε d accuracy

/-- The optimality assertion (i) of Lemma 13.3.3: passing the actual computed
all-order checks and the explicit finite accuracy test certifies all true Taylor
criticality tolerances. The finite-loop assertion (ii) is separate. -/
theorem lemma_13_3_3_optimality {n q : ℕ}
    {A : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {δ ζ : ℝ} {ε : Fin q → ℝ} {d : Fin q → EuclideanSpace ℝ (Fin n)}
    {accuracy : ℕ → ℝ} (h : edaTerminationCheck A δ ζ ε d accuracy)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (horacle : ∀ a, 1 ≤ a → a ≤ q →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ accuracy a) :
    ∀ a : Fin q, TaylorModel.criticality f (InexactTrustRegion.modelOrder a) x δ ≤
      ε a * δ ^ InexactTrustRegion.modelOrder a /
        (InexactTrustRegion.modelOrder a).factorial :=
  h.true_optimality f x horacle

end CartisGouldToint

namespace CartisGouldToint

/-- The guarded oracle, actual computed model, both approximate objective
values and legal parameter updates of ARqpEDA. This component does not prescribe
stopping or derivative model-stationarity tests, which the parameter bound does not use. -/
abbrev edaRegularizationModelTrace {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (O : InexactRegularization.OracleSettings p)
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (T : Set ℕ)
    (x d s : ℕ → EuclideanSpace ℝ (Fin n)) (accuracy : ℕ → ℕ → ℝ)
    (σ ρ F₀ F₁ h₀ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
  InexactRegularization.FunctionTrace f p O A T x d s accuracy σ ρ F₀ F₁ h₀
    η₁ η₂ γ₁ γ₂ γ₃ σmin N

/-- **Corrected Lemma 13.3.5.** The literal short-step derivative-accuracy guard
requires `max(κs,κh)` in the uniform regularization bound. Both actual objective
errors are included, with the known unit tensor-oracle constant (13.3.3).
The all-derivative request range is repaired from the final Step 2 text `1:q`
to `1:p`, as required by equation (13.1.46); the short-step guard is retained. -/
theorem lemma_13_3_5_corrected {n p N : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : InexactRegularization.OracleSettings p}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ} {T : Set ℕ}
    {x d s : ℕ → EuclideanSpace ℝ (Fin n)} {accuracy : ℕ → ℕ → ℝ}
    {σ ρ F₀ F₁ h₀ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ}
    (h : edaRegularizationModelTrace f p O A T x d s accuracy σ ρ F₀ F₁ h₀
      η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hsmall : O.stepCoefficient ≤ (1 - η₂) / 4) (hunit : O.errorBound = 1) :
    ∀ k ≤ N, σ k ≤ max (σ 0) (γ₃ *
      (2 * L + 4 * ((p + 1).factorial : ℝ) *
        max O.stepCoefficient O.initialCap) / (1 - η₂)) := by
  intro k hk
  simpa only [InexactRegularization.parameterCoefficient, hunit, mul_one] using
    h.parameter_le hf (zero_le_one.trans hL) hlip hsmall hk

/-- The printed bound in Lemma 13.3.5 is valid under the explicit extra
condition `κh≤κs`, which is absent from the printed algorithm. -/
theorem lemma_13_3_5_of_cap_le {n p N : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : InexactRegularization.OracleSettings p}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ} {T : Set ℕ}
    {x d s : ℕ → EuclideanSpace ℝ (Fin n)} {accuracy : ℕ → ℕ → ℝ}
    {σ ρ F₀ F₁ h₀ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ}
    (h : edaRegularizationModelTrace f p O A T x d s accuracy σ ρ F₀ F₁ h₀
      η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hsmall : O.stepCoefficient ≤ (1 - η₂) / 4) (hunit : O.errorBound = 1)
    (hcap : O.initialCap ≤ O.stepCoefficient) :
    ∀ k ≤ N, σ k ≤ max (σ 0) (γ₃ *
      (2 * L + 4 * ((p + 1).factorial : ℝ) * O.stepCoefficient) / (1 - η₂)) :=
  fun _ hk => h.parameter_le_of_cap_le hf (zero_le_one.trans hL) hlip hsmall hcap hunit hk

open InexactRegularization InexactRegularization.Counterexample in
/-- An actual EDA trial has exact zero objective values with positive request
one, all source smoothness and reference tests, and a global computed-model
minimizer. Its allowed update to 64 violates the printed upper bound 32, even
though both EDA restrictions on `κs=1/16` hold. -/
theorem arqpedaPrintedBoundCounterexample :
    FunctionTrace (fun _ : ℝ => 0) 1 FunctionCounterexample.settings (fun _ => data) Set.univ
      (fun _ => 0) (fun _ => 1) (fun _ => 125 / 4) (fun _ _ => 1000)
      parameter (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1)
      (1 / 4) (1 / 2) (1 / 2) 2 3 1 1 ∧
    ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ j ≤ 1, ∀ x y : ℝ,
      ‖iteratedFDeriv ℝ j (fun _ : ℝ => (0 : ℝ)) x -
        iteratedFDeriv ℝ j (fun _ : ℝ => (0 : ℝ)) y‖ ≤ ‖x - y‖) ∧
    (‖(1 : ℝ)‖ ≤ 1 ∧ ∀ t : ℝ, ‖t‖ ≤ 1 →
      TaylorModel.jetDecrement data 1 t ≤ TaylorModel.jetDecrement data 1 1) ∧
    ((1 : ℝ) / 4 < TaylorModel.jetDecrement data 1 1 ∧
      (1 : ℝ) / 8 ≤ model data 1 (parameter 0) 0 - model data 1 (parameter 0) 1) ∧
    (∀ t : ℝ, model data 1 32 (125 / 4) ≤ model data 1 32 t) ∧
    (FunctionCounterexample.settings.stepCoefficient ≤ ((1 : ℝ) / 4) / 4 ∧
      FunctionCounterexample.settings.stepCoefficient ≤ (1 - (1 : ℝ) / 2) / 4 ∧
      FunctionCounterexample.settings.errorBound = 1) ∧
    max (parameter 0)
      (3 * (2 * (1 : ℝ) + 4 * ((1 + 1 : ℕ).factorial : ℝ) *
        FunctionCounterexample.settings.stepCoefficient) / (1 - 1 / 2)) < parameter 1 :=
  ⟨FunctionCounterexample.trace, smoothness.1, smoothness.2, reference_maximizes,
    reference_tests, step_minimizes, FunctionCounterexample.coefficient_restrictions,
    FunctionCounterexample.printed_bound_violated⟩

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion

/-- The actual EDA oracle, computed objective ratio and radius-update trace. -/
abbrev edaModelTrace {n q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (x d s : ℕ → EuclideanSpace ℝ (Fin n))
    (Δ ρ F₀ F₁ h₀ : ℕ → ℝ) (ε : Fin q → ℝ) (accuracy : ℕ → ℕ → ℝ)
    (ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax : ℝ) (N : ℕ) : Prop :=
  FunctionModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
    ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N

/-- Lemma 13.3.3, both clauses. The explicit Step 1.4.1 budget test certifies
true all-order optimality. Moreover, the source uniform request threshold forces
that test to pass, so Step 1.4.2 cannot be selected. The needed radius floor is
derived from actual approximate objective values and computed-ratio updates. -/
theorem lemma_13_3_3 {n q N k : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → EuclideanSpace ℝ (Fin n)}
    {Δ ρ F₀ F₁ h₀ : ℕ → ℝ} {ε : Fin q → ℝ} {accuracy : ℕ → ℕ → ℝ}
    {ζ θ κs κh η₁ η₂ γ₁ γ₂ γ₃ Δmax L H : ℝ}
    (h : edaModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
      ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hL : 1 ≤ L) (hκh : 0 ≤ κh)
    (hk : k ≤ N) (hH0 : 0 ≤ H)
    (hH : ∀ a, 1 ≤ a → a ≤ q → accuracy k a ≤ H)
    (horacle : ∀ a, 1 ≤ a → a ≤ q →
      ‖A k a - iteratedFDeriv ℝ a f (x k)‖ ≤ accuracy k a)
    (direction : Fin q → EuclideanSpace ℝ (Fin n))
    (happrox : ∀ a, ζ * TaylorModel.jetCriticality (A k) (modelOrder a)
      (optimalityRadius θ (Δ k)) ≤
      TaylorModel.jetDecrement (A k) (modelOrder a) (direction a))
    (hpass : ∀ a, TaylorModel.jetDecrement (A k) (modelOrder a) (direction a) ≤
      ζ / 2 * ε a * optimalityRadius θ (Δ k) ^ modelOrder a / (modelOrder a).factorial) :
    let δ := optimalityRadius θ (Δ k)
    let κδ := radiusConstant f h.order_pos (x 0) θ (Δ 0) γ₁ η₂ L κs 1 κh / 2
    let optimal := ∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (x k) δ ≤
      ε a * δ ^ modelOrder a / (modelOrder a).factorial
    (tensorErrorBudget (accuracy k) q δ ≤
      ζ / 2 * minimumAccuracy h.order_pos ε * δ ^ q / q.factorial → optimal) ∧
    (ContDiff ℝ q f →
      (∀ a, 1 ≤ a → a ≤ q → ∀ u v,
        ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖) →
      H ≤ accuracyThreshold q ζ κδ 1 (minimumAccuracy h.order_pos ε) →
      edaTerminationCheck (A k) δ ζ ε direction (accuracy k) ∧ optimal) := by
  dsimp only
  have hδ := le_min h.cap_pos.le (h.updates.pos hk).le
  have hδ1 := (min_le_left θ (Δ k)).trans h.cap_le_one
  have hmake (hver : tensorErrorBudget (accuracy k) q (optimalityRadius θ (Δ k)) ≤
      ζ / 2 * minimumAccuracy h.order_pos ε * optimalityRadius θ (Δ k) ^ q / q.factorial) :
      edaTerminationCheck (A k) (optimalityRadius θ (Δ k)) ζ ε direction (accuracy k) :=
    ⟨h.order_pos, hδ, hδ1, h.zeta_pos, h.zeta_le_one, h.accuracy_pos,
      happrox, hpass, hver⟩
  refine ⟨fun hver => (hmake hver).true_optimality f (x k) horacle, ?_⟩
  intro hf hlip hsmall
  have hb := radiusConstant_bounds (L := L) f h.order_pos (x 0)
    h.cap_pos.le h.cap_le_one h.updates.initial_pos.le h.updates.gamma1_pos.le
    h.updates.eta2_lt_one.le (by linarith : 0 ≤ L) h.request_factor_nonneg
    (by norm_num : (0 : ℝ) ≤ 1) hκh
  have hfloor := h.optimalityRadius_lower hf hL hlip (by simpa only [mul_one] using hb.2) hk
  have hc := terminationCheck_of_accuracyThreshold h.order_pos hδ hδ1
    h.zeta_pos h.zeta_le_one (div_nonneg hb.1 (by norm_num)) (by norm_num : (0 : ℝ) < 1)
    hH0 h.accuracy_pos rfl hfloor hsmall hH happrox hpass
  have hc' : edaTerminationCheck (A k) (optimalityRadius θ (Δ k)) ζ ε direction
      (accuracy k) := by
    apply hmake
    simpa only [tensorErrorBudget, optimalityRadius, one_mul] using hc.verified
  exact ⟨hc', hc'.true_optimality f (x k) horacle⟩

end CartisGouldToint

namespace CartisGouldToint

/-- The per-order computed tests and actual finite accuracy budgets in Step1.5.1
of ARqpEDA, using the algorithm's vector of optimality radii. -/
abbrev edaRegularizationTerminationCheck {n q : ℕ}
    (A : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (δ : Fin q → ℝ) (ζ : ℝ) (ε : Fin q → ℝ)
    (d : Fin q → EuclideanSpace ℝ (Fin n)) (accuracy : ℕ → ℝ) : Prop :=
  InexactRegularization.VectorTerminationCheck A δ ζ ε d accuracy

/-- Lemma13.3.6(i): each explicitly verified vector-radius computed optimality
test certifies the corresponding true Taylor criticality condition. The separate
finite-loop assertion(ii) requires a proved solver radius-floor theorem. -/
theorem lemma_13_3_6_optimality {n q : ℕ}
    {A : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {δ ε : Fin q → ℝ} {ζ : ℝ} {d : Fin q → EuclideanSpace ℝ (Fin n)}
    {accuracy : ℕ → ℝ} (h : edaRegularizationTerminationCheck A δ ζ ε d accuracy)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (horacle : ∀ a, 1 ≤ a → a ≤ q →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ accuracy a) :
    ∀ a : Fin q, TaylorModel.criticality f (InexactTrustRegion.modelOrder a) x (δ a) ≤
      ε a * δ a ^ InexactTrustRegion.modelOrder a / (InexactTrustRegion.modelOrder a).factorial :=
  h.true_optimality f x horacle

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion

/-- The full finite ARqpEDA operational execution of Algorithm13.3.2, including
both approximate objective values and the literal explicit stopping budgets. -/
abbrev arqpedaRun {n p q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : InexactRegularization.Explicit.Settings p q) (ε : Fin q → ℝ)
    (D : InexactRegularization.Explicit.ExecutionData (EuclideanSpace ℝ (Fin n)) q)
    (N : ℕ) : Prop := InexactRegularization.Explicit.Run f P ε D N

/-- Lemma13.3.6 with the genuine corrected guarded parameter cap. The explicit
finite error budgets certify true optimality. Actual oracle and radius histories
force those budgets under the displayed uniform accuracy threshold, so a finished
computed optimality loop takes Step1.5.1. The original printed-cap assertion
remains a separate open target. -/
theorem lemma_13_3_6_corrected {n p q N k : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : InexactRegularization.Explicit.Settings p q} {ε : Fin q → ℝ}
    {D : InexactRegularization.Explicit.ExecutionData (EuclideanSpace ℝ (Fin n)) q}
    (h : arqpedaRun f P ε D N) (hk : k ≤ N) (hselected : D.selected k = none) :
    let optimal := ∀ a : Fin q,
      TaylorModel.criticality f (modelOrder a) (D.point k) (D.checkedRadius k a) ≤
        ε a * D.checkedRadius k a ^ modelOrder a / (modelOrder a).factorial
    ((∀ a : Fin q, tensorErrorBudget (D.accuracy k) (modelOrder a) (D.checkedRadius k a) ≤
      P.zeta / 2 * ε a * D.checkedRadius k a ^ modelOrder a / (modelOrder a).factorial) →
        optimal) ∧
    (ContDiff ℝ p f → ∀ L : ℝ, 1 ≤ L →
      (∀ i, i ≤ p → ∀ x y,
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖) →
      ∀ H : ℝ, 0 ≤ H → (∀ i, 1 ≤ i → i ≤ q → D.accuracy k i ≤ H) →
      H ≤ InexactRegularization.verificationThreshold q P.zeta
        (InexactRegularization.stepRadiusCoefficient P.zeta P.theta
          (InexactRegularization.executionTensorCap P.toSettings L)
          (InexactRegularization.executionParameterCap P.toSettings L))
        1 (minimumAccuracy P.order_pos ε) →
      InexactRegularization.Explicit.StopsAt P ε D k ∧ optimal) := by
  dsimp only
  refine ⟨fun hbudget => (h.stopped_optimality hk ⟨hselected, hbudget⟩).2, ?_⟩
  intro hf L hL hlip H hH hrequests hsmall
  exact h.passing_check_stops hf hL hlip hk hselected hH hrequests hsmall

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion EvaluationComplexity

/-- A corrected termination companion to Theorem13.3.8. The explicit positive
margin theta < zeta/2 controls failure of the literal computed stopping test,
including budget-only failures after all initial computed tests pass. The
original unrestricted theorem remains open. Both source accuracy exponents,
initialized derivative counts and two function calls per actual trial are kept. -/
theorem theorem_13_3_8_effective_margin {n p q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : InexactRegularization.Explicit.Settings p q) (x₀ : EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ p f) (hmargin : P.theta < P.zeta / 2) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖)
    (hlow : ∀ x, flow ≤ f x) :
    ∃ κA > 0, ∃ κB > 0, ∃ κF > 0, ∃ κD > 0,
      ∀ (ε : Fin q → ℝ)
        (D : InexactRegularization.Explicit.ExecutionData (EuclideanSpace ℝ (Fin n)) q),
      D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬InexactRegularization.Explicit.StopsAt P ε D k) →
        arqpedaRun f P ε D N) →
      ∃ K : ℕ, InexactRegularization.Explicit.StopsAt P ε D K ∧
        (∀ a, 0 < D.checkedRadius K a ∧ D.checkedRadius K a ≤ 1) ∧
        (∀ a, TaylorModel.criticality f (modelOrder a) (D.point K) (D.checkedRadius K a) ≤
          ε a * D.checkedRadius K a ^ modelOrder a / (modelOrder a).factorial) ∧
        (q ≤ 2 → ∀ a, TaylorModel.criticality f (modelOrder a) (D.point K) 1 ≤
          ε a / (modelOrder a).factorial) ∧ arqpedaRun f P ε D K ∧
        (∀ k < K, ¬InexactRegularization.Explicit.StopsAt P ε D k) ∧
        (2 * ((successfulIterations D.trials K).card : ℝ)) ≤
          κA * (f x₀ - flow) / InexactRegularization.accuracyFactor P.toSettings ε + κF ∧
        (derivativeEvaluations D.trials D.ratio P.eta1 K : ℝ) ≤
          κA * (f x₀ - flow) / InexactRegularization.accuracyFactor P.toSettings ε +
          κB * |Real.log (minimumAccuracy P.order_pos ε)| + κD := by
  obtain ⟨κA, hA, κB, hB, κF, hF, κD, hD, hall⟩ :=
    InexactRegularization.Explicit.evaluation_complexity f P x₀ hf hmargin hL hlip hlow
  refine ⟨κA, hA, κB, hB, κF, hF, κD, hD, ?_⟩
  intro ε D hinit hprefix
  obtain ⟨K, hstop, hlegal, hopt, hrun, hfirst, hfcount, hdcount⟩ := hall ε D hinit hprefix
  refine ⟨K, hstop, hlegal, hopt, ?_, hrun, hfirst, hfcount, hdcount⟩
  intro hq a
  exact TaylorModel.criticality_unit_le_of_radius f (D.point K)
    (by unfold modelOrder; omega) (by unfold modelOrder; omega)
    (hlegal a).1 (hlegal a).2 (hopt a)

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion EvaluationComplexity InexactRegularization

/-- An unconditional literal-stopping companion to Theorem13.3.8, with the coarser
`epsilon_min^(-(q+1))` rate. Every computed trial obeys the current-reference
comparison, so no extra theta-versus-zeta margin is required. The positive
coefficient is fixed before all accuracies and data. Both objective evaluations
per trial and every initialized derivative evaluation are counted. The original
sharper p-dependent rate remains a separate target. -/
theorem theorem_13_3_8_current_check {n p q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : InexactRegularization.Explicit.Settings p q) (x₀ : EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ x, flow ≤ f x) :
    let M := executionTensorCap P.toSettings L
    let S := executionParameterCap P.toSettings L
    ∃ c > 0, ∀ (ε : Fin q → ℝ)
      (D : InexactRegularization.Explicit.ExecutionData (EuclideanSpace ℝ (Fin n)) q),
      D.point 0 = x₀ →
      (∀ N, (∀ k < N, ¬InexactRegularization.Explicit.StopsAt P ε D k) →
        arqpedaRun f P ε D N) →
      ∃ K, InexactRegularization.Explicit.StopsAt P ε D K ∧ arqpedaRun f P ε D K ∧
        (∀ k < K, ¬InexactRegularization.Explicit.StopsAt P ε D k) ∧
        (∀ a, 0 < D.checkedRadius K a ∧ D.checkedRadius K a ≤ 1) ∧
        (∀ a, TaylorModel.criticality f (modelOrder a) (D.point K)
          (D.checkedRadius K a) ≤ ε a * D.checkedRadius K a ^ modelOrder a /
            (modelOrder a).factorial) ∧
        ((2 * (successfulIterations D.trials K).card) : ℝ) ≤
          2 * trialCountFactor P.toSettings * ((f x₀ - flow) /
            (c * (minimumAccuracy P.order_pos ε) ^ (q + 1))) +
            2 * |trialCountOffset P.toSettings S| + 2 ∧
        (derivativeEvaluations D.trials D.ratio P.eta1 K : ℝ) ≤
          (f x₀ - flow) / (c * (minimumAccuracy P.order_pos ε) ^ (q + 1)) +
            accuracyCountSlope P.toSettings * |Real.log (minimumAccuracy P.order_pos ε)| +
            accuracyCountOffset P.toSettings M S + 1 :=
  InexactRegularization.Explicit.evaluation_complexity_current f P x₀ hf hL hlip hlow

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion InexactRegularization.GuardedCounterexample

/-- An actual ARqpEDA execution refutes both fixed-coefficient assertions of
Lemma13.3.7. Exact function evaluations satisfy all explicit error requests.
Before literal termination, its actual successful trial violates both printed
decrease bounds. This finite example makes no claim against complexity
statements whose constants are existentially quantified. -/
theorem arqpedaPrintedDecreaseCounterexample :
    ContDiff ℝ 1 Real.sin ∧
    (∀ i, i ≤ 1 → ∀ x y, ‖iteratedFDeriv ℝ i Real.sin x -
      iteratedFDeriv ℝ i Real.sin y‖ ≤ ‖x - y‖) ∧
    (∀ x, -1 ≤ Real.sin x) ∧
    InexactRegularization.Explicit.Run Real.sin settings (fun _ => 1 / 2) data 125 ∧
    (124 ∈ data.trials ∧ settings.eta1 ≤ data.ratio 124 ∧ ‖data.step 124‖ < 1) ∧
    (∀ k < 125, ¬InexactRegularization.Explicit.StopsAt settings (fun _ => 1 / 2) data k) ∧
    (∀ k a, data.solvedRadius k a = 1) ∧
    TaylorModel.jetDecrement (data.jet 124) 1 (data.step 124) <
      printedModelConstant * (1 / 2 : ℝ) ^ 2 ∧
    Real.sin (data.point 124) - Real.sin (data.point 125) <
      settings.eta1 / 2 * printedModelConstant * (1 / 2 : ℝ) ^ 2 :=
  ⟨source_regularity.1, source_regularity.2.1, source_regularity.2.2, run,
    successful_short_trial, (fun k _ => never_stops k), unit_solved_radii,
    model_floor_violated, objective_floor_violated⟩
end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion
/-- **Lemma13.3.2.** Actual TRqEDA computed Taylor decrements satisfy (13.1.34),
with the exact source radius constant and known unit oracle bound. Accepted
trials also satisfy the true decrease (13.1.35). Both approximate objective
errors and the actual computed ratio are used; no exact ratio is assumed. -/
theorem lemma_13_3_2 {n q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → EuclideanSpace ℝ (Fin n)}
    {Δ ρ F₀ F₁ h₀ : ℕ → ℝ} {ε : Fin q → ℝ} {accuracy : ℕ → ℕ → ℝ}
    {ζ θ κs κh η₁ η₂ γ₁ γ₂ γ₃ Δmax L : ℝ} {N k : ℕ}
    (h : FunctionModelTrace f A T j x d s Δ ρ F₀ F₁ h₀ ε accuracy
      ζ θ κs η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L) (hκh : 0 ≤ κh) (hκs : κs ≤ η₁ / 4)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hpoint : ∀ i < N, i ∈ T → x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i)
    (hk : k < N) (hT : k ∈ T) :
    let κδ := InexactTrustRegion.radiusConstant f h.order_pos (x 0)
      θ (Δ 0) γ₁ η₂ L κs 1 κh / 2
    (ζ * κδ) ^ (q + 1) / q.factorial * minimumAccuracy h.order_pos ε ^ (q + 1) ≤
      decrement (A k) (modelOrder (j k)) (s k) ∧
    (η₁ ≤ ρ k → η₁ * (ζ * κδ) ^ (q + 1) / (2 * (q.factorial : ℝ)) *
      minimumAccuracy h.order_pos ε ^ (q + 1) ≤ f (x k) - f (x (k + 1))) := by
  dsimp only
  have hκ := InexactTrustRegion.radiusConstant_bounds (L := L) f h.order_pos (x 0)
    h.cap_pos.le h.cap_le_one h.updates.initial_pos.le h.updates.gamma1_pos.le
    h.updates.eta2_lt_one.le (by linarith : 0 ≤ L) h.request_factor_nonneg zero_le_one hκh
  have hκupper := hκ.2
  simp only [mul_one] at hκupper
  exact ⟨h.model_decrease hf hL hlip hκ.1 hκupper hk.le hT,
    fun ha => h.function_decrease hf hL hlip hκ.1 hκupper hκs hpoint hk hT ha⟩
end CartisGouldToint
