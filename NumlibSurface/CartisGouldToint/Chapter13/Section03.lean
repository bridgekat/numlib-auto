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
