import Numlib.Analysis.Calculus.TaylorModel
import Numlib.Optimization.Regularization.Inexact.ModelDecrease
import Numlib.Optimization.Regularization.Inexact.RadiusLoop
import Numlib.Optimization.TrustRegion.Inexact.Acceptance
import Numlib.Optimization.HighOrder.ModelDecrease
import Numlib.Optimization.EvaluationComplexity.TrialUpdates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Trial counts and positive model decrease for implicit dynamic accuracy

Trial counts distinguish parameter updates from accuracy-only iterations, using the terminal
parameter after the counted updates. Approximate Taylor polynomials are finite polynomials of the
actual approximate derivative tensors. The model-comparison conditions of Step 2 imply both the
penalty lower bound and strict positivity of the acceptance ratio denominator.
-/

namespace CartisGouldToint

/-- The approximate Taylor model formed from a sequence of approximate derivative tensors. -/
noncomputable def inexactTaylorModel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (s : E) : ℝ :=
  TaylorModel.ofJet A p s

/-- Lemma 13.1.13: a trial step that improves on a strictly improving comparison step yields
at least the regularization penalty in the approximate Taylor decrement. That decrement is
strictly positive, so the denominator of equation (13.1.58) is nonzero. The two model comparisons
are the operational conditions (13.1.54) and (13.1.55) of Step 2. -/
theorem lemma_13_1_13 {n : ℕ}
    (A : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (p : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (d s : EuclideanSpace ℝ (Fin n))
    (hd : ModelDecrease.penalized (inexactTaylorModel A p) p σ d <
      ModelDecrease.penalized (inexactTaylorModel A p) p σ 0)
    (hs : ModelDecrease.penalized (inexactTaylorModel A p) p σ s ≤
      ModelDecrease.penalized (inexactTaylorModel A p) p σ d) :
    σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1) ≤
        inexactTaylorModel A p 0 - inexactTaylorModel A p s ∧
      0 < inexactTaylorModel A p 0 - inexactTaylorModel A p s ∧
      inexactTaylorModel A p 0 - inexactTaylorModel A p s ≠ 0 := by
  have hpos := ModelDecrease.decrement_pos (inexactTaylorModel A p) p hσ d s hd hs
  exact ⟨ModelDecrease.penalty_le_decrement _ _ _ _ (hs.trans hd.le),
    hpos, ne_of_gt hpos⟩

/-- The set of successful trials: accuracy-only iterations are excluded even if an arbitrary
stored acceptance ratio happens to exceed the acceptance threshold. -/
def successfulTrials (T : Set ℕ) (ρ : ℕ → ℝ) (η₁ : ℝ) : Set ℕ :=
  {i | i ∈ T ∧ η₁ ≤ ρ i}

/-- Lemma 13.1.1: the number of TRqIDA trials is bounded by the successful trial count and the
available logarithmic radius range. Accuracy-improving iterations leave the radius unchanged.
The prefix is `0 ≤ i < N` and its terminal radius is `Δ N`; thus the inclusive source count
`T_k` corresponds to `N = k+1` with a bound at `Δ_(k+1)`. This repairs the source's terminal-index
mismatch. The trust-region factor ranges are those required by its shrinking update rule,
correcting the regularization ranges accidentally printed in Algorithm 13.1.1. -/
theorem lemma_13_1_1 {T : Set ℕ} {Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ Δmax Δmin : ℝ} {N : ℕ}
    (h : EvaluationComplexity.TrialTrustRegionUpdates T Δ ρ η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hminpos : 0 < Δmin) (hmin : Δmin ≤ Δ N) :
    ((EvaluationComplexity.successfulIterations T N).card : ℝ) ≤
      (EvaluationComplexity.successfulIterations (successfulTrials T ρ η₁) N).card *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      |Real.log (Δmin / Δ 0)| / |Real.log γ₂| := by
  apply EvaluationComplexity.iteration_bound_of_parameter_lower_on_trials
    (S := successfulTrials T ρ η₁) (δ := Δ) (γs := γ₃) (γu := γ₂)
    (fun _ hi => hi.1) (fun _ hi => h.pos hi)
    (lt_of_lt_of_le zero_lt_one h.one_le_gamma3)
    (h.gamma1_pos.trans_le h.gamma1_le_gamma2) h.gamma2_lt_one hmin hminpos
  · intro i hi hS
    exact h.successful_le hi hS.1 hS.2
  · intro i hi hT hS
    exact h.unsuccessful_le hi hT (fun hρ => hS ⟨hT, hρ⟩)
  · intro i hi hT
    exact h.inactive_eq hi hT

/-- Lemma 13.1.9: the number of ARqpIDA trials is bounded by successful trials and the
logarithmic regularization range. Step 5 iterations keep `σ` fixed. The half-open prefix of `N`
updates is bounded using `σ N`, repairing the same terminal-index mismatch as Lemma 13.1.1. -/
theorem lemma_13_1_9 {T : Set ℕ} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin σmax : ℝ} {N : ℕ}
    (h : EvaluationComplexity.TrialRegularizationUpdates T σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hmax : σ N ≤ σmax) :
    ((EvaluationComplexity.successfulIterations T N).card : ℝ) ≤
      (EvaluationComplexity.successfulIterations (successfulTrials T ρ η₁) N).card *
        (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (σmax / σ 0) / Real.log γ₂ := by
  apply EvaluationComplexity.iteration_bound_of_parameter_upper_on_trials
    (S := successfulTrials T ρ η₁) (σ := σ) (γs := γ₁) (γu := γ₂)
    (fun _ hi => hi.1) (fun _ hi => h.pos hi)
    h.gamma1_pos h.gamma1_lt_one h.one_lt_gamma2 hmax
  · intro i hi hS
    exact h.successful_ge hi hS.1 hS.2
  · intro i hi hT hS
    exact h.unsuccessful_ge hi hT (fun hρ => hS ⟨hT, hρ⟩)
  · intro i hi hT
    exact h.inactive_eq hi hT

/-- The failed computed test and model comparison of TRqIDA on its actual trial set.
This selection component is sufficient for Lemma 13.1.2; it excludes accuracy-only
iterations and makes no claim to specify the complete algorithm. -/
abbrev idaSelectedTrials {n q : ℕ}
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (Δ : ℕ → ℝ)
    (d s : ℕ → EuclideanSpace ℝ (Fin n)) (ε : Fin q → ℝ) (ζ θ : ℝ) : Prop :=
  InexactTrustRegion.SelectedTrials A T j Δ d s ε ζ θ

/-- The actual normalized inexact Taylor gap (13.1.25). -/
noncomputable abbrev idaScaledGap {n q : ℕ}
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (j : ℕ → Fin q) (Δ : ℕ → ℝ) (d : ℕ → EuclideanSpace ℝ (Fin n)) (θ : ℝ) (i : ℕ) : ℝ :=
  InexactTrustRegion.scaledGap A j Δ d θ i

/-- The finite minimum over the actual inclusive trial prefix `T ∩ [0:k]`. -/
noncomputable abbrev idaPrefixGap {n q : ℕ}
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (Δ : ℕ → ℝ)
    (d : ℕ → EuclideanSpace ℝ (Fin n)) (θ : ℝ) (k : ℕ) (hk : k ∈ T) : ℝ :=
  InexactTrustRegion.prefixGap A T j Δ d θ k hk

/-- **Lemma 13.1.2.** Every trial-prefix minimum satisfies (13.1.26), and the
actual chosen comparison step gives (13.1.27). Both follow from the failed computed
optimality test and Step 2's model comparison. Derivative accuracy and later updates
are unnecessary for this lemma about the actual approximate Taylor polynomials. -/
theorem lemma_13_1_2 {n q : ℕ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {Δ : ℕ → ℝ}
    {d s : ℕ → EuclideanSpace ℝ (Fin n)} {ε : Fin q → ℝ} {ζ θ : ℝ} {k : ℕ}
    (h : idaSelectedTrials A T j Δ d s ε ζ θ) (hk : k ∈ T) :
    ζ / 2 * InexactTrustRegion.minimumAccuracy h.order_pos ε ≤ idaPrefixGap A T j Δ d θ k hk ∧
      idaScaledGap A j Δ d θ k * (min θ (Δ k)) ^ InexactTrustRegion.modelOrder (j k) /
        (InexactTrustRegion.modelOrder (j k)).factorial ≤
          inexactTaylorModel (A k) (InexactTrustRegion.modelOrder (j k)) 0 -
            inexactTaylorModel (A k) (InexactTrustRegion.modelOrder (j k)) (s k) :=
  ⟨h.prefixGap_lower hk, h.model_decrease hk⟩

end CartisGouldToint

namespace CartisGouldToint

/-- Lemma 13.1.3: at a trial of TRqIDA, the small-radius bound guarantees the
actual objective ratio is at least `η₂`, so the permitted update does not shrink
the radius. Derivative errors are bounded by their oracle constants times the
requested accuracies; Step 2 bounds each requested accuracy by the actual step
length. These are the primitive conditions (13.1.2) and (13.1.9). -/
theorem lemma_13_1_3 {n q : ℕ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ}
    {d s x : ℕ → EuclideanSpace ℝ (Fin n)} {ε : Fin q → ℝ} {ζ θ : ℝ}
    (h : InexactTrustRegion.SelectedTrials A T j Δ d s ε ζ θ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ q f)
    {L κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax : ℝ} {N k : ℕ}
    (hu : EvaluationComplexity.TrialTrustRegionUpdates T Δ ρ η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hkN : k < N) (hk : k ∈ T) (hL : 1 ≤ L) (hκs : 0 ≤ κs) (hκmax : 0 ≤ κmax)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (κ : ℕ → ℝ) (accuracy : ℕ → ℕ → ℝ)
    (hκ : ∀ a, 1 ≤ a → a ≤ q → 0 ≤ κ a ∧ κ a ≤ κmax)
    (horacle : ∀ a, 1 ≤ a → a ≤ q →
      ‖A k a - iteratedFDeriv ℝ a f (x k)‖ ≤ κ a * accuracy k a)
    (hrequest : ∀ a, 1 ≤ a → a ≤ q →
      accuracy k a ≤ κs * ‖s k‖ ^ (q - a + 1))
    (hzero : A k 0 (fun _ => 0) = f (x k))
    (hratio : ρ k = (f (x k) - f (x k + s k)) /
      InexactTrustRegion.decrement (A k) (InexactTrustRegion.modelOrder (j k)) (s k))
    (hsmall : Δ k ≤ min θ ((1 - η₂) /
      (L + 4 * ((q + 1).factorial : ℝ) * κs * κmax) *
      InexactTrustRegion.scaledGap A j Δ d θ k)) :
    η₂ ≤ ρ k ∧ Δ k ≤ Δ (k + 1) := by
  have herr : ∀ a, 1 ≤ a → a ≤ InexactTrustRegion.modelOrder (j k) →
      ‖A k a - iteratedFDeriv ℝ a f (x k)‖ ≤
        (κs * κmax) * ‖s k‖ ^ (q - a + 1) := by
    intro a ha haj
    have haq : a ≤ q := haj.trans (by exact (j k).isLt)
    calc _ ≤ κ a * accuracy k a := horacle a ha haq
      _ ≤ κ a * (κs * ‖s k‖ ^ (q - a + 1)) :=
        mul_le_mul_of_nonneg_left (hrequest a ha haq) (hκ a ha haq).1
      _ ≤ κmax * (κs * ‖s k‖ ^ (q - a + 1)) :=
        mul_le_mul_of_nonneg_right (hκ a ha haq).2 (by positivity)
      _ = _ := by ring
  have hs := h.very_successful hf hL (mul_nonneg hκs hκmax) hu.eta2_lt_one
    hlip x hk hzero herr (by
      simpa only [InexactTrustRegion.acceptanceCoefficient, mul_assoc] using hsmall)
  rw [← hratio] at hs
  exact ⟨hs, (show Δ (k + 1) ∈ Set.Icc (Δ k) (min Δmax (γ₃ * Δ k)) by
    simpa only [ite_eq_left hs] using hu.update k hkN hk).1⟩

end CartisGouldToint

namespace CartisGouldToint

/-- Lemma 13.1.10: a positive truncated computed Taylor decrement retains at
least half its value in the full inexact regularized model at a small radius.
The uniform tensor bound (13.1.63) is derived from Lipschitz lower derivatives,
the primitive oracle errors and the nonincreasing requested accuracy cap. -/
theorem lemma_13_1_10 {n p j : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {L κmax κh σ α δ : ℝ}
    (hL : 1 ≤ L) (hκmax : 0 ≤ κmax) (hκh : 0 ≤ κh) (hσ : 0 ≤ σ)
    (hlip : ∀ a, a < p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (κ accuracy : ℕ → ℝ)
    (hκ : ∀ a, 1 ≤ a → a ≤ p → 0 ≤ κ a ∧ κ a ≤ κmax)
    (haccuracy : ∀ a, 1 ≤ a → a ≤ p → accuracy a ≤ κh)
    (horacle : ∀ a, 1 ≤ a → a ≤ p →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ κ a * accuracy a)
    (hj : 0 < j) (hjp : j ≤ p) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 (α / (4 * max (L + κmax * κh) σ)))
    (d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖ ≤ δ)
    (htest : α * δ ^ j / j.factorial ≤ TaylorModel.jetDecrement A j d) :
    α / 2 * δ ^ j / j.factorial ≤
      ModelDecrease.penalized (inexactTaylorModel A p) p σ 0 -
        ModelDecrease.penalized (inexactTaylorModel A p) p σ d := by
  apply TaylorModel.penalized_decrement_ge_half A hj hjp
    (by positivity : 0 < L + κmax * κh) hσ hδ
    (hsmall.trans (min_le_left _ _)) (hsmall.trans (min_le_right _ _))
    (fun a hja hap => TaylorModel.norm_jet_le_of_lipschitz_oracle
      (by linarith) hκh hlip A x κ accuracy hκ haccuracy horacle (by omega) hap) d hd htest

end CartisGouldToint

namespace CartisGouldToint

/-- Lemma 13.1.11: for each tested positive order, the actual radius-halving
program exits finitely through Step 1.2 or Step 1.3. Every intermediate radius
lies between its initial and final values, and the final radius satisfies the
exact floor (13.1.66). The selected directions may be any feasible directions;
the stronger approximation requirement (13.1.52) is unnecessary for this result. -/
theorem lemma_13_1_11 {n p j : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {L κmax κh σ ζ ε δ₀ : ℝ}
    (hL : 1 ≤ L) (hκmax : 0 ≤ κmax) (hκh : 0 ≤ κh) (hσ : 0 ≤ σ)
    (hlip : ∀ a, a < p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (κ accuracy : ℕ → ℝ)
    (hκ : ∀ a, 1 ≤ a → a ≤ p → 0 ≤ κ a ∧ κ a ≤ κmax)
    (haccuracy : ∀ a, 1 ≤ a → a ≤ p → accuracy a ≤ κh)
    (horacle : ∀ a, 1 ≤ a → a ≤ p →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ κ a * accuracy a)
    (hj : 0 < j) (hjp : j ≤ p) (hζ : 0 < ζ) (hε : 0 < ε)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (d : ℕ → EuclideanSpace ℝ (Fin n))
    (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t) :
    ∃ N, InexactRegularization.HalvingRun A j p σ ζ ε δ₀ d N ∧
      min (ζ * ε / (16 * max (L + κmax * κh) σ)) δ₀ ≤
        BacktrackingGradient.step δ₀ N ∧
      ∀ t ≤ N, BacktrackingGradient.step δ₀ N ≤ BacktrackingGradient.step δ₀ t ∧
        BacktrackingGradient.step δ₀ t ≤ δ₀ := by
  exact InexactRegularization.exists_halvingRun A hj hjp
    (by positivity : 0 < L + κmax * κh) hσ hζ hε hδ₀ hδ₀1
    (fun a hja hap => TaylorModel.norm_jet_le_of_lipschitz_oracle
      (by linarith) hκh hlip A x κ accuracy hκ haccuracy horacle (by omega) hap) d hd

end CartisGouldToint
