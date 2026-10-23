import Numlib.Optimization.TrustRegion.Inexact.Complexity
import Numlib.Optimization.TrustRegion.Inexact.RadiusConsequences
import Numlib.Optimization.Regularization.Inexact.ParameterCounterexample
import Numlib.Analysis.Calculus.TaylorModel
import Numlib.Optimization.Regularization.Inexact.ModelDecrease
import Numlib.Optimization.Regularization.Inexact.RadiusLoop
import Numlib.Optimization.TrustRegion.Inexact.Acceptance
import Numlib.Optimization.TrustRegion.Inexact.Radius
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
    (h : EvaluationComplexity.TrialRegularizationUpdates T σ ρ η₁ η₂ γ₁ γ₂
      γ₃ σmin N)
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
    (j : ℕ → Fin q) (Δ : ℕ → ℝ) (d : ℕ → EuclideanSpace ℝ (Fin n)) (θ :
      ℝ) (i : ℕ) : ℝ :=
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
    ζ / 2 * InexactTrustRegion.minimumAccuracy h.order_pos ε ≤ idaPrefixGap A T j Δ d
      θ k hk ∧
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
    (hu : EvaluationComplexity.TrialTrustRegionUpdates T Δ ρ η₁ η₂ γ₁ γ₂
      γ₃ Δmax N)
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

namespace CartisGouldToint

/-- The TRqIDA model, derivative oracle, requested accuracy, ratio and update
components needed for the radius analysis. It specifies primitive operations,
not the whole program or any of its radius conclusions. -/
abbrev idaModelTrace {n q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (x d s : ℕ → EuclideanSpace ℝ (Fin n))
    (Δ ρ : ℕ → ℝ) (ε : Fin q → ℝ) (accuracy : ℕ → ℕ → ℝ)
    (ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax : ℝ) (N : ℕ) : Prop :=
  InexactTrustRegion.ModelTrace f A T j x d s Δ ρ ε accuracy
    ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N

/-- Lemma 13.1.4: the inclusive trial-prefix minimum gives the stated trust-radius
floor, with its separate empty-prefix case, and every actual optimality radius
satisfies (13.1.32). The source constant retains the printed initial radius and
derivative maximum. The minimum of the initial radius powers is its qth power,
since all orders from one through q are tested and the radius is at most one. -/
theorem lemma_13_1_4 {n q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → EuclideanSpace ℝ (Fin n)}
    {Δ ρ : ℕ → ℝ} {ε : Fin q → ℝ} {accuracy : ℕ → ℕ → ℝ}
    {ζ θ κs κmax κh η₁ η₂ γ₁ γ₂ γ₃ Δmax L : ℝ} {N k : ℕ}
    (h : idaModelTrace f A T j x d s Δ ρ ε accuracy
      ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L) (hκh : 0 ≤ κh)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hkN : k ≤ N) :
    let κΔ := InexactTrustRegion.radiusConstant f h.order_pos (x 0)
      θ (Δ 0) γ₁ η₂ L κs κmax κh
    (if hk : (InexactTrustRegion.trialPrefix T k).Nonempty then
      min (γ₁ * θ) (κΔ * InexactTrustRegion.prefixGapOfNonempty A T j Δ d θ k hk)
      else γ₁ * θ) ≤ Δ k ∧
    ζ * (κΔ / 2) * InexactTrustRegion.minimumAccuracy h.order_pos ε ≤
      InexactTrustRegion.optimalityRadius θ (Δ k) := by
  classical
  dsimp only
  have hκ := InexactTrustRegion.radiusConstant_bounds (L := L) f h.order_pos (x 0)
    h.cap_pos.le h.cap_le_one h.updates.initial_pos.le h.updates.gamma1_pos.le
    h.updates.eta2_lt_one.le (by linarith : 0 ≤ L) h.request_factor_nonneg
    h.oracle_constant_nonneg hκh
  refine ⟨?_, h.optimalityRadius_lower hf hL hlip hκ.2 hkN⟩
  split_ifs with hk
  · exact h.prefix_radius_lower hf hL hlip hκ.2 hkN hk
  · exact h.radius_lower_of_no_trials hkN hk

end CartisGouldToint

namespace CartisGouldToint

/-- The oracle constants and primitive request-reduction settings for ARqpIDA. -/
abbrev idaRegularizationOracleSettings (p : ℕ) := InexactRegularization.OracleSettings p

/-- The actual inexact model/oracle/acceptance/update components of ARqpIDA.
The accuracy request is checked on short steps only; accuracy-only steps preserve
both the point and the regularization parameter. This is not a full stopping trace. -/
abbrev idaRegularizationModelTrace {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (O : idaRegularizationOracleSettings p)
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (T : Set ℕ)
    (x d s : ℕ → EuclideanSpace ℝ (Fin n)) (accuracy : ℕ → ℕ → ℝ) (σ ρ :
      ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
  InexactRegularization.ModelTrace f p O A T x d s accuracy σ ρ η₁ η₂ γ₁ γ₂
    γ₃ σmin N

/-- **Corrected Lemma 13.1.14.** With the literal short-step accuracy guard,
the uniform parameter constant uses `max(κs,κh)`. The cap `κh` is derived from
initial requests and actual multiplicative accuracy reductions. The printed
coefficient omits this necessary large-step contribution.

The final Step 2 index range is repaired from `1:q` to `1:p`, as explicitly
required by the referenced equation (13.1.46). All `p` derivative errors enter
the computed polynomial. The short-step guard itself is retained. -/
theorem lemma_13_1_14_corrected {n p N : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : idaRegularizationOracleSettings p}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ} {T : Set ℕ}
    {x d s : ℕ → EuclideanSpace ℝ (Fin n)} {accuracy : ℕ → ℕ → ℝ} {σ ρ :
      ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ}
    (h : idaRegularizationModelTrace f p O A T x d s accuracy σ ρ
      η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖) :
    ∀ k ≤ N, σ k ≤ max (σ 0) (γ₃ *
      (2 * L + 4 * ((p + 1).factorial : ℝ) *
        max O.stepCoefficient O.initialCap * O.errorBound) / (1 - η₂)) :=
  fun _ hk => h.parameter_le hf (zero_le_one.trans hL) hlip hk

/-- The printed coefficient in Lemma 13.1.14 is valid under the explicit
additional condition `κh≤κs`. This condition is absent from Algorithm 13.1.2. -/
theorem lemma_13_1_14_of_cap_le {n p N : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : idaRegularizationOracleSettings p}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ} {T : Set ℕ}
    {x d s : ℕ → EuclideanSpace ℝ (Fin n)} {accuracy : ℕ → ℕ → ℝ} {σ ρ :
      ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ}
    (h : idaRegularizationModelTrace f p O A T x d s accuracy σ ρ
      η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hcap : O.initialCap ≤ O.stepCoefficient) :
    ∀ k ≤ N, σ k ≤ max (σ 0) (γ₃ *
      (2 * L + 4 * ((p + 1).factorial : ℝ) *
        O.stepCoefficient * O.errorBound) / (1 - η₂)) :=
  fun _ hk => h.parameter_le_of_cap_le hf (zero_le_one.trans hL) hlip hcap hk

open InexactRegularization InexactRegularization.Counterexample in
/-- One actual guarded-accuracy trial for the zero objective takes the exact
computed-model minimizer `125/4`, rejects it with ratio zero, and raises the
parameter from 32 to 64. All source Lipschitz conditions, the Step 1 maximization
and both reference tests hold, while the printed upper bound is 60. -/
theorem arqpidaPrintedBoundCounterexample :
    ModelTrace (fun _ : ℝ => 0) 1 settings (fun _ => data) Set.univ
      (fun _ => 0) (fun _ => 1) (fun _ => 125 / 4) (fun _ _ => 1000)
      parameter (fun _ => 0) (1 / 4) (1 / 2) (1 / 2) 2 3 1 1 ∧
    ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ j ≤ 1, ∀ x y : ℝ,
      ‖iteratedFDeriv ℝ j (fun _ : ℝ => (0 : ℝ)) x -
        iteratedFDeriv ℝ j (fun _ : ℝ => (0 : ℝ)) y‖ ≤ ‖x - y‖) ∧
    (‖(1 : ℝ)‖ ≤ 1 ∧ ∀ t : ℝ, ‖t‖ ≤ 1 →
      TaylorModel.jetDecrement data 1 t ≤ TaylorModel.jetDecrement data 1 1) ∧
    ((1 : ℝ) / 4 < TaylorModel.jetDecrement data 1 1 ∧
      (1 : ℝ) / 8 ≤ model data 1 (parameter 0) 0 - model data 1 (parameter 0) 1) ∧
    (∀ t : ℝ, model data 1 32 (125 / 4) ≤ model data 1 32 t) ∧
    max (parameter 0)
      (3 * (2 * (1 : ℝ) + 4 * ((1 + 1 : ℕ).factorial : ℝ) *
        settings.stepCoefficient * settings.errorBound) / (1 - 1 / 2)) < parameter 1 :=
  ⟨trace,smoothness.1,smoothness.2,reference_maximizes,reference_tests,
    step_minimizes,printed_bound_violated⟩

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion

/-- Actual point updates added to the primitive IDA model, oracle and radius trace. -/
abbrev idaExecutionTrace {n q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (x d s : ℕ → EuclideanSpace ℝ (Fin n))
    (Δ ρ : ℕ → ℝ) (ε : Fin q → ℝ) (accuracy : ℕ → ℕ → ℝ)
    (ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax : ℝ) (N : ℕ) : Prop :=
  ExecutionTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax η₁ η₂ γ₁ γ₂
    γ₃ Δmax N

/-- Lemma 13.1.5: the selected actual computed model and derived radius floor
give (13.1.34), and accepted actual point updates give (13.1.35). The latter
retains the source's factor one half, which is also used by the EDA variant. -/
theorem lemma_13_1_5 {n q N k : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → EuclideanSpace ℝ (Fin n)}
    {Δ ρ : ℕ → ℝ} {ε : Fin q → ℝ} {accuracy : ℕ → ℕ → ℝ}
    {ζ θ κs κmax κh η₁ η₂ γ₁ γ₂ γ₃ Δmax L : ℝ}
    (h : idaExecutionTrace f A T j x d s Δ ρ ε accuracy
      ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L) (hκh : 0 ≤ κh)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hk : k < N) (hT : k ∈ T) :
    let κδ := radiusConstant f h.order_pos (x 0) θ (Δ 0) γ₁ η₂ L κs κmax κh / 2
    let μ := minimumAccuracy h.order_pos ε
    (ζ * κδ) ^ (q + 1) / q.factorial * μ ^ (q + 1) ≤
      decrement (A k) (modelOrder (j k)) (s k) ∧
    (η₁ ≤ ρ k → η₁ * (ζ * κδ) ^ (q + 1) / (2 * (q.factorial : ℝ)) *
      μ ^ (q + 1) ≤ f (x k) - f (x (k + 1))) := by
  have hb := radiusConstant_bounds (L := L) f h.order_pos (x 0)
    h.cap_pos.le h.cap_le_one h.updates.initial_pos.le h.updates.gamma1_pos.le
    h.updates.eta2_lt_one.le (by linarith : 0 ≤ L) h.request_factor_nonneg
    h.oracle_constant_nonneg hκh
  have hb1 := h.toModelTrace.radiusCoefficient_le_one hL hb.2
  exact ⟨h.toModelTrace.model_decrease hf hL hlip hb.1 hb1 hb.2 hk.le hT,
    fun ha => h.function_decrease hf hL hlip hb.1 hb1 hb.2 hk hT ha⟩

/-- Lemma 13.1.6: at any genuine Step 2 candidate, the source uniform request
threshold makes every derivative-accuracy check pass. The selected failed test
and actual model comparison are the primitive Step 1–2 operations; the trial
length lower bound is proved from the actual tensor norms. -/
theorem lemma_13_1_6 {n q N k : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → EuclideanSpace ℝ (Fin n)}
    {Δ ρ : ℕ → ℝ} {ε : Fin q → ℝ} {accuracy : ℕ → ℕ → ℝ}
    {ζ θ κs κmax κh η₁ η₂ γ₁ γ₂ γ₃ Δmax L H : ℝ}
    (h : idaModelTrace f A T j x d s Δ ρ ε accuracy
      ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L) (hκh : 0 ≤ κh)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hk : k ≤ N) (haccuracy : ∀ a, 1 ≤ a → a ≤ q → accuracy k a ≤ κh)
    (horacle : ∀ a, 1 ≤ a → a ≤ q →
      ‖A k a - iteratedFDeriv ℝ a f (x k)‖ ≤ κmax * accuracy k a)
    (hH : ∀ a, 1 ≤ a → a ≤ q → accuracy k a ≤ H)
    (hfailed : ζ / 2 * ε (j k) * optimalityRadius θ (Δ k) ^ modelOrder (j k) /
      (modelOrder (j k)).factorial < decrement (A k) (modelOrder (j k)) (d k))
    (hcomparison : TaylorModel.ofJet (A k) (modelOrder (j k)) (s k) ≤
      TaylorModel.ofJet (A k) (modelOrder (j k)) (d k))
    (hsmall : H ≤ κs *
      (ζ ^ (q + 1) *
        (radiusConstant f h.order_pos (x 0) θ (Δ 0) γ₁ η₂ L κs κmax κh / 2) ^ q /
        (4 * (q.factorial : ℝ) * (L + κmax * κh))) ^ q *
      minimumAccuracy h.order_pos ε ^ (q * (q + 1))) :
    ∀ a, 1 ≤ a → a ≤ q → accuracy k a ≤ κs * ‖s k‖ ^ (q - a + 1) := by
  let κ := radiusConstant f h.order_pos (x 0) θ (Δ 0) γ₁ η₂ L κs κmax κh
  let μ := minimumAccuracy h.order_pos ε
  let M := L + κmax * κh
  have hb := radiusConstant_bounds (L := L) f h.order_pos (x 0)
    h.cap_pos.le h.cap_le_one h.updates.initial_pos.le h.updates.gamma1_pos.le
    h.updates.eta2_lt_one.le (by linarith : 0 ≤ L) h.request_factor_nonneg
    h.oracle_constant_nonneg hκh
  have hb1 := h.radiusCoefficient_le_one hL hb.2
  have hμ := (minimumAccuracy_pos h.order_pos h.accuracy_pos).le
  have hμ1 : μ ≤ 1 := (minimumAccuracy_le h.order_pos ε (j k)).trans (h.accuracy_le_one _)
  have hκ0 : 0 ≤ κ := hb.1
  have hκhalf0 : 0 ≤ κ / 2 := div_nonneg hκ0 (by norm_num)
  change 0 ≤ μ at hμ
  have hM : 1 ≤ M := hL.trans (le_add_of_nonneg_right
    (mul_nonneg h.oracle_constant_nonneg hκh))
  have hA : ∀ a, 1 ≤ a → a ≤ modelOrder (j k) → ‖A k a‖ ≤ M := by
    intro a ha haj
    exact TaylorModel.norm_jet_le_of_lipschitz_oracle (by linarith) hκh
      (fun b hb => hlip b (by omega)) (A k) (x k) (fun _ => κmax) (accuracy k)
      (fun _ _ _ => ⟨h.oracle_constant_nonneg, le_rfl⟩) haccuracy horacle ha
      (haj.trans (j k).isLt)
  have htest : ζ / 2 * μ * optimalityRadius θ (Δ k) ^ modelOrder (j k) /
      (modelOrder (j k)).factorial ≤ decrement (A k) (modelOrder (j k)) (s k) := by
    have he := mul_le_mul_of_nonneg_right
      (minimumAccuracy_le h.order_pos ε (j k))
      (show 0 ≤ ζ / 2 * optimalityRadius θ (Δ k) ^ modelOrder (j k) /
        (modelOrder (j k)).factorial by
          have hδ := le_min h.cap_pos.le (h.updates.pos hk).le
          have hz := h.zeta_pos
          positivity)
    have hc := sub_le_sub_left hcomparison (TaylorModel.ofJet (A k) (modelOrder (j k)) 0)
    have he' : ζ / 2 * μ * optimalityRadius θ (Δ k) ^ modelOrder (j k) /
        (modelOrder (j k)).factorial ≤
        ζ / 2 * ε (j k) * optimalityRadius θ (Δ k) ^ modelOrder (j k) /
        (modelOrder (j k)).factorial := by convert he using 1 <;> ring
    exact he'.trans (hfailed.le.trans hc)
  have hstep := norm_step_ge_of_failed_test (A k) (j k).isLt h.zeta_pos.le
    h.zeta_le_one hκhalf0 (by dsimp [κ]; linarith)
    hM hμ hμ1 (h.optimalityRadius_lower hf hL (fun a _ ha => hlip a ha) hb.2 hk)
    (s k) hA htest
  have hc : 0 ≤ accuracyThreshold q ζ (κ / 2) M μ := by
    unfold accuracyThreshold
    have hz := h.zeta_pos
    have hM0 : 0 ≤ M := by linarith
    positivity
  have hc1 := accuracyThreshold_le_one (q := q) h.zeta_pos.le h.zeta_le_one
    hκhalf0 (by dsimp [κ]; linarith) hM hμ hμ1
  apply requests_of_norm_floor hc hc1 h.request_factor_nonneg _ (accuracy k) hH (s k) hstep
  convert hsmall using 1
  unfold accuracyThreshold
  rw [mul_pow, ← pow_mul]
  simp only [Nat.mul_comm (q + 1) q]
  dsimp [κ, M, μ]
  ring

/-- Lemma 13.1.7: the source uniform accuracy threshold makes the all-order
passing computed Step 1 loop certify true approximate optimality. The explicit
finite tensor-error budget is derived, not assumed. -/
theorem lemma_13_1_7 {n q N k : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → EuclideanSpace ℝ (Fin n)}
    {Δ ρ : ℕ → ℝ} {ε : Fin q → ℝ} {accuracy : ℕ → ℕ → ℝ}
    {ζ θ κs κmax κh η₁ η₂ γ₁ γ₂ γ₃ Δmax L H : ℝ}
    (h : idaModelTrace f A T j x d s Δ ρ ε accuracy
      ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L) (hκh : 0 ≤ κh)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hk : k ≤ N) (hH0 : 0 ≤ H)
    (hH : ∀ a, 1 ≤ a → a ≤ q → accuracy k a ≤ H)
    (horacle : ∀ a, 1 ≤ a → a ≤ q →
      ‖A k a - iteratedFDeriv ℝ a f (x k)‖ ≤ κmax * accuracy k a)
    (direction : Fin q → EuclideanSpace ℝ (Fin n))
    (happrox : ∀ a, ζ * TaylorModel.jetCriticality (A k) (modelOrder a)
      (optimalityRadius θ (Δ k)) ≤ TaylorModel.jetDecrement (A k) (modelOrder a) (direction a))
    (hpass : ∀ a, TaylorModel.jetDecrement (A k) (modelOrder a) (direction a) ≤
      ζ / 2 * ε a * optimalityRadius θ (Δ k) ^ modelOrder a / (modelOrder a).factorial)
    (hsmall : H ≤ accuracyThreshold q ζ
      (radiusConstant f h.order_pos (x 0) θ (Δ 0) γ₁ η₂ L κs κmax κh / 2)
      κmax (minimumAccuracy h.order_pos ε)) :
    ∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (x k)
      (optimalityRadius θ (Δ k)) ≤
      ε a * optimalityRadius θ (Δ k) ^ modelOrder a / (modelOrder a).factorial := by
  by_cases hzero : κmax = 0
  · have hδ := le_min h.cap_pos.le (h.updates.pos hk).le
    have hζ := h.zeta_pos
    have hμ := minimumAccuracy_pos h.order_pos h.accuracy_pos
    have hh : TerminationCheck (A k) (optimalityRadius θ (Δ k)) ζ ε direction
        (fun _ => 0) := by
      refine ⟨h.order_pos, hδ, (min_le_left θ (Δ k)).trans h.cap_le_one,
        h.zeta_pos, h.zeta_le_one, h.accuracy_pos, happrox, hpass, ?_⟩
      simp only [tensorErrorBudget, zero_mul, zero_div, Finset.sum_const_zero]
      positivity
    exact hh.true_optimality f (x k) (by simpa only [hzero, zero_mul] using horacle)
  have hκmax : 0 < κmax := lt_of_le_of_ne h.oracle_constant_nonneg (Ne.symm hzero)
  have hb := radiusConstant_bounds (L := L) f h.order_pos (x 0)
    h.cap_pos.le h.cap_le_one h.updates.initial_pos.le h.updates.gamma1_pos.le
    h.updates.eta2_lt_one.le (by linarith : 0 ≤ L) h.request_factor_nonneg
    h.oracle_constant_nonneg hκh
  have hh := terminationCheck_of_accuracyThreshold h.order_pos
    (le_min h.cap_pos.le (h.updates.pos hk).le) ((min_le_left _ _).trans h.cap_le_one)
    h.zeta_pos h.zeta_le_one (div_nonneg hb.1 (by norm_num)) hκmax hH0 h.accuracy_pos rfl
    (h.optimalityRadius_lower hf hL hlip hb.2 hk) hsmall hH happrox hpass
  exact hh.true_optimality f (x k) horacle

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion

/-- Accuracy-independent settings of the actual TRqIDA algorithm. -/
abbrev trqidaSettings (q : ℕ) := InexactTrustRegion.Settings q

/-- Actual TRqIDA execution, including computed selection, primitive tensor
oracles, actual function ratios and point/radius updates, both concrete accuracy
branches, geometric request reductions and rejected-step derivative reuse. -/
abbrev trqidaRun {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : trqidaSettings q) (ε : Fin q → ℝ)
    (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (x d s : ℕ → EuclideanSpace ℝ (Fin n))
    (Δ ρ : ℕ → ℝ) (accuracy : ℕ → ℕ → ℝ) (N : ℕ) : Prop :=
  InexactTrustRegion.Run f P ε A T j x d s Δ ρ accuracy N

/-- Theorem 13.1.8: all five positive complexity coefficients are fixed before
every admissible accuracy request. An actual TRqIDA execution reaches a first
true all-order approximate minimizer within the objective and derivative budgets,
even though the implicit-accuracy algorithm cannot observe that fact.

Both counters include initialization; the derivative additive coefficient also
covers the final threshold-crossing accuracy reduction. A positive fixed radius
coefficient covers a vanishing initial jet and exact tensor oracles. In the
printed conclusion the criticality order `q` is repaired to the tested order `j`.
The initialization typo `1<γ₂` is corrected to the contraction range `γ₂<1`
required by its actual radius updates and logarithmic counting argument. -/
theorem theorem_13_1_8 {n q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : trqidaSettings q)
    (x₀ : EuclideanSpace ℝ (Fin n))
    {Δ₀ L flow : ℝ} (hL : 1 ≤ L) (hf : ContDiff ℝ q f)
    (hlip : ∀ a, a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ κA > 0, ∃ κB > 0, ∃ κC > 0, ∃ κE > 0, ∃ κF > 0,
      ∀ (ε : Fin q → ℝ) (A : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace
        ℝ (Fin n)) ℝ) (T : Set ℕ)
        (j : ℕ → Fin q) (x d s : ℕ → EuclideanSpace ℝ (Fin n)) (Δ ρ : ℕ →
          ℝ) (accuracy : ℕ → ℕ → ℝ),
      x 0 = x₀ → Δ 0 = Δ₀ →
      (∀ N, (∀ i < N, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) →
        trqidaRun f P ε A T j x d s Δ ρ accuracy N) →
      ∃ K, optimalityRadius P.theta (Δ K) ∈ Set.Ioc 0 1 ∧
        (∀ a : Fin q, TaylorModel.criticality f (modelOrder a) (x K)
          (optimalityRadius P.theta (Δ K)) ≤
          ε a * optimalityRadius P.theta (Δ K) ^ modelOrder a / (modelOrder a).factorial) ∧
        trqidaRun f P ε A T j x d s Δ ρ accuracy K ∧
        (∀ i < K, NotOptimal f ε (x i) (optimalityRadius P.theta (Δ i))) ∧
        (functionEvaluations T K : ℝ) ≤
          κA * (f x₀ - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
          κB * |Real.log (minimumAccuracy P.order_pos ε)| + κC ∧
        (derivativeEvaluations T ρ P.eta1 K : ℝ) ≤
          κA * (f x₀ - flow) / minimumAccuracy P.order_pos ε ^ (q + 1) +
          κE * |Real.log (minimumAccuracy P.order_pos ε)| + κF :=
  InexactTrustRegion.evaluation_complexity (Δ₀ := Δ₀) f P x₀ hL hf hlip hlow

end CartisGouldToint
