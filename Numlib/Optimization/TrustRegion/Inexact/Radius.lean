import Numlib.Optimization.TrustRegion.Inexact.Acceptance
import Numlib.Optimization.TrustRegion.HighOrder.Radius
import Numlib.Optimization.EvaluationComplexity.TrialRadius

/-!
# Radius floors for implicit dynamic accuracy

The computed selection, primitive tensor errors, requested accuracies, actual
objective ratios and permitted radius updates imply the source radius floors.
The cap in the radius floor gives the initial induction step directly; no bound
on an initial scaled model gap is assumed.
-/

namespace InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The minimum computed scaled gap over a nonempty inclusive trial prefix. -/
noncomputable def prefixGapOfNonempty {q : ℕ}
    (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ) (j : ℕ → Fin q)
    (Δ : ℕ → ℝ) (d : ℕ → E) (θ : ℝ) (k : ℕ) (hk : (trialPrefix T k).Nonempty) : ℝ :=
  (trialPrefix T k).inf' hk (scaledGap A j Δ d θ)

/-- Every trial gap in a nonempty inclusive prefix is at least its finite minimum. -/
theorem prefixGapOfNonempty_le {q : ℕ} (A : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (Δ : ℕ → ℝ) (d : ℕ → E) (θ : ℝ) (k : ℕ)
    (hk : (trialPrefix T k).Nonempty) {i : ℕ} (hi : i ≤ k) (hT : i ∈ T) :
    prefixGapOfNonempty A T j Δ d θ k hk ≤ scaledGap A j Δ d θ i :=
  Finset.inf'_le _ (mem_trialPrefix.mpr ⟨hi, hT⟩)

/-- A trial endpoint gives the same minimum as the original endpoint-based API. -/
@[simp] theorem prefixGapOfNonempty_eq {q : ℕ} (A : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (Δ : ℕ → ℝ) (d : ℕ → E) (θ : ℝ) (k : ℕ) (hk : k ∈ T) :
    prefixGapOfNonempty A T j Δ d θ k (trialPrefix_nonempty hk) =
      prefixGap A T j Δ d θ k hk := rfl

/-- Among all positive orders through q, the smallest power of a unit radius
is its qth power, exactly as in the initial source constant. -/
theorem minimumRadiusPower_eq {q : ℕ} (hq : 0 < q) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    minimumAccuracy hq (fun a : Fin q => δ ^ modelOrder a) = δ ^ q := by
  apply le_antisymm
  · let a : Fin q := ⟨q - 1, by omega⟩
    have ha : modelOrder a = q := by dsimp [modelOrder, a]; omega
    simpa only [ha] using minimumAccuracy_le hq (fun a : Fin q => δ ^ modelOrder a) a
  · apply Finset.le_inf'
    intro a _
    exact pow_le_pow_of_le_one hδ hδ1 a.isLt

/-- The source radius constant, retaining its initial derivative maximum and radius factor. -/
noncomputable def radiusConstant {q : ℕ} (f : E → ℝ) (hq : 0 < q) (x₀ : E)
    (θ Δ₀ γ₁ η₂ L κs κmax κh : ℝ) : ℝ :=
  min 1 (γ₁ * (1 - η₂) / acceptanceCoefficient q L (κs * κmax)) *
    min θ (Δ₀ * (optimalityRadius θ Δ₀) ^ q /
      (2 * (q : ℝ) * (HighOrderTrustRegion.initialDerivativeBound f q hq x₀ + κmax * κh)))

/-- The source constant is nonnegative and no larger than the small-radius factor.
Its initial derivative denominator may vanish; the cap still gives these bounds. -/
theorem radiusConstant_bounds {q : ℕ} (f : E → ℝ) (hq : 0 < q) (x₀ : E)
    {θ Δ₀ γ₁ η₂ L κs κmax κh : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hΔ₀ : 0 ≤ Δ₀) (hγ : 0 ≤ γ₁)
    (hη : η₂ ≤ 1) (hL : 0 ≤ L) (hκs : 0 ≤ κs) (hκmax : 0 ≤ κmax) (hκh : 0 ≤ κh) :
    0 ≤ radiusConstant f hq x₀ θ Δ₀ γ₁ η₂ L κs κmax κh ∧
      radiusConstant f hq x₀ θ Δ₀ γ₁ η₂ L κs κmax κh ≤
        γ₁ * ((1 - η₂) / acceptanceCoefficient q L (κs * κmax)) := by
  have hB := HighOrderTrustRegion.initialDerivativeBound_nonneg f hq x₀
  have hC : 0 ≤ acceptanceCoefficient q L (κs * κmax) := by
    dsimp [acceptanceCoefficient]
    positivity
  have ha : 0 ≤ min 1 (γ₁ * (1 - η₂) / acceptanceCoefficient q L (κs * κmax)) :=
    le_min (by norm_num) (div_nonneg (mul_nonneg hγ (sub_nonneg.mpr hη)) hC)
  have hb : 0 ≤ min θ (Δ₀ * optimalityRadius θ Δ₀ ^ q /
      (2 * (q : ℝ) * (HighOrderTrustRegion.initialDerivativeBound f q hq x₀ + κmax * κh))) := by
    apply le_min hθ
    exact div_nonneg (mul_nonneg hΔ₀ (pow_nonneg (le_min hθ hΔ₀) _)) (by positivity)
  refine ⟨mul_nonneg ha hb, ?_⟩
  unfold radiusConstant
  calc _ ≤ min 1 (γ₁ * (1 - η₂) / acceptanceCoefficient q L (κs * κmax)) * 1 :=
        mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hθ1) ha
    _ = min 1 (γ₁ * (1 - η₂) / acceptanceCoefficient q L (κs * κmax)) := mul_one _
    _ ≤ γ₁ * (1 - η₂) / acceptanceCoefficient q L (κs * κmax) := min_le_right _ _
    _ = _ := by ring

/-- Every nonempty trial prefix retains the failed-test lower bound. -/
theorem SelectedTrials.prefixGapOfNonempty_lower {q : ℕ}
    {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ} {j : ℕ → Fin q}
    {Δ : ℕ → ℝ} {d s : ℕ → E} {ε : Fin q → ℝ} {ζ θ : ℝ}
    (h : SelectedTrials A T j Δ d s ε ζ θ) (k : ℕ) (hk : (trialPrefix T k).Nonempty) :
    ζ / 2 * minimumAccuracy h.order_pos ε ≤ prefixGapOfNonempty A T j Δ d θ k hk := by
  apply Finset.le_inf'
  intro i hi
  exact h.scaledGap_lower (mem_trialPrefix.mp hi).2

/-- Primitive model, derivative-oracle, requested-accuracy, ratio and update components
needed for the TRqIDA radius analysis. Whole-program termination is not a field. -/
structure ModelTrace {q : ℕ} (f : E → ℝ)
    (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ) (j : ℕ → Fin q)
    (x d s : ℕ → E) (Δ ρ : ℕ → ℝ) (ε : Fin q → ℝ) (accuracy : ℕ → ℕ → ℝ)
    (ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax : ℝ) (N : ℕ) : Prop
    extends SelectedTrials A T j Δ d s ε ζ θ where
  updates : EvaluationComplexity.TrialTrustRegionUpdates T Δ ρ η₁ η₂ γ₁ γ₂ γ₃ Δmax N
  initial_cap : θ ≤ Δ 0
  cap_accuracy : minimumAccuracy order_pos ε ≤ θ
  request_factor_nonneg : 0 ≤ κs
  oracle_constant_nonneg : 0 ≤ κmax
  oracle : ∀ i < N, i ∈ T → ∀ a, 1 ≤ a → a ≤ q →
    ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ κmax * accuracy i a
  requests : ∀ i < N, i ∈ T → ∀ a, 1 ≤ a → a ≤ q →
    accuracy i a ≤ κs * ‖s i‖ ^ (q - a + 1)
  exact_constant : ∀ i < N, i ∈ T → A i 0 (fun _ => 0) = f (x i)
  ratio : ∀ i < N, i ∈ T →
    ρ i = (f (x i) - f (x i + s i)) / decrement (A i) (modelOrder (j i)) (s i)

namespace ModelTrace
variable {q : ℕ} {f : E → ℝ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {T : Set ℕ} {j : ℕ → Fin q} {x d s : ℕ → E} {Δ ρ : ℕ → ℝ} {ε : Fin q → ℝ}
  {ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax L : ℝ} {N : ℕ} {accuracy : ℕ → ℕ → ℝ}

/-- Every shorter prefix retains the same actual model and oracle rules. -/
theorem restrict (h : ModelTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax
    η₁ η₂ γ₁ γ₂ γ₃ Δmax N) {M : ℕ} (hM : M ≤ N) :
    ModelTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax M :=
  { h with
    updates := h.updates.restrict hM
    oracle := fun i hi => h.oracle i (hi.trans_le hM)
    requests := fun i hi => h.requests i (hi.trans_le hM)
    exact_constant := fun i hi => h.exact_constant i (hi.trans_le hM)
    ratio := fun i hi => h.ratio i (hi.trans_le hM) }

/-- Primitive oracle and request bounds give the actual tensor-error estimate. -/
theorem tensor_error (h : ModelTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    {i : ℕ} (hi : i < N) (hT : i ∈ T) {a : ℕ} (ha : 1 ≤ a) (haq : a ≤ q) :
    ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ (κs * κmax) * ‖s i‖ ^ (q - a + 1) := by
  calc _ ≤ κmax * accuracy i a := h.oracle i hi hT a ha haq
    _ ≤ κmax * (κs * ‖s i‖ ^ (q - a + 1)) :=
      mul_le_mul_of_nonneg_left (h.requests i hi hT a ha haq) h.oracle_constant_nonneg
    _ = _ := by ring

/-- Small-radius acceptance follows from actual smoothness and tensor accuracy. -/
theorem very_successful
    (h : ModelTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {i : ℕ} (hi : i < N) (hT : i ∈ T)
    (hsmall : Δ i ≤ min θ ((1 - η₂) / acceptanceCoefficient q L (κs * κmax) *
      scaledGap A j Δ d θ i)) : η₂ ≤ ρ i := by
  rw [h.ratio i hi hT]
  exact h.toSelectedTrials.very_successful hf hL
    (mul_nonneg h.request_factor_nonneg h.oracle_constant_nonneg) h.updates.eta2_lt_one
    hlip x hT (h.exact_constant i hi hT)
    (fun a ha haj => h.tensor_error hi hT ha (haj.trans (j i).isLt)) hsmall

/-- Any valid scaled gap floor gives the corresponding radius floor throughout the run. -/
theorem radius_floor (h : ModelTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {κ μ : ℝ} (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L (κs * κmax)))
    (hμ : 0 ≤ μ) (hgap : ∀ i < N, i ∈ T → μ ≤ scaledGap A j Δ d θ i)
    {k : ℕ} (hk : k ≤ N) : min (γ₁ * θ) (κ * μ) ≤ Δ k := by
  have hK := mul_nonneg h.request_factor_nonneg h.oracle_constant_nonneg
  apply h.updates.min_cap_scaled_gap_le h.cap_pos.le h.initial_cap
    (div_nonneg (by linarith [h.updates.eta2_lt_one]) (by
      dsimp [acceptanceCoefficient]; positivity)) hκ hμ (scaledGap A j Δ d θ) hgap
    (fun i hi hT hh => h.very_successful hf hL hlip hi hT hh) hk

/-- The inclusive prefix minimum gives the actual radius bound (13.1.30). -/
theorem prefix_radius_lower
    (h : ModelTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {κ : ℝ} (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L (κs * κmax)))
    {k : ℕ} (hkN : k ≤ N) (hk : (trialPrefix T k).Nonempty) :
    min (γ₁ * θ) (κ * prefixGapOfNonempty A T j Δ d θ k hk) ≤ Δ k := by
  have hμ : 0 ≤ prefixGapOfNonempty A T j Δ d θ k hk :=
    (mul_nonneg (div_nonneg h.zeta_pos.le (by norm_num))
      (minimumAccuracy_pos h.order_pos h.accuracy_pos).le).trans
        (h.toSelectedTrials.prefixGapOfNonempty_lower k hk)
  exact (h.restrict hkN).radius_floor hf hL hlip hκ hμ
    (fun i hi hT => prefixGapOfNonempty_le A T j Δ d θ k hk hi.le hT) le_rfl

/-- A prefix without trials retains the initial radius, which is above the source cap floor. -/
theorem radius_lower_of_no_trials
    (h : ModelTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    {k : ℕ} (hkN : k ≤ N) (hk : ¬ (trialPrefix T k).Nonempty) : γ₁ * θ ≤ Δ k := by
  have heq : Δ k = Δ 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [h.updates.inactive_eq (by omega) (by
        intro hT
        exact hk ⟨k, mem_trialPrefix.mpr ⟨by omega, hT⟩⟩)]
      exact ih (by omega) (by
        intro hh
        obtain ⟨i, hi⟩ := hh
        exact hk ⟨i, mem_trialPrefix.mpr ⟨(mem_trialPrefix.mp hi).1.trans (by omega),
          (mem_trialPrefix.mp hi).2⟩⟩)
  rw [heq]
  exact (mul_le_of_le_one_left h.cap_pos.le
    (h.updates.gamma1_le_gamma2.trans h.updates.gamma2_lt_one.le)).trans h.initial_cap

/-- The actual optimality radius has a uniform accuracy-dependent floor. -/
theorem optimalityRadius_lower
    (h : ModelTrace f A T j x d s Δ ρ ε accuracy ζ θ κs κmax η₁ η₂ γ₁ γ₂ γ₃ Δmax N)
    (hf : ContDiff ℝ q f) (hL : 1 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a ≤ q → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {κ : ℝ} (hκ : κ ≤ γ₁ * ((1 - η₂) / acceptanceCoefficient q L (κs * κmax)))
    {k : ℕ} (hkN : k ≤ N) :
    ζ * (κ / 2) * minimumAccuracy h.order_pos ε ≤ optimalityRadius θ (Δ k) := by
  have hK := mul_nonneg h.request_factor_nonneg h.oracle_constant_nonneg
  have hC : 1 ≤ acceptanceCoefficient q L (κs * κmax) := by
    dsimp [acceptanceCoefficient]
    have hh : 0 ≤ 4 * ((q + 1).factorial : ℝ) * (κs * κmax) := by positivity
    linarith
  have hη0 : 0 ≤ η₂ := h.updates.eta1_pos.le.trans h.updates.eta1_le_eta2
  have hc : (1 - η₂) / acceptanceCoefficient q L (κs * κmax) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hκγ : κ ≤ γ₁ := hκ.trans (mul_le_of_le_one_right h.updates.gamma1_pos.le hc)
  have hμ := minimumAccuracy_pos h.order_pos h.accuracy_pos
  have hγ1 : γ₁ ≤ 1 := h.updates.gamma1_le_gamma2.trans h.updates.gamma2_lt_one.le
  have hsmall : ζ * (κ / 2) * minimumAccuracy h.order_pos ε ≤ γ₁ * θ := by
    calc _ = κ * (ζ / 2 * minimumAccuracy h.order_pos ε) := by ring
      _ ≤ γ₁ * minimumAccuracy h.order_pos ε := by
        apply mul_le_mul hκγ _
          (mul_nonneg (div_nonneg h.zeta_pos.le (by norm_num)) hμ.le)
          h.updates.gamma1_pos.le
        nlinarith [h.zeta_le_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left h.cap_accuracy h.updates.gamma1_pos.le
  apply le_min
  · exact hsmall.trans (mul_le_of_le_one_left h.cap_pos.le hγ1)
  · have hrad := h.radius_floor hf hL hlip hκ
      (mul_nonneg (div_nonneg h.zeta_pos.le (by norm_num)) hμ.le)
      (fun i _ hi => h.toSelectedTrials.scaledGap_lower hi) hkN
    have heq : κ * (ζ / 2 * minimumAccuracy h.order_pos ε) =
        ζ * (κ / 2) * minimumAccuracy h.order_pos ε := by ring
    rw [heq, min_eq_right hsmall] at hrad
    exact hrad

end ModelTrace
end InexactTrustRegion
