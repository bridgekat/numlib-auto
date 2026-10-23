import Numlib.Optimization.EvaluationComplexity.ParameterUpdates
import Numlib.Optimization.TrustRegion.FirstOrder

/-!
# Cartis–Gould–Toint, Section 2.3: trust-region iteration counts

Lemma 2.3.1 uses only the radius-update component (2.3.7) of TR1. The hypothesis
below spells out that component, including its parameter ranges, through
`TrustRegionRadiusUpdates`; model construction and step selection play no role.
Counts use `N` updates, with indices `i < N`. Thus the source's inclusive set
`S_k` is represented by `successfulIterations ρ η₁ (k + 1)`.
-/

namespace CartisGouldToint

/-- The successful iterations (2.3.9) in a prefix of `N` updates. This corresponds
to the inclusive prefix (2.3.10) with the endpoint index `N - 1` when `N > 0`. -/
noncomputable def successfulIterations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : Finset ℕ :=
  EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} N

/-- An index belongs to the successful prefix exactly when it lies in the prefix
and its acceptance ratio is at least the threshold. -/
@[simp]
theorem mem_successfulIterations {ρ : ℕ → ℝ} {η₁ : ℝ} {N i : ℕ} :
    i ∈ successfulIterations ρ η₁ N ↔ i < N ∧ η₁ ≤ ρ i :=
  EvaluationComplexity.mem_successfulIterations

/-- **Lemma 2.3.1.** The update rules of TR1 and a positive lower bound on the
current radius bound the number of updates by the number of successful ones.
The half-open prefix corrects the inclusive-prefix indexing shorthand in the
source proof: `N = |S| + |U|` counts exactly the updates from `Δ₀` to `Δ_N`. -/
theorem lemma_2_3_1 {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ Δmin : ℝ} {N : ℕ}
    (h : EvaluationComplexity.TrustRegionRadiusUpdates Δ ρ η₁ η₂ γ₁ γ₂ γ₃ N)
    (hminpos : 0 < Δmin) (hmin : Δmin ≤ Δ N) :
    (N : ℝ) ≤ (successfulIterations ρ η₁ N).card *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      |Real.log (Δmin / Δ 0)| / |Real.log γ₂| :=
  EvaluationComplexity.iteration_bound_of_parameter_lower (S := {i | η₁ ≤ ρ i})
    (fun _ hi => h.pos hi) (by linarith [h.one_lt_gamma3])
    (h.gamma1_pos.trans_le h.gamma1_le_gamma2) h.gamma2_lt_one hmin hminpos
    (fun _ hi hs => h.successful_le hi hs)
    (fun _ hi hu => h.unsuccessful_le hi hu)

/-- A Cauchy step minimizes the actual quadratic model along the feasible
negative-gradient ray, including the zero-gradient case. -/
abbrev cauchyPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f₀ : ℝ) (g : E) (B : E →L[ℝ] E) (Δ : ℝ) (s : E) : Prop :=
  QuadraticTrustRegion.IsCauchyPoint f₀ g B Δ s

/-- **Lemma 2.3.2.** The actual Cauchy minimizer gives the quadratic model
reduction (2.3.12). A positive trust-region radius and a nonzero gradient make
the acceptance-ratio denominator strictly positive for every permitted trial
step (2.3.4). Symmetry of `B` is unnecessary for this bound. -/
theorem lemma_2_3_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f₀ Δ : ℝ} {g sC s : E} {B : E →L[ℝ] E}
    (hΔ : 0 < Δ) (hc : cauchyPoint f₀ g B Δ sC)
    (hs : QuadraticTrustRegion.model f₀ g B s ≤
      QuadraticTrustRegion.model f₀ g B sC) :
    (1 / 2 : ℝ) * ‖g‖ * min (‖g‖ / (1 + ‖B‖)) Δ ≤
        QuadraticTrustRegion.model f₀ g B 0 - QuadraticTrustRegion.model f₀ g B sC ∧
      (g ≠ 0 → 0 < QuadraticTrustRegion.model f₀ g B 0 -
        QuadraticTrustRegion.model f₀ g B s) :=
  ⟨QuadraticTrustRegion.cauchy_decrease hΔ.le hc,
    fun hg => QuadraticTrustRegion.predicted_decrease_pos hΔ hg hc hs⟩

/-- A finite operational trace of TR1, with actual derivatives, model steps,
Cauchy minimizers, objective-based ratios and the three radius-update intervals. -/
abbrev tr1Run {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) (x s sC : ℕ → E) (B : ℕ → E →L[ℝ] E)
    (Δ ρ : ℕ → ℝ) (η₁ η₂ γ₁ γ₂ γ₃ ε : ℝ) (N : ℕ) : Prop :=
  FirstOrderTrustRegion.Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N

/-- **Lemma 2.3.3.** The small-radius condition (2.3.15) gives a very
successful trial, hence success and a nondecreasing radius. The source's
normalization `L ≥ 1` is explicit. -/
theorem lemma_2_3_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {x s sC : ℕ → E} {B : ℕ → E →L[ℝ] E}
    {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ ε L κB : ℝ} {N i : ℕ}
    (h : tr1Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ j < N, ‖B j‖ ≤ κB) (hi : i < N)
    (hsmall : Δ i < (1 - η₂) * ‖g (x i)‖ / (2 * (L + κB))) :
    η₂ ≤ ρ i ∧ η₁ ≤ ρ i ∧ Δ i ≤ Δ (i + 1) := by
  have hs := h.very_successful hL hLone hB hi hsmall
  exact ⟨hs, h.updates.eta1_le_eta2.trans hs,
    h.radius_le_next_of_very_successful hi hs⟩

/-- **Lemma 2.3.4.** The trust-region radius satisfies (2.3.17), with the
minimum taken on the inclusive prefix `0,…,N`. -/
theorem lemma_2_3_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {x s sC : ℕ → E} {B : ℕ → E →L[ℝ] E}
    {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ ε L κB : ℝ} {N : ℕ}
    (h : tr1Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) :
    (γ₁ * (1 - η₂) / (2 * (L + κB)) * min 1 (Δ 0 / ‖g (x 0)‖)) *
      FirstOrderTrustRegion.prefixMinimum (fun i => ‖g (x i)‖) N ≤ Δ N :=
  h.radius_lower_prefixMinimum hL hLone hB

/-- **Lemma 2.3.5.** Every permitted trial achieves (2.3.19), with the
explicit accuracy-independent model-decrease constant (2.3.20). -/
theorem lemma_2_3_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {x s sC : ℕ → E} {B : ℕ → E →L[ℝ] E}
    {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ ε L κB : ℝ} {N i : ℕ}
    (h : tr1Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ j, ‖B j‖ ≤ κB) (hi : i < N) :
    FirstOrderTrustRegion.decreaseConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB *
      ‖g (x i)‖ * FirstOrderTrustRegion.prefixMinimum (fun j => ‖g (x j)‖) i ≤
      QuadraticTrustRegion.model (f (x i)) (g (x i)) (B i) 0 -
        QuadraticTrustRegion.model (f (x i)) (g (x i)) (B i) (s i) :=
  h.model_decrease_prefixMinimum hL hLone hB hi

/-- The explicit successful-iteration constant; a zero initial gradient
terminates immediately, for which the harmless constant `1` suffices. -/
noncomputable def tr1SuccessfulConstant (g₀ Δ₀ η₁ η₂ γ₁ L κB : ℝ) : ℝ :=
  if g₀ = 0 then 1 else
    1 / (η₁ * FirstOrderTrustRegion.decreaseConstant g₀ Δ₀ η₂ γ₁ L κB)

/-- **Lemma 2.3.6.** Every nonterminated prefix has the stated successful
iteration budget. The constant is explicit and independent of `ε`; the initial
zero-gradient case has zero trials. -/
theorem lemma_2_3_6 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {x s sC : ℕ → E} {B : ℕ → E →L[ℝ] E}
    {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ ε L κB flow : ℝ} {N : ℕ}
    (h : tr1Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, κS = tr1SuccessfulConstant ‖g (x 0)‖ (Δ 0) η₁ η₂ γ₁ L κB ∧
      ((successfulIterations ρ η₁ N).card : ℝ) ≤ κS * (f (x 0) - flow) / ε ^ 2 := by
  have hε := h.accuracy_pos
  have hgap : 0 ≤ f (x 0) - flow := sub_nonneg.mpr (hlow _)
  by_cases hg0 : ‖g (x 0)‖ = 0
  · have hN : N = 0 := by
      by_contra hN
      have ht := h.not_terminated 0 (by omega)
      rw [hg0] at ht
      linarith
    refine ⟨1, zero_lt_one, by simp [tr1SuccessfulConstant, hg0], ?_⟩
    simp only [hN, successfulIterations, EvaluationComplexity.successfulIterations,
      Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  · have hgp : 0 < ‖g (x 0)‖ := norm_pos_iff.mpr (by
      intro hh
      exact hg0 (by simp [hh]))
    have hc := FirstOrderTrustRegion.decreaseConstant_pos hgp h.updates.initial_pos
      h.updates.eta2_lt_one h.updates.gamma1_pos hLone
      ((norm_nonneg _).trans (hB 0))
    refine ⟨_, div_pos zero_lt_one (mul_pos h.updates.eta1_pos hc),
      by simp [tr1SuccessfulConstant, hg0], ?_⟩
    convert h.successful_card_le hL hLone hB hgp (hlow _) using 1
    · rfl
    · ring

/-- **Theorem 2.3.7.** A consistent TR1 execution reaches the requested
accuracy. Function calls are one initial evaluation plus one per trial; gradient
calls are one initial evaluation plus one per accepted trial. All four positive
constants below are fixed independently of `ε`, including the logarithmic term.
The formula explicitly covers an initial stop. -/
theorem theorem_2_3_7 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {x s sC : ℕ → E} {B : ℕ → E →L[ℝ] E}
    {Δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ ε L κB flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖g (x i)‖) →
      tr1Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLone : 1 ≤ L)
    (hB : ∀ i, ‖B i‖ ≤ κB) (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κBcount > 0, ∃ κC > 0,
      κS = tr1SuccessfulConstant ‖g (x 0)‖ (Δ 0) η₁ η₂ γ₁ L κB ∧
      κA = κS * (1 + Real.log γ₃ / |Real.log γ₂|) ∧
      κBcount = 1 / |Real.log γ₂| ∧
      κC = |Real.log (min (Δ 0) (γ₁ * (1 - η₂) / (2 * (L + κB))) / Δ 0)| /
        |Real.log γ₂| + 1 ∧
      ∃ K, ‖g (x K)‖ ≤ ε ∧ tr1Run f g x s sC B Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε K ∧
        ((K + 1 : ℕ) : ℝ) ≤ κA * (f (x 0) - flow) / ε ^ 2 +
          κBcount * |Real.log ε| + κC ∧
        (((successfulIterations ρ η₁ K).card + 1 : ℕ) : ℝ) ≤
          κS * (f (x 0) - flow) / ε ^ 2 + 1 := by
  have h0 := hprefix 0 (by simp)
  obtain ⟨K, hstop, hK⟩ := FirstOrderTrustRegion.exists_termination
    hprefix hL hLone hB hlow
  obtain ⟨κS, hSpos, hSeq, hScount⟩ := lemma_2_3_6 hK hL hLone hB hlow
  let A := 1 + Real.log γ₃ / |Real.log γ₂|
  let C := |Real.log (min (Δ 0) (γ₁ * (1 - η₂) / (2 * (L + κB))) / Δ 0)| /
    |Real.log γ₂|
  have hγ₂ : 0 < γ₂ := h0.updates.gamma1_pos.trans_le h0.updates.gamma1_le_gamma2
  have hlogneg : Real.log γ₂ < 0 := Real.log_neg hγ₂ h0.updates.gamma2_lt_one
  have hlog : 0 < |Real.log γ₂| := abs_pos.mpr (ne_of_lt hlogneg)
  have hγ₃ := Real.log_pos h0.updates.one_lt_gamma3
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hε := h0.accuracy_pos
  have hgap : 0 ≤ f (x 0) - flow := sub_nonneg.mpr (hlow _)
  refine ⟨κS, hSpos, κS * A, mul_pos hSpos hA, 1 / |Real.log γ₂|,
    div_pos zero_lt_one hlog, C + 1, by linarith, hSeq, rfl, rfl, rfl,
    K, hstop, hK, ?_, ?_⟩
  · by_cases hg0 : ‖g (x 0)‖ = 0
    · have hzero : K = 0 := by
        by_contra hzero
        have ht := hK.not_terminated 0 (by omega)
        rw [hg0] at ht
        linarith
      rw [hzero]
      push_cast
      have hp : 0 ≤ κS * A * (f (x 0) - flow) / ε ^ 2 := by positivity
      have hq : 0 ≤ 1 / |Real.log γ₂| * |Real.log ε| := by positivity
      linarith
    · have hgp : 0 < ‖g (x 0)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
      have hb := hK.iterations_le hL hLone hB hgp (hlow _)
      have hκ : κS = 1 /
          (η₁ * FirstOrderTrustRegion.decreaseConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB) := by
        simpa only [tr1SuccessfulConstant, ite_eq_right hg0] using hSeq
      push_cast
      calc
        (K : ℝ) + 1 ≤ (f (x 0) - flow) /
            (η₁ * FirstOrderTrustRegion.decreaseConstant ‖g (x 0)‖ (Δ 0) η₂ γ₁ L κB *
              ε ^ 2) * A +
            (|Real.log (min (Δ 0) (γ₁ * (1 - η₂) / (2 * (L + κB))) / Δ 0)| +
              |Real.log ε|) / |Real.log γ₂| + 1 := add_le_add hb le_rfl
        _ = _ := by rw [hκ]; dsimp [C]; ring
  · simpa only [Nat.cast_add, Nat.cast_one] using add_le_add hScount (le_rfl : (1 : ℝ) ≤ 1)

end CartisGouldToint
