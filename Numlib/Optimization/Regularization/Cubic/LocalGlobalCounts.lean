import Numlib.Optimization.Regularization.Cubic.LocalComplexity
import Numlib.Optimization.EvaluationComplexity.FilteredCount

/-!
# Global successful-trial counts for tightened cubic regularization

Endpoint derivative decreases give a budget for any positive threshold.
Point preservation on rejection transfers that budget to current-point checks
with exactly one initialization allowance.
-/

namespace CubicRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ L : ℝ} {N : ℕ}

/-- Actual acceptance and model decrease give the cubic objective reduction,
independently of any stopping tolerance. -/
theorem TightenedRun.successful_decrease
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) :
    η₁ * σmin / 6 * ‖s i‖ ^ 3 ≤ f (x i) - f (x (i + 1)) := by
  have hr := (le_div_iff₀ (h.denominator_pos hi)).mp ((h.ratio i hi) ▸ hs)
  have hd := mul_le_mul_of_nonneg_left (h.model_decrease hi).le h.updates.eta1_pos.le
  have hmin := mul_le_mul_of_nonneg_right (h.updates.min_le (show i ≤ N by omega))
    (pow_nonneg (norm_nonneg (s i)) 3)
  rw [h.point_update i hi, ite_eq_left hs]
  rw [TaylorModel.eval_zero] at hr hd
  nlinarith [mul_le_mul_of_nonneg_left hmin h.updates.eta1_pos.le]

/-- The objective never increases along an actual tightened execution. -/
theorem TightenedRun.objective_nonincrease
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    {i : ℕ} (hi : i < N) : f (x (i + 1)) ≤ f (x i) := by
  by_cases hs : η₁ ≤ ρ i
  · have hh := h.successful_decrease hi hs
    have hη := h.updates.eta1_pos
    have hσ := h.updates.min_pos
    have hn := pow_nonneg (norm_nonneg (s i)) 3
    have hz : 0 ≤ η₁ * σmin / 6 * ‖s i‖ ^ 3 := by positivity
    linarith only [hh, hz]
  · rw [h.point_update i hi, ite_eq_right hs]

/-- Every accepted endpoint above a positive threshold spends its uniform
`threshold^(3/2)` objective budget, without an accuracy-at-most-one restriction. -/
theorem TightenedRun.endpoint_successful_decrease
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {ζ : ℝ} (hζ : 0 < ζ) {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hg : ζ < ‖fderiv ℝ f (x (i + 1))‖) :
    decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ζ ^ (3 / 2 : ℝ) ≤
      f (x i) - f (x (i + 1)) := by
  let c := 2 / (L + θ + max (σ 0) (γ₃ * L / (1 - η₂)))
  have hσ₀ := h.updates.pos (Nat.zero_le N)
  have hθ := h.theta_pos
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hstat : ‖fderiv ℝ (model f (x i) (σ i)) (s i)‖ ≤ θ / 2 * ‖s i‖ ^ 2 := by
    have hh := (h.stationary i hi).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ.le)
    nlinarith
  have hstep := h.toModelTrace.step_length_lower hf hL hθ.le hlip hi hstat
  rw [h.point_update i hi, ite_eq_left hs] at hg
  have hbase : c * ζ ≤ ‖s i‖ ^ 2 :=
    (mul_le_mul_of_nonneg_left hg.le hc).trans hstep
  have hp := Real.rpow_le_rpow (mul_nonneg hc hζ.le) hbase (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hs3 : (‖s i‖ ^ 2) ^ (3 / 2 : ℝ) = ‖s i‖ ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg (s i))]
    norm_num
  rw [hs3, Real.mul_rpow hc hζ.le] at hp
  have hcoeff : 0 ≤ η₁ * σmin / 6 := by
    have hη := h.updates.eta1_pos
    have hmin := h.updates.min_pos
    positivity
  have hb := mul_le_mul_of_nonneg_left hp hcoeff
  have hb' : decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ζ ^ (3 / 2 : ℝ) ≤
      η₁ * σmin / 6 * ‖s i‖ ^ 3 := by
    simpa only [decreaseCoefficient, c, mul_assoc] using hb
  exact hb'.trans (h.successful_decrease hi hs)

/-- The source large-current-gradient count is valid with one initialization
allowance: rejection preserves the point and each large accepted endpoint
spends the actual objective budget. -/
theorem TightenedRun.large_gradient_card_le
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {flow ζ : ℝ} (hlow : ∀ y, flow ≤ f y) (hζ : 0 < ζ) :
    ((successfulIterations {i | η₁ ≤ ρ i ∧ ζ < ‖fderiv ℝ f (x i)‖} N).card : ℝ) ≤
      (f (x 0) - flow) /
        (decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ζ ^ (3 / 2 : ℝ)) + 1 := by
  have hη := h.updates.eta1_pos
  have hmin := h.updates.min_pos
  have hσ := h.updates.pos (Nat.zero_le N)
  have hθ := h.theta_pos
  have hd : 0 < decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ζ ^ (3 / 2 : ℝ) := by
    unfold decreaseCoefficient
    positivity
  have hb := card_successful_le_gap_div (f := fun i => f (x i)) (k := N)
    (S := {i | η₁ ≤ ρ i ∧ ζ < ‖fderiv ℝ f (x (i + 1))‖}) hd (hlow (x N))
    (fun i hi hs => h.endpoint_successful_decrease hf hL hlip hζ hi hs.1 hs.2)
    (fun i hi _ => h.objective_nonincrease hi)
  have hc := card_current_le_endpoint_add_one (S := {i | η₁ ≤ ρ i})
    (P := fun i => ζ < ‖fderiv ℝ f (x i)‖) (N := N) (by
      intro i hi hu
      change ¬η₁ ≤ ρ i at hu
      rw [h.point_update i hi, ite_eq_right hu])
  have hc' : ((successfulIterations
      {i | η₁ ≤ ρ i ∧ ζ < ‖fderiv ℝ f (x i)‖} N).card : ℝ) ≤
      (successfulIterations
        {i | η₁ ≤ ρ i ∧ ζ < ‖fderiv ℝ f (x (i + 1))‖} N).card + 1 := by
    exact_mod_cast hc
  exact hc'.trans (add_le_add hb le_rfl)

end CubicRegularization

namespace CubicRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ L ℓ : ℝ} {N : ℕ} {xstar ustar : E}

/-- The actual number of successful pre-target trials is the global
large-gradient budget plus the safe finite local budget. The source exclusion
of small gradients outside the positive-curvature region is retained. -/
theorem TightenedRun.local_global_successful_card_le
    (h : TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N)
    (hf : ContDiff ℝ 2 f) (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L) (hzero : fderiv ℝ f xstar = 0)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {flow ζ ε : ℝ} (hlow : ∀ y, flow ≤ f y) (hζ : 0 < ζ) (hε : 0 < ε)
    (hζbound : ζ ≤ localThreshold ℓ L θ (max (σ 0) (γ₃ * L / (1 - η₂))) η₂ / 2)
    (hfail : ∀ i < N, ε < ‖fderiv ℝ f (x i)‖)
    (hexclude : ∀ i < N, ε < ‖fderiv ℝ f (x i)‖ →
      ‖fderiv ℝ f (x i)‖ ≤ ζ → ‖x i - xstar‖ ≤ ℓ / (4 * L)) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      (f (x 0) - flow) /
        (decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ζ ^ (3 / 2 : ℝ)) + 1 +
          quadraticIterationBudget ζ ε := by
  classical
  let B := quadraticIterationBudget ζ ε
  have hsmall : (successfulIterations
      {i | η₁ ≤ ρ i ∧ ¬ζ < ‖fderiv ℝ f (x i)‖} N).card ≤ B := by
    by_cases hex : ∃ i < N, ‖fderiv ℝ f (x i)‖ ≤ ζ
    · let k₀ := Nat.find hex
      have hk := Nat.find_spec hex
      have hbefore : ∀ i < k₀, ¬(i < N ∧ ‖fderiv ℝ f (x i)‖ ≤ ζ) :=
        fun i hi => Nat.find_min hex hi
      have hx₀ := hexclude k₀ hk.1 (hfail k₀ hk.1) hk.2
      have hcap : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
        (h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
      have hz := localThreshold_pos hℓ hL h.theta_pos hcap h.updates.eta2_lt_one
      have hζlocal : ζ ≤ localThreshold ℓ L θ
          (max (σ 0) (γ₃ * L / (1 - η₂))) η₂ :=
        hζbound.trans (half_le_self hz.le)
      have hcount : N ≤ k₀ + B := by
        by_contra hn
        have hBN : k₀ + B < N := not_le.mp hn
        obtain ⟨_, hq⟩ := h.local_persistence hf hstar hℓ hL hzero hlip hk.1.le
          hx₀ (hk.2.trans hζlocal)
        let c := localQuadraticConstant ℓ L θ (max (σ 0) (γ₃ * L / (1 - η₂)))
        have hc := localQuadraticConstant_pos hℓ hL h.theta_pos.le hcap
        have hsmall : c * ζ ≤ 1 / 2 := by
          have hh := (localThreshold_bounds ℓ L θ
            (max (σ 0) (γ₃ * L / (1 - η₂))) η₂).1
          have hm := (le_div_iff₀ (show 0 < 2 * c by positivity)).mp hh
          have hmul := mul_le_mul_of_nonneg_left hζlocal hc.le
          nlinarith only [hm, hmul]
        have hp := quadraticIterationBudget_sufficient hc.le hζ hε hk.2 hsmall
          (fun n _ => norm_nonneg (fderiv ℝ f (x (k₀ + n)))) (by
            intro n hn
            have hh := hq (k₀ + n) (by omega) (by omega)
            simpa only [Nat.add_assoc] using hh.2)
        exact (not_lt_of_ge hp) (hfail (k₀ + B) hBN)
      have hsub : successfulIterations
          {i | η₁ ≤ ρ i ∧ ¬ζ < ‖fderiv ℝ f (x i)‖} N ⊆
            Finset.Ico k₀ (k₀ + B) := by
        intro i hi
        obtain ⟨hiN, _, hgi⟩ := mem_successfulIterations.mp hi
        have hki : k₀ ≤ i := by
          by_contra hn
          exact hbefore i (not_le.mp hn) ⟨hiN, le_of_not_gt hgi⟩
        exact Finset.mem_Ico.mpr ⟨hki, hiN.trans_le hcount⟩
      have hh := Finset.card_le_card hsub
      simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hh
    · have hempty : successfulIterations
          {i | η₁ ≤ ρ i ∧ ¬ζ < ‖fderiv ℝ f (x i)‖} N = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hiN, _, hgi⟩ := mem_successfulIterations.mp hi
        exact hex ⟨i, hiN, le_of_not_gt hgi⟩
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
  have hlarge := h.large_gradient_card_le hf hL.le hlip hlow hζ
  have hpart := Finset.card_filter_add_card_filter_not
    (s := successfulIterations {i | η₁ ≤ ρ i} N)
    (fun i => ζ < ‖fderiv ℝ f (x i)‖)
  have he : (successfulIterations {i | η₁ ≤ ρ i ∧ ζ < ‖fderiv ℝ f (x i)‖} N).card +
      (successfulIterations {i | η₁ ≤ ρ i ∧ ¬ζ < ‖fderiv ℝ f (x i)‖} N).card =
        (successfulIterations {i | η₁ ≤ ρ i} N).card := by
    simpa only [successfulIterations, Finset.filter_filter, Set.mem_ofPred_eq] using hpart
  have hsreal : ((successfulIterations
      {i | η₁ ≤ ρ i ∧ ¬ζ < ‖fderiv ℝ f (x i)‖} N).card : ℝ) ≤ B := by
    exact_mod_cast hsmall
  have hereal := congrArg (fun n : ℕ => (n : ℝ)) he
  push_cast at hereal
  linarith only [hlarge, hsreal, hereal]

end CubicRegularization

namespace CubicRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The repaired global/local cubic bound gives the actual first target,
large-gradient and total successful counts, total trials, and initialized
function and derivative schedules. All coefficients are independent of the
requested accuracy; only the explicit local budget depends on it. -/
theorem exists_local_global_complexity {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ L ℓ ζ ε flow : ℝ} {xstar ustar : E}
    (hf : ContDiff ℝ 2 f) (hstar : SecondOrderTrustRegion.IsLeastEigenpair f xstar ℓ ustar)
    (hℓ : 0 < ℓ) (hL : 0 < L) (hzero : fderiv ℝ f xstar = 0)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) (hζ : 0 < ζ) (hε : 0 < ε)
    (hζbound : ζ ≤ localThreshold ℓ L θ (max (σ 0) (γ₃ * L / (1 - η₂))) η₂ / 2)
    (hexclude : ∀ i, ε < ‖fderiv ℝ f (x i)‖ →
      ‖fderiv ℝ f (x i)‖ ≤ ζ → ‖x i - xstar‖ ≤ ℓ / (4 * L))
    (hprefix : ∀ N, (∀ i < N, ε < ‖fderiv ℝ f (x i)‖) →
      TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ N) :
    let G := (f (x 0) - flow) /
      (decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ζ ^ (3 / 2 : ℝ))
    let B := quadraticIterationBudget ζ ε
    let A := 1 + |Real.log γ₁| / Real.log γ₂
    let C := Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
    ∃ K, ‖fderiv ℝ f (x K)‖ ≤ ε ∧
      (∀ i < K, ε < ‖fderiv ℝ f (x i)‖) ∧
      TightenedRun f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ K ∧
      ((successfulIterations
        {i | η₁ ≤ ρ i ∧ ζ < ‖fderiv ℝ f (x i)‖} K).card : ℝ) ≤
        G + 1 ∧
      ((successfulIterations {i | η₁ ≤ ρ i} K).card : ℝ) ≤ G + 1 + B ∧
      (K : ℝ) ≤ (G + 1 + B) * A + C ∧
      (K : ℝ) + 1 ≤ (G + 1 + B) * A + C + 1 ∧
      ((successfulIterations {i | η₁ ≤ ρ i} K).card : ℝ) + 1 ≤ G + B + 2 := by
  dsimp only
  let G := (f (x 0) - flow) /
    (decreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ * ζ ^ (3 / 2 : ℝ))
  let B := quadraticIterationBudget ζ ε
  let A := 1 + |Real.log γ₁| / Real.log γ₂
  let C := Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
  have hfinite : ∀ N, (∀ i < N, ε < ‖fderiv ℝ f (x i)‖) →
      (N : ℝ) ≤ (G + 1 + B) * A + C := by
    intro N hfail
    have h := hprefix N hfail
    have hc := h.local_global_successful_card_le hf hstar hℓ hL hzero hlip hlow hζ hε
      hζbound hfail (fun i _ => hexclude i)
    have ht := iteration_bound_of_parameter_upper
      (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.updates.pos hi)
      h.updates.gamma1_pos h.updates.gamma1_lt_one h.updates.one_lt_gamma2
      (h.toModelTrace.parameter_le hf hL.le hlip le_rfl)
      (fun _ hi hs => h.updates.successful_ge hi hs)
      (fun _ hi hu => h.updates.unsuccessful_ge hi hu)
    have hlog := Real.log_pos h.updates.one_lt_gamma2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    exact ht.trans (add_le_add (mul_le_mul_of_nonneg_right hc hA) le_rfl)
  have hex : ∃ K, ‖fderiv ℝ f (x K)‖ ≤ ε := by
    by_contra hn
    push Not at hn
    obtain ⟨N, hN⟩ := exists_nat_gt ((G + 1 + B) * A + C)
    exact (not_le_of_gt hN) (hfinite N (fun i _ => hn i))
  let K := Nat.find hex
  have hK : ‖fderiv ℝ f (x K)‖ ≤ ε := Nat.find_spec hex
  have hfirst : ∀ i < K, ε < ‖fderiv ℝ f (x i)‖ :=
    fun i hi => lt_of_not_ge (Nat.find_min hex hi)
  have h := hprefix K hfirst
  have hlarge := h.large_gradient_card_le hf hL.le hlip hlow hζ
  have hc := h.local_global_successful_card_le hf hstar hℓ hL hzero hlip hlow hζ hε
    hζbound hfirst (fun i _ => hexclude i)
  have ht := hfinite K hfirst
  refine ⟨K, hK, hfirst, h, hlarge, hc, ht, ?_, ?_⟩
  · linarith only [ht]
  · linarith only [hc]

end CubicRegularization
