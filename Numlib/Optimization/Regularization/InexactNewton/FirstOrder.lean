import Numlib.Optimization.Regularization.InexactNewton.Counting
import Numlib.Optimization.Regularization.InexactNewton.Step
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# First-order complexity of inexact regularized Newton executions

Actual accepted cubic decrease and the next-gradient squared-step bound give
a fixed positive epsilon-to-the-three-halves objective budget. Coupled-parameter
updates bound every rejected block, and the finite budgets force a first true stop.
-/

namespace InexactRegularizedNewton
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The fixed coefficient multiplying the first-accuracy power in every
accepted trial with a nonterminal first-gradient endpoint. -/
noncomputable def firstOrderDecrease (σmax γ₂ η κ₂ κ₃ L : ℝ) : ℝ :=
  η * (2 / (L + 4 * upperBound σmax γ₂ η κ₂ L + 2 * κ₃)) ^ (3 / 2 : ℝ)

/-- Positive acceptance, upper initialization and gradient control give a
positive objective-decrease coefficient independently of stopping accuracy. -/
theorem firstOrderDecrease_pos {σmax γ₂ η κ₂ κ₃ L : ℝ}
    (hmax : 0 < σmax) (hη : 0 < η) (hκ : 0 < κ₃) (hL : 0 ≤ L) :
    0 < firstOrderDecrease σmax γ₂ η κ₂ κ₃ L := by
  have hcap : 0 < upperBound σmax γ₂ η κ₂ L := hmax.trans_le (le_max_left _ _)
  unfold firstOrderDecrease
  positivity

namespace Run
variable {f : E → ℝ} {x s : ℕ → E} {V : ℕ → Submodule ℝ E}
  {μ ℓ σL σU ρ : ℕ → ℝ}
  {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ L : ℝ}
  {ε₂ : WithTop ℝ} {N : ℕ}

/-- The actual cubic ratio implies cubic objective decrease at acceptance. -/
theorem successful_decrease
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) {i : ℕ} (hi : i < N)
    (ha : η ≤ ρ i) : η * ‖s i‖ ^ 3 ≤ f (x i) - f (x (i + 1)) := by
  have hn : 0 < ‖s i‖ := norm_pos_iff.mpr (h.step_ne_zero hf hi)
  have hr := ha
  rw [h.ratio i hi] at hr
  rw [h.point_update i hi, ite_eq_left ha]
  exact (le_div_iff₀ (pow_pos hn 3)).mp hr

/-- Rejection preserves the actual point and therefore its objective value. -/
theorem rejected_point
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) {i : ℕ} (hi : i < N) (ha : ¬η ≤ ρ i) :
    x (i + 1) = x i := by rw [h.point_update i hi, ite_eq_right ha]

/-- With the second test disabled, nontermination means the actual gradient
norm exceeds the first accuracy. -/
theorem gradient_gt_of_disabled
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hdisabled : ε₂ = ⊤) {i : ℕ} (hi : i < N) :
    ε₁ < ‖gradient f (x i)‖ := by
  by_contra hn
  apply h.not_terminated i hi
  apply (RegularizedTrustRegion.stopped_iff _ _ _ _ _).mpr
  refine ⟨le_of_not_gt hn, ?_⟩
  intro e he
  simp only [hdisabled] at he
  exact (WithTop.top_ne_coe he).elim

/-- A large actual next gradient gives the uniform first-order objective
budget at every accepted trial, without any curvature transport premise. -/
theorem successful_decrease_of_next_gradient
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η ≤ ρ i)
    (hg : ε₁ ≤ ‖gradient f (x (i + 1))‖) :
    firstOrderDecrease σmax γ₂ η κ₂ κ₃ L * ε₁ ^ (3 / 2 : ℝ) ≤
      f (x i) - f (x (i + 1)) := by
  let a := 2 / (L + 4 * upperBound σmax γ₂ η κ₂ L + 2 * κ₃)
  have hcap := h.upperBound_pos (L := L)
  have hκ := h.kappa3_pos
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hbase : a * ε₁ ≤ ‖s i‖ ^ 2 :=
    (mul_le_mul_of_nonneg_left hg ha0).trans (h.step_lower hf hL hlip hi ha)
  have hp := Real.rpow_le_rpow (mul_nonneg ha0 h.first_accuracy_pos.le) hbase
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hs3 : (‖s i‖ ^ 2) ^ (3 / 2 : ℝ) = ‖s i‖ ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg (s i))]
    norm_num
  rw [hs3, Real.mul_rpow ha0 h.first_accuracy_pos.le] at hp
  have hb := mul_le_mul_of_nonneg_left hp h.eta_pos.le
  have hb' : firstOrderDecrease σmax γ₂ η κ₂ κ₃ L * ε₁ ^ (3 / 2 : ℝ) ≤
      η * ‖s i‖ ^ 3 := by simpa only [firstOrderDecrease, a, mul_assoc] using hb
  exact hb'.trans (h.successful_decrease hf hi ha)

/-- All but possibly the last accepted trial have a nonterminal endpoint and
consume the fixed first-order objective budget. -/
theorem firstOrder_successful_card_le
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hdisabled : ε₂ = ⊤)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ((successfulIterations {i | η ≤ ρ i} N).card : ℝ) ≤
      (f (x 0) - flow) /
        (firstOrderDecrease σmax γ₂ η κ₂ κ₃ L * ε₁ ^ (3 / 2 : ℝ)) + 1 := by
  have hc := firstOrderDecrease_pos (γ₂ := γ₂) (κ₂ := κ₂)
    (h.sigmaMin_pos.trans_le h.sigmaMin_le_max)
    h.eta_pos h.kappa3_pos hL
  have hd := mul_pos hc (Real.rpow_pos_of_pos h.first_accuracy_pos (3 / 2))
  have hgap : 0 ≤ f (x 0) - flow := sub_nonneg.mpr (hlow _)
  cases N with
  | zero => simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]; positivity
  | succ k =>
    have hh := card_successful_le_gap_div
      (S := {i | η ≤ ρ i}) (f := fun i => f (x i)) hd (hlow (x k))
      (fun i hi ha => h.successful_decrease_of_next_gradient hf hL hlip (by omega) ha
        (h.gradient_gt_of_disabled hdisabled (by omega)).le)
      (fun i hi ha => by rw [h.rejected_point (by omega) ha])
    have hs : ((successfulIterations {i | η ≤ ρ i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | η ≤ ρ i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | η ≤ ρ i} k
    exact hs.trans (add_le_add hh le_rfl)

/-- The finite objective budget and the actual coupled updates bound all
trials in first-order mode, including a terminal rejected block. -/
theorem firstOrder_iterations_le
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hdisabled : ε₂ = ⊤)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    (N : ℝ) ≤ ((f (x 0) - flow) /
        (firstOrderDecrease σmax γ₂ η κ₂ κ₃ L * ε₁ ^ (3 / 2 : ℝ)) + 1) *
        (2 + Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁) +
      Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁ + 1 := by
  have hmin : σmin ≤ upperBound σmax γ₂ η κ₂ L :=
    h.sigmaMin_le_max.trans (le_max_left _ _)
  have hratio : 0 ≤ Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁ :=
    div_nonneg (Real.log_nonneg ((one_le_div h.sigmaMin_pos).mpr hmin))
      (Real.log_pos h.gamma1_gt_one).le
  exact (h.iterations_le_successful hf hL hlip).trans (by
    gcongr
    exact h.firstOrder_successful_card_le hdisabled hf hL hlip hlow)

end Run

/-- Every consistent first-order execution reaches its first actual stopping
point; the objective and rejected-trial budgets prove termination. -/
theorem exists_firstOrder_termination {f : E → ℝ} {x s : ℕ → E}
    {V : ℕ → Submodule ℝ E} {μ ℓ σL σU ρ : ℕ → ℝ}
    {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ L flow : ℝ}
    (hprefix : ∀ N,
      (∀ i < N, ¬RegularizedTrustRegion.Stopped f (x i) (μ i) ε₁ ⊤) →
      Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ ⊤ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hlow : ∀ y, flow ≤ f y) :
    ∃ K, RegularizedTrustRegion.Stopped f (x K) (μ K) ε₁ ⊤ ∧
      Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
        κ₁ κ₂ κ₃ κ₄ ε₁ ⊤ K ∧
      ∀ i < K, ¬RegularizedTrustRegion.Stopped f (x i) (μ i) ε₁ ⊤ := by
  classical
  have hex : ∃ K, RegularizedTrustRegion.Stopped f (x K) (μ K) ε₁ ⊤ := by
    by_contra hn
    push Not at hn
    let bound := ((f (x 0) - flow) /
        (firstOrderDecrease σmax γ₂ η κ₂ κ₃ L * ε₁ ^ (3 / 2 : ℝ)) + 1) *
        (2 + Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁) +
      Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁ + 1
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hn i)).firstOrder_iterations_le rfl hf hL hlip hlow
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩ <;>
    exact fun i hi => Nat.find_min hex hi

end InexactRegularizedNewton
