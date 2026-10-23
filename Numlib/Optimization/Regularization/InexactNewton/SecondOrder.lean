import Numlib.Optimization.Regularization.InexactNewton.FirstOrder
import Numlib.Optimization.TrustRegion.Regularized.SecondOrder

/-!
# Projected second-order complexity of inexact regularized Newton executions

The actual current projected curvature gives a large step when its gradient
already passes. The actual next gradient gives the other decrease branch.
A credit attached only to the gradient test joins these branches without moving
curvature certificates between varying model subspaces or rejected iterates.
-/

namespace InexactRegularizedNewton
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The common positive objective-decrease coefficient for the gradient and
current projected-curvature branches. -/
noncomputable def secondOrderDecrease (σmax γ₂ η κ₂ κ₃ κ₄ L : ℝ) : ℝ :=
  min (firstOrderDecrease σmax γ₂ η κ₂ κ₃ L)
    (η / (κ₄ + upperBound σmax γ₂ η κ₂ L) ^ 3)

/-- Both primitive model controls give a positive accuracy-independent coefficient. -/
theorem secondOrderDecrease_pos {σmax γ₂ η κ₂ κ₃ κ₄ L : ℝ}
    (hmax : 0 < σmax) (hη : 0 < η) (hκ₃ : 0 < κ₃) (hκ₄ : 0 < κ₄) (hL : 0 ≤ L) :
    0 < secondOrderDecrease σmax γ₂ η κ₂ κ₃ κ₄ L := by
  have hcap : 0 < upperBound σmax γ₂ η κ₂ L := hmax.trans_le (le_max_left _ _)
  exact lt_min (firstOrderDecrease_pos hmax hη hκ₃ hL) (by positivity)

/-- The exact common scale in the second-order complexity statement. -/
noncomputable def secondOrderScale (ε₁ ε₂ : ℝ) : ℝ :=
  min (ε₁ ^ (3 / 2 : ℝ)) (ε₂ ^ 3)

/-- Two positive tolerances give a positive common scale. -/
theorem secondOrderScale_pos {ε₁ ε₂ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    0 < secondOrderScale ε₁ ε₂ := by
  exact lt_min (Real.rpow_pos_of_pos h₁ _) (pow_pos h₂ _)

namespace Run
variable {f : E → ℝ} {x s : ℕ → E} {V : ℕ → Submodule ℝ E}
  {μ ℓ σL σU ρ : ℕ → ℝ}
  {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ e L : ℝ}
  {ε₂ : WithTop ℝ} {N : ℕ}

/-- Failure of the finite joint test is a large actual gradient or negative
actual least curvature on the current model subspace. -/
theorem finite_failure
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hfinite : ε₂ = (e : WithTop ℝ))
    {i : ℕ} (hi : i < N) : ε₁ < ‖gradient f (x i)‖ ∨ μ i < -e := by
  by_cases hg : ε₁ < ‖gradient f (x i)‖
  · exact Or.inl hg
  · right
    by_contra hm
    apply h.not_terminated i hi
    apply (RegularizedTrustRegion.stopped_iff _ _ _ _ _).mpr
    refine ⟨le_of_not_gt hg, ?_⟩
    intro a ha
    have he : e = a := WithTop.coe_injective (hfinite.symm.trans ha)
    simpa only [←he] using le_of_not_gt hm

/-- Negative actual current projected curvature forces a uniform accepted
objective decrease through the genuine model-curvature and multiplier bounds. -/
theorem successful_decrease_of_curvature
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hfinite : ε₂ = (e : WithTop ℝ)) (he : 0 < e)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η ≤ ρ i) (hμ : μ i ≤ -e) :
    η / (κ₄ + upperBound σmax γ₂ η κ₂ L) ^ 3 * e ^ 3 ≤
      f (x i) - f (x (i + 1)) := by
  let C := κ₄ + upperBound σmax γ₂ η κ₂ L
  have hcap := h.upperBound_pos (L := L)
  have hκ := h.kappa4_pos
  have hC : 0 < C := by dsimp [C]; positivity
  have hs := h.finite_projected_step_lower hf hL hlip hi.le
    (by rw [hfinite]; exact WithTop.coe_ne_top)
  have hsn : e / C ≤ ‖s i‖ := by
    have hh := mul_le_mul_of_nonneg_left hμ (inv_nonneg.mpr hC.le)
    dsimp only [C] at hh ⊢
    rw [div_eq_mul_inv]
    nlinarith
  have hp := pow_le_pow_left₀ (div_nonneg he.le hC.le) hsn 3
  have hh := mul_le_mul_of_nonneg_left hp h.eta_pos.le
  rw [div_pow] at hh
  have hd := h.successful_decrease hf hi ha
  calc
    _ = η * (e ^ 3 / C ^ 3) := by ring
    _ ≤ η * ‖s i‖ ^ 3 := hh
    _ ≤ _ := hd

/-- Every accepted finite-mode trial consumes half a common objective unit
in the gradient-credit potential, even when its endpoint is terminal. -/
theorem successful_credit_decrease
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hfinite : ε₂ = (e : WithTop ℝ)) (he : 0 < e)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η ≤ ρ i) :
    let d := secondOrderDecrease σmax γ₂ η κ₂ κ₃ κ₄ L * secondOrderScale ε₁ e
    d / 2 ≤ RegularizedTrustRegion.creditPotential f ε₁ d (x i) -
      RegularizedTrustRegion.creditPotential f ε₁ d (x (i + 1)) := by
  classical
  dsimp only
  let c := secondOrderDecrease σmax γ₂ η κ₂ κ₃ κ₄ L
  let d := c * secondOrderScale ε₁ e
  have hc : 0 < c := secondOrderDecrease_pos
    (h.sigmaMin_pos.trans_le h.sigmaMin_le_max) h.eta_pos h.kappa3_pos h.kappa4_pos hL
  have hd : 0 < d := mul_pos hc (secondOrderScale_pos h.first_accuracy_pos he)
  have hnoninc : f (x (i + 1)) ≤ f (x i) := by
    have hh := h.successful_decrease hf hi ha
    have hz : 0 ≤ η * ‖s i‖ ^ 3 := mul_nonneg h.eta_pos.le (by positivity)
    linarith
  by_cases hcurrent : ‖gradient f (x i)‖ ≤ ε₁
  · have hμ : μ i < -e := (h.finite_failure hfinite hi).resolve_left (not_lt_of_ge hcurrent)
    have hh := h.successful_decrease_of_curvature hfinite he hf hL hlip hi ha hμ.le
    have hb : d ≤ f (x i) - f (x (i + 1)) := by
      apply le_trans _ hh
      exact mul_le_mul (min_le_right _ _) (min_le_right _ _)
        (secondOrderScale_pos h.first_accuracy_pos he).le
        (hc.le.trans (min_le_right _ _))
    change d / 2 ≤ _
    unfold RegularizedTrustRegion.creditPotential
    rw [ite_eq_left hcurrent]
    split_ifs <;> linarith
  · by_cases hnext : ‖gradient f (x (i + 1))‖ ≤ ε₁
    · change d / 2 ≤ _
      unfold RegularizedTrustRegion.creditPotential
      rw [ite_eq_right hcurrent, ite_eq_left hnext]
      linarith
    · have hh := h.successful_decrease_of_next_gradient hf hL hlip hi ha
        (le_of_not_ge hnext)
      have hb : d ≤ f (x i) - f (x (i + 1)) := by
        apply le_trans _ hh
        exact mul_le_mul (min_le_left _ _) (min_le_left _ _)
          (secondOrderScale_pos h.first_accuracy_pos he).le
          (firstOrderDecrease_pos (h.sigmaMin_pos.trans_le h.sigmaMin_le_max)
            h.eta_pos h.kappa3_pos hL).le
      change d / 2 ≤ _
      unfold RegularizedTrustRegion.creditPotential
      rw [ite_eq_right hcurrent, ite_eq_right hnext]
      linarith

/-- The actual objective budget bounds every accepted finite-mode trial,
including the terminal one, using a credit independent of the changing subspace. -/
theorem secondOrder_successful_card_le
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hfinite : ε₂ = (e : WithTop ℝ)) (he : 0 < e)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ((successfulIterations {i | η ≤ ρ i} N).card : ℝ) ≤
      2 * (f (x 0) - flow) /
        (secondOrderDecrease σmax γ₂ η κ₂ κ₃ κ₄ L *
          secondOrderScale ε₁ e) + 1 := by
  let d := secondOrderDecrease σmax γ₂ η κ₂ κ₃ κ₄ L * secondOrderScale ε₁ e
  have hc := secondOrderDecrease_pos (γ₂ := γ₂) (κ₂ := κ₂)
    (h.sigmaMin_pos.trans_le h.sigmaMin_le_max) h.eta_pos h.kappa3_pos h.kappa4_pos hL
  have hd : 0 < d := mul_pos hc (secondOrderScale_pos h.first_accuracy_pos he)
  have hlo : flow - d / 2 ≤ RegularizedTrustRegion.creditPotential f ε₁ d (x N) :=
    (sub_le_sub_right (hlow _) _).trans
      (RegularizedTrustRegion.creditPotential_bounds f ε₁ hd.le (x N)).1
  have hh := card_successful_le_gap_div
    (S := {i | η ≤ ρ i}) (f := fun i => RegularizedTrustRegion.creditPotential f ε₁ d (x i))
    (show 0 < d / 2 by positivity) hlo
    (fun i hi ha => h.successful_credit_decrease hfinite he hf hL hlip hi ha)
    (fun i hi ha => by rw [h.rejected_point hi ha])
  have hinit := (RegularizedTrustRegion.creditPotential_bounds f ε₁ hd.le (x 0)).2
  have hb : (RegularizedTrustRegion.creditPotential f ε₁ d (x 0) - (flow - d / 2)) /
      (d / 2) ≤ (f (x 0) - (flow - d / 2)) / (d / 2) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hinit _) (by positivity)
  have heq : (f (x 0) - (flow - d / 2)) / (d / 2) =
      2 * (f (x 0) - flow) / d + 1 := by field_simp; ring
  exact hh.trans (by simpa only [heq, d] using hb)

/-- Actual rejected-parameter growth and the credited objective budget bound
all finite-mode trials, with no curvature comparison across subspaces. -/
theorem secondOrder_iterations_le
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hfinite : ε₂ = (e : WithTop ℝ)) (he : 0 < e)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    (N : ℝ) ≤ (2 * (f (x 0) - flow) /
        (secondOrderDecrease σmax γ₂ η κ₂ κ₃ κ₄ L * secondOrderScale ε₁ e) + 1) *
        (2 + Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁) +
      Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁ + 1 := by
  have hmin : σmin ≤ upperBound σmax γ₂ η κ₂ L :=
    h.sigmaMin_le_max.trans (le_max_left _ _)
  have hratio : 0 ≤ Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁ :=
    div_nonneg (Real.log_nonneg ((one_le_div h.sigmaMin_pos).mpr hmin))
      (Real.log_pos h.gamma1_gt_one).le
  exact (h.iterations_le_successful hf hL hlip).trans (by
    gcongr
    exact h.secondOrder_successful_card_le hfinite he hf hL hlip hlow)

end Run

/-- Every consistent finite-second-order execution reaches its first actual
joint target on the terminating model subspace within the finite objective budget. -/
theorem exists_secondOrder_termination {f : E → ℝ} {x s : ℕ → E}
    {V : ℕ → Submodule ℝ E} {μ ℓ σL σU ρ : ℕ → ℝ}
    {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ e L flow : ℝ}
    (hprefix : ∀ N,
      (∀ i < N, ¬RegularizedTrustRegion.Stopped f (x i) (μ i) ε₁ (e : WithTop ℝ)) →
      Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
        κ₁ κ₂ κ₃ κ₄ ε₁ (e : WithTop ℝ) N)
    (he : 0 < e) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hlow : ∀ y, flow ≤ f y) :
    ∃ K, RegularizedTrustRegion.Stopped f (x K) (μ K) ε₁ (e : WithTop ℝ) ∧
      Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
        κ₁ κ₂ κ₃ κ₄ ε₁ (e : WithTop ℝ) K ∧
      ∀ i < K, ¬RegularizedTrustRegion.Stopped f (x i) (μ i) ε₁ (e : WithTop ℝ) := by
  classical
  have hex : ∃ K, RegularizedTrustRegion.Stopped f (x K) (μ K) ε₁ (e : WithTop ℝ) := by
    by_contra hn
    push Not at hn
    let bound := (2 * (f (x 0) - flow) /
        (secondOrderDecrease σmax γ₂ η κ₂ κ₃ κ₄ L * secondOrderScale ε₁ e) + 1) *
        (2 + Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁) +
      Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁ + 1
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hn i)).secondOrder_iterations_le
      rfl he hf hL hlip hlow
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩ <;>
    exact fun i hi => Nat.find_min hex hi

end InexactRegularizedNewton
