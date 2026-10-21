import Numlib.Optimization.HigherOrderRegularizationComplexity
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Sufficient Taylor decrease with finitely many exceptions

An actual regularization trial can pay its descent budget through its full Taylor prediction
or a lower bound on its step length. The latter pays the parameter floor and factorial
normalization explicitly. Finitely many exceptional trials add only a fixed cost to the
successful-trial budget. All acceptance ratios and parameter updates remain actual trial laws.
-/

noncomputable section
open scoped Nat
namespace Optimization.RegularizationSufficientDecrease
open HigherOrderRegularization RegularizedTaylorModel ParameterUpdates

/-- The actual minimum of the nonempty finite active-order tolerance family. -/
def minimumTolerance (q : ℕ) (hq : 1 ≤ q) (ε : ℕ → ℝ) : ℝ :=
  (Finset.Icc 1 q).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hq⟩⟩ ε

/-- Every active tolerance bounds the common minimum from above. -/
theorem minimumTolerance_le {q : ℕ} (hq : 1 ≤ q) (ε : ℕ → ℝ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 q) : minimumTolerance q hq ε ≤ ε j :=
  Finset.inf'_le ε hj

/-- Positive active tolerances have a strictly positive finite minimum. -/
theorem minimumTolerance_pos {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) : 0 < minimumTolerance q hq ε := by
  exact (Finset.lt_inf'_iff _).mpr hε

/-- Bounding the finite minimum is equivalent to bounding every active tolerance. -/
theorem le_minimumTolerance_iff {q : ℕ} (hq : 1 ≤ q) (ε : ℕ → ℝ) (a : ℝ) :
    a ≤ minimumTolerance q hq ε ↔ ∀ j ∈ Finset.Icc 1 q, a ≤ ε j :=
  Finset.le_inf'_iff _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A full Taylor prediction pays one active tolerance, or the step pays the powered
minimum-tolerance threshold. The coefficient and exponent are fixed algorithmic data. -/
def HasTaylorDecrease (f : E → ℝ) (p q : ℕ) (hq : 1 ≤ q)
    (ε : ℕ → ℝ) (κ ω : ℝ) (x s : E) : Prop :=
  (∃ j ∈ Finset.Icc 1 q, κ * (ε j) ^ ω ≤
    taylorModel f p x 0 - taylorModel f p x s) ∨
      κ * (minimumTolerance q hq ε) ^ ω ≤ ‖s‖ ^ (p + 1)

/-- The two alternative sufficient-decrease rules characterize the named condition. -/
theorem hasTaylorDecrease_iff {f : E → ℝ} {p q : ℕ} {hq : 1 ≤ q}
    {ε : ℕ → ℝ} {κ ω : ℝ} {x s : E} :
    HasTaylorDecrease f p q hq ε κ ω x s ↔
      (∃ j ∈ Finset.Icc 1 q, κ * (ε j) ^ ω ≤
        taylorModel f p x 0 - taylorModel f p x s) ∨
      κ * (minimumTolerance q hq ε) ^ ω ≤ ‖s‖ ^ (p + 1) := Iff.rfl

omit [NormedSpace ℝ E] in
/-- A positive real root states exactly the same nonnegative powered step threshold. -/
theorem powered_step_iff_root {p : ℕ} {a : ℝ} (ha : 0 ≤ a) (s : E) :
    a ≤ ‖s‖ ^ (p + 1) ↔ a ^ (((p + 1 : ℕ) : ℝ)⁻¹) ≤ ‖s‖ := by
  simpa only [Real.rpow_natCast] using
    (Real.rpow_inv_le_iff_of_pos ha (norm_nonneg s)
      (show (0 : ℝ) < (p + 1 : ℕ) by positivity)).symm

/-- The root threshold factors into the coefficient root and the tolerance power. -/
theorem root_threshold_eq {p : ℕ} {κ e ω : ℝ} (hκ : 0 ≤ κ) (he : 0 ≤ e) :
    (κ * e ^ ω) ^ (((p + 1 : ℕ) : ℝ)⁻¹) =
      κ ^ (((p + 1 : ℕ) : ℝ)⁻¹) * e ^ (ω / ((p + 1 : ℕ) : ℝ)) := by
  rw [Real.mul_rpow hκ (Real.rpow_nonneg he _), ← Real.rpow_mul he]
  rw [div_eq_mul_inv]

/-- The effective coefficient includes the normalization paid by the step-length branch. -/
def decreaseFactor (params : RegularizationParameters) (p : ℕ) (κ : ℝ) : ℝ :=
  min κ (params.sigmaMin / ((p + 1)! : ℝ) * κ)

/-- The fixed effective coefficient is strictly positive. -/
theorem decreaseFactor_pos (params : RegularizationParameters) (p : ℕ) {κ : ℝ}
    (hκ : 0 < κ) : 0 < decreaseFactor params p κ := by
  exact lt_min hκ (mul_pos (div_pos params.sigmaMin_pos (by positivity)) hκ)

variable {params : RegularizationParameters} {p q N : ℕ} {hq : 1 ≤ q}
  {f : E → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ} {ε : ℕ → ℝ} {κ ω : ℝ}

/-- Either sufficient-decrease rule controls the actual full acceptance prediction. -/
theorem prediction_lower (h : TrialPrefix params p f x s σ N)
    (hκ : 0 ≤ κ) (hω : 0 ≤ ω) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    {k : ℕ} (hk : k < N) (hs : HasTaylorDecrease f p q hq ε κ ω (x k) (s k)) :
    decreaseFactor params p κ * (minimumTolerance q hq ε) ^ ω ≤
      taylorModel f p (x k) 0 - taylorModel f p (x k) (s k) := by
  have he := (minimumTolerance_pos hq hε).le
  rcases hs with ⟨j, hj, hjdec⟩ | hs
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg he _)).trans
        ((mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow he (minimumTolerance_le hq ε hj) hω) hκ).trans hjdec)
  · calc
      _ ≤ (params.sigmaMin / ((p + 1)! : ℝ) * κ) *
          (minimumTolerance q hq ε) ^ ω :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg he _)
      _ = params.sigmaMin / ((p + 1)! : ℝ) *
          (κ * (minimumTolerance q hq ε) ^ ω) := by ring
      _ ≤ params.sigmaMin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) :=
        mul_le_mul_of_nonneg_left hs (div_nonneg params.sigmaMin_pos.le (by positivity))
      _ ≤ σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (h.toRegularizationPrefix.lower (by omega))
            (by positivity)) (pow_nonneg (norm_nonneg _) _)
      _ ≤ _ := h.predicted_decrease hk

/-- Successful actual trials realize the fixed sufficient objective decrease. -/
theorem accepted_decrease (h : TrialPrefix params p f x s σ N)
    (hκ : 0 ≤ κ) (hω : 0 ≤ ω) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    {k : ℕ} (hk : k < N) (ha : params.eta1 ≤ ratio f p (x k) (s k))
    (hs : HasTaylorDecrease f p q hq ε κ ω (x k) (s k)) :
    params.eta1 * decreaseFactor params p κ * (minimumTolerance q hq ε) ^ ω ≤
      f (x k) - f (x (k + 1)) := by
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (prediction_lower h hκ hω hε hk hs)
    params.eta1_pos.le).trans (h.accepted_decrease hk ha)

/-- A uniformly finite exceptional set adds its cardinality to the successful-trial
budget. Every other accepted step obeys the actual sufficient-decrease rule. -/
theorem success_count_le_with_exceptions (h : TrialPrefix params p f x s σ N)
    (hκ : 0 < κ) (hω : 0 ≤ ω) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    {low : ℝ} (hlow : low ≤ f (x N)) (bad : Finset ℕ) (B : ℕ)
    (hbad : bad.card ≤ B)
    (hgood : ∀ k < N, params.eta1 ≤ ratio f p (x k) (s k) → k ∉ bad →
      HasTaylorDecrease f p q hq ε κ ω (x k) (s k)) :
    (successCount (fun k => params.eta1 ≤ ratio f p (x k) (s k)) N : ℝ) ≤
      (f (x 0) - low) /
        (params.eta1 * decreaseFactor params p κ * (minimumTolerance q hq ε) ^ ω) + B := by
  classical
  let S := (Finset.range N).filter (fun k => params.eta1 ≤ ratio f p (x k) (s k))
  let d := params.eta1 * decreaseFactor params p κ * (minimumTolerance q hq ε) ^ ω
  have hd : 0 < d := mul_pos (mul_pos params.eta1_pos (decreaseFactor_pos params p hκ))
    (Real.rpow_pos_of_pos (minimumTolerance_pos hq hε) _)
  have hb : ((S \ bad).card : ℝ) ≤ (f (x 0) - low) / d := by
    apply (le_div_iff₀ hd).mpr
    apply EvaluationComplexity.card_mul_le_gap (u := fun k => f (x k))
      (S := S \ bad) (n := N) (δ := d) (low := low)
      (fun k hk => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk).1).1) hlow
      (fun k hk => h.objective_nonincrease hk)
    intro k hk
    obtain ⟨hkS, hkbad⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hkN, hkacc⟩ := Finset.mem_filter.mp hkS
    have hk := Finset.mem_range.mp hkN
    exact accepted_decrease h hκ.le hω hε hk hkacc (hgood k hk hkacc hkbad)
  have hc : (S.card : ℝ) ≤ ((S \ bad).card : ℝ) + (bad.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := S) (t := bad))
  have hB : (bad.card : ℝ) ≤ B := by exact_mod_cast hbad
  change (S.card : ℝ) ≤ _
  linarith

/-- Legal actual parameter updates turn the exceptional successful-trial budget into
objective and cached derivative query budgets. All coefficients outside the displayed
tolerance power depend only on fixed method data and the exceptional-set bound. -/
theorem evaluation_bounds (h : TrialPrefix params p f x s σ N)
    {L : ℝ} (hf : DiagonalLipschitz f p L) (hp : 1 ≤ p)
    (hκ : 0 < κ) (hω : 0 ≤ ω) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    {low : ℝ} (hlow : low ≤ f (x N)) (bad : Finset ℕ) (B : ℕ)
    (hbad : bad.card ≤ B)
    (hgood : ∀ k < N, params.eta1 ≤ ratio f p (x k) (s k) → k ∉ bad →
      HasTaylorDecrease f p q hq ε κ ω (x k) (s k)) :
    let M := max (σ 0) (params.gamma3 * (L / (1 - params.eta2)))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (M / σ 0) / Real.log params.gamma2
    let Q := (f (x 0) - low) /
      (params.eta1 * decreaseFactor params p κ * (minimumTolerance q hq ε) ^ ω) + B
    (functionEvaluations N : ℝ) ≤ C * Q + D + 1 ∧
      (derivativeEvaluations params p f x s N : ℝ) ≤ Q + 1 := by
  dsimp only
  have hC : 0 ≤ 1 + |Real.log params.gamma1| / Real.log params.gamma2 :=
    add_nonneg zero_le_one
      (div_nonneg (abs_nonneg _) (Real.log_pos params.one_lt_gamma2).le)
  have hs := success_count_le_with_exceptions h hκ hω hε hlow bad B hbad hgood
  have ht := h.toRegularizationPrefix.total_count_le le_rfl (h.sigma_upper hf hp le_rfl)
  have hm := mul_le_mul_of_nonneg_left hs hC
  simp only [functionEvaluations, derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  constructor <;> linarith

/-- A fixed bound for all legal nonattaining prefixes forces a genuine first stop.
The exceptional set may vary with the prefix, but its cardinality bound is fixed. -/
theorem exists_first_with_evaluation_bounds {L low : ℝ} {P : ℕ → Prop}
    (hf : DiagonalLipschitz f p L) (hp : 1 ≤ p)
    (hκ : 0 < κ) (hω : 0 ≤ ω) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    (hlow : ∀ y, low ≤ f y) (B : ℕ)
    (hprefix : ∀ N, (∀ k < N, ¬P k) → TrialPrefix params p f x s σ N)
    (hgood : ∀ N, (∀ k < N, ¬P k) → ∃ bad : Finset ℕ, bad.card ≤ B ∧
      ∀ k < N, params.eta1 ≤ ratio f p (x k) (s k) → k ∉ bad →
        HasTaylorDecrease f p q hq ε κ ω (x k) (s k)) :
    let M := max (σ 0) (params.gamma3 * (L / (1 - params.eta2)))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (M / σ 0) / Real.log params.gamma2
    let Q := (f (x 0) - low) /
      (params.eta1 * decreaseFactor params p κ * (minimumTolerance q hq ε) ^ ω) + B
    ∃ K : ℕ, P K ∧ (∀ k < K, ¬P k) ∧
      (functionEvaluations K : ℝ) ≤ C * Q + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 1 := by
  dsimp only
  have hb : ∀ N, (∀ k < N, ¬P k) →
      (N : ℝ) ≤ (1 + |Real.log params.gamma1| / Real.log params.gamma2) *
        ((f (x 0) - low) /
          (params.eta1 * decreaseFactor params p κ * (minimumTolerance q hq ε) ^ ω) + B) +
        Real.log (max (σ 0) (params.gamma3 * (L / (1 - params.eta2))) / σ 0) /
          Real.log params.gamma2 + 1 := by
    intro N hn
    obtain ⟨bad, hbad, hg⟩ := hgood N hn
    have hc := (evaluation_bounds (hprefix N hn) hf hp hκ hω hε
      (hlow (x N)) bad B hbad hg).1
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one] at hc
    linarith
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hb
  obtain ⟨bad, hbad, hg⟩ := hgood K hfirst
  exact ⟨K, hK, hfirst, evaluation_bounds (hprefix K hfirst) hf hp hκ hω hε
    (hlow (x K)) bad B hbad hg⟩

end Optimization.RegularizationSufficientDecrease
