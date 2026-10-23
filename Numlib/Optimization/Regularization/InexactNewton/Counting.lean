import Numlib.Optimization.Regularization.InexactNewton.Parameter
import Numlib.Optimization.EvaluationComplexity.Updates

/-!
# Rejected-trial budgets for coupled regularization updates

After a rejection the lower parameter is at least its positive reset floor.
Subsequent rejected trials multiply it by at least the expansion factor. Replacing
its zero reset state by the floor divided by that factor gives a positive
parameter whose every rejection expands geometrically.
-/

namespace InexactRegularizedNewton
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The positive effective lower parameter replaces a reset to zero by one
geometric expansion below the positive reset floor. -/
noncomputable def effectiveLower (σmin γ a : ℝ) : ℝ := max (σmin / γ) a

namespace Run
variable {f : E → ℝ} {x s : ℕ → E} {V : ℕ → Submodule ℝ E}
  {μ ℓ σL σU ρ : ℕ → ℝ}
  {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ L : ℝ}
  {ε₂ : WithTop ℝ} {N : ℕ}

/-- The primitive coupled updates retain ordered bounds, positive upper
parameters and a lower parameter that is either zero or above the reset floor. -/
theorem parameter_state
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) {i : ℕ} (hi : i ≤ N) :
    (σL i = 0 ∨ σmin ≤ σL i) ∧ σL i ≤ σU i ∧ 0 < σU i := by
  have hγ : 0 < γ₁ := zero_lt_one.trans h.gamma1_gt_one
  induction i with
  | zero =>
    rw [h.lower_initial]
    exact ⟨Or.inl rfl, h.sigmaMin_pos.le.trans h.upper_initial.1,
      h.sigmaMin_pos.trans_le h.upper_initial.1⟩
  | succ i ih =>
    have hiN : i < N := by omega
    obtain ⟨hstate, horder, hpos⟩ := ih hiN.le
    have hb := h.update i hiN
    split_ifs at hb with ha hsmall
    · rw [hb.1, hb.2]
      exact ⟨Or.inl rfl, hpos.le, hpos⟩
    · exact ⟨Or.inr hb.1.1, hb.2.1, h.sigmaMin_pos.trans_le (hb.1.1.trans hb.2.1)⟩
    · have hn : 0 < ‖s i‖ := norm_pos_iff.mpr (h.step_ne_zero hf hiN)
      have hr : σmin ≤ ℓ i / ‖s i‖ :=
        (le_div_iff₀ hn).mpr (le_of_not_gt hsmall)
      have hrp : 0 < ℓ i / ‖s i‖ := h.sigmaMin_pos.trans_le hr
      rw [hb.1, hb.2]
      refine ⟨Or.inr ?_, mul_le_mul_of_nonneg_right h.gamma1_le_gamma2 hrp.le, ?_⟩
      · exact hr.trans (le_mul_of_one_le_left hrp.le h.gamma1_gt_one.le)
      · exact mul_pos (hγ.trans_le h.gamma1_le_gamma2) hrp

/-- Every rejected trial raises the next lower parameter above its reset floor. -/
theorem unsuccessful_lower_ge
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) {i : ℕ} (hi : i < N)
    (ha : ¬η ≤ ρ i) : σmin ≤ σL (i + 1) := by
  have hb := h.update i hi
  rw [ite_eq_right ha] at hb
  split_ifs at hb with hsmall
  · exact hb.1.1
  · have hn : 0 < ‖s i‖ := norm_pos_iff.mpr (h.step_ne_zero hf hi)
    have hr : σmin ≤ ℓ i / ‖s i‖ :=
      (le_div_iff₀ hn).mpr (le_of_not_gt hsmall)
    rw [hb.1]
    exact hr.trans (le_mul_of_one_le_left (h.sigmaMin_pos.trans_le hr).le
      h.gamma1_gt_one.le)

/-- Once above the reset floor, a rejection expands the actual lower parameter
by at least the first expansion factor. -/
theorem unsuccessful_lower_growth
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) {i : ℕ} (hi : i < N)
    (ha : ¬η ≤ ρ i) (hfloor : σmin ≤ σL i) :
    γ₁ * σL i ≤ σL (i + 1) := by
  have hn : 0 < ‖s i‖ := norm_pos_iff.mpr (h.step_ne_zero hf hi)
  have hs := h.step i hi.le (Or.inl hi)
  have hsmall : ¬ℓ i < σmin * ‖s i‖ := by
    exact not_lt_of_ge ((mul_le_mul_of_nonneg_right hfloor hn.le).trans hs.lower)
  have hb := h.update i hi
  rw [ite_eq_right ha, ite_eq_right hsmall] at hb
  rw [hb.1]
  apply mul_le_mul_of_nonneg_left _ (zero_lt_one.trans h.gamma1_gt_one).le
  exact (le_div_iff₀ hn).mpr hs.lower

/-- Every effective lower parameter is positive and bounded by the derived
uniform upper cap, including the terminal endpoint. -/
theorem effectiveLower_bounds
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i ≤ N) :
    0 < effectiveLower σmin γ₁ (σL i) ∧
      effectiveLower σmin γ₁ (σL i) ≤ upperBound σmax γ₂ η κ₂ L := by
  have hγ : 0 < γ₁ := zero_lt_one.trans h.gamma1_gt_one
  have hbase : 0 < σmin / γ₁ := div_pos h.sigmaMin_pos hγ
  have hbasele : σmin / γ₁ ≤ σmin :=
    (div_le_iff₀ hγ).mpr (le_mul_of_one_le_right h.sigmaMin_pos.le h.gamma1_gt_one.le)
  exact ⟨hbase.trans_le (le_max_left _ _), max_le
    (hbasele.trans (h.sigmaMin_le_max.trans (le_max_left _ _)))
    ((h.parameter_state hf hi).2.1.trans (h.upper_le hf hL hlip hi))⟩

/-- Rejection always expands the positive effective lower parameter. -/
theorem unsuccessful_effectiveLower_growth
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) {i : ℕ} (hi : i < N)
    (ha : ¬η ≤ ρ i) :
    γ₁ * effectiveLower σmin γ₁ (σL i) ≤ effectiveLower σmin γ₁ (σL (i + 1)) := by
  have hγ : 0 < γ₁ := zero_lt_one.trans h.gamma1_gt_one
  rcases (h.parameter_state hf hi.le).1 with hz | hfloor
  · rw [effectiveLower, hz, max_eq_left (div_nonneg h.sigmaMin_pos.le hγ.le)]
    have he : γ₁ * (σmin / γ₁) = σmin := by field_simp
    rw [he]
    exact (h.unsuccessful_lower_ge hf hi ha).trans (le_max_right _ _)
  · have hbase : σmin / γ₁ ≤ σL i :=
      ((div_le_iff₀ hγ).mpr
        (le_mul_of_one_le_right h.sigmaMin_pos.le h.gamma1_gt_one.le)).trans hfloor
    rw [effectiveLower, max_eq_right hbase]
    exact (h.unsuccessful_lower_growth hf hi ha hfloor).trans (le_max_right _ _)

/-- The effective lower parameter is reset to its positive base after acceptance. -/
theorem successful_effectiveLower_eq
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) {i : ℕ} (hi : i < N) (ha : η ≤ ρ i) :
    effectiveLower σmin γ₁ (σL (i + 1)) = σmin / γ₁ := by
  have hb := h.update i hi
  rw [ite_eq_left ha] at hb
  rw [effectiveLower, hb.1, max_eq_left]
  exact div_nonneg h.sigmaMin_pos.le (zero_lt_one.trans h.gamma1_gt_one).le

/-- The actual lower initialization fixes the positive effective base exactly. -/
theorem initial_effectiveLower_eq
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) :
    effectiveLower σmin γ₁ (σL 0) = σmin / γ₁ := by
  rw [effectiveLower, h.lower_initial, max_eq_left]
  exact div_nonneg h.sigmaMin_pos.le (zero_lt_one.trans h.gamma1_gt_one).le

/-- Every trial is counted by the actual expansion on rejection and the bounded
reset on acceptance. This includes an initial or terminal rejected block. -/
theorem iterations_le_successful
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) :
    (N : ℝ) ≤ ((successfulIterations {i | η ≤ ρ i} N).card : ℝ) *
        (2 + Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁) +
      Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁ + 1 := by
  let C := upperBound σmax γ₂ η κ₂ L
  let a := σmin / γ₁
  have hC : 0 < C := h.upperBound_pos
  have hγ : 0 < γ₁ := zero_lt_one.trans h.gamma1_gt_one
  have ha : 0 < a := div_pos h.sigmaMin_pos hγ
  have hmin : σmin ≤ C := h.sigmaMin_le_max.trans (le_max_left _ _)
  have haC : a < C := (show a < σmin from
    (div_lt_self h.sigmaMin_pos h.gamma1_gt_one)).trans_le hmin
  have hlog : 0 < Real.log γ₁ := Real.log_pos h.gamma1_gt_one
  have hh := iteration_bound_of_parameter_upper
    (S := {i | η ≤ ρ i}) (σ := fun i => effectiveLower σmin γ₁ (σL i))
    (γs := a / C) (γu := γ₁) (σmax := C)
    (fun i hi => (h.effectiveLower_bounds hf hL hlip hi).1)
    (div_pos ha hC) ((div_lt_one hC).mpr haC) h.gamma1_gt_one
    (h.effectiveLower_bounds hf hL hlip le_rfl).2
    (fun i hi hiS => by
      change η ≤ ρ i at hiS
      rw [h.successful_effectiveLower_eq hi hiS]
      change a / C * effectiveLower σmin γ₁ (σL i) ≤ a
      calc
        _ ≤ a / C * C := mul_le_mul_of_nonneg_left
          (h.effectiveLower_bounds hf hL hlip hi.le).2 (div_nonneg ha.le hC.le)
        _ = a := div_mul_cancel₀ _ hC.ne')
    (fun i hi hiS => h.unsuccessful_effectiveLower_growth hf hi hiS)
  rw [h.initial_effectiveLower_eq] at hh
  have hratio : |Real.log (a / C)| = Real.log (C / a) := by
    rw [show a / C = (C / a)⁻¹ by rw [inv_div], Real.log_inv,
      abs_neg, abs_of_pos (Real.log_pos ((one_lt_div ha).mpr haC))]
  have hsplit : Real.log (C / a) / Real.log γ₁ =
      Real.log (C / σmin) / Real.log γ₁ + 1 := by
    have he : C / a = C / σmin * γ₁ := by dsimp [a]; field_simp
    rw [he, Real.log_mul (div_ne_zero hC.ne' h.sigmaMin_pos.ne') hγ.ne']
    field_simp
  simpa only [hratio, hsplit, show (1 : ℝ) + (_ + 1) = 2 + _ by ring, C, a, add_assoc] using hh

/-- Any contiguous block of rejected trials has the exact source logarithmic
length allowance, including blocks at the beginning or end of an execution. -/
theorem rejected_block_le
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    (hrej : ∀ i, a ≤ i → i < b → ¬η ≤ ρ i) :
    ((b - a : ℕ) : ℝ) ≤
      Real.log (upperBound σmax γ₂ η κ₂ L / σmin) / Real.log γ₁ + 1 := by
  let C := upperBound σmax γ₂ η κ₂ L
  let t := σmin / γ₁
  have hC : 0 < C := h.upperBound_pos
  have hγ : 0 < γ₁ := zero_lt_one.trans h.gamma1_gt_one
  have ht : 0 < t := div_pos h.sigmaMin_pos hγ
  have hlog : 0 < Real.log γ₁ := Real.log_pos h.gamma1_gt_one
  have hindex : a + (b - a) = b := by omega
  have hh := iteration_bound_of_parameter_upper
    (S := (∅ : Set ℕ)) (σ := fun k => effectiveLower σmin γ₁ (σL (a + k)))
    (γs := 1 / 2) (γu := γ₁) (σmax := C) (k := b - a)
    (fun i hi => (h.effectiveLower_bounds hf hL hlip (by omega)).1)
    (by norm_num) (by norm_num) h.gamma1_gt_one
    (by simpa only [hindex] using (h.effectiveLower_bounds hf hL hlip hb).2)
    (fun _ _ hi => (Set.notMem_empty _ hi).elim)
    (fun i hi _ => h.unsuccessful_effectiveLower_growth hf (by omega)
      (hrej (a + i) (by omega) (by omega)))
  simp only [successfulIterations, Set.mem_empty_iff_false, Finset.filter_false, Finset.card_empty,
    Nat.cast_zero, zero_mul, zero_add, Nat.add_zero] at hh
  have hbase : t ≤ effectiveLower σmin γ₁ (σL a) := le_max_left _ _
  have hp := (h.effectiveLower_bounds hf hL hlip (hab.trans hb)).1
  have hratio : C / effectiveLower σmin γ₁ (σL a) ≤ C / t :=
    div_le_div_of_nonneg_left hC.le ht hbase
  have hl := Real.log_le_log (div_pos hC hp) hratio
  have hsplit : Real.log (C / t) / Real.log γ₁ =
      Real.log (C / σmin) / Real.log γ₁ + 1 := by
    have he : C / t = C / σmin * γ₁ := by dsimp [t]; field_simp
    rw [he, Real.log_mul (div_ne_zero hC.ne' h.sigmaMin_pos.ne') hγ.ne']
    field_simp
  exact hh.trans (by rw [← hsplit]; exact div_le_div_of_nonneg_right hl hlog.le)

end Run
end InexactRegularizedNewton
