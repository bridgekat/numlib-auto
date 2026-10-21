import Numlib.Optimization.ResidualRegularizationRun
import Numlib.Optimization.HigherOrderRegularizationComplexity

/-!
# Normalized residual iterate quality

Quality controls derivatives on the actual computed model directions, allowing that set to
be empty. At first and second order this is the genuine stopping test. The third-order
certificate chooses the empty set at strict positive curvature and otherwise retains all
computed directions. No normalized ratios are used at a zero residual.
-/

noncomputable section
namespace Optimization.ResidualRegularization
open HigherOrderRegularization ParameterUpdates

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F]

/-- Iterate quality with the exact normalized derivative tests, permitting empty directions. -/
def Quality (order : ℕ) (epsilon0 : ℝ) (epsilon : Fin 3 → ℝ)
    (r : E → F) (ell : ℝ) (x : E) (M : Set E) : Prop :=
  ‖r x‖ ≤ epsilon0 ∨ match normalizedResidualMeasures r ell x with
    | none => True
    | some m => m.first ≤ epsilon 0 ∧ (2 ≤ order → epsilon 1 < m.second ∨
      (-epsilon 1 ≤ m.second ∧ (3 ≤ order → ∀ d ∈ M,
        m.cubic d ≤ epsilon 2 ∧ m.quadratic d ≤ epsilon 1)))

/-- Elimination of quality at actual nonzero normalized measures. -/
theorem quality_iff_of_measures {order : ℕ} {epsilon0 ell : ℝ} {epsilon : Fin 3 → ℝ}
    {r : E → F} {x : E} {M : Set E} {m : NormalizedResidualMeasures E}
    (hm : normalizedResidualMeasures r ell x = some m) :
    Quality order epsilon0 epsilon r ell x M ↔ ‖r x‖ ≤ epsilon0 ∨
      m.first ≤ epsilon 0 ∧ (2 ≤ order → epsilon 1 < m.second ∨
        (-epsilon 1 ≤ m.second ∧ (3 ≤ order → ∀ d ∈ M,
          m.cubic d ≤ epsilon 2 ∧ m.quadratic d ≤ epsilon 1))) := by
  simp only [Quality, hm]

/-- Every genuine stopping test supplies iterate quality. -/
theorem Stationary.quality {order : ℕ} {epsilon0 ell : ℝ} {epsilon : Fin 3 → ℝ}
    {r : E → F} {x : E} {M : Set E}
    (h : Stationary order epsilon0 epsilon r ell x M) :
    Quality order epsilon0 epsilon r ell x M := by
  rcases h with h | h
  · exact Or.inl h
  refine Or.inr ?_
  cases hm : normalizedResidualMeasures r ell x with
  | none => trivial
  | some m =>
    simp only [hm] at h ⊢
    refine ⟨h.1, fun hq => ?_⟩
    rcases h.2 hq with hc | hc
    · exact Or.inl hc
    · exact Or.inr ⟨hc.1, fun ht => (hc.2 ht).2⟩

/-- Below third order the quality and actual stopping tests coincide. -/
theorem quality_iff_stationary_of_order_le_two {order : ℕ} (hq : order ≤ 2)
    (epsilon0 : ℝ) (epsilon : Fin 3 → ℝ) (r : E → F) (ell : ℝ) (x : E) (M : Set E) :
    Quality order epsilon0 epsilon r ell x M ↔ Stationary order epsilon0 epsilon r ell x M := by
  have ht : ¬3 ≤ order := by omega
  simp only [Quality, Stationary, ht, false_implies]
  rfl

/-- A failed quality test supplies a genuine enabled derivative violation, including absolute
quadratic violation on a computed model direction. -/
theorem not_quality_witness {order : ℕ} {epsilon0 ell : ℝ} {epsilon : Fin 3 → ℝ}
    {r : E → F} {x : E} {M : Set E} {m : NormalizedResidualMeasures E}
    (hm : normalizedResidualMeasures r ell x = some m)
    (h : ¬Quality order epsilon0 epsilon r ell x M) :
    epsilon0 < ‖r x‖ ∧
      (epsilon 0 < m.first ∨
        (2 ≤ order ∧ epsilon 1 < max 0 (-m.second)) ∨
        (3 ≤ order ∧ ∃ d ∈ M,
          epsilon 2 < m.cubic d ∨ epsilon 1 < m.quadratic d)) := by
  rw [quality_iff_of_measures hm] at h
  refine ⟨lt_of_not_ge (fun hr => h (Or.inl hr)), ?_⟩
  by_cases hg : m.first ≤ epsilon 0
  · right
    by_cases hc : -epsilon 1 ≤ m.second
    · right
      have hq3 : 3 ≤ order := by
        by_contra hn
        exact h (Or.inr ⟨hg, fun _ => Or.inr ⟨hc, fun hq => (hn hq).elim⟩⟩)
      refine ⟨hq3, ?_⟩
      by_contra! hd
      exact h (Or.inr ⟨hg, fun _ => Or.inr ⟨hc, fun _ d hdm =>
        hd d hdm⟩⟩)
    · left
      have hq2 : 2 ≤ order := by
        by_contra hn
        exact h (Or.inr ⟨hg, fun hq => (hn hq).elim⟩)
      refine ⟨hq2, ?_⟩
      have hb : epsilon 1 < -m.second := by linarith [lt_of_not_ge hc]
      exact hb.trans_le (le_max_right _ _)
  · exact Or.inl (lt_of_not_ge hg)

/-- A third-order quality point supplies the exact source certificate, with the empty set
chosen at strict positive curvature and all current directions retained otherwise. -/
theorem Quality.certificate {epsilon0 ell : ℝ} {epsilon : Fin 3 → ℝ}
    {r : E → F} {x : E} {M : Set E} (h : Quality 3 epsilon0 epsilon r ell x M)
    (he0 : 0 ≤ epsilon0) (he2 : 0 ≤ epsilon 1) (hunit : ∀ d ∈ M, ‖d‖ = 1) :
    ‖r x‖ ≤ epsilon0 ∨ ∃ m : NormalizedResidualMeasures E,
      normalizedResidualMeasures r ell x = some m ∧
      ∃ D : Set E, D = (if epsilon 1 < m.second then ∅ else M) ∧
        m.first ≤ epsilon 0 ∧ -epsilon 1 ≤ m.second ∧
        (∀ d ∈ D, m.cubic d ≤ epsilon 2) ∧
        D ⊆ residualFlatDirections r ell (epsilon 1) x := by
  rcases h with hr | h
  · exact Or.inl hr
  cases hm : normalizedResidualMeasures r ell x with
  | none =>
    left
    have hz := (normalizedResidualMeasures_eq_none_iff r ell x).mp hm
    simpa only [hz, norm_zero] using he0
  | some m =>
    right
    simp only [hm] at h
    refine ⟨m, rfl, ?_⟩
    by_cases hc : epsilon 1 < m.second
    · exact ⟨∅, by simp [hc], h.1, by linarith, by simp, Set.empty_subset _⟩
    · have hb := (h.2 (by decide)).resolve_left hc
      refine ⟨M, by simp [hc], h.1, hb.1, fun d hd => (hb.2 (by decide) d hd).1, ?_⟩
      intro d hd
      exact ⟨hunit d hd, m, hm, (hb.2 (by decide) d hd).2⟩

variable {params : RegularizationParameters} {q p N : ℕ} {theta epsilon : Fin 3 → ℝ}
  {epsilon0 ell : ℝ} {r : E → F} {x s : ℕ → E} {sigma : ℕ → ℝ}

/-- Objective monotonicity on an actual prefix gives residual norm monotonicity. -/
theorem RunPrefix.residual_norm_nonincrease
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {k : ℕ} (hk : k < N) : ‖r (x (k + 1))‖ ≤ ‖r (x k)‖ := by
  have hell : 0 < ell := by linarith [h.exponent_ge_two]
  have hm := h.toARpPrefix.toTrialPrefix.objective_nonincrease hk
  change ‖r (x (k + 1))‖ ^ ell / ell ≤ ‖r (x k)‖ ^ ell / ell at hm
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hell).mp
    ((div_le_div_iff_of_pos_right hell).mp hm)

/-- Every residual norm along a legal prefix is bounded by the initial norm. -/
theorem RunPrefix.residual_norm_le_initial
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {k : ℕ} (hk : k ≤ N) : ‖r (x k)‖ ≤ ‖r (x 0)‖ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (h.residual_norm_nonincrease (by omega)).trans (ih (by omega))

/-- A legal residual prefix restricts to any earlier trial index. -/
theorem RunPrefix.restrict
    (h : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma N)
    {M : ℕ} (hM : M ≤ N) : RunPrefix params q p theta epsilon epsilon0 r ell x s sigma M where
  initial_lower := h.toARpPrefix.initial_lower
  update k hk := h.toARpPrefix.update k (hk.trans_le hM)
  decrease k hk := h.toARpPrefix.decrease k (hk.trans_le hM)
  iterate k hk := h.toARpPrefix.iterate k (hk.trans_le hM)
  order_pos := h.toARpPrefix.order_pos
  order_le_three := h.toARpPrefix.order_le_three
  degree_ge_order := h.toARpPrefix.degree_ge_order
  theta_pos := h.toARpPrefix.theta_pos
  theta_le_one := h.toARpPrefix.theta_le_one
  epsilon_pos := h.toARpPrefix.epsilon_pos
  residuals k hk := h.toARpPrefix.residuals k (hk.trans_le hM)
  exponent_ge_two := h.exponent_ge_two
  residual_tolerance_pos := h.residual_tolerance_pos

end Optimization.ResidualRegularization
