import Numlib.Optimization.Constrained.TwoPhase.Run

/-!
# Derived invariants and reset counts for actual two-phase executions

Primitive inner model acceptance gives residual nonincrease. Exact target
updates then yield all outer residual/gap bounds and a fixed decrease on every
reset. The bounded objective range pays for the actual reset count.
-/

namespace Constrained.TwoPhase
open Set TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] {p : ℕ} {closedReset : Bool} {f : E → ℝ} {c : E → F}
  {C : Set E} {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ : ℝ} {D : Data E} {N : ℕ}

/-- Nonnegative target gaps and primal residual bounds are consequences of
actual inner executions and the three literal target-update branches. -/
theorem PhaseTwoRun.invariants (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N)
    {k : ℕ} (hk : k ≤ N) :
    0 ≤ f (D.point k) - D.target k ∧ ‖residual f c (D.target k) (D.point k)‖ ≤ ε₀ := by
  induction k with
  | zero =>
    rw [h.initial_target]
    have hc : ‖c (D.point 0)‖ ≤ ε₀ := h.initial_constraint.trans
      (mul_le_of_le_one_left h.primal_pos.le h.theta_lt_one.le)
    exact ⟨reset_gap_nonneg _ _ _ _, (residual_reset h.primal_pos.le hc).le⟩
  | succ k ih =>
    have hkN : k < N := by omega
    have hres := (h.inner_residual_le hkN).trans (ih (by omega)).2
    have hc := (constraint_norm_le_residual f c (D.target k) (D.point (k + 1))).trans hres
    rw [h.target_update k hkN]
    unfold nextTarget
    split_ifs with hreset hover
    · exact ⟨reset_gap_nonneg _ _ _ _, (residual_reset h.primal_pos.le hc).le⟩
    · exact ⟨(reflect_gap_pos hover).le, by rw [residual_reflect]; exact hres⟩
    · exact ⟨sub_nonneg.mpr (not_lt.mp hover), hres⟩

/-- Every reset gives exactly the primal-tolerance augmented residual norm. -/
theorem PhaseTwoRun.reset_residual (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N)
    {k : ℕ} (hk : k < N)
    (hr : ResetGuard closedReset f c ε₀ θ (D.target k) (D.point (k + 1))) :
    ‖residual f c (D.target (k + 1)) (D.point (k + 1))‖ = ε₀ := by
  have hc := (constraint_norm_le_residual f c (D.target k) (D.point (k + 1))).trans
    ((h.inner_residual_le hk).trans (h.invariants hk.le).2)
  rw [h.target_update k hk, nextTarget, ite_eq_left hr]
  exact residual_reset h.primal_pos.le hc

/-- Actual reflection preserves the old-target residual, which never exceeds
its current primal bound. -/
theorem PhaseTwoRun.reflection_residual
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) {k : ℕ} (hk : k < N)
    (hr : ¬ResetGuard closedReset f c ε₀ θ (D.target k) (D.point (k + 1)))
    (hf : f (D.point (k + 1)) < D.target k) :
    ‖residual f c (D.target (k + 1)) (D.point (k + 1))‖ =
      ‖residual f c (D.target k) (D.point (k + 1))‖ ∧
      ‖residual f c (D.target k) (D.point (k + 1))‖ ≤ ε₀ := by
  refine ⟨?_, (h.inner_residual_le hk).trans (h.invariants hk.le).2⟩
  rw [h.target_update k hk, nextTarget, ite_eq_right hr, ite_eq_left hf, residual_reflect]

/-- The actual target decreases by at least `(1−θ) ε₀` on each reset. -/
theorem PhaseTwoRun.reset_drop (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N)
    {k : ℕ} (hk : k < N)
    (hr : ResetGuard closedReset f c ε₀ θ (D.target k) (D.point (k + 1))) :
    (1 - θ) * ε₀ ≤ D.target k - D.target (k + 1) := by
  rw [h.target_update k hk, nextTarget, ite_eq_left hr]
  exact reset_decrease h.primal_pos.le h.theta_pos.le h.theta_lt_one.le hr.le

/-- All actual target-update branches are nonincreasing. -/
theorem PhaseTwoRun.target_succ_le
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) {k : ℕ} (hk : k < N) :
    D.target (k + 1) ≤ D.target k := by
  by_cases hr : ResetGuard closedReset f c ε₀ θ (D.target k) (D.point (k + 1))
  · have hh := h.reset_drop hk hr
    have hpos : 0 < (1 - θ) * ε₀ := mul_pos (sub_pos.mpr h.theta_lt_one) h.primal_pos
    linarith
  · rw [h.target_update k hk, nextTarget, ite_eq_right hr]
    split_ifs with hf
    · exact (reflect_lt hf).le
    · exact le_rfl

/-- Any later actual target is no greater than an earlier actual target. -/
theorem PhaseTwoRun.target_le (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : D.target j ≤ D.target i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (h.target_succ_le (by omega)).trans (ih (by omega))

/-- The actual constraints and nonnegative objective-target gaps are both
bounded by the requested primal tolerance. -/
theorem PhaseTwoRun.component_bounds
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) {k : ℕ} (hk : k ≤ N) :
    ‖c (D.point k)‖ ≤ ε₀ ∧ f (D.point k) - D.target k ≤ ε₀ := by
  have hh := h.invariants hk
  exact ⟨(constraint_norm_le_residual _ _ _ _).trans hh.2,
    (le_abs_self _).trans ((abs_gap_le_residual _ _ _ _).trans hh.2)⟩

/-- Bounds on the objective in the near-feasible region give the exact source
target interval, including the allowed endpoint `ε₀=1`. -/
theorem PhaseTwoRun.target_bounds
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) {β flow fup : ℝ} (hβ : ε₀ ≤ β)
    (hf : ∀ z ∈ C, ‖c z‖ ≤ β → flow ≤ f z ∧ f z ≤ fup) {k : ℕ} (hk : k ≤ N) :
    flow - 1 ≤ D.target k ∧ D.target k ≤ fup := by
  obtain ⟨hlo, hup⟩ := hf _ (h.mem hk) ((h.component_bounds hk).1.trans hβ)
  have hgap := (h.component_bounds hk).2
  have hnonneg := (h.invariants hk).1
  constructor <;> linarith [h.primal_le_one]

/-- The actual reset indices in the first N outer returns. -/
noncomputable def resetIterations (closedReset : Bool) (f : E → ℝ) (c : E → F)
    (ε₀ θ : ℝ) (D : Data E) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun k =>
    ResetGuard closedReset f c ε₀ θ (D.target k) (D.point (k + 1)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Reset membership is exactly the actual guarded target branch. -/
@[simp] theorem mem_resetIterations {k : ℕ} :
    k ∈ resetIterations closedReset f c ε₀ θ D N ↔ k < N ∧
      ResetGuard closedReset f c ε₀ θ (D.target k) (D.point (k + 1)) := by
  classical
  simp only [resetIterations, Finset.mem_filter, Finset.mem_range]

/-- The bounded actual target range pays for every reset, giving the printed
inverse-primal-tolerance outer-reset bound with its exact constant. -/
theorem PhaseTwoRun.card_resets_le
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) {β flow fup : ℝ} (hβ : ε₀ ≤ β)
    (hf : ∀ z ∈ C, ‖c z‖ ≤ β → flow ≤ f z ∧ f z ≤ fup) :
    ((resetIterations closedReset f c ε₀ θ D N).card : ℝ) ≤
      (fup - flow + 1) / (1 - θ) * ε₀⁻¹ := by
  classical
  let K := resetIterations closedReset f c ε₀ θ D N
  let d := (1 - θ) * ε₀
  have hd : 0 < d := mul_pos (sub_pos.mpr h.theta_lt_one) h.primal_pos
  have hsum : (K.card : ℝ) * d ≤ D.target 0 - D.target N := by
    calc
      _ = ∑ _k ∈ K, d := by simp
      _ ≤ ∑ k ∈ K, (D.target k - D.target (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hkN, hr⟩ := mem_resetIterations.mp hk
        exact h.reset_drop hkN hr
      _ ≤ ∑ k ∈ Finset.range N, (D.target k - D.target (k + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro k hk _
          exact sub_nonneg.mpr (h.target_succ_le (Finset.mem_range.mp hk))
      _ = _ := Finset.sum_range_sub' D.target N
  have hstart := (h.target_bounds hβ hf (Nat.zero_le N)).2
  have hend := (h.target_bounds hβ hf le_rfl).1
  have hh : (K.card : ℝ) ≤ (fup - flow + 1) / d := (le_div_iff₀ hd).mpr (by linarith)
  have he : (fup - flow + 1) / d = (fup - flow + 1) / (1 - θ) * ε₀⁻¹ := by
    dsimp [d]
    rw [div_mul_eq_div_div, div_eq_mul_inv]
  simpa only [K, he] using hh

end Constrained.TwoPhase
