import Numlib.Optimization.Regularization.Constrained.TerminalRadii
import Numlib.Optimization.Regularization.HighOrder.Monotone
import Numlib.Optimization.Constrained.TwoPhase.Run

/-!
# Complete inner executions for a repaired two-phase target method

Every old-target call is completed at fixed absolute all-order accuracies.
Quantitative certificate radii are extracted from its actual terminal run;
no radius floor or outer progress is an execution field. Closed reset,
reflection, fallback and updated-target tests determine the outer method.
-/

namespace Constrained.TwoPhase
open Set InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Natural inputs for extracting quantitative radii from an actual completed
constrained inner execution. Its fields contain no certificate or radius floor. -/
structure CompletedRadiusInputs {p q : ℕ} (m : E → ℝ) (X : Set E)
    (P : ConstrainedRegularization.Settings p q) (ε : Fin q → ℝ)
    (D : ConstrainedRegularization.ExecutionData E q) (K : ℕ) (L : ℝ) : Prop where
  closed : IsClosed X
  convex : Convex ℝ X
  smooth : ContDiff ℝ p m
  constant : 1 ≤ L
  lipschitz : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
    ‖iteratedFDeriv ℝ i m y - iteratedFDeriv ℝ i m z‖ ≤ L * ‖y - z‖
  run : ConstrainedRegularization.Run m X P ε D K
  target : ConstrainedRegularization.TargetAt m X P ε D K
  initial_radius : ∀ a, D.radius 0 a = 1

/-- Extract genuine quantitative terminal certificate radii from the proved
inner solver theorem. The default is unused whenever the natural inputs hold. -/
noncomputable def completedRadius {p q : ℕ} (m : E → ℝ) (X : Set E)
    (P : ConstrainedRegularization.Settings p q) (ε : Fin q → ℝ)
    (D : ConstrainedRegularization.ExecutionData E q) (K : ℕ) (L : ℝ) : Fin q → ℝ := by
  classical
  exact if h : CompletedRadiusInputs m X P ε D K L then
    Classical.choose (h.run.target_optimality_with_radius_floor h.closed h.convex
      h.smooth h.constant h.lipschitz h.initial_radius h.target)
    else fun _ => 1

/-- The extracted radii have actual optimality and a fixed quantitative floor
because the complete inner execution satisfies the terminal solver theorem. -/
theorem completedRadius_spec {p q : ℕ} {m : E → ℝ} {X : Set E}
    {P : ConstrainedRegularization.Settings p q} {ε : Fin q → ℝ}
    {D : ConstrainedRegularization.ExecutionData E q} {K : ℕ} {L : ℝ}
    (h : CompletedRadiusInputs m X P ε D K L) :
    ConstrainedRegularization.OptimalityAt m X ε (D.point K)
      (completedRadius m X P ε D K L) ∧
    ∀ a, ConstrainedRegularization.radiusCoefficient P L
      (HighOrderRegularization.parameterCap P L) * ε a ≤ completedRadius m X P ε D K L a := by
  classical
  rw [completedRadius, dite_eq_left h]
  exact Classical.choose_spec (h.run.target_optimality_with_radius_floor h.closed h.convex
    h.smooth h.constant h.lipschitz h.initial_radius h.target)

/-- Fixed absolute inner accuracies with a strict margin below the outer tests. -/
def completedInnerAccuracy {q : ℕ} (β θ ε₀ : ℝ) (ε : Fin q → ℝ) : Fin q → ℝ :=
  fun a => β * θ * ε₀ * ε a

/-- Actual outer points and targets, and complete primitive inner execution arrays. -/
structure CompletedData (E : Type*) (q : ℕ) where
  point : ℕ → E
  target : ℕ → ℝ
  inner : ℕ → ConstrainedRegularization.ExecutionData E q
  length : ℕ → ℕ

variable {F : Type*} [NormedAddCommGroup F]

/-- Every actual normalized all-order target-merit test passes at the supplied radii. -/
def CompletedMeritTarget {q : ℕ} (f : E → ℝ) (c : E → F) (X : Set E)
    (ε : Fin q → ℝ) (t : ℝ) (x : E) (δ : Fin q → ℝ) : Prop :=
  ∀ a, TaylorModel.constrainedCriticality (targetMerit f c t) (modelOrder a) X x (δ a) ≤
    ε a * ‖residual f c t x‖ * δ a ^ modelOrder a / (modelOrder a).factorial

/-- The repaired method returns by its actual fallback guard or by all actual
updated-target criticality tests, at radii extracted from the completed inner call. -/
def CompletedStopAfter {p q : ℕ} (f : E → ℝ) (c : E → F) (X : Set E)
    (P : ConstrainedRegularization.Settings p q) (β θ ε₀ L : ℝ) (ε : Fin q → ℝ)
    (D : CompletedData E q) (k : ℕ) : Prop :=
  (¬ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1)) ∧
    D.target k ≤ f (D.point (k + 1))) ∨
  CompletedMeritTarget f c X ε
    (nextTarget true f c ε₀ θ (D.target k) (D.point (k + 1))) (D.point (k + 1))
    (completedRadius (targetMerit f c (D.target k)) X P
      (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L)

/-- A primitive completed-inner replacement of the target method. Only actual
inner traces, terminal tests and target/point updates are fields. -/
structure CompletedRun {p q : ℕ} (f : E → ℝ) (c : E → F) (X : Set E)
    (P : ConstrainedRegularization.Settings p q) (β θ ε₀ L : ℝ) (ε : Fin q → ℝ)
    (D : CompletedData E q) (N : ℕ) : Prop where
  margin_pos : 0 < β
  margin_lt_one : β < 1
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  primal_pos : 0 < ε₀
  primal_le_one : ε₀ ≤ 1
  dual_pos : ∀ a, 0 < ε a
  dual_le_one : ∀ a, ε a ≤ 1
  initial_mem : D.point 0 ∈ X
  initial_constraint : ‖c (D.point 0)‖ ≤ θ * ε₀
  initial_target : D.target 0 = resetTarget f c ε₀ (D.point 0)
  inner_run : ∀ k < N, ConstrainedRegularization.Run (targetMerit f c (D.target k)) X P
    (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k)
  inner_target : ∀ k < N, ConstrainedRegularization.TargetAt
    (targetMerit f c (D.target k)) X P (completedInnerAccuracy β θ ε₀ ε)
      (D.inner k) (D.length k)
  inner_first : ∀ k < N, ∀ i < D.length k, ¬ConstrainedRegularization.TargetAt
    (targetMerit f c (D.target k)) X P (completedInnerAccuracy β θ ε₀ ε) (D.inner k) i
  inner_radius : ∀ k < N, ∀ a, (D.inner k).radius 0 a = 1
  inner_start : ∀ k < N, (D.inner k).point 0 = D.point k
  inner_end : ∀ k < N, (D.inner k).point (D.length k) = D.point (k + 1)
  target_update : ∀ k < N, D.target (k + 1) =
    nextTarget true f c ε₀ θ (D.target k) (D.point (k + 1))
  continues : ∀ k, k + 1 < N → ¬CompletedStopAfter f c X P β θ ε₀ L ε D k

namespace CompletedRun
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {X : Set E}
  {P : ConstrainedRegularization.Settings p q} {β θ ε₀ L : ℝ} {ε : Fin q → ℝ}
  {D : CompletedData E q} {N : ℕ}

/-- Every shorter prefix retains every primitive completed-inner rule. -/
theorem restrict (h : CompletedRun f c X P β θ ε₀ L ε D N) {M : ℕ} (hM : M ≤ N) :
    CompletedRun f c X P β θ ε₀ L ε D M := {
  h with
  inner_run := fun k hk => h.inner_run k (hk.trans_le hM)
  inner_target := fun k hk => h.inner_target k (hk.trans_le hM)
  inner_first := fun k hk => h.inner_first k (hk.trans_le hM)
  inner_radius := fun k hk => h.inner_radius k (hk.trans_le hM)
  inner_start := fun k hk => h.inner_start k (hk.trans_le hM)
  inner_end := fun k hk => h.inner_end k (hk.trans_le hM)
  target_update := fun k hk => h.target_update k (hk.trans_le hM)
  continues := fun k hk => h.continues k (hk.trans_le hM) }

/-- Every actual outer point is feasible by its genuine constrained inner execution. -/
theorem mem (h : CompletedRun f c X P β θ ε₀ L ε D N) {k : ℕ} (hk : k ≤ N) :
    D.point k ∈ X := by
  cases k with
  | zero => exact h.initial_mem
  | succ k =>
    rw [← h.inner_end k (by omega)]
    exact (h.inner_run k (by omega)).point_mem le_rfl

/-- True inner objective updates imply nonincrease of the old-target residual. -/
theorem inner_residual_le (h : CompletedRun f c X P β θ ε₀ L ε D N)
    {k : ℕ} (hk : k < N) :
    ‖residual f c (D.target k) (D.point (k + 1))‖ ≤
      ‖residual f c (D.target k) (D.point k)‖ := by
  apply residual_le_of_merit_le
  rw [← h.inner_start k hk, ← h.inner_end k hk]
  exact (h.inner_run k hk).modelTrace.objective_le (Nat.zero_le _) le_rfl

/-- All nonnegative target gaps and primal residual bounds follow from the
actual completed inner executions and the exact target updates. -/
theorem invariants (h : CompletedRun f c X P β θ ε₀ L ε D N)
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

/-- Every actual target update is nonincreasing, with the fixed reset decrease
obtained from the old residual disk. -/
theorem target_succ_le (h : CompletedRun f c X P β θ ε₀ L ε D N)
    {k : ℕ} (hk : k < N) : D.target (k + 1) ≤ D.target k := by
  rw [h.target_update k hk]
  unfold nextTarget
  split_ifs with hr hover
  · have hd := reset_decrease h.primal_pos.le h.theta_pos.le h.theta_lt_one.le hr.le
    have hz : 0 < (1 - θ) * ε₀ := by have := h.theta_lt_one; have := h.primal_pos; positivity
    linarith
  · exact (reflect_lt hover).le
  · rfl

/-- A bounded objective in the near-feasible band gives a fixed interval for
every target generated by actual completed inner calls. -/
theorem target_bounds (h : CompletedRun f c X P β θ ε₀ L ε D N)
    {flow fup : ℝ}
    (hf : ∀ z ∈ X, ‖c z‖ ≤ 1 → flow ≤ f z ∧ f z ≤ fup)
    {k : ℕ} (hk : k ≤ N) : flow - 1 ≤ D.target k ∧ D.target k ≤ fup := by
  have hres := (h.invariants hk).2
  have hc := (constraint_norm_le_residual f c (D.target k) (D.point k)).trans hres
  obtain ⟨hlo, hup⟩ := hf _ (h.mem hk) (hc.trans h.primal_le_one)
  have hgap := (abs_gap_le_residual f c (D.target k) (D.point k)).trans hres
  have hnonneg := (h.invariants hk).1
  have hgapupper := (le_abs_self (f (D.point k) - D.target k)).trans hgap
  constructor <;> linarith [h.primal_le_one]

end CompletedRun
end Constrained.TwoPhase
