import Numlib.Optimization.Constrained.TwoPhase.CompletedRun

/-!
# Constructed completed-inner outer executions

Actual constrained inner solves produce first-target endpoints. Exact closed
reset, reflection and fallback target updates preserve the feasible residual
band at every state, including continuations after an outer stopping check.
Recursion constructs total arrays without an execution-availability assumption.
-/

namespace Constrained.TwoPhase
open Set InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F]

/-- A feasible outer point and target in the actual primal residual band. -/
structure CompletedState (f : E → ℝ) (c : E → F) (X : Set E) (ε₀ : ℝ) where
  point : E
  target : ℝ
  mem : point ∈ X
  gap_nonneg : 0 ≤ f point - target
  residual_le : ‖residual f c target point‖ ≤ ε₀

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Actual objective bounds on the near-feasible band give the target interval. -/
theorem CompletedState.target_bounds {f : E → ℝ} {c : E → F} {X : Set E}
    {ε₀ flow fup : ℝ} (z : CompletedState f c X ε₀) (hε₀ : ε₀ ≤ 1)
    (hband : ∀ x ∈ X, ‖c x‖ ≤ 1 → flow ≤ f x ∧ f x ≤ fup) :
    z.target ∈ Icc (flow - 1) fup := by
  have hc := (constraint_norm_le_residual f c z.target z.point).trans z.residual_le
  obtain ⟨hlo, hup⟩ := hband _ z.mem (hc.trans hε₀)
  have hg := (le_abs_self (f z.point - z.target)).trans
    ((abs_gap_le_residual f c z.target z.point).trans z.residual_le)
  exact ⟨by linarith, by linarith [z.gap_nonneg]⟩

/-- An actual completed constrained solve, including first-target and initialization rules. -/
structure CompletedCall (f : E → ℝ) (c : E → F) (X : Set E) {p q : ℕ}
    (P : ConstrainedRegularization.Settings p q) (ε : Fin q → ℝ) {ε₀ : ℝ}
    (z : CompletedState f c X ε₀) where
  data : ConstrainedRegularization.ExecutionData E q
  length : ℕ
  start : data.point 0 = z.point
  run : ConstrainedRegularization.Run (targetMerit f c z.target) X P ε data length
  target : ConstrainedRegularization.TargetAt (targetMerit f c z.target) X P ε data length
  first : ∀ i < length, ¬ConstrainedRegularization.TargetAt
    (targetMerit f c z.target) X P ε data i
  initial_radius : ∀ a, data.radius 0 a = 1

/-- The actual constrained solver constructs a complete inner execution at every legal state. -/
theorem exists_completedCall (f : E → ℝ) (c : E → F) (X : Set E)
    (hX : IsClosed X) (hconv : Convex ℝ X) {p q : ℕ}
    (P : ConstrainedRegularization.Settings p q) {ε₀ L flow fup : ℝ} (hε₀ : ε₀ ≤ 1)
    (hL : 1 ≤ L) (hband : ∀ x ∈ X, ‖c x‖ ≤ 1 → flow ≤ f x ∧ f x ≤ fup)
    (hreg : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
      ∀ i, 1 ≤ i → i ≤ p → ∀ y w,
        ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
          iteratedFDeriv ℝ i (targetMerit f c t) w‖ ≤ L * ‖y - w‖)
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (z : CompletedState f c X ε₀) : Nonempty (CompletedCall f c X P ε z) := by
  obtain ⟨hsm, hlip⟩ := hreg z.target (z.target_bounds hε₀ hband)
  have hlow : ∀ x ∈ X, 0 ≤ targetMerit f c z.target x := by
    intro x _
    rw [targetMerit_eq_residual]
    positivity
  obtain ⟨_, _, _, _, _, _, hall⟩ := ConstrainedRegularization.exists_certified_execution
    (targetMerit f c z.target) X hX hconv P z.point z.mem hsm hL hlip hlow
  obtain ⟨D, K, _, hx, _, hδ, hr, ht, hfirst, _⟩ := hall ε hε
  exact ⟨⟨D, K, hx, hr, ht, hfirst, hδ⟩⟩

/-- Actual endpoints and exact target updates preserve admissibility even after stopping. -/
noncomputable def advanceCompletedState {f : E → ℝ} {c : E → F} {X : Set E}
    {p q : ℕ} {P : ConstrainedRegularization.Settings p q} {ε : Fin q → ℝ}
    {ε₀ θ : ℝ} (hε₀ : 0 ≤ ε₀) (z : CompletedState f c X ε₀)
    (t : CompletedCall f c X P ε z) : CompletedState f c X ε₀ := by
  classical
  let x := t.data.point t.length
  have hmem : x ∈ X := t.run.point_mem le_rfl
  have hres : ‖residual f c z.target x‖ ≤ ε₀ := by
    apply le_trans _ z.residual_le
    apply residual_le_of_merit_le
    rw [←t.start]
    exact t.run.modelTrace.objective_le (Nat.zero_le _) le_rfl
  have hc := (constraint_norm_le_residual f c z.target x).trans hres
  have hg : 0 ≤ f x - nextTarget true f c ε₀ θ z.target x ∧
      ‖residual f c (nextTarget true f c ε₀ θ z.target x) x‖ ≤ ε₀ := by
    unfold nextTarget
    split_ifs with hr hover
    · exact ⟨reset_gap_nonneg _ _ _ _, (residual_reset hε₀ hc).le⟩
    · exact ⟨(reflect_gap_pos hover).le, by rw [residual_reflect]; exact hres⟩
    · exact ⟨sub_nonneg.mpr (not_lt.mp hover), hres⟩
  exact ⟨x, nextTarget true f c ε₀ θ z.target x, hmem, hg.1, hg.2⟩

/-- Genuine completed inner solves recursively construct total outer arrays.
Every prefix before the actual outer stopping checks satisfies all primitive
rules. Uniform smoothness is required only for targets in the derived interval;
no outer execution, stopping index, decrease floor or budget is assumed. -/
theorem exists_completed_execution (f : E → ℝ) (c : E → F) (X : Set E)
    (hX : IsClosed X) (hconv : Convex ℝ X) {p q : ℕ}
    (P : ConstrainedRegularization.Settings p q) {β θ ε₀ L flow fup : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hL : 1 ≤ L)
    (hband : ∀ x ∈ X, ‖c x‖ ≤ 1 → flow ≤ f x ∧ f x ≤ fup)
    (hreg : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
      ∀ i, 1 ≤ i → i ≤ p → ∀ y w,
        ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
          iteratedFDeriv ℝ i (targetMerit f c t) w‖ ≤ L * ‖y - w‖)
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (x₀ : E) (hx₀ : x₀ ∈ X) (hc₀ : ‖c x₀‖ ≤ θ * ε₀) :
    ∃ D : CompletedData E q, D.point 0 = x₀ ∧
      ∀ N, (∀ k, k + 1 < N → ¬CompletedStopAfter f c X P β θ ε₀ L ε D k) →
        CompletedRun f c X P β θ ε₀ L ε D N := by
  classical
  have hc : ‖c x₀‖ ≤ ε₀ := hc₀.trans (mul_le_of_le_one_left hε₀.le hθ1.le)
  let z₀ : CompletedState f c X ε₀ := ⟨x₀, resetTarget f c ε₀ x₀, hx₀,
    reset_gap_nonneg _ _ _ _, (residual_reset hε₀.le hc).le⟩
  have hα : ∀ a, 0 < completedInnerAccuracy β θ ε₀ ε a ∧
      completedInnerAccuracy β θ ε₀ ε a ≤ 1 := by
    intro a
    dsimp only [completedInnerAccuracy]
    refine ⟨by have := (hε a).1; positivity, ?_⟩
    have hbt : β * θ ≤ 1 :=
      (mul_le_of_le_one_left hθ.le hβ1.le).trans hθ1.le
    have hbte : β * θ * ε₀ ≤ 1 :=
      (mul_le_of_le_one_left hε₀.le hbt).trans hε₀1
    exact (mul_le_of_le_one_left (hε a).1.le hbte).trans (hε a).2
  let trial : (z : CompletedState f c X ε₀) →
      CompletedCall f c X P (completedInnerAccuracy β θ ε₀ ε) z :=
    fun z => Classical.choice (exists_completedCall f c X hX hconv P hε₀1 hL hband hreg
      (completedInnerAccuracy β θ ε₀ ε) hα z)
  let z : ℕ → CompletedState f c X ε₀ :=
    fun n => Nat.rec z₀ (fun _ w => advanceCompletedState (θ := θ) hε₀.le w (trial w)) n
  let D : CompletedData E q := {
    point := fun k => (z k).point
    target := fun k => (z k).target
    inner := fun k => (trial (z k)).data
    length := fun k => (trial (z k)).length }
  refine ⟨D, rfl, ?_⟩
  intro N hnot
  exact {
    margin_pos := hβ
    margin_lt_one := hβ1
    theta_pos := hθ
    theta_lt_one := hθ1
    primal_pos := hε₀
    primal_le_one := hε₀1
    dual_pos := fun a => (hε a).1
    dual_le_one := fun a => (hε a).2
    initial_mem := hx₀
    initial_constraint := hc₀
    initial_target := rfl
    inner_run := fun k _ => (trial (z k)).run
    inner_target := fun k _ => (trial (z k)).target
    inner_first := fun k _ => (trial (z k)).first
    inner_radius := fun k _ => (trial (z k)).initial_radius
    inner_start := fun k _ => (trial (z k)).start
    inner_end := fun _ _ => rfl
    target_update := fun _ _ => rfl
    continues := hnot }

end Constrained.TwoPhase
