import Numlib.Optimization.Regularization.Convex.FirstOrder
import Numlib.Optimization.Constrained.TwoPhase.Target

/-!
# Actual two-phase target iterations with primitive inner executions

Index zero denotes the book's first Phase2 point. Each inner call is a genuine
first-order ARp-CC execution interrupted at its first actual return test. Literal
and repaired reset guards are separate modes: the repair closes the reset branch
at residual equality, leaving the inner test and all other rules unchanged.
-/

namespace Constrained.TwoPhase
open Set TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

/-- The genuine constrained first-order Taylor optimality measure. -/
noncomputable def firstCriticality (h : E → ℝ) (C : Set E) (x : E) : ℝ :=
  constrainedCriticality h 1 C x 1

/-- The literal inner return test(7.2.10), including its nonstrict residual branch. -/
def InnerReturn (f : E → ℝ) (c : E → F) (C : Set E) (ε₀ ε₁ θ t : ℝ) (x : E) : Prop :=
  ‖residual f c t x‖ ≤ θ * ε₀ ∨ f x < t ∨
    firstCriticality (targetMerit f c t) C x ≤ ε₁ * ‖residual f c t x‖

/-- Literal Step2 resets strictly below the threshold; the repaired guard
includes equality so that every residual-based inner return triggers reset. -/
def ResetGuard (closedReset : Bool) (f : E → ℝ) (c : E → F) (ε₀ θ t : ℝ)
    (x : E) : Prop :=
  if closedReset then ‖residual f c t x‖ ≤ θ * ε₀ else ‖residual f c t x‖ < θ * ε₀

/-- The actual next target follows reset, reflection or unchanged terminal target. -/
noncomputable def nextTarget (closedReset : Bool) (f : E → ℝ) (c : E → F)
    (ε₀ θ t : ℝ) (x : E) : ℝ := by
  classical
  exact if ResetGuard closedReset f c ε₀ θ t x then resetTarget f c ε₀ x
    else if f x < t then reflectTarget f t x else t

/-- A small actual constrained merit derivative, normalized by the actual residual. -/
def MeritTarget (f : E → ℝ) (c : E → F) (C : Set E) (ε₁ t : ℝ) (x : E) : Prop :=
  firstCriticality (targetMerit f c t) C x ≤ ε₁ * ‖residual f c t x‖

/-- Literal Step2(c) or the actual updated-target criticality test terminates. -/
def StopAfter (closedReset : Bool) (f : E → ℝ) (c : E → F) (C : Set E)
    (ε₀ ε₁ θ t : ℝ) (x : E) : Prop :=
  (¬ResetGuard closedReset f c ε₀ θ t x ∧ t ≤ f x) ∨
    MeritTarget f c C ε₁ (nextTarget closedReset f c ε₀ θ t x) x

/-- Actual outer points, targets and complete primitive inner-call arrays. -/
structure Data (E : Type*) where
  point : ℕ → E
  target : ℕ → ℝ
  inner : ℕ → ConvexRegularization.Data E
  length : ℕ → ℕ

/-- A finite actual Phase2 execution. Inner accuracy `ε₁ θ ε₀` is a fixed
legal first-order tolerance for each call, and the caller interrupts at the first
literal return test. No target decrease, residual bound or count is assumed. -/
structure PhaseTwoRun {p : ℕ} (closedReset : Bool) (f : E → ℝ) (c : E → F)
    (C : Set E) (P : ConvexRegularization.Settings p) (ε₀ ε₁ θ : ℝ)
    (D : Data E) (N : ℕ) : Prop where
  primal_pos : 0 < ε₀
  primal_le_one : ε₀ ≤ 1
  dual_pos : 0 < ε₁
  dual_le_one : ε₁ ≤ 1
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  initial_mem : D.point 0 ∈ C
  initial_constraint : ‖c (D.point 0)‖ ≤ θ * ε₀
  initial_target : D.target 0 = resetTarget f c ε₀ (D.point 0)
  inner_run : ∀ k < N, ConvexRegularization.Run (targetMerit f c (D.target k)) C P
    (ε₁ * θ * ε₀) (D.inner k) (D.length k)
  inner_start : ∀ k < N, (D.inner k).point 0 = D.point k
  inner_end : ∀ k < N, (D.inner k).point (D.length k) = D.point (k + 1)
  inner_return : ∀ k < N, InnerReturn f c C ε₀ ε₁ θ (D.target k) (D.point (k + 1))
  inner_first : ∀ k < N, ∀ i < D.length k,
    ¬InnerReturn f c C ε₀ ε₁ θ (D.target k) ((D.inner k).point i)
  target_update : ∀ k < N, D.target (k + 1) =
    nextTarget closedReset f c ε₀ θ (D.target k) (D.point (k + 1))
  continues : ∀ k, k + 1 < N →
    ¬StopAfter closedReset f c C ε₀ ε₁ θ (D.target k) (D.point (k + 1))

/-- The actual literal Phase2 rule uses the printed strict reset guard. -/
abbrev LiteralPhaseTwoRun {p : ℕ} := @PhaseTwoRun E F _ _ _ p false

/-- The corrected Phase2 rule changes only the reset guard to include equality. -/
abbrev CorrectedPhaseTwoRun {p : ℕ} := @PhaseTwoRun E F _ _ _ p true

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Either reset guard implies the common closed residual-disk bound. -/
theorem ResetGuard.le {closedReset : Bool} {f : E → ℝ} {c : E → F}
    {ε₀ θ t : ℝ} {x : E} (h : ResetGuard closedReset f c ε₀ θ t x) :
    ‖residual f c t x‖ ≤ θ * ε₀ := by
  cases closedReset <;> simp only [ResetGuard, Bool.false_eq_true, ite_false,
    ite_true] at h
  · exact h.le
  · exact h

variable {p : ℕ} {closedReset : Bool} {f : E → ℝ} {c : E → F} {C : Set E}
  {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ : ℝ} {D : Data E} {N : ℕ}

/-- All actual outer points inherit feasibility from genuine inner executions. -/
theorem PhaseTwoRun.mem (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N)
    {k : ℕ} (hk : k ≤ N) : D.point k ∈ C := by
  cases k with
  | zero => exact h.initial_mem
  | succ k =>
    rw [←h.inner_end k (by omega)]
    exact (h.inner_run k (by omega)).mem le_rfl

/-- Actual primitive inner objective nonincrease gives actual residual nonincrease. -/
theorem PhaseTwoRun.inner_residual_le
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) {k : ℕ} (hk : k < N) :
    ‖residual f c (D.target k) (D.point (k + 1))‖ ≤
      ‖residual f c (D.target k) (D.point k)‖ := by
  apply residual_le_of_merit_le
  rw [←h.inner_start k hk, ←h.inner_end k hk]
  exact (h.inner_run k hk).objective_le (Nat.zero_le _) le_rfl

/-- The repaired Step2 cannot terminate through fallback without an actual
normalized merit certificate: every residual-based inner return resets first. -/
theorem CorrectedPhaseTwoRun.target_of_stop
    (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N) {k : ℕ} (hk : k < N)
    (hs : StopAfter true f c C ε₀ ε₁ θ (D.target k) (D.point (k + 1))) :
    MeritTarget f c C ε₁ (D.target (k + 1)) (D.point (k + 1)) := by
  rw [h.target_update k hk]
  rcases hs with ⟨hreset, hgap⟩ | htarget
  · have hn : ¬‖residual f c (D.target k) (D.point (k + 1))‖ ≤ θ * ε₀ := by
      simpa only [ResetGuard, ite_true] using hreset
    rcases h.inner_return k hk with hr | hover | hcrit
    · exact (hn hr).elim
    · exact (not_lt_of_ge hgap hover).elim
    · have ht : nextTarget true f c ε₀ θ (D.target k) (D.point (k + 1)) = D.target k := by
        simp only [nextTarget, ite_eq_right hreset, ite_eq_right (not_lt_of_ge hgap)]
      simpa only [MeritTarget, ht] using hcrit
  · exact htarget

end Constrained.TwoPhase
