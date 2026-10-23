import Numlib.Optimization.HighOrder.ConstrainedCriticality
import Numlib.Optimization.HighOrder.CriticalityApproximate
import Numlib.Analysis.SpecialFunctions.Log.GeometricBudget
import Numlib.Optimization.TrustRegion.Inexact.Selection

/-!
# Operational least-Euclidean-norm outer iterations

An explicit inner-call relation supplies the actual computed point, radii and
evaluation counters. Its optimality interface is a separate hypothesis. Failure
of the actual outer stopping tests then forces residual contraction, and the
first true target follows from the resulting natural logarithmic budget.
-/

namespace LeastNorm
open TaylorModel InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]
/-- The actual least-squares merit associated with a residual map. -/
noncomputable def merit (r : E → F) (x : E) : ℝ := ‖r x‖ ^ 2 / 2
variable {q : ℕ}
/-- The soundness interface of an explicit inner-call relation, including actual endpoint
criticality. -/
def InnerSound (r : E → F) (X : Set E)
    (call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop) : Prop :=
  ∀ xs ε x δ nf nd, call xs ε x δ nf nd →
    x ∈ X ∧ (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      ∀ a, constrainedCriticality (merit r) (modelOrder a) X x (δ a) ≤
        ε a * δ a ^ modelOrder a / (modelOrder a).factorial

/-- The exact outer stopping rule, with the initial point tested for residual size only. -/
def TargetAt (r : E → F) (X : Set E) (ε₀ : ℝ) (ε : Fin q → ℝ)
    (x : ℕ → E) (δ : ℕ → Fin q → ℝ) (k : ℕ) : Prop :=
  if k = 0 then ‖r (x 0)‖ ≤ ε₀ else ‖r (x k)‖ ≤ ε₀ ∨
    ∀ a, constrainedCriticality (merit r) (modelOrder a) X (x k) (δ k a) ≤
      ε a * ‖r (x k)‖ * δ k a ^ modelOrder a / (modelOrder a).factorial

/-- Primitive finite least-norm executions with actual inner calls, counters and pre-target
tests. -/
structure Run (r : E → F) (X : Set E)
    (call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop)
    (ε₀ β : ℝ) (ε : Fin q → ℝ) (x : ℕ → E) (δ : ℕ → Fin q → ℝ)
    (nf nd : ℕ → ℕ) (N : ℕ) : Prop where
  primal_pos : 0 < ε₀
  primal_lt_one : ε₀ < 1
  accuracy : ∀ a, 0 < ε a ∧ ε a < 1
  contraction_pos : 0 < β
  contraction_lt_one : β < 1
  initial_scale : β * ‖r (x 0)‖ < 1
  initial_feasible : x 0 ∈ X
  not_terminated : ∀ k < N, ¬TargetAt r X ε₀ ε x δ k
  inner : ∀ k < N, call (x k) (fun a => β * ‖r (x k)‖ * ε a)
    (x (k + 1)) (δ (k + 1)) (nf k) (nd k)

namespace Run
variable {r : E → F} {X : Set E}
  {call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop}
  {ε₀ β : ℝ} {ε : Fin q → ℝ} {x : ℕ → E} {δ : ℕ → Fin q → ℝ}
  {nf nd : ℕ → ℕ} {N : ℕ}
/-- A nonterminal point has residual norm greater than the primal tolerance. -/
theorem residual_gt (h : Run r X call ε₀ β ε x δ nf nd N) {k : ℕ} (hk : k < N) :
    ε₀ < ‖r (x k)‖ := by
  have hn := h.not_terminated k hk
  by_cases hz : k = 0
  · subst k
    simpa only [TargetAt, ite_true, not_le] using hn
  · exact lt_of_not_ge (fun hb => hn (by simp only [TargetAt, ite_false, hz]; exact Or.inl hb))

/-- Actual inner optimality and failure of the true outer test force strict residual contraction. -/
theorem residual_contracts (h : Run r X call ε₀ β ε x δ nf nd N)
    (hsound : InnerSound r X call) {k : ℕ} (hk : k + 1 < N) :
    ‖r (x (k + 1))‖ < β * ‖r (x k)‖ := by
  classical
  obtain ⟨_, hδ, hc⟩ := hsound _ _ _ _ _ _ (h.inner k (by omega))
  have hn := h.not_terminated (k + 1) hk
  have hn' : ¬∀ a, constrainedCriticality (merit r) (modelOrder a) X
      (x (k + 1)) (δ (k + 1) a) ≤
        ε a * ‖r (x (k + 1))‖ * δ (k + 1) a ^ modelOrder a / (modelOrder a).factorial :=
    by
      intro hh
      apply hn
      simp only [TargetAt, show k + 1 ≠ 0 by omega, ite_false]
      exact Or.inr hh
  push Not at hn'
  obtain ⟨a, ha⟩ := hn'
  have hh := ha.trans_le (hc a)
  have hpos : 0 < ε a * δ (k + 1) a ^ modelOrder a / (modelOrder a).factorial := by
    exact div_pos (mul_pos (h.accuracy a).1 (pow_pos (hδ a).1 _)) (by positivity)
  have he : ε a * ‖r (x (k + 1))‖ * δ (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial =
      ‖r (x (k + 1))‖ * (ε a * δ (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial) := by ring
  rw [he] at hh
  have he' : β * ‖r (x k)‖ * ε a * δ (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial =
      (β * ‖r (x k)‖) * (ε a * δ (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial) := by ring
  rw [he'] at hh
  exact (mul_lt_mul_iff_left₀ hpos).mp hh
/-- Every finite prefix is again a primitive execution. -/
theorem restrict (h : Run r X call ε₀ β ε x δ nf nd N) {M : ℕ} (hM : M ≤ N) :
    Run r X call ε₀ β ε x δ nf nd M where
  primal_pos := h.primal_pos
  primal_lt_one := h.primal_lt_one
  accuracy := h.accuracy
  contraction_pos := h.contraction_pos
  contraction_lt_one := h.contraction_lt_one
  initial_scale := h.initial_scale
  initial_feasible := h.initial_feasible
  not_terminated := fun k hk => h.not_terminated k (hk.trans_le hM)
  inner := fun k hk => h.inner k (hk.trans_le hM)

/-- Every nonterminal residual satisfies the genuine geometric envelope. -/
theorem residual_le_geometric (h : Run r X call ε₀ β ε x δ nf nd N)
    (hsound : InnerSound r X call) {k : ℕ} (hk : k < N) :
    ‖r (x k)‖ ≤ ‖r (x 0)‖ * β ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := h.residual_contracts hsound hk
    have hi := mul_le_mul_of_nonneg_left (ih (by omega)) h.contraction_pos.le
    calc _ ≤ β * ‖r (x k)‖ := hh.le
      _ ≤ β * (‖r (x 0)‖ * β ^ k) := hi
      _ = _ := by rw [pow_succ]; ring

/-- A nonterminal index lies strictly before the natural logarithmic budget. -/
theorem nonterminal_index_lt_budget (h : Run r X call ε₀ β ε x δ nf nd N)
    (hsound : InnerSound r X call) {k : ℕ} (hk : k < N) :
    k < GeometricDecay.budget ‖r (x 0)‖ ε₀ β := by
  by_contra hn
  have hbk : GeometricDecay.budget ‖r (x 0)‖ ε₀ β ≤ k := Nat.le_of_not_gt hn
  have hpow := pow_le_pow_of_le_one h.contraction_pos.le h.contraction_lt_one.le hbk
  have hstep := mul_le_mul_of_nonneg_left hpow (norm_nonneg (r (x 0)))
  have hbound := GeometricDecay.bound_at_budget (norm_nonneg (r (x 0))) h.primal_pos
    h.contraction_pos h.contraction_lt_one
  have hh := (h.residual_le_geometric hsound hk).trans (hstep.trans hbound)
  exact (not_le_of_gt (h.residual_gt hk)) hh

/-- Every consistent pre-target prefix has length at most the logarithmic budget. -/
theorem iterations_le_budget (h : Run r X call ε₀ β ε x δ nf nd N)
    (hsound : InnerSound r X call) : N ≤ GeometricDecay.budget ‖r (x 0)‖ ε₀ β := by
  by_contra hn
  have hb : GeometricDecay.budget ‖r (x 0)‖ ε₀ β < N := Nat.lt_of_not_ge hn
  exact Nat.lt_irrefl _ (h.nonterminal_index_lt_budget hsound hb)
end Run

variable {r : E → F} {X : Set E}
  {call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop}
  {ε₀ β : ℝ} {ε : Fin q → ℝ} {x : ℕ → E} {δ : ℕ → Fin q → ℝ}
  {nf nd : ℕ → ℕ}
/-- Every consistent execution reaches a first actual outer target within the natural budget. -/
theorem exists_first_target (hsound : InnerSound r X call)
    (hprefix : ∀ N, (∀ k < N, ¬TargetAt r X ε₀ ε x δ k) →
      Run r X call ε₀ β ε x δ nf nd N) :
    ∃ K, TargetAt r X ε₀ ε x δ K ∧ Run r X call ε₀ β ε x δ nf nd K ∧
      (∀ k < K, ¬TargetAt r X ε₀ ε x δ k) ∧
        K ≤ GeometricDecay.budget ‖r (x 0)‖ ε₀ β := by
  classical
  have hex : ∃ K, TargetAt r X ε₀ ε x δ K := by
    by_contra hn
    push Not at hn
    let B := GeometricDecay.budget ‖r (x 0)‖ ε₀ β
    have h := hprefix (B + 1) (fun k _ => hn k)
    have hb := h.iterations_le_budget hsound
    change B + 1 ≤ B at hb
    omega
  let K := Nat.find hex
  have hfirst : ∀ k < K, ¬TargetAt r X ε₀ ε x δ k := fun k hk => Nat.find_min hex hk
  have hrun := hprefix K hfirst
  exact ⟨K, Nat.find_spec hex, hrun, hfirst, hrun.iterations_le_budget hsound⟩
end LeastNorm
