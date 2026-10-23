import Numlib.Optimization.LeastNorm.Run
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Actual least-norm inner-call evaluation budgets

The least-squares per-call complexity and derived residual contraction give
a uniform finite geometric bound, preserving all primal and dual accuracy
exponents. The finite maximum is over actual requested orders.
-/

namespace LeastNorm
/-- A finite maximum over the requested positive orders. -/
noncomputable def maximumWeight {q : ℕ} (hq : 0 < q) (w : Fin q → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hq⟩, Finset.mem_univ _⟩ w

theorem le_maximumWeight {q : ℕ} (hq : 0 < q) (w : Fin q → ℝ) (a : Fin q) :
    w a ≤ maximumWeight hq w := Finset.le_sup' _ (Finset.mem_univ _)

theorem maximumWeight_le {q : ℕ} (hq : 0 < q) (w : Fin q → ℝ) {C : ℝ}
    (h : ∀ a, w a ≤ C) : maximumWeight hq w ≤ C :=
  (Finset.sup'_le_iff _ _).mpr (fun a _ => h a)

theorem maximumWeight_nonneg {q : ℕ} (hq : 0 < q) {w : Fin q → ℝ}
    (h : ∀ a, 0 ≤ w a) : 0 ≤ maximumWeight hq w :=
  (h ⟨0, hq⟩).trans (le_maximumWeight hq w ⟨0, hq⟩)

/-- The genuine least-squares cost at a nonterminal residual is bounded by a
linear residual envelope and a fixed primal-accuracy weight. -/
theorem residual_cost_le {R ε₀ β ε π : ℝ} (hε₀ : 0 < ε₀) (hR : ε₀ ≤ R)
    (hβ : 0 < β) (hε : 0 < ε) (hπ : 1 < π) :
    R ^ 2 * (β * R * ε) ^ (-π) ≤ R * (β ^ (-π) * ε₀ ^ (1 - π) * ε ^ (-π)) := by
  have hRp : 0 < R := hε₀.trans_le hR
  have hh := Real.rpow_le_rpow_of_nonpos hε₀ hR (by linarith : 1 - π ≤ 0)
  have hid : R ^ 2 * (β * R * ε) ^ (-π) =
      R * (β ^ (-π) * R ^ (1 - π) * ε ^ (-π)) := by
    rw [Real.mul_rpow (mul_pos hβ hRp).le hε.le,
      Real.mul_rpow hβ.le hRp.le,
      show 1 - π = 1 + -π by ring, Real.rpow_add hRp, Real.rpow_one]
    ring
  rw [hid]
  gcongr

/-- The finite maximum is attained by an actual requested order. -/
theorem exists_maximumWeight {q : ℕ} (hq : 0 < q) (w : Fin q → ℝ) :
    ∃ a, maximumWeight hq w = w a := by
  obtain ⟨a, _, he⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ) (show Finset.univ.Nonempty from ⟨⟨0, hq⟩, Finset.mem_univ _⟩) w
  exact ⟨a, he⟩

/-- Positive geometric sums have a uniform bound independent of their finite length. -/
theorem geometric_sum_le {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, β ^ k ≤ 1 / (1 - β) := by
  have hh : (∑ k ∈ Finset.range N, β ^ k) * (1 - β) = 1 - β ^ N := by
    have he := geom_sum_mul β N
    nlinarith
  apply (le_div_iff₀ (sub_pos.mpr hβ1)).mpr
  rw [hh]
  exact sub_le_self _ (pow_nonneg hβ N)

/-- The actual per-call function and derivative evaluation bounds, measured
from the genuine least-squares starting merit and requested inner tolerances. -/
def InnerCounts {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {q : ℕ} (r : E → F)
    (call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop)
    (hq : 0 < q) (π : Fin q → ℝ) (κF κD : ℝ) : Prop :=
  ∀ xs tol y δ nf nd, call xs tol y δ nf nd →
    (nf : ℝ) ≤ κF * merit r xs * maximumWeight hq (fun a => (tol a) ^ (-π a)) ∧
    (nd : ℝ) ≤ κD * merit r xs * maximumWeight hq (fun a => (tol a) ^ (-π a))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]
namespace Run
variable {q : ℕ} {r : E → F} {X : Set E}
  {call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop}
  {ε₀ β : ℝ} {ε : Fin q → ℝ} {x : ℕ → E} {δ : ℕ → Fin q → ℝ}
  {nf nd : ℕ → ℕ} {N : ℕ}

/-- Actual per-call least-squares evaluation bounds sum to a uniform geometric
bound. It retains the primal and dual accuracy exponents for every order. -/
theorem evaluations_le (h : Run r X call ε₀ β ε x δ nf nd N)
    (hsound : InnerSound r X call) (hq : 0 < q) (π : Fin q → ℝ)
    (hπ : ∀ a, 1 < π a) {κ : ℝ} (hκ : 0 ≤ κ) (count : ℕ → ℕ)
    (hcount : ∀ k < N, (count k : ℝ) ≤ κ * merit r (x k) *
      maximumWeight hq (fun a => (β * ‖r (x k)‖ * ε a) ^ (-π a))) :
    (∑ k ∈ Finset.range N, (count k : ℝ)) ≤
      κ / 2 * ‖r (x 0)‖ / (1 - β) *
        maximumWeight hq (fun a => β ^ (-π a) * ε₀ ^ (1 - π a) * ε a ^ (-π a)) := by
  let W := maximumWeight hq
    (fun a => β ^ (-π a) * ε₀ ^ (1 - π a) * ε a ^ (-π a))
  have hW : 0 ≤ W := maximumWeight_nonneg hq (fun a => mul_nonneg
    (mul_nonneg (Real.rpow_nonneg h.contraction_pos.le _)
      (Real.rpow_nonneg h.primal_pos.le _)) (Real.rpow_nonneg (h.accuracy a).1.le _))
  have heach (k : ℕ) (hk : k < N) :
      (count k : ℝ) ≤ κ / 2 * ‖r (x 0)‖ * β ^ k * W := by
    obtain ⟨a, ha⟩ := exists_maximumWeight hq
      (fun a => (β * ‖r (x k)‖ * ε a) ^ (-π a))
    have hh := residual_cost_le h.primal_pos (h.residual_gt hk).le
      h.contraction_pos (h.accuracy a).1 (hπ a)
    have hma := le_maximumWeight hq
      (fun a => β ^ (-π a) * ε₀ ^ (1 - π a) * ε a ^ (-π a)) a
    calc
      _ ≤ κ * merit r (x k) *
          maximumWeight hq (fun a => (β * ‖r (x k)‖ * ε a) ^ (-π a)) := hcount k hk
      _ = κ / 2 * (‖r (x k)‖ ^ 2 * (β * ‖r (x k)‖ * ε a) ^ (-π a)) := by
        rw [ha]; unfold merit; ring
      _ ≤ κ / 2 * (‖r (x k)‖ *
          (β ^ (-π a) * ε₀ ^ (1 - π a) * ε a ^ (-π a))) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ κ / 2 * (‖r (x k)‖ * W) := by gcongr
      _ ≤ κ / 2 * ((‖r (x 0)‖ * β ^ k) * W) := by
        gcongr
        exact h.residual_le_geometric hsound hk
      _ = _ := by ring
  calc
    _ ≤ ∑ k ∈ Finset.range N, κ / 2 * ‖r (x 0)‖ * β ^ k * W :=
      Finset.sum_le_sum (fun k hk => heach k (Finset.mem_range.mp hk))
    _ = κ / 2 * ‖r (x 0)‖ * W * ∑ k ∈ Finset.range N, β ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ κ / 2 * ‖r (x 0)‖ * W * (1 / (1 - β)) :=
      mul_le_mul_of_nonneg_left (geometric_sum_le h.contraction_pos.le h.contraction_lt_one N)
        (by positivity)
    _ = _ := by ring
end Run
end LeastNorm
