import Mathlib.Algebra.Module.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Equally spaced finite chains

Points advance by a fixed vector up to a finite endpoint, then remain fixed. The construction
uses only an additive real module; optimizer-specific acceptance rules are separate.
-/
namespace Optimization.FiniteChain
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The equally spaced chain, continued constantly after its endpoint. -/
def point (N : ℕ) (v : E) (k : ℕ) : E := ((min k N : ℕ) : ℝ) • v

/-- The chain increment, zero after the endpoint. -/
def step (N : ℕ) (v : E) (k : ℕ) : E := if k < N then v else 0

/-- Before the endpoint the point has its unclamped affine expression. -/
@[simp] theorem point_of_le {N k : ℕ} (v : E) (hk : k ≤ N) :
    point N v k = (k : ℝ) • v := by simp [point, Nat.min_eq_left hk]

/-- At and after the endpoint the point is constant. -/
@[simp] theorem point_of_ge {N k : ℕ} (v : E) (hk : N ≤ k) :
    point N v k = (N : ℝ) • v := by simp [point, Nat.min_eq_right hk]

/-- Consecutive points differ by the declared increment. -/
theorem point_add_step (N : ℕ) (v : E) (k : ℕ) :
    point N v (k + 1) = point N v k + step N v k := by
  by_cases hk : k < N
  · simp [point_of_le v (Nat.le_of_lt hk), step, hk, Nat.cast_add, add_smul]
  · have hNk : N ≤ k := Nat.le_of_not_gt hk
    simp [point_of_ge v hNk, point_of_ge v (hNk.trans (Nat.le_succ k)), step, hk]

end Optimization.FiniteChain
