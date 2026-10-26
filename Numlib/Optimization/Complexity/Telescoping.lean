import Numlib.Optimization.Complexity.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Telescoping sums over successful iterations

The total decrease of the objective over the successful iterations of a method is at most
`f(x_0) - f_low` ([cartis2022evaluation], (2.2.12)–(2.2.13) and every "bound on the number of
successful iterations" lemma). The statements are for real sequences `φ k = f (x k)` whose value is
unchanged at unsuccessful iterations (the iterate is not updated).

* `Optimization.sum_successSet_sub_eq`: `∑_{j ∈ 𝒮_k} (φ_j - φ_{j+1}) = φ_0 - φ_{k+1}`.
* `Optimization.card_successSet_mul_le_of_decrease`: if every successful iteration decreases `φ`
  by at least `c`, then `c |𝒮_k| ≤ φ_0 - φ_low` (division form
  `Optimization.card_successSet_le_div_of_decrease`).
* `Optimization.card_mul_le_of_decrease`: the same for any subset `T` of iterations of a
  nonincreasing sequence (e.g. "good" successful iterations).
-/

open Finset

namespace Optimization

variable {φ : ℕ → ℝ} {succ : ℕ → Prop} {k : ℕ} {c φlow : ℝ}

/-- If `φ` is unchanged at unsuccessful iterations `j ≤ k`, the decreases over the successful
iterations `𝒮_k` telescope: `∑_{j ∈ 𝒮_k} (φ_j - φ_{j+1}) = φ_0 - φ_{k+1}`. -/
theorem sum_successSet_sub_eq (h : ∀ j ≤ k, ¬ succ j → φ (j + 1) = φ j) :
    ∑ j ∈ successSet succ k, (φ j - φ (j + 1)) = φ 0 - φ (k + 1) := by
  classical
  rw [successSet_eq_filter, sum_filter_of_ne, sum_range_sub']
  intro j hj hne
  by_contra hs
  exact hne (by rw [h j (Nat.lt_succ_iff.1 (mem_range.1 hj)) hs, sub_self])

/-- If `φ` is unchanged at unsuccessful iterations `j ≤ k`, decreases by at least `c` at the
successful ones, and `φlow ≤ φ_{k+1}`, then `c |𝒮_k| ≤ φ_0 - φlow`. -/
theorem card_successSet_mul_le_of_decrease (h : ∀ j ≤ k, ¬ succ j → φ (j + 1) = φ j)
    (hdec : ∀ j ≤ k, succ j → c ≤ φ j - φ (j + 1)) (hlow : φlow ≤ φ (k + 1)) :
    c * (successSet succ k).card ≤ φ 0 - φlow := by
  have hsum : ∑ _j ∈ successSet succ k, c ≤ ∑ j ∈ successSet succ k, (φ j - φ (j + 1)) :=
    sum_le_sum fun j hj => by
      rw [mem_successSet] at hj
      exact hdec j hj.1 hj.2
  rw [sum_successSet_sub_eq h, sum_const, nsmul_eq_mul] at hsum
  linarith

/-- Division form of `Optimization.card_successSet_mul_le_of_decrease`:
`|𝒮_k| ≤ (φ_0 - φlow) / c` for `c > 0`. -/
theorem card_successSet_le_div_of_decrease (hc : 0 < c)
    (h : ∀ j ≤ k, ¬ succ j → φ (j + 1) = φ j)
    (hdec : ∀ j ≤ k, succ j → c ≤ φ j - φ (j + 1)) (hlow : φlow ≤ φ (k + 1)) :
    ((successSet succ k).card : ℝ) ≤ (φ 0 - φlow) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact card_successSet_mul_le_of_decrease h hdec hlow

/-- If `φ` is nonincreasing on `[0, k + 1]`, decreases by at least `c` at every iteration of a
set `T ⊆ [0, k]`, and `φlow ≤ φ_{k+1}`, then `c |T| ≤ φ_0 - φlow`. -/
theorem card_mul_le_of_decrease {T : Finset ℕ} (hT : T ⊆ range (k + 1))
    (hmono : ∀ j ≤ k, φ (j + 1) ≤ φ j) (hdec : ∀ j ∈ T, c ≤ φ j - φ (j + 1))
    (hlow : φlow ≤ φ (k + 1)) :
    c * T.card ≤ φ 0 - φlow := by
  have h1 : ∑ _j ∈ T, c ≤ ∑ j ∈ T, (φ j - φ (j + 1)) := sum_le_sum hdec
  have h2 : ∑ j ∈ T, (φ j - φ (j + 1)) ≤ ∑ j ∈ range (k + 1), (φ j - φ (j + 1)) :=
    sum_le_sum_of_subset_of_nonneg hT fun j hj _ =>
      sub_nonneg.2 (hmono j (Nat.lt_succ_iff.1 (mem_range.1 hj)))
  rw [sum_range_sub', sum_const, nsmul_eq_mul] at *
  linarith

/-- The form of `Optimization.card_mul_le_of_decrease` over `[0, N)`: if `φ` is nonincreasing
on `[0, N]` and decreases by at least `c` at every iteration of `T ⊆ [0, N)`, then
`|T| c ≤ φ_0 - φ_N`. -/
theorem card_mul_le_sub_of_decrease {T : Finset ℕ} {N : ℕ} (hT : T ⊆ range N)
    (hmono : ∀ j < N, φ (j + 1) ≤ φ j) (hdec : ∀ j ∈ T, c ≤ φ j - φ (j + 1)) :
    (T.card : ℝ) * c ≤ φ 0 - φ N := by
  have h1 : ∑ _j ∈ T, c ≤ ∑ j ∈ T, (φ j - φ (j + 1)) := sum_le_sum hdec
  have h2 : ∑ j ∈ T, (φ j - φ (j + 1)) ≤ ∑ j ∈ range N, (φ j - φ (j + 1)) :=
    sum_le_sum_of_subset_of_nonneg hT fun j hj _ => sub_nonneg.2 (hmono j (mem_range.1 hj))
  rw [sum_range_sub', sum_const, nsmul_eq_mul] at *
  linarith

/-- Division form of `Optimization.card_mul_le_of_decrease`: `|T| ≤ (φ_0 - φlow) / c` for
`c > 0`. -/
theorem card_le_div_of_decrease {T : Finset ℕ} (hc : 0 < c) (hT : T ⊆ range (k + 1))
    (hmono : ∀ j ≤ k, φ (j + 1) ≤ φ j) (hdec : ∀ j ∈ T, c ≤ φ j - φ (j + 1))
    (hlow : φlow ≤ φ (k + 1)) :
    (T.card : ℝ) ≤ (φ 0 - φlow) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact card_mul_le_of_decrease hT hmono hdec hlow

end Optimization
