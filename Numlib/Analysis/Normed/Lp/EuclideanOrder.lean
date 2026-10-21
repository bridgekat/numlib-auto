import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean order comparison

On nonnegative finite real coordinate vectors, the Euclidean norm detects equality
in a coordinatewise comparison.
-/

namespace EuclideanSpace
variable {ι : Type*} [Fintype ι]

/-- Ordered nonnegative real vectors with equal Euclidean norms have equal coordinates. -/
theorem eq_of_nonneg_of_le_of_norm_eq {x y : EuclideanSpace ℝ ι}
    (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) (hnorm : ‖x‖ = ‖y‖) : x = y := by
  have hsum : ∑ i, x i ^ 2 = ∑ i, y i ^ 2 := by
    rw [← real_norm_sq_eq, ← real_norm_sq_eq, hnorm]
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ Finset.univ) => sq_le_sq₀ (hx i) ((hx i).trans (hxy i)) |>.2 (hxy i))).mp hsum
  apply PiLp.ext
  intro i
  exact (sq_eq_sq₀ (hx i) ((hx i).trans (hxy i))).mp (heq i (Finset.mem_univ i))

end EuclideanSpace
