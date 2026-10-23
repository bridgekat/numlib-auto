import Numlib.Analysis.Calculus.TaylorModel
import Mathlib.Tactic

/-!
# Operator-norm growth of finite tensor Taylor polynomials

The factorial-normalized coefficient norm sum bounds the actual finite tensor
polynomial outside the unit ball, in arbitrary real normed spaces.
-/

namespace TaylorModel
open scoped BigOperators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The finite sum of factorial-normalized tensor operator norms. -/
noncomputable def jetNormSum (A : FormalMultilinearSeries ℝ E F) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1), ‖A i‖ / i.factorial

/-- The finite coefficient norm sum is nonnegative. -/
theorem jetNormSum_nonneg (A : FormalMultilinearSeries ℝ E F) (p : ℕ) :
    0 ≤ jetNormSum A p := Finset.sum_nonneg (fun _ _ => by positivity)

/-- Beyond the unit ball, the actual tensor polynomial has at most degree-p growth. -/
theorem norm_ofJet_le_mul_pow (A : FormalMultilinearSeries ℝ E F) (p : ℕ)
    (s : E) (hs : 1 ≤ ‖s‖) : ‖ofJet A p s‖ ≤ jetNormSum A p * ‖s‖ ^ p := by
  rw [ofJet_eq_sum]
  calc _ ≤ ∑ i ∈ Finset.range (p + 1),
        ‖((i.factorial : ℝ)⁻¹) • A i (fun _ => s)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p + 1), (‖A i‖ / i.factorial) * ‖s‖ ^ p := by
      apply Finset.sum_le_sum
      intro i hi
      have hip : i ≤ p := by have := Finset.mem_range.mp hi; omega
      have hop := (A i).le_opNorm (fun _ => s)
      simp only [Fin.prod_const] at hop
      have hp := pow_le_pow_right₀ hs hip
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (i.factorial : ℝ)⁻¹)]
      have hh := mul_le_mul_of_nonneg_left
        (hop.trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _)))
        (show 0 ≤ (i.factorial : ℝ)⁻¹ by positivity)
      convert hh using 1; ring
    _ = _ := (Finset.sum_mul _ _ _).symm

end TaylorModel
