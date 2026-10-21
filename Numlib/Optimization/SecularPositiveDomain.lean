import Numlib.Optimization.WeightedSecularResolvent
import Numlib.Analysis.InnerProductSpace.Coercive

/-!
# Positivity and order on the spectral resolvent domain

The signs of genuine shifted eigenvalues determine positivity of the shifted quadratic form.
-/

noncomputable section
open scoped InnerProductSpace
namespace Optimization.SecularResolvent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E}

/-- Nonnegative shifted eigenvalues give a positive semidefinite shifted operator. -/
theorem isPositive_shift (hH : H.IsSymmetric) {t : ℝ}
    (ht : ∀ i, 0 ≤ t + hH.eigenvalues rfl i) :
    (H + t • (1 : E →ₗ[ℝ] E)).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hH x y]
  · intro x
    rw [← (hH.eigenvectorBasis rfl).repr.inner_map_map]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [RCLike.re_to_real, star_trivial, dotProduct]
    change (0 : ℝ) ≤ ∑ i, _
    apply Finset.sum_nonneg
    intro i _
    rw [repr_shift_apply]
    nlinarith [mul_nonneg (ht i)
      (sq_nonneg ((hH.eigenvectorBasis rfl).repr x i))]

/-- Strictly positive shifted eigenvalues give an invertible positive shifted operator. -/
theorem isPositive_isUnit_shift (hH : H.IsSymmetric) {t : ℝ}
    (ht : Admissible hH t) :
    (H + t • (1 : E →ₗ[ℝ] E)).IsPositive ∧
      IsUnit (H + t • (1 : E →ₗ[ℝ] E)) :=
  ⟨isPositive_shift hH (fun i => (ht i).le), isUnit_shift hH t (fun i => (ht i).ne')⟩

/-- Strict decrease between any two shifts with positive spectral denominators. -/
theorem spectralNormSq_lt_of_lt {ι : Type*} [Fintype ι] (e γ : ι → ℝ)
    {x y : ℝ} (hx : ∀ i, 0 < x + e i) (hxy : x < y)
    (hγ : ∃ i, γ i ≠ 0) : spectralNormSq e γ y < spectralNormSq e γ x := by
  unfold spectralNormSq
  apply Finset.sum_lt_sum
  · intro i _
    have hy : 0 < y + e i := by linarith [hx i]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos (hx i))
      (sq_le_sq₀ (hx i).le hy.le |>.2 (by linarith))
  · obtain ⟨i, hi⟩ := hγ
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have hy : 0 < y + e i := by linarith [hx i]
    exact div_lt_div_of_pos_left (sq_pos_of_ne_zero hi) (sq_pos_of_pos (hx i))
      (sq_lt_sq₀ (hx i).le hy.le |>.2 (by linarith))

end Optimization.SecularResolvent
