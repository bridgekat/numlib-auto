import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Norm bounds from a nonnegative spectral enclosure

Diagonalization bounds the norm of a self-adjoint operator between its nonnegative
spectral endpoints. The lower endpoint may be negative: that case is automatic.
-/

open scoped InnerProductSpace
namespace LinearMap.IsSymmetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →ₗ[ℝ] E}

/-- Squared norms are the sums of the squared real eigenbasis coordinates. -/
theorem norm_sq_eq_sum_eigenvector_coordinates (hT : T.IsSymmetric) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ((hT.eigenvectorBasis rfl).repr x i) ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).repr.norm_map x, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- A shifted self-adjoint operator with nonnegative shifted spectrum has the corresponding
norm bounds. No invertibility is required, so zero shifted eigenvalues are allowed. -/
theorem norm_shift_bounds_of_eigenvalue_bounds (hT : T.IsSymmetric) {a b t : ℝ}
    (hpos : ∀ i, 0 ≤ t + hT.eigenvalues rfl i)
    (hlo : ∀ i, a ≤ hT.eigenvalues rfl i) (hup : ∀ i, hT.eigenvalues rfl i ≤ b)
    (x : E) : (t + a) * ‖x‖ ≤ ‖T x + t • x‖ ∧
      ‖T x + t • x‖ ≤ (t + b) * ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  have : Nontrivial E := nontrivial_of_ne x 0 hx
  have hb : 0 ≤ t + b := by
    let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
    linarith [hpos i, hup i]
  have hn := hT.norm_sq_eq_sum_eigenvector_coordinates x
  have htn : ‖T x + t • x‖ ^ 2 = ∑ i,
      (t + hT.eigenvalues rfl i) ^ 2 * ((hT.eigenvectorBasis rfl).repr x i) ^ 2 := by
    rw [hT.norm_sq_eq_sum_eigenvector_coordinates]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply,
      hT.eigenvectorBasis_apply_self_apply, smul_eq_mul, RCLike.ofReal_real_eq_id, id_eq]
    ring
  have hu : ‖T x + t • x‖ ^ 2 ≤ ((t + b) * ‖x‖) ^ 2 := by
    rw [htn, mul_pow, hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hpos i) (by linarith [hup i]) 2) (sq_nonneg _)
  constructor
  · by_cases ha : 0 ≤ t + a
    · have hl : ((t + a) * ‖x‖) ^ 2 ≤ ‖T x + t • x‖ ^ 2 := by
        rw [htn, mul_pow, hn, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ ha (by linarith [hlo i]) 2) (sq_nonneg _)
      nlinarith [norm_nonneg (T x + t • x), mul_nonneg ha (norm_nonneg x)]
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) (norm_nonneg x)).trans
        (norm_nonneg _)
  · nlinarith [norm_nonneg (T x + t • x), mul_nonneg hb (norm_nonneg x)]

end LinearMap.IsSymmetric
