import Numlib.Optimization.Quadratic.Krylov.RegularizationMonotonicity

/-!
# Lower bounds on actual Lanczos solve radii

An ambient Rayleigh upper bound controls the actual shifted projected operator.
Its positive definiteness and genuine right side give the source radius floor.
-/

open scoped Matrix ComplexOrder
namespace Lanczos
open Krylov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- A genuine shifted projected solve has right-side norm at most its ambient
Rayleigh upper bound times its radius. -/
theorem norm_rhs_le_of_quadratic_upper (A : E →ₗ[ℝ] E) {g : E} (hA : A.IsSymmetric)
    {m : ℕ} (hm : m + 1 ≤ grade A g) (y : EuclideanSpace ℝ (Fin (m + 1)))
    {τ U : ℝ} (hU : ∀ v, inner ℝ (A v) v ≤ U * ‖v‖ ^ 2)
    (hPD : (tridiag A g (m + 1) + τ • 1).PosDef)
    (hsolve : Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) :
    0 < U + τ ∧ ‖g‖ ≤ (U + τ) * ‖y‖ := by
  let T := tridiag A g (m + 1) + τ • 1
  have hbound : ∀ z : EuclideanSpace ℝ (Fin (m + 1)),
      inner ℝ (Matrix.toEuclideanLin T z) z ≤ (U + τ) * ‖z‖ ^ 2 := by
    intro z
    rw [← inner_shifted_apply_basisEmbedding A g hA hm z z τ]
    change inner ℝ (A (basisEmbedding A g hm z) + τ • basisEmbedding A g hm z)
      (basisEmbedding A g hm z) ≤ _
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      (basisEmbedding A g hm).norm_map]
    have hh := hU (basisEmbedding A g hm z)
    rw [(basisEmbedding A g hm).norm_map] at hh
    nlinarith
  let e : EuclideanSpace ℝ (Fin (m + 1)) := PiLp.single 2 0 (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have he0 : e ≠ 0 := by intro h; rw [h, norm_zero] at he; norm_num at he
  have hpos := ((Matrix.posDef_iff_isSymmetricCoercive _).mp hPD).isCoercive.inner_self_pos he0
  have hhi : 0 < U + τ := by
    have hb := hbound e
    rw [he] at hb
    simp only [one_pow, mul_one] at hb
    simpa only [RCLike.re_to_real] using lt_of_lt_of_le hpos hb
  have hb : (Matrix.toEuclideanLin T).IsSymmetricBoundedBy (-(U + τ)) (U + τ) := {
    isSymmetric := ((Matrix.posDef_iff_isSymmetricCoercive _).mp hPD).isSymmetric
    le_re_inner := fun z => (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hhi.le)
      (sq_nonneg ‖z‖)).trans (by simpa only [RCLike.re_to_real] using
        ((Matrix.posDef_iff_isSymmetricCoercive _).mp hPD).isPositive.2 z)
    re_inner_le := fun z => by simpa only [RCLike.re_to_real] using hbound z }
  have hh := hb.norm_apply_le y
  rw [hsolve] at hh
  refine ⟨hhi, ?_⟩
  simpa only [norm_neg, norm_smul, PiLp.norm_single, norm_one, Real.norm_eq_abs,
    abs_norm, mul_one] using hh
end Lanczos
