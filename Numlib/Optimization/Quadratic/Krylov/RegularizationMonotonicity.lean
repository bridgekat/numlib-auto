import Numlib.Optimization.Quadratic.Krylov.Regularization
import Numlib.Krylov.Lanczos.Grade

/-!
# Ordered radii for actual regularized Lanczos minimizers

Radial multipliers and genuine complementary shifted-system comparisons give
monotone subproblem norms and the full-space minimizer bound, including singular
ambient shifted systems.
-/

open scoped Matrix ComplexOrder
namespace QuadraticKrylov
open Krylov Lanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nested shifted solve with a radial multiplier has radius at most any feasible
later radial cap. -/
theorem norm_le_of_radial_nested_shifted_solve (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.IsSymmetric) {m l : ℕ} (hml : m ≤ l) (hl : l + 1 ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (z : EuclideanSpace ℝ (Fin (l + 1)))
    {σ r R : ℝ} (hσ : 0 < σ) (hr : 2 < r) (hR : 0 ≤ R) (hzR : ‖z‖ ≤ R)
    (hPD : (tridiag A g (l + 1) + (σ * R ^ (r - 2)) • 1).PosDef)
    (hy : Matrix.toEuclideanLin (tridiag A g (m + 1) + (σ * ‖y‖ ^ (r - 2)) • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (hz : Matrix.toEuclideanLin (tridiag A g (l + 1) + (σ * R ^ (r - 2)) • 1) z =
      -(‖g‖ • PiLp.single 2 (0 : Fin (l + 1)) (1 : ℝ))) : ‖y‖ ≤ R := by
  by_contra hn
  have hnorm : R < ‖y‖ := lt_of_not_ge hn
  have hpow := Real.rpow_lt_rpow hR hnorm (by linarith : 0 < r - 2)
  have hshift := Lanczos.multiplier_le_of_nested_shifted_solve A hg hA hml hl y z
    (mul_nonneg hσ.le (Real.rpow_nonneg hR _)) (hzR.trans hnorm.le)
    (by ring : (σ * ‖y‖ ^ (r - 2)) * (‖y‖ ^ 2 - ‖y‖ ^ 2) = 0) hPD hy hz
  nlinarith
end QuadraticKrylov

namespace QuadraticKrylov
open Krylov Lanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- Every actual regularized projected solve has norm at most a genuine full-space minimizer. -/
theorem norm_le_norm_of_regularized_ambient_min (A : E →L[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.toLinearMap.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A.toLinearMap g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (x : E) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hy : Matrix.toEuclideanLin (tridiag A.toLinearMap g (m + 1) +
      (σ * ‖y‖ ^ (r - 2)) • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (hx : ∀ z, QuadraticOptimality.regularized A g σ r x ≤
      QuadraticOptimality.regularized A g σ r z) : ‖y‖ ≤ ‖x‖ := by
  obtain ⟨hstat, hPSD⟩ := QuadraticOptimality.necessary_regularized hA g x hr σ hx
  have hsolve : (A.toLinearMap + (σ * ‖x‖ ^ (r - 2)) •
      (LinearMap.id : E →ₗ[ℝ] E)) x = -g := by
    change A x + (σ * ‖x‖ ^ (r - 2)) • x = -g
    rw [eq_neg_iff_add_eq_zero]
    calc _ = (g + A x) + (σ * ‖x‖ ^ (r - 2)) • x := by abel
      _ = 0 := by rw [hstat]; simp
  have hgrade : grade A.toLinearMap g - 1 + 1 = grade A.toLinearMap g := by omega
  obtain ⟨z, hz, hzsolve, hzPD⟩ := Lanczos.exists_grade_shifted_solve_le_norm
    A.toLinearMap hg hA hgrade (σ * ‖x‖ ^ (r - 2)) x hsolve hPSD
  exact norm_le_of_radial_nested_shifted_solve A.toLinearMap hg hA (by omega)
    hgrade.le y z hσ hr (norm_nonneg _) hz hzPD hy hzsolve
end QuadraticKrylov

namespace QuadraticKrylov
open Krylov Lanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- Actual nested global regularization minimizers have ordered radii. -/
theorem norm_le_norm_of_projected_regularized_min (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.IsSymmetric) {m l : ℕ} (hml : m ≤ l) (hl : l + 1 ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (z : EuclideanSpace ℝ (Fin (l + 1)))
    {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hy : ∀ w, QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (tridiag A g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) σ r y ≤
      QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (tridiag A g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) σ r w)
    (hz : ∀ w, QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (tridiag A g (l + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (l + 1)) (1 : ℝ)) σ r z ≤
      QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (tridiag A g (l + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (l + 1)) (1 : ℝ)) σ r w) : ‖y‖ ≤ ‖z‖ := by
  have hm : m + 1 ≤ grade A g := (Nat.add_le_add_right hml 1).trans hl
  obtain ⟨hysolve, _⟩ := projected_optimality A hg hm y hr hy
  obtain ⟨hzsolve, hzPD⟩ := projected_optimality A hg hl z hr hz
  exact norm_le_of_radial_nested_shifted_solve A hg hA hml hl y z hσ hr
    (norm_nonneg _) le_rfl hzPD hysolve hzsolve
end QuadraticKrylov
