import Numlib.Krylov.Lanczos.Grade
import Mathlib.Tactic
/-!
# Trust-region comparison in actual nested Lanczos spaces

Stationarity, feasibility and complementary slackness imply ordered
trust-region multipliers and radii. The ambient comparison uses a genuine
grade projection, including singular positive-semidefinite shifted systems.
-/

open scoped Matrix ComplexOrder
namespace Lanczos
open Krylov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Nonnegative complementary trust-region shifts and actual nested solves give ordered
multipliers and ordered norms. All assumptions are the primitive solve and KKT conditions. -/
theorem trust_region_compare_of_shifted_solve (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.IsSymmetric) {m l : ℕ} (hml : m ≤ l) (hl : l + 1 ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (z : EuclideanSpace ℝ (Fin (l + 1)))
    {τ μ Δ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) (hy : ‖y‖ ≤ Δ) (hz : ‖z‖ ≤ Δ)
    (hcompy : τ * (‖y‖ ^ 2 - Δ ^ 2) = 0)
    (hcompz : μ * (‖z‖ ^ 2 - Δ ^ 2) = 0)
    (hPD : (tridiag A g (l + 1) + μ • 1).PosDef)
    (hsolvey : Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (hsolvez : Matrix.toEuclideanLin (tridiag A g (l + 1) + μ • 1) z =
      -(‖g‖ • PiLp.single 2 (0 : Fin (l + 1)) (1 : ℝ))) :
    τ ≤ μ ∧ ‖y‖ ≤ ‖z‖ := by
  have hle := multiplier_le_of_nested_shifted_solve A hg hA hml hl y z hμ hz
    hcompy hPD hsolvey hsolvez
  refine ⟨hle, ?_⟩
  rcases eq_or_lt_of_le hμ with hzero | hpos
  · have hτ0 : τ = 0 := by linarith
    have hμ0 : μ = 0 := hzero.symm
    subst τ
    subst μ
    exact norm_le_norm_of_nested_shifted_solve A hg hA hml hl y z 0 hPD hsolvey hsolvez
  · have hs : ‖z‖ ^ 2 - Δ ^ 2 = 0 := (mul_eq_zero.mp hcompz).resolve_left hpos.ne'
    have hd : 0 ≤ Δ := (norm_nonneg z).trans hz
    have he : ‖z‖ = Δ := by nlinarith [norm_nonneg z]
    simpa only [he] using hy

/-- Primitive trust-region KKT conditions compare an actual projected solve with a genuine
ambient stationary solution. No invertibility of the ambient shifted system is needed. -/
theorem trust_region_compare_ambient (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (x : E) {τ μ Δ : ℝ}
    (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) (hy : ‖y‖ ≤ Δ) (hx : ‖x‖ ≤ Δ)
    (hcompy : τ * (‖y‖ ^ 2 - Δ ^ 2) = 0)
    (hcompx : μ * (‖x‖ ^ 2 - Δ ^ 2) = 0)
    (hsolvey : Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (hsolvex : (A + μ • (LinearMap.id : E →ₗ[ℝ] E)) x = -g)
    (hPSD : ∀ v, 0 ≤ inner ℝ ((A + μ • (LinearMap.id : E →ₗ[ℝ] E)) v) v) :
    τ ≤ μ ∧ ‖y‖ ≤ ‖x‖ := by
  have hG : 0 < grade A g := grade_pos_of_ne_zero A g hg
  let l := grade A g - 1
  have hl : l + 1 = grade A g := by omega
  have hml : m ≤ l := by omega
  obtain ⟨z, hz, hsolvez, hPD⟩ := exists_grade_shifted_solve_le_norm A hg hA hl μ x
    hsolvex hPSD
  have hle := multiplier_le_of_nested_shifted_solve A hg hA hml hl.le y z hμ
    (hz.trans hx) hcompy hPD hsolvey hsolvez
  refine ⟨hle, ?_⟩
  rcases eq_or_lt_of_le hμ with hzero | hpos
  · have hτ0 : τ = 0 := by linarith
    have hμ0 : μ = 0 := hzero.symm
    subst τ
    subst μ
    exact (norm_le_norm_of_nested_shifted_solve A hg hA hml hl.le y z 0 hPD
      hsolvey hsolvez).trans hz
  · have hs : ‖x‖ ^ 2 - Δ ^ 2 = 0 := (mul_eq_zero.mp hcompx).resolve_left hpos.ne'
    have hd : 0 ≤ Δ := (norm_nonneg x).trans hx
    have he : ‖x‖ = Δ := by nlinarith [norm_nonneg x]
    simpa only [he] using hy
end Lanczos
