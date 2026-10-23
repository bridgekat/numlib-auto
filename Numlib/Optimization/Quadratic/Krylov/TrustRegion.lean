import Numlib.Optimization.Quadratic.Krylov.Regularization
import Numlib.Optimization.Quadratic.Optimality.TrustRegion
import Mathlib.Tactic
/-!
# Actual constrained Lanczos minimizers

Global trust-region minimality supplies the shifted semidefinite system.
The nonzero initial direction and unreduced tridiagonal structure make the
shifted projected matrix positive definite, including interior minimizers.
-/

open scoped Matrix ComplexOrder
namespace Matrix
/-- An actual trust-region minimizer admits a semidefinite shifted solve and the true
nonnegative complementary multiplier. -/
theorem trust_region_minimizer_solve {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℝ} (hT : T.IsSymm) (b y : EuclideanSpace ℝ n)
    {Δ : ℝ} (hΔ : 0 < Δ) (hy : ‖y‖ ≤ Δ)
    (hmin : ∀ z, ‖z‖ ≤ Δ → QuadraticOptimality.model
      (toEuclideanLin T).toContinuousLinearMap b y ≤
      QuadraticOptimality.model (toEuclideanLin T).toContinuousLinearMap b z) :
    ∃ τ : ℝ, 0 ≤ τ ∧ toEuclideanLin (T + τ • 1) y = -b ∧
      (T + τ • 1).PosSemidef ∧ τ * (‖y‖ ^ 2 - Δ ^ 2) = 0 := by
  obtain ⟨τ, hτ, hstat, hPSD, hcomp⟩ := QuadraticOptimality.necessary_trust_region
    hT.isSymmetric_toEuclideanLin b y hΔ hy hmin
  have hsolve : toEuclideanLin (T + τ • 1) y = -b := by
    simp only [map_add, map_smul, toEuclideanLin_one, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    change b + toEuclideanLin T y = -τ • y at hstat
    apply eq_neg_of_add_eq_zero_left
    calc _ = (b + toEuclideanLin T y) + τ • y := by abel
      _ = 0 := by rw [hstat]; simp
  refine ⟨τ, hτ, hsolve, ?_, hcomp⟩
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_iff_isSymm.mpr hT).add
      (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  · intro v
    have hh := hPSD (WithLp.toLp 2 v)
    rw [star_trivial, ← EuclideanSpace.inner_toLp_toLp_real, real_inner_comm]
    change 0 ≤ inner ℝ (toEuclideanLin T (WithLp.toLp 2 v) + τ • WithLp.toLp 2 v)
      (WithLp.toLp 2 v) at hh
    simpa only [← toEuclideanLin_toLp, map_add, map_smul, toEuclideanLin_one,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] using hh

/-- Any shifted solve at a true constrained minimizer has the multiplier and semidefiniteness
provided by global minimality; the nonzero right side makes the multiplier unique. -/
theorem trust_region_shift_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℝ} (hT : T.IsSymm) {b : EuclideanSpace ℝ n} (hb : b ≠ 0)
    (y : EuclideanSpace ℝ n) {Δ : ℝ} (hΔ : 0 < Δ) (hy : ‖y‖ ≤ Δ)
    (hmin : ∀ z, ‖z‖ ≤ Δ → QuadraticOptimality.model
      (toEuclideanLin T).toContinuousLinearMap b y ≤
      QuadraticOptimality.model (toEuclideanLin T).toContinuousLinearMap b z)
    {τ : ℝ} (hsolve : toEuclideanLin (T + τ • 1) y = -b) :
    0 ≤ τ ∧ (T + τ • 1).PosSemidef ∧ τ * (‖y‖ ^ 2 - Δ ^ 2) = 0 := by
  obtain ⟨t, ht, hs, hPSD, hcomp⟩ := trust_region_minimizer_solve hT b y hΔ hy hmin
  have hy0 : y ≠ 0 := by
    intro he
    simp only [he, map_zero, eq_comm, neg_eq_zero] at hsolve
    exact hb hsolve
  have he : τ • y = t • y := by
    simp only [map_add, map_smul, toEuclideanLin_one, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hsolve hs
    exact add_left_cancel (hsolve.trans hs.symm)
  have hτ : τ = t := smul_left_injective ℝ hy0 he
  subst τ
  exact ⟨ht, hPSD, hcomp⟩
end Matrix

namespace QuadraticKrylov
open Krylov Lanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
/-- A true projected trust-region minimizer has a positive-definite shifted Lanczos matrix,
including an interior solution with zero multiplier. -/
theorem projected_trust_region_optimality (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0)
    {m : ℕ} (hm : m + 1 ≤ grade A g) (y : EuclideanSpace ℝ (Fin (m + 1)))
    {Δ : ℝ} (hΔ : 0 < Δ) (hy : ‖y‖ ≤ Δ)
    (hmin : ∀ z, ‖z‖ ≤ Δ → QuadraticOptimality.model
      (Matrix.toEuclideanLin (tridiag A g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) y ≤
      QuadraticOptimality.model
      (Matrix.toEuclideanLin (tridiag A g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) z)
    {τ : ℝ} (hsolve : Matrix.toEuclideanLin (tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) :
    0 ≤ τ ∧ (tridiag A g (m + 1) + τ • 1).PosDef ∧
      τ * (‖y‖ ^ 2 - Δ ^ 2) = 0 := by
  have hb : (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ) :
      EuclideanSpace ℝ (Fin (m + 1))) ≠ 0 := by
    intro he
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v 0) he
    have h0' : ‖g‖ = 0 := by simpa [PiLp.single_apply] using h0
    exact (norm_ne_zero_iff.mpr hg) h0'
  obtain ⟨hτ, hPSD, hcomp⟩ := Matrix.trust_region_shift_posSemidef
    (tridiag_isSymm A g (m + 1)) hb y hΔ hy hmin hsolve
  refine ⟨hτ, ?_, hcomp⟩
  apply Matrix.posDef_of_tridiagonal_solve (shifted_tridiag A g (m + 1) τ)
    (shifted_tridiag_offdiag_ne A g hm τ) hPSD
    (neg_ne_zero.mpr (norm_ne_zero_iff.mpr hg)) y
  simpa only [neg_smul] using hsolve

/-- The true ambient residual of a constrained Lanczos minimizer has the sharp
spectral decay bound with its actual trust-region radius. -/
theorem trust_region_residual_bound (A : E →L[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.toLinearMap.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A.toLinearMap g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) {Δ : ℝ} (hΔ : 0 < Δ) (hy : ‖y‖ ≤ Δ)
    (hmin : ∀ z, ‖z‖ ≤ Δ → QuadraticOptimality.model
      (Matrix.toEuclideanLin (tridiag A.toLinearMap g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) y ≤
      QuadraticOptimality.model
      (Matrix.toEuclideanLin (tridiag A.toLinearMap g (m + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) z)
    {τ : ℝ} (hsolve : Matrix.toEuclideanLin
      (tridiag A.toLinearMap g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) :
    let hT := shifted_tridiag_isHermitian A.toLinearMap g (m + 1) τ
    let κ := hT.greatestEigenvalue / hT.leastEigenvalue
    ‖A (basisEmbedding A.toLinearMap g hm y) +
      τ • basisEmbedding A.toLinearMap g hm y + g‖ ≤
        2 * ‖A‖ * κ * Δ * ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m := by
  dsimp only
  obtain ⟨_, hPD, _⟩ := projected_trust_region_optimality A.toLinearMap hg hm y
    hΔ hy hmin hsolve
  have hr := norm_residual_le A hg hA hm y τ hsolve hPD.isUnit
    (hPD.isHermitian.leastEigenvalue_pos hPD) hPD.isHermitian.leastEigenvalue_le_greatest
    hPD.isHermitian.isSymmetricBoundedBy_extrema
  rw [(basisEmbedding A.toLinearMap g hm).norm_map] at hr
  have hk : 1 ≤ hPD.isHermitian.greatestEigenvalue / hPD.isHermitian.leastEigenvalue :=
    (one_le_div (hPD.isHermitian.leastEigenvalue_pos hPD)).mpr
      hPD.isHermitian.leastEigenvalue_le_greatest
  have hsqrt : 1 ≤ Real.sqrt (hPD.isHermitian.greatestEigenvalue /
      hPD.isHermitian.leastEigenvalue) := by
    rw [Real.le_sqrt (by norm_num) (zero_le_one.trans hk)]
    simpa using hk
  have hq : 0 ≤ (Real.sqrt (hPD.isHermitian.greatestEigenvalue /
      hPD.isHermitian.leastEigenvalue) - 1) /
      (Real.sqrt (hPD.isHermitian.greatestEigenvalue /
      hPD.isHermitian.leastEigenvalue) + 1) := by positivity
  apply hr.trans
  gcongr
end QuadraticKrylov
