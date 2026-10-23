import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Optimization.Quadratic.Optimality.Regularization
import Mathlib.Tactic
open scoped Matrix BigOperators ComplexOrder

/-!
# Actual optimality of regularized matrix quadratics

True global minimality yields the actual shifted linear equation and matrix
semidefiniteness, with the multiplier determined by the minimizer radius.
-/

namespace Matrix
/-- A true regularized matrix minimizer solves its shifted system with semidefinite shifted
matrix. -/
theorem regularized_minimizer_solve {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℝ} (hT : T.IsSymm) (b y : EuclideanSpace ℝ n) {r : ℝ} (hr : 2 < r) (σ
      : ℝ)
    (hmin : ∀ z, QuadraticOptimality.regularized (toEuclideanLin T).toContinuousLinearMap b σ
      r y ≤
      QuadraticOptimality.regularized (toEuclideanLin T).toContinuousLinearMap b σ r z) :
    let τ := σ * ‖y‖ ^ (r - 2)
    toEuclideanLin (T + τ • 1) y = -b ∧ (T + τ • 1).PosSemidef := by
  dsimp only
  obtain ⟨hstat, hPSD⟩ := QuadraticOptimality.necessary_regularized
    hT.isSymmetric_toEuclideanLin b y hr σ hmin
  let τ := σ * ‖y‖ ^ (r - 2)
  have hsolve : toEuclideanLin (T + τ • 1) y = -b := by
    simp only [map_add, map_smul, toEuclideanLin_one, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    change b + toEuclideanLin T y = -τ • y at hstat
    apply eq_neg_of_add_eq_zero_left
    calc _ = (b + toEuclideanLin T y) + τ • y := by abel
      _ = 0 := by rw [hstat]; simp
  refine ⟨hsolve, ?_⟩
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_iff_isSymm.mpr hT).add
      (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  · intro v
    have hh := hPSD (WithLp.toLp 2 v)
    rw [star_trivial, ←EuclideanSpace.inner_toLp_toLp_real, real_inner_comm]
    change 0 ≤ inner ℝ (toEuclideanLin T (WithLp.toLp 2 v) + τ • WithLp.toLp 2 v)
      (WithLp.toLp 2 v) at hh
    simpa only [←toEuclideanLin_toLp, map_add, map_smul, toEuclideanLin_one,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] using hh

end Matrix
