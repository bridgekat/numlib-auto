import Numlib.Optimization.KrylovSubproblemReduction

/-!
# Positive definite shifted Lanczos subproblems

An unreduced Lanczos compression is cyclic from its first coordinate. Its nonzero
first-coordinate gradient excludes a singular positive semidefinite shifted operator
at a global regularized minimizer. The resulting residual bounds concern the actual
Lanczos step and its actual radial multiplier.
-/

noncomputable section
open scoped InnerProductSpace
open Set Optimization.QuadraticSubproblem
namespace Optimization.KrylovSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : E →ₗ[ℝ] E} {g : E}
  [FiniteDimensional ℝ (Krylov.fullSubspace A g)]

/-- Before or at the grade, every internal Lanczos subdiagonal is nonzero. -/
theorem lanczos_tridiag_isUnreduced {m : ℕ} (hm : m ≤ Krylov.grade A g) :
    (Lanczos.tridiag A g m).IsUnreducedUpperHessenberg := by
  rw [Matrix.isUnreducedUpperHessenberg_iff_fin]
  refine ⟨(Lanczos.tridiag_isTridiagonal A g m).isUpperHessenberg, ?_⟩
  intro k hk
  simp only [Lanczos.tridiag_apply, show ¬k + 1 = k by omega,
    show ¬k + 1 + 1 = k by omega, ite_false, ite_true]
  exact fun h => (not_le_of_gt (by omega : k + 1 < Krylov.grade A g))
    ((Lanczos.beta_eq_zero_iff (A := A) (b := g) k).mp h)

/-- A stationary reduced shifted system with a positive semidefinite shift has
strictly positive definite shift: the first-coordinate right-hand side is cyclic. -/
theorem lanczos_shift_posDef_of_stationary (hg : g ≠ 0)
    {m : ℕ} (hm : m + 1 ≤ Krylov.grade A g) (lambda : ℝ)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hstat : ‖g‖ • EuclideanSpace.single 0 1 +
      Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1)) y + lambda • y = 0)
    (hpos : ((Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1))).toContinuousLinearMap +
      lambda • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (m + 1)))).IsPositive) :
    (∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i +
      lambda * y i = -(if i = 0 then ‖g‖ else 0)) ∧
    (Lanczos.tridiag A g (m + 1) + lambda • 1).PosDef := by
  have hsystem : Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1) +
      lambda • 1) y = (-‖g‖) • EuclideanSpace.single 0 1 := by
    have he : Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1) +
        lambda • 1) y =
        Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1)) y +
          lambda • y := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        Matrix.toEuclideanLin_one_apply]
    rw [he, neg_smul]
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc, add_comm, add_left_comm] using hstat
  have hsys : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i +
      lambda * y i = -(if i = 0 then ‖g‖ else 0) := by
    intro i
    have he := congrArg (fun z : EuclideanSpace ℝ (Fin (m + 1)) => z i) hsystem
    by_cases hi : i = 0 <;>
      simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, PiLp.smul_apply, PiLp.single_apply, hi, ite_true, ite_false,
        mul_one, mul_zero, neg_zero] using he
  refine ⟨hsys, ?_⟩
  have hshape := (lanczos_tridiag_isUnreduced hm).add_smul_one lambda
  apply hshape.posDef_of_posSemidef_of_solve_first ?_
    (neg_ne_zero.mpr (norm_ne_zero_iff.mpr hg)) hsystem
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  convert hpos.toLinearMap using 1
  ext z
  simp only [map_add, map_smul, Matrix.toEuclideanLin_one,
    ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.coe_toContinuousLinearMap, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.id_apply]

/-- A regularized Lanczos global minimizer has its actual reduced stationary
system and a positive definite shifted matrix, so no hard case occurs internally. -/
theorem lanczos_regularized_shift_posDef (hg : g ≠ 0)
    {m : ℕ} (hm : m + 1 ≤ Krylov.grade A g) {sigma r : ℝ}
    (hsigma : 0 ≤ sigma) (hr : 2 < r) {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hmin : IsMinOn (powerRegularizedQuadratic (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1))).toContinuousLinearMap sigma r)
      univ y) :
    (∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i +
      (sigma * ‖y‖ ^ (r - 2)) * y i = -(if i = 0 then ‖g‖ else 0)) ∧
    (Lanczos.tridiag A g (m + 1) + (sigma * ‖y‖ ^ (r - 2)) • 1).PosDef := by
  have hsym : (Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1))).IsSymmetric :=
    (Lanczos.tridiag_isSymm A g (m + 1)).isSymmetric_toEuclideanLin
  obtain ⟨hstat, hpos⟩ := (isMin_powerRegularized_iff_shift hsym hsigma hr).mp hmin
  apply lanczos_shift_posDef_of_stationary hg hm _ _ hpos
  simpa only [LinearMap.coe_toContinuousLinearMap'] using hstat

end Optimization.KrylovSubproblem
