import Numlib.Optimization.Quadratic.Optimality.CubicMinimum
import Numlib.Krylov.Convergence.LogarithmicBudget
import Numlib.Optimization.Quadratic.Krylov.RegularizationConvergence
import Numlib.Analysis.InnerProductSpace.Symmetric.SpectralExtrema

/-!
# A negative printed Lanczos iteration bound on an actual quadratic

The swap Hessian and first coordinate vector have Krylov grade at least two.
Actual cubic-regularized global minimizers exist in every generated subspace
and in the ambient space. Their actual maximum shifted condition number is
strictly above one. An allowed positive relative tolerance makes the printed
integer-ceiling bound minus one, excluding every generated iteration.
The metric is the identity and both regularization parameters are fixed: sigma
is one and the penalty power is three.
-/

namespace QuadraticKrylov.LogCountCounterexample
open scoped Matrix
/-- The Euclidean plane of the quadratic example. -/
abbrev E := EuclideanSpace ℝ (Fin 2)
/-- The bounded symmetric operator swapping the two coordinates. -/
noncomputable def A : E →L[ℝ] E :=
  (Matrix.toEuclideanLin (![![0,1],![1,0]] : Matrix (Fin 2) (Fin 2) ℝ)).toContinuousLinearMap
/-- The nonzero first-coordinate linear coefficient. -/
noncomputable def g : E := WithLp.toLp 2 ![1,0]
/-- The true action of the swap operator on every vector. -/
theorem A_apply (v : E) : A v = WithLp.toLp 2 ![v 1,v 0] := by
  change WithLp.toLp 2
    ((![![0,1],![1,0]] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ WithLp.ofLp v) = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The actual Hessian is symmetric for the Euclidean inner product. -/
theorem A_symmetric : A.toLinearMap.IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, A_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring
/-- The chosen gradient is nonzero. -/
theorem g_ne : g ≠ 0 := by
  intro h
  have hh := congrArg (fun v : E => v 0) h
  norm_num [g] at hh
/-- The chosen Hessian has strictly positive operator norm. -/
theorem A_ne : A ≠ 0 := by
  intro h
  have hh := congrArg (fun B : E →L[ℝ] E => B g 1) h
  norm_num [A_apply, g] at hh
/-- The first two actual Krylov vectors are independent. -/
theorem two_le_grade : 2 ≤ Krylov.grade A.toLinearMap g := by
  by_contra hn
  have hm := (Krylov.grade_le_iff A.toLinearMap g (m := 1)).mp (by omega)
  rw [pow_one, Krylov.subspace_one] at hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have h1 := congrArg (fun v : E => v 1) ha
  norm_num [A_apply, g] at h1

open Krylov Lanczos
/-- The genuine greatest eigenvalue of the swap operator. -/
noncomputable def U : ℝ := A_symmetric.greatestEigenvalue
  (by simp [E]) (by norm_num : 0 < 2)
/-- Actual global cubic minima in every generated Lanczos space admit a positive
relative tolerance for which the literal integer-ceiling count is negative. -/
theorem actual_family_negative_budget :
    ∃ (G : ℕ) (Y : (i : Fin (G + 1)) → EuclideanSpace ℝ (Fin (i.val + 1))) (x : E),
      G + 1 = grade A.toLinearMap g ∧
      (∀ z, QuadraticOptimality.regularized A g 1 3 x ≤
        QuadraticOptimality.regularized A g 1 3 z) ∧
      (∀ i w, QuadraticOptimality.regularized
        (Matrix.toEuclideanLin (tridiag A.toLinearMap g (i.val + 1))).toContinuousLinearMap
        (‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)) 1 3 (Y i) ≤
        QuadraticOptimality.regularized
        (Matrix.toEuclideanLin (tridiag A.toLinearMap g (i.val + 1))).toContinuousLinearMap
        (‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)) 1 3 w) ∧
      let shifts := fun i => (1 : ℝ) * ‖Y i‖ ^ ((3 : ℝ) - 2)
      let K := maxCondition A.toLinearMap g G shifts
      let t := (1 : ℝ) * ‖x‖ ^ ((3 : ℝ) - 2)
      ∃ θ > 0,
        (⌈Real.log (4 * ‖A‖ * K / θ * (t / 1) ^ (1 / ((3 : ℝ) - 2)) *
          ((U + t) / ‖g‖) ^ 2) /
          Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉ : ℤ) + 1 = -1 ∧
        ¬∃ i : Fin (G + 1), ((i.val + 1 : ℕ) : ℤ) ≤ min
          ((⌈Real.log (4 * ‖A‖ * K / θ * (t / 1) ^ (1 / ((3 : ℝ) - 2)) *
            ((U + t) / ‖g‖) ^ 2) /
            Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉ : ℤ) + 1) (G + 1) := by
  classical
  let G := grade A.toLinearMap g - 1
  have hG : G + 1 = grade A.toLinearMap g := by dsimp [G]; have := two_le_grade; omega
  have hGpos : 0 < G := by have := two_le_grade; omega
  have hy : ∀ i : Fin (G + 1), ∃ y : EuclideanSpace ℝ (Fin (i.val + 1)),
      ∀ w, QuadraticOptimality.regularized
        (Matrix.toEuclideanLin (tridiag A.toLinearMap g (i.val + 1))).toContinuousLinearMap
        (‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)) 1 3 y ≤
        QuadraticOptimality.regularized
        (Matrix.toEuclideanLin (tridiag A.toLinearMap g (i.val + 1))).toContinuousLinearMap
        (‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)) 1 3 w := by
    intro i
    exact QuadraticOptimality.exists_cubic_regularized_min _ _ zero_lt_one
  choose Y hY using hy
  obtain ⟨x, hx⟩ := QuadraticOptimality.exists_cubic_regularized_min A g zero_lt_one
  let shifts := fun i : Fin (G + 1) => (1 : ℝ) * ‖Y i‖ ^ ((3 : ℝ) - 2)
  let K := maxCondition A.toLinearMap g G shifts
  let t := (1 : ℝ) * ‖x‖ ^ ((3 : ℝ) - 2)
  have hopt := fun i : Fin (G + 1) => projected_optimality A.toLinearMap g_ne
    (show i.val + 1 ≤ grade A.toLinearMap g by omega) (Y i) (by norm_num : (2 : ℝ) < 3) (hY i)
  have hK : 1 < K := by
    have hkle : 1 ≤ K := one_le_maxCondition A.toLinearMap g G shifts (fun i => (hopt i).2)
    apply lt_of_le_of_ne hkle
    intro he
    have hz := eq_zero_of_maxCondition_eq_one A.toLinearMap g G hG.le shifts
      (hopt (Fin.last G)).2 he.symm
    omega
  have hxne : x ≠ 0 := by
    intro he
    have hstat := QuadraticOptimality.stationary_of_regularized_min A_symmetric g
      (by norm_num : (2 : ℝ) < 3) 1 x hx
    rw [he] at hstat
    simp only [map_zero, add_zero, smul_zero] at hstat
    exact g_ne hstat
  have hupper : ∀ v : E, inner ℝ (A v) v ≤ U * ‖v‖ ^ 2 :=
    A_symmetric.inner_apply_le_greatestEigenvalue (by simp [E]) (by norm_num : 0 < 2)
  have hb := uniform_regularized_bounds A g_ne A_symmetric hG Y x
    zero_lt_one (by norm_num : (2 : ℝ) < 3) le_rfl hupper hY hx
  have hUt : 0 < U + t := hb.2.1
  let C := 4 * ‖A‖ * K * ‖x‖ * ((U + t) / ‖g‖) ^ 2
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (norm_pos_iff.mpr A_ne))
      (zero_lt_one.trans hK)) (norm_pos_iff.mpr hxne))
      (sq_pos_of_pos (div_pos hUt (norm_pos_iff.mpr g_ne)))
  obtain ⟨θ, hθ, hnegative⟩ := Krylov.exists_negative_logarithmic_budget hC hK
  refine ⟨G, Y, x, hG, hx, hY, θ, hθ, ?_⟩
  have he : 4 * ‖A‖ * K / θ * (t / 1) ^ (1 / ((3 : ℝ) - 2)) *
      ((U + t) / ‖g‖) ^ 2 = C / θ := by
    dsimp only [C, t]
    norm_num only [show (3 : ℝ) - 2 = 1 by norm_num, one_div, div_one, one_mul,
      Real.rpow_one]
    ring
  constructor
  · change (⌈Real.log (4 * ‖A‖ * K / θ * (t / 1) ^ (1 / ((3 : ℝ) - 2)) *
      ((U + t) / ‖g‖) ^ 2) / Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉ : ℤ) + 1 = -1
    rw [he]
    exact hnegative
  · change ¬∃ i : Fin (G + 1), ((i.val + 1 : ℕ) : ℤ) ≤ min
      ((⌈Real.log (4 * ‖A‖ * K / θ * (t / 1) ^ (1 / ((3 : ℝ) - 2)) *
        ((U + t) / ‖g‖) ^ 2) / Real.log ((Real.sqrt K + 1) / (Real.sqrt K - 1))⌉ : ℤ) + 1) (G + 1)
    rw [he, hnegative]
    rintro ⟨i, hi⟩
    have := hi.trans (min_le_left _ _)
    omega
end QuadraticKrylov.LogCountCounterexample
