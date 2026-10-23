import Numlib.Optimization.Quadratic.Krylov.RegularizationMonotonicity
import Numlib.Krylov.Lanczos.RadiusLower
import Numlib.Krylov.Lanczos.ConditionNumber
import Numlib.Krylov.Convergence.ChebyshevFactor

/-!
# Finite relative-gradient convergence of actual regularized Lanczos minimizers

Actual global subproblem minima give the common radius floor and geometric
residual envelope. Their true finite maximum condition number controls the
logarithmic iteration budget, with exact convergence at the Krylov grade and
a separately justified condition-one case.
-/

open scoped Matrix ComplexOrder
namespace QuadraticKrylov
open Krylov Lanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every actual regularized Lanczos minimizer has the common source radius
floor and uniform geometric residual envelope. -/
theorem uniform_regularized_bounds (A : E →L[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.toLinearMap.IsSymmetric) {G : ℕ} (hG : G + 1 = grade A.toLinearMap g)
    (Y : (i : Fin (G + 1)) → EuclideanSpace ℝ (Fin (i.val + 1))) (x : E)
    {σ r U B : ℝ} (hσ : 0 < σ) (hr : 2 < r) (hB : ‖A‖ ≤ B)
    (hU : ∀ v, inner ℝ (A v) v ≤ U * ‖v‖ ^ 2)
    (hmin : ∀ i w, QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (tridiag A.toLinearMap g (i.val + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)) σ r (Y i) ≤
      QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (tridiag A.toLinearMap g (i.val + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)) σ r w)
    (hx : ∀ z, QuadraticOptimality.regularized A g σ r x ≤
      QuadraticOptimality.regularized A g σ r z) :
    let shifts := fun i => σ * ‖Y i‖ ^ (r - 2)
    let K := maxCondition A.toLinearMap g G shifts
    let t := σ * ‖x‖ ^ (r - 2)
    1 ≤ K ∧ 0 < U + t ∧ ∀ i : Fin (G + 1),
      ‖g‖ / (U + t) ≤ ‖Y i‖ ∧
      ‖A (basisEmbedding A.toLinearMap g (by omega : i.val + 1 ≤ grade A.toLinearMap g) (Y i)) +
        shifts i • basisEmbedding A.toLinearMap g (by omega : i.val + 1 ≤ grade A.toLinearMap g)
          (Y i) + g‖ ≤ 2 * B * K * ‖x‖ * chebyshevFactor K ^ i.val := by
  let shifts := fun i : Fin (G + 1) => σ * ‖Y i‖ ^ (r - 2)
  let K := maxCondition A.toLinearMap g G shifts
  let t := σ * ‖x‖ ^ (r - 2)
  have hdim : ∀ i : Fin (G + 1), i.val + 1 ≤ grade A.toLinearMap g := fun i => by omega
  have hopt := fun i => projected_optimality A.toLinearMap hg (hdim i) (Y i) hr (hmin i)
  have hPD := fun i => (hopt i).2
  have hK : 1 ≤ K := one_le_maxCondition A.toLinearMap g G shifts hPD
  have hnorm := fun i => norm_le_norm_of_regularized_ambient_min A hg hA
    (hdim i) (Y i) x hσ hr (hopt i).1 hx
  have hshift : ∀ i, shifts i ≤ t := fun i => mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) (hnorm i) (by linarith)) hσ.le
  have hlow := fun i => norm_rhs_le_of_quadratic_upper A.toLinearMap hA (hdim i)
    (Y i) hU (hPD i) (hopt i).1
  have hUt : 0 < U + t := lt_of_lt_of_le (hlow 0).1 (by linarith [hshift 0])
  refine ⟨hK, hUt, fun i => ⟨?_, ?_⟩⟩
  · apply (div_le_iff₀ hUt).mpr
    have hh := (hlow i).2
    have ht := mul_le_mul_of_nonneg_right (add_le_add_left (hshift i) U) (norm_nonneg (Y i))
    dsimp [shifts] at ht
    nlinarith only [hh, ht]
  · have hb := regularized_gradient_bound A hg hA (hdim i) (Y i) hσ hr (hmin i)
    dsimp only at hb
    rw [norm_fderiv_regularized A g hA hr σ,
      (basisEmbedding A.toLinearMap g (hdim i)).norm_map] at hb
    have hrad : (σ * ‖Y i‖ ^ (r - 2) / σ) ^ (1 / (r - 2)) = ‖Y i‖ := by
      rw [mul_div_cancel_left₀ _ hσ.ne', ←Real.rpow_mul (norm_nonneg _),
        mul_one_div_cancel (by linarith : r - 2 ≠ 0), Real.rpow_one]
    rw [hrad] at hb
    change _ ≤ 2 * ‖A‖ * conditionNumber A.toLinearMap g i.val (shifts i) * ‖Y i‖ *
      chebyshevFactor (conditionNumber A.toLinearMap g i.val (shifts i)) ^ i.val at hb
    have hcond := one_le_conditionNumber A.toLinearMap g i.val (shifts i) (hPD i)
    have hle := conditionNumber_le_maxCondition A.toLinearMap g G shifts i
    have hpow := mul_chebyshevFactor_pow_le
      (C := 2 * ‖A‖ * ‖Y i‖) (by positivity) hcond hle i.val
    have hB0 : 0 ≤ B := (norm_nonneg A).trans hB
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hq : 0 ≤ chebyshevFactor K := chebyshevFactor_nonneg hK
    apply hb.trans
    calc _ ≤ 2 * ‖A‖ * K * ‖Y i‖ * chebyshevFactor K ^ i.val := by nlinarith only [hpow]
      _ ≤ 2 * B * K * ‖x‖ * chebyshevFactor K ^ i.val := by
        gcongr
        exact hnorm i
end QuadraticKrylov



namespace QuadraticKrylov
open Krylov Lanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- True regularized Lanczos minimizers reach the relative model-gradient test
within the natural logarithmic budget or exact Krylov grade. -/
theorem regularized_relative_gradient_hitting (A : E →L[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.toLinearMap.IsSymmetric) {G : ℕ} (hG : G + 1 = grade A.toLinearMap g)
    (Y : (i : Fin (G + 1)) → EuclideanSpace ℝ (Fin (i.val + 1))) (x : E)
    {σ r U B θ : ℝ} (hσ : 0 < σ) (hr : 2 < r) (hB : ‖A‖ ≤ B) (hθ : 0 < θ)
    (hU : ∀ v, inner ℝ (A v) v ≤ U * ‖v‖ ^ 2)
    (hmin : ∀ i w, QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (tridiag A.toLinearMap g (i.val + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)) σ r (Y i) ≤
      QuadraticOptimality.regularized
      (Matrix.toEuclideanLin (tridiag A.toLinearMap g (i.val + 1))).toContinuousLinearMap
      (‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)) σ r w)
    (hx : ∀ z, QuadraticOptimality.regularized A g σ r x ≤
      QuadraticOptimality.regularized A g σ r z) :
    let shifts := fun i => σ * ‖Y i‖ ^ (r - 2)
    let K := maxCondition A.toLinearMap g G shifts
    let t := σ * ‖x‖ ^ (r - 2)
    let C := 2 * B * K * ‖x‖
    let ε := θ / 2 * (‖g‖ / (U + t)) ^ 2
    ∃ i : Fin (G + 1),
      i.val + 1 ≤ min (if K = 1 then 1 else GeometricDecay.budget C ε (chebyshevFactor K) + 1)
        (G + 1) ∧
      ‖fderiv ℝ (QuadraticOptimality.regularized A g σ r)
        (basisEmbedding A.toLinearMap g (by omega : i.val + 1 ≤ grade A.toLinearMap g) (Y i))‖ ≤
        θ / 2 * ‖Y i‖ ^ 2 := by
  classical
  let shifts := fun i : Fin (G + 1) => σ * ‖Y i‖ ^ (r - 2)
  let K := maxCondition A.toLinearMap g G shifts
  let t := σ * ‖x‖ ^ (r - 2)
  let C := 2 * B * K * ‖x‖
  let ε := θ / 2 * (‖g‖ / (U + t)) ^ 2
  have hdim : ∀ i : Fin (G + 1), i.val + 1 ≤ grade A.toLinearMap g := fun i => by omega
  let R := fun i : Fin (G + 1) => ‖fderiv ℝ (QuadraticOptimality.regularized A g σ r)
    (basisEmbedding A.toLinearMap g (hdim i) (Y i))‖
  change ∃ i : Fin (G + 1), i.val + 1 ≤
    min (if K = 1 then 1 else GeometricDecay.budget C ε (chebyshevFactor K) + 1)
      (G + 1) ∧ R i ≤ θ / 2 * ‖Y i‖ ^ 2
  obtain ⟨hK, hUt, hb⟩ := uniform_regularized_bounds A hg hA hG Y x hσ hr hB hU hmin hx
  have hε : 0 < ε := mul_pos (half_pos hθ) (sq_pos_of_pos (div_pos (norm_pos_iff.mpr hg) hUt))
  have hbound : ∀ i, R i ≤ C * chebyshevFactor K ^ i.val := by
    intro i
    dsimp [R]
    rw [norm_fderiv_regularized A g hA hr σ, (basisEmbedding A.toLinearMap g (hdim i)).norm_map]
    exact (hb i).2
  have hexact : R (Fin.last G) = 0 := by
    have hsolve := (projected_optimality A.toLinearMap hg hG.le (Y (Fin.last G)) hr
      (hmin (Fin.last G))).1
    have he := residual_eq_zero_at_grade A.toLinearMap hg hA hG (Y (Fin.last G))
      (σ * ‖Y (Fin.last G)‖ ^ (r - 2)) hsolve
    dsimp [R]
    rw [norm_fderiv_regularized A g hA hr σ,
      (basisEmbedding A.toLinearMap g (hdim (Fin.last G))).norm_map]
    change A (basisEmbedding A.toLinearMap g (hdim (Fin.last G)) (Y (Fin.last G))) +
      (σ * ‖Y (Fin.last G)‖ ^ (r - 2)) •
        basisEmbedding A.toLinearMap g (hdim (Fin.last G)) (Y (Fin.last G)) + g = 0 at he
    rw [he, norm_zero]
  have htarget : ∀ i, R i ≤ ε → R i ≤ θ / 2 * ‖Y i‖ ^ 2 := by
    intro i hi
    apply hi.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hUt.le) (hb i).1 2) (half_pos hθ).le
  by_cases hone : K = 1
  · have hPD := (projected_optimality A.toLinearMap hg hG.le (Y (Fin.last G)) hr
      (hmin (Fin.last G))).2
    have hG0 := eq_zero_of_maxCondition_eq_one A.toLinearMap g G hG.le shifts hPD hone
    refine ⟨Fin.last G, ?_, htarget _ (by rw [hexact]; exact hε.le)⟩
    simp only [hone, ite_true, Fin.val_last, hG0]
    omega
  · have hKgt : 1 < K := lt_of_le_of_ne hK (Ne.symm hone)
    have hB0 : 0 ≤ B := (norm_nonneg A).trans hB
    have hC : 0 ≤ C := by dsimp [C]; positivity
    obtain ⟨i, hi, hRi⟩ := GeometricDecay.exists_fin_le_min_grade hC hε
      (chebyshevFactor_pos hKgt) (chebyshevFactor_lt_one K) R hexact hbound
    refine ⟨i, ?_, htarget i hRi⟩
    simpa only [hone, ite_false] using hi
end QuadraticKrylov
