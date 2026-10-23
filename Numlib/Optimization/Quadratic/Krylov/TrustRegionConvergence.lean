import Numlib.Optimization.Quadratic.Krylov.TrustRegion
import Numlib.Krylov.Lanczos.ConditionNumber
import Numlib.Krylov.Convergence.ChebyshevFactor
import Mathlib.Tactic
/-!
# Finite convergence of actual constrained Lanczos minimizers

Every bound is derived from true projected global minima and actual stationary
shifts. The maximum condition number is the finite maximum through the exact
grade. Natural ceilings include large tolerances, and the condition-one branch
is justified by cyclicity rather than by a vanishing one-dimensional factor.
-/

open scoped Matrix ComplexOrder
namespace QuadraticKrylov
open Krylov Lanczos
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A true finite sequence of constrained Lanczos minimizers reaches a positive residual
tolerance within the natural logarithmic budget or exact grade. The genuine maximum
condition-one case terminates in one step. -/
theorem trust_region_exists_residual_le (A : E →L[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.toLinearMap.IsSymmetric) {G : ℕ} (hG : G + 1 = grade A.toLinearMap g)
    (ys : (i : Fin (G + 1)) → EuclideanSpace ℝ (Fin (i.val + 1)))
    (shifts : Fin (G + 1) → ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hfeas : ∀ i, ‖ys i‖ ≤ Δ)
    (hmin : ∀ i z, ‖z‖ ≤ Δ → projectedQuadratic A.toLinearMap g i.val (ys i) ≤
      projectedQuadratic A.toLinearMap g i.val z)
    (hsolve : ∀ i, Matrix.toEuclideanLin
      (tridiag A.toLinearMap g (i.val + 1) + shifts i • 1) (ys i) =
        -(‖g‖ • PiLp.single 2 (0 : Fin (i.val + 1)) (1 : ℝ)))
    {B ε : ℝ} (hB : ‖A‖ ≤ B) (hε : 0 < ε) :
    let K := maxCondition A.toLinearMap g G shifts
    ∃ i : Fin (G + 1),
      i.val + 1 ≤ min
        (if K = 1 then 1 else GeometricDecay.budget (2 * B * K * Δ) ε
          (chebyshevFactor K) + 1) (G + 1) ∧
      ‖A (basisEmbedding A.toLinearMap g (by omega : i.val + 1 ≤ grade A.toLinearMap g)
        (ys i)) + shifts i •
          basisEmbedding A.toLinearMap g (by omega : i.val + 1 ≤ grade A.toLinearMap g)
            (ys i) + g‖ ≤ ε := by
  let K := maxCondition A.toLinearMap g G shifts
  change ∃ i : Fin (G + 1), i.val + 1 ≤ min
    (if K = 1 then 1 else GeometricDecay.budget (2 * B * K * Δ) ε
      (chebyshevFactor K) + 1) (G + 1) ∧ _
  have hPD : ∀ i, (tridiag A.toLinearMap g (i.val + 1) + shifts i • 1).PosDef := by
    intro i
    exact (projected_trust_region_optimality A.toLinearMap hg (by omega) (ys i)
      hΔ (hfeas i) (hmin i) (hsolve i)).2.1
  have hK : 1 ≤ K := one_le_maxCondition A.toLinearMap g G shifts hPD
  let R : ℕ → ℝ := fun m => if hm : m < G + 1 then
    ‖A (basisEmbedding A.toLinearMap g (by omega : m + 1 ≤ grade A.toLinearMap g)
      (ys ⟨m, hm⟩)) + shifts ⟨m, hm⟩ •
        basisEmbedding A.toLinearMap g (by omega : m + 1 ≤ grade A.toLinearMap g)
          (ys ⟨m, hm⟩) + g‖ else 0
  have hexact : R G = 0 := by
    dsimp only [R]
    rw [dite_eq_left (Nat.lt_succ_self G)]
    have hh := residual_eq_zero_at_grade A.toLinearMap hg hA hG
      (ys (Fin.last G)) (shifts (Fin.last G)) (hsolve (Fin.last G))
    exact norm_eq_zero.mpr hh
  by_cases hone : K = 1
  · have hG0 : G = 0 := eq_zero_of_maxCondition_eq_one A.toLinearMap g G hG.le shifts
      (hPD (Fin.last G)) hone
    subst G
    refine ⟨0, by simp [hone], ?_⟩
    have hh : R 0 = 0 := hexact
    dsimp only [R] at hh
    rw [dite_eq_left (by norm_num : 0 < 0 + 1)] at hh
    exact hh.le.trans hε.le
  · have hKpos : 1 < K := lt_of_le_of_ne hK (Ne.symm hone)
    have hBn : 0 ≤ B := (norm_nonneg A).trans hB
    have hC : 0 ≤ 2 * B * K * Δ := by positivity
    have hbound : ∀ m < G + 1, R m ≤ (2 * B * K * Δ) * chebyshevFactor K ^ m := by
      intro m hm
      let i : Fin (G + 1) := ⟨m, hm⟩
      have hκ := one_le_conditionNumber A.toLinearMap g m (shifts i) (hPD i)
      have hle := conditionNumber_le_maxCondition A.toLinearMap g G shifts i
      have hq := chebyshevFactor_nonneg hκ
      have hr := trust_region_residual_bound A hg hA (by omega) (ys i) hΔ
        (hfeas i) (hmin i) (hsolve i)
      dsimp only at hr
      change R m ≤ _
      dsimp only [R]
      rw [dite_eq_left hm]
      calc
        _ ≤ 2 * ‖A‖ * conditionNumber A.toLinearMap g m (shifts i) * Δ *
            chebyshevFactor (conditionNumber A.toLinearMap g m (shifts i)) ^ m := hr
        _ ≤ 2 * B * conditionNumber A.toLinearMap g m (shifts i) * Δ *
            chebyshevFactor (conditionNumber A.toLinearMap g m (shifts i)) ^ m := by
          gcongr
        _ = (2 * B * Δ) * conditionNumber A.toLinearMap g m (shifts i) *
            chebyshevFactor (conditionNumber A.toLinearMap g m (shifts i)) ^ m := by ring
        _ ≤ (2 * B * Δ) * K * chebyshevFactor K ^ m :=
          mul_chebyshevFactor_pow_le (by positivity) hκ hle m
        _ = (2 * B * K * Δ) * chebyshevFactor K ^ m := by ring
    obtain ⟨m, hm, hn, hr⟩ := GeometricDecay.exists_le_min_grade hC hε
      (chebyshevFactor_pos hKpos) (chebyshevFactor_lt_one K) R (Nat.succ_pos G)
      (by simpa using hexact) hbound
    refine ⟨⟨m, hm⟩, ?_, ?_⟩
    · simpa only [ite_eq_right hone] using hn
    · simpa only [R, dite_eq_left hm] using hr
end QuadraticKrylov
