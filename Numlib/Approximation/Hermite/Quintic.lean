/-
Upstreaming candidate: explicit two-endpoint quintic Hermite interpolation and uniform jet bounds.
Natural home: Hermite interpolation beside Mathlib.LinearAlgebra.Lagrange.
-/
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Quintic Hermite interpolation from endpoint residuals

The data vector comprises the initial value, first and second derivatives, followed by
the three residuals at the other endpoint. The resulting degree-at-most-five polynomial
has the prescribed two endpoint jets. On bounded data cubes all derivatives through order
two are bounded uniformly on `[0,1]`; compactness chooses the bound before the data.
-/

open Polynomial Set

namespace Hermite

/-- The quintic polynomial from the three initial jets and three terminal residuals. -/
noncomputable def quinticFromResiduals (a : Fin 6 → ℝ) : ℝ[X] :=
  C (a 0) + C (a 1) * X + C (a 2 / 2) * X ^ 2 +
    C (10 * a 3 - 4 * a 4 + a 5 / 2) * X ^ 3 +
    C (-15 * a 3 + 7 * a 4 - a 5) * X ^ 4 +
    C (6 * a 3 - 3 * a 4 + a 5 / 2) * X ^ 5

/-- The interpolation polynomial has degree at most five, including degenerate data. -/
theorem quinticFromResiduals_natDegree_le (a : Fin 6 → ℝ) :
    (quinticFromResiduals a).natDegree ≤ 5 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [quinticFromResiduals, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  have h0 : n ≠ 0 := by omega
  have h1 : 1 ≠ n := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  have h5 : n ≠ 5 := by omega
  simp [h0, h1, h2, h3, h4, h5]

/-- Explicit coefficients of the quintic interpolation polynomial. -/
theorem quinticFromResiduals_coeff (a : Fin 6 → ℝ) (j : Fin 6) :
    (quinticFromResiduals a).coeff j =
      ![a 0, a 1, a 2 / 2, 10 * a 3 - 4 * a 4 + a 5 / 2,
        -15 * a 3 + 7 * a 4 - a 5, 6 * a 3 - 3 * a 4 + a 5 / 2] j := by
  fin_cases j <;> simp only [quinticFromResiduals, coeff_add,
    coeff_C_mul, coeff_X, coeff_C] <;> norm_num

/-- The initial jets and terminal residuals of the explicit quintic polynomial. -/
theorem quinticFromResiduals_endpoints (a : Fin 6 → ℝ) :
    (quinticFromResiduals a).eval 0 = a 0 ∧
    (derivative (quinticFromResiduals a)).eval 0 = a 1 ∧
    (derivative (derivative (quinticFromResiduals a))).eval 0 = a 2 ∧
    (quinticFromResiduals a).eval 1 = a 0 + a 1 + a 2 / 2 + a 3 ∧
    (derivative (quinticFromResiduals a)).eval 1 = a 1 + a 2 + a 4 ∧
    (derivative (derivative (quinticFromResiduals a))).eval 1 = a 2 + a 5 := by
  repeat' constructor <;> norm_num [quinticFromResiduals, derivative_add, derivative_C_mul,
    derivative_pow, derivative_X] <;> ring_nf

/-- A uniform bound on a bounded data cube for the actual derivatives of orders zero
through two. The positive bound is chosen before the data and evaluation point. -/
theorem quinticFromResiduals_uniform_bound (κ : ℝ) :
    ∃ K > 0, ∀ a : Fin 6 → ℝ, (∀ j, |a j| ≤ κ) →
      ∀ j ≤ 2, ∀ t ∈ Icc (0 : ℝ) 1,
        |iteratedDeriv j (fun z => (quinticFromResiduals a).eval z) t| ≤ K := by
  let S : Set ((Fin 6 → ℝ) × ℝ) :=
    Icc (fun _ => -κ) (fun _ => κ) ×ˢ Icc (0 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let G : ((Fin 6 → ℝ) × ℝ) → (Fin 3 → ℝ) := fun z j =>
    (derivative^[j.val] (quinticFromResiduals z.1)).eval z.2
  have hG : Continuous G := by
    apply continuous_pi
    intro j
    fin_cases j <;>
      simp only [G, Function.iterate_zero_apply,
        Function.iterate_succ_apply', quinticFromResiduals, derivative_add,
        derivative_C, derivative_C_mul, derivative_pow, derivative_X, eval_add, eval_mul,
        eval_C, eval_X, eval_pow]
    all_goals fun_prop
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max K 0 + 1, by positivity, ?_⟩
  intro a ha j hj t ht
  have hm : (a, t) ∈ S := ⟨⟨fun i => (abs_le.mp (ha i)).1,
    fun i => (abs_le.mp (ha i)).2⟩, ht⟩
  have hcoord := norm_le_pi_norm (G (a,t)) (⟨j,by omega⟩ : Fin 3)
  rw [Polynomial.iteratedDeriv_eval]
  have hcoord' : |(derivative^[j] (quinticFromResiduals a)).eval t| ≤ ‖G (a,t)‖ := by
    simpa [G, Real.norm_eq_abs] using hcoord
  exact hcoord'.trans ((hK (a,t) hm).trans (by linarith [le_max_left K (0 : ℝ)]))
end Hermite
