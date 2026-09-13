import Numlib.Approximation.Hermite
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section04

/-!
# Quarteroni–Sacco–Saleri §8.8: applications

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §8.8: the finite element analysis of a clamped beam with piecewise cubic
Hermite elements (§8.8.1) and the tomographic reconstruction by parametric splines (§8.8.2). An
applications section contributes nodes only for numbered results; the one here is (8.64), the
canonical cubic Hermite basis of the reference interval `[0, 1]`, dual to the values and the
derivatives at its endpoints as (8.62) prescribes. The variational problem (8.60), the system
(8.67)–(8.69) and the conjugate gradient experiments are not stated.

## Main results

* `equation_8_64_basis` — the four cubics `φ̂₀⁽⁰⁾, φ̂₀⁽¹⁾, φ̂₁⁽⁰⁾, φ̂₁⁽¹⁾` of (8.64).
* `equation_8_64` — they are dual to the values and derivatives at `0` and `1`.
* `equation_8_64_hermite` — the cubic Hermite interpolant at the two nodes `0, 1` is
  `f(0) φ̂₀⁽⁰⁾ + f'(0) φ̂₀⁽¹⁾ + f(1) φ̂₁⁽⁰⁾ + f'(1) φ̂₁⁽¹⁾`, the reference-interval instance
  of (8.32) with `m_i = 1` (Example 8.6 at the nodes `0, 1`).
-/

open Polynomial

namespace QuarteroniSaccoSaleri.Chapter08

/-- **(8.64), the cubic Hermite basis of `[0, 1]`**: `equation_8_64_basis i k` is the function
`φ̂_i^{(k)}` associated with the node `i ∈ {0, 1}` and the derivative order `k ∈ {0, 1}`,

`φ̂₀⁽⁰⁾ = 1 - 3x̂² + 2x̂³`, `φ̂₀⁽¹⁾ = x̂ - 2x̂² + x̂³`,
`φ̂₁⁽⁰⁾ = 3x̂² - 2x̂³`, `φ̂₁⁽¹⁾ = -x̂² + x̂³`. -/
noncomputable def equation_8_64_basis (i k : Fin 2) : ℝ[X] :=
  ![![1 - 3 * X ^ 2 + 2 * X ^ 3, X - 2 * X ^ 2 + X ^ 3],
    ![3 * X ^ 2 - 2 * X ^ 3, -X ^ 2 + X ^ 3]] i k

/-- **(8.64)**: the four cubics satisfy the conditions (8.62) on the reference interval,
`(φ̂_i^{(k)})^{(p)}(j) = δ_ij δ_kp` for `i, j, k, p ∈ {0, 1}` — the functions with superscript `0`
take the value `δ_ij` and have zero derivative at the nodes, those with superscript `1` vanish
at the nodes and have derivative `δ_ij` there. -/
theorem equation_8_64 (i j k p : Fin 2) :
    (derivative^[(p : ℕ)] (equation_8_64_basis i k)).eval ((j : ℕ) : ℝ)
      = if i = j ∧ k = p then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases p <;>
    norm_num [equation_8_64_basis]

/-- The nodes `0, 1` of the reference interval are distinct. -/
theorem equation_8_64_injective : Function.Injective (![0, 1] : Fin 2 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- **(8.64), as a Hermite interpolant.** The cubic Hermite interpolant of `f` at the nodes `0, 1`
with values and first derivatives — `Hermite.interpolate ![0, 1] ![1, 1] f` — is

`f(0) φ̂₀⁽⁰⁾ + f'(0) φ̂₀⁽¹⁾ + f(1) φ̂₁⁽⁰⁾ + f'(1) φ̂₁⁽¹⁾`,

by the uniqueness `Hermite.eq_interpolate`: it is (8.32) on the reference element with `m_i = 1`,
and Example 8.6 at the two nodes. -/
theorem equation_8_64_hermite (f : ℝ → ℝ) :
    Hermite.interpolate ![0, 1] ![1, 1] f
      = C (f 0) * equation_8_64_basis 0 0 + C (deriv f 0) * equation_8_64_basis 0 1
        + C (f 1) * equation_8_64_basis 1 0 + C (deriv f 1) * equation_8_64_basis 1 1 := by
  refine (Hermite.eq_interpolate equation_8_64_injective ?_ ?_).symm
  · have hsum : ∑ i : Fin 2, ((![1, 1] : Fin 2 → ℕ) i + 1) = 4 := by simp [Fin.sum_univ_two]
    rw [hsum]
    refine lt_of_le_of_lt ?_ (show ((3 : ℕ) : WithBot ℕ) < ((4 : ℕ) : WithBot ℕ) by norm_num)
    simp only [equation_8_64_basis, Matrix.cons_val_zero, Matrix.cons_val_one]
    compute_degree!
  · intro i j hj
    have hj1 : j ≤ 1 := by fin_cases i <;> simpa using hj
    interval_cases j <;> fin_cases i <;> norm_num [equation_8_64_basis, iteratedDeriv_one]

end QuarteroniSaccoSaleri.Chapter08
