/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Hermite
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section04

/-!
# Quarteroni, Sacco and Saleri, Section 8.8: Applications

This module formalizes the numbered result of Section 8.8 of [quarteroni2000numerical]. The section
applies interpolation to the finite element analysis of a clamped beam with piecewise cubic Hermite
elements (Section 8.8.1) and to tomographic reconstruction by parametric splines (Section 8.8.2).
Its numbered result is (8.64): the cubic Hermite basis $\hat\varphi_0^{(0)}, \hat\varphi_0^{(1)},
\hat\varphi_1^{(0)}, \hat\varphi_1^{(1)}$ of the reference interval $[0, 1]$, which is dual to the
values and the derivatives at the endpoints as (8.62) prescribes. The proofs use the Hermite
interpolant `Hermite.interpolate` of `Numlib.Approximation.Hermite`.

## Main definitions

* (8.64), `QuarteroniSaccoSaleri.Chapter08.equation_8_64_basis`: the four cubic polynomials
  $\hat\varphi_i^{(k)}$ of (8.64).

## Main results

* (8.64), `QuarteroniSaccoSaleri.Chapter08.equation_8_64`: $(\hat\varphi_i^{(k)})^{(p)}(j) =
  \delta_{ij} \delta_{kp}$ for $i, j, k, p \in \{0, 1\}$.
* (8.64), `QuarteroniSaccoSaleri.Chapter08.equation_8_64_hermite`: the cubic Hermite interpolant at
  the nodes $0, 1$ is $f(0) \hat\varphi_0^{(0)} + f'(0) \hat\varphi_0^{(1)} + f(1)
  \hat\varphi_1^{(0)} + f'(1) \hat\varphi_1^{(1)}$.

## Not formalized

* **The variational problem (8.60).**
* **The linear system (8.67)–(8.69).**
* **The conjugate gradient experiments of Section 8.8.1.**
* **The tomographic reconstruction of Section 8.8.2.**
-/

open Polynomial

namespace QuarteroniSaccoSaleri.Chapter08

/-- **Equation (8.64)** of [quarteroni2000numerical], the cubic Hermite basis of $[0, 1]$. For a
node $i \in \{0, 1\}$ and a derivative order $k \in \{0, 1\}$, the cubic polynomial
$\hat\varphi_i^{(k)}$ is
$$\hat\varphi_0^{(0)}(\hat x) = 1 - 3\hat x^2 + 2\hat x^3, \qquad \hat\varphi_0^{(1)}(\hat x) =
  \hat x - 2\hat x^2 + \hat x^3,$$
$$\hat\varphi_1^{(0)}(\hat x) = 3\hat x^2 - 2\hat x^3, \qquad \hat\varphi_1^{(1)}(\hat x) =
  -\hat x^2 + \hat x^3.$$

The polynomial $\hat\varphi_i^{(k)}$ is `QuarteroniSaccoSaleri.Chapter08.equation_8_64_basis i
k`. -/
noncomputable def equation_8_64_basis (i k : Fin 2) : ℝ[X] :=
  ![![1 - 3 * X ^ 2 + 2 * X ^ 3, X - 2 * X ^ 2 + X ^ 3],
    ![3 * X ^ 2 - 2 * X ^ 3, -X ^ 2 + X ^ 3]] i k

/-- **Equation (8.64)** of [quarteroni2000numerical], the conditions (8.62). For all
$i, j, k, p \in \{0, 1\}$,
$$(\hat\varphi_i^{(k)})^{(p)}(j) = \delta_{ij} \delta_{kp}.$$
So the functions with superscript $0$ take the value $\delta_{ij}$ at the node $j$ and have
derivative $0$ at the nodes, and the functions with superscript $1$ vanish at the nodes and have
derivative $\delta_{ij}$ at the node $j$. -/
theorem equation_8_64 (i j k p : Fin 2) :
    (derivative^[(p : ℕ)] (equation_8_64_basis i k)).eval ((j : ℕ) : ℝ)
      = if i = j ∧ k = p then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases p <;>
    norm_num [equation_8_64_basis]

/-- The nodes $0$ and $1$ of the reference interval are distinct. This supports (8.64). -/
theorem equation_8_64_injective : Function.Injective (![0, 1] : Fin 2 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- **Equation (8.64)** of [quarteroni2000numerical], as a Hermite interpolant. Let
$f : \mathbb{R} \to \mathbb{R}$. The cubic Hermite interpolant of $f$ at the nodes $0, 1$ with
the values and the first derivatives is
$$f(0) \hat\varphi_0^{(0)} + f'(0) \hat\varphi_0^{(1)} + f(1) \hat\varphi_1^{(0)} + f'(1)
  \hat\varphi_1^{(1)}.$$

The interpolant is `Hermite.interpolate ![0, 1] ![1, 1] f`, and $f'$ is `deriv f`. This is
(8.32) on the reference interval with $m_i = 1$, and Example 8.6 at the nodes $0$ and $1$. The
proof uses the uniqueness `Hermite.eq_interpolate`. -/
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
