import Numlib.Analysis.Calculus.QuinticHermite
import NumlibSurface.CartisGouldToint.AppendixA.Section09

/-!
# Quintic interpolation and the missing initial-jet bound

The interpolation and explicit coefficient clauses of Lemma B.2.1 hold as written.
Its final bound from residuals alone is false: adding an arbitrary constant changes none of
the residuals. The corrected uniform statement adds the initial-jet bound used in Theorem A.9.1.
-/

noncomputable section
open Polynomial

namespace CartisGouldToint.AppendixB.Chapter02

/-- The valid interpolation and explicit-coefficient clauses of Lemma B.2.1. -/
theorem lemma_B_2_1_interpolation (a b : ℕ → ℝ) :
    ∃ P : ℝ[X], P.natDegree ≤ 5 ∧
      (∀ j ≤ 2, iteratedDeriv j (fun x => P.eval x) 0 = a j ∧
        iteratedDeriv j (fun x => P.eval x) 1 = b j) ∧
      P.coeff 0 = a 0 ∧ P.coeff 1 = a 1 ∧ P.coeff 2 = a 2 / 2 ∧
      P.coeff 3 = 10 * Hermite.quinticResidual a b 0 -
        4 * Hermite.quinticResidual a b 1 + Hermite.quinticResidual a b 2 / 2 ∧
      P.coeff 4 = -15 * Hermite.quinticResidual a b 0 +
        7 * Hermite.quinticResidual a b 1 - Hermite.quinticResidual a b 2 ∧
      P.coeff 5 = 6 * Hermite.quinticResidual a b 0 -
        3 * Hermite.quinticResidual a b 1 + Hermite.quinticResidual a b 2 / 2 := by
  refine ⟨Hermite.quinticPolynomial a b, Hermite.natDegree_quinticPolynomial_le a b,
    fun j hj => Hermite.iteratedDeriv_quinticPolynomial_endpoints a b hj, ?_⟩
  norm_num [Hermite.coeff_quinticPolynomial, Hermite.quinticCoefficient]

/-- The residual-only uniform bound in Lemma B.2.1 fails already for constant data and
`κ_f = 1`. No choice of an interpolating polynomial can repair its value at the left endpoint. -/
theorem no_uniform_hermite_bound_of_residuals :
    ¬∃ B > (0 : ℝ), ∀ (a b : ℕ → ℝ),
      (∀ j ≤ 2, |Hermite.quinticResidual a b j| ≤ 1) →
      ∃ P : ℝ[X], P.natDegree ≤ 5 ∧
        (∀ j ≤ 2, iteratedDeriv j (fun x => P.eval x) 0 = a j ∧
          iteratedDeriv j (fun x => P.eval x) 1 = b j) ∧
        ∀ j ≤ 2, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |iteratedDeriv j (fun x => P.eval x) t| ≤ B := by
  rintro ⟨B, _hB, h⟩
  let a : ℕ → ℝ := Hermite.constantJet (B + 1)
  have hr : ∀ j ≤ 2, |Hermite.quinticResidual a a j| ≤ 1 := by
    intro j hj
    interval_cases j <;> simp [a, Hermite.constantJet, Hermite.quinticResidual]
  obtain ⟨P, _hdeg, hjets, hbound⟩ := h a a hr
  have hv : P.eval 0 = B + 1 := by simpa [a, Hermite.constantJet] using (hjets 0 (by omega)).1
  have hb := hbound 0 (by omega) 0 (by constructor <;> norm_num)
  change |P.eval 0| ≤ B at hb
  rw [hv] at hb
  linarith [le_abs_self (B + 1)]

/-- Corrected Lemma B.2.1 uniform bound: initial derivatives must be bounded as well as
the three residuals. The positive constant is chosen before all endpoint data. -/
theorem lemma_B_2_1_corrected (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ B > (0 : ℝ), ∀ (a b : ℕ → ℝ), (∀ j ≤ 2, |a j| ≤ κ) →
      (∀ j ≤ 2, |Hermite.quinticResidual a b j| ≤ κ) →
      ∃ P : ℝ[X], P.natDegree ≤ 5 ∧
        (∀ j ≤ 2, iteratedDeriv j (fun x => P.eval x) 0 = a j ∧
          iteratedDeriv j (fun x => P.eval x) 1 = b j) ∧
        ∀ j ≤ 2, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |iteratedDeriv j (fun x => P.eval x) t| ≤ B := by
  obtain ⟨L, B, h⟩ := CartisGouldToint.AppendixA.Section09.theorem_A_9_1 2 κ
    (zero_le_one.trans hκ)
  refine ⟨(B : ℝ) + 1, by positivity, fun a b ha hr => ?_⟩
  obtain ⟨P, hdeg, hjets, _hLip, hbound⟩ := h 1 a b zero_lt_one (by
    intro j hj
    simpa only [one_pow, mul_one, ← Hermite.quinticResidual_eq_endpointTaylor_discrepancy a b hj]
      using hr j hj)
  refine ⟨P, by simpa using hdeg, hjets, fun j hj t ht => ?_⟩
  exact (hbound ha hκ j hj t ht).trans (by linarith)

end CartisGouldToint.AppendixB.Chapter02
