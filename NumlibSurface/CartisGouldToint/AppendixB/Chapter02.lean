import Numlib.Approximation.Hermite.Quintic
import Numlib.Optimization.SteepestDescent.Exact.CorridorEuclidean
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Appendix B.2: quintic Hermite interpolation

The endpoint interpolation and coefficient assertions in Lemma B.2.1 are valid. Its
printed residual-only uniform bound is false: the polynomial with constant value `M`
has three zero residuals and unbounded size as `M` grows. The declaration
`quinticHermite_residual_only_bound_false` proves this obstruction. The original numbered
item remains marked wrong in its plan; `lemma_B_2_1_corrected` supplies the endpoint and
coefficient assertions together with the valid uniform estimate when the three initial
jets are bounded as well.

The remaining construction uses the book's global rounding convention: its
canonical iteration horizon is the natural floor of the inverse-square rate.

-/

open Polynomial Set

namespace CartisGouldToint
/-- The quintic Hermite polynomial of (B.2.1)–(B.2.2), for arbitrary endpoint jets. -/
noncomputable def quinticHermite (f0 g0 H0 f1 g1 H1 : ℝ) : ℝ[X] :=
  Hermite.quinticFromResiduals ![f0, g0, H0, f1 - f0 - g0 - H0 / 2,
    g1 - g0 - H0, H1 - H0]

/-- All six endpoint conditions of Lemma B.2.1, with actual function derivatives. -/
theorem quinticHermite_endpoints (f0 g0 H0 f1 g1 H1 : ℝ) :
    (quinticHermite f0 g0 H0 f1 g1 H1).eval 0 = f0 ∧
    iteratedDeriv 1 (fun z => (quinticHermite f0 g0 H0 f1 g1 H1).eval z) 0 = g0 ∧
    iteratedDeriv 2 (fun z => (quinticHermite f0 g0 H0 f1 g1 H1).eval z) 0 = H0 ∧
    (quinticHermite f0 g0 H0 f1 g1 H1).eval 1 = f1 ∧
    iteratedDeriv 1 (fun z => (quinticHermite f0 g0 H0 f1 g1 H1).eval z) 1 = g1 ∧
    iteratedDeriv 2 (fun z => (quinticHermite f0 g0 H0 f1 g1 H1).eval z) 1 = H1 := by
  have h := Hermite.quinticFromResiduals_endpoints
    ![f0, g0, H0, f1 - f0 - g0 - H0 / 2, g1 - g0 - H0, H1 - H0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [quinticHermite, Polynomial.iteratedDeriv_eval] using h1
  · simpa [quinticHermite, Polynomial.iteratedDeriv_eval, Function.iterate_succ_apply'] using h2
  · rw [quinticHermite, h3]
    ring_nf
  · simpa [quinticHermite, Polynomial.iteratedDeriv_eval] using h4
  · simpa [quinticHermite, Polynomial.iteratedDeriv_eval, Function.iterate_succ_apply'] using h5

/-- **Corrected Lemma B.2.1.** Endpoint jets and explicit coefficients are exact for
all data. A positive uniform bound on derivatives of order zero through two exists when
both residuals and the initial jets are bounded. The bound is chosen before all six
endpoint values; the added initial-jet bounds repair the false final claim in the source. -/
theorem lemma_B_2_1_corrected {κ : ℝ} (_hκ : 1 ≤ κ) :
    ∃ K > 0, ∀ f0 g0 H0 f1 g1 H1 : ℝ,
      let r0 := f1 - f0 - g0 - H0 / 2
      let r1 := g1 - g0 - H0
      let r2 := H1 - H0
      let q := quinticHermite f0 g0 H0 f1 g1 H1
      q.natDegree ≤ 5 ∧
      q.eval 0 = f0 ∧ iteratedDeriv 1 (fun z => q.eval z) 0 = g0 ∧
      iteratedDeriv 2 (fun z => q.eval z) 0 = H0 ∧
      q.eval 1 = f1 ∧ iteratedDeriv 1 (fun z => q.eval z) 1 = g1 ∧
      iteratedDeriv 2 (fun z => q.eval z) 1 = H1 ∧
      (∀ j : Fin 6, q.coeff j =
        ![f0,g0,H0/2,10*r0-4*r1+r2/2,-15*r0+7*r1-r2,6*r0-3*r1+r2/2] j) ∧
      (|f0| ≤ κ → |g0| ≤ κ → |H0| ≤ κ →
        |r0| ≤ κ → |r1| ≤ κ → |r2| ≤ κ →
        ∀ j ≤ 2, ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv j (fun z => q.eval z) t| ≤ K) := by
  obtain ⟨K,hK,hbound⟩ := Hermite.quinticFromResiduals_uniform_bound κ
  refine ⟨K,hK,?_⟩
  intro f0 g0 H0 f1 g1 H1
  dsimp only
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := quinticHermite_endpoints f0 g0 H0 f1 g1 H1
  refine ⟨Hermite.quinticFromResiduals_natDegree_le _,h0,h1,h2,h3,h4,h5,?_,?_⟩
  · intro j
    exact Hermite.quinticFromResiduals_coeff _ j
  · intro hf0 hg0 hH0 hr0 hr1 hr2
    apply hbound
    intro j
    fin_cases j <;> assumption
end CartisGouldToint
namespace CartisGouldToint
/-- Equal constant endpoint data give the constant polynomial, regardless of its size. -/
@[simp] theorem quinticHermite_constant (M : ℝ) : quinticHermite M 0 0 M 0 0 = C M := by
  simp [quinticHermite, Hermite.quinticFromResiduals]

/-- The residual-only uniform bound printed in Lemma B.2.1 fails already at the
zeroth derivative and the left endpoint. Constant polynomials give a counterexample. -/
theorem quinticHermite_residual_only_bound_false {κ : ℝ} (hκ : 0 ≤ κ) :
    ¬∃ K : ℝ, ∀ f0 g0 H0 f1 g1 H1 : ℝ,
      |f1 - f0 - g0 - H0 / 2| ≤ κ → |g1 - g0 - H0| ≤ κ → |H1 - H0| ≤ κ →
      |(quinticHermite f0 g0 H0 f1 g1 H1).eval 0| ≤ K := by
  rintro ⟨K,hK⟩
  have h := hK (|K| + 1) 0 0 (|K| + 1) 0 0
    (by simpa using hκ) (by simpa using hκ) (by simpa using hκ)
  simp only [quinticHermite_constant, eval_C] at h
  rw [abs_of_pos (by positivity : 0 < |K| + 1)] at h
  linarith [le_abs_self K]


/-- Primitive data for the Appendix B.2 construction, using the book's global
integer-floor convention for the inverse-square horizon. The actual smooth curves
and corridor objective are constructed from these primitive data. -/
noncomputable def sdexCounterexampleData (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ExactSteepestDescent.Corridor.Parameters :=
  ExactSteepestDescent.Corridor.Parameters.ofAccuracy ε hε hε1

/-- The actual Euclidean objective (B.2.24), with the genuine piecewise quintic
corridor and a smooth bounded terminal extension beyond the final source iterate. -/
noncomputable def sdexCounterexample (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ExactSteepestDescent.Corridor.euclideanObjective (sdexCounterexampleData ε hε hε1) z

/-- The actual Appendix B.2 objective is globally twice continuously differentiable. -/
theorem contDiff_sdexCounterexample (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ContDiff ℝ 2 (sdexCounterexample ε hε hε1) := by
  exact ExactSteepestDescent.Corridor.contDiff_euclideanObjective _

/-- Lemma B.2.4: the actual source corridor objective is uniformly bounded below
on the whole Euclidean plane. The lower bound is chosen before the accuracy,
including the left linear continuation and the bounded smooth right extension. -/
theorem lemma_B_2_4 : ∃ B > 0, ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
    ∀ z : EuclideanSpace ℝ (Fin 2), -B ≤ sdexCounterexample ε hε hε1 z := by
  obtain ⟨B,hB,H⟩ := ExactSteepestDescent.Corridor.objective_bounded_below
  exact ⟨B,hB,fun ε hε hε1 z => H (sdexCounterexampleData ε hε hε1) (z 0, z 1)⟩

/-- The genuine Euclidean corridor term f₂ of (B.2.19)–(B.2.20). -/
noncomputable def sdexCorridor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    EuclideanSpace ℝ (Fin 2) → ℝ :=
  ExactSteepestDescent.Corridor.euclideanResidual (sdexCounterexampleData ε hε hε1)

/-- Lemma B.2.3: the corridor value, both actual first partial derivatives and
all four second partial entries are uniformly bounded. The global bound proved
here includes both closed connector strips in the source, including every join. -/
theorem lemma_B_2_3 : ∃ B > 0, ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
    ∀ z : EuclideanSpace ℝ (Fin 2),
      |sdexCorridor ε hε hε1 z| ≤ B ∧
      (∀ i : Fin 2, |fderiv ℝ (sdexCorridor ε hε hε1) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ B) ∧
      ∀ i j : Fin 2, |iteratedFDeriv ℝ 2 (sdexCorridor ε hε hε1) z
        ![EuclideanSpace.basisFun (Fin 2) ℝ i, EuclideanSpace.basisFun (Fin 2) ℝ j]| ≤ B := by
  obtain ⟨B,hB,H⟩ := ExactSteepestDescent.Corridor.euclideanResidual_partials_bounded
  exact ⟨B,hB,fun ε hε hε1 => H (sdexCounterexampleData ε hε hε1)⟩

/-- Lemma B.2.5: the actual source objective has a globally Lipschitz Euclidean
gradient, with a common positive constant preceding the requested accuracy. -/
theorem lemma_B_2_5 : ∃ L > 0, ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
    ∀ x y : EuclideanSpace ℝ (Fin 2),
      ‖gradient (sdexCounterexample ε hε hε1) x -
        gradient (sdexCounterexample ε hε hε1) y‖ ≤ L * ‖x-y‖ := by
  obtain ⟨L,hL,H⟩ := ExactSteepestDescent.Corridor.euclideanObjective_gradient_lipschitz
  exact ⟨L,hL,fun ε hε hε1 => H (sdexCounterexampleData ε hε hε1)⟩

end CartisGouldToint
