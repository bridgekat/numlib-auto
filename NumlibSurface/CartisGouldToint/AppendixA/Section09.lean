import Numlib.Analysis.Calculus.FiniteHermiteInterpolation

/-!
# Uniform Hermite interpolation

The constants depend only on interpolation order and the compatibility bound, independently
of spacing and endpoint jets. Finite compatible jets extend to the whole real line.
-/
namespace CartisGouldToint.AppendixA.Section09
open Polynomial
open scoped NNReal

/-- Theorem A.9.1: endpoint-compatible Hermite interpolation with uniform highest-derivative
Lipschitz and conditional lower-derivative bounds. -/
theorem theorem_A_9_1 (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L B : ℝ≥0, ∀ (s : ℝ) (a b : ℕ → ℝ), 0 < s →
      (∀ j ≤ p, |b j - (derivative^[j] (Hermite.endpointTaylor p a)).eval s| ≤
        κ * s ^ (p + 1 - j)) →
      ∃ P : ℝ[X], P.natDegree ≤ 2 * p + 1 ∧
        (∀ j ≤ p, iteratedDeriv j (fun x => P.eval x) 0 = a j ∧
          iteratedDeriv j (fun x => P.eval x) s = b j) ∧
        LipschitzOnWith L (iteratedDeriv p (fun x => P.eval x)) (Set.Icc 0 s) ∧
        ((∀ j ≤ p, |a j| ≤ κ) → s ≤ κ → ∀ j ≤ p, ∀ x ∈ Set.Icc (0 : ℝ) s,
          |iteratedDeriv j (fun x => P.eval x) x| ≤ B) :=
  Hermite.interval_hermite_derivative_bounds p κ hκ

/-- Finite real knots `x 0, …, x N` and derivative data through order `p` satisfying (A.32).
Only the indicated finite ranges of the two data functions are used. In particular no knot
`x (N + 1)` is required. -/
structure CompatibleFiniteJetData (p N : ℕ) (κ : ℝ) where
  /-- The real interpolation knots, restricted to indices at most `N`. -/
  x : ℕ → ℝ
  /-- The prescribed derivatives, restricted to knot indices at most `N` and orders at most `p`. -/
  jet : ℕ → ℕ → ℝ
  /-- Successive knots are strictly increasing. -/
  increasing : ∀ i < N, x i < x (i + 1)
  /-- The successive Taylor discrepancies obey (A.32). -/
  compatible : ∀ i < N, ∀ j ≤ p,
    |jet (i + 1) j -
      (derivative^[j] (Hermite.endpointTaylor p (jet i))).eval (x (i + 1) - x i)| ≤
      κ * (x (i + 1) - x i) ^ (p + 1 - j)

/-- Theorem A.9.2: general finite Hermite interpolation. The constants are chosen before
all finite data. Under the additional bounds on initial jets and spacings, every derivative
through order `p` is bounded on the whole real line. -/
theorem theorem_A_9_2 (p : ℕ) (_hp : 0 < p) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L B : ℝ≥0, ∀ (N : ℕ), 0 < N → ∀ D : CompatibleFiniteJetData p N κ,
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
        (∀ i ≤ N, ∀ j ≤ p, iteratedDeriv j f (D.x i) = D.jet i j) ∧
        ((∀ i < N, ∀ j ≤ p, |D.jet i j| ≤ κ) →
          (∀ i < N, D.x (i + 1) - D.x i ≤ κ) →
          ∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B) := by
  obtain ⟨L, B, h⟩ := Hermite.exists_contDiff_lipschitz_iteratedDeriv_of_finite_jets p κ hκ
  exact ⟨L, B, fun N hN D => h N hN D.x D.jet D.increasing D.compatible⟩

end CartisGouldToint.AppendixA.Section09
