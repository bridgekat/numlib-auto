import Numlib.Analysis.Calculus.FiniteHermiteInterpolation

/-!
# Uniformly bounded interpolation at unit knots

A fixed bound on scalar jets at integer knots gives global interpolation and boundedness
constants independent of the number of knots.
-/

noncomputable section
open scoped NNReal
namespace Hermite

/-- Uniformly bounded jets at integer knots admit bounded smooth interpolation with uniform
constants independent of the number of knots. -/
theorem exists_contDiff_bounded_of_unit_knots (p : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ L B : ℝ≥0, ∀ N : ℕ, 0 < N → ∀ a : ℕ → ℕ → ℝ,
      (∀ i ≤ N, ∀ j ≤ p, |a i j| ≤ A) →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
        (∀ i ≤ N, ∀ j ≤ p, iteratedDeriv j f (i : ℝ) = a i j) ∧
        (∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B) := by
  obtain ⟨C, hC, hbound⟩ := exists_endpointTaylor_unit_bound p
  let κ := A + A * C + 1
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hAκ : A ≤ κ := by dsimp [κ]; nlinarith
  have h1κ : 1 ≤ κ := by dsimp [κ]; nlinarith
  obtain ⟨L, B, hinterp⟩ :=
    exists_contDiff_lipschitz_iteratedDeriv_of_finite_jets p κ hκ
  refine ⟨L, B, ?_⟩
  intro N hN a ha
  obtain ⟨f, hf, hLip, hjet, hb⟩ := hinterp N hN (fun i => (i : ℝ)) a
    (by intro i _; exact_mod_cast Nat.lt_succ_self i)
    (by
      intro i hi j hj
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_pow, mul_one]
      exact (abs_sub _ _).trans ((add_le_add (ha (i + 1) (by omega) j hj)
        (hbound (a i) A hA (ha i (by omega)) j hj)).trans (by dsimp [κ]; linarith)))
  refine ⟨f, hf, hLip, hjet, hb (fun i hi j hj => (ha i hi.le j hj).trans hAκ) ?_⟩
  intro i _
  simpa using h1κ

end Hermite
