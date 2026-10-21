import NumlibSurface.CartisGouldToint.Chapter11.Section01.SignedDefinite
import NumlibSurface.CartisGouldToint.Chapter11.Section01.SignedRegularization

/-!
# Complete signed diagonal classifications of Section 11.1.3

The two classifications include the all-positive case and the easy/hard alternatives whenever
a negative direction exists. Companion theorems provide actual attainment, uniqueness in the
easy case, unique secular roots, all-negative arbitrary directions and hard completion existence.
The regularization target and the hard-case subtraction correct the supplied transcription.
-/

open Matrix

namespace CartisGouldToint.Chapter11.Section01

variable {n : ℕ} (p : Fin n → Bool) {g s : EuclideanSpace ℝ (Fin n)}

/-- Section 11.1.3: full signed trust-region classification. The positive branch includes its
interior/boundary equality edge. With any negative direction, the explicit easy secular step or
the complete hard affine sphere gives exactly all global minimizers. Empty sign spaces and zero
gradients are retained; unique-root and arbitrary-direction clauses are companion theorems. -/
theorem signedDiagonalSubproblem {Δ : ℝ} (hΔ : 0 < Δ) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s ↔
      if ∀ i, p i = true then s = if ‖g‖ ≤ Δ then -g else (-Δ / ‖g‖) • g
      else
        (∃ lambda : ℝ, 1 < lambda ∧ s = signedDiagonalStep p g lambda ∧
          ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
            ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 = Δ ^ 2) ∨
        (signComponent p false g = 0 ∧ ∃ z : EuclideanSpace ℝ (Fin n),
          s = signedDiagonalHardStep p g z ∧
            ‖signComponent p false z‖ ^ 2 = Δ ^ 2 - ‖signComponent p true g‖ ^ 2 / 4) := by
  classical
  by_cases hpos : ∀ i, p i = true
  · rw [ite_eq_left hpos]
    have hp : p = fun _ => true := funext hpos
    subst p
    exact positiveDiagonalTrustRegion_iff hΔ
  · rw [ite_eq_right hpos]
    have hneg : ∃ i, p i = false := by
      obtain ⟨i, hi⟩ := not_forall.mp hpos
      cases he : p i
      · exact ⟨i, he⟩
      · exact (hi he).elim
    exact signedTrustRegion_cases_iff p hΔ hneg

/-- Section 11.1.3: full signed regularization classification for `r > 2`, `sigma > 0`.
The corrected norm target is `(lambda / sigma) ^ (2 / (r - 2))`. At shift `1`, the negative norm
squared subtracts the fixed positive contribution. The hard-family threshold and completion
existence are supplied by `signedRegularization_hard_iff` and `exists_signedRegularization_hard`. -/
theorem signedDiagonalRegularization {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) :
    Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s ↔
      if ∀ i, p i = true then
        ∃ lambda : ℝ, 0 ≤ lambda ∧ s = (-(lambda + 1)⁻¹) • g ∧
          lambda = σ * (‖g‖ / (lambda + 1)) ^ (r - 2)
      else
        (∃ lambda : ℝ, 1 < lambda ∧ s = signedDiagonalStep p g lambda ∧
          ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
            ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 =
              (lambda / σ) ^ (2 / (r - 2))) ∨
        (signComponent p false g = 0 ∧ ∃ z : EuclideanSpace ℝ (Fin n),
          s = signedDiagonalHardStep p g z ∧
            ‖signComponent p false z‖ ^ 2 =
              σ ^ (-2 / (r - 2)) - ‖signComponent p true g‖ ^ 2 / 4) := by
  classical
  by_cases hpos : ∀ i, p i = true
  · rw [ite_eq_left hpos]
    have hp : p = fun _ => true := funext hpos
    subst p
    exact positiveDiagonalRegularization_iff hσ hr
  · rw [ite_eq_right hpos]
    have hneg : ∃ i, p i = false := by
      obtain ⟨i, hi⟩ := not_forall.mp hpos
      cases he : p i
      · exact ⟨i, he⟩
      · exact (hi he).elim
    rw [← Optimization.QuadraticSubproblem.inverse_radial_target_eq σ 2 r]
    exact signedRegularization_cases_iff p hσ hr hneg

end CartisGouldToint.Chapter11.Section01
