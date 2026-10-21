import NumlibSurface.CartisGouldToint.Chapter11.Section01.SignedDiagonal

/-!
# Definite special cases of Section 11.1.3

The positive diagonal case includes both the feasible unconstrained minimizer and the radial
boundary solution. The negative diagonal case includes the entire sphere when the gradient is zero.
-/

open Matrix
open scoped ComplexOrder

namespace CartisGouldToint.Chapter11.Section01

variable {n : ℕ} {g s : EuclideanSpace ℝ (Fin n)}

/-- For an all-positive diagonal, a feasible unconstrained solution is the unique minimizer. -/
theorem positiveDiagonalTrustRegion_interior {Δ : ℝ} (hΔ : 0 < Δ) (hg : ‖g‖ ≤ Δ) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal (fun _ : Fin n => true)) 1 Δ (-g) ∧
      ∀ s, Chapter08.Section01.trustRegionMinimizer g
        (signedDiagonal (fun _ : Fin n => true)) 1 Δ s → s = -g := by
  have hstat : toEuclideanLin (signedDiagonal (fun _ : Fin n => true) +
      (0 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) (-g) = -g := by
    rw [signedDiagonal_stationary_coordinates]
    intro i
    simp
  have hp : (signedDiagonal (fun _ : Fin n => true) +
      (0 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    rw [signedDiagonal_shift, posDef_diagonal_iff]
    norm_num
  have hm := (Chapter08.Section02.theorem_8_2_7
    (signedDiagonal_isSymm (fun _ : Fin n => true)) Matrix.PosDef.one hΔ).1.mpr
    ⟨by simpa [weightedNorm_one] using hg, 0, le_refl 0, hstat, hp.posSemidef, by simp⟩
  exact ⟨hm, (Chapter08.Section02.theorem_8_2_7
    (signedDiagonal_isSymm (fun _ : Fin n => true)) Matrix.PosDef.one hΔ).2
    0 hm (le_refl 0) hstat hp (by simp)⟩

/-- For either constant sign, the radial boundary solution is unique when its shift is positive.
The positive sign requires the unconstrained minimizer to lie outside the ball. -/
theorem constantSignTrustRegion_boundary (b : Bool) {Δ : ℝ} (hΔ : 0 < Δ)
    (hg : 0 < ‖g‖) (hshift : 0 ≤ ‖g‖ / Δ - if b then 1 else -1) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal (fun _ : Fin n => b)) 1 Δ
        ((-Δ / ‖g‖) • g) ∧
      ∀ s, Chapter08.Section01.trustRegionMinimizer g
        (signedDiagonal (fun _ : Fin n => b)) 1 Δ s → s = (-Δ / ‖g‖) • g := by
  let lambda := ‖g‖ / Δ - if b then 1 else -1
  have hn : ‖(-Δ / ‖g‖) • g‖ = Δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hΔ, abs_of_pos hg,
      div_mul_cancel₀ _ hg.ne']
  have hstat : toEuclideanLin (signedDiagonal (fun _ : Fin n => b) +
      lambda • (1 : Matrix (Fin n) (Fin n) ℝ)) ((-Δ / ‖g‖) • g) = -g := by
    rw [signedDiagonal_stationary_coordinates]
    intro i
    change (lambda + if b then 1 else -1) * ((-Δ / ‖g‖) * g i) = -g i
    dsimp [lambda]
    field_simp
    ring
  have hp : (signedDiagonal (fun _ : Fin n => b) +
      lambda • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    rw [signedDiagonal_shift, posDef_diagonal_iff]
    intro i
    dsimp [lambda]
    simpa using div_pos hg hΔ
  have hc : lambda * (Chapter08.Section01.weightedNorm 1 ((-Δ / ‖g‖) • g) ^ 2 - Δ ^ 2) = 0 := by
    simp [weightedNorm_one, hn]
  have hm := (Chapter08.Section02.theorem_8_2_7
    (signedDiagonal_isSymm (fun _ : Fin n => b)) Matrix.PosDef.one hΔ).1.mpr
    ⟨by simpa only [weightedNorm_one] using hn.le, lambda, hshift, hstat, hp.posSemidef, hc⟩
  exact ⟨hm, (Chapter08.Section02.theorem_8_2_7
    (signedDiagonal_isSymm (fun _ : Fin n => b)) Matrix.PosDef.one hΔ).2
    lambda hm hshift hstat hp hc⟩

/-- The complete all-positive trust-region classification, with equality in the interior branch. -/
theorem positiveDiagonalTrustRegion_iff {Δ : ℝ} (hΔ : 0 < Δ) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal (fun _ : Fin n => true)) 1 Δ s ↔
      s = if ‖g‖ ≤ Δ then -g else (-Δ / ‖g‖) • g := by
  split_ifs with hg
  · exact ⟨fun hs => (positiveDiagonalTrustRegion_interior hΔ hg).2 s hs,
      fun hs => hs ▸ (positiveDiagonalTrustRegion_interior hΔ hg).1⟩
  · have hg' : Δ < ‖g‖ := lt_of_not_ge hg
    have hb := constantSignTrustRegion_boundary true hΔ (lt_trans hΔ hg')
      (sub_nonneg.mpr ((one_le_div hΔ).mpr hg'.le))
    exact ⟨fun hs => hb.2 s hs, fun hs => hs ▸ hb.1⟩

/-- With an all-negative diagonal and nonzero gradient, the negative gradient boundary step
is the unique global minimizer. -/
theorem negativeDiagonalTrustRegion_iff {Δ : ℝ} (hΔ : 0 < Δ) (hg : g ≠ 0) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal (fun _ : Fin n => false)) 1 Δ s ↔
      s = (-Δ / ‖g‖) • g := by
  have hb := constantSignTrustRegion_boundary false hΔ (norm_pos_iff.mpr hg)
    (by change 0 ≤ ‖g‖ / Δ - -1
        have := div_nonneg (norm_nonneg g) hΔ.le
        linarith)
  exact ⟨fun hs => hb.2 s hs, fun hs => hs ▸ hb.1⟩

/-- With an all-negative diagonal and zero gradient, every boundary direction minimizes.
A positive dimension is necessary for boundary necessity. -/
theorem negativeDiagonalTrustRegion_zero_iff {Δ : ℝ} (hΔ : 0 < Δ) (hn : 0 < n) :
    Chapter08.Section01.trustRegionMinimizer 0 (signedDiagonal (fun _ : Fin n => false)) 1 Δ s ↔
      ‖s‖ = Δ := by
  constructor
  · exact signedTrustRegion_boundary _ hΔ ⟨⟨0, hn⟩, rfl⟩
  · intro hs
    apply (signedTrustRegion_iff (fun _ : Fin n => false) hΔ).mpr
    exact ⟨hs.le, 1, zero_le_one, by intro i; norm_num,
      by intro i; norm_num, by rw [hs]; ring⟩

/-- In dimension zero both signed subproblems have the unique available step, including a
zero trust-region radius and every regularization exponent. -/
theorem zeroDimensional_signedSubproblems (p : Fin 0 → Bool)
    (g s : EuclideanSpace ℝ (Fin 0)) {Δ : ℝ} (hΔ : 0 ≤ Δ) (σ r : ℝ) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s ∧
      Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s := by
  have hs : s = 0 := Subsingleton.elim _ _
  constructor
  · refine ⟨by simpa only [weightedNorm_one, hs, norm_zero] using hΔ, ?_⟩
    intro y _
    change Chapter08.Section01.quadraticModel g (signedDiagonal p) s ≤
      Chapter08.Section01.quadraticModel g (signedDiagonal p) y
    have he : y = s := Subsingleton.elim _ _
    rw [he]
  · intro y _
    change Chapter08.Section01.regularizedModel g (signedDiagonal p) 1 σ r s ≤
      Chapter08.Section01.regularizedModel g (signedDiagonal p) 1 σ r y
    have he : y = s := Subsingleton.elim _ _
    rw [he]

end CartisGouldToint.Chapter11.Section01
