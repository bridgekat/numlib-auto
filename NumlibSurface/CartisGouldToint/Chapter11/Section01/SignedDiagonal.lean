import NumlibSurface.CartisGouldToint.Chapter11.Section01
import Numlib.LinearAlgebra.Matrix.SignedDiagonal
import Numlib.Optimization.QuadraticBallExistence
import Numlib.Optimization.RadialPowerTarget

/-!
# Signed diagonal subproblems in Section 11.1.3

These statements concern the actual diagonal Hessian with entries `±1`. They use the source
optimality theorems of Section 8.2, retaining the singular shift and zero-dimensional sign spaces.
The regularization radius uses `(lambda / sigma) ^ (2 / (r - 2))` for its squared norm.
-/

open Matrix
open scoped ComplexOrder

namespace CartisGouldToint.Chapter11.Section01

variable {n : ℕ} (p : Fin n → Bool) {g s : EuclideanSpace ℝ (Fin n)}

/-- The complete source trust-region optimality conditions specialized to a signed diagonal. -/
theorem signedTrustRegion_iff {Δ : ℝ} (hΔ : 0 < Δ) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s ↔
      ‖s‖ ≤ Δ ∧ ∃ lambda : ℝ, 0 ≤ lambda ∧
        (∀ i, (lambda + if p i then 1 else -1) * s i = -g i) ∧
        (∀ i, 0 ≤ lambda + if p i then 1 else -1) ∧
        lambda * (‖s‖ ^ 2 - Δ ^ 2) = 0 := by
  rw [(Chapter08.Section02.theorem_8_2_7 (signedDiagonal_isSymm p) Matrix.PosDef.one hΔ).1]
  simp only [weightedNorm_one, signedDiagonal_shift_posSemidef_iff,
    signedDiagonal_stationary_coordinates]

/-- A negative sign forces every trust-region minimizer onto the boundary, including `g = 0`. -/
theorem signedTrustRegion_boundary {Δ : ℝ} (hΔ : 0 < Δ) (hneg : ∃ i, p i = false)
    (hs : Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s) : ‖s‖ = Δ := by
  obtain ⟨hfeas, lambda, hlambda, _, hp, hc⟩ := (signedTrustRegion_iff p hΔ).mp hs
  obtain ⟨i, hi⟩ := hneg
  have he := hp i
  simp [hi] at he
  have hsq : ‖s‖ ^ 2 = Δ ^ 2 := by nlinarith
  nlinarith [norm_nonneg s]

/-- Above the negative eigenvalue pole, the boundary secular equation gives an actual minimizer. -/
theorem signedTrustRegion_easy {Δ lambda : ℝ} (hΔ : 0 < Δ) (hlambda : 1 < lambda)
    (hroot : ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
      ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 = Δ ^ 2) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ
      (signedDiagonalStep p g lambda) := by
  have hnorm : ‖signedDiagonalStep p g lambda‖ = Δ := by
    have he := norm_sq_signedDiagonalStep p g lambda
    nlinarith [norm_nonneg (signedDiagonalStep p g lambda)]
  apply (Chapter08.Section02.theorem_8_2_7 (signedDiagonal_isSymm p)
    Matrix.PosDef.one hΔ).1.mpr
  refine ⟨by simpa only [weightedNorm_one] using hnorm.le,
    lambda, by linarith, signedDiagonalStep_stationary p g (by linarith) (by linarith),
    (signedDiagonal_shift_posDef p hlambda).posSemidef, ?_⟩
  simp [weightedNorm_one, hnorm]

/-- Every easy signed trust-region solution is the unique global minimizer. -/
theorem signedTrustRegion_easy_unique {Δ lambda : ℝ} (hΔ : 0 < Δ) (hlambda : 1 < lambda)
    (hroot : ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
      ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 = Δ ^ 2)
    (hs : Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s) :
    s = signedDiagonalStep p g lambda := by
  have hm := signedTrustRegion_easy p hΔ hlambda hroot
  apply (Chapter08.Section02.theorem_8_2_7 (signedDiagonal_isSymm p)
    Matrix.PosDef.one hΔ).2 lambda hm (by linarith)
    (signedDiagonalStep_stationary p g (by linarith) (by linarith))
    (signedDiagonal_shift_posDef p hlambda) _ s hs
  have he := norm_sq_signedDiagonalStep p g lambda
  simp only [weightedNorm_one]
  rw [he, hroot, sub_self, mul_zero]

/-- Every hard step with the prescribed negative squared norm is a global trust-region minimizer.
The equality threshold is included, and the negative sign space may be zero-dimensional. -/
theorem signedTrustRegion_hard (hg : signComponent p false g = 0)
    {Δ : ℝ} (hΔ : 0 < Δ) (z : EuclideanSpace ℝ (Fin n))
    (hz : ‖signComponent p false z‖ ^ 2 = Δ ^ 2 - ‖signComponent p true g‖ ^ 2 / 4) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ
      (signedDiagonalHardStep p g z) := by
  have he := norm_sq_signedDiagonalHardStep p g z
  have hn : ‖signedDiagonalHardStep p g z‖ = Δ := by
    nlinarith [norm_nonneg (signedDiagonalHardStep p g z)]
  apply (Chapter08.Section02.theorem_8_2_7 (signedDiagonal_isSymm p)
    Matrix.PosDef.one hΔ).1.mpr
  refine ⟨by simpa only [weightedNorm_one] using hn.le, 1, zero_le_one,
    (signedDiagonalHardStep_stationary_iff p g z).mpr hg,
    signedDiagonal_shift_one_posSemidef p, ?_⟩
  simp [weightedNorm_one, hn]

/-- At multiplier `1`, the corrected hard-case norm formula is necessary and sufficient. -/
theorem signedTrustRegion_hard_norm_iff {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖signedDiagonalHardStep p g z‖ = Δ ↔
      ‖signComponent p false z‖ ^ 2 = Δ ^ 2 - ‖signComponent p true g‖ ^ 2 / 4 := by
  have he := norm_sq_signedDiagonalHardStep p g z
  constructor <;> intro hh <;> nlinarith [norm_nonneg (signedDiagonalHardStep p g z)]

/-- The complete source regularization optimality conditions for the actual signed matrix. -/
theorem signedRegularization_iff {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) :
    Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s ↔
      ∃ lambda : ℝ, lambda = σ * ‖s‖ ^ (r - 2) ∧
        (∀ i, (lambda + if p i then 1 else -1) * s i = -g i) ∧
        (∀ i, 0 ≤ lambda + if p i then 1 else -1) := by
  rw [(Chapter08.Section02.theorem_8_2_8 (signedDiagonal_isSymm p)
    Matrix.PosDef.one hσ hr).1]
  simp only [weightedNorm_one, signedDiagonal_shift_posSemidef_iff,
    signedDiagonal_stationary_coordinates]

/-- Signed trust-region subproblems always possess a global minimizer. -/
theorem exists_signedTrustRegion (g : EuclideanSpace ℝ (Fin n)) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ s, Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s := by
  obtain ⟨s, hs, hm⟩ := Optimization.QuadraticSubproblem.exists_isMinOn_ball_quadratic
    g (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (signedDiagonal p)) hΔ
  refine ⟨s, ?_⟩
  simpa only [Chapter08.Section01.trustRegionMinimizer, weightedNorm_one,
    Chapter08.Section01.quadraticModel_eq_quadratic] using And.intro hs hm

/-- A nonzero negative gradient implies that the negative sign space is nonempty. -/
theorem exists_negative_of_signComponent_ne_zero (hg : signComponent p false g ≠ 0) :
    ∃ i, p i = false := by
  by_contra h
  apply hg
  ext i
  have hi : p i ≠ false := fun hi => h ⟨i, hi⟩
  simp [hi]

/-- For a nonzero negative gradient the actual minimizer has a multiplier strictly above `1`. -/
theorem signedTrustRegion_easy_necessary {Δ : ℝ} (hΔ : 0 < Δ)
    (hg : signComponent p false g ≠ 0)
    (hs : Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s) :
    ∃ lambda : ℝ, 1 < lambda ∧ s = signedDiagonalStep p g lambda ∧
      ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
        ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 = Δ ^ 2 := by
  obtain ⟨hf, lambda, hl, hstat, hp, hc⟩ :=
    (Chapter08.Section02.theorem_8_2_7 (signedDiagonal_isSymm p)
      Matrix.PosDef.one hΔ).1.mp hs
  obtain ⟨i, hi⟩ := exists_negative_of_signComponent_ne_zero p hg
  have hb := (signedDiagonal_shift_posSemidef_iff p lambda).mp hp i
  simp only [hi, Bool.false_eq_true, ite_false] at hb
  have hne : lambda ≠ 1 := by
    intro he
    rw [he] at hstat
    exact hg ((signedDiagonal_stationary_one_iff p g s).mp hstat).1
  have hlambda : 1 < lambda := lt_of_le_of_ne (by linarith) (Ne.symm hne)
  have heq := (signedDiagonal_stationary_iff p g s (by linarith) (by linarith)).mp hstat
  refine ⟨lambda, hlambda, heq, ?_⟩
  have hn := signedTrustRegion_boundary p hΔ ⟨i, hi⟩ hs
  rw [← norm_sq_signedDiagonalStep, ← heq, hn]

/-- With nonzero negative gradient the secular equation has exactly one root above `1`.
This includes existence, rather than assuming a supplied root certificate. -/
theorem existsUnique_signedTrustRegion_root {Δ : ℝ} (hΔ : 0 < Δ)
    (hg : signComponent p false g ≠ 0) :
    ∃! lambda : ℝ, 1 < lambda ∧
      ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
        ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 = Δ ^ 2 := by
  obtain ⟨s, hs⟩ := exists_signedTrustRegion p g hΔ.le
  obtain ⟨lambda, hl, heq, hroot⟩ := signedTrustRegion_easy_necessary p hΔ hg hs
  refine ⟨lambda, ⟨hl, hroot⟩, ?_⟩
  rintro mu ⟨hmu, hmuroot⟩
  have he := signedTrustRegion_easy_unique p hΔ hl hroot
    (signedTrustRegion_easy p hΔ hmu hmuroot)
  have hstatl := signedDiagonalStep_stationary p g (by linarith : lambda + 1 ≠ 0)
    (by linarith : lambda - 1 ≠ 0)
  have hstatm := signedDiagonalStep_stationary p g (by linarith : mu + 1 ≠ 0)
    (by linarith : mu - 1 ≠ 0)
  rw [he] at hstatm
  have hn : signedDiagonalStep p g lambda ≠ 0 := by
    intro hz
    have hb := signedTrustRegion_boundary p hΔ
      (exists_negative_of_signComponent_ne_zero p hg) (signedTrustRegion_easy p hΔ hl hroot)
    simp [hz] at hb
    linarith
  have hcoord : ∃ i, signedDiagonalStep p g lambda i ≠ 0 := by
    by_contra hh
    apply hn
    ext i
    simpa using not_not.mp (fun hi => hh ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hcoord
  have hli := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) hstatl
  have hmi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) hstatm
  rw [signedDiagonal_shift_apply] at hli hmi
  have heprod : (mu - lambda) * signedDiagonalStep p g lambda i = 0 := by
    linear_combination hmi - hli
  exact sub_eq_zero.mp ((mul_eq_zero.mp heprod).resolve_right hi)

/-- When the negative gradient vanishes and the positive part fits at shift `1`, the hard
family gives exactly all minimizers. The non-strict threshold includes the equality case. -/
theorem signedTrustRegion_hard_iff {Δ : ℝ} (hΔ : 0 < Δ)
    (hneg : ∃ i, p i = false) (hg : signComponent p false g = 0)
    (hsmall : ‖signComponent p true g‖ ≤ 2 * Δ) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s ↔
      ∃ z : EuclideanSpace ℝ (Fin n), s = signedDiagonalHardStep p g z ∧
        ‖signComponent p false z‖ ^ 2 = Δ ^ 2 - ‖signComponent p true g‖ ^ 2 / 4 := by
  constructor
  · intro hs
    obtain ⟨hf, lambda, hl, hstat, hp, hc⟩ :=
      (Chapter08.Section02.theorem_8_2_7 (signedDiagonal_isSymm p)
        Matrix.PosDef.one hΔ).1.mp hs
    obtain ⟨i, hi⟩ := hneg
    have hb := (signedDiagonal_shift_posSemidef_iff p lambda).mp hp i
    simp only [hi, Bool.false_eq_true, ite_false] at hb
    have hn := signedTrustRegion_boundary p hΔ ⟨i, hi⟩ hs
    have he : lambda = 1 := by
      by_contra hne
      have hlarge : 1 < lambda := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      have heq := (signedDiagonal_stationary_iff p g s (by linarith) (by linarith)).mp hstat
      have hnorm := norm_sq_signedDiagonalStep p g lambda
      rw [hg, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero, ← heq, hn] at hnorm
      have hprod := (div_eq_iff (pow_ne_zero 2 (by linarith : lambda + 1 ≠ 0))).mp hnorm.symm
      have hstrict : 0 < Δ ^ 2 * ((lambda + 1) ^ 2 - 4) :=
        mul_pos (sq_pos_of_pos hΔ) (by nlinarith)
      nlinarith [norm_nonneg (signComponent p true g)]
    rw [he] at hstat
    have hsplus := ((signedDiagonal_stationary_one_iff p g s).mp hstat).2
    have hsform : s = signedDiagonalHardStep p g s := by
      rw [signedDiagonalHardStep, ← hsplus, signComponent_add]
    refine ⟨s, hsform, ?_⟩
    exact (signedTrustRegion_hard_norm_iff p hΔ.le s).mp (by rw [← hsform, hn])
  · rintro ⟨z, rfl, hz⟩
    exact signedTrustRegion_hard p hg hΔ z hz

/-- Every signed power-regularized subproblem has a global minimizer. -/
theorem exists_signedRegularization (g : EuclideanSpace ℝ (Fin n)) {σ r : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) :
    ∃ s, Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s := by
  obtain ⟨s, hs⟩ := Optimization.QuadraticSubproblem.exists_isMinOn_powerRegularizedQuadratic
    g (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (signedDiagonal p)) hσ hr
  refine ⟨s, ?_⟩
  change IsMinOn (Chapter08.Section01.regularizedModel g (signedDiagonal p) 1 σ r) Set.univ s
  have he : Chapter08.Section01.regularizedModel g (signedDiagonal p) 1 σ r =
      Optimization.QuadraticSubproblem.powerRegularizedQuadratic g
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (signedDiagonal p)) σ r := by
    ext x
    simp only [Chapter08.Section01.regularizedModel, weightedNorm_one,
      Chapter08.Section01.quadraticModel_eq_quadratic,
      Optimization.QuadraticSubproblem.powerRegularizedQuadratic]
  rw [he]
  exact hs

/-- Above the pole, the corrected squared secular equation gives a global regularized minimizer. -/
theorem signedRegularization_easy {σ r lambda : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hlambda : 1 < lambda)
    (hroot : ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
      ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 =
        (lambda / σ) ^ (2 / (r - 2))) :
    Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r
      (signedDiagonalStep p g lambda) := by
  apply (Chapter08.Section02.theorem_8_2_8 (signedDiagonal_isSymm p)
    Matrix.PosDef.one hσ hr).1.mpr
  refine ⟨lambda, ?_, signedDiagonalStep_stationary p g (by linarith) (by linarith),
    (signedDiagonal_shift_posDef p hlambda).posSemidef⟩
  simp only [weightedNorm_one]
  apply (Optimization.QuadraticSubproblem.radialShift_iff_sq_radius
    (norm_nonneg _) (by linarith) hσ (by linarith : r - 2 ≠ 0)).mpr
  rw [norm_sq_signedDiagonalStep, hroot]

/-- At multiplier `1`, the corrected hard-step norm formula gives global regularized minimizers.
The negative squared norm subtracts the positive contribution, including the equality threshold. -/
theorem signedRegularization_hard {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hg : signComponent p false g = 0) (z : EuclideanSpace ℝ (Fin n))
    (hz : ‖signComponent p false z‖ ^ 2 =
      (1 / σ) ^ (2 / (r - 2)) - ‖signComponent p true g‖ ^ 2 / 4) :
    Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r
      (signedDiagonalHardStep p g z) := by
  apply (Chapter08.Section02.theorem_8_2_8 (signedDiagonal_isSymm p)
    Matrix.PosDef.one hσ hr).1.mpr
  refine ⟨1, ?_, (signedDiagonalHardStep_stationary_iff p g z).mpr hg,
    signedDiagonal_shift_one_posSemidef p⟩
  simp only [weightedNorm_one]
  apply (Optimization.QuadraticSubproblem.radialShift_iff_sq_radius
    (norm_nonneg _) zero_le_one hσ (by linarith : r - 2 ≠ 0)).mpr
  rw [norm_sq_signedDiagonalHardStep, hz]
  ring

/-- With a negative eigendirection, every trust-region minimizer is either the nonsingular
secular solution or a singular hard solution, and both alternatives are sufficient. -/
theorem signedTrustRegion_cases_iff {Δ : ℝ} (hΔ : 0 < Δ) (hneg : ∃ i, p i = false) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s ↔
      (∃ lambda : ℝ, 1 < lambda ∧ s = signedDiagonalStep p g lambda ∧
        ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
          ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 = Δ ^ 2) ∨
      (signComponent p false g = 0 ∧ ∃ z : EuclideanSpace ℝ (Fin n),
        s = signedDiagonalHardStep p g z ∧
          ‖signComponent p false z‖ ^ 2 = Δ ^ 2 - ‖signComponent p true g‖ ^ 2 / 4) := by
  constructor
  · intro hs
    obtain ⟨hf, lambda, hl, hstat, hp, hc⟩ :=
      (Chapter08.Section02.theorem_8_2_7 (signedDiagonal_isSymm p)
        Matrix.PosDef.one hΔ).1.mp hs
    obtain ⟨i, hi⟩ := hneg
    have hb := (signedDiagonal_shift_posSemidef_iff p lambda).mp hp i
    simp only [hi, Bool.false_eq_true, ite_false] at hb
    have hn := signedTrustRegion_boundary p hΔ ⟨i, hi⟩ hs
    by_cases he : lambda = 1
    · right
      rw [he] at hstat
      obtain ⟨hg, hsplus⟩ := (signedDiagonal_stationary_one_iff p g s).mp hstat
      have hsform : s = signedDiagonalHardStep p g s := by
        rw [signedDiagonalHardStep, ← hsplus, signComponent_add]
      refine ⟨hg, s, hsform, ?_⟩
      exact (signedTrustRegion_hard_norm_iff p hΔ.le s).mp (by rw [← hsform, hn])
    · left
      have hlambda : 1 < lambda := lt_of_le_of_ne (by linarith) (Ne.symm he)
      have heq := (signedDiagonal_stationary_iff p g s (by linarith) (by linarith)).mp hstat
      refine ⟨lambda, hlambda, heq, ?_⟩
      rw [← norm_sq_signedDiagonalStep, ← heq, hn]
  · rintro (⟨lambda, hl, rfl, hroot⟩ | ⟨hg, z, rfl, hz⟩)
    · exact signedTrustRegion_easy p hΔ hl hroot
    · exact signedTrustRegion_hard p hg hΔ z hz

/-- Below the hard-case threshold, the full negative-component norm constraint has a solution.
This follows from actual attainment, including equality and zero gradient. -/
theorem exists_signedTrustRegion_hard {Δ : ℝ} (hΔ : 0 < Δ)
    (hneg : ∃ i, p i = false) (hg : signComponent p false g = 0)
    (hsmall : ‖signComponent p true g‖ ≤ 2 * Δ) :
    ∃ z : EuclideanSpace ℝ (Fin n),
      ‖signComponent p false z‖ ^ 2 = Δ ^ 2 - ‖signComponent p true g‖ ^ 2 / 4 ∧
        Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ
          (signedDiagonalHardStep p g z) := by
  obtain ⟨s, hs⟩ := exists_signedTrustRegion p g hΔ.le
  obtain ⟨z, rfl, hz⟩ := (signedTrustRegion_hard_iff p hΔ hneg hg hsmall).mp hs
  exact ⟨z, hz, hs⟩

/-- The trust-region hard norm constraint is solvable exactly at or below its threshold. -/
theorem exists_signedTrustRegion_completion_iff {Δ : ℝ} (hΔ : 0 < Δ)
    (hneg : ∃ i, p i = false) (hg : signComponent p false g = 0) :
    (∃ z : EuclideanSpace ℝ (Fin n),
      ‖signComponent p false z‖ ^ 2 = Δ ^ 2 - ‖signComponent p true g‖ ^ 2 / 4) ↔
        ‖signComponent p true g‖ / 2 ≤ Δ := by
  constructor
  · rintro ⟨z, hz⟩
    nlinarith [sq_nonneg ‖signComponent p false z‖, norm_nonneg (signComponent p true g)]
  · intro hsmall
    obtain ⟨z, hz, _⟩ := exists_signedTrustRegion_hard p hΔ hneg hg (by linarith)
    exact ⟨z, hz⟩

/-- At the exact trust-region hard threshold, the free negative component vanishes, so the
hard family reduces to a unique global minimizer. -/
theorem signedTrustRegion_hard_equality_iff {Δ : ℝ} (hΔ : 0 < Δ)
    (hneg : ∃ i, p i = false) (hg : signComponent p false g = 0)
    (he : ‖signComponent p true g‖ = 2 * Δ) :
    Chapter08.Section01.trustRegionMinimizer g (signedDiagonal p) 1 Δ s ↔
      s = (-(2 : ℝ)⁻¹) • signComponent p true g := by
  rw [signedTrustRegion_hard_iff p hΔ hneg hg he.le]
  constructor
  · rintro ⟨z, hs, hz⟩
    have hz0 : ‖signComponent p false z‖ = 0 := by
      rw [he] at hz
      nlinarith [norm_nonneg (signComponent p false z)]
    simpa only [signedDiagonalHardStep, norm_eq_zero.mp hz0, add_zero] using hs
  · intro hs
    refine ⟨0, by simpa only [signedDiagonalHardStep, signComponent_zero, add_zero] using hs, ?_⟩
    rw [signComponent_zero, norm_zero, he]
    ring

end CartisGouldToint.Chapter11.Section01
