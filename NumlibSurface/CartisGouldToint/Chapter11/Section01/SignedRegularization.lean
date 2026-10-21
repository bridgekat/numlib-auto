import NumlibSurface.CartisGouldToint.Chapter11.Section01.SignedDiagonal

/-!
# Regularized signed diagonal classification

The actual power-regularized minimizers determine the secular multiplier. The norm target
retains a single power of the multiplier inside the real power, correcting the transcription.
-/

open Matrix
open Optimization.QuadraticSubproblem
open scoped ComplexOrder

namespace CartisGouldToint.Chapter11.Section01

variable {n : ℕ} (p : Fin n → Bool) {g s : EuclideanSpace ℝ (Fin n)}

/-- The corrected squared secular equation is exactly the radial multiplier condition. -/
theorem signedRegularization_easy_radial {σ r lambda : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hlambda : 1 < lambda)
    (hroot : ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
      ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 =
        (lambda / σ) ^ (2 / (r - 2))) :
    lambda = σ * ‖signedDiagonalStep p g lambda‖ ^ (r - 2) := by
  apply (radialShift_iff_sq_radius (norm_nonneg _) (by linarith) hσ
    (by linarith : r - 2 ≠ 0)).mpr
  rw [norm_sq_signedDiagonalStep, hroot]

/-- The regularized minimizer from an easy secular root is unique. -/
theorem signedRegularization_easy_unique {σ r lambda : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hlambda : 1 < lambda)
    (hroot : ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
      ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 =
        (lambda / σ) ^ (2 / (r - 2)))
    (hs : Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s) :
    s = signedDiagonalStep p g lambda := by
  have hrad := signedRegularization_easy_radial p hσ hr hlambda hroot
  apply (Chapter08.Section02.theorem_8_2_8 (signedDiagonal_isSymm p)
    Matrix.PosDef.one hσ hr).2 _ (signedRegularization_easy p hσ hr hlambda hroot) s hs
  rw [weightedNorm_one, ← hrad]
  exact signedDiagonal_shift_posDef p hlambda

/-- Nonzero negative gradient forces every regularized minimizer to an easy secular root. -/
theorem signedRegularization_easy_necessary {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hg : signComponent p false g ≠ 0)
    (hs : Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s) :
    ∃ lambda : ℝ, 1 < lambda ∧ s = signedDiagonalStep p g lambda ∧
      ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
        ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 =
          (lambda / σ) ^ (2 / (r - 2)) := by
  obtain ⟨lambda, hrad, hstat, hp⟩ := (Chapter08.Section02.theorem_8_2_8
    (signedDiagonal_isSymm p) Matrix.PosDef.one hσ hr).1.mp hs
  rw [weightedNorm_one] at hrad
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
  rw [← norm_sq_signedDiagonalStep, ← heq]
  exact (radialShift_iff_sq_radius (norm_nonneg _) (by linarith) hσ
    (by linarith : r - 2 ≠ 0)).mp hrad

/-- The corrected regularization secular equation has a unique root above `1` when the negative
gradient is nonzero. Existence follows from attainment of the actual global minimum. -/
theorem existsUnique_signedRegularization_root {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hg : signComponent p false g ≠ 0) :
    ∃! lambda : ℝ, 1 < lambda ∧
      ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
        ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 =
          (lambda / σ) ^ (2 / (r - 2)) := by
  obtain ⟨s, hs⟩ := exists_signedRegularization p g hσ hr
  obtain ⟨lambda, hl, heq, hroot⟩ := signedRegularization_easy_necessary p hσ hr hg hs
  refine ⟨lambda, ⟨hl, hroot⟩, ?_⟩
  rintro mu ⟨hmu, hmuroot⟩
  have he := signedRegularization_easy_unique p hσ hr hl hroot
    (signedRegularization_easy p hσ hr hmu hmuroot)
  have hlrad := signedRegularization_easy_radial p hσ hr hl hroot
  have hmrad := signedRegularization_easy_radial p hσ hr hmu hmuroot
  rw [he, ← hlrad] at hmrad
  exact hmrad

/-- The hard family gives exactly all regularized minimizers below the non-strict positive-gradient
threshold. The negative space is required to be nonempty; no dimension bound on it is used. -/
theorem signedRegularization_hard_iff {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hneg : ∃ i, p i = false) (hg : signComponent p false g = 0)
    (hsmall : ‖signComponent p true g‖ ≤ 2 * (1 / σ) ^ (1 / (r - 2))) :
    Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s ↔
      ∃ z : EuclideanSpace ℝ (Fin n), s = signedDiagonalHardStep p g z ∧
        ‖signComponent p false z‖ ^ 2 =
          (1 / σ) ^ (2 / (r - 2)) - ‖signComponent p true g‖ ^ 2 / 4 := by
  constructor
  · intro hs
    obtain ⟨lambda, hrad, hstat, hp⟩ := (Chapter08.Section02.theorem_8_2_8
      (signedDiagonal_isSymm p) Matrix.PosDef.one hσ hr).1.mp hs
    rw [weightedNorm_one] at hrad
    obtain ⟨i, hi⟩ := hneg
    have hb := (signedDiagonal_shift_posSemidef_iff p lambda).mp hp i
    simp only [hi, Bool.false_eq_true, ite_false] at hb
    have he : lambda = 1 := by
      by_contra hne
      have hl : 1 < lambda := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      have heq := (signedDiagonal_stationary_iff p g s (by linarith) (by linarith)).mp hstat
      have hnorm : ‖s‖ = (lambda + 1)⁻¹ * ‖signComponent p true g‖ := by
        rw [heq, signedDiagonalStep, hg, smul_zero, add_zero, norm_smul,
          Real.norm_eq_abs, abs_neg, abs_inv, abs_of_pos (by linarith : 0 < lambda + 1)]
      have hprod : (lambda + 1) * ‖s‖ = ‖signComponent p true g‖ := by
        rw [hnorm, ← mul_assoc, mul_inv_cancel₀ (by linarith : lambda + 1 ≠ 0), one_mul]
      have hR : 0 < (1 / σ) ^ (1 / (r - 2)) := Real.rpow_pos_of_pos (by positivity) _
      have hlt : ‖s‖ < (1 / σ) ^ (1 / (r - 2)) := by
        have hh := mul_pos (sub_pos.mpr hl) hR
        nlinarith [norm_nonneg s]
      have hrad' := (radialShift_iff_radius (norm_nonneg s) (by linarith) hσ
        (by linarith : r - 2 ≠ 0)).mp hrad
      have htarget : (1 / σ) ^ (1 / (r - 2)) < (lambda / σ) ^ (1 / (r - 2)) := by
        apply Real.rpow_lt_rpow (by positivity) ((div_lt_div_iff_of_pos_right hσ).mpr hl)
        positivity
      rw [← hrad'] at htarget
      exact (not_lt_of_ge hlt.le) htarget
    rw [he] at hstat hrad
    have hsplus := ((signedDiagonal_stationary_one_iff p g s).mp hstat).2
    have hsform : s = signedDiagonalHardStep p g s := by
      rw [signedDiagonalHardStep, ← hsplus, signComponent_add]
    refine ⟨s, hsform, ?_⟩
    have hsq := (radialShift_iff_sq_radius (norm_nonneg s) zero_le_one hσ
      (by linarith : r - 2 ≠ 0)).mp hrad
    have hn := norm_sq_signedDiagonalHardStep p g s
    rw [← hsform, hsq] at hn
    linarith
  · rintro ⟨z, rfl, hz⟩
    exact signedRegularization_hard p hσ hr hg z hz

/-- With a negative eigendirection, the easy secular family and the singular hard family
exhaust all regularized minimizers, with the corrected power target and subtraction. -/
theorem signedRegularization_cases_iff {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hneg : ∃ i, p i = false) :
    Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s ↔
      (∃ lambda : ℝ, 1 < lambda ∧ s = signedDiagonalStep p g lambda ∧
        ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
          ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 =
            (lambda / σ) ^ (2 / (r - 2))) ∨
      (signComponent p false g = 0 ∧ ∃ z : EuclideanSpace ℝ (Fin n),
        s = signedDiagonalHardStep p g z ∧
          ‖signComponent p false z‖ ^ 2 =
            (1 / σ) ^ (2 / (r - 2)) - ‖signComponent p true g‖ ^ 2 / 4) := by
  constructor
  · intro hs
    obtain ⟨lambda, hrad, hstat, hp⟩ := (Chapter08.Section02.theorem_8_2_8
      (signedDiagonal_isSymm p) Matrix.PosDef.one hσ hr).1.mp hs
    rw [weightedNorm_one] at hrad
    obtain ⟨i, hi⟩ := hneg
    have hb := (signedDiagonal_shift_posSemidef_iff p lambda).mp hp i
    simp only [hi, Bool.false_eq_true, ite_false] at hb
    by_cases he : lambda = 1
    · right
      rw [he] at hstat hrad
      obtain ⟨hg, hsplus⟩ := (signedDiagonal_stationary_one_iff p g s).mp hstat
      have hsform : s = signedDiagonalHardStep p g s := by
        rw [signedDiagonalHardStep, ← hsplus, signComponent_add]
      refine ⟨hg, s, hsform, ?_⟩
      have hsq := (radialShift_iff_sq_radius (norm_nonneg s) zero_le_one hσ
      (by linarith : r - 2 ≠ 0)).mp hrad
      have hn := norm_sq_signedDiagonalHardStep p g s
      rw [← hsform, hsq] at hn
      linarith
    · left
      have hlambda : 1 < lambda := lt_of_le_of_ne (by linarith) (Ne.symm he)
      have heq := (signedDiagonal_stationary_iff p g s (by linarith) (by linarith)).mp hstat
      refine ⟨lambda, hlambda, heq, ?_⟩
      rw [← norm_sq_signedDiagonalStep, ← heq]
      exact (radialShift_iff_sq_radius (norm_nonneg s) (by linarith) hσ
        (by linarith : r - 2 ≠ 0)).mp hrad
  · rintro (⟨lambda, hl, rfl, hroot⟩ | ⟨hg, z, rfl, hz⟩)
    · exact signedRegularization_easy p hσ hr hl hroot
    · exact signedRegularization_hard p hσ hr hg z hz

omit p in
/-- With a positive diagonal, the regularized minimizer is a negative-gradient step determined
by the nonnegative scalar multiplier, including the zero-gradient solution. -/
theorem positiveDiagonalRegularization_iff {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) :
    Chapter08.Section01.regularizedMinimizer g (signedDiagonal (fun _ : Fin n => true)) 1 σ r s ↔
      ∃ lambda : ℝ, 0 ≤ lambda ∧ s = (-(lambda + 1)⁻¹) • g ∧
        lambda = σ * (‖g‖ / (lambda + 1)) ^ (r - 2) := by
  have hnorm (lambda : ℝ) (hl : 0 ≤ lambda) :
      ‖(-(lambda + 1)⁻¹) • g‖ = ‖g‖ / (lambda + 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv,
      abs_of_pos (by linarith : 0 < lambda + 1)]
    exact (div_eq_inv_mul _ _).symm
  constructor
  · intro hs
    obtain ⟨lambda, hrad, hstat, hp⟩ := (Chapter08.Section02.theorem_8_2_8
      (signedDiagonal_isSymm (fun _ : Fin n => true)) Matrix.PosDef.one hσ hr).1.mp hs
    rw [weightedNorm_one] at hrad
    have hl : 0 ≤ lambda := by rw [hrad]; positivity
    have heq : s = (-(lambda + 1)⁻¹) • g := by
      ext i
      have hi := (signedDiagonal_stationary_coordinates _ g s lambda).mp hstat i
      change (lambda + 1) * s i = -g i at hi
      change s i = -(lambda + 1)⁻¹ * g i
      field_simp
      nlinarith
    refine ⟨lambda, hl, heq, ?_⟩
    rw [heq, hnorm lambda hl] at hrad
    exact hrad
  · rintro ⟨lambda, hl, rfl, hrad⟩
    apply (Chapter08.Section02.theorem_8_2_8
      (signedDiagonal_isSymm (fun _ : Fin n => true)) Matrix.PosDef.one hσ hr).1.mpr
    refine ⟨lambda, ?_, ?_, ?_⟩
    · rw [weightedNorm_one, hnorm lambda hl]
      exact hrad
    · rw [signedDiagonal_stationary_coordinates]
      intro i
      change (lambda + 1) * (-(lambda + 1)⁻¹ * g i) = -g i
      field_simp
    · rw [signedDiagonal_shift_posSemidef_iff]
      intro i
      change 0 ≤ lambda + 1
      linarith

omit p in
/-- All-positive regularization has a unique global minimizer, even when the gradient is zero. -/
theorem positiveDiagonalRegularization_unique {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hs : Chapter08.Section01.regularizedMinimizer g
      (signedDiagonal (fun _ : Fin n => true)) 1 σ r s)
    {t : EuclideanSpace ℝ (Fin n)}
    (ht : Chapter08.Section01.regularizedMinimizer g
      (signedDiagonal (fun _ : Fin n => true)) 1 σ r t) : t = s := by
  apply (Chapter08.Section02.theorem_8_2_8
    (signedDiagonal_isSymm (fun _ : Fin n => true)) Matrix.PosDef.one hσ hr).2 _ hs t ht
  rw [signedDiagonal_shift, posDef_diagonal_iff]
  intro i
  rw [weightedNorm_one]
  change 0 < σ * ‖s‖ ^ (r - 2) + 1
  positivity

/-- At and below the corrected hard threshold, negative completion vectors actually exist. -/
theorem exists_signedRegularization_hard {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hneg : ∃ i, p i = false) (hg : signComponent p false g = 0)
    (hsmall : ‖signComponent p true g‖ / 2 ≤ σ ^ (-1 / (r - 2))) :
    ∃ z : EuclideanSpace ℝ (Fin n),
      ‖signComponent p false z‖ ^ 2 = σ ^ (-2 / (r - 2)) -
        ‖signComponent p true g‖ ^ 2 / 4 ∧
        Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r
          (signedDiagonalHardStep p g z) := by
  have hsmall' : ‖signComponent p true g‖ ≤ 2 * (1 / σ) ^ (1 / (r - 2)) := by
    rw [inverse_radial_target_eq]
    linarith
  obtain ⟨s, hs⟩ := exists_signedRegularization p g hσ hr
  obtain ⟨z, rfl, hz⟩ := (signedRegularization_hard_iff p hσ hr hneg hg hsmall').mp hs
  rw [inverse_radial_target_eq] at hz
  exact ⟨z, hz, hs⟩

omit p in
/-- The all-positive scalar regularization equation has exactly one nonnegative root. -/
theorem existsUnique_positiveDiagonalRegularization_root {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) :
    ∃! lambda : ℝ, 0 ≤ lambda ∧ lambda = σ * (‖g‖ / (lambda + 1)) ^ (r - 2) := by
  have hnorm (lambda : ℝ) (hl : 0 ≤ lambda) :
      ‖(-(lambda + 1)⁻¹) • g‖ = ‖g‖ / (lambda + 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv,
      abs_of_pos (by linarith : 0 < lambda + 1)]
    exact (div_eq_inv_mul _ _).symm
  obtain ⟨s, hs⟩ := exists_signedRegularization (fun _ : Fin n => true) g hσ hr
  obtain ⟨lambda, hl, heq, hroot⟩ := (positiveDiagonalRegularization_iff hσ hr).mp hs
  refine ⟨lambda, ⟨hl, hroot⟩, ?_⟩
  rintro mu ⟨hm, hmroot⟩
  have hmin := (positiveDiagonalRegularization_iff hσ hr).mpr ⟨mu, hm, rfl, hmroot⟩
  have he := positiveDiagonalRegularization_unique hσ hr hs hmin
  have hn := congrArg norm he
  rw [heq, hnorm mu hm, hnorm lambda hl] at hn
  rw [hmroot, hn, ← hroot]

/-- The corrected hard-case threshold is necessary and sufficient for negative norm completions.
The condition includes equality; completion existence is derived from actual minimizers. -/
theorem exists_signedRegularization_completion_iff {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hneg : ∃ i, p i = false) (hg : signComponent p false g = 0) :
    (∃ z : EuclideanSpace ℝ (Fin n), ‖signComponent p false z‖ ^ 2 =
      σ ^ (-2 / (r - 2)) - ‖signComponent p true g‖ ^ 2 / 4) ↔
        ‖signComponent p true g‖ / 2 ≤ σ ^ (-1 / (r - 2)) := by
  have hR : 0 ≤ σ ^ (-1 / (r - 2)) := Real.rpow_nonneg hσ.le _
  have hsq : (σ ^ (-1 / (r - 2))) ^ 2 = σ ^ (-2 / (r - 2)) := by
    rw [← Real.rpow_mul_natCast hσ.le]
    congr 1
    ring
  constructor
  · rintro ⟨z, hz⟩
    rw [← hsq] at hz
    nlinarith [sq_nonneg ‖signComponent p false z‖, norm_nonneg (signComponent p true g)]
  · intro hsmall
    obtain ⟨z, hz, _⟩ := exists_signedRegularization_hard p hσ hr hneg hg hsmall
    exact ⟨z, hz⟩

/-- At the exact regularization hard threshold, the hard family has a unique minimizer. -/
theorem signedRegularization_hard_equality_iff {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    (hneg : ∃ i, p i = false) (hg : signComponent p false g = 0)
    (he : ‖signComponent p true g‖ = 2 * (1 / σ) ^ (1 / (r - 2))) :
    Chapter08.Section01.regularizedMinimizer g (signedDiagonal p) 1 σ r s ↔
      s = (-(2 : ℝ)⁻¹) • signComponent p true g := by
  have hsq : ((1 / σ) ^ (1 / (r - 2))) ^ 2 = (1 / σ) ^ (2 / (r - 2)) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / σ)]
    congr 1
    ring
  rw [signedRegularization_hard_iff p hσ hr hneg hg he.le]
  constructor
  · rintro ⟨z, hs, hz⟩
    have hz0 : ‖signComponent p false z‖ = 0 := by
      rw [he, ← hsq] at hz
      nlinarith [norm_nonneg (signComponent p false z)]
    simpa only [signedDiagonalHardStep, norm_eq_zero.mp hz0, add_zero] using hs
  · intro hs
    refine ⟨0, by simpa only [signedDiagonalHardStep, signComponent_zero, add_zero] using hs, ?_⟩
    rw [signComponent_zero, norm_zero, he, ← hsq]
    ring

end CartisGouldToint.Chapter11.Section01
