import Numlib.Eigen.ShiftedInverseBatches

/-!
# Rayleigh errors of actual shifted inverse batches

The estimates use the actual orthonormal eigenbasis and inverse powers. A nonzero coordinate
in a lowest eigenspace supplies the normalization lower bound. Repeated lowest eigenvalues
are retained, and only the gap to the remaining spectrum enters the error estimate.
-/

noncomputable section
open scoped InnerProductSpace BigOperators
namespace Krylov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)

/-- The squared norm of an inverse power dominates any one of its spectral coordinates. -/
theorem sq_repr_le_norm_shiftedInversePower_sq (x : E) (t : ℝ)
    (ht : ∀ j, t + hA.eigenvalues rfl j ≠ 0) (m : ℕ)
    (i : Fin (Module.finrank ℝ E)) :
    ((hA.eigenvectorBasis rfl).repr x i / (t + hA.eigenvalues rfl i) ^ m) ^ 2 ≤
      ‖shiftedInversePower A t x m‖ ^ 2 := by
  rw [norm_shiftedInversePower_sq hA x t ht]
  exact Finset.single_le_sum (fun j _ => sq_nonneg
    ((hA.eigenvectorBasis rfl).repr x j / (t + hA.eigenvalues rfl j) ^ m))
      (Finset.mem_univ i)

/-- The Rayleigh error above any reference value is an exact weighted spectral sum.
The input must be nonzero so that the computed vector has unit norm. -/
theorem inner_shiftedInverseBatch_sub (x : E) (hx : x ≠ 0) (t a : ℝ)
    (ht : ∀ j, t + hA.eigenvalues rfl j ≠ 0) (m : ℕ) :
    inner ℝ (shiftedInverseBatch A t x m) (A (shiftedInverseBatch A t x m)) - a =
      (∑ j, (hA.eigenvalues rfl j - a) *
        ((hA.eigenvectorBasis rfl).repr x j / (t + hA.eigenvalues rfl j) ^ m) ^ 2) /
          ‖shiftedInversePower A t x m‖ ^ 2 := by
  have hn : ‖shiftedInversePower A t x m‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (shiftedInversePower_ne_zero
      (Optimization.SecularResolvent.isUnit_shift hA t ht) hx m))
  rw [inner_shiftedInverseBatch hA x t ht,
    ← norm_shiftedInversePower_sq hA x t ht, sub_eq_iff_eq_add]
  apply (div_eq_iff hn).mpr
  rw [add_mul, div_mul_cancel₀ _ hn, norm_shiftedInversePower_sq hA x t ht,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every actual regular inverse batch has Rayleigh quotient above a spectral lower bound. -/
theorem inner_shiftedInverseBatch_ge (x : E) (hx : x ≠ 0) {t a : ℝ}
    (ht : ∀ j, t + hA.eigenvalues rfl j ≠ 0)
    (ha : ∀ j, a ≤ hA.eigenvalues rfl j) (m : ℕ) :
    a ≤ inner ℝ (shiftedInverseBatch A t x m) (A (shiftedInverseBatch A t x m)) := by
  apply sub_nonneg.mp
  rw [inner_shiftedInverseBatch_sub hA x hx t a ht m]
  exact div_nonneg (Finset.sum_nonneg fun j _ =>
    mul_nonneg (sub_nonneg.mpr (ha j)) (sq_nonneg _)) (sq_nonneg _)

/-- A positive gap above the lowest eigenspace and a spectral width bound control the
unnormalized Rayleigh numerator. The terms in the full lowest eigenspace vanish exactly. -/
theorem sum_rayleighError_inversePower_le (x : E) {t a d L : ℝ}
    (ht : 0 < t + a) (hd : 0 < d) (hL : 0 ≤ L)
    (hlo : ∀ j, a ≤ hA.eigenvalues rfl j)
    (hgap : ∀ j, hA.eigenvalues rfl j ≠ a → d ≤ hA.eigenvalues rfl j - a)
    (hwidth : ∀ j, hA.eigenvalues rfl j - a ≤ L) (m : ℕ) :
    (∑ j, (hA.eigenvalues rfl j - a) *
      ((hA.eigenvectorBasis rfl).repr x j / (t + hA.eigenvalues rfl j) ^ m) ^ 2) ≤
      L * ‖x‖ ^ 2 / d ^ (2 * m) := by
  rw [hA.norm_sq_eq_sum_eigenvector_coordinates, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : hA.eigenvalues rfl j = a
  · rw [hj, sub_self, zero_mul]
    positivity
  · have hjp : 0 < t + hA.eigenvalues rfl j := by linarith [hlo j]
    have hdj : d ≤ t + hA.eigenvalues rfl j := by linarith [hgap j hj]
    calc
      _ ≤ L * ((hA.eigenvectorBasis rfl).repr x j /
          (t + hA.eigenvalues rfl j) ^ m) ^ 2 :=
        mul_le_mul_of_nonneg_right (hwidth j) (sq_nonneg _)
      _ = (L * ((hA.eigenvectorBasis rfl).repr x j) ^ 2) /
          (t + hA.eigenvalues rfl j) ^ (2 * m) := by
        rw [div_pow, ← pow_mul, Nat.mul_comm m 2]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hL (sq_nonneg _))
        (pow_pos hd _) (pow_le_pow_left₀ hd.le hdj _)

/-- Finite spectra admit a positive gap above any spectral minimum. If every eigenvalue
is equal, any positive gap works because there are no remaining spectral values. -/
theorem exists_spectralGap {a : ℝ} (hlo : ∀ j, a ≤ hA.eigenvalues rfl j) :
    ∃ d : ℝ, 0 < d ∧ ∀ j, hA.eigenvalues rfl j ≠ a →
      d ≤ hA.eigenvalues rfl j - a := by
  classical
  have hfinite : ∀ s : Finset (Fin (Module.finrank ℝ E)),
      ∃ d : ℝ, 0 < d ∧ ∀ j ∈ s, hA.eigenvalues rfl j ≠ a →
        d ≤ hA.eigenvalues rfl j - a := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert j s _ ih =>
      obtain ⟨d, hd, hds⟩ := ih
      by_cases hj : hA.eigenvalues rfl j = a
      · refine ⟨d, hd, ?_⟩
        intro l hl hlne
        rcases Finset.mem_insert.mp hl with rfl | hl
        · exact (hlne hj).elim
        · exact hds l hl hlne
      · refine ⟨min d (hA.eigenvalues rfl j - a),
          lt_min hd (lt_of_le_of_ne (sub_nonneg.mpr (hlo j)) (sub_ne_zero.mpr hj).symm), ?_⟩
        intro l hl hlne
        rcases Finset.mem_insert.mp hl with rfl | hl
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hds l hl hlne)
  obtain ⟨d, hd, hds⟩ := hfinite Finset.univ
  exact ⟨d, hd, fun j => hds j (Finset.mem_univ j)⟩

/-- A finite spectrum has a nonnegative width above any reference value. -/
theorem exists_spectralWidth (a : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j, hA.eigenvalues rfl j - a ≤ L := by
  classical
  let L := ∑ j, max 0 (hA.eigenvalues rfl j - a)
  refine ⟨L, Finset.sum_nonneg (fun j _ => le_max_left _ _), ?_⟩
  intro j
  exact (le_max_right _ _).trans (Finset.single_le_sum
    (fun l _ => le_max_left 0 (hA.eigenvalues rfl l - a)) (Finset.mem_univ j))

/-- If the spectrum is constant, every genuine inverse batch has exactly that Rayleigh
quotient, including all multiplicities and all positive batch lengths. -/
theorem inner_shiftedInverseBatch_eq_of_spectrum_eq (x : E) (hx : x ≠ 0)
    (t a : ℝ) (ht : t + a ≠ 0) (ha : ∀ j, hA.eigenvalues rfl j = a) (m : ℕ) :
    inner ℝ (shiftedInverseBatch A t x m) (A (shiftedInverseBatch A t x m)) = a := by
  apply sub_eq_zero.mp
  rw [inner_shiftedInverseBatch_sub hA x hx t a (fun j => by rw [ha j]; exact ht)]
  simp only [ha, sub_self, zero_mul, Finset.sum_const_zero, zero_div]

/-- The genuine Rayleigh error decays with twice the inverse-batch length. The constant
uses an actual nonzero lowest-eigenspace coordinate, never an assumed error oracle. -/
theorem inner_shiftedInverseBatch_sub_le (x : E)
    {i : Fin (Module.finrank ℝ E)} (hi : (hA.eigenvectorBasis rfl).repr x i ≠ 0)
    {t d L : ℝ} (ht : 0 < t + hA.eigenvalues rfl i) (hd : 0 < d) (hL : 0 ≤ L)
    (hlo : ∀ j, hA.eigenvalues rfl i ≤ hA.eigenvalues rfl j)
    (hgap : ∀ j, hA.eigenvalues rfl j ≠ hA.eigenvalues rfl i →
      d ≤ hA.eigenvalues rfl j - hA.eigenvalues rfl i)
    (hwidth : ∀ j, hA.eigenvalues rfl j - hA.eigenvalues rfl i ≤ L) (m : ℕ) :
    inner ℝ (shiftedInverseBatch A t x m) (A (shiftedInverseBatch A t x m)) -
      hA.eigenvalues rfl i ≤
        (L * ‖x‖ ^ 2 / ((hA.eigenvectorBasis rfl).repr x i) ^ 2) *
          ((t + hA.eigenvalues rfl i) / d) ^ (2 * m) := by
  have hx : x ≠ 0 := by intro h; apply hi; simp [h]
  have hreg : ∀ j, t + hA.eigenvalues rfl j ≠ 0 :=
    fun j => ne_of_gt (by linarith [hlo j])
  rw [inner_shiftedInverseBatch_sub hA x hx t _ hreg]
  have hn := sq_repr_le_norm_shiftedInversePower_sq hA x t hreg m i
  have hp : 0 < ((hA.eigenvectorBasis rfl).repr x i /
      (t + hA.eigenvalues rfl i) ^ m) ^ 2 :=
    sq_pos_of_ne_zero (div_ne_zero hi (pow_ne_zero m ht.ne'))
  have hs := sum_rayleighError_inversePower_le hA x ht hd hL hlo hgap hwidth m
  calc
    _ ≤ (L * ‖x‖ ^ 2 / d ^ (2 * m)) /
        (((hA.eigenvectorBasis rfl).repr x i /
          (t + hA.eigenvalues rfl i) ^ m) ^ 2) := by
      exact div_le_div₀ (by positivity) hs hp hn
    _ = _ := by
      rw [div_pow, ← pow_mul, Nat.mul_comm m 2, div_pow]
      field_simp

end Krylov
