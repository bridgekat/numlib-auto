import Numlib.Eigen.PowerMethod
import Numlib.Optimization.SecularResolvent
import Numlib.Analysis.InnerProductSpace.SpectralNormBounds

/-!
# Spectral coordinates of normalized shifted inverse batches

The batch is the existing actual inverse iteration, with a fixed shift during the batch.
Its coordinate formulas retain every vector in a repeated eigenspace. No spectral coefficient,
normalization, or Rayleigh estimate is supplied as algorithmic data.
-/

noncomputable section
open scoped InnerProductSpace BigOperators
namespace Krylov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A batch of normalized inverse iterations with the additive shift convention `A + t I`. -/
noncomputable def shiftedInverseBatch (A : E →ₗ[ℝ] E) (t : ℝ) (x : E) (m : ℕ) : E :=
  inverseIterate A (-t) x m

/-- The unnormalized power underlying a fixed-shift inverse batch. -/
noncomputable def shiftedInversePower (A : E →ₗ[ℝ] E) (t : ℝ) (x : E) (m : ℕ) : E :=
  (Ring.inverse (A + t • (1 : E →ₗ[ℝ] E)) ^ m) x

/-- The normalized inverse batch is the normalization of its genuine inverse power. -/
theorem shiftedInverseBatch_eq (A : E →ₗ[ℝ] E) (t : ℝ) (x : E) (m : ℕ) :
    shiftedInverseBatch A t x m =
      ‖shiftedInversePower A t x m‖⁻¹ • shiftedInversePower A t x m := by
  simp [shiftedInverseBatch, inverseIterate, powerIterate, shiftedInversePower,
    sub_eq_add_neg]

/-- A batch starts at the normalization of the given vector. -/
@[simp] theorem shiftedInverseBatch_zero (A : E →ₗ[ℝ] E) (t : ℝ) (x : E) :
    shiftedInverseBatch A t x 0 = ‖x‖⁻¹ • x := by
  simp [shiftedInverseBatch_eq, shiftedInversePower]

/-- Every inner iteration solves the same shifted system and then normalizes its result. -/
theorem shiftedInverseBatch_succ (A : E →ₗ[ℝ] E) (t : ℝ) (x : E) (m : ℕ) :
    shiftedInverseBatch A t x (m + 1) =
      ‖Ring.inverse (A + t • 1) (shiftedInverseBatch A t x m)‖⁻¹ •
        Ring.inverse (A + t • 1) (shiftedInverseBatch A t x m) := by
  unfold shiftedInverseBatch inverseIterate
  simp only [neg_smul, sub_neg_eq_add]
  exact powerIterate_succ (Ring.inverse (A + t • 1)) x m

/-- A nonsingular shifted inverse power cannot annihilate a nonzero starting vector. -/
theorem shiftedInversePower_ne_zero {A : E →ₗ[ℝ] E} {t : ℝ}
    (ht : IsUnit (A + t • 1)) {x : E} (hx : x ≠ 0) (m : ℕ) :
    shiftedInversePower A t x m ≠ 0 := by
  have hi : IsUnit (Ring.inverse (A + t • 1)) := by
    rw [Ring.inverse_of_isUnit ht]
    exact Units.isUnit _
  exact fun h => hx (((Module.End.isUnit_iff _).mp (hi.pow m)).injective
    (h.trans (map_zero _).symm))

/-- Every nonsingular batch with a nonzero input has norm one. -/
theorem norm_shiftedInverseBatch {A : E →ₗ[ℝ] E} {t : ℝ}
    (ht : IsUnit (A + t • 1)) {x : E} (hx : x ≠ 0) (m : ℕ) :
    ‖shiftedInverseBatch A t x m‖ = 1 := by
  rw [shiftedInverseBatch_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (shiftedInversePower_ne_zero ht hx m))]

section Spectral
variable [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)

/-- Coordinates of a genuine inverse power in the actual orthonormal eigenbasis. -/
theorem repr_shiftedInversePower (x : E) (t : ℝ)
    (ht : ∀ i, t + hA.eigenvalues rfl i ≠ 0) (m : ℕ)
    (i : Fin (Module.finrank ℝ E)) :
    (hA.eigenvectorBasis rfl).repr (shiftedInversePower A t x m) i =
      (hA.eigenvectorBasis rfl).repr x i / (t + hA.eigenvalues rfl i) ^ m := by
  induction m with
  | zero => simp [shiftedInversePower]
  | succ m ih =>
    rw [shiftedInversePower, pow_succ', Module.End.mul_apply,
      Optimization.SecularResolvent.repr_inverse_apply hA _ t ht]
    change (hA.eigenvectorBasis rfl).repr (shiftedInversePower A t x m) i / _ = _
    rw [ih, pow_succ, div_div]

/-- Parseval gives the exact normalization factor for the whole batch. -/
theorem norm_shiftedInversePower_sq (x : E) (t : ℝ)
    (ht : ∀ i, t + hA.eigenvalues rfl i ≠ 0) (m : ℕ) :
    ‖shiftedInversePower A t x m‖ ^ 2 =
      ∑ i, ((hA.eigenvectorBasis rfl).repr x i /
        (t + hA.eigenvalues rfl i) ^ m) ^ 2 := by
  rw [← (hA.eigenvectorBasis rfl).repr.norm_map, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [repr_shiftedInversePower hA x t ht]

/-- Exact normalized spectral coordinates, including repeated eigenvalues. -/
theorem repr_shiftedInverseBatch (x : E) (t : ℝ)
    (ht : ∀ i, t + hA.eigenvalues rfl i ≠ 0) (m : ℕ)
    (i : Fin (Module.finrank ℝ E)) :
    (hA.eigenvectorBasis rfl).repr (shiftedInverseBatch A t x m) i =
      ((hA.eigenvectorBasis rfl).repr x i / (t + hA.eigenvalues rfl i) ^ m) /
        ‖shiftedInversePower A t x m‖ := by
  rw [shiftedInverseBatch_eq, map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, repr_shiftedInversePower hA x t ht]
  ring

/-- Any present eigenvector coordinate remains present throughout a regular inverse batch. -/
theorem repr_shiftedInverseBatch_ne_zero {x : E} {t : ℝ}
    (ht : ∀ i, t + hA.eigenvalues rfl i ≠ 0) (m : ℕ)
    {i : Fin (Module.finrank ℝ E)} (hi : (hA.eigenvectorBasis rfl).repr x i ≠ 0) :
    (hA.eigenvectorBasis rfl).repr (shiftedInverseBatch A t x m) i ≠ 0 := by
  have hx : x ≠ 0 := by intro h; apply hi; simp [h]
  rw [repr_shiftedInverseBatch hA x t ht]
  exact div_ne_zero (div_ne_zero hi (pow_ne_zero m (ht i)))
    (norm_ne_zero_iff.mpr (shiftedInversePower_ne_zero
      (Optimization.SecularResolvent.isUnit_shift hA t ht) hx m))


/-- A common positive spectral lower bound bounds the norm of every actual inverse power. -/
theorem norm_shiftedInversePower_le (x : E) {t a : ℝ}
    (ha : 0 < t + a) (hlo : ∀ i, a ≤ hA.eigenvalues rfl i) (m : ℕ) :
    ‖shiftedInversePower A t x m‖ ≤ ‖x‖ / (t + a) ^ m := by
  have ht : ∀ i, t + hA.eigenvalues rfl i ≠ 0 := fun i => ne_of_gt (by linarith [hlo i])
  have hs : ‖shiftedInversePower A t x m‖ ^ 2 ≤ (‖x‖ / (t + a) ^ m) ^ 2 := by
    rw [norm_shiftedInversePower_sq hA x t ht, div_pow,
      hA.norm_sq_eq_sum_eigenvector_coordinates, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    rw [div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg _)
      (pow_pos (pow_pos ha m) 2)
    exact pow_le_pow_left₀ (pow_nonneg ha.le m)
      (pow_le_pow_left₀ ha.le (by linarith [hlo i]) m) 2
  nlinarith [norm_nonneg (shiftedInversePower A t x m),
    div_nonneg (norm_nonneg x) (pow_nonneg ha.le m)]

/-- Every present coordinate in a lowest eigenspace is amplified by a regular batch
started at a unit vector; simplicity of the lowest eigenvalue is unnecessary. -/
theorem abs_repr_shiftedInverseBatch_ge {x : E} (hx : ‖x‖ = 1) {t : ℝ}
    {i : Fin (Module.finrank ℝ E)}
    (ht : 0 < t + hA.eigenvalues rfl i)
    (hlo : ∀ j, hA.eigenvalues rfl i ≤ hA.eigenvalues rfl j) (m : ℕ) :
    |(hA.eigenvectorBasis rfl).repr x i| ≤
      |(hA.eigenvectorBasis rfl).repr (shiftedInverseBatch A t x m) i| := by
  have hreg : ∀ j, t + hA.eigenvalues rfl j ≠ 0 :=
    fun j => ne_of_gt (by linarith [hlo j])
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; norm_num)
  have hn : 0 < ‖shiftedInversePower A t x m‖ :=
    norm_pos_iff.mpr (shiftedInversePower_ne_zero
      (Optimization.SecularResolvent.isUnit_shift hA t hreg) hx0 m)
  have hb := norm_shiftedInversePower_le hA x ht hlo m
  rw [hx] at hb
  rw [repr_shiftedInverseBatch hA x t hreg, abs_div, abs_div,
    abs_of_pos (pow_pos ht m), abs_of_pos hn]
  have hb' := (le_div_iff₀ (pow_pos ht m)).mp hb
  rw [le_div_iff₀ hn]
  apply (le_div_iff₀ (pow_pos ht m)).mpr
  nlinarith [abs_nonneg ((hA.eigenvectorBasis rfl).repr x i),
    mul_le_mul_of_nonneg_left hb' (abs_nonneg ((hA.eigenvectorBasis rfl).repr x i))]

/-- The Rayleigh numerator of a batch is an exact spectral weighted average. -/
theorem inner_shiftedInverseBatch (x : E) (t : ℝ)
    (ht : ∀ i, t + hA.eigenvalues rfl i ≠ 0) (m : ℕ) :
    inner ℝ (shiftedInverseBatch A t x m) (A (shiftedInverseBatch A t x m)) =
      (∑ i, hA.eigenvalues rfl i *
        ((hA.eigenvectorBasis rfl).repr x i / (t + hA.eigenvalues rfl i) ^ m) ^ 2) /
      (∑ i, ((hA.eigenvectorBasis rfl).repr x i /
        (t + hA.eigenvalues rfl i) ^ m) ^ 2) := by
  rw [← norm_shiftedInversePower_sq hA x t ht,
    ← (hA.eigenvectorBasis rfl).repr.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, hA.eigenvectorBasis_apply_self_apply,
    RCLike.ofReal_real_eq_id, id_eq, repr_shiftedInverseBatch hA x t ht]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Spectral
end Krylov
