import Numlib.Krylov.Lanczos
import Numlib.LinearAlgebra.Matrix.InverseDecay
import Numlib.Projection.OneDimensional
import Mathlib.Tactic

open scoped BigOperators Matrix

/-!
# Actual Lanczos embeddings and residual decay

The canonical Arnoldi basis gives the actual isometric Krylov embedding.
The Lanczos identity and tridiagonal inverse decay bound the true shifted
residual, including grade termination and an equal - endpoint spectrum.
-/

namespace Lanczos
open Krylov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual isometric embedding from canonical Arnoldi coordinates into the Krylov space. -/
noncomputable def basisEmbedding (A : E →ₗ[ℝ] E) (g : E) {m : ℕ} (hm : m ≤ grade A g) :
    EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] E :=
  (subspace A g m).subtypeₗᵢ.comp
    (Arnoldi.orthonormalBasis A g hm).repr.symm.toLinearIsometry

/-- The canonical Krylov embedding equals the sum of actual Arnoldi basis vectors. -/
theorem basisEmbedding_apply (A : E →ₗ[ℝ] E) (g : E) {m : ℕ} (hm : m ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin m)) : basisEmbedding A g hm y = ∑ i, y i • Arnoldi.vec A g
      i := by
  change ((Arnoldi.orthonormalBasis A g hm).repr.symm y : E) = _
  rw [← OrthonormalBasis.sum_repr_symm]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Arnoldi.coe_orthonormalBasis_apply]

/-- A coordinate unit vector maps to the corresponding actual Arnoldi vector. -/
theorem basisEmbedding_single (A : E →ₗ[ℝ] E) (g : E) {m : ℕ} (hm : m ≤ grade A g) (i
  : Fin m) :
    basisEmbedding A g hm (PiLp.single 2 i (1 : ℝ)) = Arnoldi.vec A g i := by
  rw [basisEmbedding_apply]
  simp [PiLp.single_apply]

/-- Actual Arnoldi coordinates are recovered by the inner product with the basis vector. -/
theorem inner_basisEmbedding_vec (A : E →ₗ[ℝ] E) (g : E) {m : ℕ} (hm : m ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    inner ℝ (basisEmbedding A g hm y) (Arnoldi.vec A g i) = y i := by
  rw [←basisEmbedding_single A g hm i, (basisEmbedding A g hm).inner_map_map]
  simp [PiLp.inner_apply, PiLp.single_apply]

/-- Every embedded vector lies in its actual finite Krylov subspace. -/
theorem basisEmbedding_mem (A : E →ₗ[ℝ] E) (g : E) {m : ℕ} (hm : m ≤ grade A g)
    (y : EuclideanSpace ℝ (Fin m)) : basisEmbedding A g hm y ∈ subspace A g m := by
  change ((Arnoldi.orthonormalBasis A g hm).repr.symm y : E) ∈ _
  exact ((Arnoldi.orthonormalBasis A g hm).repr.symm y).property

/-- Every actual Lanczos off - diagonal coefficient before grade is bounded by the operator norm. -/
theorem coeff_norm_le (A : E →L[ℝ] E) (g : E) {j : ℕ} (hj : j < grade A.toLinearMap g) :
    Lanczos.beta A.toLinearMap g j ≤ ‖A‖ := by
  have he := Lanczos.coe_beta A.toLinearMap g j
  change Lanczos.beta A.toLinearMap g j =
    inner ℝ (Arnoldi.vec A.toLinearMap g (j + 1)) (A (Arnoldi.vec A.toLinearMap g j)) at he
  by_cases hnext : j + 1 < grade A.toLinearMap g
  · have hh := abs_real_inner_le_norm (Arnoldi.vec A.toLinearMap g (j + 1))
      (A (Arnoldi.vec A.toLinearMap g j))
    rw [Arnoldi.norm_vec_eq_one_of_lt_grade A.toLinearMap g hnext, one_mul] at hh
    calc _ ≤ |Lanczos.beta A.toLinearMap g j| := le_abs_self _
      _ = |inner ℝ (Arnoldi.vec A.toLinearMap g (j + 1))
        (A (Arnoldi.vec A.toLinearMap g j))| := congrArg abs he
      _ ≤ ‖A (Arnoldi.vec A.toLinearMap g j)‖ := hh
      _ ≤ ‖A‖ := by simpa only [Arnoldi.norm_vec_eq_one_of_lt_grade A.toLinearMap g hj,
        mul_one] using A.le_opNorm (Arnoldi.vec A.toLinearMap g j)
  · have hv := (Arnoldi.vec_eq_zero_iff A.toLinearMap g (j + 1)).mpr (by omega)
    rw [hv, inner_zero_left] at he
    rw [he]
    exact norm_nonneg _


/-- The normalized initial coordinate reconstructs the actual nonzero right side. -/
theorem basisEmbedding_initial (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ grade A g) :
    basisEmbedding A g hm (‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) = g := by
  rw [map_smul, basisEmbedding_single]
  change ‖g‖ • Arnoldi.vec A g 0 = g
  simp [Arnoldi.vec_zero A g hg, smul_smul, norm_ne_zero_iff.mpr hg]

/-- The actual Lanczos embedding satisfies its projected matrix relation and rank - one
remainder. -/
theorem apply_basisEmbedding (A : E →ₗ[ℝ] E) (g : E) (hA : A.IsSymmetric) {m : ℕ}
    (hm : m + 1 ≤ grade A g) (y : EuclideanSpace ℝ (Fin (m + 1))) :
    A (basisEmbedding A g hm y) = basisEmbedding A g hm (Matrix.toEuclideanLin (Lanczos.tridiag
      A g (m + 1)) y) +
      (Lanczos.beta A g m * y (Fin.last m)) • Arnoldi.vec A g (m + 1) := by
  rw [basisEmbedding_apply, Lanczos.apply_sum g hA m]
  congr 1
  rw [basisEmbedding_apply]
  congr 1

/-- Scalar shifting preserves the exact Lanczos relation with the same rank - one remainder. -/
theorem shifted_apply_basisEmbedding (A : E →ₗ[ℝ] E) (g : E) (hA : A.IsSymmetric) {m : ℕ}
    (hm : m + 1 ≤ grade A g) (y : EuclideanSpace ℝ (Fin (m + 1))) (τ : ℝ) :
    A (basisEmbedding A g hm y) + τ • basisEmbedding A g hm y =
      basisEmbedding A g hm (Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1) + τ • 1) y) +
      (Lanczos.beta A g m * y (Fin.last m)) • Arnoldi.vec A g (m + 1) := by
  rw [apply_basisEmbedding A g hA hm]
  simp only [map_add, map_smul, Matrix.toEuclideanLin_one,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  abel


/-- A true shifted projected solve has exactly its Lanczos rank - one residual. -/
theorem residual_eq (A : E →ₗ[ℝ] E) {g : E} (hg : g ≠ 0) (hA : A.IsSymmetric) {m : ℕ}
    (hm : m + 1 ≤ grade A g) (y : EuclideanSpace ℝ (Fin (m + 1))) (τ : ℝ)
    (hsolve : Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) :
    A (basisEmbedding A g hm y) + τ • basisEmbedding A g hm y + g =
      (Lanczos.beta A g m * y (Fin.last m)) • Arnoldi.vec A g (m + 1) := by
  rw [shifted_apply_basisEmbedding A g hA hm y τ, hsolve, map_neg, basisEmbedding_initial A hg hm]
  abel

/-- The true Lanczos residual norm is bounded by the last projected coordinate times operator
norm. -/
theorem norm_residual_le_coeff (A : E →L[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.toLinearMap.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A.toLinearMap g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (τ : ℝ)
    (hsolve : Matrix.toEuclideanLin (Lanczos.tridiag A.toLinearMap g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) :
    ‖A (basisEmbedding A.toLinearMap g hm y) + τ • basisEmbedding A.toLinearMap g hm y +
      g‖ ≤
      ‖A‖ * |y (Fin.last m)| := by
  change ‖A.toLinearMap (basisEmbedding A.toLinearMap g hm y) + τ • basisEmbedding
    A.toLinearMap g hm y + g‖ ≤ _
  rw [residual_eq A.toLinearMap hg hA hm y τ hsolve, norm_smul, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Lanczos.beta_nonneg A.toLinearMap g m)]
  have hv : ‖Arnoldi.vec A.toLinearMap g (m + 1)‖ ≤ 1 := by
    by_cases hn : m + 1 < grade A.toLinearMap g
    · exact (Arnoldi.norm_vec_eq_one_of_lt_grade _ _ hn).le
    · rw [(Arnoldi.vec_eq_zero_iff _ _ _).mpr (by omega), norm_zero]; norm_num
  calc _ ≤ Lanczos.beta A.toLinearMap g m * |y (Fin.last m)| :=
      mul_le_of_le_one_right (mul_nonneg (Lanczos.beta_nonneg _ _ _) (abs_nonneg _)) hv
    _ ≤ ‖A‖ * |y (Fin.last m)| := mul_le_mul_of_nonneg_right
      (coeff_norm_le A g (by omega)) (abs_nonneg _)


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The last coordinate of an actual tridiagonal solve has the sharp inverse - decay estimate. -/
theorem last_coordinate_le {m : ℕ} {T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (htri : T.IsTridiagonal) (hunit : IsUnit T) {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (hT : (Matrix.toEuclideanLin T).IsSymmetricBoundedBy lo hi)
    (g : E) (y : EuclideanSpace ℝ (Fin (m + 1)))
    (hsolve : Matrix.toEuclideanLin T y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) :
    |y (Fin.last m)| ≤ 2 / lo * ((Real.sqrt (hi / lo) - 1) / (Real.sqrt (hi / lo) + 1)) ^ m *
      ‖g‖ := by
  have hy : y = -(‖g‖ • Matrix.toEuclideanLin T⁻¹ (PiLp.single 2 (0 : Fin (m + 1)) (1 :
    ℝ))) := by
    rw [←Matrix.toEuclideanLin_nonsing_inv_mul_apply hunit y, hsolve, map_neg, map_smul]
  rw [hy]
  have he : (Matrix.toEuclideanLin T⁻¹ (PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) (Fin.last
    m) =
      T⁻¹ (Fin.last m) 0 := by
    change (T⁻¹ *ᵥ Pi.single 0 (1 : ℝ)) (Fin.last m) = _
    simp [Matrix.mulVec_single]
  have hd := Matrix.inverse_entry_decay htri hunit hlo hle hT (Fin.last m) 0
  simp only [Fin.val_last, Fin.val_zero, Nat.dist_zero_right, Real.norm_eq_abs] at hd
  change |-(‖g‖ * (Matrix.toEuclideanLin T⁻¹ (PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (Fin.last m))| ≤ _
  rw [abs_neg, abs_mul, abs_of_nonneg (norm_nonneg _), he]
  nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg g)]


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A true shifted positive - spectrum solve bounds its right - side norm by the largest
spectral bound. -/
theorem norm_rhs_le {m : ℕ} {T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (hT : (Matrix.toEuclideanLin T).IsSymmetricBoundedBy lo hi)
    (g : E) (y : EuclideanSpace ℝ (Fin (m + 1)))
    (hsolve : Matrix.toEuclideanLin T y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ))) : ‖g‖ ≤ hi * ‖y‖ := by
  have hs : (Matrix.toEuclideanLin T).IsSymmetricBoundedBy (-hi) hi := {
    isSymmetric := hT.isSymmetric
    le_re_inner := fun v => le_trans (mul_le_mul_of_nonneg_right (by linarith : -hi ≤ lo)
      (sq_nonneg ‖v‖)) (hT.le_re_inner v)
    re_inner_le := hT.re_inner_le }
  have hh := hs.norm_apply_le y
  rw [hsolve] at hh
  simpa only [norm_neg, norm_smul, PiLp.norm_single, norm_one, Real.norm_eq_abs,
    abs_norm, mul_one] using hh


omit [FiniteDimensional ℝ E] in
/-- The actual shifted Lanczos matrix is Hermitian for every real scalar shift. -/
theorem shifted_tridiag_isHermitian (A : E →ₗ[ℝ] E) (g : E) (m : ℕ) (τ : ℝ) :
    (tridiag A g m + τ • 1).IsHermitian :=
  (Matrix.isHermitian_iff_isSymm.mpr (tridiag_isSymm A g m)).add
    (Matrix.isHermitian_one.smul (by rfl : IsSelfAdjoint τ))

omit [FiniteDimensional ℝ E] in
/-- Scalar shifting preserves the actual Lanczos matrix tridiagonal structure. -/
theorem shifted_tridiag (A : E →ₗ[ℝ] E) (g : E) (m : ℕ) (τ : ℝ) :
    (Lanczos.tridiag A g m + τ • 1).IsTridiagonal := by
  intro i j hij
  have hn : i ≠ j := by intro he; subst j; rcases hij with ⟨k, hk, hki⟩ | ⟨k, hk, hki⟩
    <;> exact (lt_irrefl i) (hk.trans hki)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hn, smul_zero, add_zero]
  exact Lanczos.tridiag_isTridiagonal A g m i j hij

/-- The actual Lanczos residual has the sharp condition - number and radius decay bound. -/
theorem norm_residual_le (A : E →L[ℝ] E) {g : E} (hg : g ≠ 0)
    (hA : A.toLinearMap.IsSymmetric) {m : ℕ} (hm : m + 1 ≤ grade A.toLinearMap g)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (τ : ℝ)
    (hsolve : Matrix.toEuclideanLin (Lanczos.tridiag A.toLinearMap g (m + 1) + τ • 1) y =
      -(‖g‖ • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)))
    (hunit : IsUnit (Lanczos.tridiag A.toLinearMap g (m + 1) + τ • 1))
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (hT : (Matrix.toEuclideanLin (Lanczos.tridiag A.toLinearMap g (m + 1) + τ •
      1)).IsSymmetricBoundedBy lo hi) :
    ‖A (basisEmbedding A.toLinearMap g hm y) + τ • basisEmbedding A.toLinearMap g hm y +
      g‖ ≤
      2 * ‖A‖ * (hi / lo) * ‖basisEmbedding A.toLinearMap g hm y‖ *
        ((Real.sqrt (hi / lo) - 1) / (Real.sqrt (hi / lo) + 1)) ^ m := by
  have hcoord := last_coordinate_le (shifted_tridiag A.toLinearMap g (m + 1) τ)
    hunit hlo hle hT g y hsolve
  have hgupper := norm_rhs_le hlo hle hT g y hsolve
  have hfac : 0 ≤ ((Real.sqrt (hi / lo) - 1) / (Real.sqrt (hi / lo) + 1)) ^ m := by
    apply pow_nonneg
    apply div_nonneg _ (by positivity)
    have hh : (1 : ℝ) ≤ Real.sqrt (hi / lo) := by
      rw [Real.le_sqrt (by norm_num) (div_nonneg (hlo.le.trans hle) hlo.le)]
      exact (le_div_iff₀ hlo).mpr (by simpa using hle)
    linarith
  have hc := mul_le_mul_of_nonneg_left hcoord (norm_nonneg A)
  have hu := mul_le_mul_of_nonneg_left hgupper
    (mul_nonneg (norm_nonneg A) (mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlo.le)
      hfac))
  have hn := (basisEmbedding A.toLinearMap g hm).norm_map y
  rw [hn]
  calc _ ≤ ‖A‖ * |y (Fin.last m)| := norm_residual_le_coeff A hg hA hm y τ hsolve
    _ ≤ ‖A‖ * (2 / lo * ((Real.sqrt (hi / lo) - 1) / (Real.sqrt (hi / lo) + 1)) ^ m *
      ‖g‖) := hc
    _ ≤ ‖A‖ * (2 / lo * ((Real.sqrt (hi / lo) - 1) / (Real.sqrt (hi / lo) + 1)) ^ m * (hi
      * ‖y‖)) :=
      by nlinarith only [hu]
    _ = _ := by ring


/-- Every actual projected off - diagonal entry before grade remains nonzero after shifting. -/
theorem shifted_tridiag_offdiag_ne (A : E →ₗ[ℝ] E) (g : E) {m : ℕ}
    (hm : m + 1 ≤ grade A g) (τ : ℝ) (j : Fin m) :
    (Lanczos.tridiag A g (m + 1) + τ • 1) j.castSucc j.succ ≠ 0 := by
  have hn : j.castSucc ≠ j.succ := by intro he; have hh := congrArg Fin.val he; simp at hh
  have hb : Lanczos.beta A g j ≠ 0 := by
    have he := Lanczos.coe_beta A g (j : ℕ)
    change Lanczos.beta A g j = Arnoldi.coeff A g (j + 1) j at he
    rw [he]
    rw [ne_eq, Arnoldi.coeff_succ_self_eq_zero_iff]
    omega
  simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hn,
    Lanczos.tridiag_apply, Fin.ext_iff] using hb


end Lanczos
