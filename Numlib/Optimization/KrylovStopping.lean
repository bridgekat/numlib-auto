import Numlib.Optimization.KrylovSubproblemBounds
import Numlib.Analysis.SpecialFunctions.GeometricStopping

/-!
# Finite-grade Lanczos stopping bounds

The geometric decay estimates can use any uniform upper bound for the shifted
condition numbers. A scalar shifted enclosure forces grade one, so its stopping
count is one even though the zeroth geometric power is one.
-/

noncomputable section
open scoped InnerProductSpace
namespace Optimization.KrylovSubproblem

/-- The Chebyshev contraction factor of a positive definite condition number. -/
def chebyshevRate (kappa : ℝ) : ℝ :=
  (Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)

/-- The contraction factor is nonnegative for condition numbers at least one. -/
theorem chebyshevRate_nonneg {kappa : ℝ} (hk : 1 ≤ kappa) :
    0 ≤ chebyshevRate kappa := by
  have h := Real.one_le_sqrt.mpr hk
  unfold chebyshevRate
  positivity

/-- A condition number greater than one gives a strictly positive factor. -/
theorem chebyshevRate_pos {kappa : ℝ} (hk : 1 < kappa) :
    0 < chebyshevRate kappa := by
  have h : 1 < Real.sqrt kappa := (Real.lt_sqrt zero_le_one).mpr (by simpa using hk)
  exact div_pos (sub_pos.mpr h) (by positivity)

/-- Every finite nonnegative condition number gives a factor below one. -/
theorem chebyshevRate_lt_one (kappa : ℝ) : chebyshevRate kappa < 1 := by
  unfold chebyshevRate
  apply (div_lt_one (by positivity : 0 < Real.sqrt kappa + 1)).mpr
  linarith

/-- Enlarging a condition number enlarges its Chebyshev factor. -/
theorem chebyshevRate_mono {a b : ℝ} (hab : a ≤ b) :
    chebyshevRate a ≤ chebyshevRate b := by
  have hs := Real.sqrt_le_sqrt hab
  unfold chebyshevRate
  rw [div_le_div_iff₀ (by positivity : 0 < Real.sqrt a + 1)
    (by positivity : 0 < Real.sqrt b + 1)]
  nlinarith

/-- A logarithmic Lanczos iteration bound, using a natural ceiling. -/
def lanczosStoppingCount (A kappa : ℝ) : ℕ :=
  if kappa ≤ 1 then 1 else
    ⌈Real.log A / Real.log ((Real.sqrt kappa + 1) / (Real.sqrt kappa - 1))⌉₊ + 1

/-- For a nondegenerate condition number this is precisely geometric logarithmic inversion. -/
theorem lanczosStoppingCount_eq {A kappa : ℝ} (hk : 1 < kappa) :
    lanczosStoppingCount A kappa =
      GeometricStopping.decayCount A (chebyshevRate kappa) + 1 := by
  simp only [lanczosStoppingCount, not_le.mpr hk, ↓reduceIte,
    GeometricStopping.decayCount, chebyshevRate, inv_div]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : E →ₗ[ℝ] E} {g : E} [FiniteDimensional ℝ (Krylov.fullSubspace A g)]

/-- A scalar shifted second Lanczos compression contradicts the nonzero first
subdiagonal. This proves the one-step branch of a uniform condition-number-one bound. -/
theorem grade_le_one_of_scalar_second_shift {a b lambda : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hk : b / a ≤ 1)
    (hB : (Matrix.toEuclideanLin (Lanczos.tridiag A g 2 + lambda • 1)).IsSymmetricBoundedBy a b) :
    Krylov.grade A g ≤ 1 := by
  have he : b = a := le_antisymm ((div_le_one ha).mp hk) hab
  subst b
  have hs := hB.apply_eq_smul (EuclideanSpace.single (0 : Fin 2) 1)
  have hv := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hs
  have hbeta : Lanczos.beta A g 0 = 0 := by
    simpa [Matrix.toLpLin_apply, Matrix.mulVec_single, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Lanczos.tridiag_apply] using hv
  have hz := (Lanczos.beta_eq_zero_iff (A := A) (b := g) 0).mp hbeta
  omega

/-- The actual full shifted residual vanishes at the Krylov grade. -/
theorem lanczos_shifted_residual_eq_zero_of_grade (hA : A.IsSymmetric) (hg : g ≠ 0)
    {m : ℕ} (hm : m + 1 = Krylov.grade A g) (y : Fin (m + 1) → ℝ) (lambda : ℝ)
    (hy : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i + lambda * y i =
      -(if i = 0 then ‖g‖ else 0)) :
    g + A (lanczosStep A g y) + lambda • lanczosStep A g y = 0 := by
  rw [lanczos_shifted_residual hA hg m y lambda hy,
    (Lanczos.beta_eq_zero_iff (A := A) (b := g) m).mpr hm.ge, zero_mul, zero_smul]

end Optimization.KrylovSubproblem

namespace Optimization.KrylovSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {H : E →L[ℝ] E} {g : E}
  [FiniteDimensional ℝ (Krylov.fullSubspace H.toLinearMap g)]

/-- A full-space upper Rayleigh bound and an upper shift bound control the norm
of the actual reduced stationary step from below. Positivity of the denominator
is proved from the nonempty positive definite compression. -/
theorem lanczos_stationary_norm_lower_bound (hH : H.IsSymmetric)
    {m : ℕ} (hm : m + 1 ≤ Krylov.grade H.toLinearMap g)
    {a b L lambda nu : ℝ} (ha : 0 < a) (hshift : lambda ≤ nu)
    (hupper : ∀ z, ⟪H z, z⟫_ℝ ≤ L * ‖z‖ ^ 2)
    (hB : (Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (m + 1) +
      lambda • 1)).IsSymmetricBoundedBy a b)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : ∀ i, (Lanczos.tridiag H.toLinearMap g (m + 1)).mulVec y i + lambda * y i =
      -(if i = 0 then ‖g‖ else 0)) :
    0 < L + nu ∧ ‖g‖ / (L + nu) ≤ ‖y‖ := by
  let Q := lanczosEmbedding H.toLinearMap g hm
  let T := Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (m + 1) + lambda • 1)
  have heq (x : EuclideanSpace ℝ (Fin (m + 1))) :
      ⟪T x, x⟫_ℝ = ⟪H (Q x), Q x⟫_ℝ + lambda * ‖x‖ ^ 2 := by
    have ht : Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (m + 1)) x =
        compressedHessian Q H x := by
      ext i
      exact (compressedHessian_lanczosEmbedding_apply hH rfl hm x i).symm
    simp only [T, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      Matrix.toEuclideanLin_one_apply, ht, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    change ⟪Q.toContinuousLinearMap.adjoint (H (Q x)), x⟫_ℝ + _ = _
    rw [ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hU (x : EuclideanSpace ℝ (Fin (m + 1))) : ⟪T x, x⟫_ℝ ≤ (L + nu) * ‖x‖ ^ 2 := by
    rw [heq]
    have h := hupper (Q x)
    rw [Q.norm_map] at h
    nlinarith [mul_le_mul_of_nonneg_right hshift (sq_nonneg ‖x‖)]
  have hUpos : 0 < L + nu := by
    have hlow := hB.le_re_inner (EuclideanSpace.single (0 : Fin (m + 1)) 1)
    have hu := hU (EuclideanSpace.single (0 : Fin (m + 1)) 1)
    simp only [PiLp.norm_single, norm_one, one_pow, mul_one,
      RCLike.re_to_real] at hlow hu
    exact ha.trans_le (hlow.trans hu)
  have hnorm : ‖T.toContinuousLinearMap‖ ≤ L + nu := by
    apply ContinuousLinearMap.norm_le_of_isSymmetricBoundedBy hUpos.le
    refine ⟨hB.isSymmetric, ?_, hU⟩
    intro x
    exact (mul_le_mul_of_nonneg_right (by linarith : -(L + nu) ≤ a)
      (sq_nonneg ‖x‖)).trans (hB.le_re_inner x)
  have hsys : T y = (-‖g‖) • EuclideanSpace.single 0 1 := by
    ext i
    by_cases hi : i = 0 <;>
      simpa only [T, Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, PiLp.smul_apply, PiLp.single_apply, hi, ite_true, ite_false,
        mul_one, mul_zero, neg_zero] using hy i
  refine ⟨hUpos, (div_le_iff₀ hUpos).mpr ?_⟩
  have hn : ‖T y‖ = ‖g‖ := by simp [hsys, norm_smul, PiLp.norm_single]
  calc ‖g‖ = ‖T y‖ := hn.symm
    _ ≤ ‖T.toContinuousLinearMap‖ * ‖y‖ := T.toContinuousLinearMap.le_opNorm y
    _ ≤ (L + nu) * ‖y‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖y‖ * (L + nu) := mul_comm _ _

end Optimization.KrylovSubproblem
