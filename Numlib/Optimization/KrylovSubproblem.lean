import Numlib.LinearAlgebra.Matrix.HessenbergSolutionDecay
import Numlib.Optimization.QuadraticSubproblem
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Preconditioned
import Numlib.Order.Filter.Extr
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Quadratic subproblems on isometric subspaces

Compression by an isometric embedding preserves the quadratic model and every radial
regularizer. Thus subspace minimizers are exactly reduced minimizers, and their stationarity
is the projection of the original shifted residual. The Lanczos residual formulas use the
existing three-term recurrence and include exact breakdown at the grade.
-/

noncomputable section
open scoped InnerProductSpace
open Set Metric
namespace Optimization.KrylovSubproblem
open QuadraticSubproblem
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

/-- The Hessian compressed to an isometric coordinate space. -/
def compressedHessian (Q : F →ₗᵢ[ℝ] E) (H : E →L[ℝ] E) : F →L[ℝ] F :=
  Q.toContinuousLinearMap.adjoint ∘L H ∘L Q.toContinuousLinearMap

/-- Isometric compression preserves symmetry. -/
theorem compressedHessian_isSymmetric (Q : F →ₗᵢ[ℝ] E) {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) : (compressedHessian Q H).IsSymmetric := by
  intro x y
  change ⟪Q.toContinuousLinearMap.adjoint (H (Q x)), y⟫_ℝ =
    ⟪x, Q.toContinuousLinearMap.adjoint (H (Q y))⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact hH (Q x) (Q y)

/-- The compressed model has exactly the original value at the represented point. -/
@[simp] theorem quadratic_map (Q : F →ₗᵢ[ℝ] E) (g : E) (H : E →L[ℝ] E) (s : F) :
    quadratic g H (Q s) =
      quadratic (Q.toContinuousLinearMap.adjoint g) (compressedHessian Q H) s := by
  simp [quadratic, compressedHessian, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- Every radial exponent and coefficient transport through an isometric embedding. -/
@[simp] theorem powerRegularizedQuadratic_map (Q : F →ₗᵢ[ℝ] E) (g : E)
    (H : E →L[ℝ] E) (sigma r : ℝ) (s : F) :
    powerRegularizedQuadratic g H sigma r (Q s) =
      powerRegularizedQuadratic (Q.toContinuousLinearMap.adjoint g)
        (compressedHessian Q H) sigma r s := by
  simp [powerRegularizedQuadratic]

/-- Arbitrary represented feasible sets have exactly the reduced quadratic minimizers. -/
theorem quadratic_isMinOn_image_iff (Q : F →ₗᵢ[ℝ] E) (g : E) (H : E →L[ℝ] E)
    (K : Set F) (s : F) :
    IsMinOn (quadratic g H) (Q '' K) (Q s) ↔
      IsMinOn (quadratic (Q.toContinuousLinearMap.adjoint g) (compressedHessian Q H)) K s := by
  simpa only [Function.comp_def, quadratic_map] using
    isMinOn_image_iff (quadratic g H) Q K s

/-- Arbitrary represented feasible sets have exactly the reduced regularized minimizers. -/
theorem powerRegularized_isMinOn_image_iff (Q : F →ₗᵢ[ℝ] E) (g : E)
    (H : E →L[ℝ] E) (sigma r : ℝ) (K : Set F) (s : F) :
    IsMinOn (powerRegularizedQuadratic g H sigma r) (Q '' K) (Q s) ↔
      IsMinOn (powerRegularizedQuadratic (Q.toContinuousLinearMap.adjoint g)
        (compressedHessian Q H) sigma r) K s := by
  simpa only [Function.comp_def, powerRegularizedQuadratic_map] using
    isMinOn_image_iff (powerRegularizedQuadratic g H sigma r) Q K s

omit [CompleteSpace E] [CompleteSpace F] in
/-- The represented reduced ball is precisely the original ball intersected with the range. -/
theorem image_closedBall (Q : F →ₗᵢ[ℝ] E) (delta : ℝ) :
    Q '' closedBall 0 delta = closedBall 0 delta ∩ Set.range Q := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨by simpa using hs, ⟨s, rfl⟩⟩
  · rintro ⟨hx, s, rfl⟩
    exact ⟨s, by simpa using hx, rfl⟩

/-- Trust-region and radial regularization minimizers in an isometric subspace are exactly
those of the compressed Hessian and gradient. No stationarity or optimizer is assumed. -/
theorem subspaceMinimizer_iff_reduced (Q : F →ₗᵢ[ℝ] E) (g : E) (H : E →L[ℝ] E)
    (delta sigma r : ℝ) (s : F) :
    (IsMinOn (quadratic g H) (closedBall 0 delta ∩ Set.range Q) (Q s) ↔
      IsMinOn (quadratic (Q.toContinuousLinearMap.adjoint g) (compressedHessian Q H))
        (closedBall 0 delta) s) ∧
    (IsMinOn (powerRegularizedQuadratic g H sigma r) (Set.range Q) (Q s) ↔
      IsMinOn (powerRegularizedQuadratic (Q.toContinuousLinearMap.adjoint g)
        (compressedHessian Q H) sigma r) Set.univ s) := by
  refine ⟨?_, ?_⟩
  · rw [← image_closedBall]
    exact quadratic_isMinOn_image_iff Q g H _ s
  · simpa only [Set.image_univ] using
      powerRegularized_isMinOn_image_iff Q g H sigma r Set.univ s

/-- Reduced shifted stationarity is the vanishing projection of the actual full residual. -/
theorem reduced_stationary_iff (Q : F →ₗᵢ[ℝ] E) (g : E) (H : E →L[ℝ] E)
    (lambda : ℝ) (s : F) :
    Q.toContinuousLinearMap.adjoint g + compressedHessian Q H s + lambda • s = 0 ↔
      Q.toContinuousLinearMap.adjoint (g + H (Q s) + lambda • Q s) = 0 := by
  have hQ : Q.toContinuousLinearMap.adjoint (Q s) = s := by
    exact congrArg (fun A : F →L[ℝ] F => A s) Q.adjoint_comp_self
  simp only [map_add, map_smul, compressedHessian, ContinuousLinearMap.comp_apply, hQ]
  rfl

end Optimization.KrylovSubproblem

namespace Optimization.KrylovSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A reduced coefficient vector represents the actual Lanczos expansion in the original
space. The basis vectors and coefficients are those of the existing Lanczos process. -/
def lanczosStep (A : E →ₗ[ℝ] E) (g : E) {m : ℕ} (y : Fin m → ℝ) : E :=
  ∑ j, y j • Arnoldi.vec A g j

/-- The existing Arnoldi orthonormal basis, bundled as an isometric parametrization of
its Krylov subspace. -/
def lanczosEmbedding (A : E →ₗ[ℝ] E) (g : E)
    [FiniteDimensional ℝ (Krylov.fullSubspace A g)] {m : ℕ}
    (hm : m ≤ Krylov.grade A g) : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] E :=
  (Krylov.subspace A g m).subtypeₗᵢ.comp
    (Arnoldi.orthonormalBasis A g hm).repr.symm.toLinearIsometry

/-- The isometric parametrization uses the actual Lanczos expansion coefficients. -/
theorem lanczosEmbedding_apply (A : E →ₗ[ℝ] E) (g : E)
    [FiniteDimensional ℝ (Krylov.fullSubspace A g)] {m : ℕ}
    (hm : m ≤ Krylov.grade A g) (y : EuclideanSpace ℝ (Fin m)) :
    lanczosEmbedding A g hm y = lanczosStep A g y := by
  have h := congrArg (fun z : Krylov.subspace A g m => (z : E))
    ((Arnoldi.orthonormalBasis A g hm).sum_repr_symm y)
  change (((Arnoldi.orthonormalBasis A g hm).repr.symm y : Krylov.subspace A g m) : E) = _
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Arnoldi.coe_orthonormalBasis_apply,
    lanczosStep] using h.symm

/-- The range of the Lanczos parametrization is exactly the existing Krylov subspace. -/
theorem range_lanczosEmbedding (A : E →ₗ[ℝ] E) (g : E)
    [FiniteDimensional ℝ (Krylov.fullSubspace A g)] {m : ℕ}
    (hm : m ≤ Krylov.grade A g) :
    Set.range (lanczosEmbedding A g hm) = Krylov.subspace A g m := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((Arnoldi.orthonormalBasis A g hm).repr.symm y).property
  · intro hx
    refine ⟨(Arnoldi.orthonormalBasis A g hm).repr ⟨x, hx⟩, ?_⟩
    change (((Arnoldi.orthonormalBasis A g hm).repr.symm
      ((Arnoldi.orthonormalBasis A g hm).repr ⟨x, hx⟩) : Krylov.subspace A g m) : E) = x
    rw [LinearIsometryEquiv.symm_apply_apply]

/-- The full shifted residual is exactly the last Lanczos direction times the final reduced
coordinate. The reduced system is an explicit algebraic premise, not a residual oracle. -/
theorem lanczos_shifted_residual {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) {g : E}
    (hg : g ≠ 0) (m : ℕ) (y : Fin (m + 1) → ℝ) (lambda : ℝ)
    (hy : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i + lambda * y i =
      -(if i = 0 then ‖g‖ else 0)) :
    g + A (lanczosStep A g y) + lambda • lanczosStep A g y =
      (Lanczos.beta A g m * y (Fin.last m)) • Arnoldi.vec A g (m + 1) := by
  have hstart : (∑ i : Fin (m + 1), (if i = 0 then ‖g‖ else 0) • Arnoldi.vec A g i) = g := by
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.val_zero]
    rw [Arnoldi.vec_zero A g hg, smul_smul]
    change (‖g‖ * ‖g‖⁻¹) • g = g
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_smul]
  have hsum : (∑ i : Fin (m + 1),
      ((Lanczos.tridiag A g (m + 1)).mulVec y i + lambda * y i) • Arnoldi.vec A g i) = -g := by
    simp_rw [hy, neg_smul]
    rw [Finset.sum_neg_distrib, hstart]
  have hrec : A (lanczosStep A g y) =
      (∑ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i • Arnoldi.vec A g i) +
        (Lanczos.beta A g m * y (Fin.last m)) • Arnoldi.vec A g (m + 1) := by
    simpa only [lanczosStep, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_real_eq_id,
      Matrix.map_id, id_eq] using Lanczos.apply_sum g hA m y
  rw [hrec]
  have he : (∑ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i • Arnoldi.vec A g i) +
      lambda • lanczosStep A g y = -g := by
    simpa only [add_smul, Finset.sum_add_distrib, lanczosStep,
      Finset.smul_sum, smul_smul] using hsum
  calc
    _ = (g + ((∑ i : Fin (m + 1),
        (Lanczos.tridiag A g (m + 1)).mulVec y i • Arnoldi.vec A g i) +
        lambda • lanczosStep A g y)) +
        (Lanczos.beta A g m * y (Fin.last m)) • Arnoldi.vec A g (m + 1) := by abel
    _ = _ := by rw [he, add_neg_cancel, zero_add]

/-- The exact full residual norm before breakdown, and at breakdown itself. The latter
case follows from the zero Lanczos coefficient rather than assigning a norm to a zero basis
vector. -/
theorem lanczos_shifted_residual_norm {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) {g : E}
    (hg : g ≠ 0) [FiniteDimensional ℝ (Krylov.fullSubspace A g)]
    (m : ℕ) (hm : m + 1 ≤ Krylov.grade A g) (y : Fin (m + 1) → ℝ) (lambda : ℝ)
    (hy : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i + lambda * y i =
      -(if i = 0 then ‖g‖ else 0)) :
    ‖g + A (lanczosStep A g y) + lambda • lanczosStep A g y‖ =
      Lanczos.beta A g m * |y (Fin.last m)| := by
  rw [lanczos_shifted_residual hA hg m y lambda hy, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Lanczos.beta_nonneg A g m)]
  rcases lt_or_eq_of_le hm with h | h
  · rw [Arnoldi.norm_vec_eq_one_of_lt_grade A g h, mul_one]
  · rw [(Lanczos.beta_eq_zero_iff (A := A) (b := g) m).mpr h.ge]
    simp

/-- A symmetric preconditioned Krylov space stays metric-orthogonal to every generalized
eigenspace missed by its initial dual gradient. No extremality of the eigenvalue is needed. -/
theorem fullSubspace_le_metric_orthogonal {H M Minv : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (hM : Krylov.IsPreconditioner M Minv)
    (V : Submodule ℝ E) (mu : ℝ) (hV : ∀ v ∈ V, H v = mu • M v)
    {g : E} (hg : ∀ v ∈ V, ⟪g, v⟫_ℝ = 0) :
    Krylov.fullSubspace (Minv ∘ₗ H) (Minv g) ≤ (V.map M)ᗮ := by
  apply Krylov.fullSubspace_le_of_mem_invtSubmodule
  · intro x hx
    apply ((V.map M).mem_orthogonal' _).mpr
    rintro _ ⟨v, hv, rfl⟩
    have hzero := (((V.map M).mem_orthogonal' _).mp hx) (M v) ⟨v, hv, rfl⟩
    change ⟪Minv (H x), M v⟫_ℝ = 0
    rw [hM.isSymmetric_inv, hM.inv_apply, hH, hV v hv, real_inner_smul_right, hzero, mul_zero]
  · apply ((V.map M).mem_orthogonal' _).mpr
    rintro _ ⟨v, hv, rfl⟩
    rw [hM.isSymmetric_inv, hM.inv_apply]
    exact hg v hv

/-- Missing a generalized eigenspace reduces the maximum Krylov grade by its entire
dimension, including repeated eigenvalues. -/
theorem grade_add_finrank_le_of_metric_orthogonal [FiniteDimensional ℝ E]
    {H M Minv : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (hM : Krylov.IsPreconditioner M Minv)
    (V : Submodule ℝ E) (mu : ℝ) (hV : ∀ v ∈ V, H v = mu • M v)
    {g : E} (hg : ∀ v ∈ V, ⟪g, v⟫_ℝ = 0) :
    Krylov.grade (Minv ∘ₗ H) (Minv g) + Module.finrank ℝ V ≤ Module.finrank ℝ E := by
  have hle := Submodule.finrank_mono (fullSubspace_le_metric_orthogonal hH hM V mu hV hg)
  have hsum := (V.map M).finrank_add_finrank_orthogonal
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective M
    ⟨hM.isSymmetricCoercive.isCoercive.injective, fun x => ⟨Minv x, hM.apply_inv x⟩⟩
  have hdim : Module.finrank ℝ (V.map M) = Module.finrank ℝ V := e.finrank_map_eq V
  change Krylov.grade (Minv ∘ₗ H) (Minv g) ≤ Module.finrank ℝ (V.map M)ᗮ at hle
  omega

end Optimization.KrylovSubproblem

namespace Optimization.KrylovSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : E →ₗ[ℝ] E} {g : E} [FiniteDimensional ℝ (Krylov.fullSubspace A g)]

/-- Every Lanczos off-diagonal coefficient is bounded by an operator bound, including
breakdown. The bound uses the same inner product as the Lanczos construction. -/
theorem lanczos_beta_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖A z‖ ≤ C * ‖z‖) (m : ℕ) (hm : m + 1 ≤ Krylov.grade A g) :
    Lanczos.beta A g m ≤ C := by
  rcases lt_or_eq_of_le hm with hm | hm
  · have he : ⟪Arnoldi.vec A g (m + 1), A (Arnoldi.vec A g m)⟫_ℝ =
        Lanczos.beta A g m := by
      simpa only [Arnoldi.coeff, RCLike.ofReal_real_eq_id, id_eq] using
        (Lanczos.coe_beta A g m).symm
    calc Lanczos.beta A g m = |⟪Arnoldi.vec A g (m + 1),
        A (Arnoldi.vec A g m)⟫_ℝ| := by rw [he, abs_of_nonneg (Lanczos.beta_nonneg A g m)]
      _ ≤ ‖Arnoldi.vec A g (m + 1)‖ * ‖A (Arnoldi.vec A g m)‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * (C * 1) := by
        simp only [Arnoldi.norm_vec_eq_one_of_lt_grade A g hm, one_mul, mul_one]
        simpa only [Arnoldi.norm_vec_eq_one_of_lt_grade A g (by omega : m < Krylov.grade A g),
          mul_one] using hC (Arnoldi.vec A g m)
      _ = C := by ring
  · rw [(Lanczos.beta_eq_zero_iff (A := A) (b := g) m).mpr hm.ge]
    exact hC0

/-- The actual Lanczos shifted residual satisfies a Chebyshev bound. Quadratic-form
bounds `a,b` describe the shifted compression itself; the estimate applies to any
reduced stationary step, with its actual norm bounded by `R`. It remains valid at the
grade and for condition number one. It is valid in an energy inner product as well as
in the original Euclidean metric. -/
theorem lanczos_subproblem_residual_bound (hA : A.IsSymmetric) (hg : g ≠ 0)
    {C R a b : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖A z‖ ≤ C * ‖z‖)
    (ha : 0 < a) (hab : a ≤ b) (m : ℕ) (hm : m + 1 ≤ Krylov.grade A g)
    (lambda : ℝ) (y : EuclideanSpace ℝ (Fin (m + 1))) (hR : ‖y‖ ≤ R)
    (hB : (Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1) +
      lambda • 1)).IsSymmetricBoundedBy a b)
    (hy : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i +
      lambda * y i = -(if i = 0 then ‖g‖ else 0)) :
    ‖g + A (lanczosStep A g y) + lambda • lanczosStep A g y‖ ≤
      2 * C * (b / a) * R *
        ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ m := by
  have hsys : Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1) + lambda • 1) y =
      (-‖g‖) • EuclideanSpace.single 0 1 := by
    ext i
    by_cases hi : i = 0 <;>
      simpa only [hi, ite_true, ite_false, mul_one, mul_zero, neg_zero,
      Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, PiLp.smul_apply, PiLp.single_apply] using hy i
  have hshape := (Lanczos.tridiag_isTridiagonal A g (m + 1)).isUpperHessenberg.add_smul_one lambda
  have hlast := hshape.solution_coordinate_le ha hab hB hsys (Fin.last m)
  have hκ : 1 ≤ b / a := (one_le_div ha).mpr hab
  have hrate : 0 ≤ (Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1) := by
    have hs : 1 ≤ Real.sqrt (b / a) := (Real.one_le_sqrt).mpr hκ
    positivity
  have hR0 : 0 ≤ R := (norm_nonneg y).trans hR
  rw [lanczos_shifted_residual_norm hA hg m hm y lambda hy]
  calc Lanczos.beta A g m * |y (Fin.last m)| ≤
      C * (2 * ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ m * ‖y‖) :=
        mul_le_mul (lanczos_beta_le hC0 hC m hm) hlast (abs_nonneg _) hC0
    _ ≤ C * (2 * ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ m * R) := by
      gcongr
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_right hκ
        (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * C) hR0) (pow_nonneg hrate m))
      nlinarith

end Optimization.KrylovSubproblem
