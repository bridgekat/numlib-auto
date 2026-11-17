/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.QuadratureInverse

/-!
# §3.5. Lanczos and CG as model reduction

The spectral distribution of a Hermitian operator and starting vector determines the moments
matched by the Lanczos compression. The same Gauss–Christoffel rule applied to the reciprocal
gives the squared CG energy error, scaled by the squared initial residual norm.

## Main definitions

* `LiesenStrakos.Chapter03.normalizedSpectralMeasure` assigns a probability weight to the
  spectral data of a nonzero starting vector.
* `LiesenStrakos.Chapter03.lanczosGaussRule` uses the eigenvalues of the Lanczos compression
  and the squared first components of its normalized eigenvectors.

## Main results

* `LiesenStrakos.Chapter03.lanczos_moment_matching` gives exactness through degree $2n-1$.
* `LiesenStrakos.Chapter03.remark_3_5_1` relates the first moment to the Rayleigh quotient.
* `LiesenStrakos.Chapter03.theorem_3_5_2` identifies the normalized CG error with the reciprocal
  quadrature error.
-/

open MeasureTheory Polynomial
open scoped ENNReal

namespace LiesenStrakos.Chapter03

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The measure in (3.5.3) of [liesen2013krylov] has weight
$|\langle y_j,v\rangle|^2/\|v\|^2$ at each eigenvalue $\lambda_j$, for $v\ne0$.
Weights at repeated eigenvalues add. -/
noncomputable def normalizedSpectralMeasure {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) :
    Measure ℝ :=
  ENNReal.ofReal (‖v‖ ^ 2)⁻¹ • Krylov.spectralMeasure hA rfl v

/-- The integral against the normalized spectral measure is the unnormalized integral divided
by $\|v\|^2$. -/
theorem integral_normalizedSpectralMeasure {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (v : E) (f : ℝ → ℝ) :
    ∫ t, f t ∂(normalizedSpectralMeasure hA v) =
      (‖v‖ ^ 2)⁻¹ * ∫ t, f t ∂(Krylov.spectralMeasure hA rfl v) := by
  rw [normalizedSpectralMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- The Gauss–Christoffel rule of the Lanczos tridiagonal matrix $T_n$ for $n>0$:
$\sum_j |(z_j)_1|^2 f(\theta_j)$, where $(\theta_j,z_j)$ are its orthonormal eigenpairs. -/
noncomputable def lanczosGaussRule (A : E →ₗ[𝕜] E) (v : E) {n : ℕ} (hn : 0 < n)
    (f : ℝ → ℝ) : ℝ :=
  ∑ j, ((Lanczos.tridiag_isHermitian A v n).eigenvectorBasis j ⟨0, hn⟩) ^ 2 *
    f ((Lanczos.tridiag_isHermitian A v n).eigenvalues j)

omit [FiniteDimensional 𝕜 E] in
private theorem mul_inv_norm_sq_assoc {v : E} (hv : v ≠ 0) (q : ℝ) :
    (‖v‖ ^ 2)⁻¹ * (‖v‖ ^ 2 * q) = q := by
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 hv)), one_mul]

/-- **Equation (3.5.6)** of [liesen2013krylov].
The $n$-node Lanczos quadrature rule matches every moment of order less than $2n$ of the
spectral measure of the normalized starting vector. -/
theorem lanczos_moment_matching {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {v : E} (hv : v ≠ 0) {n j : ℕ} (hn : 0 < n) (hgrade : n ≤ Krylov.grade A v)
    (hj : j < 2 * n) :
    ∫ t, t ^ j ∂(normalizedSpectralMeasure hA v) =
      lanczosGaussRule A v hn (fun t => t ^ j) := by
  have hdim := (Krylov.finrank_subspace A v n).trans (min_eq_left hgrade)
  have heq := Lanczos.gauss_quadrature hA rfl v hn hdim
    (f := X ^ j) (by simpa using hj)
  simp only [eval_pow, eval_X] at heq
  rw [integral_normalizedSpectralMeasure, heq,
    Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag hA v hn hdim]
  exact mul_inv_norm_sq_assoc hv _

/-- **Remark 3.5.1** of [liesen2013krylov].
The first moment of the normalized spectral measure is the Rayleigh quotient of the
starting vector. -/
theorem remark_3_5_1 {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) :
    ∫ t, t ∂(normalizedSpectralMeasure hA v) =
      RCLike.re (inner 𝕜 v (A v)) / ‖v‖ ^ 2 := by
  rw [integral_normalizedSpectralMeasure]
  have hm := congrArg RCLike.re (Krylov.inner_aeval_eq_integral hA rfl v (X : ℝ[X]))
  simp only [map_X, aeval_X, eval_X, RCLike.ofReal_re] at hm
  rw [← hm, div_eq_mul_inv, mul_comm]

/-- **Theorem 3.5.2** of [liesen2013krylov].
For positive definite Hermitian $A$, the squared CG energy error at a positive step $n$
through the grade, divided by the squared norm of the nonzero initial residual, is the
Gauss–Christoffel quadrature error for $\lambda \mapsto \lambda^{-1}$. -/
theorem theorem_3_5_2 {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive) (b x₀ xstar : E)
    (hstar : A xstar = b) (hr : b - A x₀ ≠ 0) {n : ℕ} (hn : 0 < n)
    (hgrade : n ≤ Krylov.grade A (b - A x₀)) :
    (energyNorm A (xstar - (CG.iterate A b x₀ n).x)) ^ 2 / ‖b - A x₀‖ ^ 2 =
      (∫ t, t⁻¹ ∂(normalizedSpectralMeasure hA.isSymmetric (b - A x₀))) -
        lanczosGaussRule A (b - A x₀) hn Inv.inv := by
  let r := b - A x₀
  let x := (CG.iterate A b x₀ n).x
  let K := Krylov.subspace A r n
  have hx : IsGalerkin A b x₀ K x := CG.isGalerkinIterate b x₀ hA n
  let z : K := ⟨x - x₀, hx.mem⟩
  let v : K := ⟨r, Krylov.self_mem_subspace A r hn⟩
  have hres : r - A (z : E) ∈ Kᗮ := by
    change (b - A x₀) - A (x - x₀) ∈ Kᗮ
    rw [← residual_eq_sub_apply_sub]
    exact hx.orth
  have hz : compression A K z = v := by
    have hp := (Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hres)
    rw [map_sub, K.orthogonalProjectionOnto_mem_subspace_eq_self v] at hp
    exact (sub_eq_zero.1 hp).symm
  have hu : A (xstar - x₀) = r := by rw [map_sub, hstar]
  have hdim : Module.finrank 𝕜 K = n :=
    (Krylov.finrank_subspace A r n).trans (min_eq_left hgrade)
  have hfull := Krylov.integral_inv_spectralMeasure_of_apply_eq hA.isSymmetric rfl hu
  have hred := Krylov.integral_inv_spectralMeasure_of_apply_eq
    (compression.isSymmetric A K hA.isSymmetric) hdim hz
  rw [← hu, ← hA.energyNorm_sq] at hfull
  rw [← hz, compression.inner_apply, ← hA.energyNorm_sq] at hred
  change (∫ t, t⁻¹ ∂(Krylov.spectralMeasure hA.isSymmetric rfl (A (xstar - x₀)))) =
    energyNorm A (xstar - x₀) ^ 2 at hfull
  rw [hu] at hfull
  have hquad := Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag hA.isSymmetric
    r hn hdim (fun t => t⁻¹)
  change (∫ t, t⁻¹ ∂(Krylov.spectralMeasure
    (compression.isSymmetric A K hA.isSymmetric) hdim v)) = _ at hquad
  rw [← hz] at hquad
  have hquad' : energyNorm A (x - x₀) ^ 2 = ‖r‖ ^ 2 * lanczosGaussRule A r hn Inv.inv :=
    hred.symm.trans hquad
  have hpy := IsGalerkin.energyNorm_sq_add hA hx hstar (y := x₀) (by simp)
  have hnorm : ‖r‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hr)
  change _ / ‖r‖ ^ 2 = _ - lanczosGaussRule A r hn Inv.inv
  rw [integral_normalizedSpectralMeasure, hfull]
  apply (div_eq_iff hnorm).2
  have hsolve : (‖r‖ ^ 2)⁻¹ * (energyNorm A (xstar - x₀)) ^ 2 * ‖r‖ ^ 2 =
      (energyNorm A (xstar - x₀)) ^ 2 := by
    rw [mul_comm (‖r‖ ^ 2)⁻¹, mul_assoc, inv_mul_cancel₀ hnorm, mul_one]
  rw [sub_mul, hsolve, mul_comm (lanczosGaussRule A r hn Inv.inv), ← hquad']
  linarith

end LiesenStrakos.Chapter03
