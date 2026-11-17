/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Quadrature

/-!
# Reciprocal spectral moments

The reciprocal moment of the spectral measure of $v=Au$ for a symmetric operator $A$ is the
real part of $\langle v,u\rangle$. Eigenvectors in the kernel have zero weight in this measure.

## Main results

* `Krylov.integral_inv_spectralMeasure_of_apply_eq` evaluates the reciprocal spectral moment.
-/

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- For symmetric $A$ and $Au=v$, the integral of $\lambda^{-1}$ against the spectral
measure of $(A,v)$ equals $\operatorname{Re}\langle v,u\rangle$. A zero eigenvalue contributes
zero weight because $v$ is in the range of $A$. -/
theorem integral_inv_spectralMeasure_of_apply_eq {N : ℕ} {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hN : Module.finrank 𝕜 E = N) {u v : E} (hu : A u = v) :
    ∫ t, t⁻¹ ∂(spectralMeasure hA hN v) = RCLike.re (inner 𝕜 v u) := by
  let Y := hA.eigenvectorBasis hN
  rw [integral_spectralMeasure, ← Y.sum_inner_mul_inner, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  let μ := hA.eigenvalues hN i
  let z := inner 𝕜 (Y i) u
  have hv : inner 𝕜 (Y i) v = (μ : 𝕜) * z := by
    rw [← hu, ← hA, hA.apply_eigenvectorBasis hN i, inner_smul_left, RCLike.conj_ofReal]
  change ‖inner 𝕜 (Y i) v‖ ^ 2 * μ⁻¹ = RCLike.re (inner 𝕜 v (Y i) * z)
  rw [← inner_conj_symm v (Y i), hv, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, RCLike.ofReal_re,
    norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
  rcases eq_or_ne μ 0 with h | h
  · simp [h]
  · field_simp

end Krylov
