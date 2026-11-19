/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Interval.Finset.Fin
import Numlib.Krylov.Convergence.CGIterationLimit
import NumlibSurface.LiesenStrakos.Chapter05.Section06

/-!
# Liesen and Strakoš, §5.9: Rounding errors in conjugate gradients

The composite-polynomial convergence bound separates large eigenvalues from a spectral
interval containing the rest. The bound yields an exact-arithmetic iteration limit.
With rounding errors, the residual computed from an iterate may differ from the recursively
updated residual.

## Conventions

* The eigenvalues are indexed in decreasing order. The first $\ell$ entries are the largest
  $\ell$ eigenvalues, and the entry at index $\ell$ is the largest retained eigenvalue.

## Deviations from the source

* **Section 5.9** (generalization). The ceiling in the idealized iteration count is a natural
  number, and the residual gap is a module identity.

## Not formalized

* The finite-precision delay and attainable-accuracy estimates discussed in §§5.9.1–5.9.4
  require a model of rounding in the CG recurrence.
-/

open Finset

namespace LiesenStrakos.Chapter05

/-- **Equation (5.9.1)** of [liesen2013krylov]. For eigenvalues in decreasing order on
$\{0,\dots,N\}$, the **effective condition number** after discarding the first $\ell$ entries is
the eigenvalue at $\ell$ divided by the eigenvalue at $N$. A zero denominator gives zero.

**Generalization.** The total ratio accepts arbitrary real arrays, using descending order for
the source's spectral interpretation. -/
noncomputable def effectiveConditionNumber {N : ℕ} (μ : Fin (N + 1) → ℝ)
    (ℓ : Fin (N + 1)) : ℝ :=
  μ ℓ / μ (Fin.last N)

/-- **Theorem 5.9.1** of [liesen2013krylov]. Let $A$ be symmetric coercive of dimension $N+1$, let
$Ax=b$, and let $x_0$ be the initial approximation. Given a relative tolerance $\delta>0$ and
an integer $0\le \ell \le N$, put $\kappa_\ell$ equal to the ratio of the largest eigenvalue
remaining after removing $\ell$ largest eigenvalues to the smallest eigenvalue. After
$$n=\ell+\left\lceil \tfrac12\log(2/\delta)\sqrt{\kappa_\ell}\right\rceil$$
exact CG steps, $\|x-x_n\|_A/\|x-x_0\|_A\le\delta$. If the initial error is zero, the ratio is zero.
The ceiling is taken in the naturals.

**Generalization.** The natural ceiling allows every positive tolerance, with ceiling zero for
tolerances at least two. -/
theorem theorem_5_9_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive)
    {N : ℕ} (hN : Module.finrank 𝕜 E = N + 1) {b x x₀ : E} (hx : A x = b)
    (ℓ : Fin (N + 1)) {δ : ℝ} (hδ : 0 < δ) :
    let κ := effectiveConditionNumber (hA.isSymmetric.eigenvalues hN) ℓ
    let n := (ℓ : ℕ) + ⌈(1 / 2 : ℝ) * Real.log (2 / δ) * Real.sqrt κ⌉₊
    energyNorm A (x - (CG.iterate A b x₀ n).x) / energyNorm A (x - x₀) ≤ δ := by
  let μ := hA.isSymmetric.eigenvalues hN
  have hμ : Antitone μ := hA.isSymmetric.eigenvalues_antitone hN
  have hmin : 0 < μ (Fin.last N) := by
    have hp := hA.re_pos_of_hasEigenvalue (hA.isSymmetric.hasEigenvalue_eigenvalues hN (Fin.last N))
    simpa only [RCLike.ofReal_re] using hp
  have hle : μ (Fin.last N) ≤ μ ℓ := hμ (Fin.le_last ℓ)
  have hhigh (i : Fin (N + 1)) (hi : i ∈ Iio ℓ) : μ ℓ ≤ μ i :=
    hμ (le_of_lt (mem_Iio.mp hi))
  have hlow (i : Fin (N + 1)) (hi : i ∉ Iio ℓ) : μ i ∈ Set.Icc (μ (Fin.last N)) (μ ℓ) :=
    ⟨hμ (Fin.le_last i), hμ (le_of_not_gt (fun h => hi (mem_Iio.mpr h)))⟩
  simpa only [effectiveConditionNumber, Fin.card_Iio] using
    CG.energyNorm_error_le_of_iteration_limit hN hA hx hmin hle (Iio ℓ) hhigh hlow hδ

/-- **Section 5.9.3** of [liesen2013krylov]. The **recursive residual gap** at a computed
approximate solution $y$ is $(b-Ay)-\hat r$, where $\hat r$ is the recursively computed residual.

**Generalization.** The same difference is defined on modules over any semiring. -/
def recursiveResidualGap {𝕜 E : Type*} [Semiring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (A : E →ₗ[𝕜] E) (b y r : E) : E :=
  b - A y - r

/-- **Equations (5.9.4)–(5.9.6)** of [liesen2013krylov].
In the eigenbasis of a positive definite operator, the CG polynomial multiplies each initial
error component by its value at the corresponding eigenvalue. The normalized spectral weights
of the initial residual give the squared components and the energy norm of the error. -/
theorem cg_error_spectral_components {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetricCoercive) {N : ℕ} (hN : Module.finrank 𝕜 E = N)
    {b x x₀ : E} (hx : A x = b) (hr : b - A x₀ ≠ 0) {n : ℕ}
    (hn : n ≤ Krylov.grade A (b - A x₀)) :
    let r₀ := b - A x₀
    let e := x - (CG.iterate A b x₀ n).x
    let μ := hA.isSymmetric.eigenvalues hN
    let B := hA.isSymmetric.eigenvectorBasis hN
    let w (i : Fin N) := ‖B.repr r₀ i‖ ^ 2 / ‖r₀‖ ^ 2
    let p := cgIterationPolynomial A r₀ n
    (∀ i, ‖B.repr e i‖ ^ 2 = (p.eval (μ i)) ^ 2 * (‖r₀‖ ^ 2 / (μ i) ^ 2) * w i) ∧
    energyNorm A e ^ 2 = ‖r₀‖ ^ 2 * ∑ i, w i / μ i * (p.eval (μ i)) ^ 2 ∧
    e = ∑ i, (((p.eval (μ i) : ℝ) : 𝕜) * B.repr (x - x₀) i) • B i := by
  let r₀ := b - A x₀
  let e := x - (CG.iterate A b x₀ n).x
  let μ := hA.isSymmetric.eigenvalues hN
  let B := hA.isSymmetric.eigenvectorBasis hN
  let w (i : Fin N) := ‖B.repr r₀ i‖ ^ 2 / ‖r₀‖ ^ 2
  let p := cgIterationPolynomial A r₀ n
  have hμ (i : Fin N) : 0 < μ i := by
    simpa only [RCLike.ofReal_re] using
      hA.re_pos_of_hasEigenvalue (hA.isSymmetric.hasEigenvalue_eigenvalues hN i)
  have hpol : e = Polynomial.aeval A (p.map (algebraMap ℝ 𝕜)) (x - x₀) :=
    Krylov.error_eq_aeval_of_injective hA.isCoercive.injective hx
      ((CG.isGalerkinIterate b x₀ hA n).residual_eq_aeval_normalized_charpoly hA hn)
  have he (i : Fin N) : B.repr e i = ((p.eval (μ i) : ℝ) : 𝕜) * B.repr (x - x₀) i := by
    rw [hpol, hA.isSymmetric.repr_aeval_apply hN]
    change (p.map (algebraMap ℝ 𝕜)).eval (μ i : 𝕜) * _ = _
    rw [← RCLike.algebraMap_eq_ofReal, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hr₀ : r₀ = A (x - x₀) := by rw [map_sub, hx]
  have hz (i : Fin N) : B.repr r₀ i = (μ i : 𝕜) * B.repr (x - x₀) i := by
    rw [hr₀]
    exact B.repr_apply_of_apply_eq_smul (hA.isSymmetric.apply_eigenvectorBasis hN) (x - x₀) i
  have hcomp (i : Fin N) :
      ‖B.repr e i‖ ^ 2 = (p.eval (μ i)) ^ 2 * (‖r₀‖ ^ 2 / (μ i) ^ 2) * w i := by
    rw [he]
    dsimp [w]
    rw [hz]
    simp only [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    field_simp [(hμ i).ne', norm_ne_zero_iff.2 hr]
    rw [mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 hr)]
  refine ⟨hcomp, ?_, ?_⟩
  · change energyNorm A e ^ 2 = ‖r₀‖ ^ 2 * ∑ i, w i / μ i * (p.eval (μ i)) ^ 2
    rw [hA.energyNorm_sq, hA.isSymmetric.re_inner_apply_self_eq_sum hN, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change μ i * ‖B.repr e i‖ ^ 2 = _
    rw [hcomp]
    field_simp [(hμ i).ne']
  · change e = ∑ i, (((p.eval (μ i) : ℝ) : 𝕜) * B.repr (x - x₀) i) • B i
    simp_rw [← he]
    exact (B.sum_repr e).symm

end LiesenStrakos.Chapter05
