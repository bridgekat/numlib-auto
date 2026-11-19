/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Interval.Finset.Fin
import Numlib.Approximation.FiniteMinimaxWeights
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Convergence.CGError
import Numlib.Krylov.Convergence.CGSpectrum
import NumlibSurface.LiesenStrakos.Chapter03.Section05

/-!
# Liesen and Strakoš, §5.6: Conjugate gradients in exact arithmetic

In exact arithmetic conjugate gradients decreases the energy norm of the error by an
amount measured by the squared residual norm and the step length. The search directions
have explicit expansions in the orthogonal residuals. The polynomial formulation also yields
bounds in terms of the spectrum.

## Main results

* Theorem 5.6.1, `LiesenStrakos.Chapter05.theorem_5_6_1`: energy errors telescope over the
  intervening CG steps.
* Corollary 5.6.2, `LiesenStrakos.Chapter05.corollary_5_6_2_spectral`: energy error is the
  difference of inverse spectral moments with the Gauss quadrature weights.
* Lemma 5.6.4, `LiesenStrakos.Chapter05.lemma_5_6_4_i` and related results: expansions, norms
  and inner products of residuals and directions.
* Theorem 5.6.6, `LiesenStrakos.Chapter05.theorem_5_6_6_sharp`: an initial error that attains
  the spectral minimax bound.
* Corollary 5.6.7, `LiesenStrakos.Chapter05.corollary_5_6_7`: the Chebyshev bound for CG.

## Deviations from the source

* **Theorems 5.6.1, 5.6.5 and 5.6.6** (generalization). The energy identities and bounds use
  total CG sequences, including the terminal update or stationary tail where specified.
* **Corollary 5.6.2** (generalization). The inverse moment formula holds through the grade even
  when the grade is smaller than the ambient dimension.
* **Theorem 5.6.3** (correction). Inverse-eigenvalue factors weight each summand once, as required
  by the relation between the error and the residual.
* **Corollary 5.6.7** (generalization). The endpoints can be spectral bounds on a symmetric
  operator in an arbitrary real or complex inner product space.

-/

open Finset Krylov Polynomial

namespace LiesenStrakos.Chapter05

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ x : E}

local notation "r[" j "]" => CG.State.r (CG.iterate A b x₀ j)
local notation "p[" j "]" => CG.State.p (CG.iterate A b x₀ j)
local notation "x[" j "]" => CG.State.x (CG.iterate A b x₀ j)
local notation "a[" j "]" => CG.alpha A (CG.iterate A b x₀ j)
local notation "r₀" => b - A x₀
local notation "d₀" => grade A (b - A x₀)

/-- **Equation (5.6.3)** of [liesen2013krylov]. The **CG iteration polynomial** at step $n$
is the characteristic polynomial of the $n$-th Lanczos tridiagonal $T_n$ divided by its
constant term. When that term is zero this expression gives the zero polynomial.

**Generalization.** The characteristic polynomial is normalized using total division. The CG
interpretation applies through the grade under the positive definiteness hypothesis. -/
noncomputable abbrev cgIterationPolynomial (A : E →ₗ[𝕜] E) (r : E) (n : ℕ) : ℝ[X] :=
  Lanczos.normalizedCharpoly A r n

/-- **Theorem 5.6.1** of [liesen2013krylov]. Let $A$ be symmetric coercive, $Ax=b$, and
$k\le n$. For the CG iterates $x_k,x_n$ from $x_0$, one has
$$\|x-x_k\|_A^2=\sum_{j=k}^{n-1}\operatorname{Re}(\alpha_j)\|r_j\|^2+\|x-x_n\|_A^2.$$
The identity also holds after exact termination, when subsequent residuals vanish.

**Generalization.** The identity includes equal indices and indices beyond the grade using the
total CG recurrence. -/
theorem theorem_5_6_1 (hA : A.IsSymmetricCoercive) (hx : A x = b) {k n : ℕ} (hkn : k ≤ n) :
    energyNorm A (x - x[k]) ^ 2 =
      (∑ j ∈ Ico k n, RCLike.re a[j] * ‖r[j]‖ ^ 2) + energyNorm A (x - x[n]) ^ 2 :=
  CG.energyNorm_error_sq_sub_eq_sum_Ico b x₀ hA hx hkn

/-- **Theorem 5.6.1** of [liesen2013krylov], one-step identity. For symmetric coercive $A$,
solution $x$ and CG iterates from $x_0$, the difference of the squared energy errors at steps
$j$ and $j+1$ is $\operatorname{Re}(\alpha_j)\|r_j\|^2$.

**Generalization.** The identity holds also on the stationary tail after convergence. -/
theorem theorem_5_6_1_one_step (hA : A.IsSymmetricCoercive) (hx : A x = b) (n : ℕ) :
    energyNorm A (x - x[n]) ^ 2 - energyNorm A (x - x[n + 1]) ^ 2 =
      RCLike.re a[n] * ‖r[n]‖ ^ 2 :=
  CG.energyNorm_error_sq_sub b x₀ hA hx n

/-- **Corollary 5.6.2** of [liesen2013krylov], equations (5.6.13). Let $A$ be symmetric
coercive, $Ax=b$, and $d$ the grade of $r_0$ in a finite-dimensional full Krylov space.
For $n \le d$, the squared energy error is
$$\|x-x_n\|_A^2=\sum_{j=n}^{d-1}\operatorname{Re}(\alpha_j)\|r_j\|^2
 =\|r_0\|^2\big((T_d^{-1}e_1,e_1)-(T_n^{-1}e_1,e_1)\big).$$
The empty $T_0$ has contribution zero. In the full-grade setting of the book, $d=N$.

**Reading.** Final grade replaces ambient dimension and allows step zero.
-/
theorem corollary_5_6_2 [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hA : A.IsSymmetricCoercive) (hx : A x = b) {n : ℕ} (hn : n ≤ d₀) :
    energyNorm A (x - x[n]) ^ 2 = ∑ j ∈ Ico n d₀, RCLike.re a[j] * ‖r[j]‖ ^ 2 ∧
      energyNorm A (x - x[n]) ^ 2 = ‖r₀‖ ^ 2 *
        (Lanczos.tridiagInvFirst A r₀ d₀ - Lanczos.tridiagInvFirst A r₀ n) :=
  ⟨CG.energyNorm_error_sq_eq_sum b x₀ hA hx n,
    CG.energyNorm_error_sq_eq_sub_inner_inv hA hx hn⟩

/-- **Corollary 5.6.2**, formula (5.6.14) of [liesen2013krylov].
The squared CG energy error is $\|r_0\|^2$ times the difference of the inverse spectral moments,
using the normalized initial residual weights for $A$ and the first-coordinate weights for $T_n$.

**Generalization.** The formula holds through the grade of $r_0$, which may be smaller than the
ambient dimension. -/
theorem corollary_5_6_2_spectral [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetricCoercive) {b x₀ x : E} (hx : A x = b) (hr : b - A x₀ ≠ 0) {N n : ℕ}
    (hN : Module.finrank 𝕜 E = N) (hpos : 0 < n) (hn : n ≤ Krylov.grade A (b - A x₀)) :
    let r := b - A x₀
    let ω (i : Fin N) := ‖inner 𝕜 (hA.isSymmetric.eigenvectorBasis hN i) r‖ ^ 2 / ‖r‖ ^ 2
    let μ := hA.isSymmetric.eigenvalues hN
    energyNorm A (x - (CG.iterate A b x₀ n).x) ^ 2 =
      ‖r‖ ^ 2 * ((∑ i, ω i * (μ i)⁻¹) -
        LiesenStrakos.Chapter03.lanczosGaussRule A r hpos Inv.inv) := by
  subst N
  let r := b - A x₀
  have h := LiesenStrakos.Chapter03.theorem_3_5_2 hA b x₀ x hx hr hpos hn
  rw [LiesenStrakos.Chapter03.integral_normalizedSpectralMeasure,
    Krylov.integral_spectralMeasure, Finset.mul_sum] at h
  have hnorm : ‖r‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hr)
  dsimp only
  rw [mul_comm (‖b - A x₀‖ ^ 2)]
  apply (div_eq_iff hnorm).1
  simpa only [div_eq_inv_mul, mul_assoc] using h

/-- **Theorem 5.6.3** of [liesen2013krylov]. Let $A$ be symmetric coercive and finite dimensional,
$Ax=b$, and let $n$ be at most the grade of $r_0=b-Ax_0$. Write $\mu_i$ and $u_i$ for the
eigenvalues and orthonormal eigenvectors of $A$, $w_i=|\langle u_i,r_0\rangle|^2$, and
$q_i=\prod_j(1-\mu_i/\theta_j)$ for the $n$-th Ritz values $\theta_j$. The squared residual norm
is $\sum_i q_i^2 w_i$, the squared Euclidean error norm is $\sum_i(q_i/\mu_i)^2 w_i$, and
the squared energy error norm is $\sum_i\mu_i(q_i/\mu_i)^2 w_i$.

**Correction.** In the printed Euclidean and energy expressions, the inverse-eigenvalue
weight appears inside every Ritz factor. Since the error is $A^{-1}r_n$, the factors
$\mu_i^{-2}$ and $\mu_i^{-1}$ each apply once per spectral summand. The weights $w_i$ here
absorb the common factor $\|r_0\|^2$, and the identities also hold below full grade. -/
theorem theorem_5_6_3 [FiniteDimensional 𝕜 E] (hA : A.IsSymmetricCoercive)
    {N : ℕ} (hN : Module.finrank 𝕜 E = N) (hx : A x = b) {n : ℕ} (hn : n ≤ d₀) :
    let μ := hA.isSymmetric.eigenvalues hN
    let θ := (Lanczos.tridiag_isHermitian A (b - A x₀) n).eigenvalues
    let q (i : Fin N) := ∏ j, (1 - μ i / θ j)
    let w (i : Fin N) := ‖(hA.isSymmetric.eigenvectorBasis hN).repr (b - A x₀) i‖ ^ 2
    ‖r[n]‖ ^ 2 = ∑ i, q i ^ 2 * w i ∧
      ‖x - x[n]‖ ^ 2 = ∑ i, (q i / μ i) ^ 2 * w i ∧
      energyNorm A (x - x[n]) ^ 2 = ∑ i, μ i * (q i / μ i) ^ 2 * w i := by
  simpa only [CG.residual_eq] using
    (CG.isGalerkinIterate b x₀ hA n).squared_norms_eq_sum_eigenvalues hA hN hx hn

section Directions

variable [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- **Lemma 5.6.4(1)** of [liesen2013krylov]. Before the grade of the initial residual, the $n$-th
CG direction is a sum of the previous and current residuals,
$$p_n=\|r_n\|^2\sum_{j=0}^n\|r_j\|^{-2}r_j.$$

**Generalization.** This direction identity comes from the recurrence and does not require
positive definiteness. -/
theorem lemma_5_6_4_i {n : ℕ} (hn : n < d₀) :
    p[n] = ∑ j ∈ range (n + 1), ((‖r[n]‖ ^ 2 / ‖r[j]‖ ^ 2 : ℝ) : 𝕜) • r[j] :=
  CG.direction_eq_sum_residual b x₀ (CG.residual_ne_zero_of_lt_grade b x₀ hn)

/-- **Lemma 5.6.4(2)** of [liesen2013krylov]. For symmetric coercive $A$, before the grade of
the initial residual the direction has squared norm
$$\|p_n\|^2=\|r_n\|^4\sum_{j=0}^n\|r_j\|^{-2}.$$ -/
theorem lemma_5_6_4_ii (hA : A.IsSymmetricCoercive) {n : ℕ} (hn : n < d₀) :
    ‖p[n]‖ ^ 2 = ‖r[n]‖ ^ 4 * ∑ j ∈ range (n + 1), (‖r[j]‖ ^ 2)⁻¹ :=
  CG.norm_direction_sq_eq_sum b x₀ hA (CG.residual_ne_zero_of_lt_grade b x₀ hn)

omit [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] in
/-- **Lemma 5.6.4(3)** of [liesen2013krylov]. For symmetric coercive $A$ and $n<\ell$,
the CG direction $p_n$ is orthogonal to the later residual $r_\ell$. -/
theorem lemma_5_6_4_iii (hA : A.IsSymmetricCoercive) {n ℓ : ℕ} (hnℓ : n < ℓ) :
    inner 𝕜 p[n] r[ℓ] = 0 := by
  rw [← inner_conj_symm, CG.inner_residual_direction_eq_zero b x₀ hA hnℓ, map_zero]

omit [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] in
/-- **Lemma 5.6.4(4)** of [liesen2013krylov]. For symmetric coercive $A$ and $\ell\le n$,
the inner product of $p_n$ and $r_\ell$ is $\|r_n\|^2$. -/
theorem lemma_5_6_4_iv (hA : A.IsSymmetricCoercive) {n ℓ : ℕ} (hℓn : ℓ ≤ n) :
    inner 𝕜 p[n] r[ℓ] = ((‖r[n]‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_conj_symm, CG.inner_residual_direction_eq b x₀ hA hℓn, RCLike.conj_ofReal]

/-- **Lemma 5.6.4(5)** of [liesen2013krylov]. For symmetric coercive $A$ and $n\le\ell$ with
$n$ before termination, the inner product of two CG directions is
$$\langle p_n,p_\ell\rangle=\|p_n\|^2\frac{\|r_\ell\|^2}{\|r_n\|^2}.$$

**Reading.** The index in the denominator is strictly before the grade, and the later index may
be on the zero tail. -/
theorem lemma_5_6_4_v (hA : A.IsSymmetricCoercive) {n ℓ : ℕ} (hnℓ : n ≤ ℓ) (hn : n < d₀) :
    inner 𝕜 p[n] p[ℓ] = ((‖p[n]‖ ^ 2 * (‖r[ℓ]‖ ^ 2 / ‖r[n]‖ ^ 2) : ℝ) : 𝕜) :=
  CG.inner_direction_eq_scale b x₀ hA hnℓ (CG.residual_ne_zero_of_lt_grade b x₀ hn)

end Directions

/-- **Theorem 5.6.5** of [liesen2013krylov]. For a symmetric coercive $A$ with solution $x$,
the consecutive CG errors $e_n=x-x_n$ and $e_{n+1}=x-x_{n+1}$ before the finite grade of $r_0$
satisfy
$$\frac{\|e_n\|^2-\|e_{n+1}\|^2}{\|p_n\|^2}
  =\frac{\|e_n\|_A^2+\|e_{n+1}\|_A^2}{\|p_n\|_A^2}.$$

**Generalization.** The identity includes the last update to the exact solution. -/
theorem theorem_5_6_5 [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hA : A.IsSymmetricCoercive) (hx : A x = b) {n : ℕ} (hn : n < d₀) :
    (‖x - x[n]‖ ^ 2 - ‖x - x[n + 1]‖ ^ 2) / ‖p[n]‖ ^ 2 =
      (energyNorm A (x - x[n]) ^ 2 + energyNorm A (x - x[n + 1]) ^ 2) /
        energyNorm A p[n] ^ 2 :=
  CG.norm_error_sq_sub_div_eq b x₀ hA hx hn

/-- **Theorem 5.6.5** of [liesen2013krylov], strict monotonicity. If $A$ is symmetric coercive,
$Ax=b$, and $d$ is the finite grade of $r_0$, the Euclidean norms of the CG errors decrease
strictly on the steps from $0$ through $d$. -/
theorem theorem_5_6_5_strict [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hA : A.IsSymmetricCoercive) (hx : A x = b) :
    StrictAntiOn (fun n => ‖x - x[n]‖) (Set.Iic d₀) :=
  CG.norm_error_strictAntiOn b x₀ hA hx

/-- **Theorem 5.6.6** of [liesen2013krylov], the upper bound. Let $A$ be symmetric coercive in
positive finite dimension, with eigenvalues $\mu_i$, and let $Ax=b$. The relative CG energy
error after $n$ steps from $x_0$ is bounded by
$$\inf_{\deg p\le n,\,p(0)=1}\max_i |p(\mu_i)|.$$
A zero initial error gives a ratio of zero.

**Generalization.** The bound holds for every step and includes a zero initial error with total
division. -/
theorem theorem_5_6_6 [FiniteDimensional 𝕜 E] {N : ℕ} [NeZero N]
    (hN : Module.finrank 𝕜 E = N) (hA : A.IsSymmetricCoercive) (hx : A x = b) (n : ℕ) :
    energyNorm A (x - x[n]) / energyNorm A (x - x₀) ≤
      ⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1},
        ⨆ i, ‖p.1.eval (hA.isSymmetric.eigenvalues hN i : 𝕜)‖ :=
  CG.energyNorm_error_le_spectralMinimax hN hA hx n

/-- **Theorem 5.6.6** of [liesen2013krylov], sharpness. For each step $n$ an initial vector
attains the spectral minimax bound. The initial error can be chosen to have unit energy norm.
The result holds for every $n$, including steps at which all CG errors have already vanished.

**Generalization.** The sharpness statement includes steps beyond the minimal-polynomial degree
and uses a unit initial energy error. -/
theorem theorem_5_6_6_sharp [FiniteDimensional 𝕜 E] {N : ℕ} [NeZero N]
    (hN : Module.finrank 𝕜 E = N) (hA : A.IsSymmetricCoercive) (hx : A x = b) (n : ℕ) :
    ∃ y₀ : E, energyNorm A (x - y₀) = 1 ∧
      energyNorm A (x - (CG.iterate A b y₀ n).x) / energyNorm A (x - y₀) =
        ⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1},
          ⨆ i, ‖p.1.eval (hA.isSymmetric.eigenvalues hN i : 𝕜)‖ := by
  let μ := hA.isSymmetric.eigenvalues hN
  let B := hA.isSymmetric.eigenvectorBasis hN
  let M : ℝ := ⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1},
    ⨆ i, ‖p.1.eval (μ i : 𝕜)‖
  obtain ⟨w, hw, hsum, hmin⟩ :=
    Polynomial.exists_probability_weights_eval_minimax_sq_le (fun i => (μ i : 𝕜)) n
  have hμ (i : Fin N) : 0 < μ i := by
    simpa only [RCLike.ofReal_re] using
      hA.re_pos_of_hasEigenvalue (hA.isSymmetric.hasEigenvalue_eigenvalues hN i)
  let e := B.repr.symm (WithLp.toLp 2 (fun i => (Real.sqrt (w i / μ i) : 𝕜)))
  have hre (i : Fin N) : B.repr e i = (Real.sqrt (w i / μ i) : 𝕜) := by
    have h := B.repr.apply_symm_apply (WithLp.toLp 2 (fun i => (Real.sqrt (w i / μ i) : 𝕜)))
    exact congrArg (fun z : EuclideanSpace 𝕜 (Fin N) => z i) h
  have hmode (i : Fin N) : μ i * ‖B.repr e i‖ ^ 2 = w i := by
    rw [hre, RCLike.norm_ofReal, sq_abs, Real.sq_sqrt (div_nonneg (hw i) (hμ i).le)]
    field_simp [(hμ i).ne']
  have hnorm_sq : energyNorm A e ^ 2 = 1 := by
    rw [hA.energyNorm_sq, hA.isSymmetric.re_inner_apply_self_eq_sum hN]
    change (∑ i, μ i * ‖B.repr e i‖ ^ 2) = _
    simp only [hmode, hsum]
  have hnorm : energyNorm A e = 1 := by
    nlinarith [energyNorm_nonneg A e]
  let y₀ := x - e
  have he : x - y₀ = e := sub_sub_cancel x e
  have hg := CG.isGalerkinIterate b y₀ hA n
  obtain ⟨p, hp, hp₀, hres⟩ := exists_residual_poly hg.mem
  have herr := error_eq_aeval_of_injective hA.isCoercive.injective hx hres
  rw [he] at herr
  have hsquare : energyNorm A (x - (CG.iterate A b y₀ n).x) ^ 2 =
      ∑ i, w i * ‖p.eval (μ i : 𝕜)‖ ^ 2 := by
    rw [herr, hA.energyNorm_sq, hA.isSymmetric.re_inner_apply_self_eq_sum hN]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hrep : B.repr (aeval A p e) i = p.eval (μ i : 𝕜) * B.repr e i :=
      hA.isSymmetric.repr_aeval_apply hN p e i
    change μ i * ‖B.repr (aeval A p e) i‖ ^ 2 = _
    rw [hrep, norm_mul, mul_pow, mul_left_comm, hmode, mul_comm]
  have hupper := CG.energyNorm_error_le_spectralMinimax (x₀ := y₀) hN hA hx n
  rw [he, hnorm, div_one] at hupper
  change energyNorm A (x - (CG.iterate A b y₀ n).x) ≤ M at hupper
  have hnonneg := energyNorm_nonneg A (x - (CG.iterate A b y₀ n).x)
  have hlower : M ≤ energyNorm A (x - (CG.iterate A b y₀ n).x) := by
    apply (sq_le_sq₀ (hnonneg.trans hupper) hnonneg).1
    rw [hsquare]
    exact hmin p hp hp₀
  refine ⟨y₀, by rw [he, hnorm], ?_⟩
  rw [he, hnorm, div_one]
  exact hupper.antisymm hlower

/-- **Corollary 5.6.7** of [liesen2013krylov]. Let $A$ be symmetric on an inner product space over
the real or complex numbers with quadratic form between $\alpha\|v\|^2$ and $\beta\|v\|^2$, where
$0<\alpha\le\beta$. If $Ax=b$, then the CG iterates from $x_0$ satisfy
$$\frac{\|x-x_n\|_A}{\|x-x_0\|_A}
 \le 2\biggl(\frac{\sqrt{\beta/\alpha}-1}{\sqrt{\beta/\alpha}+1}\biggr)^n.$$
A zero initial error gives a ratio of zero.

**Generalization.** The bounds need not be attained eigenvalues and the operator need not
act on a finite-dimensional space. -/
theorem corollary_5_6_7 {α β : ℝ} (hA : A.IsSymmetricBoundedBy α β) (hα : 0 < α)
    (hαβ : α ≤ β) (hx : A x = b) (n : ℕ) :
    energyNorm A (x - x[n]) / energyNorm A (x - x₀) ≤
      2 * ((Real.sqrt (β / α) - 1) / (Real.sqrt (β / α) + 1)) ^ n := by
  rcases eq_or_ne (energyNorm A (x - x₀)) 0 with hz | hz
  · rw [hz, div_zero]
    have hκ : 1 ≤ β / α := (one_le_div hα).2 hαβ
    have hs : 1 ≤ Real.sqrt (β / α) := by simpa using Real.sqrt_le_sqrt hκ
    have hq : 0 ≤ (Real.sqrt (β / α) - 1) / (Real.sqrt (β / α) + 1) :=
      div_nonneg (sub_nonneg.2 hs) (by positivity)
    positivity
  rw [div_le_iff₀ (lt_of_le_of_ne (energyNorm_nonneg _ _) hz.symm)]
  exact IsGalerkinIterate.energyNorm_error_le hα hαβ hA
    (CG.isGalerkinIterate b x₀ (hA.isSymmetricCoercive hα) n) hx

/-- **Theorem 5.6.9** of [liesen2013krylov]. Let $A$ be symmetric coercive in finite dimension
with $Ax=b$, and let $\tilde x_0$ be chosen so that $x-\tilde x_0$ is the orthogonal
projection of $x-x_0$ after discarding $\ell$ of the largest eigenvalues, counting
multiplicity. Then for every $n$ the CG errors from the two starting points satisfy
$$\|x-\tilde x_n\|_A\le\|x-x_n\|_A,\qquad
 \|x-x_{n+\ell}\|_A\le\|x-\tilde x_n\|_A.$$
The discarded modes are specified by an initial segment of the decreasing eigenvalue ordering. -/
theorem theorem_5_6_9 [FiniteDimensional 𝕜 E] (hA : A.IsSymmetricCoercive)
    {N : ℕ} (hN : Module.finrank 𝕜 E = N) (hx : A x = b) (ℓ : Fin N) {y₀ : E}
    (hy₀ : ∀ i, (hA.isSymmetric.eigenvectorBasis hN).repr (x - y₀) i =
      if i < ℓ then 0 else (hA.isSymmetric.eigenvectorBasis hN).repr (x - x₀) i)
    (n : ℕ) :
    energyNorm A (x - (CG.iterate A b y₀ n).x) ≤ energyNorm A (x - x[n]) ∧
      energyNorm A (x - x[n + ℓ.val]) ≤ energyNorm A (x - (CG.iterate A b y₀ n).x) := by
  have hD (i : Fin N) (hi : i ∉ Iio ℓ) (j : Fin N) (hj : j ∈ Iio ℓ) :
      hA.isSymmetric.eigenvalues hN i ≤ hA.isSymmetric.eigenvalues hN j :=
    hA.isSymmetric.eigenvalues_antitone hN
      ((mem_Iio.mp hj).le.trans (le_of_not_gt (fun h => hi (mem_Iio.mpr h))))
  simpa only [Fin.card_Iio] using
    CG.energyNorm_error_le_truncated hN hA hx (Iio ℓ) hD
      (by simpa only [mem_Iio] using hy₀) n

/-- **Theorem 5.6.10** of [liesen2013krylov]. Let $Ax=b$ with $A$ symmetric of finite
dimension and spectrum in $[a,c]\subset(0,\infty)$. Set $w_i=|\langle u_i,r_0\rangle|^2$ for
orthonormal eigenvectors $u_i$, and let $\theta_j$ be the $n$-th Ritz values. Up to the grade
of $r_0$, the squared CG energy error equals
$$\xi^{-(2n+1)}\sum_i w_i\prod_j(\mu_i-\theta_j)^2$$
for some $\xi\in[a,c]$. The weights incorporate the factor $\|r_0\|^2$ of the source.

**Generalization.** The interval may enclose the spectrum and the formula includes step zero. -/
theorem theorem_5_6_10 [FiniteDimensional 𝕜 E] {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hA : A.IsSymmetricBoundedBy a c) {N : ℕ} (hN : Module.finrank 𝕜 E = N)
    (hx : A x = b) {n : ℕ} (hn : n ≤ d₀) :
    let μ := (hA.isSymmetricCoercive ha).isSymmetric.eigenvalues hN
    let θ := (Lanczos.tridiag_isHermitian A (b - A x₀) n).eigenvalues
    let w (i : Fin N) :=
      ‖((hA.isSymmetricCoercive ha).isSymmetric.eigenvectorBasis hN).repr (b - A x₀) i‖ ^ 2
    ∃ ξ ∈ Set.Icc a c, energyNorm A (x - x[n]) ^ 2 =
      (∑ i, (∏ j, (μ i - θ j) ^ 2) * w i) / ξ ^ (2 * n + 1) :=
  CG.exists_energyNorm_error_eq_monicRitzProduct ha hac hA hN hx hn

end LiesenStrakos.Chapter05
