/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Projection.Optimality

/-!
# One-dimensional projection processes

Let $A$ be a linear operator on an inner product space $E$ and let $b \in E$. A one-dimensional
projection step for $Ax = b$ uses the trial space $K = \operatorname{span}\{v\}$ and the test space
$L = \operatorname{span}\{w\}$ ([saad2003iterative] (5.12)–(5.13)). From $x$, with the residual
$r = b - Ax$, it gives
$$x' = x + \frac{\langle w, r \rangle}{\langle w, Av \rangle}\, v.$$
The three classical instances are steepest descent ($v = w = r$), the minimal residual iteration
($v = r$, $w = Ar$) and residual-norm steepest descent ($v = A^H r$, $w = Av$). With $v = w = d$ the
step is the exact line search along $d$, the step of every conjugate-direction method.

For convergence, the file proves Kantorovich's inequality ([saad2003iterative] Lemma 5.8), the
contraction of the energy norm of the error by steepest descent ([saad2003iterative] Theorem 5.9,
[quarteroni2000numerical] Theorem 4.10), and the contraction of the residual by the minimal residual
iteration ([saad2003iterative] Theorem 5.10). Here $A$ is symmetric with $\lambda_{\min} \|u\|^2 \le
\operatorname{Re}\langle Au, u \rangle \le \lambda_{\max} \|u\|^2$ for all $u$, where
$0 < \lambda_{\min}$, and $\|u\|_A = \sqrt{\operatorname{Re}\langle Au, u \rangle}$ is the energy
norm.

## Main definitions

* `Projection.step1`: the one-dimensional projection step onto $\operatorname{span}\{v\}$
  orthogonally to $\operatorname{span}\{w\}$.
* `Projection.steepestDescentStep`: the step with $v = w = r$.
* `Projection.minResStep`: the step with $v = r$ and $w = Ar$.
* `Projection.residualNormSDStep`: the step with $v = A^H r$ and $w = Av$.

## Main results

* `Projection.step1_isPetrovGalerkin`: if $\langle w, Av \rangle \neq 0$, the step satisfies the
  Petrov–Galerkin condition for $\operatorname{span}\{v\}$ and $\operatorname{span}\{w\}$.
* `Projection.steepestDescentStep_isGalerkin`: for coercive $A$, steepest descent is the Galerkin
  step on $\operatorname{span}\{r\}$.
* `Projection.minResStep_isMinResidual`: the minimal residual step minimizes the residual norm over
  $x + \operatorname{span}\{r\}$.
* `Projection.kantorovich_inequality`: if $Ay = x$, then $\operatorname{Re}\langle Ax, x \rangle
  \operatorname{Re}\langle y, x \rangle \le \frac{(\lambda_{\max} + \lambda_{\min})^2}{4
  \lambda_{\max} \lambda_{\min}} \|x\|^4$.
* `Projection.energyNorm_steepestDescentStep_le`: steepest descent contracts the energy norm of the
  error by $(\lambda_{\max} - \lambda_{\min}) / (\lambda_{\max} + \lambda_{\min})$.
* `Projection.tendsto_iterate_steepestDescentStep`: the steepest-descent iterates converge to the
  solution from every starting point.
* `Projection.norm_residual_minResStep_le`: for bounded $A$ with $c \|x\|^2 \le
  \operatorname{Re}\langle Ax, x \rangle$, the minimal residual step contracts the residual by
  $\sqrt{1 - c^2 / \|A\|^2}$.
* `Projection.energyNorm_step1_sq_eq`: the exact line search along $d$ lowers the squared energy
  norm of the error by $|\langle d, r \rangle|^2 / \operatorname{Re}\langle Ad, d \rangle$.

## Implementation notes

* The estimates do not use the spectral theorem. Its role is taken by polarization
  (`LinearMap.IsSymmetricBoundedBy.norm_apply_le`) and by the quadratic-form inequalities for
  $(A - \lambda_{\min})(\lambda_{\max} - A) \ge 0$. So the results hold in every inner product
  space; completeness is needed only to define the adjoint in `Projection.residualNormSDStep`.
* The bounds $\lambda_{\min}$ and $\lambda_{\max}$ are stated as `LinearMap.IsSymmetricBoundedBy`.
  They need not be eigenvalues of $A$.
* Division by zero is $0$. Hence the step is $x' = x$ when $\langle w, Av \rangle = 0$, and the
  one-step identities hold without hypotheses at a breakdown.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Let $C$ be a symmetric operator. For all $w, z$, $\operatorname{Re}\langle Cz, w \rangle =
\operatorname{Re}\langle Cw, z \rangle$. -/
theorem IsSymmetric.re_inner_comm {C : F →ₗ[𝕜] F} (hC : C.IsSymmetric) (w z : F) :
    RCLike.re (inner 𝕜 (C z) w) = RCLike.re (inner 𝕜 (C w) z) := by
  rw [hC z w, ← inner_conj_symm]
  exact RCLike.conj_re _

namespace IsSymmetricBoundedBy

/-- **Polarization**: for a symmetric operator the numerical radius controls the norm. Let $C$ be
symmetric with $-d \|u\|^2 \le \operatorname{Re}\langle Cu, u \rangle \le d \|u\|^2$ for all
$u$. Then
$$\|Cu\| \le d \|u\| \quad\text{for every } u.$$

This replaces the spectral theorem in all the estimates of this file. -/
theorem norm_apply_le {C : F →ₗ[𝕜] F} {d : ℝ} (hC : C.IsSymmetricBoundedBy (-d) d) (u : F) :
    ‖C u‖ ≤ d * ‖u‖ := by
  have hpol : ∀ w z : F, 4 * RCLike.re (inner 𝕜 (C w) z) ≤ 2 * d * (‖w‖ ^ 2 + ‖z‖ ^ 2) := by
    intro w z
    have h1 := hC.re_inner_le (w + z)
    have h2 := hC.le_re_inner (w - z)
    have e1 : RCLike.re (inner 𝕜 (C (w + z)) (w + z))
        = RCLike.re (inner 𝕜 (C w) w) + 2 * RCLike.re (inner 𝕜 (C w) z)
          + RCLike.re (inner 𝕜 (C z) z) := by
      simp only [map_add, inner_add_left, inner_add_right]
      rw [hC.isSymmetric.re_inner_comm w z]
      ring
    have e2 : RCLike.re (inner 𝕜 (C (w - z)) (w - z))
        = RCLike.re (inner 𝕜 (C w) w) - 2 * RCLike.re (inner 𝕜 (C w) z)
          + RCLike.re (inner 𝕜 (C z) z) := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      rw [hC.isSymmetric.re_inner_comm w z]
      ring
    rw [e1] at h1
    rw [e2] at h2
    have hd2 : d * (‖w + z‖ ^ 2 + ‖w - z‖ ^ 2) = d * (2 * (‖w‖ ^ 2 + ‖z‖ ^ 2)) := by
      rw [parallelogram_law_with_norm 𝕜 w z]
    linarith
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hu2 : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  have hd : 0 ≤ d := by
    have h1 := hC.le_re_inner u
    have h2 := hC.re_inner_le u
    nlinarith [h1, h2, hu2]
  rcases eq_or_ne (C u) 0 with h0 | h0
  · rw [h0, norm_zero]; positivity
  have hkey := hpol u (((‖u‖ / ‖C u‖ : ℝ) : 𝕜) • C u)
  have hnormz : ‖((‖u‖ / ‖C u‖ : ℝ) : 𝕜) • C u‖ = ‖u‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (by positivity)]
    field_simp
  have hinnerz : RCLike.re (inner 𝕜 (C u) (((‖u‖ / ‖C u‖ : ℝ) : 𝕜) • C u)) = ‖u‖ * ‖C u‖ := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_mul, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
    field_simp
  rw [hnormz, hinnerz] at hkey
  nlinarith [hkey, hupos]

/-- Let $B$ be symmetric with $\lambda_{\min} \|u\|^2 \le \operatorname{Re}\langle Bu, u \rangle \le
\lambda_{\max} \|u\|^2$ for all $u$. Then for every $u$,
$$\|Bu\|^2 + \lambda_{\min} \lambda_{\max} \|u\|^2 \le (\lambda_{\min} + \lambda_{\max})
  \operatorname{Re}\langle Bu, u \rangle.$$
This is the quadratic-form version of the operator inequality
$(B - \lambda_{\min})(\lambda_{\max} - B) \ge 0$. -/
theorem norm_apply_sq_add_le {B : F →ₗ[𝕜] F} {lmin lmax : ℝ}
    (hB : B.IsSymmetricBoundedBy lmin lmax) (u : F) :
    ‖B u‖ ^ 2 + lmin * lmax * ‖u‖ ^ 2 ≤ (lmin + lmax) * RCLike.re (inner 𝕜 (B u) u) := by
  have hre : ∀ (r : ℝ) (v : F), RCLike.re ((r : 𝕜) * inner 𝕜 v v) = r * ‖v‖ ^ 2 := by
    intro r v
    rw [RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  have hC : (B - (((lmin + lmax) / 2 : ℝ) : 𝕜) • LinearMap.id :
      F →ₗ[𝕜] F).IsSymmetricBoundedBy (-((lmax - lmin) / 2)) ((lmax - lmin) / 2) := by
    refine ⟨fun v w => ?_, fun v => ?_, fun v => ?_⟩
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
      rw [hB.isSymmetric v w]
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub]
      rw [hre]
      linarith [hB.le_re_inner v]
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub]
      rw [hre]
      linarith [hB.re_inner_le v]
  have hnorm := norm_apply_le hC u
  have happ : (B - (((lmin + lmax) / 2 : ℝ) : 𝕜) • LinearMap.id : F →ₗ[𝕜] F) u
      = B u - (((lmin + lmax) / 2 : ℝ) : 𝕜) • u := rfl
  rw [happ] at hnorm
  have hsq : ‖B u - (((lmin + lmax) / 2 : ℝ) : 𝕜) • u‖ ^ 2
      ≤ ((lmax - lmin) / 2) ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg (B u - (((lmin + lmax) / 2 : ℝ) : 𝕜) • u), norm_nonneg u, hnorm]
  rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, norm_smul,
    RCLike.norm_ofReal, mul_pow, sq_abs] at hsq
  linarith

/-- **Degenerate bounds.** Let $B$ be symmetric with $\operatorname{Re}\langle Bu, u \rangle = l
\|u\|^2$ for all $u$, that is, with both bounds of `LinearMap.IsSymmetricBoundedBy` equal to
$l$. Then $Bu = lu$ for every $u$.

This is why the Chebyshev convergence bounds hold, and are trivial, without a strict gap between
the bounds. -/
theorem apply_eq_smul {B : F →ₗ[𝕜] F} {l : ℝ} (hB : B.IsSymmetricBoundedBy l l) (u : F) :
    B u = (l : 𝕜) • u := by
  have hre : RCLike.re (inner 𝕜 (B u) u) = l * ‖u‖ ^ 2 :=
    le_antisymm (hB.re_inner_le u) (hB.le_re_inner u)
  have hexp : ‖B u - (l : 𝕜) • u‖ ^ 2
      = ‖B u‖ ^ 2 - 2 * (l * RCLike.re (inner 𝕜 (B u) u)) + l ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, norm_smul,
      RCLike.norm_ofReal, mul_pow, sq_abs]
  have hkey : ‖B u‖ ^ 2 + l * l * ‖u‖ ^ 2 ≤ (l + l) * (l * ‖u‖ ^ 2) := by
    have h := hB.norm_apply_sq_add_le u
    rwa [hre] at h
  have hzero : ‖B u - (l : 𝕜) • u‖ ^ 2 ≤ 0 := by
    rw [hexp, hre]
    nlinarith [hkey]
  rw [← sub_eq_zero, ← norm_eq_zero, ← sq_eq_zero_iff]
  exact le_antisymm hzero (sq_nonneg _)

/-- Let $B$ be symmetric with $\lambda_{\min} \|u\|^2 \le \operatorname{Re}\langle Bu, u \rangle \le
\lambda_{\max} \|u\|^2$ for all $u$, where $0 \le \lambda_{\min}$. Then for every $u$,
$$\lambda_{\min} \operatorname{Re}\langle Bu, u \rangle \le \|Bu\|^2.$$
This is the operator inequality $\lambda_{\min} B \le B^2$. -/
theorem le_norm_apply_sq {B : F →ₗ[𝕜] F} {lmin lmax : ℝ} (hl : 0 ≤ lmin)
    (hB : B.IsSymmetricBoundedBy lmin lmax) (u : F) :
    lmin * RCLike.re (inner 𝕜 (B u) u) ≤ ‖B u‖ ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hcs : RCLike.re (inner 𝕜 (B u) u) ≤ ‖B u‖ * ‖u‖ := re_inner_le_norm _ _
  have h1 : lmin * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 (B u) u) := hB.le_re_inner u
  have h2 : lmin * ‖u‖ ≤ ‖B u‖ := by nlinarith
  nlinarith [norm_nonneg (B u)]

/-- Let $B$ be symmetric with $\lambda_{\min} \|u\|^2 \le \operatorname{Re}\langle Bu, u \rangle \le
\lambda_{\max} \|u\|^2$ for all $u$, where $0 \le \lambda_{\min}$. Then for every $u$,
$$\|Bu\|^2 \le \lambda_{\max} \operatorname{Re}\langle Bu, u \rangle.$$
This is the operator inequality $B^2 \le \lambda_{\max} B$. -/
theorem norm_apply_sq_le {B : F →ₗ[𝕜] F} {lmin lmax : ℝ} (hl : 0 ≤ lmin)
    (hB : B.IsSymmetricBoundedBy lmin lmax) (u : F) :
    ‖B u‖ ^ 2 ≤ lmax * RCLike.re (inner 𝕜 (B u) u) := by
  have h1 := hB.norm_apply_sq_add_le u
  have h2 := hB.re_inner_le u
  nlinarith [mul_nonneg hl (sub_nonneg.2 h2)]

end IsSymmetricBoundedBy

end LinearMap

namespace Projection

/-- The **one-dimensional projection step** onto $\operatorname{span}\{v\}$ orthogonally to
$\operatorname{span}\{w\}$ ([saad2003iterative], (5.12)). From $x$, with the residual
$r = b - Ax$,
$$x \mapsto x + \frac{\langle w, r \rangle}{\langle w, Av \rangle}\, v.$$
If $\langle w, Av \rangle = 0$, the quotient is $0$ by the convention of division by zero, and
the step returns $x$. -/
noncomputable def step1 (A : E →ₗ[𝕜] E) (b : E) (v w : E) (x : E) : E :=
  x + (inner 𝕜 w (b - A x) / inner 𝕜 w (A v)) • v

variable {A : E →ₗ[𝕜] E} {b : E}

/-- Let $\langle w, Av \rangle \neq 0$. Then the one-dimensional step from $x$ satisfies the
Petrov–Galerkin condition for $(A, b, x, \operatorname{span}\{v\}, \operatorname{span}\{w\})$.

The condition $\langle w, Av \rangle \neq 0$ makes the denominator of the step nonzero. The
three classical instances differ only in the choice of $v$ and $w$. -/
theorem step1_isPetrovGalerkin (v w x : E) (h : inner 𝕜 w (A v) ≠ 0) :
    IsPetrovGalerkin A b x (𝕜 ∙ v) (𝕜 ∙ w) (step1 A b v w x) := by
  refine ⟨?_, ?_⟩
  · rw [step1, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right, step1, map_add, map_smul,
      show b - (A x + (inner 𝕜 w (b - A x) / inner 𝕜 w (A v)) • A v)
        = (b - A x) - (inner 𝕜 w (b - A x) / inner 𝕜 w (A v)) • A v from by abel,
      inner_sub_right, inner_smul_right]
    field_simp
    ring

/-- **The exact line search.** Let $A$ be coercive. For every $d$ and $x$, the one-dimensional step
with $v = w = d$ from $x$ satisfies the Galerkin condition for
$(A, b, x, \operatorname{span}\{d\})$.

No nondegeneracy hypothesis is needed: for $d \neq 0$ coercivity gives
$\langle d, Ad \rangle \neq 0$, and for $d = 0$ the step returns $x$ and the span is zero. This
is the exact line search along $d$ for the energy functional ([quarteroni2000numerical] (4.39),
(7.36)), the step of every conjugate-direction method (`Numlib.Projection.ConjugateDirection`). -/
theorem step1_isGalerkin (hA : A.IsCoercive) (d x : E) :
    IsGalerkin A b x (𝕜 ∙ d) (step1 A b d d x) := by
  rcases eq_or_ne d 0 with rfl | hd
  · refine ⟨?_, ?_⟩
    · rw [step1, smul_zero, add_zero, sub_self]
      exact Submodule.zero_mem _
    · rw [Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top]
      exact Submodule.mem_top
  · refine step1_isPetrovGalerkin d d x fun hcon => ?_
    have hpos := hA.inner_self_pos hd
    rw [inner_eq_zero_symm.1 hcon, map_zero] at hpos
    exact lt_irrefl 0 hpos

/-- The **steepest descent step** ([saad2003iterative], Algorithm 5.2): the one-dimensional step
with $v = w = r$, where $r = b - Ax$ is the residual at $x$. -/
noncomputable def steepestDescentStep (A : E →ₗ[𝕜] E) (b : E) (x : E) : E :=
  step1 A b (b - A x) (b - A x) x

/-- The **minimal residual iteration step** ([saad2003iterative], Algorithm 5.3): the
one-dimensional step with $v = r$ and $w = Ar$, where $r = b - Ax$ is the residual at $x$. -/
noncomputable def minResStep (A : E →ₗ[𝕜] E) (b : E) (x : E) : E :=
  step1 A b (b - A x) (A (b - A x)) x

/-- The **residual-norm steepest descent step** ([saad2003iterative], Algorithm 5.4). Let $E$ be
complete and let $A$ be a bounded operator. The step is the one-dimensional step with
$v = A^H r$ and $w = Av$, where $r = b - Ax$ is the residual at $x$ and $A^H$ is the adjoint of
$A$. -/
noncomputable def residualNormSDStep [CompleteSpace E] (A : E →L[𝕜] E) (b : E) (x : E) : E :=
  step1 (A : E →ₗ[𝕜] E) b ((ContinuousLinearMap.adjoint A) (b - A x))
    (A ((ContinuousLinearMap.adjoint A) (b - A x))) x

/-- If the residual $b - Ax$ is zero and $v = b - Ax$, the one-dimensional step returns $x$. -/
private theorem step1_of_residual_eq_zero {v w x : E} (h0 : b - A x = 0) (hv : v = b - A x) :
    step1 A b v w x = x := by
  rw [step1, hv, h0, smul_zero, add_zero]

/-- **Steepest descent is a Galerkin step.** Let $A$ be coercive and let $r = b - Ax$. The steepest
descent step from $x$ satisfies the Galerkin condition for
$(A, b, x, \operatorname{span}\{r\})$.

Coercivity gives the nondegeneracy $\langle r, Ar \rangle \neq 0$ for $r \neq 0$. If $r = 0$ the
step returns $x$. -/
theorem steepestDescentStep_isGalerkin (x : E) (hA : A.IsCoercive) :
    IsGalerkin A b x (𝕜 ∙ (b - A x)) (steepestDescentStep A b x) := by
  rcases eq_or_ne (b - A x) 0 with h0 | h0
  · rw [steepestDescentStep, step1_of_residual_eq_zero h0 rfl]
    exact ⟨by simp, by rw [h0]; exact Submodule.zero_mem _⟩
  · refine step1_isPetrovGalerkin (b - A x) (b - A x) x fun hcon => ?_
    have hpos := hA.inner_self_pos h0
    rw [inner_eq_zero_symm.1 hcon, map_zero] at hpos
    exact lt_irrefl 0 hpos

/-- **The minimal residual step minimizes the residual.** Let $r = b - Ax$. The minimal residual
step $x'$ from $x$ satisfies the minimal-residual condition for
$(A, b, x, \operatorname{span}\{r\})$: it minimizes $\|b - Ay\|$ over
$y \in x + \operatorname{span}\{r\}$. No hypothesis on $A$ is needed.

With $L = AK$ the minimization is the one-dimensional step, whose nondegeneracy condition is
$Ar \neq 0$. If $Ar = 0$, every point of the line has the residual $r$, and the step, which
returns $x$, is a minimizer. -/
theorem minResStep_isMinResidual (x : E) :
    IsMinResidual A b x (𝕜 ∙ (b - A x)) (minResStep A b x) := by
  have hmap : (𝕜 ∙ (b - A x)).map A = 𝕜 ∙ A (b - A x) := by
    rw [Submodule.map_span, Set.image_singleton]
  rcases eq_or_ne (A (b - A x)) 0 with h0 | h0
  · have hstep : minResStep A b x = x := by
      rw [minResStep, step1, h0, inner_zero_left, inner_zero_left, zero_div, zero_smul, add_zero]
    refine ⟨by rw [hstep, sub_self]; exact Submodule.zero_mem _, fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
    have hy' : y = x + c • (b - A x) := by rw [hc]; abel
    rw [hstep, hy', map_add, map_smul, h0, smul_zero, add_zero]
  · refine IsMinResidual.iff_isPetrovGalerkin.2 ?_
    rw [hmap]
    exact step1_isPetrovGalerkin (b - A x) (A (b - A x)) x fun hcon =>
      h0 (inner_self_eq_zero.1 hcon)

/-- **Kantorovich's inequality** ([saad2003iterative], Lemma 5.8). Let $A$ be symmetric with
$\lambda_{\min} \|u\|^2 \le \operatorname{Re}\langle Au, u \rangle \le \lambda_{\max} \|u\|^2$
for all $u$, where $0 < \lambda_{\min}$. If $Ay = x$, then
$$\operatorname{Re}\langle Ax, x \rangle \cdot \operatorname{Re}\langle y, x \rangle \le
  \frac{(\lambda_{\max} + \lambda_{\min})^2}{4 \lambda_{\max} \lambda_{\min}} \|x\|^4.$$

The vector $y$ is $A^{-1} x$. Asking for it as a hypothesis avoids the inverse of $A$. -/
theorem kantorovich_inequality {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) (x : E) {y : E} (hy : A y = x) :
    RCLike.re (inner 𝕜 (A x) x) * RCLike.re (inner 𝕜 y x) ≤
      (lmax + lmin) ^ 2 / (4 * lmax * lmin) * ‖x‖ ^ 4 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hll : lmin ≤ lmax := by
    nlinarith [hA.le_re_inner x, hA.re_inner_le x, hx2]
  have hlmax : 0 < lmax := lt_of_lt_of_le hl hll
  have hAc : A.IsSymmetricCoercive := hA.isSymmetricCoercive hl
  -- transport `A` to the energy space, where it has the same quadratic-form bounds
  let A' : WithEnergy A hAc →ₗ[𝕜] WithEnergy A hAc :=
    (WithEnergy.equiv A hAc).toLinearMap ∘ₗ A ∘ₗ (WithEnergy.equiv A hAc).symm.toLinearMap
  have hA'app : ∀ u : E, A' (WithEnergy.equiv A hAc u) = WithEnergy.equiv A hAc (A u) :=
    fun _ => rfl
  have hinnerW : ∀ u v : E, inner 𝕜 (WithEnergy.equiv A hAc u) (WithEnergy.equiv A hAc v)
      = inner 𝕜 (A u) v := fun _ _ => rfl
  have hnormW : ∀ u : E, ‖WithEnergy.equiv A hAc u‖ ^ 2 = RCLike.re (inner 𝕜 (A u) u) := by
    intro u
    rw [WithEnergy.norm_equiv]
    exact hAc.energyNorm_sq u
  have hsq : ∀ u : E, RCLike.re (inner 𝕜 (A (A u)) u) = ‖A u‖ ^ 2 := by
    intro u
    rw [hA.isSymmetric (A u) u]
    exact inner_self_eq_norm_sq _
  have hsurj := (WithEnergy.equiv A hAc).surjective
  have hA'bound : A'.IsSymmetricBoundedBy lmin lmax := by
    refine ⟨fun v w => ?_, fun v => ?_, fun v => ?_⟩
    · obtain ⟨u, rfl⟩ := hsurj v
      obtain ⟨z, rfl⟩ := hsurj w
      rw [hA'app, hA'app, hinnerW, hinnerW]
      exact hA.isSymmetric (A u) z
    · obtain ⟨u, rfl⟩ := hsurj v
      rw [hA'app, hinnerW, hnormW, hsq]
      exact LinearMap.IsSymmetricBoundedBy.le_norm_apply_sq hl.le hA u
    · obtain ⟨u, rfl⟩ := hsurj v
      rw [hA'app, hinnerW, hnormW, hsq]
      exact LinearMap.IsSymmetricBoundedBy.norm_apply_sq_le hl.le hA u
  have hK1 := hA'bound.norm_apply_sq_add_le (WithEnergy.equiv A hAc y)
  rw [hA'app, hnormW, hnormW, hinnerW, hsq, hy] at hK1
  -- `hK1 : ‖x‖² + lmin lmax re⟪A y, y⟫ ≤ (lmin + lmax) re⟪A x, y⟫` after the substitutions
  have hβ : RCLike.re (inner 𝕜 x y) = RCLike.re (inner 𝕜 y x) := by
    rw [← inner_conj_symm y x]
    exact (RCLike.conj_re _).symm
  have hαnn : 0 ≤ RCLike.re (inner 𝕜 (A x) x) :=
    le_trans (by positivity) (hA.le_re_inner x)
  have hβnn : 0 ≤ RCLike.re (inner 𝕜 y x) := by
    rw [← hβ, ← hy]
    exact le_trans (by positivity) (hA.le_re_inner y)
  rw [hβ] at hK1
  have hnn : 0 ≤ RCLike.re (inner 𝕜 (A x) x) + lmin * lmax * RCLike.re (inner 𝕜 y x) :=
    add_nonneg hαnn (mul_nonneg (mul_nonneg hl.le hlmax.le) hβnn)
  have hsquare : (RCLike.re (inner 𝕜 (A x) x) + lmin * lmax * RCLike.re (inner 𝕜 y x)) ^ 2
      ≤ ((lmin + lmax) * ‖x‖ ^ 2) ^ 2 := by nlinarith [hK1, hnn]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hsquare,
    sq_nonneg (RCLike.re (inner 𝕜 (A x) x) - lmin * lmax * RCLike.re (inner 𝕜 y x))]

/-- For symmetric coercive $A$, every $d$ and real $t$, $\|d - tAd\|_A^2 = \|d\|_A^2 - 2t \|Ad\|^2 +
t^2 \operatorname{Re}\langle A^2 d, Ad \rangle$. -/
private theorem energyNorm_sub_smul_apply_sq (hAc : A.IsSymmetricCoercive) (d : E) (t : ℝ) :
    energyNorm A (d - (t : 𝕜) • A d) ^ 2
      = energyNorm A d ^ 2 - 2 * t * ‖A d‖ ^ 2
        + t ^ 2 * RCLike.re (inner 𝕜 (A (A d)) (A d)) := by
  have hsym : RCLike.re (inner 𝕜 (A (A d)) d) = ‖A d‖ ^ 2 := by
    rw [hAc.isSymmetric (A d) d]
    exact inner_self_eq_norm_sq _
  rw [hAc.energyNorm_sq, hAc.energyNorm_sq]
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul, map_sub,
    inner_self_eq_norm_sq]
  rw [hsym]
  ring

/-- For symmetric $A$ and $r = b - Ax$, the steepest descent step is $x + (\|r\|^2 /
\operatorname{Re}\langle Ar, r \rangle)\, r$, with a real step length. -/
private theorem steepestDescentStep_eq (hsym : A.IsSymmetric) (x : E) :
    steepestDescentStep A b x
      = x + ((‖b - A x‖ ^ 2 / RCLike.re (inner 𝕜 (A (b - A x)) (b - A x)) : ℝ) : 𝕜)
          • (b - A x) := by
  have hself : inner 𝕜 (A (b - A x)) (b - A x)
      = ((RCLike.re (inner 𝕜 (A (b - A x)) (b - A x)) : ℝ) : 𝕜) := by
    refine (RCLike.conj_eq_iff_re.1 ?_).symm
    rw [inner_conj_symm]
    exact (hsym (b - A x) (b - A x)).symm
  have hscal : inner 𝕜 (b - A x) (b - A x) / inner 𝕜 (b - A x) (A (b - A x))
      = ((‖b - A x‖ ^ 2 / RCLike.re (inner 𝕜 (A (b - A x)) (b - A x)) : ℝ) : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K, ← hsym (b - A x) (b - A x), hself,
      ← RCLike.ofReal_pow, ← RCLike.ofReal_div, RCLike.ofReal_re]
  rw [steepestDescentStep, step1, hscal]

/-- **Contraction by steepest descent** ([saad2003iterative], Theorem 5.9). Let $A$ be symmetric
with $\lambda_{\min} \|u\|^2 \le \operatorname{Re}\langle Au, u \rangle \le \lambda_{\max}
\|u\|^2$ for all $u$, where $0 < \lambda_{\min}$, and let $Ax^* = b$. For every $x$, the
steepest descent step $x'$ from $x$ satisfies
$$\|x^* - x'\|_A \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}}
  \|x^* - x\|_A.$$
-/
theorem energyNorm_steepestDescentStep_le {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) {xstar : E} (hstar : A xstar = b) (x : E) :
    energyNorm A (xstar - steepestDescentStep A b x) ≤
      (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x) := by
  have hAc : A.IsSymmetricCoercive := hA.isSymmetricCoercive hl
  have hAd : A (xstar - x) = b - A x := by rw [map_sub, hstar]
  rcases eq_or_ne (b - A x) 0 with h0 | h0
  · have hd0 : xstar - x = 0 := by
      have h1 := hA.le_re_inner (xstar - x)
      rw [hAd, h0, inner_zero_left, map_zero] at h1
      have h2 : ‖xstar - x‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
    rw [steepestDescentStep, step1_of_residual_eq_zero h0 rfl, hd0]
    simp [energyNorm]
  have hr2 : (0 : ℝ) < ‖b - A x‖ ^ 2 := by positivity
  have hll : lmin ≤ lmax := by
    nlinarith [hA.le_re_inner (b - A x), hA.re_inner_le (b - A x), hr2]
  have hlmax : 0 < lmax := lt_of_lt_of_le hl hll
  set q : ℝ := RCLike.re (inner 𝕜 (A (b - A x)) (b - A x)) with hqdef
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) (hA.le_re_inner (b - A x))
  set a : ℝ := ‖b - A x‖ ^ 2 / q with hadef
  have hstep : steepestDescentStep A b x = x + (a : 𝕜) • (b - A x) := by
    rw [hadef, hqdef]
    exact steepestDescentStep_eq hA.isSymmetric x
  have herr : xstar - steepestDescentStep A b x = (xstar - x) - (a : 𝕜) • A (xstar - x) := by
    rw [hstep, hAd]; abel
  have hexp0 := energyNorm_sub_smul_apply_sq hAc (xstar - x) a
  rw [← herr, hAd, ← hqdef] at hexp0
  have hexp : energyNorm A (xstar - steepestDescentStep A b x) ^ 2
      = energyNorm A (xstar - x) ^ 2 - ‖b - A x‖ ^ 4 / q := by
    rw [hexp0, hadef]
    field_simp
    ring
  -- Kantorovich applied to the residual, whose preimage is the error
  have hkant := kantorovich_inequality hl hA (b - A x) hAd
  have hconj : RCLike.re (inner 𝕜 (xstar - x) (b - A x)) = energyNorm A (xstar - x) ^ 2 := by
    rw [hAc.energyNorm_sq, ← hAd, ← inner_conj_symm]
    exact RCLike.conj_re _
  rw [hconj, ← hqdef] at hkant
  have hkant' : 4 * lmax * lmin * (q * energyNorm A (xstar - x) ^ 2)
      ≤ ‖b - A x‖ ^ 4 * (lmax + lmin) ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * lmax * lmin)] at hkant
    nlinarith [hkant]
  have hfrac : 4 * lmax * lmin / (lmax + lmin) ^ 2 * energyNorm A (xstar - x) ^ 2
      ≤ ‖b - A x‖ ^ 4 / q := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hqpos]
    nlinarith [hkant']
  have hcoeff : ((lmax - lmin) / (lmax + lmin)) ^ 2
      = 1 - 4 * lmax * lmin / (lmax + lmin) ^ 2 := by
    field_simp
    ring
  have hcnn : 0 ≤ (lmax - lmin) / (lmax + lmin) := by
    apply div_nonneg <;> linarith
  have henn := energyNorm_nonneg A (xstar - x)
  have hsq : energyNorm A (xstar - steepestDescentStep A b x) ^ 2
      ≤ ((lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x)) ^ 2 := by
    rw [hexp, mul_pow, hcoeff]
    nlinarith [hfrac]
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (energyNorm_nonneg _ _), Real.sqrt_sq (mul_nonneg hcnn henn)] at hfin

/-- **Contraction by the minimal residual iteration** ([saad2003iterative], Theorem 5.10). Let $A$
be a bounded operator, and let $c > 0$ with $c \|x\|^2 \le \operatorname{Re}\langle Ax, x
\rangle$ for all $x$. For all $b$ and $x$, the minimal residual step $x'$ from $x$ satisfies
$$\|b - Ax'\| \le \sqrt{1 - c^2 / \|A\|^2}\, \|b - Ax\|.$$

$\|A\|$ is the operator norm. The space $E$ need not be complete. The proof bounds the quotient
in `Projection.norm_residual_minResStep_sq_eq` from below. -/
theorem norm_residual_minResStep_le {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) (b x : E) :
    ‖b - A (minResStep (A : E →ₗ[𝕜] E) b x)‖ ≤
      Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x‖ := by
  have hmin := minResStep_isMinResidual (A := (A : E →ₗ[𝕜] E)) (b := b) x
  set θ : ℝ := c / ‖A‖ ^ 2 with hθ
  have hθnn : 0 ≤ θ := by positivity
  have hstep := hmin.min (x + (θ : 𝕜) • (b - A x))
    (by rw [add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hres : b - (A : E →ₗ[𝕜] E) (x + (θ : 𝕜) • (b - A x))
      = (b - A x) - (θ : 𝕜) • A (b - A x) := by
    simp only [map_add, map_smul]; abel
  rw [hres] at hstep
  have hRich := ContinuousLinearMap.norm_sub_smul_apply_sq_le hA hθnn (b - A x)
  have hcoeff : 1 - 2 * θ * c + θ ^ 2 * ‖A‖ ^ 2 = 1 - c ^ 2 / ‖A‖ ^ 2 := by
    rcases eq_or_ne ‖A‖ 0 with h | h
    · rw [hθ, h]; norm_num
    · rw [hθ]; field_simp; ring
  rw [hcoeff] at hRich
  have hsq : ‖b - (A : E →ₗ[𝕜] E) (minResStep (A : E →ₗ[𝕜] E) b x)‖ ^ 2
      ≤ (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x‖ ^ 2 := by
    refine le_trans ?_ hRich
    nlinarith [hstep, norm_nonneg (b - (A : E →ₗ[𝕜] E) (minResStep (A : E →ₗ[𝕜] E) b x)),
      norm_nonneg ((b - A x) - (θ : 𝕜) • A (b - A x))]
  simp only [ContinuousLinearMap.coe_coe] at hsq ⊢
  rcases eq_or_ne ‖b - A x‖ 0 with hr0 | hr0
  · rw [hr0] at hsq ⊢
    have hz : ‖b - A (minResStep (A : E →ₗ[𝕜] E) b x)‖ ^ 2 = 0 :=
      le_antisymm (by simpa using hsq) (sq_nonneg _)
    rw [pow_eq_zero_iff two_ne_zero |>.1 hz, mul_zero]
  · have hR2 : (0 : ℝ) < ‖b - A x‖ ^ 2 := by positivity
    have hknn : 0 ≤ 1 - c ^ 2 / ‖A‖ ^ 2 := by
      nlinarith [hsq, sq_nonneg ‖b - A (minResStep (A : E →ₗ[𝕜] E) b x)‖, hR2]
    have hfin := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hknn, Real.sqrt_sq (norm_nonneg _)] at hfin

/-- **The one-step identity of the minimal residual iteration** ([saad2003iterative], (5.18)). Let
$r = b - Ax$, and let $r' = b - Ax'$ be the residual after the minimal residual step. Then
$$\|r'\|^2 = \|r\|^2 \left(1 - \frac{|\langle Ar, r \rangle|^2}{\|r\|^2 \|Ar\|^2}\right).$$
The source writes this as $\|r'\| = \|r\| \sin \angle(r, Ar)$.

No hypothesis is needed. If $r = 0$ or $Ar = 0$ the step returns $x$, and both sides are
$\|r\|^2$, because division by zero is $0$. A lower bound for the quotient turns this identity
into the contraction `Projection.norm_residual_minResStep_le`. -/
theorem norm_residual_minResStep_sq_eq (x : E) :
    ‖b - A (minResStep A b x)‖ ^ 2
      = ‖b - A x‖ ^ 2 *
        (1 - ‖inner 𝕜 (A (b - A x)) (b - A x)‖ ^ 2
              / (‖b - A x‖ ^ 2 * ‖A (b - A x)‖ ^ 2)) := by
  rcases eq_or_ne (b - A x) 0 with h1 | h1
  · rw [minResStep, step1_of_residual_eq_zero h1 rfl, h1]
    simp
  rcases eq_or_ne (A (b - A x)) 0 with h0 | h0
  · simp [minResStep, step1, h0]
  have hApos : (0 : ℝ) < ‖A (b - A x)‖ ^ 2 := by positivity
  have hden : inner 𝕜 (A (b - A x)) (A (b - A x)) = ((‖A (b - A x)‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
  have hstep : b - A (minResStep A b x)
      = (b - A x)
        - (inner 𝕜 (A (b - A x)) (b - A x) / ((‖A (b - A x)‖ ^ 2 : ℝ) : 𝕜)) • A (b - A x) := by
    rw [minResStep, step1, hden, map_add, map_smul]
    abel
  have hkey : (inner 𝕜 (A (b - A x)) (b - A x) / ((‖A (b - A x)‖ ^ 2 : ℝ) : 𝕜))
        * (starRingEnd 𝕜) (inner 𝕜 (A (b - A x)) (b - A x))
      = ((‖inner 𝕜 (A (b - A x)) (b - A x)‖ ^ 2 / ‖A (b - A x)‖ ^ 2 : ℝ) : 𝕜) := by
    rw [div_mul_eq_mul_div, RCLike.mul_conj]
    push_cast
    ring
  have hinner : RCLike.re (inner 𝕜 (b - A x)
        ((inner 𝕜 (A (b - A x)) (b - A x) / ((‖A (b - A x)‖ ^ 2 : ℝ) : 𝕜)) • A (b - A x)))
      = ‖inner 𝕜 (A (b - A x)) (b - A x)‖ ^ 2 / ‖A (b - A x)‖ ^ 2 := by
    rw [inner_smul_right, ← inner_conj_symm (b - A x) (A (b - A x)), hkey, RCLike.ofReal_re]
  have hnorm : ‖(inner 𝕜 (A (b - A x)) (b - A x) / ((‖A (b - A x)‖ ^ 2 : ℝ) : 𝕜))
        • A (b - A x)‖ ^ 2
      = ‖inner 𝕜 (A (b - A x)) (b - A x)‖ ^ 2 / ‖A (b - A x)‖ ^ 2 := by
    rw [norm_smul, norm_div, RCLike.norm_ofReal, abs_of_pos hApos, mul_pow, div_pow]
    field_simp
  rw [hstep, norm_sub_sq (𝕜 := 𝕜), hinner, hnorm]
  field_simp
  ring

/-- **The one-step identity of steepest descent** ([saad2003iterative], the display before Lemma
5.8, (5.20)). Let $A$ be symmetric coercive, let $Ax^* = b$, and let $x'$ be the steepest
descent step from $x$. With the error $d = x^* - x$ and the residual $r = b - Ax = Ad$,
$$\|x^* - x'\|_A^2 = \|d\|_A^2 \left(1 - \frac{\|r\|^4}{\operatorname{Re}\langle Ar, r \rangle\,
  \|d\|_A^2}\right).$$

The source writes the quotient as $\langle r, r \rangle^2 / (\langle Ar, r \rangle \langle
A^{-1} r, r \rangle)$, where $\langle r, r \rangle = \|r\|^2$ and $\langle A^{-1} r, r \rangle =
\langle d, Ad \rangle = \|d\|_A^2$. A lower bound for the quotient by Kantorovich's inequality
is the proof of `Projection.energyNorm_steepestDescentStep_le`. -/
theorem energyNorm_steepestDescentStep_sq_eq (hA : A.IsSymmetricCoercive) {xstar : E}
    (hstar : A xstar = b) (x : E) :
    energyNorm A (xstar - steepestDescentStep A b x) ^ 2
      = energyNorm A (xstar - x) ^ 2 *
        (1 - ‖b - A x‖ ^ 4
              / (RCLike.re (inner 𝕜 (A (b - A x)) (b - A x))
                  * energyNorm A (xstar - x) ^ 2)) := by
  have hAd : A (xstar - x) = b - A x := by rw [map_sub, hstar]
  rcases eq_or_ne (b - A x) 0 with h0 | h0
  · have hd0 : xstar - x = 0 := hA.isCoercive.injective (by rw [hAd, h0, map_zero])
    rw [steepestDescentStep, step1_of_residual_eq_zero h0 rfl, hd0, h0]
    simp [energyNorm]
  have hd0 : xstar - x ≠ 0 := fun h => h0 (by rw [← hAd, h, map_zero])
  set q : ℝ := RCLike.re (inner 𝕜 (A (b - A x)) (b - A x)) with hq
  have hqpos : 0 < q := hA.isCoercive.inner_self_pos h0
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hene : energyNorm A (xstar - x) ≠ 0 := ne_of_gt (hA.energyNorm_pos hd0)
  set a : ℝ := ‖b - A x‖ ^ 2 / q with ha
  have hstep : steepestDescentStep A b x = x + (a : 𝕜) • (b - A x) := by
    rw [ha, hq]
    exact steepestDescentStep_eq hA.isSymmetric x
  have herr : xstar - steepestDescentStep A b x = (xstar - x) - (a : 𝕜) • A (xstar - x) := by
    rw [hstep, hAd]; abel
  have hexp := energyNorm_sub_smul_apply_sq hA (xstar - x) a
  rw [← herr, hAd, ← hq] at hexp
  rw [hexp, ha]
  field_simp
  ring

/-- If $\langle w, b - Ax \rangle = 0$, the one-dimensional step with vectors $v$, $w$ from $x$
returns $x$, because its coefficient is zero. -/
theorem step1_eq_self_of_inner_eq_zero {v w x : E} (h : inner 𝕜 w (b - A x) = 0) :
    step1 A b v w x = x := by
  rw [step1, h, zero_div, zero_smul, add_zero]

/-- **The one-step identity of the exact line search** ([quarteroni2000numerical] (7.37)–(7.38)).
Let $A$ be symmetric coercive and let $Ax^* = b$. For all $d$ and $x$, let $r = b - Ax$ and let
$x' = x + (\langle d, r \rangle / \langle d, Ad \rangle)\, d$ be the step along $d$. Then
$$\|x^* - x'\|_A^2 = \|x^* - x\|_A^2 - \frac{|\langle d, r \rangle|^2}{\operatorname{Re}\langle
  Ad, d \rangle}.$$

No hypothesis on $d$ is needed: for $d = 0$ the step returns $x$ and the quotient is $0/0 = 0$.
The identity follows from Pythagoras in the energy norm for the Galerkin step
(`Projection.step1_isGalerkin`, `IsGalerkin.energyNorm_sq_add`). The case $d = r$ is
`Projection.energyNorm_steepestDescentStep_sq_eq`. Over $\mathbb{R}$ the numerator is
$\langle d, r \rangle^2$. The form $\rho_k = 1 - \sigma_k$ of the source is
`Projection.energyNorm_step1_sq_eq_mul`. -/
theorem energyNorm_step1_sq_eq (hA : A.IsSymmetricCoercive) {xstar : E} (hstar : A xstar = b)
    (d x : E) :
    energyNorm A (xstar - step1 A b d d x) ^ 2
      = energyNorm A (xstar - x) ^ 2
        - ‖inner 𝕜 d (b - A x)‖ ^ 2 / RCLike.re (inner 𝕜 (A d) d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [step1]
  have hq : 0 < RCLike.re (inner 𝕜 (A d) d) := hA.isCoercive.inner_self_pos hd
  have hqK : inner 𝕜 d (A d) = ((RCLike.re (inner 𝕜 (A d) d) : ℝ) : 𝕜) := by
    rw [← hA.isSymmetric d d]
    exact (RCLike.conj_eq_iff_re.1 (by rw [inner_conj_symm, ← hA.isSymmetric d d])).symm
  have hgal := step1_isGalerkin (b := b) hA.isCoercive d x
  have hpy := hgal.energyNorm_sq_add hA hstar (y := x) (by rw [sub_self]; exact zero_mem _)
  have hdiff : step1 A b d d x - x
      = (inner 𝕜 d (b - A x) / ((RCLike.re (inner 𝕜 (A d) d) : ℝ) : 𝕜)) • d := by
    rw [step1, hqK, add_sub_cancel_left]
  have hsmul : energyNorm A (step1 A b d d x - x) ^ 2
      = ‖inner 𝕜 d (b - A x)‖ ^ 2 / RCLike.re (inner 𝕜 (A d) d) := by
    rw [hdiff, hA.energyNorm_sq, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      RCLike.conj_mul, (hA.isSymmetric d d).trans hqK, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul]
    simp only [RCLike.ofReal_re, norm_div, RCLike.norm_ofReal, abs_of_pos hq, div_pow]
    field_simp
  rw [hpy, hsmul]
  ring

/-- **The contraction factor of the exact line search** ([quarteroni2000numerical] (7.38)). Let $A$
be symmetric coercive and let $Ax^* = b$. For all $d$ and $x$, with $r = b - Ax$ and $x'$ the
step along $d$,
$$\|x^* - x'\|_A^2 = (1 - \sigma)\, \|x^* - x\|_A^2, \qquad \sigma = \frac{|\langle d, r
  \rangle|^2}{\operatorname{Re}\langle Ad, d \rangle\, \|x^* - x\|_A^2}.$$
The source writes the factor as $\rho = 1 - \sigma$. When $x = x^*$ both sides are zero. -/
theorem energyNorm_step1_sq_eq_mul (hA : A.IsSymmetricCoercive) {xstar : E} (hstar : A xstar = b)
    (d x : E) :
    energyNorm A (xstar - step1 A b d d x) ^ 2
      = energyNorm A (xstar - x) ^ 2 *
        (1 - ‖inner 𝕜 d (b - A x)‖ ^ 2
              / (RCLike.re (inner 𝕜 (A d) d) * energyNorm A (xstar - x) ^ 2)) := by
  rw [energyNorm_step1_sq_eq hA hstar d x]
  rcases eq_or_ne (energyNorm A (xstar - x)) 0 with h0 | h0
  · have hx : xstar - x = 0 := hA.energyNorm_eq_zero_iff.1 h0
    have hr : b - A x = 0 := by rw [← hstar, ← map_sub, hx, map_zero]
    simp [h0, hr]
  · field_simp

/-- Let $A$ be symmetric coercive and let $Ax^* = b$. For all $d$ and $x$, the step $x'$ along $d$
from $x$ satisfies $\|x^* - x'\|_A \le \|x^* - x\|_A$. -/
theorem energyNorm_step1_le (hA : A.IsSymmetricCoercive) {xstar : E} (hstar : A xstar = b)
    (d x : E) : energyNorm A (xstar - step1 A b d d x) ≤ energyNorm A (xstar - x) := by
  refine energyNorm_le_of_sq_le ?_
  rw [energyNorm_step1_sq_eq hA hstar d x]
  have : 0 ≤ ‖inner 𝕜 d (b - A x)‖ ^ 2 / RCLike.re (inner 𝕜 (A d) d) :=
    div_nonneg (by positivity) (hA.isPositive.re_inner_nonneg_left d)
  linarith

/-- **Strict decrease** ([quarteroni2000numerical] §7.2.4, the remark after (7.38)). Let $A$ be
symmetric coercive and let $Ax^* = b$. If $\langle d, b - Ax \rangle \neq 0$, the step $x'$
along $d$ from $x$ satisfies
$$\|x^* - x'\|_A < \|x^* - x\|_A.$$
If $\langle d, b - Ax \rangle = 0$, the step returns $x$
(`Projection.step1_eq_self_of_inner_eq_zero`). -/
theorem energyNorm_step1_lt (hA : A.IsSymmetricCoercive) {xstar : E} (hstar : A xstar = b)
    {d x : E} (h : inner 𝕜 d (b - A x) ≠ 0) :
    energyNorm A (xstar - step1 A b d d x) < energyNorm A (xstar - x) := by
  have hd : d ≠ 0 := fun hd => h (by rw [hd, inner_zero_left])
  have hq : 0 < RCLike.re (inner 𝕜 (A d) d) := hA.isCoercive.inner_self_pos hd
  have hsq : energyNorm A (xstar - step1 A b d d x) ^ 2 < energyNorm A (xstar - x) ^ 2 := by
    rw [energyNorm_step1_sq_eq hA hstar d x]
    have : 0 < ‖inner 𝕜 d (b - A x)‖ ^ 2 / RCLike.re (inner 𝕜 (A d) d) :=
      div_pos (by positivity) hq
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (energyNorm_nonneg A _) hsq

/-- **Convergence from a contraction.** Let $N : E \to \mathbb{R}$ be nonnegative with
$\|v\| \le C\, N(v)$ for all $v$, and let $0 \le \rho < 1$. If a sequence $(x_k)$ satisfies
$N(x^* - x_{k+1}) \le \rho\, N(x^* - x_k)$ for every $k$, then $x_k \to x^*$.

The function $N$ can be any norm equivalent to the norm of $E$, an energy norm, or the residual
norm of a coercive operator. The convergence theorems of this file use this result. -/
theorem tendsto_of_forall_norm_succ_le {N : E → ℝ} {C ρ : ℝ} {xseq : ℕ → E} {xstar : E}
    (hN : ∀ v : E, ‖v‖ ≤ C * N v) (hN0 : ∀ v : E, 0 ≤ N v) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ k, N (xstar - xseq (k + 1)) ≤ ρ * N (xstar - xseq k)) :
    Filter.Tendsto xseq Filter.atTop (nhds xstar) := by
  have hC : ∀ v : E, ‖v‖ ≤ max C 0 * N v := fun v =>
    (hN v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hN0 v))
  have hgeom : ∀ k, N (xstar - xseq k) ≤ ρ ^ k * N (xstar - xseq 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc N (xstar - xseq (k + 1)) ≤ ρ * N (xstar - xseq k) := h k
          _ ≤ ρ * (ρ ^ k * N (xstar - xseq 0)) := mul_le_mul_of_nonneg_left ih hρ0
          _ = ρ ^ (k + 1) * N (xstar - xseq 0) := by ring
  have hbound : ∀ k, ‖xstar - xseq k‖ ≤ max C 0 * N (xstar - xseq 0) * ρ ^ k := by
    intro k
    calc ‖xstar - xseq k‖ ≤ max C 0 * N (xstar - xseq k) := hC _
      _ ≤ max C 0 * (ρ ^ k * N (xstar - xseq 0)) :=
          mul_le_mul_of_nonneg_left (hgeom k) (le_max_right _ _)
      _ = max C 0 * N (xstar - xseq 0) * ρ ^ k := by ring
  have hpow : Filter.Tendsto (fun k : ℕ => ρ ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hlim : Filter.Tendsto (fun k : ℕ => max C 0 * N (xstar - xseq 0) * ρ ^ k)
      Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul (max C 0 * N (xstar - xseq 0))
  have hzero : Filter.Tendsto (fun k : ℕ => ‖xstar - xseq k‖) Filter.atTop (nhds 0) :=
    squeeze_zero (fun k => norm_nonneg _) hbound hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using hzero

/-! ### Convergence of the steepest-descent iterates -/

/-- Let $E \neq 0$, and let $A$ be symmetric with $\lambda_{\min} \|u\|^2 \le
\operatorname{Re}\langle Au, u \rangle \le \lambda_{\max} \|u\|^2$ for all $u$, where
$0 < \lambda_{\min}$. Then the steepest-descent factor satisfies
$$0 \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}} < 1.$$
On a nonzero space, any nonzero vector forces $\lambda_{\min} \le \lambda_{\max}$. -/
theorem steepestDescentFactor_mem_Ico [Nontrivial E] {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) :
    0 ≤ (lmax - lmin) / (lmax + lmin) ∧ (lmax - lmin) / (lmax + lmin) < 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hv2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have hll : lmin ≤ lmax := by nlinarith [hA.le_re_inner v, hA.re_inner_le v]
  have hs : 0 < lmax + lmin := by linarith
  exact ⟨div_nonneg (by linarith) hs.le, by rw [div_lt_one hs]; linarith⟩

/-- **The steepest-descent rate** ([saad2003iterative] Theorem 5.9, [quarteroni2000numerical]
Theorem 4.10). Let $A$ be symmetric with $\lambda_{\min} \|u\|^2 \le \operatorname{Re}\langle
Au, u \rangle \le \lambda_{\max} \|u\|^2$ for all $u$, where $0 < \lambda_{\min}$, and let
$Ax^* = b$. Let $x_k$ be the $k$-th steepest-descent iterate from $x_0$. Then for every $k$,
$$\|x^* - x_k\|_A \le \left(\frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} +
  \lambda_{\min}}\right)^k \|x^* - x_0\|_A.$$
-/
theorem energyNorm_iterate_steepestDescentStep_le {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) {xstar : E} (hstar : A xstar = b) (x₀ : E) (k : ℕ) :
    energyNorm A (xstar - (steepestDescentStep A b)^[k] x₀) ≤
      ((lmax - lmin) / (lmax + lmin)) ^ k * energyNorm A (xstar - x₀) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim _ (0 : E), energyNorm]
  have hρ := (steepestDescentFactor_mem_Ico hl hA).1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact (energyNorm_steepestDescentStep_le hl hA hstar _).trans
      (mul_le_mul_of_nonneg_left ih hρ)

/-- **Convergence of steepest descent** ([saad2003iterative] Theorem 5.9, [quarteroni2000numerical]
Theorem 4.10). Let $A$ be symmetric with $\lambda_{\min} \|u\|^2 \le \operatorname{Re}\langle
Au, u \rangle \le \lambda_{\max} \|u\|^2$ for all $u$, where $0 < \lambda_{\min}$, and let
$Ax^* = b$. Then for every $x_0$ the steepest-descent iterates from $x_0$ converge to $x^*$.

The energy norm of the error contracts by a factor less than $1$, and it is at least
$\sqrt{\lambda_{\min}}$ times the norm (`Projection.tendsto_of_forall_norm_succ_le`). -/
theorem tendsto_iterate_steepestDescentStep {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) {xstar : E} (hstar : A xstar = b) (x₀ : E) :
    Filter.Tendsto (fun k => (steepestDescentStep A b)^[k] x₀) Filter.atTop (nhds xstar) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [Subsingleton.elim _ xstar]
    exact tendsto_const_nhds
  obtain ⟨hρ0, hρ1⟩ := steepestDescentFactor_mem_Ico hl hA
  have hs : 0 < Real.sqrt lmin := Real.sqrt_pos.2 hl
  refine tendsto_of_forall_norm_succ_le (N := energyNorm A) (C := (Real.sqrt lmin)⁻¹)
    (fun v => ?_) (energyNorm_nonneg A) hρ0 hρ1 fun k => ?_
  · rw [← div_eq_inv_mul, le_div_iff₀ hs, mul_comm]
    exact hA.isCoerciveWith.norm_le_energyNorm hl.le v
  · rw [Function.iterate_succ_apply']
    exact energyNorm_steepestDescentStep_le hl hA hstar _

end Projection
