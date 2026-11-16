/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Matrix.PosDef
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.Stationary.Splitting

/-!
# The alternating direction implicit iteration

Let $H$ and $V$ be continuous linear operators on an inner product space $E$ over $\mathbb{R}$ or
$\mathbb{C}$, and let $r > 0$. The **Peaceman–Rachford iteration** for $(H + V) x = b$ splits each
sweep into two half-steps, and each half-step inverts only one of the two terms:
$$(H + rI) x_{k+1/2} = (rI - V) x_k + b, \qquad (V + rI) x_{k+1} = (rI - H) x_{k+1/2} + b.$$
Their composition is the affine iteration $x \mapsto P_r x + f_r(b)$ with
$$P_r = (V + rI)^{-1} (H - rI) (H + rI)^{-1} (V - rI), \qquad f_r(b) = (V + rI)^{-1} \bigl(I - (H -
  rI)(H + rI)^{-1}\bigr) b,$$
and it comes from the splitting $H + V = M - N$ with $M = (2r)^{-1} (H + rI)(V + rI)$ and
$N = (2r)^{-1} (H - rI)(V - rI)$. This is Algorithm 4.3 and the identities (4.50)–(4.52) of
[saad2003iterative], §4.3. The source states no numbered result there and asserts the convergence in
one sentence. This module proves that if $H$ and $V$ are coercive, the iterates converge from every
starting vector, and that the spectral radius of $P_r$ is less than $1$.

Following [quarteroni2000numerical], §4.3.6, the module also treats the two-parameter sweep $P_{r_1,
r_2} = (V + r_2 I)^{-1} (H - r_2 I) (H + r_1 I)^{-1} (V - r_1 I)$, where $r_i = 1/\alpha_i$ for the
parameters $\alpha_1, \alpha_2$ of the source; the one-parameter sweep is the case $r_1 = r_2$. For
symmetric positive definite $H$ and $V$, the spectral radius of $P_{r_1, r_2}$ is at most the
product of the maxima of $|\lambda - r_2| / (\lambda + r_1)$ over the spectrum of $H$ and of
$|\mu - r_1| / (\mu + r_2)$ over the spectrum of $V$. When both spectra lie in $[\gamma, \delta]$
with $\gamma > 0$, the parameter $r = \sqrt{\gamma \delta}$ gives $\rho(P_r) \le \bigl((1 -
\sqrt{\gamma/\delta}) / (1 + \sqrt{\gamma/\delta})\bigr)^2$. The last section states these results
for matrices.

## Main definitions

* `Stationary.peacemanRachford`: the sweep operator $P_r$ of (4.50) in [saad2003iterative].
* `Stationary.peacemanRachfordConst`: the affine part $f_r(b)$ of (4.51) in [saad2003iterative].
* `Stationary.peacemanRachfordSplitting`: the splitting $H + V = M - N$ of (4.52) in
  [saad2003iterative].
* `Stationary.peacemanRachfordTwo`: the two-parameter sweep operator $P_{r_1, r_2}$.
* `Stationary.peacemanRachfordTwoConst` and `Stationary.peacemanRachfordTwoSweep`: the affine part
  of the two-parameter sweep, and the sweep written as two half-steps.

## Main results

* `Stationary.norm_sub_smul_sq_add_le_norm_add_smul_sq`: the Cayley inequality
  $\|Ax - rx\|^2 + 4rc\|x\|^2 \le \|Ax + rx\|^2$ for $A$ coercive with constant $c$.
* `Stationary.norm_cayley_lt_one`: the Cayley transform $(A - rI)(A + rI)^{-1}$ of a coercive
  operator is a strict contraction.
* `Stationary.norm_conj_peacemanRachford_lt_one`: for coercive $H$ and $V$,
  $\|(V + rI) P_r (V + rI)^{-1}\| < 1$.
* `Stationary.spectralRadius_peacemanRachford_lt_one`: for coercive $H$ and $V$, $\rho(P_r) < 1$.
* `Stationary.tendsto_peacemanRachford`: for coercive $H$ and $V$, the iterates converge to the
  solution of $(H + V) x = b$ from every starting vector.
* `Stationary.norm_cayleyTwo_le`: the norm of $(A - r_2 I)(A + r_1 I)^{-1}$ for a self-adjoint $A$
  is bounded by any bound of $|t - r_2| / |t + r_1|$ on the spectrum.
* `Stationary.spectralRadius_peacemanRachfordTwo_le`: the spectral bound for the two-parameter sweep
  of symmetric positive definite operators.
* `Stationary.spectralRadius_peacemanRachford_le_of_spectrum_subset`: the bound for spectra in
  $[\gamma, \delta]$ with $r = \sqrt{\gamma\delta}$.
* `Matrix.PosDef.complexSpectralRadius_peacemanRachford_lt_one`,
  `Matrix.PosDef.complexSpectralRadius_peacemanRachfordTwo_le` and
  `Matrix.IsHermitian.complexSpectralRadius_peacemanRachford_le_of_spectrum_subset`: the spectral
  bounds for real symmetric positive definite matrices.

## Proof outline

The convergence proof rests on one inequality. If $\operatorname{Re} \langle Ax, x \rangle \ge c
\|x\|^2$ for all $x$ and $r > 0$, then $\|Ax - rx\|^2 + 4rc\|x\|^2 \le \|Ax + rx\|^2$, which is the
expansion of both sides. It says that the Cayley transform $(A - rI)(A + rI)^{-1}$ is a strict
contraction, with the factor $1 - 4rc / (\|A\| + r)^2$. Conjugation by $V + rI$ turns $P_r$ into the
product of the Cayley transforms of $H$ and of $V$. So this product is a strict contraction, $P_r$
is similar to it, and the iterates converge from every starting vector. For the two-parameter
bounds, the norm of the Cayley transform $(A - r_2 I)(A + r_1 I)^{-1}$ of a self-adjoint $A$ is the
maximum of $|t - r_2| / |t + r_1|$ over the spectrum, by the continuous functional calculus.

## Implementation notes

* No commutativity of $H$ and $V$ is used. The commutativity hypothesis of the literature belongs to
  the theory of the optimal sequence of parameters, which is not treated here. The splitting
  identity $M - N = H + V$ does not need it either, because the terms $HV$ cancel.
* No symmetry is used for convergence. Coercivity alone, $\operatorname{Re} \langle Hx, x \rangle
  \ge c \|x\|^2$ with $c > 0$, which a symmetric positive definite operator has, carries the
  argument. So the convergence theorem covers nonsymmetric $H$ and $V$.
* The bound $\|P_r\| < 1$ is false in general. Only the conjugated operator
  $(V + rI) P_r (V + rI)^{-1}$ is a contraction in the operator norm. The operator $P_r$ itself
  satisfies the spectral radius bound, and convergence rests on that bound.
* The results are stated in an inner product space, complete where an inverse is needed. Inverses of
  operators are `Ring.inverse`, which is $0$ at a non-invertible operator. Matrices reach the
  operator results through `Matrix.toEuclideanCLM`, and real matrices through `Matrix.complexify`
  and `Matrix.complexSpectralRadius`.
* The bounds for symmetric positive definite operators are stated on a complex Hilbert space, where
  the continuous functional calculus of a self-adjoint operator is available.
* In the bound for spectra in $[\gamma, \delta]$, the source adds the proviso
  "$\gamma/\delta \to 0$". It is not a hypothesis of the bound.
-/

open Filter Topology

namespace Stationary

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### The Cayley contraction inequality -/

/-- The **Cayley inequality**. Let $E$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$,
let $c \in \mathbb{R}$, and let $A$ be a linear operator on $E$ with $\operatorname{Re} \langle
Ax, x \rangle \ge c \|x\|^2$ for every $x \in E$. Let $r > 0$. Then for every $x \in E$,
$$\|Ax - rx\|^2 + 4rc\|x\|^2 \le \|Ax + rx\|^2.$$

Both sides expand to $\|Ax\|^2 \pm 2r \operatorname{Re} \langle Ax, x \rangle + r^2 \|x\|^2$, so
the content is the lower bound on the cross term. The statement uses neither symmetry, nor
completeness, nor finite dimension. The hypothesis on $A$ is `LinearMap.IsCoerciveWith A c`. -/
theorem norm_sub_smul_sq_add_le_norm_add_smul_sq {A : E →ₗ[𝕜] E} {c : ℝ}
    (hA : A.IsCoerciveWith c) {r : ℝ} (hr : 0 < r) (x : E) :
    ‖A x - (r : 𝕜) • x‖ ^ 2 + 4 * r * c * ‖x‖ ^ 2 ≤ ‖A x + (r : 𝕜) • x‖ ^ 2 := by
  have h1 : RCLike.re (inner 𝕜 (A x) ((r : 𝕜) • x)) = r * RCLike.re (inner 𝕜 (A x) x) := by
    rw [inner_smul_right, RCLike.re_ofReal_mul]
  have h2 : ‖((r : 𝕜) • x)‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hr, mul_pow]
  rw [norm_add_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜), h1, h2]
  nlinarith [hA x]

/-- Let $A$ be a linear operator on an inner product space with $\operatorname{Re} \langle Ax, x
\rangle \ge c \|x\|^2$ for all $x$, where $c > 0$, and let $r > 0$. Then
$\|Ax - rx\| < \|Ax + rx\|$ for every $x \neq 0$. -/
theorem norm_sub_smul_lt_norm_add_smul {A : E →ₗ[𝕜] E} {c : ℝ} (hA : A.IsCoerciveWith c)
    (hc : 0 < c) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ≠ 0) :
    ‖A x - (r : 𝕜) • x‖ < ‖A x + (r : 𝕜) • x‖ := by
  have h := norm_sub_smul_sq_add_le_norm_add_smul_sq hA hr x
  have hpos : (0 : ℝ) < 4 * r * c * ‖x‖ ^ 2 := by positivity
  have hlt : ‖A x - (r : 𝕜) • x‖ ^ 2 < ‖A x + (r : 𝕜) • x‖ ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt

/-! ### The Cayley transform of a coercive operator -/

section Cayley

variable [CompleteSpace E]

/-- Let $E$ be a Hilbert space over $\mathbb{R}$ or $\mathbb{C}$, let $c > 0$, let $A$ be a
continuous linear operator on $E$ with $\operatorname{Re} \langle Ax, x \rangle \ge c \|x\|^2$
for all $x$, and let $r > 0$. Then $A + rI$ is invertible.

The operator $A + rI$ is coercive with constant $c + r$, and the Lax–Milgram theorem gives the
inverse. -/
theorem isUnit_add_smul_one {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {r : ℝ} (hr : 0 < r) :
    IsUnit (A + (r : 𝕜) • (1 : E →L[𝕜] E)) := by
  obtain ⟨e, he, -⟩ := ContinuousLinearMap.exists_equiv_of_isCoerciveWith
    (by linarith : (0 : ℝ) < c + r) (ContinuousLinearMap.isCoerciveWith_add_smul_one hA (r := r))
  refine ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 E).symm e, ?_⟩
  rw [← he]
  ext x
  rw [← ContinuousLinearEquiv.unitsEquiv_apply 𝕜 E, MulEquiv.apply_symm_apply]
  rfl

/-- Let $E$ be a Hilbert space over $\mathbb{R}$ or $\mathbb{C}$, let $c > 0$, let $A$ be a
continuous linear operator on $E$ with $\operatorname{Re} \langle Ax, x \rangle \ge c \|x\|^2$
for all $x$, and let $r > 0$. Then the Cayley transform $(A - rI)(A + rI)^{-1}$ satisfies, for
every $y \in E$,
$$\bigl\|(A - rI)(A + rI)^{-1} y\bigr\|^2 \le \left(1 - \frac{4rc}{(\|A\| + r)^2}\right)
  \|y\|^2.$$

The proof applies the Cayley inequality at $x = (A + rI)^{-1} y$ and uses
$\|y\| \le (\|A\| + r) \|x\|$. -/
theorem norm_cayley_apply_sq_le {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {r : ℝ} (hr : 0 < r) (y : E) :
    ‖((A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)) y‖ ^ 2
      ≤ (1 - 4 * r * c / (‖A‖ + r) ^ 2) * ‖y‖ ^ 2 := by
  have hu : IsUnit (A + (r : 𝕜) • (1 : E →L[𝕜] E)) := isUnit_add_smul_one hc hA hr
  have hSx : (A + (r : 𝕜) • (1 : E →L[𝕜] E)) (Ring.inverse (A + (r : 𝕜) • 1) y) = y := by
    have h := Ring.mul_inverse_cancel _ hu
    calc (A + (r : 𝕜) • (1 : E →L[𝕜] E)) (Ring.inverse (A + (r : 𝕜) • 1) y)
        = ((A + (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)) y := rfl
      _ = y := by rw [h]; rfl
  set x : E := Ring.inverse (A + (r : 𝕜) • 1) y with hxdef
  have hsum : A x + (r : 𝕜) • x = y := by simpa using hSx
  have hLHS : ((A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)) y = A x - (r : 𝕜) • x := by
    simp [hxdef]
  have hkey : ‖A x - (r : 𝕜) • x‖ ^ 2 + 4 * r * c * ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    have h := norm_sub_smul_sq_add_le_norm_add_smul_sq hA hr x
    simp only [ContinuousLinearMap.coe_coe] at h
    rwa [hsum] at h
  have hnormS : ‖A + (r : 𝕜) • (1 : E →L[𝕜] E)‖ ≤ ‖A‖ + r := by
    refine (norm_add_le _ _).trans ?_
    have hone : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have : ‖(r : 𝕜) • (1 : E →L[𝕜] E)‖ ≤ r := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hr]
      nlinarith
    linarith
  have hlow : ‖y‖ ≤ (‖A‖ + r) * ‖x‖ := by
    rw [← hSx]
    calc ‖(A + (r : 𝕜) • (1 : E →L[𝕜] E)) x‖
        ≤ ‖A + (r : 𝕜) • (1 : E →L[𝕜] E)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ x
      _ ≤ (‖A‖ + r) * ‖x‖ := by gcongr
  have hy2 : ‖y‖ ^ 2 ≤ (‖A‖ + r) ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg y, norm_nonneg x]
  have h4rc : (0 : ℝ) ≤ 4 * r * c := by positivity
  have hq : 4 * r * c / (‖A‖ + r) ^ 2 * ‖y‖ ^ 2 ≤ 4 * r * c * ‖x‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hy2 h4rc]
  rw [hLHS, sub_mul, one_mul]
  linarith

/-- Let $E$ be a Hilbert space over $\mathbb{R}$ or $\mathbb{C}$, let $c > 0$, let $A$ be a
continuous linear operator on $E$ with $\operatorname{Re} \langle Ax, x \rangle \ge c \|x\|^2$
for all $x$, and let $r > 0$. Then the Cayley transform of $A$ is a strict contraction:
$$\bigl\|(A - rI)(A + rI)^{-1}\bigr\| < 1.$$

The inverse is `Ring.inverse`. -/
theorem norm_cayley_lt_one {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {r : ℝ} (hr : 0 < r) :
    ‖(A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)‖ < 1 := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hz : ((A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)) = 0 := by
      ext x; exact Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact zero_lt_one
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hcA : c ≤ ‖A‖ := by
      have h1 : c * ‖v‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A v) v) := hA v
      have h2 : RCLike.re (inner 𝕜 (A v) v) ≤ ‖A‖ * ‖v‖ ^ 2 :=
        calc RCLike.re (inner 𝕜 (A v) v) ≤ ‖inner 𝕜 (A v) v‖ := RCLike.re_le_norm _
          _ ≤ ‖A v‖ * ‖v‖ := norm_inner_le_norm _ _
          _ ≤ ‖A‖ * ‖v‖ * ‖v‖ := by gcongr; exact A.le_opNorm v
          _ = ‖A‖ * ‖v‖ ^ 2 := by ring
      exact le_of_mul_le_mul_right (by linarith) (by positivity : (0 : ℝ) < ‖v‖ ^ 2)
    have hq0 : (0 : ℝ) ≤ 1 - 4 * r * c / (‖A‖ + r) ^ 2 := by
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith [sq_nonneg (‖A‖ - r), norm_nonneg A]
    have hq1 : 1 - 4 * r * c / (‖A‖ + r) ^ 2 < 1 := by
      have : (0 : ℝ) < 4 * r * c / (‖A‖ + r) ^ 2 := by positivity
      linarith
    have hbound : ‖(A - (r : 𝕜) • 1) * Ring.inverse (A + (r : 𝕜) • 1)‖
        ≤ Real.sqrt (1 - 4 * r * c / (‖A‖ + r) ^ 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num)
        (by positivity) ?_
      rw [mul_pow, Real.sq_sqrt hq0]
      exact norm_cayley_apply_sq_le hc hA hr y
    have hsq : Real.sqrt (1 - 4 * r * c / (‖A‖ + r) ^ 2) < 1 := by
      have h := Real.sqrt_lt_sqrt hq0 hq1
      rwa [Real.sqrt_one] at h
    linarith

end Cayley

/-! ### The Peaceman–Rachford sweep -/

/-- The **Peaceman–Rachford sweep operator** with parameter $r$ of two continuous linear operators
$H$ and $V$ is
$$P_r = (V + rI)^{-1} (H - rI) (H + rI)^{-1} (V - rI).$$
This is (4.50) of [saad2003iterative].

The inverses are `Ring.inverse`, which is $0$ at a non-invertible operator. -/
noncomputable def peacemanRachford (H V : E →L[𝕜] E) (r : ℝ) : E →L[𝕜] E :=
  Ring.inverse (V + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) *
    (V - (r : 𝕜) • 1)

/-- The **affine part** of one Peaceman–Rachford sweep with parameter $r$ and right-hand side $b$ is
$$f_r(b) = (V + rI)^{-1} \bigl(I - (H - rI)(H + rI)^{-1}\bigr) b.$$
This is (4.51) of [saad2003iterative]. -/
noncomputable def peacemanRachfordConst (H V : E →L[𝕜] E) (r : ℝ) (b : E) : E :=
  Ring.inverse (V + (r : 𝕜) • 1) ((1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) b)

/-- One sweep of Algorithm 4.3 of [saad2003iterative], written as its two half-steps: from $x_k$,
solve $(H + rI) x_{k+1/2} = (rI - V) x_k + b$, and then solve
$(V + rI) x_{k+1} = (rI - H) x_{k+1/2} + b$. -/
noncomputable def peacemanRachfordSweep (H V : E →L[𝕜] E) (r : ℝ) (b x : E) : E :=
  Ring.inverse (V + (r : 𝕜) • 1)
    (((r : 𝕜) • 1 - H) (Ring.inverse (H + (r : 𝕜) • 1) (((r : 𝕜) • 1 - V) x + b)) + b)

/-- For all $b$ and $x$, the two half-steps of Algorithm 4.3 of [saad2003iterative], applied to $x$,
give the affine step $P_r x + f_r(b)$ of (4.50)–(4.51). -/
theorem peacemanRachford_step_eq (H V : E →L[𝕜] E) (r : ℝ) (b x : E) :
    step (peacemanRachford H V r) (peacemanRachfordConst H V r b) x
      = peacemanRachfordSweep H V r b x := by
  simp only [step, peacemanRachford, peacemanRachfordConst, peacemanRachfordSweep,
    mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self, map_add, map_sub, map_smul]
  module

/-! ### The Peaceman–Rachford splitting -/

section Splitting

variable {H V : E →L[𝕜] E} {r : ℝ}

/-- A nonzero scalar multiple of an invertible operator is invertible. -/
private theorem isUnit_smul {c : 𝕜} (hc : c ≠ 0) {X : E →L[𝕜] E} (hX : IsUnit X) :
    IsUnit (c • X) := by
  have h1 : IsUnit (c • (1 : E →L[𝕜] E)) :=
    ⟨⟨c • 1, c⁻¹ • 1, by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hc, one_smul],
      by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hc, one_smul]⟩, rfl⟩
  simpa [smul_mul_assoc] using h1.mul hX

/-- A scalar multiple of the identity commutes with every operator. -/
private theorem smul_one_mul_comm (c : 𝕜) (T : E →L[𝕜] E) :
    (c • (1 : E →L[𝕜] E)) * T = T * (c • (1 : E →L[𝕜] E)) := by
  ext y
  simp

/-- The operators $H + rI$ and $H - rI$ commute; this is the only commutation used in this module,
and it involves $H$ alone, never $H$ together with $V$. -/
private theorem commute_add_sub_smul_one (H : E →L[𝕜] E) (r : ℝ) :
    (H + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) = (H - (r : 𝕜) • 1) * (H + (r : 𝕜) • 1) := by
  simp only [mul_sub, sub_mul, add_mul, mul_add, smul_one_mul_comm]
  abel

/-- Let $H$ and $V$ be continuous linear operators, let $r \neq 0$, and let $H + rI$ and $V + rI$ be
invertible. The **Peaceman–Rachford splitting** is the splitting $H + V = M - N$ with
$$M = (2r)^{-1} (H + rI)(V + rI).$$
This is (4.52) of [saad2003iterative].

The identity $M - N = H + V$, with $N = (2r)^{-1} (H - rI)(V - rI)$, is pure ring algebra: the
terms $HV$ cancel, so no commutativity of $H$ and $V$ is used. -/
noncomputable def peacemanRachfordSplitting (H V : E →L[𝕜] E) {r : ℝ} (hr : r ≠ 0)
    (hH : IsUnit (H + (r : 𝕜) • 1)) (hV : IsUnit (V + (r : 𝕜) • 1)) :
    Splitting (H + V) :=
  ⟨(2 * (r : 𝕜))⁻¹ • ((H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1)),
    isUnit_smul (inv_ne_zero (mul_ne_zero two_ne_zero (RCLike.ofReal_ne_zero.2 hr)))
      (hH.mul hV)⟩

variable {hr : r ≠ 0} {hH : IsUnit (H + (r : 𝕜) • 1)} {hV : IsUnit (V + (r : 𝕜) • 1)}

/-- The Peaceman–Rachford splitting has $M = (2r)^{-1} (H + rI)(V + rI)$, as in (4.52) of
[saad2003iterative]. -/
theorem peacemanRachfordSplitting_m :
    (peacemanRachfordSplitting H V hr hH hV).m
      = (2 * (r : 𝕜))⁻¹ • ((H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1)) := rfl

/-- The Peaceman–Rachford splitting has $N = (2r)^{-1} (H - rI)(V - rI)$, as in (4.52) of
[saad2003iterative]. The terms $HV$ cancel in $M - (H + V)$, so the splitting needs no
commutativity. -/
theorem peacemanRachfordSplitting_n :
    (peacemanRachfordSplitting H V hr hH hV).n
      = (2 * (r : 𝕜))⁻¹ • ((H - (r : 𝕜) • 1) * (V - (r : 𝕜) • 1)) := by
  have hs : (2 * (r : 𝕜)) ≠ 0 := mul_ne_zero two_ne_zero (RCLike.ofReal_ne_zero.2 hr)
  have hn : (peacemanRachfordSplitting H V hr hH hV).n
      = (2 * (r : 𝕜))⁻¹ • ((H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1)) - (H + V) := rfl
  have hexp : (H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1) - (2 * (r : 𝕜)) • (H + V)
      = (H - (r : 𝕜) • 1) * (V - (r : 𝕜) • 1) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one]
    module
  rw [hn, ← hexp, smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The iteration operator $M^{-1} N$ of the Peaceman–Rachford splitting (4.52) is the sweep
operator $P_r$ of (4.50) in [saad2003iterative]. The two expressions differ by
$(H + rI)^{-1} (H - rI) = (H - rI)(H + rI)^{-1}$, a commutation of $H$ with itself. -/
theorem peacemanRachfordSplitting_iterationOperator :
    (peacemanRachfordSplitting H V hr hH hV).iterationOperator = peacemanRachford H V r := by
  have hmu := (peacemanRachfordSplitting H V hr hH hV).isUnit
  refine hmu.mul_left_cancel ?_
  rw [Splitting.iterationOperator_eq, ← mul_assoc, Ring.mul_inverse_cancel _ hmu, one_mul,
    peacemanRachfordSplitting_n, peacemanRachfordSplitting_m, peacemanRachford, smul_mul_assoc]
  congr 1
  symm
  calc (H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1) *
        (Ring.inverse (V + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) *
          (V - (r : 𝕜) • 1))
      = (H + (r : 𝕜) • 1) * ((V + (r : 𝕜) • 1) * Ring.inverse (V + (r : 𝕜) • 1)) *
          ((H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) * (V - (r : 𝕜) • 1)) := by
        noncomm_ring
    _ = (H + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) *
          (Ring.inverse (H + (r : 𝕜) • 1) * (V - (r : 𝕜) • 1)) := by
        rw [Ring.mul_inverse_cancel _ hV]; noncomm_ring
    _ = (H - (r : 𝕜) • 1) * ((H + (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) *
          (V - (r : 𝕜) • 1) := by
        rw [commute_add_sub_smul_one]; noncomm_ring
    _ = (H - (r : 𝕜) • 1) * (V - (r : 𝕜) • 1) := by
        rw [Ring.mul_inverse_cancel _ hH]; noncomm_ring

/-- The Peaceman–Rachford splitting has
$$M^{-1} = (V + rI)^{-1} \bigl(I - (H - rI)(H + rI)^{-1}\bigr),$$
which equals $2r (V + rI)^{-1} (H + rI)^{-1}$. This is Problem P-4.5 of [saad2003iterative]. -/
theorem peacemanRachfordSplitting_ringInverse_m :
    Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m
      = Ring.inverse (V + (r : 𝕜) • 1) *
          (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) := by
  have hs : (2 * (r : 𝕜)) ≠ 0 := mul_ne_zero two_ne_zero (RCLike.ofReal_ne_zero.2 hr)
  have hmu := (peacemanRachfordSplitting H V hr hH hV).isUnit
  have hmk : (peacemanRachfordSplitting H V hr hH hV).m *
      (Ring.inverse (V + (r : 𝕜) • 1) *
        (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1))) = 1 := by
    rw [peacemanRachfordSplitting_m, smul_mul_assoc]
    have hkey : (H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1) *
        (Ring.inverse (V + (r : 𝕜) • 1) *
          (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)))
        = (2 * (r : 𝕜)) • (1 : E →L[𝕜] E) := by
      calc (H + (r : 𝕜) • 1) * (V + (r : 𝕜) • 1) *
            (Ring.inverse (V + (r : 𝕜) • 1) *
              (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)))
          = (H + (r : 𝕜) • 1) * ((V + (r : 𝕜) • 1) * Ring.inverse (V + (r : 𝕜) • 1)) *
              (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) := by noncomm_ring
        _ = (H + (r : 𝕜) • 1) -
              (H + (r : 𝕜) • 1) * (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1) := by
            rw [Ring.mul_inverse_cancel _ hV]; noncomm_ring
        _ = (H + (r : 𝕜) • 1) -
              (H - (r : 𝕜) • 1) * ((H + (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) := by
            rw [commute_add_sub_smul_one]; noncomm_ring
        _ = (2 * (r : 𝕜)) • (1 : E →L[𝕜] E) := by
            rw [Ring.mul_inverse_cancel _ hH, mul_one]
            module
    rw [hkey, smul_smul, inv_mul_cancel₀ hs, one_smul]
  calc Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m
      = Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m *
          ((peacemanRachfordSplitting H V hr hH hV).m *
            (Ring.inverse (V + (r : 𝕜) • 1) *
              (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)))) := by
        rw [hmk, mul_one]
    _ = Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m *
          (peacemanRachfordSplitting H V hr hH hV).m *
          (Ring.inverse (V + (r : 𝕜) • 1) *
            (1 - (H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1))) := by rw [mul_assoc]
    _ = _ := by rw [Ring.inverse_mul_cancel _ hmu, one_mul]

/-- For every $b$, the Peaceman–Rachford splitting has $M^{-1} b = f_r(b)$, the affine part (4.51)
of the sweep ([saad2003iterative], Problem P-4.5). -/
theorem peacemanRachfordSplitting_const (b : E) :
    Ring.inverse (peacemanRachfordSplitting H V hr hH hV).m b
      = peacemanRachfordConst H V r b := by
  rw [peacemanRachfordSplitting_ringInverse_m, mul_apply_eq_comp, peacemanRachfordConst]

end Splitting

/-! ### The two-parameter sweep -/

section Two

variable (H V : E →L[𝕜] E) (r₁ r₂ : ℝ)

/-- The **two-parameter Peaceman–Rachford sweep operator** with parameters $r_1$ and $r_2$ of two
continuous linear operators $H$ and $V$ is
$$P_{r_1, r_2} = (V + r_2 I)^{-1} (H - r_2 I) (H + r_1 I)^{-1} (V - r_1 I).$$
It is the iteration operator of the composition of the half-steps
$(H + r_1 I) x_{k+1/2} = (r_1 I - V) x_k + b$ and $(V + r_2 I) x_{k+1} = (r_2 I - H) x_{k+1/2} +
b$. This is (4.50) of [quarteroni2000numerical] with $A_1 = H$, $A_2 = V$ and
$\alpha_i = 1/r_i$.

The source writes the factors as $I - \alpha A = -\alpha (A - \alpha^{-1} I)$, and the signs
cancel between the two factors. The one-parameter operator `Stationary.peacemanRachford` is the
case $r_1 = r_2$ (`Stationary.peacemanRachfordTwo_self`). -/
noncomputable def peacemanRachfordTwo : E →L[𝕜] E :=
  Ring.inverse (V + (r₂ : 𝕜) • 1) * (H - (r₂ : 𝕜) • 1) * Ring.inverse (H + (r₁ : 𝕜) • 1) *
    (V - (r₁ : 𝕜) • 1)

/-- The **affine part** of the two-parameter Peaceman–Rachford sweep with right-hand side $b$ is
$$(V + r_2 I)^{-1} \bigl(I - (H - r_2 I)(H + r_1 I)^{-1}\bigr) b.$$
This is the vector $f$ of [quarteroni2000numerical], §4.3.6. -/
noncomputable def peacemanRachfordTwoConst (b : E) : E :=
  Ring.inverse (V + (r₂ : 𝕜) • 1) ((1 - (H - (r₂ : 𝕜) • 1) * Ring.inverse (H + (r₁ : 𝕜) • 1)) b)

/-- The two-parameter Peaceman–Rachford sweep, written as its two half-steps: from $x_k$, solve
$(H + r_1 I) x_{k+1/2} = (r_1 I - V) x_k + b$, and then solve $(V + r_2 I) x_{k+1} = (r_2 I - H)
x_{k+1/2} + b$.

The inverses are `Ring.inverse`. -/
noncomputable def peacemanRachfordTwoSweep (b x : E) : E :=
  Ring.inverse (V + (r₂ : 𝕜) • 1)
    (((r₂ : 𝕜) • 1 - H) (Ring.inverse (H + (r₁ : 𝕜) • 1) (((r₁ : 𝕜) • 1 - V) x + b)) + b)

/-- For all $b$ and $x$, the two half-steps of the two-parameter sweep, applied to $x$, give the
affine step $P_{r_1, r_2} x + f$, where $f$ is the affine part
`Stationary.peacemanRachfordTwoConst`. -/
theorem peacemanRachfordTwo_step_eq (b x : E) :
    step (peacemanRachfordTwo H V r₁ r₂) (peacemanRachfordTwoConst H V r₁ r₂ b) x
      = peacemanRachfordTwoSweep H V r₁ r₂ b x := by
  simp only [step, peacemanRachfordTwo, peacemanRachfordTwoConst, peacemanRachfordTwoSweep,
    mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self, map_add, map_sub, map_smul]
  module

/-- For equal parameters, the two-parameter sweep operator is the one-parameter one:
$P_{r, r} = P_r$. -/
theorem peacemanRachfordTwo_self (r : ℝ) :
    peacemanRachfordTwo H V r r = peacemanRachford H V r := rfl

/-- For equal parameters, the affine part of the two-parameter sweep is the affine part $f_r(b)$ of
the one-parameter sweep. -/
theorem peacemanRachfordTwoConst_self (r : ℝ) (b : E) :
    peacemanRachfordTwoConst H V r r b = peacemanRachfordConst H V r b := rfl

/-- Let $V + r_2 I$ be invertible. Then conjugation by $V + r_2 I$ turns the two-parameter sweep
operator into the product of two Cayley transforms:
$$(V + r_2 I) P_{r_1, r_2} (V + r_2 I)^{-1} = (H - r_2 I)(H + r_1 I)^{-1} \cdot (V - r_1 I)(V +
  r_2 I)^{-1}.$$
-/
theorem peacemanRachfordTwo_conj (hV : IsUnit (V + (r₂ : 𝕜) • (1 : E →L[𝕜] E))) :
    (V + (r₂ : 𝕜) • 1) * peacemanRachfordTwo H V r₁ r₂ * Ring.inverse (V + (r₂ : 𝕜) • 1)
      = ((H - (r₂ : 𝕜) • 1) * Ring.inverse (H + (r₁ : 𝕜) • 1)) *
        ((V - (r₁ : 𝕜) • 1) * Ring.inverse (V + (r₂ : 𝕜) • 1)) := by
  rw [peacemanRachfordTwo]
  calc (V + (r₂ : 𝕜) • 1) *
        (Ring.inverse (V + (r₂ : 𝕜) • 1) * (H - (r₂ : 𝕜) • 1) * Ring.inverse (H + (r₁ : 𝕜) • 1) *
          (V - (r₁ : 𝕜) • 1)) * Ring.inverse (V + (r₂ : 𝕜) • 1)
      = ((V + (r₂ : 𝕜) • 1) * Ring.inverse (V + (r₂ : 𝕜) • 1)) *
          ((H - (r₂ : 𝕜) • 1) * Ring.inverse (H + (r₁ : 𝕜) • 1) * (V - (r₁ : 𝕜) • 1) *
            Ring.inverse (V + (r₂ : 𝕜) • 1)) := by noncomm_ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hV, one_mul]; noncomm_ring

end Two

/-! ### Convergence -/

section Convergence

variable [CompleteSpace E] {H V : E →L[𝕜] E} {r : ℝ}

omit [CompleteSpace E] in
/-- Let $V + rI$ be invertible. Then conjugation by $V + rI$ turns the sweep operator (4.50) into
the product of the Cayley transforms of $H$ and of $V$:
$$(V + rI) P_r (V + rI)^{-1} = (H - rI)(H + rI)^{-1} \cdot (V - rI)(V + rI)^{-1}.$$
-/
theorem peacemanRachford_conj (hV : IsUnit (V + (r : 𝕜) • (1 : E →L[𝕜] E))) :
    (V + (r : 𝕜) • 1) * peacemanRachford H V r * Ring.inverse (V + (r : 𝕜) • 1)
      = ((H - (r : 𝕜) • 1) * Ring.inverse (H + (r : 𝕜) • 1)) *
        ((V - (r : 𝕜) • 1) * Ring.inverse (V + (r : 𝕜) • 1)) :=
  peacemanRachfordTwo_conj H V r r hV

/-- Let $E$ be a Hilbert space over $\mathbb{R}$ or $\mathbb{C}$, let $H$ and $V$ be coercive
continuous linear operators on $E$, and let $r > 0$. Then
$$\bigl\|(V + rI) P_r (V + rI)^{-1}\bigr\| < 1.$$
This is the convergence theorem that §4.3 of [saad2003iterative] asserts without proof, in its
sharp operator form.

Coercive means $\operatorname{Re} \langle Ax, x \rangle \ge c \|x\|^2$ for all $x$, for some
$c > 0$ (`LinearMap.IsCoercive`). Neither symmetry nor commutativity of $H$ and $V$ is used. The
operator $P_r$ itself need not have norm less than $1$. For this reason the statement is made
for the conjugated operator, and the spectral radius bound
`Stationary.spectralRadius_peacemanRachford_lt_one` is derived from it. -/
theorem norm_conj_peacemanRachford_lt_one (hH : (H : E →ₗ[𝕜] E).IsCoercive)
    (hV : (V : E →ₗ[𝕜] E).IsCoercive) (hr : 0 < r) :
    ‖(V + (r : 𝕜) • 1) * peacemanRachford H V r * Ring.inverse (V + (r : 𝕜) • 1)‖ < 1 := by
  obtain ⟨c₁, hc₁, hH'⟩ := hH
  obtain ⟨c₂, hc₂, hV'⟩ := hV
  rw [peacemanRachford_conj (isUnit_add_smul_one hc₂ hV' hr)]
  have h1 := norm_cayley_lt_one hc₁ hH' hr
  have h2 := norm_cayley_lt_one hc₂ hV' hr
  refine lt_of_le_of_lt (norm_mul_le _ _) ?_
  nlinarith [norm_nonneg ((H - (r : 𝕜) • (1 : E →L[𝕜] E)) * Ring.inverse (H + (r : 𝕜) • 1)),
    norm_nonneg ((V - (r : 𝕜) • (1 : E →L[𝕜] E)) * Ring.inverse (V + (r : 𝕜) • 1))]

omit [CompleteSpace E] in
/-- If $P = u^{-1} Q u$ for an invertible operator $u$, then
$\|P^k\| \le \|u^{-1}\| \, \|Q\|^k \, \|u\|$ for every $k$; this turns similarity to a
contraction into convergence of the errors. -/
private theorem norm_pow_conj_le {u : (E →L[𝕜] E)ˣ} {P Q : E →L[𝕜] E}
    (hP : (↑u⁻¹ : E →L[𝕜] E) * Q * ↑u = P) (k : ℕ) :
    ‖P ^ k‖ ≤ ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖Q‖ ^ k * ‖(u : E →L[𝕜] E)‖ := by
  have hQ : ∀ j : ℕ, ‖Q ^ j‖ ≤ ‖Q‖ ^ j := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ j ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (by gcongr)
  rw [← hP, u.conj_pow']
  calc ‖(↑u⁻¹ : E →L[𝕜] E) * Q ^ k * ↑u‖
      ≤ ‖(↑u⁻¹ : E →L[𝕜] E) * Q ^ k‖ * ‖(u : E →L[𝕜] E)‖ := norm_mul_le _ _
    _ ≤ ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖Q ^ k‖ * ‖(u : E →L[𝕜] E)‖ := by
        gcongr
        exact norm_mul_le _ _
    _ ≤ ‖(↑u⁻¹ : E →L[𝕜] E)‖ * ‖Q‖ ^ k * ‖(u : E →L[𝕜] E)‖ := by gcongr; exact hQ k

/-- Let $E$ be a Hilbert space over $\mathbb{R}$ or $\mathbb{C}$, let $H$ and $V$ be coercive
continuous linear operators on $E$, and let $r > 0$. Then the sweep operator has spectral radius
$\rho(P_r) < 1$.

The spectral radius is taken over the scalar field of $E$. The operator $P_r$ is similar to the
product of two Cayley transforms, and similarity preserves the spectrum. -/
theorem spectralRadius_peacemanRachford_lt_one (hH : (H : E →ₗ[𝕜] E).IsCoercive)
    (hV : (V : E →ₗ[𝕜] E).IsCoercive) (hr : 0 < r) :
    spectralRadius 𝕜 (peacemanRachford H V r) < 1 := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have : Subsingleton (E →L[𝕜] E) := ⟨fun _ _ => by ext x; exact Subsingleton.elim _ _⟩
    simp
  · obtain ⟨c₂, hc₂, hV'⟩ := hV
    obtain ⟨u, hu⟩ := isUnit_add_smul_one hc₂ hV' hr
    have hQ : ‖(u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)‖ < 1 := by
      have h := norm_conj_peacemanRachford_lt_one hH ⟨c₂, hc₂, hV'⟩ hr
      rwa [← hu, Ring.inverse_unit] at h
    have hle : spectralRadius 𝕜 (peacemanRachford H V r)
        ≤ ‖(u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)‖₊ := by
      rw [spectralRadius_eq_of_unital,
        ← spectrum.units_conjugate (a := peacemanRachford H V r) (u := u),
        ← spectralRadius_eq_of_unital]
      exact spectralRadius_le_nnnorm _
    refine lt_of_le_of_lt hle ?_
    rwa [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_one, coe_nnnorm]

/-- Let $E$ be a Hilbert space over $\mathbb{R}$ or $\mathbb{C}$, let $H$ and $V$ be coercive
continuous linear operators on $E$, let $r > 0$, and let $x, b \in E$ satisfy $(H + V) x = b$.
Then for every $x_0 \in E$, the iterates of $y \mapsto P_r y + f_r(b)$ from $x_0$ converge to
$x$. This is the convergence that §4.3 of [saad2003iterative] asserts in one sentence.

No commutativity of $H$ and $V$ is used, and no symmetry. -/
theorem tendsto_peacemanRachford (hH : (H : E →ₗ[𝕜] E).IsCoercive)
    (hV : (V : E →ₗ[𝕜] E).IsCoercive) (hr : 0 < r) {b x : E} (hx : (H + V) x = b) (x₀ : E) :
    Tendsto (fun k => (step (peacemanRachford H V r) (peacemanRachfordConst H V r b))^[k] x₀)
      atTop (𝓝 x) := by
  obtain ⟨c₁, hc₁, hH'⟩ := hH
  obtain ⟨c₂, hc₂, hV'⟩ := hV
  have hHu : IsUnit (H + (r : 𝕜) • (1 : E →L[𝕜] E)) := isUnit_add_smul_one hc₁ hH' hr
  have hVu : IsUnit (V + (r : 𝕜) • (1 : E →L[𝕜] E)) := isUnit_add_smul_one hc₂ hV' hr
  -- the solution of `(H + V) x = b` is a fixed point of the sweep
  have hfix : peacemanRachford H V r x + peacemanRachfordConst H V r b = x := by
    have h1 : (1 : E →L[𝕜] E) - peacemanRachford H V r
        = Ring.inverse (peacemanRachfordSplitting H V hr.ne' hHu hVu).m * (H + V) := by
      rw [← peacemanRachfordSplitting_iterationOperator (hr := hr.ne') (hH := hHu) (hV := hVu)]
      exact Splitting.one_sub_iterationOperator _
    have h2 := congrArg (fun T : E →L[𝕜] E => T x) h1
    simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp] at h2
    rw [hx, peacemanRachfordSplitting_const] at h2
    rw [← h2]
    abel
  -- the sweep operator is similar to a strict contraction
  obtain ⟨u, hu⟩ := hVu
  have hP : (↑u⁻¹ : E →L[𝕜] E) *
      ((u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)) * ↑u
      = peacemanRachford H V r := by
    calc (↑u⁻¹ : E →L[𝕜] E) *
          ((u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)) * ↑u
        = ((↑u⁻¹ : E →L[𝕜] E) * ↑u) * peacemanRachford H V r *
            ((↑u⁻¹ : E →L[𝕜] E) * ↑u) := by noncomm_ring
      _ = peacemanRachford H V r := by rw [u.inv_mul, one_mul, mul_one]
  have hQnorm : ‖(u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)‖ < 1 := by
    have h := norm_conj_peacemanRachford_lt_one ⟨c₁, hc₁, hH'⟩ ⟨c₂, hc₂, hV'⟩ hr
    rwa [← hu, Ring.inverse_unit] at h
  -- and so the errors go to zero
  rw [← tendsto_sub_nhds_zero_iff]
  simp only [step_iterate_sub _ _ hfix]
  refine squeeze_zero_norm (fun k => (peacemanRachford H V r ^ k).le_opNorm _) ?_
  have hlim : Tendsto (fun k : ℕ => ‖(↑u⁻¹ : E →L[𝕜] E)‖ *
      ‖(u : E →L[𝕜] E) * peacemanRachford H V r * (↑u⁻¹ : E →L[𝕜] E)‖ ^ k *
      ‖(u : E →L[𝕜] E)‖ * ‖x₀ - x‖) atTop (𝓝 0) := by
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hQnorm
    simpa using ((h0.const_mul ‖(↑u⁻¹ : E →L[𝕜] E)‖).mul_const
      ‖(u : E →L[𝕜] E)‖).mul_const ‖x₀ - x‖
  refine squeeze_zero (fun k => by positivity) (fun k => ?_) hlim
  exact mul_le_mul_of_nonneg_right (norm_pow_conj_le hP k) (norm_nonneg _)

end Convergence

/-!
### The spectral bounds for symmetric positive definite $H$ and $V$

These bounds are stated on a complex Hilbert space, where the continuous functional calculus of a
self-adjoint operator is available. A real symmetric matrix reaches them through `Matrix.complexify`
and `Matrix.toEuclideanCLM`.
-/

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Let $F$ be a complex Hilbert space, let $A$ be a self-adjoint continuous linear operator on $F$,
and let $r_1, r_2 \in \mathbb{R}$ with $t + r_1 \neq 0$ for every $t$ in the real spectrum of
$A$. Let $M \ge 0$ satisfy $|t - r_2| / |t + r_1| \le M$ for every $t$ in the real spectrum of
$A$. Then
$$\bigl\|(A - r_2 I)(A + r_1 I)^{-1}\bigr\| \le M.$$

The norm is in fact the maximum of $|t - r_2| / |t + r_1|$ over the spectrum. The operator is
the continuous functional calculus of $t \mapsto (t - r_2) / (t + r_1)$ at $A$, and the calculus
is isometric (`norm_cfc_le`). The one-parameter case $r_1 = r_2$ for coercive operators is
`Stationary.norm_cayley_lt_one`, which needs no functional calculus. -/
theorem norm_cayleyTwo_le {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {r₁ r₂ : ℝ}
    (hr : ∀ t ∈ spectrum ℝ A, t + r₁ ≠ 0) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t ∈ spectrum ℝ A, |t - r₂| / |t + r₁| ≤ M) :
    ‖(A - (r₂ : ℂ) • 1) * Ring.inverse (A + (r₁ : ℂ) • 1)‖ ≤ M := by
  have hcont : ContinuousOn (fun t : ℝ => (t + r₁)⁻¹) (spectrum ℝ A) :=
    ContinuousOn.inv₀ (by fun_prop) hr
  have hsmul : ∀ r : ℝ, (r : ℂ) • (1 : F →L[ℂ] F) = algebraMap ℝ (F →L[ℂ] F) r := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have h1 : A - (r₂ : ℂ) • 1 = cfc (fun t : ℝ => t - r₂) A := by
    rw [cfc_sub (f := fun t : ℝ => t) (g := fun _ => r₂) (a := A), cfc_id' ℝ A, cfc_const r₂ A,
      hsmul]
  have h2 : Ring.inverse (A + (r₁ : ℂ) • 1) = cfc (fun t : ℝ => (t + r₁)⁻¹) A := by
    rw [cfc_inv (f := fun t : ℝ => t + r₁) (a := A) hr (by fun_prop) hA,
      cfc_add (a := A) (fun t : ℝ => t) (fun _ => r₁), cfc_id' ℝ A, cfc_const r₁ A, hsmul]
  rw [h1, h2, ← cfc_mul _ _ A (by fun_prop) hcont]
  refine norm_cfc_le hM fun t ht => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_inv, ← div_eq_mul_inv]
  exact h t ht

/-- Let $F$ be a complex Hilbert space, let $H$ and $V$ be symmetric coercive continuous linear
operators on $F$, let $r_1, r_2 > 0$, and let $M_1, M_2 \ge 0$. Assume that
$|t - r_2| / (t + r_1) \le M_1$ for every $t$ in the real spectrum of $H$, and that
$|t - r_1| / (t + r_2) \le M_2$ for every $t$ in the real spectrum of $V$. Then
$$\rho(P_{r_1, r_2}) \le M_1 M_2.$$
This is the display after (4.50) of [quarteroni2000numerical], §4.3.6, in the letters
$r_i = 1/\alpha_i$. The source states the case where $M_1$ and $M_2$ are the two maxima.

The hypothesis on $H$ and $V$ is `LinearMap.IsSymmetricCoercive`. The operator $P_{r_1, r_2}$ is
similar to the product of two Cayley transforms (`Stationary.peacemanRachfordTwo_conj`), and
each of them is bounded by `Stationary.norm_cayleyTwo_le`. -/
theorem spectralRadius_peacemanRachfordTwo_le {H V : F →L[ℂ] F}
    (hH : (H : F →ₗ[ℂ] F).IsSymmetricCoercive) (hV : (V : F →ₗ[ℂ] F).IsSymmetricCoercive)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ t ∈ spectrum ℝ H, |t - r₂| / (t + r₁) ≤ M₁)
    (h₂ : ∀ t ∈ spectrum ℝ V, |t - r₁| / (t + r₂) ≤ M₂) :
    spectralRadius ℂ (peacemanRachfordTwo H V r₁ r₂) ≤ ENNReal.ofReal (M₁ * M₂) := by
  obtain ⟨c₁, hc₁, hH'⟩ := hH.isCoercive
  obtain ⟨c₂, hc₂, hV'⟩ := hV.isCoercive
  have hHpos : ∀ t ∈ spectrum ℝ H, 0 < t + r₁ := fun t ht => by
    linarith [ContinuousLinearMap.le_of_mem_spectrum_real_of_isCoerciveWith hH' ht]
  have hVpos : ∀ t ∈ spectrum ℝ V, 0 < t + r₂ := fun t ht => by
    linarith [ContinuousLinearMap.le_of_mem_spectrum_real_of_isCoerciveWith hV' ht]
  have hCH : ‖(H - (r₂ : ℂ) • 1) * Ring.inverse (H + (r₁ : ℂ) • 1)‖ ≤ M₁ := by
    refine norm_cayleyTwo_le hH.isSymmetric.isSelfAdjoint (fun t ht => (hHpos t ht).ne') hM₁
      fun t ht => ?_
    rw [abs_of_pos (hHpos t ht)]
    exact h₁ t ht
  have hCV : ‖(V - (r₁ : ℂ) • 1) * Ring.inverse (V + (r₂ : ℂ) • 1)‖ ≤ M₂ := by
    refine norm_cayleyTwo_le hV.isSymmetric.isSelfAdjoint (fun t ht => (hVpos t ht).ne') hM₂
      fun t ht => ?_
    rw [abs_of_pos (hVpos t ht)]
    exact h₂ t ht
  have hVu : IsUnit (V + (r₂ : ℂ) • (1 : F →L[ℂ] F)) := isUnit_add_smul_one hc₂ hV' hr₂
  have hconj := peacemanRachfordTwo_conj H V r₁ r₂ hVu
  refine (spectralRadius_le_nnnorm_conj hVu _).trans ?_
  refine le_of_eq_of_le (congrArg (fun T : F →L[ℂ] F => ((‖T‖₊ : NNReal) : ENNReal)) hconj) ?_
  rw [← enorm_eq_nnnorm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    ((norm_mul_le _ _).trans (mul_le_mul hCH hCV (norm_nonneg _) hM₁))

/-- For $0 < a \le b$ and $a^2 \le t \le b^2$, $|t - ab| / (t + ab) \le (b - a) / (b + a)$, the
common value at the two endpoints. -/
private theorem abs_sub_div_add_le {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : a ^ 2 ≤ t)
    (ht' : t ≤ b ^ 2) : |t - a * b| / (t + a * b) ≤ (b - a) / (b + a) := by
  have hb : 0 < b := ha.trans_le hab
  have htpos : 0 < t + a * b := by nlinarith
  rw [div_le_div_iff₀ htpos (by linarith)]
  rcases le_or_gt (a * b) t with h | h
  · rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left ht' ha.le]
  · rw [abs_of_neg (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left ht hb.le]

/-- Let $F$ be a complex Hilbert space, let $0 < \gamma \le \delta$, and let $H$ and $V$ be
symmetric continuous linear operators on $F$ with $\gamma \|x\|^2 \le \operatorname{Re} \langle
Hx, x \rangle \le \delta \|x\|^2$ and $\gamma \|x\|^2 \le \operatorname{Re} \langle Vx, x
\rangle \le \delta \|x\|^2$ for all $x$. Then the parameter $r = \sqrt{\gamma \delta}$ gives
$$\rho(P_r) \le \left(\frac{1 - \sqrt{\gamma/\delta}}{1 + \sqrt{\gamma/\delta}}\right)^2.$$
This is the last display of [quarteroni2000numerical], §4.3.6, where the parameter is
$\alpha_1 = \alpha_2 = 1/\sqrt{\delta\gamma}$.

The source adds the proviso "provided $\gamma/\delta \to 0$ as the size grows", which is not a
hypothesis of the inequality. The hypotheses on $H$ and $V$ are
`LinearMap.IsSymmetricBoundedBy`. The proof is
`Stationary.spectralRadius_peacemanRachfordTwo_le` at $r_1 = r_2 = r$: on $[\gamma, \delta]$ the
function $t \mapsto |t - r| / (t + r)$ is largest at the endpoints, where it equals
$(\sqrt\delta - \sqrt\gamma) / (\sqrt\delta + \sqrt\gamma)$. -/
theorem spectralRadius_peacemanRachford_le_of_spectrum_subset {H V : F →L[ℂ] F} {γ δ : ℝ}
    (hγ : 0 < γ) (hγδ : γ ≤ δ) (hH : (H : F →ₗ[ℂ] F).IsSymmetricBoundedBy γ δ)
    (hV : (V : F →ₗ[ℂ] F).IsSymmetricBoundedBy γ δ) :
    spectralRadius ℂ (peacemanRachford H V (Real.sqrt (γ * δ))) ≤
      ENNReal.ofReal (((1 - Real.sqrt (γ / δ)) / (1 + Real.sqrt (γ / δ))) ^ 2) := by
  set a := Real.sqrt γ with ha_def
  set b := Real.sqrt δ with hb_def
  have ha : 0 < a := Real.sqrt_pos.mpr hγ
  have hab : a ≤ b := Real.sqrt_le_sqrt hγδ
  have hb : 0 < b := ha.trans_le hab
  have ha2 : a ^ 2 = γ := Real.sq_sqrt hγ.le
  have hb2 : b ^ 2 = δ := Real.sq_sqrt (hγ.le.trans hγδ)
  have hr : Real.sqrt (γ * δ) = a * b := Real.sqrt_mul hγ.le δ
  have hK : (1 - Real.sqrt (γ / δ)) / (1 + Real.sqrt (γ / δ)) = (b - a) / (b + a) := by
    rw [Real.sqrt_div hγ.le, ← ha_def, ← hb_def]
    field_simp
  have hK0 : 0 ≤ (b - a) / (b + a) := div_nonneg (by linarith) (by linarith)
  have hbound : ∀ {A : F →L[ℂ] F}, (A : F →ₗ[ℂ] F).IsSymmetricBoundedBy γ δ →
      ∀ t ∈ spectrum ℝ A, |t - a * b| / (t + a * b) ≤ (b - a) / (b + a) := by
    intro A hA t ht
    obtain ⟨h1, h2⟩ :=
      ContinuousLinearMap.mem_Icc_of_mem_spectrum_real_of_isSymmetricBoundedBy hA ht
    exact abs_sub_div_add_le ha hab (ha2 ▸ h1) (hb2 ▸ h2)
  rw [hK, hr, sq, ← peacemanRachfordTwo_self]
  exact spectralRadius_peacemanRachfordTwo_le (hH.isSymmetricCoercive hγ)
    (hV.isSymmetricCoercive hγ) (mul_pos ha hb) (mul_pos ha hb) hK0 hK0 (hbound hH) (hbound hV)

end Complex

end Stationary

/-!
### Matrices

This section reads the sweep of two square matrices through `Matrix.toEuclideanCLM`, and the bounds
of the previous sections for real symmetric positive definite matrices through `Matrix.complexify`
and `Matrix.complexSpectralRadius`. The matrix is written out as $(V + r_2 I)^{-1} (H - r_2 I) (H +
r_1 I)^{-1} (V - r_1 I)$ with Mathlib's matrix inverse, which is $0$ at a singular matrix. The
nonsingularity of the shifts is a hypothesis where the operator results need it, and it follows from
positive definiteness in the corollaries.
-/

namespace Matrix

open Stationary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {H V : Matrix ι ι 𝕜} {r₁ r₂ : ℝ}

/-- Let $H$ and $V$ be square matrices over $\mathbb{R}$ or $\mathbb{C}$, and let
$r_1, r_2 \in \mathbb{R}$ be such that $H + r_1 I$ and $V + r_2 I$ are nonsingular. Then the
matrix
$$(V + r_2 I)^{-1} (H - r_2 I) (H + r_1 I)^{-1} (V - r_1 I)$$
acts on the Euclidean space of vectors indexed by $\iota$ as the operator $P_{r_1, r_2}$
(`Stationary.peacemanRachfordTwo`) of the operators of $H$ and $V$. -/
theorem toEuclideanCLM_peacemanRachfordTwo (hH : IsUnit (H + (r₁ : 𝕜) • (1 : Matrix ι ι 𝕜)))
    (hV : IsUnit (V + (r₂ : 𝕜) • (1 : Matrix ι ι 𝕜))) :
    toEuclideanCLM (n := ι) (𝕜 := 𝕜)
        ((V + (r₂ : 𝕜) • 1)⁻¹ * (H - (r₂ : 𝕜) • 1) * (H + (r₁ : 𝕜) • 1)⁻¹ *
          (V - (r₁ : 𝕜) • 1)) =
      peacemanRachfordTwo (toEuclideanCLM (n := ι) (𝕜 := 𝕜) H)
        (toEuclideanCLM (n := ι) (𝕜 := 𝕜) V) r₁ r₂ := by
  rw [peacemanRachfordTwo, map_mul, map_mul, map_mul, toEuclideanCLM_nonsing_inv hV,
    toEuclideanCLM_nonsing_inv hH, toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one,
    toEuclideanCLM_sub_smul_one, toEuclideanCLM_sub_smul_one]

/-- Let $H$ and $V$ be square matrices over $\mathbb{R}$ or $\mathbb{C}$ such that $H + r_1 I$ and
$V + r_2 I$ are nonsingular. Then the matrix $(V + r_2 I)^{-1} \bigl(I - (H - r_2 I)(H + r_1
I)^{-1}\bigr)$ acts on every vector $b$ as the affine part `Stationary.peacemanRachfordTwoConst`
of the operators of $H$ and $V$. -/
theorem toEuclideanCLM_peacemanRachfordTwoConst
    (hH : IsUnit (H + (r₁ : 𝕜) • (1 : Matrix ι ι 𝕜)))
    (hV : IsUnit (V + (r₂ : 𝕜) • (1 : Matrix ι ι 𝕜))) (b : EuclideanSpace 𝕜 ι) :
    toEuclideanCLM (n := ι) (𝕜 := 𝕜)
        ((V + (r₂ : 𝕜) • 1)⁻¹ * (1 - (H - (r₂ : 𝕜) • 1) * (H + (r₁ : 𝕜) • 1)⁻¹)) b =
      peacemanRachfordTwoConst (toEuclideanCLM (n := ι) (𝕜 := 𝕜) H)
        (toEuclideanCLM (n := ι) (𝕜 := 𝕜) V) r₁ r₂ b := by
  rw [peacemanRachfordTwoConst, map_mul, map_sub, map_mul, map_one,
    toEuclideanCLM_nonsing_inv hV, toEuclideanCLM_nonsing_inv hH, toEuclideanCLM_add_smul_one,
    toEuclideanCLM_add_smul_one, toEuclideanCLM_sub_smul_one]
  rfl

end RCLike

section Real

variable {H V : Matrix ι ι ℝ} {r₁ r₂ : ℝ}

/-- If $A + rI$ is nonsingular for a real square matrix $A$, then so is the complexification of $A$
plus $rI$. -/
private theorem isUnit_complexify_add_smul_one {A : Matrix ι ι ℝ} {r : ℝ}
    (hA : IsUnit (A + r • (1 : Matrix ι ι ℝ))) :
    IsUnit (complexify A + (r : ℂ) • (1 : Matrix ι ι ℂ)) := by
  rwa [← complexify_one, ← complexify_smul, ← complexify_add, isUnit_complexify_iff]

/-- Let $H$ and $V$ be real square matrices, and let $r_1, r_2 \in \mathbb{R}$ be such that
$H + r_1 I$ and $V + r_2 I$ are nonsingular. Then the complex spectral radius of the real matrix
$$(V + r_2 I)^{-1} (H - r_2 I) (H + r_1 I)^{-1} (V - r_1 I)$$
is the spectral radius of the operator $P_{r_1, r_2}$ (`Stationary.peacemanRachfordTwo`) of the
complexifications of $H$ and $V$ on `EuclideanSpace ℂ ι`. -/
theorem complexSpectralRadius_peacemanRachfordTwo (hH : IsUnit (H + r₁ • (1 : Matrix ι ι ℝ)))
    (hV : IsUnit (V + r₂ • (1 : Matrix ι ι ℝ))) :
    complexSpectralRadius ((V + r₂ • 1)⁻¹ * (H - r₂ • 1) * (H + r₁ • 1)⁻¹ * (V - r₁ • 1)) =
      spectralRadius ℂ (peacemanRachfordTwo (toEuclideanCLM (n := ι) (𝕜 := ℂ) (complexify H))
        (toEuclideanCLM (n := ι) (𝕜 := ℂ) (complexify V)) r₁ r₂) := by
  have h : toEuclideanCLM (n := ι) (𝕜 := ℂ)
      ((complexify V + (r₂ : ℂ) • 1)⁻¹ * (complexify H - (r₂ : ℂ) • 1) *
        (complexify H + (r₁ : ℂ) • 1)⁻¹ * (complexify V - (r₁ : ℂ) • 1)) =
      peacemanRachfordTwo (toEuclideanCLM (n := ι) (𝕜 := ℂ) (complexify H))
        (toEuclideanCLM (n := ι) (𝕜 := ℂ) (complexify V)) r₁ r₂ :=
    toEuclideanCLM_peacemanRachfordTwo (isUnit_complexify_add_smul_one hH)
      (isUnit_complexify_add_smul_one hV)
  have hc : complexify ((V + r₂ • 1)⁻¹ * (H - r₂ • 1) * (H + r₁ • 1)⁻¹ * (V - r₁ • 1)) =
      (complexify V + (r₂ : ℂ) • 1)⁻¹ * (complexify H - (r₂ : ℂ) • 1) *
        (complexify H + (r₁ : ℂ) • 1)⁻¹ * (complexify V - (r₁ : ℂ) • 1) := by
    simp only [complexify_mul, complexify_inv, complexify_add, complexify_sub, complexify_smul,
      complexify_one]
  rw [complexSpectralRadius, hc, ← h, spectralRadius_eq_of_unital, spectralRadius_eq_of_unital,
    AlgEquiv.spectrum_eq (toEuclideanCLM (n := ι) (𝕜 := ℂ))]

/-- Let $H$ and $V$ be real symmetric positive definite matrices, let $r_1, r_2 > 0$, and let
$M_1, M_2 \ge 0$. Assume that $|t - r_2| / (t + r_1) \le M_1$ for every eigenvalue $t$ of $H$,
and that $|t - r_1| / (t + r_2) \le M_2$ for every eigenvalue $t$ of $V$. Then
$$\rho\bigl((V + r_2 I)^{-1} (H - r_2 I) (H + r_1 I)^{-1} (V - r_1 I)\bigr) \le M_1 M_2.$$
This is the display after (4.50) of [quarteroni2000numerical], §4.3.6, with $r_i = 1/\alpha_i$.

The spectral radius is `Matrix.complexSpectralRadius`, and the eigenvalues are the real spectrum
`spectrum ℝ`. The proof is `Stationary.spectralRadius_peacemanRachfordTwo_le` for the
complexified matrices. The matrices $H$ and $V$ need not commute. -/
theorem PosDef.complexSpectralRadius_peacemanRachfordTwo_le (hH : H.PosDef) (hV : V.PosDef)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ t ∈ spectrum ℝ H, |t - r₂| / (t + r₁) ≤ M₁)
    (h₂ : ∀ t ∈ spectrum ℝ V, |t - r₁| / (t + r₂) ≤ M₂) :
    complexSpectralRadius ((V + r₂ • 1)⁻¹ * (H - r₂ • 1) * (H + r₁ • 1)⁻¹ * (V - r₁ • 1)) ≤
      ENNReal.ofReal (M₁ * M₂) := by
  rw [complexSpectralRadius_peacemanRachfordTwo (hH.add (PosDef.one.smul hr₁)).isUnit
    (hV.add (PosDef.one.smul hr₂)).isUnit]
  refine spectralRadius_peacemanRachfordTwo_le hH.isSymmetricCoercive_toEuclideanCLM_complexify
    hV.isSymmetricCoercive_toEuclideanCLM_complexify hr₁ hr₂ hM₁ hM₂ ?_ ?_
  · rwa [spectrum_real_toEuclideanCLM_complexify]
  · rwa [spectrum_real_toEuclideanCLM_complexify]

/-- Let $H$ and $V$ be real symmetric positive definite matrices and let $r > 0$. Then
$$\rho\bigl((V + rI)^{-1} (H - rI) (H + rI)^{-1} (V - rI)\bigr) < 1.$$
This is the convergence of the alternating direction implicit iteration of [saad2003iterative],
§4.3, and of [quarteroni2000numerical], §4.3.6, for $\alpha_1 = \alpha_2$.

The spectral radius is `Matrix.complexSpectralRadius`. The proof is
`Stationary.spectralRadius_peacemanRachford_lt_one` for the complexified matrices. The matrices
$H$ and $V$ need not commute. -/
theorem PosDef.complexSpectralRadius_peacemanRachford_lt_one (hH : H.PosDef) (hV : V.PosDef)
    {r : ℝ} (hr : 0 < r) :
    complexSpectralRadius ((V + r • 1)⁻¹ * (H - r • 1) * (H + r • 1)⁻¹ * (V - r • 1)) < 1 := by
  rw [complexSpectralRadius_peacemanRachfordTwo (hH.add (PosDef.one.smul hr)).isUnit
    (hV.add (PosDef.one.smul hr)).isUnit, peacemanRachfordTwo_self]
  exact spectralRadius_peacemanRachford_lt_one
    hH.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive
    hV.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive hr

/-- Let $H$ and $V$ be real symmetric matrices whose eigenvalues lie in $[\gamma, \delta]$, with
$0 < \gamma \le \delta$. Then the parameter $r = \sqrt{\gamma \delta}$ gives
$$\rho\bigl((V + rI)^{-1} (H - rI) (H + rI)^{-1} (V - rI)\bigr) \le \left(\frac{1 -
  \sqrt{\gamma/\delta}}{1 + \sqrt{\gamma/\delta}}\right)^2.$$
This is the last display of [quarteroni2000numerical], §4.3.6.

The spectral radius is `Matrix.complexSpectralRadius`, and the eigenvalues are the real spectrum
`spectrum ℝ`. The proof is `Matrix.PosDef.complexSpectralRadius_peacemanRachfordTwo_le` at
$r_1 = r_2 = r$, as in `Stationary.spectralRadius_peacemanRachford_le_of_spectrum_subset`. -/
theorem IsHermitian.complexSpectralRadius_peacemanRachford_le_of_spectrum_subset
    (hH : H.IsHermitian) (hV : V.IsHermitian) {γ δ : ℝ} (hγ : 0 < γ) (hγδ : γ ≤ δ)
    (h₁ : spectrum ℝ H ⊆ Set.Icc γ δ) (h₂ : spectrum ℝ V ⊆ Set.Icc γ δ) :
    complexSpectralRadius ((V + √(γ * δ) • 1)⁻¹ * (H - √(γ * δ) • 1) *
        (H + √(γ * δ) • 1)⁻¹ * (V - √(γ * δ) • 1)) ≤
      ENNReal.ofReal (((1 - √(γ / δ)) / (1 + √(γ / δ))) ^ 2) := by
  have hpos : ∀ {A : Matrix ι ι ℝ} (hA : A.IsHermitian), spectrum ℝ A ⊆ Set.Icc γ δ → A.PosDef :=
    fun hA h => (IsHermitian.posDef_iff_eigenvalues_pos hA).mpr fun i =>
      hγ.trans_le (h (by
        rw [IsHermitian.spectrum_real_eq_range_eigenvalues hA]; exact ⟨i, rfl⟩)).1
  set a := √γ with ha_def
  set b := √δ with hb_def
  have ha : 0 < a := Real.sqrt_pos.mpr hγ
  have hab : a ≤ b := Real.sqrt_le_sqrt hγδ
  have hb : 0 < b := ha.trans_le hab
  have ha2 : a ^ 2 = γ := Real.sq_sqrt hγ.le
  have hb2 : b ^ 2 = δ := Real.sq_sqrt (hγ.le.trans hγδ)
  have hr : √(γ * δ) = a * b := Real.sqrt_mul hγ.le δ
  have hK : (1 - √(γ / δ)) / (1 + √(γ / δ)) = (b - a) / (b + a) := by
    rw [Real.sqrt_div hγ.le, ← ha_def, ← hb_def]
    field_simp
  have hK0 : 0 ≤ (b - a) / (b + a) := div_nonneg (by linarith) (by linarith)
  have hbound : ∀ {A : Matrix ι ι ℝ}, spectrum ℝ A ⊆ Set.Icc γ δ →
      ∀ t ∈ spectrum ℝ A, |t - a * b| / (t + a * b) ≤ (b - a) / (b + a) := fun h t ht =>
    Stationary.abs_sub_div_add_le ha hab (ha2 ▸ (h ht).1) (hb2 ▸ (h ht).2)
  rw [hK, hr, sq]
  exact PosDef.complexSpectralRadius_peacemanRachfordTwo_le (hpos hH h₁) (hpos hV h₂)
    (mul_pos ha hb) (mul_pos ha hb) hK0 hK0 (hbound h₁) (hbound h₂)

end Real

end Matrix
