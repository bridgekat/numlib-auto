/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Stationary.ADI
import NumlibSurface.SaadSparse.Chapter02.Section02

/-!
# Saad, Section 4.3: Alternating direction methods

This module formalizes §4.3 of [saad2003iterative], the alternating direction implicit (ADI) method
of Peaceman and Rachford. The matrix of a discretized elliptic operator is split as $A = H + V$
(4.49), with $H$ and $V$ the horizontal and the vertical three-point differences. One sweep of
Algorithm 4.3 with parameter $r$ solves the two half-steps
$$(H + rI) u_{k+1/2} = (rI - V) u_k + b, \qquad (V + rI) u_{k+1} = (rI - H) u_{k+1/2} + b.$$
The sweep is the affine map $u \mapsto G_r u + f_r$ of (4.50)–(4.51), and it is the stationary
iteration of the splitting $A = M - N$ with $M = (H + rI)(V + rI)/(2r)$ of (4.52); Problem P-4.5
gives the closed form $f_r = 2r(V + rI)^{-1}(H + rI)^{-1}b$. The affine identity is total.
The splitting and the two linear solve identities use the corresponding nonsingularity conditions.

The section states no numbered result. It claims in prose that the sweep converges when $H$ and $V$
are symmetric positive definite and $r > 0$ is a constant. The module proves this claim, from every
starting vector and for every right-hand side, without any assumption that $H$ and $V$ commute, and
applies it to the five-point matrix of §2.2.5. The proofs specialize `Numlib.Stationary.ADI` through
`Matrix.toEuclideanCLM`.

## Main definitions

* Algorithm 4.3, `SaadSparse.Chapter04.adiHalfStep` and `SaadSparse.Chapter04.adiStep`: the
  intermediate vector and one sweep of the Peaceman–Rachford method.
* Equations (4.50)–(4.51), `SaadSparse.Chapter04.G_adi` and `SaadSparse.Chapter04.f_adi`: the
  iteration matrix $G_r$ and the affine part $f_r$ of one sweep.
* Equation (4.52), `SaadSparse.Chapter04.adiSplitting`: the splitting of $H + V$ with
  $M = (H + rI)(V + rI)/(2r)$.
* Equation (4.49), `SaadSparse.Chapter04.modelH` and `SaadSparse.Chapter04.modelV`: the horizontal
  and vertical parts of the five-point matrix of the model problem.

## Main results

* Equations (4.50)–(4.51), `SaadSparse.Chapter04.equation_4_50`: one sweep is
  $u \mapsto G_r u + f_r$.
* Equation (4.52), `SaadSparse.Chapter04.equation_4_52` and
  `SaadSparse.Chapter04.adiSplitting_iterationOperator`: the splitting has
  $N = (H - rI)(V - rI)/(2r)$ and iteration matrix $G_r$.
* Problem P-4.5, `SaadSparse.Chapter04.f_adi_eq` and `SaadSparse.Chapter04.f_adi_eq_m_inv_mulVec`:
  $f_r = 2r(V + rI)^{-1}(H + rI)^{-1}b = M^{-1}b$.
* §4.3, `SaadSparse.Chapter04.adi_complexSpectralRadius_lt_one`: for symmetric positive definite
  $H$, $V$ and $r > 0$, $\rho(G_r) < 1$.
* §4.3, `SaadSparse.Chapter04.adi_converges`: for symmetric positive definite $H$, $V$ and $r > 0$,
  the sweeps converge to the solution of $(H + V)x = b$.
* Equation (4.49), `SaadSparse.Chapter04.laplacian2D_eq_modelH_add_modelV` and
  `SaadSparse.Chapter04.adi_model_problem`: the five-point matrix is $H + V$, and ADI converges on
  it for every $r > 0$.

## Implementation notes

* All matrices are indexed by an arbitrary finite type, not by `Fin n`, because the model problem
  needs the product index `Fin n₁ × Fin n₂`.
* The model splitting is `SaadSparse.Chapter02.laplacian2D_eq_kroneckerSum` read as the sum of its
  two Kronecker factors: $H = T_1 \otimes I$ and $V = I \otimes T_2$, with $T_1$ and $T_2$ the
  one-dimensional Laplacians. This is the only discretization that this section needs.
* The commutativity of $H$ and $V$ belongs to the theory of the optimal parameter sequence, which
  the book only cites. It is not needed for the convergence with a constant parameter, and it is not
  assumed.

## Deviations from the source

* **Algorithm 4.3 and Equations (4.50)–(4.51)** (reading). The sweep takes the current
  parameter as input, and its inverse formulas are totalized at singular shifts.
  The solve identities require the corresponding shift to be nonsingular.
  See `SaadSparse.Chapter04.adiHalfStep`, `SaadSparse.Chapter04.adiStep`,
  `SaadSparse.Chapter04.adiHalfStep_spec`, `SaadSparse.Chapter04.adiStep_spec`,
  `SaadSparse.Chapter04.G_adi`, `SaadSparse.Chapter04.f_adi` and
  `SaadSparse.Chapter04.equation_4_50`.
* **Equation (4.52) and Problem P-4.5** (generalization). For the splitting, nonzero
  parameters of either sign are allowed when both shifts are nonsingular. The simplification
  of the affine term uses only the horizontal shift's nonsingularity.
  See `SaadSparse.Chapter04.adiSplitting`, `SaadSparse.Chapter04.adiSplitting_m`,
  `SaadSparse.Chapter04.equation_4_52`, `SaadSparse.Chapter04.adiSplitting_iterationOperator`,
  `SaadSparse.Chapter04.f_adi_eq` and `SaadSparse.Chapter04.f_adi_eq_m_inv_mulVec`.
* **Equation (4.49), model split and convergence** (reading). The concrete split uses
  the constant-coefficient negative Laplacean of §2.2.5. The abstract ADI convergence
  theorem applies to any two symmetric positive definite matrices.
  See `SaadSparse.Chapter04.modelH`, `SaadSparse.Chapter04.modelV`,
  `SaadSparse.Chapter04.laplacian2D_eq_modelH_add_modelV` and
  `SaadSparse.Chapter04.adi_model_problem`.

## Not formalized

* **The optimal parameter $r$ and the cyclic parameter sequences.** The book states no formula,
  bound or theorem for them, and cites a theory that exists only when $H$ and $V$ commute.
* **The claim that ADI with the optimal $r$ has the asymptotic rate of SSOR with the optimal
  $\omega$ on the model problem.** It is an asymptotic remark with no constant and no proof.
* **The operation count $O(n^2 \log n)$.**
* **The parabolic formulation (4.53)–(4.56) and the time-stepping pair after it.** It is a
  semi-discretization of a partial differential equation, and it is not the image of Algorithm 4.3
  under $r = 2/\Delta t$, because the sign patterns differ.
* **The remark that each half-step decouples into independent tridiagonal systems in the line
  ordering.** It is about a data layout, not about the iteration.
-/

open Filter Matrix Stationary Topology
open scoped Kronecker

namespace SaadSparse.Chapter04

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H V : Matrix ι ι ℝ} {r : ℝ}

/-! ### Elementary facts used throughout -/

private theorem isUnit_smul_matrix {c : ℝ} (hc : c ≠ 0) {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    IsUnit (c • M) := by
  rw [isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hc) (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det M).mp hM))

private theorem splitting_n_eq {R : Type*} [Ring R] {a : R} (s : Stationary.Splitting a) :
    s.n = s.m - a := rfl

/-! ### Algorithm 4.3 -/

/-- **Algorithm 4.3** of [saad2003iterative], the half-step. For
$H, V \in \mathbb{R}^{\iota \times \iota}$ and $r \in \mathbb{R}$, the **intermediate vector**
of one Peaceman–Rachford sweep from $u_k$ is
$$u_{k+1/2} = (H + rI)^{-1} \big( (rI - V) u_k + b \big).$$

**Reading.** The source gives a linear solve with the current positive parameter $\rho_k$.
The definition takes the current parameter $r$ as input and returns zero when $H+rI$
is singular, by totalized inversion. For an invertible shift it gives the source's solve. -/
noncomputable def adiHalfStep (H V : Matrix ι ι ℝ) (r : ℝ) (b x : ι → ℝ) : ι → ℝ :=
  (H + r • 1)⁻¹ *ᵥ ((r • 1 - V) *ᵥ x + b)

/-- **Algorithm 4.3** of [saad2003iterative] (Peaceman–Rachford). One **ADI sweep** with parameter
$r$ from $u_k$ is the horizontal half-step $(H + rI) u_{k+1/2} = (rI - V) u_k + b$ followed by
the vertical half-step
$$(V + rI) u_{k+1} = (rI - H) u_{k+1/2} + b.$$

**Reading.** The source gives both solves in a loop over positive parameters. The definition
is one sweep with the supplied parameter $r$, using inverses totalized to zero at singular
shifts. Iterating it at fixed $r$ gives the stationary case. -/
noncomputable def adiStep (H V : Matrix ι ι ℝ) (r : ℝ) (b x : ι → ℝ) : ι → ℝ :=
  (V + r • 1)⁻¹ *ᵥ ((r • 1 - H) *ᵥ adiHalfStep H V r b x + b)

/-- **Algorithm 4.3** of [saad2003iterative], first half-step. If $H + rI$ is nonsingular, the
intermediate vector satisfies
$$(H + rI) u_{k+1/2} = (rI - V) u_k + b.$$

**Reading.** The source requests a solve. Invertibility of the horizontal shift ensures
that the totalized inverse formula implements that solve.
-/
theorem adiHalfStep_spec (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))) (b x : ι → ℝ) :
    (H + r • 1) *ᵥ adiHalfStep H V r b x = (r • 1 - V) *ᵥ x + b :=
  mulVec_nonsing_inv_mulVec hH _

/-- **Algorithm 4.3** of [saad2003iterative], second half-step. If $V + rI$ is nonsingular, the
sweep satisfies
$$(V + rI) u_{k+1} = (rI - H) u_{k+1/2} + b.$$

**Reading.** The source requests a solve. Invertibility of the vertical shift ensures that
the totalized inverse formula implements that solve for the given intermediate vector.
-/
theorem adiStep_spec (hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))) (b x : ι → ℝ) :
    (V + r • 1) *ᵥ adiStep H V r b x = (r • 1 - H) *ᵥ adiHalfStep H V r b x + b :=
  mulVec_nonsing_inv_mulVec hV _

/-! ### The affine form (4.50)–(4.51) -/

/-- **Equation (4.50)** of [saad2003iterative]. The **iteration matrix** of one Peaceman–Rachford
sweep with parameter $r$ is
$$G_r = (V + rI)^{-1} (H - rI) (H + rI)^{-1} (V - rI).$$

**Reading.** The source uses ordinary inverses on nonsingular shifts. The totalized
definition is zero if either shift is singular.
-/
noncomputable def G_adi (H V : Matrix ι ι ℝ) (r : ℝ) : Matrix ι ι ℝ :=
  (V + r • 1)⁻¹ * (H - r • 1) * (H + r • 1)⁻¹ * (V - r • 1)

/-- **Equation (4.51)** of [saad2003iterative]. The **affine part** of one Peaceman–Rachford sweep
with parameter $r$ is
$$f_r = (V + rI)^{-1} \big( I - (H - rI)(H + rI)^{-1} \big) b.$$

**Reading.** The shifted inverses are totalized to zero at singular matrices. The
formula agrees with the source when both shifts are nonsingular.
-/
noncomputable def f_adi (H V : Matrix ι ι ℝ) (r : ℝ) (b : ι → ℝ) : ι → ℝ :=
  (V + r • 1)⁻¹ *ᵥ ((1 - (H - r • 1) * (H + r • 1)⁻¹) *ᵥ b)

/-- **Equations (4.50)–(4.51)** of [saad2003iterative]. For all $H$, $V$, $r$, $b$ and $u$, one
sweep of Algorithm 4.3 is
$$u \mapsto G_r u + f_r.$$

**Reading.** The source rewrites the two linear solves when the shifted matrices are
nonsingular. The affine identity holds for the totalized sweep at all shifts, including
singular ones. -/
theorem equation_4_50 (H V : Matrix ι ι ℝ) (r : ℝ) (b x : ι → ℝ) :
    adiStep H V r b x = G_adi H V r *ᵥ x + f_adi H V r b := by
  simp only [adiStep, adiHalfStep, G_adi, f_adi, ← mulVec_mulVec, mulVec_add, sub_mulVec,
    mulVec_sub, one_mulVec, smul_mulVec, mulVec_smul]
  module

/-! ### The bridge to the backbone -/

/-- **Equation (4.50)** of [saad2003iterative], the backbone form. If $H + rI$ and $V + rI$ are
nonsingular, the operator of $G_r$ on the Euclidean space is the Peaceman–Rachford operator
`Stationary.peacemanRachford` of the operators of $H$ and $V$.

The operators are taken with `Matrix.toEuclideanCLM`. -/
theorem toEuclideanCLM_G_adi (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ)))
    (hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))) :
    toEuclideanCLM (𝕜 := ℝ) (G_adi H V r)
      = peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r := by
  rw [G_adi, peacemanRachford, map_mul, map_mul, map_mul, toEuclideanCLM_nonsing_inv hV,
    toEuclideanCLM_nonsing_inv hH, toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one,
    toEuclideanCLM_sub_smul_one, toEuclideanCLM_sub_smul_one]
  norm_num

/-- **Equation (4.51)** of [saad2003iterative], the backbone form. If $H + rI$ and $V + rI$ are
nonsingular, the vector $f_r$ is `Stationary.peacemanRachfordConst` of the operators of $H$ and
$V$, applied to $b$. -/
theorem toLp_f_adi (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ)))
    (hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))) (b : ι → ℝ) :
    (WithLp.toLp 2 (f_adi H V r b) : EuclideanSpace ℝ ι)
      = peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
          (WithLp.toLp 2 b) := by
  have h : toEuclideanCLM (𝕜 := ℝ) ((V + r • 1)⁻¹ * (1 - (H - r • 1) * (H + r • 1)⁻¹))
      = Ring.inverse (toEuclideanCLM (𝕜 := ℝ) V + (r : ℝ) • 1) *
        (1 - (toEuclideanCLM (𝕜 := ℝ) H - (r : ℝ) • 1) *
          Ring.inverse (toEuclideanCLM (𝕜 := ℝ) H + (r : ℝ) • 1)) := by
    rw [map_mul, toEuclideanCLM_nonsing_inv hV, toEuclideanCLM_add_smul_one, map_sub, map_one,
      map_mul, toEuclideanCLM_nonsing_inv hH, toEuclideanCLM_add_smul_one,
      toEuclideanCLM_sub_smul_one]
  rw [f_adi, mulVec_mulVec, ← toEuclideanCLM_toLp, h, peacemanRachfordConst, mul_apply_eq_comp]
  rfl

/-! ### The splitting (4.52) and Problem P-4.5 -/

/-- **Equation (4.52)** of [saad2003iterative], the splitting. Let $r \neq 0$, and let $H + rI$ and
$V + rI$ be nonsingular. The **ADI splitting** of $A = H + V$ is the splitting $A = M - N$ with
$$M = \frac{1}{2r} (H + rI)(V + rI).$$

**Generalization.** Equation (4.52) uses a positive parameter. A nonzero parameter
of either sign gives the same splitting when the shifted factors are nonsingular.
-/
noncomputable def adiSplitting (H V : Matrix ι ι ℝ) {r : ℝ} (hr : r ≠ 0)
    (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))) (hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))) :
    Stationary.Splitting (H + V) :=
  ⟨(2 * r)⁻¹ • ((H + r • 1) * (V + r • 1)),
    isUnit_smul_matrix (inv_ne_zero (mul_ne_zero two_ne_zero hr)) (hH.mul hV)⟩

/-- **Equation (4.52)** of [saad2003iterative]. The matrix of the ADI splitting is
$M = (H + rI)(V + rI)/(2r)$.

**Generalization.** The formula holds for the splitting defined with any nonzero
parameter and invertible shifted factors. -/
theorem adiSplitting_m {hr : r ≠ 0} {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))}
    {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    (adiSplitting H V hr hH hV).m = (2 * r)⁻¹ • ((H + r • 1) * (V + r • 1)) := rfl

private theorem toEuclideanCLM_adiSplitting_m {hr : r ≠ 0}
    {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))} {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    toEuclideanCLM (𝕜 := ℝ) (adiSplitting H V hr hH hV).m
      = (peacemanRachfordSplitting (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) hr
          (isUnit_toEuclideanCLM_add_smul_one hH) (isUnit_toEuclideanCLM_add_smul_one hV)).m := by
  rw [adiSplitting_m, peacemanRachfordSplitting_m, map_smul, map_mul,
    toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one]
  norm_num

private theorem toEuclideanCLM_adiSplitting_n {hr : r ≠ 0}
    {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))} {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    toEuclideanCLM (𝕜 := ℝ) (adiSplitting H V hr hH hV).n
      = (peacemanRachfordSplitting (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) hr
          (isUnit_toEuclideanCLM_add_smul_one hH) (isUnit_toEuclideanCLM_add_smul_one hV)).n := by
  rw [splitting_n_eq, splitting_n_eq, map_sub, toEuclideanCLM_adiSplitting_m, map_add]

/-- **Equation (4.52)** of [saad2003iterative], the complementary part. The ADI splitting has
$$N = \frac{1}{2r} (H - rI)(V - rI),$$
so that $M - N = H + V$.

**Generalization.** The source gives the positive-parameter case. The complementary
matrix has this form for any nonzero parameter with nonsingular shifts. -/
theorem equation_4_52 {hr : r ≠ 0} {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))}
    {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    (adiSplitting H V hr hH hV).n = (2 * r)⁻¹ • ((H - r • 1) * (V - r • 1)) := by
  refine toEuclideanCLM_injective ?_
  rw [toEuclideanCLM_adiSplitting_n, peacemanRachfordSplitting_n, map_smul, map_mul,
    toEuclideanCLM_sub_smul_one, toEuclideanCLM_sub_smul_one]
  norm_num

/-- **Equation (4.52)** of [saad2003iterative], the iteration matrix. The iteration matrix
$I - M^{-1}A$ of the ADI splitting is the matrix $G_r$ of (4.50).

**Generalization.** The source uses a positive parameter. The identification holds
for any nonzero parameter when both shifted factors are nonsingular. -/
theorem adiSplitting_iterationOperator {hr : r ≠ 0}
    {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))} {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} :
    (adiSplitting H V hr hH hV).iterationOperator = G_adi H V r := by
  refine toEuclideanCLM_injective ?_
  rw [toEuclideanCLM_G_adi hH hV, ← peacemanRachfordSplitting_iterationOperator
      (hr := hr) (hH := isUnit_toEuclideanCLM_add_smul_one hH)
      (hV := isUnit_toEuclideanCLM_add_smul_one hV),
    Stationary.Splitting.iterationOperator, Stationary.Splitting.iterationOperator, map_sub,
    map_one, map_mul, toEuclideanCLM_ringInverse (adiSplitting H V hr hH hV).isUnit,
    toEuclideanCLM_adiSplitting_m, map_add]

/-- **Problem P-4.5** of [saad2003iterative], the closed form. If $H + rI$ is nonsingular, the
affine part (4.51) of the sweep is
$$f_r = 2r (V + rI)^{-1} (H + rI)^{-1} b.$$

**Generalization.** Problem P-4.5 uses the positive-parameter splitting with both shifted
factors invertible. The affine identity needs only invertibility of $H+rI$ because
both sides are zero when $V+rI$ is singular under totalized inversion.
-/
theorem f_adi_eq (hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))) (b : ι → ℝ) :
    f_adi H V r b = (2 * r) • ((V + r • 1)⁻¹ *ᵥ ((H + r • 1)⁻¹ *ᵥ b)) := by
  have hkey : (1 : Matrix ι ι ℝ) - (H - r • 1) * (H + r • 1)⁻¹
      = (2 * r) • (H + r • 1)⁻¹ := by
    have h2 : ((H + r • 1) - (H - r • 1)) * (H + r • (1 : Matrix ι ι ℝ))⁻¹
        = (2 * r) • (H + r • 1)⁻¹ := by
      rw [show (H + r • 1) - (H - r • (1 : Matrix ι ι ℝ)) = (2 * r) • (1 : Matrix ι ι ℝ) by module,
        smul_mul_assoc, one_mul]
    rwa [sub_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hH)] at h2
  rw [f_adi, hkey, smul_mulVec, mulVec_smul]

/-- **Problem P-4.5** of [saad2003iterative], the splitting form. Let $r \neq 0$, and let $H + rI$
and $V + rI$ be nonsingular. The affine part (4.51) is $f_r = M^{-1}b$ for the matrix $M$ of the
splitting (4.52). So one sweep of Algorithm 4.3 is the stationary iteration of that splitting.

**Generalization.** Problem P-4.5 uses the positive-parameter splitting. The same
identity holds for every nonzero parameter with both shifted factors invertible. -/
theorem f_adi_eq_m_inv_mulVec {hr : r ≠ 0} {hH : IsUnit (H + r • (1 : Matrix ι ι ℝ))}
    {hV : IsUnit (V + r • (1 : Matrix ι ι ℝ))} (b : ι → ℝ) :
    f_adi H V r b = (adiSplitting H V hr hH hV).m⁻¹ *ᵥ b := by
  refine (nonsing_inv_mulVec_eq (adiSplitting H V hr hH hV).isUnit ?_).symm
  rw [adiSplitting_m, f_adi_eq hH, smul_mulVec, mulVec_smul, ← mulVec_mulVec,
    mulVec_nonsing_inv_mulVec hV, mulVec_nonsing_inv_mulVec hH, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero hr), one_smul]

/-! ### Convergence -/

/-- If $H \in \mathbb{R}^{\iota \times \iota}$ is symmetric positive definite and $r > 0$, then
$H + rI$ is nonsingular, so the half-steps of Algorithm 4.3 are well defined. It supports the
convergence claim of §4.3 of [saad2003iterative]. -/
theorem isUnit_add_smul_one_of_posDef (hH : H.PosDef) (hr : 0 < r) :
    IsUnit (H + r • (1 : Matrix ι ι ℝ)) :=
  (hH.add (PosDef.one.smul hr)).isUnit

/-- **Section 4.3** of [saad2003iterative], the spectral radius. Let
$H, V \in \mathbb{R}^{\iota \times \iota}$ be symmetric positive definite and let $r > 0$. Then
the iteration matrix (4.50) satisfies
$$\rho(G_r) < 1.$$

The proof specializes `Matrix.PosDef.complexSpectralRadius_peacemanRachford_lt_one`. The
Euclidean operator norm of $G_r$ need not be less than $1$. What is less than $1$ is the norm of
its conjugate by $V + rI$, which is the product of two Cayley transforms, and a similarity
preserves the spectrum. -/
theorem adi_complexSpectralRadius_lt_one (hH : H.PosDef) (hV : V.PosDef) (hr : 0 < r) :
    complexSpectralRadius (G_adi H V r) < 1 :=
  hH.complexSpectralRadius_peacemanRachford_lt_one hV hr

/-- **Section 4.3** of [saad2003iterative], the convergence claim, which the book states without
proof. Let $H, V \in \mathbb{R}^{\iota \times \iota}$ be symmetric positive definite, let
$r > 0$, and let $x$ solve $(H + V)x = b$. Then for every starting vector $u_0$ the iterates of
Algorithm 4.3 satisfy
$$u_k \to x.$$

The commutativity of $H$ and $V$ is not needed, and it is not assumed. -/
theorem adi_converges (hH : H.PosDef) (hV : V.PosDef) (hr : 0 < r) (b x₀ : ι → ℝ) {x : ι → ℝ}
    (hx : (H + V) *ᵥ x = b) :
    Tendsto (fun k => (adiStep H V r b)^[k] x₀) atTop (𝓝 x) := by
  have hHu : IsUnit (H + r • (1 : Matrix ι ι ℝ)) := isUnit_add_smul_one_of_posDef hH hr
  have hVu : IsUnit (V + r • (1 : Matrix ι ι ℝ)) := isUnit_add_smul_one_of_posDef hV hr
  obtain ⟨c₁, hc₁, h₁⟩ := ((posDef_iff_isSymmetricCoercive H).1 hH).isCoercive
  obtain ⟨c₂, hc₂, h₂⟩ := ((posDef_iff_isSymmetricCoercive V).1 hV).isCoercive
  have hxe : (toEuclideanCLM (𝕜 := ℝ) H + toEuclideanCLM (𝕜 := ℝ) V)
      (WithLp.toLp 2 x : EuclideanSpace ℝ ι) = WithLp.toLp 2 b := by
    rw [← map_add, toEuclideanCLM_toLp, hx]
  have hlim := tendsto_peacemanRachford (H := toEuclideanCLM (𝕜 := ℝ) H)
    (V := toEuclideanCLM (𝕜 := ℝ) V) ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩ hr hxe (WithLp.toLp 2 x₀)
  have hstep : ∀ y : ι → ℝ, (WithLp.toLp 2 (adiStep H V r b y) : EuclideanSpace ℝ ι)
      = step (peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r)
          (peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
            (WithLp.toLp 2 b)) (WithLp.toLp 2 y) := by
    intro y
    have hs : step (peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r)
        (peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
          (WithLp.toLp 2 b)) (WithLp.toLp 2 y)
        = peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
            (WithLp.toLp 2 y)
          + peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
            (WithLp.toLp 2 b) := rfl
    rw [hs, equation_4_50, WithLp.toLp_add, ← toEuclideanCLM_toLp, toEuclideanCLM_G_adi hHu hVu,
      toLp_f_adi hHu hVu]
  have hiter : ∀ k : ℕ, (WithLp.toLp 2 ((adiStep H V r b)^[k] x₀) : EuclideanSpace ℝ ι)
      = (step (peacemanRachford (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r)
          (peacemanRachfordConst (toEuclideanCLM (𝕜 := ℝ) H) (toEuclideanCLM (𝕜 := ℝ) V) r
            (WithLp.toLp 2 b)))^[k] (WithLp.toLp 2 x₀) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep, ih]
  have hconv := ((PiLp.continuous_ofLp 2 (fun _ : ι => ℝ)).tendsto _).comp hlim
  refine Filter.Tendsto.congr (fun k => ?_) hconv
  simp only [Function.comp_apply, ← hiter k, WithLp.ofLp_toLp]

/-- **Section 4.3** of [saad2003iterative], the convergence claim with the limit named. Let
$H, V \in \mathbb{R}^{\iota \times \iota}$ be symmetric positive definite and let $r > 0$. Then
for every $b$ and every starting vector $u_0$ the iterates of Algorithm 4.3 converge to
$(H + V)^{-1} b$.

The matrix $H + V$ is symmetric positive definite, so the system always has a solution. -/
theorem adi_tendsto_inv_mulVec (hH : H.PosDef) (hV : V.PosDef) (hr : 0 < r) (b x₀ : ι → ℝ) :
    Tendsto (fun k => (adiStep H V r b)^[k] x₀) atTop (𝓝 ((H + V)⁻¹ *ᵥ b)) :=
  adi_converges hH hV hr b x₀
    (mulVec_nonsing_inv_mulVec (Matrix.PosDef.isUnit (Matrix.PosDef.add hH hV)) b)

/-! ### (4.49) for the model problem -/

section ModelProblem

open SaadSparse.Chapter02

/-- **Equation (4.49)** of [saad2003iterative], the horizontal part for the model problem. For mesh
sizes $n_1, n_2$ and spacing $h_1$, the matrix $H = T_1 \otimes I_{n_2}$, where $T_1 = h_1^{-2}
\operatorname{tridiag}(-1, 2, -1)$ of order $n_1$ is the one-dimensional Laplacian in the first
coordinate.

**Reading.** The source describes a horizontal difference operator with variable
coefficients. This definition is the constant-coefficient negative second difference
used by the positive definite model problem in §2.2.5. -/
noncomputable def modelH (n₁ n₂ : ℕ) (h₁ : ℝ) : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  laplacian1D n₁ h₁ ⊗ₖ (1 : Matrix (Fin n₂) (Fin n₂) ℝ)

/-- **Equation (4.49)** of [saad2003iterative], the vertical part for the model problem. For mesh
sizes $n_1, n_2$ and spacing $h_2$, the matrix $V = I_{n_1} \otimes T_2$, where $T_2 = h_2^{-2}
\operatorname{tridiag}(-1, 2, -1)$ of order $n_2$ is the one-dimensional Laplacian in the second
coordinate.

**Reading.** The source describes a vertical difference operator with variable
coefficients. This definition is the constant-coefficient negative second difference
used by the positive definite model problem in §2.2.5. -/
noncomputable def modelV (n₁ n₂ : ℕ) (h₂ : ℝ) : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  (1 : Matrix (Fin n₁) (Fin n₁) ℝ) ⊗ₖ laplacian1D n₂ h₂

/-- **Equation (4.49)** of [saad2003iterative], for the model problem. The five-point matrix of
§2.2.5 on an $n_1 \times n_2$ grid with spacings $h_1$, $h_2$ is $H + V$, with $H$ and $V$ the
horizontal and vertical one-dimensional Laplacians.

The five-point matrix is `SaadSparse.Chapter02.laplacian2D`. The identity is
`SaadSparse.Chapter02.laplacian2D_eq_kroneckerSum` read as the sum of its two Kronecker factors.

**Reading.** Equation (4.49) gives the split system with variable coefficients. This identity
states the operator decomposition for the constant-coefficient $-\Delta$ model problem. -/
theorem laplacian2D_eq_modelH_add_modelV (n₁ n₂ : ℕ) (h₁ h₂ : ℝ) :
    laplacian2D n₁ n₂ h₁ h₂ = modelH n₁ n₂ h₁ + modelV n₁ n₂ h₂ :=
  laplacian2D_eq_kroneckerSum n₁ n₂ h₁ h₂

private theorem posDef_kronecker_one {m p : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef) :
    (A ⊗ₖ (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef := by
  obtain ⟨c, hc, hcw⟩ := ((posDef_iff_isSymmetricCoercive A).1 hA).isCoercive
  have hz : (toEuclideanLin (0 : Matrix (Fin p) (Fin p) ℝ)).IsCoerciveWith 0 := by
    intro z; simp
  have hsum : A ⊗ₖ (1 : Matrix (Fin p) (Fin p) ℝ) = A ⊕ₖ (0 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [kroneckerSum_def, kronecker_zero, add_zero]
  rw [hsum, posDef_iff_isSymmetricCoercive]
  refine ⟨isSymmetric_toEuclideanLin_iff.2 (isHermitian_kroneckerSum
    (Matrix.PosDef.isHermitian hA) isHermitian_zero), c, hc, ?_⟩
  have h := isCoerciveWith_kroneckerSum hcw hz
  rwa [add_zero] at h

private theorem posDef_one_kronecker {m p : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} (hB : B.PosDef) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ B).PosDef := by
  obtain ⟨c, hc, hcw⟩ := ((posDef_iff_isSymmetricCoercive B).1 hB).isCoercive
  have hz : (toEuclideanLin (0 : Matrix (Fin m) (Fin m) ℝ)).IsCoerciveWith 0 := by
    intro z; simp
  have hsum : (1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ B = (0 : Matrix (Fin m) (Fin m) ℝ) ⊕ₖ B := by
    rw [kroneckerSum_def, zero_kronecker, zero_add]
  rw [hsum, posDef_iff_isSymmetricCoercive]
  refine ⟨isSymmetric_toEuclideanLin_iff.2 (isHermitian_kroneckerSum isHermitian_zero
    (Matrix.PosDef.isHermitian hB)), c, hc, ?_⟩
  have h := isCoerciveWith_kroneckerSum hz hcw
  rwa [zero_add] at h

/-- For $h_1 \neq 0$, the horizontal part $H$ of the model problem is symmetric positive definite.
It supports `SaadSparse.Chapter04.adi_model_problem`. -/
theorem modelH_posDef (n₁ n₂ : ℕ) {h₁ : ℝ} (h₁0 : h₁ ≠ 0) : (modelH n₁ n₂ h₁).PosDef :=
  posDef_kronecker_one (laplacian1D_posDef n₁ h₁0)

/-- For $h_2 \neq 0$, the vertical part $V$ of the model problem is symmetric positive definite. It
supports `SaadSparse.Chapter04.adi_model_problem`. -/
theorem modelV_posDef (n₁ n₂ : ℕ) {h₂ : ℝ} (h₂0 : h₂ ≠ 0) : (modelV n₁ n₂ h₂).PosDef :=
  posDef_one_kronecker (laplacian1D_posDef n₂ h₂0)

/-- **Section 4.3** of [saad2003iterative], the model problem. Let $h_1, h_2 \neq 0$, let $r > 0$,
and let $x$ solve $Ax = b$ for the five-point matrix $A$ of §2.2.5 on an $n_1 \times n_2$ grid.
Then Algorithm 4.3 for the splitting $A = H + V$ into the horizontal and vertical
one-dimensional Laplacians converges to $x$ from every starting vector.

**Reading.** This instance uses the constant-coefficient $-\Delta$ discretization of §2.2.5.
The result concerns convergence at each fixed positive parameter. The source's asymptotic
rate comparison concerns the optimal parameter. -/
theorem adi_model_problem (n₁ n₂ : ℕ) {h₁ h₂ : ℝ} (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0) {r : ℝ}
    (hr : 0 < r) (b x₀ : Fin n₁ × Fin n₂ → ℝ) {x : Fin n₁ × Fin n₂ → ℝ}
    (hx : laplacian2D n₁ n₂ h₁ h₂ *ᵥ x = b) :
    Tendsto (fun k => (adiStep (modelH n₁ n₂ h₁) (modelV n₁ n₂ h₂) r b)^[k] x₀) atTop (𝓝 x) :=
  adi_converges (modelH_posDef n₁ n₂ h₁0) (modelV_posDef n₁ n₂ h₂0) hr b x₀
    (by rwa [← laplacian2D_eq_modelH_add_modelV])

end ModelProblem

end SaadSparse.Chapter04
