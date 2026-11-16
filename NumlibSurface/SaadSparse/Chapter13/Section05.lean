/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Multigrid.TwoGrid
import NumlibSurface.SaadSparse.Chapter13.Section04

/-!
# Saad, Section 13.5: Analysis of the two-grid cycle

This module formalizes Section 13.5 of [saad2003iterative]: the two subspaces (13.57)–(13.61) of the
Galerkin two-grid cycle, the pair of norms $\|\cdot\|_D$ and $\|\cdot\|_{D^{-1}}$ of Section 13.5.2,
the smoothing property (13.62) and the approximation property (13.63), Theorem 13.3 with its rate
(13.64), Example 13.7 on full weighting of a sine mode, and Example 13.8, which verifies the
smoothing property for weighted Jacobi. The smooth subspace
$\mathcal{S}_h = \operatorname{Ran}(Q_h)$ is the range of the prolongation, the oscillatory subspace
$\mathcal{T}_h = \operatorname{Ran}(T_h^H)$ is its $A_h$-orthogonal complement, and the fine space
is their direct sum. Theorem 13.3 says that one coarse-grid correction followed by one smoothing
step contracts the $A_h$-norm of the error by the factor $\sqrt{1 - \alpha/\beta}$.

The proofs specialize `Numlib.Multigrid.TwoGrid`, whose hypotheses `Multigrid.IsSmootherWith` and
`Multigrid.IsApproximationWith` are (13.62) and (13.63) for an abstract dual pair of seminorms. This
module adds the concrete pair of the book, $\|x\|_D = (Dx, x)^{1/2}$ and
$\|y\|_{D^{-1}} = (D^{-1}y, y)^{1/2}$ with $D = \operatorname{diag}(A)$, and proves that it is a
dual pair, by the Cauchy–Schwarz inequality in the $D$-inner product.

## Main definitions

* Equation (13.58), `SaadSparse.Chapter13.smoothSubspace`: the smooth subspace
  $\mathcal{S}_h = \operatorname{Ran}(Q_h)$.
* Equation (13.58), `SaadSparse.Chapter13.oscillatorySubspace`: the oscillatory subspace
  $\mathcal{T}_h = \operatorname{Ran}(T_h^H)$.
* Section 13.5.2, `SaadSparse.Chapter13.normD`: the norm $\|x\|_D = (Dx, x)^{1/2}$.
* Section 13.5.2, `SaadSparse.Chapter13.normDinv`: the norm $\|y\|_{D^{-1}} = (D^{-1}y, y)^{1/2}$.
* Equation (13.62), `SaadSparse.Chapter13.equation_13_62`: the smoothing property with constant
  $\alpha$.
* Equation (13.63), `SaadSparse.Chapter13.equation_13_63`: the approximation property with constant
  $\beta$.
* Equation (13.19), `SaadSparse.Chapter13.weightedJacobiSmoother`: the weighted Jacobi smoother
  $I - \omega D^{-1}A$.
* Section 13.5.2, `SaadSparse.Chapter13.diagScaled`: the scaled matrix $D^{-1/2} A D^{-1/2}$.
* Example 13.8, `SaadSparse.Chapter13.gammaJacobi`: the constant
  $\gamma = \rho(D^{-1/2} A D^{-1/2})$.

## Main results

* Equation (13.59), `SaadSparse.Chapter13.equation_13_59`:
  $\Omega_h = \mathcal{S}_h \oplus \mathcal{T}_h$.
* Equation (13.60), `SaadSparse.Chapter13.equation_13_60` and
  `SaadSparse.Chapter13.equation_13_60_ker`: $\mathcal{S}_h = \operatorname{Ran}(I_H^h) =
  \operatorname{Null}(T_h^H)$.
* Equation (13.61), `SaadSparse.Chapter13.equation_13_61` and
  `SaadSparse.Chapter13.equation_13_61_ker`: $\mathcal{T}_h = \operatorname{Null}(I_h^H A_h) =
  \operatorname{Null}(Q_h)$.
* Equation (13.61), `SaadSparse.Chapter13.oscillatorySubspace_ne_ker_of_restriction`: in general
  $\mathcal{T}_h \neq \operatorname{Null}(I_h^H)$.
* Example 13.7, `SaadSparse.Chapter13.example_13_7` and `SaadSparse.Chapter13.example_13_7_smul`:
  full weighting maps the fine sine mode $w_k^h$ to $\cos^2(\theta_k/2)$ times a coarse sine wave.
* Example 13.7, `SaadSparse.Chapter13.example_13_7_le_half`: on the upper half of the spectrum the
  factor $\cos^2(\theta_k/2)$ is at most $\frac12$.
* Section 13.5.2, `SaadSparse.Chapter13.isDualSeminormPair_normD`:
  $|(u, w)| \le \|u\|_{D^{-1}}\|w\|_D$.
* Theorem 13.3, `SaadSparse.Chapter13.theorem_13_3_le`: $\alpha \le \beta$ when the coarse grid is
  smaller.
* Theorem 13.3 and equation (13.64), `SaadSparse.Chapter13.theorem_13_3`: $\|S_h T_h^H e\|_A \le
  \sqrt{1 - \alpha/\beta}\,\|e\|_A$.
* Theorem 13.3, `SaadSparse.Chapter13.theorem_13_3_cycle`: the same contraction for the two-grid
  operator with at least one post-smoothing step.
* Theorem 13.3, `SaadSparse.Chapter13.theorem_13_3_lt_one`: the rate $\sqrt{1 - \alpha/\beta}$ is
  less than $1$ when $0 < \alpha \le \beta$.
* Example 13.8, `SaadSparse.Chapter13.example_13_8_of_le`: weighted Jacobi has the smoothing
  property with $\alpha = \omega(2 - \omega\gamma)$ for every $\gamma$ with
  $(Ax, x) \le \gamma(Dx, x)$.
* Example 13.8, `SaadSparse.Chapter13.hasEigenvalue_gammaJacobi` and
  `SaadSparse.Chapter13.le_gammaJacobi`: $\gamma$ is an eigenvalue of $D^{-1/2} A D^{-1/2}$ and
  satisfies $(Ax, x) \le \gamma(Dx, x)$.
* Example 13.8, `SaadSparse.Chapter13.example_13_8`: weighted Jacobi has the smoothing property with
  $\alpha = \omega(2 - \omega\gamma)$, $\gamma = \rho(D^{-1/2} A D^{-1/2})$.
* Example 13.8, `SaadSparse.Chapter13.example_13_8_pos`: $\alpha > 0$ for $0 < \omega < 2/\gamma$.

## Implementation notes

* The pair of grids satisfies the standing hypotheses `SaadSparse.Chapter13.IsCoarsening` of Section
  13.4: $A_h$ is symmetric positive definite, $I_H^h$ is injective, and $I_h^H$ is a positive
  multiple of $(I_H^h)^T$.
* The norms $\|\cdot\|_D$ and $\|\cdot\|_{D^{-1}}$ are `energyNorm` at $D$ and at $D^{-1}$, and the
  $A$-norm is `energyNorm` at $A$. Their duality is `Multigrid.isDualSeminormPair_energy`, whose two
  inputs are the positive definiteness of $D$ and the fact that $D^{-1}$ is a right inverse of $D$.
* The book writes the constant of Example 13.8 both as $\rho(D^{-1/2} A D^{-1/2})$ and as
  $\rho(D^{-1}A)$. The two matrices are similar, so the numbers are equal. The library states the
  bound with the symmetric matrix, where it is the largest eigenvalue `SaadSparse.lambdaMax`. The
  smoothing property itself is `Multigrid.isSmootherWith_richardson` at
  $D = \operatorname{diag}(A)$.

## Deviations from the source

* **Equation (13.61)** (correction). The book's last equality reads
  $\mathcal{T}_h = \operatorname{Null}(I_h^H)$, without the factor $A_h$; this is false, and
  $\mathcal{T}_h = \operatorname{Null}(I_h^H A_h)$. See `SaadSparse.Chapter13.equation_13_61` and
  `SaadSparse.Chapter13.oscillatorySubspace_ne_ker_of_restriction`.
-/

open Finset Matrix Stationary

open scoped SaadSparse Real

namespace SaadSparse.Chapter13

variable {n m : ℕ}

/-- The action of a product of matrices on a vector: $(MN)x = M(Nx)$. -/
private theorem mul_act {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (N : Matrix (Fin q) (Fin r) ℝ)
    (x : EuclideanSpace ℝ (Fin r)) : ((M * N) ⬝ x) = M ⬝ (N ⬝ x) := by
  rw [Matrix.toLpLin_mul_same]
  rfl

/-- For real matrices $M$ and $N$, $(Mx, Ny) = (N^T M x, y)$. -/
private theorem inner_act_act (M N : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : inner ℝ (M ⬝ x) (N ⬝ y) = inner ℝ ((Nᵀ * M) ⬝ x) y := by
  rw [← LinearMap.adjoint_inner_left (toEuclideanLin N) y (M ⬝ x), adjoint_toEuclideanLin,
    mul_act]

/-- A vector $v$ is in the null space of the linear map of a matrix $M$ if and only if $Mv = 0$. -/
private theorem mem_ker_toEuclideanLin_iff {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (v : Fin q → ℝ) :
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin q)) ∈ LinearMap.ker (toEuclideanLin M)
      ↔ M *ᵥ v = 0 :=
  ⟨fun h => congrArg WithLp.ofLp (LinearMap.mem_ker.1 h),
    fun h => LinearMap.mem_ker.2 (WithLp.ofLp_injective 2 h)⟩

/-! ### Section 13.5.1: Two important subspaces, (13.57)–(13.61) -/

section Subspaces

variable {A : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
  {P : Matrix (Fin n) (Fin m) ℝ}

/-- **Equation (13.58)** of [saad2003iterative]. The **smooth subspace**
$\mathcal{S}_h = \operatorname{Ran}(Q_h)$ is the range of the coarse-grid projector
$Q_h = I_H^h A_H^{-1} I_h^H A_h$.

By `SaadSparse.Chapter13.equation_13_60` it is the range of the prolongation. -/
noncomputable def smoothSubspace (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (toEuclideanLin (coarseProjector R A P))

/-- The smooth subspace is the range of the coarse-grid projector $Q_h$. -/
theorem smoothSubspace_def (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    smoothSubspace R A P = LinearMap.range (toEuclideanLin (coarseProjector R A P)) := rfl

/-- **Equation (13.58)** of [saad2003iterative]. The **oscillatory subspace**
$\mathcal{T}_h = \operatorname{Ran}(T_h^H)$ is the range of the coarse-grid correction operator
$T_h^H = I - Q_h$: the errors that a coarse-grid correction can leave. -/
noncomputable def oscillatorySubspace (R : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (toEuclideanLin (coarseCorrection R A P))

/-- The oscillatory subspace is the range of the coarse-grid correction operator $T_h^H$. -/
theorem oscillatorySubspace_def (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    oscillatorySubspace R A P = LinearMap.range (toEuclideanLin (coarseCorrection R A P)) := rfl

/-- **Equation (13.60)** of [saad2003iterative], the range. If $(A_h, I_h^H, I_H^h)$ is a
coarsening, then the smooth subspace is the range of the prolongation:
$$\mathcal{S}_h = \operatorname{Ran}(Q_h) = \operatorname{Ran}(I_H^h).$$

The inclusion $\subseteq$ follows from the form of $Q_h$. The reverse inclusion follows from the
Galerkin identity $A_H = I_h^H A_h I_H^h$, which makes $Q_h$ fix every vector of
$\operatorname{Ran}(I_H^h)$. -/
theorem equation_13_60 (h : IsCoarsening A R P) :
    smoothSubspace R A P = LinearMap.range (toEuclideanLin P) := by
  rw [smoothSubspace_def, toEuclideanLin_coarseProjector h, Multigrid.range_coarseProjection]

/-- **Equation (13.60)** of [saad2003iterative], the null space. If $(A_h, I_h^H, I_H^h)$ is a
coarsening, then the smooth subspace is the null space of the coarse-grid correction operator:
$$\operatorname{Null}(T_h^H) = \mathcal{S}_h.$$
So the coarse-grid correction annihilates exactly the coarse space. -/
theorem equation_13_60_ker (h : IsCoarsening A R P) :
    LinearMap.ker (toEuclideanLin (coarseCorrection R A P)) = smoothSubspace R A P := by
  rw [toEuclideanLin_coarseCorrection h, Multigrid.ker_coarseCorrection, equation_13_60 h]

/-- **Equation (13.61)** of [saad2003iterative]. If $(A_h, I_h^H, I_H^h)$ is a coarsening, then the
oscillatory subspace is the null space of $I_h^H A_h$:
$$\mathcal{T}_h = \operatorname{Null}(I_h^H A_h).$$
These are the vectors whose residual is orthogonal to the coarse space.

**Correction.** The book drops the factor $A_h$ in the last equality of (13.61) and writes
$\mathcal{T}_h = \operatorname{Null}(I_h^H)$. This is false: $\mathcal{T}_h$ is the
$A_h$-orthogonal complement of $\operatorname{Ran}(I_H^h)$, while $\operatorname{Null}(I_h^H)$
is its Euclidean orthogonal complement. See
`SaadSparse.Chapter13.oscillatorySubspace_ne_ker_of_restriction`. Nothing in the chapter uses
the false form: the proof of Theorem 13.3 uses only that $\mathcal{T}_h$ is $A_h$-orthogonal to
$\operatorname{Ran}(I_H^h)$. -/
theorem equation_13_61 (h : IsCoarsening A R P) :
    oscillatorySubspace R A P = LinearMap.ker (toEuclideanLin (R * A)) := by
  have hker : LinearMap.range (Multigrid.coarseCorrection (toEuclideanLin A)
        h.isSymmetricCoercive (toEuclideanLin P))
      = LinearMap.ker (toEuclideanLin (Pᵀ * A)) := by
    rw [Multigrid.range_coarseCorrection, adjoint_toEuclideanLin, ← Matrix.toLpLin_mul_same]
  obtain ⟨c, hc, rfl⟩ := h.exists_smul
  rw [oscillatorySubspace_def, toEuclideanLin_coarseCorrection h, hker, Matrix.smul_mul, map_smul,
    LinearMap.ker_smul _ _ hc.ne']

/-- **Equation (13.61)** of [saad2003iterative], the null space of $Q_h$. If $(A_h, I_h^H, I_H^h)$
is a coarsening, then the oscillatory subspace is the null space of the coarse-grid projector:
$$\operatorname{Null}(Q_h) = \mathcal{T}_h.$$
-/
theorem equation_13_61_ker (h : IsCoarsening A R P) :
    LinearMap.ker (toEuclideanLin (coarseProjector R A P)) = oscillatorySubspace R A P := by
  rw [oscillatorySubspace_def, toEuclideanLin_coarseProjector h, toEuclideanLin_coarseCorrection h,
    Multigrid.ker_coarseProjection, Multigrid.range_coarseCorrection]

/-- **Equation (13.59)** of [saad2003iterative]. If $(A_h, I_h^H, I_H^h)$ is a coarsening, then the
fine space is the direct sum of the smooth and the oscillatory subspaces:
$$\Omega_h = \mathcal{S}_h \oplus \mathcal{T}_h.$$

The sum is direct because $Q_h$ is a projector, and it is $A_h$-orthogonal by Lemma 13.1. The
statement is `IsCompl`. -/
theorem equation_13_59 (h : IsCoarsening A R P) :
    IsCompl (smoothSubspace R A P) (oscillatorySubspace R A P) := by
  rw [equation_13_60 h, oscillatorySubspace_def, toEuclideanLin_coarseCorrection h,
    Multigrid.range_coarseCorrection]
  exact Multigrid.isCompl_range_ker (toEuclideanLin A) h.isSymmetricCoercive (toEuclideanLin P)

end Subspaces

/-! ### The last equality of (13.61) is false -/

/-- The prolongation from a one-point coarse grid to a two-point fine grid that sets the first
component and leaves the second one zero, the matrix $\begin{bmatrix} 1 \\ 0 \end{bmatrix}$. -/
private def counterProlongation : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

private theorem laplacian1D_two : laplacian1D 2 = !![2, -1; -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [laplacian1D_apply]

private theorem transpose_mul_counterProlongation :
    counterProlongationᵀ * counterProlongation = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [counterProlongation, Matrix.mul_apply, Fin.sum_univ_two]

private theorem injective_counterProlongation :
    Function.Injective (toEuclideanLin counterProlongation) := by
  intro x y hxy
  have hxy' : counterProlongation *ᵥ WithLp.ofLp x = counterProlongation *ᵥ WithLp.ofLp y :=
    congrArg WithLp.ofLp hxy
  have hres := congrArg (fun z => counterProlongationᵀ *ᵥ z) hxy'
  simp only [Matrix.mulVec_mulVec, transpose_mul_counterProlongation, Matrix.one_mulVec] at hres
  exact WithLp.ofLp_injective 2 hres

/-- **Equation (13.61)** of [saad2003iterative], the printed form is false. There is a coarsening
$(A_h, I_h^H, I_H^h)$ with $A_h \in \mathbb{R}^{2 \times 2}$ and a one-point coarse grid whose
oscillatory subspace is not the null space of the restriction:
$$\mathcal{T}_h \neq \operatorname{Null}(I_h^H).$$

The example is $A_h = \operatorname{tridiag}(-1, 2, -1)$ of order two, the prolongation
$I_H^h = \begin{bmatrix} 1 \\ 0 \end{bmatrix}$ and the restriction $I_h^H = (I_H^h)^T$. The
second coordinate vector $e$ lies in $\operatorname{Null}(I_h^H)$ but not in
$\mathcal{T}_h = \operatorname{Null}(I_h^H A_h)$, because $A_h e = (-1, 2)$ is not orthogonal to
the coarse space. The argument of Section 13.5.1 compares the decompositions $\Omega_h =
\operatorname{Ran}(Q_h) \oplus \operatorname{Null}(Q_h)$ and $\Omega_h =
\operatorname{Ran}(I_H^h) \oplus \operatorname{Null}((I_H^h)^T)$. They have the same first
summand but need not have the same second summand: the first decomposition is $A_h$-orthogonal
and the second is Euclidean orthogonal. -/
theorem oscillatorySubspace_ne_ker_of_restriction :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 1) (Fin 2) ℝ)
      (P : Matrix (Fin 2) (Fin 1) ℝ), IsCoarsening A R P ∧
        oscillatorySubspace R A P ≠ LinearMap.ker (toEuclideanLin R) := by
  have hcoarse : IsCoarsening (laplacian1D 2) counterProlongationᵀ counterProlongation :=
    ⟨laplacian1D_posDef 2, injective_counterProlongation, 1, one_pos, (one_smul ℝ _).symm⟩
  refine ⟨laplacian1D 2, counterProlongationᵀ, counterProlongation, hcoarse, ?_⟩
  rw [equation_13_61 hcoarse]
  intro hcontra
  have h1 : (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))
      ∈ LinearMap.ker (toEuclideanLin counterProlongationᵀ) := by
    rw [mem_ker_toEuclideanLin_iff]
    ext i
    fin_cases i
    simp [counterProlongation, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [← hcontra, mem_ker_toEuclideanLin_iff] at h1
  have h2 := congrFun h1 (0 : Fin 1)
  norm_num [counterProlongation, laplacian1D_two, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at h2

/-! ### Example 13.7: What full weighting does to a sine mode -/

/-- The coarse index $k$ read as an index of the fine grid of $2m + 1$ points. The $m$ coarse modes
$w_k^{2h}$ and the first $m$ fine modes $w_k^h$ have the same $k$, and their angles satisfy
$\theta_k^{2h} = 2\theta_k^h$. -/
def coarseIndex (m : ℕ) (k : Fin m) : Fin (2 * m + 1) :=
  ⟨(k : ℕ), k.isLt.trans_le (by omega)⟩

/-- The coarse angle is twice the fine angle: $2\theta_k^h = k\pi/(m+1) = \theta_k^{2h}$ for a
coarse index $k$, with the fine grid of $2m + 1$ points. -/
theorem two_mul_theta_coarseIndex (m : ℕ) (k : Fin m) :
    2 * theta (2 * m + 1) (coarseIndex m k) = (((k : ℕ) : ℝ) + 1) * π / ((m : ℝ) + 1) := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [theta, show ((coarseIndex m k : Fin (2 * m + 1)) : ℕ) = (k : ℕ) from rfl]
  push_cast
  field_simp
  ring

/-- **Example 13.7** of [saad2003iterative]. In one dimension, full weighting maps the fine sine
mode $w_k^h$ of the grid of $2m + 1$ points to the sine wave of the same frequency on the coarse
grid, scaled by $\cos^2(\theta_k/2)$:
$$(I_h^{2h} w_k^h)_j = \cos^2\frac{\theta_k}{2} \, \sin(2j\theta_k), \qquad j = 1, \dots, m.$$

This holds for every fine index $k$. The proof is
`Multigrid.fullWeighting_mulVec_sineVec_apply`: the stencil $\frac14 [1\ 2\ 1]$ together with
$\sin((2j-1)\theta) + \sin((2j+1)\theta) = 2\sin(2j\theta)\cos\theta$, and then the half-angle
formula $(1 + \cos\theta)/2 = \cos^2(\theta/2)$. -/
theorem example_13_7 (m : ℕ) (k : Fin (2 * m + 1)) (q : Fin m) :
    (restriction1D m *ᵥ sineVec (2 * m + 1) k) q
      = Real.cos (theta (2 * m + 1) k / 2) ^ 2
        * Real.sin (2 * (((q : ℕ) : ℝ) + 1) * theta (2 * m + 1) k) := by
  rw [theta]
  exact Multigrid.fullWeighting_mulVec_sineVec_apply k q

/-- **Example 13.7** of [saad2003iterative], the coarse modes. A fine mode whose index $k$ is that
of a coarse mode is mapped by full weighting to that coarse mode, damped by
$\cos^2(\theta_k^h/2)$:
$$I_h^{2h} w_k^h = \cos^2\frac{\theta_k^h}{2} \, w_k^{2h}.$$
-/
theorem example_13_7_smul (m : ℕ) (k : Fin m) :
    restriction1D m *ᵥ sineVec (2 * m + 1) (coarseIndex m k)
      = Real.cos (theta (2 * m + 1) (coarseIndex m k) / 2) ^ 2 • sineVec m k := by
  funext q
  rw [Pi.smul_apply, smul_eq_mul, example_13_7, sineVec_apply,
    ← two_mul_theta_coarseIndex m k]
  ring_nf

/-- **Example 13.7** of [saad2003iterative], the oscillatory half. On the fine grid of $n = 2m + 1$
points, if $k > n/2$, then the damping factor of full weighting satisfies
$$\cos^2\frac{\theta_k}{2} \le \frac12.$$
So an oscillatory mode is close to the null space of $I_h^{2h}$.

With the $0$-based index `k`, the condition is `2 * m + 2 ≤ 2 * (k + 1)`. -/
theorem example_13_7_le_half (m : ℕ) {k : Fin (2 * m + 1)}
    (hk : 2 * m + 2 ≤ 2 * ((k : ℕ) + 1)) :
    Real.cos (theta (2 * m + 1) k / 2) ^ 2 ≤ 1 / 2 := by
  have h := sin_sq_theta_div_two_ge_half (2 * m + 1) (k := k) (by omega)
  have hpy := Real.sin_sq_add_cos_sq (theta (2 * m + 1) k / 2)
  linarith

/-! ### Section 13.5.2: The two norms of the convergence analysis -/

section Norms

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Section 13.5.2** of [saad2003iterative]. The **$D$-norm** of $x \in \mathbb{R}^n$, with $D$
the diagonal of $A$, is
$$\|x\|_D = (Dx, x)^{1/2} = \|D^{1/2}x\|_2.$$

The definition is `energyNorm` at $D$. For a matrix $A$ with a nonpositive diagonal entry this
is not a norm; the results below assume that $A$ is positive definite. -/
noncomputable def normD (A : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyNorm (toEuclideanLin (diagPart A)) x

/-- **Section 13.5.2** of [saad2003iterative]. The **$D^{-1}$-norm** of $y \in \mathbb{R}^n$, with
$D$ the diagonal of $A$, is
$$\|y\|_{D^{-1}} = (D^{-1}y, y)^{1/2} = \|D^{-1/2}y\|_2.$$
For a residual $y = Ae$ it is the norm that the book writes $\|Ae\|_{D^{-1}}$.

The definition is `energyNorm` at the Lean matrix inverse of $D$. -/
noncomputable def normDinv (A : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyNorm (toEuclideanLin (diagPart A)⁻¹) y

/-- The diagonal of a symmetric positive definite matrix is positive definite. -/
theorem posDef_diagPart (hA : A.PosDef) : (diagPart A).PosDef := by
  have hd : diagPart A = diagonal fun i => A i i := rfl
  rw [hd, Matrix.posDef_diagonal_iff]
  exact fun i => Matrix.PosDef.diag_pos hA

/-- The diagonal of a symmetric positive definite matrix is invertible. -/
theorem isUnit_diagPart_of_posDef (hA : A.PosDef) : IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).2 fun i => (Matrix.PosDef.diag_pos hA (i := i)).ne'

/-- The inverse of the diagonal of a symmetric positive definite matrix is positive definite, so
$\|\cdot\|_{D^{-1}}$ is a norm. -/
theorem posDef_inv_diagPart (hA : A.PosDef) : ((diagPart A)⁻¹).PosDef := by
  rw [inv_diagPart (isUnit_diagPart_of_posDef hA), Matrix.posDef_diagonal_iff]
  exact fun i => inv_pos.2 (Matrix.PosDef.diag_pos hA)

/-- For a symmetric positive definite matrix $A$, its diagonal $D$ is a symmetric coercive operator,
so $\|\cdot\|_D$ is the norm of an inner product. -/
theorem isSymmetricCoercive_diagPart (hA : A.PosDef) :
    (toEuclideanLin (diagPart A)).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive _).1 (posDef_diagPart hA)

/-- For a symmetric positive definite matrix $A$, the inverse $D^{-1}$ of its diagonal is a
symmetric coercive operator, so $\|\cdot\|_{D^{-1}}$ is the norm of an inner product. -/
theorem isSymmetricCoercive_inv_diagPart (hA : A.PosDef) :
    (toEuclideanLin (diagPart A)⁻¹).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive _).1 (posDef_inv_diagPart hA)

/-- For a symmetric positive definite matrix $A$ with diagonal $D$, $D(D^{-1}u) = u$ for every $u$.
This is the hypothesis of `Multigrid.isDualSeminormPair_energy`. -/
theorem toEuclideanLin_diagPart_inv (hA : A.PosDef) (u : EuclideanSpace ℝ (Fin n)) :
    (diagPart A ⬝ ((diagPart A)⁻¹ ⬝ u)) = u :=
  Matrix.toEuclideanLin_mul_nonsing_inv_apply (isUnit_diagPart_of_posDef hA) u

/-- **Section 13.5.2** of [saad2003iterative]. For a symmetric positive definite matrix $A$,
$\|x\|_D^2 = \sum_i a_{ii} x_i^2$. -/
theorem normD_sq (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    normD A x ^ 2 = ∑ i, A i i * WithLp.ofLp x i ^ 2 := by
  rw [normD, (isSymmetricCoercive_diagPart hA).energyNorm_sq, real_inner_apply_self,
    RCLike.re_to_real, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    rw [show diagPart A = diagonal fun j => A j j from rfl, mulVec_diagonal]
    ring

/-- **Section 13.5.2** of [saad2003iterative]. For a symmetric positive definite matrix $A$,
$\|y\|_{D^{-1}}^2 = \sum_i y_i^2/a_{ii}$. -/
theorem normDinv_sq (hA : A.PosDef) (y : EuclideanSpace ℝ (Fin n)) :
    normDinv A y ^ 2 = ∑ i, WithLp.ofLp y i ^ 2 / A i i := by
  rw [normDinv, (isSymmetricCoercive_inv_diagPart hA).energyNorm_sq, real_inner_apply_self,
    RCLike.re_to_real, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    rw [inv_diagPart (isUnit_diagPart_of_posDef hA), mulVec_diagonal]
    ring

/-- **Section 13.5.2** of [saad2003iterative], the duality of the two norms. Let $A$ be symmetric
positive definite. Then $\|\cdot\|_D$ and $\|\cdot\|_{D^{-1}}$ are dual to each other:
$$|(u, w)| \le \|u\|_{D^{-1}} \, \|w\|_D \quad \text{for all } u, w.$$

This is the Cauchy–Schwarz inequality in the $D$-inner product, with $(u, w) = (D D^{-1}u, w)$,
and it is the only property of the pair that Theorem 13.3 uses. The statement is
`Multigrid.IsDualSeminormPair`. -/
theorem isDualSeminormPair_normD (hA : A.PosDef) :
    Multigrid.IsDualSeminormPair ℝ (normD A) (normDinv A) :=
  Multigrid.isDualSeminormPair_energy (isSymmetricCoercive_diagPart hA)
    (toEuclideanLin_diagPart_inv hA)

end Norms

/-! ### Section 13.5.2: The smoothing and approximation properties, (13.62)–(13.63) -/

/-- **Equation (13.62)** of [saad2003iterative]. A smoother with error propagation operator $S$ has
the **smoothing property** with constant $\alpha$ if
$$\|Se\|_A^2 \le \|e\|_A^2 - \alpha \|Ae\|_{D^{-1}}^2 \quad \text{for every error } e.$$

It is a property of the smoother and cannot be proved by linear algebra alone; Example 13.8
verifies it for weighted Jacobi. The definition is `Multigrid.IsSmootherWith`. -/
def equation_13_62 (A S : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : Prop :=
  Multigrid.IsSmootherWith (toEuclideanLin A) (normDinv A) (toEuclideanLin S) α

/-- The smoothing property (13.62) written out: $\|Se\|_A^2 \le \|e\|_A^2 - \alpha\|Ae\|_{D^{-1}}^2$
for every $e$. -/
theorem equation_13_62_iff (A S : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    equation_13_62 A S α ↔ ∀ e : EuclideanSpace ℝ (Fin n),
      energyNorm (toEuclideanLin A) (S ⬝ e) ^ 2
        ≤ energyNorm (toEuclideanLin A) e ^ 2 - α * normDinv A (A ⬝ e) ^ 2 :=
  Iff.rfl

/-- **Equation (13.63)** of [saad2003iterative]. The coarse space $\operatorname{Ran}(I_H^h)$ has
the **approximation property** with constant $\beta$ if every error is approximated from it to
within $\beta\|e\|_A^2$ in the $D$-norm:
$$\min_{u_H \in \Omega_H} \|e - I_H^h u_H\|_D^2 \le \beta \|e\|_A^2 \quad \text{for every } e.$$

The definition is `Multigrid.IsApproximationWith`, which asks for some $u_H$ with this bound. On
a finite-dimensional coarse space the minimum is attained, so this is the same statement
(`SaadSparse.Chapter13.equation_13_63_iff`). -/
def equation_13_63 (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) : Prop :=
  Multigrid.IsApproximationWith (toEuclideanLin A) (normD A) (LinearMap.range (toEuclideanLin P)) β

/-- The approximation property (13.63) written out: for every $e$ there is a coarse vector $u$ with
$\|e - I_H^h u\|_D^2 \le \beta\|e\|_A^2$. -/
theorem equation_13_63_iff (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) :
    equation_13_63 A P β ↔ ∀ e : EuclideanSpace ℝ (Fin n), ∃ u : EuclideanSpace ℝ (Fin m),
      normD A (e - (P ⬝ u)) ^ 2 ≤ β * energyNorm (toEuclideanLin A) e ^ 2 := by
  refine ⟨fun h e => ?_, fun h e => ?_⟩
  · obtain ⟨c, ⟨u, rfl⟩, hc⟩ := h e
    exact ⟨u, hc⟩
  · obtain ⟨u, hu⟩ := h e
    exact ⟨_, ⟨u, rfl⟩, hu⟩

/-! ### Section 13.5.2: Theorem 13.3 -/

section Theorem133

variable {A : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
  {P : Matrix (Fin n) (Fin m) ℝ} {S : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}

/-- If $(A, R, P)$ is a coarsening and $m < n$, then the oscillatory subspace contains a nonzero
vector.

This is why the inequality $\alpha \le \beta$ of Theorem 13.3 holds. For $m = n$ the coarse-grid
correction is zero and every pair of constants is admissible. -/
theorem exists_ne_zero_mem_oscillatorySubspace (h : IsCoarsening A R P) (hmn : m < n) :
    ∃ e ∈ oscillatorySubspace R A P, e ≠ 0 := by
  refine (Submodule.ne_bot_iff _).1 fun hbot => absurd hmn (not_lt.2 ?_)
  set f := LinearMap.adjoint (toEuclideanLin P) ∘ₗ toEuclideanLin A with hf
  have hrange : oscillatorySubspace R A P = LinearMap.ker f := by
    rw [oscillatorySubspace_def, toEuclideanLin_coarseCorrection h,
      Multigrid.range_coarseCorrection]
  have hker : Module.finrank ℝ (LinearMap.ker f) = 0 := by
    rw [hrange] at hbot
    rw [hbot, finrank_bot]
  have hadd : Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f)
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
    LinearMap.finrank_range_add_finrank_ker f
  have hle : Module.finrank ℝ (LinearMap.range f) ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) :=
    Submodule.finrank_le _
  rw [hker, add_zero, finrank_euclideanSpace_fin] at hadd
  rw [finrank_euclideanSpace_fin] at hle
  omega

/-- **Theorem 13.3** of [saad2003iterative], comparison of the constants. Let $(A_h, I_h^H, I_H^h)$
be a coarsening with $m < n$. If the smoother $S$ has the smoothing property (13.62) with
constant $\alpha$ and the coarse space has the approximation property (13.63) with constant
$\beta$, then
$$\alpha \le \beta.$$

The hypothesis $m < n$, a coarse grid with fewer points, is needed: see
`SaadSparse.Chapter13.exists_ne_zero_mem_oscillatorySubspace`. -/
theorem theorem_13_3_le (h : IsCoarsening A R P) (hmn : m < n) (hsm : equation_13_62 A S α)
    (happ : equation_13_63 A P β) : α ≤ β := by
  obtain ⟨e, hmem, he0⟩ := exists_ne_zero_mem_oscillatorySubspace h hmn
  rw [oscillatorySubspace_def, toEuclideanLin_coarseCorrection h] at hmem
  exact Multigrid.IsSmootherWith.le_of_isApproximationWith (hA := h.isSymmetricCoercive) hsm
    (isDualSeminormPair_normD h.posDef) happ hmem he0

/-- **Theorem 13.3** of [saad2003iterative] for a full two-grid cycle. Let $(A_h, I_h^H, I_H^h)$ be
a coarsening, let the smoother $S$ have the smoothing property (13.62) with constant
$\alpha \ge 0$, and let the coarse space have the approximation property (13.63) with constant
$\beta > 0$. Then for all $\nu_1 \ge 0$ and $\nu_2 \ge 1$ the two-grid operator
$M_H^h = S^{\nu_2} T_h^H S^{\nu_1}$ of (13.43) satisfies
$$\|M_H^h v\|_A \le \sqrt{1 - \alpha/\beta} \, \|v\|_A \quad \text{for every } v.$$

If $\alpha > \beta$, the square root of the negative number is $0$ in Lean. -/
theorem theorem_13_3_cycle (h : IsCoarsening A R P) (hsm : equation_13_62 A S α)
    (happ : equation_13_63 A P β) (hα : 0 ≤ α) (hβ : 0 < β) {ν₁ ν₂ : ℕ} (hν : 1 ≤ ν₂)
    (v : EuclideanSpace ℝ (Fin n)) :
    energyNorm (toEuclideanLin A) (equation_13_43 R A P S ν₁ ν₂ ⬝ v)
      ≤ Real.sqrt (1 - α / β) * energyNorm (toEuclideanLin A) v := by
  have hop : (equation_13_43 R A P S ν₁ ν₂ ⬝ v)
      = Multigrid.twoGridOperator (toEuclideanLin A) h.isSymmetricCoercive (toEuclideanLin P)
          (toEuclideanLin S) ν₁ ν₂ v :=
    congrFun (congrArg _ (equation_13_43_eq h S ν₁ ν₂)) v
  rw [hop]
  exact Multigrid.energyNorm_twoGridOperator_le (hA := h.isSymmetricCoercive) hsm
    (isDualSeminormPair_normD h.posDef) happ hα hβ hν v

/-- **Theorem 13.3** of [saad2003iterative] and equation (13.64). Let $(A_h, I_h^H, I_H^h)$ be a
coarsening, let the smoother $S$ have the smoothing property (13.62) with constant
$\alpha \ge 0$, and let the coarse space have the approximation property (13.63) with constant
$\beta > 0$. Then one coarse-grid correction followed by one smoothing step contracts the
$A$-norm of the error:
$$\|S T_h^H e\|_A \le \sqrt{1 - \alpha/\beta} \, \|e\|_A \quad \text{for every } e.$$

If $\alpha > \beta$, the square root of the negative number is $0$ in Lean. -/
theorem theorem_13_3 (h : IsCoarsening A R P) (hsm : equation_13_62 A S α)
    (happ : equation_13_63 A P β) (hα : 0 ≤ α) (hβ : 0 < β) (v : EuclideanSpace ℝ (Fin n)) :
    energyNorm (toEuclideanLin A) ((S * coarseCorrection R A P) ⬝ v)
      ≤ Real.sqrt (1 - α / β) * energyNorm (toEuclideanLin A) v := by
  have heq : S * coarseCorrection R A P = equation_13_43 R A P S 0 1 := by
    rw [equation_13_43, pow_zero, pow_one, Matrix.mul_one]
  rw [heq]
  exact theorem_13_3_cycle h hsm happ hα hβ le_rfl v

/-- **Theorem 13.3** of [saad2003iterative], convergence. If $0 < \alpha \le \beta$, then the rate
(13.64) is less than one:
$$\sqrt{1 - \alpha/\beta} < 1.$$
So the two-level iteration converges. -/
theorem theorem_13_3_lt_one (hα : 0 < α) (hβ : 0 < β) (hle : α ≤ β) :
    Real.sqrt (1 - α / β) < 1 := by
  have hpos : 0 < α / β := div_pos hα hβ
  calc Real.sqrt (1 - α / β) < Real.sqrt 1 := by
        refine Real.sqrt_lt_sqrt (by linarith [div_le_one_of_le₀ hle hβ.le]) (by linarith)
    _ = 1 := Real.sqrt_one

end Theorem133

/-! ### Example 13.8: The smoothing property of weighted Jacobi -/

section Example138

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Equation (13.19)** of [saad2003iterative] as a smoother. The **weighted Jacobi smoother** has
the error propagation operator
$$S(\omega) = I - \omega D^{-1} A,$$
with $D$ the diagonal of $A$.

The inverse is the Lean matrix inverse, which is $0$ if $D$ is singular. -/
noncomputable def weightedJacobiSmoother (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - ω • ((diagPart A)⁻¹ * A)

/-- The weighted Jacobi smoother is the smoother (13.40) with the approximate inverse
$B = \omega D^{-1}$. -/
theorem weightedJacobiSmoother_eq_smoother (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    weightedJacobiSmoother A ω = smoother A (ω • (diagPart A)⁻¹) := by
  rw [weightedJacobiSmoother, smoother_def, Matrix.smul_mul]

/-- If $D$ is invertible and $\omega \neq 0$, then the weighted Jacobi smoother is the iteration
operator of `Matrix.jorSplitting`, as in Section 13.2.2. -/
theorem weightedJacobiSmoother_eq_iterationOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    weightedJacobiSmoother A ω = (jorSplitting A h hω).iterationOperator :=
  (jorSplitting_iterationOperator_eq A h hω).symm

/-- The linear map of the weighted Jacobi smoother is $1 - \omega \, (D^{-1} \circ A)$, the form
that `Multigrid.isSmootherWith_richardson` expects. -/
theorem toEuclideanLin_weightedJacobiSmoother (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    toEuclideanLin (weightedJacobiSmoother A ω)
      = 1 - (ω : ℝ) • (toEuclideanLin (diagPart A)⁻¹ ∘ₗ toEuclideanLin A) := by
  rw [weightedJacobiSmoother, map_sub, map_smul, Matrix.toEuclideanLin_mul,
    Matrix.toEuclideanLin_one]
  rfl

/-- **Example 13.8** of [saad2003iterative], with a general constant. Let $A$ be symmetric positive
definite with diagonal $D$, and let $\gamma$ satisfy
$$(Ax, x) \le \gamma \, (Dx, x) \quad \text{for every } x.$$
Then for every $\omega \in \mathbb{R}$ the weighted Jacobi smoother $S(\omega)$ has the
smoothing property (13.62) with the constant $\alpha = \omega(2 - \omega\gamma)$.

The computation is (13.65): the expansion of $\|S(\omega)e\|_A^2$ leaves $\|e\|_A^2 -
(\omega(2I - \omega D^{-1/2} A D^{-1/2}) D^{-1/2} A e, D^{-1/2} A e)$. -/
theorem example_13_8_of_le (hA : A.PosDef) {γ : ℝ}
    (hγ : ∀ x : EuclideanSpace ℝ (Fin n),
      inner ℝ (A ⬝ x) x ≤ γ * inner ℝ (diagPart A ⬝ x) x) (ω : ℝ) :
    equation_13_62 A (weightedJacobiSmoother A ω) (ω * (2 - ω * γ)) := by
  have hrich := Multigrid.isSmootherWith_richardson (𝕜 := ℝ)
    ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA) (isSymmetricCoercive_diagPart hA)
    (toEuclideanLin_diagPart_inv hA) (γ := γ) (fun x => by simpa using hγ x) ω
  rw [equation_13_62, toEuclideanLin_weightedJacobiSmoother]
  exact hrich

/-- The matrix $D^{1/2} = \operatorname{diag}(\sqrt{a_{ii}})$ of the square roots of the diagonal
entries of $A$. -/
noncomputable def diagSqrt (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => Real.sqrt (A i i)

/-- The matrix $D^{-1/2} = \operatorname{diag}(1/\sqrt{a_{ii}})$ of the inverse square roots of the
diagonal entries of $A$. An entry with $a_{ii} \le 0$ gives $0$, because the Lean square root of
a nonpositive number is $0$ and $0^{-1} = 0$. -/
noncomputable def diagInvSqrt (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => (Real.sqrt (A i i))⁻¹

/-- **Section 13.5.2** of [saad2003iterative], also used in Section 13.6.1. The **symmetrically
scaled matrix** is
$$\hat A = D^{-1/2} A D^{-1/2}.$$
For a matrix with a positive diagonal, its diagonal entries are $1$. Its spectral radius is the
constant $\gamma$ of Example 13.8. -/
noncomputable def diagScaled (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagInvSqrt A * A * diagInvSqrt A

/-- The matrix $D^{1/2}$ is symmetric. -/
theorem transpose_diagSqrt (A : Matrix (Fin n) (Fin n) ℝ) : (diagSqrt A)ᵀ = diagSqrt A :=
  Matrix.diagonal_transpose _

/-- For a symmetric positive definite matrix $A$, $D^{1/2} D^{1/2} = D$. -/
theorem diagSqrt_mul_diagSqrt (hA : A.PosDef) : diagSqrt A * diagSqrt A = diagPart A := by
  rw [diagSqrt, Matrix.diagonal_mul_diagonal]
  exact congrArg _ (funext fun i =>
    Real.mul_self_sqrt (Matrix.PosDef.diag_pos hA (i := i)).le)

/-- For a symmetric positive definite matrix $A$, $D^{-1/2} D^{1/2} = I$. -/
theorem diagInvSqrt_mul_diagSqrt (hA : A.PosDef) : diagInvSqrt A * diagSqrt A = 1 := by
  rw [diagInvSqrt, diagSqrt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg _ (funext fun i =>
    inv_mul_cancel₀ (Real.sqrt_pos.2 (Matrix.PosDef.diag_pos hA (i := i))).ne')

/-- For a symmetric positive definite matrix $A$, $D^{1/2} D^{-1/2} = I$. -/
theorem diagSqrt_mul_diagInvSqrt (hA : A.PosDef) : diagSqrt A * diagInvSqrt A = 1 := by
  rw [diagInvSqrt, diagSqrt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg _ (funext fun i =>
    mul_inv_cancel₀ (Real.sqrt_pos.2 (Matrix.PosDef.diag_pos hA (i := i))).ne')

/-- The symmetrically scaled matrix $D^{-1/2} A D^{-1/2}$ of a symmetric matrix $A$ is symmetric. -/
theorem isHermitian_diagScaled (hA : A.IsHermitian) : (diagScaled A).IsHermitian := by
  have hdiag : (diagInvSqrt A)ᴴ = diagInvSqrt A := by
    rw [diagInvSqrt, Matrix.diagonal_conjTranspose]
    exact congrArg _ (funext fun i => rfl)
  rw [Matrix.IsHermitian, diagScaled, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hdiag,
    hA, Matrix.mul_assoc]

/-- **Example 13.8** of [saad2003iterative]. For a symmetric positive definite
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, the constant
$$\gamma = \rho(D^{-1/2} A D^{-1/2})$$
is the largest eigenvalue of the symmetrically scaled matrix. It is its spectral radius because
the scaled matrix is symmetric positive definite.

The book also writes $\gamma = \rho(D^{-1}A)$; the two matrices are similar. The definition is
`SaadSparse.lambdaMax` of the scaled matrix. -/
noncomputable def gammaJacobi [NeZero n] (hA : A.PosDef) : ℝ :=
  lambdaMax (isHermitian_diagScaled (Matrix.PosDef.isHermitian hA))

/-- **Example 13.8** of [saad2003iterative], $\gamma$ is an eigenvalue. For a symmetric positive
definite $A$ with $n \ge 1$, the number $\gamma$ is an eigenvalue of $D^{-1/2} A D^{-1/2}$.

By `SaadSparse.Chapter13.le_gammaJacobi` no eigenvalue exceeds it. The eigenvalues of the scaled
matrix are positive, so $\gamma$ is its spectral radius $\rho(D^{-1/2} A D^{-1/2})$. -/
theorem hasEigenvalue_gammaJacobi [NeZero n] (hA : A.PosDef) :
    Module.End.HasEigenvalue (toEuclideanLin (diagScaled A)) (gammaJacobi hA) := by
  have hH := isHermitian_diagScaled (Matrix.PosDef.isHermitian hA)
  have hval : ∃ i, hH.eigenvalues i = gammaJacobi hA := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hH.eigenvalues
    exact ⟨i, hi.symm⟩
  obtain ⟨i, hi⟩ := hval
  exact (hH.hasEigenvalue_toEuclideanLin_iff _).2 ⟨i, by simpa using hi⟩

/-- **Example 13.8** of [saad2003iterative], the bound on the quadratic form. For a symmetric
positive definite $A$ with $n \ge 1$ and every $x$,
$$(Ax, x) \le \gamma \, (Dx, x).$$

The substitution $v = D^{1/2}x$ turns this into the Rayleigh quotient bound
$(D^{-1/2} A D^{-1/2} v, v) \le \gamma (v, v)$. -/
theorem le_gammaJacobi [NeZero n] (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A ⬝ x) x ≤ gammaJacobi hA * inner ℝ (diagPart A ⬝ x) x := by
  have hbd := isSymmetricBoundedBy_toEuclideanLin
    (isHermitian_diagScaled (Matrix.PosDef.isHermitian hA))
  have h := hbd.re_inner_le (diagSqrt A ⬝ x)
  have hmat : diagSqrt A * (diagScaled A * diagSqrt A) = A := by
    calc diagSqrt A * (diagScaled A * diagSqrt A)
        = diagSqrt A * diagInvSqrt A * A * (diagInvSqrt A * diagSqrt A) := by
          rw [diagScaled]; noncomm_ring
      _ = A := by
          rw [diagSqrt_mul_diagInvSqrt hA, diagInvSqrt_mul_diagSqrt hA, Matrix.one_mul,
            Matrix.mul_one]
  have hinner : inner ℝ (diagScaled A ⬝ (diagSqrt A ⬝ x)) (diagSqrt A ⬝ x) = inner ℝ (A ⬝ x) x := by
    rw [← mul_act, inner_act_act, transpose_diagSqrt, hmat]
  have hnorm : ‖(diagSqrt A ⬝ x)‖ ^ 2 = inner ℝ (diagPart A ⬝ x) x := by
    rw [← real_inner_self_eq_norm_sq, inner_act_act, transpose_diagSqrt, diagSqrt_mul_diagSqrt hA]
  rw [RCLike.re_to_real, hinner, hnorm] at h
  exact h

/-- **Example 13.8** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite with $n \ge 1$, and let $\gamma = \rho(D^{-1/2} A D^{-1/2})$. Then for every
$\omega \in \mathbb{R}$ the weighted Jacobi smoother $S(\omega) = I - \omega D^{-1}A$ has the
smoothing property (13.62) with the constant
$$\alpha = \omega(2 - \omega\gamma).$$

The constant is positive for $0 < \omega < 2/\gamma$ (`SaadSparse.Chapter13.example_13_8_pos`),
but the inequality holds for every $\omega$. -/
theorem example_13_8 [NeZero n] (hA : A.PosDef) (ω : ℝ) :
    equation_13_62 A (weightedJacobiSmoother A ω) (ω * (2 - ω * gammaJacobi hA)) :=
  example_13_8_of_le hA (le_gammaJacobi hA) ω

/-- **Example 13.8** of [saad2003iterative], the range of $\omega$. Let $\gamma > 0$ and
$0 < \omega < 2/\gamma$. Then the smoothing constant is positive:
$$\omega(2 - \omega\gamma) > 0.$$

This is the range $0 < \omega < 2/\rho(D^{-1}A)$ of the book, on which weighted Jacobi also
converges. The converse, that $\alpha > 0$ only on this range, is not stated here. -/
theorem example_13_8_pos {γ ω : ℝ} (hγ : 0 < γ) (hω : 0 < ω) (hω2 : ω < 2 / γ) :
    0 < ω * (2 - ω * γ) := by
  have h : ω * γ < 2 := by
    rw [lt_div_iff₀ hγ] at hω2
    linarith
  exact mul_pos hω (by linarith)

end Example138

end SaadSparse.Chapter13
