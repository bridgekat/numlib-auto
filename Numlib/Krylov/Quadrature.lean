/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Lagrange
import Numlib.Approximation.Quadrature
import Numlib.Eigen.Sturm
import Numlib.Krylov.OrthogonalPolynomials

/-!
# Quadratic forms, Gauss and Gauss–Radau quadrature through Lanczos

Let $A$ be a symmetric operator on a finite-dimensional inner product space, and let $v$ be a
vector. A quadratic form $\langle v, f(A) v \rangle$ is an integral $\int f \, d\mu_v$ against the
discrete spectral measure $\mu_v$ of $(A, v)$ (`Krylov.spectralMeasure`), and the Lanczos process
computes Gauss and Gauss–Radau quadrature rules for this measure ([golub2013matrix], §10.2, after
Golub and Meurant; [meurant2006lanczos], §2, for the Gauss rule). The module
`Numlib.Krylov.OrthogonalPolynomials` provides the measure and the exactness of the $m$-point Gauss
rule of the compression of $A$ (`Lanczos.gauss_quadrature`). This module adds integrands that are
not polynomials, the Golub–Welsch form of the Gauss rule, the Gauss–Radau rule through a modified
Lanczos matrix, the remainders of both rules, and the two-sided bound
$$G_m(f) \le \langle v, f(A) v \rangle \le GR_m(a)(f)$$
for integrands whose derivatives of order $2m$ and $2m + 1$ have suitable signs.

The Gauss rule has as nodes the eigenvalues $\theta_j$ of the Lanczos matrix $T_m$, and as weights
$\|v\|^2$ times the squared first components of its normalized eigenvectors ([golub2013matrix], Fact
3 and (10.2.12)). The Gauss–Radau rule with a prescribed node $a$ comes from the
$(m+1) \times (m+1)$ matrix $\tilde T$ that agrees with $T_{m+1}$ except in its last diagonal entry
$\tilde\alpha = a + \beta_{m-1}^2 ((T_m - a)^{-1})_{m-1,m-1}$, which makes $a$ an eigenvalue
([golub2013matrix], §10.2.5, after Golub (1973)). This rule integrates every polynomial of degree at
most $2m$ exactly.

## Main definitions

* `Lanczos.radauCorrection`: the correction $\beta_{m-1}^2 ((T_m - a)^{-1})_{m-1,m-1}$ of the last
  diagonal entry.
* `Lanczos.radauTridiag`: the Gauss–Radau Lanczos matrix $\tilde T$.

## Main results

* `Matrix.IsHermitian.inner_cfc_eq_integral_spectralMeasure`: $v^H f(A) v = \int f \, d\mu_v$ for a
  Hermitian matrix $A$ and every $f : \mathbb{R} \to \mathbb{R}$ ([golub2013matrix], (10.2.6)).
* `Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag`: the Golub–Welsch form of the Gauss
  rule, $G_m(f) = \|v\|^2 \sum_j s_{j,0}^2 f(\theta_j)$ ([golub2013matrix], Fact 3 and (10.2.12)).
* `Lanczos.radauTridiag_hasEigenvalue`: $a$ is an eigenvalue of $\tilde T$.
* `Lanczos.radau_quadrature`: the rule of $\tilde T$ has the node $a$ and integrates every
  polynomial of degree at most $2m$ exactly.
* `Lanczos.exists_gauss_error_eq` and `Lanczos.exists_radau_error_eq`: the remainders of the two
  rules in Hermite form.
* `Lanczos.gauss_le_integral_le_radau`: the two-sided bound
  $G_m(f) \le \int f \, d\mu_v \le GR_m(a)(f)$.

## Proof outline

The Golub–Welsch form interpolates $f$ by a polynomial on the finitely many eigenvalues involved, so
only the polynomial moments $\langle v, p(A_m) v \rangle = \|v\|^2 \, p(T_m)_{00}$ have to be
compared. The Gauss–Radau rule is exact to degree $2m$ because the entry $(T^j)_{00}$ for $j \le 2m$
does not depend on the last diagonal entry of a tridiagonal matrix $T$
(`Matrix.pow_apply_zero_zero_eq_of_isTridiagonal`). The remainders are instances of the Hermite
remainder for a finite measure, `Quadrature.exists_error_eq_of_hermite`, and the two-sided bound is
an instance of `Quadrature.gauss_le_integral_le_gaussRadau`. Their hypotheses need distinct nodes
inside the interval that carries the spectrum. The nodes are distinct because $T_m$ and $\tilde T$
are unreduced, and an eigenvector of an unreduced symmetric tridiagonal matrix has a nonzero first
component (`Matrix.IsUnreducedUpperHessenberg.apply_zero_ne_zero_of_isSymm`). The nodes lie in the
interval because a rule with positive weights that is exact to a high enough degree has its nodes in
the support interval (`Quadrature.mem_Icc_of_isExactOnMeasure`).

## Notation

* $\mu_v$ is the spectral measure `Krylov.spectralMeasure` of $(A, v)$.
* $T_m$ is the Lanczos matrix `Lanczos.tridiag A v m`.
* $\beta_j$ is the Lanczos coefficient `Lanczos.beta A v j`.
* $(\theta_j, s_j)$ are the eigenpairs of $T_m$, and $(\tilde\theta_j, \tilde s_j)$ are those of
  $\tilde T$, with orthonormal eigenvectors.
* $m$ is the number of Lanczos steps. The hypothesis $\dim \mathcal{K}_m(A, v) = m$, which is
  `Module.finrank 𝕜 (Krylov.subspace A v m) = m`, says that the process has not broken down before
  step $m$.

## Implementation notes

* For a matrix, $f(A)$ is the continuous functional calculus `cfc f A` of Mathlib. The spectral
  measure of `Matrix.toEuclideanLin A` is built from `LinearMap.IsSymmetric.eigenvectorBasis`, and
  the eigenbasis `Matrix.IsHermitian.eigenvectorBasis` of Mathlib is a reindexing of it, so the two
  sums agree (`Matrix.IsHermitian.integral_spectralMeasure_toEuclideanLin`).
* The inverse in `Lanczos.radauCorrection` is `Matrix.inv`, which is $0$ at a singular matrix. The
  results about the Gauss–Radau rule assume that $T_m - a I$ is invertible.
-/

open MeasureTheory Polynomial Finset

open scoped Matrix

/-! ### Quadratic forms of a Hermitian matrix as integrals -/

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- Let $A$ be a Hermitian $n \times n$ matrix over $\mathbb{K}$ with
$A = U \operatorname{diag}(\lambda) U^H$ for the unitary matrix $U$ of eigenvectors. Then for
every $f : \mathbb{R} \to \mathbb{R}$ and $v \in \mathbb{K}^n$
$$v^H f(A) v = \sum_i |(U^H v)_i|^2 \, f(\lambda_i).$$

Here $f(A)$ is `cfc f A`, $U$ is `Matrix.IsHermitian.eigenvectorUnitary`, and $\lambda_i$ is
`Matrix.IsHermitian.eigenvalues`. -/
theorem star_dotProduct_cfc_mulVec (hA : A.IsHermitian) (f : ℝ → ℝ) (v : n → 𝕜) :
    star v ⬝ᵥ (cfc f A *ᵥ v) =
      ((∑ i, ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ v) i‖ ^ 2 *
        f (hA.eigenvalues i) : ℝ) : 𝕜) := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  have hw : star v ᵥ* U = star (star U *ᵥ v) := by
    rw [star_mulVec, ← star_eq_conjTranspose, star_star]
  rw [cfc_eq hA f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← mulVec_mulVec,
    ← mulVec_mulVec, dotProduct_mulVec, hw]
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Pi.star_apply]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, ← mul_assoc, mul_comm _ ((f (hA.eigenvalues i) : ℝ) : 𝕜), mul_assoc,
    RCLike.conj_mul]
  ring

/-- Let $A$ be a Hermitian $n \times n$ matrix with $A = U \operatorname{diag}(\lambda) U^H$, and
let $v \in \mathbb{K}^n$. The spectral measure $\mu_v$ of the operator `Matrix.toEuclideanLin A`
and the vector $v$ satisfies, for every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f \, d\mu_v = \sum_i |(U^H v)_i|^2 \, f(\lambda_i).$$

The measure `Krylov.spectralMeasure` is built from `LinearMap.IsSymmetric.eigenvectorBasis`. The
basis `Matrix.IsHermitian.eigenvectorBasis` of Mathlib is the same basis reindexed by
`Fintype.equivOfCardEq`, so the two sums agree term by term. -/
theorem integral_spectralMeasure_toEuclideanLin (hA : A.IsHermitian) (v : EuclideanSpace 𝕜 n)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂(Krylov.spectralMeasure (isSymmetric_toEuclideanLin_iff.mpr hA)
      finrank_euclideanSpace v) =
      ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ v.ofLp) i‖ ^ 2 *
        f (hA.eigenvalues i) := by
  rw [Krylov.integral_spectralMeasure]
  refine Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)) _ _ fun i => ?_
  have hev : hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) i) =
      (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace i := by
    simp [IsHermitian.eigenvalues, IsHermitian.eigenvalues₀]
  have hvec : (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ v.ofLp)
      (Fintype.equivOfCardEq (Fintype.card_fin _) i) =
      inner 𝕜 ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace i)
        v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp only [mulVec, dotProduct, star_apply, eigenvectorUnitary_apply,
      IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply,
      Pi.star_apply]
  rw [hev, hvec]

/-- **Quadratic forms as integrals** ([golub2013matrix], (10.2.6)). Let $A$ be a Hermitian
$n \times n$ matrix over $\mathbb{K}$, and let $v \in \mathbb{K}^n$. For every
$f : \mathbb{R} \to \mathbb{R}$,
$$v^H f(A) v = \int f \, d\mu_v,$$
where $\mu_v$ is the spectral measure of $(A, v)$ and $f(A)$ is the continuous functional
calculus `cfc f A`. -/
theorem inner_cfc_eq_integral_spectralMeasure (hA : A.IsHermitian) (f : ℝ → ℝ) (v : n → 𝕜) :
    star v ⬝ᵥ (cfc f A *ᵥ v) =
      ((∫ x, f x ∂(Krylov.spectralMeasure (isSymmetric_toEuclideanLin_iff.mpr hA)
        finrank_euclideanSpace (WithLp.toLp 2 v)) : ℝ) : 𝕜) := by
  rw [star_dotProduct_cfc_mulVec hA, integral_spectralMeasure_toEuclideanLin hA]

end Matrix.IsHermitian

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℝ}

/-- Let $T$ be a real symmetric matrix with $T = U \operatorname{diag}(\theta) U^T$ for an
orthonormal eigenbasis $U$. Then for every real polynomial $p$, the diagonal entries of $p(T)$
are
$$p(T)_{ii} = \sum_j U_{ij}^2 \, p(\theta_j).$$
-/
theorem aeval_apply_self (hT : T.IsHermitian) (p : ℝ[X]) (i : n) :
    aeval T p i i = ∑ j, (hT.eigenvectorBasis j i) ^ 2 * p.eval (hT.eigenvalues j) := by
  have h := star_dotProduct_cfc_mulVec hT (fun x => p.eval x) (Pi.single i 1)
  rw [cfc_polynomial p T hT.isSelfAdjoint] at h
  have hl : star (Pi.single i (1 : ℝ)) ⬝ᵥ (aeval T p *ᵥ Pi.single i 1) = aeval T p i i := by
    simp [star_trivial]
  rw [hl] at h
  rw [h]
  simp only [RCLike.ofReal_real_eq_id, id]
  refine sum_congr rfl fun j _ => ?_
  have hs : (star (hT.eigenvectorUnitary : Matrix n n ℝ) *ᵥ Pi.single i 1) j =
      hT.eigenvectorBasis j i := by
    simp [star_trivial]
  rw [hs, Real.norm_eq_abs, sq_abs]

end Matrix.IsHermitian

/-! ### The Golub–Welsch form of the Gauss rule, and Gauss–Radau -/

namespace Lanczos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open Krylov

/-- The real symmetric Lanczos matrix $T_m$ is Hermitian. -/
theorem tridiag_isHermitian (A : E →ₗ[𝕜] E) (v : E) (m : ℕ) : (tridiag A v m).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (tridiag_isSymm A v m)

section GolubWelsch

variable [FiniteDimensional 𝕜 E]

/-- Two functions that agree at the eigenvalues of $B$ have the same integral against the spectral
measure of $B$. -/
private theorem integral_spectralMeasure_congr {n : ℕ} {B : E →ₗ[𝕜] E} (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (u : E) {f g : ℝ → ℝ}
    (hfg : ∀ i, f (hB.eigenvalues hn i) = g (hB.eigenvalues hn i)) :
    ∫ x, f x ∂(spectralMeasure hB hn u) = ∫ x, g x ∂(spectralMeasure hB hn u) := by
  rw [integral_spectralMeasure, integral_spectralMeasure]
  exact sum_congr rfl fun i _ => by rw [hfg]

/-- For the compression $A_m$ of a symmetric $A$ to $\mathcal{K}_m$, with
$0 < m \le \operatorname{grade}(A, v)$, and every real polynomial $p$, $\langle v, p(A_m) v
\rangle = \|v\|^2 \, p(T_m)_{00}$. -/
private theorem inner_aeval_compression {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) {m : ℕ}
    (hm : 0 < m) (hmg : m ≤ grade A v) (p : ℝ[X]) :
    inner 𝕜 (⟨v, self_mem_subspace A v hm⟩ : subspace A v m)
        (aeval (compression A (subspace A v m)) (p.map (algebraMap ℝ 𝕜))
          ⟨v, self_mem_subspace A v hm⟩) =
      ((‖v‖ ^ 2 * aeval (tridiag A v m) p ⟨0, hm⟩ ⟨0, hm⟩ : ℝ) : 𝕜) := by
  set b := Arnoldi.orthonormalBasis A v hmg
  have hv0 : v ≠ 0 := by
    rintro rfl
    have := grade_zero A
    omega
  have hb0 : (⟨v, self_mem_subspace A v hm⟩ : subspace A v m) =
      ((‖v‖ : ℝ) : 𝕜) • b ⟨0, hm⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Arnoldi.coe_orthonormalBasis_apply, Fin.val_mk,
      Arnoldi.vec_zero A v hv0, smul_smul, mul_inv_cancel₀ (by simpa using hv0), one_smul]
  have hmat : LinearMap.toMatrixAlgEquiv b.toBasis (compression A (subspace A v m)) =
      (tridiag A v m).map (algebraMap ℝ 𝕜) := by
    rw [← hessenbergSq_eq_map_tridiag v hA, Arnoldi.hessenbergSq_eq_toMatrix_compression A v hmg]
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hentry : ∀ g : Module.End 𝕜 (subspace A v m),
      inner 𝕜 (b ⟨0, hm⟩) (g (b ⟨0, hm⟩)) =
        LinearMap.toMatrixAlgEquiv b.toBasis g ⟨0, hm⟩ ⟨0, hm⟩ :=
    fun g => by
      rw [LinearMap.toMatrixAlgEquiv_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  have haeval : LinearMap.toMatrixAlgEquiv b.toBasis
      (aeval (compression A (subspace A v m)) (p.map (algebraMap ℝ 𝕜))) =
      (aeval (tridiag A v m) p).map (algebraMap ℝ 𝕜) := by
    have he := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b.toBasis :
      Module.End 𝕜 (subspace A v m) →ₐ[𝕜] Matrix (Fin m) (Fin m) 𝕜)
      (compression A (subspace A v m)) (p.map (algebraMap ℝ 𝕜))
    rw [AlgEquiv.coe_toAlgHom] at he
    have hmap : (tridiag A v m).map (algebraMap ℝ 𝕜) =
        (Algebra.ofId ℝ 𝕜).mapMatrix (tridiag A v m) := rfl
    rw [← he, hmat, aeval_map_algebraMap, hmap, aeval_algHom_apply, AlgHom.mapMatrix_apply]
    rfl
  rw [hb0, inner_smul_left, map_smul, inner_smul_right, hentry, haeval, Matrix.map_apply,
    RCLike.conj_ofReal, RCLike.algebraMap_eq_ofReal]
  push_cast
  ring

/-- **The Golub–Welsch form of the Gauss rule** ([golub2013matrix], Fact 3 and (10.2.12)). Let $E$
be finite-dimensional, let $A$ be symmetric, let $v \in E$, and let $m \ge 1$ with
$\dim \mathcal{K}_m(A, v) = m$. Let $(\theta_j, s_j)$ be the eigenpairs of $T_m$ with
orthonormal eigenvectors. Then for every $f : \mathbb{R} \to \mathbb{R}$, the integral of $f$
against the spectral measure of the compression of $A$ to $\mathcal{K}_m$ and of the vector $v$
is
$$\int f \, d\mu_{A_m, v} = \|v\|^2 \sum_j s_{j,0}^2 \, f(\theta_j).$$
The left side is the $m$-point Gauss rule of `Lanczos.gauss_quadrature`. -/
theorem integral_spectralMeasure_compression_eq_sum_tridiag {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (v : E) {m : ℕ} (hm : 0 < m) (hmk : Module.finrank 𝕜 (subspace A v m) = m) (f : ℝ → ℝ) :
    ∫ x, f x ∂(spectralMeasure (compression.isSymmetric A (subspace A v m) hA) hmk
      ⟨v, self_mem_subspace A v hm⟩) =
      ‖v‖ ^ 2 * ∑ j, ((tridiag_isHermitian A v m).eigenvectorBasis j ⟨0, hm⟩) ^ 2 *
        f ((tridiag_isHermitian A v m).eigenvalues j) := by
  have hmg : m ≤ grade A v := by
    have h := finrank_subspace A v m
    rw [hmk] at h
    omega
  set hC := compression.isSymmetric A (subspace A v m) hA
  set hT := tridiag_isHermitian A v m
  set S : Finset ℝ := univ.image (hC.eigenvalues hmk) ∪ univ.image hT.eigenvalues
  obtain ⟨p, hp⟩ : ∃ p : ℝ[X], ∀ x ∈ S, p.eval x = f x :=
    ⟨Lagrange.interpolate S id f, fun x hx => by
      simpa using Lagrange.eval_interpolate_at_node (r := f) (Set.injOn_id _) hx⟩
  have hpC : ∀ i, f (hC.eigenvalues hmk i) = p.eval (hC.eigenvalues hmk i) := fun i =>
    (hp _ (mem_union_left _ (mem_image_of_mem _ (mem_univ i)))).symm
  have hpT : ∀ j, f (hT.eigenvalues j) = p.eval (hT.eigenvalues j) := fun j =>
    (hp _ (mem_union_right _ (mem_image_of_mem _ (mem_univ j)))).symm
  rw [integral_spectralMeasure_congr hC hmk _ (g := fun x => p.eval x) hpC]
  simp_rw [hpT]
  rw [← Matrix.IsHermitian.aeval_apply_self hT p ⟨0, hm⟩]
  refine RCLike.ofReal_injective (K := 𝕜) ?_
  rw [← inner_aeval_compression hA v hm hmg p]
  exact (inner_aeval_eq_integral hC hmk _ p).symm

end GolubWelsch

/-- The **Gauss–Radau correction** of the last diagonal entry: for $m \ge 1$ and $a \in \mathbb{R}$
it is
$$\beta_{m-1}^2 \, ((T_m - a I)^{-1})_{m-1,m-1},$$
and for $m = 0$ it is $0$. The inverse is `Matrix.inv`, which is $0$ at a singular matrix. -/
noncomputable def radauCorrection (A : E →ₗ[𝕜] E) (v : E) (m : ℕ) (a : ℝ) : ℝ :=
  if h : 0 < m then
    beta A v (m - 1) ^ 2 * (tridiag A v m - a • 1)⁻¹ ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
  else 0

/-- **The Gauss–Radau Lanczos matrix** ([golub2013matrix], §10.2.5). For $m \in \mathbb{N}$ and
$a \in \mathbb{R}$, it is the $(m+1) \times (m+1)$ matrix $\tilde T$ with the entries of
$T_{m+1}$, except the last diagonal entry, which is
$$\tilde\alpha = a + \beta_{m-1}^2 \, ((T_m - a I)^{-1})_{m-1,m-1}.$$
For $m = 0$ it is the $1 \times 1$ matrix $(a)$.

In the indexing of the source this entry is $\tilde\alpha_{k+1} = a + \beta_k^2 e_k^T (T_k - a
I)^{-1} e_k$. The source prints $\beta_{k+1}$ in place of $\beta_k$ in this formula, and the
definition uses $\beta_k$. The last diagonal entry is $a$ plus `Lanczos.radauCorrection`. -/
noncomputable def radauTridiag (A : E →ₗ[𝕜] E) (v : E) (m : ℕ) (a : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = Fin.last m ∧ j = Fin.last m then a + radauCorrection A v m a
    else tridiag A v (m + 1) i j

variable (A : E →ₗ[𝕜] E) (v : E) (m : ℕ) (a : ℝ)

/-- The Gauss–Radau matrix $\tilde T$ is symmetric. -/
theorem radauTridiag_isSymm : (radauTridiag A v m a).IsSymm := by
  refine Matrix.IsSymm.ext_iff.2 fun i j => ?_
  simp only [radauTridiag, Matrix.of_apply]
  by_cases h : i = Fin.last m ∧ j = Fin.last m
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.2, h'.1⟩]
    exact ((tridiag_isSymm A v (m + 1)).apply i j)

/-- The Gauss–Radau matrix $\tilde T$ is Hermitian, that is, real symmetric. -/
theorem radauTridiag_isHermitian : (radauTridiag A v m a).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (radauTridiag_isSymm A v m a)

/-- The Gauss–Radau matrix $\tilde T$ agrees with $T_{m+1}$ in every entry except the last diagonal
entry. -/
theorem radauTridiag_apply_of_ne {i j : Fin (m + 1)} (h : ¬(i = Fin.last m ∧ j = Fin.last m)) :
    radauTridiag A v m a i j = tridiag A v (m + 1) i j := by
  simp only [radauTridiag, Matrix.of_apply, ite_eq_right h]

/-- **The Radau eigenvector** ([golub2013matrix], §10.2.5). If $T_m - a I$ is invertible, then there
is $x \in \mathbb{R}^m$ with
$$\tilde T \begin{bmatrix} x \\ -1 \end{bmatrix} = a \begin{bmatrix} x \\ -1 \end{bmatrix}.$$
The proof takes $x = \beta_{m-1} (T_m - a I)^{-1} e_{m-1}$. -/
theorem radauTridiag_mulVec_snoc (ha : IsUnit (tridiag A v m - a • 1).det) :
    ∃ x : Fin m → ℝ, radauTridiag A v m a *ᵥ (Fin.snoc x (-1) : Fin (m + 1) → ℝ) =
      a • (Fin.snoc x (-1) : Fin (m + 1) → ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨Fin.elim0, ?_⟩
    ext i
    fin_cases i
    simp [radauTridiag, radauCorrection, Matrix.mulVec, dotProduct]
  set T := tridiag A v m
  set R := (T - a • 1)⁻¹
  set β := beta A v (m - 1)
  have hTRm : T * R = 1 + a • R := by
    have h := Matrix.mul_nonsing_inv _ ha
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h
    rw [← h]
    abel
  have hTR : ∀ i k, ∑ l, T i l * R l k = (if i = k then 1 else 0) + a * R i k := by
    intro i k
    have h := congrFun (congrFun hTRm i) k
    rw [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul] at h
    exact h
  refine ⟨fun i => β * R i ⟨m - 1, by omega⟩, ?_⟩
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hrow : ∀ k : Fin m, radauTridiag A v m a (Fin.last m) k.castSucc =
        if (k : ℕ) + 1 = m then beta A v k else 0 := by
      intro k
      rw [radauTridiag_apply_of_ne A v m a fun h => absurd h.2 (Fin.castSucc_ne_last k),
        tridiag_apply]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hll : radauTridiag A v m a (Fin.last m) (Fin.last m) =
        a + β ^ 2 * R ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩ := by
      simp only [radauTridiag, Matrix.of_apply, and_self, ↓reduceIte, radauCorrection, hm,
        ↓reduceDIte]
      rfl
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
      hrow, hll, Pi.smul_apply, smul_eq_mul]
    rw [sum_eq_single ⟨m - 1, by omega⟩]
    · rw [ite_eq_left (by simp; omega)]
      ring
    · intro k _ hk
      rw [ite_eq_right fun h => hk (Fin.ext (by simp; omega)), zero_mul]
    · simp
  · have hcol : radauTridiag A v m a i.castSucc (Fin.last m) =
        if (i : ℕ) + 1 = m then beta A v i else 0 := by
      rw [radauTridiag_apply_of_ne A v m a fun h => absurd h.1 (Fin.castSucc_ne_last i),
        tridiag_apply]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ite_eq_right (by omega)]
      by_cases h : (i : ℕ) + 1 = m
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h, ite_eq_right (by omega)]
    have hin : ∀ k : Fin m, radauTridiag A v m a i.castSucc k.castSucc = T i k := fun k => by
      rw [radauTridiag_apply_of_ne A v m a fun h => absurd h.1 (Fin.castSucc_ne_last i)]
      rfl
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
      hcol, hin, Pi.smul_apply, smul_eq_mul]
    have hs : ∑ k, T i k * (β * R k ⟨m - 1, by omega⟩) =
        β * ((if i = ⟨m - 1, by omega⟩ then 1 else 0) + a * R i ⟨m - 1, by omega⟩) := by
      rw [← hTR, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [hs]
    by_cases h : (i : ℕ) + 1 = m
    · have hi : i = ⟨m - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [ite_eq_left h, ite_eq_left hi, show beta A v i = β by rw [show (i : ℕ) = m - 1 by omega]]
      ring
    · have hi : i ≠ ⟨m - 1, by omega⟩ := fun h' => h (by rw [h']; simp; omega)
      rw [ite_eq_right h, ite_eq_right hi]
      ring

/-- **The prescribed node is an eigenvalue** ([golub2013matrix], §10.2.5). If $T_m - a I$ is
invertible, then $a$ is an eigenvalue of the Gauss–Radau matrix $\tilde T$, with the eigenvector
of `Lanczos.radauTridiag_mulVec_snoc`. -/
theorem radauTridiag_hasEigenvalue (ha : IsUnit (tridiag A v m - a • 1).det) :
    a ∈ spectrum ℝ (radauTridiag A v m a) := by
  obtain ⟨x, hx⟩ := radauTridiag_mulVec_snoc A v m a ha
  rw [spectrum.mem_iff, ← Matrix.mulVec_injective_iff_isUnit]
  intro hinj
  have hz : (Fin.snoc x (-1) : Fin (m + 1) → ℝ) = 0 := hinj (by
    rw [Matrix.mulVec_zero, Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hx, sub_self])
  simpa using congrFun hz (Fin.last m)

/-- **Low moments of the Gauss–Radau matrix** ([golub2013matrix], §10.2.5). For every $j \le 2m$,
$$(\tilde T^j)_{00} = (T_{m+1}^j)_{00}.$$
-/
theorem radau_moment_eq {j : ℕ} (hj : j ≤ 2 * m) :
    ((radauTridiag A v m a) ^ j) 0 0 = ((tridiag A v (m + 1)) ^ j) 0 0 :=
  (Matrix.pow_apply_zero_zero_eq_of_isTridiagonal (tridiag_isTridiagonal A v (m + 1))
    (fun _ _ h => (radauTridiag_apply_of_ne A v m a h).symm) hj).symm

/-- **The Gauss–Radau rule through Lanczos** ([golub2013matrix], §10.2.5). Let $E$ have dimension
$n$, let $A$ be symmetric, let $v \in E$, and let $\dim \mathcal{K}_{m+1}(A, v) = m + 1$, so
that the process has not broken down before step $m + 1$. Let $a \in \mathbb{R}$ with
$T_m - a I$ invertible, and let $(\tilde\theta_j, \tilde s_j)$ be the eigenpairs of $\tilde T$
with orthonormal eigenvectors. Then $a$ is one of the nodes $\tilde\theta_j$, and for every real
polynomial $f$ of degree at most $2m$
$$\int f \, d\mu_v = \|v\|^2 \sum_j \tilde s_{j,0}^2 \, f(\tilde\theta_j).$$
-/
theorem radau_quadrature [FiniteDimensional 𝕜 E] {n : ℕ} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (hmk : Module.finrank 𝕜 (subspace A v (m + 1)) = m + 1)
    (ha : IsUnit (tridiag A v m - a • 1).det) {f : ℝ[X]} (hf : f.natDegree ≤ 2 * m) :
    (∃ j, (radauTridiag_isHermitian A v m a).eigenvalues j = a) ∧
      ∫ x, f.eval x ∂(spectralMeasure hA hn v) =
        ‖v‖ ^ 2 * ∑ j, ((radauTridiag_isHermitian A v m a).eigenvectorBasis j 0) ^ 2 *
          f.eval ((radauTridiag_isHermitian A v m a).eigenvalues j) := by
  refine ⟨by
    have h := radauTridiag_hasEigenvalue A v m a ha
    rw [(radauTridiag_isHermitian A v m a).spectrum_real_eq_range_eigenvalues] at h
    exact h, ?_⟩
  have hmom : aeval (radauTridiag A v m a) f 0 0 = aeval (tridiag A v (m + 1)) f 0 0 := by
    rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_apply, Matrix.sum_apply]
    refine sum_congr rfl fun k hk => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply,
      radau_moment_eq A v m a (by have := mem_range.1 hk; omega)]
  rw [← Matrix.IsHermitian.aeval_apply_self (radauTridiag_isHermitian A v m a) f 0, hmom,
    gauss_quadrature hA hn v (Nat.succ_pos m) hmk (by omega),
    integral_spectralMeasure_compression_eq_sum_tridiag hA v (Nat.succ_pos m) hmk,
    ← Matrix.IsHermitian.aeval_apply_self (tridiag_isHermitian A v (m + 1)) f]
  rfl

end Lanczos

/-! ### Facts about the spectral measure -/

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {A : E →ₗ[𝕜] E}

/-- Every function $f : \mathbb{R} \to \mathbb{R}$ is integrable against the spectral measure
$\mu_v$, which has finite support. -/
theorem integrable_spectralMeasure (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E)
    (f : ℝ → ℝ) : Integrable f (spectralMeasure hA hn v) := by
  rw [spectralMeasure, integrable_finsetSum_measure]
  exact fun i _ => (integrable_dirac (by simp)).smul_measure (by simp)

/-- The spectral measure $\mu_v$ is finite. Its total mass is $\|v\|^2$. -/
instance isFiniteMeasure_spectralMeasure (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (v : E) : IsFiniteMeasure (spectralMeasure hA hn v) := by
  refine ⟨?_⟩
  rw [spectralMeasure, Measure.finsetSum_apply]
  exact ENNReal.sum_lt_top.2 fun i _ => by simp

/-- If every eigenvalue of $A$ lies in $[a, b]$, then the spectral measure $\mu_v$ is carried by
$[a, b]$: $\mu_v(\mathbb{R} \setminus [a, b]) = 0$. -/
theorem spectralMeasure_compl_Icc (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E)
    {a b : ℝ} (hab : ∀ i, hA.eigenvalues hn i ∈ Set.Icc a b) :
    spectralMeasure hA hn v (Set.Icc a b)ᶜ = 0 := by
  rw [spectralMeasure, Measure.finsetSum_apply]
  refine sum_eq_zero fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Icc.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.2 (hab i)), smul_zero]

end Krylov

/-! ### The Lanczos Gauss and Gauss–Radau rules as quadrature rules -/

namespace Lanczos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open Krylov Quadrature

/-- Below the grade the Lanczos matrix is unreduced: $(T_k)_{i, i+1} = \beta_i \neq 0$ for
$i + 1 < k \le \operatorname{grade}(A, v)$. -/
private theorem tridiag_succ_ne_zero {A : E →ₗ[𝕜] E} (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {k : ℕ} (hk : k ≤ grade A v) (i : ℕ)
    (h : i + 1 < k) : tridiag A v k ⟨i, by omega⟩ ⟨i + 1, h⟩ ≠ 0 := by
  rw [tridiag_apply, ite_eq_right (by simp), ite_eq_left (by simp)]
  intro h0
  rw [beta_eq_zero_iff v] at h0
  dsimp only at h0
  omega

/-- For $k \le \operatorname{grade}(A, v)$ the Lanczos matrix $T_k$ is an unreduced upper Hessenberg
matrix. -/
private theorem tridiag_isUnreducedUpperHessenberg {A : E →ₗ[𝕜] E} (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {k : ℕ} (hk : k ≤ grade A v) :
    (tridiag A v k).IsUnreducedUpperHessenberg :=
  Matrix.isUnreducedUpperHessenberg_iff_fin.2 ⟨(tridiag_isTridiagonal A v k).isUpperHessenberg,
    fun i h => by
      rw [(tridiag_isSymm A v k).apply ⟨i, by omega⟩ ⟨i + 1, h⟩]
      exact tridiag_succ_ne_zero v hk i h⟩

/-- The Gauss–Radau matrix $\tilde T$ is tridiagonal. -/
theorem radauTridiag_isTridiagonal (A : E →ₗ[𝕜] E) (v : E) (m : ℕ) (a : ℝ) :
    (radauTridiag A v m a).IsTridiagonal := by
  intro i j h
  have hne : ¬(i = Fin.last m ∧ j = Fin.last m) := by
    rintro ⟨rfl, rfl⟩
    rcases h with ⟨k, h1, h2⟩ | ⟨k, h1, h2⟩ <;> exact absurd (h1.trans h2) (lt_irrefl _)
  rw [radauTridiag_apply_of_ne A v m a hne]
  exact tridiag_isTridiagonal A v (m + 1) i j h

variable [FiniteDimensional 𝕜 E] {n : ℕ} {A : E →ₗ[𝕜] E}

private theorem ne_zero_of_finrank {v : E} {m : ℕ} (hm : 0 < m)
    (hmk : Module.finrank 𝕜 (subspace A v m) = m) : v ≠ 0 := by
  rintro rfl
  have h := finrank_subspace A (0 : E) m
  rw [hmk, grade_zero] at h
  omega

private theorem le_grade_of_finrank {v : E} {m : ℕ}
    (hmk : Module.finrank 𝕜 (subspace A v m) = m) : m ≤ grade A v := by
  have h := finrank_subspace A v m
  rw [hmk] at h
  omega

/-- The $m$-point Lanczos Gauss rule, with nodes $\theta_j$ and weights $\|v\|^2 s_{j,0}^2$, has
distinct nodes, which lie in every interval that contains the eigenvalues of $A$, it has
positive weights, and it is exact to degree $2m - 1$. -/
private theorem gauss_rule (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) {m : ℕ}
    (hm : 0 < m) (hmk : Module.finrank 𝕜 (subspace A v m) = m) {a b : ℝ}
    (hab : ∀ i, hA.eigenvalues hn i ∈ Set.Icc a b) :
    Function.Injective (tridiag_isHermitian A v m).eigenvalues ∧
      (∀ j, (tridiag_isHermitian A v m).eigenvalues j ∈ Set.Icc a b) ∧
      IsExactOnMeasure (spectralMeasure hA hn v)
        (fun j => ‖v‖ ^ 2 * ((tridiag_isHermitian A v m).eigenvectorBasis j ⟨0, hm⟩) ^ 2)
        (tridiag_isHermitian A v m).eigenvalues (2 * m - 1) := by
  set hT := tridiag_isHermitian A v m
  have hmg := le_grade_of_finrank hmk
  have hv := ne_zero_of_finrank hm hmk
  have hU := tridiag_isUnreducedUpperHessenberg v hmg
  have hinj : Function.Injective hT.eigenvalues :=
    hT.eigenvalues_injective_of_isUnreducedUpperHessenberg hU
  have hexact : IsExactOnMeasure (spectralMeasure hA hn v)
      (fun j => ‖v‖ ^ 2 * (hT.eigenvectorBasis j ⟨0, hm⟩) ^ 2) hT.eigenvalues (2 * m - 1) := by
    intro p hp
    have hnat : p.natDegree < 2 * m := by
      have := natDegree_le_of_degree_le hp
      omega
    rw [gauss_quadrature hA hn v hm hmk hnat,
      integral_spectralMeasure_compression_eq_sum_tridiag hA v hm hmk (fun x => p.eval x),
      mul_sum]
    exact sum_congr rfl fun j _ => by ring
  refine ⟨hinj, fun j => ?_, hexact⟩
  have hw : ∀ i, 0 < ‖v‖ ^ 2 * (hT.eigenvectorBasis i ⟨0, hm⟩) ^ 2 := fun i => by
    have h1 : (hT.eigenvectorBasis i) ⟨0, hm⟩ ≠ 0 :=
      hU.apply_zero_ne_zero_of_isSymm (tridiag_isSymm A v m) (hT.mulVec_eigenvectorBasis i)
        (fun h => by
          have h2 := hT.eigenvectorBasis.orthonormal.1 i
          rw [show hT.eigenvectorBasis i = 0 from WithLp.ofLp_injective 2 (by simpa using h),
            norm_zero] at h2
          exact zero_ne_one h2) hm
    exact mul_pos (pow_pos (norm_pos_iff.2 hv) 2) ((even_two.pow_pos_iff two_ne_zero).2 h1)
  refine mem_Icc_of_isExactOnMeasure (spectralMeasure_compl_Icc hA hn v hab)
    (fun p => integrable_spectralMeasure hA hn v _) hexact
    (P := ∏ i ∈ univ.erase j, (X - C (hT.eigenvalues i)) ^ 2) ?_ (fun t _ => ?_) (fun i hij => ?_)
    ?_
  · rw [natDegree_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow 2]
    simp only [natDegree_pow, natDegree_X_sub_C, sum_const, card_erase_of_mem (mem_univ j),
      card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  · rw [eval_prod]
    exact prod_nonneg fun i _ => by simp only [eval_pow]; positivity
  · rw [eval_prod]
    exact prod_eq_zero (mem_erase.2 ⟨hij, mem_univ i⟩) (by simp)
  · refine mul_pos (hw j) ?_
    rw [eval_prod]
    exact prod_pos fun i hi => by
      simp only [eval_pow, eval_sub, eval_X, eval_C]
      exact (even_two.pow_pos_iff two_ne_zero).2 (sub_ne_zero.2 (hinj.ne (mem_erase.1 hi).1.symm))

private theorem zero_eq_mk {m : ℕ} : (0 : Fin (m + 1)) = ⟨0, Nat.succ_pos m⟩ := rfl

/-- The Lanczos Gauss–Radau rule, with nodes $\tilde\theta_j$ and weights
$\|v\|^2 \tilde s_{j,0}^2$, has distinct nodes, which lie in every interval $[a, b]$ that
contains the eigenvalues of $A$, it has $a$ among its nodes, and it is exact to degree $2m$. -/
private theorem radau_rule (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) {m : ℕ}
    (hmk : Module.finrank 𝕜 (subspace A v (m + 1)) = m + 1) {a b : ℝ}
    (ha : IsUnit (tridiag A v m - a • 1).det) (hab : ∀ i, hA.eigenvalues hn i ∈ Set.Icc a b) :
    Function.Injective (radauTridiag_isHermitian A v m a).eigenvalues ∧
      (∀ j, (radauTridiag_isHermitian A v m a).eigenvalues j ∈ Set.Icc a b) ∧
      IsExactOnMeasure (spectralMeasure hA hn v)
        (fun j => ‖v‖ ^ 2 * ((radauTridiag_isHermitian A v m a).eigenvectorBasis j 0) ^ 2)
        (radauTridiag_isHermitian A v m a).eigenvalues (2 * m) ∧
      ∃ i₀, (radauTridiag_isHermitian A v m a).eigenvalues i₀ = a := by
  set hR := radauTridiag_isHermitian A v m a
  set θ := hR.eigenvalues
  have hmg := le_grade_of_finrank hmk
  have hv := ne_zero_of_finrank (Nat.succ_pos m) hmk
  have hsup : ∀ (i : ℕ) (h : i + 1 < m + 1),
      radauTridiag A v m a ⟨i, by omega⟩ ⟨i + 1, h⟩ ≠ 0 := fun i h => by
    rw [radauTridiag_apply_of_ne A v m a fun h' => by
      have := congrArg Fin.val h'.1
      simp at this
      omega]
    exact tridiag_succ_ne_zero v hmg i h
  have hRS : (radauTridiag A v m a).IsSymm := Matrix.isHermitian_iff_isSymm.1 hR
  have hU : (radauTridiag A v m a).IsUnreducedUpperHessenberg :=
    Matrix.isUnreducedUpperHessenberg_iff_fin.2
      ⟨(radauTridiag_isTridiagonal A v m a).isUpperHessenberg, fun i h => by
        rw [hRS.apply ⟨i, by omega⟩ ⟨i + 1, h⟩]
        exact hsup i h⟩
  have hinj : Function.Injective θ := hR.eigenvalues_injective_of_isUnreducedUpperHessenberg hU
  have hexact : IsExactOnMeasure (spectralMeasure hA hn v)
      (fun j => ‖v‖ ^ 2 * (hR.eigenvectorBasis j 0) ^ 2) θ (2 * m) := by
    intro p hp
    rw [(radau_quadrature A v m a hA hn hmk ha (natDegree_le_of_degree_le hp)).2, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have hspec := radauTridiag_hasEigenvalue A v m a ha
  rw [hR.spectrum_real_eq_range_eigenvalues] at hspec
  obtain ⟨i₀, hi₀⟩ := hspec
  change θ i₀ = a at hi₀
  have hw : ∀ i, 0 < ‖v‖ ^ 2 * (hR.eigenvectorBasis i 0) ^ 2 := fun i => by
    have h1 : (hR.eigenvectorBasis i) 0 ≠ 0 := by
      rw [zero_eq_mk]
      exact hU.apply_zero_ne_zero_of_isSymm hRS (hR.mulVec_eigenvectorBasis i) (fun h => by
          have h2 := hR.eigenvectorBasis.orthonormal.1 i
          rw [show hR.eigenvectorBasis i = 0 from WithLp.ofLp_injective 2 (by simpa using h),
            norm_zero] at h2
          exact zero_ne_one h2) (Nat.succ_pos m)
    exact mul_pos (pow_pos (norm_pos_iff.2 hv) 2) ((even_two.pow_pos_iff two_ne_zero).2 h1)
  have hsupp := spectralMeasure_compl_Icc hA hn v hab
  have hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) (spectralMeasure hA hn v) :=
    fun p => integrable_spectralMeasure hA hn v _
  refine ⟨hinj, fun j => ?_, hexact, i₀, hi₀⟩
  by_cases hj : j = i₀
  · rw [hj, hi₀]
    have : Nontrivial E := ⟨⟨v, 0, hv⟩⟩
    have hn0 : 0 < n := hn ▸ Module.finrank_pos
    exact ⟨le_rfl, (hab ⟨0, hn0⟩).1.trans (hab ⟨0, hn0⟩).2⟩
  set S := (univ.erase j).erase i₀
  set P : ℝ[X] := (X - C a) * ∏ i ∈ S, (X - C (θ i)) ^ 2
  have hPeval : ∀ t, P.eval t = (t - a) * ∏ i ∈ S, (t - θ i) ^ 2 := fun t => by
    simp [P, eval_prod]
  have hprod : 0 < ∏ i ∈ S, (θ j - θ i) ^ 2 := prod_pos fun i hi =>
    (even_two.pow_pos_iff two_ne_zero).2 (sub_ne_zero.2 (hinj.ne
      (mem_erase.1 (mem_erase.1 hi).2).1.symm))
  have hPzero : ∀ i, i ≠ j → P.eval (θ i) = 0 := fun i hij => by
    rw [hPeval]
    by_cases hi : i = i₀
    · rw [hi, hi₀, sub_self, zero_mul]
    · rw [prod_eq_zero (mem_erase.2 ⟨hi, mem_erase.2 ⟨hij, mem_univ i⟩⟩) (by simp), mul_zero]
  have hPnonneg : ∀ t ∈ Set.Icc a b, 0 ≤ P.eval t := fun t ht => by
    rw [hPeval]
    exact mul_nonneg (by linarith [ht.1]) (prod_nonneg fun i _ => sq_nonneg _)
  have hPdeg : P.natDegree = 2 * m - 1 := by
    rw [(monic_X_sub_C a).natDegree_mul (monic_prod_of_monic _ _ fun i _ =>
      (monic_X_sub_C _).pow 2), natDegree_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow 2]
    simp only [natDegree_pow, natDegree_X_sub_C, sum_const, smul_eq_mul, S,
      card_erase_of_mem (mem_erase.2 ⟨Ne.symm hj, mem_univ i₀⟩), card_erase_of_mem (mem_univ j),
      card_univ, Fintype.card_fin]
    omega
  have hlow : a < θ j := by
    rcases lt_or_gt_of_ne (hinj.ne hj : θ j ≠ θ i₀) with h | h
    · exfalso
      rw [hi₀] at h
      have hI : ∫ t, P.eval t ∂(spectralMeasure hA hn v) =
          ‖v‖ ^ 2 * (hR.eigenvectorBasis j 0) ^ 2 * P.eval (θ j) := by
        rw [← hexact P (degree_le_of_natDegree_le (by omega))]
        exact sum_eq_single j (fun i _ hij => by rw [hPzero i hij, mul_zero]) (by simp)
      have hnn : 0 ≤ ∫ t, P.eval t ∂(spectralMeasure hA hn v) := by
        refine integral_nonneg_of_ae ?_
        have hae : ∀ᵐ t ∂(spectralMeasure hA hn v), t ∈ Set.Icc a b := by
          rw [MeasureTheory.ae_iff]
          exact hsupp
        filter_upwards [hae] with t ht using hPnonneg t ht
      rw [hI, hPeval] at hnn
      have : (θ j - a) * ∏ i ∈ S, (θ j - θ i) ^ 2 < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hprod
      nlinarith [hw j]
    · rwa [hi₀] at h
  refine mem_Icc_of_isExactOnMeasure hsupp hint hexact (P := P) (by omega) hPnonneg hPzero ?_
  rw [hPeval]
  exact mul_pos (hw j) (mul_pos (by linarith) hprod)

/-- **The Gauss remainder for the spectral measure** ([golub2013matrix], §10.2.2, the remainder
$R_G$). Let $E$ have dimension $n$, let $A$ be symmetric, let $v \in E$, and let $m \ge 1$ with
$\dim \mathcal{K}_m(A, v) = m$. Let $[a, b]$ contain every eigenvalue of $A$, and let $f$ be
$2m$ times continuously differentiable on $\mathbb{R}$. Then there is $\eta \in [a, b]$ with
$$\int f \, d\mu_v - \int f \, d\mu_{A_m, v} = \frac{f^{(2m)}(\eta)}{(2m)!} \int \chi_{T_m}(x)^2
  \, d\mu_v(x),$$
where $\mu_{A_m, v}$ is the spectral measure of the compression of $A$ to $\mathcal{K}_m$, that
is, the $m$-point Gauss rule, and $\chi_{T_m}$ is the characteristic polynomial of $T_m$.

The result is an instance of `Quadrature.exists_error_eq_of_hermite` with every node double. The
nodes, which are the Ritz values, are distinct because $T_m$ is unreduced. -/
theorem exists_gauss_error_eq (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) {m : ℕ}
    (hm : 0 < m) (hmk : Module.finrank 𝕜 (subspace A v m) = m) {a b : ℝ}
    (hab : ∀ i, hA.eigenvalues hn i ∈ Set.Icc a b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * m : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, ∫ x, f x ∂(spectralMeasure hA hn v) -
        ∫ x, f x ∂(spectralMeasure (compression.isSymmetric A (subspace A v m) hA) hmk
          ⟨v, self_mem_subspace A v hm⟩) =
      iteratedDeriv (2 * m) f η / (2 * m).factorial *
        ∫ x, ((tridiag A v m).charpoly.eval x) ^ 2 ∂(spectralMeasure hA hn v) := by
  set hT := tridiag_isHermitian A v m
  obtain ⟨hinj, hmem, hexact⟩ := gauss_rule hA hn v hm hmk hab
  have hN : 2 * m - 1 + 1 = 2 * m := by omega
  obtain ⟨η, hη, heq⟩ := exists_error_eq_of_hermite (spectralMeasure_compl_Icc hA hn v hab) hinj
    hmem (m := fun _ => 1) (N := 2 * m - 1)
    (by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; omega)
    (Or.inl fun t _ => by
      rw [Hermite.eval_nodal]
      exact prod_nonneg fun i _ => by rw [show (1 + 1 : ℕ) = 2 from rfl]; positivity)
    hexact (by rw [hN]; exact hf)
  rw [hN] at heq
  have hnodal : ∀ t, (Hermite.nodal hT.eigenvalues fun _ => 1).eval t =
      ((tridiag A v m).charpoly.eval t) ^ 2 := fun t => by
    rw [Hermite.eval_nodal, hT.charpoly_eq, eval_prod, ← prod_pow]
    simp
  have hG : ∫ x, f x ∂(spectralMeasure (compression.isSymmetric A (subspace A v m) hA) hmk
      ⟨v, self_mem_subspace A v hm⟩) =
      ∑ j, ‖v‖ ^ 2 * (hT.eigenvectorBasis j ⟨0, hm⟩) ^ 2 * f (hT.eigenvalues j) := by
    rw [integral_spectralMeasure_compression_eq_sum_tridiag hA v hm hmk, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  refine ⟨η, hη, ?_⟩
  rw [hG, integral_congr_ae (Filter.Eventually.of_forall fun t => (hnodal t).symm)]
  exact heq

/-- **The Gauss–Radau remainder for the spectral measure** ([golub2013matrix], §10.2.2, the
remainder $R_{GR(a)}$). Let $E$ have dimension $n$, let $A$ be symmetric, let $v \in E$, and let
$\dim \mathcal{K}_{m+1}(A, v) = m + 1$. Let $[a, b]$ contain every eigenvalue of $A$, let
$T_m - a I$ be invertible, and let $f$ be $2m + 1$ times continuously differentiable on
$\mathbb{R}$. Then there is $\eta \in [a, b]$ with
$$\int f \, d\mu_v - \|v\|^2 \sum_j \tilde s_{j,0}^2 \, f(\tilde\theta_j) =
  \frac{f^{(2m+1)}(\eta)}{(2m+1)!} \int (x - a) \prod_{\tilde\theta_j \neq a} (x -
  \tilde\theta_j)^2 \, d\mu_v(x).$$

The result is an instance of `Quadrature.exists_error_eq_of_hermite` with a simple node at $a$
and double nodes elsewhere. The nodes are distinct because $\tilde T$ is unreduced, and they lie
in $[a, b]$ because the rule is exact to degree $2m$ with positive weights. -/
theorem exists_radau_error_eq (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) {m : ℕ}
    (hmk : Module.finrank 𝕜 (subspace A v (m + 1)) = m + 1) {a b : ℝ}
    (ha : IsUnit (tridiag A v m - a • 1).det) (hab : ∀ i, hA.eigenvalues hn i ∈ Set.Icc a b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((2 * m + 1 : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, ∫ x, f x ∂(spectralMeasure hA hn v) -
        ‖v‖ ^ 2 * ∑ j, ((radauTridiag_isHermitian A v m a).eigenvectorBasis j 0) ^ 2 *
          f ((radauTridiag_isHermitian A v m a).eigenvalues j) =
      iteratedDeriv (2 * m + 1) f η / (2 * m + 1).factorial *
        ∫ x, (x - a) * ∏ j ∈ univ.filter
            (fun j => (radauTridiag_isHermitian A v m a).eigenvalues j ≠ a),
          (x - (radauTridiag_isHermitian A v m a).eigenvalues j) ^ 2
          ∂(spectralMeasure hA hn v) := by
  set hR := radauTridiag_isHermitian A v m a
  set θ := hR.eigenvalues
  obtain ⟨hinj, hmem, hexact, i₀, hi₀⟩ := radau_rule hA hn v hmk ha hab
  change Function.Injective θ at hinj
  change θ i₀ = a at hi₀
  set mult : Fin (m + 1) → ℕ := fun j => if j = i₀ then 0 else 1
  have hm0 : mult i₀ = 0 := ite_eq_left rfl
  have hm1 : ∀ j, j ≠ i₀ → mult j = 1 := fun j hj => ite_eq_right hj
  have hsum : ∑ j, (mult j + 1) = 2 * m + 1 := by
    rw [Fintype.sum_eq_add_sum_compl i₀, hm0,
      sum_congr rfl fun j hj => by rw [hm1 j (by simpa using hj)], sum_const, card_compl,
      card_singleton, Fintype.card_fin, smul_eq_mul]
    omega
  obtain ⟨η, hη, heq⟩ := exists_error_eq_of_hermite (spectralMeasure_compl_Icc hA hn v hab) hinj
    hmem hsum
    (Or.inl fun t ht => by
      rw [Hermite.eval_nodal]
      refine prod_nonneg fun j _ => ?_
      by_cases hj : j = i₀
      · rw [hj, hm0, hi₀, pow_one]
        linarith [ht.1]
      · rw [hm1 j hj]
        exact pow_two_nonneg _)
    hexact hf
  have hfilter : univ.filter (fun j => θ j ≠ a) = {i₀}ᶜ := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_compl, mem_singleton]
    exact ⟨fun h h' => h (by rw [h']; exact hi₀), fun h h' => h (hinj (h'.trans hi₀.symm))⟩
  have hnodal : ∀ t, (Hermite.nodal θ mult).eval t =
      (t - a) * ∏ j ∈ univ.filter (fun j => θ j ≠ a), (t - θ j) ^ 2 := fun t => by
    rw [Hermite.eval_nodal, Fintype.prod_eq_mul_prod_compl i₀, hm0, hi₀, pow_one, hfilter]
    congr 1
    exact prod_congr rfl fun j hj => by rw [hm1 j (by simpa using hj)]
  have hR' : ‖v‖ ^ 2 * ∑ j, (hR.eigenvectorBasis j 0) ^ 2 * f (θ j) =
      ∑ j, ‖v‖ ^ 2 * (hR.eigenvectorBasis j 0) ^ 2 * f (θ j) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  refine ⟨η, hη, ?_⟩
  rw [hR', integral_congr_ae (Filter.Eventually.of_forall fun t => (hnodal t).symm)]
  exact heq

/-- **The two-sided Gauss and Gauss–Radau bound** ([golub2013matrix], §10.2.2 and §10.2.6). Let $E$
have dimension $n$, let $A$ be symmetric, let $v \in E$, and let $m \ge 1$ with
$\dim \mathcal{K}_{m+1}(A, v) = m + 1$. Let $[a, b]$ contain every eigenvalue of $A$, and let
$T_m - a I$ be invertible. Let $f$ be $2m + 1$ times continuously differentiable on an open set
$U \supseteq [a, b]$, with $f^{(2m)} \ge 0$ and $f^{(2m+1)} \le 0$ on $[a, b]$. Then
$$\|v\|^2 \sum_j s_{j,0}^2 \, f(\theta_j) \le \int f \, d\mu_v \le \|v\|^2 \sum_j \tilde
  s_{j,0}^2 \, f(\tilde\theta_j).$$
So the Lanczos Gauss rule is a lower bound and the Lanczos Gauss–Radau rule is an upper bound
for $\int f \, d\mu_v$, which is $v^H f(A) v$ by
`Matrix.IsHermitian.inner_cfc_eq_integral_spectralMeasure`.

The example of the source is $f(\lambda) = \lambda^{-2}$ with $0 < a$. The result is an instance
of the bound `Quadrature.gauss_le_integral_le_gaussRadau` for measures. -/
theorem gauss_le_integral_le_radau (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E)
    {m : ℕ} (hm : 0 < m) (hmk : Module.finrank 𝕜 (subspace A v (m + 1)) = m + 1) {a b : ℝ}
    (ha : IsUnit (tridiag A v m - a • 1).det) (hab : ∀ i, hA.eigenvalues hn i ∈ Set.Icc a b)
    {U : Set ℝ} (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((2 * m + 1 : ℕ) : WithTop ℕ∞) f U)
    (heven : ∀ t ∈ Set.Icc a b, 0 ≤ iteratedDeriv (2 * m) f t)
    (hodd : ∀ t ∈ Set.Icc a b, iteratedDeriv (2 * m + 1) f t ≤ 0) :
    ‖v‖ ^ 2 * ∑ j, ((tridiag_isHermitian A v m).eigenvectorBasis j ⟨0, hm⟩) ^ 2 *
        f ((tridiag_isHermitian A v m).eigenvalues j) ≤ ∫ x, f x ∂(spectralMeasure hA hn v) ∧
      ∫ x, f x ∂(spectralMeasure hA hn v) ≤
        ‖v‖ ^ 2 * ∑ j, ((radauTridiag_isHermitian A v m a).eigenvectorBasis j 0) ^ 2 *
          f ((radauTridiag_isHermitian A v m a).eigenvalues j) := by
  set hR := radauTridiag_isHermitian A v m a
  have hmk' : Module.finrank 𝕜 (subspace A v m) = m := by
    have h := finrank_subspace A v m
    have := le_grade_of_finrank hmk
    omega
  obtain ⟨hinjG, hmemG, hexactG⟩ := gauss_rule hA hn v hm hmk' hab
  obtain ⟨hinjR, hmemR, hexactR, i₀, hi₀⟩ := radau_rule hA hn v hmk ha hab
  set σ := Equiv.swap (0 : Fin (m + 1)) i₀
  have hexactR' : IsExactOnMeasure (spectralMeasure hA hn v)
      ((fun j => ‖v‖ ^ 2 * (hR.eigenvectorBasis j 0) ^ 2) ∘ σ) (hR.eigenvalues ∘ σ) (2 * m) :=
    fun p hp => (Equiv.sum_comp σ fun i => ‖v‖ ^ 2 * (hR.eigenvectorBasis i 0) ^ 2 *
      p.eval (hR.eigenvalues i)).trans (hexactR p hp)
  obtain ⟨h1, h2⟩ := gauss_le_integral_le_gaussRadau (spectralMeasure_compl_Icc hA hn v hab) hm
    hinjG hmemG hexactG (hinjR.comp σ.injective) (fun i => hmemR _)
    (by simp [σ, Equiv.swap_apply_left, hi₀]) hexactR' hU hUsub hf heven hodd
  refine ⟨le_of_eq_of_le ?_ h1, h2.trans_eq ?_⟩
  · rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  · refine (Equiv.sum_comp σ fun i => ‖v‖ ^ 2 * (hR.eigenvectorBasis i 0) ^ 2 *
      f (hR.eigenvalues i)).trans ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring

end Lanczos
