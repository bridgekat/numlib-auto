/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.KrylovEigen
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section10

/-!
# Quarteroni, Sacco and Saleri, Section 5.11: The Lanczos method

This module formalizes Section 5.11 of [quarteroni2000numerical], the Lanczos method for the extreme
eigenvalues of a symmetric matrix $A \in \mathbb{R}^{n \times n}$ with eigenvalues
$\lambda_1 \ge \dots \ge \lambda_n$ (5.66). By the Courant–Fischer theorem, $\lambda_1$ and
$\lambda_n$ are the maximum and the minimum of the Rayleigh quotient $r(x) = x^T A x / x^T x$. The
Lanczos process of Section 4.4.3 builds from a starting vector $q^{(1)}$ the symmetric tridiagonal
matrices $H_m = V_m^T A V_m$, where the columns of $V_m$ are an orthonormal basis of the Krylov
subspace $\mathcal{K}_m(A, q^{(1)})$. The eigenvalues $\eta_1 \ge \dots \ge \eta_m$ of $H_m$ satisfy
$\lambda_n \le \eta_m$ and $\eta_1 \le \lambda_1$ (5.67), and the Kaniel–Paige bound (Property 5.12)
shows that $\eta_1$ approaches $\lambda_1$ at a rate given by a Chebyshev polynomial. The proofs
specialize `Numlib.Eigen.MinMax`, `Numlib.Krylov.Lanczos`, `Numlib.Eigen.RayleighRitz` and
`Numlib.Eigen.KrylovEigen`.

## Main definitions

* Section 5.11, `QuarteroniSaccoSaleri.Chapter05.rayleigh`: the Rayleigh quotient
  $r(x) = x^T A x / x^T x$.
* Section 5.11, `QuarteroniSaccoSaleri.Chapter05.lanczosTridiag`: the Lanczos matrices $H_m$.
* Section 5.11, `QuarteroniSaccoSaleri.Chapter05.lanczosEigenvalues`: the eigenvalues
  $\eta_1 \ge \dots \ge \eta_m$ of $H_m$.

## Main results

* Section 5.11, `QuarteroniSaccoSaleri.Chapter05.rayleigh_eq_rayleighQuotient`: $r(x)$ is the
  backbone's Rayleigh quotient.
* Section 5.11, `QuarteroniSaccoSaleri.Chapter05.courantFischer`: $\lambda_1 = \max_{x \neq 0} r(x)$
  and $\lambda_n = \min_{x \neq 0} r(x)$.
* Section 5.11, `QuarteroniSaccoSaleri.Chapter05.lanczosTridiag_apply` and
  `QuarteroniSaccoSaleri.Chapter05.lanczosEigenvalues_eq`: $(H_m)_{ij} = v_i^T A v_j$, and before
  breakdown the eigenvalues of $H_m$ are the Ritz values.
* Equation (5.67), `QuarteroniSaccoSaleri.Chapter05.equation_5_67`:
  $\eta_1 = \max_{\mathcal{K}_m} r \le \lambda_1$ and
  $\eta_m = \min_{\mathcal{K}_m} r \ge \lambda_n$.
* Property 5.12, `QuarteroniSaccoSaleri.Chapter05.property_5_12`: the Kaniel–Paige bound
  $\lambda_1 - \eta_1 \le (\lambda_1 - \lambda_n) \tan^2\phi_1 / T_{m-1}(1 + 2\rho_1)^2$.
* Display after Property 5.12, `QuarteroniSaccoSaleri.Chapter05.property_5_12_min`: the
  corresponding bound for $\eta_m - \lambda_n$.

## Conventions

* The symmetric matrix $A$ is `A : Matrix (Fin n) (Fin n) ℝ` with `hA : A.IsSymm`, acting on
  `EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanLin`.
* The eigenvalues $\lambda_1 \ge \dots \ge \lambda_n$ are `hA.isSymmetric_toEuclideanLin.eigenvalues
  finrank_euclideanSpace_fin`, indexed from $0$, so $\lambda_i$ is the value at $i - 1$. The
  orthonormal eigenvectors $u_i$ are `hA.isSymmetric_toEuclideanLin.eigenvectorBasis
  finrank_euclideanSpace_fin (i - 1)`.
* The Lanczos vectors $v_i$ are `Arnoldi.vec (toEuclideanLin A) q₁ i`, and the Krylov subspace
  $\mathcal{K}_m(A, q^{(1)})$ is `Krylov.subspace (toEuclideanLin A) q₁ m`. "Before breakdown" means
  $\dim \mathcal{K}_m(A, q^{(1)}) = m$.

## Deviations from the source

* **Totalization.** The Rayleigh quotient is totalized at the zero vector. See
  `QuarteroniSaccoSaleri.Chapter05.rayleigh`.
* **Totalization.** The Lanczos and Ritz arrays are defined beyond breakdown, with a full-prefix
  requirement for the compression interpretation. See
  `QuarteroniSaccoSaleri.Chapter05.lanczosTridiag`,
  `QuarteroniSaccoSaleri.Chapter05.lanczosTridiag_apply`,
  `QuarteroniSaccoSaleri.Chapter05.lanczosEigenvalues`.
* **Reading.** The Ritz extrema use the Krylov trial space and its projected dimension. See
  `QuarteroniSaccoSaleri.Chapter05.equation_5_67`.
* **Scope.** The extremal Ritz bounds make their angle, spectral gaps and full-rank prefix
  hypotheses explicit. See `QuarteroniSaccoSaleri.Chapter05.property_5_12`,
  `QuarteroniSaccoSaleri.Chapter05.property_5_12_min`.

## Not formalized

* **Example 5.18.** It is numerical.
* **Program 45.**
* **The remarks on reorthogonalization.** They are prose.
-/

open Filter Finset Matrix Polynomial Topology Krylov

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### The Rayleigh quotient and the Courant–Fischer theorem -/

/-- **Section 5.11** of [quarteroni2000numerical]. For $A \in \mathbb{R}^{n \times n}$ and
$x \in \mathbb{R}^n$, $x \neq 0$, the **Rayleigh quotient** is $$r(x) = \frac{x^T A x}{x^T x}.$$

The Lean definition gives $r(0) = 0$, by the convention that division by zero gives zero.

**Reading.** The quotient is defined on the zero vector by total division. Its variational
interpretation uses only nonzero vectors.
-/
noncomputable def rayleigh (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ (A *ᵥ x)) / (x ⬝ᵥ x)

/-- For $A \in \mathbb{R}^{n \times n}$ and $x \in \mathbb{R}^n$, the Rayleigh quotient $r(x)$ of
Section 5.11 of [quarteroni2000numerical] is the backbone's `LinearMap.rayleighQuotient` of
`Matrix.toEuclideanLin A` at $x$, because $\langle Ax, x \rangle = x^T A x$ and
$\|x\|^2 = x^T x$. -/
theorem rayleigh_eq_rayleighQuotient (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    rayleigh A (WithLp.ofLp x) = (toEuclideanLin A).rayleighQuotient x := by
  rw [LinearMap.rayleighQuotient, rayleigh, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    ofLp_toEuclideanLin]
  simp

/-- **Section 5.11** of [quarteroni2000numerical] (Courant–Fischer theorem). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $n \ge 1$, and let its eigenvalues be ordered
as in (5.66), $\lambda_1 \ge \dots \ge \lambda_n$. Then $$\lambda_1 = \max_{x \neq 0} r(x),
\qquad \lambda_n = \min_{x \neq 0} r(x),$$ and both extrema are attained.

Here $n = N + 1$. The proof uses `LinearMap.IsSymmetric.rayleighQuotient_mem_Icc` for the bounds
and `LinearMap.IsSymmetric.rayleighQuotient_eigenvectorBasis` for their attainment. -/
theorem courantFischer {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hA : A.IsSymm) :
    IsGreatest {c | ∃ x : Fin (N + 1) → ℝ, x ≠ 0 ∧ c = rayleigh A x}
        ((hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin 0) ∧
      IsLeast {c | ∃ x : Fin (N + 1) → ℝ, x ≠ 0 ∧ c = rayleigh A x}
        ((hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin (Fin.last N)) := by
  set hA' := hA.isSymmetric_toEuclideanLin
  have hne : ∀ x : Fin (N + 1) → ℝ, x ≠ 0 →
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (N + 1))) ≠ 0 :=
    fun x hx h => hx (by simpa using congrArg WithLp.ofLp h)
  have hmem : ∀ i, hA'.eigenvalues finrank_euclideanSpace_fin i ∈
      {c | ∃ x : Fin (N + 1) → ℝ, x ≠ 0 ∧ c = rayleigh A x} := fun i =>
    ⟨WithLp.ofLp (hA'.eigenvectorBasis finrank_euclideanSpace_fin i),
      fun h => hA'.eigenvectorBasis_ne_zero finrank_euclideanSpace_fin i (by
        simpa using congrArg (WithLp.toLp 2) h),
      by rw [rayleigh_eq_rayleighQuotient, hA'.rayleighQuotient_eigenvectorBasis]⟩
  refine ⟨⟨hmem 0, ?_⟩, ⟨hmem (Fin.last N), ?_⟩⟩
  · rintro c ⟨x, hx, rfl⟩
    have h := hA'.rayleighQuotient_mem_Icc finrank_euclideanSpace_fin (hne x hx)
    rw [← rayleigh_eq_rayleighQuotient] at h
    exact h.2
  · rintro c ⟨x, hx, rfl⟩
    have h := hA'.rayleighQuotient_mem_Icc finrank_euclideanSpace_fin (hne x hx)
    rw [← rayleigh_eq_rayleighQuotient] at h
    exact h.1

/-! ### The Lanczos matrices -/

/-- **Section 5.11** of [quarteroni2000numerical], the Lanczos matrices. For
$A \in \mathbb{R}^{n \times n}$, a starting vector $q^{(1)} \in \mathbb{R}^n$ and
$m \in \mathbb{N}$, the matrix $H_m = V_m^T A V_m \in \mathbb{R}^{m \times m}$ of Section 4.4.3
is the symmetric tridiagonal matrix of the coefficients $\alpha_j$, $\beta_j$ of the Lanczos
recurrence.

This is the backbone's `Lanczos.tridiag`.

**Reading.** The arrays are defined for any matrix and step count using padded recurrence data. The
intended symmetric compression interpretation requires symmetry, and the eigenvalue comparison
requires a full-rank Krylov prefix.
-/
noncomputable def lanczosTridiag (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Lanczos.tridiag (toEuclideanLin A) q₁ m

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, and let $q^{(1)} \in \mathbb{R}^n$. Then the
Lanczos matrix $H_m = V_m^T A V_m$ of Section 5.11 of [quarteroni2000numerical] has the entries
$$(H_m)_{ij} = v_i^T A v_j,$$ where $v_i$ are the Lanczos vectors.

The Lanczos vectors are `Arnoldi.vec (toEuclideanLin A) q₁ i`. The proof specializes
`Lanczos.hessenbergSq_eq_map_tridiag`.

**Reading.** The arrays are defined for any matrix and step count using padded recurrence data. The
intended symmetric compression interpretation requires symmetry, and the eigenvalue comparison
requires a full-rank Krylov prefix.
-/
theorem lanczosTridiag_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {m : ℕ} (i j : Fin m) :
    lanczosTridiag A q₁ m i j = inner ℝ (Arnoldi.vec (toEuclideanLin A) q₁ i)
      (toEuclideanLin A (Arnoldi.vec (toEuclideanLin A) q₁ j)) := by
  have h := congrFun (congrFun (Lanczos.hessenbergSq_eq_map_tridiag q₁
    hA.isSymmetric_toEuclideanLin m) i) j
  rw [Arnoldi.hessenbergSq, Matrix.of_apply, Matrix.map_apply, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  exact h.symm

/-- **Section 5.11** of [quarteroni2000numerical]. For $A \in \mathbb{R}^{n \times n}$ and a
starting vector $q^{(1)}$, the eigenvalues $\eta_1 \ge \eta_2 \ge \dots \ge \eta_m$ of the
Lanczos matrix $H_m$, sorted decreasingly.

This is the backbone's list of Ritz values `Lanczos.ritzValues`, indexed by `Fin m` from $0$.

**Reading.** The arrays are defined for any matrix and step count using padded recurrence data. The
intended symmetric compression interpretation requires symmetry, and the eigenvalue comparison
requires a full-rank Krylov prefix.
-/
noncomputable def lanczosEigenvalues (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (m : ℕ) : Fin m → ℝ :=
  Lanczos.ritzValues (toEuclideanLin A) q₁ m

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $q^{(1)} \in \mathbb{R}^n$, and assume
that the Lanczos process has not broken down: $\dim \mathcal{K}_m(A, q^{(1)}) = m$. Then the
sorted eigenvalues of $H_m$ are the sorted eigenvalues of the compression of $A$ to the Krylov
subspace $\mathcal{K}_m(A, q^{(1)})$, that is, the Ritz values. This supports Section 5.11 of
[quarteroni2000numerical].

The proof specializes `Lanczos.ritzValues_eq_eigenvalues_compression`. -/
theorem lanczosEigenvalues_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {m : ℕ}
    (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m) :
    lanczosEigenvalues A q₁ m =
      (compression.isSymmetric (toEuclideanLin A) (Krylov.subspace (toEuclideanLin A) q₁ m)
        hA.isSymmetric_toEuclideanLin).eigenvalues hm :=
  Lanczos.ritzValues_eq_eigenvalues_compression q₁ hA.isSymmetric_toEuclideanLin hm

/-- If the Krylov subspace $\mathcal{K}_m(A, q^{(1)})$ of a matrix $A \in \mathbb{R}^{n \times n}$
has dimension $m$, then $m \le n$. This is needed for the indices in (5.67) of
[quarteroni2000numerical]. -/
theorem le_of_finrank_krylov_eq (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    {m : ℕ} (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m) : m ≤ n :=
  hm ▸ (Submodule.finrank_le _).trans_eq finrank_euclideanSpace_fin

/-- **Equation (5.67)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, let $q^{(1)} \in \mathbb{R}^n$, and let $m \ge 1$ with
$\dim \mathcal{K}_m(A, q^{(1)}) = m$ (no breakdown). Then the eigenvalues
$\eta_1 \ge \dots \ge \eta_m$ of $H_m$ satisfy $$\eta_1 = \max_{y \in \mathcal{K}_m,\, y \neq 0}
r(y) \le \lambda_1(A), \qquad \eta_m = \min_{y \in \mathcal{K}_m,\, y \neq 0} r(y) \ge
\lambda_n(A),$$ and both extrema are attained. So at each step the extreme eigenvalues of $H_m$
are a lower bound for $\lambda_1(A)$ and an upper bound for $\lambda_n(A)$.

The source writes $y = V_m x$ with $x \in \mathbb{R}^m$, $x \neq 0$; the Lean statement takes
$y$ in the Krylov subspace directly. The proof uses `Krylov.rayleighQuotient_compression` with
`LinearMap.IsSymmetric.rayleighQuotient_mem_Icc` and
`LinearMap.IsSymmetric.rayleighQuotient_eigenvectorBasis` for the compression, and the Cauchy
interlacing results `LinearMap.IsSymmetric.eigenvalues_compression_le` and
`LinearMap.IsSymmetric.eigenvalues_le_eigenvalues_compression` for the bounds.

**Reading.** The variational extrema range over the nonzero vectors in the full-rank Krylov
subspace, equivalently over coordinates in the projected dimension. The printed display writes
ambient-dimensional coordinates in the projected quotient.
-/
theorem equation_5_67 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {m : ℕ} (hm0 : 0 < m)
    (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m) :
    IsGreatest {c | ∃ y ∈ Krylov.subspace (toEuclideanLin A) q₁ m, y ≠ 0 ∧
        c = rayleigh A (WithLp.ofLp y)} (lanczosEigenvalues A q₁ m ⟨0, hm0⟩) ∧
      lanczosEigenvalues A q₁ m ⟨0, hm0⟩ ≤
        (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
          ⟨0, lt_of_lt_of_le hm0 (le_of_finrank_krylov_eq A q₁ hm)⟩ ∧
      IsLeast {c | ∃ y ∈ Krylov.subspace (toEuclideanLin A) q₁ m, y ≠ 0 ∧
        c = rayleigh A (WithLp.ofLp y)} (lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩) ∧
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
          ⟨n - 1, by have := le_of_finrank_krylov_eq A q₁ hm; omega⟩ ≤
        lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩ := by
  set hA' := hA.isSymmetric_toEuclideanLin
  set K := Krylov.subspace (toEuclideanLin A) q₁ m with hK
  set hC := compression.isSymmetric (toEuclideanLin A) K hA'
  have hmn : m ≤ n := le_of_finrank_krylov_eq A q₁ hm
  rw [lanczosEigenvalues_eq hA q₁ hm]
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0.ne'
  have hlast : (⟨m' + 1 - 1, by omega⟩ : Fin (m' + 1)) = Fin.last m' := Fin.ext (by simp)
  -- the variational identities
  have hmem : ∀ i, hC.eigenvalues hm i ∈
      {c | ∃ y ∈ K, y ≠ 0 ∧ c = rayleigh A (WithLp.ofLp y)} := fun i =>
    ⟨(hC.eigenvectorBasis hm i : EuclideanSpace ℝ (Fin n)), (hC.eigenvectorBasis hm i).2,
      fun h => hC.eigenvectorBasis_ne_zero hm i (Subtype.ext h),
      by rw [rayleigh_eq_rayleighQuotient, ← rayleighQuotient_compression,
        hC.rayleighQuotient_eigenvectorBasis]⟩
  have hbound : ∀ y ∈ K, y ≠ 0 → rayleigh A (WithLp.ofLp y) ∈
      Set.Icc (hC.eigenvalues hm (Fin.last m')) (hC.eigenvalues hm 0) := fun y hy hy0 => by
    have h := hC.rayleighQuotient_mem_Icc hm (x := ⟨y, hy⟩) fun h => hy0 (congrArg Subtype.val h)
    rw [rayleighQuotient_compression] at h
    rwa [rayleigh_eq_rayleighQuotient]
  refine ⟨⟨hmem 0, ?_⟩, ?_, ?_, ?_⟩
  · rintro c ⟨y, hy, hy0, rfl⟩
    exact (hbound y hy hy0).2
  · exact hA'.eigenvalues_compression_le K finrank_euclideanSpace_fin hm hmn 0
  · rw [hlast]
    refine ⟨hmem (Fin.last m'), ?_⟩
    rintro c ⟨y, hy, hy0, rfl⟩
    exact (hbound y hy hy0).1
  · rw [hlast]
    have h := hA'.eigenvalues_le_eigenvalues_compression K finrank_euclideanSpace_fin hm hmn
      (Fin.last m')
    convert h using 3
    simp
    omega

/-! ### Property 5.12 -/

/-- **Property 5.12** of [quarteroni2000numerical] (Kaniel–Paige bound). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $n \ge 2$, with eigenvalues
$\lambda_1 \ge \dots \ge \lambda_n$ as in (5.66) and orthonormal eigenvectors $u_1, \dots, u_n$,
and assume $\lambda_1 > \lambda_2 > \lambda_n$. Let $q^{(1)} \in \mathbb{R}^n$ be a unit vector
with $(q^{(1)})^T u_1 \neq 0$, let $m \ge 1$ with $\dim \mathcal{K}_m(A, q^{(1)}) = m$, and let
$\eta_1 \ge \dots \ge \eta_m$ be the eigenvalues of $H_m$. Let $\phi_1$ be the angle between
$q^{(1)}$ and $u_1$, let $$\rho_1 = \frac{\lambda_1 - \lambda_2}{\lambda_2 - \lambda_n},$$ and
let $T_{m-1}$ be the Chebyshev polynomial of degree $m - 1$. Then
$\cos\phi_1 = |(q^{(1)})^T u_1|$ and $$\lambda_1 \ge \eta_1 \ge \lambda_1 - \frac{(\lambda_1 -
\lambda_n) \tan^2\phi_1}{T_{m-1}(1 + 2\rho_1)^2}.$$

The hypothesis $\lambda_2 > \lambda_n$ implies $n \ge 3$. It keeps $\rho_1$ finite, and
$(q^{(1)})^T u_1 \neq 0$ keeps $\tan\phi_1$ finite. The angle $\phi_1$ is `Submodule.angle` of
the line through $q^{(1)}$ and $u_1$, and $T_{m-1}$ is `Polynomial.Chebyshev.T ℝ (m - 1)`. The
proof specializes `Lanczos.kaniel_paige_saad` at the first index, where the deflation product is
empty, through `QuarteroniSaccoSaleri.Chapter05.lanczosEigenvalues_eq`, and uses
`Submodule.cosAngle_span_singleton` for $\cos\phi_1$.

**Reading.** Lean assumes explicitly that the required spectral gaps are strict, the initial angle
has nonzero cosine, and the Krylov prefix has full rank. These conditions keep the displayed tangent
and gap quotients defined and make the Ritz interpretation valid.
-/
theorem property_5_12 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hn : 2 ≤ n)
    {q₁ : EuclideanSpace ℝ (Fin n)} (hq₁ : ‖q₁‖ = 1) {m : ℕ} (hm0 : 0 < m)
    (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m)
    (hgap : (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨1, by omega⟩ <
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨0, by omega⟩)
    (hspread : (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
        ⟨n - 1, by omega⟩ <
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨1, by omega⟩)
    (hc : inner ℝ q₁ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin
      ⟨0, by omega⟩) ≠ 0) :
    let lam := (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
    let φ₁ := (ℝ ∙ q₁).angle
      ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin ⟨0, by omega⟩)
    let ρ₁ := (lam ⟨0, by omega⟩ - lam ⟨1, by omega⟩) / (lam ⟨1, by omega⟩ - lam ⟨n - 1, by omega⟩)
    Real.cos φ₁ = |inner ℝ q₁ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis
        finrank_euclideanSpace_fin ⟨0, by omega⟩)| ∧
      lanczosEigenvalues A q₁ m ⟨0, hm0⟩ ≤ lam ⟨0, by omega⟩ ∧
      lam ⟨0, by omega⟩ - (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) * Real.tan φ₁ ^ 2 /
          ((Chebyshev.T ℝ (m - 1 : ℕ)).eval (1 + 2 * ρ₁)) ^ 2 ≤
        lanczosEigenvalues A q₁ m ⟨0, hm0⟩ := by
  intro lam φ₁ ρ₁
  set hA' := hA.isSymmetric_toEuclideanLin
  set u := hA'.eigenvectorBasis finrank_euclideanSpace_fin
  have hq₁0 : q₁ ≠ 0 := by simp [← norm_pos_iff, hq₁]
  have hu0 : u ⟨0, by omega⟩ ≠ 0 := hA'.eigenvectorBasis_ne_zero finrank_euclideanSpace_fin _
  have hcos : Real.cos φ₁ = |inner ℝ q₁ (u ⟨0, by omega⟩)| := by
    rw [Submodule.cos_angle, Submodule.cosAngle_span_singleton hq₁0, hq₁, u.norm_eq_one, mul_one,
      div_one, Real.norm_eq_abs]
  have htan : Real.tan φ₁ = (ℝ ∙ q₁).tanAngle (u ⟨0, by omega⟩) := Submodule.tan_angle _ hu0
  rw [lanczosEigenvalues_eq hA q₁ hm]
  have hkps :=
    Lanczos.kaniel_paige_saad_eigenvectorBasis hA' finrank_euclideanSpace_fin hm ⟨0, hm0⟩
    ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨n - 1, by omega⟩ rfl rfl
    (fun j => Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    (fun j => Fin.le_iff_val_le_val.mpr (by simp; omega))
    (by rwa [real_inner_comm]) hgap hspread
    (fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _))
    (k := m - 1) (by simp; omega)
  have hmin : IsMin (⟨0, hm0⟩ : Fin m) := fun j _ => Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  simp only [Finset.Iio_eq_empty.mpr hmin, Finset.prod_empty, one_mul, Set.mem_Icc,
    div_pow] at hkps
  refine ⟨hcos, by linarith [hkps.1], ?_⟩
  simp only [lam, ρ₁]
  rw [htan, mul_div_assoc]
  linarith [hkps.2]

/-- **Display after Property 5.12** of [quarteroni2000numerical], the smallest eigenvalue. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $n \ge 2$, with eigenvalues
$\lambda_1 \ge \dots \ge \lambda_n$ and orthonormal eigenvectors $u_1, \dots, u_n$, and assume
$\lambda_n < \lambda_{n-1} < \lambda_1$. Let $q^{(1)} \in \mathbb{R}^n$ be a unit vector with
$(q^{(1)})^T u_n \neq 0$, let $m \ge 1$ with $\dim \mathcal{K}_m(A, q^{(1)}) = m$, and let
$\eta_1 \ge \dots \ge \eta_m$ be the eigenvalues of $H_m$. Let $\phi_n$ be the angle between
$q^{(1)}$ and $u_n$, and let $$\rho_n = \frac{\lambda_{n-1} - \lambda_n}{\lambda_1 -
\lambda_{n-1}}.$$ Then $\cos\phi_n = |(q^{(1)})^T u_n|$ and $$\lambda_n \le \eta_m \le
\lambda_n + \frac{(\lambda_1 - \lambda_n) \tan^2\phi_n}{T_{m-1}(1 + 2\rho_n)^2}.$$

The proof applies `QuarteroniSaccoSaleri.Chapter05.property_5_12` to $-A$. The Krylov subspaces
of $A$ and $-A$ are the same (`Krylov.subspace_neg`), the compression is negated
(`compression.neg`), and the sorted eigenvalues are negated and reversed
(`LinearMap.IsSymmetric.eigenvalues_neg`), so the largest Ritz value of $-A$ is $-\eta_m$ and
the largest eigenvalue of $-A$ is $-\lambda_n$. The strict inequalities keep $\rho_n$ finite and
make $\lambda_n$ simple, so the eigenvector of $-A$ for $-\lambda_n$ is $u_n$ up to a scalar
(`LinearMap.IsSymmetric.exists_smul_eigenvectorBasis_neg`); $(q^{(1)})^T u_n \neq 0$ keeps
$\tan\phi_n$ finite.

**Reading.** Lean assumes explicitly that the required spectral gaps are strict, the initial angle
has nonzero cosine, and the Krylov prefix has full rank. These conditions keep the displayed tangent
and gap quotients defined and make the Ritz interpretation valid.
-/
theorem property_5_12_min {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hn : 2 ≤ n)
    {q₁ : EuclideanSpace ℝ (Fin n)} (hq₁ : ‖q₁‖ = 1) {m : ℕ} (hm0 : 0 < m)
    (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m)
    (hgap : (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
        ⟨n - 1, by omega⟩ <
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨n - 2, by omega⟩)
    (hspread : (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
        ⟨n - 2, by omega⟩ <
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨0, by omega⟩)
    (hc : inner ℝ q₁ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin
      ⟨n - 1, by omega⟩) ≠ 0) :
    let lam := (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
    let φₙ := (ℝ ∙ q₁).angle
      ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin
        ⟨n - 1, by omega⟩)
    let ρₙ := (lam ⟨n - 2, by omega⟩ - lam ⟨n - 1, by omega⟩) /
      (lam ⟨0, by omega⟩ - lam ⟨n - 2, by omega⟩)
    Real.cos φₙ = |inner ℝ q₁ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis
        finrank_euclideanSpace_fin ⟨n - 1, by omega⟩)| ∧
      lam ⟨n - 1, by omega⟩ ≤ lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩ ∧
      lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩ ≤
        lam ⟨n - 1, by omega⟩ + (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) * Real.tan φₙ ^ 2 /
          ((Chebyshev.T ℝ (m - 1 : ℕ)).eval (1 + 2 * ρₙ)) ^ 2 := by
  intro lam φₙ ρₙ
  set T := toEuclideanLin A with hTd
  set hT := hA.isSymmetric_toEuclideanLin with hTdef
  set hnE : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
    with hnEdef
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set il : Fin n := ⟨n - 1, by omega⟩ with hil
  set il1 : Fin n := ⟨n - 2, by omega⟩ with hil1
  have hrev0 : (i0.rev : Fin n) = il := by
    apply Fin.ext; simp [Fin.val_rev, hi0, hil]
  have hrev1 : (i1.rev : Fin n) = il1 := by
    apply Fin.ext; simp [Fin.val_rev, hi1, hil1]
  have hrevl : (il.rev : Fin n) = i0 := by
    apply Fin.ext; simp only [Fin.val_rev, hi0, hil]; omega
  -- the eigenvector of `-T` for its largest eigenvalue is a multiple of `u_n`
  have hsimple : ∀ j : Fin n, j ≠ i0.rev →
      hT.eigenvalues hnE j ≠ hT.eigenvalues hnE i0.rev := by
    intro j hj
    rw [hrev0] at hj ⊢
    have hjl : j ≤ il1 := by
      have := j.isLt
      have : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
      exact Fin.le_def.2 (by simp only [hil1]; omega)
    have hanti := hT.eigenvalues_antitone hnE hjl
    intro h
    rw [h] at hanti
    exact absurd hanti (not_le.2 hgap)
  obtain ⟨c, hc0, hcw⟩ := hT.exists_smul_eigenvectorBasis_neg hnE i0 hsimple
  rw [hrev0] at hcw
  -- the Krylov subspace and the compression
  have hmneg : Module.finrank ℝ (Krylov.subspace (-T) q₁ m) = m := by
    rw [Krylov.subspace_neg]; exact hm
  have hkps := Lanczos.kaniel_paige_saad_eigenvectorBasis hT.neg hnE hmneg ⟨0, hm0⟩ i0 i1 i0 il
    rfl (by simp [hi0, hi1]) (fun j => Fin.le_def.2 (Nat.zero_le _))
    (fun j => Fin.le_def.2 (by simp only [hil]; omega))
    (by rw [hcw, real_inner_smul_left]
        exact mul_ne_zero hc0 (fun h => hc (by rw [real_inner_comm]; exact h)))
    (by rw [hT.eigenvalues_neg hnE i0, hT.eigenvalues_neg hnE i1, hrev0, hrev1]; linarith)
    (by rw [hT.eigenvalues_neg hnE i1, hT.eigenvalues_neg hnE il, hrev1, hrevl]; linarith)
    (fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _))
    (k := m - 1) (by simp; omega)
  -- rewrite the three quantities of the conclusion
  have hrevm : ((⟨0, hm0⟩ : Fin m).rev) = ⟨m - 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev])
  have hηm : (compression.isSymmetric (-T) (Krylov.subspace (-T) q₁ m)
      hT.neg).eigenvalues hmneg ⟨0, hm0⟩
      = -lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩ := by
    rw [hT.neg.eigenvalues_compression_congr (Krylov.subspace_neg T q₁ m) hmneg hm,
      LinearMap.IsSymmetric.eigenvalues_congr _
        (compression.isSymmetric T (Krylov.subspace T q₁ m) hT).neg
        (compression.neg T (Krylov.subspace T q₁ m)) hm,
      (compression.isSymmetric T (Krylov.subspace T q₁ m) hT).eigenvalues_neg hm,
      hrevm, lanczosEigenvalues_eq hA q₁ hm]
  rw [hηm, hT.eigenvalues_neg hnE i0, hT.eigenvalues_neg hnE i1, hT.eigenvalues_neg hnE il,
    hrev0, hrev1, hrevl, hcw, Submodule.tanAngle_smul _ hc0] at hkps
  have hmin : IsMin (⟨0, hm0⟩ : Fin m) := fun j _ => Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  simp only [Finset.Iio_eq_empty.mpr hmin, Finset.prod_empty, one_mul, Set.mem_Icc,
    div_pow] at hkps
  have harg : (1 : ℝ) + 2 * ((-hT.eigenvalues hnE il - -hT.eigenvalues hnE il1) /
      (-hT.eigenvalues hnE il1 - -hT.eigenvalues hnE i0))
      = 1 + 2 * ((hT.eigenvalues hnE il1 - hT.eigenvalues hnE il) /
        (hT.eigenvalues hnE i0 - hT.eigenvalues hnE il1)) := by ring
  rw [harg] at hkps
  have hcos : Real.cos φₙ = |inner ℝ q₁ (hT.eigenvectorBasis hnE il)| := by
    rw [Submodule.cos_angle, Submodule.cosAngle_span_singleton (by simp [← norm_pos_iff, hq₁]),
      hq₁, (hT.eigenvectorBasis hnE).norm_eq_one, mul_one, div_one, Real.norm_eq_abs]
  have htan : Real.tan φₙ = (ℝ ∙ q₁).tanAngle (hT.eigenvectorBasis hnE il) :=
    Submodule.tan_angle _ (hT.eigenvectorBasis_ne_zero hnE il)
  refine ⟨hcos, by linarith [hkps.1], ?_⟩
  simp only [lam, ρₙ]
  rw [htan, mul_div_assoc]
  linarith [hkps.2]

end QuarteroniSaccoSaleri.Chapter05
