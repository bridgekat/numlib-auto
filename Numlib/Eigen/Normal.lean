/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.NormalSpectrum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Lagrange
import Numlib.Algebra.Polynomial.Commute
import Numlib.LinearAlgebra.Matrix.Charpoly

/-!
# Normal operators in finite dimension

Let $E$ be a finite-dimensional inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
and let $A \colon E \to E$ be linear with adjoint $A^*$. The operator $A$ is **normal** if
$A^* A = A A^*$. This file proves the spectral theorem for normal operators: over an algebraically
closed field, a normal operator is diagonalizable, its eigenspaces are pairwise orthogonal, they are
the eigenspaces of $A^*$ at the conjugate eigenvalues, and $A^*$ is a polynomial in $A$. The last
statement is the algebraic form of the spectral theorem that the Faber–Manteuffel theory of
short-recurrence Krylov methods needs ([saad2003iterative], §6.10).

The file then gives the matrix forms: a normal matrix is unitarily diagonalizable,
$A = \sum_i \lambda_i u_i u_i^H$ for an orthonormal eigenbasis $(u_i)$, and two commuting normal
matrices are simultaneously unitarily diagonalizable. It also characterizes the matrices $A$ for
which $A^H$ is a polynomial of degree at most one in $A$.

## Main definitions

* `LinearMap.IsStarNormal.eigenvectorBasis`: an orthonormal basis of eigenvectors of a normal
  operator, over an algebraically closed field.
* `LinearMap.IsStarNormal.eigenvalues`: the eigenvalue of a normal operator at each vector of that
  basis.

## Main results

* `LinearMap.IsStarNormal.norm_adjoint_apply`: a normal $A$ satisfies $\|A^* v\| = \|A v\|$, hence
  $\ker A^* = \ker A$ (`LinearMap.IsStarNormal.ker_adjoint_eq_ker`).
* `LinearMap.IsStarNormal.ker_pow`: a normal $N$ satisfies $\ker N^k = \ker N$ for $k \neq 0$.
* `LinearMap.IsStarNormal.maxGenEigenspace_eq_eigenspace`: a normal operator has no generalized
  eigenvectors that are not eigenvectors.
* `LinearMap.IsStarNormal.iSup_eigenspace_eq_top`: over an algebraically closed field, the
  eigenspaces of a normal operator span $E$.
* `LinearMap.IsStarNormal.eigenspace_adjoint`: the eigenspace of $A^*$ at $\bar\mu$ is the
  eigenspace of $A$ at $\mu$.
* `LinearMap.isStarNormal_of_adjoint_apply_eq_smul`: conversely, an operator whose eigenvectors are
  all eigenvectors of its adjoint is normal.
* `LinearMap.IsStarNormal.orthogonalFamily_eigenspaces` and
  `LinearMap.IsStarNormal.direct_sum_isInternal`: the eigenspaces of a normal operator are pairwise
  orthogonal, and over an algebraically closed field they decompose $E$.
* `LinearMap.IsStarNormal.exists_aeval_eq_adjoint`: over an algebraically closed field, $A^* = q(A)$
  for a polynomial $q$; its matrix form is `Matrix.IsStarNormal.exists_aeval_eq_conjTranspose`.
* `Matrix.exists_natDegree_le_one_aeval_eq_conjTranspose_iff`: $A^H = q(A)$ with $\deg q \le 1$ if
  and only if $A = e^{i\theta}(\rho I + B)$ with $\theta, \rho$ real and $B$ skew-Hermitian
  ([saad2003iterative], §6.10).
* `LinearMap.IsSymmetric.exists_orthonormalBasis_eigenvector_of_pairwise_commute`: a finite family
  of pairwise commuting symmetric operators has a common orthonormal eigenbasis.
* `LinearMap.IsStarNormal.exists_orthonormalBasis_eigenvector_of_commute` and
  `Matrix.IsStarNormal.exists_unitary_conj_diagonal_of_commute`: two commuting normal operators have
  a common orthonormal eigenbasis, and two commuting normal matrices are simultaneously unitarily
  diagonalizable ([quarteroni2000numerical], §1.8). The symmetric and Hermitian cases over any field
  $\mathbb{K}$ are `LinearMap.IsSymmetric.exists_orthonormalBasis_eigenvector_of_commute` and
  `Matrix.IsHermitian.exists_unitary_conj_diagonal_of_commute`.
* `Matrix.IsStarNormal.spectral_theorem`: over an algebraically closed field, a matrix is normal if
  and only if it is unitarily similar to a diagonal matrix.
* `Matrix.IsStarNormal.eq_sum_smul_vecMulVec` and `Matrix.IsHermitian.eq_sum_smul_vecMulVec`: a
  normal matrix, and a Hermitian matrix over any field $\mathbb{K}$, is the sum
  $\sum_i \lambda_i u_i u_i^H$ of rank-one projectors onto orthonormal eigenvectors.
* `Matrix.exists_eq_smul_vecMulVec_self_of_rank_le_one`: a real symmetric matrix of rank at most one
  is $\beta x x^T$ for a unit vector $x$.
* `Matrix.abs_dotProduct_mulVec_le`: for a real symmetric $A$ and a unit vector $x$,
  $|x^T A x| \le \max_i |\lambda_i|$.

## Proof outline

The proofs avoid both the Schur triangulation and the Jordan form, neither of which Mathlib has. A
normal $A$ satisfies $\|A^* v\| = \|A v\|$, so $\ker A^* = \ker A$. If $N$ is normal and
$N(Nx) = 0$, then $Nx \in \ker N = \ker N^*$, so $\|Nx\|^2 = \langle N^* N x, x \rangle = 0$; hence
$\ker N^k = \ker N$. A scalar shift $A - \mu I$ of a normal operator is normal, so a normal operator
has no generalized eigenvectors other than eigenvectors. Over an algebraically closed field the
maximal generalized eigenspaces span $E$, so the eigenspaces of a normal operator span $E$: this is
diagonalizability without a triangulation theorem. The same shift argument identifies the
eigenspaces of $A$ and $A^*$. Conversely, if $A$ shares its eigenvectors with $A^*$, the inner
product that forces the eigenvalues to be conjugate also excludes generalized eigenvectors, so $A$
is normal. A polynomial that takes the value $\bar\mu$ at every eigenvalue $\mu$ evaluates to $A^*$,
and Lagrange interpolation gives one.

For two commuting normal operators, each is split into commuting symmetric parts, and Mathlib's
joint eigenbasis of a commuting family of symmetric operators is used. The four parts commute
because the adjoint of a normal operator is a polynomial in it.

## Implementation notes

* Only the statements that need the eigenspaces to span assume `[IsAlgClosed 𝕜]`. Everything else
  holds over $\mathbb{R}$ as well: the norm identity, the kernels, the shift, and the identity of
  the eigenspaces of $A$ and $A^*$.
* Dot notation does not reach these lemmas. They are in the namespaces `LinearMap` and `Matrix`, but
  the hypothesis `IsStarNormal A` is a structure in the root namespace. So a normality hypothesis
  `hA` is passed as `LinearMap.IsStarNormal.ker_adjoint_eq_ker hA` and not as
  `hA.ker_adjoint_eq_ker`. This follows the lemmas `ContinuousLinearMap.IsStarNormal` of Mathlib.
* The adjoint $A^*$ is `LinearMap.adjoint A`, and the conjugate transpose $A^H$ of a matrix is `Aᴴ`.
-/

open Module End Polynomial

open scoped ComplexConjugate

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A N : E →ₗ[𝕜] E}

/-! ### Normality through norms -/

/-- A normal operator $A$ on a finite-dimensional inner product space satisfies
$\|A^* v\| = \|A v\|$ for every vector $v$.

Both sides squared are quadratic forms, $\langle v, A^* A v \rangle$ and
$\langle v, A A^* v \rangle$, and normality says that the two operators are equal. -/
theorem IsStarNormal.norm_adjoint_apply (hA : IsStarNormal A) (v : E) :
    ‖A.adjoint v‖ = ‖A v‖ := by
  have hc : A * A.adjoint = A.adjoint * A := by
    simpa only [star_eq_adjoint] using hA.star_comm_self.eq.symm
  have h : (inner 𝕜 (A.adjoint v) (A.adjoint v) : 𝕜) = inner 𝕜 (A v) (A v) := by
    calc (inner 𝕜 (A.adjoint v) (A.adjoint v) : 𝕜)
        = inner 𝕜 v (A (A.adjoint v)) := LinearMap.adjoint_inner_left A _ v
      _ = inner 𝕜 v (A.adjoint (A v)) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, hc]
      _ = inner 𝕜 (A v) (A v) := LinearMap.adjoint_inner_right A v (A v)
  have h2 : ((‖A.adjoint v‖ : 𝕜)) ^ 2 = ((‖A v‖ : 𝕜)) ^ 2 := by
    rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K]
    exact h
  have h3 : ‖A.adjoint v‖ ^ 2 = ‖A v‖ ^ 2 := by exact_mod_cast h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

/-- For a normal operator $A$ and a vector $x$, $A^* x = 0$ if and only if $A x = 0$. -/
theorem IsStarNormal.adjoint_apply_eq_zero_iff (hA : IsStarNormal A) (x : E) :
    A.adjoint x = 0 ↔ A x = 0 := by
  rw [← norm_eq_zero (a := A.adjoint x), ← norm_eq_zero (a := A x),
    IsStarNormal.norm_adjoint_apply hA]

/-- A normal operator $A$ and its adjoint have the same kernel: $\ker A^* = \ker A$. -/
theorem IsStarNormal.ker_adjoint_eq_ker (hA : IsStarNormal A) : ker A.adjoint = ker A :=
  Submodule.ext fun x => by
    simp only [mem_ker, IsStarNormal.adjoint_apply_eq_zero_iff hA]

/-- If $A$ is normal, then $A - \mu I$ is normal for every scalar $\mu$. -/
theorem IsStarNormal.sub_smul_one (hA : IsStarNormal A) (μ : 𝕜) :
    IsStarNormal (A - μ • (1 : E →ₗ[𝕜] E)) := by
  have hc : ∀ (c : 𝕜) (X : E →ₗ[𝕜] E), Commute (c • (1 : E →ₗ[𝕜] E)) X := by
    intro c X
    have h : Commute (algebraMap 𝕜 (E →ₗ[𝕜] E) c) X := Algebra.commutes c X
    rwa [Algebra.algebraMap_eq_smul_one] at h
  refine ⟨?_⟩
  have hstar : star (A - μ • (1 : E →ₗ[𝕜] E)) = star A - conj μ • (1 : E →ₗ[𝕜] E) := by
    rw [star_sub, star_smul, star_one, starRingEnd_apply]
  rw [hstar]
  exact Commute.sub_left (hA.star_comm_self.sub_right (hc μ (star A)).symm) (hc _ _)

/-- The adjoint of $A - \mu I$ is $A^* - \bar\mu I$. -/
theorem adjoint_sub_smul_one (A : E →ₗ[𝕜] E) (μ : 𝕜) :
    (A - μ • (1 : E →ₗ[𝕜] E)).adjoint = A.adjoint - conj μ • (1 : E →ₗ[𝕜] E) := by
  rw [← star_eq_adjoint, ← star_eq_adjoint, star_sub, star_smul, star_one, starRingEnd_apply]

/-!
### No generalized eigenvectors

The three private lemmas below assume only that $N^* y = 0$ whenever $N y = 0$, that is,
$\ker N \le \ker N^*$. Both a normality hypothesis and a hypothesis of shared eigenvectors give
this.
-/

private theorem apply_eq_zero_of_ker_le {N : E →ₗ[𝕜] E}
    (h : ∀ y : E, N y = 0 → N.adjoint y = 0) {x : E} (hx : N (N x) = 0) : N x = 0 := by
  have h1 : N.adjoint (N x) = 0 := h (N x) hx
  have h2 : (inner 𝕜 (N x) (N x) : 𝕜) = 0 := by
    rw [← LinearMap.adjoint_inner_right N x (N x), h1, inner_zero_right]
  exact inner_self_eq_zero.1 h2

private theorem ker_pow_succ_of_ker_le {N : E →ₗ[𝕜] E}
    (h : ∀ y : E, N y = 0 → N.adjoint y = 0) (j : ℕ) : ker (N ^ (j + 1)) = ker N := by
  induction j with
  | zero => rw [zero_add, pow_one]
  | succ j ih =>
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_ker] at hx ⊢
      have h1 : N x ∈ ker (N ^ (j + 1)) := by
        rw [mem_ker, ← Module.End.mul_apply, ← pow_succ]
        exact hx
      rw [ih, mem_ker] at h1
      exact apply_eq_zero_of_ker_le h h1
    · rw [mem_ker] at hx ⊢
      rw [pow_succ, Module.End.mul_apply, hx, map_zero]

private theorem maxGenEigenspace_eq_eigenspace_of_ker_le {A : E →ₗ[𝕜] E} {μ : 𝕜}
    (h : ∀ y : E, (A - μ • (1 : E →ₗ[𝕜] E)) y = 0 →
      (A - μ • (1 : E →ₗ[𝕜] E)).adjoint y = 0) :
    maxGenEigenspace A μ = eigenspace A μ := by
  refine le_antisymm (fun x hx => ?_) (by simpa using genEigenspace_le_maximal A μ 1)
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace A μ x).1 hx
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [pow_zero, Module.End.one_apply] at hk
    rw [hk]
    exact Submodule.zero_mem _
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hmem : x ∈ ker ((A - μ • (1 : E →ₗ[𝕜] E)) ^ (j + 1)) := hk
    rw [ker_pow_succ_of_ker_le h j, ← eigenspace_def] at hmem
    exact hmem

/-- If $N$ is normal and $N(Nx) = 0$, then $Nx = 0$.

The vector $Nx$ lies in $\ker N = \ker N^*$, so $\|Nx\|^2 = \langle N^*(Nx), x \rangle = 0$. -/
theorem IsStarNormal.apply_eq_zero_of_apply_apply_eq_zero (hN : IsStarNormal N) {x : E}
    (h : N (N x) = 0) : N x = 0 :=
  apply_eq_zero_of_ker_le (fun y hy => (IsStarNormal.adjoint_apply_eq_zero_iff hN y).2 hy) h

/-- If $N$ is normal, then $\ker N^k = \ker N$ for every $k \neq 0$. -/
theorem IsStarNormal.ker_pow (hN : IsStarNormal N) {k : ℕ} (hk : k ≠ 0) :
    ker (N ^ k) = ker N := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact ker_pow_succ_of_ker_le (fun y hy => (IsStarNormal.adjoint_apply_eq_zero_iff hN y).2 hy) j

/-- A normal operator has no generalized eigenvectors other than eigenvectors. Let $A$ be a normal
operator on a finite-dimensional inner product space over $\mathbb{K}$, and let
$\mu \in \mathbb{K}$. Then the maximal generalized eigenspace $\bigcup_k \ker (A - \mu I)^k$ of
$A$ at $\mu$ equals the eigenspace $\ker (A - \mu I)$.

This is `LinearMap.IsStarNormal.ker_pow` for the normal operator $A - \mu I$. -/
theorem IsStarNormal.maxGenEigenspace_eq_eigenspace (hA : IsStarNormal A) (μ : 𝕜) :
    maxGenEigenspace A μ = eigenspace A μ :=
  maxGenEigenspace_eq_eigenspace_of_ker_le fun y hy =>
    (IsStarNormal.adjoint_apply_eq_zero_iff (IsStarNormal.sub_smul_one hA μ) y).2 hy

private theorem iSup_eigenspace_eq_top_of_maxGen [IsAlgClosed 𝕜] {A : E →ₗ[𝕜] E}
    (h : ∀ μ : 𝕜, maxGenEigenspace A μ = eigenspace A μ) : ⨆ μ : 𝕜, eigenspace A μ = ⊤ := by
  simp_rw [← h]
  exact iSup_maxGenEigenspace_eq_top A

omit [FiniteDimensional 𝕜 E] in
/-- Two operators that agree on every eigenspace of an operator whose eigenspaces span the space are
equal. -/
private theorem eq_of_forall_eigenspace {A : E →ₗ[𝕜] E} (hsup : ⨆ μ : 𝕜, eigenspace A μ = ⊤)
    {f g : E →ₗ[𝕜] E} (h : ∀ (μ : 𝕜) (x : E), x ∈ eigenspace A μ → f x = g x) : f = g := by
  have hker : (⨆ μ : 𝕜, eigenspace A μ) ≤ ker (f - g) :=
    iSup_le fun μ x hx => by
      rw [mem_ker, sub_apply, sub_eq_zero]
      exact h μ x hx
  rw [hsup, top_le_iff, ker_eq_top] at hker
  exact sub_eq_zero.1 hker

/-- **A normal operator is diagonalizable.** Let $E$ be a finite-dimensional inner product space
over an algebraically closed field $\mathbb{K}$, and let $A \colon E \to E$ be normal. Then the
eigenspaces of $A$ span $E$:
$$\sum_{\mu \in \mathbb{K}} \ker (A - \mu I) = E.$$

Over such a field the maximal generalized eigenspaces always span $E$, and for a normal operator
they are the eigenspaces. -/
theorem IsStarNormal.iSup_eigenspace_eq_top [IsAlgClosed 𝕜] (hA : IsStarNormal A) :
    ⨆ μ : 𝕜, eigenspace A μ = ⊤ :=
  iSup_eigenspace_eq_top_of_maxGen (IsStarNormal.maxGenEigenspace_eq_eigenspace hA)

/-! ### A normal operator and its adjoint share their eigenvectors -/

/-- **A normal operator and its adjoint have the same eigenvectors**, with conjugate eigenvalues.
Let $A$ be a normal operator on a finite-dimensional inner product space over $\mathbb{K}$, and
let $\mu \in \mathbb{K}$. Then
$$\ker (A^* - \bar\mu I) = \ker (A - \mu I).$$

This is the easy direction of [saad2003iterative], Lemma 1.15. The operator $A - \mu I$ is
normal, and a normal operator has the same kernel as its adjoint. No algebraic closedness is
needed. -/
theorem IsStarNormal.eigenspace_adjoint (hA : IsStarNormal A) (μ : 𝕜) :
    eigenspace A.adjoint (conj μ) = eigenspace A μ := by
  rw [eigenspace_def, eigenspace_def, ← adjoint_sub_smul_one A μ]
  exact IsStarNormal.ker_adjoint_eq_ker (IsStarNormal.sub_smul_one hA μ)

/-- If $Ax = \mu x$ and $A^* x = \nu x$, then $A^* x = \bar\mu x$. -/
private theorem adjoint_apply_eq_conj_smul {A : E →ₗ[𝕜] E} {μ ν : 𝕜} {x : E} (hx : A x = μ • x)
    (hν : A.adjoint x = ν • x) : A.adjoint x = conj μ • x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have h : (inner 𝕜 x (A.adjoint x) : 𝕜) = inner 𝕜 (A x) x := LinearMap.adjoint_inner_right A x x
    rw [hν, hx, inner_smul_right, inner_smul_left] at h
    have hxx : (inner 𝕜 x x : 𝕜) ≠ 0 := fun hc => hx0 (inner_self_eq_zero.1 hc)
    rw [hν, mul_right_cancel₀ hxx h]

/-- **An operator that shares its eigenvectors with its adjoint is normal.** Let $E$ be a
finite-dimensional inner product space over an algebraically closed field $\mathbb{K}$, and let
$A \colon E \to E$ be linear. Assume that for every $\mu \in \mathbb{K}$ and every $x$ with
$Ax = \mu x$ there is a $\nu \in \mathbb{K}$ with $A^* x = \nu x$. Then $A$ is normal.

This is the substantial direction of [saad2003iterative], Lemma 1.15. The identity $\langle x,
A^* x \rangle = \langle Ax, x \rangle$ forces $\nu = \bar\mu$. The same identity applied to
$(A - \mu I) u = x$ forces $\|x\|^2 = 0$, so $A$ has no generalized eigenvectors other than
eigenvectors and is diagonalizable. On each eigenspace both $A^* A$ and $A A^*$ act as
$|\mu|^2$. -/
theorem isStarNormal_of_adjoint_apply_eq_smul [IsAlgClosed 𝕜] {A : E →ₗ[𝕜] E}
    (h : ∀ (μ : 𝕜) (x : E), A x = μ • x → ∃ ν : 𝕜, A.adjoint x = ν • x) : IsStarNormal A := by
  have hconj : ∀ (μ : 𝕜) (x : E), x ∈ eigenspace A μ → A.adjoint x = conj μ • x := by
    intro μ x hx
    obtain ⟨ν, hν⟩ := h μ x (mem_eigenspace_iff.1 hx)
    exact adjoint_apply_eq_conj_smul (mem_eigenspace_iff.1 hx) hν
  have hker : ∀ μ : 𝕜, ∀ y : E, (A - μ • (1 : E →ₗ[𝕜] E)) y = 0 →
      (A - μ • (1 : E →ₗ[𝕜] E)).adjoint y = 0 := by
    intro μ y hy
    have hy' : y ∈ eigenspace A μ := by rwa [eigenspace_def, mem_ker]
    rw [adjoint_sub_smul_one, sub_apply, smul_apply, Module.End.one_apply, hconj μ y hy',
      sub_self]
  have hsup : ⨆ μ : 𝕜, eigenspace A μ = ⊤ :=
    iSup_eigenspace_eq_top_of_maxGen fun μ =>
      maxGenEigenspace_eq_eigenspace_of_ker_le (hker μ)
  refine ⟨?_⟩
  change star A * A = A * star A
  rw [star_eq_adjoint]
  refine eq_of_forall_eigenspace hsup fun μ x hx => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, mem_eigenspace_iff.1 hx, hconj μ x hx,
    map_smul, map_smul, mem_eigenspace_iff.1 hx, hconj μ x hx, smul_smul, smul_smul, mul_comm]

/-! ### The spectral theorem for normal operators -/

/-- **The eigenspaces of a normal operator are mutually orthogonal.** Let $A$ be normal, let
$\mu \neq \nu$, and let $Ax = \mu x$ and $Ay = \nu y$. Then $\langle x, y \rangle = 0$.

The proof computes $\bar\mu \langle x, y \rangle = \langle Ax, y \rangle = \langle x, A^* y
\rangle = \bar\nu \langle x, y \rangle$, since $y$ is an eigenvector of $A^*$ for $\bar\nu$. -/
theorem IsStarNormal.inner_eq_zero_of_ne (hA : IsStarNormal A) {μ ν : 𝕜} (hμν : μ ≠ ν) {x y : E}
    (hx : x ∈ eigenspace A μ) (hy : y ∈ eigenspace A ν) : (inner 𝕜 x y : 𝕜) = 0 := by
  have hy' : A.adjoint y = conj ν • y :=
    mem_eigenspace_iff.1 (by rw [IsStarNormal.eigenspace_adjoint hA ν]; exact hy)
  have hx' : A x = μ • x := mem_eigenspace_iff.1 hx
  have key : conj μ * (inner 𝕜 x y : 𝕜) = conj ν * inner 𝕜 x y := by
    calc conj μ * (inner 𝕜 x y : 𝕜)
        = inner 𝕜 (A x) y := by rw [hx', inner_smul_left]
      _ = inner 𝕜 x (A.adjoint y) := (LinearMap.adjoint_inner_right A x y).symm
      _ = conj ν * inner 𝕜 x y := by rw [hy', inner_smul_right]
  have hne : conj μ - conj ν ≠ 0 :=
    sub_ne_zero.2 fun hc => hμν ((starRingEnd 𝕜).injective hc)
  have hzero : (conj μ - conj ν) * (inner 𝕜 x y : 𝕜) = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left hne

/-- Let $A$ be a normal operator on a finite-dimensional inner product space over $\mathbb{K}$. Then
the eigenspaces $\ker (A - \mu I)$, for $\mu \in \mathbb{K}$, form an orthogonal family of
subspaces.

The family is indexed by all scalars $\mu$, most of which give the zero subspace. -/
theorem IsStarNormal.orthogonalFamily_eigenspaces (hA : IsStarNormal A) :
    OrthogonalFamily 𝕜 (fun μ : 𝕜 => eigenspace A μ) fun μ => (eigenspace A μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨x, hx⟩ ⟨y, hy⟩
  exact IsStarNormal.inner_eq_zero_of_ne hA hμν hx hy

/-- The eigenspaces of a normal operator form an orthogonal family, indexed by the eigenvalues and
not by all scalars. This is the form that `OrthogonalFamily.isInternal_iff` uses. -/
theorem IsStarNormal.orthogonalFamily_eigenspaces' (hA : IsStarNormal A) :
    OrthogonalFamily 𝕜 (fun μ : Eigenvalues A => eigenspace A μ) fun μ =>
      (eigenspace A μ).subtypeₗᵢ :=
  (IsStarNormal.orthogonalFamily_eigenspaces hA).comp Subtype.coe_injective

/-- **The spectral theorem for normal operators.** Let $E$ be a finite-dimensional inner product
space over an algebraically closed field $\mathbb{K}$, and let $A \colon E \to E$ be normal.
Then $E$ is the internal direct sum of the eigenspaces of $A$, one for each eigenvalue of $A$.

By `LinearMap.IsStarNormal.orthogonalFamily_eigenspaces` the decomposition is orthogonal. This
is the counterpart for normal operators of `LinearMap.IsSymmetric.direct_sum_isInternal` for
symmetric operators. -/
theorem IsStarNormal.direct_sum_isInternal [IsAlgClosed 𝕜] (hA : IsStarNormal A) :
    DirectSum.IsInternal fun μ : Eigenvalues A => eigenspace A μ := by
  refine (IsStarNormal.orthogonalFamily_eigenspaces' hA).isInternal_iff.mpr ?_
  change (⨆ μ : { μ : 𝕜 // eigenspace A μ ≠ ⊥ }, eigenspace A μ)ᗮ = ⊥
  rw [iSup_ne_bot_subtype, IsStarNormal.iSup_eigenspace_eq_top hA,
    Submodule.top_orthogonal_eq_bot]

/-! ### The adjoint of a normal operator is a polynomial in it -/

/-- Let $E$ be a finite-dimensional inner product space over an algebraically closed field
$\mathbb{K}$, and let $A \colon E \to E$ be normal. If a polynomial $q \in \mathbb{K}[X]$
satisfies $q(\mu) = \bar\mu$ at every eigenvalue $\mu$ of $A$, then $q(A) = A^*$.

Both operators act as $\bar\mu$ on the eigenspace at $\mu$, and the eigenspaces span $E$. -/
theorem IsStarNormal.aeval_eq_adjoint_of_eval_eq [IsAlgClosed 𝕜] (hA : IsStarNormal A) {q : 𝕜[X]}
    (hq : ∀ μ : 𝕜, HasEigenvalue A μ → q.eval μ = conj μ) : aeval A q = A.adjoint := by
  refine eq_of_forall_eigenspace (IsStarNormal.iSup_eigenspace_eq_top hA) fun μ x hx => ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have h2 : A.adjoint x = conj μ • x :=
      mem_eigenspace_iff.1 (by rw [IsStarNormal.eigenspace_adjoint hA μ]; exact hx)
    rw [aeval_apply_of_mem_apply_eq_smul (mem_eigenspace_iff.1 hx), h2,
      hq μ (hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩)]

/-- **The adjoint of a normal operator is a polynomial in it.** Let $E$ be a finite-dimensional
inner product space over an algebraically closed field $\mathbb{K}$, and let $A \colon E \to E$
be normal. Then there is a polynomial $q \in \mathbb{K}[X]$ with $q(A) = A^*$.

The polynomial $q$ interpolates $z \mapsto \bar z$ at the finitely many eigenvalues, and
`LinearMap.IsStarNormal.aeval_eq_adjoint_of_eval_eq` applies. No bound on the degree is stated,
because a user can reduce any such $q$ modulo an annihilating polynomial of $A$. -/
theorem IsStarNormal.exists_aeval_eq_adjoint [IsAlgClosed 𝕜] (hA : IsStarNormal A) :
    ∃ q : 𝕜[X], aeval A q = A.adjoint := by
  classical
  obtain ⟨s, hsmem⟩ : ∃ s : Finset 𝕜, ∀ μ : 𝕜, HasEigenvalue A μ → μ ∈ s :=
    ⟨(finite_hasEigenvalue A).toFinset, fun _ h => (Set.Finite.mem_toFinset _).2 h⟩
  obtain ⟨q, hq⟩ : ∃ q : 𝕜[X], ∀ μ ∈ s, q.eval μ = conj μ :=
    ⟨Lagrange.interpolate (ι := 𝕜) (F := 𝕜) s _root_.id (fun z => conj z),
      fun _ hμ => Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hμ⟩
  exact ⟨q, IsStarNormal.aeval_eq_adjoint_of_eval_eq hA fun μ hμ => hq μ (hsmem μ hμ)⟩

/-! ### The orthonormal eigenbasis of a normal operator -/

section EigenvectorBasis

variable {n : ℕ} [IsAlgClosed 𝕜]

/-- **An orthonormal basis of eigenvectors of a normal operator.** Let $E$ be an inner product space
of dimension $n$ over an algebraically closed field $\mathbb{K}$, and let $A \colon E \to E$ be
normal. This is an orthonormal basis $(u_0, \dots, u_{n-1})$ of $E$ in which each $u_i$ is an
eigenvector of $A$.

The eigenspaces are mutually orthogonal and decompose $E$
(`LinearMap.IsStarNormal.direct_sum_isInternal`), so orthonormal bases of the eigenspaces
together give an orthonormal basis of $E$, subordinate to the decomposition. This is the
counterpart for normal operators of `LinearMap.IsSymmetric.eigenvectorBasis`. Unlike there, the
eigenvalues need not be real, so `LinearMap.IsStarNormal.eigenvalues` takes values in
$\mathbb{K}$, and the basis is in no particular order. -/
noncomputable def IsStarNormal.eigenvectorBasis (hA : IsStarNormal A)
    (hn : Module.finrank 𝕜 E = n) : OrthonormalBasis (Fin n) 𝕜 E :=
  (IsStarNormal.direct_sum_isInternal hA).subordinateOrthonormalBasis hn
    (IsStarNormal.orthogonalFamily_eigenspaces' hA)

/-- The eigenvalue $\lambda_i \in \mathbb{K}$ of a normal operator at the $i$-th vector $u_i$ of the
orthonormal eigenbasis `LinearMap.IsStarNormal.eigenvectorBasis`, for $i < n$. -/
noncomputable def IsStarNormal.eigenvalues (hA : IsStarNormal A) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : 𝕜 :=
  (((IsStarNormal.direct_sum_isInternal hA).subordinateOrthonormalBasisIndex hn i
    (IsStarNormal.orthogonalFamily_eigenspaces' hA) : Eigenvalues A) : 𝕜)

/-- Let $E$ be an inner product space of dimension $n$ over an algebraically closed field, and let
$A \colon E \to E$ be normal. Then the vectors of `LinearMap.IsStarNormal.eigenvectorBasis` are
eigenvectors of $A$, with the eigenvalues `LinearMap.IsStarNormal.eigenvalues`:
$A u_i = \lambda_i u_i$ for every $i < n$. -/
theorem IsStarNormal.apply_eigenvectorBasis (hA : IsStarNormal A) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) :
    A (IsStarNormal.eigenvectorBasis hA hn i) =
      IsStarNormal.eigenvalues hA hn i • IsStarNormal.eigenvectorBasis hA hn i :=
  mem_eigenspace_iff.1
    ((IsStarNormal.direct_sum_isInternal hA).subordinateOrthonormalBasis_subordinate hn i
      (IsStarNormal.orthogonalFamily_eigenspaces' hA))

end EigenvectorBasis

/-! ### Commuting symmetric operators -/

/-- **A commuting finite family of symmetric operators has a common orthonormal eigenbasis.** Let
$E$ be an inner product space of dimension $n$ over $\mathbb{K}$, let $\iota$ be a finite type,
and let $(T_j)_{j \in \iota}$ be symmetric operators on $E$ that commute pairwise. Then there
are an orthonormal basis $(b_0, \dots, b_{n-1})$ of $E$ and scalars $d_{a j} \in \mathbb{K}$
with
$$T_j b_a = d_{a j} \, b_a \quad \text{for all } a < n \text{ and } j \in \iota.$$

The joint eigenspaces $\bigcap_j \ker (T_j - \alpha_j I)$ are mutually orthogonal and span $E$
(`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`). Only finitely many of them are nonzero,
and an orthonormal basis subordinate to the nonzero ones consists of joint eigenvectors. -/
theorem IsSymmetric.exists_orthonormalBasis_eigenvector_of_pairwise_commute {ι : Type*}
    [Finite ι] {T : ι → E →ₗ[𝕜] E} (hT : ∀ i, (T i).IsSymmetric)
    (hC : Pairwise (Function.onFun Commute T)) {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
    ∃ (b : OrthonormalBasis (Fin n) 𝕜 E) (d : Fin n → ι → 𝕜), ∀ a j, T j (b a) = d a j • b a := by
  classical
  set V : (ι → 𝕜) → Submodule 𝕜 E := fun α => ⨅ j, eigenspace (T j) (α j) with hVdef
  have hVfam := IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have htop : ⨆ α, V α = ⊤ := IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have hfin : {α | V α ≠ ⊥}.Finite := by
    refine (Set.Finite.pi fun j => finite_hasEigenvalue (T j)).subset fun α hα => ?_
    refine Set.mem_univ_pi.mpr fun j => hasEigenvalue_iff.mpr fun hbot => hα ?_
    exact le_bot_iff.mp ((iInf_le _ j).trans hbot.le)
  let _ : Fintype {α // V α ≠ ⊥} := hfin.fintype
  have hVfam' : OrthogonalFamily 𝕜 (fun α : {α // V α ≠ ⊥} => V α)
      fun α => (V α).subtypeₗᵢ := hVfam.comp Subtype.coe_injective
  have hV : DirectSum.IsInternal fun α : {α // V α ≠ ⊥} => V α := by
    refine hVfam'.isInternal_iff.mpr ?_
    rw [iSup_ne_bot_subtype, htop, Submodule.top_orthogonal_eq_bot]
  exact ⟨hV.subordinateOrthonormalBasis hn hVfam',
    fun a => (hV.subordinateOrthonormalBasisIndex hn a hVfam').val, fun a j =>
      mem_eigenspace_iff.mp
        ((Submodule.mem_iInf _).mp (hV.subordinateOrthonormalBasis_subordinate hn a hVfam') j)⟩

/-- **Two commuting symmetric operators have a common orthonormal eigenbasis.** Let $E$ be an inner
product space of dimension $m$ over $\mathbb{K}$, and let $S, T \colon E \to E$ be symmetric
with $ST = TS$. Then there are an orthonormal basis $(b_0, \dots, b_{m-1})$ of $E$ and scalars
$d_a, e_a \in \mathbb{K}$ with $S b_a = d_a b_a$ and $T b_a = e_a b_a$ for all $a < m$.

This is the case of a pair in
`LinearMap.IsSymmetric.exists_orthonormalBasis_eigenvector_of_pairwise_commute`. The field
$\mathbb{K}$ can be $\mathbb{R}$ or $\mathbb{C}$. -/
theorem IsSymmetric.exists_orthonormalBasis_eigenvector_of_commute {S T : E →ₗ[𝕜] E}
    (hS : S.IsSymmetric) (hT : T.IsSymmetric) (hST : Commute S T) {m : ℕ}
    (hm : Module.finrank 𝕜 E = m) :
    ∃ (b : OrthonormalBasis (Fin m) 𝕜 E) (d e : Fin m → 𝕜),
      (∀ a, S (b a) = d a • b a) ∧ ∀ a, T (b a) = e a • b a := by
  have hF : ∀ i, (![S, T] i).IsSymmetric := by
    intro i
    fin_cases i
    · exact hS
    · exact hT
  have hFcomm : Pairwise (Function.onFun Commute ![S, T]) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Function.onFun] <;>
      first | exact absurd rfl hij | exact hST | exact hST.symm
  obtain ⟨b, d, hd⟩ := exists_orthonormalBasis_eigenvector_of_pairwise_commute hF hFcomm hm
  exact ⟨b, fun a => d a 0, fun a => d a 1, fun a => hd a 0, fun a => hd a 1⟩

/-! ### Commuting normal operators -/

/-- If the field $\mathbb{K}$ (which is $\mathbb{R}$ or $\mathbb{C}$) is algebraically closed, then
its imaginary unit $i$ is nonzero.

The number $-1$ is a square in $\mathbb{K}$, and if $i = 0$ then every scalar is real. -/
theorem _root_.RCLike.I_ne_zero_of_isAlgClosed [IsAlgClosed 𝕜] : (RCLike.I : 𝕜) ≠ 0 := by
  intro hI
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : 𝕜) two_pos
  have hzr := RCLike.re_add_im z
  rw [hI, mul_zero, add_zero] at hzr
  rw [← hzr, ← RCLike.ofReal_pow] at hz
  have h : (RCLike.re z) ^ 2 = -1 := by exact_mod_cast hz
  nlinarith [sq_nonneg (RCLike.re z)]

/-- The Hermitian part $H(X) = (X + X^*)/2$ of an operator $X$. -/
private noncomputable def hermPart (X : E →ₗ[𝕜] E) : E →ₗ[𝕜] E := (2⁻¹ : 𝕜) • (X + X.adjoint)

/-- The operator $S(X) = (X - X^*)/(2i)$, which is symmetric and satisfies $X = H(X) + i S(X)$. -/
private noncomputable def skewPart (X : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (2 * RCLike.I : 𝕜)⁻¹ • (X - X.adjoint)

private theorem hermPart_isSymmetric (X : E →ₗ[𝕜] E) : (hermPart X).IsSymmetric := by
  intro x y
  simp only [hermPart, smul_apply, add_apply, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, adjoint_inner_left, adjoint_inner_right, map_inv₀, RCLike.conj_ofNat]
  ring

private theorem skewPart_isSymmetric (X : E →ₗ[𝕜] E) : (skewPart X).IsSymmetric := by
  intro x y
  simp only [skewPart, smul_apply, sub_apply, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, adjoint_inner_left, adjoint_inner_right, map_inv₀, map_mul, RCLike.conj_ofNat,
    RCLike.conj_I]
  rw [mul_neg, inv_neg]
  ring

private theorem hermPart_add_I_smul_skewPart (hI : (RCLike.I : 𝕜) ≠ 0) (X : E →ₗ[𝕜] E) :
    hermPart X + (RCLike.I : 𝕜) • skewPart X = X := by
  rw [hermPart, skewPart, smul_smul, mul_inv, ← mul_assoc, mul_comm (RCLike.I : 𝕜),
    mul_assoc, mul_inv_cancel₀ hI, mul_one, ← smul_add,
    show X + X.adjoint + (X - X.adjoint) = (2 : 𝕜) • X by module, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

private theorem commute_parts {X Y : E →ₗ[𝕜] E} (h₁ : Commute X Y) (h₂ : Commute X Y.adjoint)
    (h₃ : Commute X.adjoint Y) (h₄ : Commute X.adjoint Y.adjoint) :
    Commute (hermPart X) (hermPart Y) ∧ Commute (hermPart X) (skewPart Y) ∧
      Commute (skewPart X) (hermPart Y) ∧ Commute (skewPart X) (skewPart Y) := by
  simp only [hermPart, skewPart]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine Commute.smul_left (Commute.smul_right ?_ _) _
  · exact (h₁.add_right h₂).add_left (h₃.add_right h₄)
  · exact (h₁.sub_right h₂).add_left (h₃.sub_right h₄)
  · exact (h₁.add_right h₂).sub_left (h₃.add_right h₄)
  · exact (h₁.sub_right h₂).sub_left (h₃.sub_right h₄)

/-- **Commuting normal operators have a common orthonormal eigenbasis.** Let $E$ be an inner product
space of dimension $n$ over an algebraically closed field $\mathbb{K}$, and let
$A, B \colon E \to E$ be normal with $AB = BA$. Then there are an orthonormal basis
$(b_0, \dots, b_{n-1})$ of $E$ and scalars $d_i, e_i \in \mathbb{K}$ with $A b_i = d_i b_i$ and
$B b_i = e_i b_i$ for all $i < n$.

This is the finite-dimensional case of the spectral theorem for commuting normal operators; see
[quarteroni2000numerical], §1.8.

The proof uses no restriction to eigenspaces. Write $X = H(X) + i S(X)$ with
$H(X) = (X + X^*)/2$ and $S(X) = (X - X^*)/(2i)$, both symmetric. All four of $A, A^*, B, B^*$
commute: $A$ with $A^*$ by normality, $A$ with $B$ by hypothesis, $A$ with $B^*$ because
$B^* = q(B)$ is a polynomial in $B$ (`LinearMap.IsStarNormal.exists_aeval_eq_adjoint`), and the
others by taking adjoints. So the four symmetric parts commute pairwise, and their joint
orthonormal eigenbasis
(`LinearMap.IsSymmetric.exists_orthonormalBasis_eigenvector_of_pairwise_commute`) is the claimed
basis. -/
theorem IsStarNormal.exists_orthonormalBasis_eigenvector_of_commute [IsAlgClosed 𝕜]
    {A B : E →ₗ[𝕜] E} (hA : IsStarNormal A) (hB : IsStarNormal B) (hAB : Commute A B) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) :
    ∃ (b : OrthonormalBasis (Fin n) 𝕜 E) (d e : Fin n → 𝕜),
      (∀ i, A (b i) = d i • b i) ∧ ∀ i, B (b i) = e i • b i := by
  classical
  have hI : (RCLike.I : 𝕜) ≠ 0 := RCLike.I_ne_zero_of_isAlgClosed
  -- the four operators commute pairwise
  obtain ⟨qA, hqA⟩ := IsStarNormal.exists_aeval_eq_adjoint hA
  obtain ⟨qB, hqB⟩ := IsStarNormal.exists_aeval_eq_adjoint hB
  have hAA' : Commute A A.adjoint := by
    have := hA.star_comm_self.symm
    rwa [star_eq_adjoint] at this
  have hBB' : Commute B B.adjoint := by
    have := hB.star_comm_self.symm
    rwa [star_eq_adjoint] at this
  have hAB' : Commute A B.adjoint := by
    have := hAB.aeval_right qB
    rwa [hqB] at this
  have hA'B : Commute A.adjoint B := by
    have := hAB.symm.aeval_right qA
    rw [hqA] at this
    exact this.symm
  have hA'B' : Commute A.adjoint B.adjoint := by
    have h := congrArg LinearMap.adjoint hAB.eq
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, adjoint_comp, adjoint_comp] at h
    exact h.symm
  obtain ⟨-, cAA₂, -, -⟩ := commute_parts (Commute.refl A) hAA' hAA'.symm (Commute.refl _)
  obtain ⟨cAB₁, cAB₂, cAB₃, cAB₄⟩ := commute_parts hAB hAB' hA'B hA'B'
  obtain ⟨-, cBB₂, -, -⟩ := commute_parts (Commute.refl B) hBB' hBB'.symm (Commute.refl _)
  -- the commuting family of symmetric parts
  set T : Fin 4 → E →ₗ[𝕜] E := ![hermPart A, skewPart A, hermPart B, skewPart B] with hT
  have hTsymm : ∀ i, (T i).IsSymmetric := by
    intro i
    fin_cases i
    · exact hermPart_isSymmetric A
    · exact skewPart_isSymmetric A
    · exact hermPart_isSymmetric B
    · exact skewPart_isSymmetric B
  have cAA₂' := cAA₂.symm
  have cAB₁' := cAB₁.symm
  have cAB₂' := cAB₂.symm
  have cAB₃' := cAB₃.symm
  have cAB₄' := cAB₄.symm
  have cBB₂' := cBB₂.symm
  have hTcomm : Pairwise (Function.onFun Commute T) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [hT, Function.onFun] <;>
      first | exact absurd rfl hij | assumption
  obtain ⟨b, idx, hmem⟩ :=
    IsSymmetric.exists_orthonormalBasis_eigenvector_of_pairwise_commute hTsymm hTcomm hn
  refine ⟨b, fun a => idx a 0 + RCLike.I * idx a 1, fun a => idx a 2 + RCLike.I * idx a 3,
    fun a => ?_, fun a => ?_⟩
  · have h0 := hmem a 0
    have h1 := hmem a 1
    simp only [hT, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [← hermPart_add_I_smul_skewPart hI A, add_apply, smul_apply, h0, h1, smul_smul, add_smul]
  · have h2 := hmem a 2
    have h3 := hmem a 3
    simp only [hT, Matrix.cons_val] at h2 h3
    rw [← hermPart_add_I_smul_skewPart hI B, add_apply, smul_apply, h2, h3, smul_smul, add_smul]

end LinearMap

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

private theorem toEuclideanLin_mul' (X Y : Matrix n n 𝕜) :
    toEuclideanLin (X * Y) = toEuclideanLin X * toEuclideanLin Y :=
  map_mul (toLpLinAlgEquiv (R := 𝕜) (n := n) 2) X Y

private theorem star_toEuclideanLin (A : Matrix n n 𝕜) :
    star (toEuclideanLin A) = toEuclideanLin (star A) := by
  rw [LinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- A square matrix $A$ over $\mathbb{K}$ is normal if and only if the operator
`Matrix.toEuclideanLin A` that it defines on Euclidean space is normal.

The map `Matrix.toEuclideanLin` is an algebra equivalence that takes the conjugate transpose to
the adjoint. -/
theorem isStarNormal_toEuclideanLin_iff {A : Matrix n n 𝕜} :
    IsStarNormal (toEuclideanLin A) ↔ IsStarNormal A := by
  constructor
  · intro h
    refine ⟨?_⟩
    refine toEuclideanLin.injective ?_
    rw [toEuclideanLin_mul', toEuclideanLin_mul', ← star_toEuclideanLin]
    exact h.star_comm_self.eq
  · intro h
    refine ⟨?_⟩
    rw [star_toEuclideanLin]
    exact h.star_comm_self.map (toLpLinAlgEquiv (R := 𝕜) (n := n) 2)

/-- For a square matrix $A$ over $\mathbb{K}$ and a polynomial $q$, $q(A) = A^H$ if and only if
$q(L) = L^*$ for the operator $L$ = `Matrix.toEuclideanLin A` on Euclidean space. -/
theorem aeval_eq_conjTranspose_iff {A : Matrix n n 𝕜} {q : 𝕜[X]} :
    aeval (toEuclideanLin A) q = LinearMap.adjoint (toEuclideanLin A) ↔ aeval A q = Aᴴ := by
  have halg : aeval (toEuclideanLin A) q = toEuclideanLin (aeval A q) :=
    aeval_algHom_apply (toLpLinAlgEquiv (R := 𝕜) (n := n) 2) A q
  rw [halg, ← toEuclideanLin_conjTranspose_eq_adjoint]
  exact toEuclideanLin.injective.eq_iff

/-- **The conjugate transpose of a normal matrix is a polynomial in the matrix.** Let $A$ be a
normal square matrix over an algebraically closed field $\mathbb{K}$. Then there is a polynomial
$q \in \mathbb{K}[X]$ with $q(A) = A^H$.

This is `LinearMap.IsStarNormal.exists_aeval_eq_adjoint`, transported along the algebra
equivalence between matrices and operators on Euclidean space, which takes the conjugate
transpose to the adjoint. -/
theorem IsStarNormal.exists_aeval_eq_conjTranspose [IsAlgClosed 𝕜] {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) : ∃ q : 𝕜[X], aeval A q = Aᴴ := by
  obtain ⟨q, hq⟩ :=
    LinearMap.IsStarNormal.exists_aeval_eq_adjoint (isStarNormal_toEuclideanLin_iff.2 hA)
  exact ⟨q, aeval_eq_conjTranspose_iff.1 hq⟩

omit [DecidableEq n] in
/-- A normal matrix over an algebraically closed field has an orthonormal basis of eigenvectors,
indexed by the index type of the matrix. -/
private theorem exists_orthonormalBasis_eigenvector [IsAlgClosed 𝕜] {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) :
    ∃ (c : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) (d : n → 𝕜),
      ∀ j, A *ᵥ ⇑(c j) = d j • ⇑(c j) := by
  classical
  have hT : IsStarNormal (toEuclideanLin A) := isStarNormal_toEuclideanLin_iff.2 hA
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  refine ⟨(LinearMap.IsStarNormal.eigenvectorBasis hT finrank_euclideanSpace).reindex e,
    fun j => LinearMap.IsStarNormal.eigenvalues hT finrank_euclideanSpace (e.symm j),
    fun j => ?_⟩
  have h := LinearMap.IsStarNormal.apply_eigenvectorBasis hT finrank_euclideanSpace (e.symm j)
  rw [OrthonormalBasis.reindex_apply]
  simpa [toLpLin_apply] using congrArg WithLp.ofLp h

/-- Let $A$ be a square matrix over $\mathbb{K}$, and let $(c_j)$ be an orthonormal basis of
Euclidean space with $A c_j = d_j c_j$ for all $j$. Let $U$ be the matrix whose $j$-th column is
$c_j$, that is, the change-of-basis matrix from the standard basis to $(c_j)$. Then
$$U^H A U = \operatorname{diag}(d).$$

This is the step from an eigenbasis to a unitary diagonalization. The spectral theorem for one
normal matrix and the one for a commuting pair both use it. -/
theorem conjTranspose_toMatrix_mul_mul_toMatrix_eq_diagonal
    (c : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) {A : Matrix n n 𝕜} {d : n → 𝕜}
    (hcd : ∀ j, A *ᵥ ⇑(c j) = d j • ⇑(c j)) :
    ((EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix c.toBasis)ᴴ * A
      * (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix c.toBasis = diagonal d := by
  set U : Matrix n n 𝕜 := (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix c.toBasis with hU
  have hUmem : U ∈ Matrix.unitaryGroup n 𝕜 :=
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary c
  have hentry : ∀ i j, U i j = ⇑(c j) i := fun _ _ => rfl
  have hAU : A * U = U * diagonal d := by
    ext i j
    have h1 : (A *ᵥ ⇑(c j)) i = d j * ⇑(c j) i := by rw [hcd j]; rfl
    calc (A * U) i j = (A *ᵥ ⇑(c j)) i := by
          rw [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hentry k j]
      _ = d j * ⇑(c j) i := h1
      _ = U i j * d j := by rw [hentry i j, mul_comm]
      _ = (U * diagonal d) i j := (Matrix.mul_diagonal _ _ _ _).symm
  rw [Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    (Unitary.mem_iff.1 hUmem).1, Matrix.one_mul]

/-- **The spectral theorem for normal matrices.** Let $A$ be a square matrix over an algebraically
closed field $\mathbb{K}$. Then $A$ is normal if and only if there are a unitary matrix $U$ and
a vector $d$ with
$$U^H A U = \operatorname{diag}(d).$$

This is [saad2003iterative], Theorem 1.14. For the forward direction, the matrix $U$ has the
orthonormal eigenbasis `LinearMap.IsStarNormal.eigenvectorBasis` as its columns. Conversely, a
diagonal matrix commutes with its conjugate transpose, and conjugation by a unitary matrix is a
$\star$-automorphism (`Unitary.conjStarAlgAut`), which preserves normality. This is the
counterpart for normal matrices of `Matrix.IsHermitian.spectral_theorem` for Hermitian matrices. -/
theorem IsStarNormal.spectral_theorem [IsAlgClosed 𝕜] {A : Matrix n n 𝕜} :
    IsStarNormal A ↔
      ∃ U ∈ Matrix.unitaryGroup n 𝕜, ∃ d : n → 𝕜, Uᴴ * A * U = Matrix.diagonal d := by
  constructor
  · intro hA
    obtain ⟨c, d, hcd⟩ := exists_orthonormalBasis_eigenvector hA
    exact ⟨_, (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary c, d,
      conjTranspose_toMatrix_mul_mul_toMatrix_eq_diagonal c hcd⟩
  · rintro ⟨U, hUmem, d, hd⟩
    have hdiag : IsStarNormal (Matrix.diagonal d) := ⟨by
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Commute, SemiconjBy,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)⟩
    -- `A = U diag(d) Uᴴ` is the image of a normal matrix under a `⋆`-automorphism
    have hA : A = Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) ⟨U, hUmem⟩ (Matrix.diagonal d) := by
      change A = U * Matrix.diagonal d * star U
      rw [← hd, ← Matrix.star_eq_conjTranspose]
      simp only [← Matrix.mul_assoc, (Unitary.mem_iff.1 hUmem).2, Matrix.one_mul]
      rw [Matrix.mul_assoc, (Unitary.mem_iff.1 hUmem).2, Matrix.mul_one]
    rw [hA]
    exact hdiag.map _

/-- An orthonormal basis of joint eigenvectors of the operators of $A$ and $B$ on Euclidean space
gives a unitary $U$ with $U^H A U$ and $U^H B U$ both diagonal. -/
private theorem exists_unitary_conj_diagonal_of_orthonormalBasis {A B : Matrix n n 𝕜}
    (b : OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n))
    {d e : Fin (Fintype.card n) → 𝕜} (hd : ∀ a, toEuclideanLin A (b a) = d a • b a)
    (he : ∀ a, toEuclideanLin B (b a) = e a • b a) :
    ∃ U ∈ unitaryGroup n 𝕜, ∃ d e : n → 𝕜,
      star U * A * U = diagonal d ∧ star U * B * U = diagonal e := by
  set eq : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with heq
  set c := b.reindex eq with hc
  refine ⟨_, (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary c,
    fun j => d (eq.symm j), fun j => e (eq.symm j), ?_, ?_⟩
  · rw [star_eq_conjTranspose]
    refine conjTranspose_toMatrix_mul_mul_toMatrix_eq_diagonal c fun j => ?_
    have h := hd (eq.symm j)
    rw [hc, OrthonormalBasis.reindex_apply]
    simpa [toLpLin_apply] using congrArg WithLp.ofLp h
  · rw [star_eq_conjTranspose]
    refine conjTranspose_toMatrix_mul_mul_toMatrix_eq_diagonal c fun j => ?_
    have h := he (eq.symm j)
    rw [hc, OrthonormalBasis.reindex_apply]
    simpa [toLpLin_apply] using congrArg WithLp.ofLp h

/-- **Commuting normal matrices are simultaneously unitarily diagonalizable.** Let $A$ and $B$ be
normal square matrices over an algebraically closed field $\mathbb{K}$ with $AB = BA$. Then
there are a unitary matrix $U$ and vectors $d$, $e$ with
$$U^H A U = \operatorname{diag}(d), \qquad U^H B U = \operatorname{diag}(e).$$

This is the third consequence of the Schur decomposition in [quarteroni2000numerical], §1.8. It
follows that $U^H (A + B) U = \operatorname{diag}(d + e)$, so the eigenvalues of $A + B$ are the
sums $d_i + e_i$ of eigenvalues of $A$ and $B$, with the $i$-th column of $U$ as a common
eigenvector. This is the matrix form of
`LinearMap.IsStarNormal.exists_orthonormalBasis_eigenvector_of_commute`. -/
theorem IsStarNormal.exists_unitary_conj_diagonal_of_commute [IsAlgClosed 𝕜] {A B : Matrix n n 𝕜}
    (hA : IsStarNormal A) (hB : IsStarNormal B) (hAB : Commute A B) :
    ∃ U ∈ unitaryGroup n 𝕜, ∃ d e : n → 𝕜,
      star U * A * U = diagonal d ∧ star U * B * U = diagonal e := by
  obtain ⟨b, d, e, hd, he⟩ :=
    LinearMap.IsStarNormal.exists_orthonormalBasis_eigenvector_of_commute
      (isStarNormal_toEuclideanLin_iff.2 hA) (isStarNormal_toEuclideanLin_iff.2 hB)
      (hAB.map (toLpLinAlgEquiv (R := 𝕜) (n := n) 2)) finrank_euclideanSpace
  exact exists_unitary_conj_diagonal_of_orthonormalBasis b hd he

/-- **Commuting Hermitian matrices are simultaneously unitarily diagonalizable.** Let $A$ and $B$ be
Hermitian square matrices over $\mathbb{K}$ with $AB = BA$. Then there are a unitary matrix $U$
and vectors $d$, $e$ with $U^H A U = \operatorname{diag}(d)$ and
$U^H B U = \operatorname{diag}(e)$.

This is the matrix form of
`LinearMap.IsSymmetric.exists_orthonormalBasis_eigenvector_of_commute`. It holds over
$\mathbb{R}$ as well as over $\mathbb{C}$. It is the Hermitian case of
`Matrix.IsStarNormal.exists_unitary_conj_diagonal_of_commute`, which needs an algebraically
closed field for general normal matrices. -/
theorem IsHermitian.exists_unitary_conj_diagonal_of_commute {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ U ∈ unitaryGroup n 𝕜, ∃ d e : n → 𝕜,
      star U * A * U = diagonal d ∧ star U * B * U = diagonal e := by
  obtain ⟨b, d, e, hd, he⟩ :=
    (isSymmetric_toEuclideanLin_iff.mpr hA).exists_orthonormalBasis_eigenvector_of_commute
      (isSymmetric_toEuclideanLin_iff.mpr hB) (hAB.map (toLpLinAlgEquiv (R := 𝕜) (n := n) 2))
      finrank_euclideanSpace
  exact exists_unitary_conj_diagonal_of_orthonormalBasis b hd he

/-- Let $U$ be a unitary matrix over $\mathbb{K}$ with columns $u_i$, and let $A$ be a square matrix
with $U^H A U = \operatorname{diag}(d)$. Then $A$ is the sum of rank-one projectors
$$A = \sum_i d_i \, u_i u_i^H.$$

This is the display after Property 1.5 in [quarteroni2000numerical], §1.8. The column $u_i$ is
`Uᵀ i`, and $u_i u_i^H$ is `Matrix.vecMulVec (Uᵀ i) (star (Uᵀ i))`. -/
theorem eq_sum_smul_vecMulVec_of_conj_eq_diagonal {U A : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) {d : n → 𝕜} (hd : star U * A * U = diagonal d) :
    A = ∑ i, d i • vecMulVec (Uᵀ i) (star (Uᵀ i)) := by
  have hstar' : U * star U = 1 := (Unitary.mem_iff.1 hU).2
  have hA : A = U * diagonal d * star U := by
    rw [← hd]
    calc A = U * star U * A * (U * star U) := by rw [hstar', Matrix.one_mul, Matrix.mul_one]
      _ = U * (star U * A * U) * star U := by simp only [Matrix.mul_assoc]
  rw [hA]
  ext i j
  rw [Matrix.sum_apply, Matrix.mul_apply]
  simp only [mul_diagonal, Matrix.smul_apply, vecMulVec_apply, transpose_apply, Pi.star_apply,
    star_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The spectral decomposition of a normal matrix** as a sum of rank-one projectors. Let $A$ be a
normal square matrix over an algebraically closed field $\mathbb{K}$. Then there are a unitary
matrix $U$ with columns $u_i$ and a vector $d$ with
$$U^H A U = \operatorname{diag}(d), \qquad A = \sum_i d_i \, u_i u_i^H.$$

This is the second consequence of the Schur decomposition in [quarteroni2000numerical], §1.8,
$A = U \Lambda U^H$. The matrix $U$ is the one of `Matrix.IsStarNormal.spectral_theorem`, and
its columns $u_i$ = `Uᵀ i` form an orthonormal eigenbasis. -/
theorem IsStarNormal.eq_sum_smul_vecMulVec [IsAlgClosed 𝕜] {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) :
    ∃ U ∈ unitaryGroup n 𝕜, ∃ d : n → 𝕜, star U * A * U = diagonal d ∧
      A = ∑ i, d i • vecMulVec (Uᵀ i) (star (Uᵀ i)) := by
  obtain ⟨U, hU, d, hd⟩ := IsStarNormal.spectral_theorem.mp hA
  rw [← star_eq_conjTranspose] at hd
  exact ⟨U, hU, d, hd, eq_sum_smul_vecMulVec_of_conj_eq_diagonal hU hd⟩

/-! ### The Hermitian spectral decomposition -/

/-- Let $d \in \mathbb{R}^n$ be such that the diagonal matrix $\operatorname{diag}(d)$ over
$\mathbb{K}$ is Hermitian. Then the eigenvalues of $\operatorname{diag}(d)$, counted with
multiplicity, are the entries $d_i$, as multisets. -/
theorem IsHermitian.map_eigenvalues_diagonal {d : n → ℝ}
    (hD : (diagonal fun i => (d i : 𝕜)).IsHermitian) :
    Multiset.map hD.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
  have h := hD.roots_charpoly_eq_eigenvalues
  rw [roots_charpoly_diagonal] at h
  refine Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜)) ?_
  simpa only [Multiset.map_map, Function.comp_def] using h.symm

/-! ### Hermitian matrices as sums of rank-one projectors -/

/-- **The spectral decomposition of a Hermitian matrix** as a sum of rank-one projectors onto its
orthonormal eigenvectors. Let $A$ be a Hermitian matrix over $\mathbb{K}$ with eigenvalues
$\lambda_l$ and orthonormal eigenvectors $q_l$. Then
$$A = \sum_l \lambda_l \, q_l q_l^H.$$

This is the Hermitian counterpart of `Matrix.IsStarNormal.eq_sum_smul_vecMulVec`, and it holds
over $\mathbb{R}$ as well as $\mathbb{C}$. The eigenvectors are Mathlib's
`Matrix.IsHermitian.eigenvectorBasis` and the real eigenvalues are
`Matrix.IsHermitian.eigenvalues`. -/
theorem IsHermitian.eq_sum_smul_vecMulVec {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = ∑ l, (hA.eigenvalues l : 𝕜) •
      vecMulVec ⇑(hA.eigenvectorBasis l) (star ⇑(hA.eigenvectorBasis l)) :=
  eq_sum_smul_vecMulVec_of_conj_eq_diagonal hA.eigenvectorUnitary.2
    hA.star_eigenvectorUnitary_mul_mul

/-- The eigenvectors $q_l$ of a Hermitian matrix in `Matrix.IsHermitian.eigenvectorBasis` are unit
vectors: $q_l^H q_l = 1$. -/
theorem IsHermitian.star_dotProduct_eigenvectorBasis_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (l : n) : star ⇑(hA.eigenvectorBasis l) ⬝ᵥ ⇑(hA.eigenvectorBasis l) = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    hA.eigenvectorBasis.orthonormal.1 l]
  simp

omit [DecidableEq n] in
/-- Let $Z$ be a real symmetric $n \times n$ matrix with $n \ge 1$ and
$\operatorname{rank} Z \le 1$. Then there are $\beta \in \mathbb{R}$ and $x \in \mathbb{R}^n$
with $x^T x = 1$ and $Z = \beta \, x x^T$. -/
theorem exists_eq_smul_vecMulVec_self_of_rank_le_one [Nonempty n] {Z : Matrix n n ℝ}
    (hZ : Z.IsSymm) (hr : Z.rank ≤ 1) :
    ∃ (β : ℝ) (x : n → ℝ), x ⬝ᵥ x = 1 ∧ Z = β • vecMulVec x x := by
  classical
  have hH : Z.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hZ
  have hsum : Z = ∑ l, hH.eigenvalues l •
      vecMulVec ⇑(hH.eigenvectorBasis l) ⇑(hH.eigenvectorBasis l) := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, star_trivial] using hH.eq_sum_smul_vecMulVec
  have hunit : ∀ l, ⇑(hH.eigenvectorBasis l) ⬝ᵥ ⇑(hH.eigenvectorBasis l) = 1 := fun l => by
    simpa only [star_trivial] using hH.star_dotProduct_eigenvectorBasis_self l
  rw [hH.rank_eq_card_non_zero_eigs, Fintype.card_le_one_iff] at hr
  by_cases h0 : ∀ l, hH.eigenvalues l = 0
  · refine ⟨0, _, hunit (Classical.arbitrary n), ?_⟩
    refine hsum.trans ?_
    simp [h0]
  · push Not at h0
    obtain ⟨l₀, hl₀⟩ := h0
    refine ⟨hH.eigenvalues l₀, _, hunit l₀, hsum.trans ?_⟩
    refine Finset.sum_eq_single l₀ (fun l _ hl => ?_) (by simp)
    by_cases h : hH.eigenvalues l = 0
    · rw [h, zero_smul]
    · exact absurd (congrArg Subtype.val (hr ⟨l, h⟩ ⟨l₀, hl₀⟩)) hl

/-- **The Rayleigh quotient bound.** Let $A$ be a real symmetric matrix with eigenvalues
$\lambda_i$, and let $k$ be an index with $|\lambda_i| \le |\lambda_k|$ for all $i$. Then every
$x$ with $x^T x = 1$ satisfies
$$|x^T A x| \le |\lambda_k|.$$
-/
theorem abs_dotProduct_mulVec_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {k : n}
    (hk : ∀ i, |hA.eigenvalues i| ≤ |hA.eigenvalues k|) {x : n → ℝ} (hx : x ⬝ᵥ x = 1) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ |hA.eigenvalues k| := by
  set q := fun l => ⇑(hA.eigenvectorBasis l)
  have hsum : A = ∑ l, hA.eigenvalues l • vecMulVec (q l) (q l) := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, star_trivial] using hA.eq_sum_smul_vecMulVec
  have hexp : x ⬝ᵥ (A *ᵥ x) = ∑ l, hA.eigenvalues l * (q l ⬝ᵥ x) ^ 2 := by
    conv_lhs => rw [hsum]
    rw [sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, dotProduct_comm x (q l), sq]
  have hpars : ∑ l, (q l ⬝ᵥ x) ^ 2 = 1 := by
    have h := hA.eigenvectorBasis.sum_sq_norm_inner_right (WithLp.toLp 2 x)
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial, hx] at h
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [EuclideanSpace.inner_eq_star_dotProduct, Real.norm_eq_abs, sq_abs]
    simp [q, dotProduct_comm]
  rw [hexp]
  calc |∑ l, hA.eigenvalues l * (q l ⬝ᵥ x) ^ 2|
      ≤ ∑ l, |hA.eigenvalues l| * (q l ⬝ᵥ x) ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp_rw [abs_mul, abs_sq]
    _ ≤ ∑ l, |hA.eigenvalues k| * (q l ⬝ᵥ x) ^ 2 :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hk l) (sq_nonneg _)
    _ = |hA.eigenvalues k| := by rw [← Finset.mul_sum, hpars, mul_one]

/-! ### Matrices whose conjugate transpose is affine in them -/

section AffineConjTranspose

/-- The conjugate of $e^{i\theta}$ is $e^{-i\theta}$ for real $\theta$. -/
private theorem star_exp_mul_I (θ : ℝ) :
    star (Complex.exp (θ * Complex.I)) = Complex.exp (-(θ * Complex.I)) := by
  rw [show star (Complex.exp ((θ : ℂ) * Complex.I))
      = starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) from rfl, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- For real $\theta$, $e^{i\theta} \, \overline{e^{i\theta}} = 1$. -/
private theorem exp_mul_I_mul_star (θ : ℝ) :
    Complex.exp (θ * Complex.I) * star (Complex.exp (θ * Complex.I)) = 1 := by
  rw [star_exp_mul_I, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- For a polynomial $q = cX + a$ of degree at most one, $q(A) = aI + cA$. -/
private theorem aeval_C_mul_X_add_C (A : Matrix n n ℂ) (c a : ℂ) :
    aeval A (C c * X + C a) = a • (1 : Matrix n n ℂ) + c • A := by
  rw [map_add, map_mul, aeval_C, aeval_C, aeval_X, ← Algebra.smul_def,
    Algebra.algebraMap_eq_smul_one, add_comm]

/-- **The matrices whose conjugate transpose is affine in them.** Let $A$ be a complex square
matrix. Then $A^H = q(A)$ for a polynomial $q$ of degree at most one if and only if there are
real numbers $\theta$, $\rho$ and a matrix $B$ with $B^H = -B$ such that
$$A = e^{i\theta} (\rho I + B).$$

This is the sharp form of the closing remark of [saad2003iterative], §6.10. That remark is the
case $\nu(A) \le 1$ of the Faber–Manteuffel theory, in which the conjugate gradient method
applies. No normality is assumed: the left side implies it.

The forward direction writes $A^H = \alpha I + \beta A$ and takes conjugate transposes, which
gives $(1 - \bar\beta \beta) A = (\bar\alpha + \bar\beta \alpha) I$. So either $A$ is a scalar
matrix, or $|\beta| = 1$. In the second case $\beta = -e^{-2i\theta}$ for a real $\theta$, the
same identity forces $\alpha e^{i\theta}$ to be real, and $B = e^{-i\theta} A - \rho I$ with
$2\rho = \alpha e^{i\theta}$ is skew-Hermitian. -/
theorem exists_natDegree_le_one_aeval_eq_conjTranspose_iff {A : Matrix n n ℂ} :
    (∃ q : ℂ[X], q.natDegree ≤ 1 ∧ aeval A q = Aᴴ) ↔
      ∃ (θ ρ : ℝ) (B : Matrix n n ℂ), Bᴴ = -B ∧
        A = Complex.exp (θ * Complex.I) •
          ((ρ : ℂ) • (1 : Matrix n n ℂ) + B) := by
  constructor
  · rintro ⟨q, hq1, hq2⟩
    obtain ⟨α, b, hAH⟩ : ∃ α b : ℂ, Aᴴ = α • (1 : Matrix n n ℂ) + b • A :=
      ⟨q.coeff 0, q.coeff 1, by
        conv_lhs => rw [← hq2, eq_X_add_C_of_natDegree_le_one hq1]
        rw [aeval_C_mul_X_add_C]⟩
    have hAAH : A = star α • (1 : Matrix n n ℂ) + star b • Aᴴ := by
      have h := congrArg conjTranspose hAH
      rwa [conjTranspose_conjTranspose, conjTranspose_add,
        conjTranspose_smul, conjTranspose_smul, conjTranspose_one] at h
    have h2 : A = star α • (1 : Matrix n n ℂ)
        + star b • (α • (1 : Matrix n n ℂ) + b • A) := by
      rw [hAH] at hAAH
      exact hAAH
    have hkey : ((1 : ℂ) - star b * b) • A
        = (star α + star b * α) • (1 : Matrix n n ℂ) :=
      calc ((1 : ℂ) - star b * b) • A = A - (star b * b) • A := by rw [sub_smul, one_smul]
        _ = (star α • (1 : Matrix n n ℂ)
              + star b • (α • (1 : Matrix n n ℂ) + b • A))
              - (star b * b) • A := by rw [← h2]
        _ = (star α + star b * α) • (1 : Matrix n n ℂ) := by module
    by_cases hsc : ∃ c : ℂ, A = c • (1 : Matrix n n ℂ)
    · obtain ⟨c, rfl⟩ := hsc
      refine ⟨Complex.arg c, ‖c‖, 0, by simp, ?_⟩
      rw [add_zero, smul_smul, mul_comm, Complex.norm_mul_exp_arg_mul_I]
    · have hne : Nonempty n := by
        rcases isEmpty_or_nonempty n with hE | hN
        · refine absurd ⟨0, ?_⟩ hsc
          ext i
          exact (hE.false i).elim
        · exact hN
      obtain ⟨i⟩ := hne
      have hsmul_one : ∀ c : ℂ, c • (1 : Matrix n n ℂ) = 0 → c = 0 := by
        intro c hc
        have := congrFun (congrFun hc i) i
        simpa using this
      have hd : star b * b = 1 := by
        by_contra hd0
        refine hsc ⟨((1 : ℂ) - star b * b)⁻¹ * (star α + star b * α), ?_⟩
        have hdne : (1 : ℂ) - star b * b ≠ 0 := sub_ne_zero.2 (Ne.symm hd0)
        rw [mul_smul, ← hkey, inv_smul_smul₀ hdne]
      have he : star α + star b * α = 0 := by
        refine hsmul_one _ ?_
        rw [← hkey, hd, sub_self, zero_smul]
      have hbnorm : ‖b‖ = 1 := by
        have h := congrArg norm hd
        rw [norm_mul, norm_star, norm_one] at h
        have h0 : (‖b‖ - 1) * (‖b‖ + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 h0 with h1 | h1
        · linarith
        · exfalso; linarith [norm_nonneg b]
      obtain ⟨θ, w, hw, hww, hbw⟩ : ∃ (θ : ℝ) (w : ℂ),
          w = Complex.exp (θ * Complex.I) ∧ w * star w = 1 ∧ b = -(star w) ^ 2 := by
        refine ⟨-(Complex.arg (-b)) / 2, _, rfl, exp_mul_I_mul_star _, ?_⟩
        have hexp : Complex.exp ((Complex.arg (-b) : ℂ) * Complex.I) = -b := by
          have h := Complex.norm_mul_exp_arg_mul_I (-b)
          rwa [norm_neg, hbnorm, Complex.ofReal_one, one_mul] at h
        rw [star_exp_mul_I, sq, ← Complex.exp_add,
          show -(((-(Complex.arg (-b)) / 2 : ℝ) : ℂ) * Complex.I)
                + -(((-(Complex.arg (-b)) / 2 : ℝ) : ℂ) * Complex.I)
              = ((Complex.arg (-b) : ℝ) : ℂ) * Complex.I by push_cast; ring,
          hexp, neg_neg]
      have hsb : star b = -w ^ 2 := by rw [hbw, star_neg, star_pow, star_star]
      have hαstar : star α = w ^ 2 * α := by
        have hα' : star α = -(star b * α) := by linear_combination he
        rw [hα', hsb]
        ring
      have hreal : star (α * w) = α * w := by
        rw [star_mul, hαstar]
        calc star w * (w ^ 2 * α) = (w * star w) * (w * α) := by ring
          _ = α * w := by rw [hww, one_mul, mul_comm]
      obtain ⟨r, hr⟩ : ∃ r : ℝ, ((r : ℂ)) = α * w :=
        ⟨(α * w).re, Complex.conj_eq_iff_re.1 hreal⟩
      have hαw : w * α = 2 * ((r / 2 : ℝ) : ℂ) := by
        rw [mul_comm w α, ← hr]
        push_cast
        ring
      have hwb : w * b = -star w := by
        rw [hbw]
        calc w * -(star w) ^ 2 = -((w * star w) * star w) := by ring
          _ = -star w := by rw [hww, one_mul]
      have hρstar : star (((r / 2 : ℝ) : ℂ)) = ((r / 2 : ℝ) : ℂ) := Complex.conj_ofReal _
      refine ⟨θ, r / 2, star w • A - ((r / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ), ?_, ?_⟩
      · rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_smul,
          conjTranspose_one, star_star, hAH, hρstar, smul_add, smul_smul, smul_smul,
          hαw, hwb]
        module
      · have hinner : ((r / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)
            + (star w • A - ((r / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
            = star w • A := by abel
        rw [← hw, hinner, smul_smul, hww, one_smul]
  · rintro ⟨θ, ρ, B, hB, hA⟩
    have hww : Complex.exp (θ * Complex.I) * star (Complex.exp (θ * Complex.I)) = 1 :=
      exp_mul_I_mul_star θ
    have hρstar : star ((ρ : ℂ)) = ((ρ : ℂ)) := Complex.conj_ofReal _
    have hBeq : B = star (Complex.exp (θ * Complex.I)) • A
        - (ρ : ℂ) • (1 : Matrix n n ℂ) := by
      rw [hA, smul_smul, mul_comm (star (Complex.exp (θ * Complex.I))), hww, one_smul]
      abel
    have hAH : Aᴴ = star (Complex.exp (θ * Complex.I)) •
        ((ρ : ℂ) • (1 : Matrix n n ℂ) + -B) := by
      conv_lhs => rw [hA]
      rw [conjTranspose_smul, conjTranspose_add, conjTranspose_smul,
        conjTranspose_one, hB, hρstar]
    refine ⟨C (-(star (Complex.exp (θ * Complex.I))) ^ 2)
        * X + C (2 * (ρ : ℂ) * star (Complex.exp (θ * Complex.I))),
      natDegree_linear_le, ?_⟩
    rw [aeval_C_mul_X_add_C, hAH, hBeq]
    module

end AffineConjTranspose

end Matrix
