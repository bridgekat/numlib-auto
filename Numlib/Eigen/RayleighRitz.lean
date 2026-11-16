/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Order.Filter.Extr
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Eigen.MinMax
import Numlib.Krylov.Arnoldi

/-!
# Rayleigh–Ritz approximation

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $A$ be a
linear operator on $E$, and let $K$ be a subspace of $E$ with orthogonal projection $P_K$. A **Ritz
pair** of $A$ on $K$ is a pair $(\theta, u)$ with $u \in K$, $u \neq 0$ and $Au - \theta u \perp K$.
This Galerkin condition holds exactly when $(\theta, u)$ is an eigenpair of the compression
$A_K = P_K A|_K$, and it needs only an inner product and an orthogonal projection onto $K$: no
finite dimension and no completeness. The oblique (Petrov–Galerkin) version asks
$Au - \theta u \perp L$ for a test space $L$, and it is the eigenvalue problem of the oblique
compression $Q A|_K$ for a projector $Q$ onto $K$ along $L^\perp$. The module proves the error
analysis of the Rayleigh–Ritz procedure in [saad2011numerical], §4.3: exactness on an invariant
subspace (Proposition 4.3), the residual bounds with a coupling constant $\gamma$ (Theorems 4.3 and
4.7), and, for a symmetric $A$ (§4.3.2), the variational characterization of the Ritz values with
Cauchy interlacing (Proposition 4.4 and Corollary 4.1), the error of the Rayleigh quotient and of
the Ritz values (Lemmas 4.1 and 4.2, Theorem 4.5), and the error of the Ritz vectors (Theorem 4.6
and Proposition 4.5). The Hermitian bounds rest on the Courant–Fischer theorem, Theorem 1.9 of the
same book, which `Numlib.Eigen.MinMax` proves.

The module also proves two results on the Arnoldi process from [saad2011numerical], §6.1–6.2: the
characteristic polynomial of the Hessenberg matrix $H_m$ minimizes $\|p(A) b\|$ over the monic
polynomials $p$ of degree $m$ (Theorem 6.1, which rests on the polynomial compression identity of
Proposition 6.4, proved in `Numlib.Analysis.InnerProductSpace.Projection.Compression`), and the
residual norm of a Ritz vector $V_m y$ is $|h_{m+1,m}| \, |y_m|$ in the 1-based notation of the
source (Proposition 6.8). The last result is the optimality of the compression in the Frobenius
norm, Theorem 8.1.14 of [golub2013matrix]: for $Q$ with orthonormal columns, $\|AQ - QS\|_F$ is
least at $S = Q^H A Q$.

## Main definitions

* `Krylov.IsRitzPair`: $(\theta, u)$ is a Ritz pair of $A$ on $K$ if $u \in K$, $u \neq 0$ and
  $Au - \theta u \in K^\perp$.
* `Krylov.IsObliqueRitzPair`: $(\theta, u)$ is an oblique Ritz pair of $A$ on the trial space $K$
  and the test space $L$ if $u \in K$, $u \neq 0$ and $Au - \theta u \in L^\perp$.

## Main results

* `Krylov.isRitzPair_iff_hasEigenvector`: the Ritz pairs of $A$ on $K$ are exactly the eigenpairs of
  the compression $A_K$.
* `Krylov.isObliqueRitzPair_iff_hasEigenvector`: the oblique Ritz pairs are exactly the eigenpairs
  of the oblique compression $Q A|_K$.
* `Krylov.IsRitzPair.hasEigenvector_of_invt`: on an $A$-invariant subspace $K$, every Ritz pair is
  an eigenpair of $A$.
* `Krylov.compression_residual_le`: if $Au = \mu u$ and $\|P_K A x\| \le \gamma \|x\|$ for
  $x \in K^\perp$, then $\|(A_K - \mu) P_K u\| \le \gamma \|u - P_K u\|$.
* `Krylov.compressionBy_residual_le`: the same bound for the oblique compression, with $\gamma$ a
  bound on $Q(A - \mu)$.
* `Krylov.IsRitzPair.rayleighQuotient_eq`: a Ritz value is the Rayleigh quotient of its Ritz vector.
* `LinearMap.IsSymmetric.isGreatest_eigenvalues_compression`: for a symmetric $A$, the $i$-th Ritz
  value is the max–min value of the Rayleigh quotient of $A$ over the $(i + 1)$-dimensional
  subspaces of $K$.
* `LinearMap.IsSymmetric.eigenvalues_compression_le`: Cauchy interlacing, $\theta_i \le \lambda_i$.
* `LinearMap.IsSymmetric.ritz_value_error_le`: $0 \le \lambda_0 - \theta_0 \le C \tan^2 \angle(u,
  K)$ for an eigenvector $u$ of the largest eigenvalue $\lambda_0$.
* `LinearMap.IsSymmetric.ritz_value_error_le_of_forall_inner_eq_zero`: $0 \le \lambda_i - \theta_i
  \le C (\|u - y\| / \|y\|)^2$ for a nonzero $y \in K$ orthogonal to the first $i$ Ritz vectors.
* `LinearMap.IsSymmetric.sin_angle_ritzVector_le`: some Ritz vector $w$ for $\theta$ satisfies $\sin
  \angle(u, w) \le \sqrt{1 + \gamma^2 / \delta^2} \, \sin \angle(u, K)$.
* `LinearMap.IsSymmetric.abs_ritz_value_sub_le`: $|\theta - \lambda| \le C \sin^2 \angle(u, w)$ for
  a Ritz pair $(\theta, w)$ and an eigenpair $(\lambda, u)$.
* `Arnoldi.charpoly_compression_isMinOn`: the characteristic polynomial of the compression to
  $\mathcal{K}_m(A, b)$ minimizes $\|p(A) b\|$ over the monic $p$ of degree $m$.
* `Arnoldi.norm_ritz_residual_eq`: the Ritz vector $V_{m+1} y$ of an eigenpair $(\theta, y)$ of
  $H_{m+1}$ has residual norm $|h_{m+1,m}| \, |y_m|$.
* `Matrix.isLeast_frobenius_norm_mul_sub_mul`: the least value of $\|AQ - QS\|_F$ over all $S$ is
  $\|(I - QQ^H) A Q\|_F$.

## Proof outline

The residual bounds come from the identity $(A_K - \mu) P_K u = -P_K A (I - P_K) u$ for an eigenpair
$(\mu, u)$ of $A$. The Hermitian bounds use one observation: if $Au = \lambda u$ and $A$ is
symmetric, then the quadratic form of $A - \lambda$ takes the same value at $y$ and at $u - y$. A
competitor $y$ chosen in $K$ then bounds the distance from $\lambda$ to its Rayleigh quotient, and
the variational characterization of the Ritz values turns this into a bound on the Ritz value.
Interlacing holds because the max–min over the subspaces of $K$ ranges over fewer competitors than
the max–min over all subspaces of $E$. The optimality of the characteristic polynomial follows from
Cayley–Hamilton, which makes $p(A) b$ orthogonal to the Krylov subspace, and from Pythagoras. The
Frobenius-norm optimality is also Pythagoras: the residual splits into its components in the range
of $Q$ and orthogonal to it.

## Notation

* $\rho_A(x) = \operatorname{Re} \langle Ax, x \rangle / \|x\|^2$: the Rayleigh quotient
  `LinearMap.rayleighQuotient`, with the value $0$ at $x = 0$.
* $\sin \angle(u, K) = \|u - P_K u\| / \|u\|$ and $\tan \angle(u, K) = \|u - P_K u\| / \|P_K u\|$:
  the angle functions `Submodule.sinAngle` and `Submodule.tanAngle`. For vectors, $\angle(u, w)$ is
  the angle between $u$ and the line $\mathbb{K} w$, `(𝕜 ∙ w).sinAngle u`.
* $\lambda_i$ and $\theta_i$: the eigenvalues of a symmetric $A$ and of its compression $A_K$,
  sorted decreasingly and indexed from $0$, so that $\lambda_0$ is the largest. They are
  `LinearMap.IsSymmetric.eigenvalues` of `hA` and of `compression.isSymmetric A K hA`.
* $v_j$ and $h_{ij} = \langle v_i, A v_j \rangle$: the Arnoldi vectors `Arnoldi.vec A b j` and the
  Hessenberg entries `Arnoldi.coeff A b i j`, indexed from $0$. $H_m$ is
  `Arnoldi.hessenbergSq A b m`, and $V_m y = \sum_{j < m} y_j v_j$.

## Implementation notes

* The inner product $\langle x, y \rangle$ is conjugate-linear in $x$, as in Mathlib.
* The coupling constant $\gamma$ and the bound $C$ on the quadratic form of $A - \lambda$ enter as
  hypotheses, not as operator norms. So the results apply to an unbounded $A$, and to sharper
  constants that a particular $K$ provides. For a bounded $A$,
  `Krylov.norm_starProjection_apply_le_opNorm` and `Krylov.abs_re_inner_sub_le_opNorm` supply the
  hypotheses with the operator norms. This is the same choice that `Numlib.Eigen.MinMax` makes for
  Weyl's inequality.
* The constant of `Krylov.compression_residual_le` and of the Ritz vector bound is
  $\|P_K A (I - P_K)\|$, not $\|(I - P_K) A P_K\|$. For a Krylov subspace built by the Arnoldi
  process, the second is the single Hessenberg entry $h_{m+1,m}$. The two agree when $A$ is
  symmetric, because each is then the adjoint of the other. So $\gamma = h_{m+1,m}$ can be used in
  the symmetric results, but not by a nonsymmetric consumer of `Krylov.compression_residual_le`.
* In the oblique bounds the constant bounds $Q(A - \mu)$ and not $QA$: unlike $P_K (I - P_K)$, the
  composite $Q (I - P_K)$ need not vanish, so the shift does not drop out of the residual identity.
* Theorem 4.5 of [saad2011numerical] is stated for every index, with the leading Ritz vectors
  projected out. `LinearMap.IsSymmetric.ritz_value_error_le_of_forall_inner_eq_zero` takes the
  competitor $y$ as data instead of constructing it from a spectral projector. The case of the
  largest eigenvalue is `LinearMap.IsSymmetric.ritz_value_error_le`, where the projection is the
  identity.
* Theorem 4.6 of [saad2011numerical] is stated, as in the source, as the existence of some Ritz
  vector for the given Ritz value. The Ritz vector produced is the projection of $P_K u$ onto the
  $\theta$-eigenspace of the compression. When that projection vanishes, the bound is vacuous,
  because its right-hand side is then at least $1$.
* The source completes $Q$ to an orthogonal matrix in Theorem 8.1.14 of [golub2013matrix]. The
  projection form $I - QQ^H$ avoids the completion.
* Both Arnoldi results hold past breakdown: the first up to and including the step at which the
  process terminates, the second with no hypothesis on the grade.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-!
### Projections and angles

Four facts about the orthogonal projection `Submodule.starProjection` and about the angles of
`Numlib.Analysis.InnerProductSpace.Projection.Angle` that the Hermitian bounds below need.
-/

/-- Let $K$ be a subspace of $E$ with an orthogonal projection $P_K$, let $u \in E$ and let
$v \in K$. Then
$$\|u - v\|^2 = \|u - P_K u\|^2 + \|P_K u - v\|^2.$$

The error $u - P_K u$ lies in $K^\perp$ and $P_K u - v$ lies in $K$. The case $v = 0$ is the
usual splitting of $\|u\|^2$, and the identity is the reason that $P_K u$ is the best
approximation of $u$ from $K$. -/
theorem norm_sub_sq_eq_add_of_mem (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) {v : E}
    (hv : v ∈ K) :
    ‖u - v‖ ^ 2 = ‖u - K.starProjection u‖ ^ 2 + ‖K.starProjection u - v‖ ^ 2 := by
  have h1 : u - v = (u - K.starProjection u) + (K.starProjection u - v) := by abel
  have h2 : inner 𝕜 (u - K.starProjection u) (K.starProjection u - v) = (0 : 𝕜) :=
    Submodule.inner_left_of_mem_orthogonal
      (Submodule.sub_mem _ (K.starProjection_apply_mem u) hv)
      (K.sub_starProjection_mem_orthogonal u)
  rw [h1]
  simp only [pow_two]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h2

/-- Let $u, v \in E$. If $\langle v, u \rangle = \langle v, v \rangle$, then the orthogonal
projection of $u$ onto the line $\mathbb{K} v$ is $v$.

This is how a vector is recognized as the projection of another vector onto its own line. It
turns the Ritz vector of `LinearMap.IsSymmetric.sin_angle_ritzVector_le` into an angle. -/
theorem starProjection_span_singleton_eq_self {v u : E}
    (h : inner 𝕜 v u = inner 𝕜 v v) : (𝕜 ∙ v).starProjection u = v :=
  Submodule.eq_starProjection_of_mem_orthogonal (Submodule.mem_span_singleton_self v)
    (Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by rw [inner_sub_right, h, sub_self]))

/-- Let $v \in E$ be nonzero and let $w \in E$. The cosine of the angle between $w$ and the line
$\mathbb{K} v$ is the normalized inner product:
$$\cos \angle(w, \mathbb{K} v) = \frac{|\langle v, w \rangle|}{\|v\| \, \|w\|}.$$

For $w = 0$ both sides are $0$. On lines, `Submodule.cosAngle` is thus the ordinary cosine of
the angle between two vectors. -/
theorem cosAngle_span_singleton {v : E} (hv : v ≠ 0) (w : E) :
    (𝕜 ∙ v).cosAngle w = ‖inner 𝕜 v w‖ / (‖v‖ * ‖w‖) := by
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  rw [cosAngle, starProjection_singleton 𝕜 w, norm_smul, norm_div, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖v‖ ^ 2)]
  field_simp

/-- Let $v, w \in E$ be nonzero. The angle between two vectors is symmetric:
$$\sin \angle(w, \mathbb{K} v) = \sin \angle(v, \mathbb{K} w).$$

Mathlib has no angle between a vector and a subspace. This result says that the one-sided
`Submodule.sinAngle` gives a symmetric notion on lines, so that the eigenvector bound and the
eigenvalue bound below can use the same $\sin \angle(u, w)$. -/
theorem sinAngle_span_singleton_comm {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    (𝕜 ∙ v).sinAngle w = (𝕜 ∙ w).sinAngle v := by
  have hnorm : ‖inner 𝕜 v w‖ = ‖inner 𝕜 w v‖ := by
    rw [← inner_conj_symm v w, RCLike.norm_conj]
  have hcos : (𝕜 ∙ v).cosAngle w = (𝕜 ∙ w).cosAngle v := by
    rw [cosAngle_span_singleton hv, cosAngle_span_singleton hw, hnorm, mul_comm ‖w‖ ‖v‖]
  have h1 := (𝕜 ∙ v).cosAngle_sq_add_sinAngle_sq hw
  have h2 := (𝕜 ∙ w).cosAngle_sq_add_sinAngle_sq hv
  rw [hcos] at h1
  exact (pow_left_inj₀ (sinAngle_nonneg _ _) (sinAngle_nonneg _ _) two_ne_zero).1 (by linarith)

/-- Let $W \le K$ be subspaces of $E$ with orthogonal projections $P_W$ and $P_K$, and let
$u \in E$. Then
$$\|u - (P_K u - P_W u)\|^2 = \|u - P_K u\|^2 + \|P_W u\|^2.$$

This is the estimate behind Theorem 4.5 of [saad2011numerical] at a general index, where $W$ is
the span of the Ritz vectors already computed and $P_K u - P_W u$ is the competitor orthogonal
to them. The source states it as an inequality. It is an equality, because
$P_W (u - P_K u) = 0$. -/
theorem norm_sub_sub_starProjection_sq (W K : Submodule 𝕜 E) [W.HasOrthogonalProjection]
    [K.HasOrthogonalProjection] (hWK : W ≤ K) (u : E) :
    ‖u - (K.starProjection u - W.starProjection u)‖ ^ 2
      = ‖u - K.starProjection u‖ ^ 2 + ‖W.starProjection u‖ ^ 2 := by
  have hsplit : u - (K.starProjection u - W.starProjection u)
      = (u - K.starProjection u) + W.starProjection u := by module
  have horth : inner 𝕜 (u - K.starProjection u) (W.starProjection u) = (0 : 𝕜) :=
    Submodule.inner_left_of_mem_orthogonal (hWK (W.starProjection_apply_mem u))
      (K.sub_starProjection_mem_orthogonal u)
  rw [hsplit]
  simp only [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth]

end Submodule

namespace Krylov

/-! ### Ritz pairs and oblique Ritz pairs -/

/-- Let $A$ be a linear operator on $E$, let $K$ (the trial space) and $L$ (the test space) be
subspaces of $E$, and let $\theta \in \mathbb{K}$ and $u \in E$. The pair $(\theta, u)$ is an
**oblique Ritz pair** (or Petrov–Galerkin Ritz pair) of $A$ on $K$ and $L$ if $u \in K$,
$u \neq 0$ and
$$Au - \theta u \in L^\perp.$$

For $L = K$ this is `Krylov.IsRitzPair`. By `Krylov.isObliqueRitzPair_iff_hasEigenvector`, the
oblique Ritz pairs are the eigenpairs of the oblique compression `compressionBy Q A` for a
projector $Q$ onto $K$ along $L^\perp$. -/
structure IsObliqueRitzPair (A : E →ₗ[𝕜] E) (K L : Submodule 𝕜 E) (θ : 𝕜) (u : E) : Prop where
  /-- The Ritz vector $u$ lies in the trial space $K$. -/
  mem : u ∈ K
  /-- The Ritz vector $u$ is nonzero. -/
  ne_zero : u ≠ 0
  /-- The Petrov–Galerkin condition: the residual $Au - \theta u$ is orthogonal to the test space
  $L$. -/
  residual_mem_orthogonal : A u - θ • u ∈ Lᗮ

/-- Let $A$ be a linear operator on $E$, let $K$ be a subspace of $E$, and let
$\theta \in \mathbb{K}$ and $u \in E$. The pair $(\theta, u)$ is a **Ritz pair** of $A$ on $K$,
with **Ritz value** $\theta$ and **Ritz vector** $u$, if $u \in K$, $u \neq 0$ and
$$Au - \theta u \in K^\perp.$$

By `Krylov.isRitzPair_iff_hasEigenvector`, the Ritz pairs are exactly the eigenpairs of the
compression `compression A K`. -/
structure IsRitzPair (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) (θ : 𝕜) (u : E) : Prop where
  /-- The Ritz vector $u$ lies in the subspace $K$. -/
  mem : u ∈ K
  /-- The Ritz vector $u$ is nonzero. -/
  ne_zero : u ≠ 0
  /-- The Galerkin condition: the residual $Au - \theta u$ is orthogonal to $K$. -/
  residual_mem_orthogonal : A u - θ • u ∈ Kᗮ

variable {A : E →ₗ[𝕜] E} {K L : Submodule 𝕜 E} {θ : 𝕜} {u : E}

/-- A Ritz pair of $A$ on $K$ is an oblique Ritz pair of $A$ on $K$ with the test space $K$. -/
theorem IsRitzPair.isObliqueRitzPair (h : IsRitzPair A K θ u) : IsObliqueRitzPair A K K θ u :=
  ⟨h.mem, h.ne_zero, h.residual_mem_orthogonal⟩

/-- An oblique Ritz pair of $A$ on $K$ with the test space $K$ is a Ritz pair of $A$ on $K$. -/
theorem IsObliqueRitzPair.isRitzPair (h : IsObliqueRitzPair A K K θ u) : IsRitzPair A K θ u :=
  ⟨h.mem, h.ne_zero, h.residual_mem_orthogonal⟩

/-- The pair $(\theta, u)$ is a Ritz pair of $A$ on $K$ if and only if it is an oblique Ritz pair of
$A$ on $K$ with the test space $K$. -/
theorem isRitzPair_iff_isObliqueRitzPair :
    IsRitzPair A K θ u ↔ IsObliqueRitzPair A K K θ u :=
  ⟨IsRitzPair.isObliqueRitzPair, IsObliqueRitzPair.isRitzPair⟩

/-- Let $A$ be a linear operator on $E$, let $K$ and $L$ be subspaces of $E$, and let $Q : E \to K$
be a linear projector onto $K$ along $L^\perp$: $Qx = x$ for $x \in K$, and $\ker Q = L^\perp$.
Let $\theta \in \mathbb{K}$ and $u \in K$. Then $(\theta, u)$ is an oblique Ritz pair of $A$ on
$K$ and $L$ if and only if $u$ is an eigenvector, with eigenvalue $\theta$, of the oblique
compression
$$Q A|_K : K \to K.$$

The oblique compression is `compressionBy Q A` of
`Numlib.Analysis.InnerProductSpace.Projection.Compression`. Such a $Q$ exists exactly when
$K \cap L^\perp = 0$, by `LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot`. The
projectors $V (W^H V)^{-1} W^H$ built from bases $V$ of $K$ and $W$ of $L$ are the concrete
instances. -/
theorem isObliqueRitzPair_iff_hasEigenvector (A : E →ₗ[𝕜] E) {K L : Submodule 𝕜 E}
    {Q : E →ₗ[𝕜] K} (hQ : ∀ x : K, Q x = x) (hker : LinearMap.ker Q = Lᗮ) (θ : 𝕜) (u : K) :
    IsObliqueRitzPair A K L θ (u : E) ↔ Module.End.HasEigenvector (compressionBy Q A) θ u := by
  have key : compressionBy Q A u = θ • u ↔ A (u : E) - θ • (u : E) ∈ Lᗮ := by
    rw [← hker, LinearMap.mem_ker, map_sub, map_smul, hQ u, sub_eq_zero]
    exact Iff.rfl
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, key]
  exact ⟨fun h => ⟨h.residual_mem_orthogonal, fun h0 => h.ne_zero (Submodule.coe_eq_zero.2 h0)⟩,
    fun h => ⟨u.2, fun h0 => h.2 (Submodule.coe_eq_zero.1 h0), h.1⟩⟩

/-- Let $A$ be a linear operator on $E$, let $K$ be a subspace of $E$ with an orthogonal projection
$P_K$, and let $\theta \in \mathbb{K}$ and $u \in K$. Then $(\theta, u)$ is a Ritz pair of $A$
on $K$ if and only if $u$ is an eigenvector, with eigenvalue $\theta$, of the compression
$$A_K = P_K A|_K : K \to K.$$

So the Rayleigh–Ritz condition on $E$ and the eigenvalue problem on $K$ are the same statement.
The Ritz vector is `(u : E)` on the left and `u : K` on the right.
`Krylov.IsRitzPair.hasEigenvector` and `Krylov.isRitzPair_of_hasEigenvector` are the two
directions in forms that avoid the coercion. -/
theorem isRitzPair_iff_hasEigenvector (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (θ : 𝕜) (u : K) :
    IsRitzPair A K θ (u : E) ↔ Module.End.HasEigenvector (compression A K) θ u := by
  rw [isRitzPair_iff_isObliqueRitzPair, compression.eq_compressionBy]
  exact isObliqueRitzPair_iff_hasEigenvector A
    K.orthogonalProjectionOnto_mem_subspace_eq_self
    (by ext x; exact Submodule.orthogonalProjectionOnto_eq_zero_iff) θ u

/-- If $(\theta, u)$ is a Ritz pair of $A$ on a subspace $K$ with an orthogonal projection, then
$u$, as an element of $K$, is an eigenvector of the compression $A_K$ with eigenvalue $\theta$.
This is the forward direction of `Krylov.isRitzPair_iff_hasEigenvector`. -/
theorem IsRitzPair.hasEigenvector [K.HasOrthogonalProjection] (h : IsRitzPair A K θ u) :
    Module.End.HasEigenvector (compression A K) θ ⟨u, h.mem⟩ :=
  (isRitzPair_iff_hasEigenvector A K θ ⟨u, h.mem⟩).1 h

/-- If $(\theta, u)$ is a Ritz pair of $A$ on a subspace $K$ with an orthogonal projection, then
$\theta$ is an eigenvalue of the compression $A_K$. So the Ritz values of a finite-dimensional
$K$ are the eigenvalues of a small matrix. -/
theorem IsRitzPair.hasEigenvalue [K.HasOrthogonalProjection] (h : IsRitzPair A K θ u) :
    Module.End.HasEigenvalue (compression A K) θ :=
  Module.End.hasEigenvalue_of_hasEigenvector h.hasEigenvector

/-- Let $K$ be a subspace with an orthogonal projection. If $u \in K$ is an eigenvector of the
compression $A_K$ with eigenvalue $\theta$, then $(\theta, u)$ is a Ritz pair of $A$ on $K$.
This is the converse direction of `Krylov.isRitzPair_iff_hasEigenvector`. -/
theorem isRitzPair_of_hasEigenvector (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (θ : 𝕜) {u : K}
    (h : Module.End.HasEigenvector (compression A K) θ u) : IsRitzPair A K θ (u : E) :=
  (isRitzPair_iff_hasEigenvector A K θ u).2 h

/-- Let $(\theta, u)$ be an oblique Ritz pair of $A$ on the trial space $K$ and the test space $L$.
If $K$ is $A$-invariant and $K \cap L^\perp = 0$, then $(\theta, u)$ is an eigenpair of $A$:
$u \neq 0$ and $Au = \theta u$. This is the remark that precedes Theorem 4.7 of
[saad2011numerical].

The residual lies in $K$, because $K$ is invariant, and in $L^\perp$, by the Petrov–Galerkin
condition. The condition $K \cap L^\perp = 0$ is the condition under which the oblique projector
onto $K$ along $L^\perp$ exists. The test space $L$ is otherwise arbitrary. -/
theorem IsObliqueRitzPair.hasEigenvector_of_invt (h : IsObliqueRitzPair A K L θ u)
    (hK : K ∈ Module.End.invtSubmodule A) (hKL : K ⊓ Lᗮ = ⊥) :
    Module.End.HasEigenvector A θ u := by
  refine ⟨Module.End.mem_eigenspace_iff.2 ?_, h.ne_zero⟩
  have hmem : A u - θ • u ∈ K ⊓ Lᗮ :=
    ⟨Submodule.sub_mem _ ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hK _ h.mem)
      (Submodule.smul_mem _ _ h.mem), h.residual_mem_orthogonal⟩
  rw [hKL, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- Let $(\theta, u)$ be a Ritz pair of $A$ on a subspace $K$. If $K$ is $A$-invariant, then
$(\theta, u)$ is an eigenpair of $A$: $u \neq 0$ and $Au = \theta u$. This is Proposition 4.3 of
[saad2011numerical].

The residual lies in $K$ and in $K^\perp$, so it is zero. No orthogonal projection onto $K$ and
no finite dimension are needed. -/
theorem IsRitzPair.hasEigenvector_of_invt (h : IsRitzPair A K θ u)
    (hK : K ∈ Module.End.invtSubmodule A) : Module.End.HasEigenvector A θ u :=
  h.isObliqueRitzPair.hasEigenvector_of_invt hK K.inf_orthogonal_eq_bot

/-- If $(\theta, u)$ is a Ritz pair of $A$ on an $A$-invariant subspace $K$, then $\theta$ is an
eigenvalue of $A$. -/
theorem IsRitzPair.hasEigenvalue_of_invt (h : IsRitzPair A K θ u)
    (hK : K ∈ Module.End.invtSubmodule A) : Module.End.HasEigenvalue A θ :=
  Module.End.hasEigenvalue_of_hasEigenvector (h.hasEigenvector_of_invt hK)

/-! ### A Ritz value is a Rayleigh quotient -/

/-- If $(\theta, u)$ is a Ritz pair of $A$ on $K$, then
$$\langle u, Au \rangle = \theta \, \|u\|^2.$$

This is the Galerkin condition tested against the Ritz vector itself. So the Ritz vector
determines the Ritz value. -/
theorem IsRitzPair.inner_self_apply (h : IsRitzPair A K θ u) :
    inner 𝕜 u (A u) = θ * ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
  have h0 := (Submodule.mem_orthogonal K _).1 h.residual_mem_orthogonal u h.mem
  rw [inner_sub_right, inner_smul_right, sub_eq_zero, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow] at h0
  exact h0

/-- If $(\theta, u)$ is a Ritz pair of $A$ on $K$, then
$\langle Au, u \rangle = \bar\theta \, \|u\|^2$. This is `Krylov.IsRitzPair.inner_self_apply`
with the operator in the first argument of the inner product, the order that the Rayleigh
quotient uses. -/
theorem IsRitzPair.inner_apply_self (h : IsRitzPair A K θ u) :
    inner 𝕜 (A u) u = (starRingEnd 𝕜) θ * ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_conj_symm (A u) u, h.inner_self_apply, map_mul, RCLike.conj_ofReal]

/-- If $(\theta, u)$ is a Ritz pair of $A$ on $K$, then $\operatorname{Re} \langle Au, u \rangle =
\operatorname{Re} \theta \, \|u\|^2$. -/
theorem IsRitzPair.re_inner_apply_self (h : IsRitzPair A K θ u) :
    RCLike.re (inner 𝕜 (A u) u) = RCLike.re θ * ‖u‖ ^ 2 := by
  rw [h.inner_apply_self, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im, RCLike.ofReal_re,
    RCLike.ofReal_im]
  ring

/-- If $(\theta, u)$ is a Ritz pair of $A$ on $K$, then the Rayleigh quotient of $A$ at the Ritz
vector is the real part of the Ritz value:
$$\rho_A(u) = \operatorname{Re} \theta.$$

No symmetry of $A$ is needed: the Galerkin condition alone forces the identity. This is why a
Rayleigh–Ritz procedure computes a Ritz value as a Rayleigh quotient. -/
theorem IsRitzPair.rayleighQuotient_eq (h : IsRitzPair A K θ u) :
    A.rayleighQuotient u = RCLike.re θ := by
  have hn : (0 : ℝ) < ‖u‖ ^ 2 := by
    have := h.ne_zero
    positivity
  rw [LinearMap.rayleighQuotient, h.re_inner_apply_self, mul_div_assoc,
    div_self (ne_of_gt hn), mul_one]

/-- Let $A$ be symmetric. If $(\theta, u)$ is a Ritz pair of $A$ on $K$, then $\theta$ is real:
$\bar\theta = \theta$.

Over $\mathbb{K} = \mathbb{R}$ this is trivial. Over $\mathbb{C}$ it makes the bounds below,
which compare $\operatorname{Re} \theta$ with real eigenvalues, statements about $\theta$
itself. -/
theorem IsRitzPair.conj_eq (hA : A.IsSymmetric) (h : IsRitzPair A K θ u) :
    (starRingEnd 𝕜) θ = θ := by
  have hn : ((‖u‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    simpa using pow_ne_zero 2 (norm_ne_zero_iff.2 h.ne_zero)
  refine mul_right_cancel₀ hn ?_
  rw [← h.inner_apply_self, hA u u, h.inner_self_apply]

/-- Let $K$ be a subspace with an orthogonal projection and let $y \in K$. The Rayleigh quotient of
the compression $A_K$ at $y$ is the Rayleigh quotient of $A$ at $y$:
$$\rho_{A_K}(y) = \rho_A(y).$$

The projection does not change the inner product against a test vector from $K$. This makes the
variational characterizations of the Ritz values and of the eigenvalues of $A$ comparable, and
it is the whole content of Cauchy interlacing. -/
theorem rayleighQuotient_compression (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (y : K) :
    (compression A K).rayleighQuotient y = A.rayleighQuotient (y : E) := by
  rw [LinearMap.rayleighQuotient, LinearMap.rayleighQuotient, compression.inner_apply]
  rfl

/-- Let $E$ have finite dimension $n + 1$, and let $A$ be symmetric with eigenvalues
$\lambda_0 \ge \dots \ge \lambda_n$. If $(\theta, u)$ is a Ritz pair of $A$ on a subspace $K$,
then
$$\lambda_n \le \operatorname{Re} \theta \le \lambda_0.$$

The reason is that $\operatorname{Re} \theta$ is a Rayleigh quotient of $A$
(`Krylov.IsRitzPair.rayleighQuotient_eq`), and `LinearMap.IsSymmetric.rayleighQuotient_mem_Icc`
bounds those. By `Krylov.IsRitzPair.conj_eq`, $\theta$ is real. The sharper statement, that the
$i$-th Ritz value is at most the $i$-th eigenvalue, is
`LinearMap.IsSymmetric.eigenvalues_compression_le`. -/
theorem IsRitzPair.mem_Icc [FiniteDimensional 𝕜 E] {n : ℕ} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n + 1) (h : IsRitzPair A K θ u) :
    RCLike.re θ ∈ Set.Icc (hA.eigenvalues hn (Fin.last n)) (hA.eigenvalues hn 0) := by
  rw [← h.rayleighQuotient_eq]
  exact hA.rayleighQuotient_mem_Icc hn h.ne_zero

/-! ### The residual bound with the coupling constant $\gamma$ -/

/-- For $u \in E$ and $\mu \in \mathbb{K}$, the vector $(A_K - \mu) P_K u$, read in $E$, is
$P_K A P_K u - \mu P_K u$. -/
private theorem coe_compression_sub_smul (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (μ : 𝕜) (u : E) :
    ((compression A K (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : K) : E)
      = K.starProjection (A (K.starProjection u)) - μ • K.starProjection u := rfl

/-- Let $A$ be a bounded operator on $E$, let $K$ be a subspace with an orthogonal projection $P_K$,
and let $x \in K^\perp$. Then
$$\|P_K A x\| \le \|P_K A (I - P_K)\| \, \|x\|.$$

So a bounded $A$ satisfies the coupling hypothesis of `Krylov.compression_residual_le` with
$\gamma = \|P_K A (I - P_K)\|$, the constant of [saad2011numerical]. The residual bounds take
$\gamma$ as a hypothesis instead of this operator norm, so that they apply to an unbounded $A$
and to the sharper values of $\gamma$ that a particular $K$ provides. For a symmetric $A$ and a
Krylov subspace built by the Arnoldi process, $\gamma$ is one Hessenberg entry;
`Arnoldi.starProjection_apply_vec` is the adjoint statement. -/
theorem norm_starProjection_apply_le_opNorm (A : E →L[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] {x : E} (hx : x ∈ Kᗮ) :
    ‖K.starProjection (A x)‖
      ≤ ‖K.starProjection ∘L (A ∘L (1 - K.starProjection))‖ * ‖x‖ := by
  have hfix : (1 - K.starProjection) x = x := by
    rw [sub_apply, one_apply_eq_self, Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hx, Submodule.coe_zero, sub_zero]
  calc ‖K.starProjection (A x)‖
      = ‖(K.starProjection ∘L (A ∘L (1 - K.starProjection))) x‖ := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hfix]
    _ ≤ ‖K.starProjection ∘L (A ∘L (1 - K.starProjection))‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _

/-- Let $K$ be a subspace of $E$ with an orthogonal projection $P_K$, and let
$\gamma \in \mathbb{R}$ satisfy $\|P_K A x\| \le \gamma \|x\|$ for all $x \in K^\perp$. If
$Au = \mu u$, then
$$\|(A_K - \mu) P_K u\| \le \gamma \, \|u - P_K u\|.$$
This is Theorem 4.3 of [saad2011numerical].

So a subspace that captures $u$ well carries an approximate eigenpair $(\mu, P_K u)$ of $A_K$
with a small residual, and the error analysis of Rayleigh–Ritz reduces to the distance from $u$
to $K$. The proof uses the residual identity `compression.apply_sub_smul_orthogonalProjection`,
which says that the left-hand vector is $-P_K A (I - P_K) u$. No finite dimension, completeness,
symmetry, or normalization of $u$ is used. -/
theorem compression_residual_le {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    {γ : ℝ} (hγ : ∀ x ∈ Kᗮ, ‖K.starProjection (A x)‖ ≤ γ * ‖x‖) {μ : 𝕜} {u : E}
    (hu : A u = μ • u) :
    ‖(compression A K (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E)‖
      ≤ γ * ‖u - K.starProjection u‖ := by
  rw [compression.apply_sub_smul_orthogonalProjection A K hu, norm_neg]
  exact hγ _ (K.sub_starProjection_mem_orthogonal u)

/-!
### The oblique residual bounds

An oblique projection method takes a search subspace $K$ and a test subspace $L$, and its
compression is $A_m = Q A P_K$ for the projector $Q$ onto $K$ along $L^\perp$ ([saad2011numerical],
§4.3.3). The composition with the orthogonal projection $P_K$ on the right makes $A_m$ vanish on
$K^\perp$, so that the a priori bounds are again in terms of $\|(I - P_K) u\|$. Only the projector
$Q$ is oblique here; the distance from $u$ to $K$ is still measured orthogonally.
-/

/-- Let $K$ be a subspace with an orthogonal projection $P_K$, let $Q : E \to K$ be a linear
projector onto $K$ ($Qx = x$ for $x \in K$), and let $A_m = Q A|_K$. If $Au = \mu u$, then
$$(A_m - \mu) P_K u = -Q (A - \mu) (u - P_K u).$$

Unlike the orthogonal case `compression.apply_sub_smul_orthogonalProjection`, the shift $\mu$
does not drop out of the right-hand side, because $Q (I - P_K)$ need not vanish when $Q$ is
oblique. For this reason the constant of `Krylov.compressionBy_residual_le` is a bound on
$Q(A - \mu)$ and not on $QA$. -/
theorem compressionBy_apply_sub_smul_orthogonalProjection {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {Q : E →ₗ[𝕜] K} (hQ : ∀ x : K, Q x = x) {μ : 𝕜} {u : E}
    (hu : A u = μ • u) :
    (compressionBy Q A (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E)
      = -(Q (A (u - K.starProjection u) - μ • (u - K.starProjection u)) : E) := by
  have hQP : (Q (K.starProjection u) : E) = K.starProjection u :=
    congrArg Subtype.val (hQ ⟨_, K.starProjection_apply_mem u⟩)
  have harg : A (u - K.starProjection u) - μ • (u - K.starProjection u)
      = -(A (K.starProjection u) - μ • K.starProjection u) := by
    rw [map_sub, hu]; module
  rw [harg]
  simp only [map_neg, map_sub, map_smul, Submodule.coe_neg, Submodule.coe_sub,
    Submodule.coe_smul, hQP, neg_neg]
  rfl

/-- Let $K$ be a subspace with an orthogonal projection $P_K$, let $Q : E \to K$ be a linear
projector onto $K$, and let $A_m = Q A|_K$. Let $\gamma \in \mathbb{R}$ satisfy
$\|Q(Ax - \mu x)\| \le \gamma \|x\|$ for all $x \in K^\perp$. If $Au = \mu u$, then
$$\|(A_m - \mu) P_K u\| \le \gamma \, \|u - P_K u\|.$$
This is the first inequality of Theorem 4.7 of [saad2011numerical].

The oblique compression $A_m$ is `compressionBy Q A`. This is the oblique form of
`Krylov.compression_residual_le`: for $Q = P_K$ it is that theorem, since
$P_K (A - \mu) x = P_K A x$ for $x \in K^\perp$. -/
theorem compressionBy_residual_le {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {Q : E →ₗ[𝕜] K} (hQ : ∀ x : K, Q x = x) {γ : ℝ} {μ : 𝕜}
    (hγ : ∀ x ∈ Kᗮ, ‖(Q (A x - μ • x) : E)‖ ≤ γ * ‖x‖) {u : E} (hu : A u = μ • u) :
    ‖(compressionBy Q A (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E)‖
      ≤ γ * ‖u - K.starProjection u‖ := by
  rw [compressionBy_apply_sub_smul_orthogonalProjection hQ hu, norm_neg]
  exact hγ _ (K.sub_starProjection_mem_orthogonal u)

/-- Under the hypotheses of `Krylov.compressionBy_residual_le`, the residual of the whole
eigenvector satisfies
$$\|A_m P_K u - \mu u\| \le \sqrt{|\mu|^2 + \gamma^2} \, \|u - P_K u\|,$$
where $A_m P_K u \in K$ is read as a vector of $E$. This is the second inequality of Theorem 4.7
of [saad2011numerical].

The vector $A_m P_K u - \mu u$ is $(A_m - \mu) P_K u - \mu (I - P_K) u$. The two terms lie in
$K$ and in $K^\perp$, and Pythagoras gives the constant, as in
`Krylov.compression_residual_le'`. -/
theorem compressionBy_residual_le' {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {Q : E →ₗ[𝕜] K} (hQ : ∀ x : K, Q x = x) {γ : ℝ} {μ : 𝕜}
    (hγ : ∀ x ∈ Kᗮ, ‖(Q (A x - μ • x) : E)‖ ≤ γ * ‖x‖) {u : E} (hu : A u = μ • u) :
    ‖(compressionBy Q A (K.orthogonalProjectionOnto u) : E) - μ • u‖
      ≤ Real.sqrt (‖μ‖ ^ 2 + γ ^ 2) * ‖u - K.starProjection u‖ := by
  set v : E := (compressionBy Q A (K.orthogonalProjectionOnto u) : E) with hv
  have hcoe : (compressionBy Q A (K.orthogonalProjectionOnto u)
      - μ • K.orthogonalProjectionOnto u : E) = v - μ • K.starProjection u := rfl
  have hle : ‖v - μ • K.starProjection u‖ ≤ γ * ‖u - K.starProjection u‖ := by
    rw [← hcoe]; exact compressionBy_residual_le hQ hγ hu
  have hrmem : v - μ • K.starProjection u ∈ K :=
    Submodule.sub_mem _ (compressionBy Q A (K.orthogonalProjectionOnto u)).2
      (Submodule.smul_mem _ _ (K.starProjection_apply_mem u))
  have hqmem : (-μ) • (u - K.starProjection u) ∈ Kᗮ :=
    Submodule.smul_mem _ _ (K.sub_starProjection_mem_orthogonal u)
  have hsplit : v - μ • u
      = (v - μ • K.starProjection u) + (-μ) • (u - K.starProjection u) := by module
  have hpyth : ‖v - μ • u‖ ^ 2
      = ‖v - μ • K.starProjection u‖ ^ 2 + ‖μ‖ ^ 2 * ‖u - K.starProjection u‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_right_of_mem_orthogonal hrmem hqmem), norm_smul, norm_neg]
    ring
  have hsq : ‖v - μ • u‖ ^ 2 ≤ (Real.sqrt (‖μ‖ ^ 2 + γ ^ 2) * ‖u - K.starProjection u‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [hpyth, hle, norm_nonneg (v - μ • K.starProjection u),
      norm_nonneg (u - K.starProjection u)]
  exact le_of_sq_le_sq hsq (by positivity)

/-- Under the hypotheses of `Krylov.compression_residual_le`, the residual of the whole eigenvector
satisfies
$$\|P_K A P_K u - \mu u\| \le \sqrt{|\mu|^2 + \gamma^2} \, \|u - P_K u\|.$$

Here the compression is read as the operator $P_K A P_K$ on all of $E$. The extra $|\mu|^2$
comes from the term $-\mu (I - P_K) u$, which is orthogonal to the residual of
`Krylov.compression_residual_le`. So $\sqrt{|\mu|^2 + \gamma^2}$ is the constant that Pythagoras
gives, and this argument cannot improve it. -/
theorem compression_residual_le' {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    {γ : ℝ} (hγ : ∀ x ∈ Kᗮ, ‖K.starProjection (A x)‖ ≤ γ * ‖x‖) {μ : 𝕜} {u : E}
    (hu : A u = μ • u) :
    ‖K.starProjection (A (K.starProjection u)) - μ • u‖
      ≤ Real.sqrt (‖μ‖ ^ 2 + γ ^ 2) * ‖u - K.starProjection u‖ :=
  compressionBy_residual_le' (Q := (K.orthogonalProjectionOnto : E →ₗ[𝕜] K))
    (fun x => K.orthogonalProjectionOnto_mem_subspace_eq_self x) (fun x hx => by
      rw [map_sub, map_smul, ContinuousLinearMap.coe_coe,
        K.orthogonalProjectionOnto_apply_of_mem_orthogonal hx, smul_zero, sub_zero]
      exact hγ x hx) hu

/-!
### The shifted quadratic form

The Hermitian bounds read a difference of an eigenvalue and a Rayleigh quotient as the quadratic
form of $A - \lambda$, and their hypothesis is a bound on that form. The following facts about the
form are used in the proofs.
-/

/-- For real $\lambda$, the real part of $\langle Ax, x \rangle - \lambda \langle x, x \rangle$ is
$\operatorname{Re} \langle Ax, x \rangle - \lambda \|x\|^2$. -/
private theorem re_inner_sub (A : E →ₗ[𝕜] E) (lam : ℝ) (x : E) :
    RCLike.re (inner 𝕜 (A x) x - (lam : 𝕜) * inner 𝕜 x x)
      = RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2 := by
  rw [map_sub, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul,
    RCLike.ofReal_re]

/-- If $A$ is symmetric and $Au = \lambda u$ with $\lambda$ real, then the quadratic form $\langle
Ax, x \rangle - \lambda \langle x, x \rangle$ takes the same value at $x + cu$ as at $x$. -/
private theorem inner_shift_add (hA : A.IsSymmetric) {lam : ℝ} (hu : A u = (lam : 𝕜) • u)
    (x : E) (c : 𝕜) :
    inner 𝕜 (A (x + c • u)) (x + c • u) - (lam : 𝕜) * inner 𝕜 (x + c • u) (x + c • u)
      = inner 𝕜 (A x) x - (lam : 𝕜) * inner 𝕜 x x := by
  have h1 : inner 𝕜 (A u) x = (lam : 𝕜) * inner 𝕜 u x := by
    rw [hu, inner_smul_left, RCLike.conj_ofReal]
  have h2 : inner 𝕜 (A x) u = (lam : 𝕜) * inner 𝕜 x u := by
    rw [hA x u, hu, inner_smul_right]
  have h3 : inner 𝕜 (A u) u = (lam : 𝕜) * inner 𝕜 u u := by
    rw [hu, inner_smul_left, RCLike.conj_ofReal]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, h1, h2, h3]
  ring

/-- The quadratic form $\langle Ax, x \rangle - \lambda \langle x, x \rangle$ takes the same value
at $-x$ as at $x$. -/
private theorem inner_shift_neg (A : E →ₗ[𝕜] E) (lam : ℝ) (x : E) :
    inner 𝕜 (A (-x)) (-x) - (lam : 𝕜) * inner 𝕜 (-x) (-x)
      = inner 𝕜 (A x) x - (lam : 𝕜) * inner 𝕜 x x := by
  simp

/-- If $A$ is symmetric and $Au = \lambda u$ with $\lambda$ real, then the quadratic form $\langle
Ax, x \rangle - \lambda \langle x, x \rangle$ takes the same value at $u - w$ as at $w$. -/
private theorem inner_sub_shift (hA : A.IsSymmetric) {lam : ℝ} (hu : A u = (lam : 𝕜) • u)
    (w : E) :
    inner 𝕜 (A (u - w)) (u - w) - (lam : 𝕜) * inner 𝕜 (u - w) (u - w)
      = inner 𝕜 (A w) w - (lam : 𝕜) * inner 𝕜 w w := by
  have h1 := inner_shift_add hA hu (-w) 1
  rw [show -w + (1 : 𝕜) • u = u - w by module] at h1
  rw [h1, inner_shift_neg]

/-- Let $A$ be a bounded operator on $E$, let $\lambda \in \mathbb{R}$ and let $x \in E$. Then
$$\left| \operatorname{Re} \langle Ax, x \rangle - \lambda \|x\|^2 \right| \le \|A - \lambda I\|
  \, \|x\|^2.$$

So a bounded $A$ satisfies the quadratic-form hypothesis of the Hermitian bounds with
$C = \|A - \lambda I\|$; the proof is Cauchy–Schwarz. As with $\gamma$, the bounds take $C$ as a
hypothesis instead of this operator norm, so that they apply to an unbounded $A$ and to a
sharper $C$. `Numlib.Eigen.MinMax` makes the same choice for Weyl's inequality. -/
theorem abs_re_inner_sub_le_opNorm (A : E →L[𝕜] E) (lam : ℝ) (x : E) :
    |RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2|
      ≤ ‖A - (lam : 𝕜) • (1 : E →L[𝕜] E)‖ * ‖x‖ ^ 2 := by
  have hx : inner 𝕜 ((A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x) x
      = inner 𝕜 (A x) x - (lam : 𝕜) * inner 𝕜 x x := by
    simp [inner_sub_left, inner_smul_left, RCLike.conj_ofReal]
  have hre : RCLike.re (inner 𝕜 ((A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x) x)
      = RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2 := by
    rw [hx, map_sub, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul,
      RCLike.ofReal_re]
  rw [← hre]
  calc |RCLike.re (inner 𝕜 ((A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x) x)|
      ≤ ‖inner 𝕜 ((A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x) x‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖(A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖A - (lam : 𝕜) • (1 : E →L[𝕜] E)‖ * ‖x‖) * ‖x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖A - (lam : 𝕜) • (1 : E →L[𝕜] E)‖ * ‖x‖ ^ 2 := by ring

end Krylov

namespace LinearMap.IsSymmetric

open Krylov

/-!
### The Hermitian bounds

For a symmetric $A$, the Ritz values are the max–min values of the Rayleigh quotient over the
subspaces of $K$; this is Courant–Fischer applied to the compression. The errors of the Ritz values
and of the Ritz vectors are controlled by the angle between the exact eigenvector and $K$.
-/

/-- Let $E$ be finite-dimensional, let $A$ be symmetric, and let $K$ be a subspace of dimension $m$.
For $0 \le i < m$, the $i$-th eigenvalue $\theta_i$ of the compression $A_K$, in decreasing
order, is the greatest element of the set of $c \in \mathbb{R}$ for which there is a subspace
$S \le K$ of dimension $i + 1$ with $c \le \rho_A(x)$ for all nonzero $x \in S$. That is,
$$\theta_i = \max_{S \le K, \ \dim S = i + 1} \ \inf_{x \in S, \ x \neq 0} \rho_A(x).$$
This is Proposition 4.4 of [saad2011numerical] (Courant–Fischer for the Ritz values).

It is Courant–Fischer for the compression, read back on $E$: the Rayleigh quotient of $A_K$ at
$y \in K$ is that of $A$ at $y$ (`Krylov.rayleighQuotient_compression`), and the subspaces of
$K$ correspond to the subspaces of the subtype under `Submodule.map K.subtype` and
`Submodule.comap K.subtype`. The statement uses `IsGreatest` over an explicit set of reals, as
`LinearMap.IsSymmetric.isGreatest_eigenvalues` does, because the `iSup` and `iInf` forms would
carry a junk value. -/
theorem isGreatest_eigenvalues_compression [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (K : Submodule 𝕜 E) {m : ℕ} (hm : Module.finrank 𝕜 K = m) (i : Fin m) :
    IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 E, S ≤ K ∧ Module.finrank 𝕜 S = (i : ℕ) + 1 ∧
        ∀ x ∈ S, x ≠ 0 → c ≤ A.rayleighQuotient x}
      ((compression.isSymmetric A K hA).eigenvalues hm i) := by
  obtain ⟨⟨S, hS, hb⟩, hub⟩ := (compression.isSymmetric A K hA).isGreatest_eigenvalues hm i
  constructor
  · refine ⟨S.map K.subtype, ?_, ?_, ?_⟩
    · rintro x ⟨y, -, rfl⟩
      exact y.2
    · rw [Submodule.finrank_map_subtype_eq, hS]
    · rintro x ⟨y, hy, rfl⟩ hx0
      rw [Submodule.subtype_apply, ← rayleighQuotient_compression A K y]
      exact hb y hy fun h => hx0 (by rw [h]; rfl)
  · rintro c ⟨T, hTK, hTdim, hTb⟩
    refine hub ⟨T.comap K.subtype, ?_, ?_⟩
    · rw [(Submodule.comapSubtypeEquivOfLe hTK).finrank_eq, hTdim]
    · intro y hy hy0
      rw [rayleighQuotient_compression A K y]
      exact hTb _ hy fun h => hy0 (Subtype.ext h)

/-- **Cauchy interlacing**, upper bound. Let $E$ have finite dimension $n$, let $A$ be symmetric,
and let $K$ be a subspace of dimension $m \le n$. For each $0 \le i < m$, the $i$-th Ritz value
is at most the $i$-th eigenvalue of $A$, both sorted decreasingly:
$$\theta_i \le \lambda_i.$$
This is Corollary 4.1 of [saad2011numerical].

The max–min that gives $\theta_i$ (`LinearMap.IsSymmetric.isGreatest_eigenvalues_compression`)
ranges over the $(i + 1)$-dimensional subspaces of $K$. The max–min that gives $\lambda_i$
(`LinearMap.IsSymmetric.isGreatest_eigenvalues`) ranges over all of them, so it has more
competitors. The hypothesis $m \le n$ only supplies the index cast; it follows from
`Submodule.finrank_le`. -/
theorem eigenvalues_compression_le [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (K : Submodule 𝕜 E) {n m : ℕ} (hn : Module.finrank 𝕜 E = n) (hm : Module.finrank 𝕜 K = m)
    (hmn : m ≤ n) (i : Fin m) :
    (compression.isSymmetric A K hA).eigenvalues hm i ≤ hA.eigenvalues hn (Fin.castLE hmn i) := by
  obtain ⟨⟨S, -, hS, hb⟩, -⟩ := hA.isGreatest_eigenvalues_compression K hm i
  exact (hA.isGreatest_eigenvalues hn (Fin.castLE hmn i)).2 ⟨S, hS, hb⟩

/-- **Cauchy interlacing**, lower bound. Let $E$ have finite dimension $n$, let $A$ be symmetric,
and let $K$ be a subspace of dimension $m \le n$. For each $0 \le i < m$,
$$\lambda_{i + (n - m)} \le \theta_i,$$
both families sorted decreasingly. At the last index $i = m - 1$ this is (5.67) of
[quarteroni2000numerical], $\lambda_m(H_m) \ge \lambda_n(A)$ in the 1-based notation of that
source.

This is the companion of `LinearMap.IsSymmetric.eigenvalues_compression_le`. It is the lower
half of `LinearMap.IsSymmetric.eigenvalues_restrict_interlace` for the compression, whose
Rayleigh quotient is that of $A$ (`Krylov.rayleighQuotient_compression`). -/
theorem eigenvalues_le_eigenvalues_compression [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (K : Submodule 𝕜 E) {n m : ℕ} (hn : Module.finrank 𝕜 E = n)
    (hm : Module.finrank 𝕜 K = m) (hmn : m ≤ n) (i : Fin m) :
    hA.eigenvalues hn ⟨(i : ℕ) + (n - m), by omega⟩
      ≤ (compression.isSymmetric A K hA).eigenvalues hm i :=
  (hA.eigenvalues_restrict_interlace hn (compression.isSymmetric A K hA) hm hmn
    (fun y => by rw [compression.inner_apply]) i).1

/-- **The Ritz values increase with the subspace.** Let $E$ be finite-dimensional, let $A$ be
symmetric, and let $K \le K'$ be subspaces of dimensions $m \le m'$. For each $0 \le i < m$, the
$i$-th Ritz value on $K$ is at most the $i$-th Ritz value on $K'$, both sorted decreasingly.
This is the mechanism behind the convergence of Davidson's method, Theorem 8.1 of
[saad2011numerical].

The proof uses `LinearMap.IsSymmetric.isGreatest_eigenvalues_compression` twice: the max–min for
$K$ ranges over the $(i + 1)$-dimensional subspaces of $K$, which are also subspaces of $K'$.
Cauchy interlacing `LinearMap.IsSymmetric.eigenvalues_compression_le` is the extreme case
$K' = E$. -/
theorem eigenvalues_compression_mono [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {K K' : Submodule 𝕜 E} (hKK' : K ≤ K') {m m' : ℕ} (hm : Module.finrank 𝕜 K = m)
    (hm' : Module.finrank 𝕜 K' = m') (hmm' : m ≤ m') (i : Fin m) :
    (compression.isSymmetric A K hA).eigenvalues hm i
      ≤ (compression.isSymmetric A K' hA).eigenvalues hm' (Fin.castLE hmm' i) := by
  obtain ⟨⟨S, hSK, hS, hb⟩, -⟩ := hA.isGreatest_eigenvalues_compression K hm i
  refine (hA.isGreatest_eigenvalues_compression K' hm' (Fin.castLE hmm' i)).2
    ⟨S, hSK.trans hKK', ?_, hb⟩
  simpa using hS

/-- Let $T$ be a symmetric operator on $E$, let $W$ be a subspace with an orthogonal projection
$P_W$, and let $\theta, \lambda, \delta \in \mathbb{R}$. Suppose that $Tq = \theta q$ for all
$q \in W$ and that $\delta \|z\| \le \|Tz - \lambda z\|$ for all $z \in W^\perp$. Then for every
$y \in E$,
$$\delta \, \|y - P_W y\| \le \|Ty - \lambda y\|.$$

The component of $y$ in $W$ contributes $(\theta - \lambda) P_W y$. This is orthogonal to the
contribution $(T - \lambda)(y - P_W y)$ of the other component, because $W$ is $T$-invariant and
$T$ is symmetric, so $W^\perp$ is $T$-invariant too. Pythagoras then discards the $W$ term. This
is the step of the eigenvector bound of [saad2011numerical] that turns a small residual into a
small angle to the eigenspace of the nearest Ritz value. -/
theorem mul_norm_sub_starProjection_le {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] {θ lam δ : ℝ} (hW : ∀ q ∈ W, T q = (θ : 𝕜) • q)
    (hδ : ∀ z ∈ Wᗮ, δ * ‖z‖ ≤ ‖T z - (lam : 𝕜) • z‖) (y : E) :
    δ * ‖y - W.starProjection y‖ ≤ ‖T y - (lam : 𝕜) • y‖ := by
  have hpW : W.starProjection y ∈ W := W.starProjection_apply_mem y
  have hyp : y - W.starProjection y ∈ Wᗮ := W.sub_starProjection_mem_orthogonal y
  have hinv : T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y) ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal]
    intro q hq
    have hqz : inner 𝕜 q (y - W.starProjection y) = (0 : 𝕜) :=
      (Submodule.mem_orthogonal W _).1 hyp q hq
    have h1 : inner 𝕜 q (T (y - W.starProjection y)) = (0 : 𝕜) := by
      rw [← hT q (y - W.starProjection y), hW q hq, inner_smul_left, hqz, mul_zero]
    rw [inner_sub_right, inner_smul_right, h1, hqz, mul_zero, sub_zero]
  have hsplit : T y - (lam : 𝕜) • y
      = ((θ : 𝕜) - (lam : 𝕜)) • W.starProjection y
        + (T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y)) := by
    rw [map_sub, hW _ hpW, sub_smul]
    module
  have horth : inner 𝕜 (((θ : 𝕜) - (lam : 𝕜)) • W.starProjection y)
      (T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y)) = (0 : 𝕜) :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.smul_mem _ _ hpW) hinv
  have hnorm : ‖T y - (lam : 𝕜) • y‖ ^ 2
      = ‖((θ : 𝕜) - (lam : 𝕜)) • W.starProjection y‖ ^ 2
        + ‖T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y)‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hlow := hδ _ hyp
  nlinarith [norm_nonneg (T y - (lam : 𝕜) • y),
    norm_nonneg (T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y)),
    sq_nonneg ‖((θ : 𝕜) - (lam : 𝕜)) • W.starProjection y‖,
    norm_nonneg (y - W.starProjection y)]

/-- Let $E$ have finite dimension $n$, let $T$ be symmetric with eigenvalues
$\mu_0, \dots, \mu_{n-1}$, and let $\theta, \lambda, \delta \in \mathbb{R}$ with $\delta \ge 0$.
Suppose that $\delta \le |\mu_i - \lambda|$ for every $i$ with $\mu_i \neq \theta$. Then every
$z$ orthogonal to the eigenspace $\ker(T - \theta)$ satisfies
$$\delta \, \|z\| \le \|Tz - \lambda z\|.$$

This gives the lower bound that `LinearMap.IsSymmetric.mul_norm_sub_starProjection_le` needs. In
an eigenvector basis, $(T - \lambda) z$ has the coordinates $(\mu_i - \lambda) c_i$, and
$z \perp \ker(T - \theta)$ removes the coordinates with $\mu_i = \theta$. For $T = A_K$ this
identifies the $\delta$ of [saad2011numerical]: the distance from the exact eigenvalue $\lambda$
to the Ritz values other than $\theta$. -/
theorem mul_norm_le_norm_sub_smul [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {θ lam δ : ℝ} (hδ0 : 0 ≤ δ)
    (hsep : ∀ i : Fin n, hT.eigenvalues hn i ≠ θ → δ ≤ |hT.eigenvalues hn i - lam|)
    {z : E} (hz : z ∈ (Module.End.eigenspace T (θ : 𝕜))ᗮ) :
    δ * ‖z‖ ≤ ‖T z - (lam : 𝕜) • z‖ := by
  have hrepr : ∀ i, ‖(hT.eigenvectorBasis hn).repr (T z - (lam : 𝕜) • z) i‖
      = |hT.eigenvalues hn i - lam| * ‖(hT.eigenvectorBasis hn).repr z i‖ := by
    intro i
    have h1 : (hT.eigenvectorBasis hn).repr (T z - (lam : 𝕜) • z) i
        = ((hT.eigenvalues hn i - lam : ℝ) : 𝕜) * (hT.eigenvectorBasis hn).repr z i := by
      rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, inner_sub_right,
        inner_smul_right, ← hT (hT.eigenvectorBasis hn i) z, hT.apply_eigenvectorBasis,
        inner_smul_left, RCLike.conj_ofReal, RCLike.ofReal_sub]
      ring
    rw [h1, norm_mul, RCLike.norm_ofReal]
  have hzero : ∀ i, hT.eigenvalues hn i = θ → (hT.eigenvectorBasis hn).repr z i = 0 := by
    intro i hi
    have hbi : hT.eigenvectorBasis hn i ∈ Module.End.eigenspace T (θ : 𝕜) :=
      Module.End.mem_eigenspace_iff.2 (by rw [hT.apply_eigenvectorBasis, hi])
    rw [OrthonormalBasis.repr_apply_apply]
    exact (Submodule.mem_orthogonal _ z).1 hz _ hbi
  have hsq : (δ * ‖z‖) ^ 2 ≤ ‖T z - (lam : 𝕜) • z‖ ^ 2 := by
    rw [mul_pow, hT.norm_sq_eq_sum_norm_repr_sq hn z,
      hT.norm_sq_eq_sum_norm_repr_sq hn (T z - (lam : 𝕜) • z), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hrepr i, mul_pow]
    by_cases hi : hT.eigenvalues hn i = θ
    · rw [hzero i hi]
      simp
    · have h := hsep i hi
      have hsq2 : δ ^ 2 ≤ |hT.eigenvalues hn i - lam| ^ 2 := by nlinarith [h, hδ0]
      exact mul_le_mul_of_nonneg_right hsq2 (sq_nonneg _)
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- Let $A$ be symmetric, and let $\lambda, C \in \mathbb{R}$ satisfy $|\operatorname{Re} \langle
Ax, x \rangle - \lambda \|x\|^2| \le C \|x\|^2$ for all $x \in E$. If $Au = \lambda u$ and
$y \neq 0$, then
$$|\lambda - \rho_A(y)| \le C \left( \frac{\|u - y\|}{\|y\|} \right)^2.$$
This is Lemma 4.2 of [saad2011numerical]; Lemma 4.1 is the case $y = P_K u$.

The quadratic form of $A - \lambda$ has $u$ in its kernel and is symmetric, so it takes the same
value at $y$ as at $u - y$: $\langle (A - \lambda) y, y \rangle = \langle (A - \lambda)(u - y),
u - y \rangle$. Division by $\|y\|^2$ gives the ratio. Nothing here is special to a projection:
the Rayleigh–Ritz eigenvalue analysis applies this lemma to a competitor chosen in the
approximation space. -/
theorem abs_sub_rayleighQuotient_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {lam C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u : E} (hu : A u = (lam : 𝕜) • u) {y : E} (hy : y ≠ 0) :
    |lam - A.rayleighQuotient y| ≤ C * (‖u - y‖ / ‖y‖) ^ 2 := by
  have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hvpos : (0 : ℝ) < ‖y‖ ^ 2 := by positivity
  have key : RCLike.re (inner 𝕜 (A y) y) - lam * ‖y‖ ^ 2
      = RCLike.re (inner 𝕜 (A (u - y)) (u - y)) - lam * ‖u - y‖ ^ 2 := by
    rw [← re_inner_sub A lam y, ← re_inner_sub A lam (u - y), inner_sub_shift hA hu y]
  have hrw : lam - A.rayleighQuotient y
      = (lam * ‖y‖ ^ 2 - RCLike.re (inner 𝕜 (A y) y)) / ‖y‖ ^ 2 := by
    rw [LinearMap.rayleighQuotient, sub_div, mul_div_assoc, div_self (ne_of_gt hvpos), mul_one]
  have hcancel : C * (‖u - y‖ / ‖y‖) ^ 2 * ‖y‖ ^ 2 = C * ‖u - y‖ ^ 2 := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hvpos, div_le_iff₀ hvpos, hcancel, abs_sub_comm, key]
  exact hC _

/-- Let $A$ be symmetric, let $K$ be a subspace with an orthogonal projection $P_K$, and let
$\lambda, C \in \mathbb{R}$ satisfy $|\operatorname{Re} \langle Ax, x \rangle - \lambda \|x\|^2|
\le C \|x\|^2$ for all $x \in E$. If $Au = \lambda u$ and $P_K u \neq 0$, then
$$|\lambda - \rho_A(P_K u)| \le C \tan^2 \angle(u, K).$$
This is Lemma 4.1 of [saad2011numerical].

The identity behind it is $(A - \lambda) P_K u = -(A - \lambda)(I - P_K) u$. Since $A - \lambda$
is symmetric and $(A - \lambda) u = 0$, it gives $\langle (A - \lambda) P_K u, P_K u \rangle =
\langle (A - \lambda)(I - P_K) u, (I - P_K) u \rangle$, and division by $\|P_K u\|^2$ gives
$\tan^2 \angle(u, K)$. The hypothesis $P_K u \neq 0$ is necessary, not only because
`Submodule.tanAngle` has the junk value $0$ there: for $u \perp K$ the left-hand side is
$|\lambda|$ and the right-hand side is $0$. -/
theorem abs_sub_rayleighQuotient_starProjection_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] {lam C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u : E} (hu : A u = (lam : 𝕜) • u) (hPu : K.starProjection u ≠ 0) :
    |lam - A.rayleighQuotient (K.starProjection u)| ≤ C * K.tanAngle u ^ 2 := by
  have h := hA.abs_sub_rayleighQuotient_le hC hu hPu
  rwa [← K.tanAngle_mul_norm hPu, mul_div_assoc, div_self (norm_ne_zero_iff.2 hPu), mul_one] at h

/-- Let $E$ have finite dimension $n + 1$, let $A$ be symmetric with largest eigenvalue $\lambda_0$,
and let $K$ be a subspace of dimension $m + 1$ with largest Ritz value $\theta_0$, the largest
eigenvalue of $A_K$. Let $C \in \mathbb{R}$ satisfy $|\operatorname{Re} \langle Ax, x \rangle -
\lambda_0 \|x\|^2| \le C \|x\|^2$ for all $x \in E$. If $Au = \lambda_0 u$ and $P_K u \neq 0$,
then
$$0 \le \lambda_0 - \theta_0 \le C \tan^2 \angle(u, K).$$
This is Theorem 4.5 of [saad2011numerical] for the largest eigenvalue.

The lower bound is `LinearMap.IsSymmetric.eigenvalues_compression_le` at $i = 0$. For the upper
bound, $P_K u$ is a nonzero element of $K$, so $\rho_A(P_K u) \le \theta_0$, and
`LinearMap.IsSymmetric.abs_sub_rayleighQuotient_starProjection_le` bounds
$\lambda_0 - \rho_A(P_K u)$. So a subspace at a small angle to $u$ carries a Ritz value close to
$\lambda_0$, with an error quadratic in the angle. -/
theorem ritz_value_error_le [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {K : Submodule 𝕜 E} {n m : ℕ} (hn : Module.finrank 𝕜 E = n + 1)
    (hm : Module.finrank 𝕜 K = m + 1) {C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x) - hA.eigenvalues hn 0 * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u : E} (hu : A u = ((hA.eigenvalues hn 0 : ℝ) : 𝕜) • u) (hPu : K.starProjection u ≠ 0) :
    hA.eigenvalues hn 0 - (compression.isSymmetric A K hA).eigenvalues hm 0
      ∈ Set.Icc 0 (C * K.tanAngle u ^ 2) := by
  have hmn : m + 1 ≤ n + 1 := by
    have h := Submodule.finrank_le (R := 𝕜) K
    rw [hm, hn] at h
    exact h
  have hz : Fin.castLE hmn (0 : Fin (m + 1)) = (0 : Fin (n + 1)) := by ext; simp
  have hycoe : ((K.orthogonalProjectionOnto u : K) : E) = K.starProjection u := rfl
  have hy0 : (K.orthogonalProjectionOnto u : K) ≠ 0 := fun h => hPu (by rw [← hycoe, h]; rfl)
  have h1 : A.rayleighQuotient (K.starProjection u)
      ≤ (compression.isSymmetric A K hA).eigenvalues hm 0 := by
    have h := ((compression.isSymmetric A K hA).rayleighQuotient_mem_Icc hm hy0).2
    rwa [rayleighQuotient_compression A K _, hycoe] at h
  have h2 := (abs_le.1 (hA.abs_sub_rayleighQuotient_starProjection_le K hC hu hPu)).2
  have h3 := hA.eigenvalues_compression_le K hn hm hmn 0
  rw [hz] at h3
  exact ⟨by linarith, by linarith⟩

/-- Let $E$ have finite dimension $n$, let $A$ be symmetric with eigenvalues
$\lambda_0 \ge \dots \ge \lambda_{n-1}$, and let $K$ be a subspace of dimension $m \le n$. Let
$\theta_0 \ge \dots \ge \theta_{m-1}$ be the eigenvalues of the compression $A_K$, with
orthonormal eigenvectors $\tilde u_0, \dots, \tilde u_{m-1}$. Fix $0 \le i < m$, let
$C \in \mathbb{R}$ satisfy $|\operatorname{Re} \langle Ax, x \rangle - \lambda_i \|x\|^2| \le C
\|x\|^2$ for all $x \in E$, and let $Au = \lambda_i u$. If $y \in K$ is nonzero and
$\langle \tilde u_j, y \rangle = 0$ for all $j < i$, then
$$0 \le \lambda_i - \theta_i \le C \left( \frac{\|u - y\|}{\|y\|} \right)^2.$$
This is Theorem 4.5 of [saad2011numerical].

The eigenvectors $\tilde u_j$ are `LinearMap.IsSymmetric.eigenvectorBasis` of the compression.
The lower bound is Cauchy interlacing. For the upper bound, $y$ is a competitor in Rayleigh's
recursive characterization of $\theta_i$
(`LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal`), so $\rho_A(y) \le \theta_i$,
and `LinearMap.IsSymmetric.abs_sub_rayleighQuotient_le` bounds $\lambda_i - \rho_A(y)$.
`LinearMap.IsSymmetric.ritz_value_error_le` is the case $i = 0$, where the orthogonality
condition is empty and $y = P_K u$ is the natural competitor. The display of the source is the
case $y = P_K u_i - P_W u_i$, with $W$ the span of the Ritz vectors already computed:
`Submodule.norm_sub_sub_starProjection_sq` evaluates the numerator there as
$\|(I - P_K) u_i\|^2 + \|P_W u_i\|^2$, which is the $\|(I - P_K) u_i\|^2 + \|\tilde Q_i u_i\|^2$
of the source. -/
theorem ritz_value_error_le_of_forall_inner_eq_zero [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {K : Submodule 𝕜 E} {n m : ℕ}
    (hn : Module.finrank 𝕜 E = n) (hm : Module.finrank 𝕜 K = m) (hmn : m ≤ n) (i : Fin m)
    {C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x)
      - hA.eigenvalues hn (Fin.castLE hmn i) * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u : E} (hu : A u = ((hA.eigenvalues hn (Fin.castLE hmn i) : ℝ) : 𝕜) • u)
    {y : E} (hyK : y ∈ K) (hy0 : y ≠ 0)
    (hyorth : ∀ j : Fin m, j < i →
      inner 𝕜 ((((compression.isSymmetric A K hA).eigenvectorBasis hm j : K) : E)) y = (0 : 𝕜)) :
    hA.eigenvalues hn (Fin.castLE hmn i) - (compression.isSymmetric A K hA).eigenvalues hm i
      ∈ Set.Icc 0 (C * (‖u - y‖ / ‖y‖) ^ 2) := by
  have hysub : (⟨y, hyK⟩ : K) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have h1 : A.rayleighQuotient y ≤ (compression.isSymmetric A K hA).eigenvalues hm i := by
    have hmem := ((compression.isSymmetric A K hA).isGreatest_rayleighQuotient_orthogonal hm i).2
      ⟨⟨y, hyK⟩, hysub, fun j hj => hyorth j hj, rfl⟩
    rwa [rayleighQuotient_compression A K ⟨y, hyK⟩] at hmem
  have h2 := (abs_le.1 (hA.abs_sub_rayleighQuotient_le hC hu hy0)).2
  have h3 := hA.eigenvalues_compression_le K hn hm hmn i
  exact ⟨by linarith, by linarith⟩

/-- Let $A$ be symmetric, let $K$ be a finite-dimensional subspace, and let
$\gamma, \delta, \theta, \lambda \in \mathbb{R}$ with $\delta > 0$. Suppose that
$\|P_K A x\| \le \gamma \|x\|$ for all $x \in K^\perp$, that $\theta$ is an eigenvalue of the
compression $A_K$, and that $\delta \|z\| \le \|A_K z - \lambda z\|$ for every $z \in K$
orthogonal to the $\theta$-eigenspace of $A_K$. If $Au = \lambda u$ and $u \neq 0$, then there
is a Ritz pair $(\theta, w)$ of $A$ on $K$ with
$$\sin \angle(u, w) \le \sqrt{1 + \gamma^2 / \delta^2} \, \sin \angle(u, K).$$
This is Theorem 4.6 of [saad2011numerical].

By `LinearMap.IsSymmetric.mul_norm_le_norm_sub_smul`, the hypothesis on $\delta$ follows from
the separation of $\lambda$ from the Ritz values other than $\theta$. So a subspace at a small
angle to an eigenvector contains a Ritz vector at a comparably small angle to it, if the Ritz
value is well separated. The angle $\angle(u, w)$ is `(𝕜 ∙ w).sinAngle u`. The Ritz vector
produced is the projection $w$ of $P_K u$ onto the $\theta$-eigenspace of $A_K$, for which the
projection of $u$ onto $\mathbb{K} w$ is $w$. Then $\|u - w\|^2$ splits by Pythagoras into
$\|u - P_K u\|^2$ and $\|P_K u - w\|^2$, and the residual bound with the separation bound
controls the second by $(\gamma / \delta) \|u - P_K u\|$. Where that projection vanishes, the
inequality is vacuous because its right-hand side is at least $1$, and any Ritz vector for
$\theta$ serves. This is why the statement is an existence statement, and why $\theta$ is
assumed to be a Ritz value. -/
theorem sin_angle_ritzVector_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {K : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K] {γ δ θ lam : ℝ} (hδ0 : 0 < δ)
    (hγ : ∀ x ∈ Kᗮ, ‖K.starProjection (A x)‖ ≤ γ * ‖x‖)
    (hθ : Module.End.HasEigenvalue (compression A K) (θ : 𝕜))
    (hδ : ∀ z ∈ (Module.End.eigenspace (compression A K) (θ : 𝕜))ᗮ,
      δ * ‖z‖ ≤ ‖compression A K z - (lam : 𝕜) • z‖)
    {u : E} (hu : A u = (lam : 𝕜) • u) (hu0 : u ≠ 0) :
    ∃ w : E, IsRitzPair A K (θ : 𝕜) w ∧
      (𝕜 ∙ w).sinAngle u ≤ Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u := by
  have hupos : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hR : (0 : ℝ) ≤ 1 + γ ^ 2 / δ ^ 2 := by positivity
  have hres : ‖compression A K (K.orthogonalProjectionOnto u)
      - (lam : 𝕜) • K.orthogonalProjectionOnto u‖ ≤ γ * ‖u - K.starProjection u‖ := by
    have h := compression_residual_le hγ hu
    have hcast : (compression A K (K.orthogonalProjectionOnto u) : E)
        - (lam : 𝕜) • ((K.orthogonalProjectionOnto u : K) : E)
        = ((compression A K (K.orthogonalProjectionOnto u)
          - (lam : 𝕜) • K.orthogonalProjectionOnto u : K) : E) := rfl
    rw [hcast, Submodule.norm_coe] at h
    exact h
  have haux := (compression.isSymmetric A K hA).mul_norm_sub_starProjection_le
    (W := Module.End.eigenspace (compression A K) (θ : 𝕜)) (θ := θ) (lam := lam) (δ := δ)
    (fun _q hq => Module.End.mem_eigenspace_iff.1 hq) hδ (K.orthogonalProjectionOnto u)
  set W := Module.End.eigenspace (compression A K) (θ : 𝕜) with hWdef
  set y : K := K.orthogonalProjectionOnto u with hydef
  set p : K := W.starProjection y with hpdef
  have hsqkey : ‖y - p‖ ^ 2 * δ ^ 2 ≤ γ ^ 2 * ‖u - K.starProjection u‖ ^ 2 := by
    nlinarith [mul_nonneg hδ0.le (norm_nonneg (y - p)), norm_nonneg (y - p),
      norm_nonneg (u - K.starProjection u)]
  have hsin : K.sinAngle u * ‖u‖ = ‖u - K.starProjection u‖ := K.sinAngle_mul_norm u
  have hcoe : ‖y - p‖ = ‖K.starProjection u - (p : E)‖ := by
    rw [← Submodule.norm_coe (y - p)]
    rfl
  have hdiv : ‖K.starProjection u - (p : E)‖ ^ 2
      ≤ γ ^ 2 / δ ^ 2 * ‖u - K.starProjection u‖ ^ 2 := by
    rw [← hcoe, div_mul_eq_mul_div, le_div_iff₀ hδ2]
    exact hsqkey
  have hnn : 0 ≤ Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u :=
    mul_nonneg (Real.sqrt_nonneg _) (Submodule.sinAngle_nonneg K u)
  have hprod : (Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u) ^ 2
      = (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR]
  rcases eq_or_ne p 0 with hp0 | hp0
  · obtain ⟨q, hq⟩ := hθ.exists_hasEigenvector
    refine ⟨(q : E), isRitzPair_of_hasEigenvector A K (θ : 𝕜) hq,
      (Submodule.sinAngle_le_one _ _).trans ?_⟩
    have hpy : ‖K.starProjection u‖ ^ 2 + ‖u - K.starProjection u‖ ^ 2 = ‖u‖ ^ 2 :=
      K.norm_starProjection_sq_add_norm_sub_sq u
    have h0 : ‖K.starProjection u - (p : E)‖ = ‖K.starProjection u‖ := by
      rw [hp0]
      simp
    have h1 : (1 : ℝ) ≤ (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u ^ 2 := by
      have e2 : K.sinAngle u ^ 2 * ‖u‖ ^ 2 = ‖u - K.starProjection u‖ ^ 2 := by
        rw [← mul_pow, hsin]
      rw [h0] at hdiv
      nlinarith [hdiv, hpy, e2, hupos]
    refine le_of_sq_le_sq ?_ hnn
    rw [one_pow, hprod]
    exact h1
  · have hpW : p ∈ W := W.starProjection_apply_mem y
    refine ⟨(p : E), isRitzPair_of_hasEigenvector A K (θ : 𝕜) ⟨hpW, hp0⟩, ?_⟩
    have hyE : ((y : K) : E) = K.starProjection u := rfl
    have hyperp : y - p ∈ Wᗮ := W.sub_starProjection_mem_orthogonal y
    have hpy : inner 𝕜 p y = inner 𝕜 p p := by
      have h := Submodule.inner_right_of_mem_orthogonal hpW hyperp
      rw [inner_sub_right, sub_eq_zero] at h
      exact h
    have hinner : inner 𝕜 ((p : K) : E) u = inner 𝕜 ((p : K) : E) ((p : K) : E) := by
      have h := Submodule.inner_right_of_mem_orthogonal p.2 (K.sub_starProjection_mem_orthogonal u)
      rw [inner_sub_right, sub_eq_zero] at h
      rw [h, ← hyE]
      simp only [← Submodule.coe_inner]
      exact hpy
    have hproj : (𝕜 ∙ ((p : K) : E)).starProjection u = ((p : K) : E) :=
      Submodule.starProjection_span_singleton_eq_self hinner
    have hnormeq : (𝕜 ∙ ((p : K) : E)).sinAngle u * ‖u‖ = ‖u - ((p : K) : E)‖ := by
      rw [Submodule.sinAngle_mul_norm, hproj]
    have hpyth : ‖u - ((p : K) : E)‖ ^ 2
        = ‖u - K.starProjection u‖ ^ 2 + ‖K.starProjection u - ((p : K) : E)‖ ^ 2 :=
      K.norm_sub_sq_eq_add_of_mem u p.2
    have hsqle : (𝕜 ∙ ((p : K) : E)).sinAngle u ^ 2
        ≤ (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u ^ 2 := by
      have e1 : (𝕜 ∙ ((p : K) : E)).sinAngle u ^ 2 * ‖u‖ ^ 2 = ‖u - ((p : K) : E)‖ ^ 2 := by
        rw [← mul_pow, hnormeq]
      have e2 : K.sinAngle u ^ 2 * ‖u‖ ^ 2 = ‖u - K.starProjection u‖ ^ 2 := by
        rw [← mul_pow, hsin]
      nlinarith [hdiv, e1, e2, hupos, hpyth]
    have hb : (𝕜 ∙ ((p : K) : E)).sinAngle u ^ 2
        ≤ (Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u) ^ 2 := by
      rw [hprod]
      exact hsqle
    exact le_of_sq_le_sq hb hnn

/-- Let $A$ be symmetric, let $K$ be a subspace, and let $\lambda, C \in \mathbb{R}$ satisfy
$|\operatorname{Re} \langle Ax, x \rangle - \lambda \|x\|^2| \le C \|x\|^2$ for all $x \in E$.
If $Au = \lambda u$ with $u \neq 0$, and $(\theta, w)$ is a Ritz pair of $A$ on $K$ with
$\theta$ real, then
$$|\theta - \lambda| \le C \sin^2 \angle(u, w).$$
This is Proposition 4.5 of [saad2011numerical].

So the Ritz value is accurate to second order in the angle between the Ritz vector and the
eigenvector, which is why a Rayleigh–Ritz eigenvalue is much more accurate than its eigenvector.
The angle $\angle(u, w)$ is `(𝕜 ∙ w).sinAngle u`. The proof is the one of
`LinearMap.IsSymmetric.abs_sub_rayleighQuotient_starProjection_le`: the quadratic form of
$A - \lambda$ does not change when a multiple of $u$ is subtracted, so
$(\theta - \lambda) \|w\|^2$ can be evaluated at the component of $w$ orthogonal to $u$, whose
norm is $\sin \angle(u, w) \, \|w\|$. With `LinearMap.IsSymmetric.sin_angle_ritzVector_le` this
gives $|\theta - \lambda| \le C (1 + \gamma^2 / \delta^2) \sin^2 \angle(u, K)$. -/
theorem abs_ritz_value_sub_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {K : Submodule 𝕜 E}
    {lam C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u w : E} (hu : A u = (lam : 𝕜) • u) (hu0 : u ≠ 0) {θ : ℝ}
    (h : IsRitzPair A K (θ : 𝕜) w) :
    |θ - lam| ≤ C * (𝕜 ∙ w).sinAngle u ^ 2 := by
  have hw0 : w ≠ 0 := h.ne_zero
  have hwpos : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
  rw [← Submodule.sinAngle_span_singleton_comm hu0 hw0]
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, c • u = (𝕜 ∙ u).starProjection w :=
    Submodule.mem_span_singleton.1 ((𝕜 ∙ u).starProjection_apply_mem w)
  have hxnorm : ‖w - (𝕜 ∙ u).starProjection w‖ = (𝕜 ∙ u).sinAngle w * ‖w‖ :=
    ((𝕜 ∙ u).sinAngle_mul_norm w).symm
  have hQ : RCLike.re (inner 𝕜 (A (w - (𝕜 ∙ u).starProjection w)) (w - (𝕜 ∙ u).starProjection w))
      - lam * ‖w - (𝕜 ∙ u).starProjection w‖ ^ 2
      = RCLike.re (inner 𝕜 (A w) w) - lam * ‖w‖ ^ 2 := by
    rw [← re_inner_sub A lam (w - (𝕜 ∙ u).starProjection w), ← re_inner_sub A lam w, ← hc,
      show w - c • u = w + (-c) • u by module, inner_shift_add hA hu w (-c)]
  have hQw : RCLike.re (inner 𝕜 (A w) w) - lam * ‖w‖ ^ 2 = (θ - lam) * ‖w‖ ^ 2 := by
    rw [h.re_inner_apply_self, RCLike.ofReal_re]
    ring
  have hbound := hC (w - (𝕜 ∙ u).starProjection w)
  rw [hQ, hQw, abs_mul, abs_of_pos hwpos, hxnorm, mul_pow] at hbound
  refine le_of_mul_le_mul_right ?_ hwpos
  calc |θ - lam| * ‖w‖ ^ 2 ≤ C * ((𝕜 ∙ u).sinAngle w ^ 2 * ‖w‖ ^ 2) := hbound
    _ = C * (𝕜 ∙ u).sinAngle w ^ 2 * ‖w‖ ^ 2 := by ring

end LinearMap.IsSymmetric

namespace Arnoldi

open Krylov

variable (A : E →ₗ[𝕜] E) (b : E)

/-! ### Optimality of the characteristic polynomial of the Hessenberg matrix -/

/-- A vector orthogonal to the Arnoldi vectors $v_0, \dots, v_{m-1}$ is orthogonal to the Krylov
subspace $\mathcal{K}_m(A, b)$. -/
private theorem mem_orthogonal_of_forall_inner_vec {m : ℕ} {x : E}
    (h : ∀ i < m, inner 𝕜 (vec A b i) x = (0 : 𝕜)) : x ∈ (subspace A b m)ᗮ := by
  rw [← span_vec]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem y hy => obtain ⟨i, hi, rfl⟩ := hy; exact h i hi
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]

section Charpoly

variable [FiniteDimensional 𝕜 (fullSubspace A b)]

/-- Let the Krylov space of $A$ and $b$ be finite-dimensional, and let $m$ be at most the grade of
$b$ with respect to $A$. Let $p$ be the characteristic polynomial of the compression of $A$ to
$\mathcal{K}_m(A, b)$. Then
$$p(A) \, b \perp \mathcal{K}_m(A, b).$$

This is Cayley–Hamilton for the compression, $p(A_K) b = 0$, read back on $E$ through
`compressionBy.apply_aeval_of_forall_pow_lt_mem`. That lemma needs the Krylov vectors only up to
$A^{m-1} b$, so $\mathcal{K}_m(A, b)$ need not be $A$-invariant. -/
theorem aeval_charpoly_mem_orthogonal {m : ℕ} (hm : m ≤ grade A b) :
    aeval A (LinearMap.charpoly (compression A (subspace A b m))) b ∈ (subspace A b m)ᗮ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
    rw [subspace_zero, Submodule.mem_bot] at hw
    rw [hw, inner_zero_left]
  have hdeg : (LinearMap.charpoly (compression A (subspace A b m))).natDegree = m := by
    rw [LinearMap.charpoly_natDegree, finrank_subspace, min_eq_left hm]
  have hb : b ∈ subspace A b m := self_mem_subspace A b hm0
  have h := compressionBy.apply_aeval_of_forall_pow_lt_mem
    ((subspace A b m).orthogonalProjectionOnto : E →ₗ[𝕜] subspace A b m)
    (subspace A b m).orthogonalProjectionOnto_mem_subspace_eq_self A
    (LinearMap.charpoly (compression A (subspace A b m)))
    (x := ⟨b, hb⟩) fun i hi => pow_apply_mem_subspace A b (hdeg ▸ hi)
  rw [← compression.eq_compressionBy, LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at h
  rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
  exact h

/-- Let the Krylov space of $A$ and $b$ be finite-dimensional, let $m$ be at most the grade of $b$
with respect to $A$, and let $c$ be the characteristic polynomial of the compression of $A$ to
$\mathcal{K}_m(A, b)$. Then for every monic polynomial $p$ of degree $m$,
$$\|c(A) \, b\| \le \|p(A) \, b\|.$$
This is Theorem 6.1 of [saad2011numerical].

By `Arnoldi.hessenbergSq_eq_toMatrix_compression`, $c$ is also the characteristic polynomial of
the Arnoldi matrix $H_m$. The proof is a best-approximation argument in $\mathcal{K}_m$:
$c(A) b \perp \mathcal{K}_m$ by `Arnoldi.aeval_charpoly_mem_orthogonal`, while a monic $p$ of
degree $m$ differs from $c$ by a polynomial of degree less than $m$, so
$p(A) b - c(A) b \in \mathcal{K}_m$. Pythagoras then gives the inequality. It holds up to and
including $m$ equal to the grade, where the minimum value is $0$. The source leaves the
hypothesis on $m$ implicit: it speaks of the characteristic polynomial of $V_m^H A V_m$ for an
orthonormal basis $V_m$ of $\mathcal{K}_m$ with $m$ columns, and that basis exists exactly when
$\dim \mathcal{K}_m = m$, that is, when $m$ is at most the grade. The hypothesis is needed here
for the same reason: the degree of the characteristic polynomial is $\dim \mathcal{K}_m$, and
past the grade the competitors include polynomials of a degree that the compression cannot
reach. -/
theorem charpoly_compression_isMinOn {m : ℕ} (hm : m ≤ grade A b) :
    IsMinOn (fun p : 𝕜[X] => ‖aeval A p b‖) {p : 𝕜[X] | p.Monic ∧ p.natDegree = m}
      (LinearMap.charpoly (compression A (subspace A b m))) := by
  set c := LinearMap.charpoly (compression A (subspace A b m)) with hc
  have hcm : c.Monic := LinearMap.charpoly_monic _
  have hcd : c.natDegree = m := by
    rw [hc, LinearMap.charpoly_natDegree, finrank_subspace, min_eq_left hm]
  refine isMinOn_iff.2 fun p hp => ?_
  obtain ⟨hpm, hpd⟩ := hp
  have hdegp : p.degree = (m : ℕ) := hpd ▸ degree_eq_natDegree hpm.ne_zero
  have hdegc : c.degree = (m : ℕ) := hcd ▸ degree_eq_natDegree hcm.ne_zero
  have hlt : (p - c).degree < (m : ℕ) := by
    rw [← hdegp]
    exact degree_sub_lt_left (hdegp.trans hdegc.symm) hpm.ne_zero
      (by rw [hpm.leadingCoeff, hcm.leadingCoeff])
  have hmem : aeval A (p - c) b ∈ subspace A b m := aeval_apply_mem_subspace A b hlt
  have hsplit : aeval A p b = aeval A c b + aeval A (p - c) b := by
    rw [map_sub, LinearMap.sub_apply]
    abel
  have hpyth : ‖aeval A p b‖ ^ 2 = ‖aeval A c b‖ ^ 2 + ‖aeval A (p - c) b‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_left_of_mem_orthogonal hmem (aeval_charpoly_mem_orthogonal A b hm))
  exact le_of_sq_le_sq (by nlinarith) (norm_nonneg _)

end Charpoly

/-! ### The cheap Arnoldi residual -/

/-- Below the grade, the coordinates of $V_m y = \sum_{j < m} y_j v_j$ in the Arnoldi vectors are
$\langle v_i, V_m y \rangle = y_i$. -/
private theorem inner_vec_sum [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) (y : Fin m → 𝕜) (i : Fin m) :
    inner 𝕜 (vec A b i) (∑ j, y j • vec A b j) = y i := by
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      norm_vec_eq_one_of_lt_grade A b (i.2.trans_le hm)]
    simp
  · intro j _ hj
    rw [inner_smul_right, inner_vec_eq_zero A b fun h => hj (Fin.val_injective h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The Hessenberg matrix is the matrix of $A$ in the Arnoldi coordinates:
$\langle v_i, A V_m y \rangle = (H_m y)_i$. -/
private theorem inner_vec_apply_sum {m : ℕ} (y : Fin m → 𝕜) (i : Fin m) :
    inner 𝕜 (vec A b i) (A (∑ j, y j • vec A b j))
      = (hessenbergSq A b m).mulVec y i := by
  rw [map_sum, inner_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, hessenbergSq, Matrix.of_apply, coeff, mul_comm]

/-- Let the Krylov space of $A$ and $b$ be finite-dimensional, let $m$ be at most the grade of $b$
with respect to $A$, and let $y \in \mathbb{K}^m$ be nonzero with $H_m y = \theta y$. Then
$(\theta, V_m y)$ is a Ritz pair of $A$ on $\mathcal{K}_m(A, b)$, where
$V_m y = \sum_{j < m} y_j v_j$. This follows [saad2011numerical].

This is the Rayleigh–Ritz condition tested against the Arnoldi vectors. They span
$\mathcal{K}_m$ and, below the grade, are orthonormal, so that
$\langle v_i, V_m y \rangle = y_i$ and $\langle v_i, A V_m y \rangle = (H_m y)_i$. It makes the
residual formula `Arnoldi.norm_ritz_residual_eq` a statement about Ritz pairs. -/
theorem isRitzPair_of_mulVec_eq_smul [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) {y : Fin m → 𝕜} (hy0 : y ≠ 0) {θ : 𝕜}
    (h : (hessenbergSq A b m).mulVec y = θ • y) :
    IsRitzPair A (subspace A b m) θ (∑ j, y j • vec A b j) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
  refine ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (vec_mem_subspace_of_lt A b j.2),
    fun h0 => hi ?_, mem_orthogonal_of_forall_inner_vec A b fun k hk => ?_⟩
  · rw [← inner_vec_sum A b hm y i, h0, inner_zero_right]
    rfl
  · rw [inner_sub_right, inner_smul_right, inner_vec_apply_sum A b y ⟨k, hk⟩,
      inner_vec_sum A b hm y ⟨k, hk⟩, h]
    simp

/-- The last row of the rectangular Hessenberg matrix $\bar H_{m+1}$ has a single nonzero entry: the
last entry of $\bar H_{m+1} y$ is $h_{m+1,m} \, y_m$. -/
private theorem hessenberg_mulVec_last (m : ℕ) (y : Fin (m + 1) → 𝕜) :
    (hessenberg A b (m + 1)).mulVec y (Fin.last (m + 1))
      = coeff A b (m + 1) m * y (Fin.last m) := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_single (Fin.last m) (fun j _ hj => ?_) fun h =>
    absurd (Finset.mem_univ (Fin.last m)) h
  rw [hessenberg, Matrix.of_apply, Fin.val_last,
    coeff_eq_zero_of_lt A b (Nat.succ_lt_succ (Fin.val_lt_last hj)), zero_mul]

/-- The rows of the rectangular Hessenberg matrix $\bar H_{m+1}$ above the last row are the rows of
the square matrix $H_{m+1}$. -/
private theorem hessenberg_mulVec_castSucc (m : ℕ) (y : Fin (m + 1) → 𝕜) (i : Fin (m + 1)) :
    (hessenberg A b (m + 1)).mulVec y i.castSucc = (hessenbergSq A b (m + 1)).mulVec y i := by
  simp [Matrix.mulVec, dotProduct, hessenberg, hessenbergSq]

/-- Let $y \in \mathbb{K}^{m+1}$ and $\theta \in \mathbb{K}$ satisfy $H_{m+1} y = \theta y$, and let
$\tilde u = V_{m+1} y = \sum_{j \le m} y_j v_j$. Then the residual of $\tilde u$ is a multiple
of one Arnoldi vector:
$$A \tilde u - \theta \tilde u = h_{m+1,m} \, y_m \, v_{m+1}.$$
This follows [saad2011numerical].

The indices start at $0$, so in the 1-based notation of the source the identity reads $(A -
\theta I) \tilde u = h_{k+1,k} \, y_k \, v_{k+1}$ with $k = m + 1$. The eigenvalue equation
cancels all rows of the Arnoldi relation $A V_{m+1} = V_{m+2} \bar H_{m+1}$ except the last, and
the last row of $\bar H_{m+1}$ has the single entry $h_{m+1,m}$. No hypothesis on the grade is
needed: after breakdown both $v_{m+1}$ and $h_{m+1,m}$ are $0$. -/
theorem apply_sub_smul_sum_eq (m : ℕ) (y : Fin (m + 1) → 𝕜) (θ : 𝕜)
    (hy : (hessenbergSq A b (m + 1)).mulVec y = θ • y) :
    A (∑ j, y j • vec A b j) - θ • ∑ j, y j • vec A b j
      = (coeff A b (m + 1) m * y (Fin.last m)) • vec A b (m + 1) := by
  have hsum := apply_sum A b (m + 1) y
  rw [Fin.sum_univ_castSucc (n := m + 1), hessenberg_mulVec_last A b m y] at hsum
  have hrow : ∀ i : Fin (m + 1), (hessenberg A b (m + 1)).mulVec y i.castSucc = θ * y i := by
    intro i
    rw [hessenberg_mulVec_castSucc A b m y i, hy]
    rfl
  rw [hsum]
  have hcast : ∀ i : Fin (m + 1),
      (hessenberg A b (m + 1)).mulVec y i.castSucc • vec A b (i.castSucc : ℕ)
        = θ • (y i • vec A b (i : ℕ)) := by
    intro i
    rw [hrow i, mul_smul]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hcast i, ← Finset.smul_sum]
  abel

/-- **The cheap Arnoldi residual.** Let $y \in \mathbb{K}^{m+1}$ and $\theta \in \mathbb{K}$ satisfy
$H_{m+1} y = \theta y$, and let $\tilde u = V_{m+1} y = \sum_{j \le m} y_j v_j$. Then
$$\|A \tilde u - \theta \tilde u\| = |h_{m+1,m}| \, |y_m|.$$
This is Proposition 6.8 of [saad2011numerical].

The indices start at $0$, so in the 1-based notation of the source the identity reads
$\|(A - \theta I) \tilde u\| = |h_{k+1,k}| \, |y_k|$ with $k = m + 1$. The residual norm is the
product of one subdiagonal Hessenberg entry and the last coordinate of the small eigenvector. So
the accuracy of a Ritz pair is known without forming $\tilde u$, which makes a restarted Arnoldi
method practical. By `Arnoldi.isRitzPair_of_mulVec_eq_smul`, the
hypothesis says, below the grade, that $(\theta, \tilde u)$ is a Ritz pair of $A$ on
$\mathcal{K}_{m+1}(A, b)$. The identity holds past breakdown as well, where both sides are $0$. -/
theorem norm_ritz_residual_eq (m : ℕ) (y : Fin (m + 1) → 𝕜) (θ : 𝕜)
    (hy : (hessenbergSq A b (m + 1)).mulVec y = θ • y) :
    ‖A (∑ j, y j • vec A b j) - θ • ∑ j, y j • vec A b j‖
      = ‖coeff A b (m + 1) m‖ * ‖y (Fin.last m)‖ := by
  rw [apply_sub_smul_sum_eq A b m y θ hy, norm_smul, norm_mul]
  rcases eq_or_ne (vec A b (m + 1)) 0 with h0 | h0
  · rw [coeff, h0, inner_zero_left]
    simp
  · rw [norm_vec_eq_one_of_ne_zero A b h0, mul_one]

end Arnoldi

/-! ### Ritz optimality in the Frobenius norm -/

namespace Matrix

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

open scoped Matrix.Norms.Frobenius

variable [DecidableEq n] [DecidableEq r]

/-- **Optimality of the compression.** Let $A \in \mathbb{K}^{n \times n}$ and let
$Q \in \mathbb{K}^{n \times r}$ have orthonormal columns, $Q^H Q = I$. The least value of the
Frobenius norm $\|AQ - QS\|_F$ over all $S \in \mathbb{K}^{r \times r}$ exists and is
$$\min_S \|AQ - QS\|_F = \|(I - QQ^H) A Q\|_F.$$
This is Theorem 8.1.14 of [golub2013matrix].

The minimum is attained at $S = Q^H A Q$, and by `Matrix.frobenius_norm_mul_sub_mul_sq` this
minimizer is unique. No symmetry of $A$ is needed. The norm is the Frobenius norm of the scope
`Matrix.Norms.Frobenius`. -/
theorem isLeast_frobenius_norm_mul_sub_mul (A : Matrix n n 𝕜) {Q : Matrix n r 𝕜}
    (hQ : Qᴴ * Q = 1) :
    IsLeast (Set.range fun S : Matrix r r 𝕜 => ‖A * Q - Q * S‖) ‖(1 - Q * Qᴴ) * A * Q‖ := by
  refine ⟨⟨Qᴴ * A * Q, ?_⟩, ?_⟩
  · have := frobenius_norm_mul_sub_mul_sq A hQ (Qᴴ * A * Q)
    rw [sub_self, norm_zero, zero_pow two_ne_zero, zero_add] at this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  · rintro _ ⟨S, rfl⟩
    have := frobenius_norm_mul_sub_mul_sq A hQ S
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [this]
    exact le_add_of_nonneg_left (sq_nonneg _)

end Matrix
