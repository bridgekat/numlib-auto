/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.InnerProductSpace.Projection.OrthonormalBasis
import Numlib.Eigen.RayleighRitz
import Numlib.Krylov.Block
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Lanczos
import Numlib.RingTheory.Polynomial.ChebyshevEllipse
import Numlib.RingTheory.Polynomial.ChebyshevMinimax

/-!
# Convergence of the Krylov subspace towards an eigenvector

Let $A$ be a symmetric operator on an inner product space $E$ over $\mathbb{R}$ or $\mathbb{C}$,
with eigenvalues $\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{n-1}$ and orthonormal eigenvectors
$u_0, \dots, u_{n-1}$. For a starting vector $v$, let $\mathcal{K}_m(A, v) = \operatorname{span}\{v,
A v, \dots, A^{m-1} v\}$ be the Krylov subspace. This module bounds the angle
$\theta(u_i, \mathcal{K}_m)$ between $u_i$ and the Krylov subspace, and through it the error of the
Ritz values, the eigenvalues of the compression of $A$ to $\mathcal{K}_m$. These are the convergence
estimates of the symmetric Lanczos process due to Kaniel, Paige and Saad. The presentation follows
[saad2011numerical], §6.6, and uses the angles of
`Numlib.Analysis.InnerProductSpace.Projection.Angle`. With $T_k$ the Chebyshev polynomial of the
first kind,
$$\gamma_i = \frac{\lambda_i - \lambda_{i+1}}{\lambda_{i+1} - \lambda_{n-1}}, \qquad \kappa_i =
  \prod_{j < i} \frac{\lambda_j - \lambda_{n-1}}{\lambda_j - \lambda_i},$$
the main bound is $\tan\theta(u_i, \mathcal{K}_m) \le \kappa_i \tan\theta(u_i, v) / T_k(1 + 2
\gamma_i)$ for $i + k < m$. The Kaniel–Paige–Saad theorem bounds the Ritz values $\theta_i$ by $0
\le \lambda_i - \theta_i \le (\lambda_0 - \lambda_{n-1}) (\kappa_i \tan\theta(u_i, v) / T_k(1 + 2
\gamma_i))^2$, with the constant $\kappa_i$ built from the Ritz values. A block version holds for
block Krylov subspaces.

Without symmetry, the same variational idea bounds the distance from an eigenvector $u_i$ of a
diagonalizable operator to $\mathcal{K}_m(A, v)$, for $v = \sum_k \alpha_k u_k$. The bounds then
have the factor $\xi_i = \sum_{k \neq i} |\alpha_k| / |\alpha_i|$, and an explicit geometric or
Chebyshev rate follows when a disc or an ellipse encloses the rest of the spectrum. The module also
identifies the subdiagonal Arnoldi coefficient as the norm of $(1 - P_m) A$ on $\mathcal{K}_m$, and
the eigenvalues of the Lanczos tridiagonal matrix as the Ritz values.

## Main definitions

* `Polynomial.deflator`: the polynomial $\prod_{j \in s} (r_j - X) / (r_j - c)$, which vanishes at
  each $r_j$ and has the value $1$ at $c$.
* `Lanczos.ritzValues`: the eigenvalues of the Lanczos tridiagonal matrix $T_m$, sorted in
  decreasing order.

## Main results

* `Lanczos.tan_angle_eq_iInf`: for an eigenpair $(\mu, u)$ of a symmetric $A$ with $\|u\| = 1$ and
  $\langle u, v \rangle \neq 0$, $\tan\theta(u, \mathcal{K}_m) = \min \{ \|p(A) w\| / |\langle u, v
  \rangle| : \deg p < m, \ p(\mu) = 1 \}$, where $w = v - \langle u, v \rangle u$;
  `Lanczos.tan_angle_eq_iInf_mul` is the form with $w$ normalized, and
  `Lanczos.exists_norm_aeval_div_eq_tan_angle` says that the minimum is attained.
* `Lanczos.tan_angle_le_of_forall_abs_eval_le`: a real polynomial with $p(\lambda_i) = 1$ and
  $|p| \le M$ at the other eigenvalues gives $\tan\theta(u_i, \mathcal{K}_m) \le M \tan\theta(u_i,
  v)$.
* `Polynomial.exists_deflated_chebyshev`: the competitor polynomial, the product of a polynomial
  with prescribed roots and a normalized Chebyshev polynomial of an interval.
* `Lanczos.tan_angle_le`: $\tan\theta(u_i, \mathcal{K}_m) \le \kappa_i \tan\theta(u_i, v) / T_k(1 +
  2 \gamma_i)$.
* `Lanczos.kaniel_paige_saad`: the Kaniel–Paige–Saad bound on the Ritz values.
* `Lanczos.ritzValues_eq_eigenvalues_compression`: before a breakdown, the eigenvalues of the
  Lanczos tridiagonal matrix are the Ritz values.
* `BlockLanczos.kaniel_paige_saad`: the block version, due to Underwood (Theorem 10.3.2 of
  [golub2013matrix]).
* `Arnoldi.norm_starProjection_comp_orthogonal_eq_coeff`: the norm of $(1 - P_m) A$ on
  $\mathcal{K}_m$ is the subdiagonal Arnoldi coefficient ([saad2011numerical], Proposition 6.6).
* `Arnoldi.norm_sub_starProjection_le_iInf`: the distance from an eigenvector of a diagonalizable
  operator to $\mathcal{K}_m$ is bounded by a minimum over polynomials ([saad2011numerical], Lemma
  6.2).
* `Arnoldi.norm_sub_starProjection_le_of_mem_closedBall`: the geometric bound
  $\xi_i (\rho / |\lambda_i - c|)^{m-1}$ when a disc of centre $c$ and radius $\rho$ encloses the
  rest of the spectrum ([saad2011numerical], Proposition 6.10).
* `Arnoldi.norm_sub_starProjection_le_of_mem_ellipse`: the Chebyshev bound when an ellipse encloses
  the rest of the spectrum ([saad2011numerical], Theorem 6.8).

## Proof outline

The proofs use the three ingredients of the conjugate gradient error bound of
`Numlib.Krylov.Convergence.CG`: a variational characterization, a bound on the norm of a polynomial
in $A$, and a Chebyshev min–max problem. The first lemma turns the angle into a polynomial
approximation problem, because $\langle u, p(A) x \rangle = p(\mu) \langle u, x \rangle$ for an
eigenpair $(\mu, u)$. A polynomial with roots at the eigenvalues before $\lambda_i$ removes them
from the min–max problem at the cost of the factor $\kappa_i$, and the Chebyshev polynomial of the
interval that contains the remaining eigenvalues, normalized at $\lambda_i$, is optimal for what
remains. For the Ritz values, the lower bound $\theta_i \le \lambda_i$ is Cauchy interlacing. The
upper bound is the Courant–Fischer theorem for the compression: the competitor vector is orthogonal
to the first $i$ Ritz vectors, because the competitor polynomial vanishes at the corresponding Ritz
values. Without symmetry, the triangle inequality replaces the theorem of Pythagoras, which is why
the factor $\xi_i$ appears. For an ellipse, the competitor is the shifted and normalized Chebyshev
polynomial of `Numlib.RingTheory.Polynomial.ChebyshevEllipse`; its maximum on the ellipse is known,
and the maximum modulus principle carries the bound into the region that the ellipse encloses.

## Implementation notes

* Indices start at $0$: $\lambda_0$ is the largest eigenvalue and $\lambda_{n-1}$ the smallest, and
  the Ritz values $\theta_0 \ge \theta_1 \ge \dots$ are indexed by `Fin m`.
* The eigenvector estimates hold for every orthonormal eigenbasis $b$ with real eigenvalues
  $\lambda$ ($A b_j = \lambda_j b_j$, and `Antitone lam` where the order matters), as in the "any
  Schur decomposition" of the textbooks. The corollaries named `…_eigenvectorBasis` specialize them
  to `LinearMap.IsSymmetric.eigenvectorBasis`.
* [saad2011numerical] states the first lemma with the spectral projector onto the whole eigenspace
  of $\lambda_i$. Here the projector is onto the line through the single eigenvector $u_i$. This
  keeps the statement true at a multiple eigenvalue: the components of $v$ along the other
  eigenvectors for $\lambda_i$ then belong to $w$, and no Krylov subspace can separate them from
  $u_i$. The proof uses only that, for symmetric $A$, the line through $u_i$ and its orthogonal
  complement are both invariant.
* The angle bound and the Ritz value bound each have two forms. The form `…_of_mem_Icc` takes as
  data an interval $[lo, hi]$ that contains the eigenvalues after the $i$-th; it is the general
  statement, with the sharper constant $\lambda_i - lo$ in place of $\lambda_0 - \lambda_{n-1}$. The
  other form specializes it to the interval $[\lambda_{n-1}, \lambda_{i+1}]$, which is the form of
  the literature.
* Neighbouring and extreme indices are given as data with their defining properties, not computed:
  `iS` with `i + 1 = iS`, and `first` and `last` with `IsBot first` and `IsTop last`. This keeps
  `Fin` arithmetic out of the statements, and a user who knows only part of the spectrum can still
  apply them.
* The tangent of the angle `Submodule.tanAngle` has the value $0$ when the projection of the vector
  onto the subspace is $0$.
-/

open Polynomial Polynomial.Chebyshev Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### The angle between a vector and a line -/

namespace Submodule

/-- Let $u \in E$ be a unit vector and $x \in E$. Then the tangent of the angle between $u$ and the
line through $x$ is
$$\tan\theta(u, \mathbb{K} x) = \frac{\|x - \langle u, x \rangle u\|}{|\langle u, x \rangle|}.$$

No hypothesis is needed: if $x$ is orthogonal to $u$, both sides have the Lean value $0$. -/
theorem tanAngle_span_singleton {u : E} (hu : ‖u‖ = 1) (x : E) :
    (𝕜 ∙ x).tanAngle u = ‖x - (inner 𝕜 u x : 𝕜) • u‖ / ‖(inner 𝕜 u x : 𝕜)‖ := by
  have hconj : (inner 𝕜 x u : 𝕜) = starRingEnd 𝕜 (inner 𝕜 u x) := (inner_conj_symm x u).symm
  rcases eq_or_ne (inner 𝕜 u x : 𝕜) 0 with h | h
  · have hp : (𝕜 ∙ x).starProjection u = 0 := by
      rw [starProjection_singleton, hconj, h, map_zero, zero_div, zero_smul]
    rw [tanAngle, hp, norm_zero, div_zero, h, norm_zero, div_zero]
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact h (inner_zero_right u)
    have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
    have hnormxu : ‖(inner 𝕜 x u : 𝕜)‖ = ‖(inner 𝕜 u x : 𝕜)‖ := by
      rw [hconj, RCLike.norm_conj]
    have hproj : ‖(𝕜 ∙ x).starProjection u‖ = ‖(inner 𝕜 u x : 𝕜)‖ / ‖x‖ := by
      rw [starProjection_singleton, norm_smul, norm_div, hnormxu, RCLike.norm_ofReal,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2)]
      field_simp
    have hpyth1 : ‖(𝕜 ∙ x).starProjection u‖ ^ 2 + ‖u - (𝕜 ∙ x).starProjection u‖ ^ 2 = 1 := by
      rw [norm_starProjection_sq_add_norm_sub_sq, hu, one_pow]
    have hpyth2 : ‖(inner 𝕜 u x : 𝕜)‖ ^ 2 + ‖x - (inner 𝕜 u x : 𝕜) • u‖ ^ 2 = ‖x‖ ^ 2 := by
      have h2 := (𝕜 ∙ u).norm_starProjection_sq_add_norm_sub_sq x
      rw [starProjection_unit_singleton 𝕜 hu x, norm_smul, hu, mul_one] at h2
      exact h2
    have hsq : ‖u - (𝕜 ∙ x).starProjection u‖ ^ 2 = (‖x - (inner 𝕜 u x : 𝕜) • u‖ / ‖x‖) ^ 2 := by
      rw [div_pow, eq_div_iff (by positivity)]
      rw [hproj, div_pow] at hpyth1
      field_simp at hpyth1 ⊢
      nlinarith [hpyth1, hpyth2]
    have hnum : ‖u - (𝕜 ∙ x).starProjection u‖ = ‖x - (inner 𝕜 u x : 𝕜) • u‖ / ‖x‖ :=
      (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    rw [tanAngle, hnum, hproj, div_div_div_cancel_right₀ hxn.ne']

/-- The tangent of the angle between a vector $u$ and a subspace depends only on the subspace: if
$K = L$, then $\tan\theta(u, K) = \tan\theta(u, L)$.

This holds even when the two `HasOrthogonalProjection` instances are found in different ways. A
direct rewrite of the subspace under `Submodule.tanAngle` fails, because the instance argument
depends on the subspace. -/
theorem tanAngle_congr {K L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : K = L) (u : E) : K.tanAngle u = L.tanAngle u := by
  subst h
  rfl

/-- Let $K$ be a subspace with an orthogonal projection $P_K$, and let $u \in E$. Then the
orthogonal projection of $u$ onto the line through $P_K u$ is $P_K u$. -/
theorem starProjection_span_singleton_starProjection (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (u : E) :
    (𝕜 ∙ K.starProjection u).starProjection u = K.starProjection u := by
  refine starProjection_span_singleton_eq_self ?_
  have h0 := K.starProjection_inner_eq_zero u _ (K.starProjection_apply_mem u)
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [← inner_conj_symm (K.starProjection u) u, h0, inner_conj_symm]

/-- Let $K$ be a subspace with an orthogonal projection $P_K$, and let $u \in E$. Then the tangent
of the angle between $u$ and the line through $P_K u$ equals the tangent of the angle between
$u$ and $K$:
$$\tan\theta(u, \mathbb{K} P_K u) = \tan\theta(u, K).$$

So the projection realizes the angle. -/
theorem tanAngle_span_singleton_starProjection (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (u : E) : (𝕜 ∙ K.starProjection u).tanAngle u = K.tanAngle u := by
  rw [tanAngle, tanAngle, starProjection_span_singleton_starProjection]

/-- If $\langle u, x \rangle \neq 0$, then the orthogonal projection of $u$ onto the line through
$x$ is not $0$. -/
theorem starProjection_span_singleton_ne_zero {u x : E} (h : (inner 𝕜 u x : 𝕜) ≠ 0) :
    (𝕜 ∙ x).starProjection u ≠ 0 := by
  intro h0
  refine h ?_
  have hx : x ∈ (𝕜 ∙ x) := mem_span_singleton_self x
  have h1 := (𝕜 ∙ x).starProjection_inner_eq_zero u x hx
  rw [inner_sub_left, h0, sub_eq_zero] at h1
  rw [h1, inner_zero_left]

end Submodule

/-! ### Polynomials in a symmetric operator, tested against an eigenvector -/

/-- Let $A$ be a linear operator on $E$ and let $A u = c u$. Then for every polynomial $p$ over
$\mathbb{K}$, $p(A) u = p(c) u$. -/
theorem Polynomial.aeval_apply_of_apply_eq_smul {A : E →ₗ[𝕜] E} {u : E} {c : 𝕜} (h : A u = c • u)
    (p : 𝕜[X]) : aeval A p u = p.eval c • u :=
  Module.End.aeval_apply_of_mem_apply_eq_smul h

/-- Let $b$ be an orthonormal basis of $E$ with $A b_j = \mu_j b_j$ for all $j$, let $p$ be a
polynomial over $\mathbb{K}$, let $M \ge 0$, and let $x \in E$. If $|p(\mu_j)| \le M$ for every
$j$ with $\langle b_j, x \rangle \neq 0$, then
$$\|p(A) x\| \le M \|x\|.$$

Only the eigenvalues whose eigenvectors occur in $x$ matter. This lets a competitor polynomial
have its roots at the eigenvalues that the vector does not contain. The coordinate
$\langle b_j, x \rangle$ is `b.repr x j`. -/
theorem OrthonormalBasis.norm_aeval_apply_le_of_forall_repr {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) {A : E →ₗ[𝕜] E} {μ : ι → 𝕜} (hb : ∀ i, A (b i) = μ i • b i)
    (p : 𝕜[X]) {M : ℝ} (hM : 0 ≤ M) {x : E} (hp : ∀ j, b.repr x j ≠ 0 → ‖p.eval (μ j)‖ ≤ M) :
    ‖aeval A p x‖ ≤ M * ‖x‖ := by
  have key : ‖aeval A p x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [← b.repr.norm_map (aeval A p x), EuclideanSpace.norm_sq_eq, mul_pow, ← b.repr.norm_map x,
      EuclideanSpace.norm_sq_eq (b.repr x), Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [b.repr_aeval_apply_of_apply_eq_smul hb, norm_mul, mul_pow]
    rcases eq_or_ne (b.repr x j) 0 with hz | hz
    · rw [hz]
      simp
    · gcongr
      exact hp j hz
  nlinarith [norm_nonneg (aeval A p x), mul_nonneg hM (norm_nonneg x)]

namespace LinearMap.IsSymmetric

variable {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- Let $A$ be symmetric and let $A u = \mu u$ with $\mu$ real. Then for every polynomial $p$ over
$\mathbb{K}$ and every $x \in E$
$$\langle u, p(A) x \rangle = p(\mu) \langle u, x \rangle.$$

This identity turns the geometry of the Krylov subspace into a polynomial approximation problem. -/
theorem inner_aeval_apply_of_apply_eq_smul {u : E} {μ : ℝ} (hu : A u = (μ : 𝕜) • u) (p : 𝕜[X])
    (x : E) : (inner 𝕜 u (aeval A p x) : 𝕜) = p.eval (μ : 𝕜) * inner 𝕜 u x := by
  have hpow : ∀ k : ℕ, (inner 𝕜 u ((A ^ k) x) : 𝕜) = (μ : 𝕜) ^ k * inner 𝕜 u x := by
    intro k
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ← hA u, hu, inner_smul_left, RCLike.conj_ofReal, ih]
        ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, inner_add_right, hp, hq, eval_add, add_mul]
  | monomial k a =>
      have hmon : aeval A (monomial k a) x = a • (A ^ k) x := by simp [aeval_monomial]
      rw [hmon, inner_smul_right, hpow, eval_monomial]
      ring

variable {n : ℕ} [FiniteDimensional 𝕜 E] (hn : Module.finrank 𝕜 E = n)
include hn

/-- Let $A$ be symmetric on a space of finite dimension $n$, with the eigenvalues $\lambda_j$ and
the orthonormal eigenbasis $b_j$ of `LinearMap.IsSymmetric.eigenvalues` and
`LinearMap.IsSymmetric.eigenvectorBasis`. Let $p$ be a polynomial over $\mathbb{K}$, $M \ge 0$
and $x \in E$. If $|p(\lambda_j)| \le M$ for every $j$ with $\langle b_j, x \rangle \neq 0$,
then $\|p(A) x\| \le M \|x\|$.

This is `OrthonormalBasis.norm_aeval_apply_le_of_forall_repr` for this eigenbasis. -/
theorem norm_aeval_apply_le_of_forall_repr (p : 𝕜[X]) {M : ℝ} (hM : 0 ≤ M) {x : E}
    (hp : ∀ j : Fin n, (hA.eigenvectorBasis hn).repr x j ≠ 0 →
      ‖p.eval (hA.eigenvalues hn j : 𝕜)‖ ≤ M) :
    ‖aeval A p x‖ ≤ M * ‖x‖ :=
  (hA.eigenvectorBasis hn).norm_aeval_apply_le_of_forall_repr (hA.apply_eigenvectorBasis hn) p hM
    hp

end LinearMap.IsSymmetric

/-!
### The deflating polynomial

For a finite set $s$ of indices, real numbers $r_j$ and a real number $c$, the deflating polynomial
is $\prod_{j \in s} (r_j - X) / (r_j - c)$. It vanishes at each $r_j$ and has the value $1$ at $c$.
The product of a competitor polynomial with it removes the eigenvalues indexed by $s$ from a min–max
problem. On an interval $[lo, hi]$ to the left of $c$, the cost is the factor
$\prod_{j \in s} (r_j - lo) / (r_j - c)$.
-/

section Deflator

variable {ι : Type*}

/-- The **deflating polynomial** of a finite set $s$ of indices, real numbers $r_j$ and a real
number $c$:
$$\prod_{j \in s} \frac{r_j - X}{r_j - c}.$$

It has degree at most $|s|$, vanishes at every $r_j$, and has the value $1$ at $c$ if no $r_j$
equals $c$. Each factor is $(r_j - c)^{-1} (r_j - X)$ with the Lean inverse, so the polynomial
is $0$ if some $r_j$ equals $c$. -/
noncomputable def Polynomial.deflator (s : Finset ι) (r : ι → ℝ) (c : ℝ) : ℝ[X] :=
  ∏ j ∈ s, C (r j - c)⁻¹ * (C (r j) - X)

namespace Polynomial

variable (s : Finset ι) (r : ι → ℝ) (c : ℝ)

/-- The value of the deflating polynomial at $t$ is $\prod_{j \in s} (r_j - t) / (r_j - c)$. -/
theorem deflator_eval (t : ℝ) :
    (deflator s r c).eval t = ∏ j ∈ s, (r j - t) / (r j - c) := by
  rw [deflator, eval_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [eval_mul, eval_C, eval_sub, eval_C, eval_X,
    div_eq_inv_mul]

/-- The deflating polynomial has degree at most $|s|$, the number of its prescribed roots. This is
its cost in the degree of the min–max problem. -/
theorem deflator_degree_le : (deflator s r c).degree ≤ s.card := by
  rw [deflator]
  refine degree_le_of_natDegree_le (le_trans (natDegree_prod_le s _) ?_)
  refine le_trans (Finset.sum_le_sum (g := fun _ => 1) fun j _ => ?_) (by simp)
  compute_degree

/-- If $r_j \neq c$ for all $j \in s$, the deflating polynomial has the value $1$ at $c$. -/
theorem deflator_eval_self (h : ∀ j ∈ s, r j ≠ c) : (deflator s r c).eval c = 1 := by
  rw [deflator_eval]
  exact Finset.prod_eq_one fun j hj => div_self (sub_ne_zero.2 (h j hj))

/-- The deflating polynomial vanishes at $r_j$ for every $j \in s$. -/
theorem deflator_eval_eq_zero {j : ι} (hj : j ∈ s) : (deflator s r c).eval (r j) = 0 := by
  rw [deflator_eval]
  exact Finset.prod_eq_zero hj (by rw [sub_self, zero_div])

/-- Let $c < r_j$ for all $j \in s$, and let $lo \le t \le hi < c$. Then the deflating polynomial
satisfies
$$\Bigl| \prod_{j \in s} \frac{r_j - t}{r_j - c} \Bigr| \le \prod_{j \in s} \frac{r_j -
  lo}{r_j - c}.$$
-/
theorem abs_deflator_eval_le (h : ∀ j ∈ s, c < r j) {lo hi t : ℝ} (hhi : hi < c) (hlo : lo ≤ t)
    (ht : t ≤ hi) : |(deflator s r c).eval t| ≤ ∏ j ∈ s, (r j - lo) / (r j - c) := by
  have hfac : ∀ j ∈ s, 0 ≤ (r j - t) / (r j - c) := fun j hj =>
    div_nonneg (by linarith [h j hj]) (by linarith [h j hj])
  rw [deflator_eval, abs_of_nonneg (Finset.prod_nonneg hfac)]
  refine Finset.prod_le_prod₀ hfac fun j hj => ?_
  exact div_le_div_of_nonneg_right (by linarith) (by linarith [h j hj])

/-- **The competitor polynomial of the Krylov eigenvalue bounds.** Let $s$ be a finite set of
indices, $r_j$ real numbers, and $lo < hi < c$ real numbers with $c < r_j$ for all $j \in s$.
Let $k \in \mathbb{N}$. Then there is a real polynomial $q$ of degree at most $|s| + k$ with
$q(c) = 1$ and $q(r_j) = 0$ for all $j \in s$, such that for all $t \in [lo, hi]$
$$|q(t)| \le \frac{\prod_{j \in s} (r_j - lo) / (r_j - c)}{T_k\bigl( (2 c - hi - lo) / (hi - lo)
  \bigr)},$$
where $T_k$ is the Chebyshev polynomial of the first kind.

The polynomial $q$ is the deflating polynomial `Polynomial.deflator` for $s$, multiplied by the
Chebyshev polynomial of $[lo, hi]$ normalized to $1$ at $c$. The bound is the product of the two
bounds: the numerator is the cost of the deflation, and $1 / T_k$ is the Chebyshev min–max
value. -/
theorem exists_deflated_chebyshev (hr : ∀ j ∈ s, c < r j) {lo hi : ℝ} (hlohi : lo < hi)
    (hhi : hi < c) (k : ℕ) :
    ∃ q : ℝ[X], q.degree ≤ ((s.card + k : ℕ) : WithBot ℕ) ∧ q.eval c = 1 ∧
      (∀ j ∈ s, q.eval (r j) = 0) ∧
      ∀ t ∈ Set.Icc lo hi, |q.eval t| ≤
        (∏ j ∈ s, (r j - lo) / (r j - c)) /
          (T ℝ k).eval ((2 * c - hi - lo) / (hi - lo)) := by
  have hd : (0 : ℝ) < hi - lo := by linarith
  have hnotmem : c ∉ Set.Icc lo hi := fun hc => absurd hc.2 (not_le.2 hhi)
  have hz1 : (1 : ℝ) ≤ (2 * c - hi - lo) / (hi - lo) := by
    rw [le_div_iff₀ hd]
    linarith
  have hT : (1 : ℝ) ≤ (T ℝ k).eval ((2 * c - hi - lo) / (hi - lo)) := one_le_eval_T hz1 k
  have hkappa : (0 : ℝ) ≤ ∏ j ∈ s, (r j - lo) / (r j - c) :=
    Finset.prod_nonneg fun j hj => div_nonneg (by linarith [hr j hj]) (by linarith [hr j hj])
  have habsT : |(T ℝ k).eval ((hi + lo - 2 * c) / (hi - lo))| =
      (T ℝ k).eval ((2 * c - hi - lo) / (hi - lo)) := by
    have hneg : (hi + lo - 2 * c) / (hi - lo) = -((2 * c - hi - lo) / (hi - lo)) := by
      rw [← neg_div]
      congr 1
      ring
    have h1 : |(T ℝ k).eval (-((2 * c - hi - lo) / (hi - lo)))| =
        |(T ℝ k).eval ((2 * c - hi - lo) / (hi - lo))| := by simp [T_eval_neg, abs_mul]
    rw [hneg, h1, abs_of_nonneg (by linarith)]
  refine ⟨deflator s r c * shifted k lo hi c, ?_, ?_, ?_, ?_⟩
  · refine le_trans (degree_mul_le _ _) ?_
    calc (deflator s r c).degree + (shifted k lo hi c).degree
        ≤ ((s.card : ℕ) : WithBot ℕ) + ((k : ℕ) : WithBot ℕ) :=
          add_le_add (deflator_degree_le s r c) (shifted_degree_le k lo hi c)
      _ = ((s.card + k : ℕ) : WithBot ℕ) := by push_cast; ring
  · rw [eval_mul, deflator_eval_self _ _ _ fun j hj => (hr j hj).ne',
      shifted_eval_self _ hlohi hnotmem, one_mul]
  · intro j hj
    rw [eval_mul, deflator_eval_eq_zero _ _ _ hj, zero_mul]
  · intro t ht
    have hbdd : BddAbove ((fun t' => |(shifted k lo hi c).eval t'|) '' Set.Icc lo hi) :=
      (isCompact_Icc.image (shifted k lo hi c).continuous.abs).bddAbove
    have h2 := le_csSup hbdd ⟨t, ht, rfl⟩
    rw [sSup_abs_eval_shifted _ hlohi hnotmem, habsT] at h2
    rw [eval_mul, abs_mul, ← mul_one_div]
    exact mul_le_mul (abs_deflator_eval_le s r c hr hhi ht.1 ht.2) h2 (abs_nonneg _) hkappa

end Polynomial

end Deflator

/-! ### The angle between an eigenvector and the Krylov subspace -/

namespace Lanczos

section Lemma

variable {A : E →ₗ[𝕜] E} {u v : E} {μ : ℝ} (hA : A.IsSymmetric) (hu : ‖u‖ = 1)
  (hAu : A u = (μ : 𝕜) • u)
include hA hu hAu

/-- For a polynomial $p$ with $p(\mu) = 1$, the tangent of the angle between the eigenvector $u$ and
the line through $p(A) v$ is $\|p(A) w\| / |\langle u, v \rangle|$, where
$w = v - \langle u, v \rangle u$. -/
private theorem tanAngle_span_singleton_aeval (p : 𝕜[X]) (hp : p.eval (μ : 𝕜) = 1) :
    (𝕜 ∙ aeval A p v).tanAngle u =
      ‖aeval A p (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖ := by
  have h1 : (inner 𝕜 u (aeval A p v) : 𝕜) = inner 𝕜 u v := by
    rw [hA.inner_aeval_apply_of_apply_eq_smul hAu, hp, one_mul]
  have h2 : aeval A p (v - (inner 𝕜 u v : 𝕜) • u) = aeval A p v - (inner 𝕜 u v : 𝕜) • u := by
    rw [map_sub, map_smul, Polynomial.aeval_apply_of_apply_eq_smul hAu, hp, one_smul]
  rw [Submodule.tanAngle_span_singleton hu, h1, h2]

variable (hv : (inner 𝕜 u v : 𝕜) ≠ 0)
include hv

/-- Let $A$ be symmetric, let $u$ be a unit vector with $A u = \mu u$ for a real $\mu$, and let
$\langle u, v \rangle \neq 0$. Let $w = v - \langle u, v \rangle u$ be the part of $v$
orthogonal to $u$. Then for every polynomial $p$ over $\mathbb{K}$ of degree less than $m$ with
$p(\mu) = 1$
$$\tan\theta(u, \mathcal{K}_m(A, v)) \le \frac{\|p(A) w\|}{|\langle u, v \rangle|}.$$

The vector $p(A) v$ lies in the Krylov subspace, and the angle to a line in a subspace is at
least the angle to the subspace. -/
theorem tan_angle_le_norm_aeval_div {m : ℕ} (p : 𝕜[X]) (hdeg : p.degree < m)
    (hp : p.eval (μ : 𝕜) = 1) :
    (Krylov.subspace A v m).tanAngle u ≤
      ‖aeval A p (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖ := by
  have hinner : (inner 𝕜 u (aeval A p v) : 𝕜) ≠ 0 := by
    rw [hA.inner_aeval_apply_of_apply_eq_smul hAu, hp, one_mul]
    exact hv
  rw [← tanAngle_span_singleton_aeval hA hu hAu p hp]
  exact Submodule.tanAngle_le_of_le
    ((Submodule.span_singleton_le_iff_mem _ _).2 (Krylov.aeval_apply_mem_subspace A v hdeg))
    (Submodule.starProjection_span_singleton_ne_zero hinner)

/-- Let $A$ be symmetric, let $u$ be a unit vector with $A u = \mu u$ for a real $\mu$, let
$\langle u, v \rangle \neq 0$, and let $m > 0$. Then there is a polynomial $p$ of degree less
than $m$ with $p(\mu) = 1$ that attains the bound of `Lanczos.tan_angle_le_norm_aeval_div`:
$$\frac{\|p(A) w\|}{|\langle u, v \rangle|} = \tan\theta(u, \mathcal{K}_m(A, v)), \qquad w = v -
  \langle u, v \rangle u.$$

The polynomial $p$ is the one that carries $v$ to the orthogonal projection of $u$ onto the
Krylov subspace. So the infimum of `Lanczos.tan_angle_eq_iInf` is a minimum. -/
theorem exists_norm_aeval_div_eq_tan_angle {m : ℕ} (hm : 0 < m) :
    ∃ p : 𝕜[X], p.degree < m ∧ p.eval (μ : 𝕜) = 1 ∧
      ‖aeval A p (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖ =
        (Krylov.subspace A v m).tanAngle u := by
  have hvK : v ∈ Krylov.subspace A v m := Krylov.self_mem_subspace A v hm
  have hproj : (Krylov.subspace A v m).starProjection u ≠ 0 := by
    intro h0
    refine hv ?_
    have h1 := (Krylov.subspace A v m).starProjection_inner_eq_zero u v hvK
    rw [inner_sub_left, h0, sub_eq_zero] at h1
    rw [h1, inner_zero_left]
  have hinner : (inner 𝕜 u ((Krylov.subspace A v m).starProjection u) : 𝕜) ≠ 0 := by
    have h1 := (Krylov.subspace A v m).starProjection_inner_eq_zero u _
      ((Krylov.subspace A v m).starProjection_apply_mem u)
    rw [inner_sub_left, sub_eq_zero] at h1
    rw [h1]
    exact inner_self_ne_zero.2 hproj
  obtain ⟨q, hqdeg, hq⟩ := (Krylov.mem_subspace_iff_exists_aeval A v).1
    ((Krylov.subspace A v m).starProjection_apply_mem u)
  have hd : q.eval (μ : 𝕜) ≠ 0 := by
    intro h0
    rw [← hq, hA.inner_aeval_apply_of_apply_eq_smul hAu, h0, zero_mul] at hinner
    exact hinner rfl
  have hp' : ((q.eval (μ : 𝕜))⁻¹ • q).eval (μ : 𝕜) = 1 := by
    rw [eval_smul, smul_eq_mul, inv_mul_cancel₀ hd]
  have hsm : aeval A ((q.eval (μ : 𝕜))⁻¹ • q) v =
      (q.eval (μ : 𝕜))⁻¹ • (Krylov.subspace A v m).starProjection u := by
    rw [map_smul, LinearMap.smul_apply, hq]
  refine ⟨(q.eval (μ : 𝕜))⁻¹ • q, lt_of_le_of_lt (degree_smul_le _ q) hqdeg, hp', ?_⟩
  rw [← tanAngle_span_singleton_aeval hA hu hAu _ hp', hsm,
    Submodule.tanAngle_congr (Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hd)) _) u,
    Submodule.tanAngle_span_singleton_starProjection]

/-- **The angle between an eigenvector and the Krylov subspace as a polynomial minimum.** Let $A$ be
symmetric, let $u$ be a unit vector with $A u = \mu u$ for a real $\mu$, and let $v$ be a
starting vector with $\langle u, v \rangle \neq 0$. Let $w = v - \langle u, v \rangle u$ be the
part of $v$ orthogonal to $u$. Then for every $m$
$$\tan\theta(u, \mathcal{K}_m(A, v)) = \inf \Bigl\{ \frac{\|p(A) w\|}{|\langle u, v \rangle|} :
  \deg p < m, \ p(\mu) = 1 \Bigr\}.$$

For $m > 0$ the infimum is attained (`Lanczos.exists_norm_aeval_div_eq_tan_angle`). For $m = 0$
both sides are $0$: the set of polynomials is empty, its Lean infimum is $0$, and
$\mathcal{K}_0 = \{0\}$.

Only the eigenpair is needed, not a full eigenbasis, and the space need not have finite
dimension. For symmetric $A$, the line through $u$ and its orthogonal complement are both
invariant, and this splits $p(A) v$ into its component along $u$ and the rest. Here $u$ is a
single eigenvector, not the whole eigenspace of $\mu$. At a multiple eigenvalue, the components
of $v$ along the other eigenvectors for $\mu$ are part of $w$, because no Krylov subspace can
separate them from $u$. -/
theorem tan_angle_eq_iInf (m : ℕ) :
    (Krylov.subspace A v m).tanAngle u =
      ⨅ p : {p : 𝕜[X] // p.degree < m ∧ p.eval (μ : 𝕜) = 1},
        ‖aeval A (p : 𝕜[X]) (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hempty : IsEmpty {p : 𝕜[X] // p.degree < (0 : ℕ) ∧ p.eval (μ : 𝕜) = 1} := by
      refine ⟨fun p => ?_⟩
      have hne : (p : 𝕜[X]) ≠ 0 := by
        intro h0
        have h1 := p.2.2
        rw [h0, eval_zero] at h1
        exact zero_ne_one h1
      have h1 : (p : 𝕜[X]).degree < 0 := by exact_mod_cast p.2.1
      exact absurd h1 (not_lt.2 (zero_le_degree_iff.2 hne))
    rw [Submodule.tanAngle_congr (Krylov.subspace_zero A v) u, Submodule.tanAngle_bot,
      Real.iInf_of_isEmpty]
  · have hbdd : BddBelow (Set.range fun p : {p : 𝕜[X] // p.degree < m ∧ p.eval (μ : 𝕜) = 1} =>
        ‖aeval A (p : 𝕜[X]) (v - (inner 𝕜 u v : 𝕜) • u)‖ / ‖(inner 𝕜 u v : 𝕜)‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨p, rfl⟩
      positivity
    obtain ⟨p, hdeg, hp, hval⟩ := exists_norm_aeval_div_eq_tan_angle hA hu hAu hv hm
    have hnonempty : Nonempty {p : 𝕜[X] // p.degree < m ∧ p.eval (μ : 𝕜) = 1} :=
      ⟨⟨p, hdeg, hp⟩⟩
    refine le_antisymm
      (le_ciInf fun q => tan_angle_le_norm_aeval_div hA hu hAu hv (q : 𝕜[X]) q.2.1 q.2.2) ?_
    rw [← hval]
    exact ciInf_le hbdd ⟨p, hdeg, hp⟩

/-- Let $A$ be symmetric, let $u$ be a unit vector with $A u = \mu u$ for a real $\mu$, and let
$\langle u, v \rangle \neq 0$. Let $w = v - \langle u, v \rangle u$ and $y = w / \|w\|$. Then
for every $m$
$$\tan\theta(u, \mathcal{K}_m(A, v)) = \inf \{ \|p(A) y\| : \deg p < m, \ p(\mu) = 1 \} \cdot
  \tan\theta(u, v).$$

This is `Lanczos.tan_angle_eq_iInf` in the normalized form of [saad2011numerical]. If $w = 0$,
that is, if $v$ is a multiple of $u$, then the Lean value of $y$ is $0$ and both sides are $0$;
the source adopts this convention explicitly. Here $\tan\theta(u, v)$ is the tangent of the
angle between $u$ and the line through $v$. -/
theorem tan_angle_eq_iInf_mul (m : ℕ) :
    (Krylov.subspace A v m).tanAngle u =
      ⨅ p : {p : 𝕜[X] // p.degree < m ∧ p.eval (μ : 𝕜) = 1},
        ‖aeval A (p : 𝕜[X]) (((‖v - (inner 𝕜 u v : 𝕜) • u‖ : ℝ) : 𝕜)⁻¹ •
            (v - (inner 𝕜 u v : 𝕜) • u))‖ * (𝕜 ∙ v).tanAngle u := by
  rw [tan_angle_eq_iInf hA hu hAu hv m, Submodule.tanAngle_span_singleton hu v]
  refine iInf_congr fun p => ?_
  rcases eq_or_ne (v - (inner 𝕜 u v : 𝕜) • u) 0 with h0 | h0
  · rw [h0]
    simp
  · have hw : (0 : ℝ) < ‖v - (inner 𝕜 u v : 𝕜) • u‖ := norm_pos_iff.2 h0
    rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hw.le]
    field_simp

end Lemma

/-!
### From a polynomial estimate to an angle bound

The statements below take any orthonormal eigenbasis $b$ of $A$, with $A b_j = \lambda_j b_j$ for
real eigenvalues $\lambda_j$, sorted in decreasing order where the statement needs it. They do not
use the eigenbasis `LinearMap.IsSymmetric.eigenvectorBasis` of Mathlib, because at a multiple
eigenvalue the eigenvector $u_i = b_i$ is not unique, and the statements of the textbooks quantify
over every Schur decomposition. Such an operator $A$ is symmetric
(`OrthonormalBasis.isSymmetric_of_apply_eq_ofReal_smul`), and its sorted eigenvalues are $\lambda$
(`LinearMap.IsSymmetric.eigenvalues_eq_of_apply_eq_ofReal_smul`).
-/

section Eigenbasis

variable {A : E →ₗ[𝕜] E} {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
  {lam : Fin n → ℝ} (hb : ∀ j, A (b j) = (lam j : 𝕜) • b j)
include hb

/-- Let $b$ be an orthonormal basis with $A b_j = \lambda_j b_j$ for real $\lambda_j$. Then for
every real polynomial $q$ and every $x \in E$, the coordinates of $q(A) x$ are $\langle b_j,
q(A) x \rangle = q(\lambda_j) \langle b_j, x \rangle$. -/
theorem repr_aeval_map_apply (q : ℝ[X]) (x : E) (j : Fin n) :
    b.repr (aeval A (q.map (algebraMap ℝ 𝕜)) x) j = ((q.eval (lam j) : ℝ) : 𝕜) * b.repr x j := by
  rw [b.repr_aeval_apply_of_apply_eq_smul hb, eval_map_apply, RCLike.algebraMap_eq_ofReal]

/-- **Every competitor polynomial gives an angle bound.** Let $b$ be an orthonormal basis of $E$
with $A b_j = \lambda_j b_j$ for real $\lambda_j$, let $i$ be an index, and let
$\langle b_i, v \rangle \neq 0$. Let $p$ be a real polynomial of degree less than $m$ with
$p(\lambda_i) = 1$, and let $M \ge 0$ with $|p(\lambda_j)| \le M$ for all $j \neq i$. Then
$$\tan\theta(b_i, \mathcal{K}_m(A, v)) \le M \tan\theta(b_i, v).$$

This is the part of the Krylov eigenvector estimate that does not depend on the choice of the
polynomial. The content of a Chebyshev bound such as `Lanczos.tan_angle_le` is the choice of $p$
and the estimate of $M$. Here $\tan\theta(b_i, v)$ is the tangent of the angle between $b_i$ and
the line through $v$. -/
theorem tan_angle_le_of_forall_abs_eval_le (i : Fin n) {v : E}
    (hv : (inner 𝕜 (b i) v : 𝕜) ≠ 0) {m : ℕ} (p : ℝ[X])
    (hdeg : p.degree < m) (hp : p.eval (lam i) = 1) {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ j : Fin n, j ≠ i → |p.eval (lam j)| ≤ M) :
    (Krylov.subspace A v m).tanAngle (b i) ≤ M * (𝕜 ∙ v).tanAngle (b i) := by
  have hu : ‖b i‖ = 1 := b.norm_eq_one i
  have hdeg' : (p.map (algebraMap ℝ 𝕜)).degree < (m : ℕ) := lt_of_le_of_lt degree_map_le hdeg
  have hp' : (p.map (algebraMap ℝ 𝕜)).eval ((lam i : ℝ) : 𝕜) = 1 := by
    rw [eval_map_apply, RCLike.algebraMap_eq_ofReal, hp, RCLike.ofReal_one]
  have hwi : b.repr (v - (inner 𝕜 (b i) v : 𝕜) • b i) i = 0 := by
    rw [OrthonormalBasis.repr_apply_apply, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hu]
    simp
  have hbnd' : ∀ j : Fin n, b.repr (v - (inner 𝕜 (b i) v : 𝕜) • b i) j ≠ 0 →
      ‖(p.map (algebraMap ℝ 𝕜)).eval ((lam j : ℝ) : 𝕜)‖ ≤ M := by
    intro j hj
    rw [eval_map_apply, RCLike.algebraMap_eq_ofReal, RCLike.norm_ofReal]
    refine hbnd j fun hji => hj ?_
    rw [hji, hwi]
  have h1 := tan_angle_le_norm_aeval_div (b.isSymmetric_of_apply_eq_ofReal_smul hb) hu (hb i) hv
    (p.map (algebraMap ℝ 𝕜)) hdeg' hp'
  have h2 := b.norm_aeval_apply_le_of_forall_repr hb (p.map (algebraMap ℝ 𝕜)) hM hbnd'
  refine h1.trans ?_
  rw [Submodule.tanAngle_span_singleton hu v, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h2 (norm_nonneg _)

/-! ### The Chebyshev bound on the angle -/

/-- **The Chebyshev bound on the angle between an eigenvector and the Krylov subspace**, with the
enclosing interval as data. Let $b$ be an orthonormal basis of $E$ with $A b_j = \lambda_j b_j$
for real $\lambda_j$, let $i$ be an index, and let $\langle b_i, v \rangle \neq 0$. Let
$lo < hi < \lambda_i$, let $\lambda_j \in [lo, hi]$ for all $j > i$, and let
$\lambda_i < \lambda_j$ for all $j < i$. Then for all $m$ and $k$ with $i + k < m$
$$\tan\theta(b_i, \mathcal{K}_m(A, v)) \le \frac{\kappa}{T_k\bigl( (2 \lambda_i - hi - lo) /
  (hi - lo) \bigr)} \tan\theta(b_i, v), \qquad \kappa = \prod_{j < i} \frac{\lambda_j -
  lo}{\lambda_j - \lambda_i},$$
where $T_k$ is the Chebyshev polynomial of the first kind.

The competitor is the product of the polynomial with roots at the $i$ eigenvalues before
$\lambda_i$, which removes them from the problem at the cost of the factor $\kappa$, and the
Chebyshev polynomial of $[lo, hi]$ normalized to $1$ at $\lambda_i$, which is the min–max choice
for what remains. The best bound is at $k = m - 1 - i$. -/
theorem tan_angle_le_of_mem_Icc (i : Fin n) {v : E}
    (hv : (inner 𝕜 (b i) v : 𝕜) ≠ 0) {lo hi : ℝ} (hlohi : lo < hi) (hhi : hi < lam i)
    (hmem : ∀ j : Fin n, i < j → lam j ∈ Set.Icc lo hi)
    (hsep : ∀ j : Fin n, j < i → lam i < lam j)
    {m k : ℕ} (hm : (i : ℕ) + k < m) :
    (Krylov.subspace A v m).tanAngle (b i) ≤
      (∏ j ∈ Finset.Iio i, (lam j - lo) / (lam j - lam i)) /
        (T ℝ k).eval ((2 * lam i - hi - lo) / (hi - lo)) * (𝕜 ∙ v).tanAngle (b i) := by
  have hsep' : ∀ j ∈ Finset.Iio i, lam i < lam j := fun j hj => hsep j (Finset.mem_Iio.1 hj)
  have hT : (1 : ℝ) ≤ (T ℝ k).eval ((2 * lam i - hi - lo) / (hi - lo)) :=
    one_le_eval_T (by rw [le_div_iff₀ (by linarith : (0 : ℝ) < hi - lo)]; linarith) k
  have hM : (0 : ℝ) ≤ (∏ j ∈ Finset.Iio i, (lam j - lo) / (lam j - lam i)) /
      (T ℝ k).eval ((2 * lam i - hi - lo) / (hi - lo)) :=
    div_nonneg (Finset.prod_nonneg fun j hj =>
      div_nonneg (by linarith [hsep' j hj]) (by linarith [hsep' j hj])) (by linarith)
  obtain ⟨q, hqdeg, hq1, hqz, hqb⟩ := exists_deflated_chebyshev (Finset.Iio i) lam (lam i) hsep'
    hlohi hhi k
  refine tan_angle_le_of_forall_abs_eval_le b hb i hv q ?_ hq1 hM ?_
  · refine lt_of_le_of_lt hqdeg ?_
    rw [Nat.cast_lt, Fin.card_Iio]
    omega
  · intro j hj
    rcases lt_or_gt_of_ne hj with hji | hji
    · rw [hqz j (Finset.mem_Iio.2 hji), abs_zero]
      exact hM
    · exact hqb _ (hmem j hji)

/-! ### The Kaniel–Paige–Saad bound on the Ritz values -/

/-- Let $b$ be an orthonormal basis of $E$ with $A b_j = \lambda_j b_j$ for real $\lambda_j$. Let
$q$ be a real polynomial, $y \in E$, $s$ a set of indices, and $lo \le c$ and $M$ real numbers.
Suppose that $lo \le \lambda_j$ and $|q(\lambda_j)| \le M$ for all $j \in s$, and that for every
$j \notin s$ either $c \le \lambda_j$ or $\langle b_j, y \rangle = 0$. Then, with $z = q(A) y$,
$$c \|z\|^2 - \operatorname{Re} \langle A z, z \rangle \le (c - lo) M^2 \sum_{j \in s} |\langle
  b_j, y \rangle|^2.$$

This estimate is shared by the single-vector and the block Kaniel–Paige–Saad bounds. -/
theorem mul_norm_sq_aeval_sub_re_inner_le (q : ℝ[X]) (y : E) {c lo M : ℝ} (hclo : lo ≤ c)
    (s : Finset (Fin n)) (hs : ∀ j ∉ s, c ≤ lam j ∨ b.repr y j = 0) (hlo : ∀ j ∈ s, lo ≤ lam j)
    (hqM : ∀ j ∈ s, |q.eval (lam j)| ≤ M) :
    c * ‖aeval A (q.map (algebraMap ℝ 𝕜)) y‖ ^ 2 -
        RCLike.re (inner 𝕜 (A (aeval A (q.map (algebraMap ℝ 𝕜)) y))
          (aeval A (q.map (algebraMap ℝ 𝕜)) y)) ≤
      (c - lo) * M ^ 2 * ∑ j ∈ s, ‖b.repr y j‖ ^ 2 := by
  refine (b.mul_norm_sq_sub_re_inner_le_sum hb c _ fun j hj => (hs j hj).imp_right fun h => by
    rw [repr_aeval_map_apply b hb, h, mul_zero]).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [repr_aeval_map_apply b hb, norm_mul, RCLike.norm_ofReal, mul_pow]
  rcases le_or_gt c (lam j) with hcj | hcj
  · have h1 : (c - lam j) * (|q.eval (lam j)| ^ 2 * ‖b.repr y j‖ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ (c - lo) * M ^ 2 * ‖b.repr y j‖ ^ 2 :=
      mul_nonneg (mul_nonneg (sub_nonneg.2 hclo) (sq_nonneg M)) (sq_nonneg _)
    linarith
  · have hq : |q.eval (lam j)| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hqM j hj) 2
    calc (c - lam j) * (|q.eval (lam j)| ^ 2 * ‖b.repr y j‖ ^ 2)
        ≤ (c - lo) * (M ^ 2 * ‖b.repr y j‖ ^ 2) :=
          mul_le_mul (by linarith [hlo j hj]) (mul_le_mul_of_nonneg_right hq (by positivity))
            (by positivity) (by linarith [hlo j hj])
      _ = (c - lo) * M ^ 2 * ‖b.repr y j‖ ^ 2 := by ring

variable (hlam : Antitone lam)
include hlam

/-- **The Kaniel–Paige–Saad bound**, upper half, with the enclosing interval as data. Let $A$ be
symmetric, and let $b$ be an orthonormal basis of $E$ with $A b_j = \lambda_j b_j$, where
$\lambda_0 \ge \lambda_1 \ge \dots$ are real. Let $\mathcal{K}_m = \mathcal{K}_m(A, v)$ have
dimension $m$, and let $\theta_0 \ge \theta_1 \ge \dots \ge \theta_{m-1}$ be the eigenvalues of
the compression of $A$ to $\mathcal{K}_m$, the Ritz values. Let $i$ be an index of the Ritz
values and $i'$ an index of the eigenvalues, with $\langle b_{i'}, v \rangle \neq 0$. Suppose
that $lo < hi < \lambda_{i'}$, that $\lambda_j \in [lo, hi]$ for all $j > i'$, and that
$\lambda_{i'} < \theta_j$ for all $j < i$. Then for every $k$ with $i + k < m$
$$\lambda_{i'} - \theta_i \le (\lambda_{i'} - lo) \Bigl( \frac{\kappa}{T_k\bigl( (2
  \lambda_{i'} - hi - lo) / (hi - lo) \bigr)} \tan\theta(b_{i'}, v) \Bigr)^2, \qquad \kappa =
  \prod_{j < i} \frac{\theta_j - lo}{\theta_j - \lambda_{i'}}.$$

No hypothesis relates the two indices, but the intended application has $i' = i$, and then this
is the Kaniel–Paige–Saad estimate. The proof is the Courant–Fischer theorem for the compression.
The competitor $q(A) v$, with $q$ from `Polynomial.exists_deflated_chebyshev`, is orthogonal to
the first $i$ Ritz vectors because $q$ vanishes at the corresponding Ritz values. So its
Rayleigh quotient is at most $\theta_i$, and the deflation cost $\kappa$ is in terms of the Ritz
values, not the eigenvalues. The spread $\lambda_{i'} - lo$ is sharper than the spread
$\lambda_0 - \lambda_{n-1}$ of the usual statement.

The Ritz values are `LinearMap.IsSymmetric.eigenvalues` of the compression, through
`compression.isSymmetric`. -/
theorem eigenvalues_sub_eigenvalues_compression_le_of_mem_Icc (hA : A.IsSymmetric) {v : E} {m : ℕ}
    (hm : Module.finrank 𝕜 (Krylov.subspace A v m) = m) (i : Fin m) (i' : Fin n)
    (hv : (inner 𝕜 (b i') v : 𝕜) ≠ 0) {lo hi : ℝ} (hlohi : lo < hi) (hhi : hi < lam i')
    (hmem : ∀ j : Fin n, i' < j → lam j ∈ Set.Icc lo hi)
    (hθ : ∀ j : Fin m, j < i →
      lam i' < (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j)
    {k : ℕ} (hk : (i : ℕ) + k < m) :
    lam i' - (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm i ≤
      (lam i' - lo) *
        ((∏ j ∈ Finset.Iio i,
            ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j - lo) /
              ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
                lam i')) /
            (T ℝ k).eval ((2 * lam i' - hi - lo) / (hi - lo)) *
          (𝕜 ∙ v).tanAngle (b i')) ^ 2 := by
  set K := Krylov.subspace A v m with hK
  set hC := compression.isSymmetric A K hA with hCdef
  have hvK : v ∈ K := Krylov.self_mem_subspace A v i.pos
  have hu : ‖b i'‖ = 1 := b.norm_eq_one i'
  obtain ⟨q, hqdeg, hq1, hqz, hqb⟩ := exists_deflated_chebyshev (Finset.Iio i)
    (hC.eigenvalues hm) (lam i') (fun j hj => hθ j (Finset.mem_Iio.1 hj)) hlohi hhi k
  set M : ℝ := (∏ j ∈ Finset.Iio i, (hC.eigenvalues hm j - lo) / (hC.eigenvalues hm j - lam i')) /
    (T ℝ k).eval ((2 * lam i' - hi - lo) / (hi - lo)) with hMdef
  -- the competitor vector and its eigenbasis coordinates
  set qc : 𝕜[X] := q.map (algebraMap ℝ 𝕜) with hqc
  set x := aeval A qc v with hx
  have hqq : qc.degree < (m : ℕ) := by
    refine lt_of_le_of_lt degree_map_le (lt_of_le_of_lt hqdeg ?_)
    rw [Nat.cast_lt, Fin.card_Iio]
    omega
  have hxK : x ∈ K := Krylov.aeval_apply_mem_subspace A v hqq
  have hcv : b.repr v i' = (inner 𝕜 (b i') v : 𝕜) := OrthonormalBasis.repr_apply_apply _ _ _
  have hxi : b.repr x i' = b.repr v i' := by
    rw [hx, hqc, repr_aeval_map_apply b hb, hq1, RCLike.ofReal_one, one_mul]
  -- orthogonality to the first `i` Ritz vectors
  have hqne : qc ≠ 0 := by
    intro h0
    have h1 : ((q.eval (lam i') : ℝ) : 𝕜) = 0 := by
      rw [← RCLike.algebraMap_eq_ofReal, ← eval_map_apply, ← hqc, h0, eval_zero]
    rw [hq1] at h1
    simp at h1
  have hnd : qc.natDegree < m := (Polynomial.natDegree_lt_iff_degree_lt hqne).2 hqq
  have hy : (⟨x, hxK⟩ : K) = aeval (compression A K) qc ⟨v, hvK⟩ :=
    Subtype.ext (compression.aeval_apply_of_forall_pow_mem A K qc (x := ⟨v, hvK⟩)
      (fun l hl => Krylov.pow_apply_mem_subspace A v (lt_of_le_of_lt hl hnd))).symm
  have horth : ∀ j : Fin m, j < i →
      (inner 𝕜 (hC.eigenvectorBasis hm j) (⟨x, hxK⟩ : K) : 𝕜) = 0 := by
    intro j hj
    rw [← OrthonormalBasis.repr_apply_apply, hy, hC.repr_aeval_apply hm, hqc, eval_map_apply,
      RCLike.algebraMap_eq_ofReal,
      hqz j (Finset.mem_Iio.2 hj), RCLike.ofReal_zero, zero_mul]
  -- Courant–Fischer for the compression
  have hx0 : x ≠ 0 := by
    intro h0
    refine hv ?_
    rw [← hcv, ← hxi, h0]
    simp
  have hle : A.rayleighQuotient x ≤ hC.eigenvalues hm i :=
    (hC.isGreatest_rayleighQuotient_orthogonal hm i).2
      ⟨_, fun h0 => hx0 (Submodule.coe_eq_zero.2 h0), horth,
        Krylov.rayleighQuotient_compression A _ _⟩
  -- the part of `v` orthogonal to the eigenvector
  set w := v - (inner 𝕜 (b i') v : 𝕜) • b i' with hw
  have hwnorm : ∑ j ∈ Finset.Ioi i', ‖b.repr v j‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← b.repr.norm_map w, EuclideanSpace.norm_sq_eq]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j hj => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity)
    rw [hw, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, inner_sub_right,
      inner_smul_right, b.inner_eq_zero (ne_of_gt (Finset.mem_Ioi.1 hj)), mul_zero, sub_zero]
  -- the numerator and the denominator
  have hN := mul_norm_sq_aeval_sub_re_inner_le b hb q v (c := lam i') (lo := lo) (M := M)
    (lt_trans hlohi hhi).le (Finset.Ioi i')
    (fun j hj => Or.inl (hlam (not_lt.1 (by simpa using hj))))
    (fun j hj => (hmem j (Finset.mem_Ioi.1 hj)).1)
    (fun j hj => hqb _ (hmem j (Finset.mem_Ioi.1 hj)))
  have hDge : ‖(inner 𝕜 (b i') v : 𝕜)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq, ← hcv, ← hxi]
    exact Finset.single_le_sum (f := fun j => ‖b.repr x j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i')
  have hcpos : (0 : ℝ) < ‖(inner 𝕜 (b i') v : 𝕜)‖ ^ 2 := by
    positivity
  have hlo : lo < lam i' := lt_trans hlohi hhi
  have hCD : (lam i' - lo) * M ^ 2 * ∑ j ∈ Finset.Ioi i', ‖b.repr v j‖ ^ 2 ≤
      (lam i' - lo) * (M * (‖w‖ / ‖(inner 𝕜 (b i') v : 𝕜)‖)) ^ 2 *
        ‖(inner 𝕜 (b i') v : 𝕜)‖ ^ 2 := by
    have hne : ‖(inner 𝕜 (b i') v : 𝕜)‖ ≠ 0 := norm_ne_zero_iff.2 hv
    calc (lam i' - lo) * M ^ 2 * ∑ j ∈ Finset.Ioi i', ‖b.repr v j‖ ^ 2
        ≤ (lam i' - lo) * M ^ 2 * ‖w‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hwnorm (mul_nonneg (sub_pos.2 hlo).le (sq_nonneg M))
      _ = _ := by field_simp
  have hgoal := A.sub_rayleighQuotient_le_of_le
    (mul_nonneg (sub_pos.2 hlo).le (sq_nonneg _)) hcpos hDge (hN.trans hCD)
  rw [Submodule.tanAngle_span_singleton hu v]
  linarith

/-!
### The bounds in the form of the literature

Here `iS` is the successor of `i`, and `first` and `last` are the extreme indices. So
$[\lambda_{last}, \lambda_{iS}]$ is the smallest interval that contains the eigenvalues after the
$i$-th, and $\lambda_{first} - \lambda_{last}$ is the spread of the spectrum. The indices are given
as data with their defining properties. This avoids `Fin` arithmetic, and the statements remain
usable when only part of the spectrum is known.
-/

/-- **The Chebyshev bound on the angle between an eigenvector and the Krylov subspace.** Let $b$ be
an orthonormal basis of $E$ with $A b_j = \lambda_j b_j$, where $\lambda_0 \ge \lambda_1 \ge
\dots \ge \lambda_{n-1}$ are real, let $i$ be an index with $i + 1 < n$, and let
$\langle b_i, v \rangle \neq 0$. Suppose that $\lambda_{i+1} < \lambda_i$, that
$\lambda_{n-1} < \lambda_{i+1}$, and that $\lambda_i < \lambda_j$ for all $j < i$. Then for all
$m$ and $k$ with $i + k < m$
$$\tan\theta(b_i, \mathcal{K}_m(A, v)) \le \frac{\kappa_i \tan\theta(b_i, v)}{T_k(1 + 2
  \gamma_i)},$$
where $T_k$ is the Chebyshev polynomial of the first kind and
$$\gamma_i = \frac{\lambda_i - \lambda_{i+1}}{\lambda_{i+1} - \lambda_{n-1}}, \qquad \kappa_i =
  \prod_{j < i} \frac{\lambda_j - \lambda_{n-1}}{\lambda_j - \lambda_i}.$$

The hypotheses make the constants finite: $\lambda_i$ is separated from the eigenvalues before
it and from the one after it, and the spectrum below $\lambda_i$ is not a single point. The
indices $i + 1$ and $n - 1$ are given as `iS` with `i + 1 = iS` and `last` with `IsTop last`.
This is `Lanczos.tan_angle_le_of_mem_Icc` with the interval $[\lambda_{n-1}, \lambda_{i+1}]$,
the smallest one that contains the eigenvalues after the $i$-th. -/
theorem tan_angle_le (i iS last : Fin n) (hiS : (i : ℕ) + 1 = (iS : ℕ))
    (hlast : IsTop last) {v : E}
    (hv : (inner 𝕜 (b i) v : 𝕜) ≠ 0)
    (hgap : lam iS < lam i) (hspread : lam last < lam iS)
    (hsep : ∀ j : Fin n, j < i → lam i < lam j)
    {m k : ℕ} (hm : (i : ℕ) + k < m) :
    (Krylov.subspace A v m).tanAngle (b i) ≤
      (∏ j ∈ Finset.Iio i, (lam j - lam last) / (lam j - lam i)) * (𝕜 ∙ v).tanAngle (b i) /
        (T ℝ k).eval (1 + 2 * ((lam i - lam iS) / (lam iS - lam last))) := by
  have harg : 1 + 2 * ((lam i - lam iS) / (lam iS - lam last)) =
      (2 * lam i - lam iS - lam last) / (lam iS - lam last) := by
    have hne : lam iS - lam last ≠ 0 := by linarith
    field_simp
    ring
  rw [harg, ← div_mul_eq_mul_div]
  refine tan_angle_le_of_mem_Icc b hb i hv hspread hgap (fun j hj => ⟨?_, ?_⟩) hsep hm
  · exact hlam (hlast j)
  · refine hlam ?_
    rw [Fin.le_def, ← hiS]
    omega

/-- **The Kaniel–Paige–Saad bound**, upper half, in the form of [saad2011numerical]. Let $A$ be
symmetric, and let $b$ be an orthonormal basis of $E$ with $A b_j = \lambda_j b_j$, where
$\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{n-1}$ are real. Let
$\mathcal{K}_m = \mathcal{K}_m(A, v)$ have dimension $m$, and let
$\theta_0 \ge \dots \ge \theta_{m-1}$ be the Ritz values, the eigenvalues of the compression of
$A$ to $\mathcal{K}_m$. Let $i$ be an index of the Ritz values and $i'$ an index of the
eigenvalues with $i' + 1 < n$ and $\langle b_{i'}, v \rangle \neq 0$. Suppose that
$\lambda_{i'+1} < \lambda_{i'}$, that $\lambda_{n-1} < \lambda_{i'+1}$, and that
$\lambda_{i'} < \theta_j$ for all $j < i$. Then for every $k$ with $i + k < m$
$$\lambda_{i'} - \theta_i \le (\lambda_0 - \lambda_{n-1}) \Bigl( \frac{\kappa \tan\theta(b_{i'},
  v)}{T_k(1 + 2 \gamma)} \Bigr)^2,$$
where
$$\gamma = \frac{\lambda_{i'} - \lambda_{i'+1}}{\lambda_{i'+1} - \lambda_{n-1}}, \qquad \kappa =
  \prod_{j < i} \frac{\theta_j - \lambda_{n-1}}{\theta_j - \lambda_{i'}}.$$

The deflation constant $\kappa$ is built from the Ritz values, unlike the one in
`Lanczos.tan_angle_le`. The intended application has $i' = i$. The matching lower bound
$0 \le \lambda_i - \theta_i$ is Cauchy interlacing, a statement about the compression alone,
independent of the Krylov structure. This is
`Lanczos.eigenvalues_sub_eigenvalues_compression_le_of_mem_Icc` with the interval
$[\lambda_{n-1}, \lambda_{i'+1}]$, weakened from the sharper spread
$\lambda_{i'} - \lambda_{n-1}$ to $\lambda_0 - \lambda_{n-1}$. The indices $0$, $i' + 1$ and
$n - 1$ are given as `first`, `iS` and `last`. -/
theorem eigenvalues_sub_eigenvalues_compression_le (hA : A.IsSymmetric)
    {v : E} {m : ℕ}
    (hm : Module.finrank 𝕜 (Krylov.subspace A v m) = m) (i : Fin m) (i' iS first last : Fin n)
    (hiS : (i' : ℕ) + 1 = (iS : ℕ)) (hfirst : IsBot first)
    (hlast : IsTop last) (hv : (inner 𝕜 (b i') v : 𝕜) ≠ 0)
    (hgap : lam iS < lam i') (hspread : lam last < lam iS)
    (hθ : ∀ j : Fin m, j < i →
      lam i' < (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j)
    {k : ℕ} (hk : (i : ℕ) + k < m) :
    lam i' - (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm i ≤
      (lam first - lam last) *
        ((∏ j ∈ Finset.Iio i,
            ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j - lam last) /
              ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j - lam i')) *
            (𝕜 ∙ v).tanAngle (b i') /
          (T ℝ k).eval (1 + 2 * ((lam i' - lam iS) / (lam iS - lam last)))) ^ 2 := by
  have harg : 1 + 2 * ((lam i' - lam iS) / (lam iS - lam last)) =
      (2 * lam i' - lam iS - lam last) / (lam iS - lam last) := by
    have hne : lam iS - lam last ≠ 0 := by linarith
    field_simp
    ring
  rw [harg, ← div_mul_eq_mul_div]
  refine le_trans (eigenvalues_sub_eigenvalues_compression_le_of_mem_Icc b hb hlam hA hm i i' hv
    hspread hgap (fun j hj => ⟨?_, ?_⟩) hθ hk) ?_
  · exact hlam (hlast j)
  · refine hlam ?_
    rw [Fin.le_def, ← hiS]
    omega
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h1 := hlam (hfirst i')
    linarith

/-- **The Kaniel–Paige–Saad theorem.** Let $E$ have finite dimension, let $A$ be symmetric, and let
$b$ be an orthonormal eigenbasis $u_0, \dots, u_{n-1}$ with $A u_j = \lambda_j u_j$, where
$\lambda_0 \ge \dots \ge \lambda_{n-1}$ are real; any such basis is allowed, as in a Schur
decomposition $Z^T A Z = \operatorname{diag}(\lambda)$. Let
$\mathcal{K}_m = \mathcal{K}_m(A, v)$ have dimension $m$, and let
$\theta_0 \ge \dots \ge \theta_{m-1}$ be the Ritz values, the eigenvalues of the compression of
$A$ to $\mathcal{K}_m$. Let $i + 1 < n$, $\langle u_i, v \rangle \neq 0$,
$\lambda_{i+1} < \lambda_i$, $\lambda_{n-1} < \lambda_{i+1}$, and $\lambda_i < \theta_j$ for all
$j < i$. Then for every $k$ with $i + k < m$
$$0 \le \lambda_i - \theta_i \le (\lambda_0 - \lambda_{n-1}) \Bigl( \frac{\kappa_i
  \tan\theta(u_i, v)}{T_k(1 + 2 \gamma_i)} \Bigr)^2,$$
where $T_k$ is the Chebyshev polynomial of the first kind and
$$\gamma_i = \frac{\lambda_i - \lambda_{i+1}}{\lambda_{i+1} - \lambda_{n-1}}, \qquad \kappa_i =
  \prod_{j < i} \frac{\theta_j - \lambda_{n-1}}{\theta_j - \lambda_i}.$$
So the Ritz values of the symmetric Lanczos process approach the extreme eigenvalues of $A$ from
below, at a rate that the Chebyshev polynomial of the part of the spectrum below the sought
eigenvalue controls.

The hypothesis that $\mathcal{K}_m$ has dimension $m$ means that the Lanczos process has not
broken down. The index $i$ is given twice, as `i : Fin m` and `i' : Fin n` with equal values,
and the indices $0$, $i + 1$ and $n - 1$ are given as `first`, `iS` and `last`. The lower bound
is Cauchy interlacing, `LinearMap.IsSymmetric.eigenvalues_compression_le`, which is independent
of the Krylov structure. The upper bound is
`Lanczos.eigenvalues_sub_eigenvalues_compression_le`. The special case for the eigenbasis of
Mathlib is `Lanczos.kaniel_paige_saad_eigenvectorBasis`. -/
theorem kaniel_paige_saad [FiniteDimensional 𝕜 E] (hA : A.IsSymmetric) {v : E} {m : ℕ}
    (hm : Module.finrank 𝕜 (Krylov.subspace A v m) = m) (i : Fin m) (i' iS first last : Fin n)
    (hii : (i : ℕ) = (i' : ℕ)) (hiS : (i' : ℕ) + 1 = (iS : ℕ)) (hfirst : IsBot first)
    (hlast : IsTop last) (hv : (inner 𝕜 (b i') v : 𝕜) ≠ 0)
    (hgap : lam iS < lam i') (hspread : lam last < lam iS)
    (hθ : ∀ j : Fin m, j < i →
      lam i' < (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j)
    {k : ℕ} (hk : (i : ℕ) + k < m) :
    lam i' - (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm i ∈
      Set.Icc 0 ((lam first - lam last) *
        ((∏ j ∈ Finset.Iio i,
            ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j - lam last) /
              ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j - lam i')) *
            (𝕜 ∙ v).tanAngle (b i') /
          (T ℝ k).eval (1 + 2 * ((lam i' - lam iS) / (lam iS - lam last)))) ^ 2) := by
  have hn : Module.finrank 𝕜 E = n := by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hmn : m ≤ n := by
    rw [← hm, ← hn]
    exact Submodule.finrank_le _
  refine ⟨?_, eigenvalues_sub_eigenvalues_compression_le b hb hlam hA hm i i' iS first last hiS
    hfirst hlast hv hgap hspread hθ hk⟩
  have h := hA.eigenvalues_compression_le (Krylov.subspace A v m) hn hm hmn i
  rw [show Fin.castLE hmn i = i' from Fin.ext (by simpa using hii),
    hA.eigenvalues_eq_of_apply_eq_ofReal_smul hn b hb hlam] at h
  linarith

end Eigenbasis

/-- **The Kaniel–Paige–Saad theorem for the eigenbasis of Mathlib.** This is
`Lanczos.kaniel_paige_saad` for the eigenbasis `hA.eigenvectorBasis hn` and the eigenvalues
`hA.eigenvalues hn`. Under the same hypotheses, $0 \le \lambda_i - \theta_i \le (\lambda_0 -
\lambda_{n-1}) (\kappa_i \tan\theta(u_i, v) / T_k(1 + 2 \gamma_i))^2$. -/
theorem kaniel_paige_saad_eigenvectorBasis {A : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {v : E} {m : ℕ}
    (hm : Module.finrank 𝕜 (Krylov.subspace A v m) = m) (i : Fin m) (i' iS first last : Fin n)
    (hii : (i : ℕ) = (i' : ℕ)) (hiS : (i' : ℕ) + 1 = (iS : ℕ)) (hfirst : IsBot first)
    (hlast : IsTop last)
    (hv : (inner 𝕜 (hA.eigenvectorBasis hn i') v : 𝕜) ≠ 0)
    (hgap : hA.eigenvalues hn iS < hA.eigenvalues hn i')
    (hspread : hA.eigenvalues hn last < hA.eigenvalues hn iS)
    (hθ : ∀ j : Fin m, j < i → hA.eigenvalues hn i' <
      (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j)
    {k : ℕ} (hk : (i : ℕ) + k < m) :
    hA.eigenvalues hn i' -
        (compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm i ∈
      Set.Icc 0 ((hA.eigenvalues hn first - hA.eigenvalues hn last) *
        ((∏ j ∈ Finset.Iio i,
            ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
                hA.eigenvalues hn last) /
              ((compression.isSymmetric A (Krylov.subspace A v m) hA).eigenvalues hm j -
                hA.eigenvalues hn i')) *
            (𝕜 ∙ v).tanAngle (hA.eigenvectorBasis hn i') /
          (T ℝ k).eval (1 + 2 * ((hA.eigenvalues hn i' - hA.eigenvalues hn iS) /
            (hA.eigenvalues hn iS - hA.eigenvalues hn last)))) ^ 2) :=
  kaniel_paige_saad _ (hA.apply_eigenvectorBasis hn) (hA.eigenvalues_antitone hn) hA hm i i' iS
    first last hii hiS hfirst hlast hv hgap hspread hθ hk

end Lanczos

/-!
### The Arnoldi residual operator on a Krylov subspace

Let $v_0, v_1, \dots$ be the Arnoldi vectors of $A$ and $b$ (`Arnoldi.vec`), the Gram–Schmidt
orthonormalization of the Krylov sequence, with the value $0$ after a breakdown, and let
$h_{ij} = \langle v_i, A v_j \rangle$ be the Arnoldi coefficients (`Arnoldi.coeff`). Let $P_m$ be
the orthogonal projection onto $\mathcal{K}_m(A, b)$. The subdiagonal coefficient $h_{m, m-1}$,
which [saad2011numerical] writes $h_{m+1,m}$ in its numbering from $1$, is the $\beta_m$ of the
Lanczos process.
-/

namespace Arnoldi

variable (A : E →ₗ[𝕜] E) (b : E)

/-- The linear map $(1 - P_m) A$, which sends $x$ to the part of $A x$ outside $\mathcal{K}_m$. -/
private noncomputable def outside (m : ℕ) : E →ₗ[𝕜] E :=
  (LinearMap.id - ((subspace A b m).starProjection : E →ₗ[𝕜] E)) ∘ₗ A

/-- The value of $(1 - P_m) A$ at $x$ is $A x - P_m A x$. -/
private theorem outside_apply (m : ℕ) (x : E) :
    outside A b m x = A x - (subspace A b m).starProjection (A x) := rfl

/-- If $j + 2 \le m$, then $(1 - P_m) A v_j = 0$. -/
private theorem outside_vec_eq_zero {m j : ℕ} (h : j + 2 ≤ m) : outside A b m (vec A b j) = 0 := by
  have hmem : A (vec A b j) ∈ subspace A b m :=
    subspace_mono A b h (map_subspace_le A b (j + 1) ⟨_, vec_mem_subspace A b j, rfl⟩)
  rw [outside_apply, Submodule.starProjection_eq_self_iff.2 hmem, sub_self]

/-- Let $m > 0$. At the last Arnoldi vector of $\mathcal{K}_m$, the image leaves $\mathcal{K}_m$
along $v_m$, with the subdiagonal coefficient as its size:
$$A v_{m-1} - P_m A v_{m-1} = h_{m, m-1} v_m.$$

This is part of Proposition 6.6 of [saad2011numerical]. -/
theorem sub_starProjection_apply_vec_last {m : ℕ} (hm : 0 < m) :
    A (vec A b (m - 1)) - (subspace A b m).starProjection (A (vec A b (m - 1)))
      = coeff A b m (m - 1) • vec A b m := by
  have h := starProjection_apply_vec A b (m - 1)
  rw [show m - 1 + 1 = m from by omega] at h
  exact h

/-- Each Arnoldi vector has norm at most one: $1$ before a breakdown and $0$ after it. -/
private theorem norm_vec_le_one (j : ℕ) : ‖vec A b j‖ ≤ 1 := by
  rcases eq_or_ne (vec A b j) 0 with h | h
  · rw [h, norm_zero]; norm_num
  · rw [norm_vec_eq_one_of_ne_zero A b h]

/-- **The residual operator on the Krylov subspace.** Let $m > 0$ and $y \in \mathcal{K}_m(A, b)$.
Then
$$\|A y - P_m A y\| \le |h_{m, m-1}| \, \|y\|.$$

This is Proposition 6.6 of [saad2011numerical]. Only the last Arnoldi vector contributes,
because $(1 - P_m) A v_j = 0$ for $j + 2 \le m$ and $(1 - P_m) A v_{m-1} = h_{m, m-1} v_m$. -/
theorem norm_sub_starProjection_apply_le {m : ℕ} (hm : 0 < m) {y : E} (hy : y ∈ subspace A b m) :
    ‖A y - (subspace A b m).starProjection (A y)‖ ≤ ‖coeff A b m (m - 1)‖ * ‖y‖ := by
  have hval : outside A b m y
      = (inner 𝕜 (vec A b (m - 1)) y : 𝕜) • coeff A b m (m - 1) • vec A b m := by
    conv_lhs => rw [eq_sum_inner_smul_vec A b hy]
    rw [map_sum, Finset.sum_eq_single (m - 1)]
    · rw [map_smul, outside_apply, sub_starProjection_apply_vec_last A b hm]
    · intro j hj hjne
      have hjlt : j < m := Finset.mem_range.1 hj
      rw [map_smul, outside_vec_eq_zero A b (by omega), smul_zero]
    · intro hc
      exact absurd (Finset.mem_range.2 (by omega)) hc
  rw [← outside_apply, hval, norm_smul, norm_smul]
  have h1 : ‖(inner 𝕜 (vec A b (m - 1)) y : 𝕜)‖ ≤ ‖y‖ :=
    (norm_inner_le_norm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_vec_le_one A b (m - 1)) (norm_nonneg y))
  have h2 : ‖coeff A b m (m - 1)‖ * ‖vec A b m‖ ≤ ‖coeff A b m (m - 1)‖ := by
    simpa using mul_le_mul_of_nonneg_left (norm_vec_le_one A b m) (norm_nonneg _)
  calc ‖(inner 𝕜 (vec A b (m - 1)) y : 𝕜)‖ * (‖coeff A b m (m - 1)‖ * ‖vec A b m‖)
      ≤ ‖y‖ * ‖coeff A b m (m - 1)‖ := mul_le_mul h1 h2 (by positivity) (norm_nonneg y)
    _ = ‖coeff A b m (m - 1)‖ * ‖y‖ := mul_comm _ _

/-- **The dual half of Proposition 6.6** of [saad2011numerical]. Let $A$ be symmetric, let $m > 0$,
and let $x$ be orthogonal to $\mathcal{K}_m(A, b)$. Then
$$\|P_m A x\| \le |h_{m, m-1}| \, \|x\|.$$

The operator $P_m A (1 - P_m)$ is the adjoint of $(1 - P_m) A P_m$. This bound is the hypothesis
on the coupling constant $\gamma$ of `LinearMap.IsSymmetric.sin_angle_ritzVector_le`, so it is
the form in which Proposition 6.6 enters the Ritz vector bounds of `Numlib.Eigen.RayleighRitz`. -/
theorem norm_starProjection_apply_le_of_mem_orthogonal (hA : A.IsSymmetric) {m : ℕ} (hm : 0 < m)
    {x : E} (hx : x ∈ (subspace A b m)ᗮ) :
    ‖(subspace A b m).starProjection (A x)‖ ≤ ‖coeff A b m (m - 1)‖ * ‖x‖ := by
  set K := subspace A b m with hK
  set p := K.starProjection (A x) with hp
  rcases eq_or_lt_of_le (norm_nonneg p) with h0 | hpos
  · rw [← h0]
    positivity
  have hpK : p ∈ K := Submodule.starProjection_apply_mem _ _
  -- `⟪p, p⟫ = ⟪x, A p - P_K (A p)⟫`
  have h1 : (inner 𝕜 (A x) p : 𝕜) = inner 𝕜 p p := by
    have h := Submodule.inner_left_of_mem_orthogonal (𝕜 := 𝕜) hpK
      (Submodule.sub_starProjection_mem_orthogonal (K := K) (A x))
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have h2 : (inner 𝕜 x (A p - K.starProjection (A p)) : 𝕜) = inner 𝕜 p p := by
    rw [inner_sub_right, Submodule.inner_left_of_mem_orthogonal
      (Submodule.starProjection_apply_mem K (A p)) hx, sub_zero, ← hA x p, h1]
  have h3 : ‖p‖ ^ 2 ≤ ‖x‖ * (‖coeff A b m (m - 1)‖ * ‖p‖) := by
    have hcs : ‖(inner 𝕜 x (A p - K.starProjection (A p)) : 𝕜)‖
        ≤ ‖x‖ * ‖A p - K.starProjection (A p)‖ := norm_inner_le_norm _ _
    rw [h2] at hcs
    have hsq : ‖(inner 𝕜 p p : 𝕜)‖ = ‖p‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg p)]
    rw [hsq] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left
      (norm_sub_starProjection_apply_le A b hm hpK) (norm_nonneg x))
  have h4 : ‖p‖ * ‖p‖ ≤ ‖coeff A b m (m - 1)‖ * ‖x‖ * ‖p‖ := by nlinarith [h3]
  exact le_of_mul_le_mul_right h4 hpos

/-- **The norm of the residual operator is the subdiagonal coefficient.** Let the full Krylov
subspace of $A$ and $b$ have finite dimension, and let $0 < m \le g$, where $g$ is the grade of
$b$ with respect to $A$. Then $|h_{m, m-1}|$ is the greatest element of the set
$$\{ \|A y - P_m A y\| : y \in \mathcal{K}_m(A, b), \ \|y\| = 1 \}.$$

This is Proposition 6.6 of [saad2011numerical], in the form that the Ritz bounds of
`Numlib.Eigen.RayleighRitz` use. The bound is `Arnoldi.norm_sub_starProjection_apply_le`, and
the last Arnoldi vector $v_{m-1}$ attains it: $(1 - P_m) A v_{m-1} = h_{m, m-1} v_m$, and $v_m$
is a unit vector unless the process has terminated, in which case $h_{m, m-1} = 0$ too. The
coefficient $h_{m, m-1}$ is `Arnoldi.coeff A b m (m - 1)`, and the grade is `Krylov.grade`. -/
theorem norm_starProjection_comp_orthogonal_eq_coeff [FiniteDimensional 𝕜 (fullSubspace A b)]
    {m : ℕ} (hm : 0 < m) (hgr : m ≤ grade A b) :
    IsGreatest {r : ℝ | ∃ y ∈ subspace A b m, ‖y‖ = 1 ∧
        ‖A y - (subspace A b m).starProjection (A y)‖ = r} ‖coeff A b m (m - 1)‖ := by
  constructor
  · refine ⟨vec A b (m - 1), vec_mem_subspace_of_lt A b (by omega),
      norm_vec_eq_one_of_lt_grade A b (by omega), ?_⟩
    rw [sub_starProjection_apply_vec_last A b hm, norm_smul]
    rcases lt_or_eq_of_le hgr with hlt | heq
    · rw [norm_vec_eq_one_of_lt_grade A b hlt, mul_one]
    · have h0 : vec A b m = 0 := (vec_eq_zero_iff A b m).2 heq.ge
      have hw : w A b (m - 1) = 0 := by
        have hv := vec_succ_eq A b (m - 1)
        rw [show m - 1 + 1 = m from by omega, h0] at hv
        rcases smul_eq_zero.1 hv.symm with hc | hc
        · have : ‖w A b (m - 1)‖ = 0 := by
            simpa using congrArg RCLike.re (inv_eq_zero.1 hc)
          exact norm_eq_zero.1 this
        · exact hc
      have hcoeff : coeff A b m (m - 1) = 0 := by
        have hcs := coeff_succ_self A b (m - 1)
        rw [show m - 1 + 1 = m from by omega] at hcs
        rw [hcs, hw, norm_zero, RCLike.ofReal_zero]
      rw [hcoeff, norm_zero, zero_mul]
  · rintro r ⟨y, hy, hy1, rfl⟩
    simpa [hy1] using norm_sub_starProjection_apply_le A b hm hy

end Arnoldi

namespace Lanczos

/-- **The Ritz vector bound of the Lanczos process** ([saad2011numerical], §6.6.3). Let $A$ be
symmetric, let $m > 0$, and let $\theta$ be a real eigenvalue of the compression $A_m$ of $A$ to
$\mathcal{K}_m = \mathcal{K}_m(A, v)$. Let $A u = \lambda u$ with $u \neq 0$ and $\lambda$ real,
and let $\delta > 0$ satisfy $\delta \|z\| \le \|A_m z - \lambda z\|$ for every
$z \in \mathcal{K}_m$ orthogonal to the $\theta$-eigenspace of $A_m$. Then there is a Ritz pair
$(\theta, w)$ of $A$ on $\mathcal{K}_m$ with
$$\sin\theta(u, \mathbb{K} w) \le \sqrt{1 + \beta_m^2 / \delta^2} \, \sin\theta(u,
  \mathcal{K}_m),$$
where $\beta_m = |h_{m, m-1}|$ is the modulus of the subdiagonal Arnoldi coefficient.

This is `LinearMap.IsSymmetric.sin_angle_ritzVector_le` with the coupling constant
$\gamma = \beta_m$ of `Arnoldi.norm_starProjection_apply_le_of_mem_orthogonal`. The Ritz pair is
`Krylov.IsRitzPair`, and `Lanczos.tan_angle_le` bounds the right side by a Chebyshev quotient. -/
theorem sin_angle_ritzVector_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) {m : ℕ} (hm : 0 < m)
    {δ θ lam : ℝ} (hδ0 : 0 < δ)
    (hθ : Module.End.HasEigenvalue (compression A (subspace A v m)) (θ : 𝕜))
    (hδ : ∀ z ∈ (Module.End.eigenspace (compression A (subspace A v m)) (θ : 𝕜))ᗮ,
      δ * ‖z‖ ≤ ‖compression A (subspace A v m) z - (lam : 𝕜) • z‖)
    {u : E} (hu : A u = (lam : 𝕜) • u) (hu0 : u ≠ 0) :
    ∃ w : E, IsRitzPair A (subspace A v m) (θ : 𝕜) w ∧
      (𝕜 ∙ w).sinAngle u ≤
        Real.sqrt (1 + ‖Arnoldi.coeff A v m (m - 1)‖ ^ 2 / δ ^ 2) *
          (subspace A v m).sinAngle u :=
  hA.sin_angle_ritzVector_le hδ0
    (fun _x hx => Arnoldi.norm_starProjection_apply_le_of_mem_orthogonal A v hA hm hx) hθ hδ hu hu0

/-- **The Lanczos matrix is the compression in the Lanczos basis.** Let the full Krylov subspace of
$A$ and $b$ have finite dimension, let $A$ be symmetric, and let $\mathcal{K}_m(A, b)$ have
dimension $m$, so that the Lanczos process has not broken down before step $m$. Then the
eigenvalues of the real symmetric tridiagonal matrix $T_m$ = `Lanczos.tridiag A b m`, sorted in
decreasing order, are the eigenvalues of the compression of $A$ to $\mathcal{K}_m$, sorted in
decreasing order: the Ritz values.

This is Theorem 6.19 of [saad2003iterative], through
`Arnoldi.hessenbergSq_eq_toMatrix_compression`. The two matrices $T_m$ and $H_m = V_m^H A V_m$
are equal, so their characteristic polynomials agree, and so do their sorted lists of real
roots. This turns `Lanczos.kaniel_paige_saad`, a statement about Ritz values, into Property 5.12
of [quarteroni2000numerical], a statement about the eigenvalues of $H_m$. The left side is
`Matrix.IsHermitian.eigenvalues₀`; the index cast `Fin.cast` matches the two index types. -/
theorem eigenvalues_tridiag_eq_eigenvalues_compression {A : E →ₗ[𝕜] E} (b : E)
    [FiniteDimensional 𝕜 (fullSubspace A b)] (hA : A.IsSymmetric) {m : ℕ}
    (hm : Module.finrank 𝕜 (subspace A b m) = m) :
    (Matrix.isHermitian_iff_isSymm.mpr (tridiag_isSymm A b m)).eigenvalues₀
      = (compression.isSymmetric A (subspace A b m) hA).eigenvalues hm
        ∘ Fin.cast (Fintype.card_fin m) := by
  have hmg : m ≤ grade A b := by
    rw [finrank_subspace] at hm
    exact min_eq_left_iff.mp hm
  set hT := Matrix.isHermitian_iff_isSymm.mpr (tridiag_isSymm A b m) with hTdef
  have hchar : (compression A (subspace A b m)).charpoly
      = (tridiag A b m).charpoly.map (algebraMap ℝ 𝕜) := by
    rw [← LinearMap.charpoly_toMatrix _ (Arnoldi.orthonormalBasis A b hmg).toBasis,
      ← Arnoldi.hessenbergSq_eq_toMatrix_compression A b hmg, hessenbergSq_eq_map_tridiag b hA,
      Matrix.charpoly_map]
  have hcast : List.ofFn ((compression.isSymmetric A (subspace A b m) hA).eigenvalues hm
      ∘ Fin.cast (Fintype.card_fin m))
      = List.ofFn ((compression.isSymmetric A (subspace A b m) hA).eigenvalues hm) :=
    (List.ofFn_congr (Fintype.card_fin m).symm
      ((compression.isSymmetric A (subspace A b m) hA).eigenvalues hm)).symm
  rw [← List.ofFn_inj, ← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀, hcast,
    ← LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues, hchar,
    hT.splits_charpoly.roots_map, Multiset.map_map]
  congr 2
  ext x
  simp

/-- The **Ritz values** $\theta_0 \ge \theta_1 \ge \dots \ge \theta_{m-1}$ of the Lanczos process:
the eigenvalues of the Lanczos tridiagonal matrix $T_m$ = `Lanczos.tridiag A b m`, sorted in
decreasing order and indexed by `Fin m`.

These are the Ritz values of (10.1.7) of [golub2013matrix]. If $\mathcal{K}_m(A, b)$ has
dimension $m$, they are the eigenvalues of the compression of $A$ to the Krylov subspace
(`Lanczos.ritzValues_eq_eigenvalues_compression`). The definition uses
`Matrix.IsHermitian.sortedEigenvalues`. -/
noncomputable def ritzValues (A : E →ₗ[𝕜] E) (b : E) (m : ℕ) : Fin m → ℝ :=
  (Matrix.isHermitian_iff_isSymm.mpr (tridiag_isSymm A b m)).sortedEigenvalues

/-- Let the full Krylov subspace of $A$ and $b$ have finite dimension, let $A$ be symmetric, and let
$\mathcal{K}_m(A, b)$ have dimension $m$. Then the Ritz values `Lanczos.ritzValues A b m` are
the eigenvalues of the compression of $A$ to $\mathcal{K}_m(A, b)$, sorted in decreasing order.

This is `Lanczos.eigenvalues_tridiag_eq_eigenvalues_compression`, with the index type `Fin m`. -/
theorem ritzValues_eq_eigenvalues_compression {A : E →ₗ[𝕜] E} (b : E)
    [FiniteDimensional 𝕜 (fullSubspace A b)] (hA : A.IsSymmetric) {m : ℕ}
    (hm : Module.finrank 𝕜 (subspace A b m) = m) :
    ritzValues A b m = (compression.isSymmetric A (subspace A b m) hA).eigenvalues hm := by
  ext i
  rw [ritzValues, Matrix.IsHermitian.sortedEigenvalues_apply,
    eigenvalues_tridiag_eq_eigenvalues_compression b hA hm]
  simp [Fin.cast]

end Lanczos

/-! ### The block Kaniel–Paige–Saad bound -/

namespace BlockLanczos

section Eigenbasis

variable {A : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
  {lam : Fin n → ℝ} (hb : ∀ j, A (b j) = (lam j : 𝕜) • b j) (hlam : Antitone lam)
  (hA : A.IsSymmetric)
include hb hlam hA

/-- For a real polynomial $q$ of degree less than $k$ with $|q| \ge 1$ at
$\lambda_0, \dots, \lambda_{i'}$ and $|q| \le M$ at $\lambda_j$ for $j \ge p$, the $i$-th Ritz
value $\mu_i$ on the block Krylov subspace satisfies $\lambda_{i'} - (\lambda_{first} -
\lambda_{last}) (M t)^2 \le \mu_i$; the competitor is $q(A) y$ for a nonzero $y$ in the span of
the starting block, orthogonal to the first $i$ Ritz vectors and with no eigencomponents between
$i'$ and $p$. -/
private theorem sub_le_eigenvalues_compression_of_poly {p : ℕ} (v : Fin p → E)
    (hv : LinearIndependent 𝕜 v) {t : ℝ}
    (ht : ∀ x ∈ Submodule.span 𝕜 (Set.range v),
      ‖x - (Submodule.span 𝕜 (b '' {j | (j : ℕ) < p})).starProjection x‖ ≤
        t * ‖(Submodule.span 𝕜 (b '' {j | (j : ℕ) < p})).starProjection x‖)
    {k d : ℕ} (hd : Module.finrank 𝕜 (Krylov.blockSubspace A v k) = d) (i : Fin d)
    (i' first last : Fin n) (hii : (i : ℕ) = i') (hip : (i' : ℕ) < p)
    (hfirst : IsBot first) (hlast : IsTop last)
    (q : ℝ[X]) (hq : q.degree < k) {M : ℝ}
    (hqM : ∀ j : Fin n, p ≤ (j : ℕ) → |q.eval (lam j)| ≤ M)
    (hq1 : ∀ j : Fin n, (j : ℕ) ≤ i' → 1 ≤ |q.eval (lam j)|) :
    lam i' - (lam first - lam last) * (M * t) ^ 2 ≤
      (compression.isSymmetric A (Krylov.blockSubspace A v k) hA).eigenvalues hd i := by
  classical
  set W := Krylov.blockSubspace A v k with hW
  set hC := compression.isSymmetric A W hA with hCdef
  set V := Submodule.span 𝕜 (Set.range v) with hV
  set P := (Submodule.span 𝕜 (b '' {j | (j : ℕ) < p})).starProjection with hP
  set qc : 𝕜[X] := q.map (algebraMap ℝ 𝕜) with hqc
  have hqcdeg : qc.degree < k := lt_of_le_of_lt degree_map_le hq
  -- `q(A)` maps the span of the block into the block Krylov subspace
  have hmemW : ∀ y ∈ V, aeval A qc y ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      exact Krylov.subspace_le_blockSubspace A v l k
        (Krylov.aeval_apply_mem_subspace A (v l) hqcdeg)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact W.add_mem hy hz
    | smul c y _ hy => rw [map_smul]; exact W.smul_mem c hy
  -- the constraints: orthogonality to the first `i` Ritz vectors, no component in `(i', p)`
  set S : Finset (Fin n) := Finset.univ.filter fun j : Fin n => (i' : ℕ) < j ∧ (j : ℕ) < p
    with hS
  let g : V →ₗ[𝕜] (Fin i → 𝕜) × (S → 𝕜) :=
    LinearMap.prod
      (LinearMap.pi fun j : Fin i =>
        innerₛₗ 𝕜 ((hC.eigenvectorBasis hd ⟨j, j.2.trans i.2⟩ : W) : E) ∘ₗ
          aeval A qc ∘ₗ V.subtype)
      (LinearMap.pi fun j : S => innerₛₗ 𝕜 (b j) ∘ₗ V.subtype)
  have hVdim : Module.finrank 𝕜 V = p := by rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hScard : S.card ≤ p - 1 - i' := by
    have h := Finset.card_le_card_of_injOn (s := S) (t := Finset.Ioo (i' : ℕ) p)
      (fun j : Fin n => (j : ℕ))
      (fun j hj => by
        have h := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).2
        exact Finset.mem_coe.2 (Finset.mem_Ioo.2 h))
      (fun a _ c _ h => Fin.ext h)
    rw [Nat.card_Ioo] at h
    omega
  have hdim : Module.finrank 𝕜 ((Fin i → 𝕜) × (S → 𝕜)) < Module.finrank 𝕜 V := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, hVdim]
    omega
  obtain ⟨y, hyker, hy0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  have hg : g y = 0 := LinearMap.mem_ker.1 hyker
  have horth1 : ∀ j : Fin i, inner 𝕜 ((hC.eigenvectorBasis hd ⟨j, j.2.trans i.2⟩ : W) : E)
      (aeval A qc (y : E)) = 0 := fun j => by
    have := congrFun (congrArg Prod.fst hg) j
    simpa [g] using this
  have horth2 : ∀ j ∈ S, inner 𝕜 (b j) (y : E) = 0 := fun j hj => by
    have := congrFun (congrArg Prod.snd hg) ⟨j, hj⟩
    simpa [g] using this
  -- the competitor
  set yE : E := (y : E) with hyE
  have hyE0 : yE ≠ 0 := fun h => hy0 (Subtype.ext h)
  set x : E := aeval A qc yE with hx
  have hxW : x ∈ W := hmemW yE y.2
  have hrepr : ∀ j : Fin n, b.repr x j = ((q.eval (lam j) : ℝ) : 𝕜) * b.repr yE j := fun j =>
    Lanczos.repr_aeval_map_apply b hb q yE j
  have hzero : ∀ j : Fin n, (i' : ℕ) < j → (j : ℕ) < p → b.repr yE j = 0 := fun j h1 h2 => by
    rw [OrthonormalBasis.repr_apply_apply]
    exact horth2 j (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩)
  -- the angle hypothesis in coordinates
  have hPy := b.norm_sq_starProjection_span_image ({j | (j : ℕ) < p} : Set (Fin n)) yE
  have hQy := b.norm_sq_sub_starProjection_span_image ({j | (j : ℕ) < p} : Set (Fin n)) yE
  have hty : ‖yE - P yE‖ ^ 2 ≤ t ^ 2 * ‖P yE‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ht yE y.2) 2
  have hPpos : 0 < ‖P yE‖ ^ 2 := by
    refine pow_pos (norm_pos_iff.2 fun h0 => hyE0 ?_) 2
    have h := ht yE y.2
    rw [h0, sub_zero, norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  -- the denominator
  have hden : ‖P yE‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hPy, ← b.repr.norm_map x, EuclideanSpace.norm_sq_eq (b.repr x)]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with hj
    · rw [hrepr, norm_mul, RCLike.norm_ofReal, mul_pow]
      by_cases h1 : (j : ℕ) ≤ i'
      · have h := hq1 j h1
        have h2 : 1 ≤ |q.eval (lam j)| ^ 2 := by nlinarith
        nlinarith [sq_nonneg ‖b.repr yE j‖]
      · rw [hzero j (by omega) hj]
        simp
    · positivity
  -- the numerator
  set s : Finset (Fin n) := Finset.univ.filter fun j : Fin n => p ≤ (j : ℕ) with hs
  have hspread : lam i' - lam last ≤ lam first - lam last := by
    linarith [hlam (hfirst i')]
  have hN : lam i' * ‖x‖ ^ 2 - RCLike.re (inner 𝕜 (A x) x) ≤
      (lam first - lam last) * (M * t) ^ 2 * ‖P yE‖ ^ 2 := by
    have h := Lanczos.mul_norm_sq_aeval_sub_re_inner_le b hb q yE (c := lam i') (lo := lam last)
      (M := M) (hlam (hlast i')) s
      (fun j hj => by
        have hjp : (j : ℕ) < p := by simpa [hs] using hj
        by_cases h1 : (j : ℕ) ≤ i'
        · exact Or.inl (hlam (Fin.le_def.2 h1))
        · exact Or.inr (hzero j (by omega) hjp))
      (fun j _ => hlam (hlast j))
      (fun j hj => hqM j (by simpa [hs] using hj))
    have hsum : ∑ j ∈ s, ‖b.repr yE j‖ ^ 2 = ‖yE - P yE‖ ^ 2 := by
      rw [hQy, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : (j : ℕ) < p
      · simp [hj, not_le.2 hj]
      · simp [hj, not_lt.1 hj]
    rw [hsum] at h
    refine h.trans ?_
    have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
    calc (lam i' - lam last) * M ^ 2 * ‖yE - P yE‖ ^ 2
        ≤ (lam first - lam last) * M ^ 2 * (t ^ 2 * ‖P yE‖ ^ 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hspread hM2) hty (by positivity) ?_
          exact mul_nonneg (by linarith [hlam (hlast i')]) hM2
      _ = (lam first - lam last) * (M * t) ^ 2 * ‖P yE‖ ^ 2 := by ring
  -- the competitor is admissible for the Courant–Fischer characterization of `μ_i`
  have hx0 : x ≠ 0 := fun h => by
    have := hPpos.trans_le hden
    rw [h, norm_zero] at this
    simp at this
  have hle : A.rayleighQuotient x ≤ hC.eigenvalues hd i :=
    (hC.isGreatest_rayleighQuotient_orthogonal hd i).2
      ⟨⟨x, hxW⟩, fun h0 => hx0 (congrArg Subtype.val h0), fun j hj => horth1 ⟨j, hj⟩,
        Krylov.rayleighQuotient_compression A W ⟨x, hxW⟩⟩
  have hbound := A.sub_rayleighQuotient_le_of_le
    (mul_nonneg (by linarith [hlam (hfirst last)]) (sq_nonneg (M * t))) hPpos hden hN
  linarith

/-- **The block Kaniel–Paige–Saad theorem.** Let $E$ have finite dimension, let $A$ be symmetric,
and let $z_0, \dots, z_{n-1}$ be an orthonormal eigenbasis with $A z_j = \lambda_j z_j$, where
$\lambda_0 \ge \dots \ge \lambda_{n-1}$ are real; any such basis is allowed, as in a Schur
decomposition $Z^T A Z = \operatorname{diag}(\lambda)$. Let $v_0, \dots, v_{p-1}$ be a linearly
independent starting block, and let $\mu_0 \ge \mu_1 \ge \dots$ be the eigenvalues of the
compression of $A$ to the block Krylov subspace
$$\mathcal{K}_{k+1}(A, v) = \operatorname{span}\{ A^j v_l : j \le k, \ l < p \}.$$
Let $P$ be the orthogonal projection onto $\operatorname{span}\{z_0, \dots, z_{p-1}\}$, and
suppose that $\|x - P x\| \le t \|P x\|$ for every $x$ in the span of the block. Then for every
index $i < p$ of the Ritz values with $p < n$
$$\lambda_i - (\lambda_0 - \lambda_{n-1}) \Bigl( \frac{t}{T_k(1 + 2 \rho_i)} \Bigr)^2 \le \mu_i
  \le \lambda_i, \qquad \rho_i = \frac{\lambda_i - \lambda_p}{\lambda_p - \lambda_{n-1}},$$
where $T_k$ is the Chebyshev polynomial of the first kind.

This theorem is due to Underwood; it is Theorem 10.3.2 of [golub2013matrix]. The best constant
$t$ is $\tan\varphi_p$, the tangent of the largest principal angle between the span of the block
and the span of $z_0, \dots, z_{p-1}$.

The indices are given as data: `i'` with the value of `i` in the numbering of the eigenvalues,
`iP` with the value $p$, and `first` and `last` with `IsBot first` and `IsTop last`. No gap
hypothesis is needed. When $\lambda_p = \lambda_{n-1}$ or $\lambda_i = \lambda_p$, the quantity
$\rho_i$ is $0$ (by the Lean convention $x / 0 = 0$, or as a true zero), $T_k(1) = 1$, and the
bound holds with the constant competitor. The upper bound is Cauchy interlacing. The lower bound
is the Courant–Fischer theorem for the compression, with the competitor $c(A) y$: here $c$ is
the Chebyshev polynomial of $[\lambda_{n-1}, \lambda_p]$ normalized at $\lambda_i$, and $y$ is a
vector in the span of the block that a dimension count makes orthogonal to the first $i$ Ritz
vectors and free of eigencomponents strictly between $i$ and $p$. The special case for the
eigenbasis of Mathlib is `BlockLanczos.kaniel_paige_saad_eigenvectorBasis`. -/
theorem kaniel_paige_saad {p : ℕ} (v : Fin p → E) (hv : LinearIndependent 𝕜 v) {t : ℝ}
    (ht : ∀ x ∈ Submodule.span 𝕜 (Set.range v),
      ‖x - (Submodule.span 𝕜 (b '' {j | (j : ℕ) < p})).starProjection x‖ ≤
        t * ‖(Submodule.span 𝕜 (b '' {j | (j : ℕ) < p})).starProjection x‖)
    {k d : ℕ} (hd : Module.finrank 𝕜 (Krylov.blockSubspace A v (k + 1)) = d) (i : Fin d)
    (i' iP first last : Fin n) (hii : (i : ℕ) = i') (hiP : (i' : ℕ) < iP) (hP : (iP : ℕ) = p)
    (hfirst : IsBot first) (hlast : IsTop last) :
    lam i' - (lam first - lam last) *
        (t / (T ℝ k).eval (1 + 2 * ((lam i' - lam iP) / (lam iP - lam last)))) ^ 2 ≤
        (compression.isSymmetric A (Krylov.blockSubspace A v (k + 1)) hA).eigenvalues hd i ∧
      (compression.isSymmetric A (Krylov.blockSubspace A v (k + 1)) hA).eigenvalues hd i ≤
        lam i' := by
  have hn : Module.finrank 𝕜 E = n := by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hdn : d ≤ n := by
    rw [← hd, ← hn]
    exact Submodule.finrank_le _
  refine ⟨?_, ?_⟩
  swap
  · have h := hA.eigenvalues_compression_le (Krylov.blockSubspace A v (k + 1)) hn hd hdn i
    rwa [show Fin.castLE hdn i = i' from Fin.ext (by simpa using hii),
      hA.eigenvalues_eq_of_apply_eq_ofReal_smul hn b hb hlam] at h
  have hip : (i' : ℕ) < p := hP ▸ hiP
  have hPi : lam iP ≤ lam i' := hlam hiP.le
  have hlP : lam last ≤ lam iP := hlam (hlast iP)
  set γ := 1 + 2 * ((lam i' - lam iP) / (lam iP - lam last)) with hγ
  by_cases hgen : lam last < lam iP ∧ lam iP < lam i'
  · obtain ⟨h1, h2⟩ := hgen
    have hden : 0 < lam iP - lam last := by linarith
    have hγ1 : 1 ≤ γ := by
      have : 0 ≤ (lam i' - lam iP) / (lam iP - lam last) := div_nonneg (by linarith) hden.le
      linarith
    have hT : 1 ≤ (T ℝ k).eval γ := one_le_eval_T hγ1 k
    set a : ℝ := 2 / (lam iP - lam last) with ha
    set c : ℝ := -(lam iP + lam last) / (lam iP - lam last) with hc
    have haff : ∀ s : ℝ, a * s + c = (2 * s - lam iP - lam last) / (lam iP - lam last) := by
      intro s
      rw [ha, hc]
      field_simp
      ring
    have haγ : a * lam i' + c = γ := by
      rw [haff, hγ]
      field_simp
      ring
    set q : ℝ[X] :=
      Polynomial.C ((T ℝ k).eval γ)⁻¹ * (T ℝ k).comp (Polynomial.C a * X + Polynomial.C c)
      with hq
    have hqeval : ∀ s : ℝ, q.eval s = ((T ℝ k).eval γ)⁻¹ * (T ℝ k).eval (a * s + c) := by
      intro s
      simp [hq, eval_comp]
    have hqdeg : q.degree < (k + 1 : ℕ) := by
      refine lt_of_le_of_lt degree_le_natDegree ?_
      have hlin : (Polynomial.C a * X + Polynomial.C c).natDegree ≤ 1 := by
        refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
        exact (natDegree_C_mul_le _ _).trans (by simp)
      have hcomp : ((T ℝ k).comp (Polynomial.C a * X + Polynomial.C c)).natDegree ≤ k := by
        refine natDegree_comp_le.trans ?_
        rw [natDegree_T]
        simpa using Nat.mul_le_mul (le_refl k) hlin
      have := (natDegree_C_mul_le ((T ℝ k).eval γ)⁻¹ _).trans hcomp
      exact_mod_cast Nat.lt_succ_of_le this
    have hmain := sub_le_eigenvalues_compression_of_poly b hb hlam hA v hv ht hd i i' first last
      hii hip hfirst hlast q hqdeg (M := ((T ℝ k).eval γ)⁻¹)
      (fun j hj => by
        have hjP : iP ≤ j := Fin.le_def.2 (by omega)
        have hl : lam last ≤ lam j := hlam (hlast j)
        have hu : lam j ≤ lam iP := hlam hjP
        have habs : |a * lam j + c| ≤ 1 := by
          rw [haff, abs_le, le_div_iff₀ hden, div_le_iff₀ hden]
          constructor <;> linarith
        rw [hqeval, abs_mul, abs_of_pos (inv_pos.2 (by linarith))]
        have := abs_eval_T_real_le_one (k : ℤ) habs
        calc ((T ℝ k).eval γ)⁻¹ * |(T ℝ k).eval (a * lam j + c)| ≤ ((T ℝ k).eval γ)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left this (inv_nonneg.2 (by linarith))
          _ = ((T ℝ k).eval γ)⁻¹ := mul_one _)
      (fun j hj => by
        have hij : lam i' ≤ lam j := hlam (Fin.le_def.2 hj)
        have harg : γ ≤ a * lam j + c := by
          rw [← haγ]
          have : 0 < a := div_pos two_pos hden
          nlinarith
        have hmono := eval_T_le_eval_T hγ1 harg k
        rw [hqeval, abs_of_nonneg (mul_nonneg (inv_nonneg.2 (by linarith)) (by linarith)),
          le_inv_mul_iff₀ (by linarith), mul_one]
        exact hmono)
    rwa [show ((T ℝ k).eval γ)⁻¹ * t = t / (T ℝ k).eval γ by ring] at hmain
  · have hγ1 : γ = 1 := by
      rw [hγ]
      rcases eq_or_lt_of_le hlP with h | h
      · rw [h, sub_self, div_zero]; ring
      · have : lam iP = lam i' := le_antisymm hPi (not_lt.1 fun h' => hgen ⟨h, h'⟩)
        rw [this, sub_self, zero_div]; ring
    have hmain := sub_le_eigenvalues_compression_of_poly b hb hlam hA v hv ht hd i i' first last
      hii hip hfirst hlast 1 (by rw [degree_one]; exact_mod_cast Nat.succ_pos k) (M := 1)
      (fun j _ => by simp) (fun j _ => by simp)
    rw [hγ1, T_eval_one, div_one]
    simpa using hmain

end Eigenbasis

/-- **The block Kaniel–Paige–Saad theorem for the eigenbasis of Mathlib.** This is
`BlockLanczos.kaniel_paige_saad` for the eigenbasis `hA.eigenvectorBasis hn` and the eigenvalues
`hA.eigenvalues hn`. Under the same hypotheses, $\lambda_i - (\lambda_0 - \lambda_{n-1}) (t /
T_k(1 + 2 \rho_i))^2 \le \mu_i \le \lambda_i$. -/
theorem kaniel_paige_saad_eigenvectorBasis {A : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] {n : ℕ}
    (hA : A.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {p : ℕ} (v : Fin p → E)
    (hv : LinearIndependent 𝕜 v) {t : ℝ}
    (ht : ∀ x ∈ Submodule.span 𝕜 (Set.range v),
      ‖x - (Submodule.span 𝕜 (hA.eigenvectorBasis hn '' {j | (j : ℕ) < p})).starProjection x‖ ≤
        t * ‖(Submodule.span 𝕜 (hA.eigenvectorBasis hn '' {j | (j : ℕ) < p})).starProjection x‖)
    {k d : ℕ} (hd : Module.finrank 𝕜 (Krylov.blockSubspace A v (k + 1)) = d) (i : Fin d)
    (i' iP first last : Fin n) (hii : (i : ℕ) = i') (hiP : (i' : ℕ) < iP) (hP : (iP : ℕ) = p)
    (hfirst : IsBot first) (hlast : IsTop last) :
    hA.eigenvalues hn i' - (hA.eigenvalues hn first - hA.eigenvalues hn last) *
        (t / (T ℝ k).eval (1 + 2 * ((hA.eigenvalues hn i' - hA.eigenvalues hn iP) /
          (hA.eigenvalues hn iP - hA.eigenvalues hn last)))) ^ 2 ≤
        (compression.isSymmetric A (Krylov.blockSubspace A v (k + 1)) hA).eigenvalues hd i ∧
      (compression.isSymmetric A (Krylov.blockSubspace A v (k + 1)) hA).eigenvalues hd i ≤
        hA.eigenvalues hn i' :=
  kaniel_paige_saad _ (hA.apply_eigenvectorBasis hn) (hA.eigenvalues_antitone hn) hA v hv ht hd i
    i' iP first last hii hiP hP hfirst hlast

end BlockLanczos

/-!
### The distance to a Krylov subspace without symmetry

For a diagonalizable operator, the variational argument still gives a one-sided bound, with the
triangle inequality in place of the theorem of Pythagoras of the symmetric case. The cost is the
factor $\xi_i = \sum_{k \neq i} |\alpha_k| / |\alpha_i|$, which measures how much of the starting
vector lies away from the eigenvector that is approximated. Here $P_m$ is the orthogonal projection
onto $\mathcal{K}_m(A, v)$.
-/

namespace Arnoldi

section Diagonalizable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E →ₗ[𝕜] E} {u : ι → E} {lam α : ι → 𝕜}
  {v : E} {i : ι} {m : ℕ}

/-- **The distance from an eigenvector to a Krylov subspace, for one competitor polynomial.** Let
$u_k$ be a finite family of vectors with $A u_k = \lambda_k u_k$, let $v = \sum_k \alpha_k u_k$,
and let $\alpha_i \neq 0$. Then for every polynomial $p$ of degree less than $m$ with
$p(\lambda_i) = 1$
$$\|u_i - P_m u_i\| \le \frac{\sum_{k \neq i} |\alpha_k| \, |p(\lambda_k)| \,
  \|u_k\|}{|\alpha_i|}.$$

The competitor vector is $\alpha_i^{-1} p(A) v$, whose $u_i$-component is exactly $u_i$; the
rest is the combination of the other $u_k$ weighted by the values of $p$ at their eigenvalues.
The proof uses neither the linear independence of the family, nor the invertibility of $A$, nor
any symmetry, only that $v$ is the given combination of eigenvectors. So the family may repeat
an eigenvalue or omit part of the spectrum. -/
theorem norm_sub_starProjection_le_of_eval_eq_one (hu : ∀ k, A (u k) = lam k • u k)
    (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) {p : 𝕜[X]} (hdeg : p.degree < m)
    (hp : p.eval (lam i) = 1) :
    ‖u i - (subspace A v m).starProjection (u i)‖ ≤
      (∑ k ∈ Finset.univ.erase i, ‖α k‖ * ‖p.eval (lam k)‖ * ‖u k‖) / ‖α i‖ := by
  have hmem : (aeval A p) v ∈ subspace A v m :=
    (Krylov.mem_subspace_iff_exists_aeval A v).2 ⟨p, hdeg, rfl⟩
  refine ((isBestApprox_starProjection _ (u i)).2 _ (Submodule.smul_mem _ (α i)⁻¹ hmem)).trans ?_
  have hexp : (α i)⁻¹ • (aeval A p) v
      = ∑ k, ((α i)⁻¹ * α k * p.eval (lam k)) • u k := by
    rw [hv, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Polynomial.aeval_apply_of_apply_eq_smul (hu k), smul_smul, smul_smul]
  have hsplit : ∑ k, ((α i)⁻¹ * α k * p.eval (lam k)) • u k
      = u i + ∑ k ∈ Finset.univ.erase i, ((α i)⁻¹ * α k * p.eval (lam k)) • u k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hp, mul_one, inv_mul_cancel₀ hα, one_smul]
  have hdiff : u i - (α i)⁻¹ • (aeval A p) v
      = -∑ k ∈ Finset.univ.erase i, ((α i)⁻¹ * α k * p.eval (lam k)) • u k := by
    rw [hexp, hsplit]; abel
  rw [hdiff, norm_neg, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
  rw [norm_smul, norm_mul, norm_mul, norm_inv]
  ring

/-- **The distance from an eigenvector to a Krylov subspace, with a bound on the polynomial.** Let
$u_k$ be a finite family of unit vectors with $A u_k = \lambda_k u_k$, let
$v = \sum_k \alpha_k u_k$, and let $\alpha_i \neq 0$. Let $p$ be a polynomial of degree less
than $m$ with $p(\lambda_i) = 1$, and let $|p(\lambda_k)| \le M$ for all $k \neq i$. Then
$$\|u_i - P_m u_i\| \le \xi_i M, \qquad \xi_i = \sum_{k \neq i} \frac{|\alpha_k|}{|\alpha_i|}.$$

This is Lemma 6.2 of [saad2011numerical]. The bound $M$ is given as data, as in the other
polynomial estimates of this library. `Arnoldi.norm_sub_starProjection_le_iInf` is the form with
the best polynomial, and `Arnoldi.norm_sub_starProjection_le_of_mem_closedBall` is the explicit
estimate for a disc that encloses the rest of the spectrum. -/
theorem norm_sub_starProjection_le_mul (hu : ∀ k, A (u k) = lam k • u k) (hu1 : ∀ k, ‖u k‖ = 1)
    (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) {p : 𝕜[X]} (hdeg : p.degree < m)
    (hp : p.eval (lam i) = 1) {M : ℝ} (hM : ∀ k ≠ i, ‖p.eval (lam k)‖ ≤ M) :
    ‖u i - (subspace A v m).starProjection (u i)‖ ≤
      (∑ k ∈ Finset.univ.erase i, ‖α k‖ / ‖α i‖) * M := by
  refine (norm_sub_starProjection_le_of_eval_eq_one hu hv hα hdeg hp).trans ?_
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [hu1 k, mul_one]
  calc ‖α k‖ * ‖p.eval (lam k)‖ / ‖α i‖
      = ‖α k‖ / ‖α i‖ * ‖p.eval (lam k)‖ := by ring
    _ ≤ ‖α k‖ / ‖α i‖ * M :=
        mul_le_mul_of_nonneg_left (hM k (Finset.ne_of_mem_erase hk)) (by positivity)

/-- **The distance from an eigenvector to a Krylov subspace, with the optimal polynomial.** Let
$u_k$ be a finite family of vectors with $A u_k = \lambda_k u_k$, let $v = \sum_k \alpha_k u_k$,
let $\alpha_i \neq 0$, and let $m > 0$. Then
$$\|u_i - P_m u_i\| \le \inf_{\deg p < m, \ p(\lambda_i) = 1} \frac{\sum_{k \neq i} |\alpha_k|
  \, |p(\lambda_k)| \, \|u_k\|}{|\alpha_i|}.$$

This is Lemma 6.2 of [saad2011numerical] with the optimal polynomial. The source bounds each
$|p(\lambda_k)|$ by their maximum $\varepsilon_i^{(m)}$ and states the result as
$\xi_i \varepsilon_i^{(m)}$ with $\xi_i = \sum_{k \neq i} |\alpha_k| / |\alpha_i|$. The bound
with the weights inside the sum is sharper, and `Arnoldi.norm_sub_starProjection_le_mul` weakens
it to the printed form. The hypothesis $m > 0$ is necessary: for $m = 0$ the Krylov subspace is
$\{0\}$, the left side is $\|u_i\|$, and the set of polynomials is empty, so the Lean infimum is
$0$. -/
theorem norm_sub_starProjection_le_iInf (hu : ∀ k, A (u k) = lam k • u k)
    (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) (hm : 0 < m) :
    ‖u i - (subspace A v m).starProjection (u i)‖ ≤
      ⨅ p : {p : 𝕜[X] // p.degree < m ∧ p.eval (lam i) = 1},
        (∑ k ∈ Finset.univ.erase i, ‖α k‖ * ‖(p : 𝕜[X]).eval (lam k)‖ * ‖u k‖) / ‖α i‖ := by
  have hone : (1 : 𝕜[X]).degree < (m : ℕ) := by
    rw [Polynomial.degree_one]
    exact_mod_cast hm
  have : Nonempty {p : 𝕜[X] // p.degree < m ∧ p.eval (lam i) = 1} := ⟨⟨1, hone, by simp⟩⟩
  exact le_ciInf fun p => norm_sub_starProjection_le_of_eval_eq_one hu hv hα p.2.1 p.2.2

/-- **Geometric decay of the distance for a disc.** Let $u_k$ be a finite family of unit vectors
with $A u_k = \lambda_k u_k$, let $v = \sum_k \alpha_k u_k$, let $\alpha_i \neq 0$, and let
$m > 0$. Let $c$ be a scalar with $\lambda_i \neq c$, and let $|\lambda_k - c| \le \rho$ for all
$k \neq i$. Then
$$\|u_i - P_m u_i\| \le \xi_i \Bigl( \frac{\rho}{|\lambda_i - c|} \Bigr)^{m-1}, \qquad \xi_i =
  \sum_{k \neq i} \frac{|\alpha_k|}{|\alpha_i|}.$$

This is Proposition 6.10 of [saad2011numerical]. The competitor is
$p(z) = ((z - c) / (\lambda_i - c))^{m-1}$, which `Polynomial.zarantonello` shows to be optimal
on a circle. The bound is informative exactly when $\rho < |\lambda_i - c|$, that is, when the
disc separates $\lambda_i$ from the rest of the spectrum. No hypothesis requires this, because
the inequality holds in all cases. -/
theorem norm_sub_starProjection_le_of_mem_closedBall (hu : ∀ k, A (u k) = lam k • u k)
    (hu1 : ∀ k, ‖u k‖ = 1) (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) (hm : 0 < m) {c : 𝕜} {ρ : ℝ}
    (hc : lam i ≠ c) (hρ : ∀ k ≠ i, ‖lam k - c‖ ≤ ρ) :
    ‖u i - (subspace A v m).starProjection (u i)‖ ≤
      (∑ k ∈ Finset.univ.erase i, ‖α k‖ / ‖α i‖) * (ρ / ‖lam i - c‖) ^ (m - 1) := by
  have hci : lam i - c ≠ 0 := sub_ne_zero.2 hc
  have hev : ∀ z : 𝕜, ((C (lam i - c)⁻¹ * (X - C c)) ^ (m - 1) : 𝕜[X]).eval z
      = ((lam i - c)⁻¹ * (z - c)) ^ (m - 1) := by
    intro z; simp
  have hdeg : ((C (lam i - c)⁻¹ * (X - C c)) ^ (m - 1) : 𝕜[X]).degree < (m : ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le (n := m - 1) ?_) ?_
    · have h1 : (C (lam i - c)⁻¹ * (X - C c) : 𝕜[X]).natDegree ≤ 1 := by compute_degree
      calc ((C (lam i - c)⁻¹ * (X - C c)) ^ (m - 1) : 𝕜[X]).natDegree
          ≤ (m - 1) * (C (lam i - c)⁻¹ * (X - C c) : 𝕜[X]).natDegree :=
            Polynomial.natDegree_pow_le
        _ ≤ (m - 1) * 1 := by gcongr
        _ = m - 1 := by ring
    · exact_mod_cast Nat.sub_lt hm one_pos
  refine norm_sub_starProjection_le_mul hu hu1 hv hα hdeg ?_ ?_
  · rw [hev, inv_mul_cancel₀ hci, one_pow]
  · intro k hk
    rw [hev, norm_pow, norm_mul, norm_inv, ← div_eq_inv_mul]
    gcongr
    exact hρ k hk

end Diagonalizable

section Ellipse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E →ₗ[ℂ] E} {u : ι → E} {lam α : ι → ℂ}
  {v : E} {i : ι} {m : ℕ}

/-- **The Chebyshev bound on the distance for an ellipse.** Let $E$ be a complex inner product
space, let $u_k$ be a finite family of unit vectors with $A u_k = \lambda_k u_k$, let
$v = \sum_k \alpha_k u_k$, let $\alpha_i \neq 0$, and let $m > 0$. Let $c, d \in \mathbb{C}$
with $d \neq 0$ and $\rho \ge 1$, and let $\mathcal{E}$ be the closed region bounded by the
ellipse $\{ c + d (w + w^{-1})/2 : |w| = \rho \}$, which has the foci $c \pm d$. Suppose that
$\lambda_k \in \mathcal{E}$ for all $k \neq i$ and $\lambda_i \notin \mathcal{E}$. Then
$$\|u_i - P_m u_i\| \le \xi_i \frac{T_{m-1}\bigl( (\rho + \rho^{-1})/2 \bigr)}{\bigl|
  T_{m-1}\bigl( (c - \lambda_i)/d \bigr) \bigr|}, \qquad \xi_i = \sum_{k \neq i}
  \frac{|\alpha_k|}{|\alpha_i|},$$
where $T_{m-1}$ is the Chebyshev polynomial of the first kind, real in the numerator and complex
in the denominator.

This is Theorem 6.8 of [saad2011numerical], the ellipse counterpart of
`Arnoldi.norm_sub_starProjection_le_of_mem_closedBall`. The number $(\rho + \rho^{-1})/2$ is the
ratio $a / |d|$ of the semi-major axis to the focal semi-distance. Since $T_{m-1}$ is even or
odd, $|T_{m-1}((c - \lambda_i)/d)| = |T_{m-1}((\lambda_i - c)/d)|$. The source writes $T_k$ both
for the real Chebyshev polynomial in the numerator and for the complex one in the denominator.
The region $\mathcal{E}$ is `Set.filledEllipse c d ρ`. The competitor is the shifted and
normalized Chebyshev polynomial `Polynomial.Chebyshev.shiftedComplex (m - 1) c d (lam i)`. Its
maximum on the ellipse is `Polynomial.Chebyshev.sSup_norm_eval_shiftedComplex_ellipse`, and the
maximum modulus principle
`Polynomial.Chebyshev.norm_eval_shiftedComplex_le_of_mem_filledEllipse` carries the bound into
the enclosed region. Since $\lambda_i$ is outside the region, the denominator is not $0$
(`Polynomial.Chebyshev.eval_T_sub_div_ne_zero_of_notMem_filledEllipse`). -/
theorem norm_sub_starProjection_le_of_mem_ellipse (hu : ∀ k, A (u k) = lam k • u k)
    (hu1 : ∀ k, ‖u k‖ = 1) (hv : v = ∑ k, α k • u k) (hα : α i ≠ 0) (hm : 0 < m) {c d : ℂ}
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hd : d ≠ 0) (hi : lam i ∉ Set.filledEllipse c d ρ)
    (hlam : ∀ k ≠ i, lam k ∈ Set.filledEllipse c d ρ) :
    ‖u i - (subspace A v m).starProjection (u i)‖
      ≤ (∑ k ∈ Finset.univ.erase i, ‖α k‖ / ‖α i‖) *
        ((T ℝ ((m - 1 : ℕ) : ℤ)).eval ((ρ + ρ⁻¹) / 2)
          / ‖(T ℂ ((m - 1 : ℕ) : ℤ)).eval ((c - lam i) / d)‖) := by
  have hγ : (T ℂ ((m - 1 : ℕ) : ℤ)).eval ((c - lam i) / d) ≠ 0 :=
    Polynomial.Chebyshev.eval_T_sub_div_ne_zero_of_notMem_filledEllipse (m - 1) hρ hd hi
  have hdeg : (Polynomial.Chebyshev.shiftedComplex (m - 1) c d (lam i)).degree < (m : ℕ) := by
    refine lt_of_le_of_lt (Polynomial.Chebyshev.shiftedComplex_degree_le (m - 1) c d (lam i)) ?_
    exact_mod_cast Nat.sub_lt hm one_pos
  refine norm_sub_starProjection_le_mul hu hu1 hv hα hdeg
    (Polynomial.Chebyshev.shiftedComplex_eval_self (m - 1) hd hγ) fun k hk => ?_
  exact Polynomial.Chebyshev.norm_eval_shiftedComplex_le_of_mem_filledEllipse (m - 1) hρ hd hγ
    (hlam k hk)

end Ellipse

end Arnoldi
