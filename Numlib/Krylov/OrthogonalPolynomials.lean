/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Perturbation
import Numlib.Eigen.RayleighRitz
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Convergence.Superlinear
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Lanczos
import Numlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Lanczos process as orthogonal polynomials

Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K}$, and let $v \in E$. The
form $\langle p, q \rangle_v = \langle p(A) v, q(A) v \rangle$ is a sesquilinear form on the
polynomials $\mathbb{K}[X]$, and it is an inner product on the polynomials of degree less than the
grade of $v$, because such a polynomial annihilates $v$ only if it is zero. For symmetric $A$ the
Lanczos vectors are the orthonormal polynomials of this form evaluated at $A$: the Lanczos
polynomial $p_j$ has degree $j$ and satisfies $p_j(A) v = v_j$. It comes from the three-term
recurrence $\beta_{j+1} p_{j+2} = (X - \alpha_{j+1}) p_{j+1} - \beta_j p_j$ that the Lanczos process
runs ([meurant2006lanczos], §2.2; [saad2003iterative], §6.6.2). Two consequences follow for
$m \le \operatorname{grade}(A, v)$: the characteristic polynomial of the tridiagonal matrix $T_m$ is
the monic multiple of $p_m$, and the Ritz values of $A$ on $\mathcal{K}_m(A, v)$ are the eigenvalues
of $T_m$ and the roots of $p_m$.

In finite dimension the form is an integral against the discrete spectral measure $\mu = \sum_l
|\langle u_l, v \rangle|^2 \delta_{\lambda_l}$ of $(A, v)$, so the Lanczos polynomials are the
orthonormal polynomials of $\mu$. The $m$-point Gauss rule of $\mu$ is the spectral measure of the
compressed pair: it integrates every polynomial of degree at most $2m - 1$ exactly, its nodes are
the Ritz values, and its weights are $\|v\|^2$ times the squared first components of the
eigenvectors of $T_m$ ([meurant2006lanczos], Theorem 1). For $f(\lambda) = \lambda^{-1}$ the error
of this rule is the conjugate gradient error, which is the Dahlquist–Golub–Nash identity
([meurant2006lanczos], Theorem 9). The module ends with two results that belong to this subject but
not to the Lanczos process itself: the Christoffel–Darboux identity for any polynomials that obey a
three-term recurrence ([han2009theoretical], Theorem 3.7.3), and the persistence theorem of Paige
for Ritz values ([meurant2006lanczos], Theorem 5).

## Main definitions

* `Krylov.polyInner`: the form $\langle p, q \rangle_v = \langle p(A) v, q(A) v \rangle$ on
  $\mathbb{K}[X]$.
* `Krylov.spectralMeasure`: the measure $\sum_l |\langle u_l, v \rangle|^2 \delta_{\lambda_l}$ over
  an orthonormal eigenbasis $(u_l)$ of a symmetric $A$.
* `Lanczos.poly`: the Lanczos polynomials, $p_0 = 1/\|v\|$ and $\beta_{j+1} p_{j+2} = (X -
  \alpha_{j+1}) p_{j+1} - \beta_j p_j$.
* `Lanczos.tridiagInvFirst`: the number $(T_m^{-1} e_1, e_1)$.

## Main results

* `Krylov.aeval_eq_zero_iff_of_degree_lt_grade`: a polynomial of degree less than the grade of $v$
  annihilates $v$ only if it is zero.
* `Krylov.polyInner_nondegenerate`: below the grade, $\langle p, p \rangle_v = 0$ only for $p = 0$.
* `Krylov.polyInner_eq_integral`: $\langle p, q \rangle_v = \int p q \, d\mu$ for real polynomials
  $p$, $q$.
* `Lanczos.aeval_poly`: $p_j(A) v = v_j$ for symmetric $A$ and every $j$.
* `Lanczos.poly_degree` and `Lanczos.polyInner_poly`: below the grade, $p_j$ has degree $j$, and the
  $p_j$ are orthonormal for $\langle \cdot, \cdot \rangle_v$.
* `Lanczos.aeval_charpoly_tridiag`: $\chi_{T_m}(A) v = \|v\| \beta_0 \cdots \beta_{m-1} v_m$.
* `Lanczos.charpoly_tridiag_eq`: $\chi_{T_m} = \|v\| \beta_0 \cdots \beta_{m-1} \, p_m$ for
  $m < \operatorname{grade}(A, v)$.
* `Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag`: the Ritz values of $A$ on
  $\mathcal{K}_m$ are the eigenvalues of $T_m$.
* `Lanczos.hasEigenvalue_compression_iff_isRoot_poly`: the Ritz values of $A$ on $\mathcal{K}_m$ are
  the roots of $p_m$.
* `Lanczos.gauss_quadrature` and `Lanczos.gauss_quadrature_eq_sum`: the $m$-point Gauss rule of
  $\mu$ integrates the polynomials of degree at most $2m - 1$ exactly.
* `Polynomial.christoffel_darboux`: the Christoffel–Darboux identity in a form without division,
  with the quotient forms and the confluent forms beside it.
* `Lanczos.persistence`: a Ritz value $\theta$ of $T_{m+1}$ with unit eigenvector $z$ is within
  $\beta_m |z_m|$ of a Ritz value of every later $T_k$.
* `Lanczos.isUnit_tridiag`: for a symmetric coercive operator, $T_m$ is nonsingular for
  $m \le \operatorname{grade}$.
* `CG.energyNorm_error_sq_eq_sub_inner_inv`: $\|x^* - x_k\|_A^2 = \|r_0\|^2 \big( (T_n^{-1} e_1,
  e_1) - (T_k^{-1} e_1, e_1) \big)$ with $n = \operatorname{grade}(A, r_0)$.

## Proof outline

The identity for $\chi_{T_m}(A) v$ is the Cayley–Hamilton theorem for the compression of $A$ to
$\mathcal{K}_m$ (`Arnoldi.aeval_charpoly_mem_orthogonal`), together with
`Lanczos.inner_vec_pow_apply`, the only place where the scalar $\|v\| \beta_0 \cdots \beta_{m-1}$ is
computed. The Ritz values are the eigenvalues of $T_m$ because $T_m$ is the matrix of the
compression in the Lanczos basis (`Arnoldi.hessenbergSq_eq_toMatrix_compression` and
`Lanczos.hessenbergSq_eq_map_tridiag`). They are the roots of $p_m$ by the identity of
characteristic polynomials.

## Notation

* $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. The Lanczos vectors $v_j$ are the Arnoldi vectors
  `Arnoldi.vec A v j`.
* The Lanczos coefficients are $\alpha_j = \operatorname{Re} \langle v_j, A v_j \rangle$ and
  $\beta_j = \|w_j\|$, where $w_j$ is the unnormalized next vector of the process. In Lean they
  are `Lanczos.alpha A v j` and `Lanczos.beta A v j`.
* $T_m$ is the real symmetric tridiagonal Lanczos matrix `Lanczos.tridiag A v m`, and
  $\mathcal{K}_m = \mathcal{K}_m(A, v)$ is `Krylov.subspace A v m`.
* A Ritz value of $A$ on $\mathcal{K}_m$ is an eigenvalue of the compression
  $P_{\mathcal{K}_m} A|_{\mathcal{K}_m}$, which is `compression A (Krylov.subspace A v m)`.

## Implementation notes

* As everywhere in this library, the recurrence of the Lanczos polynomials runs past breakdown with
  no hypothesis: the inverse of a vanishing $\beta$ is $0$. So `Lanczos.aeval_poly` holds at every
  index.
* `Lanczos.tridiagInvFirst` uses `Matrix.inv`, which is $0$ at a singular matrix. The nonsingularity
  `Lanczos.isUnit_tridiag` makes the Dahlquist–Golub–Nash identity meaningful. For a coercive
  operator the Galerkin iterate over $\mathcal{K}_m$ exists and is unique, and by
  `Krylov.existsUnique_isGalerkinIterate_iff_isUnit` this is the nonsingularity of $H_m = T_m$.
* The Christoffel–Darboux identity is stated without division, so that it holds over a commutative
  ring and at $x = t$.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-! ### The polynomial inner product of a Krylov pair -/

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Let $A$ be a linear operator on a vector space $V$ over a field $K$, and let $v \in V$ have a
finite-dimensional Krylov space $\mathcal{K}(A, v)$. If a polynomial $p \in K[X]$ has degree
less than $\operatorname{grade}(A, v)$, then
$$p(A) v = 0 \iff p = 0.$$
So the map $p \mapsto p(A) v$ is injective on the polynomials of degree less than the grade, and
`Krylov.polyInner` is an inner product there.

The Krylov space is `Krylov.fullSubspace A v`. -/
theorem aeval_eq_zero_iff_of_degree_lt_grade (A : Module.End K V) (v : V)
    [FiniteDimensional K (fullSubspace A v)] {p : K[X]} (hp : p.degree < grade A v) :
    aeval A p v = 0 ↔ p = 0 := by
  refine ⟨fun h => by_contra fun hp0 => ?_, fun h => by rw [h, map_zero, LinearMap.zero_apply]⟩
  have hd : p.natDegree < grade A v := by
    rw [degree_eq_natDegree hp0, Nat.cast_lt] at hp
    exact hp
  refine pow_apply_notMem_subspace_of_lt_grade A v hd ?_
  rw [pow_apply_mem_subspace_iff_exists_monic]
  refine ⟨p * C p.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hp0,
    natDegree_mul_leadingCoeff_inv p hp0, ?_⟩
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply, map_smul, h, smul_zero]

end Field

variable (A : E →ₗ[𝕜] E) (v : E)

/-- Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K}$, and let $v \in E$.
The **polynomial inner product** of the Krylov pair $(A, v)$ is the form
$$\langle p, q \rangle_v = \langle p(A) v, q(A) v \rangle \qquad (p, q \in \mathbb{K}[X])$$
([saad2003iterative], (6.85); [meurant2006lanczos], (2.4)).

The form is sesquilinear on all of $\mathbb{K}[X]$: it is conjugate-linear in the first argument
and linear in the second, as the inner product of $E$ is. It is positive semidefinite, and it is
definite only below the grade of $v$ (`Krylov.polyInner_nondegenerate`). On all of
$\mathbb{K}[X]$ its kernel is the ideal generated by the minimal polynomial of $v$. -/
noncomputable def polyInner (p q : 𝕜[X]) : 𝕜 := inner 𝕜 (aeval A p v) (aeval A q v)

/-- The form is the inner product of $E$ pulled back along the evaluation map $p \mapsto p(A) v$
(`Krylov.polyEval`): $\langle p, q \rangle_v = \langle p(A) v, q(A) v \rangle$. Its
sesquilinearity comes from this. -/
theorem polyInner_eq_inner_polyEval (p q : 𝕜[X]) :
    polyInner A v p q = inner 𝕜 (polyEval A v p) (polyEval A v q) := rfl

/-- The form is additive in its first argument: $\langle p + q, r \rangle_v = \langle p, r
\rangle_v + \langle q, r \rangle_v$. -/
theorem polyInner_add_left (p q r : 𝕜[X]) :
    polyInner A v (p + q) r = polyInner A v p r + polyInner A v q r := by
  simp [polyInner, inner_add_left]

/-- The form is additive in its second argument: $\langle p, q + r \rangle_v = \langle p, q
\rangle_v + \langle p, r \rangle_v$. -/
theorem polyInner_add_right (p q r : 𝕜[X]) :
    polyInner A v p (q + r) = polyInner A v p q + polyInner A v p r := by
  simp [polyInner, inner_add_right]

/-- The form is conjugate-homogeneous in its first argument: $\langle c p, q \rangle_v = \bar c
\langle p, q \rangle_v$. -/
theorem polyInner_smul_left (c : 𝕜) (p q : 𝕜[X]) :
    polyInner A v (c • p) q = starRingEnd 𝕜 c * polyInner A v p q := by
  simp [polyInner, inner_smul_left]

/-- The form is homogeneous in its second argument: $\langle p, c q \rangle_v = c \langle p, q
\rangle_v$. -/
theorem polyInner_smul_right (c : 𝕜) (p q : 𝕜[X]) :
    polyInner A v p (c • q) = c * polyInner A v p q := by
  simp [polyInner, inner_smul_right]

/-- The form is Hermitian: $\overline{\langle p, q \rangle_v} = \langle q, p \rangle_v$. -/
theorem polyInner_conj_symm (p q : 𝕜[X]) :
    starRingEnd 𝕜 (polyInner A v p q) = polyInner A v q p :=
  inner_conj_symm _ _

/-- The quadratic form is $\langle p, p \rangle_v = \|p(A) v\|^2$. In particular it is real and
nonnegative. -/
theorem polyInner_self (p : 𝕜[X]) : polyInner A v p p = ((‖aeval A p v‖ : ℝ) : 𝕜) ^ 2 :=
  inner_self_eq_norm_sq_to_K _

/-- For every polynomial $p$, $\langle p, p \rangle_v = 0$ if and only if $p(A) v = 0$. So the form
degenerates exactly on the polynomials that annihilate $v$. -/
theorem polyInner_self_eq_zero_iff (p : 𝕜[X]) : polyInner A v p p = 0 ↔ aeval A p v = 0 :=
  inner_self_eq_zero

/-- Let $v$ have a finite-dimensional Krylov space $\mathcal{K}(A, v)$. If $p \in \mathbb{K}[X]$ has
degree less than $\operatorname{grade}(A, v)$, then
$$\langle p, p \rangle_v = 0 \iff p = 0.$$
So `Krylov.polyInner` is an inner product on the polynomials of degree less than the grade
([meurant2006lanczos], §2.2). -/
theorem polyInner_nondegenerate [FiniteDimensional 𝕜 (fullSubspace A v)] {p : 𝕜[X]}
    (hp : p.degree < grade A v) : polyInner A v p p = 0 ↔ p = 0 := by
  rw [polyInner_self_eq_zero_iff, aeval_eq_zero_iff_of_degree_lt_grade A v hp]

/-! ### The discrete spectral measure -/

section SpectralMeasure

open MeasureTheory

variable [FiniteDimensional 𝕜 E]

/-- Let $E$ be a finite-dimensional inner product space of dimension $n$, let $A$ be a symmetric
operator on $E$, and let $v \in E$. Let $(u_l)_{l < n}$ be the orthonormal eigenbasis of $A$
that Mathlib chooses, with $A u_l = \lambda_l u_l$. The **discrete spectral measure** of
$(A, v)$ is the measure
$$\mu = \sum_{l<n} |\langle u_l, v \rangle|^2 \, \delta_{\lambda_l}$$
on $\mathbb{R}$ ([meurant2006lanczos], §2.2). Its total mass is $\|v\|^2$. The form
`Krylov.polyInner A v` of two real polynomials is the integral of their product against $\mu$
(`Krylov.polyInner_eq_integral`), so the Lanczos polynomials `Lanczos.poly` are the orthonormal
polynomials of $\mu$.

The measure is defined from the eigenvector basis `LinearMap.IsSymmetric.eigenvectorBasis`, so
it takes the symmetry of $A$ and the dimension of $E$ as arguments, not only $A$ and $v$.
Grouping the weights by eigenvalue would make it a function of $(A, v)$ alone. -/
noncomputable def spectralMeasure {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) : Measure ℝ :=
  ∑ i : Fin n, ENNReal.ofReal (‖inner 𝕜 (hA.eigenvectorBasis hn i) v‖ ^ 2) •
    Measure.dirac (hA.eigenvalues hn i)

/-- Integration against the spectral measure is the weighted sum over the eigenvalues: for every
$f : \mathbb{R} \to \mathbb{R}$,
$$\int f \, d\mu = \sum_{l<n} |\langle u_l, v \rangle|^2 f(\lambda_l).$$
-/
theorem integral_spectralMeasure {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) (f : ℝ → ℝ) :
    ∫ x, f x ∂(spectralMeasure hA hn v)
      = ∑ i : Fin n, ‖inner 𝕜 (hA.eigenvectorBasis hn i) v‖ ^ 2 * f (hA.eigenvalues hn i) := by
  rw [spectralMeasure, integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure (by simp)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- Let $E$ have dimension $n$, let $A$ be symmetric, and let $v \in E$. For real polynomials $p$
and $q$,
$$\langle p, q \rangle_v = \int p(\lambda) q(\lambda) \, d\mu(\lambda),$$
where $\mu$ is the discrete spectral measure of $(A, v)$ and $p$, $q$ are read as polynomials
over $\mathbb{K}$ ([meurant2006lanczos], (2.4)).

Both sides are the sum of $p(\lambda_l) q(\lambda_l) |\langle u_l, v \rangle|^2$ over the
eigenbasis: on the left because $p(A)$ acts diagonally in this basis
(`LinearMap.IsSymmetric.repr_aeval_apply`), and on the right by
`Krylov.integral_spectralMeasure`. -/
theorem polyInner_eq_integral {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) (p q : ℝ[X]) :
    polyInner A v (p.map (algebraMap ℝ 𝕜)) (q.map (algebraMap ℝ 𝕜))
      = ((∫ x, p.eval x * q.eval x ∂(spectralMeasure hA hn v) : ℝ) : 𝕜) := by
  have hrepr : ∀ (r : ℝ[X]) (i : Fin n),
      inner 𝕜 (hA.eigenvectorBasis hn i) (aeval A (r.map (algebraMap ℝ 𝕜)) v)
        = ((r.eval (hA.eigenvalues hn i) : ℝ) : 𝕜) *
          inner 𝕜 (hA.eigenvectorBasis hn i) v := fun r i => by
    rw [← OrthonormalBasis.repr_apply_apply, hA.repr_aeval_apply hn, eval_map_apply,
      RCLike.algebraMap_eq_ofReal, OrthonormalBasis.repr_apply_apply]
  rw [integral_spectralMeasure, polyInner,
    ← OrthonormalBasis.sum_inner_mul_inner (hA.eigenvectorBasis hn)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have hconj : inner 𝕜 (aeval A (p.map (algebraMap ℝ 𝕜)) v) (hA.eigenvectorBasis hn i)
      = starRingEnd 𝕜 (inner 𝕜 (hA.eigenvectorBasis hn i)
        (aeval A (p.map (algebraMap ℝ 𝕜)) v)) := (inner_conj_symm _ _).symm
  have hcc : starRingEnd 𝕜 (inner 𝕜 (hA.eigenvectorBasis hn i) v) *
      inner 𝕜 (hA.eigenvectorBasis hn i) v
      = ((‖inner 𝕜 (hA.eigenvectorBasis hn i) v‖ : ℝ) : 𝕜) ^ 2 := RCLike.conj_mul _
  rw [hconj, hrepr, hrepr, map_mul, RCLike.conj_ofReal, ← hcc]
  ring

/-- Let $E$ have dimension $n$, let $A$ be symmetric, and let $v \in E$. The moments of the spectral
measure are the moments of $(A, v)$: for every real polynomial $f$,
$$\langle v, f(A) v \rangle = \int f \, d\mu.$$
It is `Krylov.polyInner_eq_integral` at $p = 1$, and it is the form in which the measure is
used. -/
theorem inner_aeval_eq_integral {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) (f : ℝ[X]) :
    inner 𝕜 v (aeval A (f.map (algebraMap ℝ 𝕜)) v)
      = ((∫ x, f.eval x ∂(spectralMeasure hA hn v) : ℝ) : 𝕜) := by
  have h := polyInner_eq_integral hA hn v 1 f
  simpa [polyInner] using h

end SpectralMeasure

end Krylov

open Krylov

namespace Lanczos

/-! ### The Lanczos polynomials -/

/-- The pair $(p_j, p_{j+1})$ of consecutive Lanczos polynomials, defined by a one-step recursion so
that the equations of `Lanczos.poly` hold by definition. -/
private noncomputable def polyPair (A : E →ₗ[𝕜] E) (v : E) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 => (C ((‖v‖ : 𝕜))⁻¹,
      C ((beta A v 0 : 𝕜))⁻¹ * ((X - C (alpha A v 0 : 𝕜)) * C ((‖v‖ : 𝕜))⁻¹))
  | j + 1 => ((polyPair A v j).2,
      C ((beta A v (j + 1) : 𝕜))⁻¹ *
        ((X - C (alpha A v (j + 1) : 𝕜)) * (polyPair A v j).2 -
          C (beta A v j : 𝕜) * (polyPair A v j).1))

/-- Let $A$ be a linear operator on $E$ and $v \in E$, with Lanczos coefficients $\alpha_j$ and
$\beta_j$. The **Lanczos polynomials** of $(A, v)$ are given by $p_0 = 1/\|v\|$,
$p_1 = \beta_0^{-1} (X - \alpha_0) p_0$ and
$$p_{j+2} = \beta_{j+1}^{-1} \big( (X - \alpha_{j+1}) p_{j+1} - \beta_j p_j \big),$$
with $0^{-1} = 0$. This is the three-term recurrence $\beta_{j+1} p_{j+2} = (X - \alpha_{j+1})
p_{j+1} - \beta_j p_j$ that the Lanczos process runs ([meurant2006lanczos], §2.2;
[saad2003iterative], §6.6.2).

For symmetric $A$ these are the polynomials that produce the Lanczos vectors, $p_j(A) v = v_j$
(`Lanczos.aeval_poly`). So below the grade they are the orthonormal polynomials of
`Krylov.polyInner A v` (`Lanczos.polyInner_poly`), and $p_j$ has degree $j$
(`Lanczos.poly_degree`).

The recurrence is divided by $\beta_{j+1}$, not multiplied out, so that it holds at every index:
from the grade onwards the vanishing $\beta$ inverts to $0$, and both $p_j$ and $v_j$ are $0$. -/
noncomputable def poly (A : E →ₗ[𝕜] E) (v : E) (j : ℕ) : 𝕜[X] := (polyPair A v j).1

variable (A : E →ₗ[𝕜] E) (v : E)

/-- The first Lanczos polynomial is the constant $p_0 = 1/\|v\|$: the Lanczos process starts from
the normalized vector. -/
theorem poly_zero : poly A v 0 = C ((‖v‖ : 𝕜))⁻¹ := rfl

/-- The first step of the recurrence: $p_1 = \beta_0^{-1} (X - \alpha_0) p_0$, that is,
$\beta_0 p_1 = (X - \alpha_0) p_0$ when $\beta_0 \neq 0$. -/
theorem poly_one :
    poly A v 1 = C ((beta A v 0 : 𝕜))⁻¹ * ((X - C (alpha A v 0 : 𝕜)) * poly A v 0) := rfl

/-- The three-term recurrence: for every $j$,
$$p_{j+2} = \beta_{j+1}^{-1} \big( (X - \alpha_{j+1}) p_{j+1} - \beta_j p_j \big),$$
with $0^{-1} = 0$. This is $\beta_{j+1} p_{j+2} = (X - \alpha_{j+1}) p_{j+1} - \beta_j p_j$ in a
divided form that holds also after breakdown. -/
theorem poly_add_two (j : ℕ) :
    poly A v (j + 2) = C ((beta A v (j + 1) : 𝕜))⁻¹ *
      ((X - C (alpha A v (j + 1) : 𝕜)) * poly A v (j + 1) - C (beta A v j : 𝕜) * poly A v j) :=
  rfl

/-!
### The recurrence step: evaluation, degree and leading coefficient

Three computations on the shape $c \, ((X - a) p - b q)$ of the recurrence. Each of the three
inductions below uses one of them at both of its base cases, with $b = 0$ and $q = 0$, and at its
step.
-/

private theorem aeval_recur (c a b : 𝕜) (p q : 𝕜[X]) :
    aeval A (C c * ((X - C a) * p - C b * q)) v =
      c • (A (aeval A p v) - a • aeval A p v - b • aeval A q v) := by
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply, map_sub,
    LinearMap.sub_apply, map_mul, Module.End.mul_apply, map_sub, LinearMap.sub_apply, aeval_X,
    aeval_C, Module.algebraMap_end_apply, map_mul, Module.End.mul_apply, aeval_C,
    Module.algebraMap_end_apply]

private theorem natDegree_recur (c a b : 𝕜) {p q : 𝕜[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n + 1) :
    (C c * ((X - C a) * p - C b * q)).natDegree ≤ n + 1 := by
  refine le_trans (natDegree_mul_le) ?_
  rw [natDegree_C, zero_add]
  refine le_trans (natDegree_sub_le _ _) (max_le (le_trans (natDegree_mul_le) ?_)
    (le_trans (natDegree_mul_le) ?_))
  · rw [natDegree_X_sub_C]
    omega
  · rw [natDegree_C]
    omega

private theorem coeff_recur (c a b : 𝕜) {p q : 𝕜[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n) :
    (C c * ((X - C a) * p - C b * q)).coeff (n + 1) = c * p.coeff n := by
  rw [coeff_C_mul, coeff_sub, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (n := n + 1) (by omega),
    coeff_eq_zero_of_natDegree_lt (n := n + 1) (by omega), mul_zero, mul_zero, sub_zero, sub_zero]

/-- The case $j = 1$ of the recurrence, in the shape $c \, ((X - a) p - b q)$ with $b = 0$ and
$q = 0$. -/
private theorem poly_one' :
    poly A v 1 = C ((beta A v 0 : 𝕜))⁻¹ *
      ((X - C (alpha A v 0 : 𝕜)) * poly A v 0 - C (0 : 𝕜) * 0) := by
  rw [mul_zero, sub_zero]
  exact poly_one A v

/-! ### The Lanczos polynomials produce the Lanczos vectors -/

private theorem aeval_poly_zero : aeval A (poly A v 0) v = Arnoldi.vec A v 0 := by
  rw [poly_zero, aeval_C, Module.algebraMap_end_apply]
  rcases eq_or_ne v 0 with rfl | hv
  · rw [(Arnoldi.vec_eq_zero_iff_pow_apply_mem A 0 0).2 (by simp), smul_zero]
  · rw [Arnoldi.vec_zero A v hv]

/-- The normalization step of the Lanczos process: $v_{j+1} = \beta_j^{-1} w_j$. -/
private theorem vec_succ_eq_beta (j : ℕ) :
    Arnoldi.vec A v (j + 1) = ((beta A v j : 𝕜))⁻¹ • Arnoldi.w A v j := by
  have hb : beta A v j = ‖Arnoldi.w A v j‖ := rfl
  rw [Arnoldi.vec_succ_eq, ← hb]

/-- For symmetric $A$, the first unnormalized vector is $w_0 = A v_0 - \alpha_0 v_0$. -/
private theorem w_zero_eq {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) :
    Arnoldi.w A v 0 = A (Arnoldi.vec A v 0) - (alpha A v 0 : 𝕜) • Arnoldi.vec A v 0 := by
  rw [Arnoldi.w, Finset.sum_range_one, coe_alpha v hA 0]

/-- Let $A$ be a symmetric operator on $E$ and $v \in E$. The Lanczos polynomials evaluated at $A$
produce the Lanczos vectors: for every $j \in \mathbb{N}$,
$$p_j(A) v = v_j$$
([meurant2006lanczos], §2.2; [saad2003iterative], §6.6.2).

No hypothesis on the grade is needed: after breakdown both sides are $0$. The Lanczos vector
$v_j$ is the Arnoldi vector `Arnoldi.vec A v j`. -/
theorem aeval_poly {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) (j : ℕ) :
    aeval A (poly A v j) v = Arnoldi.vec A v j := by
  induction j using Nat.twoStepInduction with
  | zero => exact aeval_poly_zero A v
  | one =>
    rw [poly_one' A v, aeval_recur, aeval_poly_zero, map_zero, LinearMap.zero_apply, smul_zero,
      sub_zero, ← w_zero_eq hA v, vec_succ_eq_beta]
  | more j ih1 ih2 =>
    rw [poly_add_two, aeval_recur, ih1, ih2, ← w_succ_eq v hA j, vec_succ_eq_beta]

/-! ### Degree and orthonormality -/

/-- The $j$-th Lanczos polynomial has degree at most $j$. Below the grade it has degree exactly $j$
(`Lanczos.poly_degree`). -/
theorem poly_natDegree_le (j : ℕ) : (poly A v j).natDegree ≤ j := by
  induction j using Nat.twoStepInduction with
  | zero => rw [poly_zero]; exact le_of_eq (natDegree_C _)
  | one =>
    rw [poly_one' A v]
    exact natDegree_recur _ _ _ (by rw [poly_zero]; exact le_of_eq (natDegree_C _)) (by simp)
  | more j _ ih2 => exact poly_add_two A v j ▸ natDegree_recur _ _ _ ih2 (by omega)

/-- The coefficient of $X^j$ in the $j$-th Lanczos polynomial is
$1/(\|v\| \beta_0 \cdots \beta_{j-1})$, with $1/0 = 0$. It is the reciprocal of the scalar of
`Lanczos.aeval_charpoly_tridiag`. -/
theorem poly_coeff_self (j : ℕ) :
    (poly A v j).coeff j = (((‖v‖ * ∏ i ∈ Finset.range j, beta A v i)⁻¹ : ℝ) : 𝕜) := by
  induction j using Nat.twoStepInduction with
  | zero => rw [poly_zero, coeff_C_zero]; norm_num
  | one =>
    rw [poly_one' A v,
      coeff_recur _ _ _ (by rw [poly_zero]; exact le_of_eq (natDegree_C _)) (by simp),
      poly_zero, coeff_C_zero, Finset.prod_range_one]
    push_cast
    rw [mul_inv, mul_comm]
  | more j _ ih2 =>
    rw [poly_add_two, coeff_recur _ _ _ (poly_natDegree_le A v (j + 1))
        (le_trans (poly_natDegree_le A v j) (by omega)), ih2]
    simp only [Finset.prod_range_succ]
    push_cast
    ring

/-- If $j < \operatorname{grade}(A, v)$, then $\|v\| \beta_0 \cdots \beta_{j-1} \neq 0$: the scalar
is nonzero as long as the Lanczos process has not broken down. -/
theorem norm_mul_prod_beta_ne_zero [FiniteDimensional 𝕜 (fullSubspace A v)] {j : ℕ}
    (hj : j < grade A v) : (‖v‖ * ∏ i ∈ Finset.range j, beta A v i) ≠ 0 := by
  have hv : v ≠ 0 := fun h => by
    rw [h, grade_zero] at hj
    exact Nat.not_lt_zero _ hj
  refine mul_ne_zero (norm_ne_zero_iff.2 hv) (Finset.prod_ne_zero_iff.2 fun i hi h0 => ?_)
  have hc : Arnoldi.coeff A v (i + 1) i = 0 := by
    rw [← coe_beta A v i, h0, RCLike.ofReal_zero]
  have := Finset.mem_range.1 hi
  have := (Arnoldi.coeff_succ_self_eq_zero_iff A v i).1 hc
  omega

/-- Let $v$ have a finite-dimensional Krylov space $\mathcal{K}(A, v)$. If
$j < \operatorname{grade}(A, v)$, the $j$-th Lanczos polynomial has degree exactly $j$. So
$p_0, \dots, p_{m-1}$ is a basis of the polynomials of degree less than $m$ for every
$m \le \operatorname{grade}(A, v)$.

The statement needs no symmetry of $A$. -/
theorem poly_degree [FiniteDimensional 𝕜 (fullSubspace A v)] {j : ℕ} (hj : j < grade A v) :
    (poly A v j).degree = j := by
  refine degree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_degree_le.1 (poly_natDegree_le A v j))
    ?_
  rw [poly_coeff_self, Ne, RCLike.ofReal_eq_zero]
  exact inv_ne_zero (norm_mul_prod_beta_ne_zero A v hj)

-- Only the diagonal case needs a bound, and there the two indices are equal.
set_option linter.unusedVariables false in
/-- Let $A$ be a symmetric operator on $E$, and let $v \in E$ have a finite-dimensional Krylov space
$\mathcal{K}(A, v)$. For $i, j < \operatorname{grade}(A, v)$,
$$\langle p_i, p_j \rangle_v = \delta_{ij}.$$
So the Lanczos polynomials are the orthonormal polynomials of the pair $(A, v)$
([meurant2006lanczos], §2.2).

This is the orthonormality of the Arnoldi vectors (`Arnoldi.orthonormal`), read through
$v_j = p_j(A) v$. -/
theorem polyInner_poly {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {i j : ℕ} (hi : i < grade A v)
    (hj : j < grade A v) :
    polyInner A v (poly A v i) (poly A v j) = if i = j then 1 else 0 := by
  rw [polyInner, aeval_poly hA, aeval_poly hA]
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K,
      Arnoldi.norm_vec_eq_one_of_lt_grade A v hi, RCLike.ofReal_one, one_pow]
  · rw [ite_eq_right hij, Arnoldi.inner_vec_eq_zero A v hij]

/-! ### The characteristic polynomial of the tridiagonal matrix -/

/-- The Arnoldi coefficient is $h_{ij} = \langle v_i, A v_j \rangle$. -/
private theorem inner_vec_apply_vec (i j : ℕ) :
    inner 𝕜 (Arnoldi.vec A v i) (A (Arnoldi.vec A v j)) = Arnoldi.coeff A v i j := rfl

/-- Let $A$ be a linear operator on $E$ and $v \in E$. For every $m \in \mathbb{N}$, the component
of $A^m v$ along the $m$-th Lanczos vector is
$$\langle v_m, A^m v \rangle = \|v\| \beta_0 \cdots \beta_{m-1}.$$
This is the scalar of `Lanczos.aeval_charpoly_tridiag`.

Each step of the Lanczos process multiplies the scalar by the new $\beta$, because $v_{m+1}$ is
orthogonal to $\mathcal{K}_{m+1}$ and $\langle v_{m+1}, A v_m \rangle = \beta_m$. The statement
needs no symmetry of $A$. -/
theorem inner_vec_pow_apply (m : ℕ) :
    inner 𝕜 (Arnoldi.vec A v m) ((A ^ m) v)
      = ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) := by
  induction m with
  | zero =>
    rw [pow_zero, Module.End.one_apply, Finset.prod_range_zero, mul_one]
    rcases eq_or_ne v 0 with rfl | hv
    · rw [inner_zero_right, norm_zero, RCLike.ofReal_zero]
    · rw [Arnoldi.vec_zero A v hv, inner_smul_left, map_inv₀, RCLike.conj_ofReal,
        inner_self_eq_norm_sq_to_K, sq, ← mul_assoc, inv_mul_cancel₀ (by
          simpa using norm_ne_zero_iff.2 hv), one_mul]
  | succ m ih =>
    have hmem : (A ^ m) v ∈ subspace A v (m + 1) := pow_apply_mem_subspace A v m.lt_succ_self
    have hpow : (A ^ (m + 1)) v = A ((A ^ m) v) := by rw [pow_succ']; rfl
    rw [hpow, Arnoldi.eq_sum_inner_smul_vec A v hmem, map_sum, inner_sum,
      Finset.sum_eq_single m]
    · rw [map_smul, inner_smul_right, inner_vec_apply_vec, ← coe_beta A v m, ih,
        Finset.prod_range_succ]
      push_cast
      ring
    · intro i hi hne
      rw [map_smul, inner_smul_right, inner_vec_apply_vec,
        Arnoldi.coeff_eq_zero_of_lt A v (by have := Finset.mem_range.1 hi; omega), mul_zero]
    · intro h
      exact absurd (Finset.self_mem_range_succ m) h

variable {A}

/-- Let $A$ be symmetric, let $v$ have a finite-dimensional Krylov space, and let
$m \le \operatorname{grade}(A, v)$. Then the characteristic polynomial of $T_m$, read over
$\mathbb{K}$, is the characteristic polynomial of the compression of $A$ to $\mathcal{K}_m$. The
reason is that $T_m$ is the matrix of this compression in the Lanczos basis
(`Arnoldi.hessenbergSq_eq_toMatrix_compression` and `Lanczos.hessenbergSq_eq_map_tridiag`). -/
theorem charpoly_tridiag_map (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m ≤ grade A v) :
    (tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)
      = LinearMap.charpoly (compression A (subspace A v m)) := by
  rw [← Matrix.charpoly_map, ← hessenbergSq_eq_map_tridiag v hA m,
    Arnoldi.hessenbergSq_eq_toMatrix_compression A v hm, LinearMap.charpoly_toMatrix]

/-- Let $A$ be symmetric, let $v$ have a finite-dimensional Krylov space, and let
$m \le \operatorname{grade}(A, v)$. The characteristic polynomial $\chi_{T_m}$ of the
tridiagonal matrix $T_m$, evaluated at $A$ and applied to $v$, is
$$\chi_{T_m}(A) v = \|v\| \beta_0 \cdots \beta_{m-1} \, v_m$$
([saad2003iterative], §6.6.2 (e); [meurant2006lanczos], (2.6)). So $\chi_{T_m}$ is the monic
multiple of the $m$-th Lanczos polynomial, and its roots are the Ritz values of $A$ on
$\mathcal{K}_m(A, v)$ (`Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag`).

The proof is the Cayley–Hamilton theorem for the compression of $A$ to $\mathcal{K}_m$
(`Arnoldi.aeval_charpoly_mem_orthogonal`). It puts the vector in
$\mathcal{K}_{m+1} \cap \mathcal{K}_m^\perp$, which is the line spanned by $v_m$. The scalar is
`Lanczos.inner_vec_pow_apply`, because the terms of lower order of the characteristic polynomial
contribute nothing to it. -/
theorem aeval_charpoly_tridiag (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m ≤ grade A v) :
    aeval A ((tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)) v =
      ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) • Arnoldi.vec A v m := by
  have hcp := charpoly_tridiag_map hA v hm
  set c := LinearMap.charpoly (compression A (subspace A v m)) with hc
  have hcm : c.Monic := LinearMap.charpoly_monic _
  have hcd : c.degree = (m : ℕ) := by
    rw [degree_eq_natDegree hcm.ne_zero, hc, LinearMap.charpoly_natDegree, finrank_subspace,
      min_eq_left hm]
  have hlt : (c - X ^ m).degree < (m : WithBot ℕ) := by
    rw [← hcd]
    exact degree_sub_lt_left (by rw [hcd, degree_X_pow]) hcm.ne_zero
      (by rw [hcm.leadingCoeff, (monic_X_pow m).leadingCoeff])
  have hsplit : aeval A c v = (A ^ m) v + aeval A (c - X ^ m) v := by
    rw [map_sub, LinearMap.sub_apply, map_pow, aeval_X]
    abel
  have hinner : inner 𝕜 (Arnoldi.vec A v m) (aeval A c v)
      = inner 𝕜 (Arnoldi.vec A v m) ((A ^ m) v) := by
    rw [hsplit, inner_add_right, Submodule.inner_left_of_mem_orthogonal
      (aeval_apply_mem_subspace A v hlt) (Arnoldi.vec_mem_orthogonal A v m), add_zero]
  rw [hcp]
  refine (Arnoldi.eq_inner_smul_vec A v (aeval_apply_mem_subspace A v (by
    rw [hcd]; exact_mod_cast m.lt_succ_self)) (Arnoldi.aeval_charpoly_mem_orthogonal A v hm)).trans
    ?_
  rw [hinner, inner_vec_pow_apply]

/-! ### The Ritz values are the eigenvalues of the tridiagonal matrix -/

/-- Let $A$ be symmetric, let $v$ have a finite-dimensional Krylov space, let
$m \le \operatorname{grade}(A, v)$, and let $\theta \in \mathbb{R}$. Then $\theta$ is an
eigenvalue of the compression of $A$ to $\mathcal{K}_m(A, v)$ if and only if $\theta$ is an
eigenvalue of the Lanczos matrix $T_m$ ([meurant2006lanczos], §2.3). In other words, the Ritz
values of $A$ on $\mathcal{K}_m(A, v)$ are the eigenvalues of $T_m$.

The Ritz values are the eigenvalues of the compression by
`Krylov.isRitzPair_iff_hasEigenvector`. Below the grade the Lanczos vectors are an orthonormal
basis of $\mathcal{K}_m$, and $T_m$ is the matrix of the compression in this basis
(`Arnoldi.hessenbergSq_eq_toMatrix_compression` and `Lanczos.hessenbergSq_eq_map_tridiag`). The
proof goes through the characteristic polynomial, because the spectrum of the real matrix $T_m$
is compared with the spectrum of an operator on a space over $\mathbb{K}$. -/
theorem hasEigenvalue_compression_iff_mem_spectrum_tridiag (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m ≤ grade A v) (θ : ℝ) :
    Module.End.HasEigenvalue (compression A (subspace A v m)) (θ : 𝕜) ↔
      θ ∈ spectrum ℝ (tridiag A v m) := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum,
    ← LinearMap.spectrum_toMatrix _ (Arnoldi.orthonormalBasis A v hm).toBasis,
    ← Arnoldi.hessenbergSq_eq_toMatrix_compression A v hm, hessenbergSq_eq_map_tridiag v hA m,
    Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.charpoly_map]
  simp only [IsRoot.def, ← RCLike.algebraMap_eq_ofReal, eval_map, eval₂_hom]
  exact map_eq_zero_iff _ (algebraMap ℝ 𝕜).injective

/-- Let $A$ be symmetric, let $v$ have a finite-dimensional Krylov space, and let
$m < \operatorname{grade}(A, v)$. The characteristic polynomial of $T_m$ is the monic multiple
of the $m$-th Lanczos polynomial:
$$\chi_{T_m} = \|v\| \beta_0 \cdots \beta_{m-1} \, p_m$$
([meurant2006lanczos], (2.6)).

Both sides have degree $m$ and the same leading coefficient, and their difference annihilates
$v$, so they agree by `Krylov.aeval_eq_zero_iff_of_degree_lt_grade`. At
$m = \operatorname{grade}(A, v)$ the statement is false: there $p_m = 0$, while the
characteristic polynomial is monic. -/
theorem charpoly_tridiag_eq (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m < grade A v) :
    (tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)
      = C ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * poly A v m := by
  have hg : (‖v‖ * ∏ i ∈ Finset.range m, beta A v i) ≠ 0 := norm_mul_prod_beta_ne_zero A v hm
  have hg' : ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) ≠ 0 := by
    rwa [Ne, RCLike.ofReal_eq_zero]
  have hpd : (poly A v m).degree = (m : ℕ) := poly_degree A v hm
  have hcm : ((tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)).Monic :=
    ((tridiag A v m).charpoly_monic).map _
  have hcd : ((tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)).degree = (m : ℕ) := by
    rw [degree_eq_natDegree hcm.ne_zero, ((tridiag A v m).charpoly_monic).natDegree_map,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmd : (C ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * poly A v m).degree
      = (m : ℕ) := by
    rw [degree_mul, degree_C hg', zero_add, hpd]
  have hml : (C ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * poly A v m).leadingCoeff
      = 1 := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff, natDegree_eq_of_degree_eq_some hpd,
      poly_coeff_self, ← RCLike.ofReal_mul, mul_inv_cancel₀ hg, RCLike.ofReal_one]
  have hsub : ((tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)
      - C ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * poly A v m).degree
      < (grade A v : WithBot ℕ) := by
    refine lt_of_lt_of_le (lt_of_lt_of_le (degree_sub_lt_left (hcd.trans hmd.symm) hcm.ne_zero
      (by rw [hcm.leadingCoeff, hml])) hcd.le) ?_
    exact_mod_cast hm.le
  rw [← sub_eq_zero, ← aeval_eq_zero_iff_of_degree_lt_grade A v hsub, map_sub,
    LinearMap.sub_apply, aeval_charpoly_tridiag hA v hm.le, map_mul, Module.End.mul_apply,
    aeval_C, Module.algebraMap_end_apply, aeval_poly hA, sub_self]

/-- Let $A$ be symmetric, let $v$ have a finite-dimensional Krylov space, let
$m < \operatorname{grade}(A, v)$, and let $\theta \in \mathbb{R}$. Then $\theta$ is an
eigenvalue of the compression of $A$ to $\mathcal{K}_m(A, v)$ if and only if $p_m(\theta) = 0$.
So the Ritz values of $A$ on $\mathcal{K}_m(A, v)$ are the roots of the $m$-th Lanczos
polynomial.

This is `Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag` read through
`Lanczos.charpoly_tridiag_eq`. With `Lanczos.gauss_quadrature_eq_sum`, it says that the nodes of
the $m$-point Gauss rule of $(A, v)$ are the Ritz values. -/
theorem hasEigenvalue_compression_iff_isRoot_poly (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m < grade A v) (θ : ℝ) :
    Module.End.HasEigenvalue (compression A (subspace A v m)) (θ : 𝕜) ↔
      (poly A v m).IsRoot (θ : 𝕜) := by
  have hg' : ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) ≠ 0 := by
    rw [Ne, RCLike.ofReal_eq_zero]
    exact norm_mul_prod_beta_ne_zero A v hm
  have key : (((tridiag A v m).charpoly.eval θ : ℝ) : 𝕜)
      = ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * (poly A v m).eval (θ : 𝕜) := by
    rw [← RCLike.algebraMap_eq_ofReal, ← eval₂_hom, ← eval_map, charpoly_tridiag_eq hA v hm,
      eval_mul, eval_C, RCLike.algebraMap_eq_ofReal]
  rw [hasEigenvalue_compression_iff_mem_spectrum_tridiag hA v hm.le θ,
    Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot.def, IsRoot.def]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h0 : ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * (poly A v m).eval (θ : 𝕜)
        = 0 := by rw [← key, h, RCLike.ofReal_zero]
    exact (mul_eq_zero.1 h0).resolve_left hg'
  · have h0 : (((tridiag A v m).charpoly.eval θ : ℝ) : 𝕜) = 0 := by rw [key, h, mul_zero]
    rwa [RCLike.ofReal_eq_zero] at h0

/-! ### Gauss quadrature -/

section Gauss

open MeasureTheory

variable [FiniteDimensional 𝕜 E]

/-- Let $E$ have dimension $n$, let $A$ be symmetric, let $v \in E$, and let $m \ge 1$ with
$\dim \mathcal{K}_m(A, v) = m$. Let $\mu$ be the spectral measure of $(A, v)$, and let $\mu_m$
be the spectral measure of the compression $A_m$ of $A$ to $\mathcal{K}_m(A, v)$ and of the same
vector $v$. Then for every real polynomial $f$ of degree at most $2m - 1$,
$$\int f \, d\mu = \int f \, d\mu_m.$$
This is Theorem 1 of [meurant2006lanczos]: $\mu_m$ is the $m$-point Gauss quadrature rule of
$\mu$.

The rule is $\mu_m = \sum_{j<m} |\langle y_j, v \rangle|^2 \delta_{\theta_j}$ over an
orthonormal eigenbasis $(\theta_j, y_j)$ of $A_m$. So it has $m$ nodes, and its nodes are the
Ritz values. These are the eigenvalues of $T_m$
(`Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag`) and the roots of $p_m$
(`Lanczos.hasEigenvalue_compression_iff_isRoot_poly`). Its weights are $\|v\|^2$ times the
squared first components of the eigenvectors of $T_m$, since $v = \|v\| v_0$ and $y_j$ is
expanded in the Lanczos basis. The hypothesis $\dim \mathcal{K}_m = m$ means
$m \le \operatorname{grade}(A, v)$: the process has not yet terminated.

The proof divides $f$ by the characteristic polynomial $\chi$ of $T_m$, which is monic of degree
$m$: $f = r + \chi s$ with $r$ and $s$ of degree less than $m$. The two measures integrate $r$
in the same way because $r(A) v = r(A_m) v$. The term $\chi s$ contributes nothing to either
side: against $\mu$ because $\chi(A) v$ is orthogonal to $\mathcal{K}_m$, which contains
$s(A) v$ (`Lanczos.aeval_charpoly_tridiag`), and against $\mu_m$ because $\chi(A_m) = 0$ by the
Cayley–Hamilton theorem. -/
theorem gauss_quadrature {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) {m : ℕ} (hm : 0 < m)
    (hmk : Module.finrank 𝕜 (subspace A v m) = m) {f : ℝ[X]} (hf : f.natDegree < 2 * m) :
    ∫ x, f.eval x ∂(Krylov.spectralMeasure hA hn v)
      = ∫ x, f.eval x ∂(Krylov.spectralMeasure
          (compression.isSymmetric A (subspace A v m) hA) hmk ⟨v, self_mem_subspace A v hm⟩) := by
  have hmg : m ≤ grade A v := by
    have h := finrank_subspace A v m
    rw [hmk] at h
    omega
  have hc : ((tridiag A v m).charpoly).Monic := Matrix.charpoly_monic _
  have hcd : ((tridiag A v m).charpoly).natDegree = m := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨r, s, hfsplit, hrdeg, hsdeg⟩ : ∃ r s : ℝ[X],
      f = r + (tridiag A v m).charpoly * s ∧ r.natDegree < m ∧ s.natDegree < m := by
    refine ⟨f %ₘ (tridiag A v m).charpoly, f /ₘ (tridiag A v m).charpoly,
      (modByMonic_add_div f (tridiag A v m).charpoly).symm, ?_, ?_⟩
    · rcases eq_or_ne (f %ₘ (tridiag A v m).charpoly) 0 with h0 | h0
      · rw [h0, natDegree_zero]
        exact hm
      · have h1 := degree_modByMonic_lt f hc
        rw [degree_eq_natDegree hc.ne_zero, hcd] at h1
        exact (natDegree_lt_iff_degree_lt h0).2 h1
    · rw [natDegree_divByMonic f hc, hcd]
      omega
  have hrmap : (r.map (algebraMap ℝ 𝕜)).natDegree < m :=
    lt_of_le_of_lt natDegree_map_le hrdeg
  have hsmap : (s.map (algebraMap ℝ 𝕜)).degree < (m : WithBot ℕ) := by
    refine lt_of_le_of_lt degree_map_le ?_
    rcases eq_or_ne s 0 with rfl | h0
    · rw [degree_zero]
      exact WithBot.bot_lt_coe m
    · rw [degree_eq_natDegree h0, Nat.cast_lt]
      exact hsdeg
  have hzeroA : inner 𝕜 v (aeval A (((tridiag A v m).charpoly * s).map (algebraMap ℝ 𝕜)) v)
      = 0 := by
    rw [Polynomial.map_mul, map_mul, Module.End.mul_apply,
      ← hA.aeval_map (tridiag A v m).charpoly v (aeval A (s.map (algebraMap ℝ 𝕜)) v),
      aeval_charpoly_tridiag hA v hmg, inner_smul_left,
      Submodule.inner_left_of_mem_orthogonal (aeval_apply_mem_subspace A v hsmap)
        (Arnoldi.vec_mem_orthogonal A v m), mul_zero]
  have hzeroB : aeval (compression A (subspace A v m))
      (((tridiag A v m).charpoly * s).map (algebraMap ℝ 𝕜))
        ⟨v, self_mem_subspace A v hm⟩ = 0 := by
    rw [Polynomial.map_mul, map_mul, Module.End.mul_apply, charpoly_tridiag_map hA v hmg,
      LinearMap.aeval_self_charpoly, LinearMap.zero_apply]
  have hr : (aeval (compression A (subspace A v m)) (r.map (algebraMap ℝ 𝕜))
      ⟨v, self_mem_subspace A v hm⟩ : E) = aeval A (r.map (algebraMap ℝ 𝕜)) v :=
    compression.aeval_apply_of_forall_pow_mem A (subspace A v m) (r.map (algebraMap ℝ 𝕜))
      fun i hi => pow_apply_mem_subspace A v (lt_of_le_of_lt hi hrmap)
  have key : ((∫ x, f.eval x ∂(Krylov.spectralMeasure hA hn v) : ℝ) : 𝕜)
      = ((∫ x, f.eval x ∂(Krylov.spectralMeasure
          (compression.isSymmetric A (subspace A v m) hA) hmk
          ⟨v, self_mem_subspace A v hm⟩) : ℝ) : 𝕜) := by
    rw [← Krylov.inner_aeval_eq_integral, ← Krylov.inner_aeval_eq_integral]
    conv_lhs => rw [hfsplit]
    conv_rhs => rw [hfsplit]
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_right]
    rw [hzeroA, hzeroB, inner_zero_right, add_zero, add_zero, Submodule.coe_inner, hr]
  exact_mod_cast key

/-- Under the hypotheses of `Lanczos.gauss_quadrature`, the Gauss rule written out as a sum: for
every real polynomial $f$ of degree at most $2m - 1$,
$$\int f \, d\mu = \sum_{j<m} |\langle y_j, v \rangle|^2 \, f(\theta_j),$$
where $(\theta_j, y_j)$ is an orthonormal eigenbasis of the compression of $A$ to
$\mathcal{K}_m(A, v)$. The nodes $\theta_j$ are the Ritz values, that is, the eigenvalues of
$T_m$.

When $y_j$ is written in the Lanczos basis and $v = \|v\| v_0$, the weight
$|\langle y_j, v \rangle|^2$ is $\|v\|^2$ times the squared first component of the corresponding
eigenvector of $T_m$. This is the usual form of the rule. -/
theorem gauss_quadrature_eq_sum {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) {m : ℕ} (hm : 0 < m)
    (hmk : Module.finrank 𝕜 (subspace A v m) = m) {f : ℝ[X]} (hf : f.natDegree < 2 * m) :
    ∫ x, f.eval x ∂(Krylov.spectralMeasure hA hn v)
      = ∑ j : Fin m, ‖inner 𝕜
            ((compression.isSymmetric A (subspace A v m) hA).eigenvectorBasis hmk j)
            (⟨v, self_mem_subspace A v hm⟩ : subspace A v m)‖ ^ 2 *
          f.eval ((compression.isSymmetric A (subspace A v m) hA).eigenvalues hmk j) := by
  rw [gauss_quadrature hA hn v hm hmk hf, Krylov.integral_spectralMeasure]

end Gauss

end Lanczos

namespace Polynomial

section ChristoffelDarboux

variable {K : Type*} [CommRing K] {p : ℕ → K[X]} {a b c : ℕ → K}
  (hp₁ : p 1 = (C (a 0) * X + C (b 0)) * p 0)
  (hrec : ∀ n, p (n + 2) = (C (a (n + 1)) * X + C (b (n + 1))) * p (n + 1) - C (c (n + 1)) * p n)
  (hac : ∀ n, c (n + 1) * a n = a (n + 1))
include hp₁ hrec hac

/-- The **Christoffel–Darboux identity**, in a form without division ([han2009theoretical], Theorem
3.7.3). Let $K$ be a commutative ring, and let polynomials $p_0, p_1, \dots \in K[X]$ and
scalars $a_n, b_n, c_n \in K$ satisfy
$$p_1 = (a_0 X + b_0) p_0, \qquad p_{n+2} = (a_{n+1} X + b_{n+1}) p_{n+1} - c_{n+1} p_n,$$
with the normalization $c_{n+1} a_n = a_{n+1}$ of orthonormal polynomials. Then for every
$N \in \mathbb{N}$ and $x, t \in K$
$$a_N (x - t) \sum_{n=0}^{N} p_n(x) p_n(t) = p_{N+1}(x) p_N(t) - p_N(x) p_{N+1}(t).$$

The condition on $p_1$ is the recurrence with $p_{-1} = 0$. Because the identity is multiplied
through by $a_N (x - t)$, it holds over any commutative ring and at $x = t$.
`Polynomial.christoffel_darboux_div` is the usual quotient form. -/
theorem christoffel_darboux (N : ℕ) (x t : K) :
    a N * (x - t) * ∑ n ∈ Finset.range (N + 1), (p n).eval x * (p n).eval t =
      (p (N + 1)).eval x * (p N).eval t - (p N).eval x * (p (N + 1)).eval t := by
  induction N with
  | zero =>
    rw [Finset.sum_range_one, hp₁]
    simp only [eval_mul, eval_add, eval_C, eval_X]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, hrec N, ← hac N]
    simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X]
    linear_combination c (N + 1) * ih

/-- The **Christoffel–Darboux identity, confluent form** ([han2009theoretical], Theorem 3.7.3).
Under the hypotheses of `Polynomial.christoffel_darboux`, for every $N \in \mathbb{N}$,
$$a_N \sum_{n=0}^{N} p_n^2 = p_{N+1}' p_N - p_N' p_{N+1}$$
as an identity of polynomials. It is the limit of `Polynomial.christoffel_darboux` as $t \to x$,
with the Wronskian of two consecutive polynomials on the right. -/
theorem christoffel_darboux_confluent (N : ℕ) :
    C (a N) * ∑ n ∈ Finset.range (N + 1), p n ^ 2 =
      derivative (p (N + 1)) * p N - derivative (p N) * p (N + 1) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_one, hp₁]
    simp only [derivative_mul, derivative_add, derivative_C, derivative_X]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, hrec N, ← hac N, C_mul]
    simp only [derivative_sub, derivative_mul, derivative_add, derivative_C, derivative_X]
    linear_combination C (c (N + 1)) * ih

end ChristoffelDarboux

section Field

variable {K : Type*} [Field K] {p : ℕ → K[X]} {a b c : ℕ → K}
  (hp₁ : p 1 = (C (a 0) * X + C (b 0)) * p 0)
  (hrec : ∀ n, p (n + 2) = (C (a (n + 1)) * X + C (b (n + 1))) * p (n + 1) - C (c (n + 1)) * p n)
  (hac : ∀ n, c (n + 1) * a n = a (n + 1))
include hp₁ hrec hac

/-- The **Christoffel–Darboux identity**, quotient form ([han2009theoretical], Theorem 3.7.3). Let
$K$ be a field, and let $p_n$, $a_n$, $b_n$, $c_n$ satisfy the hypotheses of
`Polynomial.christoffel_darboux`. If $a_N \neq 0$ and $x \neq t$, then
$$\sum_{n=0}^{N} p_n(x) p_n(t) = \frac{p_{N+1}(x) p_N(t) - p_N(x) p_{N+1}(t)}{a_N (x - t)}.$$
-/
theorem christoffel_darboux_div (N : ℕ) {x t : K} (ha : a N ≠ 0) (hxt : x ≠ t) :
    ∑ n ∈ Finset.range (N + 1), (p n).eval x * (p n).eval t =
      ((p (N + 1)).eval x * (p N).eval t - (p N).eval x * (p (N + 1)).eval t) /
        (a N * (x - t)) := by
  rw [eq_div_iff (mul_ne_zero ha (sub_ne_zero.2 hxt))]
  linear_combination christoffel_darboux hp₁ hrec hac N x t

/-- The **Christoffel–Darboux identity**, confluent quotient form ([han2009theoretical], Theorem
3.7.3). Let $K$ be a field, and let $p_n$, $a_n$, $b_n$, $c_n$ satisfy the hypotheses of
`Polynomial.christoffel_darboux`. If $a_N \neq 0$, then for every $x \in K$
$$\sum_{n=0}^{N} p_n(x)^2 = \frac{p_{N+1}'(x) p_N(x) - p_N'(x) p_{N+1}(x)}{a_N}.$$
-/
theorem christoffel_darboux_confluent_div (N : ℕ) (x : K) (ha : a N ≠ 0) :
    ∑ n ∈ Finset.range (N + 1), (p n).eval x ^ 2 =
      ((derivative (p (N + 1))).eval x * (p N).eval x -
        (derivative (p N)).eval x * (p (N + 1)).eval x) / a N := by
  have h := congrArg (eval x) (christoffel_darboux_confluent hp₁ hrec hac N)
  simp only [eval_mul, eval_C, eval_sub, eval_finsetSum, eval_pow] at h
  rw [eq_div_iff ha]
  linear_combination h

end Field

end Polynomial

namespace Lanczos

section Persistence

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (A : E →ₗ[𝕜] E) (b : E) {m k : ℕ}

section Padded

/-- The leading $(m+1) \times (m+1)$ block of $T_k$ is $T_{m+1}$, because the entries depend only on
the indices. -/
private theorem tridiag_castLE (h : m + 1 ≤ k) (i j : Fin (m + 1)) :
    tridiag A b k (Fin.castLE h i) (Fin.castLE h j) = tridiag A b (m + 1) i j := by
  rw [tridiag_apply, tridiag_apply, Fin.val_castLE, Fin.val_castLE]

variable (h : m + 1 ≤ k) {y : Fin k → ℝ} {z : Fin (m + 1) → ℝ}
  (hy : ∀ j : Fin (m + 1), y (Fin.castLE h j) = z j)
  (hy0 : ∀ i : Fin k, m + 1 ≤ (i : ℕ) → y i = 0)
include hy hy0

/-- If $\hat y$ is $z$ padded with zeros, the first $m + 1$ entries of $T_k \hat y$ are the entries
of $T_{m+1} z$. -/
private theorem mulVec_castLE (i : Fin (m + 1)) :
    (tridiag A b k).mulVec y (Fin.castLE h i) = (tridiag A b (m + 1)).mulVec z i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_eq_sum_castLE_of_forall_le h _ fun j hj => by rw [hy0 j hj, mul_zero]]
  exact Finset.sum_congr rfl fun j _ => by rw [tridiag_castLE, hy]

/-- If $\hat y$ is $z$ padded with zeros, entry $m + 1$ of $T_k \hat y$ is $\beta_m z_m$. -/
private theorem mulVec_of_val_eq {i : Fin k} (hi : (i : ℕ) = m + 1) :
    (tridiag A b k).mulVec y i = beta A b m * z (Fin.last m) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_eq_sum_castLE_of_forall_le h _ fun j hj => by rw [hy0 j hj, mul_zero]]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [hy, tridiag_apply, Fin.val_castLE, Fin.val_last, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega)]
  · intro j _ hj
    have hjm : (j : ℕ) < m := lt_of_le_of_ne (Nat.lt_succ_iff.1 j.2) fun hc =>
      hj (Fin.ext (by rw [hc, Fin.val_last]))
    rw [tridiag_apply, Fin.val_castLE, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

omit hy in
/-- If $\hat y$ is $z$ padded with zeros, the entries of $T_k \hat y$ below row $m + 1$ are $0$. -/
private theorem mulVec_of_lt_val {i : Fin k} (hi : m + 1 < (i : ℕ)) :
    (tridiag A b k).mulVec y i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases le_or_gt (m + 1) (j : ℕ) with hj | hj
  · rw [hy0 j hj, mul_zero]
  · rw [tridiag_apply, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), zero_mul]

/-- If $T_{m+1} z = \theta z$ and $\hat y$ is $z$ padded with zeros, then
$T_k \hat y - \theta \hat y$ is $0$ except in entry $m + 1$, where it is $\beta_m z_m$. -/
private theorem mulVec_sub_smul {θ : ℝ} (hθ : (tridiag A b (m + 1)).mulVec z = θ • z)
    (i : Fin k) :
    (tridiag A b k).mulVec y i - θ * y i =
      if (i : ℕ) = m + 1 then beta A b m * z (Fin.last m) else 0 := by
  rcases lt_trichotomy (i : ℕ) (m + 1) with hi | hi | hi
  · have hii : Fin.castLE h ⟨(i : ℕ), hi⟩ = i := Fin.ext rfl
    rw [ite_eq_right (by omega), ← hii, mulVec_castLE A b h hy hy0, hy, hθ]
    simp
  · rw [ite_eq_left hi, mulVec_of_val_eq A b h hy hy0 hi, hy0 i hi.ge, mul_zero, sub_zero]
  · rw [ite_eq_right (by omega), mulVec_of_lt_val A b hy0 hi, hy0 i hi.le, mul_zero, sub_zero]

end Padded

/-- A sum of squares over $i < k$ whose terms vanish except at $i = m + 1$, where the term is $w^2$,
is at most $w^2$. -/
private theorem sum_ite_sq_le (h : m + 1 ≤ k) (w : ℝ) :
    ∑ i : Fin k, (if (i : ℕ) = m + 1 then w else 0) ^ 2 ≤ w ^ 2 := by
  rcases eq_or_lt_of_le h with heq | hlt
  · have hzero : ∀ i : Fin k, (if (i : ℕ) = m + 1 then w else 0) ^ 2 = 0 := fun i => by
      have hi := i.isLt
      rw [ite_eq_right (by omega), zero_pow two_ne_zero]
    rw [Finset.sum_congr rfl fun i _ => hzero i, Finset.sum_const_zero]
    exact sq_nonneg w
  · rw [Finset.sum_eq_single (⟨m + 1, hlt⟩ : Fin k)]
    · simp
    · intro j _ hj
      rw [ite_eq_right fun hc => hj (Fin.ext hc), zero_pow two_ne_zero]
    · intro hc
      exact absurd (Finset.mem_univ _) hc

/-- **Persistence of Ritz values** ([meurant2006lanczos], Theorem 5, after Paige). Let $A$ be a
linear operator on $E$ and $b \in E$, and let $m + 1 \le k$. Let $\theta \in \mathbb{R}$ be an
eigenvalue of the Lanczos matrix $T_{m+1}$ with an eigenvector $z \in \mathbb{R}^{m+1}$ of
Euclidean norm $1$. Then $T_k$ has an eigenvalue $\mu$ with
$$|\mu - \theta| \le \beta_m |z_m|.$$
So a Ritz value whose eigenvector has a small last component is approximated at every later
step.

The original result is C. C. Paige, *Accuracy and effectiveness of the Lanczos algorithm for the
symmetric eigenproblem*, Linear Algebra and its Applications 34 (1980), 235–258. Indices start
at $0$: $\beta_m = (T_k)_{m+1, m}$ is the entry of $T_k$ that first meets the zeros that pad
$z$, and $z_m$ is the last component of $z$. The statement needs no symmetry of $A$, because
$T_k$ is real symmetric by construction. -/
theorem persistence (h : m + 1 ≤ k) {θ : ℝ} {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : ‖z‖ = 1) (hθ : Matrix.toEuclideanLin (tridiag A b (m + 1)) z = θ • z) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ (tridiag A b k) ∧
      |μ - θ| ≤ beta A b m * |z (Fin.last m)| := by
  have hθ' : (tridiag A b (m + 1)).mulVec (WithLp.ofLp z) = θ • WithLp.ofLp z := by
    simpa [Matrix.toLpLin_apply] using congrArg WithLp.ofLp hθ
  obtain ⟨y, hy, hy0⟩ : ∃ y : Fin k → ℝ,
      (∀ j : Fin (m + 1), y (Fin.castLE h j) = WithLp.ofLp z j) ∧
        ∀ i : Fin k, m + 1 ≤ (i : ℕ) → y i = 0 :=
    ⟨fun i => if hi : (i : ℕ) < m + 1 then WithLp.ofLp z ⟨i, hi⟩ else 0,
      fun j => by
        dsimp only
        rw [dite_eq_left (by rw [Fin.val_castLE]; exact j.isLt)]
        simp,
      fun i hi => by
        dsimp only
        exact dite_eq_right (by omega)⟩
  have hnorm : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ = 1 := by
    have hsq : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 1 ^ 2 := by
      have e1 : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ ^ 2 =
          ∑ j : Fin (m + 1), WithLp.ofLp z j ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_eq_sum_castLE_of_forall_le h _
          fun i hi => by rw [WithLp.ofLp_toLp, hy0 i hi]; ring]
        exact Finset.sum_congr rfl fun j _ => by rw [WithLp.ofLp_toLp, hy]
      rw [e1, ← EuclideanSpace.real_norm_sq_eq z, hz]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 hsq
  have hres : ‖Matrix.toEuclideanLin (tridiag A b k) (WithLp.toLp 2 y) -
      (θ : ℝ) • (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ ≤
        beta A b m * |WithLp.ofLp z (Fin.last m)| := by
    have hcomp : ∀ i : Fin k, (Matrix.toEuclideanLin (tridiag A b k) (WithLp.toLp 2 y) -
        (θ : ℝ) • (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))) i =
          if (i : ℕ) = m + 1 then beta A b m * WithLp.ofLp z (Fin.last m) else 0 := fun i => by
      rw [← mulVec_sub_smul A b h hy hy0 hθ' i]
      simp [Matrix.toLpLin_apply]
    have hsq : ‖Matrix.toEuclideanLin (tridiag A b k) (WithLp.toLp 2 y) -
        (θ : ℝ) • (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤
          (beta A b m * |WithLp.ofLp z (Fin.last m)|) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, mul_pow, sq_abs, ← mul_pow]
      simp only [hcomp]
      exact sum_ite_sq_le h _
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (beta_nonneg A b m) (abs_nonneg _))] at this
  obtain ⟨μ, hμ, hbound⟩ := (Matrix.isSymmetric_toEuclideanLin_iff.2
    (Matrix.isHermitian_iff_isSymm.2 (tridiag_isSymm A b k))).exists_hasEigenvalue_dist_le θ
      (norm_ne_zero_iff.1 (by rw [hnorm]; norm_num))
  refine ⟨μ, (Matrix.hasEigenvalue_toEuclideanLin_iff _ _).1 hμ, ?_⟩
  rw [hnorm, div_one] at hbound
  rw [← Real.norm_eq_abs]
  exact le_trans (by simpa using hbound) hres

end Persistence

end Lanczos

/-! ### The Dahlquist–Golub–Nash error identity -/

section DahlquistGolubNash

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E}

namespace Lanczos

/-- Let $A$ be a linear operator on $E$, $r \in E$ and $m \in \mathbb{N}$. The **Gauss quadrature
estimate** of the first inverse moment $\int \lambda^{-1} \, d\mu(\lambda)$ of the spectral
measure is the number
$$(T_m^{-1} e_1, e_1),$$
where $T_m$ is the Lanczos matrix of $(A, r)$ and $e_1 \in \mathbb{R}^m$ is the first unit
vector. It is the quantity through which the Lanczos process sees the energy norm of the
conjugate gradient error ([meurant2006lanczos], Theorem 9).

The number is written as a bilinear expression, so that it is $0$ for $m = 0$. The inverse is
`Matrix.inv`, which is $0$ at a singular matrix; `Lanczos.isUnit_tridiag` gives nonsingularity
in the case of interest. -/
noncomputable def tridiagInvFirst (A : E →ₗ[𝕜] E) (r : E) (m : ℕ) : ℝ :=
  ((tridiag A r m)⁻¹).mulVec (Krylov.firstVec (1 : ℝ) m) ⬝ᵥ Krylov.firstVec (1 : ℝ) m

/-- For $m = 0$ the Gauss quadrature estimate $(T_0^{-1} e_1, e_1)$ is $0$. -/
@[simp]
theorem tridiagInvFirst_zero (A : E →ₗ[𝕜] E) (r : E) : tridiagInvFirst A r 0 = 0 := by
  simp [tridiagInvFirst, dotProduct]

/-- Let $A$ be a coercive operator on $E$, let $b, x_0 \in E$, and let $r_0 = b - A x_0$ have a
finite-dimensional Krylov space. For $m \le \operatorname{grade}(A, r_0)$, the square Hessenberg
matrix $H_m$ of the Arnoldi process for $(A, r_0)$ is nonsingular.

For a coercive operator the Galerkin iterate over $\mathcal{K}_m$ exists and is unique, and this
is the nonsingularity of $H_m$ (`Krylov.existsUnique_isGalerkinIterate_iff_isUnit`). The matrix
$H_m$ is `Arnoldi.hessenbergSq A (b - A x₀) m`. -/
theorem isUnit_hessenbergSq [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hA : A.IsCoercive) {m : ℕ} (hm : m ≤ grade A (b - A x₀)) :
    IsUnit (Arnoldi.hessenbergSq A (b - A x₀) m) :=
  (existsUnique_isGalerkinIterate_iff_isUnit hm).1
    (existsUnique_isGalerkinIterate_of_isCoercive hA b x₀ m)

/-- Let $A$ be a symmetric coercive operator on $E$, let $b, x_0 \in E$, and let $r_0 = b - A x_0$
have a finite-dimensional Krylov space. For $m \le \operatorname{grade}(A, r_0)$, the Lanczos
tridiagonal matrix $T_m$ of $(A, r_0)$ is nonsingular.

For symmetric $A$ the Hessenberg matrix $H_m$ is, entry by entry, the image of the real matrix
$T_m$ in $\mathbb{K}$, and this map is injective. So the result follows from
`Lanczos.isUnit_hessenbergSq`. -/
theorem isUnit_tridiag [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hA : A.IsSymmetricCoercive) {m : ℕ} (hm : m ≤ grade A (b - A x₀)) :
    IsUnit (tridiag A (b - A x₀) m) := by
  have h1 := isUnit_hessenbergSq hA.isCoercive hm
  have hdet : ((tridiag A (b - A x₀) m).map (algebraMap ℝ 𝕜)).det
      = algebraMap ℝ 𝕜 (tridiag A (b - A x₀) m).det := by
    rw [RingHom.map_det (algebraMap ℝ 𝕜), RingHom.mapMatrix_apply]
  rw [hessenbergSq_eq_map_tridiag (b - A x₀) hA.isSymmetric m, Matrix.isUnit_iff_isUnit_det, hdet,
    isUnit_iff_ne_zero] at h1
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact fun hc => h1 (by rw [hc, map_zero])

end Lanczos

namespace CG

open Lanczos

variable [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- Below the grade, $\langle v_i, \sum_j y_j v_j \rangle = y_i$ by the orthonormality of the
Arnoldi vectors. -/
private theorem inner_vec_sum {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) (i : Fin m) :
    inner 𝕜 (Arnoldi.vec A (b - A x₀) (i : ℕ))
        (∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ)) = y i := by
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      Arnoldi.norm_vec_eq_one_of_lt_grade A _ (lt_of_lt_of_le i.isLt hm)]
    norm_num
  · intro j _ hji
    rw [inner_smul_right,
      Arnoldi.inner_vec_eq_zero A _ (fun hc => hji (Fin.ext hc.symm)), mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

omit [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] in
/-- The $m$-th Arnoldi vector is orthogonal to $\mathcal{K}_m$:
$\langle v_m, \sum_{j<m} y_j v_j \rangle = 0$. -/
private theorem inner_vec_last_sum {m : ℕ} (y : Fin m → 𝕜) :
    inner 𝕜 (Arnoldi.vec A (b - A x₀) m) (∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ)) = 0 := by
  rw [inner_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [inner_smul_right,
    Arnoldi.inner_vec_eq_zero A _ (fun hc => absurd hc.symm (Nat.ne_of_lt j.isLt)), mul_zero]

/-- The quadratic form of $A$ on $\mathcal{K}_m$ in Arnoldi coordinates: $\langle A V_m y, V_m y
\rangle = \sum_j \overline{(H_m y)_j} \, y_j$. -/
private theorem inner_apply_sum_sum {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    inner 𝕜 (A (∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ)))
        (∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ))
      = ∑ j, (starRingEnd 𝕜) ((Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y j) * y j := by
  have hlast : inner 𝕜 ((hessenbergOf (Arnoldi.coeff A (b - A x₀)) m).mulVec y (Fin.last m) •
      Arnoldi.vec A (b - A x₀) ((Fin.last m : Fin (m + 1)) : ℕ))
      (∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ)) = 0 := by
    rw [inner_smul_left]
    have hval : ((Fin.last m : Fin (m + 1)) : ℕ) = m := rfl
    rw [hval, inner_vec_last_sum y, mul_zero]
  rw [(Arnoldi.hessenbergRelation A (b - A x₀)).apply_sum m y, sum_inner, Fin.sum_univ_castSucc,
    hlast, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left]
  have hval : ((j.castSucc : Fin (m + 1)) : ℕ) = (j : ℕ) := rfl
  have hval2 : (hessenbergOf (Arnoldi.coeff A (b - A x₀)) m).mulVec y j.castSucc
      = (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y j := rfl
  rw [hval, inner_vec_sum hm y j, hval2]

/-- With $\beta = \|r_0\|$, $\langle r_0, V_m y \rangle = \sum_j \overline{(\beta e_1)_j} \, y_j$.
-/
private theorem inner_residual_sum {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    inner 𝕜 (b - A x₀) (∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ))
      = ∑ j, (starRingEnd 𝕜) (Krylov.firstVec ((‖b - A x₀‖ : ℝ) : 𝕜) m j) * y j := by
  have key : ∀ z : E, inner 𝕜 (b - A x₀) z
      = (starRingEnd 𝕜) ((‖b - A x₀‖ : ℝ) : 𝕜) *
        inner 𝕜 (Arnoldi.vec A (b - A x₀) 0) z := by
    intro z
    conv_lhs => rw [← Arnoldi.smul_vec_zero A (b - A x₀)]
    rw [inner_smul_left]
  rw [key, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]
  by_cases hj : (j : ℕ) = 0
  · have hgrade : 0 < grade A (b - A x₀) :=
      lt_of_le_of_lt (Nat.zero_le _) (lt_of_lt_of_le j.isLt hm)
    have hj0 : Arnoldi.vec A (b - A x₀) (j : ℕ) = Arnoldi.vec A (b - A x₀) 0 := by rw [hj]
    rw [hj0, inner_self_eq_norm_sq_to_K, Arnoldi.norm_vec_eq_one_of_lt_grade A _ hgrade,
      Krylov.firstVec, ite_eq_left hj]
    push_cast
    ring
  · rw [Arnoldi.inner_vec_eq_zero A _ (Ne.symm hj), Krylov.firstVec, ite_eq_right hj, map_zero,
      mul_zero, zero_mul, mul_zero]

/-- If $A$ is symmetric coercive, $A x^* = b$ and $H_m y = \|r_0\| e_1$, then $\|x^* - (x_0 + V_m
y)\|_A^2 = \|x^* - x_0\|_A^2 - \operatorname{Re} \langle A (x^* - x_0), V_m y \rangle$. -/
private theorem energyNorm_error_sq_eq_sub (hA : A.IsSymmetricCoercive) {xstar : E}
    (hstar : A xstar = b) {m : ℕ} (hm : m ≤ grade A (b - A x₀)) {y : Fin m → 𝕜}
    (hy : (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y
      = Krylov.firstVec ((‖b - A x₀‖ : ℝ) : 𝕜) m) :
    energyNorm A (xstar - (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ))) ^ 2
      = energyNorm A (xstar - x₀) ^ 2
        - RCLike.re (inner 𝕜 (A (xstar - x₀))
            (∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ))) := by
  set S : E := ∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ) with hS
  set e : E := xstar - x₀ with he
  have hAe : A e = b - A x₀ := by rw [he, map_sub, hstar]
  have hquad : inner 𝕜 (A S) S = inner 𝕜 (A e) S := by
    rw [hAe, hS, inner_apply_sum_sum hm y, hy, ← inner_residual_sum hm y]
  have hcross : inner 𝕜 (A S) e = (starRingEnd 𝕜) (inner 𝕜 (A e) S) := by
    rw [hA.isSymmetric S e, ← inner_conj_symm]
  have hexpand : ∀ u w : E, inner 𝕜 (A (u - w)) (u - w)
      = inner 𝕜 (A u) u - inner 𝕜 (A u) w - inner 𝕜 (A w) u + inner 𝕜 (A w) w := by
    intro u w
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  have hexp : inner 𝕜 (A (e - S)) (e - S)
      = inner 𝕜 (A e) e - (starRingEnd 𝕜) (inner 𝕜 (A e) S) := by
    rw [hexpand e S, hquad, hcross]
    ring
  have hsub : xstar - (x₀ + S) = e - S := by rw [he]; abel
  rw [hsub, hA.energyNorm_sq, hA.energyNorm_sq, hexp, map_sub, RCLike.conj_re]

/-- The vector $\beta e_1$ is $\beta$ times $e_1$. -/
private theorem firstVec_eq_smul (β : ℝ) (m : ℕ) :
    Krylov.firstVec β m = β • Krylov.firstVec (1 : ℝ) m := by
  funext i
  rw [Pi.smul_apply, Krylov.firstVec, Krylov.firstVec, smul_eq_mul]
  split <;> simp

/-- For the Galerkin coordinates $y$, $\operatorname{Re} \langle r_0, V_m y \rangle = \|r_0\|^2
(T_m^{-1} e_1, e_1)$. -/
private theorem re_inner_residual_sum_eq (hA : A.IsSymmetricCoercive) {m : ℕ}
    (hm : m ≤ grade A (b - A x₀)) {y : Fin m → 𝕜}
    (hy : (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y
      = Krylov.firstVec ((‖b - A x₀‖ : ℝ) : 𝕜) m) :
    RCLike.re (inner 𝕜 (b - A x₀) (∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ)))
      = ‖b - A x₀‖ ^ 2 * tridiagInvFirst A (b - A x₀) m := by
  set T := tridiag A (b - A x₀) m with hT
  have hTu : IsUnit T := isUnit_tridiag hA hm
  set y' : Fin m → ℝ := (T⁻¹).mulVec (Krylov.firstVec ‖b - A x₀‖ m) with hy'def
  have hTy' : T.mulVec y' = Krylov.firstVec ‖b - A x₀‖ m := by
    rw [hy'def]
    exact Matrix.mulVec_nonsing_inv_mulVec hTu _
  have hmapfirst : ∀ i : Fin m,
      Krylov.firstVec ((‖b - A x₀‖ : ℝ) : 𝕜) m i
        = algebraMap ℝ 𝕜 (Krylov.firstVec ‖b - A x₀‖ m i) := by
    intro i
    rw [Krylov.firstVec, Krylov.firstVec]
    split <;> simp
  have hyeq : y = fun j => algebraMap ℝ 𝕜 (y' j) := by
    refine Matrix.mulVec_injective_iff_isUnit.2 (isUnit_hessenbergSq hA.isCoercive hm) ?_
    rw [hy]
    funext i
    have h := RingHom.map_mulVec (algebraMap ℝ 𝕜) T y' i
    rw [hTy'] at h
    simp only [Function.comp_def] at h
    rw [hessenbergSq_eq_map_tridiag (b - A x₀) hA.isSymmetric m, ← hT, ← h, hmapfirst i]
  rw [inner_residual_sum hm y, hyeq]
  have hsum : ∑ j, (starRingEnd 𝕜) (Krylov.firstVec ((‖b - A x₀‖ : ℝ) : 𝕜) m j) *
      algebraMap ℝ 𝕜 (y' j)
      = algebraMap ℝ 𝕜 (∑ j, Krylov.firstVec ‖b - A x₀‖ m j * y' j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hmapfirst j, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal]
  rw [hsum, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re]
  have hdot : ∑ j, Krylov.firstVec ‖b - A x₀‖ m j * y' j
      = Krylov.firstVec ‖b - A x₀‖ m ⬝ᵥ y' := rfl
  rw [hdot, hy'def, firstVec_eq_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    tridiagInvFirst, ← hT, dotProduct_comm]
  simp only [smul_eq_mul]
  ring

/-- The **Dahlquist–Golub–Nash identity** ([meurant2006lanczos], Theorem 9). Let $A$ be a symmetric
coercive operator on $E$, let $b, x_0, x^* \in E$ with $A x^* = b$, and let $r_0 = b - A x_0$
have a finite-dimensional Krylov space. Let $n = \operatorname{grade}(A, r_0)$, and let $x_k$ be
the conjugate gradient iterate after $k \le n$ steps. Then
$$\|x^* - x_k\|_A^2 = \|r_0\|^2 \big( (T_n^{-1} e_1, e_1) - (T_k^{-1} e_1, e_1) \big).$$
So the energy norm of the conjugate gradient error is the error of the Gauss quadrature rule for
$f(\lambda) = \lambda^{-1}$.

Each step is elementary once the Galerkin coordinates $y_k$ are known. The error expands as
$\|x^* - x_0\|_A^2 - \langle r_0, V_k y_k \rangle$, because the cross term and the quadratic
term cancel by $T_k y_k = \|r_0\| e_1$, and this inner product is
$\|r_0\|^2 (T_k^{-1} e_1, e_1)$. The first term is the same expression at $k = n$, where the
iterate is exact. The tridiagonal matrices are nonsingular up to the grade
(`Lanczos.isUnit_tridiag`), so the statement about $T_k^{-1}$ is not vacuous. The iterate $x_k$
is `(CG.iterate A b x₀ k).x`, the energy norm is `energyNorm`, and $(T_m^{-1} e_1, e_1)$ is
`Lanczos.tridiagInvFirst`. -/
theorem energyNorm_error_sq_eq_sub_inner_inv (hA : A.IsSymmetricCoercive) {xstar : E}
    (hstar : A xstar = b) {k : ℕ} (hk : k ≤ grade A (b - A x₀)) :
    energyNorm A (xstar - (CG.iterate A b x₀ k).x) ^ 2
      = ‖b - A x₀‖ ^ 2 * (tridiagInvFirst A (b - A x₀) (grade A (b - A x₀))
          - tridiagInvFirst A (b - A x₀) k) := by
  have key : ∀ m, m ≤ grade A (b - A x₀) →
      energyNorm A (xstar - (CG.iterate A b x₀ m).x) ^ 2
        = energyNorm A (xstar - x₀) ^ 2
          - ‖b - A x₀‖ ^ 2 * tridiagInvFirst A (b - A x₀) m := by
    intro m hm
    obtain ⟨y, hy, hx⟩ :=
      (isGalerkinIterate_iff_exists_mulVec_eq hm _).1 (CG.isGalerkinIterate b x₀ hA m)
    rw [hx, energyNorm_error_sq_eq_sub hA hstar hm hy,
      show A (xstar - x₀) = b - A x₀ by rw [map_sub, hstar], re_inner_residual_sum_eq hA hm hy]
  have hzero : energyNorm A (xstar - (CG.iterate A b x₀ (grade A (b - A x₀))).x) ^ 2 = 0 := by
    have h1 : A (CG.iterate A b x₀ (grade A (b - A x₀))).x = b :=
      (CG.isGalerkinIterate b x₀ hA _).apply_eq_of_grade_le le_rfl
    have h2 : (CG.iterate A b x₀ (grade A (b - A x₀))).x = xstar := by
      by_contra hne
      have h3 : A ((CG.iterate A b x₀ (grade A (b - A x₀))).x - xstar) = 0 := by
        rw [map_sub, h1, hstar, sub_self]
      have h4 := hA.isCoercive.inner_self_pos (sub_ne_zero.2 hne)
      rw [h3, inner_zero_left, map_zero] at h4
      exact lt_irrefl 0 h4
    rw [h2, sub_self, energyNorm]
    simp
  have hgrade := key _ le_rfl
  rw [hzero] at hgrade
  rw [key k hk]
  have h0 : energyNorm A (xstar - x₀) ^ 2
      = ‖b - A x₀‖ ^ 2 * tridiagInvFirst A (b - A x₀) (grade A (b - A x₀)) := by linarith
  rw [h0]
  ring

end CG

end DahlquistGolubNash
