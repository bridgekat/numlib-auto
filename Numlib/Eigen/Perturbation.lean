/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import Numlib.Eigen.PowerMethod
import Numlib.Eigen.RayleighRitz
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Topology.Algebra.Polynomial

/-!
# Eigenvalue perturbation and a posteriori bounds

This file bounds the distance from an approximate eigenvalue to the spectrum, and the motion of the
eigenvalues under a perturbation. An approximate eigenpair of an operator $A$ is a vector $x$,
usually of norm $1$, together with a scalar $\theta$, usually the Rayleigh quotient $\theta =
\operatorname{Re} \langle Ax, x \rangle$; its residual is $r = Ax - \theta x$. For a symmetric
operator on a finite-dimensional space, the residual bounds turn $\|r\|$ into a distance from
$\theta$ to the spectrum: some eigenvalue lies within $\|r\|$ of $\theta$, and the Kato–Temple bound
and its corollaries improve this to $\|r\|^2 / \delta$ when the other eigenvalues are at distance
$\delta$. A small residual and a separated eigenvalue also force a small angle between $x$ and the
eigenspace. These results follow [saad2011numerical], Chapter 3; see also [meurant2006lanczos], §2.1
and [choi2006iterative], §2.4.

For general matrices, the file proves the **Bauer–Fike theorem**: if $A = XDX^{-1}$ with $D$
diagonal, every eigenvalue of $A + E$ lies within $\kappa(X) \|E\|$ of an eigenvalue of $A$
([saad2011numerical], Theorem 3.6; [kress1998numerical], Problem 7.6; [golub2013matrix], Theorem
7.2.2). It also proves a bound of Henrici type from a Schur form ([golub2013matrix], Theorem 7.2.3),
the backward error of an approximate eigenpair ([saad2011numerical], Proposition 3.4), the theorems
of Bendixson and Hirsch on the real and imaginary parts of the eigenvalues ([saad2003iterative],
Theorem 1.35; [quarteroni2000numerical], Theorem 5.1), the Gershgorin discs and the count of the
eigenvalues in a union of discs ([saad2011numerical], Theorems 3.11 and 3.12), and the first-order
perturbation theory of a simple eigenvalue ([saad2011numerical], Definition 3.1 and §3.2.1).

## Main definitions

* `Module.End.eigenvalueCondNumber`: the condition number $\|u\| \|w\| / |\langle w, u \rangle|$ of
  a simple eigenvalue with right eigenvector $u$ and left eigenvector $w$.
* `Module.End.IsLeftEigenvector`: $\langle w, Ay \rangle = \lambda \langle w, y \rangle$ for every
  $y$.

## Main results

* `LinearMap.IsSymmetric.exists_hasEigenvalue_dist_le`: some eigenvalue $\mu$ has
  $|\mu - \theta| \le \|Ax - \theta x\| / \|x\|$.
* `LinearMap.IsSymmetric.kato_temple`: the Kato–Temple bounds $-\|r\|^2 / (b - \theta) \le \lambda -
  \theta \le \|r\|^2 / (\theta - a)$.
* `LinearMap.IsSymmetric.sin_angle_le_norm_residual_div`: $\sin \angle(x, \ker(A - \lambda)) \le
  \|r\| / \delta$.
* `LinearMap.IsSymmetric.dist_eigenvectorSpan_le_norm_residual_div`: the distance from $x$ to the
  span of a group of eigenvectors is at most $\|r\| / \delta$.
* `isLeast_eigen_backwardError`: the least norm of a perturbation that makes $(\theta, u)$ an exact
  eigenpair is $\|Au - \theta u\|$.
* `re_hasEigenvalue_mem_Icc_of_symmetricPart`, `Matrix.hirsch_re`, `Matrix.hirsch_im`: the real and
  the imaginary parts of the eigenvalues of $A$ lie between the extreme eigenvalues of $(A + A^H)/2$
  and of $(A - A^H)/(2i)$.
* `Module.End.deriv_eigenvalue_perturbation`, `Module.End.norm_deriv_eigenvalue_perturbation_le`:
  along a differentiable branch of eigenpairs of $A + tB$, the eigenvalue has the derivative
  $\langle w, Bu \rangle / \langle w, u \rangle$ at $t = 0$, of modulus at most $\|B\|$ times the
  condition number.
* `Module.End.hasDerivAt_eigenvalue_perturbation`,
  `Module.End.hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one`: a simple eigenvalue has such a
  branch.
* `Matrix.bauer_fike`, `Matrix.bauer_fike_lpOpNorm`, `Matrix.bauer_fike_residual`: the Bauer–Fike
  theorem, in the spectral norm, in every induced $p$-norm, and in residual form.
* `Matrix.exists_norm_sub_le_of_schur`: the Henrici-type bound for a matrix that need not be
  diagonalizable.
* `Matrix.spectrum_subset_iUnion_closedBall`, `Matrix.card_spectrum_of_disjoint_gershgorin`: the
  spectrum lies in the union of the Gershgorin discs, and a union of $m$ discs that is disjoint from
  the other discs contains exactly $m$ eigenvalues, counted with multiplicity.
* `Matrix.IsHermitian.exists_mem_spectrum_abs_sub_le_of_mul_sub_mul`,
  `Matrix.IsHermitian.exists_embedding_abs_sub_le_of_mul_sub_mul`: if
  $\|AQ_1 - Q_1 S\|_2 \le \varepsilon$ for an orthonormal block $Q_1$, each eigenvalue of $S$ is
  within $\varepsilon$ of an eigenvalue of $A$, and the sorted eigenvalues of $S$ are within
  $\sqrt{2} \varepsilon$ of distinct eigenvalues of $A$ ([golub2013matrix], Theorem 8.1.13).

## Proof outline

The symmetric bounds expand $x$ in an orthonormal eigenbasis $v_i$ with eigenvalues $\lambda_i$, and
compare sums $\sum_i f(\lambda_i) |\langle v_i, x \rangle|^2$. The Gershgorin count follows the
homotopy $A(t) = D + tH$ of [saad2011numerical], with $D$ the diagonal of $A$; its continuity
argument is `Polynomial.countRootsIn_eq_of_preconnected`: the number of roots of a monic polynomial
in a compact set is constant along a connected family, as long as the roots stay in the union of two
disjoint compact sets. This is a compactness argument in the coefficients and not Rouché's theorem,
so the union $S$ may consist of overlapping discs. The branch of a simple eigenvalue comes from the
inverse function theorem for $(t, \mu, z) \mapsto (t, \langle w, z \rangle, Az + tBz - \mu z)$,
whose derivative is injective because the eigenvalue is simple; no determinant and no implicit
function theorem are used. The Bauer–Fike and Henrici-type bounds rest on one resolvent step: an
eigenvalue $\mu$ of $A + E$ that is not an eigenvalue of $A$ has $\|(\mu I - A)^{-1} E\| \ge 1$.

## Implementation notes

* The residual bound for the eigenvector uses the eigenspace of $\lambda$, and not the line through
  one eigenvector, which [saad2011numerical], Theorem 3.9 uses. The two agree exactly when $\lambda$
  is simple, and that case is `LinearMap.IsSymmetric.sin_angle_span_singleton_le_norm_residual_div`.
  The doc comment of `LinearMap.IsSymmetric.sin_angle_le_norm_residual_div` gives a counterexample
  to the line form at a multiple eigenvalue.
* The block residual bound `Matrix.IsHermitian.exists_mem_spectrum_abs_sub_le_of_mul_sub_mul` has
  the constant $1$ of the residual bound for one vector, in place of the constant $\sqrt{2}$ of
  [golub2013matrix], Theorem 8.1.13.
* The count of the eigenvalues in a set $S$ is `Polynomial.countRootsIn S A.charpoly`, the number of
  roots of the characteristic polynomial in $S$, counted with multiplicity.
* Bauer–Fike, Gershgorin, Kato–Temple and Bendixson are the classical names of the results; the
  forms proved here are those of the cited texts.
* The open and the closed $\varepsilon$-pseudospectra are in `Numlib.Eigen.Pseudospectrum`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $K$ and $L$ be subspaces with orthogonal projections. If $K = L$, then
$\sin \angle(u, K) = \sin \angle(u, L)$ for every vector $u$.

This lemma is needed because `Submodule.sinAngle` depends on an instance of
`Submodule.HasOrthogonalProjection`, and two spellings of the same subspace can carry instances
found in different ways; rewriting the subspace directly under `Submodule.sinAngle` fails. It is
the analogue of `Submodule.tanAngle_congr`. -/
theorem Submodule.sinAngle_congr {K L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : K = L) (u : E) : K.sinAngle u = L.sinAngle u := by
  subst h
  rfl

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-!
### Expansion in an eigenbasis

All the bounds for symmetric operators below are inequalities between sums
$\sum_i f(\lambda_i) |\langle v_i, x \rangle|^2$ over an orthonormal eigenbasis $v$ with eigenvalues
$\lambda$.
-/

private theorem repr_sub_smul {n : ℕ} (hn : Module.finrank 𝕜 E = n) (θ : ℝ) (x : E) (i : Fin n) :
    (hA.eigenvectorBasis hn).repr (A x - (θ : 𝕜) • x) i =
      ((hA.eigenvalues hn i - θ : ℝ) : 𝕜) * (hA.eigenvectorBasis hn).repr x i := by
  rw [map_sub, PiLp.sub_apply, map_smul, PiLp.smul_apply, smul_eq_mul,
    hA.eigenvectorBasis_apply_self_apply hn]
  push_cast
  ring

private theorem norm_residual_sq {n : ℕ} (hn : Module.finrank 𝕜 E = n) (θ : ℝ) (x : E) :
    ‖A x - (θ : 𝕜) • x‖ ^ 2 =
      ∑ i, (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [hA.norm_sq_eq_sum_norm_repr_sq hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA.repr_sub_smul hn, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

/-- For a unit vector $x$ with Rayleigh quotient $\theta = \operatorname{Re} \langle Ax, x \rangle$,
residual $r = Ax - \theta x$ and eigenbasis coefficients $c_i$, and for all
$u, v \in \mathbb{R}$, $\sum_i (\lambda_i - u)(\lambda_i - v) |c_i|^2 = \|r\|^2 + (\theta -
u)(\theta - v)$; this identity is behind [saad2011numerical], Lemma 3.2 and the Kato–Temple
bounds. -/
private theorem sum_quadratic {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E} (hx : ‖x‖ = 1)
    (u v : ℝ) :
    ∑ i, (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v) *
        ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 =
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 +
        (RCLike.re (inner 𝕜 (A x) x) - u) * (RCLike.re (inner 𝕜 (A x) x) - v) := by
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  have hs : ∑ i, ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = 1 := by
    rw [← hA.norm_sq_eq_sum_norm_repr_sq hn, hx, one_pow]
  have hth : ∑ i, hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = θ :=
    (hA.re_inner_apply_self_eq_sum hn x).symm
  have hr : ‖A x - (θ : 𝕜) • x‖ ^ 2 =
      ∑ i, (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 :=
    hA.norm_residual_sq hn θ x
  have hsplit : ∀ i : Fin n,
      (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v) *
          ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 =
        (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 +
          (2 * θ - u - v) * (hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2) +
          (u * v - θ ^ 2) * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hs, hth, ← hr]
  ring

private theorem quadratic_nonneg {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E} (hx : ‖x‖ = 1)
    (u v : ℝ) (h : ∀ i, 0 ≤ (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v)) :
    0 ≤ ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 +
      (RCLike.re (inner 𝕜 (A x) x) - u) * (RCLike.re (inner 𝕜 (A x) x) - v) := by
  rw [← hA.sum_quadratic hn hx u v]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (sq_nonneg _)

/-- **Residual bound** ([saad2011numerical], Corollary 3.3). Let $A$ be a symmetric operator on a
finite-dimensional inner product space, let $\theta \in \mathbb{R}$, and let $x \neq 0$. Then
$A$ has an eigenvalue $\mu$ with
$$|\mu - \theta| \le \frac{\|Ax - \theta x\|}{\|x\|}.$$
-/
theorem exists_hasEigenvalue_dist_le (θ : ℝ) {x : E} (hx : x ≠ 0) :
    ∃ μ : 𝕜, Module.End.HasEigenvalue A μ ∧ ‖μ - (θ : 𝕜)‖ ≤ ‖A x - (θ : 𝕜) • x‖ / ‖x‖ := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have : Subsingleton E := Module.finrank_zero_iff.mp (hn'.symm.trans h)
      exact absurd (Subsingleton.elim x 0) hx
    · exact h
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
    (fun i => |hA.eigenvalues hn i - θ|) ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  refine ⟨(hA.eigenvalues hn i₀ : 𝕜), hA.hasEigenvalue_eigenvalues hn i₀, ?_⟩
  have hnorm : ‖((hA.eigenvalues hn i₀ : ℝ) : 𝕜) - (θ : 𝕜)‖ = |hA.eigenvalues hn i₀ - θ| := by
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
  rw [hnorm, le_div_iff₀ (norm_pos_iff.mpr hx)]
  have key : (|hA.eigenvalues hn i₀ - θ| * ‖x‖) ^ 2 ≤ ‖A x - (θ : 𝕜) • x‖ ^ 2 := by
    rw [mul_pow, sq_abs, hA.norm_sq_eq_sum_norm_repr_sq hn, hA.norm_residual_sq hn,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have habs := hi₀ i (Finset.mem_univ i)
    nlinarith [abs_nonneg (hA.eigenvalues hn i₀ - θ), abs_nonneg (hA.eigenvalues hn i - θ),
      sq_abs (hA.eigenvalues hn i₀ - θ), sq_abs (hA.eigenvalues hn i - θ)]
  exact le_of_sq_le_sq key (norm_nonneg _)

/-- Let $A$ be a symmetric operator on a finite-dimensional inner product space, and let $x$ be a
unit vector with Rayleigh quotient $\theta = \operatorname{Re} \langle Ax, x \rangle$ and
residual $r = Ax - \theta x$. Let $\alpha < \theta < \beta$, and suppose that no eigenvalue of
$A$ has its real part in $(\alpha, \beta)$. Then
$$(\beta - \theta)(\theta - \alpha) \le \|r\|^2.$$
This is Lemma 3.2 of [saad2011numerical]. -/
theorem rayleigh_gap_le_norm_residual_sq {x : E} (hx : ‖x‖ = 1) {α β : ℝ}
    (hαβ : α < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < β)
    (hfree : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∉ Set.Ioo α β) :
    (β - RCLike.re (inner 𝕜 (A x) x)) * (RCLike.re (inner 𝕜 (A x) x) - α) ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 := by
  set n := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  have hout : ∀ i : Fin n, hA.eigenvalues hn i ≤ α ∨ β ≤ hA.eigenvalues hn i := by
    intro i
    have hfi := hfree ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
    rwa [RCLike.ofReal_re, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hfi
  have h := hA.quadratic_nonneg hn hx α β fun i => by
    rcases hout i with h | h
    · nlinarith
    · exact mul_nonneg (by linarith) (by linarith)
  nlinarith [h]

/-- The **Kato–Temple bounds** ([saad2011numerical], Theorem 3.8). Let $A$ be a symmetric operator
on a finite-dimensional inner product space, and let $x$ be a unit vector with Rayleigh quotient
$\theta = \operatorname{Re} \langle Ax, x \rangle$ and residual $r = Ax - \theta x$. Let
$a < \theta < b$, and let $\mu$ be a scalar with $\operatorname{Re} \mu \in (a, b)$ such that
every eigenvalue of $A$ with real part in $(a, b)$ equals $\mu$. Then
$$-\frac{\|r\|^2}{b - \theta} \le \operatorname{Re} \mu - \theta \le \frac{\|r\|^2}{\theta -
  a}.$$

The scalar $\mu$ need not be an eigenvalue; this only makes the statement more general. The
lower bound has the distance from $\theta$ to the right end $b$ in the denominator, and the
upper bound the distance to the left end $a$. With the two denominators exchanged the statement
is false: for $A = \operatorname{diag}(0, 10)$ and a unit vector $x$ with $x_2^2 = 3/5$, one
gets $\theta = 6$ and $\|r\|^2 = 24$, and $(a, b) = (5, 20)$ contains only the eigenvalue $10$,
but $10 - 6 = 4 > 24 / (20 - 6)$. -/
theorem kato_temple {x : E} (hx : ‖x‖ = 1) {a b : ℝ} {μ : 𝕜}
    (hab : a < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < b)
    (hμab : RCLike.re μ ∈ Set.Ioo a b)
    (hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → RCLike.re μ' ∈ Set.Ioo a b → μ' = μ) :
    -(‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / (b - RCLike.re (inner 𝕜 (A x) x))) ≤
        RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ∧
      RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ≤
        ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 /
          (RCLike.re (inner 𝕜 (A x) x) - a) := by
  set n := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  obtain ⟨hab1, hab2⟩ := hab
  obtain ⟨hμa, hμb⟩ := Set.mem_Ioo.mp hμab
  -- every eigenvalue is either `re μ` or outside `(a, b)`
  have hout : ∀ i : Fin n, hA.eigenvalues hn i = RCLike.re μ ∨
      (hA.eigenvalues hn i ≤ a ∨ b ≤ hA.eigenvalues hn i) := by
    intro i
    by_cases hin : a < hA.eigenvalues hn i ∧ hA.eigenvalues hn i < b
    · left
      have heq := hunique ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
        (by rw [RCLike.ofReal_re, Set.mem_Ioo]; exact hin)
      rw [← heq, RCLike.ofReal_re]
    · right
      rwa [not_and_or, not_lt, not_lt] at hin
  constructor
  · have h := hA.quadratic_nonneg hn hx (RCLike.re μ) b fun i => by
      rcases hout i with h | h | h
      · rw [h]; simp
      · nlinarith
      · exact mul_nonneg (by linarith) (by linarith)
    rw [← hθ] at h
    rw [neg_le, le_div_iff₀ (by linarith : (0 : ℝ) < b - θ)]
    nlinarith [h]
  · have h := hA.quadratic_nonneg hn hx (RCLike.re μ) a fun i => by
      rcases hout i with h | h | h
      · rw [h]; simp
      · nlinarith
      · exact mul_nonneg (by linarith) (by linarith)
    rw [← hθ] at h
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < θ - a)]
    nlinarith [h]

/-- Let $A$ be a symmetric operator on a finite-dimensional inner product space, and let $x$ be a
unit vector with Rayleigh quotient $\theta = \operatorname{Re} \langle Ax, x \rangle$ and
residual $r = Ax - \theta x$. Let $\mu$ be a scalar and $\delta > 0$, suppose that every
eigenvalue $\mu' \neq \mu$ of $A$ has $\delta \le |\operatorname{Re} \mu' - \theta|$, and
suppose that $|\operatorname{Re} \mu - \theta| \le \|r\|$. Then
$$|\operatorname{Re} \mu - \theta| \le \frac{\|r\|^2}{\delta}.$$
This is Corollary 3.4 of [saad2011numerical]. -/
theorem abs_sub_rayleigh_le_norm_residual_sq_div {x : E} (hx : ‖x‖ = 1) {μ : 𝕜} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → μ' ≠ μ →
      δ ≤ |RCLike.re μ' - RCLike.re (inner 𝕜 (A x) x)|)
    (hclose : |RCLike.re μ - RCLike.re (inner 𝕜 (A x) x)| ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖) :
    |RCLike.re μ - RCLike.re (inner 𝕜 (A x) x)| ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / δ := by
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  by_cases hlt : |RCLike.re μ - θ| < δ
  · obtain ⟨hlt1, hlt2⟩ := abs_lt.mp hlt
    have hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' →
        RCLike.re μ' ∈ Set.Ioo (θ - δ) (θ + δ) → μ' = μ := by
      intro μ' h1 h2
      by_contra hne
      have hg := hgap μ' h1 hne
      obtain ⟨h21, h22⟩ := Set.mem_Ioo.mp h2
      have hcon : |RCLike.re μ' - θ| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    obtain ⟨h1, h2⟩ := hA.kato_temple hx ⟨by linarith, by linarith⟩
      (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) hunique
    rw [← hθ] at h1 h2
    rw [show θ + δ - θ = δ from by ring] at h1
    rw [show θ - (θ - δ) = δ from by ring] at h2
    exact abs_le.mpr ⟨by linarith, h2⟩
  · rw [not_lt] at hlt
    rw [le_div_iff₀ hδ]
    calc |RCLike.re μ - θ| * δ ≤ ‖A x - (θ : 𝕜) • x‖ * ‖A x - (θ : 𝕜) • x‖ :=
          mul_le_mul hclose (hlt.trans hclose) hδ.le (norm_nonneg _)
      _ = ‖A x - (θ : 𝕜) • x‖ ^ 2 := (sq _).symm

/-- **Bounds of the Rayleigh quotient.** Let $A$ be a symmetric operator on a finite-dimensional
inner product space, and suppose that every eigenvalue of $A$ has its real part in
$[\lambda_{\min}, \lambda_{\max}]$. Then for every $x \neq 0$,
$$\lambda_{\min} \le \frac{\operatorname{Re} \langle Ax, x \rangle}{\|x\|^2} \le
  \lambda_{\max}.$$
-/
theorem rayleigh_mem_Icc {lmin lmax : ℝ}
    (hspec : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax) {x : E}
    (hx : x ≠ 0) : RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax := by
  set n := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hbounds : ∀ i : Fin n, hA.eigenvalues hn i ∈ Set.Icc lmin lmax := by
    intro i
    have := hspec ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
    rwa [RCLike.ofReal_re] at this
  rw [Set.mem_Icc]
  constructor
  · rw [le_div_iff₀ hpos, hA.re_inner_apply_self_eq_sum hn, hA.norm_sq_eq_sum_norm_repr_sq hn,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hbounds i).1 (sq_nonneg _)
  · rw [div_le_iff₀ hpos, hA.re_inner_apply_self_eq_sum hn, hA.norm_sq_eq_sum_norm_repr_sq hn,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hbounds i).2 (sq_nonneg _)

/-!
### The residual bound for the eigenvector

A small residual forces the approximate eigenvector to be close to an eigenspace, if the
corresponding eigenvalue is separated from the rest of the spectrum.
-/

/-- **The residual bound for the eigenvector** ([saad2011numerical], Theorem 3.9). Let $A$ be a
symmetric operator on an inner product space of finite dimension $n$, with eigenvalues
$\lambda_i$ listed with multiplicity, and let $x$ be a unit vector with Rayleigh quotient
$\theta = \operatorname{Re} \langle Ax, x \rangle$ and residual $r = Ax - \theta x$. Let
$\lambda \in \mathbb{R}$ and $\delta > 0$, and suppose that $\delta \le |\lambda_i - \theta|$
for every $i$ with $\lambda_i \neq \lambda$. Then
$$\sin \angle(x, \ker(A - \lambda)) \le \frac{\|r\|}{\delta}.$$

The subspace is the eigenspace of $\lambda$, and not the line through one eigenvector for
$\lambda$. At a multiple eigenvalue the statement for a line is false: for
$A = \operatorname{diag}(1, 1, 5)$ and $x$ the second basis vector, $r = 0$ and $\delta = 4$,
but the angle between $x$ and the line through the first basis vector is a right angle. The
source takes $\delta$ to bound $A - \theta$ from below on the orthogonal complement of that
line, which holds only when $\lambda$ is a simple eigenvalue; the simple case is
`LinearMap.IsSymmetric.sin_angle_span_singleton_le_norm_residual_div`.

No hypothesis says that $\lambda$ is an eigenvalue. If it is not, the eigenspace is $\{0\}$, the
left side is $1$, and the separation holds at every index, so the bound still holds. The
eigenvalues are `LinearMap.IsSymmetric.eigenvalues`. The proof splits $x = p + q$ along the
eigenspace and its orthogonal complement. The residual splits as
$(\lambda - \theta) p + (A - \theta) q$, with orthogonal terms because both subspaces are
invariant, and the theorem of Pythagoras removes the term in $p$. -/
theorem sin_angle_le_norm_residual_div {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E}
    (hx : ‖x‖ = 1) {lam δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i, hA.eigenvalues hn i ≠ lam →
      δ ≤ |hA.eigenvalues hn i - RCLike.re (inner 𝕜 (A x) x)|) :
    (Module.End.eigenspace A (lam : 𝕜)).sinAngle x
      ≤ ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ / δ := by
  set W : Submodule 𝕜 E := Module.End.eigenspace A (lam : 𝕜) with hWdef
  set θ : ℝ := RCLike.re (inner 𝕜 (A x) x) with hθdef
  have hpmem : W.starProjection x ∈ W := W.starProjection_apply_mem x
  have hqmem : x - W.starProjection x ∈ Wᗮ := W.sub_starProjection_mem_orthogonal x
  have hAp : A (W.starProjection x) = (lam : 𝕜) • W.starProjection x :=
    Module.End.mem_eigenspace_iff.1 hpmem
  have hres : A (x - W.starProjection x) - (θ : 𝕜) • (x - W.starProjection x) ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hzero := (Submodule.mem_orthogonal W _).1 hqmem y hy
    have h1 : inner 𝕜 y (A (x - W.starProjection x)) = (0 : 𝕜) := by
      rw [← hA y _, Module.End.mem_eigenspace_iff.1 hy, inner_smul_left, RCLike.conj_ofReal,
        hzero, mul_zero]
    rw [inner_sub_right, inner_smul_right, h1, hzero, mul_zero, sub_zero]
  have hsplit : A x - (θ : 𝕜) • x
      = ((lam : 𝕜) - (θ : 𝕜)) • W.starProjection x
        + (A (x - W.starProjection x) - (θ : 𝕜) • (x - W.starProjection x)) := by
    rw [map_sub, hAp]
    module
  have hpyth : ‖A x - (θ : 𝕜) • x‖ ^ 2
      = ‖((lam : 𝕜) - (θ : 𝕜)) • W.starProjection x‖ ^ 2
        + ‖A (x - W.starProjection x) - (θ : 𝕜) • (x - W.starProjection x)‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_right_of_mem_orthogonal (Submodule.smul_mem _ _ hpmem) hres)
  have hlow := hA.mul_norm_le_norm_sub_smul hn hδ.le hsep hqmem
  have hle : δ * ‖x - W.starProjection x‖ ≤ ‖A x - (θ : 𝕜) • x‖ := by
    refine hlow.trans ?_
    nlinarith [hpyth, norm_nonneg (A x - (θ : 𝕜) • x),
      norm_nonneg (A (x - W.starProjection x) - (θ : 𝕜) • (x - W.starProjection x)),
      sq_nonneg (‖((lam : 𝕜) - (θ : 𝕜)) • W.starProjection x‖)]
  rw [le_div_iff₀ hδ]
  calc W.sinAngle x * δ = δ * (W.sinAngle x * ‖x‖) := by rw [hx]; ring
    _ = δ * ‖x - W.starProjection x‖ := by rw [Submodule.sinAngle_mul_norm]
    _ ≤ _ := hle

/-- **The residual bound for the eigenvector at a simple eigenvalue** ([saad2011numerical], Theorem
3.9, as printed). Let $A$, $x$, $\theta$, $r$, $\lambda$ and $\delta$ be as in
`LinearMap.IsSymmetric.sin_angle_le_norm_residual_div`. Let $u \neq 0$ satisfy $Au = \lambda u$,
and suppose that the eigenspace of $\lambda$ has dimension $1$. Then
$$\sin \angle(x, \operatorname{span}\{u\}) \le \frac{\|r\|}{\delta}.$$

The proof in the source needs the simplicity of $\lambda$ but does not state it. It takes
$\delta$ to bound $A - \theta$ from below on the orthogonal complement of $u$; at a multiple
eigenvalue that complement meets the eigenspace of $\lambda$, where $A - \theta$ is only
$\lambda - \theta$. -/
theorem sin_angle_span_singleton_le_norm_residual_div {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    {x : E} (hx : ‖x‖ = 1) {lam δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i, hA.eigenvalues hn i ≠ lam →
      δ ≤ |hA.eigenvalues hn i - RCLike.re (inner 𝕜 (A x) x)|)
    {u : E} (hu : A u = (lam : 𝕜) • u) (hu0 : u ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.eigenspace A (lam : 𝕜)) = 1) :
    (𝕜 ∙ u).sinAngle x ≤ ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ / δ := by
  have hle : (𝕜 ∙ u) ≤ Module.End.eigenspace A (lam : 𝕜) :=
    (Submodule.span_singleton_le_iff_mem _ _).2 (Module.End.mem_eigenspace_iff.2 hu)
  have heq : (𝕜 ∙ u) = Module.End.eigenspace A (lam : 𝕜) :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hsimple, finrank_span_singleton hu0])
  rw [Submodule.sinAngle_congr heq]
  exact hA.sin_angle_le_norm_residual_div hn hx hδ hsep

end LinearMap.IsSymmetric

/-- **Backward error of an approximate eigenpair** ([saad2011numerical], Proposition 3.4). Let $A$
be a bounded operator on an inner product space, let $u$ be a unit vector and let $\theta$ be a
scalar. Then the least norm $\|\Delta A\|$ of a bounded operator $\Delta A$ with
$(A - \Delta A) u = \theta u$ is $\|Au - \theta u\|$.

The least value is attained by the rank-one operator $r u^H$, built from the residual
$r = Au - \theta u$. -/
theorem isLeast_eigen_backwardError (A : E →L[𝕜] E) {u : E} (hu : ‖u‖ = 1) (θ : 𝕜) :
    IsLeast {ε : ℝ | ∃ ΔA : E →L[𝕜] E, (A - ΔA) u = θ • u ∧ ‖ΔA‖ = ε} ‖A u - θ • u‖ := by
  have huu : inner 𝕜 u u = (1 : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  constructor
  · refine ⟨InnerProductSpace.rankOne 𝕜 (A u - θ • u) u, ?_, ?_⟩
    · have hr : (InnerProductSpace.rankOne 𝕜 (A u - θ • u) u) u = A u - θ • u := by
        rw [InnerProductSpace.rankOne_apply, huu, one_smul]
      rw [sub_apply, hr, sub_sub_cancel]
    · rw [InnerProductSpace.norm_rankOne, hu, mul_one]
  · rintro ε ⟨ΔA, hΔ, rfl⟩
    have hval : ΔA u = A u - θ • u := by
      rw [sub_apply, sub_eq_iff_eq_add] at hΔ
      rw [hΔ]; abel
    calc ‖A u - θ • u‖ = ‖ΔA u‖ := by rw [hval]
      _ ≤ ‖ΔA‖ * ‖u‖ := ΔA.le_opNorm u
      _ = ‖ΔA‖ := by rw [hu, mul_one]

/-- **Bendixson's theorem** ([saad2003iterative], Theorem 1.35). Let $A$ and $H$ be linear operators
on an inner product space, and suppose that $H$ is symmetric with $\lambda_{\min} \|x\|^2 \le
\operatorname{Re} \langle Hx, x \rangle \le \lambda_{\max} \|x\|^2$ for all $x$, and that
$\operatorname{Re} \langle Hx, x \rangle = \operatorname{Re} \langle Ax, x \rangle$ for all $x$.
Then every eigenvalue $\mu$ of $A$ satisfies $\lambda_{\min} \le \operatorname{Re} \mu \le
\lambda_{\max}$.

The intended $H$ is the symmetric part $(A + A^*)/2$ of $A$, with $\lambda_{\min}$ and
$\lambda_{\max}$ its extreme eigenvalues. The bounds on $H$ are
`LinearMap.IsSymmetricBoundedBy`, and no finite dimension is needed. -/
theorem re_hasEigenvalue_mem_Icc_of_symmetricPart {A H : E →ₗ[𝕜] E} {lmin lmax : ℝ}
    (hH : H.IsSymmetricBoundedBy lmin lmax)
    (hHA : ∀ x, RCLike.re (inner 𝕜 (H x) x) = RCLike.re (inner 𝕜 (A x) x)) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) : RCLike.re μ ∈ Set.Icc lmin lmax := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hAv : A v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
  have hkey : RCLike.re (inner 𝕜 (A v) v) = RCLike.re μ * ‖v‖ ^ 2 := by
    rw [hAv, inner_smul_left, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.mul_re]
    simp
  have h1 := hH.le_re_inner v
  have h2 := hH.re_inner_le v
  rw [hHA v, hkey] at h1 h2
  exact ⟨le_of_mul_le_mul_right (by linarith) hpos,
    le_of_mul_le_mul_right (by linarith) hpos⟩

/-!
### The condition number of a simple eigenvalue

The sensitivity of a simple eigenvalue is measured by $\|u\| \|w\| / |\langle w, u \rangle|$ for a
right eigenvector $u$ and a left eigenvector $w$, that is, by the reciprocal cosine of the angle
between them ([saad2011numerical], Definition 3.1). The quantity does not change when $u$ or $w$ is
scaled, so it depends only on the eigenvalue when the eigenvalue is simple, because its two
eigenvectors are then determined up to scale.
-/

/-- The **condition number of a simple eigenvalue** ([saad2011numerical], Definition 3.1) with right
eigenvector $u$ and left eigenvector $w$ is
$$\kappa(u, w) = \frac{\|u\| \|w\|}{|\langle w, u \rangle|} = \frac{1}{\cos \angle(u, w)}.$$
If $\langle w, u \rangle = 0$, the value is $0$.

The definition mentions neither the operator nor the eigenvalue. It does not change when $u$ or
$w$ is scaled (`Module.End.eigenvalueCondNumber_smul`), so at a simple eigenvalue, where each of
the two eigenvectors spans a line, it depends only on the eigenvalue. Because of the value $0$
at $\langle w, u \rangle = 0$, `Module.End.one_le_eigenvalueCondNumber` assumes
$\langle w, u \rangle \neq 0$; at an algebraically simple eigenvalue this holds by
`Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one`. -/
noncomputable def Module.End.eigenvalueCondNumber (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (u w : E) : ℝ :=
  ‖u‖ * ‖w‖ / ‖(inner 𝕜 w u : 𝕜)‖

namespace Module.End

/-- For nonzero scalars $a$ and $b$, $\kappa(au, bw) = \kappa(u, w)$: the condition number of a
simple eigenvalue does not depend on the choice of the eigenvectors. -/
theorem eigenvalueCondNumber_smul {u w : E} {a b : 𝕜} (ha : a ≠ 0) (hb : b ≠ 0) :
    eigenvalueCondNumber 𝕜 (a • u) (b • w) = eigenvalueCondNumber 𝕜 u w := by
  have hi : ‖(inner 𝕜 (b • w) (a • u) : 𝕜)‖ = ‖b‖ * ‖a‖ * ‖(inner 𝕜 w u : 𝕜)‖ := by
    rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj]
    ring
  have hane : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hbne : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb
  rcases eq_or_ne (inner 𝕜 w u : 𝕜) 0 with h | h
  · simp [eigenvalueCondNumber, hi, h]
  · have hne : ‖(inner 𝕜 w u : 𝕜)‖ ≠ 0 := norm_ne_zero_iff.2 h
    rw [eigenvalueCondNumber, eigenvalueCondNumber, hi, norm_smul, norm_smul]
    field_simp

/-- If $\langle w, u \rangle \neq 0$, then $\kappa(u, w) \ge 1$, by the Cauchy–Schwarz inequality.
-/
theorem one_le_eigenvalueCondNumber {u w : E} (h : (inner 𝕜 w u : 𝕜) ≠ 0) :
    1 ≤ eigenvalueCondNumber 𝕜 u w := by
  rw [eigenvalueCondNumber, le_div_iff₀ (norm_pos_iff.2 h), one_mul, mul_comm]
  exact norm_inner_le_norm w u

/-- A **normal** operator is perfectly conditioned at every simple eigenvalue. Let $A$ be a normal
operator on a finite-dimensional inner product space, let $Au = \mu u$ with $u \neq 0$, let
$A^* w = \bar{\mu} w$ with $w \neq 0$, and suppose that the eigenspace of $\mu$ has dimension
$1$. Then $\kappa(u, w) = 1$.

The left and the right eigenvectors span the same line
(`LinearMap.IsStarNormal.eigenspace_adjoint`), so the angle between them is zero. -/
theorem eigenvalueCondNumber_eq_one_of_isStarNormal [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : IsStarNormal A) {μ : 𝕜} {u w : E} (hu : A u = μ • u) (hu0 : u ≠ 0)
    (hw : A.adjoint w = (starRingEnd 𝕜) μ • w) (hw0 : w ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.eigenspace A μ) = 1) :
    eigenvalueCondNumber 𝕜 u w = 1 := by
  have hwmem : w ∈ Module.End.eigenspace A μ := by
    rw [← LinearMap.IsStarNormal.eigenspace_adjoint hA μ]
    exact Module.End.mem_eigenspace_iff.2 hw
  have hle : (𝕜 ∙ u) ≤ Module.End.eigenspace A μ :=
    (Submodule.span_singleton_le_iff_mem _ _).2 (Module.End.mem_eigenspace_iff.2 hu)
  have heq : (𝕜 ∙ u) = Module.End.eigenspace A μ :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hsimple, finrank_span_singleton hu0])
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (heq ▸ hwmem)
  have hc : c ≠ 0 := by
    rintro rfl
    exact hw0 (by simp)
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  rw [eigenvalueCondNumber, inner_smul_left, norm_smul, norm_mul, RCLike.norm_conj,
    inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg u)]
  field_simp

/-! ### Left eigenvectors -/

/-- A vector $w$ is a **left eigenvector** of $A$ for the scalar $\lambda$ if $\langle w, Ay
\rangle = \lambda \langle w, y \rangle$ for every $y$.

Where the adjoint exists, this says $A^* w = \bar{\lambda} w$. The definition does not use the
adjoint, so it needs neither completeness nor finite dimension. The vector $w = 0$ is allowed;
the results that need $w \neq 0$ assume it separately. -/
def IsLeftEigenvector (A : E →ₗ[𝕜] E) (l : 𝕜) (w : E) : Prop :=
  ∀ y, (inner 𝕜 w (A y) : 𝕜) = l * inner 𝕜 w y

/-- $w$ is a left eigenvector of $A$ for $\lambda$ if and only if $\langle w, Ay \rangle = \lambda
\langle w, y \rangle$ for every $y$. -/
theorem isLeftEigenvector_iff {A : E →ₗ[𝕜] E} {l : 𝕜} {w : E} :
    IsLeftEigenvector A l w ↔ ∀ y, (inner 𝕜 w (A y) : 𝕜) = l * inner 𝕜 w y :=
  Iff.rfl

/-- If $w$ is a left eigenvector of $A$ for $\lambda$, then $\langle w, Ay \rangle = \lambda \langle
w, y \rangle$ for every vector $y$. -/
theorem IsLeftEigenvector.inner_apply {A : E →ₗ[𝕜] E} {l : 𝕜} {w : E}
    (h : IsLeftEigenvector A l w) (y : E) : (inner 𝕜 w (A y) : 𝕜) = l * inner 𝕜 w y :=
  h y

/-!
### First-order perturbation of a simple eigenvalue

Along a differentiable branch of eigenpairs of $A + tB$ the eigenvalue moves at the rate
$\langle w, Bu \rangle / \langle w, u \rangle$, whose modulus is at most $\|B\|$ times the condition
number of the eigenvalue. [saad2011numerical], §3.2.1 displays this computation. The branch is
assumed here, and it is constructed in `Module.End.hasDerivAt_eigenvalue_perturbation`, whose
hypotheses are the same relations together with the simplicity of the eigenvalue.
-/

/-- **The derivative of a simple eigenvalue** ([saad2011numerical], §3.2.1). Let $A$ and $B$ be
bounded operators on an inner product space $E$ over $\mathbb{K}$. Let $u : \mathbb{K} \to E$
and $\mu : \mathbb{K} \to \mathbb{K}$ have the derivatives $u'$ and $\mu'$ at $0$, and suppose
that $A u(t) + t B u(t) = \mu(t) u(t)$ for all $t$ near $0$. Let $w$ be a left eigenvector of
$A$ for $\lambda = \mu(0)$ with $\langle w, u(0) \rangle \neq 0$. Then
$$\mu' = \frac{\langle w, B u(0) \rangle}{\langle w, u(0) \rangle}.$$

The left eigenvector is `Module.End.IsLeftEigenvector`; in finite dimension this is
$A^* w = \bar{\lambda} w$. The branch is supplied by
`Module.End.hasDerivAt_eigenvalue_perturbation`. The derivative at $t = 0$ of the eigenvalue
equation is $A u' + B u(0) = \mu(0) u' + \mu' u(0)$, and the inner product with $w$ removes the
two terms that contain the unknown $u'$. -/
theorem deriv_eigenvalue_perturbation {A B : E →L[𝕜] E} {u : 𝕜 → E}
    {mu : 𝕜 → 𝕜} {u' : E} {mu' lam : 𝕜} {w : E}
    (hu : HasDerivAt u u' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ᶠ t in nhds 0, A (u t) + t • B (u t) = mu t • u t)
    (hw : IsLeftEigenvector (A : E →ₗ[𝕜] E) lam w) (hlam : mu 0 = lam)
    (hne : (inner 𝕜 w (u 0) : 𝕜) ≠ 0) :
    mu' = inner 𝕜 w (B (u 0)) / inner 𝕜 w (u 0) := by
  have hw' (y : E) : (inner 𝕜 w (A y) : 𝕜) = lam * inner 𝕜 w y := hw.inner_apply y
  have h1 : HasDerivAt (fun t : 𝕜 => A (u t)) (A u') 0 := by
    simpa [Function.comp_def] using A.hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hu
  have h2 : HasDerivAt (fun t : 𝕜 => B (u t)) (B u') 0 := by
    simpa [Function.comp_def] using B.hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hu
  have hid : HasDerivAt (fun t : 𝕜 => t) 1 0 := hasDerivAt_id 0
  have h3 : HasDerivAt (fun t : 𝕜 => t • B (u t)) (B (u 0)) 0 := by
    have h := HasDerivAt.smul hid h2
    rw [zero_smul, one_smul, zero_add] at h
    exact h
  have hf : HasDerivAt (fun t : 𝕜 => mu t • u t) (A u' + B (u 0)) 0 :=
    HasDerivAt.congr_of_eventuallyEq (HasDerivAt.add h1 h3)
      (heig.mono fun t ht => ht.symm)
  have hderiv : A u' + B (u 0) = mu 0 • u' + mu' • u 0 :=
    hf.unique (HasDerivAt.smul hmu hu)
  have htest := congrArg (fun y : E => (inner 𝕜 w y : 𝕜)) hderiv
  simp only [inner_add_right, inner_smul_right, hw' u', hlam] at htest
  have hmul : (inner 𝕜 w (B (u 0)) : 𝕜) = mu' * inner 𝕜 w (u 0) := by
    linear_combination htest
  rw [hmul, mul_div_assoc, div_self hne, mul_one]

/-- **The condition number bounds the first-order sensitivity** ([saad2011numerical], §3.2.1). Under
the hypotheses of `Module.End.deriv_eigenvalue_perturbation`, the derivative of the eigenvalue
satisfies
$$|\mu'| \le \|B\| \, \kappa(u(0), w).$$

No normalization of $u(0)$ or of $w$ is needed, because both sides do not change when these
vectors are scaled. -/
theorem norm_deriv_eigenvalue_perturbation_le {A B : E →L[𝕜] E} {u : 𝕜 → E}
    {mu : 𝕜 → 𝕜} {u' : E} {mu' lam : 𝕜} {w : E}
    (hu : HasDerivAt u u' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ᶠ t in nhds 0, A (u t) + t • B (u t) = mu t • u t)
    (hw : IsLeftEigenvector (A : E →ₗ[𝕜] E) lam w) (hlam : mu 0 = lam)
    (hne : (inner 𝕜 w (u 0) : 𝕜) ≠ 0) :
    ‖mu'‖ ≤ ‖B‖ * eigenvalueCondNumber 𝕜 (u 0) w := by
  have hnum : ‖(inner 𝕜 w (B (u 0)) : 𝕜)‖ ≤ ‖B‖ * (‖u 0‖ * ‖w‖) := by
    calc ‖(inner 𝕜 w (B (u 0)) : 𝕜)‖ ≤ ‖w‖ * ‖B (u 0)‖ := norm_inner_le_norm w (B (u 0))
      _ ≤ ‖w‖ * (‖B‖ * ‖u 0‖) := by
          gcongr
          exact B.le_opNorm (u 0)
      _ = ‖B‖ * (‖u 0‖ * ‖w‖) := by ring
  rw [deriv_eigenvalue_perturbation hu hmu heig hw hlam hne, norm_div, eigenvalueCondNumber]
  calc ‖(inner 𝕜 w (B (u 0)) : 𝕜)‖ / ‖(inner 𝕜 w (u 0) : 𝕜)‖
      ≤ (‖B‖ * (‖u 0‖ * ‖w‖)) / ‖(inner 𝕜 w (u 0) : 𝕜)‖ := by gcongr
    _ = ‖B‖ * (‖u 0‖ * ‖w‖ / ‖(inner 𝕜 w (u 0) : 𝕜)‖) := by ring

/-- **A simple eigenvalue moves differentiably** ([saad2011numerical], §3.2.1). Let $A$ and $B$ be
bounded operators on a finite-dimensional inner product space $E$ over $\mathbb{K}$. Let
$Au = \lambda u$, let $w$ be a left eigenvector of $A$ for $\lambda$ with
$\langle w, u \rangle \neq 0$, and suppose that every $z$ with $Az = \lambda z$ is a scalar
multiple of $u$. Then there are functions $\mu : \mathbb{K} \to \mathbb{K}$ and
$v : \mathbb{K} \to E$ and a vector $v'$ such that
* $\mu(0) = \lambda$ and $v(0) = u$;
* $A v(t) + t B v(t) = \mu(t) v(t)$ for all $t$ near $0$;
* $v$ has the derivative $v'$ at $0$;
* $\mu$ has the derivative $\langle w, Bu \rangle / \langle w, u \rangle$ at $0$.

This is the branch that `Module.End.deriv_eigenvalue_perturbation` assumes. It comes from the
inverse function theorem, without the implicit function theorem and without a determinant. The
map $F(t, \mu, z) = (t, \langle w, z \rangle, Az + tBz - \mu z)$ on
$\mathbb{K} \times \mathbb{K} \times E$ is polynomial, so its strict derivative at
$(0, \lambda, u)$ is immediate. That derivative is injective because the eigenvalue is simple:
the inner product of $(A - \lambda) \delta z = \delta\mu \, u$ with $w$ gives $\delta\mu = 0$,
then simplicity puts $\delta z$ in $\operatorname{span}\{u\}$, and
$\langle w, \delta z \rangle = 0$ gives $\delta z = 0$. In finite dimension the derivative is
then bijective, $F$ has a local inverse $g$, and the branch is
$t \mapsto g(t, \langle w, u \rangle, 0)$. The second component $\rho$ of $F'^{-1}(1, 0, 0)$
satisfies $\rho \langle w, u \rangle = \langle w, Bu \rangle$, which gives the derivative of the
eigenvalue. The constructed branch has the normalization
$\langle w, v(t) \rangle = \langle w, u \rangle$, which makes it unique; this normalization is
not part of the statement. -/
theorem hasDerivAt_eigenvalue_perturbation [FiniteDimensional 𝕜 E] {A B : E →L[𝕜] E} {l : 𝕜}
    {u w : E} (hAu : A u = l • u) (hw : IsLeftEigenvector (A : E →ₗ[𝕜] E) l w)
    (hne : (inner 𝕜 w u : 𝕜) ≠ 0)
    (hsimple : ∀ z : E, A z = l • z → ∃ c : 𝕜, z = c • u) :
    ∃ (mu : 𝕜 → 𝕜) (v : 𝕜 → E) (v' : E), mu 0 = l ∧ v 0 = u ∧
      (∀ᶠ t in nhds (0 : 𝕜), A (v t) + t • B (v t) = mu t • v t) ∧
      HasDerivAt v v' 0 ∧
      HasDerivAt mu (inner 𝕜 w (B u) / inner 𝕜 w u) 0 := by
  classical
  have hw' (y : E) : (inner 𝕜 w (A y) : 𝕜) = l * inner 𝕜 w y := hw.inner_apply y
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set π₁ : (𝕜 × 𝕜 × E) →L[𝕜] 𝕜 := ContinuousLinearMap.fst 𝕜 𝕜 (𝕜 × E) with hπ₁
  set π₂ : (𝕜 × 𝕜 × E) →L[𝕜] 𝕜 :=
    (ContinuousLinearMap.fst 𝕜 𝕜 E).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × E)) with hπ₂
  set π₃ : (𝕜 × 𝕜 × E) →L[𝕜] E :=
    (ContinuousLinearMap.snd 𝕜 𝕜 E).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × E)) with hπ₃
  have hx1 : ∀ x : 𝕜 × 𝕜 × E, π₁ x = x.1 := fun _ => rfl
  have hx2 : ∀ x : 𝕜 × 𝕜 × E, π₂ x = x.2.1 := fun _ => rfl
  have hx3 : ∀ x : 𝕜 × 𝕜 × E, π₃ x = x.2.2 := fun _ => rfl
  set p : 𝕜 × 𝕜 × E := (0, l, u) with hp
  have hp1 : p.1 = (0 : 𝕜) := rfl
  have hp2 : p.2.1 = l := rfl
  have hp3 : p.2.2 = u := rfl
  set F : (𝕜 × 𝕜 × E) → (𝕜 × 𝕜 × E) := fun x =>
    (x.1, (inner 𝕜 w x.2.2 : 𝕜), A x.2.2 + x.1 • B x.2.2 - x.2.1 • x.2.2) with hF
  set D : (𝕜 × 𝕜 × E) →L[𝕜] (𝕜 × 𝕜 × E) :=
    π₁.prod (((innerSL 𝕜 w).comp π₃).prod
      (A.comp π₃ - l • π₃ - π₂.smulRight u + π₁.smulRight (B u))) with hD
  have hDapply : ∀ x : 𝕜 × 𝕜 × E, D x =
      (x.1, (inner 𝕜 w x.2.2 : 𝕜), A x.2.2 - l • x.2.2 - x.2.1 • u + x.1 • B u) := by
    intro x
    simp [hD, hπ₁, hπ₂, hπ₃]
  -- `D` is the strict derivative of `F` at `p`.
  have hFD : HasStrictFDerivAt F D p := by
    have h1 : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => x.1) π₁ p := π₁.hasStrictFDerivAt
    have h2 : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => x.2.1) π₂ p := π₂.hasStrictFDerivAt
    have h3 : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => x.2.2) π₃ p := π₃.hasStrictFDerivAt
    have hAc : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => A x.2.2) (A.comp π₃) p :=
      (A.comp π₃).hasStrictFDerivAt
    have hin : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => (inner 𝕜 w x.2.2 : 𝕜))
        ((innerSL 𝕜 w).comp π₃) p := ((innerSL 𝕜 w).comp π₃).hasStrictFDerivAt
    have hBc : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => B x.2.2) (B.comp π₃) p :=
      (B.comp π₃).hasStrictFDerivAt
    have hsum := (hAc.add (h1.smul hBc)).sub (h2.smul h3)
    refine (h1.prodMk (hin.prodMk hsum)).congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
    rw [hDapply]
    simp only [ContinuousLinearMap.prod_apply, add_apply, sub_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, hx1, hx2, hx3, hp1, hp2, hp3, zero_smul, zero_add]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    abel_nf
  -- `D` is injective, hence an equivalence.
  have hDker : ∀ x : 𝕜 × 𝕜 × E, D x = 0 → x = 0 := by
    intro x hx
    rw [hDapply] at hx
    have e1 : x.1 = 0 := by simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.1) hx
    have e2 : (inner 𝕜 w x.2.2 : 𝕜) = 0 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.1) hx
    have e3 : A x.2.2 - l • x.2.2 - x.2.1 • u + x.1 • B u = 0 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.2) hx
    rw [e1, zero_smul, add_zero, sub_eq_zero] at e3
    have e5 : (inner 𝕜 w (A x.2.2 - l • x.2.2) : 𝕜) = inner 𝕜 w (x.2.1 • u) := by rw [e3]
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hw', e2] at e5
    have e6 : x.2.1 = 0 := by
      have hz : x.2.1 * (inner 𝕜 w u : 𝕜) = 0 := by rw [← e5]; ring
      rcases mul_eq_zero.1 hz with h | h
      · exact h
      · exact absurd h hne
    rw [e6, zero_smul, sub_eq_zero] at e3
    obtain ⟨c, hc⟩ := hsimple x.2.2 e3
    have e7 : c = 0 := by
      rw [hc, inner_smul_right] at e2
      rcases mul_eq_zero.1 e2 with h | h
      · exact h
      · exact absurd h hne
    have e8 : x.2.2 = 0 := by rw [hc, e7, zero_smul]
    exact Prod.ext e1 (Prod.ext e6 e8)
  have hDinj : Function.Injective D := by
    intro x y hxy
    have hz : D (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzz := hDker _ hz
    rwa [sub_eq_zero] at hzz
  have hDbij : Function.Bijective D :=
    ⟨hDinj, LinearMap.injective_iff_surjective.1 hDinj⟩
  set D' : (𝕜 × 𝕜 × E) ≃L[𝕜] (𝕜 × 𝕜 × E) :=
    (LinearEquiv.ofBijective (D : (𝕜 × 𝕜 × E) →ₗ[𝕜] (𝕜 × 𝕜 × E)) hDbij).toContinuousLinearEquiv
      with hD'
  have hD'coe : (D' : (𝕜 × 𝕜 × E) →L[𝕜] (𝕜 × 𝕜 × E)) = D :=
    ContinuousLinearMap.ext fun _ => rfl
  rw [← hD'coe] at hFD
  set g : (𝕜 × 𝕜 × E) → (𝕜 × 𝕜 × E) := hFD.localInverse F D' p with hg
  have hFp : F p = (0, (inner 𝕜 w u : 𝕜), 0) := by
    simp [hF, hp, hAu]
  have hgp : g (0, (inner 𝕜 w u : 𝕜), 0) = p := by
    rw [hg, ← hFp]; exact hFD.localInverse_apply_image
  have hev : ∀ᶠ y in nhds (F p), F (g y) = y := hFD.eventually_right_inverse
  have hkderiv : HasDerivAt (fun t : 𝕜 => (t, (inner 𝕜 w u : 𝕜), (0 : E)))
      ((1 : 𝕜), (0 : 𝕜), (0 : E)) 0 :=
    HasDerivAt.prodMk (hasDerivAt_id' (0 : 𝕜))
      (HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_const _ _))
  have hkcont : Filter.Tendsto (fun t : 𝕜 => (t, (inner 𝕜 w u : 𝕜), (0 : E)))
      (nhds 0) (nhds (F p)) := by
    rw [hFp]
    exact hkderiv.continuousAt
  have hevt : ∀ᶠ t in nhds (0 : 𝕜),
      F (g (t, (inner 𝕜 w u : 𝕜), 0)) = (t, (inner 𝕜 w u : 𝕜), 0) := hkcont.eventually hev
  have hgd : HasStrictFDerivAt g (D'.symm : (𝕜 × 𝕜 × E) →L[𝕜] (𝕜 × 𝕜 × E)) (F p) :=
    hFD.to_localInverse
  have hgd' : HasFDerivAt g (D'.symm : (𝕜 × 𝕜 × E) →L[𝕜] (𝕜 × 𝕜 × E))
      ((0 : 𝕜), (inner 𝕜 w u : 𝕜), (0 : E)) := by
    rw [hFp] at hgd; exact hgd.hasFDerivAt
  have hcomp : HasDerivAt (fun t : 𝕜 => g (t, (inner 𝕜 w u : 𝕜), 0))
      (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))) 0 := by
    have := hgd'.comp_hasDerivAt (0 : 𝕜) hkderiv
    simpa [Function.comp_def] using this
  -- the second component of `D'.symm (1, 0, 0)` is Saad's derivative
  have hsymm : D (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))) = ((1 : 𝕜), (0 : 𝕜), (0 : E)) := by
    rw [← hD'coe, ContinuousLinearEquiv.coe_coe, D'.apply_symm_apply]
  have hr : (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.1 = inner 𝕜 w (B u) / inner 𝕜 w u := by
    rw [hDapply] at hsymm
    have f1 : (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).1 = 1 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.1) hsymm
    have f2 : (inner 𝕜 w (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.2 : 𝕜) = 0 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.1) hsymm
    have f3 : A (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.2
        - l • (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.2
        - (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.1 • u
        + (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).1 • B u = 0 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.2) hsymm
    rw [f1, one_smul] at f3
    have f4 := congrArg (fun y : E => (inner 𝕜 w y : 𝕜)) f3
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hw', f2, inner_zero_right] at f4
    have f5 : (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.1 * (inner 𝕜 w u : 𝕜)
        = inner 𝕜 w (B u) := by linear_combination -f4
    rw [eq_div_iff hne]
    exact f5
  refine ⟨fun t => (g (t, (inner 𝕜 w u : 𝕜), 0)).2.1,
    fun t => (g (t, (inner 𝕜 w u : 𝕜), 0)).2.2,
    (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.2, ?_, ?_, ?_, ?_, ?_⟩
  · change (g ((0 : 𝕜), (inner 𝕜 w u : 𝕜), (0 : E))).2.1 = l
    rw [hgp]
  · change (g ((0 : 𝕜), (inner 𝕜 w u : 𝕜), (0 : E))).2.2 = u
    rw [hgp]
  · filter_upwards [hevt] with t ht
    have c1 : (g (t, (inner 𝕜 w u : 𝕜), 0)).1 = t := by
      simpa [hF] using congrArg (fun z : 𝕜 × 𝕜 × E => z.1) ht
    have c3 : A (g (t, (inner 𝕜 w u : 𝕜), 0)).2.2
        + (g (t, (inner 𝕜 w u : 𝕜), 0)).1 • B (g (t, (inner 𝕜 w u : 𝕜), 0)).2.2
        - (g (t, (inner 𝕜 w u : 𝕜), 0)).2.1 • (g (t, (inner 𝕜 w u : 𝕜), 0)).2.2 = 0 := by
      simpa [hF] using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.2) ht
    rw [c1, sub_eq_zero] at c3
    exact c3
  · have := (π₃.hasFDerivAt).comp_hasDerivAt (0 : 𝕜) hcomp
    simpa [Function.comp_def, hx3] using this
  · rw [← hr]
    have := (π₂.hasFDerivAt).comp_hasDerivAt (0 : 𝕜) hcomp
    simpa [Function.comp_def, hx2] using this

end Module.End

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **Bauer–Fike theorem** ([saad2011numerical], Theorem 3.6; [kress1998numerical], Problem
7.6). Let $X \in \mathbb{C}^{n \times n}$ be invertible, let $d \in \mathbb{C}^n$, and let
$A = X \operatorname{diag}(d) X^{-1}$. If $\mu$ is an eigenvalue of $A + \Delta A$, then for
some $i$
$$|\mu - d_i| \le \kappa_2(X) \|\Delta A\|_2,$$
where $\kappa_2(X) = \|X\|_2 \|X^{-1}\|_2$.

The norm is the operator norm induced by the Euclidean norm, and $\kappa_2(X)$ is
`NormedRing.condNumber X`. -/
theorem bauer_fike (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X) (ΔA : Matrix n n ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (X * Matrix.diagonal d * X⁻¹ + ΔA)) :
    ∃ i, ‖μ - d i‖ ≤ NormedRing.condNumber X * ‖ΔA‖ := by
  classical
  have hcond : NormedRing.condNumber X * ‖ΔA‖ = ‖X‖ * ‖X⁻¹‖ * ‖ΔA‖ := by
    rw [NormedRing.condNumber, Matrix.nonsing_inv_eq_ringInverse]
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨v, hv, hv0⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  have hveq : (X * Matrix.diagonal d * X⁻¹ + ΔA) *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.mp hv
    rwa [Matrix.toLin'_apply] at h
  have hne : Nonempty n := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    exact hv0 (Subsingleton.elim v 0)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ‖μ - d i‖)
    ⟨Classical.arbitrary n, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  rw [hcond]
  by_cases hz : μ - d i₀ = 0
  · rw [hz, norm_zero]; positivity
  have hδ : 0 < ‖μ - d i₀‖ := norm_pos_iff.mpr hz
  have hne0 : ∀ i, μ - d i ≠ 0 := fun i hi => by
    have h := hi₀ i (Finset.mem_univ i)
    rw [hi, norm_zero] at h
    exact hz (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  set N : Matrix n n ℂ := Matrix.diagonal (fun i => μ - d i) with hN
  set Ninv : Matrix n n ℂ := Matrix.diagonal (fun i => (μ - d i)⁻¹) with hNinv
  have hNN : Ninv * N = 1 := by
    rw [hNinv, hN, Matrix.diagonal_mul_diagonal,
      show (fun i => (μ - d i)⁻¹ * (μ - d i)) = (1 : n → ℂ) from
        funext fun i => inv_mul_cancel₀ (hne0 i)]
    simp
  have hXd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX
  have hXinvX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hXd
  set w := X⁻¹ *ᵥ v with hw
  have hvw : X *ᵥ w = v := by rw [hw, Matrix.mulVec_nonsing_inv_mulVec hX]
  have hw0 : w ≠ 0 := fun h => hv0 (by rw [← hvw, h, Matrix.mulVec_zero])
  have key : N *ᵥ w = (X⁻¹ * ΔA * X) *ᵥ w := by
    have e1 : (X⁻¹ * ΔA * X) *ᵥ w = X⁻¹ *ᵥ (ΔA *ᵥ v) := by
      rw [← hvw, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e2 : ΔA *ᵥ v = μ • v - (X * Matrix.diagonal d * X⁻¹) *ᵥ v := by
      rw [← hveq, Matrix.add_mulVec]; abel
    have e3 : X⁻¹ *ᵥ ((X * Matrix.diagonal d * X⁻¹) *ᵥ v) = Matrix.diagonal d *ᵥ w := by
      rw [Matrix.mulVec_mulVec, show X⁻¹ * (X * Matrix.diagonal d * X⁻¹)
          = Matrix.diagonal d * X⁻¹ by rw [← mul_assoc, ← mul_assoc, hXinvX, one_mul],
        ← Matrix.mulVec_mulVec]
    rw [e1, e2, Matrix.mulVec_sub, Matrix.mulVec_smul, e3, ← hw, hN]
    funext i
    simp [Matrix.mulVec_diagonal, sub_mul]
  set u : EuclideanSpace ℂ n := WithLp.toLp 2 w with hu
  have hu0 : u ≠ 0 := fun h => hw0 (by simpa [hu] using congrArg WithLp.ofLp h)
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hid : Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv (Matrix.toEuclideanCLM (𝕜 := ℂ) N u) = u := by
    have hmap : Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv * Matrix.toEuclideanCLM (𝕜 := ℂ) N = 1 := by
      rw [← map_mul, hNN, map_one]
    calc Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv (Matrix.toEuclideanCLM (𝕜 := ℂ) N u)
        = (Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv * Matrix.toEuclideanCLM (𝕜 := ℂ) N) u := rfl
      _ = u := by rw [hmap]; rfl
  have hkey2 : Matrix.toEuclideanCLM (𝕜 := ℂ) N u
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u := by
    rw [hu, Matrix.toEuclideanCLM_toLp, Matrix.toEuclideanCLM_toLp, key]
  have hbound : ‖u‖ ≤ ‖Ninv‖ * (‖X⁻¹ * ΔA * X‖ * ‖u‖) := by
    calc ‖u‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u)‖ := by rw [← hkey2, hid]
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv‖ *
            ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Ninv‖ * (‖X⁻¹ * ΔA * X‖ * ‖u‖) := by
          rw [Matrix.l2_opNorm_toEuclideanCLM]
          exact mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
  have hNinvle : ‖Ninv‖ ≤ ‖μ - d i₀‖⁻¹ := by
    rw [hNinv, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [norm_inv]
    gcongr
    exact hi₀ i (Finset.mem_univ i)
  have hmul : ‖X⁻¹ * ΔA * X‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have h1 : 1 ≤ ‖Ninv‖ * ‖X⁻¹ * ΔA * X‖ := by nlinarith [hbound, hupos]
  have h2 : 1 ≤ ‖μ - d i₀‖⁻¹ * (‖X⁻¹‖ * ‖ΔA‖ * ‖X‖) :=
    h1.trans (mul_le_mul hNinvle hmul (norm_nonneg _) (by positivity))
  have h3 : ‖μ - d i₀‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ := by
    have h4 := mul_le_mul_of_nonneg_left h2 hδ.le
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at h4
  calc ‖μ - d i₀‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ := h3
    _ = ‖X‖ * ‖X⁻¹‖ * ‖ΔA‖ := by ring

/-- **The Bauer–Fike theorem in residual form.** Let $X \in \mathbb{C}^{n \times n}$ be invertible,
let $d \in \mathbb{C}^n$, and let $A = X \operatorname{diag}(d) X^{-1}$. For every unit vector
$u \in \mathbb{C}^n$ and every $\theta \in \mathbb{C}$ there is an index $i$ with
$$|\theta - d_i| \le \kappa_2(X) \|Au - \theta u\|,$$
where $\kappa_2(X) = \|X\|_2 \|X^{-1}\|_2$.

The vector $u$ is in `EuclideanSpace ℂ n`, and $A$ acts on it through `Matrix.toEuclideanLin`. -/
theorem bauer_fike_residual (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X)
    {u : EuclideanSpace ℂ n} (hu : ‖u‖ = 1) (θ : ℂ) :
    ∃ i, ‖θ - d i‖ ≤ NormedRing.condNumber X *
      ‖Matrix.toEuclideanLin (X * Matrix.diagonal d * X⁻¹) u - θ • u‖ := by
  classical
  set A := X * Matrix.diagonal d * X⁻¹ with hA
  set r : EuclideanSpace ℂ n := Matrix.toEuclideanLin A u - θ • u with hr
  -- the rank-one backward perturbation `r uᴴ`
  set M : Matrix n n ℂ :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (InnerProductSpace.rankOne ℂ r u) with hM
  have hMapply : Matrix.toEuclideanCLM (𝕜 := ℂ) M = InnerProductSpace.rankOne ℂ r u := by
    rw [hM, StarAlgEquiv.apply_symm_apply]
  have hMnorm : ‖M‖ = ‖r‖ := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, hMapply, InnerProductSpace.norm_rankOne, hu, mul_one]
  have huu : inner ℂ u u = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hu0 : WithLp.ofLp u ≠ 0 := by
    intro h
    have : u = 0 := by
      apply WithLp.ofLp_injective
      simpa using h
    rw [this, norm_zero] at hu
    exact one_ne_zero hu.symm
  have hclm : Matrix.toEuclideanCLM (𝕜 := ℂ) (A + (-M)) u = θ • u := by
    rw [map_add, map_neg, hMapply]
    change Matrix.toEuclideanLin A u + -(inner ℂ u u • r) = θ • u
    rw [huu, one_smul, hr]
    abel
  have heig : (A + (-M)) *ᵥ (WithLp.ofLp u) = θ • WithLp.ofLp u := by
    have h := congrArg WithLp.ofLp hclm
    rw [Matrix.add_mulVec, Matrix.neg_mulVec]
    simpa using h
  have hspec : θ ∈ spectrum ℂ (A + (-M)) := by
    rw [← Matrix.spectrum_toLin']
    refine Module.End.hasEigenvalue_iff_mem_spectrum.mp
      (Module.End.hasEigenvalue_of_hasEigenvector (x := WithLp.ofLp u) ⟨?_, hu0⟩)
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact heig
  obtain ⟨i, hi⟩ := bauer_fike X d hX (-M) hspec
  exact ⟨i, by rwa [norm_neg, hMnorm] at hi⟩

/-- **The Gershgorin theorem**, row form ([saad2011numerical], Theorem 3.11; [kress1998numerical],
Theorem 7.7). The spectrum of $A \in \mathbb{C}^{n \times n}$ lies in the union of the closed
discs with centers $a_{ii}$ and radii $\sum_{j \neq i} |a_{ij}|$:
$$\sigma(A) \subseteq \bigcup_i \Big\{ z \in \mathbb{C} : |z - a_{ii}| \le \sum_{j \neq i}
  |a_{ij}| \Big\}.$$

The version for one eigenvalue is Mathlib's `eigenvalue_mem_ball`. -/
theorem spectrum_subset_iUnion_closedBall (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ i, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) := by
  intro μ hμ
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨i, hi⟩ := _root_.eigenvalue_mem_ball (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- **The Gershgorin theorem**, column form ([saad2011numerical], Theorem 3.11; [saad2003iterative],
Theorem 4.6). The spectrum of $A \in \mathbb{C}^{n \times n}$ lies in the union of the closed
discs with centers $a_{jj}$ and radii $\sum_{i \neq j} |a_{ij}|$.

A matrix and its transpose have the same spectrum, so this is the row form for the transpose. -/
theorem spectrum_subset_iUnion_closedBall_col (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ j, Metric.closedBall (A j j) (∑ i ∈ Finset.univ.erase j, ‖A i j‖) := by
  intro μ hμ
  have hT : μ ∈ spectrum ℂ Aᵀ := by rwa [Matrix.spectrum_transpose]
  simpa using spectrum_subset_iUnion_closedBall Aᵀ hT

/-- **Counting eigenvalues in Gershgorin discs** ([saad2011numerical], Theorem 3.12). Let
$A \in \mathbb{C}^{n \times n}$ and let $\tau$ be a set of indices. Let $S$ be the union of the
Gershgorin discs $\{z : |z - a_{ii}| \le \sum_{j \neq i} |a_{ij}|\}$ for $i \in \tau$, and let
$S'$ be the union of these discs for $i \notin \tau$. If $S$ and $S'$ are disjoint, then $S$
contains exactly $|\tau|$ eigenvalues of $A$, counted with algebraic multiplicity.

The count is `Polynomial.countRootsIn S A.charpoly`, the number of roots of the characteristic
polynomial in $S$, counted with multiplicity; by `Matrix.mem_spectrum_iff_isRoot_charpoly` this
is the sum of the algebraic multiplicities of the eigenvalues in $S$. The proof is the homotopy
$A(t) = D + tH$ of the source, with $D$ the diagonal of $A$ and $H = A - D$. The Gershgorin
discs of $A(t)$ are those of $A$ with the radii multiplied by $t$, so for $0 \le t \le 1$ the
eigenvalues of $A(t)$ stay in $S \cup S'$; at $t = 0$ the eigenvalues are the diagonal entries,
and exactly those with index in $\tau$ lie in $S$. The continuity argument of the source, that
the eigenvalues cannot move from $S$ to $S'$, is `Polynomial.countRootsIn_eq_of_preconnected`, a
compactness argument in the coefficients that needs no complex analysis. -/
theorem card_spectrum_of_disjoint_gershgorin (A : Matrix n n ℂ) (τ : Finset n) {S S' : Set ℂ}
    (hS : S = ⋃ i ∈ τ, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖))
    (hS' : S' = ⋃ i ∈ τᶜ, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖))
    (hdisj : Disjoint S S') :
    A.charpoly.countRootsIn S = τ.card := by
  classical
  set r : n → ℝ := fun i => ∑ j ∈ Finset.univ.erase i, ‖A i j‖ with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => Finset.sum_nonneg fun j _ => norm_nonneg _
  set D : Matrix n n ℂ := Matrix.diagonal fun i => A i i with hD
  set H : Matrix n n ℂ := A - D with hH
  set M : ℝ → Matrix n n ℂ := fun t => D + (t : ℂ) • H with hM
  have hMdiag : ∀ t i, M t i i = A i i := by
    intro t i; simp [hM, hD, hH, Matrix.diagonal_apply_eq]
  have hMoff : ∀ t i j, i ≠ j → M t i j = (t : ℂ) * A i j := by
    intro t i j hij; simp [hM, hD, hH, Matrix.diagonal_apply_ne _ hij]
  have hM0 : M 0 = D := by simp [hM]
  have hM1 : M 1 = A := by simp [hM, hH]
  have hMcont : Continuous M :=
    continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  -- the two unions of discs are compact, and together they are all the discs
  have hScpt : IsCompact S := by
    rw [hS]; exact τ.finite_toSet.isCompact_biUnion fun i _ => isCompact_closedBall _ _
  have hS'cpt : IsCompact S' := by
    rw [hS']; exact τᶜ.finite_toSet.isCompact_biUnion fun i _ => isCompact_closedBall _ _
  have hunion : S ∪ S' = ⋃ i, Metric.closedBall (A i i) (r i) := by
    ext z
    simp only [hS, hS', Set.mem_union, Set.mem_iUnion, Finset.mem_compl, exists_prop, hr]
    constructor
    · rintro (⟨i, _, hi⟩ | ⟨i, _, hi⟩) <;> exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      by_cases h : i ∈ τ
      · exact Or.inl ⟨i, h, hi⟩
      · exact Or.inr ⟨i, h, hi⟩
  -- Gershgorin for `M t`: its discs are those of `A` with the radii scaled by `t ≤ 1`
  have hroots : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ z ∈ (M t).charpoly.roots, z ∈ S ∪ S' := by
    intro t ht z hz
    rw [hunion]
    have hz' : z ∈ spectrum ℂ (M t) := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Matrix.spectrum_subset_iUnion_closedBall (M t) hz')
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [hMdiag t i] at hi
    refine Metric.closedBall_subset_closedBall ?_ hi
    calc ∑ j ∈ Finset.univ.erase i, ‖M t i j‖
        = ∑ j ∈ Finset.univ.erase i, |t| * ‖A i j‖ := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hMoff t i j (Finset.ne_of_mem_erase hj).symm]
          simp
      _ = |t| * r i := by rw [hr, Finset.mul_sum]
      _ ≤ r i := by
          rw [abs_of_nonneg ht.1]
          exact mul_le_of_le_one_left (hr0 i) ht.2
  have hcard : ∀ t : ℝ, Multiset.card (M t).charpoly.roots = Fintype.card n := fun t =>
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (M t).charpoly)).trans
      (Matrix.charpoly_natDegree_eq_dim _)
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have key := Polynomial.countRootsIn_eq_of_preconnected (T := Set.Icc (0 : ℝ) 1)
    (p := fun t => (M t.1).charpoly) (n := Fintype.card n) hScpt hS'cpt hdisj
    (fun _ => Matrix.charpoly_monic _)
    (fun _ => Matrix.charpoly_natDegree_eq_dim _)
    (fun t => hcard t.1)
    (fun t z hz => hroots t.1 t.2 z hz)
    (fun j => (Matrix.continuous_coeff_charpoly hMcont j).comp continuous_subtype_val)
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  simp only at key
  -- at `t = 0` the roots are the diagonal entries, and `a_ii ∈ S` exactly for `i ∈ τ`
  rw [← hM1, ← key, hM0, Matrix.charpoly_diagonal, Polynomial.countRootsIn_prod_univ_X_sub_C]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra hiτ
    exact Set.disjoint_left.mp hdisj hi (by
      rw [hS']
      exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_compl.mpr hiτ, Metric.mem_closedBall_self (hr0 i)⟩)
  · intro hiτ
    rw [hS]
    exact Set.mem_iUnion₂.mpr ⟨i, hiτ, Metric.mem_closedBall_self (hr0 i)⟩

/-- **An isolated Gershgorin disc contains exactly one eigenvalue** ([saad2011numerical], the
special case of Theorem 3.12 noted after its proof). Let $A \in \mathbb{C}^{n \times n}$, let
$S$ be the Gershgorin disc $\{z : |z - a_{ii}| \le \sum_{j \neq i} |a_{ij}|\}$ of the index $i$,
and let $S'$ be the union of the other Gershgorin discs. If $S$ and $S'$ are disjoint, then $S$
contains exactly one eigenvalue of $A$, counted with algebraic multiplicity.

It follows that the eigenvalue in an isolated disc is simple. This is the case $\tau = \{i\}$ of
`Matrix.card_spectrum_of_disjoint_gershgorin`. -/
theorem card_spectrum_of_isolated_gershgorin (A : Matrix n n ℂ) (i : n) {S S' : Set ℂ}
    (hS : S = Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖))
    (hS' : S' = ⋃ k ∈ ({i} : Finset n)ᶜ,
      Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖))
    (hdisj : Disjoint S S') :
    A.charpoly.countRootsIn S = 1 := by
  have := card_spectrum_of_disjoint_gershgorin A {i} (by simpa using hS) hS' hdisj
  simpa using this

end Matrix

/-!
### The theorem of Hirsch

The real and the imaginary parts of every eigenvalue of $A$ lie between the extreme eigenvalues of
the Hermitian part $H = (A + A^H)/2$ and of the matrix $S = (A - A^H)/(2i)$, respectively
([quarteroni2000numerical], Theorem 5.1). Both bounds are Bendixson's theorem
`re_hasEigenvalue_mem_Icc_of_symmetricPart` for matrices, through `Matrix.toEuclideanLin`; the bound
for the imaginary part is the bound for the real part of $-iA$, whose Hermitian part is $S$.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Bendixson's theorem for matrices.** Let $A, H \in \mathbb{K}^{n \times n}$ with $H$ Hermitian,
and suppose that $\operatorname{Re} \langle Hx, x \rangle = \operatorname{Re} \langle Ax, x
\rangle$ for every $x \in \mathbb{K}^n$. Then every eigenvalue $\mu$ of $A$ satisfies
$$\lambda_{\min}(H) \le \operatorname{Re} \mu \le \lambda_{\max}(H).$$

Here $\lambda_{\min}(H)$ and $\lambda_{\max}(H)$ are the infimum and the supremum of
`Matrix.IsHermitian.eigenvalues`. -/
theorem re_mem_Icc_eigenvalues_of_mem_spectrum {A H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hHA : ∀ x : EuclideanSpace 𝕜 n, RCLike.re (inner 𝕜 (toEuclideanLin H x) x)
      = RCLike.re (inner 𝕜 (toEuclideanLin A x) x))
    {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A) :
    RCLike.re μ ∈ Set.Icc (⨅ i, hH.eigenvalues i) (⨆ i, hH.eigenvalues i) := by
  refine re_hasEigenvalue_mem_Icc_of_symmetricPart (hH.isSymmetricBoundedBy_toEuclideanLin
    fun i => ⟨ciInf_le (Set.finite_range _).bddBelow i, le_ciSup (Set.finite_range _).bddAbove i⟩)
    hHA ((hasEigenvalue_toEuclideanLin_iff A μ).mpr hμ)

/-- **The theorem of Hirsch**, real part ([quarteroni2000numerical], Theorem 5.1). Let
$A \in \mathbb{K}^{n \times n}$ and let $H = (A + A^H)/2$ be its Hermitian part. Then every
eigenvalue $\mu$ of $A$ satisfies
$$\lambda_{\min}(H) \le \operatorname{Re} \mu \le \lambda_{\max}(H).$$

This half is also due to Bendixson. The matrix $H$ is `Matrix.hermitianPart A`, and
$\lambda_{\min}(H)$ and $\lambda_{\max}(H)$ are the infimum and the supremum of its eigenvalues. -/
theorem hirsch_re (A : Matrix n n 𝕜) {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A) :
    RCLike.re μ ∈ Set.Icc (⨅ i, (hermitianPart_isHermitian A).eigenvalues i)
      (⨆ i, (hermitianPart_isHermitian A).eigenvalues i) :=
  re_mem_Icc_eigenvalues_of_mem_spectrum _ (re_inner_hermitianPart A) hμ

/-- **The theorem of Hirsch**, imaginary part ([quarteroni2000numerical], Theorem 5.1). Let
$A \in \mathbb{C}^{n \times n}$ and let $S = (A - A^H)/(2i)$. Then every eigenvalue $\mu$ of $A$
satisfies
$$\lambda_{\min}(S) \le \operatorname{Im} \mu \le \lambda_{\max}(S).$$

The matrix $S$ is `Matrix.skewHermitianPart A`, and $\lambda_{\min}(S)$ and $\lambda_{\max}(S)$
are the infimum and the supremum of its eigenvalues. The proof applies the real part of the
theorem to $-iA$, whose Hermitian part is $S$ and whose eigenvalues are $-i$ times those of $A$. -/
theorem hirsch_im (A : Matrix n n ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    μ.im ∈ Set.Icc (⨅ i, (skewHermitianPart_isHermitian A).eigenvalues i)
      (⨆ i, (skewHermitianPart_isHermitian A).eigenvalues i) := by
  have hμ' : (-Complex.I) • μ ∈ spectrum ℂ ((-Complex.I) • A) := by
    rw [show (-Complex.I) = (Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero) : ℂ)
      from rfl, ← Units.smul_def, ← Units.smul_def, spectrum.unit_smul_eq_smul]
    exact Set.smul_mem_smul_set hμ
  have h := re_mem_Icc_eigenvalues_of_mem_spectrum (skewHermitianPart_isHermitian A)
    (fun x => by rw [skewHermitianPart_eq_hermitianPart, re_inner_hermitianPart]) hμ'
  simpa [Complex.mul_re] using h

end Matrix

/-!
### Algebraically simple eigenvalues

At an eigenvalue $\lambda$ of algebraic multiplicity one, that is, with a maximal generalized
eigenspace of dimension $1$, the two hypotheses of `Module.End.hasDerivAt_eigenvalue_perturbation`,
$\langle w, u \rangle \neq 0$ and geometric simplicity, are theorems. The first is the opening
paragraph of the proof of [quarteroni2000numerical], Theorem 5.4, without the diagonalizability
assumed there.
-/

namespace Module.End

variable [FiniteDimensional 𝕜 E]

/-- Let $A$ be a linear operator on a finite-dimensional inner product space, and let
$Au = \lambda u$ with $u \neq 0$. If the maximal generalized eigenspace of $\lambda$ has
dimension $1$, then it is $\operatorname{span}\{u\}$. -/
theorem maxGenEigenspace_eq_span_singleton_of_finrank_eq_one {A : E →ₗ[𝕜] E} {l : 𝕜} {u : E}
    (hAu : A u = l • u) (hu : u ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.maxGenEigenspace A l) = 1) :
    Module.End.maxGenEigenspace A l = 𝕜 ∙ u := by
  have hle : (𝕜 ∙ u) ≤ Module.End.maxGenEigenspace A l :=
    (Submodule.span_singleton_le_iff_mem _ _).2
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hAu))
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hsimple, finrank_span_singleton hu])).symm

/-- **A right and a left eigenvector for an algebraically simple eigenvalue are not orthogonal**
([quarteroni2000numerical], Theorem 5.4, the first step of the proof; [saad2011numerical],
§3.2.1). Let $A$ be a linear operator on a finite-dimensional inner product space, let
$Au = \lambda u$ with $u \neq 0$, and let $w \neq 0$ be a left eigenvector of $A$ for $\lambda$.
If the maximal generalized eigenspace of $\lambda$ has dimension $1$, then
$\langle w, u \rangle \neq 0$.

Suppose that $\langle w, u \rangle = 0$. Then $u$ lies in $\{w\}^\perp$, which is the range of
$A - \lambda$: the range is contained in $\{w\}^\perp$ because $w$ is a left eigenvector, and
both have codimension one, since the kernel of $A - \lambda$ is the line through $u$. So
$u = (A - \lambda) z$ for some $z$, and $z$ is a generalized eigenvector of index two, with
$(A - \lambda)^2 z = 0$ and $(A - \lambda) z \neq 0$, in a generalized eigenspace that is only a
line. Thus the hypothesis $\langle w, u \rangle \neq 0$ of
`Module.End.hasDerivAt_eigenvalue_perturbation` holds automatically at an algebraically simple
eigenvalue. -/
theorem inner_ne_zero_of_finrank_maxGenEigenspace_eq_one {A : E →ₗ[𝕜] E} {l : 𝕜} {u w : E}
    (hAu : A u = l • u) (hu : u ≠ 0) (hw : IsLeftEigenvector A l w)
    (hw0 : w ≠ 0) (hsimple : Module.finrank 𝕜 (Module.End.maxGenEigenspace A l) = 1) :
    (inner 𝕜 w u : 𝕜) ≠ 0 := by
  intro hwu
  set B : E →ₗ[𝕜] E := A - l • 1 with hBdef
  have hBapply : ∀ y, B y = A y - l • y := fun y => by simp [hBdef]
  have hBu : B u = 0 := by rw [hBapply, hAu, sub_self]
  -- the kernel of `B` is the line through `u`
  have hker : LinearMap.ker B = 𝕜 ∙ u := by
    rw [hBdef, ← Module.End.eigenspace_def,
      ← Krylov.maxGenEigenspace_eq_eigenspace_of_finrank_eq_one hsimple]
    exact maxGenEigenspace_eq_span_singleton_of_finrank_eq_one hAu hu hsimple
  -- the range of `B` is the orthogonal complement of `w`
  have hrange_le : LinearMap.range B ≤ (𝕜 ∙ w)ᗮ := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hBapply, inner_sub_right,
      inner_smul_right, hw.inner_apply, sub_self]
  have hrange : LinearMap.range B = (𝕜 ∙ w)ᗮ := by
    refine Submodule.eq_of_le_of_finrank_le hrange_le ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker B
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 ∙ w)
    rw [hker, finrank_span_singleton hu] at h1
    rw [finrank_span_singleton hw0] at h2
    omega
  -- so `u = B z` for some `z`, a generalized eigenvector of index two
  have humem : u ∈ LinearMap.range B := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hwu
  obtain ⟨z, hz⟩ := humem
  have hzmem : z ∈ Module.End.maxGenEigenspace A l := by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨2, by rw [pow_two, Module.End.mul_apply, ← hBdef, hz, hBu]⟩
  rw [maxGenEigenspace_eq_span_singleton_of_finrank_eq_one hAu hu hsimple,
    Submodule.mem_span_singleton] at hzmem
  obtain ⟨c, rfl⟩ := hzmem
  rw [map_smul, hBu, smul_zero] at hz
  exact hu hz.symm

/-- **A simple eigenvalue moves differentiably**, for an algebraically simple eigenvalue. Let $A$
and $B$ be bounded operators on a finite-dimensional inner product space $E$ over $\mathbb{K}$,
let $Au = \lambda u$ with $u \neq 0$, let $w \neq 0$ be a left eigenvector of $A$ for $\lambda$,
and suppose that the maximal generalized eigenspace of $\lambda$ has dimension $1$. Then there
are functions $\mu : \mathbb{K} \to \mathbb{K}$ and $v : \mathbb{K} \to E$ and a vector $v'$
such that
* $\mu(0) = \lambda$ and $v(0) = u$;
* $A v(t) + t B v(t) = \mu(t) v(t)$ for all $t$ near $0$;
* $v$ has the derivative $v'$ at $0$;
* $\mu$ has the derivative $\langle w, Bu \rangle / \langle w, u \rangle$ at $0$.

This is `Module.End.hasDerivAt_eigenvalue_perturbation` with its two hypotheses,
$\langle w, u \rangle \neq 0$ and geometric simplicity, replaced by the single hypothesis of
algebraic simplicity. It is the branch that [quarteroni2000numerical], Theorem 5.4 presupposes
when it calls $\lambda$ simple. -/
theorem hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one {A B : E →L[𝕜] E} {l : 𝕜}
    {u w : E} (hAu : A u = l • u) (hu : u ≠ 0)
    (hw : IsLeftEigenvector (A : E →ₗ[𝕜] E) l w) (hw0 : w ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.maxGenEigenspace (A : E →ₗ[𝕜] E) l) = 1) :
    ∃ (mu : 𝕜 → 𝕜) (v : 𝕜 → E) (v' : E), mu 0 = l ∧ v 0 = u ∧
      (∀ᶠ t in nhds (0 : 𝕜), A (v t) + t • B (v t) = mu t • v t) ∧
      HasDerivAt v v' 0 ∧
      HasDerivAt mu (inner 𝕜 w (B u) / inner 𝕜 w u) 0 := by
  refine hasDerivAt_eigenvalue_perturbation hAu hw
    (inner_ne_zero_of_finrank_maxGenEigenspace_eq_one (A := (A : E →ₗ[𝕜] E)) hAu hu hw hw0
      hsimple) fun z hz => ?_
  have hz' : z ∈ Module.End.maxGenEigenspace (A : E →ₗ[𝕜] E) l :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hz)
  rw [maxGenEigenspace_eq_span_singleton_of_finrank_eq_one (A := (A : E →ₗ[𝕜] E)) hAu hu hsimple,
    Submodule.mem_span_singleton] at hz'
  obtain ⟨c, rfl⟩ := hz'
  exact ⟨c, rfl⟩

end Module.End

/-! ### The distance to a group of eigenvectors -/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- Let $A$ be a symmetric operator on an inner product space of dimension $n$, with orthonormal
eigenbasis $v_i$, and let $s$ be a set of indices. A vector $x$ is orthogonal to
$\operatorname{span}\{v_i \mid i \in s\}$ if and only if $\langle v_i, x \rangle = 0$ for every
$i \in s$.

The span is `LinearMap.IsSymmetric.eigenvectorSpan`, and the coefficients are those of
`LinearMap.IsSymmetric.eigenvectorBasis`. -/
theorem mem_orthogonal_eigenvectorSpan_iff {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    {s : Finset (Fin n)} {x : E} :
    x ∈ (hA.eigenvectorSpan hn s)ᗮ ↔ ∀ i ∈ s, (hA.eigenvectorBasis hn).repr x i = 0 := by
  rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le, Submodule.isOrtho_comm,
    eigenvectorSpan, Submodule.isOrtho_span]
  simp only [Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, forall_eq, OrthonormalBasis.repr_apply_apply]

/-- **The distance from an approximate eigenvector to a group of eigenvectors**
([quarteroni2000numerical], Property 5.6; [isaacson1994analysis], pp. 142–143). Let $A$ be a
symmetric operator on an inner product space of dimension $n$, with eigenvalues $\lambda_i$ and
orthonormal eigenvectors $v_i$. Let $\theta \in \mathbb{R}$, let $x$ be a vector with residual
$r = Ax - \theta x$, let $s$ be a set of indices, and let $\delta > 0$ satisfy
$\delta \le |\lambda_i - \theta|$ for every $i \notin s$. Then
$$\|x - P_s x\| \le \frac{\|r\|}{\delta},$$
where $P_s$ is the orthogonal projection onto $\operatorname{span}\{v_i \mid i \in s\}$.

The source also assumes $|\lambda_i - \theta| \le \|r\|$ for $i \in s$; that hypothesis is not
needed. If $s$ is the set of the indices of one eigenvalue, the result is the residual bound for
one eigenspace, `LinearMap.IsSymmetric.sin_angle_le_norm_residual_div`. The proof splits
$x = p + q$ along the span and its orthogonal complement, which are both invariant under $A$.
The residual splits as $(A - \theta) p + (A - \theta) q$ with orthogonal terms, so
$\|r\| \ge \|(A - \theta) q\|$, and in the eigenbasis $\|(A - \theta) q\|^2 = \sum_{i \notin s}
(\lambda_i - \theta)^2 |q_i|^2 \ge \delta^2 \|q\|^2$. -/
theorem dist_eigenvectorSpan_le_norm_residual_div {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (s : Finset (Fin n)) (θ : ℝ) (x : E) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∉ s, δ ≤ |hA.eigenvalues hn i - θ|) :
    ‖x - (hA.eigenvectorSpan hn s).starProjection x‖ ≤ ‖A x - (θ : 𝕜) • x‖ / δ := by
  set W : Submodule 𝕜 E := hA.eigenvectorSpan hn s with hWdef
  set p : E := W.starProjection x with hpdef
  set q : E := x - p with hqdef
  have hpmem : p ∈ W := W.starProjection_apply_mem x
  have hqmem : q ∈ Wᗮ := W.sub_starProjection_mem_orthogonal x
  have hpres : A p - (θ : 𝕜) • p ∈ W :=
    (hA.mem_eigenvectorSpan_iff hn).mpr fun i hi => by
      rw [hA.repr_sub_smul hn, (hA.mem_eigenvectorSpan_iff hn).mp hpmem i hi, mul_zero]
  have hqres : A q - (θ : 𝕜) • q ∈ Wᗮ :=
    (hA.mem_orthogonal_eigenvectorSpan_iff hn).mpr fun i hi => by
      rw [hA.repr_sub_smul hn, (hA.mem_orthogonal_eigenvectorSpan_iff hn).mp hqmem i hi, mul_zero]
  have hsplit : A x - (θ : 𝕜) • x = (A p - (θ : 𝕜) • p) + (A q - (θ : 𝕜) • q) := by
    rw [hqdef, map_sub, smul_sub]
    abel
  have hpyth : ‖A x - (θ : 𝕜) • x‖ ^ 2
      = ‖A p - (θ : 𝕜) • p‖ ^ 2 + ‖A q - (θ : 𝕜) • q‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_right_of_mem_orthogonal hpres hqres)
  have hlow : δ * ‖q‖ ≤ ‖A q - (θ : 𝕜) • q‖ := by
    have hsq : (δ * ‖q‖) ^ 2 ≤ ‖A q - (θ : 𝕜) • q‖ ^ 2 := by
      rw [mul_pow, hA.norm_residual_sq hn θ q, hA.norm_sq_eq_sum_norm_repr_sq hn q,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : i ∈ s
      · rw [(hA.mem_orthogonal_eigenvectorSpan_iff hn).mp hqmem i hi]
        simp
      · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h := hsep i hi
        nlinarith [sq_abs (hA.eigenvalues hn i - θ), abs_nonneg (hA.eigenvalues hn i - θ)]
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  rw [le_div_iff₀ hδ, mul_comm]
  refine hlow.trans ?_
  nlinarith [hpyth, norm_nonneg (A x - (θ : 𝕜) • x), norm_nonneg (A q - (θ : 𝕜) • q),
    sq_nonneg ‖A p - (θ : 𝕜) • p‖]

end LinearMap.IsSymmetric

/-!
### The resolvent step, the bound from a Schur form, and approximate invariant subspaces

The step shared by the resolvent-based perturbation bounds is
`NormedRing.one_le_norm_inverse_mul_of_not_isUnit_sub` in `Numlib.Analysis.Normed.Ring.Inverse`
([golub2013matrix], (7.2.1), through Lemma 2.3.3 there): if $\mu$ is an eigenvalue of $A + E$ but
not of $A$, then $\|(\mu - A)^{-1} E\| \ge 1$, because otherwise
$\mu - A - E = (\mu - A)(1 - (\mu - A)^{-1} E)$ would be invertible by the Neumann series.
`Matrix.exists_norm_sub_le_of_schur` is [golub2013matrix], Theorem 7.2.3, a bound of Henrici type
for a matrix that need not be diagonalizable: with a Schur form $Q^H A Q = D + N$, the resolvent of
$D + N$ is a finite Neumann series in $(\mu - D)^{-1} N$, whose length is the nilpotency index of
the entrywise absolute value $|N|$.
`Matrix.IsHermitian.exists_mem_spectrum_abs_sub_le_of_mul_sub_mul` is the block form of the residual
bound ([golub2013matrix], Theorem 8.1.13, with the constant $1$ of the residual bound for one vector
in place of the constant $\sqrt{2}$ of the source): an orthonormal block $Q_1$ and a Hermitian $S$
with $\|AQ_1 - Q_1 S\|_2 \le \varepsilon$ put an eigenvalue of $A$ within $\varepsilon$ of every
eigenvalue of $S$.
-/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E]

/-- **Orthonormal eigenvectors are a sublist of the sorted spectrum.** Let $T$ be a symmetric
operator on an inner product space of dimension $N$, with eigenvalues
$\lambda_0(T) \ge \dots \ge \lambda_{N-1}(T)$. Let $v_0, \dots, v_{r-1}$ be orthonormal with
$T v_k = s_k v_k$, where $s$ is antitone. Then there is a strictly increasing map $\sigma : \{0,
\dots, r-1\} \to \{0, \dots, N-1\}$ with $\lambda_{\sigma(k)}(T) = s_k$ for every $k$.

Each value $c$ occurs among the $s_k$ at most as often as among the eigenvalues, because the
$v_k$ with $s_k = c$ are independent vectors in the eigenspace of $c$, and a sorted submultiset
of a sorted list is a sublist. The map $\sigma$ is an order embedding `Fin r ↪o Fin N`, and the
eigenvalues are `LinearMap.IsSymmetric.eigenvalues`. -/
theorem exists_orderEmbedding_eigenvalues_eq {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {N : ℕ}
    (hN : Module.finrank 𝕜 E = N) {r : ℕ} {v : Fin r → E} (hv : Orthonormal 𝕜 v)
    {s : Fin r → ℝ} (hs : Antitone s) (hTv : ∀ k, T (v k) = (s k : 𝕜) • v k) :
    ∃ σ : Fin r ↪o Fin N, ∀ k, hT.eigenvalues hN (σ k) = s k := by
  classical
  -- the multiplicities
  have hcount : ∀ c : ℝ, (Finset.univ.filter fun k => c = s k).card ≤
      (Finset.univ.filter fun j => c = hT.eigenvalues hN j).card := by
    intro c
    have hmem : ∀ k, c = s k → v k ∈ hT.eigenvectorSpan hN
        (Finset.univ.filter fun j => c = hT.eigenvalues hN j) := by
      intro k hk
      rw [hT.mem_eigenvectorSpan_iff hN]
      intro j hj
      have hj' : hT.eigenvalues hN j ≠ c := fun h' =>
        hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'.symm⟩)
      rw [OrthonormalBasis.repr_apply_apply]
      have h1 := hT (hT.eigenvectorBasis hN j) (v k)
      rw [hTv, hT.apply_eigenvectorBasis, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
        ← hk] at h1
      have h2 : ((hT.eigenvalues hN j : 𝕜) - c) *
          inner 𝕜 (hT.eigenvectorBasis hN j) (v k) = 0 := by
        rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (by exact_mod_cast hj'))
    set I := Finset.univ.filter fun k => c = s k with hI
    have hli : LinearIndependent 𝕜 fun k : (I : Set (Fin r)) => v k :=
      hv.linearIndependent.comp _ Subtype.val_injective
    have hle : Submodule.span 𝕜 (Set.range fun k : (I : Set (Fin r)) => v k) ≤
        hT.eigenvectorSpan hN (Finset.univ.filter fun j => c = hT.eigenvalues hN j) :=
      Submodule.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        exact hmem k (Finset.mem_filter.1 k.2).2)
    have := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hli, hT.finrank_eigenvectorSpan hN] at this
    simpa using this
  -- a sorted sub-multiset of a sorted list is a sublist
  have hsub : List.Subperm (List.ofFn s) (List.ofFn (hT.eigenvalues hN)) := by
    rw [← Multiset.coe_le, ← Fin.univ_val_map, ← Fin.univ_val_map, Multiset.le_iff_count]
    intro c
    rw [Multiset.count_map, Multiset.count_map]
    exact hcount c
  have hsl := List.sublist_of_subperm_of_sortedGE hsub hs.sortedGE_ofFn
    (hT.eigenvalues_antitone hN).sortedGE_ofFn
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 hsl
  refine ⟨(Fin.castOrderIso (List.length_ofFn (f := s)).symm).toOrderEmbedding.trans
    (f.trans (Fin.castOrderIso (List.length_ofFn (f := hT.eigenvalues hN))).toOrderEmbedding),
    fun k => ?_⟩
  have := hf (Fin.cast (List.length_ofFn (f := s)).symm k)
  rw [List.get_ofFn, List.get_ofFn] at this
  simpa using this.symm

end LinearMap.IsSymmetric

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem not_isUnit_sub_sub_of_mem_spectrum_add {A E : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 (A + E)) : ¬IsUnit ((μ • 1 - A) - E) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] at hμ
  rwa [sub_sub]

private theorem isUnit_smul_one_sub_of_notMem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hA : μ ∉ spectrum 𝕜 A) : IsUnit (μ • 1 - A) := by
  rwa [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, not_not] at hA

section L2

open scoped Matrix.Norms.L2Operator

/-- **The resolvent step** in the spectral norm. Let $A, E \in \mathbb{K}^{n \times n}$. If $\mu$ is
an eigenvalue of $A + E$ but not of $A$, then
$$1 \le \|(\mu I - A)^{-1} E\|_2,$$
and so $1 \le \|(\mu I - A)^{-1}\|_2 \|E\|_2$.

This step is shared by [golub2013matrix], Theorems 7.2.1–7.2.3 and 7.9.8; it is (7.2.1) there,
through Lemma 2.3.3. -/
theorem one_le_norm_mul_of_mem_spectrum_add {A E : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 (A + E)) (hA : μ ∉ spectrum 𝕜 A) : 1 ≤ ‖(μ • 1 - A)⁻¹ * E‖ := by
  rw [nonsing_inv_eq_ringInverse]
  exact NormedRing.one_le_norm_inverse_mul_of_not_isUnit_sub
    (isUnit_smul_one_sub_of_notMem_spectrum hA) (not_isUnit_sub_sub_of_mem_spectrum_add hμ)

end L2

/-- **The resolvent step** in every induced $p$-norm. Let $1 \le p \le \infty$ and
$A, E \in \mathbb{K}^{n \times n}$. If $\mu$ is an eigenvalue of $A + E$ but not of $A$, then
$1 \le \|(\mu I - A)^{-1} E\|_p$.

The norm $\|\cdot\|_p$ is `Matrix.lpOpNorm p`. The spectral-norm form is
`Matrix.one_le_norm_mul_of_mem_spectrum_add`. -/
theorem one_le_lpOpNorm_mul_of_mem_spectrum_add (p : ENNReal) [Fact (1 ≤ p)]
    {A E : Matrix n n 𝕜} {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 (A + E)) (hA : μ ∉ spectrum 𝕜 A) :
    1 ≤ lpOpNorm p ((μ • 1 - A)⁻¹ * E) := by
  rw [lpOpNorm, lpCLM_mul, ← ringInverse_lpCLM]
  refine NormedRing.one_le_norm_inverse_mul_of_not_isUnit_sub
    ((isUnit_lpCLM_iff p _).mpr (isUnit_smul_one_sub_of_notMem_spectrum hA)) ?_
  have : lpCLM p (μ • 1 - A) - lpCLM p E = lpCLM p ((μ • 1 - A) - E) := by
    ext x i; simp [sub_mulVec]
  rw [this, isUnit_lpCLM_iff]
  exact not_isUnit_sub_sub_of_mem_spectrum_add hμ

/-- **The Bauer–Fike theorem in every induced $p$-norm** ([golub2013matrix], Theorem 7.2.2). Let
$1 \le p \le \infty$, let $X \in \mathbb{C}^{n \times n}$ be invertible and
$d \in \mathbb{C}^n$. If $\mu$ is an eigenvalue of $X \operatorname{diag}(d) X^{-1} + E$, then
for some $i$
$$|\mu - d_i| \le \kappa_p(X) \|E\|_p,$$
where $\kappa_p(X) = \|X\|_p \|X^{-1}\|_p$.

The norm is `Matrix.lpOpNorm p`, the condition number is `Matrix.condNumberLp p`, and
`Matrix.bauer_fike` is the case $p = 2$. If $\mu$ is no $d_i$, then $\mu$ is an eigenvalue of
$D + X^{-1} E X$ but not of $D$, so the resolvent step
`Matrix.one_le_lpOpNorm_mul_of_mem_spectrum_add` gives
$$1 \le \|(\mu - D)^{-1}\|_p \|X^{-1}\|_p \|E\|_p \|X\|_p,$$
and $\|(\mu - D)^{-1}\|_p = \max_i 1/|\mu - d_i|$ (`Matrix.lpOpNorm_diagonal`). -/
theorem bauer_fike_lpOpNorm (p : ENNReal) [Fact (1 ≤ p)] (X : Matrix n n ℂ) (d : n → ℂ)
    (hX : IsUnit X) (E : Matrix n n ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (X * diagonal d * X⁻¹ + E)) :
    ∃ i, ‖μ - d i‖ ≤ condNumberLp p X * lpOpNorm p E := by
  have hne : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have : Subsingleton (Matrix n n ℂ) := ⟨fun a b => by ext i; exact isEmptyElim i⟩
    rw [spectrum.of_subsingleton] at hμ
    exact hμ
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ‖μ - d i‖)
    ⟨Classical.arbitrary n, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  have hκ0 : 0 ≤ condNumberLp p X * lpOpNorm p E :=
    mul_nonneg (mul_nonneg (lpOpNorm_nonneg p X) (lpOpNorm_nonneg p _)) (lpOpNorm_nonneg p E)
  by_cases hz : μ - d i₀ = 0
  · rw [hz, norm_zero]
    exact hκ0
  have hδ : 0 < ‖μ - d i₀‖ := norm_pos_iff.mpr hz
  have hne0 : ∀ i, μ - d i ≠ 0 := fun i hi => by
    have h := hi₀ i (Finset.mem_univ i)
    rw [hi, norm_zero] at h
    exact hz (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  have hXd := (isUnit_iff_isUnit_det X).mp hX
  -- conjugating by `X` leaves the spectrum unchanged
  have hsim : X⁻¹ * (X * diagonal d * X⁻¹ + E) * X = diagonal d + X⁻¹ * E * X := by
    rw [Matrix.mul_add, Matrix.add_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hXd, Matrix.one_mul,
      Matrix.mul_assoc, nonsing_inv_mul _ hXd, Matrix.mul_one]
  have hspec : μ ∈ spectrum ℂ (diagonal d + X⁻¹ * E * X) := by
    rw [← hsim]
    have h := spectrum.units_conjugate' (R := ℂ) (a := X * diagonal d * X⁻¹ + E) (u := hX.unit)
    rw [coe_units_inv, IsUnit.unit_spec] at h
    rwa [h]
  have hD : μ ∉ spectrum ℂ (diagonal d) := by
    rw [spectrum_diagonal]
    rintro ⟨i, hi⟩
    exact hne0 i (by rw [hi, sub_self])
  have h1 := one_le_lpOpNorm_mul_of_mem_spectrum_add p hspec hD
  have hinv : (μ • (1 : Matrix n n ℂ) - diagonal d)⁻¹ = diagonal fun i => (μ - d i)⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_one_eq_diagonal, diagonal_sub, diagonal_mul_diagonal]
    convert diagonal_one (n := n) (α := ℂ) using 2
    funext i
    exact inv_mul_cancel₀ (hne0 i)
  have hN : lpOpNorm p (μ • (1 : Matrix n n ℂ) - diagonal d)⁻¹ ≤ ‖μ - d i₀‖⁻¹ := by
    rw [hinv, lpOpNorm_diagonal]
    refine ciSup_le fun i => ?_
    rw [norm_inv]
    exact inv_anti₀ hδ (hi₀ i (Finset.mem_univ i))
  have hmul : lpOpNorm p (X⁻¹ * E * X) ≤ lpOpNorm p X⁻¹ * lpOpNorm p E * lpOpNorm p X :=
    (lpOpNorm_mul_le p _ _).trans
      (mul_le_mul_of_nonneg_right (lpOpNorm_mul_le p _ _) (lpOpNorm_nonneg p _))
  have h2 : 1 ≤ ‖μ - d i₀‖⁻¹ * (lpOpNorm p X⁻¹ * lpOpNorm p E * lpOpNorm p X) :=
    h1.trans ((lpOpNorm_mul_le p _ _).trans
      (mul_le_mul hN hmul (lpOpNorm_nonneg p _) (by positivity)))
  have h3 := mul_le_mul_of_nonneg_left h2 hδ.le
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at h3
  calc ‖μ - d i₀‖ ≤ lpOpNorm p X⁻¹ * lpOpNorm p E * lpOpNorm p X := h3
    _ = condNumberLp p X * lpOpNorm p E := by rw [condNumberLp]; ring

section Schur

open scoped Matrix.Norms.L2Operator

/-- If $|m_{ij}| \le c |n_{ij}|$ for all entries, with $c \ge 0$, then
$|(M^k)_{ij}| \le c^k (|N|^k)_{ij}$ and $(|N|^k)_{ij} \ge 0$, where $|N|$ is the entrywise
absolute value of $N$. -/
private theorem norm_pow_apply_le {M N : Matrix n n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c * ‖N i j‖) (k : ℕ) (i j : n) :
    ‖(M ^ k) i j‖ ≤ c ^ k * ((N.map (‖·‖)) ^ k) i j ∧ 0 ≤ ((N.map (‖·‖)) ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_ne hij]
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ M, Matrix.mul_apply, pow_succ (N.map (‖·‖)), Matrix.mul_apply, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [norm_mul, map_apply]
      calc ‖(M ^ k) i l‖ * ‖M l j‖ ≤ (c ^ k * ((N.map (‖·‖)) ^ k) i l) * (c * ‖N l j‖) :=
            mul_le_mul (ih i l).1 (h l j) (norm_nonneg _)
              (mul_nonneg (pow_nonneg hc _) (ih i l).2)
        _ = c ^ (k + 1) * (((N.map (‖·‖)) ^ k) i l * ‖N l j‖) := by ring
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l).2 (by rw [map_apply]; positivity)

/-- **Perturbation bound from a Schur form** ([golub2013matrix], Theorem 7.2.3). Let
$A \in \mathbb{C}^{n \times n}$, let $Q$ be unitary with $Q^H A Q = \operatorname{diag}(d) + N$,
and let $p \ge 1$ be such that the entrywise absolute value $|N|$ satisfies $|N|^p = 0$. Let
$E \in \mathbb{C}^{n \times n}$, and let $\mu$ be an eigenvalue of $A + E$. Then for some $i$
$$|\mu - d_i| \le \max\{\theta, \theta^{1/p}\}, \qquad \theta = \|E\|_2 \sum_{k=0}^{p-1}
  \|N\|_2^k.$$

The source assumes that $N$ is strictly upper triangular; this hypothesis is not needed. For a
strictly upper triangular $N$, $p = n$ always works, and the source takes the least such $p$.
With $\delta = \min_i |\mu - d_i| > 0$, the resolvent of $D + N$ is the finite Neumann series
$\sum_{k<p} ((\mu - D)^{-1} N)^k (\mu - D)^{-1}$, by the entrywise bound $|((\mu - D)^{-1} N)^p|
\le \delta^{-p} |N|^p = 0$. So $\|(\mu - A)^{-1}\|_2 \le \sum_{k<p} \|N\|_2^k / \delta^{k+1}$,
and $1 \le \|(\mu - A)^{-1}\|_2 \|E\|_2$ gives $\delta \le \theta$ if $\delta \ge 1$, and
$\delta^p \le \theta$ if $\delta < 1$. -/
theorem exists_norm_sub_le_of_schur {A : Matrix n n ℂ} {Q : Matrix n n ℂ}
    (hQ : Q ∈ unitaryGroup n ℂ) {d : n → ℂ} {N : Matrix n n ℂ}
    (hQA : star Q * A * Q = diagonal d + N) {p : ℕ} (hp : 1 ≤ p) (hN : (N.map (‖·‖)) ^ p = 0)
    (E : Matrix n n ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ i, ‖μ - d i‖ ≤
      max (‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k)
        ((‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k) ^ (1 / p : ℝ)) := by
  set θ := ‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k with hθ
  have hθ0 : 0 ≤ θ := mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
  -- the index set is nonempty, since the spectrum of `A + E` is
  have hne : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [spectrum.mem_iff] at hμ
    exact hμ (isUnit_of_subsingleton _)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ‖μ - d i‖)
    ⟨Classical.arbitrary n, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  set δ := ‖μ - d i₀‖ with hδdef
  rcases (norm_nonneg (μ - d i₀)).eq_or_lt with hδ0 | hδ
  · rw [hδdef, ← hδ0]; exact hθ0.trans (le_max_left _ _)
  have hne0 : ∀ i, μ - d i ≠ 0 := fun i hi => by
    have h := hi₀ i (Finset.mem_univ i)
    rw [hi, norm_zero] at h
    exact hδ.ne' (le_antisymm h (norm_nonneg _))
  -- the diagonal part and its inverse
  set Dμ : Matrix n n ℂ := diagonal fun i => μ - d i with hDμ
  set Dinv : Matrix n n ℂ := diagonal fun i => (μ - d i)⁻¹ with hDinv
  have hDD : Dinv * Dμ = 1 := by
    rw [hDinv, hDμ, diagonal_mul_diagonal,
      show (fun i => (μ - d i)⁻¹ * (μ - d i)) = (1 : n → ℂ) from
        funext fun i => inv_mul_cancel₀ (hne0 i)]
    simp
  have hDinv_le : ‖Dinv‖ ≤ δ⁻¹ := by
    rw [hDinv, l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [norm_inv]
    gcongr
    exact hi₀ i (Finset.mem_univ i)
  -- `M = (μ - D)⁻¹ N` is nilpotent
  set M := Dinv * N with hM
  have hMent : ∀ i j, ‖M i j‖ ≤ δ⁻¹ * ‖N i j‖ := fun i j => by
    rw [hM, hDinv, diagonal_mul, norm_mul, norm_inv]
    gcongr
    exact hi₀ i (Finset.mem_univ i)
  have hMp : M ^ p = 0 := by
    ext i j
    have h := (norm_pow_apply_le (inv_nonneg.mpr hδ.le) hMent p i j).1
    rw [hN, Matrix.zero_apply, mul_zero] at h
    simpa using h
  -- the resolvent of `B = D + N` as a finite Neumann series
  set B := diagonal d + N with hB
  set S := ∑ k ∈ Finset.range p, M ^ k with hS
  have hSinv : S * Dinv * (μ • 1 - B) = 1 := by
    have h1 : μ • (1 : Matrix n n ℂ) - B = Dμ - N := by
      rw [hB, hDμ, ← diagonal_one, ← diagonal_smul, sub_add_eq_sub_sub, diagonal_sub]
      congr 2
      funext i
      simp
    rw [h1, Matrix.mul_assoc, Matrix.mul_sub, hDD, ← hM, geom_sum_mul_neg, hMp, sub_zero]
  have hBunit : IsUnit (μ • (1 : Matrix n n ℂ) - B) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_left_inverse hSinv)
  have hBinv : (μ • (1 : Matrix n n ℂ) - B)⁻¹ = S * Dinv := inv_eq_left_inv hSinv
  have hμB : μ ∉ spectrum ℂ B := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, not_not]; exact hBunit
  -- move the perturbation to the Schur basis
  set E' := star Q * E * Q with hE'
  have hμ' : μ ∈ spectrum ℂ (B + E') := by
    rw [← hQA, hE', ← Matrix.add_mul, ← Matrix.mul_add, star_eq_conjTranspose,
      spectrum_conjTranspose_mul_mul hQ]
    exact hμ
  have hE'n : ‖E'‖ = ‖E‖ := l2_opNorm_unitary_mul_mul_unitary (Unitary.star_mem hQ) E hQ
  have hstep := one_le_norm_mul_of_mem_spectrum_add hμ' hμB
  rw [hBinv] at hstep
  -- bound the Neumann series
  have hpow : ∀ k : ℕ, ‖M ^ k‖ ≤ ‖M‖ ^ k := by
    intro k
    rcases k with _ | k
    · rw [pow_zero, pow_zero, CStarRing.norm_one]
    · exact norm_pow_le' M (Nat.succ_pos k)
  have hMnorm : ‖M‖ ≤ δ⁻¹ * ‖N‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hDinv_le (norm_nonneg _))
  have hSnorm : ‖S * Dinv‖ ≤ ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) := by
    calc ‖S * Dinv‖ ≤ ‖S‖ * ‖Dinv‖ := norm_mul_le _ _
      _ ≤ (∑ k ∈ Finset.range p, ‖M‖ ^ k) * δ⁻¹ :=
          mul_le_mul ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hpow k)) hDinv_le
            (norm_nonneg _) (Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
      _ ≤ (∑ k ∈ Finset.range p, (δ⁻¹ * ‖N‖) ^ k) * δ⁻¹ :=
          mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun k _ =>
            pow_le_pow_left₀ (norm_nonneg _) hMnorm k) (inv_nonneg.mpr hδ.le)
      _ = ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => by ring
  have hmain : 1 ≤ ‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) := by
    calc (1 : ℝ) ≤ ‖S * Dinv * E'‖ := hstep
      _ ≤ ‖S * Dinv‖ * ‖E'‖ := norm_mul_le _ _
      _ ≤ (∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1)) * ‖E‖ := by
          rw [hE'n]; exact mul_le_mul_of_nonneg_right hSnorm (norm_nonneg _)
      _ = _ := mul_comm _ _
  rcases le_or_gt 1 δ with h1 | h1
  · -- `δ ≥ 1`: every `δ^{-(k+1)} ≤ δ⁻¹`
    refine le_max_of_le_left ?_
    have : ‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) ≤ θ * δ⁻¹ := by
      rw [hθ, mul_assoc, Finset.sum_mul]
      gcongr with k
      calc δ⁻¹ ^ (k + 1) = δ⁻¹ ^ k * δ⁻¹ := pow_succ _ _
        _ ≤ 1 * δ⁻¹ := by gcongr; exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
        _ = δ⁻¹ := one_mul _
    have h2 := hmain.trans this
    rwa [← div_eq_mul_inv, one_le_div hδ] at h2
  · -- `δ < 1`: every `δ^{-(k+1)} ≤ δ^{-p}`
    refine le_max_of_le_right ?_
    have : ‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) ≤ θ * δ⁻¹ ^ p := by
      rw [hθ, mul_assoc, Finset.sum_mul]
      gcongr with k hk
      all_goals first
        | exact (one_le_inv₀ hδ).mpr h1.le
        | exact Finset.mem_range.mp hk
    have h2 := hmain.trans this
    rw [inv_pow, ← div_eq_mul_inv, one_le_div (by positivity)] at h2
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    calc δ = (δ ^ p) ^ (1 / p : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, mul_one_div_cancel hp0, Real.rpow_one]
      _ ≤ θ ^ (1 / p : ℝ) := by gcongr

end Schur

/-- **The block residual bound** ([golub2013matrix], Theorem 8.1.13, with the constant $1$ in place
of $\sqrt{2}$). Let $A \in \mathbb{K}^{n \times n}$ and $S \in \mathbb{K}^{r \times r}$ be
Hermitian, let $Q_1 \in \mathbb{K}^{n \times r}$ have orthonormal columns, $Q_1^H Q_1 = I$, and
let $\|AQ_1 - Q_1 S\|_2 \le \varepsilon$. Then for every eigenvalue $\theta$ of $S$ there is an
eigenvalue $\mu$ of $A$ with $|\mu - \theta| \le \varepsilon$.

The norm is `Matrix.lpOpNorm 2`. A unit eigenvector $y$ of $S$ for $\theta$ gives the unit
vector $x = Q_1 y$ with $Ax - \theta x = (AQ_1 - Q_1 S) y$, and
`LinearMap.IsSymmetric.exists_hasEigenvalue_dist_le` gives the rest. The form of the source,
with $\sqrt{2} \varepsilon$ and distinct eigenvalues of $A$ for the eigenvalues of $S$, is
`Matrix.IsHermitian.exists_embedding_abs_sub_le_of_mul_sub_mul`. -/
theorem IsHermitian.exists_mem_spectrum_abs_sub_le_of_mul_sub_mul {r : Type*} [Fintype r]
    [DecidableEq r] {A : Matrix n n 𝕜} {S : Matrix r r 𝕜} (hA : A.IsHermitian)
    (hS : S.IsHermitian) {Q₁ : Matrix n r 𝕜} (hQ : Q₁ᴴ * Q₁ = 1) {ε : ℝ}
    (hε : lpOpNorm 2 (A * Q₁ - Q₁ * S) ≤ ε) {θ : ℝ} (hθ : θ ∈ spectrum ℝ S) :
    ∃ μ ∈ spectrum ℝ A, |μ - θ| ≤ ε := by
  rw [hS.spectrum_real_eq_range_eigenvalues] at hθ
  obtain ⟨k, rfl⟩ := hθ
  set y := hS.eigenvectorBasis k with hy
  have hy1 : ‖y‖ = 1 := hS.eigenvectorBasis.orthonormal.1 k
  set x : EuclideanSpace 𝕜 n := toEuclideanLin Q₁ y with hx
  -- `Q₁` is an isometry
  have hxy : ‖x‖ = ‖y‖ := by
    have h : (inner 𝕜 x x : 𝕜) = inner 𝕜 y y := by
      rw [hx, inner_toEuclideanLin_apply, hQ]
      simp
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'
  have hx1 : ‖x‖ = 1 := hxy.trans hy1
  have hx0 : x ≠ 0 := by rintro h; rw [h, norm_zero] at hx1; exact zero_ne_one hx1
  have hres : toEuclideanLin A x - ((hS.eigenvalues k : ℝ) : 𝕜) • x =
      toEuclideanLin (A * Q₁ - Q₁ * S) y := by
    have hSy : S *ᵥ ⇑y = ((hS.eigenvalues k : ℝ) : 𝕜) • ⇑y := by
      rw [hS.mulVec_eigenvectorBasis k, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    apply WithLp.ofLp_injective 2
    simp only [hx, WithLp.ofLp_sub, WithLp.ofLp_smul, toLpLin_apply, WithLp.ofLp_toLp,
      sub_mulVec, ← mulVec_mulVec, hSy, mulVec_smul]
  obtain ⟨μ, hμ, hμle⟩ := (isSymmetric_toEuclideanLin_iff.mpr hA).exists_hasEigenvalue_dist_le
    (hS.eigenvalues k) hx0
  have hμsp : μ ∈ spectrum 𝕜 A := by
    rw [← spectrum_toLpLin (p := 2)]
    exact hμ.mem_spectrum
  rw [hA.spectrum_eq_image_range] at hμsp
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hμsp
  refine ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i, ?_⟩
  rw [hres, hx1, div_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal] at hμle
  refine hμle.trans ((norm_toEuclideanLin_apply_le _ _).trans ?_)
  rw [hy1, mul_one, ← lpOpNorm_two]
  exact hε

open scoped Matrix.Norms.L2Operator in
/-- **The paired block residual bound** ([golub2013matrix], Theorem 8.1.13). Let
$A \in \mathbb{K}^{n \times n}$ and $S \in \mathbb{K}^{r \times r}$ be Hermitian, let
$Q_1 \in \mathbb{K}^{n \times r}$ have orthonormal columns, $Q_1^H Q_1 = I$, and let
$\|AQ_1 - Q_1 S\|_2 \le \varepsilon$. Let $\lambda_0(A) \ge \lambda_1(A) \ge \cdots$ and
$\lambda_0(S) \ge \lambda_1(S) \ge \cdots$ be the sorted eigenvalues. Then there is a strictly
increasing map $\sigma$ from the indices of $S$ to the indices of $A$ such that for every $k$
$$|\lambda_{\sigma(k)}(A) - \lambda_k(S)| \le \sqrt{2} \, \varepsilon.$$

The sorted eigenvalues are `Matrix.IsHermitian.eigenvalues₀`, and $\sigma$ is an order embedding
`Fin (Fintype.card r) ↪o Fin (Fintype.card n)`. With $F = AQ_1 - Q_1 S$, the Hermitian matrix
$B = A - F Q_1^H - Q_1 F^H + Q_1 (F^H Q_1) Q_1^H$ satisfies $BQ_1 = Q_1 S$. So the eigenvectors
of $S$, carried by $Q_1$, are orthonormal eigenvectors of $B$, and the sorted eigenvalues of $S$
are a sublist of those of $B$ (`LinearMap.IsSymmetric.exists_orderEmbedding_eigenvalues_eq`).
Also $(A - B) x = F Q_1^H x + Q_1 F^H (1 - Q_1 Q_1^H) x$ has norm at most $\varepsilon (\|Px\| +
\|(1 - P) x\|) \le \sqrt{2} \varepsilon \|x\|$, where $P$ is the orthogonal projection onto the
range of $Q_1$; this is the bound $\|E\|_2 \le \sqrt{2} \|E_1\|_2$ of the source. Weyl's
inequality then compares the eigenvalues of $A$ and $B$ index by index. -/
theorem IsHermitian.exists_embedding_abs_sub_le_of_mul_sub_mul {r : Type*} [Fintype r]
    [DecidableEq r] {A : Matrix n n 𝕜} {S : Matrix r r 𝕜} (hA : A.IsHermitian)
    (hS : S.IsHermitian) {Q₁ : Matrix n r 𝕜} (hQ : Q₁ᴴ * Q₁ = 1) {ε : ℝ}
    (hε : lpOpNorm 2 (A * Q₁ - Q₁ * S) ≤ ε) :
    ∃ σ : Fin (Fintype.card r) ↪o Fin (Fintype.card n),
      ∀ k, |hA.eigenvalues₀ (σ k) - hS.eigenvalues₀ k| ≤ √2 * ε := by
  set F := A * Q₁ - Q₁ * S with hF
  have hε0 : 0 ≤ ε := (lpOpNorm_nonneg 2 F).trans hε
  have hFn : ‖F‖ ≤ ε := by rw [← lpOpNorm_two]; exact hε
  -- `Q₁ᴴ F = Fᴴ Q₁ = Q₁ᴴ A Q₁ - S`
  have e1 : Q₁ᴴ * F = Q₁ᴴ * A * Q₁ - S := by
    rw [hF, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have e2 : Fᴴ * Q₁ = Q₁ᴴ * A * Q₁ - S := by
    rw [hF, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hA.eq, hS.eq,
      Matrix.sub_mul, Matrix.mul_assoc S, hQ, Matrix.mul_one]
  have hFQ : Q₁ᴴ * F = Fᴴ * Q₁ := e1.trans e2.symm
  -- the comparison matrix `B`
  set B := A - F * Q₁ᴴ - Q₁ * Fᴴ + Q₁ * (Fᴴ * Q₁) * Q₁ᴴ with hB
  have hBh : B.IsHermitian := by
    have h1 : Bᴴ = A - Q₁ * Fᴴ - F * Q₁ᴴ + Q₁ * (Q₁ᴴ * F) * Q₁ᴴ := by
      rw [hB]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul,
        conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
    change Bᴴ = B
    rw [h1, hFQ, hB]
    abel
  have hBQ : B * Q₁ = Q₁ * S := by
    rw [hB]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hQ, Matrix.mul_one]
    rw [hF]
    abel
  have hG : A - B = F * Q₁ᴴ + Q₁ * Fᴴ * (1 - Q₁ * Q₁ᴴ) := by
    rw [hB, Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    abel
  -- the perturbation `A - B` is at most `√2 ε`
  have hAB : ∀ x : EuclideanSpace 𝕜 n,
      ‖(toEuclideanLin A - toEuclideanLin B) x‖ ≤ √2 * ε * ‖x‖ := by
    intro x
    set K := LinearMap.range (toEuclideanLin Q₁) with hK
    have hP : ∀ y, toEuclideanLin (Q₁ * Q₁ᴴ) y = K.starProjection y := fun y => by
      rw [LinearMap.congr_fun (toEuclideanLin_mul_conjTranspose_eq_starProjection hQ) y]
      rfl
    have hiso : ∀ z, ‖toEuclideanLin Q₁ z‖ = ‖z‖ := fun z =>
      (toEuclideanLinearIsometry hQ).norm_map z
    have ha : ‖toEuclideanLin Q₁ᴴ x‖ = ‖K.starProjection x‖ := by
      rw [← hiso, ← toEuclideanLin_mul_apply, hP]
    have hb : toEuclideanLin (1 - Q₁ * Q₁ᴴ) x = Kᗮ.starProjection x := by
      rw [map_sub, LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply, hP,
        Submodule.starProjection_orthogonal_val]
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection x K
    have hsplit : toEuclideanLin (A - B) x = toEuclideanLin F (toEuclideanLin Q₁ᴴ x) +
        toEuclideanLin Q₁ (toEuclideanLin Fᴴ (toEuclideanLin (1 - Q₁ * Q₁ᴴ) x)) := by
      rw [hG, map_add, LinearMap.add_apply, toEuclideanLin_mul_apply F Q₁ᴴ,
        toEuclideanLin_mul_apply (Q₁ * Fᴴ), toEuclideanLin_mul_apply Q₁ Fᴴ]
    have h1 : ‖toEuclideanLin F (toEuclideanLin Q₁ᴴ x)‖ ≤ ε * ‖K.starProjection x‖ :=
      (norm_toEuclideanLin_apply_le _ _).trans (by
        rw [ha]
        exact mul_le_mul_of_nonneg_right hFn (norm_nonneg _))
    have h2 : ‖toEuclideanLin Q₁ (toEuclideanLin Fᴴ (toEuclideanLin (1 - Q₁ * Q₁ᴴ) x))‖ ≤
        ε * ‖Kᗮ.starProjection x‖ := by
      rw [hiso, hb]
      refine (norm_toEuclideanLin_apply_le _ _).trans ?_
      rw [l2_opNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right hFn (norm_nonneg _)
    have hsum : ‖K.starProjection x‖ + ‖Kᗮ.starProjection x‖ ≤ √2 * ‖x‖ := by
      rw [show √2 * ‖x‖ = √(2 * ‖x‖ ^ 2) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]]
      exact Real.le_sqrt_of_sq_le (by
        nlinarith [sq_nonneg (‖K.starProjection x‖ - ‖Kᗮ.starProjection x‖)])
    rw [← map_sub, hsplit]
    have := mul_le_mul_of_nonneg_left hsum hε0
    calc _ ≤ ‖toEuclideanLin F (toEuclideanLin Q₁ᴴ x)‖ +
          ‖toEuclideanLin Q₁ (toEuclideanLin Fᴴ (toEuclideanLin (1 - Q₁ * Q₁ᴴ) x))‖ :=
          norm_add_le _ _
      _ ≤ √2 * ε * ‖x‖ := by linarith
  -- the eigenvectors of `S`, carried by `Q₁`, are eigenvectors of `B`
  have hTA := isSymmetric_toEuclideanLin_iff.mpr hA
  have hTB := isSymmetric_toEuclideanLin_iff.mpr hBh
  have hTS := isSymmetric_toEuclideanLin_iff.mpr hS
  set y := hTS.eigenvectorBasis finrank_euclideanSpace with hy
  have hv : Orthonormal 𝕜 fun k => toEuclideanLin Q₁ (y k) :=
    y.orthonormal.comp_linearIsometry (toEuclideanLinearIsometry hQ)
  have hBv : ∀ k, toEuclideanLin B (toEuclideanLin Q₁ (y k)) =
      (hTS.eigenvalues finrank_euclideanSpace k : 𝕜) • toEuclideanLin Q₁ (y k) := fun k => by
    rw [← toEuclideanLin_mul_apply, hBQ, toEuclideanLin_mul_apply,
      hTS.apply_eigenvectorBasis, map_smul]
  obtain ⟨σ, hσ⟩ := hTB.exists_orderEmbedding_eigenvalues_eq finrank_euclideanSpace hv
    (hTS.eigenvalues_antitone finrank_euclideanSpace) hBv
  refine ⟨σ, fun k => ?_⟩
  change |hTA.eigenvalues finrank_euclideanSpace (σ k) -
    hTS.eigenvalues finrank_euclideanSpace k| ≤ _
  rw [← hσ k]
  exact hTA.abs_eigenvalues_sub_le hTB finrank_euclideanSpace hAB (σ k)

end Matrix
